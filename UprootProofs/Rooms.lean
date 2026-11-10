-- SPDX-License-Identifier: 0BSD

/-!
# A formal model of uproot's room state machine

Sources modelled:
* `src/uproot/rooms.py`               — `room`, `ready`, `freejoin`, `validate`, `sync`
* `src/uproot/services/room_service.py` — disassociate/close/open/capacity/delete
* `src/uproot/server2.py`, `server4.py` — create/update rooms, new session in room
* `src/uproot/server3.py`               — `roommain` (player admission)
* `src/uproot/core.py`                  — `create_session` sets `session.room = None`
* `src/uproot/server.py`, `jobs.py`     — startup: `synchronize_rooms`, then `sync`

Names are abstract strings. Label syntax (`valid_token`, length ≤ 128,
uniqueness) is not modelled; only its consequences for admission are.

Each `Step` is one request handler, taken as atomic: uproot serves from a single
process and event-loop thread (`cli.py`), no room-mutating handler awaits between
its reads and its writes, and every handler that can fail does so before its
first write (in-place changes are flushed only when an `Admin()` context exits
cleanly). A process crash in the middle of a handler is not modelled.
-/

namespace Rooms

abbrev RoomName := String
abbrev SName := String
abbrev Label := String
abbrev Config := String

/-- A stored room (`rooms.room`). `room` maps `""` to `None` for `config` and
`sname`, and every capacity is a non-negative `int` (`rooms.check_capacity`,
`ge=0` on the form/API fields that set one), so `Option` and `Nat` are exact.
`isOpen` is the truthiness of `room["open"]`, which is how both `ready` and
`set_room_open` read it. Whether a room is ready also depends on which configs
are loaded (`uproot.CONFIGS`), passed as `loaded`. -/
structure Room where
  config   : Option Config
  labels   : Option (List Label)
  capacity : Option Nat
  isOpen   : Bool
  sname    : Option SName

namespace Room

/-- `rooms.ready`: open, and associated with a session or a loaded config. -/
def ready (ρ : Room) (loaded : Config → Bool) : Bool :=
  ρ.isOpen && (ρ.sname.isSome || ρ.config.any loaded)

/-- `rooms.freejoin`: `not room["labels"]` is true for `None` and `[]`. -/
def freejoin (ρ : Room) : Bool :=
  (ρ.labels.getD []).isEmpty && ρ.capacity.isNone

/-- `rooms.validate` -/
def validate (ρ : Room) (label : Label) : Bool :=
  if ρ.freejoin then true
  else match ρ.labels with
    | none => true
    | some [] => label != ""
    | some ls => label != "" && ls.contains label

/-- The `capacity` local in `roommain`. -/
def cap (ρ : Room) : Nat :=
  match ρ.capacity, ρ.labels with
  | some c, _ => c
  | none, some ls => ls.length
  | none, none => 0

end Room

/-! ## Player admission (`server3.roommain`) -/

inductive Outcome
  | askLabel | badLabel | wait     -- RoomHello.html
  | resume                         -- redirect to existing started player with label
  | reuseSlot | newPlayer          -- admitted
  | full                           -- RoomFull.html (423)
  deriving DecidableEq, Repr

/-- `loaded`: the loaded configs. `labelStarted`: some started player in the
session already has `label`. `freeSlot`: `core.find_free_slot` returned a slot.
`n`: number of players. -/
def admit (loaded : Config → Bool) (ρ : Room) (label : Label) (n : Nat)
    (labelStarted freeSlot : Bool) : Outcome :=
  if ρ.labels.isSome && label == "" then .askLabel
  else if ρ.labels.isSome && !ρ.validate label then .badLabel
  else if !ρ.ready loaded then .wait
  else if label != "" && labelStarted then .resume
  else if ρ.freejoin || decide (n < ρ.cap) || freeSlot then
    (if freeSlot then .reuseSlot else .newPlayer)
  else .full

def Outcome.admitted : Outcome → Bool
  | .resume | .reuseSlot | .newPlayer => true
  | _ => false

section Admission
variable (loaded : Config → Bool) (ρ : Room) (label : Label) (n : Nat) (ls fs : Bool)

/-- A room that is not ready never lets anyone through. -/
theorem not_ready_no_admission (h : ρ.ready loaded = false) :
    (admit loaded ρ label n ls fs).admitted = false := by
  unfold admit; split <;> try rfl
  split <;> try rfl
  simp [h, Outcome.admitted]

/-- Admitted ⇒ ready. -/
theorem admitted_ready (h : (admit loaded ρ label n ls fs).admitted = true) : ρ.ready loaded = true := by
  cases hr : ρ.ready loaded
  · simp [not_ready_no_admission loaded ρ label n ls fs hr] at h
  · rfl

/-- A brand-new player is created only in a freejoin room or below capacity. -/
theorem newPlayer_within_capacity (h : admit loaded ρ label n ls fs = .newPlayer) :
    ρ.freejoin = true ∨ n < ρ.cap := by
  unfold admit at h
  repeat (split at h <;> simp_all)
  all_goals grind

/-- Hence, outside freejoin rooms, joining never grows a session past
`max n cap`: if `n ≤ cap` before, then `n' ≤ cap` after. -/
theorem join_preserves_bound (hf : ρ.freejoin = false) (hb : n ≤ ρ.cap) :
    let n' := if admit loaded ρ label n ls fs = .newPlayer then n + 1 else n
    n' ≤ ρ.cap := by
  intro n'
  by_cases h : admit loaded ρ label n ls fs = .newPlayer
  · have := newPlayer_within_capacity loaded ρ label n ls fs h
    simp [n', h]; grind
  · simp [n', h]; exact hb

/-- Capacity 0 (commit a83cb38): no new player is ever created. -/
theorem capacity_zero (h : ρ.capacity = some 0) :
    admit loaded ρ label n ls fs ≠ .newPlayer := by
  intro hp
  have := newPlayer_within_capacity loaded ρ label n ls fs hp
  simp [Room.freejoin, Room.cap, h] at this

/-- Labelled rooms never admit the empty label. -/
theorem labelled_nonempty (hl : ρ.labels.isSome = true)
    (h : (admit loaded ρ label n ls fs).admitted = true) : label ≠ "" := by
  intro he; subst he; simp [admit, hl, Outcome.admitted] at h

/-- With a non-empty label list, every admitted label is on the list. -/
theorem whitelist (ls' : List Label) (hl : ρ.labels = some ls') (hne : ls' ≠ [])
    (h : (admit loaded ρ label n ls fs).admitted = true) : label ∈ ls' := by
  have hv : ρ.validate label = true := by
    unfold admit at h
    by_cases hv : ρ.validate label = true
    · exact hv
    · exfalso; simp only [hl, hv] at h
      repeat (split at h <;> simp [Outcome.admitted] at h)
  have hfj : ρ.freejoin = false := by
    cases ls' with
    | nil => contradiction
    | cons _ _ => simp [Room.freejoin, hl]
  unfold Room.validate at hv
  simp only [hfj, hl] at hv
  split at hv
  · contradiction
  · simp_all

end Admission

/-! ## The global state machine -/

def upd {α β} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β} [DecidableEq α] (f : α → β) (a b) : upd f a b a = b := by
  simp [upd]
@[simp] theorem upd_other {α β} [DecidableEq α] (f : α → β) (a b x) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

structure World where
  rooms    : RoomName → Option Room          -- admin.rooms
  sessions : SName → Bool                    -- admin._uproot_sessions (never shrinks)
  sessRoom : SName → Option RoomName         -- session.room
  event    : RoomName → Bool                 -- events.ROOMS[r].is_set()
  configs  : Config → Bool                   -- uproot.CONFIGS (fixed while a process runs)

/-- Nothing stored, and no process running yet (the first start is a `restart`). -/
def World.init : World :=
  ⟨fun _ => none, fun _ => false, fun _ => none, fun _ => false, fun _ => false⟩

/-- `rooms.sync` -/
def World.sync (w : World) (r : RoomName) : World :=
  { w with event := upd w.event r ((w.rooms r).any (·.ready w.configs)) }

def World.setRoom (w : World) (r : RoomName) (o : Option Room) : World :=
  { w with rooms := upd w.rooms r o }

def World.link (w : World) (s : SName) (o : Option RoomName) : World :=
  { w with sessRoom := upd w.sessRoom s o }

def World.linkOpt (w : World) : Option SName → RoomName → World
  | none, _ => w
  | some s, r => w.link s (some r)

/-- `core.create_session` -/
def World.newSession (w : World) (s : SName) : World :=
  { w with sessions := upd w.sessions s true, sessRoom := upd w.sessRoom s none }

/-- `jobs.synchronize_rooms`: add each default room whose name is still free. -/
def World.addDefaults (w : World) : List (RoomName × Room) → World
  | [] => w
  | (r, ρ) :: ds => (if (w.rooms r).isNone then w.setRoom r (some ρ) else w).addDefaults ds

/-- The startup loop `for roomname in roomnames: r.sync(roomname)` (`server.py`). -/
def World.syncAll (w : World) (names : List RoomName) : World := names.foldl World.sync w

/-- A new process: rooms and sessions are stored and persist, `events.ROOMS` (an
in-memory `defaultdict(Event)`) starts out empty, and `uproot.CONFIGS` holds the
configs the project loads now (`load_config` runs before the server starts). -/
def World.start (w : World) (loaded : Config → Bool) : World :=
  { w with event := fun _ => false, configs := loaded }

/-- `room_service.ensure_session_available_for_room` -/
def available (w : World) (s : SName) (r : RoomName) : Prop :=
  w.sessions s = true ∧
  (∀ r' ρ', r' ≠ r → w.rooms r' = some ρ' → ρ'.sname ≠ some s) ∧
  (w.sessRoom s = none ∨ w.sessRoom s = some r)

inductive Step : World → World → Prop
  /-- `create_session` (also used inside other steps below). Fresh name required. -/
  | newSession (w s) : w.sessions s = false → Step w (w.newSession s)
  /-- `server2.new_room2`, `server4.create_room`, `jobs.synchronize_rooms`, and
  the CLI quick room (synced by the startup `sync` loop in `server.py`). -/
  | createRoom (w r ρ) : w.rooms r = none →
      (∀ s, ρ.sname = some s → available w s r) →
      Step w (((w.setRoom r (some ρ)).linkOpt ρ.sname r).sync r)
  /-- `server2.update_room_settings`, `server4.update_room` -/
  | updateRoom (w r cur ρ) : w.rooms r = some cur → cur.sname = none →
      (∀ s, ρ.sname = some s → available w s r) →
      Step w (((w.setRoom r (some ρ)).linkOpt ρ.sname r).sync r)
  /-- `room_service.disassociate(r, s)`, which raises unless `s` is the room's
  own session (callers, e.g. a stale admin page, may pass an outdated `s`). -/
  | disassociate (w r ρ s) : w.rooms r = some ρ → ρ.sname = some s →
      Step w (((w.setRoom r (some { ρ with sname := none })).link s none).sync r)
  /-- `room_service.close_room` after (optional) disassociation -/
  | close (w r ρ) : w.rooms r = some ρ → ρ.sname = none →
      Step w ((w.setRoom r (some { ρ with isOpen := false })).sync r)
  /-- `room_service.set_room_open`, which refuses to open a room unless that
  makes it ready (a session or a loaded config). -/
  | setOpen (w r ρ b) : w.rooms r = some ρ →
      (b = true → ρ.sname.isSome ∨ ρ.config.any w.configs) →
      Step w ((w.setRoom r (some { ρ with isOpen := b })).sync r)
  /-- `room_service.set_room_capacity` — note: does NOT call `sync`. -/
  | setCapacity (w r ρ c) : w.rooms r = some ρ →
      Step w (w.setRoom r (some { ρ with capacity := c }))
  /-- `room_service.delete_room` -/
  | delete (w r ρ) : w.rooms r = some ρ → ρ.sname = none →
      Step w ((w.setRoom r none).sync r)
  /-- `server2`/`server4` "new session in room": fresh session, room opened,
  capacity optionally pinned (`disable_growth`/`no_grow`). The session and its
  players are created before the room is touched, so a failure (e.g. bad
  usernames) changes nothing and no `sync` is missed. -/
  | sessionInRoom (w r ρ s c) : w.rooms r = some ρ → ρ.sname = none →
      w.sessions s = false →
      Step w ((((w.newSession s).setRoom r
        (some { ρ with sname := some s, isOpen := true, capacity := c })).link s (some r)).sync r)
  /-- `roommain` auto-creating a session for a ready room — does NOT call `sync`. -/
  | joinCreates (w r ρ s) : w.rooms r = some ρ → ρ.ready w.configs = true → ρ.sname = none →
      w.sessions s = false →
      Step w (((w.newSession s).setRoom r (some { ρ with sname := some s })).link s (some r))
  /-- Server (re)start, the `server.py` lifespan, which finishes before any request
  is served. Rooms and sessions persist; `events.ROOMS` starts out empty; the
  project may now load different configs (`loaded`); `synchronize_rooms` adds the
  default rooms (startup fails if one has a session); then every stored room is
  synced. (The CLI quick room, created in the same process just before startup,
  amounts to `restart` followed by `newSession` and `createRoom`.) -/
  | restart (w ds names loaded) : (∀ d ∈ ds, d.2.sname = none) →
      (∀ r, (((w.start loaded).addDefaults ds).rooms r).isSome → r ∈ names) →
      Step w (((w.start loaded).addDefaults ds).syncAll names)

/-! ## Invariants -/

/-- Waiting players are released exactly when the room is ready. -/
def EventsOK (w : World) : Prop := ∀ r, w.event r = (w.rooms r).any (·.ready w.configs)

/-- `room.sname` and `session.room` are mutually inverse, and refer to existing sessions. -/
def AssocOK (w : World) : Prop :=
  (∀ r ρ s, w.rooms r = some ρ → ρ.sname = some s → w.sessRoom s = some r ∧ w.sessions s = true) ∧
  (∀ s r, w.sessRoom s = some r → ∃ ρ, w.rooms r = some ρ ∧ ρ.sname = some s)

def RoomInv (w : World) : Prop := EventsOK w ∧ AssocOK w

theorem inv_init : RoomInv World.init := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [World.init, EventsOK]

/-! Field lemmas -/
section Fields
variable (w : World) (r : RoomName) (s : SName) (o : Option Room) (q : Option RoomName)
  (os : Option SName)
@[simp] theorem sync_rooms : (w.sync r).rooms = w.rooms := rfl
@[simp] theorem sync_sessions : (w.sync r).sessions = w.sessions := rfl
@[simp] theorem sync_sessRoom : (w.sync r).sessRoom = w.sessRoom := rfl
@[simp] theorem sync_configs : (w.sync r).configs = w.configs := rfl
@[simp] theorem setRoom_rooms : (w.setRoom r o).rooms = upd w.rooms r o := rfl
@[simp] theorem setRoom_sessions : (w.setRoom r o).sessions = w.sessions := rfl
@[simp] theorem setRoom_sessRoom : (w.setRoom r o).sessRoom = w.sessRoom := rfl
@[simp] theorem setRoom_event : (w.setRoom r o).event = w.event := rfl
@[simp] theorem setRoom_configs : (w.setRoom r o).configs = w.configs := rfl
@[simp] theorem link_rooms : (w.link s q).rooms = w.rooms := rfl
@[simp] theorem link_sessions : (w.link s q).sessions = w.sessions := rfl
@[simp] theorem link_sessRoom : (w.link s q).sessRoom = upd w.sessRoom s q := rfl
@[simp] theorem link_event : (w.link s q).event = w.event := rfl
@[simp] theorem link_configs : (w.link s q).configs = w.configs := rfl
@[simp] theorem linkOpt_rooms : (w.linkOpt os r).rooms = w.rooms := by cases os <;> rfl
@[simp] theorem linkOpt_sessions : (w.linkOpt os r).sessions = w.sessions := by cases os <;> rfl
@[simp] theorem linkOpt_event : (w.linkOpt os r).event = w.event := by cases os <;> rfl
@[simp] theorem linkOpt_configs : (w.linkOpt os r).configs = w.configs := by cases os <;> rfl
@[simp] theorem linkOpt_none : w.linkOpt none r = w := rfl
@[simp] theorem linkOpt_some : w.linkOpt (some s) r = w.link s (some r) := rfl
@[simp] theorem newSession_rooms : (w.newSession s).rooms = w.rooms := rfl
@[simp] theorem newSession_sessions : (w.newSession s).sessions = upd w.sessions s true := rfl
@[simp] theorem newSession_sessRoom : (w.newSession s).sessRoom = upd w.sessRoom s none := rfl
@[simp] theorem newSession_event : (w.newSession s).event = w.event := rfl
@[simp] theorem newSession_configs : (w.newSession s).configs = w.configs := rfl
variable (loaded : Config → Bool)
@[simp] theorem start_rooms : (w.start loaded).rooms = w.rooms := rfl
@[simp] theorem start_sessions : (w.start loaded).sessions = w.sessions := rfl
@[simp] theorem start_sessRoom : (w.start loaded).sessRoom = w.sessRoom := rfl
@[simp] theorem start_event : (w.start loaded).event r = false := rfl
@[simp] theorem start_configs : (w.start loaded).configs = loaded := rfl
end Fields

section Startup
variable (ds : List (RoomName × Room)) (names : List RoomName)

@[simp] theorem addDefaults_sessions (w : World) : (w.addDefaults ds).sessions = w.sessions := by
  induction ds generalizing w with
  | nil => rfl
  | cons d ds ih => obtain ⟨r, ρ⟩ := d; simp only [World.addDefaults, ih]; split <;> rfl
@[simp] theorem addDefaults_sessRoom (w : World) : (w.addDefaults ds).sessRoom = w.sessRoom := by
  induction ds generalizing w with
  | nil => rfl
  | cons d ds ih => obtain ⟨r, ρ⟩ := d; simp only [World.addDefaults, ih]; split <;> rfl
@[simp] theorem addDefaults_event (w : World) : (w.addDefaults ds).event = w.event := by
  induction ds generalizing w with
  | nil => rfl
  | cons d ds ih => obtain ⟨r, ρ⟩ := d; simp only [World.addDefaults, ih]; split <;> rfl
@[simp] theorem addDefaults_configs (w : World) : (w.addDefaults ds).configs = w.configs := by
  induction ds generalizing w with
  | nil => rfl
  | cons d ds ih => obtain ⟨r, ρ⟩ := d; simp only [World.addDefaults, ih]; split <;> rfl

/-- `synchronize_rooms` never replaces a stored room. -/
theorem addDefaults_keep (w : World) {r ρ} (h : w.rooms r = some ρ) :
    (w.addDefaults ds).rooms r = some ρ := by
  induction ds generalizing w with
  | nil => exact h
  | cons d ds ih =>
    obtain ⟨r', ρ'⟩ := d
    simp only [World.addDefaults]
    apply ih
    split
    · next hn =>
      have : r ≠ r' := by intro e; subst e; simp [h] at hn
      simp [this, h]
    · exact h

/-- Every room after `synchronize_rooms` was stored before or is a default room. -/
theorem addDefaults_cases (w : World) {r ρ} (h : (w.addDefaults ds).rooms r = some ρ) :
    w.rooms r = some ρ ∨ (r, ρ) ∈ ds := by
  induction ds generalizing w with
  | nil => exact .inl h
  | cons d ds ih =>
    obtain ⟨r', ρ'⟩ := d
    simp only [World.addDefaults] at h
    rcases ih _ h with h' | h'
    · split at h'
      · by_cases e : r = r'
        · subst e; simp at h'; subst h'; exact .inr (by simp)
        · simp [e] at h'; exact .inl h'
      · exact .inl h'
    · exact .inr (by simp [h'])

@[simp] theorem syncAll_rooms (w : World) : (w.syncAll names).rooms = w.rooms := by
  induction names generalizing w with
  | nil => rfl
  | cons a l ih => simp [World.syncAll, List.foldl] at ih ⊢; rw [ih]; rfl
@[simp] theorem syncAll_sessions (w : World) : (w.syncAll names).sessions = w.sessions := by
  induction names generalizing w with
  | nil => rfl
  | cons a l ih => simp [World.syncAll, List.foldl] at ih ⊢; rw [ih]; rfl
@[simp] theorem syncAll_sessRoom (w : World) : (w.syncAll names).sessRoom = w.sessRoom := by
  induction names generalizing w with
  | nil => rfl
  | cons a l ih => simp [World.syncAll, List.foldl] at ih ⊢; rw [ih]; rfl
@[simp] theorem syncAll_configs (w : World) : (w.syncAll names).configs = w.configs := by
  induction names generalizing w with
  | nil => rfl
  | cons a l ih => simp [World.syncAll, List.foldl] at ih ⊢; rw [ih]; rfl

/-- After the startup loop, each listed room's event reflects readiness. -/
theorem syncAll_event (w : World) (r : RoomName) :
    (w.syncAll names).event r =
      if r ∈ names then (w.rooms r).any (·.ready w.configs) else w.event r := by
  induction names generalizing w with
  | nil => simp [World.syncAll]
  | cons a l ih =>
    have := ih (w.sync a)
    simp only [World.syncAll, List.foldl] at this ⊢
    rw [this]
    by_cases hl : r ∈ l
    · simp [hl, World.sync]
    · by_cases ha : r = a
      · subst ha; simp [hl, World.sync]
      · simp [hl, ha, World.sync]
end Startup

/-- `sync r` repairs room `r`; everything else must already be consistent. -/
theorem events_sync {w : World} (X : World) (r : RoomName) (he : EventsOK w)
    (hev : X.event = w.event) (hcf : X.configs = w.configs)
    (hro : ∀ r', r' ≠ r → X.rooms r' = w.rooms r') :
    EventsOK (X.sync r) := by
  intro r'
  by_cases h : r' = r
  · subst h; simp [World.sync]
  · simp [World.sync, h, hev, hcf, hro r' h, he r']

/-- Theorem 1: after every step, waiting players are released iff the room is ready —
including the two steps that skip `sync` (`setCapacity`, `joinCreates`). -/
theorem step_events {w w'} (he : EventsOK w) (st : Step w w') : EventsOK w' := by
  cases st with
  | newSession => exact he
  | setCapacity r ρ c hr =>
    intro r'
    by_cases h : r' = r
    · subst h; simp [he r', hr, Room.ready]
    · simp [h, he r']
  | joinCreates r ρ s hr hready =>
    intro r'
    by_cases h : r' = r
    · subst h
      simp [Room.ready, he r', hr] at hready ⊢
      simp_all
    · simp [h, he r']
  | createRoom r => exact events_sync _ r he (by simp) (by simp) (by intro r' h; simp [h])
  | updateRoom r => exact events_sync _ r he (by simp) (by simp) (by intro r' h; simp [h])
  | disassociate r => exact events_sync _ r he (by simp) (by simp) (by intro r' h; simp [h])
  | close r => exact events_sync _ r he (by simp) (by simp) (by intro r' h; simp [h])
  | setOpen r => exact events_sync _ r he (by simp) (by simp) (by intro r' h; simp [h])
  | delete r => exact events_sync _ r he (by simp) (by simp) (by intro r' h; simp [h])
  | sessionInRoom r => exact events_sync _ r he (by simp) (by simp) (by intro r' h; simp [h])
  | restart ds names loaded _ hnames =>
    intro r
    rw [syncAll_event, syncAll_rooms, syncAll_configs]
    split
    · rfl
    · next hr =>
      cases hx : ((w.start loaded).addDefaults ds).rooms r with
      | none => simp
      | some ρ => exact absurd (hnames r (by simp [hx])) hr

/-- Helper: no room claims a session that does not exist. -/
theorem fresh_unclaimed {w : World} (h : AssocOK w) {s} (hs : w.sessions s = false) :
    (∀ r ρ, w.rooms r = some ρ → ρ.sname ≠ some s) ∧ w.sessRoom s = none := by
  constructor
  · intro r ρ hr he; have := (h.1 r ρ s hr he).2; simp_all
  · cases hq : w.sessRoom s with
    | none => rfl
    | some r =>
      obtain ⟨ρ, hr, he⟩ := h.2 s r hq
      have := (h.1 r ρ s hr he).2; simp_all

/-- Theorem 2: the room ↔ session association stays a consistent bijection. -/
theorem step_assoc {w w'} (ha : AssocOK w) (st : Step w w') : AssocOK w' := by
  obtain ⟨h1, h2⟩ := ha
  cases st with
  | newSession s hs =>
    have ⟨hu, hn⟩ := fresh_unclaimed ⟨h1, h2⟩ hs
    constructor
    · intro r ρ s' hr he
      have := hu r ρ hr
      by_cases e : s' = s
      · subst e; contradiction
      · simp [e, h1 r ρ s' hr he]
    · intro s' r hq
      by_cases e : s' = s
      · subst e; simp at hq
      · simp [e] at hq; simpa using h2 s' r hq
  | createRoom r ρ =>
    cases hs : ρ.sname <;> constructor <;> intros <;> simp_all [upd, available] <;> grind
  | updateRoom r cur ρ =>
    cases hs : ρ.sname <;> constructor <;> intros <;> simp_all [upd, available] <;> grind
  | restart ds names loaded hds =>
    constructor
    · intro r ρ s hr he
      simp only [syncAll_rooms] at hr
      rcases addDefaults_cases _ _ hr with h | h
      · simpa using h1 r ρ s (by simpa using h) he
      · have : ρ.sname = none := hds _ h
        simp [this] at he
    · intro s r hq
      simp only [syncAll_sessRoom, addDefaults_sessRoom, start_sessRoom] at hq
      obtain ⟨ρ, hr, he⟩ := h2 s r hq
      exact ⟨ρ, by simpa using addDefaults_keep ds _ (by simpa using hr), he⟩
  | _ =>
    have fu := fun s hs => fresh_unclaimed (w := w) ⟨h1, h2⟩ (s := s) hs
    constructor <;> intros <;> simp [upd] at * <;> grind

theorem step_inv {w w'} (hi : RoomInv w) (st : Step w w') : RoomInv w' :=
  ⟨step_events hi.1 st, step_assoc hi.2 st⟩

/-- Reachable states. -/
inductive Reachable : World → Prop
  | init : Reachable World.init
  | step {w w'} : Reachable w → Step w w' → Reachable w'

theorem reachable_inv {w} (h : Reachable w) : RoomInv w := by
  induction h with
  | init => exact inv_init
  | step _ st ih => exact step_inv ih st

/-! ## Consequences -/

/-- A session is associated with at most one room. -/
theorem session_one_room {w} (h : Reachable w) {r₁ r₂ ρ₁ ρ₂ s}
    (h₁ : w.rooms r₁ = some ρ₁) (e₁ : ρ₁.sname = some s)
    (h₂ : w.rooms r₂ = some ρ₂) (e₂ : ρ₂.sname = some s) : r₁ = r₂ := by
  have ⟨_, ha, _⟩ := reachable_inv h
  have := (ha r₁ ρ₁ s h₁ e₁).1; have := (ha r₂ ρ₂ s h₂ e₂).1; simp_all

/-- Waiters in room `r` are released in every reachable state iff `r` is ready. -/
theorem released_iff_ready {w} (h : Reachable w) (r : RoomName) :
    w.event r = true ↔ ∃ ρ, w.rooms r = some ρ ∧ ρ.ready w.configs = true := by
  rw [(reachable_inv h).1 r]; cases w.rooms r <;> simp

/-- A successful `set_room_open(r, True)` always releases waiters in `r`. -/
theorem open_releases {w : World} {r : RoomName} {ρ : Room}
    (hg : ρ.sname.isSome ∨ ρ.config.any w.configs) :
    ((w.setRoom r (some { ρ with isOpen := true })).sync r).event r = true := by
  cases hg <;> simp_all [World.sync, Room.ready]

/-- Deleted rooms never hold waiters. -/
theorem deleted_not_released {w r} (h : Reachable w) (hn : w.rooms r = none) :
    w.event r = false := by
  rw [(reachable_inv h).1 r, hn]; rfl

end Rooms
