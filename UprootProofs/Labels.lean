-- SPDX-License-Identifier: 0BSD

import UprootProofs.Rooms

/-!
# Room labels: each label maps to at most one player

Proves the claim in the `rooms.py` docstring that "each label maps to at most
one player" (for non-empty labels; unlabelled players are interchangeable), for
the player list of any session.

Sources modelled:
* `src/uproot/core.py`    — `initialize_player` (`label = ""`, `started = False`,
  then `data`), `find_free_slot`
* `src/uproot/server3.py` — `roommain`: resume, claim a free slot, or add a player
* `src/uproot/server1.py` — a player is started on their first page or through
  the session-wide link (`started = True`; the label is untouched)
* `src/uproot/server2.py`, `server4.py` — new sessions: unstarted players labelled
  with the assignees, which are deduplicated (`set(...)`, `ensure_assignees`)

Players are only ever appended to `session._uproot_players`, and the above are
the only writers of `label` and `started` in uproot. Out of scope: an admin can
overwrite any player field, `label` included, with `insert_fields`, and app code
(trusted) may write `player.label`.
-/

namespace Rooms

/-- The fields of a player that admission reads or writes. -/
structure Player where
  label   : Label
  started : Bool

/-- `core.find_free_slot`, transcribed: scan `session._uproot_players` in order;
an unstarted player carrying `label` (if non-empty) is returned at once, else the
first unstarted unlabelled player seen (`fallback`). Results are list positions. -/
def findFreeSlotLoop (label : Label) : List Player → Nat → Option Nat → Option Nat
  | [], _, fallback => fallback
  | p :: ps, i, fallback =>
    if !p.started then
      if label != "" && p.label == label then some i
      else findFreeSlotLoop label ps (i + 1)
        (if fallback.isNone && p.label == "" then some i else fallback)
    else findFreeSlotLoop label ps (i + 1) fallback

def findFreeSlot (ps : List Player) (label : Label) : Option Nat :=
  findFreeSlotLoop label ps 0 none

/-- Unstarted and carrying `label`. -/
def Player.isFreeWith (label : Label) (p : Player) : Bool := !p.started && p.label == label

/-- The loop is a first-match search with a fallback. -/
theorem findFreeSlotLoop_spec (label : Label) (ps : List Player) (i : Nat) (f : Option Nat) :
    findFreeSlotLoop label ps i f =
      ((if label != "" then (ps.findIdx? (Player.isFreeWith label)).map (· + i) else none).or
        (f.or ((ps.findIdx? (Player.isFreeWith "")).map (· + i)))) := by
  induction ps generalizing i f with
  | nil => cases f <;> simp [findFreeSlotLoop]
  | cons p ps ih =>
    have shift : ∀ o : Option Nat, (o.map (· + 1)).map (· + i) = o.map (· + (i + 1)) := by
      intro o; cases o <;> simp; omega
    rcases p with ⟨pl, ps0⟩
    cases ps0
    · -- unstarted
      by_cases hl : label = ""
      · subst hl
        by_cases hp : pl = ""
        · subst hp; cases f <;> simp [findFreeSlotLoop, List.findIdx?_cons, Player.isFreeWith, ih]
        · simp [findFreeSlotLoop, List.findIdx?_cons, Player.isFreeWith, hp, ih, shift]
      · by_cases hp : pl = label
        · subst hp; simp [findFreeSlotLoop, List.findIdx?_cons, Player.isFreeWith, hl]
        · by_cases hb : pl = ""
          · subst hb
            cases f <;> simp [findFreeSlotLoop, List.findIdx?_cons, Player.isFreeWith, hl, Ne.symm hl, ih, shift]
          · simp [findFreeSlotLoop, List.findIdx?_cons, Player.isFreeWith, hl, hp, hb, ih, shift]
    · simp [findFreeSlotLoop, List.findIdx?_cons, Player.isFreeWith, ih, shift]

/-- `find_free_slot` prefers an unstarted player with the requested label, else
the first unstarted unlabelled one. -/
theorem findFreeSlot_spec (ps : List Player) (label : Label) :
    findFreeSlot ps label =
      (if label != "" then ps.findIdx? (Player.isFreeWith label) else none).or
        (ps.findIdx? (Player.isFreeWith "")) := by
  simp [findFreeSlot, findFreeSlotLoop_spec]

theorem findFreeSlot_some {ps : List Player} {label : Label} {i : Nat}
    (h : findFreeSlot ps label = some i) :
    ∃ hi : i < ps.length, ps[i].started = false ∧
      (ps[i].label = label ∨
        (ps[i].label = "" ∧ (label ≠ "" → ∀ p ∈ ps, p.isFreeWith label = false))) := by
  rw [findFreeSlot_spec] at h
  by_cases hl : label = ""
  · subst hl
    rw [ite_eq_right (by simp), Option.none_or] at h
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    simp [Player.isFreeWith] at hp
    exact ⟨hi, hp.1, .inl hp.2⟩
  · rw [ite_eq_left (by simpa using hl)] at h
    cases hx : ps.findIdx? (Player.isFreeWith label) with
    | some j =>
      rw [hx, Option.some_or] at h
      cases h
      obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hx
      simp [Player.isFreeWith] at hp
      exact ⟨hi, hp.1, .inl hp.2⟩
    | none =>
      rw [hx, Option.none_or] at h
      obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
      simp [Player.isFreeWith] at hp
      exact ⟨hi, hp.1, .inr ⟨hp.2, fun _ => List.findIdx?_eq_none_iff.mp hx⟩⟩

theorem findFreeSlot_none {ps : List Player} {label : Label}
    (h : findFreeSlot ps label = none) (hl : label ≠ "") :
    ∀ p ∈ ps, p.isFreeWith label = false := by
  rw [findFreeSlot_spec, ite_eq_left (by simpa using hl)] at h
  cases hx : ps.findIdx? (Player.isFreeWith label) with
  | some j => rw [hx, Option.some_or] at h; cases h
  | none => exact List.findIdx?_eq_none_iff.mp hx

/-- `server3.roommain` on the players of the room's session (after a `joinCreates`
step, that is the new session's empty list). The redirect to an existing player
(`resume`) is decided by the scan for a started player carrying `label`; a
claimed slot gets `started = True` and the label; a new player is appended with
both. This refines `admit`: its `n`, `labelStarted` and `freeSlot` are now
computed from the list. -/
def roommain (loaded : Config → Bool) (ρ : Room) (label : Label) (ps : List Player) :
    Outcome × List Player :=
  match admit loaded ρ label ps.length (ps.any fun p => p.label == label && p.started)
      (findFreeSlot ps label).isSome, findFreeSlot ps label with
  | .reuseSlot, some i => (.reuseSlot, ps.set i ⟨label, true⟩)
  | .newPlayer, _ => (.newPlayer, ps ++ [⟨label, true⟩])
  | o, _ => (o, ps)

/-! ## Label uniqueness -/

theorem admit_reuseSlot {loaded : Config → Bool} {ρ : Room} {label : Label} {n : Nat}
    {ls fs : Bool} (h : admit loaded ρ label n ls fs = .reuseSlot) : (label != "" && ls) = false ∧ fs = true := by
  unfold admit at h
  repeat (split at h <;> try simp_all)

theorem admit_newPlayer {loaded : Config → Bool} {ρ : Room} {label : Label} {n : Nat}
    {ls fs : Bool} (h : admit loaded ρ label n ls fs = .newPlayer) : (label != "" && ls) = false ∧ fs = false := by
  unfold admit at h
  repeat (split at h <;> try simp_all)

/-- Each non-empty label is carried by at most one player. -/
def LabelsUnique (ps : List Player) : Prop :=
  ∀ L, L ≠ "" → ps.countP (fun p => p.label == L) ≤ 1

/-- No player carries `L` if none is started with it and none is free with it. -/
theorem countP_label_zero {ps : List Player} {L : Label}
    (hs : (ps.any fun p => p.label == L && p.started) = false)
    (hf : ∀ p ∈ ps, p.isFreeWith L = false) :
    ps.countP (fun p => p.label == L) = 0 := by
  rw [List.countP_eq_zero]
  intro p hp hl
  have h1 := hf p hp
  have h2 := List.any_eq_false.mp hs p hp
  cases hst : p.started <;> simp_all [Player.isFreeWith]

/-- Admission preserves label uniqueness. -/
theorem roommain_unique (loaded : Config → Bool) (ρ : Room) (label : Label) (ps : List Player)
    (h : LabelsUnique ps) : LabelsUnique (roommain loaded ρ label ps).2 := by
  unfold roommain
  split
  · next i ho hs =>
    intro L hL
    have hle := h L hL
    obtain ⟨hres, -⟩ := admit_reuseSlot ho
    obtain ⟨hi, -, hcase⟩ := findFreeSlot_some hs
    rw [List.countP_set hi]
    by_cases hLl : label = L
    · subst hLl
      have hls : (ps.any fun p => p.label == label && p.started) = false := by
        simpa [hL] using hres
      rcases hcase with hc | ⟨hc, hfree⟩
      · simp [hc]; omega
      · have h0 := countP_label_zero hls (hfree hL)
        simp [hc, Ne.symm hL, h0]
    · simp [hLl]; omega
  · next ho =>
    intro L hL
    obtain ⟨hres, hfs⟩ := admit_newPlayer ho
    rw [List.countP_append]
    by_cases hLl : label = L
    · subst hLl
      have hls : (ps.any fun p => p.label == label && p.started) = false := by
        simpa [hL] using hres
      have hnone : findFreeSlot ps label = none := by simpa using hfs
      simp [countP_label_zero hls (findFreeSlot_none hnone hL)]
    · simp [hLl]; exact h L hL
  · exact h

/-- Starting a player (`server1`) does not change labels. -/
theorem start_unique (ps : List Player) (i : Nat) (hi : i < ps.length) (h : LabelsUnique ps) :
    LabelsUnique (ps.set i { ps[i] with started := true }) := by
  intro L hL
  have := h L hL
  rw [List.countP_set hi]
  by_cases hp : ps[i].label = L <;> simp [hp] <;> omega

/-- New sessions: assignee labels are distinct, other players are unlabelled. -/
theorem create_unique (labels : List Label) (h : ∀ L, L ≠ "" → labels.count L ≤ 1) :
    LabelsUnique (labels.map fun L => (⟨L, false⟩ : Player)) := by
  intro L hL
  simpa [List.countP_map, Function.comp_def, List.count_eq_countP] using h L hL

/-- How a session's player list changes after the session is created. -/
inductive PStep : List Player → List Player → Prop
  /-- `server3.roommain` -/
  | join (loaded ρ label ps) : PStep ps (roommain loaded ρ label ps).2
  /-- `server1`: first page (`Initialize.html`) or the session-wide link -/
  | start (ps i) (h : i < ps.length) : PStep ps (ps.set i { ps[i] with started := true })

/-- Player lists of reachable sessions. `core.create_session` starts with none
(e.g. in `joinCreates`); the "new session (in room)" forms add unstarted players,
labelled with the deduplicated assignees or unlabelled. The room's settings and the
loaded configs may change arbitrarily between joins, hence `join` takes any. -/
inductive PReachable : List Player → Prop
  | create (labels : List Label) : (∀ L, L ≠ "" → labels.count L ≤ 1) →
      PReachable (labels.map fun L => ⟨L, false⟩)
  | step {ps ps'} : PReachable ps → PStep ps ps' → PReachable ps'

/-- In every reachable session, each non-empty label is carried by at most one player. -/
theorem labels_unique {ps : List Player} (h : PReachable ps) : LabelsUnique ps := by
  induction h with
  | create labels hl => exact create_unique labels hl
  | step _ st ih =>
    cases st with
    | join loaded ρ label => exact roommain_unique loaded ρ label _ ih
    | start _ i hi => exact start_unique _ i hi ih

/-- Two positions whose elements both satisfy `p` coincide if at most one element does. -/
theorem countP_le_one_inj {α} {p : α → Bool} {l : List α} {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (hc : l.countP p ≤ 1)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.countP_cons] at hc
    cases i <;> cases j
    · rfl
    · next j =>
      have hj' : j < l.length := by simpa using hj
      have pos : 0 < l.countP p :=
        List.countP_pos_iff.mpr ⟨l[j], List.getElem_mem hj', by simpa using hpj⟩
      have ha : (if p a = true then 1 else 0) = 1 := by simp [show p a = true by simpa using hpi]
      omega
    · next i =>
      have hi' : i < l.length := by simpa using hi
      have pos : 0 < l.countP p :=
        List.countP_pos_iff.mpr ⟨l[i], List.getElem_mem hi', by simpa using hpi⟩
      have ha : (if p a = true then 1 else 0) = 1 := by simp [show p a = true by simpa using hpj]
      omega
    · next i j =>
      have hi' : i < l.length := by simpa using hi
      have hj' : j < l.length := by simpa using hj
      have := ih hi' hj' (by split at hc <;> omega) (by simpa using hpi) (by simpa using hpj)
      omega

/-- The `rooms.py` claim: two players carrying the same non-empty label are the
same player. -/
theorem label_one_player {ps : List Player} (h : PReachable ps) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length)
    (hl : ps[i].label = ps[j].label) (hne : ps[i].label ≠ "") : i = j :=
  countP_le_one_inj (p := fun q => q.label == ps[i].label) hi hj (labels_unique h _ hne)
    (by simp) (by simp [hl])

end Rooms
