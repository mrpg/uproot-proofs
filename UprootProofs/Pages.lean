-- SPDX-License-Identifier: 0BSD

/-!
# Pages: what a participant's request does

A specification of how uproot answers a participant's requests to their page,
`GET` and `POST /p/{sname}/{uname}/` (`server1.show_page`): page hooks,
navigation, form submissions, timeouts and Back. uproot implements it, and
uproot's opt-in `tests/test_pages_model.py` checks that against the cases that
`lake exe page-cases` computes from this file (see `docs/pages.md`).

## Principles

A player is at a *position* (`show_page`): `-1` (`Initialize.html`), a page of
the page order (`0, …, n - 1`) or the end (`n`, `End.html`). A request ends by
displaying the page at the player's position.

1. **Entering.** A position is entered whenever navigation reaches it:
   `early`, then `before_always_once`. Then `show()` decides. A page that is not
   shown is *skipped* (`after_always_once`, then the next position is entered);
   a shown page is *displayed* (`before_once`, then the page). `End.html` is
   always shown.
2. **Once.** `before_always_once`, `before_once`, `after_once` and
   `after_always_once` run the first time their occasion arises at a position,
   always, but only once. `early` runs whenever navigation reaches a position,
   but loading the page runs it only if it has never run there.
3. **Forms.** Only the form of the page at the player's position, with a valid
   token, can be submitted. Any other request is handled as loading the page.
   A submission is accepted if the fields validate and neither `validate` nor
   `handle_stealth_fields` rejects it. Then, and only then, its ordinary fields
   are saved, all at once.
4. **Leaving.** An accepted submission leaves the page if `may_proceed` allows
   it: `after_once`, `after_always_once`, then the next position is entered.
   Otherwise the page is displayed again, with the submitted values, and with
   errors if the submission was rejected. Errors are shown on no other page.
5. **Timeouts.** After a page's deadline, every request is a timed-out
   submission: `timeout_reached` runs, the form is saved if it is accepted, and
   the page is left, whatever `may_proceed` says. Up to `TIMEOUT_TOLERANCE`
   seconds before the deadline, the same holds if `may_proceed` allows it.
6. **Back.** Back leads to the nearest earlier page that is shown, without
   crossing the start of an app, a round or an iteration of `Repeat`; if there
   is none, or `allow_back` forbids it, the player stays. The page that the
   player goes back to is entered and displayed (1, 2). Back saves nothing and
   asks no `may_proceed`. After the deadline, Back is a timed-out submission (5).
7. **Moves.** A hook may move the player forward (`move_to_page`,
   `move_to_end`). The hooks of the current step finish (entering, `show()`,
   skipping, displaying, leaving, or handling the request), then the player
   enters the target.

Hooks are app code: they may read and write any app data (`σ`), and their
results may depend on it. A request is one handler run, atomic for the
player: `show_page_wrapper` holds the player's page lock. Hooks that raise are
not modelled. Nor are changes of the page order (`Repeat`, `Between`), which
leave the positions up to the current one as they are.
-/

namespace Pages

inductive Hook
  | early | beforeAlwaysOnce | show | beforeOnce | afterOnce | afterAlwaysOnce
  | timeoutReached | mayProceed | allowBack | validate | handleStealthFields | beforeFormSave
  deriving DecidableEq, Repr

/-- The hooks that run at most once per position. -/
def Hook.once : Hook → Bool
  | .beforeAlwaysOnce | .beforeOnce | .afterOnce | .afterAlwaysOnce => true
  | _ => false

/-- What a hook that the page does not define amounts to (`default_return`). -/
def Hook.default : Hook → Bool
  | .allowBack => false
  | _ => true

/-- How a displayed page shows its form: fresh, with the submitted values (the
submission was accepted, but `may_proceed` refused), or with the submitted
values and errors (the submission was rejected). -/
inductive Shown
  | fresh | kept | errors
  deriving DecidableEq, Repr

/-- What happens, in order. `call p h b`: hook `h` of the page at `p` ran and
returned `b`. -/
inductive Ev
  | call (p : Int) (h : Hook) (result : Bool)
  | init
  | save (p : Int) (fields : List String)
  | display (p : Int) (shown : Shown)
  | error
  deriving DecidableEq, Repr

/-- A project, as far as one player's pages are concerned. `n` is the length of
the page order. `σ` is the data that app code reads and writes, `F` submitted
form data. -/
structure App (σ F : Type) where
  n : Nat
  /-- The page at `p` defines hook `h` (`hasattr`). -/
  defines : Int → Hook → Bool
  /-- Running hook `h` of the page at `p`: its result, the data afterwards, and
  the position it moves the player to, if any. Only `validate`,
  `handle_stealth_fields` and `before_form_save` receive the form data. -/
  run : Int → Hook → F → σ → Bool × σ × Option Int
  /-- The page at `p` starts an app, a round or an iteration of `Repeat`. -/
  barrier : Int → Bool
  /-- The page at `p` has fields. -/
  hasForm : Int → Bool
  /-- The submitted data pass the validation of the fields. -/
  valid : Int → F → σ → Bool
  /-- Some fields are stealth fields or uploads (`handle_stealth_fields` runs). -/
  manual : Int → F → σ → Bool
  /-- The ordinary fields, i.e., all others. -/
  ordinary : Int → F → σ → List String
  /-- Saving the ordinary fields. -/
  save : Int → F → σ → σ
  /-- The page's timeout in seconds, if any. -/
  timeout : Int → σ → Option Nat
  /-- `new_session` and `new_player`, run when a player starts. -/
  start : σ → σ
  /-- `TIMEOUT_TOLERANCE`, in seconds. -/
  tolerance : Nat

/-- A player. -/
structure St (σ : Type) where
  /-- `show_page` -/
  pos : Int
  /-- `started` -/
  started : Bool
  /-- `_uproot_what_ran`: the hooks that ran at each position -/
  ran : List (Int × Hook)
  /-- `_uproot_timeouts_until`: the deadline at each position -/
  deadline : Int → Option Nat
  /-- What has happened, in order. -/
  log : List Ev
  /-- App data. -/
  app : σ
  /-- Ghost state, never read by the handler: the furthest position that a
  hook has moved the player to (`-1` if none). It states principle 7. -/
  moved : Int

def St.init {σ} (a : σ) : St σ := ⟨-1, false, [], fun _ => none, [], a, -1⟩

/-- A request. `post src back token form`: `_uproot_from` names position `src`
(`none` if it is missing or malformed), prefixed by `back-` for Back; `token`:
`_uproot_csrf` is valid. -/
inductive Req (F : Type)
  | get
  | post (src : Option Int) (back : Bool) (token : Bool) (form : F)

/-- The submission of the form of position `k` that the request carries, if
any: `(back, form)`. -/
def Req.submission {F} : Req F → Int → Option (Bool × F)
  | .post (some p) back true form, k => if p = k then some (back, form) else none
  | _, _ => none

section Handler

variable {σ F : Type} [Inhabited F] (A : App σ F)

/-- Where a move to `t` takes a player at `cur`: forward only, and only for
players who have started (`transition_to_page`). -/
def App.moveTo (cur : Int) : Option Int → Int
  | some t => if 0 ≤ cur ∧ cur < t ∧ t ≤ A.n then t else cur
  | none => cur

/-- Run hook `h` of the page at `p`, if it defines it (`optional_call`). -/
def App.call (h : Hook) (p : Int) (s : St σ) (f : F := default) : Bool × St σ :=
  if A.defines p h then
    let r := A.run p h f s.app
    let t := A.moveTo s.pos r.2.2
    (r.1, { s with app := r.2.1, pos := t, log := s.log ++ [.call p h r.1],
                   moved := if s.pos < t ∧ s.moved < t then t else s.moved })
  else (h.default, s)

/-- Run hook `h` of the page at `p` if it has not run at `p` yet, or `again`
(`optional_call_once`). -/
def App.once (h : Hook) (p : Int) (again : Bool) (s : St σ) : St σ :=
  if A.defines p h ∧ (again ∨ (p, h) ∉ s.ran) then
    (A.call h p { s with ran := if (p, h) ∈ s.ran then s.ran else (p, h) :: s.ran }).2
  else s

/-- Display the page at `p`. -/
def St.display {σ} (s : St σ) (p : Int) (d : Shown) : St σ :=
  { s with log := s.log ++ [.display p d] }

/-- Whether the page at `c` is shown: `show()`, unless the page is to be
displayed anyway (`d = some _`). -/
def App.ask (c : Int) (d : Option Shown) (s : St σ) : Bool × St σ :=
  match d with
  | some _ => (true, s)
  | none => A.call .show c s

/-- Enter position `c` and go on from there (1, 7). `again`: run `early` even if
it ran at `c` before (navigation), as opposed to loading the page. `d = some _`:
display `c` without asking `show()` (staying, or Back, which asked it). -/
def App.visit (c : Int) (again : Bool) (d : Option Shown) (s : St σ) : St σ :=
  if hc : A.n ≤ c then
    let s := A.once .early A.n again { s with pos := A.n }
    let s := A.once .beforeAlwaysOnce A.n false s
    (A.once .beforeOnce A.n false s).display A.n (d.getD .fresh)
  else
    let s := A.once .early c again { s with pos := c }
    let s := A.once .beforeAlwaysOnce c false s
    if c < s.pos then visit s.pos true none s else
    let r := A.ask c d s
    let s := r.2
    if c < s.pos then visit s.pos true none s else
    if r.1 then
      let s := A.once .beforeOnce c false s
      if c < s.pos then visit s.pos true none s else s.display c (d.getD .fresh)
    else
      let s := A.once .afterAlwaysOnce c false s
      if c < s.pos then visit s.pos true none s else visit (c + 1) true none s
termination_by (A.n - c).toNat
decreasing_by all_goals (simp (config := { zetaDelta := true }) only at *; omega)

/-- Leave position `k` forward (4). -/
def App.leave (k : Int) (s : St σ) : St σ :=
  let s := A.once .afterOnce k false s
  let s := A.once .afterAlwaysOnce k false s
  A.visit (if k < s.pos then s.pos else k + 1) true none s

/-- Leave position `k` forward, unless it is the end. -/
def App.proceed (k : Int) (s : St σ) : St σ :=
  if k < A.n then A.leave k s else A.visit k false (some .fresh) s

/-- Load the page at position `k` (as `GET` does), unless a hook moved the player. -/
def App.load (k : Int) (s : St σ) : St σ :=
  if k < s.pos then A.visit s.pos true none s else A.visit k false none s

/-- Stay at position `k` and display it with `d`, unless a hook moved the player. -/
def App.stay (k : Int) (d : Shown) (s : St σ) : St σ :=
  if k < s.pos then A.visit s.pos true none s else A.visit k false (some d) s

/-- `handle_stealth_fields`, if some fields are stealth fields or uploads. -/
def App.stealth (k : Int) (f : F) (s : St σ) : Bool × St σ :=
  if A.manual k f s.app then A.call .handleStealthFields k s f else (true, s)

/-- Save the ordinary fields of the submitted form `f` of position `k`. -/
def App.saveForm (k : Int) (f : F) (s : St σ) : St σ :=
  { s with app := A.save k f s.app, log := s.log ++ [.save k (A.ordinary k f s.app)] }

/-- Check the submitted form `f` of position `k`, and save it if it is accepted (3). -/
def App.accept (k : Int) (f : F) (s : St σ) : Bool × St σ :=
  if A.hasForm k then
    if A.valid k f s.app then
      let v := A.call .validate k s f
      if v.1 then
        let h := A.stealth k f v.2
        if h.1 then (true, A.saveForm k f (A.call .beforeFormSave k h.2 f).2) else (false, h.2)
      else (false, v.2)
    else (false, s)
  else (true, s)

/-- Whether deadline `t` of position `k` counts as reached at time `now`: it
has passed, or it is less than `TIMEOUT_TOLERANCE` seconds away and
`may_proceed` allows it (5). -/
def App.fires (now t : Nat) (k : Int) (s : St σ) : Bool × St σ :=
  if t ≤ now then (true, s)
  else if now + A.tolerance < t then (false, s)
  else A.call .mayProceed k s

/-- Whether the deadline of position `k`, if any, counts as reached; if so,
`timeout_reached` has run. -/
def App.timedOut (now : Nat) (k : Int) (s : St σ) : Bool × St σ :=
  match s.deadline k with
  | none => (false, s)
  | some t =>
    let r := A.fires now t k s
    if r.1 then (true, (A.call .timeoutReached k r.2).2) else (false, r.2)

/-- Back from `k`, looking at position `j` (6). -/
def App.back (k j : Int) (s : St σ) : St σ :=
  if hj : j < 0 then A.stay k .fresh { s with pos := k } else
  if A.barrier j then A.stay k .fresh { s with pos := k } else
  let r := A.call .show j { s with pos := j }
  if j < r.2.pos then A.visit r.2.pos true none r.2
  else if r.1 then A.visit j true (some .fresh) r.2
  else back k (j - 1) r.2
termination_by (j + 1).toNat
decreasing_by omega

/-- A Back request on position `k`. -/
def App.goBack (k : Int) (s : St σ) : St σ :=
  let r := A.call .allowBack k s
  if k < r.2.pos then A.visit r.2.pos true none r.2
  else if r.1 then A.back k (k - 1) r.2
  else A.stay k .fresh r.2

/-- A request at time `now`, before the deadline is set. -/
def App.respond (now : Nat) (r : Req F) (s : St σ) : St σ :=
  let k := s.pos
  if k = -1 then
    match r.submission k with
    | some (false, _) =>
      A.visit 0 true none { s with started := true, app := A.start s.app, log := s.log ++ [.init] }
    | _ => s.display (-1) .fresh
  else if k < -1 ∨ A.n < k then { s with log := s.log ++ [.error] }
  else
    let t := A.timedOut now k s
    let s := t.2
    match r.submission k with
    | none => if t.1 then A.proceed k s else A.load k s
    | some (back, f) =>
      if t.1 then A.proceed k (A.accept k f s).2
      else if back then A.goBack k s
      else
        let a := A.accept k f s
        if a.1 then
          let g := A.call .mayProceed k a.2
          if g.1 then A.proceed k g.2 else A.stay k .kept g.2
        else A.stay k .errors a.2

/-- Displaying a page with a timeout sets its deadline, unless it has one (`set_timeout`). -/
def App.arm (now : Nat) (s : St σ) : St σ :=
  if 0 ≤ s.pos ∧ s.pos ≤ A.n ∧ s.deadline s.pos = none then
    match A.timeout s.pos s.app with
    | some d => { s with deadline := fun p => if p = s.pos then some (now + d) else s.deadline p }
    | none => s
  else s

/-- One request at time `now`. -/
def App.step (now : Nat) (r : Req F) (s : St σ) : St σ := A.arm now (A.respond now r s)

end Handler

/-! ## Facts about the parts of the handler

The lemmas that the theorems about requests (`## Requests`) and reachable
states (`## Reachable states`) rest on. -/

section Facts

variable {σ F : Type} [Inhabited F] (A : App σ F)

omit [Inhabited F] in
theorem moveTo_cases (cur : Int) (m : Option Int) :
    A.moveTo cur m = cur ∨ (0 ≤ cur ∧ cur < A.moveTo cur m ∧ A.moveTo cur m ≤ A.n) := by
  unfold App.moveTo; split
  · split <;> simp_all
  · simp

@[simp] theorem call_ran (h p s f) : (A.call h p s f).2.ran = s.ran := by
  unfold App.call; split <;> rfl
@[simp] theorem call_started (h p s f) : (A.call h p s f).2.started = s.started := by
  unfold App.call; split <;> rfl
@[simp] theorem call_deadline (h p s f) : (A.call h p s f).2.deadline = s.deadline := by
  unfold App.call; split <;> rfl

theorem call_pos (h p s f) : (A.call h p s f).2.pos = s.pos ∨
    (0 ≤ s.pos ∧ s.pos < (A.call h p s f).2.pos ∧ (A.call h p s f).2.pos ≤ A.n) := by
  unfold App.call; split
  · exact moveTo_cases A _ _
  · simp

theorem once_pos (h p again s) : (A.once h p again s).pos = s.pos ∨
    (0 ≤ s.pos ∧ s.pos < (A.once h p again s).pos ∧ (A.once h p again s).pos ≤ A.n) := by
  unfold App.once; split
  · exact call_pos A _ _ _ _
  · simp

theorem ask_pos (c d s) : (A.ask c d s).2.pos = s.pos ∨
    (0 ≤ s.pos ∧ s.pos < (A.ask c d s).2.pos ∧ (A.ask c d s).2.pos ≤ A.n) := by
  unfold App.ask; split
  · simp
  · exact call_pos A _ _ _ _

@[simp] theorem ask_ran (c d s) : (A.ask c d s).2.ran = s.ran := by
  unfold App.ask; split <;> simp
@[simp] theorem display_ran (s : St σ) (p d) : (s.display p d).ran = s.ran := rfl
@[simp] theorem display_pos (s : St σ) (p d) : (s.display p d).pos = s.pos := rfl

/-- Navigation from `c` ends at a position from `c` to `n`. -/
theorem visit_pos (c : Int) (again d s) (h0 : 0 ≤ c) (hn : c ≤ A.n) :
    c ≤ (A.visit c again d s).pos ∧ (A.visit c again d s).pos ≤ A.n := by
  fun_induction A.visit c again d s
  all_goals (try simp only [St.display])
  all_goals grind [once_pos, ask_pos]

/-! ### Logs and markers -/

/-- Hook `h` of the page at `p` ran. -/
def Ev.isCall (p : Int) (h : Hook) : Ev → Bool
  | .call q g _ => decide (q = p) && decide (g = h)
  | _ => false

/-- How often hook `h` of the page at `p` ran. -/
def runs (p : Int) (h : Hook) (l : List Ev) : Nat := l.countP (Ev.isCall p h)

section CallDef
variable {h : Hook} {p : Int} {s : St σ} {f : F} (hd : A.defines p h = true)
include hd
theorem call_fst : (A.call h p s f).1 = (A.run p h f s.app).1 := by simp [App.call, hd]
theorem call_pos_def : (A.call h p s f).2.pos = A.moveTo s.pos (A.run p h f s.app).2.2 := by
  simp [App.call, hd]
theorem call_log_def : (A.call h p s f).2.log = s.log ++ [.call p h (A.call h p s f).1] := by
  simp [App.call, hd]
end CallDef

theorem call_undef {h p s f} (hd : A.defines p h = false) : A.call h p s f = (h.default, s) := by
  simp [App.call, hd]

theorem call_log (h p s f) : (A.call h p s f).2.log = s.log ∨
    (A.call h p s f).2.log = s.log ++ [.call p h (A.call h p s f).1] := by
  cases hd : A.defines p h
  · simp [call_undef A hd]
  · exact .inr (call_log_def A hd)

theorem once_log (h p again s) : (A.once h p again s).log = s.log ∨
    ∃ b, (A.once h p again s).log = s.log ++ [.call p h b] := by
  unfold App.once; split
  · next hc => exact .inr ⟨_, call_log_def A hc.1⟩
  · exact .inl rfl

theorem once_ran (h p again s) (x) (hx : x ∈ s.ran) : x ∈ (A.once h p again s).ran := by
  unfold App.once; split
  · simp only [call_ran]; split <;> simp_all
  · exact hx

theorem once_mem (h p again s) (hd : A.defines p h) : (p, h) ∈ (A.once h p again s).ran := by
  unfold App.once; split
  · simp only [call_ran]; split <;> simp_all
  · next hn => simp_all

@[simp] theorem runs_nil (p h) : runs p h [] = 0 := rfl
theorem runs_append (p h l₁ l₂) : runs p h (l₁ ++ l₂) = runs p h l₁ + runs p h l₂ :=
  List.countP_append
@[simp] theorem runs_call (p h q g b) :
    runs p h [.call q g b] = if q = p ∧ g = h then 1 else 0 := by
  simp [runs, Ev.isCall]

/-- Each hook that runs at most once per position ran at most once, and only
if it is marked as having run. -/
def OnceOK (s : St σ) : Prop :=
  ∀ p h, h.once = true → runs p h s.log ≤ if (p, h) ∈ s.ran then 1 else 0

theorem call_ok (h p s f) (hh : h.once = false) (ok : OnceOK s) : OnceOK (A.call h p s f).2 := by
  intro q g hg
  have hle := ok q g hg
  have : ¬(p = q ∧ h = g) := by rintro ⟨-, rfl⟩; simp_all
  rcases call_log A h p s f with e | e <;> simp only [e, call_ran, runs_append, runs_call]
  · exact hle
  · simpa [this] using hle

theorem once_ok (h p again s) (ha : h.once = true → again = false) (ok : OnceOK s) :
    OnceOK (A.once h p again s) := by
  intro q g hg
  have hle := ok q g hg
  unfold App.once; split
  · next hc =>
    rw [call_log_def A hc.1, call_ran, runs_append, runs_call]
    by_cases hq : p = q ∧ h = g
    · obtain ⟨rfl, rfl⟩ := hq
      have : (p, h) ∉ s.ran := by cases hc.2 <;> simp_all
      simp_all
    · simp only [hq, ite_false, Nat.add_zero]
      refine Nat.le_trans hle ?_
      split <;> split <;> simp_all
  · exact hle

/-! ### Navigation -/

/-- The log grew by events that satisfy `P`. -/
def Grows (P : Ev → Prop) (s s' : St σ) : Prop := ∃ u, s'.log = s.log ++ u ∧ ∀ e ∈ u, P e

theorem Grows.refl {P : Ev → Prop} {s s' : St σ} (h : s'.log = s.log) : Grows P s s' :=
  ⟨[], by simp [h], by simp⟩

theorem Grows.trans {P Q R : Ev → Prop} {s₁ s₂ s₃ : St σ} (h₁ : Grows P s₁ s₂) (h₂ : Grows Q s₂ s₃)
    (hP : ∀ e, P e → R e) (hQ : ∀ e, Q e → R e) : Grows R s₁ s₃ := by
  obtain ⟨u, hu, pu⟩ := h₁; obtain ⟨v, hv, pv⟩ := h₂
  refine ⟨u ++ v, by simp [hv, hu], ?_⟩
  intro e he; rcases List.mem_append.mp he with h | h
  · exact hP e (pu e h)
  · exact hQ e (pv e h)

theorem Grows.mono {P Q : Ev → Prop} {s s' : St σ} (h : Grows P s s') (hPQ : ∀ e, P e → Q e) :
    Grows Q s s' := let ⟨u, hu, pu⟩ := h; ⟨u, hu, fun e he => hPQ e (pu e he)⟩

theorem call_grows (h p s f) :
    Grows (fun e => e = .call p h (A.call h p s f).1) s (A.call h p s f).2 := by
  rcases call_log A h p s f with e | e
  · exact Grows.refl e
  · exact ⟨_, e, by simp⟩

theorem once_grows (h p again s) : Grows (fun e => ∃ b, e = .call p h b) s (A.once h p again s) := by
  rcases once_log A h p again s with e | ⟨b, e⟩
  · exact Grows.refl e
  · exact ⟨_, e, by simp⟩

theorem ask_grows (c d s) : Grows (fun e => e = .call c .show (A.ask c d s).1) s (A.ask c d s).2 := by
  unfold App.ask; split
  · exact Grows.refl rfl
  · exact call_grows A _ _ _ _

/-- The hooks that navigation runs. -/
def Hook.nav : Hook → Bool
  | .early | .beforeAlwaysOnce | .show | .beforeOnce | .afterAlwaysOnce => true
  | _ => false

/-- An event of navigation from `c` to `P`: a navigation hook of a page from `c`
to `P`, and if it is `show()` at `P`, it returned `true`. -/
def NavEv (c P : Int) (e : Ev) : Prop :=
  ∃ q g b, e = .call q g b ∧ g.nav = true ∧ c ≤ q ∧ q ≤ P ∧ (q = P → g = .show → b = true)

theorem NavEv.mono {c c' P e} (h : NavEv c' P e) (hc : c ≤ c') : NavEv c P e := by
  obtain ⟨q, g, b, rfl, hg, h1, h2, h3⟩ := h
  exact ⟨q, g, b, rfl, hg, by omega, h2, h3⟩

/-- Entering `c`: `early` and `before_always_once`. -/
theorem enter_grows (c : Int) (again : Bool) (s : St σ) :
    Grows (fun e => ∃ g b, e = .call c g b ∧ g.nav = true ∧ g ≠ .show) s
      (A.once .beforeAlwaysOnce c false (A.once .early c again { s with pos := c })) :=
  Grows.trans (Grows.trans (Grows.refl (s' := { s with pos := c }) rfl) (once_grows A _ _ _ _)
      (fun e h => h) (fun e h => h))
    (once_grows A _ _ _ _)
    (fun e ⟨b, h⟩ => ⟨_, b, h, rfl, by decide⟩) (fun e ⟨b, h⟩ => ⟨_, b, h, rfl, by decide⟩)

/-- The hooks that run before a page at `p` is displayed have run there. -/
def App.Entered (s : St σ) (p : Int) : Prop :=
  ∀ h, (h = .early ∨ h = .beforeAlwaysOnce ∨ h = .beforeOnce) → A.defines p h = true → (p, h) ∈ s.ran

/-- Events of the page at `c` (navigation hooks). -/
def AtEv (c : Int) (e : Ev) : Prop := ∃ g b, e = .call c g b ∧ g.nav = true

omit [Inhabited F] in
theorem nav_next (A : App σ F) {c t : Int} {d : Option Shown} {s X Y : St σ}
    (hg : Grows (AtEv c) s X) (hct : c < t) (htY : t ≤ Y.pos)
    (ih : ∃ u sh, Y.log = X.log ++ u ++ [.display Y.pos sh] ∧ (∀ e ∈ u, NavEv t Y.pos e) ∧
      (sh = .fresh ∨ (Y.pos = t ∧ (none : Option Shown) = some sh)) ∧ A.Entered Y Y.pos) :
    ∃ u sh, Y.log = s.log ++ u ++ [.display Y.pos sh] ∧ (∀ e ∈ u, NavEv c Y.pos e) ∧
      (sh = .fresh ∨ (Y.pos = c ∧ d = some sh)) ∧ A.Entered Y Y.pos := by
  obtain ⟨u0, e0, p0⟩ := hg
  obtain ⟨u, sh, e, pu, hsh, hent⟩ := ih
  have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
  refine ⟨u0 ++ u, sh, by simp [e, e0], ?_, .inl this, hent⟩
  intro x hx; rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨g, b, rfl, hgn⟩ := p0 x hx
    exact ⟨c, g, b, rfl, hgn, Int.le_refl _, by omega, by omega⟩
  · exact (pu x hx).mono (by omega)

/-- Navigation from `c`: its log, the form it displays, and that it enters the
page that it displays. -/
theorem visit_spec (c : Int) (again d s) (h0 : 0 ≤ c) (hn : c ≤ A.n) :
    ∃ u sh, (A.visit c again d s).log = s.log ++ u ++ [.display (A.visit c again d s).pos sh] ∧
      (∀ e ∈ u, NavEv c (A.visit c again d s).pos e) ∧
      (sh = .fresh ∨ ((A.visit c again d s).pos = c ∧ d = some sh)) ∧
      A.Entered (A.visit c again d s) (A.visit c again d s).pos := by
  fun_induction A.visit c again d s with
  | case1 c again d s hc s1 s2 =>
    have hcn : c = A.n := by omega
    subst hcn
    have g : Grows (fun e => ∃ g b, e = .call A.n g b ∧ g.nav = true ∧ g ≠ .show) s
        (A.once .beforeOnce A.n false s2) :=
      Grows.trans (enter_grows A A.n again s) (once_grows A .beforeOnce A.n false s2)
        (fun e h => h) (fun e ⟨b, h⟩ => ⟨_, b, h, rfl, by decide⟩)
    obtain ⟨u, hu, pu⟩ := g
    have p1 := once_pos A .early (↑A.n) again { s with pos := ↑A.n }
    have p2 := once_pos A .beforeAlwaysOnce (↑A.n) false s1
    have p3 := once_pos A .beforeOnce (↑A.n) false s2
    have hpos : (A.once .beforeOnce (↑A.n) false s2).pos = A.n := by
      simp (config := { zetaDelta := true }) only at p1 p2 p3 ⊢; omega
    refine ⟨u, d.getD .fresh, by simp [St.display, hu, hpos], ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨g, b, rfl, hg, hs⟩ := pu e he
      exact ⟨_, g, b, rfl, hg, Int.le_refl _, by simp [St.display, hpos], fun _ h => absurd h hs⟩
    · cases d <;> simp [St.display, hpos]
    · intro h hh hd
      simp only [display_pos, hpos, display_ran] at hd ⊢
      rcases hh with rfl | rfl | rfl
      · exact once_ran A _ _ _ _ _ (once_ran A _ _ _ _ _ (once_mem A _ _ _ _ hd))
      · exact once_ran A _ _ _ _ _ (once_mem A _ _ _ _ hd)
      · exact once_mem A _ _ _ _ hd
  | case2 c again d s hc s1 s2 h1 ih =>
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have hle : s2.pos ≤ A.n := by omega
    exact nav_next A ((enter_grows A c again s).mono fun e ⟨g, b, h, hg, _⟩ => ⟨g, b, h, hg⟩) h1
      (visit_pos A _ _ _ _ (by omega) hle).1 (ih (by omega) hle)
  | case3 c again d s hc s1 s2 h1 r s3 h2 ih =>
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    have hle : s3.pos ≤ A.n := by omega
    have g : Grows (AtEv c) s s3 := Grows.trans (enter_grows A c again s) (ask_grows A c d s2)
      (fun e ⟨g, b, h, hg, _⟩ => ⟨g, b, h, hg⟩) (fun e h => ⟨_, _, h, rfl⟩)
    exact nav_next A g h2 (visit_pos A _ _ _ _ (by omega) hle).1 (ih (by omega) hle)
  | case4 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 ih =>
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    have p4 : s4.pos = s3.pos ∨ (0 ≤ s3.pos ∧ s3.pos < s4.pos ∧ s4.pos ≤ A.n) := once_pos A _ _ _ _
    have hle : s4.pos ≤ A.n := by omega
    have g : Grows (AtEv c) s s4 :=
      Grows.trans (Grows.trans (enter_grows A c again s) (ask_grows A c d s2)
        (fun e ⟨g, b, h, hg, _⟩ => ⟨g, b, h, hg⟩) (fun e h => ⟨_, _, h, rfl⟩))
        (once_grows A _ _ _ _) (fun e h => h) (fun e ⟨b, h⟩ => ⟨_, b, h, rfl⟩)
    exact nav_next A g h3 (visit_pos A _ _ _ _ (by omega) hle).1 (ih (by omega) hle)
  | case5 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 =>
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    have p4 : s4.pos = s3.pos ∨ (0 ≤ s3.pos ∧ s3.pos < s4.pos ∧ s4.pos ≤ A.n) := once_pos A _ _ _ _
    have hpos : s4.pos = c := by omega
    have g : Grows (fun e => ∃ g b, e = .call c g b ∧ g.nav = true ∧ (g = .show → b = true)) s s4 :=
      Grows.trans (Grows.trans (enter_grows A c again s) (ask_grows A c d s2)
        (fun e ⟨g, b, h, hg, hs⟩ => ⟨g, b, h, hg, fun h => absurd h hs⟩)
        (fun e h => ⟨_, _, h, rfl, fun _ => by simpa using hr⟩))
        (once_grows A _ _ _ _) (fun e h => h) (fun e ⟨b, h⟩ => ⟨_, b, h, rfl, fun hs => absurd hs (by decide)⟩)
    obtain ⟨u, hu, pu⟩ := g
    refine ⟨u, d.getD .fresh, by simp [St.display, hu, hpos], ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨g, b, rfl, hg, hs⟩ := pu e he
      exact ⟨_, g, b, rfl, hg, Int.le_refl _, by simp [St.display, hpos], fun _ => hs⟩
    · cases d <;> simp [St.display, hpos]
    · intro h hh hd
      simp only [display_pos, hpos, display_ran] at hd ⊢
      have : ∀ x ∈ s2.ran, x ∈ s4.ran := fun x hx => once_ran A _ _ _ _ _ (by simpa [s3, r] using hx)
      rcases hh with rfl | rfl | rfl
      · exact this _ (once_ran A _ _ _ _ _ (once_mem A _ _ _ _ hd))
      · exact this _ (once_mem A _ _ _ _ hd)
      · exact once_mem A _ _ _ _ hd
  | case6 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    have p4 : s4.pos = s3.pos ∨ (0 ≤ s3.pos ∧ s3.pos < s4.pos ∧ s4.pos ≤ A.n) := once_pos A _ _ _ _
    have hle : s4.pos ≤ A.n := by omega
    have g : Grows (AtEv c) s s4 :=
      Grows.trans (Grows.trans (enter_grows A c again s) (ask_grows A c d s2)
        (fun e ⟨g, b, h, hg, _⟩ => ⟨g, b, h, hg⟩) (fun e h => ⟨_, _, h, rfl⟩))
        (once_grows A _ _ _ _) (fun e h => h) (fun e ⟨b, h⟩ => ⟨_, b, h, rfl⟩)
    exact nav_next A g h4 (visit_pos A _ _ _ _ (by omega) hle).1 (ih (by omega) hle)
  | case7 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    have g : Grows (AtEv c) s s4 :=
      Grows.trans (Grows.trans (enter_grows A c again s) (ask_grows A c d s2)
        (fun e ⟨g, b, h, hg, _⟩ => ⟨g, b, h, hg⟩) (fun e h => ⟨_, _, h, rfl⟩))
        (once_grows A _ _ _ _) (fun e h => h) (fun e ⟨b, h⟩ => ⟨_, b, h, rfl⟩)
    exact nav_next A g (by omega) (visit_pos A _ _ _ _ (by omega) (by omega)).1 (ih (by omega) (by omega))


/-- A relation between states that every step of the handler respects. -/
structure StepRel (R : St σ → St σ → Prop) : Prop where
  refl : ∀ s, R s s
  trans : ∀ {s₁ s₂ s₃}, R s₁ s₂ → R s₂ s₃ → R s₁ s₃
  pos : ∀ s c, R s { s with pos := c }
  once : ∀ h p again s, (h.once = true → again = false) → R s (A.once h p again s)
  call : ∀ h p s f, h.once = false → R s (A.call h p s f).2
  /-- Recording an event that is not a hook call. -/
  note : ∀ s s' e, s'.ran = s.ran → s'.pos = s.pos → s'.log = s.log ++ [e] →
    (∀ q h b, e ≠ .call q h b) → R s s'
  deadline : ∀ s dl, R s { s with deadline := dl }

section Rel
variable {A} {R : St σ → St σ → Prop} (hR : StepRel A R)
include hR

theorem StepRel.ask (c d s) : R s (A.ask c d s).2 := by
  unfold App.ask; split
  · exact hR.refl _
  · exact hR.call _ _ _ _ rfl

theorem StepRel.display (s : St σ) (p d) : R s (s.display p d) :=
  hR.note _ _ _ rfl rfl rfl (by simp)

theorem StepRel.visit (c : Int) (again d s) : R s (A.visit c again d s) := by
  have e := fun s c again => hR.trans (hR.pos s c) (hR.once .early c again _ (by simp [Hook.once]))
  have b := fun s c => hR.once .beforeAlwaysOnce c false s (fun _ => rfl)
  have o := fun h c s => hR.once h c false s (fun _ => rfl)
  fun_induction A.visit c again d s with
  | case1 c again d s =>
    exact hR.trans (hR.trans (hR.trans (e s _ again) (b _ _)) (o _ _ _)) (hR.display _ _ _)
  | case2 c again d s _ s1 s2 _ ih => exact hR.trans (hR.trans (e s _ again) (b _ _)) ih
  | case3 c again d s _ s1 s2 _ r s3 _ ih =>
    exact hR.trans (hR.trans (hR.trans (e s _ again) (b _ _)) (hR.ask _ _ _)) ih
  | case4 c again d s _ s1 s2 _ r s3 _ _ s4 _ ih =>
    exact hR.trans (hR.trans (hR.trans (hR.trans (e s _ again) (b _ _)) (hR.ask _ _ _)) (o _ _ _)) ih
  | case5 c again d s _ s1 s2 _ r s3 _ _ s4 _ =>
    exact hR.trans (hR.trans (hR.trans (hR.trans (e s _ again) (b _ _)) (hR.ask _ _ _)) (o _ _ _))
      (hR.display _ _ _)
  | case6 c again d s _ s1 s2 _ r s3 _ _ s4 _ ih =>
    exact hR.trans (hR.trans (hR.trans (hR.trans (e s _ again) (b _ _)) (hR.ask _ _ _)) (o _ _ _)) ih
  | case7 c again d s _ s1 s2 _ r s3 _ _ s4 _ ih =>
    exact hR.trans (hR.trans (hR.trans (hR.trans (e s _ again) (b _ _)) (hR.ask _ _ _)) (o _ _ _)) ih

theorem StepRel.leave (k s) : R s (A.leave k s) :=
  hR.trans (hR.trans (hR.once _ _ _ _ fun _ => rfl) (hR.once _ _ _ _ fun _ => rfl)) (hR.visit _ _ _ _)

theorem StepRel.load (k s) : R s (A.load k s) := by
  unfold App.load; split <;> exact hR.visit _ _ _ _

theorem StepRel.stay (k d s) : R s (A.stay k d s) := by
  unfold App.stay; split <;> exact hR.visit _ _ _ _

theorem StepRel.proceed (k s) : R s (A.proceed k s) := by
  unfold App.proceed; split
  · exact hR.leave _ _
  · exact hR.visit _ _ _ _

theorem StepRel.back (k j s) : R s (A.back k j s) := by
  fun_induction A.back k j s with
  | case1 => exact hR.trans (hR.pos _ _) (hR.stay _ _ _)
  | case2 => exact hR.trans (hR.pos _ _) (hR.stay _ _ _)
  | case3 => exact hR.trans (hR.trans (hR.pos _ _) (hR.call _ _ _ _ rfl)) (hR.visit _ _ _ _)
  | case4 => exact hR.trans (hR.trans (hR.pos _ _) (hR.call _ _ _ _ rfl)) (hR.visit _ _ _ _)
  | case5 _ _ _ _ _ _ _ ih => exact hR.trans (hR.trans (hR.pos _ _) (hR.call _ _ _ _ rfl)) ih

theorem StepRel.goBack (k s) : R s (A.goBack k s) := by
  unfold App.goBack; dsimp only
  have c := hR.call .allowBack k s default rfl
  split
  · exact hR.trans c (hR.visit _ _ _ _)
  · split
    · exact hR.trans c (hR.back _ _ _)
    · exact hR.trans c (hR.stay _ _ _)

theorem StepRel.stealth (k f s) : R s (A.stealth k f s).2 := by
  unfold App.stealth; split
  · exact hR.call _ _ _ _ rfl
  · exact hR.refl _

theorem StepRel.saveForm (k f s) : R s (A.saveForm k f s) :=
  hR.note _ _ _ rfl rfl rfl (by simp)

theorem StepRel.accept (k f s) : R s (A.accept k f s).2 := by
  unfold App.accept; dsimp only
  split
  · split
    · have c := hR.call .validate k s f rfl
      split
      · have c' := hR.trans c (hR.stealth k f _)
        split
        · exact hR.trans (hR.trans c' (hR.call _ _ _ _ rfl)) (hR.saveForm _ _ _)
        · exact c'
      · exact c
    · exact hR.refl _
  · exact hR.refl _

theorem StepRel.fires (now t k s) : R s (A.fires now t k s).2 := by
  unfold App.fires; split
  · exact hR.refl _
  · split
    · exact hR.refl _
    · exact hR.call _ _ _ _ rfl

theorem StepRel.timedOut (now k s) : R s (A.timedOut now k s).2 := by
  unfold App.timedOut
  split
  · exact hR.refl _
  · dsimp only
    split
    · exact hR.trans (hR.fires _ _ _ _) (hR.call _ _ _ _ rfl)
    · exact hR.fires _ _ _ _

theorem StepRel.respond (now r s) : R s (A.respond now r s) := by
  unfold App.respond; dsimp only
  split
  · split
    · exact hR.trans (hR.note s { s with started := true, app := A.start s.app, log := s.log ++ [.init] }
        .init rfl rfl rfl (by simp)) (hR.visit _ _ _ _)
    · exact hR.display _ _ _
  · split
    · exact hR.note _ _ .error rfl rfl rfl (by simp)
    · have t := hR.timedOut now s.pos s
      split
      · split
        · exact hR.trans t (hR.proceed _ _)
        · exact hR.trans t (hR.load _ _)
      · split
        · exact hR.trans (hR.trans t (hR.accept _ _ _)) (hR.proceed _ _)
        · split
          · exact hR.trans t (hR.goBack _ _)
          · split
            · split
              · exact hR.trans (hR.trans (hR.trans t (hR.accept _ _ _)) (hR.call _ _ _ _ rfl)) (hR.proceed _ _)
              · exact hR.trans (hR.trans (hR.trans t (hR.accept _ _ _)) (hR.call _ _ _ _ rfl)) (hR.stay _ _ _)
            · exact hR.trans (hR.trans t (hR.accept _ _ _)) (hR.stay _ _ _)

theorem StepRel.arm (now s) : R s (A.arm now s) := by
  unfold App.arm
  split
  · split
    · exact hR.deadline _ _
    · exact hR.refl _
  · exact hR.refl _

theorem StepRel.step (now r s) : R s (A.step now r s) := hR.trans (hR.respond now r s) (hR.arm now _)

end Rel

/-- Markers are never removed. -/
def RanGrows (s s' : St σ) : Prop := ∀ x ∈ s.ran, x ∈ s'.ran

theorem ranGrows : StepRel A RanGrows where
  refl _ _ h := h
  trans h₁ h₂ x hx := h₂ x (h₁ x hx)
  pos _ _ _ h := h
  once h p again s _ x hx := once_ran A h p again s x hx
  call h p s f _ x hx := by simpa using hx
  note _ _ _ hr _ _ _ x hx := by rw [hr]; exact hx
  deadline _ _ _ h := h

/-- The log only grows. -/
theorem logGrows : StepRel A (fun s s' => ∃ u, s'.log = s.log ++ u) where
  refl _ := ⟨[], by simp⟩
  trans := fun ⟨u, hu⟩ ⟨v, hv⟩ => ⟨u ++ v, by simp [hv, hu]⟩
  pos _ _ := ⟨[], by simp⟩
  once h p again s _ := by
    rcases once_log A h p again s with e | ⟨b, e⟩
    · exact ⟨[], by simp [e]⟩
    · exact ⟨_, e⟩
  call h p s f _ := by
    rcases call_log A h p s f with e | e
    · exact ⟨[], by simp [e]⟩
    · exact ⟨_, e⟩
  note _ _ e _ _ hl _ := ⟨[e], hl⟩
  deadline _ _ := ⟨[], by simp⟩

theorem onceOK : StepRel A (fun s s' => OnceOK s → OnceOK s') where
  refl _ h := h
  trans h₁ h₂ h := h₂ (h₁ h)
  pos _ _ h := h
  once h p again s ha ok := once_ok A h p again s ha ok
  call h p s f hh ok := call_ok A h p s f hh ok
  note s s' e hr _ hl he ok := by
    intro q g hg
    have : runs q g s'.log = runs q g s.log := by
      rw [hl, runs_append]
      cases e <;> simp_all [runs, Ev.isCall]
    rw [this, hr]; exact ok q g hg
  deadline _ _ ok := ok

/-! ### Parts of the handler -/

/-- A call of a hook `h` with `H h`. -/
def CallOf (H : Hook → Prop) (e : Ev) : Prop := ∃ q h b, e = .call q h b ∧ H h

/-- `s'` ends a run of the handler from `s` that displays `s'.pos` with `sh`:
the log grew by events `P`, then that display, and `s'.pos`, from `0` to `n`,
is entered. -/
def App.Ends (P : Ev → Prop) (s s' : St σ) (sh : Shown) : Prop :=
  ∃ u, s'.log = s.log ++ u ++ [.display s'.pos sh] ∧ (∀ e ∈ u, P e) ∧
    A.Entered s' s'.pos ∧ 0 ≤ s'.pos ∧ s'.pos ≤ A.n

omit [Inhabited F] in
theorem Ends.mono {P Q : Ev → Prop} {s s' : St σ} {sh} (h : A.Ends P s s' sh) (hPQ : ∀ e, P e → Q e) :
    A.Ends Q s s' sh :=
  let ⟨u, e, pu, rest⟩ := h
  ⟨u, e, fun x hx => hPQ x (pu x hx), rest⟩

theorem CallOf.mono {H H' : Hook → Prop} (hH : ∀ g, H g → H' g) (e : Ev) (h : CallOf H e) : CallOf H' e :=
  let ⟨q, g, b, h1, h2⟩ := h; ⟨q, g, b, h1, hH g h2⟩

omit [Inhabited F] in
theorem Ends.pre {P : Ev → Prop} {s X Y : St σ} {sh}
    (g : Grows P s X) (h : A.Ends P X Y sh) : A.Ends P s Y sh :=
  let ⟨u0, e0, p0⟩ := g
  let ⟨u, e, pu, rest⟩ := h
  ⟨u0 ++ u, by simp [e, e0], fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact p0 x hx
    · exact pu x hx, rest⟩

theorem visit_ends (c : Int) (again d s) (h0 : 0 ≤ c) (hn : c ≤ A.n) :
    ∃ sh, A.Ends (CallOf fun h => h.nav = true) s (A.visit c again d s) sh ∧
      (sh = .fresh ∨ ((A.visit c again d s).pos = c ∧ d = some sh)) ∧ c ≤ (A.visit c again d s).pos := by
  obtain ⟨u, sh, e, pu, hsh, hent⟩ := visit_spec A c again d s h0 hn
  have hp := visit_pos A c again d s h0 hn
  refine ⟨sh, ⟨u, e, fun x hx => ?_, hent, by omega, hp.2⟩, hsh, hp.1⟩
  obtain ⟨q, g, b, rfl, hg, -⟩ := pu x hx
  exact ⟨q, g, b, rfl, hg⟩

/-- The position moves forward, if at all, and only up to `n`. -/
def App.Fwd (s s' : St σ) : Prop := s'.pos = s.pos ∨ (0 ≤ s.pos ∧ s.pos < s'.pos ∧ s'.pos ≤ A.n)

omit [Inhabited F] in
theorem Fwd.trans {s₁ s₂ s₃ : St σ} (h₁ : A.Fwd s₁ s₂) (h₂ : A.Fwd s₂ s₃) : A.Fwd s₁ s₃ := by
  unfold App.Fwd at *; omega

theorem call_fwd (h p s f) : A.Fwd s (A.call h p s f).2 := call_pos A h p s f
theorem once_fwd (h p again s) : A.Fwd s (A.once h p again s) := once_pos A h p again s

/-- Calls of hooks `H` at position `k`. -/
def Calls (k : Int) (H : Hook → Prop) (e : Ev) : Prop := ∃ h b, e = .call k h b ∧ H h

theorem call_calls (h k s f) : Grows (Calls k (· = h)) s (A.call h k s f).2 :=
  (call_grows A h k s f).mono fun _ e => ⟨h, _, e, rfl⟩

theorem once_calls (h k again s) : Grows (Calls k (· = h)) s (A.once h k again s) :=
  (once_grows A h k again s).mono fun _ ⟨b, e⟩ => ⟨h, b, e, rfl⟩

theorem Grows.calls {k : Int} {H : Hook → Prop} {s s' : St σ} (g : Grows (Calls k H) s s') :
    Grows (CallOf H) s s' :=
  g.mono fun _ ⟨h, b, e, hh⟩ => ⟨k, h, b, e, hh⟩

/-- Leaving `k`: `after_once` and `after_always_once` at `k`, then navigation
to a position after `k`. -/
theorem leave_ends (k : Int) (s : St σ) (h0 : 0 ≤ k) (hn : k < A.n) (hs : s.pos ≤ A.n) :
    A.Ends (CallOf fun h => h.nav = true ∨ h = .afterOnce) s (A.leave k s) .fresh ∧ k < (A.leave k s).pos := by
  unfold App.leave; dsimp only
  have f := Fwd.trans A (once_fwd A .afterOnce k false s) (once_fwd A .afterAlwaysOnce k false _)
  have g : Grows (Calls k fun h => h = .afterOnce ∨ h = .afterAlwaysOnce) s
      (A.once .afterAlwaysOnce k false (A.once .afterOnce k false s)) :=
    Grows.trans (once_calls A _ _ _ _) (once_calls A _ _ _ _)
      (fun _ ⟨h, b, e, hh⟩ => ⟨h, b, e, .inl hh⟩) (fun _ ⟨h, b, e, hh⟩ => ⟨h, b, e, .inr hh⟩)
  generalize A.once .afterAlwaysOnce k false (A.once .afterOnce k false s) = s2 at f g
  have ht : 0 ≤ (if k < s2.pos then s2.pos else k + 1) ∧ (if k < s2.pos then s2.pos else k + 1) ≤ A.n ∧
      k < (if k < s2.pos then s2.pos else k + 1) := by
    unfold App.Fwd at f; split <;> omega
  obtain ⟨sh, hend, hsh, hge⟩ := visit_ends A _ true none s2 ht.1 ht.2.1
  have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
  subst this
  refine ⟨Ends.pre A (g.calls.mono fun _ ⟨q, h, b, e, hh⟩ => ⟨q, h, b, e, ?_⟩) (Ends.mono A hend (CallOf.mono fun _ h => .inl h)), by omega⟩
  rcases hh with rfl | rfl
  · exact .inr rfl
  · exact .inl rfl

theorem proceed_ends (k : Int) (s : St σ) (h0 : 0 ≤ k) (hn : k ≤ A.n) (hs : s.pos ≤ A.n) :
    A.Ends (CallOf fun h => h.nav = true ∨ h = .afterOnce) s (A.proceed k s) .fresh ∧
      (k < A.n → k < (A.proceed k s).pos) := by
  unfold App.proceed; split
  · next h => exact ⟨(leave_ends A k s h0 h hs).1, fun _ => (leave_ends A k s h0 h hs).2⟩
  · next h =>
    obtain ⟨sh, hend, hsh, -⟩ := visit_ends A k false (some .fresh) s h0 hn
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this
    exact ⟨Ends.mono A hend (CallOf.mono fun _ h => .inl h), fun h' => absurd h' h⟩

theorem stay_ends (k : Int) (d : Shown) (s : St σ) (h0 : 0 ≤ k) (hk : k ≤ s.pos) (hs : s.pos ≤ A.n) :
    ∃ sh, A.Ends (CallOf fun h => h.nav = true) s (A.stay k d s) sh ∧
      (sh = .fresh ∨ ((A.stay k d s).pos = k ∧ sh = d)) := by
  unfold App.stay; split
  · next h =>
    obtain ⟨sh, hend, hsh, -⟩ := visit_ends A _ true none s (by omega) hs
    exact ⟨sh, hend, by rcases hsh with h | ⟨-, h⟩ <;> simp_all⟩
  · obtain ⟨sh, hend, hsh, -⟩ := visit_ends A k false (some d) s h0 (by omega)
    exact ⟨sh, hend, by rcases hsh with h | ⟨h1, h2⟩ <;> simp_all⟩

theorem load_ends (k : Int) (s : St σ) (h0 : 0 ≤ k) (hk : k ≤ s.pos) (hs : s.pos ≤ A.n) :
    A.Ends (CallOf fun h => h.nav = true) s (A.load k s) .fresh := by
  unfold App.load; split
  · obtain ⟨sh, hend, hsh, -⟩ := visit_ends A _ true none s (by omega) hs
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this; exact hend
  · obtain ⟨sh, hend, hsh, -⟩ := visit_ends A k false none s h0 (by omega)
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this; exact hend

theorem back_ends (k j : Int) (s : St σ) (hj : j < k) (h0 : 0 ≤ k) (hn : k ≤ A.n) :
    A.Ends (CallOf fun h => h.nav = true) s (A.back k j s) .fresh := by
  fun_induction A.back k j s with
  | case1 j s =>
    obtain ⟨sh, hend, hsh⟩ := stay_ends A k .fresh { s with pos := k } h0 (Int.le_refl _) hn
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this; exact Ends.pre A (Grows.refl rfl) hend
  | case2 j s =>
    obtain ⟨sh, hend, hsh⟩ := stay_ends A k .fresh { s with pos := k } h0 (Int.le_refl _) hn
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this; exact Ends.pre A (Grows.refl rfl) hend
  | case3 j s hj0 _ r hm =>
    have f : A.Fwd { s with pos := j } r.2 := call_fwd A _ _ _ _
    have hle : r.2.pos ≤ A.n := by unfold App.Fwd at f; simp at f; omega
    obtain ⟨sh, hend, hsh, -⟩ := visit_ends A r.2.pos true none r.2 (by omega) hle
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this
    exact Ends.pre A ((Grows.trans (Grows.refl (s' := { s with pos := j }) rfl) (call_calls A _ _ _ _)
      (fun _ h => h) (fun _ h => h)).calls.mono fun _ ⟨q, h, b, e, hh⟩ => ⟨q, h, b, e, by subst hh; rfl⟩) hend
  | case4 j s hj0 _ r _ _ =>
    obtain ⟨sh, hend, hsh, -⟩ := visit_ends A j true (some .fresh) r.2 (by omega) (by omega)
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this
    exact Ends.pre A ((Grows.trans (Grows.refl (s' := { s with pos := j }) rfl) (call_calls A _ _ _ _)
      (fun _ h => h) (fun _ h => h)).calls.mono fun _ ⟨q, h, b, e, hh⟩ => ⟨q, h, b, e, by subst hh; rfl⟩) hend
  | case5 j s hj0 _ r _ _ ih =>
    exact Ends.pre A ((Grows.trans (Grows.refl (s' := { s with pos := j }) rfl) (call_calls A _ _ _ _)
      (fun _ h => h) (fun _ h => h)).calls.mono fun _ ⟨q, h, b, e, hh⟩ => ⟨q, h, b, e, by subst hh; rfl⟩)
      (ih (by omega))

theorem goBack_ends (k : Int) (s : St σ) (h0 : 0 ≤ k) (hn : k ≤ A.n) (hk : k ≤ s.pos) (hs : s.pos ≤ A.n) :
    A.Ends (CallOf fun h => h.nav = true ∨ h = .allowBack) s (A.goBack k s) .fresh := by
  unfold App.goBack; dsimp only
  have f : A.Fwd s (A.call .allowBack k s).2 := call_fwd A _ _ _ _
  have g := (call_calls A .allowBack k s default).calls
  generalize A.call .allowBack k s = r at f g
  have hle : r.2.pos ≤ A.n := by unfold App.Fwd at f; omega
  have pre : ∀ {Y : St σ}, A.Ends (CallOf fun h => h.nav = true) r.2 Y .fresh →
      A.Ends (CallOf fun h => h.nav = true ∨ h = .allowBack) s Y .fresh := fun h =>
    Ends.pre A (g.mono fun _ ⟨q, h, b, e, hh⟩ => ⟨q, h, b, e, Or.inr hh⟩) (Ends.mono A h (CallOf.mono fun _ h => Or.inl h))
  split
  · obtain ⟨sh, hend, hsh, -⟩ := visit_ends A r.2.pos true none r.2 (by omega) hle
    have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
    subst this; exact pre hend
  · split
    · exact pre (back_ends A k (k - 1) r.2 (by omega) h0 hn)
    · obtain ⟨sh, hend, hsh⟩ := stay_ends A k .fresh r.2 h0 (by unfold App.Fwd at f; omega) hle
      have : sh = .fresh := by rcases hsh with h | ⟨-, h⟩ <;> simp_all
      subst this; exact pre hend

def Ev.isSave : Ev → Bool
  | .save .. => true
  | _ => false

theorem stealth_fwd (k f s) : A.Fwd s (A.stealth k f s).2 := by
  unfold App.stealth; split
  · exact call_fwd A _ _ _ _
  · exact .inl rfl

theorem stealth_calls (k f s) : Grows (Calls k (· = .handleStealthFields)) s (A.stealth k f s).2 := by
  unfold App.stealth; split
  · exact call_calls A _ _ _ _
  · exact Grows.refl rfl

/-- The checks of a submission: what they run, and that they save the form,
once, exactly if they accept it. -/
theorem accept_spec (k : Int) (f : F) (s : St σ) :
    A.Fwd s (A.accept k f s).2 ∧ ∃ u, (A.accept k f s).2.log = s.log ++ u ∧
      (∀ e ∈ u, Calls k (fun h => h = .validate ∨ h = .handleStealthFields ∨ h = .beforeFormSave) e ∨
        ∃ fs, e = .save k fs) ∧
      u.countP Ev.isSave = if A.hasForm k = true ∧ (A.accept k f s).1 = true then 1 else 0 := by
  have noSave : ∀ {u : List Ev}, (∀ e ∈ u, ∃ q h b, e = .call q h b) → u.countP Ev.isSave = 0 := by
    intro u hu; rw [List.countP_eq_zero]; intro e he
    obtain ⟨q, h, b, rfl⟩ := hu e he; simp [Ev.isSave]
  have gv := call_calls A .validate k s f
  have fv := call_fwd A .validate k s f
  unfold App.accept; dsimp only
  split
  · split
    · split
      · next hv =>
        have gh := stealth_calls A k f (A.call .validate k s f).2
        have fh := stealth_fwd A k f (A.call .validate k s f).2
        split
        · next hh =>
          have gb := call_calls A .beforeFormSave k (A.stealth k f (A.call .validate k s f).2).2 f
          have fb := call_fwd A .beforeFormSave k (A.stealth k f (A.call .validate k s f).2).2 f
          generalize A.call .validate k s f = v at *
          generalize A.stealth k f v.2 = w at *
          generalize A.call .beforeFormSave k w.2 f = x at *
          obtain ⟨u1, e1, p1⟩ := gv; obtain ⟨u2, e2, p2⟩ := gh; obtain ⟨u3, e3, p3⟩ := gb
          refine ⟨Fwd.trans A (Fwd.trans A (Fwd.trans A fv fh) fb) (.inl rfl),
            u1 ++ u2 ++ u3 ++ [.save k (A.ordinary k f x.2.app)], by simp [App.saveForm, e1, e2, e3], ?_, ?_⟩
          · intro e he
            simp only [List.mem_append, List.mem_singleton] at he
            rcases he with ((he | he) | he) | rfl
            · obtain ⟨h, b, rfl, rfl⟩ := p1 e he; exact .inl ⟨_, b, rfl, .inl rfl⟩
            · obtain ⟨h, b, rfl, rfl⟩ := p2 e he; exact .inl ⟨_, b, rfl, .inr (.inl rfl)⟩
            · obtain ⟨h, b, rfl, rfl⟩ := p3 e he; exact .inl ⟨_, b, rfl, .inr (.inr rfl)⟩
            · exact .inr ⟨_, rfl⟩
          · have c : ∀ {u : List Ev} {k : Int} {H : Hook → Prop}, (∀ e ∈ u, Calls k H e) →
                u.countP Ev.isSave = 0 := fun hu =>
              noSave fun e he => let ⟨h, b, h1, _⟩ := hu e he; ⟨_, h, b, h1⟩
            simp [List.countP_append, c p1, c p2, c p3, Ev.isSave, *]
        · generalize A.call .validate k s f = v at *
          obtain ⟨u1, e1, p1⟩ := gv; obtain ⟨u2, e2, p2⟩ := gh
          refine ⟨Fwd.trans A fv fh, u1 ++ u2, by simp [e1, e2], ?_, ?_⟩
          · intro e he
            rcases List.mem_append.mp he with he | he
            · obtain ⟨h, b, rfl, rfl⟩ := p1 e he; exact .inl ⟨_, b, rfl, .inl rfl⟩
            · obtain ⟨h, b, rfl, rfl⟩ := p2 e he; exact .inl ⟨_, b, rfl, .inr (.inl rfl)⟩
          · simp only [Bool.false_eq_true, and_false, ite_false]
            exact noSave fun e he => by
              rcases List.mem_append.mp he with he | he
              · obtain ⟨h, b, rfl, -⟩ := p1 e he; exact ⟨_, _, _, rfl⟩
              · obtain ⟨h, b, rfl, -⟩ := p2 e he; exact ⟨_, _, _, rfl⟩
      · obtain ⟨u1, e1, p1⟩ := gv
        refine ⟨fv, u1, e1, fun e he => ?_, ?_⟩
        · obtain ⟨h, b, rfl, rfl⟩ := p1 e he; exact .inl ⟨_, b, rfl, .inl rfl⟩
        · simp only [Bool.false_eq_true, and_false, ite_false]
          exact noSave fun e he => let ⟨h, b, h1, _⟩ := p1 e he; ⟨_, h, b, h1⟩
    · exact ⟨.inl rfl, [], by simp, by simp, by simp⟩
  · next h => exact ⟨.inl rfl, [], by simp, by simp, by simp [h]⟩

theorem fires_spec (now t : Nat) (k : Int) (s : St σ) :
    A.Fwd s (A.fires now t k s).2 ∧ Grows (Calls k (· = .mayProceed)) s (A.fires now t k s).2 := by
  unfold App.fires; split
  · exact ⟨.inl rfl, Grows.refl rfl⟩
  · split
    · exact ⟨.inl rfl, Grows.refl rfl⟩
    · exact ⟨call_fwd A _ _ _ _, call_calls A _ _ _ _⟩

theorem timedOut_spec (now : Nat) (k : Int) (s : St σ) :
    A.Fwd s (A.timedOut now k s).2 ∧
      Grows (Calls k fun h => h = .mayProceed ∨ h = .timeoutReached) s (A.timedOut now k s).2 := by
  unfold App.timedOut; split
  · exact ⟨.inl rfl, Grows.refl rfl⟩
  · next t _ =>
    dsimp only
    have ⟨f1, g1⟩ := fires_spec A now t k s
    have g1' := g1.mono (Q := Calls k fun h => h = .mayProceed ∨ h = .timeoutReached)
      fun _ ⟨h, b, e, hh⟩ => ⟨h, b, e, .inl hh⟩
    split
    · exact ⟨Fwd.trans A f1 (call_fwd A _ _ _ _), Grows.trans g1' (call_calls A _ _ _ _) (fun _ h => h)
        fun _ ⟨h, b, e, hh⟩ => ⟨h, b, e, .inr hh⟩⟩
    · exact ⟨f1, g1'⟩

end Facts

/-! ## Requests -/

section Requests

variable {σ F : Type} [Inhabited F] (A : App σ F)

theorem ite_not {α} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by simp [h]
theorem ite_yes {α} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by simp [h]

omit [Inhabited F] in
@[simp] theorem arm_log (now s) : (A.arm now s).log = s.log := by
  unfold App.arm; split <;> (try split) <;> rfl
omit [Inhabited F] in
@[simp] theorem arm_pos (now s) : (A.arm now s).pos = s.pos := by
  unfold App.arm; split <;> (try split) <;> rfl
omit [Inhabited F] in
@[simp] theorem arm_ran (now s) : (A.arm now s).ran = s.ran := by
  unfold App.arm; split <;> (try split) <;> rfl

omit [Inhabited F] in
theorem entered_arm {now s p} : A.Entered (A.arm now s) p ↔ A.Entered s p := by
  simp [App.Entered]

/-- (3) A request that does not carry the form of the player's position with a
valid token is handled exactly as loading the page. -/
theorem foreign_is_get (now : Nat) (r : Req F) (s : St σ) (h : r.submission s.pos = none) :
    A.step now r s = A.step now .get s := by
  have hg : (Req.get : Req F).submission s.pos = none := rfl
  simp only [App.step, App.respond, h, hg]

/-- (3) Submitting a form again once it has taken the player elsewhere (e.g.,
a double click on Next) is handled as loading the page. -/
theorem resubmit_is_get (now now' : Nat) (r : Req F) (s : St σ) (b : Bool) (f : F)
    (h : r.submission s.pos = some (b, f)) (hl : (A.step now r s).pos ≠ s.pos) :
    A.step now' r (A.step now r s) = A.step now' .get (A.step now r s) := by
  apply foreign_is_get
  match r, h with
  | .post (some p) back true form, h =>
    have hp : p = s.pos := by
      simp only [Req.submission] at h; split at h
      · assumption
      · cases h
    simp only [Req.submission]
    rw [ite_not (by omega)]

/-- What a request can record before it displays a page. -/
def Rec (e : Ev) : Prop := (∃ q h b, e = .call q h b) ∨ e = .init ∨ ∃ p fs, e = .save p fs

theorem CallOf.rec {H : Hook → Prop} {e : Ev} (h : CallOf H e) : Rec e :=
  let ⟨q, g, b, h1, _⟩ := h; .inl ⟨q, g, b, h1⟩

theorem Calls.rec {k : Int} {H : Hook → Prop} {e : Ev} (h : Calls k H e) : Rec e :=
  let ⟨g, b, h1, _⟩ := h; .inl ⟨k, g, b, h1⟩

/-- A request at a position from `0` to `n` ends by displaying an entered page. -/
theorem respond_ends (now : Nat) (r : Req F) (s : St σ) (h0 : 0 ≤ s.pos) (hn : s.pos ≤ A.n) :
    ∃ sh, A.Ends Rec s (A.respond now r s) sh := by
  have ⟨ft, gt⟩ := timedOut_spec A now s.pos s
  have gt' := gt.mono fun _ h => Calls.rec h
  have hk : s.pos ≤ (A.timedOut now s.pos s).2.pos ∧ (A.timedOut now s.pos s).2.pos ≤ A.n := by
    unfold App.Fwd at ft; omega
  have acc := fun f (X : St σ) => accept_spec A s.pos f X
  unfold App.respond; dsimp only
  rw [ite_not (by omega), ite_not (by omega)]
  generalize A.timedOut now s.pos s = t at *
  split
  · split
    · exact ⟨_, Ends.pre A gt' (Ends.mono A (proceed_ends A _ _ h0 hn hk.2).1 fun _ h => h.rec)⟩
    · exact ⟨_, Ends.pre A gt' (Ends.mono A (load_ends A _ _ h0 hk.1 hk.2) fun _ h => h.rec)⟩
  · next back f _ =>
    obtain ⟨fa, u, ea, pa, -⟩ := acc f t.2
    have ga : Grows Rec t.2 (A.accept s.pos f t.2).2 :=
      ⟨u, ea, fun e he => (pa e he).elim Calls.rec fun ⟨fs, h⟩ => .inr (.inr ⟨_, fs, h⟩)⟩
    have hk' : s.pos ≤ (A.accept s.pos f t.2).2.pos ∧ (A.accept s.pos f t.2).2.pos ≤ A.n := by
      unfold App.Fwd at fa; omega
    split
    · exact ⟨_, Ends.pre A gt' (Ends.pre A ga
        (Ends.mono A (proceed_ends A _ _ h0 hn hk'.2).1 fun _ h => h.rec))⟩
    · split
      · exact ⟨_, Ends.pre A gt' (Ends.mono A (goBack_ends A _ _ h0 hn hk.1 hk.2) fun _ h => h.rec)⟩
      · have fm := call_fwd A .mayProceed s.pos (A.accept s.pos f t.2).2 default
        have gm := (call_calls A .mayProceed s.pos (A.accept s.pos f t.2).2 default).mono
          fun _ h => Calls.rec h
        have hk'' : s.pos ≤ (A.call .mayProceed s.pos (A.accept s.pos f t.2).2).2.pos ∧
            (A.call .mayProceed s.pos (A.accept s.pos f t.2).2).2.pos ≤ A.n := by
          unfold App.Fwd at fm; omega
        split
        · split
          · exact ⟨_, Ends.pre A gt' (Ends.pre A ga (Ends.pre A gm
              (Ends.mono A (proceed_ends A _ _ h0 hn hk''.2).1 fun _ h => h.rec)))⟩
          · obtain ⟨sh, hend, -⟩ := stay_ends A s.pos .kept _ h0 hk''.1 hk''.2
            exact ⟨sh, Ends.pre A gt' (Ends.pre A ga (Ends.pre A gm (Ends.mono A hend fun _ h => h.rec)))⟩
        · obtain ⟨sh, hend, -⟩ := stay_ends A s.pos .errors _ h0 hk'.1 hk'.2
          exact ⟨sh, Ends.pre A gt' (Ends.pre A ga (Ends.mono A hend fun _ h => h.rec))⟩

/-- (1) A request at a valid position ends by displaying the page at the
player's position, again valid; a page other than `Initialize.html` is entered
first. Before the display, the request runs hooks, starts the player or saves
a form, and nothing else. -/
theorem step_display (now : Nat) (r : Req F) (s : St σ) (h1 : -1 ≤ s.pos) (h2 : s.pos ≤ A.n) :
    ∃ u sh, (A.step now r s).log = s.log ++ u ++ [.display (A.step now r s).pos sh] ∧ (∀ e ∈ u, Rec e) ∧
      -1 ≤ (A.step now r s).pos ∧ (A.step now r s).pos ≤ A.n ∧
      (0 ≤ (A.step now r s).pos → A.Entered (A.step now r s) (A.step now r s).pos) := by
  simp only [App.step, arm_log, arm_pos, entered_arm]
  by_cases hk : s.pos = -1
  · unfold App.respond; dsimp only; rw [ite_yes hk]
    split
    · obtain ⟨sh, ⟨u, e, pu, hent, hp0, hpn⟩, -⟩ := visit_ends A 0 true none
        { s with started := true, app := A.start s.app, log := s.log ++ [.init] } (Int.le_refl 0) (by omega)
      refine ⟨.init :: u, sh, by simp [e], fun x hx => ?_, by omega, hpn, fun _ => hent⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .inr (.inl rfl)
      · exact (pu x hx).rec
    · exact ⟨[], .fresh, by simp [St.display, hk], by simp, by simp [St.display, hk],
        by simp [St.display]; omega, by simp [St.display, hk]⟩
  · obtain ⟨sh, u, e, pu, hent, hp0, hpn⟩ := respond_ends A now r s (by omega) h2
    exact ⟨u, sh, e, pu, by omega, hpn, fun _ => hent⟩

/-! ### Saves, timeouts, errors and Back -/

theorem timedOut_far (now : Nat) (k : Int) (s : St σ)
    (hd : ∀ t, s.deadline k = some t → now + A.tolerance < t) : A.timedOut now k s = (false, s) := by
  unfold App.timedOut; split
  · rfl
  · next t ht => have := hd t ht; simp [App.fires, show ¬t ≤ now by omega, this]

theorem timedOut_fired {now : Nat} {k : Int} {s : St σ} (h : (A.timedOut now k s).1 = true) :
    ∃ t, s.deadline k = some t ∧ t ≤ now + A.tolerance := by
  unfold App.timedOut at h; split at h
  · simp at h
  · next t ht =>
    refine ⟨t, ht, ?_⟩
    by_cases hc : t ≤ now + A.tolerance
    · exact hc
    · simp [App.fires, show ¬t ≤ now by omega, show now + A.tolerance < t by omega] at h

theorem timedOut_passed (now : Nat) (k : Int) (s : St σ) (t : Nat) (ht : s.deadline k = some t)
    (hp : t ≤ now) : A.timedOut now k s = (true, (A.call .timeoutReached k s).2) := by
  simp [App.timedOut, ht, App.fires, hp]

theorem saves_calls {u : List Ev} (h : ∀ e ∈ u, ∃ q g b, e = .call q g b) : u.countP Ev.isSave = 0 := by
  rw [List.countP_eq_zero]; intro e he; obtain ⟨q, g, b, rfl⟩ := h e he; simp [Ev.isSave]

omit [Inhabited F] in
theorem Ends.saves {H : Hook → Prop} {X Y : St σ} {sh} (h : A.Ends (CallOf H) X Y sh) :
    ∃ v, Y.log = X.log ++ v ∧ v.countP Ev.isSave = 0 := by
  obtain ⟨u, e, pu, -⟩ := h
  refine ⟨u ++ [.display Y.pos sh], by simp [e], ?_⟩
  rw [List.countP_append, saves_calls fun e he => let ⟨q, g, b, h, _⟩ := pu e he; ⟨q, g, b, h⟩]
  simp [Ev.isSave]

theorem Grows.saves {k : Int} {H : Hook → Prop} {X Y : St σ} (h : Grows (Calls k H) X Y) :
    ∃ v, Y.log = X.log ++ v ∧ v.countP Ev.isSave = 0 :=
  let ⟨u, e, pu⟩ := h
  ⟨u, e, saves_calls fun e he => let ⟨g, b, h, _⟩ := pu e he; ⟨k, g, b, h⟩⟩

/-- (3, 6) A request saves at most one form: the submitted form of the
player's position, if that page has fields. Back saves only from the
tolerance window on, as a timed-out submission (5). -/
theorem step_saves (now : Nat) (r : Req F) (s : St σ) (h1 : -1 ≤ s.pos) (hn : s.pos ≤ A.n) :
    ∃ u, (A.step now r s).log = s.log ++ u ∧ u.countP Ev.isSave ≤ 1 ∧
      (u.countP Ev.isSave = 1 → ∃ back f, r.submission s.pos = some (back, f) ∧ 0 ≤ s.pos ∧
        A.hasForm s.pos = true ∧ (back = true → ∃ t, s.deadline s.pos = some t ∧ t ≤ now + A.tolerance)) := by
  simp only [App.step, arm_log]
  by_cases hk : s.pos = -1
  · unfold App.respond; dsimp only; rw [ite_yes hk]
    split
    · obtain ⟨sh, hend, -⟩ := visit_ends A 0 true none
        { s with started := true, app := A.start s.app, log := s.log ++ [.init] } (Int.le_refl 0) (by omega)
      obtain ⟨v, e, hv⟩ := Ends.saves A hend
      exact ⟨.init :: v, by simp [e], by simp [hv, Ev.isSave], by simp [hv, Ev.isSave]⟩
    · exact ⟨[.display (-1) .fresh], rfl, by simp [Ev.isSave], by simp [Ev.isSave]⟩
  · have h0 : 0 ≤ s.pos := by omega
    have ⟨ft, gt⟩ := timedOut_spec A now s.pos s
    have hfired := fun h => timedOut_fired A (now := now) (k := s.pos) (s := s) h
    obtain ⟨vt, et, ct⟩ := Grows.saves gt
    have hk1 : s.pos ≤ (A.timedOut now s.pos s).2.pos ∧ (A.timedOut now s.pos s).2.pos ≤ A.n := by
      unfold App.Fwd at ft; omega
    unfold App.respond; dsimp only
    rw [ite_not hk, ite_not (by omega)]
    generalize A.timedOut now s.pos s = t at *
    split
    · next hsub =>
      have : ∃ v, (if t.1 = true then A.proceed s.pos t.2 else A.load s.pos t.2).log =
          t.2.log ++ v ∧ v.countP Ev.isSave = 0 := by
        split
        · exact Ends.saves A (proceed_ends A _ _ h0 hn hk1.2).1
        · exact Ends.saves A (load_ends A _ _ h0 hk1.1 hk1.2)
      obtain ⟨v, e, cv⟩ := this
      exact ⟨vt ++ v, by simp [e, et], by simp [List.countP_append, ct, cv], by simp [List.countP_append, ct, cv]⟩
    · next back f hsub =>
      obtain ⟨fa, va, ea, -, ca⟩ := accept_spec A s.pos f t.2
      have hk2 : s.pos ≤ (A.accept s.pos f t.2).2.pos ∧ (A.accept s.pos f t.2).2.pos ≤ A.n := by
        unfold App.Fwd at fa; omega
      have key : ∀ {Y : St σ} {v : List Ev}, Y.log = (A.accept s.pos f t.2).2.log ++ v →
          v.countP Ev.isSave = 0 → (back = true → t.1 = true) →
          ∃ u, Y.log = s.log ++ u ∧ u.countP Ev.isSave ≤ 1 ∧
            (u.countP Ev.isSave = 1 → ∃ back' f', r.submission s.pos = some (back', f') ∧ 0 ≤ s.pos ∧
              A.hasForm s.pos = true ∧ (back' = true → ∃ t, s.deadline s.pos = some t ∧ t ≤ now + A.tolerance)) := by
        intro Y v e cv hb
        refine ⟨vt ++ va ++ v, by simp [e, ea, et], ?_, fun h1 => ⟨back, f, hsub, h0, ?_, fun hb' => hfired (hb hb')⟩⟩
        · simp only [List.countP_append, ct, cv, ca]; split <;> omega
        · simp only [List.countP_append, ct, cv, ca] at h1
          split at h1
          · next hh => exact hh.1
          · omega
      split
      · next hf => obtain ⟨v, e, cv⟩ := Ends.saves A (proceed_ends A _ _ h0 hn hk2.2).1
                   exact key e cv fun _ => hf
      · next hf =>
        split
        · obtain ⟨v, e, cv⟩ := Ends.saves A (goBack_ends A _ _ h0 hn hk1.1 hk1.2)
          exact ⟨vt ++ v, by simp [e, et], by simp [List.countP_append, ct, cv],
            by simp [List.countP_append, ct, cv]⟩
        · next hb =>
          have hb' : back = true → t.1 = true := fun h => absurd h hb
          have fm := call_fwd A .mayProceed s.pos (A.accept s.pos f t.2).2 default
          obtain ⟨vm, em, cm⟩ := Grows.saves (call_calls A .mayProceed s.pos (A.accept s.pos f t.2).2 default)
          have hk3 : s.pos ≤ (A.call .mayProceed s.pos (A.accept s.pos f t.2).2).2.pos ∧
              (A.call .mayProceed s.pos (A.accept s.pos f t.2).2).2.pos ≤ A.n := by
            unfold App.Fwd at fm; omega
          split
          · split
            · obtain ⟨v, e, cv⟩ := Ends.saves A (proceed_ends A _ _ h0 hn hk3.2).1
              exact key (v := vm ++ v) (by rw [e, em, List.append_assoc]) (by simp [List.countP_append, cm, cv]) hb'
            · obtain ⟨sh, hend, -⟩ := stay_ends A s.pos .kept _ h0 hk3.1 hk3.2
              obtain ⟨v, e, cv⟩ := Ends.saves A hend
              exact key (v := vm ++ v) (by rw [e, em, List.append_assoc]) (by simp [List.countP_append, cm, cv]) hb'
          · obtain ⟨sh, hend, -⟩ := stay_ends A s.pos .errors _ h0 hk2.1 hk2.2
            obtain ⟨v, e, cv⟩ := Ends.saves A hend
            exact key e cv hb'

/-- (5) Once the deadline has passed, every request leaves the page:
`timeout_reached` runs, `may_proceed` is not asked, and a later position is
displayed with a fresh form, i.e., without errors. -/
theorem step_timeout (now : Nat) (r : Req F) (s : St σ) (t : Nat) (h0 : 0 ≤ s.pos) (hn : s.pos < A.n)
    (ht : s.deadline s.pos = some t) (hp : t ≤ now) :
    s.pos < (A.step now r s).pos ∧
      ∃ u, (A.step now r s).log = s.log ++ u ++ [.display (A.step now r s).pos .fresh] ∧
        (∀ e ∈ u, ∀ q b, e ≠ .call q .mayProceed b) ∧
        (A.defines s.pos .timeoutReached = true → ∃ b, Ev.call s.pos .timeoutReached b ∈ u) := by
  simp only [App.step, arm_log, arm_pos]
  unfold App.respond; dsimp only
  rw [ite_not (by omega), ite_not (by omega), timedOut_passed A now s.pos s t ht hp]
  obtain ⟨vx, ex, px, dx⟩ : ∃ v, (A.call .timeoutReached s.pos s).2.log = s.log ++ v ∧
      (∀ e ∈ v, ∃ b, e = .call s.pos .timeoutReached b) ∧
      (A.defines s.pos .timeoutReached = true → ∃ b, Ev.call s.pos .timeoutReached b ∈ v) := by
    cases hd : A.defines s.pos .timeoutReached
    · exact ⟨[], by rw [call_undef A hd]; simp, by simp, by simp⟩
    · exact ⟨_, call_log_def A hd, by simp, fun _ => ⟨(A.call .timeoutReached s.pos s).1, by simp⟩⟩
  have fx := call_fwd A .timeoutReached s.pos s default
  generalize A.call .timeoutReached s.pos s = x at *
  have hx : s.pos ≤ x.2.pos ∧ x.2.pos ≤ A.n := by unfold App.Fwd at fx; omega
  have nav : ∀ e, CallOf (fun g : Hook => g.nav = true ∨ g = .afterOnce) e → ∀ q b, e ≠ .call q .mayProceed b :=
    fun e ⟨q', g, b', he, hg⟩ q b h => by subst he; cases h; simp [Hook.nav] at hg
  dsimp only
  split
  · obtain ⟨⟨w, ew, pw, -⟩, hlt⟩ := proceed_ends A s.pos x.2 h0 (by omega) hx.2
    refine ⟨hlt hn, vx ++ w, by simp [ew, ex], fun e he q b => ?_, fun hd => ?_⟩
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨b', rfl⟩ := px e he; simp
      · exact nav e (pw e he) q b
    · obtain ⟨b, hb⟩ := dx hd; exact ⟨b, List.mem_append_left _ hb⟩
  · next back f _ =>
    obtain ⟨fa, va, ea, pa, -⟩ := accept_spec A s.pos f x.2
    have ha : s.pos ≤ (A.accept s.pos f x.2).2.pos ∧ (A.accept s.pos f x.2).2.pos ≤ A.n := by
      unfold App.Fwd at fa; omega
    obtain ⟨⟨w, ew, pw, -⟩, hlt⟩ := proceed_ends A s.pos _ h0 (by omega) ha.2
    refine ⟨hlt hn, vx ++ va ++ w, by simp [ew, ea, ex], fun e he q b => ?_, fun hd => ?_⟩
    · simp only [List.mem_append] at he
      rcases he with (he | he) | he
      · obtain ⟨b', rfl⟩ := px e he; simp
      · rcases pa e he with ⟨g, b', rfl, hg⟩ | ⟨fs, rfl⟩
        · intro h; cases h; rcases hg with h | h | h <;> cases h
        · simp
      · exact nav e (pw e he) q b
    · obtain ⟨b, hb⟩ := dx hd; exact ⟨b, by simp [hb]⟩

theorem last_eq {l l' : List Ev} {a b : Ev} (h : l ++ [a] = l' ++ [b]) : a = b := by
  have := congrArg List.getLast? h; simpa using this

/-- How a request ends: the form that it displays is fresh, unless the player
stays at the position of a submitted form, which was not timed out. -/
theorem respond_shown (now : Nat) (r : Req F) (s : St σ) (h1 : -1 ≤ s.pos) (hn : s.pos ≤ A.n) :
    ∃ u sh, (A.respond now r s).log = s.log ++ u ++ [.display (A.respond now r s).pos sh] ∧
      (sh = .fresh ∨ ((A.respond now r s).pos = s.pos ∧
        ∃ f, r.submission s.pos = some (false, f) ∧ (A.timedOut now s.pos s).1 = false)) := by
  have fresh : ∀ {P : Ev → Prop} {Y : St σ}, A.Ends P s Y .fresh → ∃ u sh, Y.log = s.log ++ u ++ [.display Y.pos sh] ∧
      (sh = .fresh ∨ (Y.pos = s.pos ∧ ∃ f, r.submission s.pos = some (false, f) ∧ (A.timedOut now s.pos s).1 = false)) :=
    fun ⟨u, e, _⟩ => ⟨u, .fresh, e, .inl rfl⟩
  have fresh' : ∀ {P : Ev → Prop} {X Y : St σ} {sh} {d : Option Shown} {c : Int}, Grows P s X → A.Ends P X Y sh →
      (sh = .fresh ∨ (Y.pos = c ∧ d = some sh)) → d = none → ∃ u sh, Y.log = s.log ++ u ++ [.display Y.pos sh] ∧
      (sh = .fresh ∨ (Y.pos = s.pos ∧ ∃ f, r.submission s.pos = some (false, f) ∧ (A.timedOut now s.pos s).1 = false)) :=
    fun g h hsh hd => by
      obtain ⟨u, e, -⟩ := Ends.pre A g h
      exact ⟨u, _, e, .inl (by rcases hsh with h | ⟨-, h⟩ <;> simp_all)⟩
  by_cases hk : s.pos = -1
  · unfold App.respond; dsimp only; rw [ite_yes hk]
    split
    · obtain ⟨sh, hend, hsh, -⟩ := visit_ends A 0 true none
        { s with started := true, app := A.start s.app, log := s.log ++ [.init] } (Int.le_refl 0) (by omega)
      exact fresh' (P := fun _ => True) (Grows.mono (⟨[.init], rfl, by simp⟩ : Grows (· = .init) s _) fun _ _ => trivial)
        (Ends.mono A hend fun _ _ => trivial) hsh rfl
    · exact ⟨[], .fresh, by simp [St.display, hk], .inl rfl⟩
  · have h0 : 0 ≤ s.pos := by omega
    have ⟨ft, gt⟩ := timedOut_spec A now s.pos s
    have gt' := gt.mono fun _ h => Calls.rec h
    have hk1 : s.pos ≤ (A.timedOut now s.pos s).2.pos ∧ (A.timedOut now s.pos s).2.pos ≤ A.n := by
      unfold App.Fwd at ft; omega
    unfold App.respond; dsimp only
    rw [ite_not hk, ite_not (by omega)]
    split
    · split
      · exact fresh (Ends.pre A gt' (Ends.mono A (proceed_ends A _ _ h0 hn hk1.2).1 fun _ h => h.rec))
      · exact fresh (Ends.pre A gt' (Ends.mono A (load_ends A _ _ h0 hk1.1 hk1.2) fun _ h => h.rec))
    · next back f hsub =>
      obtain ⟨fa, va, ea, pa, -⟩ := accept_spec A s.pos f (A.timedOut now s.pos s).2
      have ga : Grows Rec (A.timedOut now s.pos s).2 (A.accept s.pos f (A.timedOut now s.pos s).2).2 :=
        ⟨va, ea, fun e he => (pa e he).elim Calls.rec fun ⟨fs, h⟩ => .inr (.inr ⟨_, fs, h⟩)⟩
      have ga' := Grows.trans gt' ga (fun _ h => h) (fun _ h => h)
      have hk2 : s.pos ≤ (A.accept s.pos f (A.timedOut now s.pos s).2).2.pos ∧
          (A.accept s.pos f (A.timedOut now s.pos s).2).2.pos ≤ A.n := by
        unfold App.Fwd at fa; omega
      split
      · exact fresh (Ends.pre A ga' (Ends.mono A (proceed_ends A _ _ h0 hn hk2.2).1 fun _ h => h.rec))
      · next hf =>
        split
        · exact fresh (Ends.pre A gt' (Ends.mono A (goBack_ends A _ _ h0 hn hk1.1 hk1.2) fun _ h => h.rec))
        · next hb =>
          have hb' : back = false := by simpa using hb
          subst hb'
          have hf' : (A.timedOut now s.pos s).1 = false := by simpa using hf
          have fm := call_fwd A .mayProceed s.pos (A.accept s.pos f (A.timedOut now s.pos s).2).2 default
          have gm := (call_calls A .mayProceed s.pos (A.accept s.pos f (A.timedOut now s.pos s).2).2 default).mono
            fun _ h => Calls.rec h
          have hk3 : s.pos ≤ (A.call .mayProceed s.pos (A.accept s.pos f (A.timedOut now s.pos s).2).2).2.pos ∧
              (A.call .mayProceed s.pos (A.accept s.pos f (A.timedOut now s.pos s).2).2).2.pos ≤ A.n := by
            unfold App.Fwd at fm; omega
          split
          · split
            · exact fresh (Ends.pre A ga' (Ends.pre A gm
                (Ends.mono A (proceed_ends A _ _ h0 hn hk3.2).1 fun _ h => h.rec)))
            · obtain ⟨sh, hend, hsh⟩ := stay_ends A s.pos .kept _ h0 hk3.1 hk3.2
              obtain ⟨u, e, -⟩ := Ends.pre A ga' (Ends.pre A gm (Ends.mono A hend fun _ h => h.rec))
              exact ⟨u, sh, e, hsh.imp_right fun ⟨hp, _⟩ => ⟨hp, f, hsub, hf'⟩⟩
          · obtain ⟨sh, hend, hsh⟩ := stay_ends A s.pos .errors _ h0 hk2.1 hk2.2
            obtain ⟨u, e, -⟩ := Ends.pre A ga' (Ends.mono A hend fun _ h => h.rec)
            exact ⟨u, sh, e, hsh.imp_right fun ⟨hp, _⟩ => ⟨hp, f, hsub, hf'⟩⟩

/-- (4) A page displays the submitted values, and errors, only if the player
stays at the position whose form they submitted, before its deadline. -/
theorem step_errors (now : Nat) (r : Req F) (s : St σ) (h1 : -1 ≤ s.pos) (hn : s.pos ≤ A.n)
    (u : List Ev) (sh : Shown) (e : (A.step now r s).log = s.log ++ u ++ [.display (A.step now r s).pos sh])
    (hsh : sh ≠ .fresh) :
    (A.step now r s).pos = s.pos ∧ ∃ f, r.submission s.pos = some (false, f) ∧ (A.timedOut now s.pos s).1 = false := by
  simp only [App.step, arm_log, arm_pos] at e ⊢
  obtain ⟨u', sh', e', h⟩ := respond_shown A now r s h1 hn
  have : sh = sh' := by
    have := last_eq (e.symm.trans e'); cases this; rfl
  subst this
  exact h.resolve_left hsh

/-- (6) Back, before the tolerance window, saves nothing and asks neither
`may_proceed` nor `after_once`. -/
theorem step_back (now : Nat) (r : Req F) (s : St σ) (f : F) (h0 : 0 ≤ s.pos) (hn : s.pos ≤ A.n)
    (hb : r.submission s.pos = some (true, f)) (hd : ∀ t, s.deadline s.pos = some t → now + A.tolerance < t) :
    ∃ u, (A.step now r s).log = s.log ++ u ∧
      ∀ e ∈ u, e.isSave = false ∧ ∀ q b, e ≠ .call q .mayProceed b ∧ e ≠ .call q .afterOnce b := by
  simp only [App.step, arm_log]
  unfold App.respond; dsimp only
  rw [ite_not (by omega), ite_not (by omega), timedOut_far A now s.pos s hd, hb]
  dsimp only
  obtain ⟨w, ew, pw, -⟩ := goBack_ends A s.pos s h0 hn (Int.le_refl _) hn
  refine ⟨w ++ [.display (A.goBack s.pos s).pos .fresh], by simp [ew], fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · obtain ⟨q', g, b', rfl, hg⟩ := pw e he
    refine ⟨rfl, fun q b => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> cases h <;> simp [Hook.nav] at hg
  · simp at he; subst he; simp [Ev.isSave]

/-! ### Moves -/

/-- What a hook does to the position and the ghost `moved`: nothing, or it
moves the player forward and `moved` becomes the furthest move. -/
def Mv (s s' : St σ) : Prop :=
  (s'.pos = s.pos ∧ s'.moved = s.moved) ∨
    (0 ≤ s.pos ∧ s.pos < s'.pos ∧ s'.moved = if s.moved < s'.pos then s'.pos else s.moved)

theorem call_mv (h p s f) : Mv s (A.call h p s f).2 := by
  unfold App.call; split
  · dsimp only
    rcases moveTo_cases A s.pos (A.run p h f s.app).2.2 with e | ⟨h0, hlt, -⟩
    · left; simp [e]
    · right; exact ⟨h0, hlt, by simp [hlt]⟩
  · left; simp

theorem once_mv (h p again s) : Mv s (A.once h p again s) := by
  unfold App.once; split
  · exact call_mv A _ _ _ _
  · left; simp

/-- While a request at `k` runs, `moved` is at most the position, which is at
least `k`, and if the player is still at `k`, no hook has moved them. -/
def J (k : Int) (s : St σ) : Prop := s.moved ≤ s.pos ∧ k ≤ s.pos ∧ (s.pos = k → s.moved < 0)

theorem J.mv {k : Int} {s s' : St σ} (hj : J k s) (h : Mv s s') : J k s' := by
  unfold J Mv at *; rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · omega
  · split at h3 <;> omega

/-- Navigation from `c` ends at the furthest move or beyond, if it starts there. -/
theorem visit_moved (c : Int) (again d s) (hm : s.moved ≤ c) (hn : c ≤ A.n) :
    (A.visit c again d s).moved ≤ (A.visit c again d s).pos := by
  have I : ∀ {s s' : St σ}, s.moved ≤ s.pos → Mv s s' → s'.moved ≤ s'.pos := fun h hm => by
    unfold Mv at hm; rcases hm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · omega
    · split at h3 <;> omega
  have ask_mv : ∀ c d s, Mv s (A.ask c d s).2 := fun c d s => by
    unfold App.ask; split
    · left; simp
    · exact call_mv A _ _ _ _
  fun_induction A.visit c again d s with
  | case1 c again d s hc s1 s2 =>
    simp only [display_pos]
    have : s.moved ≤ A.n := by omega
    exact I (I (I (show ({ s with pos := (A.n : Int) } : St σ).moved ≤ _ from this) (once_mv A _ _ _ _))
      (once_mv A _ _ _ _)) (once_mv A _ _ _ _)
  | case2 c again d s hc s1 s2 h1 ih =>
    have i2 : s2.moved ≤ s2.pos :=
      I (I (show ({ s with pos := c } : St σ).moved ≤ _ from hm) (once_mv A _ _ _ _)) (once_mv A _ _ _ _)
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    exact ih i2 (by omega)
  | case3 c again d s hc s1 s2 h1 r s3 h2 ih =>
    have i3 : s3.moved ≤ s3.pos := I (I (I (show ({ s with pos := c } : St σ).moved ≤ _ from hm)
      (once_mv A _ _ _ _)) (once_mv A _ _ _ _)) (ask_mv _ _ _)
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    exact ih i3 (by omega)
  | case4 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 ih =>
    have i4 : s4.moved ≤ s4.pos := I (I (I (I (show ({ s with pos := c } : St σ).moved ≤ _ from hm)
      (once_mv A _ _ _ _)) (once_mv A _ _ _ _)) (ask_mv _ _ _)) (once_mv A _ _ _ _)
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    have p4 : s4.pos = s3.pos ∨ (0 ≤ s3.pos ∧ s3.pos < s4.pos ∧ s4.pos ≤ A.n) := once_pos A _ _ _ _
    exact ih i4 (by omega)
  | case5 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 =>
    simp only [display_pos]
    exact I (I (I (I (show ({ s with pos := c } : St σ).moved ≤ _ from hm)
      (once_mv A _ _ _ _)) (once_mv A _ _ _ _)) (ask_mv _ _ _)) (once_mv A _ _ _ _)
  | case6 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    have i4 : s4.moved ≤ s4.pos := I (I (I (I (show ({ s with pos := c } : St σ).moved ≤ _ from hm)
      (once_mv A _ _ _ _)) (once_mv A _ _ _ _)) (ask_mv _ _ _)) (once_mv A _ _ _ _)
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    have p4 : s4.pos = s3.pos ∨ (0 ≤ s3.pos ∧ s3.pos < s4.pos ∧ s4.pos ≤ A.n) := once_pos A _ _ _ _
    exact ih i4 (by omega)
  | case7 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    have i4 : s4.moved ≤ s4.pos := I (I (I (I (show ({ s with pos := c } : St σ).moved ≤ _ from hm)
      (once_mv A _ _ _ _)) (once_mv A _ _ _ _)) (ask_mv _ _ _)) (once_mv A _ _ _ _)
    have p1 : s1.pos = c ∨ (0 ≤ c ∧ c < s1.pos ∧ s1.pos ≤ A.n) := once_pos A _ _ _ _
    have p2 : s2.pos = s1.pos ∨ (0 ≤ s1.pos ∧ s1.pos < s2.pos ∧ s2.pos ≤ A.n) := once_pos A _ _ _ _
    have p3 : s3.pos = s2.pos ∨ (0 ≤ s2.pos ∧ s2.pos < s3.pos ∧ s3.pos ≤ A.n) := ask_pos A _ _ _
    have p4 : s4.pos = s3.pos ∨ (0 ≤ s3.pos ∧ s3.pos < s4.pos ∧ s4.pos ≤ A.n) := once_pos A _ _ _ _
    exact ih (by omega) (by omega)

theorem leave_moved (k : Int) (s : St σ) (hj : J k s) (hn : k < A.n) (hs : s.pos ≤ A.n) :
    (A.leave k s).moved ≤ (A.leave k s).pos := by
  unfold App.leave; dsimp only
  have j2 := (hj.mv (once_mv A .afterOnce k false s)).mv (once_mv A .afterAlwaysOnce k false _)
  have f := Fwd.trans A (once_fwd A .afterOnce k false s) (once_fwd A .afterAlwaysOnce k false _)
  generalize A.once .afterAlwaysOnce k false (A.once .afterOnce k false s) = s2 at j2 f
  unfold J at j2; unfold App.Fwd at f
  apply visit_moved A _ _ _ _ <;> split <;> omega

theorem load_moved (k : Int) (s : St σ) (hj : J k s) (hs : s.pos ≤ A.n) :
    (A.load k s).moved ≤ (A.load k s).pos := by
  unfold J at hj; unfold App.load; split
  · exact visit_moved A _ _ _ _ (by omega) hs
  · exact visit_moved A _ _ _ _ (by omega) (by omega)

theorem stay_moved (k : Int) (d : Shown) (s : St σ) (hj : J k s) (hs : s.pos ≤ A.n) :
    (A.stay k d s).moved ≤ (A.stay k d s).pos := by
  unfold J at hj; unfold App.stay; split
  · exact visit_moved A _ _ _ _ (by omega) hs
  · exact visit_moved A _ _ _ _ (by omega) (by omega)

theorem proceed_moved (k : Int) (s : St σ) (hj : J k s) (hn : k ≤ A.n) (hs : s.pos ≤ A.n) :
    (A.proceed k s).moved ≤ (A.proceed k s).pos := by
  unfold App.proceed; split
  · exact leave_moved A k s hj (by omega) hs
  · unfold J at hj; exact visit_moved A _ _ _ _ (by omega) hn

theorem back_moved (k j : Int) (s : St σ) (hm : s.moved < 0) (hj : j < k) (h0 : 0 ≤ k) (hn : k ≤ A.n) :
    (A.back k j s).moved ≤ (A.back k j s).pos := by
  fun_induction A.back k j s with
  | case1 j s => exact stay_moved A k .fresh _ ⟨by simp; omega, by simp, fun _ => hm⟩ hn
  | case2 j s => exact stay_moved A k .fresh _ ⟨by simp; omega, by simp, fun _ => hm⟩ hn
  | case3 j s hj0 _ r hlt =>
    have hm' : Mv { s with pos := j } r.2 := call_mv A .show j { s with pos := j } default
    have f : A.Fwd { s with pos := j } r.2 := call_fwd A .show j { s with pos := j } default
    unfold Mv at hm'; unfold App.Fwd at f; simp only at hm' f
    have hle : r.2.pos ≤ A.n := by omega
    have hmv : r.2.moved ≤ r.2.pos := by
      rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · omega
      · split at h3 <;> omega
    exact visit_moved A _ _ _ _ hmv hle
  | case4 j s hj0 _ r hlt _ =>
    have hm' : Mv { s with pos := j } r.2 := call_mv A .show j { s with pos := j } default
    unfold Mv at hm'; simp only at hm'
    have hmv : r.2.moved ≤ j := by
      rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · omega
      · omega
    exact visit_moved A _ _ _ _ hmv (by omega)
  | case5 j s hj0 _ r hlt _ ih =>
    have hm' : Mv { s with pos := j } r.2 := call_mv A .show j { s with pos := j } default
    unfold Mv at hm'; simp only at hm'
    have hmv : r.2.moved < 0 := by
      rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · omega
      · omega
    exact ih hmv (by omega)

theorem goBack_moved (k : Int) (s : St σ) (hj : J k s) (h0 : 0 ≤ k) (hn : k ≤ A.n) (hs : s.pos ≤ A.n) :
    (A.goBack k s).moved ≤ (A.goBack k s).pos := by
  unfold App.goBack; dsimp only
  have j1 := hj.mv (call_mv A .allowBack k s default)
  have f := call_fwd A .allowBack k s default
  generalize A.call .allowBack k s = r at j1 f
  have hle : r.2.pos ≤ A.n := by unfold App.Fwd at f; omega
  split
  · unfold J at j1; exact visit_moved A _ _ _ _ (by omega) hle
  · split
    · unfold J at j1; exact back_moved A k (k - 1) r.2 (j1.2.2 (by omega)) (by omega) h0 hn
    · exact stay_moved A k .fresh r.2 j1 hle

theorem stealth_mv (k f s) : Mv s (A.stealth k f s).2 := by
  unfold App.stealth; split
  · exact call_mv A _ _ _ _
  · left; simp

theorem accept_J (k : Int) (f : F) (s : St σ) (hj : J k s) : J k (A.accept k f s).2 := by
  unfold App.accept; dsimp only
  split
  · split
    · have j1 := hj.mv (call_mv A .validate k s f)
      split
      · have j2 := j1.mv (stealth_mv A k f _)
        split
        · have j3 := j2.mv (call_mv A .beforeFormSave k _ f)
          exact j3
        · exact j2
      · exact j1
    · exact hj
  · exact hj

theorem timedOut_J (now : Nat) (k : Int) (s : St σ) (hj : J k s) : J k (A.timedOut now k s).2 := by
  unfold App.timedOut; split
  · exact hj
  · next t _ =>
    dsimp only
    have j1 : J k (A.fires now t k s).2 := by
      unfold App.fires; split
      · exact hj
      · split
        · exact hj
        · exact hj.mv (call_mv A _ _ _ _)
    split
    · exact j1.mv (call_mv A _ _ _ _)
    · exact j1

omit [Inhabited F] in
@[simp] theorem arm_moved (now s) : (A.arm now s).moved = s.moved := by
  unfold App.arm; split <;> (try split) <;> rfl

/-- (7) A move is never lost: a request ends at the furthest position that a
hook moved the player to during the request, or beyond. (`moved` starts the
request at `-1`, so that it records only this request's moves.) -/
theorem step_moves (now : Nat) (r : Req F) (s : St σ) (h1 : -1 ≤ s.pos) (hn : s.pos ≤ A.n) :
    (A.step now r { s with moved := -1 }).moved ≤ (A.step now r { s with moved := -1 }).pos := by
  simp only [App.step, arm_moved, arm_pos]
  unfold App.respond; dsimp only
  by_cases hk : s.pos = -1
  · rw [ite_yes hk]
    split
    · exact visit_moved A _ _ _ _ (by simp) (by omega)
    · simp [St.display, hk]
  · rw [ite_not hk, ite_not (by omega)]
    have h0 : 0 ≤ s.pos := by omega
    have j0 : J s.pos { s with moved := -1 } := ⟨by simp; omega, by simp, fun _ => by simp⟩
    have jt := timedOut_J A now s.pos _ j0
    have ft := (timedOut_spec A now s.pos { s with moved := -1 }).1
    have ht : (A.timedOut now s.pos { s with moved := -1 }).2.pos ≤ A.n := by
      unfold App.Fwd at ft; simp at ft; omega
    generalize A.timedOut now s.pos { s with moved := -1 } = t at jt ft ht
    split
    · split
      · exact proceed_moved A _ _ jt hn ht
      · exact load_moved A _ _ jt ht
    · next back f _ =>
      have ja := accept_J A s.pos f t.2 jt
      have fa := (accept_spec A s.pos f t.2).1
      have ha : (A.accept s.pos f t.2).2.pos ≤ A.n := by unfold App.Fwd at fa; omega
      split
      · exact proceed_moved A _ _ ja hn ha
      · split
        · exact goBack_moved A _ _ jt h0 hn ht
        · have jm := ja.mv (call_mv A .mayProceed s.pos (A.accept s.pos f t.2).2 default)
          have fm := call_fwd A .mayProceed s.pos (A.accept s.pos f t.2).2 default
          have hm : (A.call .mayProceed s.pos (A.accept s.pos f t.2).2).2.pos ≤ A.n := by
            unfold App.Fwd at fm; omega
          split
          · split
            · exact proceed_moved A _ _ jm hn hm
            · exact stay_moved A _ _ _ jm hm
          · exact stay_moved A _ _ _ ja ha

/-! ### Navigation without moves

When no hook moves the player, navigation is exactly as principles 1 and 6
describe. -/

/-- No hook moves the player. -/
def App.Still : Prop := ∀ p h f a, (A.run p h f a).2.2 = none

section Still
variable {A} (hst : A.Still)
include hst

theorem call_still (h p s f) : (A.call h p s f).2.pos = s.pos := by
  unfold App.call; split
  · simp only; rw [hst]; rfl
  · rfl

theorem once_still (h p again s) : (A.once h p again s).pos = s.pos := by
  unfold App.once; split
  · exact call_still hst _ _ _ _
  · rfl

theorem ask_still (c d s) : (A.ask c d s).2.pos = s.pos := by
  unfold App.ask; split
  · rfl
  · exact call_still hst _ _ _ _

omit hst in
theorem ask_log (c : Int) (s : St σ) : (A.ask c none s).2.log =
    s.log ++ (if A.defines c .show = true then [.call c .show (A.ask c none s).1] else []) := by
  cases hd : A.defines c .show
  · simp [App.ask, call_undef A hd]
  · simp [App.ask, call_log_def A hd]

omit hst in
theorem ask_undef {c : Int} {s : St σ} (hd : A.defines c .show = false) : (A.ask c none s).1 = true := by
  simp [App.ask, call_undef A hd, Hook.default]

/-- (1, 2) Forward navigation from `c` displays the first position from `c` on
whose page is shown. On its way, it enters every position (`before_always_once`)
and skips it (`show()` is false, `after_always_once`). -/
theorem visit_still (c : Int) (again : Bool) (d : Option Shown) (s : St σ) (hd : d = none)
    (h0 : 0 ≤ c) (hn : c ≤ A.n) :
    ∃ u, (A.visit c again d s).log = s.log ++ u ∧ c ≤ (A.visit c again d s).pos ∧
      (∀ j, c ≤ j → j < (A.visit c again d s).pos → Ev.call j .show false ∈ u ∧
        (A.defines j .beforeAlwaysOnce = true → (j, .beforeAlwaysOnce) ∈ (A.visit c again d s).ran) ∧
        (A.defines j .afterAlwaysOnce = true → (j, .afterAlwaysOnce) ∈ (A.visit c again d s).ran)) ∧
      ((A.visit c again d s).pos < A.n → A.defines (A.visit c again d s).pos .show = true →
        Ev.call (A.visit c again d s).pos .show true ∈ u) := by
  have lg := logGrows A
  have p2 : ∀ (s : St σ) (c : Int) (again : Bool),
      (A.once .beforeAlwaysOnce c false (A.once .early c again { s with pos := c })).pos = c :=
    fun s c again => by rw [once_still hst, once_still hst]
  fun_induction A.visit c again d s with
  | case1 c again d s hc s1 s2 =>
    obtain ⟨u, e⟩ := lg.trans (lg.trans (lg.trans (lg.pos s A.n) (lg.once _ _ again _ (by simp [Hook.once])))
      (lg.once _ _ _ _ fun _ => rfl)) (lg.trans (lg.once .beforeOnce A.n false s2 fun _ => rfl) (lg.display _ _ _))
    have hp : (A.once .beforeOnce (↑A.n) false s2).pos = A.n := by
      rw [once_still hst]; exact p2 s _ again
    refine ⟨u, e, ?_, fun j h1 h2 => ?_, fun h => ?_⟩ <;> simp only [display_pos, hp] at * <;> omega
  | case2 c again d s hc s1 s2 h1 ih => exact absurd h1 (by rw [p2]; omega)
  | case3 c again d s hc s1 s2 h1 r s3 h2 ih =>
    exact absurd h2 (by simp only [s3, r]; rw [ask_still hst, p2]; omega)
  | case4 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 ih =>
    exact absurd h3 (by simp only [s4, s3, r]; rw [once_still hst, ask_still hst, p2]; omega)
  | case5 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 =>
    subst hd
    have hp : s4.pos = c := by simp only [s4, s3, r]; rw [once_still hst, ask_still hst, p2]
    obtain ⟨u1, e1⟩ := lg.trans (lg.pos s c) (lg.trans (lg.once .early c again _ (by simp [Hook.once]))
      (lg.once .beforeAlwaysOnce c false _ fun _ => rfl))
    obtain ⟨u3, e3⟩ := lg.trans (lg.once .beforeOnce c false s3 fun _ => rfl) (lg.display s4 c (Shown.fresh))
    have e2 := ask_log (A := A) c s2
    simp only [Option.getD_none, display_pos, hp]
    refine ⟨u1 ++ (if A.defines c .show = true then [.call c .show true] else []) ++ u3, ?_, Int.le_refl _,
      fun j h1 h2 => by omega, fun _ hd => by simp [hd]⟩
    have e1' : s2.log = s.log ++ u1 := e1
    rw [e3]; simp only [s3, r] at hr ⊢; rw [e2, e1', hr]; simp
  | case6 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    exact absurd h4 (by simp only [s4, s3, r]; rw [once_still hst, ask_still hst, p2]; omega)
  | case7 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    subst hd
    obtain ⟨u', e', hle, hint, hshow⟩ := ih rfl (by omega) (by omega)
    have hr' : (A.ask c none s2).1 = false := by simpa [r] using hr
    have hdef : A.defines c .show = true := by
      cases h : A.defines c .show
      · rw [ask_undef h] at hr'; cases hr'
      · rfl
    obtain ⟨u1, e1⟩ := lg.trans (lg.pos s c) (lg.trans (lg.once .early c again _ (by simp [Hook.once]))
      (lg.once .beforeAlwaysOnce c false _ fun _ => rfl))
    have e1' : s2.log = s.log ++ u1 := e1
    have e2 : s3.log = s2.log ++ [.call c .show false] := by
      simp only [s3, r]; rw [ask_log, hr']; simp [hdef]
    obtain ⟨u3, e3⟩ := lg.once .afterAlwaysOnce c false s3 fun _ => rfl
    have e3' : s4.log = s3.log ++ u3 := e3
    have ran := fun x hx => (ranGrows A).visit (c + 1) true none s4 x hx
    refine ⟨u1 ++ [.call c .show false] ++ u3 ++ u', by rw [e', e3', e2, e1']; simp, by omega,
      fun j hj1 hj2 => ?_, fun hP hd' => by simp [hshow hP hd']⟩
    by_cases hj : j = c
    · subst hj
      refine ⟨by simp, fun hd => ran _ ?_, fun hd => ran _ (once_mem A _ _ _ _ hd)⟩
      exact once_ran A _ _ _ _ _ (by simpa [s3, r] using once_mem A .beforeAlwaysOnce j false s1 hd)
    · obtain ⟨h1, h2, h3⟩ := hint j (by omega) hj2
      exact ⟨by simp [h1], h2, h3⟩

/-- Displaying `c` (staying, or landing after Back) enters `c` and displays it. -/
theorem visit_some_still (c : Int) (again : Bool) (d : Option Shown) (s : St σ) (hd : d.isSome)
    (h0 : 0 ≤ c) (hn : c ≤ A.n) :
    (A.visit c again d s).pos = c ∧ ∃ u, (A.visit c again d s).log = s.log ++ u ∧
      ∀ e ∈ u, (∃ g b, e = .call c g b ∧ (g = .early ∨ g = .beforeAlwaysOnce ∨ g = .beforeOnce)) ∨
        ∃ sh, e = .display c sh := by
  have p2 : ∀ (s : St σ) (c : Int) (again : Bool),
      (A.once .beforeAlwaysOnce c false (A.once .early c again { s with pos := c })).pos = c :=
    fun s c again => by rw [once_still hst, once_still hst]
  have g3 : ∀ (s : St σ) (c : Int) (again : Bool),
      Grows (fun e => ∃ g b, e = .call c g b ∧ (g = .early ∨ g = .beforeAlwaysOnce ∨ g = .beforeOnce)) s
        (A.once .beforeOnce c false (A.once .beforeAlwaysOnce c false (A.once .early c again { s with pos := c }))) :=
    fun s c again => Grows.trans (Grows.trans (Grows.trans (Grows.refl (s' := { s with pos := c }) rfl)
      (once_grows A _ _ _ _) (fun _ h => h) (fun _ ⟨b, h⟩ => ⟨_, b, h, .inl rfl⟩))
      (once_grows A _ _ _ _) (fun _ h => h) (fun _ ⟨b, h⟩ => ⟨_, b, h, .inr (.inl rfl)⟩))
      (once_grows A _ _ _ _) (fun _ h => h) (fun _ ⟨b, h⟩ => ⟨_, b, h, .inr (.inr rfl)⟩)
  fun_induction A.visit c again d s with
  | case1 c again d s hc s1 s2 =>
    have hcn : c = A.n := by omega
    subst hcn
    obtain ⟨u, e, pu⟩ := g3 s (↑A.n) again
    have e' : (A.once .beforeOnce (↑A.n) false s2).log = s.log ++ u := e
    refine ⟨by simp only [display_pos]; rw [once_still hst]; exact p2 s _ again,
      u ++ [.display (↑A.n) (d.getD .fresh)], by simp [St.display, e'], fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact .inl (pu x hx)
    · simp at hx; exact .inr ⟨_, hx⟩
  | case2 c again d s hc s1 s2 h1 ih => exact absurd h1 (by rw [p2]; omega)
  | case3 c again d s hc s1 s2 h1 r s3 h2 ih =>
    exact absurd h2 (by simp only [s3, r]; rw [ask_still hst, p2]; omega)
  | case4 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 ih =>
    exact absurd h3 (by simp only [s4, s3, r]; rw [once_still hst, ask_still hst, p2]; omega)
  | case5 c again d s hc s1 s2 h1 r s3 h2 hr s4 h3 =>
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hd
    obtain ⟨u, e, pu⟩ := g3 s c again
    have e' : s4.log = s.log ++ u := e
    refine ⟨by simp only [display_pos, s4, s3, r]; rw [once_still hst]; exact p2 s c again,
      u ++ [.display c x], by simp [St.display, e'], fun y hy => ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact .inl (pu y hy)
    · simp at hy; exact .inr ⟨_, hy⟩
  | case6 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hd
    exact absurd rfl hr
  | case7 c again d s hc s1 s2 h1 r s3 h2 hr s4 h4 ih =>
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hd
    exact absurd rfl hr

/-- (6) Back from `k`, looking at `j < k` and further down: the player lands
on the nearest position from `j` down whose page is shown, without crossing a
barrier, or stays at `k` if there is none. No page is skipped on the way
(`after_always_once`). -/
theorem back_still (k j : Int) (s : St σ) (hj : j < k) (h0 : 0 ≤ k) (hn : k ≤ A.n) :
    ∃ u, (A.back k j s).log = s.log ++ u ∧ (∀ e ∈ u, ∀ q b, e ≠ .call q .afterAlwaysOnce b) ∧
      (((A.back k j s).pos ≤ j ∧ (∀ i, (A.back k j s).pos ≤ i → i ≤ j → A.barrier i = false) ∧
          (∀ i, (A.back k j s).pos < i → i ≤ j → Ev.call i .show false ∈ u) ∧
          (A.defines (A.back k j s).pos .show = true → Ev.call (A.back k j s).pos .show true ∈ u)) ∨
        ((A.back k j s).pos = k ∧ ∃ b, b ≤ j ∧ (b < 0 ∨ A.barrier b = true) ∧
          ∀ i, b < i → i ≤ j → Ev.call i .show false ∈ u)) := by
  have noAao : ∀ {c : Int} {u : List Ev}, (∀ e ∈ u, (∃ g b, e = .call c g b ∧
      (g = .early ∨ g = .beforeAlwaysOnce ∨ g = .beforeOnce)) ∨ ∃ sh, e = .display c sh) →
      ∀ e ∈ u, ∀ q b, e ≠ .call q .afterAlwaysOnce b := by
    intro c u hu e he q b h; subst h
    rcases hu _ he with ⟨g, b', h, hg⟩ | ⟨sh, h⟩ <;> cases h
    rcases hg with h | h | h <;> cases h
  have stay : ∀ (X : St σ), (A.stay k .fresh { X with pos := k }).pos = k ∧
      ∃ u, (A.stay k .fresh { X with pos := k }).log = X.log ++ u ∧ ∀ e ∈ u, ∀ q b, e ≠ .call q .afterAlwaysOnce b := by
    intro X
    unfold App.stay; rw [ite_not (Int.lt_irrefl _)]
    obtain ⟨hp, u, e, pu⟩ := visit_some_still hst k false (some .fresh) { X with pos := k } rfl h0 hn
    exact ⟨hp, u, e, noAao pu⟩
  fun_induction A.back k j s with
  | case1 j s hj0 =>
    obtain ⟨hp, u, e, pu⟩ := stay s
    exact ⟨u, e, pu, .inr ⟨hp, j, Int.le_refl _, .inl hj0, fun i h1 h2 => by omega⟩⟩
  | case2 j s hj0 hb =>
    obtain ⟨hp, u, e, pu⟩ := stay s
    exact ⟨u, e, pu, .inr ⟨hp, j, Int.le_refl _, .inr hb, fun i h1 h2 => by omega⟩⟩
  | case3 j s hj0 hb r hm => exact absurd hm (by simp [r, call_still hst])
  | case4 j s hj0 hb r hm hs =>
    obtain ⟨hp, u, e, pu⟩ := visit_some_still hst j true (some .fresh) r.2 rfl (by omega) (by omega)
    have el := call_log A .show j { s with pos := j } default
    refine ⟨(if A.defines j .show = true then [.call j .show true] else []) ++ u, ?_, fun e he q b => ?_,
      .inl ⟨by omega, fun i h1 h2 => ?_, fun i h1 h2 => by omega, fun hd => ?_⟩⟩
    · rw [e]; simp only [r] at hs ⊢
      cases hd : A.defines j .show
      · simp [call_undef A hd]
      · rw [call_log_def A hd, hs]; simp
    · rcases List.mem_append.mp he with he | he
      · split at he <;> simp at he; subst he; simp
      · exact noAao pu e he q b
    · have : i = j := by omega
      subst this; simpa using hb
    · rw [hp] at hd ⊢; simp [hd]
  | case5 j s hj0 hb r hm hs ih =>
    obtain ⟨u, e, pu, h⟩ := ih (by omega)
    have hdef : A.defines j .show = true := by
      cases hd : A.defines j .show
      · simp only [r] at hs; rw [call_undef A hd] at hs; simp [Hook.default] at hs
      · rfl
    have hs' : (A.call .show j { s with pos := j }).1 = false := by simpa [r] using hs
    have e0 : r.2.log = s.log ++ [.call j .show false] := by
      simp only [r]; rw [call_log_def A hdef, hs']
    refine ⟨.call j .show false :: u, by rw [e, e0]; simp, fun e he q b => ?_, ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · simp
      · exact pu e he q b
    · rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, b, h2, h3, h4⟩
      · refine .inl ⟨by omega, fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_, fun hd => List.mem_cons_of_mem _ (h4 hd)⟩
        · by_cases hi : i = j
          · subst hi; simpa using hb
          · exact h2 i hi1 (by omega)
        · by_cases hi : i = j
          · subst hi; simp
          · exact List.mem_cons_of_mem _ (h3 i hi1 (by omega))
      · refine .inr ⟨h1, b, by omega, h3, fun i hi1 hi2 => ?_⟩
        by_cases hi : i = j
        · subst hi; simp
        · exact List.mem_cons_of_mem _ (h4 i hi1 (by omega))

/-- (6) Back without moves, before the tolerance window: the player lands on
the nearest earlier position whose page is shown, without crossing a barrier;
they stay if `allow_back` forbids Back or there is no such page. Back skips no
page (`after_always_once`); by `step_back`, it saves nothing and asks neither
`may_proceed` nor `after_once`. -/
theorem step_back_still (now : Nat) (r : Req F) (s : St σ) (f : F) (h0 : 0 ≤ s.pos) (hn : s.pos ≤ A.n)
    (hb : r.submission s.pos = some (true, f)) (hd : ∀ t, s.deadline s.pos = some t → now + A.tolerance < t) :
    ∃ u, (A.step now r s).log = s.log ++ u ∧ (∀ e ∈ u, ∀ q b, e ≠ .call q .afterAlwaysOnce b) ∧
      (((A.step now r s).pos < s.pos ∧ (∀ i, (A.step now r s).pos ≤ i → i < s.pos → A.barrier i = false) ∧
          (∀ i, (A.step now r s).pos < i → i < s.pos → Ev.call i .show false ∈ u) ∧
          (A.defines (A.step now r s).pos .show = true → Ev.call (A.step now r s).pos .show true ∈ u)) ∨
        ((A.step now r s).pos = s.pos ∧ ((∀ b, Ev.call s.pos .allowBack b ∈ u → b = false) ∨
          ∃ b, b < s.pos ∧ (b < 0 ∨ A.barrier b = true) ∧ ∀ i, b < i → i < s.pos → Ev.call i .show false ∈ u))) := by
  simp only [App.step, arm_log, arm_pos]
  unfold App.respond; dsimp only
  rw [ite_not (by omega), ite_not (by omega), timedOut_far A now s.pos s hd, hb]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold App.goBack; dsimp only
  rw [ite_not (show ¬s.pos < (A.call .allowBack s.pos s).2.pos by rw [call_still hst]; omega)]
  obtain ⟨ua, ea, pa⟩ : ∃ ua, (A.call .allowBack s.pos s).2.log = s.log ++ ua ∧
      ∀ e ∈ ua, e = .call s.pos .allowBack (A.call .allowBack s.pos s).1 := by
    rcases call_log A .allowBack s.pos s default with e | e
    · exact ⟨[], by simp [e], by simp⟩
    · exact ⟨_, e, by simp⟩
  have hp : (A.call .allowBack s.pos s).2.pos = s.pos := call_still hst _ _ _ _
  split
  · next hallow =>
    obtain ⟨u, e, pu, h⟩ := back_still hst s.pos (s.pos - 1) (A.call .allowBack s.pos s).2 (by omega) h0 hn
    refine ⟨ua ++ u, by rw [e, ea]; simp, fun x hx q b => ?_, ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · rw [pa x hx]; simp
      · exact pu x hx q b
    · rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, b, h2, h3, h4⟩
      · exact .inl ⟨by omega, fun i hi1 hi2 => h2 i hi1 (by omega),
          fun i hi1 hi2 => List.mem_append_right _ (h3 i hi1 (by omega)),
          fun hd => List.mem_append_right _ (h4 hd)⟩
      · exact .inr ⟨h1, .inr ⟨b, by omega, h3, fun i hi1 hi2 => List.mem_append_right _ (h4 i hi1 (by omega))⟩⟩
  · next hallow =>
    unfold App.stay; rw [ite_not (by omega)]
    obtain ⟨hp', u, e, pu⟩ := visit_some_still hst s.pos false (some .fresh) _ rfl h0 hn
    refine ⟨ua ++ u, by rw [e, ea]; simp, fun x hx q b => ?_, .inr ⟨hp', .inl fun b hx => ?_⟩⟩
    · rcases List.mem_append.mp hx with hx | hx
      · rw [pa x hx]; simp
      · intro h; subst h
        rcases pu _ hx with ⟨g, b', h, hg⟩ | ⟨sh, h⟩ <;> cases h
        rcases hg with h | h | h <;> cases h
    · rcases List.mem_append.mp hx with hx | hx
      · have := pa _ hx; simp at this; rw [this]; simpa using hallow
      · rcases pu _ hx with ⟨g, b', h, hg⟩ | ⟨sh, h⟩ <;> cases h
        rcases hg with h | h | h <;> cases h

end Still

/-! ## Reachable states -/

/-- The states of a player: their requests, and what happens to them
elsewhere. The session-wide link starts them (`started`); admins and app code
of other players move them (`advance_by_one`, `revert_by_one`, `put_to_end`,
`move_to_page`, `move_to_end`), run once-hooks on the way (`reach_end`, the
markers that `move_to_page` sets up), and change app data. -/
inductive App.Reach : St σ → Prop
  | init (a : σ) : App.Reach (St.init a)
  | step {s} (now : Nat) (r : Req F) : App.Reach s → App.Reach (A.step now r s)
  | start {s} : App.Reach s → App.Reach { s with started := true }
  | move {s} (t : Int) : App.Reach s → 0 ≤ t → t ≤ A.n → (0 ≤ s.pos ∨ t = A.n) →
      App.Reach { s with pos := t }
  | once {s} (h : Hook) (p : Int) : App.Reach s → App.Reach (A.once h p false s)
  | data {s} (a : σ) : App.Reach s → App.Reach { s with app := a }

/-- The player is at `Initialize.html`, a page or the end. -/
theorem reach_pos {s : St σ} (h : A.Reach s) : -1 ≤ s.pos ∧ s.pos ≤ A.n := by
  induction h with
  | init => simp [St.init]
  | step now r _ ih =>
    obtain ⟨_, _, _, _, h1, h2, _⟩ := step_display A now r _ ih.1 ih.2
    exact ⟨h1, h2⟩
  | start _ ih => exact ih
  | move t _ h0 hn _ => exact ⟨show -1 ≤ t by omega, hn⟩
  | @once s h p _ ih => have := once_pos A h p false s; omega
  | data _ _ ih => exact ih

/-- No request fails: every request displays a page. -/
theorem reach_no_error {s : St σ} (h : A.Reach s) : Ev.error ∉ s.log := by
  induction h with
  | init => simp [St.init]
  | step now r hs ih =>
    have hp := reach_pos A hs
    obtain ⟨u, sh, e, pu, -⟩ := step_display A now r _ hp.1 hp.2
    rw [e]; intro he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | he
    · exact ih he
    · rcases pu _ he with ⟨_, _, _, h⟩ | h | ⟨_, _, h⟩ <;> cases h
    · cases he
  | start _ ih => exact ih
  | move _ _ _ _ _ ih => exact ih
  | @once s h p _ ih =>
    rcases once_log A h p false s with e | ⟨b, e⟩ <;> rw [e] <;> simp_all
  | data _ _ ih => exact ih

/-- (2) Every once-hook (`before_always_once`, `before_once`, `after_once`,
`after_always_once`) has run at most once at each position. -/
theorem reach_once {s : St σ} (h : A.Reach s) (p : Int) (g : Hook) (hg : g.once = true) :
    runs p g s.log ≤ 1 := by
  have ok : OnceOK s := by
    induction h with
    | init => intro q g _; simp [St.init]
    | step now r _ ih => exact (onceOK A).step now r _ ih
    | start _ ih => exact ih
    | move _ _ _ _ _ ih => exact ih
    | once h p _ ih => exact once_ok A h p false _ (fun _ => rfl) ih
    | data _ _ ih => exact ih
  have := ok p g hg
  split at this <;> omega

omit [Inhabited F] in
theorem Entered.mono {s s' : St σ} {p} (h : RanGrows s s') (he : A.Entered s p) : A.Entered s' p :=
  fun g hg hd => h _ (he g hg hd)

/-- (1, 2) Every page that has been displayed was entered first: its `early`,
`before_always_once` and `before_once` have run. -/
theorem reach_entered {s : St σ} (h : A.Reach s) (p : Int) (sh : Shown)
    (hd : Ev.display p sh ∈ s.log) (h0 : 0 ≤ p) : A.Entered s p := by
  induction h with
  | init => simp [St.init] at hd
  | step now r hs ih =>
    have hp := reach_pos A hs
    obtain ⟨u, sh', e, pu, -, -, hent⟩ := step_display A now r _ hp.1 hp.2
    rw [e] at hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with (hd | hd) | hd
    · exact Entered.mono A ((ranGrows A).step now r _) (ih hd)
    · rcases pu _ hd with ⟨_, _, _, h⟩ | h | ⟨_, _, h⟩ <;> cases h
    · cases hd; exact hent h0
  | start _ ih => exact ih hd
  | move _ _ _ _ _ ih => exact ih hd
  | @once s g q _ ih =>
    have hd' : Ev.display p sh ∈ s.log := by
      rcases once_log A g q false s with e | ⟨b, e⟩ <;> rw [e] at hd <;> simp_all
    exact Entered.mono A (fun x hx => once_ran A g q false s x hx) (ih hd')
  | data _ _ ih => exact ih hd

end Requests

end Pages
