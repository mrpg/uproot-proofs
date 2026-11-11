-- SPDX-License-Identifier: 0BSD

import UprootProofs.Pages

/-!
# Page cases for differential testing

`lake exe page-cases > page-cases.jsonl` prints cases of one request each: a
page order, a player, a request, and what `Pages.App.step` says the request
does (the events it records and the player afterwards). uproot's opt-in
`tests/test_pages_model.py` replays each case through `server1.show_page` and
compares (see `docs/pages.md`).

Pages have no app data (`σ = Unit`), and their hooks return fixed results.
Every hook that a page defines records its call, so that the test sees the
same events as the model.
-/

open Pages

/-- A page of a case. -/
structure Pg where
  /-- The hooks that the page defines, and what they return. -/
  hooks : List (Hook × Bool) := []
  /-- A hook that moves the player, and where to. -/
  mover : Option (Hook × Int) := none
  barrier : Bool := false
  /-- Fields: whether the submitted values are valid, and whether there is a
  stealth field. -/
  form : Option (Bool × Bool) := none
  timeout : Option Nat := none
  deriving Inhabited

def Pg.with (pg : Pg) (h : Hook) (b : Bool) : Pg :=
  { pg with hooks := (h, b) :: pg.hooks.filter (·.1 != h) }

structure Case where
  pages : List Pg
  /-- `End.html` -/
  last : Pg
  state : St Unit
  now : Nat
  req : Req Unit

def Case.pg (c : Case) (p : Int) : Pg :=
  if p = c.pages.length then c.last
  else if 0 ≤ p ∧ p < c.pages.length then c.pages.getD p.toNat {}
  else {}

def Case.app (c : Case) : App Unit Unit where
  n := c.pages.length
  defines p h := ((c.pg p).hooks.lookup h).isSome
  run p h _ _ := ((((c.pg p).hooks.lookup h).getD true), (),
    match (c.pg p).mover with
    | some (g, t) => if g = h then some t else none
    | none => none)
  barrier p := (c.pg p).barrier
  hasForm p := (c.pg p).form.isSome
  valid p _ _ := ((c.pg p).form.map (·.1)).getD true
  manual p _ _ := ((c.pg p).form.map (·.2)).getD false
  ordinary _ _ _ := ["a"]
  save _ _ a := a
  timeout p _ := (c.pg p).timeout
  start a := a
  tolerance := 1

/-! ## JSON -/

def jStr (s : String) : String := "\"" ++ s ++ "\""
def jList {α} (f : α → String) (l : List α) : String := "[" ++ ",".intercalate (l.map f) ++ "]"
def jOpt {α} (f : α → String) : Option α → String
  | none => "null"
  | some a => f a

def Pages.Hook.name : Hook → String
  | .early => "early" | .beforeAlwaysOnce => "before_always_once" | .show => "show"
  | .beforeOnce => "before_once" | .afterOnce => "after_once"
  | .afterAlwaysOnce => "after_always_once" | .timeoutReached => "timeout_reached"
  | .mayProceed => "may_proceed" | .allowBack => "allow_back" | .validate => "validate"
  | .handleStealthFields => "handle_stealth_fields" | .beforeFormSave => "before_form_save"

def Pages.Shown.name : Shown → String
  | .fresh => "fresh" | .kept => "kept" | .errors => "errors"

def jPg (pg : Pg) : String :=
  "{\"hooks\":" ++ jList (fun (h, b) => "[" ++ jStr h.name ++ "," ++ toString b ++ "]") pg.hooks
    ++ ",\"mover\":" ++ jOpt (fun (h, t) => "[" ++ jStr h.name ++ "," ++ toString t ++ "]") pg.mover
    ++ ",\"barrier\":" ++ toString pg.barrier
    ++ ",\"form\":" ++ jOpt (fun (v, st) => "{\"valid\":" ++ toString v ++ ",\"stealth\":"
      ++ toString st ++ "}") pg.form
    ++ ",\"timeout\":" ++ jOpt toString pg.timeout ++ "}"

def jEv : Ev → String
  | .call p h b => "[\"call\"," ++ toString p ++ "," ++ jStr h.name ++ "," ++ toString b ++ "]"
  | .init => "[\"init\"]"
  | .save p fs => "[\"save\"," ++ toString p ++ "," ++ jList jStr fs ++ "]"
  | .display p sh => "[\"display\"," ++ toString p ++ "," ++ jStr sh.name ++ "]"
  | .error => "[\"error\"]"

/-- Positions `-1` to `n`. -/
def positions (n : Nat) : List Int := (List.range (n + 2)).map fun (i : Nat) => (i : Int) - 1

def jSt (n : Nat) (s : St Unit) : String :=
  "{\"pos\":" ++ toString s.pos ++ ",\"started\":" ++ toString s.started
    ++ ",\"ran\":" ++ jList (fun (p, h) => "[" ++ toString p ++ "," ++ jStr h.name ++ "]") s.ran
    ++ ",\"deadlines\":" ++ jList (fun (p, t) => "[" ++ toString p ++ "," ++ toString t ++ "]")
      ((positions n).filterMap fun p => (s.deadline p).map fun t => (p, t)) ++ "}"

def jReq : Req Unit → String
  | .get => "{\"method\":\"GET\"}"
  | .post src back token _ =>
    "{\"method\":\"POST\",\"from\":" ++
      jOpt (fun p => jStr ((if back then "back-" else "") ++ toString p)) src ++
      ",\"token\":" ++ toString token ++ "}"

def Case.json (c : Case) : String :=
  let s' := c.app.step c.now c.req c.state
  "{\"pages\":" ++ jList jPg c.pages ++ ",\"end\":" ++ jPg c.last
    ++ ",\"state\":" ++ jSt c.pages.length c.state ++ ",\"now\":" ++ toString c.now
    ++ ",\"request\":" ++ jReq c.req
    ++ ",\"log\":" ++ jList jEv (s'.log.drop c.state.log.length)
    ++ ",\"after\":" ++ jSt c.pages.length s' ++ "}"

/-! ## Cases -/

def entering : List Hook := [.early, .beforeAlwaysOnce, .beforeOnce]
def all : List Hook := [.early, .beforeAlwaysOnce, .beforeOnce, .afterOnce, .afterAlwaysOnce]

/-- Shown pages (with a timeout), hidden pages, pages without hooks, and
barriers (hidden). -/
def kinds : List Pg :=
  [ { hooks := all.map (·, true), timeout := some 30 },
    { hooks := (.show, false) :: all.map (·, true) },
    {},
    { hooks := (.show, false) :: all.map (·, true), barrier := true } ]

def orders : List (List Pg) := kinds.flatMap fun a => kinds.flatMap fun b => kinds.map fun c => [a, b, c]

def now : Nat := 1000

/-- No deadline, one beyond the tolerance window, one within it, and one that
has passed. -/
def deadlines : List (Option Nat) := [none, some (now + 5), some (now + 1), some (now - 5)]

/-- The markers of a player who navigated to `k` (or none). -/
def markers (pages : List Pg) (k : Int) (entered : Bool) : List (Int × Hook) :=
  if !entered then [] else
  (List.range pages.length).flatMap fun i =>
    let pg := pages.getD i {}
    let hs := if (i : Int) < k then all else if (i : Int) = k then entering else []
    (hs.filter fun h => (pg.hooks.lookup h).isSome).map ((i : Int), ·)

def player (pages : List Pg) (k : Int) (entered : Bool) (dl : Option Nat) : St Unit :=
  ⟨k, decide (0 ≤ k), markers pages k entered, fun p => if p = k then dl else none, [], (), -1⟩

/-- A hook that the page does not define, or one that returns `true` or `false`. -/
def results : List (Option Bool) := [none, some true, some false]

def Pg.opt (pg : Pg) (h : Hook) : Option Bool → Pg
  | none => { pg with hooks := pg.hooks.filter (·.1 != h) }
  | some b => pg.with h b

/-- Forms: none, valid, invalid, rejected by `validate`, with a stealth field
that `handle_stealth_fields` rejects, or accepts. -/
def forms (pg : Pg) : List Pg :=
  let f := (pg.with .beforeFormSave true)
  [ pg,
    { f with form := some (true, false) },
    { f with form := some (false, false) },
    { (f.with .validate false) with form := some (true, false) },
    { (f.with .handleStealthFields false) with form := some (true, true) },
    { (f.with .handleStealthFields true) with form := some (true, true) } ]

def endPage : Pg := { hooks := [(.beforeAlwaysOnce, true)] }

def set (l : List Pg) (k : Nat) (pg : Pg) : List Pg := l.set k pg

/-- Requests at a page position `k`: `GET`, a stale form, one without token,
one without `_uproot_from`, the page's form, and Back. -/
def coreCases : List Case := orders.flatMap fun pages =>
  (List.range pages.length).flatMap fun k => [true, false].flatMap fun entered =>
    let base := (pages.getD k {}).with .timeoutReached true
    let mk pg dl req : Case := ⟨set pages k pg, endPage, player (set pages k pg) k entered dl, now, req⟩
    let loads := deadlines.flatMap fun dl => results.flatMap fun mp =>
      let pg := (if dl.isSome then { base with timeout := some 30 } else base).opt .mayProceed mp
      [ mk pg dl .get, mk pg dl (.post (some (k + 1)) false true ()),
        mk pg dl (.post (some k) false false ()), mk pg dl (.post none false true ()) ]
    let nexts := deadlines.flatMap fun dl => results.flatMap fun mp =>
      (forms ((if dl.isSome then { base with timeout := some 30 } else base).opt .mayProceed mp)).map
        fun pg => mk pg dl (.post (some k) false true ())
    let backs := deadlines.flatMap fun dl => results.flatMap fun ab =>
      [none, some false].flatMap fun mp =>
        ((forms (((if dl.isSome then { base with timeout := some 30 } else base).opt .allowBack ab).opt
          .mayProceed mp)).take 3).map fun pg => mk pg dl (.post (some k) true true ())
    loads ++ nexts ++ backs

/-- Requests at `Initialize.html` and `End.html`. -/
def edgeCases : List Case := orders.flatMap fun pages =>
  let n : Int := pages.length
  let mk k req : Case := ⟨pages, endPage, player pages k (decide (0 ≤ k)) none, now, req⟩
  [ mk (-1) .get, mk (-1) (.post (some (-1)) false true ()), mk (-1) (.post (some (-1)) true true ()),
    mk (-1) (.post (some (-1)) false false ()),
    mk n .get, mk n (.post (some n) false true ()), mk n (.post (some n) true true ()) ]

def allHooks : List Hook :=
  [.early, .beforeAlwaysOnce, .show, .beforeOnce, .afterOnce, .afterAlwaysOnce, .timeoutReached,
   .mayProceed, .allowBack, .validate, .handleStealthFields, .beforeFormSave]

/-- What a hook that moves the player returns. -/
def moverResult (pg : Pg) : Hook → Bool
  | .show => ((pg.hooks.lookup .show).getD true)
  | .mayProceed => false
  | _ => true

/-- Hooks that move the player: of the page before, at or after the player's
position `k`, to any later position. -/
def moveCases : List Case :=
  let some' := [ [kinds[0]!, kinds[0]!, kinds[0]!], [kinds[0]!, kinds[1]!, kinds[0]!],
    [kinds[1]!, kinds[0]!, kinds[1]!], [kinds[0]!, kinds[1]!, kinds[1]!], [kinds[1]!, kinds[3]!, kinds[0]!] ]
  some'.flatMap fun pages =>
    let n := pages.length
    (List.range n).flatMap fun k =>
      ((if k = 0 then [0, 1] else [k - 1, k, k + 1]).filter (· < n)).flatMap fun i =>
        allHooks.flatMap fun h => (((List.range (n + 1)).filter (i < ·)).map (fun (t : Nat) => (t : Int))).flatMap fun t =>
          [none, some (now + 1), some (now - 5)].flatMap fun dl =>
            let cur := (((pages.getD k {}).with .timeoutReached true).with .allowBack true)
            let cur := if dl.isSome then { cur with timeout := some 30 } else cur
            let cur := if h = .validate || h = .handleStealthFields || h = .beforeFormSave then
              { cur with form := some (true, h = .handleStealthFields) } else cur
            let pages' := set pages k cur
            let pg := pages'.getD i {}
            let pages'' := set pages' i { pg.with h (moverResult pg h) with mover := some (h, t) }
            let mk req : Case := ⟨pages'', endPage, player pages'' k true dl, now, req⟩
            [mk .get, mk (.post (some k) false true ()), mk (.post (some k) true true ())]

def main : IO Unit := do
  for c in coreCases ++ edgeCases ++ moveCases do
    IO.println c.json
