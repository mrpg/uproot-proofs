-- SPDX-License-Identifier: 0BSD

import UprootProofs.Labels

/-!
# Admission cases for differential testing

`lake exe room-cases > room-cases.jsonl` prints, for every combination of the
room settings, join label and player list below (lists of up to three players),
the outcome and resulting player list predicted by `Rooms.roommain`, with only
the config `cfg` loaded (`unknown` is not). uproot's
opt-in test `tests/test_rooms_model.py::test_admission_cases` replays each case
through the real `POST /room/{roomname}/` and compares (see `docs/rooms.md`).
-/

open Rooms

def jStr (s : String) : String := "\"" ++ s ++ "\""

def jOpt {α} (f : α → String) : Option α → String
  | none => "null"
  | some a => f a

def jList {α} (f : α → String) (l : List α) : String :=
  "[" ++ ",".intercalate (l.map f) ++ "]"

def jPlayer (p : Player) : String := "[" ++ jStr p.label ++ "," ++ toString p.started ++ "]"

def jOutcome : Outcome → String
  | .askLabel => "askLabel" | .badLabel => "badLabel" | .wait => "wait"
  | .resume => "resume" | .reuseSlot => "reuseSlot" | .newPlayer => "newPlayer"
  | .full => "full"

def playerChoices : List Player :=
  [⟨"", false⟩, ⟨"", true⟩, ⟨"a", false⟩, ⟨"a", true⟩, ⟨"b", false⟩, ⟨"b", true⟩]

def listsOfLen : Nat → List (List Player)
  | 0 => [[]]
  | n + 1 => (listsOfLen n).flatMap fun l => playerChoices.map (· :: l)

/-- All player lists of length at most `n`. -/
def allLists (n : Nat) : List (List Player) := (List.range (n + 1)).flatMap listsOfLen

def main : IO Unit := do
  let loaded : Config → Bool := (· == "cfg")
  for config in [none, some "cfg", some "unknown"] do
    for labels in [none, some [], some ["a", "b"]] do
      for capacity in [none, some 0, some 1, some 2] do
        for isOpen in [false, true] do
          for sname in [none, some "S"] do
            let ρ : Room := ⟨config, labels, capacity, isOpen, sname⟩
            for label in ["", "a", "c"] do
              -- Without a session, a join can only see the new, empty session.
              for ps in (if sname.isSome then allLists 3 else [[]]) do
                let (o, ps') := roommain loaded ρ label ps
                IO.println ("{\"config\":" ++ jOpt jStr config
                  ++ ",\"labels\":" ++ jOpt (jList jStr) labels
                  ++ ",\"capacity\":" ++ jOpt toString capacity
                  ++ ",\"open\":" ++ toString isOpen
                  ++ ",\"sname\":" ++ jOpt jStr sname
                  ++ ",\"label\":" ++ jStr label
                  ++ ",\"players\":" ++ jList jPlayer ps
                  ++ ",\"outcome\":" ++ jStr (jOutcome o)
                  ++ ",\"after\":" ++ jList jPlayer ps' ++ "}")
