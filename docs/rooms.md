# Rooms

A model of uproot's rooms: player admission, the release of waiting players,
the association between rooms and sessions, and server restarts. The model
tracks uproot at HEAD; uproot's opt-in `tests/test_rooms_model.py` (below)
checks that the two agree.

| File | Contents |
|---|---|
| `UprootProofs/Rooms.lean` | Room state machine: admission, waiter release, room–session association, restarts |
| `UprootProofs/Labels.lean` | `find_free_slot` and admission on a session's player list; label uniqueness |
| `RoomCases.lean` | `lake exe room-cases`: admission cases computed by the model, for differential testing |

## Main results

In every reachable state of the room state machine (`Reachable`):

* `released_iff_ready`: players waiting in a room are released exactly when the
  room is ready, i.e. open and associated with a session or a loaded config
  (`step_events` covers every step, including the two that skip `rooms.sync`,
  and server restarts, which may load different configs);
* `step_assoc`, `session_one_room`: `room["sname"]` and `session.room` are
  mutually inverse and refer to existing sessions, so a session belongs to at
  most one room;
* `deleted_not_released`, `open_releases`: deleted rooms hold no released
  waiters; opening a room with a session or a loaded config releases them.

For admission (`server3.roommain`):

* `not_ready_no_admission`, `labelled_nonempty`, `whitelist`: nobody is admitted
  to a room that is not ready, labelled rooms never admit the empty label, and
  with a non-empty label list only listed labels are admitted;
* `newPlayer_within_capacity`, `join_preserves_bound`, `capacity_zero`: new
  players are created only in free-join rooms or below capacity;
* `findFreeSlotLoop_spec`: the loop in `core.find_free_slot`, transcribed, is a
  first-match search for the requested label with a fallback;
* `label_one_player`: in every reachable session, two players carrying the same
  non-empty label are the same player (the claim in the `rooms.py` docstring).

## Testing the model against uproot

The theorems are about the model. uproot's opt-in test
`tests/test_rooms_model.py` (skipped unless `UPROOT_MODEL_TESTS` is set) checks
that the model describes uproot:

* `test_refinement` runs random, adversarial sequences of real room operations
  (forms, admin API, admin websocket functions, joins, restarts, the CLI quick
  room) and checks that each transition is a sequence of model `Step`s and that
  the invariants hold on the real state;
* `test_admission_cases` replays the cases from `lake exe room-cases` (56,160
  combinations of room settings, join label and player list) through
  `POST /room/{roomname}/` and compares the outcome and the resulting player
  list with the model's.

```sh
lake exe room-cases > room-cases.jsonl
cd path/to/uproot
UPROOT_MODEL_TESTS=1 UPROOT_FORMAL_CASES=path/to/room-cases.jsonl \
  uv run pytest tests/test_rooms_model.py
```

## Scope

Each `Step` is one request handler, taken as atomic; `Rooms.lean` states why
this holds for uproot (one process, one event-loop thread, no awaits between
reads and writes, failures before the first write). Configs are modelled only by
which names are loaded (`uproot.CONFIGS`, fixed while a process runs). Not
modelled: a process crash in the middle of a handler; admins overwriting player
fields (including `label`) with `insert_fields`; app code writing `player.label`.
