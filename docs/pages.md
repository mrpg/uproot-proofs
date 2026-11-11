# Pages

A specification of how uproot answers a participant's requests to their page,
`GET` and `POST /p/{sname}/{uname}/` (`server1.show_page`): page hooks,
navigation, form submissions, timeouts and Back. uproot implements it (the
functions in `server1.py` carry the names of the definitions in `Pages.lean`),
and uproot's opt-in `tests/test_pages_model.py` (below) checks that the two
agree.

| File | Contents |
|---|---|
| `UprootProofs/Pages.lean` | The handler (`App.step`), its parts, and the theorems below |
| `PageCases.lean` | `lake exe page-cases`: requests and what the specification says they do, for differential testing |

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
   token, can be submitted. Any other request is handled as loading the page. A
   submission is accepted if the fields validate and neither `validate` nor
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

## Main results

The numbers refer to the principles.

For every reachable state (`App.Reach`: requests, and what happens to the
player elsewhere: the session-wide link, admins, other players' app code):

* `reach_pos`, `reach_no_error`: the player is at `Initialize.html`, a page or
  the end, and no request fails (1);
* `reach_once`: every once-hook has run at most once at each position (2);
* `reach_entered`: every page that has been displayed was entered first: its
  `early`, `before_always_once` and `before_once` had run (1, 2).

For every request (`App.step`):

* `step_display`: it ends by displaying the page at the player's position,
  which is entered; before that, it only runs hooks, starts the player or saves
  a form (1);
* `foreign_is_get`, `resubmit_is_get`: a request that does not carry the form
  of the player's position with a valid token is handled exactly as loading the
  page; so is submitting a form again once it has taken the player elsewhere
  (3);
* `step_saves`, `accept_spec`: at most one form is saved, the submitted form of
  the player's position, exactly if it is accepted; Back saves only as a
  timed-out submission (3, 6);
* `step_errors`: submitted values and errors are displayed only if the player
  stays at the position whose form they submitted, before its deadline (4);
* `step_timeout`: after the deadline, the request leaves the page:
  `timeout_reached` runs, `may_proceed` is not asked, and a later position is
  displayed without errors (5);
* `step_back`: Back before the tolerance window saves nothing and asks neither
  `may_proceed` nor `after_once` (6);
* `step_moves`: a move is never lost: the request ends at the furthest position
  that a hook moved the player to, or beyond (7).

Without moves (`App.Still`), navigation is exactly as described:

* `visit_still`: forward navigation displays the first position from where it
  starts whose page is shown; it enters every position on its way
  (`before_always_once`) and skips it (`show()` is false, `after_always_once`)
  (1, 2);
* `step_back_still`: Back lands on the nearest earlier position whose page is
  shown, without crossing a barrier, and skips no page; the player stays if
  `allow_back` forbids Back or there is no such page (6).

## What the specification settles

uproot was changed to meet the specification. Each change follows from a
principle:

* Back after the deadline is a timed-out submission; before, `timeout_reached`
  ran and the player still went back (5).
* Back does not cross the start of an app, a round or an iteration of
  `Repeat`, the rule that reverting players already followed. Before, going
  back across the start of a round left `player.round` ahead, and going back
  from the first page of an app displayed the hidden `#StartApp`, an HTTP 500
  (6).
* `may_proceed` no longer gates Back (4, 6).
* A page that the player reaches by Back is entered and runs `before_once` if it
  has not run there: a page that was hidden on the way forward ran no
  `before_once` before (1, 2).
* A move by any hook is kept, and the target is entered: before, a move from a
  skipped page's hook was lost; one from `before_once` (as in the dropout
  pattern in the docs) displayed the target without its `early` and
  `before_always_once`; one from a `may_proceed` that refused displayed the old
  page at the new position (7).
* A form that is not the current page's, e.g., one submitted just after an
  admin advanced the player, is handled as loading the page: before, uproot
  displayed the current page without entering it, even if it was hidden (3).

## Testing the specification against uproot

The theorems are about the specification. uproot's opt-in test
`tests/test_pages_model.py` (skipped unless `UPROOT_MODEL_TESTS` is set) checks
that uproot implements it: `test_page_cases` replays the cases from
`lake exe page-cases` (81,736 requests: page orders of shown, hidden and
barrier pages and pages without hooks, players at every position with and
without the markers of having got there, `GET`, stale and foreign forms, forms
that validate or not, `validate` and `handle_stealth_fields` rejecting or not,
`may_proceed` and `allow_back` allowing or not, deadlines ahead, within the
tolerance window or passed, and hooks that move the player) through
`server1.show_page` and compares, in order, the hook calls, the start, the
saves and the page displayed, and then the player's position, markers and
deadlines.

```sh
lake exe page-cases > page-cases.jsonl
cd path/to/uproot
UPROOT_MODEL_TESTS=1 UPROOT_PAGE_CASES=path/to/page-cases.jsonl \
  uv run pytest tests/test_pages_model.py
```

## Scope

A request is one run of the handler, atomic for the player:
`show_page_wrapper` holds the player's page lock. Hooks are app code: they may
read and write any app data, their results may depend on it, and they may move
the player forward. Not modelled: hooks that raise; hooks that move the player
backward (`move_to_page` raises for pages that are not ahead); changes of the
page order (`Repeat`, `Between`), which leave the positions up to the current
one as they are; rendering, and what live methods do between requests.
