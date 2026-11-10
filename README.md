# uproot-proofs

AI-generated machine-checked proofs about [uproot](https://github.com/mrpg/uproot), written in [Lean 4](https://lean-lang.org).

| Topic | Lean | Matches `mrpg/uproot` | Documentation |
|---|---|---|---|
| Rooms | `UprootProofs/Rooms.lean`, `UprootProofs/Labels.lean` | [6e68914](https://github.com/mrpg/uproot/commit/6e689142440bc5d42abc598c46083bad0241c7f9) | [docs/rooms.md](docs/rooms.md) |

## Checking the proofs

Install Lean via [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

The proofs check if the build succeeds. No dependencies (no Mathlib) are required.

Lean version used: **4.35.0**, pinned in `lean-toolchain`.

## License

0BSD, see `LICENSE`.
