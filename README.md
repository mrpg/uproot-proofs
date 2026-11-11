# uproot-proofs

AI-generated machine-checked proofs about [uproot](https://github.com/mrpg/uproot), written in [Lean 4](https://lean-lang.org).

| Topic | Lean | Matches `mrpg/uproot` | Documentation |
|---|---|---|---|
| Rooms | `UprootProofs/{Labels,Rooms}.lean` | [910fe72](https://github.com/mrpg/uproot/commit/910fe7229a60c2f5c6ce9b37fe0a0cb85771b4a1) | [docs/rooms.md](docs/rooms.md) |
| Pages | `UprootProofs/Pages.lean` | [6c9cfbe](https://github.com/mrpg/uproot/commit/6c9cfbec90fbfc60cd51f2eb140122ae8b1732c9) | [docs/pages.md](docs/pages.md) |

## Checking the proofs

Install Lean via [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

The proofs check if the build succeeds. No dependencies (no Mathlib) are required.

Lean version used: **4.35.0**, pinned in `lean-toolchain`.

## License

0BSD, see `LICENSE`.
