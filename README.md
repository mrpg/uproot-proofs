# uproot-proofs

AI-generated machine-checked proofs about [uproot](https://github.com/mrpg/uproot), written in [Lean 4](https://lean-lang.org).

| Topic | Lean | Matches `mrpg/uproot` | Documentation |
|---|---|---|---|
| Rooms | `UprootProofs/{Labels,Rooms}.lean` | [2bb236f](https://github.com/mrpg/uproot/commit/2bb236f02a4beb7d66aa20b53ee1801087137d5a) | [docs/rooms.md](docs/rooms.md) |
| Pages | `UprootProofs/Pages.lean` | [2bb236f](https://github.com/mrpg/uproot/commit/2bb236f02a4beb7d66aa20b53ee1801087137d5a) | [docs/pages.md](docs/pages.md) |

## Checking the proofs

Install Lean via [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

The proofs check if the build succeeds. No dependencies (no Mathlib) are required.

Lean version used: **4.35.0**, pinned in `lean-toolchain`.

## License

0BSD, see `LICENSE`.
