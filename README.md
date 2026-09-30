# A counterexample to Vaught's conjecture for $L_{\omega_1,\omega}$

By Nathanael Ackerman, Cameron Freer, and Robin Knight.

A Lean 4 formalization of a countable relational language and an $L_{\omega_1,\omega}$ sentence
with exactly $\aleph_1$ countable models up to isomorphism and no perfect set of pairwise
non-isomorphic countable models, together with the general theory it rests on.

It builds on [Mathlib](https://github.com/leanprover-community/mathlib4) and
[InfinitaryLogic](https://github.com/cameronfreer/infinitary-logic) (syntax and semantics of
$L_{\omega_1,\omega}$, Scott analysis, model-code spaces, Morley counting).

## Layout

- `VaughtConjecture/` — the library.  Every module under it is built and audited (the lakefile globs are
  authoritative; `VaughtConjecture.lean` is an intentionally empty root).  Organized by mathematical topic.
- `roadmap/` — the human-owned specification: [`roadmap/README.md`](roadmap/README.md) is the
  mathematical roadmap and [`roadmap/IMPLEMENTATION.md`](roadmap/IMPLEMENTATION.md) the
  implementation order with its checkpoints, with the semantic contract, expositions, sketches,
  and sources alongside.  New mathematics is added only when it advances a roadmap target.
- `scripts/`, `.github/` — build and audit infrastructure.

## Building and checking

```sh
lake build
bash scripts/check.sh --no-build
```

CI runs the same: build against the pinned dependencies, then check that there is no `sorry`,
no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`, Mathlib's linter set with
warnings as errors, and copyright headers.

The only pins are `lean-toolchain` and the InfinitaryLogic revision in `lakefile.toml`; Mathlib
is inherited from InfinitaryLogic's manifest, and the toolchain must equal InfinitaryLogic's.  To
bump: change `rev`, run `lake update InfinitaryLogic`, copy InfinitaryLogic's `lean-toolchain`,
commit the manifest.

## Contributing

Work lands through pull requests, one topic each, in tranches of a few hundred to a thousand
lines: implementation, review against the [TauCeti review
rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics) (used as guidance),
then external review before merging.  Each PR names the roadmap layer it advances, or
`Roadmap: none` for infrastructure.  Mathlib style throughout; no compatibility shims.

## License

Apache 2.0; see [`LICENSE`](LICENSE).
