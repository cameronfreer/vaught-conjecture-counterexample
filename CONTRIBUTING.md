# Contributing

The status of the main theorem is stated in [`README.md`](README.md#status); the
mathematical map, the development history and the alternative routes are in
[`roadmap/`](roadmap/README.md).

## Pull requests and review

Work lands through pull requests, one topic each.  Each pull request names the layer of
[`roadmap/README.md`](roadmap/README.md) it advances (`Roadmap: Layer 3`), or `Roadmap: none` for
infrastructure.

There is no size limit: a pull request that carries a construction may be large.  Every pull
request, large construction pull requests included, is reviewed in full by the maintainers'
reviewers, against the [TauCeti review
rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics) (used as guidance) and
the mathematical-terminology rubric of the roadmap's "Library conventions".  It is merged only
after CI has passed on its exact head commit: the build with warnings as errors, and the audits of
`scripts/check.sh`, including the standard-axiom audit (every declaration of the library depends
only on `propext`, `Classical.choice` and `Quot.sound`).  Before opening a pull request, run

```sh
lake build
bash scripts/check.sh --no-build
```

## Conventions

- Mathlib style throughout; no compatibility shims.
- Every module under `VaughtConjecture/` is built and audited (the lakefile globs are
  authoritative; `VaughtConjecture.lean` is an intentionally empty root and nothing imports it).
  Every module carries the Mathlib copyright header, and files stay under the 1500-line ceiling of
  the linter.
- Prose, docstrings, and declaration names use mathematical terminology only: they speak of
  mathematical objects, hypotheses, constructions, and theorems, never of roles in a workflow.
  "Library conventions" in [`roadmap/README.md`](roadmap/README.md#library-conventions) lists the
  conventions: the words to avoid, one word per notion, declaration names, `## Placement`
  sections, and the review rubrics.
- New mathematics is added only when it advances a roadmap target.

## Dependency pins and upgrades

The only pins are `lean-toolchain` and the [InfinitaryLogic](https://github.com/cameronfreer/infinitary-logic) and
[ComputableModelTheory](https://github.com/cameronfreer/computable-model-theory) revisions in `lakefile.toml`.  Mathlib is not required directly: it is inherited from InfinitaryLogic's
manifest (a `cameronfreer/mathlib4` fork commit), and the toolchain must equal InfinitaryLogic's
(`scripts/check.sh` checks this).

To bump InfinitaryLogic: change its `rev` in `lakefile.toml`, run `lake update InfinitaryLogic`,
copy InfinitaryLogic's `lean-toolchain`, and commit the manifest.  To bump ComputableModelTheory:
change its `rev`, run `lake update ComputableModelTheory`, and commit the manifest (its own
manifest's InfinitaryLogic revision does not govern; ours does).  Record the new pin in the comment
above the `rev` in `lakefile.toml` and in [`roadmap/IMPLEMENTATION.md`](roadmap/IMPLEMENTATION.md),
"Dependency pins".

CI keys its dependency cache on `lean-toolchain` and `lake-manifest.json`, so the first run after a
new pin rebuilds the dependencies and is slow; later runs restore them.  CI also elaborates the
roadmap's Lean sketches, whose `#check`s of upstream names fail on a pin that removes one.  The
pinned Mathlib differs from the one in the registered formalization (see [`README.md`](README.md));
the two developments do not share a build.
