# A counterexample to Vaught's conjecture for $L_{\omega_1,\omega}$

By Nathanael Ackerman, Cameron Freer, and Robin Knight.

A Lean 4 development toward a countable relational language and an $L_{\omega_1,\omega}$ sentence
with exactly $\aleph_1$ countable models up to isomorphism and no perfect set of pairwise
non-isomorphic countable models, together with the general theory it rests on.  The construction
follows Robin Knight's unpublished 2026 draft [Kni26] and the draft of Ackerman, Freer and Knight
[AFK26] (see [`roadmap/REFERENCES.bib`](roadmap/REFERENCES.bib)).  It is not a counterexample to the
first-order Vaught conjecture.

It builds on [Mathlib](https://github.com/leanprover-community/mathlib4),
[InfinitaryLogic](https://github.com/cameronfreer/infinitary-logic) (syntax and semantics of
$L_{\omega_1,\omega}$, Scott analysis, model-code spaces, Morley counting), and
[ComputableModelTheory](https://github.com/cameronfreer/computable-model-theory) (classical
Fraïssé interfaces, factorization of tuples through age representatives, orbit isolation, atomic
and prime structures).  The intended construction obtains its top-free witnesses (the terminal
models at each countable stage, which give the lower bound) by constructing a finite age of
labelled charts and reconstructing its classical Fraïssé limit; the other countable models are
classified, not constructed.  The classical theorems are taken from the two libraries at the
pinned versions, the classical existence theorem included (see
[`roadmap/IMPLEMENTATION.md`](roadmap/IMPLEMENTATION.md), "Dependency pins").

The roadmap is organized by shared foundations and the results they support
([`roadmap/README.md`](roadmap/README.md), "Endpoints and shared foundations").  The first of
these results is the main theorem, by way of a continuous decreasing filtration by expansion
domains.  A second route to the main theorem counts full presentations (structures full for one
of countably many prescribed ages at each countable level) and compares their base reducts by
bounded back-and-forth; its count needs no separate termination theorem for expansion domains
(its existence statement is at first proved with the termination arguments).  Both routes are
retained.

## Status

The main theorem is compiled here *conditionally*.  On the terminal-classification route,
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_terminalClassification''` and
`MainTheorem.vaughtCounterexample_allCarriers_of_terminalClassification''` prove the spectrum
statement from four named hypotheses, `Expansion.FiniteCutReceiving`, `ContinuationCriterion`,
`Realization.ResidualReceiving` and `Realization.HollowReceiving Realization.IsCoverHollowAtBlock`,
each of which is open.  On the receiving-models route,
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_receivingModels'` and
`MainTheorem.vaughtCounterexample_allCarriers_of_receivingModels'` prove it from three,
`Expansion.ReceivingStableCappedReceiving`, `Realization.ReceivingResidualReceiving` and
`Realization.HollowReceiving Realization.IsReceivingCoverHollowAtBlock`, each of which is open.  The
finite coatom-extension property with apex is proved at every arity, at every stage that is zero or
a limit and at every block stage (`StageType.hasApexCoatomExtensions`,
`StageType.hasApexCoatomExtensions_blockStage`).  [`roadmap/DASHBOARD.md`](roadmap/DASHBOARD.md)
lists every named hypothesis with its status, and [`roadmap/README.md`](roadmap/README.md) the
routes to proving them.  No unconditional counterexample theorem is claimed in this repository.

## Relation to the registered formalization

The same mathematical theorem has been formalized by the same authors in a separate repository,
[`cameronfreer/vaught-conjecture-palomar`](https://github.com/cameronfreer/vaught-conjecture-palomar),
registered in the Palomar registry as
[PALOMAR-2026-10-07-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000001&version=1)
(commit `032ccb7a25b0ff6227128aa0aeba549c5901ea9a`, theorem
`PalomarChallenge.independent_challenge`).  That repository contains one proof of one statement.
This repository is a separately organized development of the same mathematics as a library: the
general theory of charts, stage types, extensions and realizations, a roadmap with status markers,
and reusable interfaces, with the main theorem assembled from named hypotheses.  It does not
reproduce or depend on the registered proof, and the registration does not extend to it.

## Layout

- `VaughtConjecture/` — the library.  Every module under it is built and audited (the lakefile globs are
  authoritative; `VaughtConjecture.lean` is an intentionally empty root).  Organized by mathematical topic.
- `roadmap/` — the roadmap: [`roadmap/README.md`](roadmap/README.md) is the
  mathematical roadmap and [`roadmap/IMPLEMENTATION.md`](roadmap/IMPLEMENTATION.md) the
  implementation order with its checkpoints, with the semantic contract, expositions, Lean
  sketches, and sources alongside.  New mathematics is added only when it advances a roadmap target.
- `scripts/`, `.github/` — build and audit infrastructure.

## Building and checking

```sh
lake build
bash scripts/check.sh --no-build
```

CI runs the same: build against the pinned dependencies, then check that there is no `sorry`,
no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`, Mathlib's linter set with
warnings as errors, and copyright headers.

The only pins are `lean-toolchain` and the InfinitaryLogic and ComputableModelTheory revisions in
`lakefile.toml`; Mathlib is inherited from InfinitaryLogic's manifest, and the toolchain must equal
InfinitaryLogic's.  To bump: change `rev`, run `lake update InfinitaryLogic` (or `lake update
ComputableModelTheory`), copy InfinitaryLogic's `lean-toolchain`, commit the manifest.  The
pinned Mathlib differs from the one in the registered formalization; the two developments do not
share a build.

## Contributing

Work lands through pull requests, one topic each, in changes of a few hundred to a thousand lines:
implementation, review against the [TauCeti review
rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics) (used as guidance), then
external review before merging.  Each PR names the layer of [`roadmap/README.md`](roadmap/README.md)
it advances (`Roadmap: Layer 3`), or `Roadmap: none` for infrastructure.  Mathlib style throughout;
no compatibility shims.  Prose, docstrings, and declaration names use mathematical terminology only:
they speak of mathematical objects, hypotheses, constructions, and theorems, never of workflow roles
such as producer, consumer, supplier, or certificate.  "Library conventions" in
[`roadmap/README.md`](roadmap/README.md#library-conventions) lists these conventions: the words to
avoid, one word per notion, declaration names, `## Placement` sections, and the review rubrics.

## Citing

For this repository, cite its URL and a commit hash.  For the counterexample theorem itself, cite
the registered formalization: Nathanael Ackerman, Cameron Freer and Robin Knight, *A counterexample
to Vaught's conjecture for infinitary logic*, Palomar entry PALOMAR-2026-10-07-000001, version 1,
`cameronfreer/vaught-conjecture-palomar` at commit `032ccb7a25b0ff6227128aa0aeba549c5901ea9a`, 2026.
Classification: MSC 2020 03C15, 03C75, 03E15; arXiv math.LO.

## License

Apache 2.0; see [`LICENSE`](LICENSE).
