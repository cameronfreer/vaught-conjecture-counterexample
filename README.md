# A counterexample to Vaught's conjecture for $L_{\omega_1,\omega}$

[![CI](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/workflows/ci.yml?query=branch%3Amain)

By Nathanael Ackerman, Cameron Freer, and Robin Knight.

A Lean 4 proof that a sentence of the infinitary logic $L_{\omega_1,\omega}$, in a countable
relational language, has exactly $\aleph_1$ countable models up to isomorphism and no perfect set
of pairwise non-isomorphic countable models, following [Kni26] and [AFK26] (see
[`roadmap/REFERENCES.bib`](roadmap/REFERENCES.bib)).  It is a counterexample to Vaught's
conjecture for $L_{\omega_1,\omega}$, not to the first-order Vaught conjecture.  The
formalization proves the stated theorem for its own sentence, `baseLanguage.densitySentence`,
following the construction of the manuscript; it does not formalize every claim of [AFK26], and it
does not identify the models of that sentence with the manuscript's class of strongly coded
templates.

## Status

The main theorem is proved, with no hypotheses:
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels : HasThinAlephOneSpectrum baseLanguage.densitySentence`.
Axioms: `propext`, `Classical.choice`, `Quot.sound` (audited in CI).  Pinned: Lean
`v4.35.0-rc3`, [InfinitaryLogic](https://github.com/cameronfreer/infinitary-logic) `eb9f12d`,
[ComputableModelTheory](https://github.com/cameronfreer/computable-model-theory) `a1fe761`.
Not covered: the first-order Vaught conjecture.  Statements the proof does not use, among them
(R1) and (R2) for every model, remain open; see [`roadmap/DASHBOARD.md`](roadmap/DASHBOARD.md).

## The theorem

[`MainTheorem/GrowthLevelRoute.lean`](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/main/VaughtConjecture/MainTheorem/GrowthLevelRoute.lean)
(namespace `VaughtConjecture`):

```lean
theorem MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels :
    HasThinAlephOneSpectrum densitySentence.{0}
```

The sentence is
[`baseLanguage.densitySentence`](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/main/VaughtConjecture/Language/Density.lean),
in a language with one relation symbol for each legal stage type at stage `ω`.  The conclusion is
[`MainTheorem.HasThinAlephOneSpectrum`](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/main/VaughtConjecture/MainTheorem/Spectrum.lean):

```lean
def HasThinAlephOneSpectrum {L : Language.{0, 1}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω) : Prop :=
  Cardinal.mk (Quotient (isoSetoid φ)) = Cardinal.aleph 1 ∧
    ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels
```

that is, the models of `φ` coded on `ℕ` have exactly `ℵ₁` isomorphism classes, and there is no
perfect set of pairwise non-isomorphic such models.

## Checking it

```sh
lake build
bash scripts/check.sh --no-build
```

`scripts/check.sh` checks the toolchain against InfinitaryLogic's, placeholders and copyright
headers, and audits every declaration of the library for axioms beyond the three above.  To print
the axioms of the main theorem alone:

```sh
echo 'import VaughtConjecture.MainTheorem.GrowthLevelRoute
#print axioms VaughtConjecture.MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels' \
  | lake env lean --stdin
```

The library builds on [Mathlib](https://github.com/leanprover-community/mathlib4),
[InfinitaryLogic](https://github.com/cameronfreer/infinitary-logic) (syntax and semantics of
$L_{\omega_1,\omega}$, Scott analysis, model-code spaces, Morley counting), and
[ComputableModelTheory](https://github.com/cameronfreer/computable-model-theory) (classical
Fraïssé interfaces, factorization of tuples through age representatives, orbit isolation, atomic
and prime structures).  Mathlib is inherited from InfinitaryLogic's manifest (the fork
`cameronfreer/mathlib4` at `346a4bd`), so `lake exe cache get` covers only part of it.  CI runs the
same commands on every push to `main` and every pull request.

The main theorem is also checked against an external reference statement with Comparator
(`bash comparator/check.sh --exact`; [`comparator/README.md`](comparator/README.md)), and the
proof milestone, with its commit, pins, axioms and checks, is recorded in
[`milestones/2026-10-11-main-theorem.md`](milestones/2026-10-11-main-theorem.md).

## Reading the proof

Under `VaughtConjecture/`: finite structures (`Stage/Basic.lean`, and the coatom extension theorem
in `Extension/ProfileTowerCompletion.lean`); the sentence and its models (`Language/Density.lean`,
`Realization/Model.lean`); the receiving constructions (`MainTheorem/LowPaddedRoute.lean`,
`MainTheorem/GrowthLevelRoute.lean`); expansion and classification
(`MainTheorem/ReceivingRoute.lean`); the count (`MainTheorem/Spectrum.lean`).  The statement on
countable models on arbitrary carriers is `MainTheorem.vaughtCounterexample_allCarriers`, and
`MainTheorem.vaughtCounterexample_allCarriers_densitySentence` for `baseLanguage.densitySentence`
by name (both in `MainTheorem/GrowthLevelRoute.lean`).  The full map is
[`roadmap/README.md`](roadmap/README.md); compiled refutations of candidate statements are in the
`*Counterexample*.lean` modules, indexed in [`roadmap/DASHBOARD.md`](roadmap/DASHBOARD.md).

## Propositions 4.32, 4.34 and 4.35, Lemma 4.33, Claim 4.37, Theorem 4.36 and Section 2 of [AFK26]

For the strongly coded template system, the formal counterparts of three propositions of [AFK26]
are proved, using at most the three axioms above, relative to the current draft of 7 October 2026
(not part of this repository; pinned by the SHA-256 of its source, `654b2780…`), not to a
published version.  Proposition 4.32, the hereditary, joint embedding and amalgamation properties
of the charts `C_β[L]`: `IsTemplateChart.hereditary`, `IsTemplateChart.jointEmbedding` and
`IsTemplateChart.amalgamation`, the last two for `β < ω₁`
([`Correspondence/Charts/Chart.lean`](VaughtConjecture/Correspondence/Charts/Chart.lean)).
Proposition 4.34, Boundedness, Reconstruction and Limits: `proposition434Target`, derived from the
stronger `proposition434Clauses_of_countable` (countable carriers, `β < ω₁`, no sentence premise),
with level zero the separate theorem `exists_lift_zero_of_realize_templateSentence`
([`Correspondence/Proposition434.lean`](VaughtConjecture/Correspondence/Proposition434.lean); notes
in [`milestones/2026-10-15-proposition-4-34.md`](milestones/2026-10-15-proposition-4-34.md)).
Proposition 4.35, at most countably many countable structures maximal at each level `β < ω₁`, up
to isomorphism in the full template language: `proposition435Target`, derived from the stronger
`maximalCountTarget`
([`Correspondence/Maximality/Count.lean`](VaughtConjecture/Correspondence/Maximality/Count.lean));
maximality is the printed Definition 2.20, `IsMaximalAt`, transcribed with its allowance for an
unchanged higher lift (notes in
[`milestones/2026-10-15-proposition-4-35.md`](milestones/2026-10-15-proposition-4-35.md)).  These are statements
about the classes `K_β` of the template dictionary (`templateStageClass`) and the repository's own
sentence `templateSentence`, the transcription of `σ[L]`.  No identification of `templateSentence`
with `baseLanguage.densitySentence`, and no transfer of the spectrum between them, is claimed; the
native count of strongly coded terminal realizations,
`Realization.stronglyCodedTerminalClasses_countable`, is an input of the proof of Proposition 4.35
and is distinct from it.

Claim 4.37 (in the proof of Theorem 4.36), Definition 2.21 for the models of `templateSentence`,
and Lemma 4.33 are proved for the same system, relative to the same pinned draft, using at most
the three axioms above.  Claim 4.37, on countable carriers and for `β < ω₁`: the lift stages of
the base reduct of a member of `K_β` have an attained greatest element (`greatestLiftStageTarget`),
a member of `K_γ` is maximal at `γ` exactly when `γ` is that greatest stage
(`maximalIffGreatestTarget`), every member of `K_β` has a maximal completion
(`maximalCompletionTarget`), unique with its stage (`maximalLiftUniqueTarget`,
`maximalCompletionUniqueTarget`), and every lift of the same base is a projection of it
(`lowerLiftsAreProjectionsTarget`); every model of `templateSentence` on a countable nonempty
carrier has exactly one maximal lift (`sentenceMaximalLiftTarget`).  Definition 2.21: every
closed tuple of such a model is eventually determined (`sentenceEventualDeterminationTarget`, from
`eventualDeterminationTarget` and `relMap_projectStructure_invariant_iff_project_eq`), at a least
threshold with an actual lift there, the projection of the maximal lift, for every positive arity
(the invariants of rank zero included), and in every lift at a stage `ζ` with `ξ ≤ ζ`, which
strengthens the printed strict inequality; no rank is identified with a stage
([`Correspondence/Maximality/Completion.lean`](VaughtConjecture/Correspondence/Maximality/Completion.lean)).
Lemma 4.33, for `β < ω₁` and every countably infinite carrier: one structure of `K_β`, chosen
before any chart is named, into which every chart of `C_β[L]` embeds, and over which every chart
embedding extends every embedding of its root, with a commuting square and exact realization of
the chart, the empty root stated separately (`universalChartModelTarget`).  It is built
positionally (`stronglyCodedUniversalRealizationTarget`) and read through its classes
(`stronglyCodedUniversalReadingTarget`), without a previously given class realization with donor
density; universality gives density at every cutoff below the block stage, zero included
(`universalityDensityTarget`, with `LegalClass.truncEquiv_project_of_le` for donors of every
rank) ([`Correspondence/Charts/UniversalTheorem.lean`](VaughtConjecture/Correspondence/Charts/UniversalTheorem.lean)
and the files `Universal*.lean` beside it).

Theorem 4.36 for `templateSentence` is proved for the same system, relative to the same pinned
draft, using at most the three axioms above, as the concrete template-system specialization of
the route of Section 2 of [AFK26]: `theorem436Target : Theorem436Target`, where
`Theorem436Target := MainTheorem.HasThinAlephOneSpectrum templateSentence.{0}`
([`Correspondence/TemplateSystem/Theorem436.lean`](VaughtConjecture/Correspondence/TemplateSystem/Theorem436.lean)
and
[`Correspondence/TemplateSystem/BackAndForth.lean`](VaughtConjecture/Correspondence/TemplateSystem/BackAndForth.lean)).
It concerns the models of `templateSentence` coded on `ℕ`, and its two conclusions have separate
proofs.  The count: exactly $\aleph_1$ isomorphism classes of models coded on `ℕ`
(`templateSentenceAlephOneTarget`,
[`Correspondence/TemplateSystem/AlephOne.lean`](VaughtConjecture/Correspondence/TemplateSystem/AlephOne.lean)),
with the maximal stage of a class as the rank (`maximalStageOfClass`), defined using the greatest
lift stage rather than the least projection-fixing stage.  Thinness: no perfect set of pairwise
non-isomorphic models coded on `ℕ` (`thinnessTarget`), from countably many back-and-forth classes
at every level below $\omega_1$ (`countableBFClassesTarget`, through the back-and-forth core
`backAndForthCoreTarget`) and `MainTheorem.isThinOnNatModels_of_countable_bfClasses`.  The
inputs: the four conditions of [AFK26, Definition 2.23] for this system,
`templateSystemConditionsTarget` (`maximalCoverageTarget`, `uniformMaximalRepresentativesTarget`,
`attainedEventualDeterminationTarget`, `invariantOccurrenceTarget`;
[`Correspondence/TemplateSystem/Conditions.lean`](VaughtConjecture/Correspondence/TemplateSystem/Conditions.lean));
the weak-system interface (`templateInvariantSystemTarget`, `templateInvariantSystem_projection`,
`weakSystemClausesTarget`, `projectedDensityAt_of_satisfiesDensityAt`, and the base as the models
of `templateSentence` on countable nonempty carriers, `templateBaseModelsTarget`;
[`Correspondence/TemplateSystem/WeakSystem.lean`](VaughtConjecture/Correspondence/TemplateSystem/WeakSystem.lean));
and the countability of the language (`baseLanguageCountableTarget`).  The statement is about
models coded on `ℕ`; a spectrum statement on all countable carriers is not made here.  This is a
distinction of scope, not an obstruction: the empty structure also satisfies `templateSentence`,
so an all-carriers formulation would count one further isomorphism class, and the passage from
models on countable nonempty carriers to models coded on `ℕ` is proved
(`nonemptyCarrierPassageTarget`, `templateModelInfiniteTarget`).  `theorem436Target` is not
itself a statement about arbitrary systems; Proposition 2.18 and Theorems 2.19, 2.25 and 2.27 of
[AFK26] for arbitrary systems, and a second proof of Theorem 4.36 through them, are the next two
paragraphs.  The theorem
concerns `templateSentence` separately from, and without reference to, the main theorem for
`baseLanguage.densitySentence` (`MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels`).  As
above, no identification of `templateSentence` with `baseLanguage.densitySentence`, and no
transfer of the spectrum between them, is claimed.

Proposition 2.18 and Theorems 2.19, 2.25 and 2.27 of Section 2 of [AFK26] are proved for arbitrary
systems, relative to the same pinned draft, using at most the three axioms above, in
[`Correspondence/Systems`](VaughtConjecture/Correspondence/Systems) (namespace
`VaughtConjecture.Correspondence`; the statements are collected in `Targets.lean`): weak systems
(Definition 2.17, `WeakSystem`) and qualifying systems (Definition 2.23, `QualifyingSystem`; the
manuscript's term is "Knight system") for an arbitrary geometry signature, invariance diagram and
invariant system.  Proposition 2.18: on countable carriers, members of `K_β` that realize a common
invariant have base reducts back-and-forth equivalent at level `β`
(`WeakSystem.bfEquivOfCommonInvariantTarget`, from the form for tuples matched through a common
pattern, `WeakSystem.bfEquivOfPatternMatchedTarget`).  Theorem 2.19: for a sentence `φ`, if at
every countable level `β` the classes of models of `φ` coded on `ℕ` that contain a model with no
lift in `K_β` are countably many, then at every level below $\omega_1$ the models of `φ` coded on
`ℕ` fall into countably many back-and-forth classes (`WeakSystem.countableBFClassesTarget`, and
the stronger `WeakSystem.countable_bfClasses_of_countable_classesWithoutLift`, with no premise
that the sentence axiomatizes the base), so there is no perfect set of pairwise non-isomorphic
coded models (`WeakSystem.thinnessTarget`).  Theorem 2.25 (a), in its general form: the base of a
qualifying system has exactly $\aleph_1$ isomorphism classes on the carriers `Fin (n + 1)` and
`ℕ`, finite carriers included and with no infiniteness premise
(`QualifyingSystem.mkBaseClassesEqAlephOneTarget`); for a sentence axiomatizing the base on all
countable nonempty carriers, its models coded on every `Fin (n + 1)` and on `ℕ` have exactly
$\aleph_1$ classes (`QualifyingSystem.mkModelClassesEqAlephOneTarget`).  Theorem 2.25 (b): no
perfect set of pairwise non-isomorphic models coded on `ℕ` of a qualifying sentence, with no
infiniteness premise (`QualifyingSystem.noPerfectSetTarget`).  Theorem 2.27 is proved only in a
form coded on `ℕ`, which is distinct from the general count:
`QualifyingSystem.hasThinAlephOneSpectrumTarget` gives `MainTheorem.HasThinAlephOneSpectrum φ`
for a qualifying sentence `φ` under the explicit extra premise `CountableMembersInfinite` (every
member of `K` on a countable carrier is infinite), which removes the finite carriers from the
count; it is a specialization and does not replace Theorem 2.25 (a).  The printed back-and-forth
systems and their relation `≡_β` are not formalized: InfinitaryLogic's `BFEquiv` and
`bfEquivSetoid` are used in their place, and no correspondence between `BFEquiv β` and `≡_β` is
claimed.  Neither Reconstruction nor the uniqueness of maximal lifts is a field or a premise of
any of these abstract theorems.

`K[L]` is an instance: `templateQualifyingSystem` is a qualifying system whose classes are
`templateStageClass`, and `templateQualifyingSentenceTarget` proves that its members on countable
carriers are infinite and that `templateSentence` is a qualifying sentence for it
([`Correspondence/Systems/TemplateQualifying.lean`](VaughtConjecture/Correspondence/Systems/TemplateQualifying.lean)).
The abstract Theorem 2.27 applied to this instance is a second proof of Theorem 4.36,
`theorem436Target_abstract : Theorem436Target`
([`Correspondence/Systems/Theorem436.lean`](VaughtConjecture/Correspondence/Systems/Theorem436.lean)),
stated separately from `theorem436Target`, which it does not replace.  The two proofs depend on
different results about `K[L]`.  The concrete proof uses Reconstruction (`reconstructionTarget`),
the uniqueness of maximal lifts (`maximalLiftUniqueTarget`) and the isomorphism invariance of the
maximal stage (`maximalStageInvariantTarget`).  The abstract theorems assume neither
Reconstruction nor the uniqueness of maximal lifts; the `K[L]` instance uses Reconstruction
through the maximal completion (`maximalCompletionTarget`) in conditions (a) and (c), and uses
neither the uniqueness of maximal lifts nor the isomorphism invariance of the maximal stage.  Both
proofs concern `templateSentence` and its models coded on `ℕ`; neither identifies
`templateSentence` with `baseLanguage.densitySentence`, and no spectrum result is transferred
between them.

The statements of [AFK26] audited against its published version on 25 October 2026, Definitions
2.6–2.8, 2.10, 2.17, 2.20, 2.21 and 2.23, Proposition 2.18, Theorems 2.19, 2.25 and 2.27,
Definitions 4.6, 4.11, 4.13, 4.16, 4.20–4.22, 4.29 and 4.31, Propositions 4.30, 4.32, 4.34 and
4.35, Lemma 4.33, Theorem 4.36 and Claim 4.37 (every statement named in this section among them),
read identically, in number and text, in the pinned draft and in [AFK26] v1,
[hexagon:2610.00188v1](https://hexagonmath.org/2610.00188v1)
([`milestones/2026-10-25-published-v1-audit.md`](milestones/2026-10-25-published-v1-audit.md)).

## Citation

GitHub's "Cite this repository" uses [`CITATION.cff`](CITATION.cff):

```bibtex
@software{AckermanFreerKnightVaughtCounterexampleLean,
  author  = {Ackerman, Nathanael and Freer, Cameron and Knight, Robin},
  title   = {Formalization of a counterexample to {Vaught}'s conjecture for {$L_{\omega_1\omega}$}},
  year    = {2026},
  url     = {https://github.com/cameronfreer/vaught-conjecture-counterexample},
  version = {main-theorem-2026-10-11},
  note    = {Lean 4; tag main-theorem-2026-10-11, commit b00bb878b12a1ef75b9aecf1ef5a1e6577645ff4},
  license = {Apache-2.0}
}
```

For the mathematics, cite our initial paper [AFK26],
[hexagon:2610.00188](https://hexagonmath.org/2610.00188) (entry `AFK26` of
[`roadmap/REFERENCES.bib`](roadmap/REFERENCES.bib)), which explains the proof strategy and many
details. A fuller account of the proof will follow.

A separate formalization of the same theorem
by the same authors is registered as Palomar entry
[PALOMAR-2026-10-07-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000001&version=1)
([`cameronfreer/vaught-conjecture-palomar`](https://github.com/cameronfreer/vaught-conjecture-palomar)
at commit `032ccb7a25b0ff6227128aa0aeba549c5901ea9a`, theorem
`PalomarChallenge.independent_challenge`); this repository does not depend on it, and the
registration does not extend to it.

## Contributing and license

See [`CONTRIBUTING.md`](CONTRIBUTING.md).  Apache 2.0; see [`LICENSE`](LICENSE).
