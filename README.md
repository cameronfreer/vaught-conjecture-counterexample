# A counterexample to Vaught's conjecture for $L_{\omega_1,\omega}$

[![CI](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/workflows/ci.yml?query=branch%3Amain)

By Nathanael Ackerman, Cameron Freer, and Robin Knight.

A Lean 4 proof that a sentence of the infinitary logic $L_{\omega_1,\omega}$, in a countable
relational language, has exactly $\aleph_1$ countable models up to isomorphism and no perfect set
of pairwise non-isomorphic countable models, following the drafts [Kni26] and [AFK26] (see
[`roadmap/REFERENCES.bib`](roadmap/REFERENCES.bib)).  It is a counterexample to Vaught's
conjecture for $L_{\omega_1,\omega}$, not to the first-order Vaught conjecture.

## Status

The main theorem is proved, with no hypotheses:
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels : HasThinAlephOneSpectrum baseLanguage.densitySentence`.
Axioms: `propext`, `Classical.choice`, `Quot.sound` (audited in CI).  Pinned: Lean
`v4.35.0-rc3`, InfinitaryLogic `e460cb6`, ComputableModelTheory `a1fe761`.
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

Mathlib is inherited from InfinitaryLogic's manifest (the fork `cameronfreer/mathlib4` at
`346a4bd`), so `lake exe cache get` covers only part of it.  CI runs the same commands on every
push to `main` and every pull request.

## Reading the proof

Under `VaughtConjecture/`: finite structures (`Stage/Basic.lean`, and the coatom extension theorem
in `Extension/ProfileTowerCompletion.lean`); the sentence and its models (`Language/Density.lean`,
`Realization/Model.lean`); the receiving constructions (`MainTheorem/LowPaddedRoute.lean`,
`MainTheorem/GrowthLevelRoute.lean`); expansion and classification
(`MainTheorem/ReceivingRoute.lean`); the count (`MainTheorem/Spectrum.lean`).  The full map is
[`roadmap/README.md`](roadmap/README.md); compiled refutations of candidate statements are in the
`*Counterexample*.lean` modules, indexed in [`roadmap/DASHBOARD.md`](roadmap/DASHBOARD.md).

## Citation

GitHub's "Cite this repository" uses [`CITATION.cff`](CITATION.cff):

```bibtex
@software{FreerVaughtCounterexampleLean,
  author  = {Freer, Cameron},
  title   = {Formalization of a counterexample to {Vaught}'s conjecture for {$L_{\omega_1\omega}$}},
  year    = {2026},
  url     = {https://github.com/cameronfreer/vaught-conjecture-counterexample},
  version = {8030d62},
  note    = {Lean 4; commit 8030d6229ad758f55e5e13fe5d5de1667d7b006d},
  license = {Apache-2.0}
}
```

For the mathematics, cite the manuscript [AFK26] (entry `AFK26` of
[`roadmap/REFERENCES.bib`](roadmap/REFERENCES.bib)).  A separate formalization of the same theorem
by the same authors is registered as Palomar entry
[PALOMAR-2026-10-07-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000001&version=1)
([`cameronfreer/vaught-conjecture-palomar`](https://github.com/cameronfreer/vaught-conjecture-palomar)
at `032ccb7`); this repository does not depend on it, and the registration does not extend to it.

## Contributing and license

See [`CONTRIBUTING.md`](CONTRIBUTING.md).  Apache 2.0; see [`LICENSE`](LICENSE).
