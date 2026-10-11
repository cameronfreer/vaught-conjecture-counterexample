# Milestone: the main theorem, 11 October 2026

The proof of the main theorem with no hypothesis, its axioms, and the checks that verify it, at
one commit.  Proposed tag: `main-theorem-2026-10-11`, an annotated tag on the commit below.

## The verified commit

| Item | Value |
| --- | --- |
| Commit | `b00bb878b12a1ef75b9aecf1ef5a1e6577645ff4` (`main`, "Check the main theorem against an external reference statement with Comparator (#200)") |
| Tree | `11e32e27566e5408ffb00c14196a89aab3d8e16c` |
| Toolchain | `leanprover/lean4:v4.35.0-rc3` (`lean-toolchain`) |
| InfinitaryLogic | [`cameronfreer/infinitary-logic`](https://github.com/cameronfreer/infinitary-logic) at `e460cb6f0bac62bbc23415f8f7957d2b00cd1172` |
| ComputableModelTheory | [`cameronfreer/computable-model-theory`](https://github.com/cameronfreer/computable-model-theory) at `a1fe76155a98f03933f7de0811e03b2473dd2e21` |
| Mathlib | the fork [`cameronfreer/mathlib4`](https://github.com/cameronfreer/mathlib4) at `346a4bd3f95e8591976c91259badc6d2c300f638`, inherited from InfinitaryLogic's manifest (`lake-manifest.json`): upstream mathlib4 `c55e6e7` plus three commits that only add `Mathlib/ModelTheory/Infinitary` (with its tests and the umbrella file `Mathlib.lean`) |

The remaining revisions of `lake-manifest.json` (checkdecls, LeanArchitect, plausible,
LeanSearchClient, importGraph, ProofWidgets4, aesop, Qq, batteries, Cli) are inherited and are
recorded there.  CI on this commit: run
[38170251484](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/38170251484)
(push to `main`), whose job `build` (build with warnings as errors, `scripts/check.sh --no-build`,
the dependency manifest) passed and whose job `comparator-clean` (`comparator/clean_check.sh`)
passed: a fresh clone of the commit, the root library built from nothing (1027 s, 2715 jobs),
then `comparator/check.sh --exact` in the mode "exact commit
b00bb878b12a1ef75b9aecf1ef5a1e6577645ff4", with "Lean default kernel accepts the solution" and
"nanoda kernel accepts the solution", and the three expected failures rejected with their
intended diagnostics.

## The theorem

`VaughtConjecture/MainTheorem/GrowthLevelRoute.lean`, namespace `VaughtConjecture`, with
`densitySentence` the sentence `baseLanguage.densitySentence` of
`VaughtConjecture/Language/Density.lean`:

```lean
theorem MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_padded Expansion.receivingStableCappedReceiving_levels
    Realization.hollowReceiving_levels
```

The conclusion, `MainTheorem.HasThinAlephOneSpectrum` (`VaughtConjecture/MainTheorem/Spectrum.lean`):

```lean
def HasThinAlephOneSpectrum {L : Language.{0, 1}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω) : Prop :=
  Cardinal.mk (Quotient (isoSetoid φ)) = Cardinal.aleph 1 ∧
    ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels
```

The models of the sentence coded on `ℕ` have exactly `ℵ₁` isomorphism classes, and there is no
perfect set of pairwise nonisomorphic such models.  The sentence is in a countable relational
language with one relation symbol for each legal stage type at stage `ω`.  Its two arguments are
(R4) and (R3) for receiving models, `Expansion.receivingStableCappedReceiving_levels` and
`Realization.hollowReceiving_levels` (same file); (R2) for receiving models,
`Realization.receivingResidualReceiving_of_padded`, enters inside
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_padded`
(`VaughtConjecture/MainTheorem/LowPaddedRoute.lean`).

## The statements on all countable carriers

Same file and namespace, each with no hypothesis:

```lean
theorem MainTheorem.vaughtCounterexample_allCarriers :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧ ¬ φ.PerfectSetDichotomyAllCountable ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure)
```

```lean
theorem MainTheorem.vaughtCounterexample_allCarriers_densitySentence :
    HasThinAlephOneSpectrum densitySentence.{0} ∧
      HasThinAlephOneSpectrumOnCountableCarriers.{w} densitySentence.{0} ∧
      ¬ densitySentence.{0}.PerfectSetDichotomyAllCountable ∧
      (∀ (M : Type w) [baseLanguage.{0}.Structure M], densitySentence.Realize M → Infinite M) ∧
      ∀ (M : Type w) [baseLanguage.{0}.Structure M] [Countable M], densitySentence.Realize M →
        ∃ c : StructureSpace baseLanguage.{0}, c ∈ ModelsOf densitySentence.{0} ∧
          Nonempty (@Language.Equiv baseLanguage.{0} M ℕ _ c.toStructure)
```

```lean
theorem MainTheorem.exists_mem_modelsOf_densitySentence_equiv.{v} (M : Type v)
    [baseLanguage.{0}.Structure M] [Countable M] (h : densitySentence.Realize M) :
    ∃ c : StructureSpace baseLanguage.{0}, c ∈ ModelsOf densitySentence.{0} ∧
      Nonempty (@Language.Equiv baseLanguage.{0} M ℕ _ c.toStructure)
```

The countable models on the carriers of an arbitrary universe `w` also have exactly `ℵ₁`
isomorphism classes (`MainTheorem.HasThinAlephOneSpectrumOnCountableCarriers`,
`VaughtConjecture/MainTheorem/AllCarriers.lean`), the library's perfect-set dichotomy on all coded
tiers fails, the density sentence has no finite model, and every countable model is isomorphic to
a coded one.  Satisfaction is `Sentenceω.Realize` on the carrier and isomorphism is
`Language.Equiv`.

## Axioms

Every declaration of the library, the main theorem included, depends only on `propext`,
`Classical.choice` and `Quot.sound`.

* **The library-wide audit.**  `scripts/check.sh` generates a file that imports every module
  under `VaughtConjecture/` and runs the command of `scripts/AxiomAudit.lean`: for every
  declaration in the namespace `VaughtConjecture` or declared in a `VaughtConjecture` module, the
  axioms (`collectAxioms`) must be among the three.  `sorryAx`, `Lean.ofReduceBool`
  (`native_decide`) and any axiom declared in the library fail it, and an audit that checks no
  declaration fails.  CI runs it on every push to `main` and every pull request.
* **The dependency manifest.**  `scripts/manifest.sh` (with `scripts/Manifest.lean`) records,
  for the main theorem and for `Realization.receivingResidualReceiving_of_padded`,
  `Realization.hollowReceiving_levels`, `Expansion.receivingStableCappedReceiving_levels` and
  `StageType.hasLadderGrowthCarriersStableAtSeed_levels`: the commit, tree and toolchain, the
  elaborated statement, the declaration dependency cone with its library declarations and their
  modules, and the axioms, checked to equal `collectAxioms`; and the import closure of
  `VaughtConjecture.MainTheorem.GrowthLevelRoute`.  It is a record for review, not a check; CI
  uploads it as the artifact `dependency-manifest`.  Its summary at this commit (run 38170251484):

  ```text
  commit: b00bb878b12a1ef75b9aecf1ef5a1e6577645ff4
  tree: 11e32e27566e5408ffb00c14196a89aab3d8e16c
  working tree: clean (tracked files)
  lean-toolchain: leanprover/lean4:v4.35.0-rc3
  VaughtConjecture.MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels: 4002 library declarations (+1329 auxiliary) in 245 modules; 30002 constants in all; axioms: Classical.choice, Quot.sound, propext
  VaughtConjecture.Realization.receivingResidualReceiving_of_padded: 2164 library declarations (+643 auxiliary) in 113 modules; 13146 constants in all; axioms: Classical.choice, Quot.sound, propext
  VaughtConjecture.Realization.hollowReceiving_levels: 2516 library declarations (+920 auxiliary) in 145 modules; 13972 constants in all; axioms: Classical.choice, Quot.sound, propext
  VaughtConjecture.Expansion.receivingStableCappedReceiving_levels: 2537 library declarations (+924 auxiliary) in 142 modules; 14132 constants in all; axioms: Classical.choice, Quot.sound, propext
  VaughtConjecture.StageType.hasLadderGrowthCarriersStableAtSeed_levels: 2172 library declarations (+844 auxiliary) in 107 modules; 13104 constants in all; axioms: Classical.choice, Quot.sound, propext
  import closure of VaughtConjecture.MainTheorem.GrowthLevelRoute: 4793 modules, 357 of them library modules (112 outside every target cone)
  ```

## Verifying it

On a checkout of the commit, with the pinned toolchain:

```sh
git checkout b00bb878b12a1ef75b9aecf1ef5a1e6577645ff4
lake build
bash scripts/check.sh --no-build
bash scripts/manifest.sh            # writes .lake/audit/manifest.txt
bash comparator/check.sh --exact    # needs bwrap, jq, python3
bash comparator/clean_check.sh WORK_DIR   # WORK_DIR must not exist
```

What each establishes:

* `lake build` builds every module under `VaughtConjecture/` (the lakefile globs), with warnings
  as errors and Mathlib's linter set.
* `scripts/check.sh --no-build` checks that `lean-toolchain` equals InfinitaryLogic's; that no
  library source contains `sorry`, `admit`, `maxHeartbeats` or `set_option autoImplicit true`;
  that every module carries the copyright header; and the library-wide axiom audit above.
* `scripts/manifest.sh` writes the dependency manifest above for the checked-out commit (and
  says whether the working tree has uncommitted changes to tracked files).
* `comparator/check.sh --exact` checks, at the commit `HEAD` with no uncommitted change in its
  inputs (it refuses to run otherwise), that the solution module `comparator/Solution.lean`
  proves the reference statement `PalomarChallenge.independent_challenge` of
  `comparator/Challenge.lean`, from `MainTheorem.vaughtCounterexample_allCarriers_densitySentence`
  with `baseLanguage.densitySentence` as the witness: Comparator (`lake comparator`) replays the
  exported proof through Lean's kernel and nanoda, allows only `propext`, `Quot.sound` and
  `Classical.choice`, and checks that the solution's statement and every declaration it uses are
  identical to the reference's.  The reference statement is compiled in a sandbox whose search
  path has only Mathlib, Mathlib's own dependencies and the toolchain; its import closure contains
  no module of this repository, InfinitaryLogic, ComputableModelTheory or
  `Mathlib.ModelTheory.Infinitary`; and the sources of the Mathlib modules it imports are those of
  upstream mathlib4 `c55e6e7`.  Three expected failures (a weakened statement, an altered
  definition, a proof by `sorry`) must each be rejected with its intended diagnostic.
* `comparator/clean_check.sh WORK_DIR` runs the same check on a fresh clone of the committed
  `HEAD`, after building the root library from nothing (the dependencies' cached build outputs
  are reused).  CI runs it on every push to `main` (job `comparator-clean`), and
  `comparator/check.sh --exact` on every pull request (job `comparator-replay`).

The full account of the Comparator check, its two modes, its outputs and its expected results is
`comparator/README.md`.

## What the Comparator check does not establish

Verbatim from `comparator/README.md`, "What it does not establish", at this commit:

* That the reference statement expresses the intended mathematics: that needs a human reading of
  `Challenge.lean` (and of the Mathlib definitions it uses, such as `Perfect`, `Cardinal.aleph`
  and the product topology).
* Anything about this repository's own statements beyond the reference statement:
  `HasThinAlephOneSpectrum`, the clauses on all countable carriers, and the identity of the
  witness sentence are not compared.  The other theorems of the repository are checked by
  `lake build` and the axiom audit of `scripts/check.sh`, not by Comparator.
* That the cached build outputs of the dependencies correspond to their sources.  Checking a
  dependency's git revision and tracked files authenticates its sources, not its `.lake/build`
  outputs (Mathlib, `InfinitaryLogic`, `ComputableModelTheory`), which are read as they are.  The
  kernels re-check every exported proof term, so a wrong dependency output cannot make a false
  proof pass; but the declarations of the reference statement that come from Mathlib are read
  from those outputs too.  On a new pin, CI downloads the Mathlib cache artifacts available for
  the pinned revision (`lake exe cache get`), builds only the outputs missing from them
  (the Mathlib modules the public cache does not have for the fork, `InfinitaryLogic` and the
  classical entry module of `ComputableModelTheory`), and caches the result; later runs reuse
  that cache.  No run builds all of Mathlib.
* That the reference's build is invisible to the solution side: what is checked is that it is
  not on the solution's search path and that `Challenge` is not in the solution's import
  closure.
* In the working-tree mode, anything about a commit.
* The correctness of the toolchain binaries, of bubblewrap, or of the kernels themselves (Lean's
  kernel and nanoda are separate implementations; `--paranoid` adds four more).
* Any Palomar registration or review.

**Comparator does not replace human review of the reference statement.**  It checks that the
solution proves the statement of `Challenge.lean`; whether that statement says what it is meant to
say is for a human reader of `Challenge.lean` (`comparator/README.md`).  The reference statement is
existential and does not name the density sentence; it omits the clauses on all countable carriers
and is not stated through `HasThinAlephOneSpectrum`.

## Scope

* The theorem is a counterexample to Vaught's conjecture for `L_{ω₁,ω}` in a countable relational
  language.  It is not a counterexample to the first-order Vaught conjecture.
* It is proved for the sentence `baseLanguage.densitySentence` of this repository, following the
  construction of [Kni26] and [AFK26].  The sentence is not claimed to formalize every claim of
  the manuscript, and its models are not identified with the manuscript's class of strongly coded
  templates.
* The proof goes through receiving models (models with finite-cut receiving): it uses (R2), (R3)
  and (R4) for receiving models only.  (R1) for every model (`Expansion.FiniteCutReceiving`) and
  (R2) for every model (`Realization.ResidualReceiving`) remain open, and so do (R3) and (R4) for
  every model (`Realization.HollowReceiving` for `Realization.IsCoverHollowAtBlock`,
  `StableCappedReceiving`): none of them is proved here, and the main theorem does not use them.
  The status of each statement is in `roadmap/DASHBOARD.md`.
* The greatest receiving index of a class (`MainTheorem.exists_isGreatest_receivingIndex`,
  `MainTheorem.receivingLastStage`, `VaughtConjecture/MainTheorem/ReceivingLastStage.lean`) is
  about receiving expansions only: it is not an index of the unrestricted expansion domains
  (`Expansion.expansionDomain`), whose last-stage theorems remain conditional on (R1) and
  next-block uniqueness of models, and it is not a Scott rank.

## The tag

To be created by the owner on the commit above (the job `comparator-clean` of run 38170251484
has passed):

```sh
git fetch origin
git tag -a main-theorem-2026-10-11 b00bb878b12a1ef75b9aecf1ef5a1e6577645ff4 \
  --cleanup=whitespace -F milestones/2026-10-11-main-theorem.md
git push origin main-theorem-2026-10-11
```

The tag message is this file, read from a checkout that contains it (`--cleanup=whitespace`
keeps its headings, which the default cleanup would remove as comment lines).  The tag names the
commit `b00bb87`, which does not contain this file.
