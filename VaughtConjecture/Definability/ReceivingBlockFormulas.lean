/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Definability.BlockDetermination

/-!
# The chart formulas at a given model expansion

Roadmap, the quantitative reconstruction pathway of `roadmap/COMPANIONS.md` ("Further companion
results"), row 1, relative to a given model expansion.

The correctness theorem of the chart formulas (`realize_blockFormula_iff`) assumes block
determination (`CoverThresholds.Determines`) at every model expansion to `λ_{ξ+1}`, `ξ < η`.  For
the forcing thresholds that hypothesis follows from finite-extension receiving of **every** model
expansion (`forcingThresholds_determines`), which is (R1) and is not proved.  The recursion of the
correctness proof, however, applies block determination only at the stage reductions of the given
expansion `R` to the block stages `λ_{ξ+1}`, `ξ < η`.  Here block determination is asked at those
reductions only (`CoverThresholds.DeterminesAt`).

**Results.**

* `forcingThresholds_determinesAt` (proved, in `VaughtConjecture.Definability.BlockDetermination`):
  block determination by the forcing thresholds at a given realization at `λ_{η+1}` that is
  exactly consistent, has legal types and has the finite-extension receiving property, with forcing
  donors at `η`.  It is the threshold lemma (`Realization.le_label_iff_exists_forcesThreshold`) for
  that realization.
* `realizeBlockFormulaOfDeterminesAtTarget` (proved, by
  `realize_blockFormula_iff_of_determinesAt`): the recursion.  In a model expansion `R` to `λ_η`
  whose reductions to `λ_{ξ+1}`, `ξ < η`, have block determination, the formula of `t` holds of
  exactly the covers of `t` in `R`.  The successor step is
  `BlockRecursion.realize_succFormula_of_determinesAt` and the limit step is
  `BlockRecursion.realize_limitFormula`, with the induction hypothesis applied to the reductions of
  `R`, whose further reductions are reductions of `R` (`Realization.reduce_reduce`).

The general correctness theorem (`realize_blockFormula_iff`) is unchanged; under its hypothesis
every model expansion has block determination at all its reductions
(`CoverThresholds.determines_iff_forall_determinesAt`).

## Placement

`roadmap/COMPANIONS.md`, Further companion results, Quantitative reconstruction, row 1.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language

/-- **Target: correctness of the chart formulas at a given model expansion.**  For threshold data
`U`, a countable block index `η` and a model expansion `R` to `λ_η` of a base structure `M`, if the
stage reduction of `R` to each block stage `λ_{ξ+1}`, `ξ < η`, has block determination for `U ξ`
(`CoverThresholds.DeterminesAt`), then the formula of every stage type `t` at `λ_η` holds of a
tuple exactly when the tuple covers `t` in `R`.  Given-model statement; the formula does not depend
on `R`.  Proved (`realize_blockFormula_iff_of_determinesAt`). -/
def RealizeBlockFormulaOfDeterminesAtTarget : Prop :=
  ∀ (U : ∀ ξ : Ordinal.{0}, CoverThresholds ξ) ⦃η : Ordinal.{0}⦄ (hη : η < ω₁) ⦃M : Type w⦄
    [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage η)),
    (∀ ξ < η, (U ξ).DeterminesAt (R.1.reduce (isSuccPrelimit_blockStage (ξ + 1)))) →
      ∀ ⦃k : ℕ⦄ (t : StageType.{0} (blockStage η) k) (c : Fin k → M),
        (blockFormula U η hη t).Realize c ↔ R.1.Covers t c

/-- Correctness of the chart formulas at a given model expansion. -/
theorem realizeBlockFormulaOfDeterminesAtTarget : RealizeBlockFormulaOfDeterminesAtTarget.{w} :=
  fun U _ hη _ _ R hU _ t c ↦ realize_blockFormula_iff_of_determinesAt U hη R hU t c

end VaughtConjecture
