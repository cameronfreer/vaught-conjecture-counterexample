/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Existence
import VaughtConjecture.AlephOne.ScottAnalysis

/-!
# A model of cardinality `ℵ₁` and Scott rank `ω₁`

**Existence** (`AlephOne.existsAlephOneModelScottRankOmegaOneTarget`): some structure of the base
language on a carrier in `Type` satisfies the density sentence, has exactly `ℵ₁` points, has
internal Scott rank `ω₁`, and its semantic Scott process of every length beyond `ω₁ + 1` has rank
`ω₁`.

The model is the base structure of the receiving model with top-free types of
`AlephOne.existsReceivingModelTarget` (on the carrier `ω₁.ToType`).  Modelhood is
`AlephOne.realizeDensitySentenceTarget`, the cardinality is `AlephOne.mk_carrier`, and both ranks
are the given-model statement `AlephOne.realizationScottRankOmegaOneOfModelTarget` for that
realization.

## Placement

This file is the first milestone (one model of cardinality `ℵ₁` with Scott rank exactly `ω₁`) of
the `ℵ₁` companion construction over the density sentence.  It imports both the existence theorem
(`VaughtConjecture.AlephOne.Existence`) and the Scott analysis
(`VaughtConjecture.AlephOne.ScottAnalysis`), neither of which imports the other.
-/

namespace VaughtConjecture.AlephOne

open Ordinal Order FirstOrder Language InfinitaryLogic.ScottProcess.Semantic

/-- **A model of the density sentence of cardinality `ℵ₁` and Scott rank `ω₁`**: the base
structure of the receiving model with top-free types of `AlephOne.existsReceivingModelTarget`,
with the ranks of `AlephOne.realizationScottRankOmegaOneOfModelTarget`. -/
theorem existsAlephOneModelScottRankOmegaOneTarget :
    ExistsAlephOneModelScottRankOmegaOneTarget := by
  obtain ⟨R, hR, htR⟩ := existsReceivingModelTarget
  let : baseLanguage.{0}.Structure Carrier :=
    (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  let : Infinite Carrier := hR.1.infinite (Ordinal.omega_pos 1)
  obtain ⟨hS, hP⟩ := realizationScottRankOmegaOneOfModelTarget R hR htR
  exact ⟨Carrier, inferInstance, inferInstance, realizeDensitySentenceTarget R hR, mk_carrier,
    hS.trans (Ordinal.lift_id _), hP⟩

end VaughtConjecture.AlephOne
