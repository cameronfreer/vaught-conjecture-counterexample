/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Modelhood
import VaughtConjecture.Realization.GateRecoveryExamples
import VaughtConjecture.Realization.Partial
import VaughtConjecture.Realization.Strictness

/-!
# Strictness for models: examples

Roadmap, manuscript correspondence, item 5 (strictness and serving indices).

**The top-free witness at `ω`.**  Under the coatom extension property with apex at `ω`, the
reconstructed realization of an ultrahomogeneous structure whose age is the age of top-free
charts at `ω` is a model (`isModel_reconstruct_of_hasApexCoatomExtensions`), so the least index at
which it is fixed by projection is `0` (`Realization.IsModel.isLeast_isFixedAt_blockStage`), and it
is not fixed by projection at stage `0`.

**Strictness fails for arbitrary realizations.**  Two families show that modelhood cannot be
dropped from `Realization.isStrict_of_forall_isModel`.

* The **all-undefined realization** (every tuple untyped) is fixed by projection at every stage,
  in particular at stage `0` (`isFixedAt_undefined`), and is its own stage reduction
  (`reduce_undefined`).  The constant family whose member at every index is the all-undefined
  realization has every index serving (`nonempty_undefinedFamily`) and the uniform fixing stage
  `0`, and it is not strict (`not_isStrict_undefinedFamily`): this is the negative special case of
  item 5.
* The **face realization** of a chart with bottom labels, read at the block stage `λ_1 = ω + ω`,
  is exactly consistent and covering, and it is fixed by projection at stage `0`
  (`isFixedAt_faceRealization_pair`), so at the index `0`.  It is therefore not a model
  (`not_isModel_faceRealization_pair`, by strictness itself), and the family with this one member
  at the index `1` is not strict (`not_isStrict_faceRealizationFamily`).  So exact consistency
  and covering do not give strictness; the uniformity clause does.
-/

namespace VaughtConjecture.Realization.StrictnessExamples

open Ordinal FirstOrder Language

/-! ### The top-free witness at `ω` -/

/-- **The top-free witness at `ω`**: under the coatom extension property with apex at `ω`, the
reconstructed realization of an ultrahomogeneous structure whose age is the age of top-free charts
is fixed by projection at the index `ξ` exactly from `ξ = 0` on. -/
example {M : Type} [(hullLanguage.{0} (blockStage 0)).Structure M]
    (hext : StageType.HasApexCoatomExtensions.{0} (blockStage 0))
    (hage : (hullLanguage.{0} (blockStage 0)).age M = topFreeAge (blockStage 0))
    (hu : (hullLanguage.{0} (blockStage 0)).IsUltrahomogeneous M) :
    IsLeast {ξ : Ordinal.{0} | (reconstruct (blockStage 0) M).IsFixedAt (blockStage ξ)} 0 ∧
      ¬ (reconstruct (blockStage 0) M).IsFixedAt 0 := by
  have hS := isModel_reconstruct_of_hasApexCoatomExtensions hext hage hu (isSuccLimit_blockStage 0)
  exact ⟨hS.isLeast_isFixedAt_blockStage,
    hS.not_isFixedAt Ordinal.isSuccPrelimit_zero (by simp [omega0_pos])⟩

/-! ### The all-undefined realization -/

/-- The **all-undefined realization** at stage `α`: no tuple is typed. -/
def undefined (α : Ordinal.{0}) (M : Type) : Realization.{0, 0} α M :=
  ⟨fun _ ↦ none⟩

/-- The all-undefined realization is fixed by projection at every stage. -/
theorem isFixedAt_undefined (α γ : Ordinal.{0}) (M : Type) : (undefined α M).IsFixedAt γ :=
  fun _ _ _ h ↦ by cases h

/-- The all-undefined realization is its own stage reduction. -/
theorem reduce_undefined {α β : Ordinal.{0}} (M : Type) (hβ : Order.IsSuccPrelimit β) :
    (undefined α M).reduce hβ = undefined β M := by
  ext
  simp [undefined]

/-- The constant family of all-undefined realizations, one at every index. -/
def undefinedFamily (M : Type) (ξ : Ordinal.{0}) : Set (Realization.{0, 0} (blockStage ξ) M) :=
  {undefined (blockStage ξ) M}

/-- Every index serves the constant family of all-undefined realizations. -/
theorem nonempty_undefinedFamily (M : Type) (ξ : Ordinal.{0}) : (undefinedFamily M ξ).Nonempty :=
  Set.singleton_nonempty _

/-- **The negative special case**: the constant family of all-undefined realizations is not
strict, since its member at the index `1` is fixed by projection at the index `0`. -/
theorem not_isStrict_undefinedFamily (M : Type) : ¬ IsStrict (undefinedFamily M) := fun h ↦
  (h (undefined (blockStage 1) M) rfl (isFixedAt_undefined _ (blockStage 0) M)).not_gt zero_lt_one

/-! ### A consistent covering realization fixed below its stage -/

/-- The chart on two points with bottom labels, read at the block stage `λ_1`. -/
noncomputable def pair : StageType.{0} (blockStage 1) 2 :=
  StageType.GateRecoveryExamples.pair.castLE zero_le

/-- Every label of a face of `pair` is bottom. -/
theorem isFixedAt_faceRealization_pair : pair.faceRealization.IsFixedAt 0 := by
  intro n t p ht d
  obtain ⟨hf, rfl⟩ := (StageType.restrictFace_eq_some_iff _ _).mp ht
  exact Label.atStage_bot

/-- The face realization of `pair` is exactly consistent and covering. -/
example : pair.faceRealization.IsConsistent ∧ pair.faceRealization.IsCovering :=
  ⟨StageType.isConsistent_faceRealization, StageType.isCovering_faceRealization⟩

/-- **The face realization of `pair` is not a model**: it is fixed by projection at stage `0`,
below its stage `λ_1`. -/
theorem not_isModel_faceRealization_pair : ¬ pair.faceRealization.IsModel := fun h ↦
  h.not_isFixedAt Ordinal.isSuccPrelimit_zero (by simp [blockStage_eq_mul, omega0_pos])
    isFixedAt_faceRealization_pair

/-- The family whose only member is the face realization of `pair`, at the index `1`. -/
def faceRealizationFamily (ξ : Ordinal.{0}) : Set (Realization.{0, 0} (blockStage ξ) (Fin 2)) :=
  {S | ∃ h : ξ = 1, S = h ▸ pair.faceRealization}

/-- **A consistent covering realization makes a family that is not strict**: the face realization
of `pair`, at the index `1`, is fixed by projection at the index `0`. -/
theorem not_isStrict_faceRealizationFamily : ¬ IsStrict faceRealizationFamily := fun h ↦
  (h pair.faceRealization ⟨rfl, rfl⟩
    (isFixedAt_faceRealization_pair.mono zero_le)).not_gt zero_lt_one

end VaughtConjecture.Realization.StrictnessExamples
