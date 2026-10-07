/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Modelhood
import VaughtConjecture.Continuation.RestrictedHollow

/-!
# Examples: cover-hollowness without a globally rigid core

* **The clauses.**  At the base block, the three restricted terminal properties unfold to their
  clauses; the rigid-core and residual ones are those of `HasTerminalProperty`.
* **For a top-free model, the predicates differ.**  A model whose actual types are top-free is
  cover-hollow, and the empty tuple is a globally rigid core of it, so it is not cover-hollow
  without a globally rigid core.  Under the coatom extension property with apex, the
  reconstruction of an ultrahomogeneous structure whose age is the age of top-free charts is such
  a model.  Both examples assume such a model (or such a structure); no model on which the
  predicates differ is constructed here.
* **The cover.**  Under the continuation criterion, every model at `ω` that is terminal at `0`
  has some restricted terminal property; a model with the hollow property and a globally rigid
  core has a rigid-core property.
* **(R3).**  (R3) for cover-hollowness at a block stage gives (R3) for the restricted predicate.
-/

namespace VaughtConjecture

open Ordinal Cardinal Realization StageType

/-! ### The clauses -/

section BaseBlock

variable {M : Type} {R : Realization.{0, 0} (blockStage 0) M}

/-- The restricted rigid-core property is the rigid-core property. -/
example {n : ℕ} (p : StageType.{0} (blockStage 0) n) :
    R.HasRestrictedTerminalProperty (.inl ⟨n, p⟩) ↔ R.HasTerminalProperty (.inl ⟨n, p⟩) :=
  Iff.rfl

/-- The restricted residual property is the residual property. -/
example (K : ℕ) :
    R.HasRestrictedTerminalProperty (.inr (.inl K)) ↔ R.HasTerminalProperty (.inr (.inl K)) :=
  Iff.rfl

/-- The restricted hollow property. -/
example : R.HasRestrictedTerminalProperty (.inr (.inr ())) ↔
    (R.IsCoverHollow ∧ ¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage 0) k) (c : Fin k → M),
      R.Covers p c ∧ R.IsGloballyRigidCore c) ∧ R.topGradeSup = ⊤ :=
  Iff.rfl

/-- **The cover at the base block**: under the continuation criterion, a model at `ω` that is
terminal at `0` has some restricted terminal property. -/
example (hcont : ContinuationCriterion.{0}) (hR : R.IsModel) (ht : R.IsTerminalAt 0) :
    ∃ P : TerminalProperty 0, R.HasRestrictedTerminalProperty P :=
  exists_hasRestrictedTerminalProperty hcont (omega0_pos.trans omega0_lt_omega_one) hR ht

/-- **A hollow model with a globally rigid core has a rigid-core property**, and not the
restricted hollow property. -/
example (h : R.HasTerminalProperty (.inr (.inr ()))) {k : ℕ}
    {p : StageType.{0} (blockStage 0) k} {c : Fin k → M} (hc : R.Covers p c)
    (hcore : R.IsGloballyRigidCore c) :
    R.HasRestrictedTerminalProperty (.inl ⟨k, p⟩) ∧
      ¬ R.HasRestrictedTerminalProperty (.inr (.inr ())) ∧ R.HasTerminalProperty (.inr (.inr ())) :=
  ⟨⟨c, hc, hcore⟩, not_hasRestrictedTerminalProperty_hollow_of_isGloballyRigidCore hc hcore, h⟩

end BaseBlock

/-! ### For a top-free model, the predicates differ -/

/-- **A top-free model is cover-hollow, but not without a globally rigid core**: for a model whose
actual types are top-free, the empty tuple covers the stage type on no points and is a globally
rigid core. -/
example {ξ : Ordinal.{0}} {M : Type} {R : Realization.{0, 0} (blockStage ξ) M} (hR : R.IsModel)
    (h : ∀ x : R.Occurrence, x.type.IsTopFree) :
    R.IsCoverHollow ∧ ¬ R.IsCoverHollowWithoutRigidCore :=
  let ⟨p, hp⟩ := hR.exists_covers_zero
  ⟨isCoverHollow_of_isTopFree h,
    fun hH ↦ hH.2 ⟨0, p, ![], hp, isGloballyRigidCore_of_forall_isTopFree h _⟩⟩

section Witness

variable {ξ : Ordinal.{0}} {M : Type} [(hullLanguage.{0} (blockStage ξ)).Structure M]

/-- **The top-free witness**: under the coatom extension property with apex, for an
ultrahomogeneous structure whose age is the age of top-free charts, its reconstruction at a block
stage is cover-hollow at a block stage, but not without a globally rigid core. -/
example (hext : HasApexCoatomExtensions.{0} (blockStage ξ))
    (hage : (hullLanguage.{0} (blockStage ξ)).age M = topFreeAge (blockStage ξ))
    (hu : (hullLanguage.{0} (blockStage ξ)).IsUltrahomogeneous M) :
    (reconstruct (blockStage ξ) M).IsCoverHollowAtBlock ∧
      ¬ (reconstruct (blockStage ξ) M).IsCoverHollowWithoutRigidCoreAtBlock := by
  have hR := isModel_reconstruct_of_hasApexCoatomExtensions hext hage hu (isSuccLimit_blockStage ξ)
  have h : ∀ x : (reconstruct (blockStage ξ) M).Occurrence, x.type.IsTopFree :=
    fun x ↦ isTopFree_of_reconstruct_eval hage.le x.eval_tuple
  obtain ⟨p, hp⟩ := hR.exists_covers_zero
  exact ⟨isCoverHollowAtBlock_iff.mpr (isCoverHollow_of_isTopFree h),
    fun hH ↦ hH.2 ⟨0, p, ![], hp, isGloballyRigidCore_of_forall_isTopFree h _⟩⟩

end Witness

/-! ### (R3) -/

/-- (R3) for cover-hollowness at a block stage gives (R3) for cover-hollowness without a globally
rigid core at a block stage. -/
example : HollowReceiving.{0, 0} IsCoverHollowAtBlock →
    HollowReceiving.{0, 0} IsCoverHollowWithoutRigidCoreAtBlock :=
  HollowReceiving.withoutRigidCore

end VaughtConjecture
