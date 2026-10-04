/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Modelhood
import VaughtConjecture.Continuation.Classification

/-!
# Examples: terminal properties and the cover of the terminal models

* **The base block.**  At `ξ = 0`, with `λ_0 = ω`, the terminal properties are countable, the
  three cases of `HasTerminalProperty` unfold to their clauses, and under the continuation
  criterion every model at `ω` that is terminal at `0` has some terminal property.
* **The top-free witness.**  The realization reconstructed from an ultrahomogeneous structure
  whose age is the age of top-free charts, at a block stage and under the coatom extension
  property with apex (which makes it a model, `isModel_reconstruct_of_hasApexCoatomExtensions`),
  has the rigid-core property `inl ⟨0, p⟩` on no points.  It is terminal, and it does not have
  the hollow property although it is cover-hollow; these two need only that the age is contained
  in the age of top-free charts.
* **Positivity.**  No model has the residual property with `K = 0`.
* **Overlap.**  The properties are not exclusive: in a top-free model every cover is a globally
  rigid core, so the witness has the rigid-core property on no points and on one point.
-/

namespace VaughtConjecture

open Ordinal Cardinal Realization StageType

/-! ### The base block -/

/-- The terminal properties at the base block are countable. -/
example : Countable (TerminalProperty 0) :=
  countable_terminalProperty (omega0_pos.trans omega0_lt_omega_one)

/-- The base block stage is `ω`. -/
example : blockStage (0 : Ordinal.{0}) = ω := blockStage_zero

section BaseBlock

variable {M : Type} {R : Realization.{0, 0} (blockStage 0) M}

/-- The rigid-core property at the base block. -/
example {n : ℕ} (p : StageType.{0} (blockStage 0) n) :
    R.HasTerminalProperty (.inl ⟨n, p⟩) ↔ ∃ c, R.Covers p c ∧ R.IsGloballyRigidCore c :=
  Iff.rfl

/-- The residual property at the base block. -/
example (K : ℕ) :
    R.HasTerminalProperty (.inr (.inl K)) ↔
      (¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage 0) k) (c : Fin k → M),
        R.Covers p c ∧ R.IsGloballyRigidCore c) ∧ R.topGradeSup = K :=
  Iff.rfl

/-- The hollow property at the base block. -/
example : R.HasTerminalProperty (.inr (.inr ())) ↔ R.IsCoverHollow ∧ R.topGradeSup = ⊤ :=
  Iff.rfl

/-- The cover at the base block: under the continuation criterion, a model at `ω` that is
terminal at `0` has some terminal property. -/
example (hcont : ContinuationCriterion.{0}) (hR : R.IsModel) (ht : R.IsTerminalAt 0) :
    ∃ P : TerminalProperty 0, R.HasTerminalProperty P :=
  exists_hasTerminalProperty hcont (omega0_pos.trans omega0_lt_omega_one) hR ht

end BaseBlock

/-! ### Positivity -/

/-- **`K = 0` is excluded from the residual property** for models. -/
example {ξ : Ordinal.{0}} {M : Type} {R : Realization.{0, 0} (blockStage ξ) M}
    (hR : R.IsModel) : ¬ R.HasTerminalProperty (.inr (.inl 0)) :=
  fun h ↦ topGradeSup_ne_zero_of_residual hR h rfl

/-! ### The top-free witness -/

section Witness

variable {ξ : Ordinal.{0}} {M : Type} [(hullLanguage.{0} (blockStage ξ)).Structure M]

/-- **The witness is terminal** at its block (`reduce_ne_reconstruct`).  This needs only that the
age is contained in the age of top-free charts. -/
example (hage : (hullLanguage.{0} (blockStage ξ)).age M ⊆ topFreeAge (blockStage ξ)) :
    (reconstruct (blockStage ξ) M).IsTerminalAt ξ :=
  fun _ hR' ↦ reduce_ne_reconstruct hage _ (blockStage_lt_blockStage_add_one ξ) hR'

/-- **The witness does not have the hollow property**, although it is cover-hollow.  Both follow
from top-freeness of its actual types, which needs only that the age is contained in the age of
top-free charts (`isTopFree_of_reconstruct_eval`). -/
example (hage : (hullLanguage.{0} (blockStage ξ)).age M ⊆ topFreeAge (blockStage ξ)) :
    ¬ (reconstruct (blockStage ξ) M).HasTerminalProperty (.inr (.inr ())) ∧
      (reconstruct (blockStage ξ) M).IsCoverHollow :=
  have h : ∀ x : (reconstruct (blockStage ξ) M).Occurrence, x.type.IsTopFree :=
    fun x ↦ isTopFree_of_reconstruct_eval hage x.eval_tuple
  ⟨not_hasTerminalProperty_hollow_of_isTopFree h, isCoverHollow_of_isTopFree h⟩

variable (hext : HasApexCoatomExtensions.{0} (blockStage ξ))
  (hage : (hullLanguage.{0} (blockStage ξ)).age M = topFreeAge (blockStage ξ))
  (hu : (hullLanguage.{0} (blockStage ξ)).IsUltrahomogeneous M)
include hext hage hu

/-- The reconstructed top-free realization is a model whose actual types are top-free. -/
private theorem isModel_reconstruct_and_isTopFree :
    (reconstruct (blockStage ξ) M).IsModel ∧
      ∀ x : (reconstruct (blockStage ξ) M).Occurrence, x.type.IsTopFree :=
  ⟨isModel_reconstruct_of_hasApexCoatomExtensions hext hage hu (isSuccLimit_blockStage ξ),
    fun x ↦ isTopFree_of_reconstruct_eval hage.le x.eval_tuple⟩

/-- **The witness has the rigid-core property on no points.** -/
example (p : StageType.{0} (blockStage ξ) 0) :
    (reconstruct (blockStage ξ) M).HasTerminalProperty (.inl ⟨0, p⟩) :=
  have h := isModel_reconstruct_and_isTopFree hext hage hu
  hasTerminalProperty_inl_zero_of_isTopFree h.1 h.2 p

/-- **Overlap**: the witness also has the rigid-core property on one point, for the type of any
occurrence on one point, since every cover of a top-free model is a globally rigid core. -/
example : ∃ q : StageType.{0} (blockStage ξ) 1,
    (reconstruct (blockStage ξ) M).HasTerminalProperty (.inl ⟨1, q⟩) := by
  obtain ⟨hR, htf⟩ := isModel_reconstruct_and_isTopFree hext hage hu
  obtain ⟨⟨k, u, q, hq⟩, rfl⟩ := hR.exists_arity_eq (isSuccLimit_blockStage ξ).bot_lt 1
  exact ⟨q, u, covers_of_eval u hq, isGloballyRigidCore_of_forall_isTopFree htf _⟩

end Witness

end VaughtConjecture
