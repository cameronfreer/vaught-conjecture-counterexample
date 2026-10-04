/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Modelhood
import VaughtConjecture.Continuation.Terminal
import VaughtConjecture.Extension.Apex

/-!
# Examples: terminality, top grade, and rigid cores

* **Top-free realizations.**  A realization whose actual types are top-free has top-grade
  supremum `0` and the empty tuple as a globally rigid core; in particular the realization
  reconstructed from a structure whose age consists of top-free charts
  (`VaughtConjecture.ClassicalLimit.Reconstruction`), the construction of the top-free witness,
  which is moreover terminal at every block (`reduce_ne_reconstruct`).
* **Small types.**  A stage type on no points is top-free, with top grade `0` and its empty core
  rigid.  In every stage type the full core (along the identity) is rigid, since every cell is
  supported on it.  Adding an apex (`StageType.addApex`) to a stage type on `n > 0` points gives
  top grade `n` and, at a limit stage, an empty core that is not rigid.
* **Terminality at the base block.**  At `ξ = 0` the block stages are `λ_0 = ω` and
  `λ_1 = ω + ω`; an expansion at `ω` of a base structure with no expansion at `ω + ω` is terminal.
-/

universe u v

namespace VaughtConjecture

open Realization StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-! ### Top-free realizations -/

/-- A realization whose actual types are top-free has top-grade supremum `0` and the empty tuple
as a globally rigid core. -/
example {M : Type v} {R : Realization.{u, v} α M} (h : ∀ x : R.Occurrence, x.type.IsTopFree) :
    R.topGradeSup = 0 ∧ R.IsGloballyRigidCore ![] :=
  ⟨topGradeSup_eq_zero_iff.mpr h, isGloballyRigidCore_of_forall_isTopFree h _⟩

/-- **The reconstructed top-free realization**: for a structure of the hull language whose age
consists of top-free charts, the reconstructed realization has top-grade supremum `0` and the
empty tuple as a globally rigid core. -/
example {M : Type} [(hullLanguage.{u} α).Structure M]
    (hage : (hullLanguage.{u} α).age M ⊆ topFreeAge α) :
    (reconstruct α M).topGradeSup = 0 ∧ (reconstruct α M).IsGloballyRigidCore ![] :=
  have h (x : (reconstruct α M).Occurrence) : x.type.IsTopFree :=
    isTopFree_of_reconstruct_eval hage x.eval_tuple
  ⟨topGradeSup_eq_zero_iff.mpr h, isGloballyRigidCore_of_forall_isTopFree h _⟩

/-- **The reconstructed top-free realization is terminal** at every block (`reduce_ne_reconstruct`):
no model at the next block stage reduces to it. -/
example {ξ : Ordinal.{u}} {M : Type} [(hullLanguage.{u} (blockStage ξ)).Structure M]
    (hage : (hullLanguage.{u} (blockStage ξ)).age M ⊆ topFreeAge (blockStage ξ)) :
    (reconstruct (blockStage ξ) M).IsTerminalAt ξ :=
  fun _ hR' ↦ reduce_ne_reconstruct hage _ (blockStage_lt_blockStage_add_one ξ) hR'

/-! ### Small types -/

/-- A stage type on no points has top grade `0`, and its empty core is rigid. -/
example (t : StageType.{u} α 0) (e : Fin 0 ↪ Fin 0) : t.topGrade = 0 ∧ t.IsRigidCoreIn e :=
  ⟨topGrade_eq_zero_iff.mpr t.isTopFree_of_zero, isRigidCoreIn_of_isTopFree t.isTopFree_of_zero e⟩

/-- In every stage type the full core is rigid: every cell is supported on it. -/
example (t : StageType.{u} α n) : t.IsRigidCoreIn (Function.Embedding.refl (Fin n)) :=
  fun _ _ hcore d hd ↦ hcore d (Scheme.mem_visibleCells.mpr fun x _ ↦ ⟨x, rfl⟩) hd

section Apex

variable {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade) (hn : 0 < n)
include ht hn

/-- **Top grade of a type with an apex**: the apex has grade `n`, the largest possible. -/
example : (t.addApex ht hn).topGrade = n := by
  refine le_antisymm (topGrade_le_iff.mpr fun d _ ↦ ?_) ?_
  · exact ((t.addApex ht hn).isWellFormed.isWellFormed.grade_le_card d).trans
      ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  · obtain ⟨d, hd, htop⟩ := exists_apex_addApex ht hn
    have hdtop : (t.addApex ht hn).label d = ⊤ :=
      top_le_iff.mp ((addApex_label_last ht hn).symm.le.trans (htop _))
    have hg : (t.addApex ht hn).toCellScheme.grade d = n := congrArg Prod.snd hd
    exact hg.symm.le.trans (grade_le_topGrade hdtop)

/-- **The empty core of a type with an apex is not rigid** at a limit stage: the type is not
top-free. -/
example (hα : Order.IsSuccLimit α) (e : Fin 0 ↪ Fin n) : ¬ (t.addApex ht hn).IsRigidCoreIn e :=
  fun h ↦ (isRigidCoreIn_empty_iff_isTopFree hα (isLegal_addApex ht hn) e).mp h _
    (addApex_label_last ht hn)

end Apex

/-! ### Terminality at the base block -/

/-- At `ξ = 0`: an expansion at `ω` of a base structure with no model expansion at `ω + ω` is
terminal at `0`. -/
example {M : Type v} [baseLanguage.{u}.Structure M] {R : Realization.{u, v} (blockStage 0) M}
    (hR : R.IsExpansionOf) (h : IsEmpty (ModelExpansion M (blockStage 1))) : R.IsTerminalAt 0 :=
  hR.isTerminalAt (by rwa [zero_add])

/-- The block stages at the base block. -/
example : blockStage (0 : Ordinal.{u}) = Ordinal.omega0 ∧
    blockStage (1 : Ordinal.{u}) = Ordinal.omega0 + Ordinal.omega0 := by
  refine ⟨blockStage_zero, ?_⟩
  rw [← zero_add (1 : Ordinal.{u}), blockStage_add_one, blockStage_zero]

end VaughtConjecture
