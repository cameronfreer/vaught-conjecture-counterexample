/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Receiving
import VaughtConjecture.Continuation.Comparison

/-!
# Examples: comparison of terminal models sharing a property

* **Cutoff receiving is not exact without rigidity.**  At a limit stage, capping a legal stage type
  `d` with a top cell at an ordinal above its other labels (`StageType.cap`) gives a member of the
  receiving family of `d` at a cutoff above those labels, with the same face on no points, that
  differs from `d`.  So the empty core is not rigid in `d`
  (`StageType.eq_of_mem_receivingFamily_of_isRigidCoreIn`): rigidity is what makes receiving
  exact, and this recovers one direction of `StageType.isRigidCoreIn_empty_iff_isTopFree`.
* **Transport.**  The rigid-core comparison of `R` with its transport `R.map e`: finite-extension
  receiving and globally rigid cores are carried along `e`.
* **The top-free instance against the reconstruction.**  For the realization reconstructed from an
  ultrahomogeneous structure whose age is the age of top-free charts, exact receiving of the legal
  top-free types follows both from finite-extension receiving
  (`Realization.exactReceivingWithin_isTopFree`) and directly
  (`exists_reconstruct_eval_eq_of_isTopFree`).  Such a structure is assumed here; its existence
  (`exists_isFraisseLimit_topFreeAge`) needs the coatom extension property
  `StageType.HasCoatomExtensions`, which is not proved.
* **Closure of the residual family.**  The legal stage types of top grade at most `K` are closed
  under the face maps and under reindexing.
-/

universe u w

namespace VaughtConjecture

open FirstOrder Language Realization StageType

variable {α : Ordinal.{u}} {n k₀ : ℕ}

/-! ### Cutoff receiving is not exact without rigidity -/

/-- A capped legal stage type with a top cell lies in the receiving family of the type at a cutoff
above its other labels, has the same face on no points, and differs from it: so the empty core is
not rigid. -/
example (hα : Order.IsSuccLimit α) {d : StageType.{u} α n} (hd : d.IsLegal) (h : ¬ d.IsTopFree)
    (ι : Fin 0 ↪ Fin n) : ¬ d.IsRigidCoreIn ι := by
  intro hr
  obtain ⟨δ, hδα, hδ⟩ := d.exists_lt_forall_label_lt hα
  obtain ⟨c, hδc, hcα, hc⟩ := Label.exists_lt_lt_isSelfVisible hα.isSuccPrelimit hδα n
  have hmem : d.cap c hc hcα ∈ receivingFamily d δ := by
    refine ⟨rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    exact (min_assoc _ _ _).trans (congrArg (min (d.label i))
      (min_eq_right (by exact_mod_cast hδc.le)))
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (d.isSome_restrictFace_of_zero ι)
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp ((d.cap c hc hcα).isSome_restrictFace_of_zero ι)
  rw [eq_of_zero p' p] at hp'
  exact h (eq_of_mem_receivingFamily_of_isRigidCoreIn hd hδ hmem hp' hp hr ▸ isTopFree_cap)

/-! ### Transport -/

/-- The rigid-core comparison of a realization with its transport along a bijection of carriers. -/
example {M N : Type w} [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]
    [Countable M] [Countable N] {R : Realization.{u, w} α M} (e : M ≃ N)
    (hα : Order.IsSuccLimit α) (he : R.IsExpansionOf) (he' : (R.map e).IsExpansionOf)
    (hrec : R.HasFiniteExtensionReceiving) {p : StageType.{u} α k₀} {x₀ : Fin k₀ → M}
    (hc : R.Covers p x₀) (hcore : R.IsGloballyRigidCore x₀) :
    ∃ f : M ≃[baseLanguage.{u}] N, ⇑f ∘ x₀ = ⇑e ∘ x₀ := by
  have hsymm : ⇑e.symm ∘ (⇑e ∘ x₀) = x₀ := by
    rw [← Function.comp_assoc, e.symm_comp_self, Function.id_comp]
  refine exists_equiv_comp_eq_of_isGloballyRigidCore hα he he' hrec
    ((hasFiniteExtensionReceiving_iff he'.isModel.isConsistent hα.isSuccPrelimit).mpr
      ((hasFiniteCutReceiving_map_iff e).mpr hrec.hasFiniteCutReceiving))
    hc ((covers_map_iff e).mpr (by rwa [hsymm])) hcore fun _ t x ι hx hxι ↦ ?_
  refine hcore t _ ι ((covers_map_iff e).mp hx) ?_
  rw [Function.comp_assoc, hxι, hsymm]

/-! ### The top-free instance against the reconstruction -/

section Reconstruction

variable {M : Type} [(hullLanguage.{u} α).Structure M]
  (hage : (hullLanguage.{u} α).age M = topFreeAge α)
  (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccLimit α)
include hage hu hα

/-- Exact receiving of the legal top-free types in the reconstruction, from finite-extension
receiving and the rigidity of every core in a top-free type. -/
example : (reconstruct α M).ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.IsTopFree} :=
  have hR := (reconstruct_of_age_eq hage).2.1
  exactReceivingWithin_isTopFree hR hα
    ((hasFiniteCutReceiving_reconstruct hage hu hα.isSuccPrelimit).hasFiniteExtensionReceiving hR
      hα.isSuccPrelimit)

/-- The same, directly from exact extension within the age of top-free charts. -/
example : (reconstruct α M).ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.IsTopFree} := by
  intro _ _ t c hc D g hD hg
  obtain ⟨v, hv, hvD⟩ := exists_reconstruct_eval_eq_of_isTopFree hage hu hc.eval_eq hD.1 hD.2 hg
  exact ⟨v, covers_of_eval v hvD, funext fun i ↦ DFunLike.congr_fun hv i⟩

end Reconstruction

/-! ### Closure of the residual family -/

section Residual

variable {K m : ℕ} {D : StageType.{u} α m}

/-- The legal stage types of top grade at most `K` are closed under the face maps. -/
example (hD : D.IsLegal ∧ D.topGrade ≤ K) {f : Fin n ↪ Fin m} {p : StageType.{u} α n}
    (hf : restrictFace f D = some p) : p.IsLegal ∧ p.topGrade ≤ K :=
  isLegal_and_topGrade_le_of_restrictFace hD hf

/-- …and under reindexing, the face map along a bijection. -/
example (hD : D.IsLegal ∧ D.topGrade ≤ K) (e : Fin m ≃ Fin m) :
    (D.reindex e).IsLegal ∧ (D.reindex e).topGrade ≤ K :=
  isLegal_and_topGrade_le_of_restrictFace hD (restrictFace_equiv D e)

end Residual

end VaughtConjecture
