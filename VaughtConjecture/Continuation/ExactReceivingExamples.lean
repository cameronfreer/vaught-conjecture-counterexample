/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.Extension.FamilyCofaces

/-!
# Examples: exact residual and hollow receiving

Checks for `VaughtConjecture.Continuation.ExactReceiving`.

* **Determination needs an acquired context.**  With the predicate `P` always true, cutoff
  determination and scheme determination both fail, already at the smallest instance: the root on
  no points (the empty root), and the one-point donor `apexPoint`, the stage type on one point
  whose only cell is an apex labelled `⊤` (`StageType.addApex` over the one-point scheme with no
  cells, `StageType.cellless`).  Its cap is a top-free stage type on the same scheme with the same
  (empty) root.  So the acquisition statements are where the hypotheses on the model are used.
* **The residual statement at `K = 0` is vacuous**: in a model at a limit stage, top-grade
  supremum `0` makes the empty tuple a globally rigid core.
* **The hollow statement at a model with exact receiving of all legal donors** holds, by the exact
  reformulation.  An ultrahomogeneous structure whose age is the age of legal charts has exact
  receiving of all legal donors (`exactReceivingWithin_reconstruct_of_legalAge`,
  `ClassicalLimit/LegalAge`), so the conclusion of (R3) holds for it.  Such a structure exists at a
  countable block stage, with a reconstruction that is a model, conditional on the coatom extension
  property with apex there (`exists_saturated_reconstruct`, `MainTheorem/SameLevelMaximal`), which
  is compiled in this repository (theorem named), `StageType.hasApexCoatomExtensions_blockStage`;
  its unbounded top-grade growth is not proved.
* **Under (R3), a globally rigid core of a cover-hollow model with unbounded growth is rigid in
  every legal donor over its type.**
* **The rigid-core instance**: top-free one-point cofaces are received exactly under finite-cut
  receiving at a limit stage.
-/

universe u w

namespace VaughtConjecture

open Finset StageType Realization

namespace ExactReceivingExamples

/-- The stage type on one point with no cells, at any stage and universe. -/
def celllessTypeAt (α : Ordinal.{u}) : StageType.{u} α 1 :=
  ⟨cellless, fun _ ↦ ⊥, isLegalBelowFullGrade_cellless.isWellFormed,
    isLegalBelowFullGrade_cellless.isCoded, CellScheme.Rows.isLawful_const_bot,
    fun _ ↦ Label.atStage_bot⟩

/-- The one-point type whose only cell is an apex of grade `1`, labelled `⊤`, at any stage. -/
noncomputable def apexPointAt (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (celllessTypeAt α).addApex isLegalBelowFullGrade_cellless one_pos

/-- The apex point is legal at every stage. -/
theorem isLegal_apexPointAt (α : Ordinal.{u}) : (apexPointAt α).IsLegal :=
  isLegal_addApex _ one_pos

/-- The apex point is not top-free at any stage: its cell is labelled `⊤`. -/
theorem not_isTopFree_apexPointAt (α : Ordinal.{u}) : ¬ (apexPointAt α).IsTopFree :=
  fun h ↦ h (Fin.last _) (addApex_label_last _ one_pos)

/-- **The apex point**: the stage type at `ω` on one point whose only cell is an apex of grade
`1`, labelled `⊤`. -/
noncomputable def apexPoint : StageType.{0} Ordinal.omega0 1 :=
  apexPointAt Ordinal.omega0

/-- The apex point is legal. -/
theorem isLegal_apexPoint : apexPoint.IsLegal :=
  isLegal_apexPointAt Ordinal.omega0

/-- The apex point is not top-free: its cell is labelled `⊤`. -/
theorem not_isTopFree_apexPoint : ¬ apexPoint.IsTopFree :=
  not_isTopFree_apexPointAt Ordinal.omega0

/-- The top grade of the apex point is at most `1`. -/
theorem topGrade_apexPoint_le : apexPoint.topGrade ≤ 1 :=
  topGrade_le_iff.mpr fun i _ ↦
    (apexPoint.isWellFormed.isWellFormed.grade_le_card i).trans
      ((card_le_univ _).trans_eq (by simp))

/-- The root of the apex point: its face on no points. -/
theorem exists_root_apexPoint : ∃ t : StageType.{0} Ordinal.omega0 0,
    restrictFace Fin.castSuccEmb apexPoint = some t :=
  Option.isSome_iff_exists.mp (apexPoint.isSome_restrictFace_of_zero Fin.castSuccEmb)

/-- **Cutoff determination fails without an acquired context**: with `P` always true, at `ω`,
the empty root, `K = 1`, and the apex point. -/
example : ¬ CutoffDetermination.{0} (fun _ _ _ ↦ True) := by
  intro h
  obtain ⟨t, ht⟩ := exists_root_apexPoint
  obtain ⟨D', hD', δ, hδ, hdet⟩ := h.exists_coface (K := 1) t (Function.Embedding.refl _)
    Ordinal.isSuccLimit_omega0 (isLegal_apexPoint.restrictFace _ ht) trivial t (restrictFace_refl t)
    apexPoint ⟨isLegal_apexPoint, ht⟩ topGrade_apexPoint_le
  exact not_isDeterminedWithin_receivingFamily_of_isTopFree Ordinal.isSuccLimit_omega0
    (isTopFree_of_zero t) ht not_isTopFree_apexPoint hD'.2 hδ hdet

/-- **Scheme determination fails without an acquired context**: with `P` always true, at `ω`,
the empty root, and the apex point. -/
example : ¬ SchemeDetermination.{0} (fun _ _ ↦ True) := by
  intro h
  obtain ⟨t, ht⟩ := exists_root_apexPoint
  obtain ⟨D', hD', hdet⟩ := h.exists_coface t (Function.Embedding.refl _)
    Ordinal.isSuccLimit_omega0 (isLegal_apexPoint.restrictFace _ ht) trivial t (restrictFace_refl t)
    apexPoint ⟨isLegal_apexPoint, ht⟩
  exact not_isDeterminedWithin_saturationFamily_of_isTopFree Ordinal.isSuccLimit_omega0
    (isTopFree_of_zero t) ht not_isTopFree_apexPoint hD'.2 hdet

end ExactReceivingExamples

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M}

/-- **The residual statement at `K = 0` is vacuous**: a model at a limit stage with top-grade
supremum `0` has a globally rigid core, the empty tuple. -/
example (hα : Order.IsSuccLimit α) (hR : R.IsModel) (h0 : R.topGradeSup = 0) :
    ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c := by
  obtain ⟨p, hp⟩ := hR.exists_covers_zero
  exact ⟨0, p, ![], hp, (hR.isGloballyRigidCore_empty_iff hα).mpr h0⟩

/-- **The conclusion of (R3) at a model with exact receiving of all legal donors**: over every
cover, every one-point coface is received exactly. -/
example (h : R.ExactReceivingWithin fun _ ↦ {D | D.IsLegal}) {n : ℕ} {t : StageType.{u} α n}
    {c : Fin n → M} (hc : R.Covers t c) {D : StageType.{u} α (n + 1)} (hD : D ∈ t.cofaces) :
    ∃ u : Fin (n + 1) → M, R.Covers D u ∧ u ∘ Fin.castSucc = c :=
  h t c hc D Fin.castSuccEmb hD.1 hD.2

/-- **Under (R3), a globally rigid core is rigid in every legal donor over its type**, in a model
at a limit stage satisfying `H` with unbounded growth. -/
example {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    (hhol : HollowReceiving.{u, w} H) (hα : Order.IsSuccLimit α) (hR : R.IsModel) (hH : H R)
    (htop : R.topGradeSup = ⊤) {n m : ℕ} {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) (hcore : R.IsGloballyRigidCore c) {D : StageType.{u} α m}
    {g : Fin n ↪ Fin m} (hD : D.IsLegal) (hg : restrictFace g D = some t) : D.IsRigidCoreIn g :=
  hhol.isRigidCoreIn hα hR hH htop hc hcore hD hg

/-- **The rigid-core instance**: under finite-cut receiving at a limit stage, a top-free one-point
coface of the type of a cover is received exactly. -/
example (hR : R.IsConsistent) (hα : Order.IsSuccLimit α) (hrec : R.HasFiniteCutReceiving)
    {n : ℕ} {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (htf : d.IsTopFree) :
    ∃ y : M, R.Covers d (Fin.snoc c y) :=
  exists_covers_snoc_of_isRigidCoreIn hR hα hrec hc hd (isRigidCoreIn_of_isTopFree htf _)

/-- **(R2) and (R3) as exact receiving within ages** (exact reformulations). -/
example : ResidualReceiving.{u, w} ↔
    ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄,
      Order.IsSuccLimit α → R.IsModel →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → R.ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.topGrade ≤ K} :=
  residualReceiving_iff

end VaughtConjecture
