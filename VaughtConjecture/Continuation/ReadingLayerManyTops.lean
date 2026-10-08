/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerDetermination

/-!
# The reading layer at several new tops

Roadmap, Layer 3 ((R3) of the table of 3.4).

The restricted reading layer reading every cell of a set `Z` of new tops of the right coatom type
at least as the marker.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

open TopReadingApexExample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The new tops: the cells of a set `Z` of cells of the right coatom type, in the profile layer. -/
noncomputable abbrev newTopsOf (I : Seed.{u} α 3) (Z : Finset (Fin I.right.card)) :
    Finset (Fin (scheme I).card) :=
  Z.image fun z ↦ embed3 I (StageType.faceCell I.restrictFace_right z)

/-- **A right coatom type with a set of new tops** `Z` below a cell `x₀`: its rows raise at the
point `3` (`StageType.RowsRaiseAt`), every cell of `Z` lies through `3`, is labelled `⊤`, and lies
below `x₀ ∈ Z`, a cell of grade `1`. -/
structure RightNewTops (tb : StageType.{u} α 4) (Z : Finset (Fin tb.card)) (x₀ : Fin tb.card) :
    Prop where
  rowsRaiseAt : tb.RowsRaiseAt 3
  mem : x₀ ∈ Z
  mem_scope : ∀ z ∈ Z, (3 : Fin 4) ∈ tb.toCellScheme.scope z
  grade_eq : tb.toCellScheme.grade x₀ = 1
  label_eq : ∀ z ∈ Z, tb.label z = ⊤
  le : ∀ z ∈ Z, tb.toCellScheme.gradedIndex z ≤ tb.toCellScheme.gradedIndex x₀

/-- One new top is a set of new tops. -/
theorem RightNewTop.rightNewTops {tb : StageType.{u} α 4} {x₀ : Fin tb.card}
    (hR : RightNewTop tb x₀) : RightNewTops tb {x₀} x₀ where
  rowsRaiseAt := hR.rowsRaiseAt
  mem := mem_singleton_self _
  mem_scope z hz := by rw [mem_singleton.mp hz]; exact hR.mem_scope
  grade_eq := hR.grade_eq
  label_eq z hz := by rw [mem_singleton.mp hz]; exact hR.label_eq
  le z hz := by rw [mem_singleton.mp hz]

/-- The new tops of the profile layer have grade at most `1`. -/
theorem grade_le_one_of_rightNewTops {Z : Finset (Fin I.right.card)} {x₀ : Fin I.right.card}
    (hR : RightNewTops I.right Z x₀) {x : Fin (scheme I).card} (hx : x ∈ newTopsOf I Z) :
    (scheme I).toCellScheme.grade x ≤ 1 := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
  rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd,
    StageType.grade_faceCell]
  exact (Prod.mk_le_mk.mp (hR.le z hz)).2.trans_eq hR.grade_eq

/-- **The fill at the short positive caps from the left coatom at several new tops**
(`TowerProfile.readingFillPos_left_of_rowTie`, the server read at the largest new top `x₀`). -/
theorem readingFillPos_left_of_rightNewTops {a z₁ z₂ : Fin I.left.card} {n : ℕ}
    {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {Z : Finset (Fin I.right.card)}
    {x₀ : Fin I.right.card} (hR : RightNewTops I.right Z x₀) :
    ReadingFillPos I (leftCell I a) (newTopsOf I Z) (Fin.last 4) := by
  obtain ⟨hgr, hrC, -⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hfr0 {f : Fin (scheme I).card → Label.{u}}
      (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
      (hfr : f (leftCell I a) ≠ ⊥) (z : Fin I.left.card) (hz : I.left.label z = ⊥) :
      f (leftCell I z) = ⊥ := by
    refine eq_bot_of_row_eq_bot hrC hf hfr (mem_below_marker hgr hrC (leftCell_mem z)) ?_
    rw [← Scheme.rowAt_of_mem, rowAt_leftCell]
    exact hL.rowAt_apex z hz
  have hcell {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) :
      ∃ z, leftCell I z = d :=
    exists_leftCell_eq (I := I) (TopReadingApexExample.last_notMem_of_subset
      ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd)).1)
  have hbelowApex (z : Fin I.left.card) : leftCell I z ∈ (scheme I).toCellScheme.below
      ((scheme I).toCellScheme.gradedIndex (leftCell I a)) := by
    have h := leftCell_mem (I := I) z
    rw [CellScheme.mem_below] at h ⊢
    have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst hL.gradedIndex_apex
    have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd hL.gradedIndex_apex
    rw [gradedIndex_leftCell, gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
    rw [gradedIndex_leftCell] at h
    exact h
  have hP (z : Fin I.right.card) (hz : z ∈ Z) : Fin.last 4 ∈ I.amalgam.toCellScheme.scope
      (StageType.faceCell I.restrictFace_right z) :=
    (last_mem_scope_right I.restrictFace_right z).mpr (hR.mem_scope z hz)
  refine readingFillPos_left_of_rowTie hR.rowsRaiseAt hgr hrC (hP x₀ hR.mem)
    ((StageType.grade_faceCell _ _).trans hR.grade_eq)
    (mem_image_of_mem _ hR.mem)
    (fun x hx ↦ by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      refine ⟨_, rfl, hP z hz, (CellScheme.mem_below _).mpr (Prod.mk_le_mk.mpr ⟨?_, ?_⟩)⟩
      · rw [StageType.scope_faceCell, StageType.scope_faceCell]
        exact map_subset_map.mpr (Prod.mk_le_mk.mp (hR.le z hz)).1
      · rw [StageType.grade_faceCell, StageType.grade_faceCell]
        exact (Prod.mk_le_mk.mp (hR.le z hz)).2)
    (leftCell_mem z₁) ((grade_leftCell z₁).trans hL.grade_one)
    (leftCell_mem z₂) ((grade_leftCell z₂).trans hL.grade_two)
    (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg ↦ ?_)
    (hbelowApex z₁) (hbelowApex z₂) (by rw [rowAt_leftCell, rowAt_leftCell]; exact hL.row_tie)
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hL.tie_one _ (isLawful_left_of_isLawfulBelow hf) z ((grade_leftCell z).symm.trans hg)
      fun hz ↦ h0 (hfr0 hf hfr z hz)
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hL.tie_two _ (isLawful_left_of_isLawfulBelow hf) z ((grade_leftCell z).symm.trans hg)
      fun hz ↦ h0 (hfr0 hf hfr z hz)
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hfr0 hf hfr z (hL.label_three z ((grade_leftCell z).symm.trans hg))

/-- **The restricted reading layer at several new tops is legal below the full grade** at every
seed on five points whose left coatom type has a tie-keeping marker and whose right coatom type
has a set of new tops below one of grade `1`: the four fill conditions. -/
theorem isLegalBelowFullGrade_readingTop_of_rightNewTops {a z₁ z₂ : Fin I.left.card}
    {n : ℕ} {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {Z : Finset (Fin I.right.card)}
    {x₀ : Fin I.right.card} (hR : RightNewTops I.right Z x₀) :
    (readingTop I (leftCell I a) (newTopsOf I Z)).IsLegalBelowFullGrade := by
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hX3 : ∀ x ∈ newTopsOf I Z, (scheme I).toCellScheme.grade x ≤ 3 :=
    fun x hx ↦ (grade_le_one_of_rightNewTops hR hx).trans (by omega)
  refine (isLegalBelowFullGrade_readingTop_iff hgr fun x hx ↦ (hX3 x hx).trans (by omega)).mpr
    ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillBot_left_of_left hL.gradedIndex_apex hL.rowAt_apex hL.face_bot _
        hR.label_eq
    · rw [mem_singleton.mp hz]
      exact readingFillBot_right_of_unique hgr hrC huniq
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillPos_left_of_rightNewTops hL hR
    · rw [mem_singleton.mp hz]
      exact readingFillPos_right_of_unique hgr hrC huniq hX3

end TowerProfile

end VaughtConjecture
