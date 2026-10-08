/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerBandFill

/-!
# Legality of the restricted reading layer from conditions on the coatom types

Roadmap, Layer 3 ((R3) of the table of 3.4).

The legality of the restricted reading layer (`TowerProfile.readingTop`) at a seed on five points,
from conditions on its two coatom types.

* **Lawfulness below the left coatom, read on the left coatom type**
  (`TowerProfile.isLawful_left_of_isLawfulBelow`, compiled in this repository (theorem named)).
* **The conditions** (`TowerProfile.LeftTie`, `TowerProfile.RightNewTop`, defined here): on the left
  coatom type, an apex marker reading the cells labelled `⊥` as `⊥`, the face off the point `3`
  labelled `⊥`, the root offsets below the grade `4` of the apex (the acquisition condition), and
  two cells `z₁`, `z₂` of grades `1`, `2` with one proper label, every lawful labelling taking one
  value at the cells of grade `1` not labelled `⊥`, the only cell of grade `2` not labelled `⊥`
  being `z₂`, and the cells of grade `3` labelled `⊥`; on the right coatom type, rows raising at
  the point `3` (`StageType.RowsRaiseAt`) and a new top `x₀` of grade `1` through `3` labelled `⊤`.
* **Legality** (`TowerProfile.readingFillPos_left_of_coatoms`,
  `TowerProfile.isLegalBelowFullGrade_readingTop_of_coatoms`, compiled): under these conditions
  the four fill conditions hold, so the reading layer of the marker and the new top is legal below
  the full grade.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The cells of the left coatom type lie below the left coatom. -/
theorem leftCell_mem (z : Fin I.left.card) :
    leftCell I z ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := by
  rw [CellScheme.mem_below, gradedIndex_leftCell, ← univ_map_left_eq]
  exact Prod.mk_le_mk.mpr ⟨map_subset_map.mpr (subset_univ _), I.left.grade_le z⟩

/-- The grade of the cell of a cell of the left coatom type. -/
theorem grade_leftCell (z : Fin I.left.card) :
    (scheme I).toCellScheme.grade (leftCell I z) = I.left.toCellScheme.grade z := by
  rw [← CellScheme.gradedIndex_snd, gradedIndex_leftCell]

/-- **A labelling lawful below the left coatom, read on the left coatom type, is lawful**: it
extends to a labelling lawful below `(univ, 4)` (the fill at `⊥`, `TowerProfile.exists_fill_four`),
which restricts to the amalgam and to its left face (`StageType.isLawful_comp_faceCell`). -/
theorem isLawful_left_of_isLawfulBelow {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d) :
    I.left.rows.IsLawful fun z ↦ f (leftCell I z) := by
  obtain ⟨g, hg, hgf, -⟩ := exists_fill_four (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3))
    (by simp) (by simp) (by decide) hf (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot
    (isSelfVisible_bot 4) fun _ _ ↦ by simp
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hg
  have hgl : (scheme I).rows.IsLawful g :=
    ⟨fun d ↦ ho d (mem_below_univ_four d), fun s ↦ hl s (mem_below_univ_four s),
      fun s t hst hgr ↦ ha s t (mem_below_univ_four t) hst hgr⟩
  have hamal : I.amalgam.rows.IsLawful (g ∘ embed3 I) := by
    have := hgl.comap (isLowerEmbedding_embed3 (I := I))
    rwa [comap_rows_embed3] at this
  have hleft := StageType.isLawful_comp_faceCell I.restrictFace_left hamal
  convert hleft using 1
  funext z
  exact (hgf _ (leftCell_mem z)).symm

/-- **A left coatom type with a tie-keeping marker** (for the restricted reading layer): an apex
`a` (the only cell at `(univ, 4)`, labelled `⊤`, reading the cells labelled `⊥` as `⊥`), the face
off the point `3` labelled `⊥`, **the root offsets below the grade `4` of the apex** (the
acquisition condition, `StageType.RootOffsetsBelow` through the identity), and two cells `z₁`, `z₂`
of grades `1`, `2` with one proper label such that: every lawful labelling takes one value at the
cells of grade `1` not labelled `⊥` (that at `z₁`), the only cell of grade `2` not labelled `⊥` is
`z₂`, and the cells of grade `3` are labelled `⊥`. -/
structure LeftTie (t' : StageType.{u} α 4) (a z₁ z₂ : Fin t'.card) : Prop where
  gradedIndex_apex : t'.toCellScheme.gradedIndex a = (univ, 4)
  eq_apex : ∀ z, t'.toCellScheme.gradedIndex z = (univ, 4) → z = a
  label_apex : t'.label a = ⊤
  rowAt_apex : ∀ z, t'.label z = ⊥ → t'.toScheme.rowAt a z = ⊥
  face_bot : ∀ z, Fin.last 3 ∉ t'.toCellScheme.scope z → t'.label z = ⊥
  rootOffsetsBelow : t'.RootOffsetsBelow (Function.Embedding.refl (Fin 4)) 4
  grade_one : t'.toCellScheme.grade z₁ = 1
  grade_two : t'.toCellScheme.grade z₂ = 2
  label_eq : t'.label z₂ = t'.label z₁
  isProper_label : IsProper (t'.label z₂)
  tie_one : ∀ p : Fin t'.card → Label.{u}, t'.rows.IsLawful p → ∀ z,
    t'.toCellScheme.grade z = 1 → t'.label z ≠ ⊥ → p z = p z₁
  eq_two : ∀ z, t'.toCellScheme.grade z = 2 → t'.label z ≠ ⊥ → z = z₂
  label_three : ∀ z, t'.toCellScheme.grade z = 3 → t'.label z = ⊥

/-- **A right coatom type with a new top** at `x₀`: its rows raise at the point `3`
(`StageType.RowsRaiseAt`), and `x₀` is a cell of grade `1` through `3` labelled `⊤`. -/
structure RightNewTop (tb : StageType.{u} α 4) (x₀ : Fin tb.card) : Prop where
  rowsRaiseAt : tb.RowsRaiseAt 3
  mem_scope : (3 : Fin 4) ∈ tb.toCellScheme.scope x₀
  grade_eq : tb.toCellScheme.grade x₀ = 1
  label_eq : tb.label x₀ = ⊤

/-- The new top of the reading layer: the cell `x₀` of the right coatom type in the profile
layer. -/
noncomputable abbrev newTops (I : Seed.{u} α 3) (x₀ : Fin I.right.card) :
    Finset (Fin (scheme I).card) :=
  ({x₀} : Finset (Fin I.right.card)).image fun z ↦
    embed3 I (StageType.faceCell I.restrictFace_right z)

/-- **The fill at the short positive caps from the left coatom, from the coatom types**
(`TowerProfile.readingFillPos_left_of_tie`, with the conditions on the cells of the profile layer
read on the left coatom type through `TowerProfile.isLawful_left_of_isLawfulBelow`). -/
theorem readingFillPos_left_of_coatoms {a z₁ z₂ : Fin I.left.card} (hL : LeftTie I.left a z₁ z₂)
    {x₀ : Fin I.right.card} (hR : RightNewTop I.right x₀) :
    ReadingFillPos I (leftCell I a) (newTops I x₀) (Fin.last 4) := by
  obtain ⟨hgr, hrC, -⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd hL.gradedIndex_apex
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
  have hoff : I.left.RootOffsetsBelow (Function.Embedding.refl (Fin 4))
      (I.left.toCellScheme.grade a) := by
    rw [hga]; exact hL.rootOffsetsBelow
  have hPx : Fin.last 4 ∈ I.amalgam.toCellScheme.scope
      (StageType.faceCell I.restrictFace_right x₀) :=
    (last_mem_scope_right I.restrictFace_right x₀).mpr hR.mem_scope
  refine readingFillPos_left_of_tie hR.rowsRaiseAt hgr hrC hPx
    ((StageType.grade_faceCell _ _).trans hR.grade_eq)
    (mem_image_of_mem _ (mem_singleton_self _))
    (fun x hx ↦ by obtain ⟨z, hz, rfl⟩ := mem_image.mp hx; rw [mem_singleton.mp hz])
    (leftCell_mem z₁) ((grade_leftCell z₁).trans hL.grade_one)
    (leftCell_mem z₂) ((grade_leftCell z₂).trans hL.grade_two)
    (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg ↦ ?_)
    (ι := Function.Embedding.refl _) rfl rfl rfl hL.label_apex
    (congrArg Prod.fst hL.gradedIndex_apex) hga.ge hoff
    (TopReadingApexExample.mem_visibleCells_refl _ _)
    (TopReadingApexExample.mem_visibleCells_refl _ _) hL.label_eq hL.isProper_label
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hL.tie_one _ (isLawful_left_of_isLawfulBelow hf) z ((grade_leftCell z).symm.trans hg)
      fun hz ↦ h0 (hfr0 hf hfr z hz)
  · obtain ⟨z, rfl⟩ := hcell hd
    rw [hL.eq_two z ((grade_leftCell z).symm.trans hg) fun hz ↦ h0 (hfr0 hf hfr z hz)]
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hfr0 hf hfr z (hL.label_three z ((grade_leftCell z).symm.trans hg))

/-- **The restricted reading layer is legal below the full grade at every seed on five points
whose left coatom type has a tie-keeping marker and whose right coatom type has a new top**: the
four fill conditions (`TowerProfile.readingFillBot_left_of_left`,
`TowerProfile.readingFillBot_right_of_unique`, `TowerProfile.readingFillPos_right_of_unique`,
`TowerProfile.readingFillPos_left_of_coatoms`), and
`TowerProfile.isLegalBelowFullGrade_readingTop_iff`. -/
theorem isLegalBelowFullGrade_readingTop_of_coatoms {a z₁ z₂ : Fin I.left.card}
    (hL : LeftTie I.left a z₁ z₂) {x₀ : Fin I.right.card} (hR : RightNewTop I.right x₀) :
    (readingTop I (leftCell I a) (newTops I x₀)).IsLegalBelowFullGrade := by
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hX3 : ∀ x ∈ newTops I x₀, (scheme I).toCellScheme.grade x ≤ 3 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [mem_singleton.mp hz, ← CellScheme.gradedIndex_snd, gradedIndex_embed3,
      CellScheme.gradedIndex_snd, StageType.grade_faceCell, hR.grade_eq]
    omega
  refine (isLegalBelowFullGrade_readingTop_iff hgr fun x hx ↦ (hX3 x hx).trans (by omega)).mpr
    ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillBot_left_of_left hL.gradedIndex_apex hL.rowAt_apex hL.face_bot _
        fun z hz ↦ by rw [mem_singleton.mp hz]; exact hR.label_eq
    · rw [mem_singleton.mp hz]
      exact readingFillBot_right_of_unique hgr hrC huniq
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillPos_left_of_coatoms hL hR
    · rw [mem_singleton.mp hz]
      exact readingFillPos_right_of_unique hgr hrC huniq hX3

end TowerProfile

end VaughtConjecture
