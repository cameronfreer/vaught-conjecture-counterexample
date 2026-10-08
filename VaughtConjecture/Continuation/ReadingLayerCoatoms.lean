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
* **At `seedThree`** (`TopReadingApexExample.leftTie_threeType`,
  `TopReadingApexExample.rightNewTop_rightType`,
  `TopReadingApexExample.readingFillPos_left_seedThree`,
  `TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedThree`, compiled): `threeType` has a
  tie-keeping marker (its apex, with `z₁`, `z₂` the cells at `(univ, 1)` and `(univ, 2)`, both
  labelled `3`; its only ordinal label is `3`, below the grade `4` of the apex; the cells of grade
  `1` labelled `3` share one value by locality and availability at `z₁`,
  `TopReadingApexExample.tie_one_threeType`), and `rightType` has a new top (its cell `{3}`;
  `TowerProfile.rowsRaiseAt_rightType`).

The conditions are explicit predicates on the coatom types; the marker condition is the
acquisition condition (root offsets below the grade of the cap), from which the tie of the marker
follows (`StageType.keepsProperRootTies_of_rootOffsetsBelow`).

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

/-- **A left coatom type with a tie-keeping marker** along a root `ι` (for the restricted reading
layer): an apex `a` (the only cell at `(univ, 4)`, labelled `⊤`), whose row reads the root cells
labelled `⊥` as `⊥` (`StageType.RootBottomRespected`) and the other cells labelled `⊥` as `⊥`; the
face off the point `3` labelled `⊥`; **the root offsets below the grade `4` of the apex** (the
acquisition condition, `StageType.RootOffsetsBelow`); and two root cells `z₁`, `z₂` of grades `1`,
`2` with one proper label such that every lawful labelling takes one value at the cells of grade
`1` not labelled `⊥` (that at `z₁`), the only cell of grade `2` not labelled `⊥` is `z₂`, and the
cells of grade `3` are labelled `⊥`. -/
structure LeftTie {n : ℕ} (t' : StageType.{u} α 4) (ι : Fin n ↪ Fin 4)
    (a z₁ z₂ : Fin t'.card) : Prop where
  gradedIndex_apex : t'.toCellScheme.gradedIndex a = (univ, 4)
  eq_apex : ∀ z, t'.toCellScheme.gradedIndex z = (univ, 4) → z = a
  label_apex : t'.label a = ⊤
  rootBottom : t'.RootBottomRespected ι a
  rowAt_apex_off : ∀ z ∉ t'.visibleCells ι, t'.label z = ⊥ → t'.toScheme.rowAt a z = ⊥
  face_bot : ∀ z, Fin.last 3 ∉ t'.toCellScheme.scope z → t'.label z = ⊥
  rootOffsetsBelow : t'.RootOffsetsBelow ι 4
  mem_one : z₁ ∈ t'.visibleCells ι
  mem_two : z₂ ∈ t'.visibleCells ι
  grade_one : t'.toCellScheme.grade z₁ = 1
  grade_two : t'.toCellScheme.grade z₂ = 2
  label_eq : t'.label z₂ = t'.label z₁
  isProper_label : IsProper (t'.label z₂)
  tie_one : ∀ p : Fin t'.card → Label.{u}, t'.rows.IsLawful p → ∀ z,
    t'.toCellScheme.grade z = 1 → t'.label z ≠ ⊥ → p z = p z₁
  eq_two : ∀ z, t'.toCellScheme.grade z = 2 → t'.label z ≠ ⊥ → z = z₂
  label_three : ∀ z, t'.toCellScheme.grade z = 3 → t'.label z = ⊥

/-- The apex of a left coatom type with a tie-keeping marker reads every cell labelled `⊥` as
`⊥`: the root cells by `StageType.RootBottomRespected`, the others by hypothesis. -/
theorem LeftTie.rowAt_apex {n : ℕ} {t' : StageType.{u} α 4} {ι : Fin n ↪ Fin 4}
    {a z₁ z₂ : Fin t'.card} (hL : LeftTie t' ι a z₁ z₂) (z : Fin t'.card) (hz : t'.label z = ⊥) :
    t'.toScheme.rowAt a z = ⊥ := by
  by_cases hv : z ∈ t'.visibleCells ι
  · exact hL.rootBottom z hv hz
  · exact hL.rowAt_apex_off z hv hz

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
theorem readingFillPos_left_of_coatoms {a z₁ z₂ : Fin I.left.card} {n : ℕ} {ι : Fin n ↪ Fin 4}
    (hL : LeftTie I.left ι a z₁ z₂)
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
  have hoff : I.left.RootOffsetsBelow ι (I.left.toCellScheme.grade a) := by
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
    (ι := ι) rfl rfl rfl hL.label_apex
    (congrArg Prod.fst hL.gradedIndex_apex) ?_ hoff hL.mem_one hL.mem_two hL.label_eq
    hL.isProper_label
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hL.tie_one _ (isLawful_left_of_isLawfulBelow hf) z ((grade_leftCell z).symm.trans hg)
      fun hz ↦ h0 (hfr0 hf hfr z hz)
  · obtain ⟨z, rfl⟩ := hcell hd
    rw [hL.eq_two z ((grade_leftCell z).symm.trans hg) fun hz ↦ h0 (hfr0 hf hfr z hz)]
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hfr0 hf hfr z (hL.label_three z ((grade_leftCell z).symm.trans hg))
  · rw [hga]
    have := Fintype.card_le_of_embedding ι
    simpa using this

/-- **The restricted reading layer is legal below the full grade at every seed on five points
whose left coatom type has a tie-keeping marker and whose right coatom type has a new top**: the
four fill conditions (`TowerProfile.readingFillBot_left_of_left`,
`TowerProfile.readingFillBot_right_of_unique`, `TowerProfile.readingFillPos_right_of_unique`,
`TowerProfile.readingFillPos_left_of_coatoms`), and
`TowerProfile.isLegalBelowFullGrade_readingTop_iff`. -/
theorem isLegalBelowFullGrade_readingTop_of_coatoms {a z₁ z₂ : Fin I.left.card}
    {n : ℕ} {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {x₀ : Fin I.right.card}
    (hR : RightNewTop I.right x₀) :
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

/-! ### The instance `seedThree` -/

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The cells of `threeType`: the apex and the cells of `S`. -/
theorem cases_threeType (z : Fin (threeType hα).card) :
    z = Fin.last _ ∨ ∃ a : Fin CaseSplitCounterexample.S.{u}.card, z = Fin.castSucc a := by
  change Fin ((threeBase hα).card + 1) at z
  induction z using Fin.lastCases with
  | last => exact .inl rfl
  | cast a => exact .inr ⟨a, rfl⟩

/-- The graded index of a cell of `S` in `threeType`. -/
theorem gradedIndex_threeType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (threeType hα).toCellScheme.gradedIndex (Fin.castSucc a) =
      (TwoFaceLiftCounterexample.cellScope a, TwoFaceLiftCounterexample.cellGrade a) :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc CaseSplitCounterexample.S 4 a

/-- The graded index of the apex of `threeType`. -/
theorem gradedIndex_threeType_last :
    (threeType hα).toCellScheme.gradedIndex (Fin.last _) = (univ, 4) :=
  StageType.addApex_gradedIndex_last (t := threeBase hα) isLegalBelowFullGrade_S (by omega)

/-- The labels of `threeType` at the cells of `S`. -/
theorem label_threeType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (threeType hα).label (Fin.castSucc a) = CaseSplitCounterexample.labelling lab3 lab3 ⊥ a :=
  StageType.addApex_label_castSucc (t := threeBase hα) isLegalBelowFullGrade_S (by omega) a

/-- The label of the apex of `threeType`. -/
theorem label_threeType_last : (threeType hα).label (Fin.last _) = ⊤ :=
  StageType.addApex_label_last (t := threeBase hα) isLegalBelowFullGrade_S (by omega)

/-- The grade of a cell of `S` in `threeType`. -/
theorem grade_threeType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (threeType hα).toCellScheme.grade (Fin.castSucc a) = TwoFaceLiftCounterexample.cellGrade a :=
  congrArg Prod.snd (gradedIndex_threeType_castSucc hα a)

/-- The apex of `threeType` has grade `4`. -/
theorem grade_threeType_last : (threeType hα).toCellScheme.grade (Fin.last _) = 4 :=
  congrArg Prod.snd (gradedIndex_threeType_last hα)

/-- **The cells of grade `1` of `threeType` labelled `3` share one value in every lawful
labelling**, that at the cell `9` (at `(univ, 1)`): locality there (it reads them as itself) and
availability (it is the only cell at its graded index). -/
theorem tie_one_threeType {p : Fin (threeType hα).card → Label.{u}}
    (hp : (threeType hα).rows.IsLawful p) (z : Fin (threeType hα).card)
    (hz : (threeType hα).toCellScheme.grade z = 1) (hl : (threeType hα).label z ≠ ⊥) :
    p z = p (Fin.castSucc (⟨9, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) := by
  set n9 : Fin CaseSplitCounterexample.S.{u}.card := ⟨9, by decide⟩ with hn9
  rcases cases_threeType hα z with hzl | ⟨a, hza⟩
  · exact absurd ((grade_threeType_last hα).symm.trans (hzl ▸ hz)) (by decide)
  subst hza
  have ha : TwoFaceLiftCounterexample.cellGrade a = 1 :=
    (grade_threeType_castSucc hα a).symm.trans hz
  have hla : CaseSplitCounterexample.live a = true :=
    live_of_labelling_three_ne_bot ((label_threeType_castSucc hα a).symm.trans_ne hl)
  have h9 : TwoFaceLiftCounterexample.cellGrade n9 = 1 := rfl
  have hl9 : CaseSplitCounterexample.live n9 = true := rfl
  have hs9 : TwoFaceLiftCounterexample.cellScope n9 = univ := rfl
  have hmem : Fin.castSucc a ∈ (threeType hα).toCellScheme.below
      ((threeType hα).toCellScheme.gradedIndex (Fin.castSucc n9)) :=
    (gradedIndex_threeType_castSucc hα a).trans_le
      (le_of_le_of_eq (Prod.mk_le_mk.mpr ⟨hs9 ▸ subset_univ _, ha.trans h9.symm |>.le⟩)
        (gradedIndex_threeType_castSucc hα n9).symm)
  have hrow : (threeType hα).toScheme.rowAt (Fin.castSucc n9) (Fin.castSucc n9) =
      (threeType hα).toScheme.rowAt (Fin.castSucc n9) (Fin.castSucc a) := by
    refine ((rowAt_threeType_castSucc hα n9 n9).trans (rowAt_S_live h9 hl9 h9 subset_rfl)).trans
      (Eq.trans ?_ ((rowAt_threeType_castSucc hα n9 a).trans
        (rowAt_S_live h9 hl9 ha (hs9 ▸ subset_univ _))).symm)
    rw [hl9, hla]
  have h1 := (hp.locality (Fin.castSucc n9)).le_of_le
    (d := ⟨Fin.castSucc n9, (threeType hα).toCellScheme.mem_below_gradedIndex _⟩)
    (d' := ⟨Fin.castSucc a, hmem⟩)
    ((Scheme.rowAt_of_mem _).symm.trans_le (hrow.le.trans_eq (Scheme.rowAt_of_mem hmem)))
    ((grade_threeType_castSucc hα a).trans_le
      ((ha.trans h9.symm).le.trans_eq (grade_threeType_castSucc hα n9).symm))
  change min (p (Fin.castSucc n9)) (p (Fin.castSucc n9)) ≤
    min (p (Fin.castSucc a)) (p (Fin.castSucc n9)) at h1
  rw [min_self] at h1
  obtain ⟨v, hv, hle⟩ := hp.availability (Fin.castSucc a) (Fin.castSucc n9)
    ((threeType hα).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hmem)).1
    ((grade_threeType_castSucc hα a).trans
      ((ha.trans h9.symm).trans (grade_threeType_castSucc hα n9).symm))
  rcases cases_threeType hα v with hvl | ⟨b, hvb⟩
  · exact absurd (congrArg Prod.snd ((gradedIndex_threeType_last hα).symm.trans
      ((hvl ▸ hv).trans (gradedIndex_threeType_castSucc hα n9)))) (by decide)
  subst hvb
  have hb : b = n9 := TwoFaceLiftCounterexample.gradedIndex_injective
    ((gradedIndex_threeType_castSucc hα b).symm.trans
      (hv.trans (gradedIndex_threeType_castSucc hα n9)))
  subst hb
  exact le_antisymm hle (h1.trans (min_le_left _ _))

/-- **`threeType` is a left coatom type with a tie-keeping marker**: the apex, and the cells `9`
and `15` (at `(univ, 1)` and `(univ, 2)`, both labelled `3`); its only ordinal label is `3`, below
the grade `4` of the apex. -/
theorem leftTie_threeType :
    LeftTie (threeType hα) (Function.Embedding.refl (Fin 4)) (Fin.last _)
      (Fin.castSucc (⟨9, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
      (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) where
  gradedIndex_apex := gradedIndex_threeType_last hα
  eq_apex _ hz := StageType.eq_last_of_gradedIndex_addApex (t := threeBase hα)
    isLegalBelowFullGrade_S (by omega) hz
  label_apex := label_threeType_last hα
  rootBottom z _ hz := (StageType.rowAt_addApex_last_eq_bot_iff (t₀ := threeBase hα)
    isLegalBelowFullGrade_S (by omega) z).mpr hz
  rowAt_apex_off z hz := absurd (mem_visibleCells_refl _ z) hz
  mem_one := mem_visibleCells_refl _ _
  mem_two := mem_visibleCells_refl _ _
  face_bot z hz := by
    rcases cases_threeType hα z with rfl | ⟨a, rfl⟩
    · exact absurd (Eq.mpr (congrArg (Fin.last 3 ∈ ·)
        (congrArg Prod.fst (gradedIndex_threeType_last hα))) (mem_univ _)) hz
    · refine (label_threeType_castSucc hα a).trans (labelling_bot_eq_bot_of_notMem a fun h3 ↦ hz ?_)
      exact Eq.mpr (congrArg (Fin.last 3 ∈ ·)
        (congrArg Prod.fst (gradedIndex_threeType_castSucc hα a))) h3
  rootOffsetsBelow := by
    intro y _ μ f hμ hy
    rcases cases_threeType hα y with rfl | ⟨a, rfl⟩
    · exact absurd ((label_threeType_last hα).symm.trans hy)
        (fun h' ↦ WithTop.coe_ne_top (WithBot.coe_injective h'.symm))
    · have hy' := (label_threeType_castSucc hα a).symm.trans hy
      rcases labelling_three_cases a with h3 | h0
      · have e := h3.symm.trans hy'
        rw [lab3, natCast_label] at e
        have h' : ((0 : Ordinal.{u}) + (3 : ℕ)) = μ + f := by
          rw [zero_add]; exact WithTop.coe_injective (WithBot.coe_injective e)
        have := ((add_natCast_eq_add_natCast_iff Ordinal.isSuccPrelimit_zero hμ).mp h').2
        omega
      · exact absurd (h0.symm.trans hy').symm WithBot.coe_ne_bot
  grade_one := (grade_threeType_castSucc hα _).trans rfl
  grade_two := (grade_threeType_castSucc hα _).trans rfl
  label_eq := by
    refine (label_threeType_castSucc hα _).trans (Eq.trans ?_ (label_threeType_castSucc hα _).symm)
    change CaseSplitCounterexample.labelling lab3 lab3 ⊥ (15 : Fin 19) =
      CaseSplitCounterexample.labelling lab3 lab3 ⊥ (9 : Fin 19)
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]
  isProper_label := by
    have e := (label_threeType_castSucc hα
      (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)).trans
      (show CaseSplitCounterexample.labelling lab3 lab3 ⊥ (15 : Fin 19) = (lab3 : Label.{u}) by
        simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
          TwoFaceLiftCounterexample.cellGrade])
    exact ⟨((3 : ℕ) : Ordinal.{u}), (natCast_label 3).symm.trans e.symm⟩
  tie_one p hp z hz hl := tie_one_threeType hα hp z hz hl
  eq_two z hz hl := by
    rcases cases_threeType hα z with rfl | ⟨a, rfl⟩
    · exact absurd ((grade_threeType_last hα).symm.trans hz) (by decide)
    · have ha : TwoFaceLiftCounterexample.cellGrade a = 2 :=
        (grade_threeType_castSucc hα a).symm.trans hz
      have h15 := eq_fifteen_of_live a ha (live_of_labelling_three_ne_bot
        ((label_threeType_castSucc hα a).symm.trans_ne hl))
      rw [show a = (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card) from h15]
      rfl
  label_three z hz := by
    rcases cases_threeType hα z with rfl | ⟨a, rfl⟩
    · exact absurd ((grade_threeType_last hα).symm.trans hz) (by decide)
    · exact (label_threeType_castSucc hα a).trans
        (labelling_three_eq_bot_of_grade ((grade_threeType_castSucc hα a).symm.trans hz))

/-- **`rightType` is a right coatom type with a new top** at its cell `{3}` (labelled `⊤`); its
rows raise at the point `3` (`TowerProfile.rowsRaiseAt_rightType`). -/
theorem rightNewTop_rightType (α : Ordinal.{u}) :
    RightNewTop (rightType α)
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) where
  rowsRaiseAt := rowsRaiseAt_rightType
  mem_scope := by
    change (3 : Fin 4) ∈ (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).scope
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
    rw [Scheme.appendFullCellScheme_scope_castSucc]
    decide
  grade_eq := by
    change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).grade
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) = 1
    rw [Scheme.appendFullCellScheme_grade_castSucc]
    rfl
  label_eq := by
    change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]

/-- **The fill at the short positive caps from the left coatom holds at `seedThree`**
(`TowerProfile.readingFillPos_left_of_coatoms`, `leftTie_threeType`, `rightNewTop_rightType`). -/
theorem readingFillPos_left_seedThree :
    ReadingFillPos (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
      (newTops (seedThree hα)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))) (Fin.last 4) :=
  readingFillPos_left_of_coatoms (leftTie_threeType hα) (rightNewTop_rightType α)

/-- **The restricted reading layer is legal below the full grade at `seedThree`**, the first
proper-labelled marker that keeps the tie of its root label
(`TowerProfile.isLegalBelowFullGrade_readingTop_of_coatoms`, `leftTie_threeType`,
`rightNewTop_rightType`). -/
theorem isLegalBelowFullGrade_readingTop_seedThree :
    (readingTop (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
      (newTops (seedThree hα)
        (Fin.castSucc (⟨3, by decide⟩ :
          Fin CaseSplitCounterexample.S.{u}.card)))).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_readingTop_of_coatoms (leftTie_threeType hα) (rightNewTop_rightType α)

end TopReadingApexExample

end VaughtConjecture
