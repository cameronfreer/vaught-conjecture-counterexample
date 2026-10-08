/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerCoatoms

/-!
# An acquired context with a proper-labelled marker: the restricted reading layer is legal

Roadmap, Layer 3 ((R3) of the table of 3.4).

The first acquired context with a proper-labelled, non-isolated marker at which the restricted
reading layer is legal, through the root form of
`TowerProfile.isLegalBelowFullGrade_readingTop_of_acquired`.

* **The left coatom type** (`TopReadingApexExample.oneType`, `TopReadingApexExample.seedOne`,
  defined here): the scheme `S` labelled `3` at its live cells of grade `1` (the cells through the
  point `3`) and `⊥` elsewhere, with the apex added; the seed with `rightType` over the face
  `{0, 1, 2}`.
* **An acquired context** (`TopReadingApexExample.markedCapContextBelow'_oneType`, compiled in this
  repository (theorem named)): along the root `{2, 3}` it is a marked-cap context with root offsets
  below the grade of its cap and root bottoms respected
  (`StageType.markedCapContextBelow'_addApex`).  The root cells `{3}` and `({2, 3}, 1)` both carry
  the proper label `3`: the apex reads them at one code strictly between `⊥` and itself (a
  non-isolated marker).
* **Legality** (`TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedOne`, compiled): the
  reading layer of the apex and the new top `{3}` of `rightType` is legal below the full grade.
  The tied cells are the root cells `z₁ = {3}` (grade `1`) and `z₂ = ({2, 3}, 2)` (grade `2`,
  labelled `⊥`, so the cap reads it as `⊥` by the root bottoms); the cells of grade `1` labelled
  `3` share one value in every lawful labelling (`TopReadingApexExample.tie_one_oneType`), no cell
  of grade `2` or `3` carries a label other than `⊥`.

The shape of this instance: the proper label sits at the cells of grade `1` only.  A proper label
at a cell of grade `2` tied to the grade `1` cells (the family `threeType`) is never a root cell
(`TopReadingApexExample.fifteen_notMem_visibleCells`); there the off-root form applies.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

include hα in
/-- The type `S` labelled `3` at its live cells of grade `1` and `⊥` elsewhere. -/
noncomputable def oneBase : StageType.{u} α 4 where
  toScheme := S
  label := CaseSplitCounterexample.labelling lab3 ⊥ ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_labelling ((isSelfVisible_natCast 3).mpr (by omega))
    (isSelfVisible_bot 2) (isSelfVisible_bot 3) bot_le bot_le
  atStage d := by
    have h3 : AtStage α lab3.{u} := (atStage_natCast 3).mpr (Ordinal.natCast_lt_of_isSuccLimit hα 3)
    unfold CaseSplitCounterexample.labelling
    split_ifs <;> first | exact h3 | exact atStage_bot

/-- **The left coatom type**: `oneBase` with the apex added.  Its apex row reads the cells of grade
`1` through the point `3`, all labelled `3`, at the code of `3`. -/
noncomputable def oneType : StageType.{u} α 4 :=
  (oneBase hα).addApex isLegalBelowFullGrade_S (by omega)

theorem isLegal_oneType : (oneType hα).IsLegal := StageType.isLegal_addApex _ _

/-- The type `oneType` has the face of `T5`: on the face `{0, 1, 2}` its labels are `⊥`. -/
theorem restrictFace_oneType :
    StageType.restrictFace (Coatom.face 3) (oneType hα) = some (faceT5 α) := by
  have hne : univ.map (Coatom.face 3) ≠ (univ : Finset (Fin 4)) := by decide
  rw [oneType, StageType.restrictFace_addApex (t := oneBase hα) isLegalBelowFullGrade_S
    (by omega) (Coatom.face 3) hne, ← restrictFace_T5, T5,
    StageType.restrictFace_addApex (t := T5₀ α) isLegalBelowFullGrade_S (by omega) (Coatom.face 3)
      hne]
  refine StageType.restrictFace_congr_label rfl fun i j hij hi ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  change CaseSplitCounterexample.labelling lab3 ⊥ ⊥ i = ⊥
  refine labelling_bot_eq_bot_of_notMem i fun h3 ↦ ?_
  obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hi (mem_coe.mpr h3)
  exact (Fin.castSucc_lt_last y).ne hy

/-- **The seed of `oneType` and `rightType`.** -/
noncomputable def seedOne : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_oneType hα) (isLegal_rightType α) (restrictFace_oneType hα)
    (restrictFace_rightType α)

/-! ### The cells and labels of `oneType` -/

theorem cases_oneType (z : Fin (oneType hα).card) :
    z = Fin.last _ ∨ ∃ a : Fin CaseSplitCounterexample.S.{u}.card, z = Fin.castSucc a := by
  change Fin ((oneBase hα).card + 1) at z
  induction z using Fin.lastCases with
  | last => exact .inl rfl
  | cast a => exact .inr ⟨a, rfl⟩

theorem gradedIndex_oneType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (oneType hα).toCellScheme.gradedIndex (Fin.castSucc a) =
      (TwoFaceLiftCounterexample.cellScope a, TwoFaceLiftCounterexample.cellGrade a) :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc CaseSplitCounterexample.S 4 a

theorem gradedIndex_oneType_last :
    (oneType hα).toCellScheme.gradedIndex (Fin.last _) = (univ, 4) :=
  StageType.addApex_gradedIndex_last (t := oneBase hα) isLegalBelowFullGrade_S (by omega)

theorem grade_oneType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (oneType hα).toCellScheme.grade (Fin.castSucc a) = TwoFaceLiftCounterexample.cellGrade a :=
  congrArg Prod.snd (gradedIndex_oneType_castSucc hα a)

theorem grade_oneType_last : (oneType hα).toCellScheme.grade (Fin.last _) = 4 :=
  congrArg Prod.snd (gradedIndex_oneType_last hα)

theorem label_oneType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (oneType hα).label (Fin.castSucc a) = CaseSplitCounterexample.labelling lab3 ⊥ ⊥ a :=
  StageType.addApex_label_castSucc (t := oneBase hα) isLegalBelowFullGrade_S (by omega) a

theorem label_oneType_last : (oneType hα).label (Fin.last _) = ⊤ :=
  StageType.addApex_label_last (t := oneBase hα) isLegalBelowFullGrade_S (by omega)

/-- The rows of `oneType` at its old cells are those of `S`. -/
theorem rowAt_oneType_castSucc (a b : Fin CaseSplitCounterexample.S.{u}.card) :
    (oneType hα).toScheme.rowAt (Fin.castSucc a) (Fin.castSucc b) =
      CaseSplitCounterexample.S.rowAt a b :=
  Scheme.rowAt_of_comap (Scheme.isLowerEmbedding_castSucc 4
    (StageType.apexRow (t := oneBase hα) isLegalBelowFullGrade_S)
    isLegalBelowFullGrade_S.not_le) Scheme.comap_rows_castSucc a b

/-- The labelling `labelling 3 ⊥ ⊥` takes the values `3` and `⊥`, the value `3` at the live cells
of grade `1` only. -/
theorem labelling_one_cases (a : Fin 19) :
    (CaseSplitCounterexample.labelling lab3 ⊥ ⊥ a = (lab3 : Label.{u}) ∧
      CaseSplitCounterexample.live a = true ∧ TwoFaceLiftCounterexample.cellGrade a = 1) ∨
      CaseSplitCounterexample.labelling lab3 ⊥ ⊥ a = (⊥ : Label.{u}) := by
  unfold CaseSplitCounterexample.labelling
  split_ifs <;> simp_all

/-- A cell of `oneType` labelled `⊤` is the apex. -/
theorem eq_last_of_label_top_one {x : Fin (oneType hα).card} (hx : (oneType hα).label x = ⊤) :
    x = Fin.last _ := by
  rcases cases_oneType hα x with hxl | ⟨a, rfl⟩
  · exact hxl
  · exfalso
    have hl := (label_oneType_castSucc hα a).symm.trans hx
    rcases labelling_one_cases a with ⟨h3, -⟩ | h0
    · rw [h3, lab3, natCast_label] at hl
      exact WithTop.coe_ne_top (WithBot.coe_injective hl)
    · rw [h0] at hl
      exact bot_ne_top hl

/-- **The cells of grade `1` of `oneType` labelled `3` share one value in every lawful
labelling**, that at the cell `9` (at `(univ, 1)`). -/
theorem tie_one_oneType {p : Fin (oneType hα).card → Label.{u}}
    (hp : (oneType hα).rows.IsLawful p) (z : Fin (oneType hα).card)
    (hz : (oneType hα).toCellScheme.grade z = 1) (hl : (oneType hα).label z ≠ ⊥) :
    p z = p (Fin.castSucc (⟨9, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) := by
  set n9 : Fin CaseSplitCounterexample.S.{u}.card := ⟨9, by decide⟩ with hn9
  rcases cases_oneType hα z with hzl | ⟨a, hza⟩
  · exact absurd ((grade_oneType_last hα).symm.trans (hzl ▸ hz)) (by decide)
  subst hza
  have ha : TwoFaceLiftCounterexample.cellGrade a = 1 :=
    (grade_oneType_castSucc hα a).symm.trans hz
  have hla : CaseSplitCounterexample.live a = true := by
    rcases labelling_one_cases a with ⟨-, h, -⟩ | h0
    · exact h
    · exact absurd ((label_oneType_castSucc hα a).trans h0) hl
  have h9 : TwoFaceLiftCounterexample.cellGrade n9 = 1 := rfl
  have hl9 : CaseSplitCounterexample.live n9 = true := rfl
  have hs9 : TwoFaceLiftCounterexample.cellScope n9 = univ := rfl
  have hmem : Fin.castSucc a ∈ (oneType hα).toCellScheme.below
      ((oneType hα).toCellScheme.gradedIndex (Fin.castSucc n9)) :=
    (gradedIndex_oneType_castSucc hα a).trans_le
      (le_of_le_of_eq (Prod.mk_le_mk.mpr ⟨hs9 ▸ subset_univ _, ha.trans h9.symm |>.le⟩)
        (gradedIndex_oneType_castSucc hα n9).symm)
  have hrow : (oneType hα).toScheme.rowAt (Fin.castSucc n9) (Fin.castSucc n9) =
      (oneType hα).toScheme.rowAt (Fin.castSucc n9) (Fin.castSucc a) := by
    refine ((rowAt_oneType_castSucc hα n9 n9).trans (rowAt_S_live h9 hl9 h9 subset_rfl)).trans
      (Eq.trans ?_ ((rowAt_oneType_castSucc hα n9 a).trans
        (rowAt_S_live h9 hl9 ha (hs9 ▸ subset_univ _))).symm)
    rw [hl9, hla]
  have h1 := (hp.locality (Fin.castSucc n9)).le_of_le
    (d := ⟨Fin.castSucc n9, (oneType hα).toCellScheme.mem_below_gradedIndex _⟩)
    (d' := ⟨Fin.castSucc a, hmem⟩)
    ((Scheme.rowAt_of_mem _).symm.trans_le (hrow.le.trans_eq (Scheme.rowAt_of_mem hmem)))
    ((grade_oneType_castSucc hα a).trans_le
      ((ha.trans h9.symm).le.trans_eq (grade_oneType_castSucc hα n9).symm))
  change min (p (Fin.castSucc n9)) (p (Fin.castSucc n9)) ≤
    min (p (Fin.castSucc a)) (p (Fin.castSucc n9)) at h1
  rw [min_self] at h1
  obtain ⟨v, hv, hle⟩ := hp.availability (Fin.castSucc a) (Fin.castSucc n9)
    ((oneType hα).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hmem)).1
    ((grade_oneType_castSucc hα a).trans
      ((ha.trans h9.symm).trans (grade_oneType_castSucc hα n9).symm))
  rcases cases_oneType hα v with hvl | ⟨b, hvb⟩
  · exact absurd (congrArg Prod.snd ((gradedIndex_oneType_last hα).symm.trans
      ((hvl ▸ hv).trans (gradedIndex_oneType_castSucc hα n9)))) (by decide)
  subst hvb
  have hb : b = n9 := TwoFaceLiftCounterexample.gradedIndex_injective
    ((gradedIndex_oneType_castSucc hα b).symm.trans
      (hv.trans (gradedIndex_oneType_castSucc hα n9)))
  subst hb
  exact le_antisymm hle (h1.trans (min_le_left _ _))

/-! ### `oneType` as an acquired context -/

/-- A cell whose scope lies in `{2, 3}` is visible through the root `{2, 3}`. -/
theorem mem_visibleCells_rootTwoThree {t' : StageType.{u} α 4} {y : Fin t'.card}
    (hy : t'.toCellScheme.scope y ⊆ {2, 3}) : y ∈ t'.visibleCells rootTwoThree := by
  refine Scheme.mem_visibleCells.mpr fun x hx ↦ ?_
  have h := hy (mem_coe.mp hx)
  simp only [mem_insert, mem_singleton] at h
  rcases h with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- The apex of `oneType` is not visible through the root `{2, 3}`. -/
theorem last_notMem_visibleCells_one :
    (Fin.last _ : Fin (oneType hα).card) ∉ (oneType hα).visibleCells rootTwoThree := by
  intro ha
  have h0 : ((0 : Fin 4) : Fin 4) ∈
      ((oneType hα).toCellScheme.scope (Fin.last _) : Set (Fin 4)) :=
    Eq.mpr (congrArg (fun s : Finset (Fin 4) ↦ (0 : Fin 4) ∈ (s : Set (Fin 4)))
      (congrArg Prod.fst (gradedIndex_oneType_last hα))) (by simp)
  obtain ⟨i, hi⟩ := Scheme.mem_visibleCells.mp ha h0
  fin_cases i <;> simp [rootTwoThree] at hi

/-- **`oneType` is an acquired marked-cap context along the root `{2, 3}`**
(`StageType.markedCapContextBelow'_addApex`): the root has two points, `2 + 1 < 4`, no root label
is `⊤`, and the root offsets lie below `4` (the root cells `{3}` and `{2, 3}` of grade `1` are
labelled `3`; the others `⊥`). -/
theorem markedCapContextBelow'_oneType :
    TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) rootTwoThree := by
  refine StageType.markedCapContextBelow'_addApex (t₀ := oneBase hα) isLegalBelowFullGrade_S
    (by omega) (by omega) (fun y hy hyt ↦ ?_) fun y _ μ f hμ hy ↦ ?_
  · exact last_notMem_visibleCells_one hα (eq_last_of_label_top_one hα hyt ▸ hy)
  · rcases cases_oneType hα y with rfl | ⟨a, rfl⟩
    · exact absurd ((label_oneType_last hα).symm.trans hy)
        (fun h' ↦ WithTop.coe_ne_top (WithBot.coe_injective h'.symm))
    · have hy' := (label_oneType_castSucc hα a).symm.trans hy
      rcases labelling_one_cases a with ⟨h3, -⟩ | h0
      · have e := h3.symm.trans hy'
        rw [lab3, natCast_label] at e
        have h' : ((0 : Ordinal.{u}) + (3 : ℕ)) = μ + f := by
          rw [zero_add]; exact WithTop.coe_injective (WithBot.coe_injective e)
        have := ((add_natCast_eq_add_natCast_iff Ordinal.isSuccPrelimit_zero hμ).mp h').2
        omega
      · exact absurd (h0.symm.trans hy').symm WithBot.coe_ne_bot

/-- **The restricted reading layer is legal at the acquired context `oneType`**
(`TowerProfile.isLegalBelowFullGrade_readingTop_of_acquired`, root form): the seed `seedOne` of
`oneType` and `rightType`, the marker the apex of `oneType` (a top cap whose row reads the root
cells `{3}` and `{2, 3}`, both labelled `3`, at one code strictly between `⊥` and itself), the new
top the cell `{3}` of `rightType`.  The tied cells are the root cells `z₁ = {3}` (grade `1`) and
`z₂ = ({2, 3}, 2)` (grade `2`, labelled `⊥`, read as `⊥` by the root bottoms). -/
theorem isLegalBelowFullGrade_readingTop_seedOne :
    (readingTop (seedOne hα) (leftCell (seedOne hα) (Fin.last _))
      (newTops (seedOne hα)
        (Fin.castSucc (⟨3, by decide⟩ :
          Fin CaseSplitCounterexample.S.{u}.card)))).IsLegalBelowFullGrade := by
  obtain ⟨c, r, hctx, hoff, hbot⟩ := markedCapContextBelow'_oneType hα
  obtain rfl := eq_last_of_label_top_one hα hctx.1.2.1
  have hgrade (a : Fin CaseSplitCounterexample.S.{u}.card)
      (hl : (oneType hα).label (Fin.castSucc a) ≠ ⊥) :
      TwoFaceLiftCounterexample.cellGrade a = 1 := by
    rcases labelling_one_cases a with ⟨-, -, h⟩ | h0
    · exact h
    · exact absurd ((label_oneType_castSucc hα a).trans h0) hl
  refine isLegalBelowFullGrade_readingTop_of_acquired (I := seedOne hα) hctx hoff hbot
    (grade_oneType_last hα)
    (fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := oneBase hα)
      isLegalBelowFullGrade_S (by omega) hz)
    (fun z _ hz ↦ (StageType.rowAt_addApex_last_eq_bot_iff (t₀ := oneBase hα)
      isLegalBelowFullGrade_S (by omega) z).mpr hz)
    (fun z hz ↦ ?_)
    (z₁ := Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
    (z₂ := Fin.castSucc (⟨12, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
    (mem_visibleCells_rootTwoThree
      ((congrArg Prod.fst (gradedIndex_oneType_castSucc hα _)).le.trans (by decide)))
    (mem_visibleCells_rootTwoThree
      ((congrArg Prod.fst (gradedIndex_oneType_castSucc hα _)).le.trans (by decide)))
    ((grade_oneType_castSucc hα _).trans rfl) ((grade_oneType_castSucc hα _).trans rfl)
    (.inl ?_) (fun p hp z hz hl ↦ ?_) (fun p _ z hz hl ↦ ?_) (fun z hz ↦ ?_)
    (rightNewTop_rightType α)
  · -- the face off the point `3` is labelled `⊥`
    rcases cases_oneType hα z with rfl | ⟨a, rfl⟩
    · exact absurd (Eq.mpr (congrArg (Fin.last 3 ∈ ·)
        (congrArg Prod.fst (gradedIndex_oneType_last hα))) (mem_univ _)) hz
    · refine (label_oneType_castSucc hα a).trans (labelling_bot_eq_bot_of_notMem a fun h3 ↦ hz ?_)
      exact Eq.mpr (congrArg (Fin.last 3 ∈ ·)
        (congrArg Prod.fst (gradedIndex_oneType_castSucc hα a))) h3
  · -- the cell `({2, 3}, 2)` is labelled `⊥`
    refine (label_oneType_castSucc hα _).trans ?_
    change CaseSplitCounterexample.labelling lab3 ⊥ ⊥ (12 : Fin 19) = ⊥
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live]
  · -- one value at the cells of grade `1`, by `tie_one_oneType` (the cells `{3}` and `9` agree)
    rw [tie_one_oneType hα hp z hz hl]
    exact (tie_one_oneType hα hp _ ((grade_oneType_castSucc hα _).trans rfl)
      ((label_oneType_castSucc hα _).trans_ne (by
        change CaseSplitCounterexample.labelling lab3 ⊥ ⊥ (3 : Fin 19) ≠ ⊥
        simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
          TwoFaceLiftCounterexample.cellGrade]))).symm
  · -- no cell of grade `2` is labelled other than `⊥`
    rcases cases_oneType hα z with rfl | ⟨a, rfl⟩
    · exact absurd ((grade_oneType_last hα).symm.trans hz) (by decide)
    · exact absurd ((grade_oneType_castSucc hα a).symm.trans hz)
        (by rw [hgrade a hl]; decide)
  · -- the cells of grade `3` are labelled `⊥`
    rcases cases_oneType hα z with rfl | ⟨a, rfl⟩
    · exact absurd ((grade_oneType_last hα).symm.trans hz) (by decide)
    · by_contra hl
      exact absurd ((grade_oneType_castSucc hα a).symm.trans hz) (by rw [hgrade a hl]; decide)

end TopReadingApexExample

end VaughtConjecture
