/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedFieldLayerLift
import VaughtConjecture.Continuation.StableRecoveryAdmittedLift

/-!
# The admitted field layer at `P`, and the first instances of its provision

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade with a restricted catalogue at the
reading grades), 3.3; the admitted field layer of `VaughtConjecture.Extension.AdmittedFieldLayer`
and the capped correctness at `P` of
`VaughtConjecture.Continuation.StableRecoveryCapCorrectness`.

**Extension through a field layer on a sub-catalogue, by a chosen template**
(`VaughtConjecture.Extension.AdmittedFieldLayerLift`).  The lifts of the canonical field layer
extend a boundary labelling by the field row of the orbit code of the labelling itself.  On a
sub-catalogue `C` the same proofs go through as soon as that orbit code lies in `C`:

* `Scheme.exists_isLawfulBelow_fieldLayerOn` (cap `⊥`): a labelling `p` lawful below `(univ, k)`
  whose orbit code is in `C` extends, unchanged at the old cells, to a labelling lawful below
  `(univ, k)` in the field layer on `C`;
* `Scheme.exists_extension_fieldLayerOn` (short positive cap `h`): if moreover `p` agrees with a
  member `a` of `C` capped at `h`, the extension agrees with the field row of `a` capped at `h`.

So the provision for a boundary state is met by **choosing** a lawful extension (the fill) whose
orbit code is admitted.

**The admitted layer at `P`** (`GatedExtensionCounterexample.admittedLayerP`).  Over the seed of
`P` with itself, the lower scheme is the doubled lower layer (`Seed.doubledLower`: the amalgam and
one copy of full scope of `P`'s dead cell of graded index `(univ, 1)`), and the layer at the grade
`2` is the admitted field layer (`Scheme.admittedFieldLayer`) for the admission `admissionP`: in the
bottom class of the private copy, capped correctness for the cap `3` with the marker at the cap
(`GatedExtensionCounterexample.IsCapCorrectP`).

* **Cap `⊥`** (`GatedExtensionCounterexample.exists_lift_bot_admittedLayerP`): the raised fill
  `(⊥, ⊥, ⊥, 3, 2 | ⊥, ⊥, ⊥, 3, 3)` (`GatedExtensionCounterexample.exists_fillP`) is lawful on the
  lower scheme, its orbit code is admitted (`GatedExtensionCounterexample.admissionP_orbitCode`),
  and so some labelling lawful below `(univ, 2)` in the admitted layer reads `P`'s lawful `(3, 2)`
  on the private copy (and `(3, 3)` on the donor copy): the extension from the private coatom at
  the cap `⊥` of `(3, 2)`, by `Scheme.exists_lift_bot_admittedFieldLayer`.
* **Cap `2` against the copy `(2, 3 | 2, 3)`**
  (`GatedExtensionCounterexample.exists_lift_two_admittedLayerP`): the glued state `(2, 3 | 2, 3)`
  (the old part of the doubled copy over `4`) is lawful and its orbit code is admitted; the raised
  fill agrees with that code capped at the least grid point `2`; and some labelling lawful below
  `(univ, 2)` in the admitted layer reads `(3, 2 | 3, 3)` on the old cells and agrees with the row
  of that code capped at `2`, by `Scheme.exists_lift_admittedFieldLayer`.

Not proved here: the extension for every boundary state and every cap (the provision clause in
full at `P`), the lifts from the donor coatom, and the bountifulness of the admitted layer.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

/-! ### The admitted layer at `P` -/

namespace GatedExtensionCounterexample

variable (β : Ordinal.{u})

/-- The lower scheme over the seed of `P` with itself: the amalgam and the copy of full scope of
the dead cell of graded index `(univ, 1)`. -/
noncomputable abbrev lowerP : Scheme.{u} 3 := (seedP β).doubledLower rfl

/-- No cell of the lower scheme lies above `(univ, 2)`. -/
theorem not_univ_two_le_lowerP (d : Fin (lowerP β).card) :
    ¬ ((univ : Finset (Fin 3)), 2) ≤ (lowerP β).toCellScheme.gradedIndex d :=
  (seedP β).not_univ_two_le_doubledLower rfl d

/-- The private copy of a labelling of the lower scheme. -/
noncomputable def privP (e : Fin (lowerP β).card → Label.{u}) (z : Fin 5) : Label.{u} :=
  e (Fin.castAdd _ (StageType.faceCell (seedP β).restrictFace_left z))

/-- The donor copy of a labelling of the lower scheme. -/
noncomputable def donP (e : Fin (lowerP β).card → Label.{u}) (z : Fin 5) : Label.{u} :=
  e (Fin.castAdd _ (StageType.faceCell ((seedP β).restrictFace_right_left rfl) z))

/-- **The admission at `P`**: in the bottom class of the private copy, capped correctness for the
cap `3` with the marker at the cap (offset `0`). -/
def admissionP (e : Fin (lowerP β).card → Label.{u}) : Prop :=
  InBottomClassP (privP β e) → IsCapCorrectP 3 3 0 (privP β e) (donP β e)

/-- **The admitted layer at `P`**: the admitted field layer at the grade `2` over the lower
scheme. -/
noncomputable abbrev admittedLayerP : Scheme.{u} 3 :=
  (lowerP β).admittedFieldLayer 2 (admissionP β) (not_univ_two_le_lowerP β)

/-- The dead cells of `P` are labelled `⊥` by every `labelling`. -/
private theorem labelling_eq_bot_of_grade {a b : Label.{u}} {z : Fin 5}
    (hz : (P β).toCellScheme.grade z = 1) : labelling a b z = ⊥ := by
  change cellGrade z = 1 at hz
  fin_cases z <;> first | rfl | (exfalso; revert hz; decide)

/-- **Glued states on the lower scheme**: two lawful labellings `labelling a b`, `labelling a' b'`
of `P` glue to a labelling of the lower scheme lawful there, reading them on the private and donor
copies and `⊥` at the dead cell of full scope. -/
theorem exists_isLawful_lowerP {a b a' b' : Label.{u}} (hL : rows.{u}.IsLawful (labelling a b))
    (hR : rows.{u}.IsLawful (labelling a' b')) :
    ∃ g : Fin (lowerP β).card → Label.{u}, (lowerP β).rows.IsLawful g ∧
      privP β g = labelling a b ∧ donP β g = labelling a' b' ∧
        ∀ i, g (Fin.natAdd _ i) = ⊥ := by
  obtain ⟨w, hw, hwL, hwR⟩ := (seedP β).exists_isLawful_glue rfl hL hR (by
    change ∀ z : Fin 5, Fin.last 1 ∉ cellScope z → labelling a b z = labelling a' b' z
    intro z hz
    fin_cases z
    · rfl
    all_goals exact absurd (by decide) hz)
  -- the glued labelling is `⊥` at the cells of grade `1`
  have hw1 (d : Fin (seedP β).amalgam.card) (hd : (seedP β).amalgam.toCellScheme.grade d = 1) :
      w d = ⊥ := by
    rcases (seedP β).eq_faceCell_or rfl d with h | h
    · rw [← h, hwL]
      rw [← h, StageType.grade_faceCell] at hd
      exact labelling_eq_bot_of_grade β hd
    · rw [← h, hwR]
      rw [← h, StageType.grade_faceCell] at hd
      exact labelling_eq_bot_of_grade β hd
  have hc2 : (seedP β).left.toCellScheme.gradedIndex (2 : Fin 5) =
      ((univ : Finset (Fin 2)), 1) := by
    change cells.gradedIndex 2 = _
    rw [gradedIndex_cells]
    rfl
  obtain ⟨i₀, -⟩ := Scheme.exists_fullCell_eq (T := (seedP β).left.toScheme) (j := 1) hc2
  refine ⟨Fin.append w fun _ ↦ ⊥, Scheme.isLawful_appendFullCells (h := (seedP β).not_univ_le 1)
    ?_ (fun _ ↦ ?_) (fun i ↦ ?_)
    fun s hs ↦ ⟨i₀, ?_⟩, ?_, ?_, fun i ↦ Fin.append_right _ _ i⟩
  · convert hw using 1
    funext d
    exact Fin.append_left _ _ d
  · rw [Fin.append_right]
    exact isSelfVisible_bot _
  · convert TransformsTo.bot _ _ using 1
    funext t
    rw [Fin.append_right, min_bot_right]
  · rw [Fin.append_right]
    induction s using Fin.addCases with
    | left d =>
      rw [Fin.append_left, hw1 d (by
        rw [← Scheme.appendFullCellsScheme_grade_castAdd]; exact hs)]
    | right j => rw [Fin.append_right]
  · funext z
    exact (Fin.append_left _ _ _).trans (hwL z)
  · funext z
    exact (Fin.append_left _ _ _).trans (hwR z)

/-- The private and donor copies of the orbit code of a labelling of the lower scheme are the
orbit map applied to its private and donor copies. -/
theorem privP_orbitCode (g : Fin (lowerP β).card → Label.{u}) :
    privP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) =
      fun z ↦ orbitMap 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g) (privP β g z) := by
  funext z
  simp only [privP, orbitCode_apply]
  rw [CellScheme.splice_of_le]
  exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans_le
    (Nat.lt_succ_iff.mp ((seedP β).grade_lt _))

/-- The donor copy of the orbit code is the orbit map applied to the donor copy. -/
theorem donP_orbitCode (g : Fin (lowerP β).card → Label.{u}) :
    donP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) =
      fun z ↦ orbitMap 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g) (donP β g z) := by
  funext z
  simp only [donP, orbitCode_apply]
  rw [CellScheme.splice_of_le]
  exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans_le
    (Nat.lt_succ_iff.mp ((seedP β).grade_lt _))

/-- **The orbit code of a glued state reading the donor's high cells at least as the private cap
is admitted.** -/
theorem admissionP_orbitCode {g : Fin (lowerP β).card → Label.{u}}
    (hZ : donP β g 1 = ⊥ ∧ donP β g 2 = ⊥)
    (hT : privP β g 3 ≤ donP β g 3 ∧ privP β g 3 ≤ donP β g 4) :
    admissionP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  intro _
  rw [privP_orbitCode, donP_orbitCode]
  refine isCapCorrectP_of_le (fun z hz ↦ ?_) fun y hy ↦ ?_
  · simp only [selfZ, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [hZ.1]
    · simp [hZ.2]
  · simp only [selfT, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact monotone_orbitMap 2 _ hT.1
    · exact monotone_orbitMap 2 _ hT.2

/-- `labelling 3 3` is lawful: the labelling `⊤ ⊤` capped at `3`. -/
theorem isLawful_labelling_three_three :
    rows.{u}.IsLawful (labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u})) := by
  have h := isLawful_labelling_top_top.{u}.min_const_of_isSelfVisible (K := 2)
    (c := ((3 : ℕ) : Label.{u})) (fun d ↦ by fin_cases d <;> decide) (by simp)
  convert h using 1
  funext d
  fin_cases d <;> simp [labelling]

/-- The **raised fill** at `P`: `(⊥, ⊥, ⊥, 3, 2)` on the private copy, `(⊥, ⊥, ⊥, 3, 3)` on the
donor copy, `⊥` at the dead cell of full scope; lawful on the lower scheme. -/
theorem exists_fillP : ∃ g : Fin (lowerP β).card → Label.{u}, (lowerP β).rows.IsLawful g ∧
    privP β g = labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) ∧
    donP β g = labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) ∧
      ∀ i, g (Fin.natAdd _ i) = ⊥ :=
  exists_isLawful_lowerP β isLawful_labelling_three_two isLawful_labelling_three_three

/-- The cells of the lower scheme have grade at most `2`. -/
theorem grade_lowerP_le (d : Fin (lowerP β).card) : (lowerP β).toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left a =>
    exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans_le
      (Nat.lt_succ_iff.mp ((seedP β).grade_lt _))
  | right i =>
    rw [Scheme.appendFullCellsScheme_grade_natAdd]
    omega

/-- **The private-coatom extension of `(3, 2)` at the cap `⊥` in the admitted layer at `P`**: some
labelling lawful below `(univ, 2)` in the admitted layer reads `P`'s lawful `(3, 2)` on the private
copy and `(3, 3)` on the donor copy.  The template is the orbit code of the raised fill, which is
admitted (`admissionP_orbitCode`). -/
theorem exists_lift_bot_admittedLayerP :
    ∃ v : Fin ((lowerP β).card + ((lowerP β).admittedCatalogue 2 (admissionP β)).card) →
        Label.{u},
      (admittedLayerP β).rows.IsLawfulBelow (univ, 2) (fun x ↦ v x) ∧
      (∀ z : Fin 5, v (Fin.castAdd _ (Fin.castAdd _
        (StageType.faceCell (seedP β).restrictFace_left z))) =
          labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) z) ∧
      ∀ z : Fin 5, v (Fin.castAdd _ (Fin.castAdd _
        (StageType.faceCell ((seedP β).restrictFace_right_left rfl) z))) =
          labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) z := by
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_fillP β
  obtain ⟨v, hv, hve⟩ := Scheme.exists_lift_bot_admittedFieldLayer
    (hS := not_univ_two_le_lowerP β) (A := admissionP β)
    (CellScheme.Rows.IsLawful.isLawfulBelow hg _)
    (admissionP_orbitCode β ⟨by rw [hgR]; rfl, by rw [hgR]; rfl⟩
      ⟨by rw [hgL, hgR]; exact le_rfl, by rw [hgL, hgR]; exact le_rfl⟩)
  refine ⟨v, hv, fun z ↦ ?_, fun z ↦ ?_⟩
  · rw [hve _ (grade_lowerP_le β _)]
    exact congrFun hgL z
  · rw [hve _ (grade_lowerP_le β _)]
    exact congrFun hgR z

private theorem gridPoint_two_zero : gridPoint.{u} 2 0 = ((2 : ℕ) : Label.{u}) := by
  simp [gridPoint]

/-- At the least grid point `2`, the labellings with values `⊥`, `2`, `3` read alike when they are
`⊥` at the same cells. -/
private theorem min_labelling_gridPoint {a b a' b' : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (ha' : 2 ≤ a')
    (hb' : 2 ≤ b') (z : Fin 5) :
    min (labelling ((a : ℕ) : Label.{u}) ((b : ℕ) : Label.{u}) z) (gridPoint 2 0) =
      min (labelling ((a' : ℕ) : Label.{u}) ((b' : ℕ) : Label.{u}) z) (gridPoint 2 0) := by
  rw [gridPoint_two_zero]
  have hle {x : ℕ} (hx : 2 ≤ x) : ((2 : ℕ) : Label.{u}) ≤ (x : ℕ) := natCast_label_le.mpr hx
  fin_cases z
  · rfl
  · rfl
  · rfl
  · exact (min_eq_right (hle ha)).trans (min_eq_right (hle ha')).symm
  · exact (min_eq_right (hle hb)).trans (min_eq_right (hle hb')).symm

/-- **The capped extension at `P`: cap `2` against the copy `(2, 3 | 2, 3)`.**  The glued state
`(2, 3 | 2, 3)` (the old part of the doubled copy over `4`) is lawful on the lower scheme and its
orbit code is admitted; and some labelling lawful below `(univ, 2)` in the admitted layer reads the
raised fill `(3, 2 | 3, 3)` on the old cells and agrees, capped at the least grid point `2`, with
the field row of that orbit code (the row of its cell in the admitted layer). -/
theorem exists_lift_two_admittedLayerP :
    ∃ g₄ : Fin (lowerP β).card → Label.{u}, (lowerP β).rows.IsLawful g₄ ∧
      privP β g₄ = labelling ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) ∧
      donP β g₄ = labelling ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) ∧
      admissionP β (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g₄)) ∧
      ∃ v : Fin ((lowerP β).card + ((lowerP β).admittedCatalogue 2 (admissionP β)).card) →
          Label.{u},
        (admittedLayerP β).rows.IsLawfulBelow (univ, 2) (fun x ↦ v x) ∧
        (∀ z : Fin 5, v (Fin.castAdd _ (Fin.castAdd _
          (StageType.faceCell (seedP β).restrictFace_left z))) =
            labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) z) ∧
        (∀ z : Fin 5, v (Fin.castAdd _ (Fin.castAdd _
          (StageType.faceCell ((seedP β).restrictFace_right_left rfl) z))) =
            labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) z) ∧
        ∀ x ∈ (admittedLayerP β).toCellScheme.below (univ, 2),
          min (v x) (gridPoint 2 0) = min ((lowerP β).fieldRowOn 2
            ((lowerP β).admittedCatalogue 2 (admissionP β))
            (orbitCode 2 ((lowerP β).toCellScheme.splice 2 (fun _ ↦ ⊥) g₄)) x) (gridPoint 2 0) := by
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_fillP β
  obtain ⟨g₄, hg₄, hg₄L, hg₄R, hg₄N⟩ :=
    exists_isLawful_lowerP β isLawful_labelling_two_three isLawful_labelling_two_three
  have h23 : ((2 : ℕ) : Label.{u}) ≤ (3 : ℕ) := natCast_label_le.mpr (by decide)
  have hA₄ := admissionP_orbitCode β (g := g₄) ⟨by rw [hg₄R]; rfl, by rw [hg₄R]; rfl⟩
    ⟨by rw [hg₄L, hg₄R], by rw [hg₄L, hg₄R]; exact h23⟩
  -- the raised fill agrees with the orbit code of `(2, 3 | 2, 3)` capped at `2`
  have hag (d : Fin (lowerP β).card) (_ : (lowerP β).toCellScheme.grade d ≤ 2) :
      min (g d) (gridPoint 2 0) = min (orbitCode 2 ((lowerP β).toCellScheme.splice 2
        (fun _ ↦ ⊥) g₄) d) (gridPoint 2 0) := by
    rw [min_orbitCode_gridPoint_zero, CellScheme.splice_of_le (grade_lowerP_le β d)]
    induction d using Fin.addCases with
    | right i => rw [hgN, hg₄N]
    | left a =>
      rcases (seedP β).eq_faceCell_or rfl a with h | h
      · rw [← h]
        have e1 := congrFun hgL ((seedP β).doublingCell rfl a)
        have e2 := congrFun hg₄L ((seedP β).doublingCell rfl a)
        simp only [privP] at e1 e2
        rw [e1, e2]
        exact min_labelling_gridPoint (by omega) (by omega) (by omega) (by omega) _
      · rw [← h]
        have e1 := congrFun hgR ((seedP β).doublingCell rfl a)
        have e2 := congrFun hg₄R ((seedP β).doublingCell rfl a)
        simp only [donP] at e1 e2
        rw [e1, e2]
        exact min_labelling_gridPoint (by omega) (by omega) (by omega) (by omega) _
  obtain ⟨v, hv, hve, hcap⟩ := Scheme.exists_lift_admittedFieldLayer
    (hS := not_univ_two_le_lowerP β) (A := admissionP β)
    (CellScheme.Rows.IsLawful.isLawfulBelow hg _)
    (admissionP_orbitCode β ⟨by rw [hgR]; rfl, by rw [hgR]; rfl⟩
      ⟨by rw [hgL, hgR]; exact le_rfl, by rw [hgL, hgR]; exact le_rfl⟩)
    (CellScheme.Rows.IsLawful.isLawfulBelow hg₄ _) hA₄ (isSelfVisible_gridPoint 2 0)
    (isShort_gridPoint 2 0) (bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 2 0)) hag
  refine ⟨g₄, hg₄, hg₄L, hg₄R, hA₄, v, hv, fun z ↦ ?_, fun z ↦ ?_, hcap⟩
  · rw [hve _ (grade_lowerP_le β _)]
    exact congrFun hgL z
  · rw [hve _ (grade_lowerP_le β _)]
    exact congrFun hgR z

end GatedExtensionCounterexample

end VaughtConjecture
