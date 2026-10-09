/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryDoubledGate

/-!
# Capped correctness at the private type `P`, for the self-donor

Roadmap, Layer 3, 3.3 (the private cap and the decoder of (R4)) and 3.1 (a completion whose
catalogue at the reading grade is restricted); the refutation
`GatedExtensionCounterexample.not_isGatedReadingExtension_doubledApex` of
`VaughtConjecture.Continuation.StableRecoveryDoubledGate`.

**The request data at `P`.**  The input is the private type `P` on two points (cells `0`, `1`,
`2` dead, of grade `1`; cells `3`, `4` of full scope and grade `2`, both labelled `⊤`), with
`f = Fin.castSuccEmb` and the self-donor `D = P`.  A **state** at the reading grade `N = 2` is the
row, on the old cells, of a cell of full scope and grade `2` of a completion of the seed of `P`
with itself.  Its values at the copies of the cells of `P` along the first coatom (the private
copy) and along the second (the donor copy) are two functions `sL`, `sR` on the cells of `P`.

* the cap `C` is `3` or `4` (grade `N = 2`); the marker `a` is a cell of grade `N` below the cap
  (`3` or `4`); the marker offset is any `R` (the request asks `R < N`; no value used below
  depends on it);
* the donor's cells requested `⊥` are `Z = {1, 2}`, the cells requested high are `T = {3, 4}`, and
  no cell is requested at a proper ordinal (`F = ∅`, so no reference is needed);
* the bottom class of the private side (`GatedExtensionCounterexample.InBottomClassP`): `⊥`
  exactly at the dead cells `0`, `1`, `2`.

Capped correctness (`GatedExtensionCounterexample.IsCapCorrectP`) asks `min (sR z) (sL C) = ⊥` for
`z ∈ Z`, and `min (vr_N^R (sL a)) (sL C) ≤ min (sR y) (sL C)` for `y ∈ T`; a state is admitted
(`GatedExtensionCounterexample.IsAdmittedP`) when it is correct as soon as its private side is in
the bottom class.

**Results** (compiled in this repository).

* `GatedExtensionCounterexample.isCapCorrectP_self_iff`: with the marker at the cap, and the
  cap's value self-visible at `N` (as every value of a row at its own cell is), capped
  correctness is the **capped reading** of the high cells: `sL C ≤ sR y` for `y ∈ T`.  With any
  marker, the capped reading implies correctness (`isCapCorrectP_of_le`).
* The two cells of full scope and grade `2` of the doubled coface have the states
  `(row_P c, row_P c)` for `c = 3, 4` (`Seed.rowAt_doubledApex_left`,
  `Seed.rowAt_doubledApex_right`, `rowAt_P_three`, `rowAt_P_four`); both fail the uncapped
  reading that defeats the readers of `not_isGatedReadingExtension_doubledApex`
  (`not_readsBoth_rowAt_P`).  Under admission:
  * the copy over the cap is **not admitted** when the marker is the cap
    (`not_isAdmittedP_rowAt_self`): it reads the other full cell at `2`, below its own value `3`;
  * it **is admitted** when the marker is the other full cell (`isAdmittedP_rowAt_self_of_ne`);
  * the copy over the other full cell is admitted for every marker and offset
    (`isAdmittedP_rowAt_other`): it reads both high cells at least as the cap.

  So the restricted catalogue does not drop exactly the states that defeat the uncapped reading:
  with the marker at the cap it drops exactly the copy over the cap, the one state failing the
  capped reading; with the other marker it drops neither.
* `exists_admitted_reader_P` (**feasibility at `P`**): the state `sL = (⊥, ⊥, ⊥, 3, 2)`,
  `sR = (⊥, ⊥, ⊥, 3, 3)` is lawful on each face, coded, agrees at the shared cell, is in the bottom
  class, is admitted for the cap `3` with every marker and offset, and reads both high cells of
  the donor exactly as the cap (uncapped).  Not compiled: that the glued state is lawful on the
  amalgam (argued: the amalgam's lawful labellings are those lawful on both coatom faces, as in
  `Coatom.isLawful_amalgamLabel`), and the bountifulness of any layer of admitted states at `P`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

/-! ### The rows of the doubled coface at the copies -/

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right) (hI : I.left.IsLegal)

/-- A copy of full scope and grade `2` reads the private copy of a cell of `T` as the cell under
it reads that cell in `T`. -/
theorem rowAt_doubledApex_left {x : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2))
    (z : Fin I.left.card) :
    (I.doubledApex hLR hI).rowAt x.castSucc
        (I.old hLR (StageType.faceCell I.restrictFace_left z)).castSucc =
      I.left.rowAt (I.doubledCell hLR x) z := by
  rw [I.rowAt_doubledApex_castSucc hLR hI (I.mem_below_of_gradedIndex_eq hLR hx _),
    doubledCell_old, doublingCell_faceCell_left]

/-- A copy of full scope and grade `2` reads the donor copy of a cell of `T` as the cell under it
reads that cell in `T`. -/
theorem rowAt_doubledApex_right {x : Fin (I.doubled hLR).card}
    (hx : (I.doubled hLR).toCellScheme.gradedIndex x = ((univ : Finset (Fin 3)), 2))
    (z : Fin I.left.card) :
    (I.doubledApex hLR hI).rowAt x.castSucc
        (I.old hLR (StageType.faceCell (I.restrictFace_right_left hLR) z)).castSucc =
      I.left.rowAt (I.doubledCell hLR x) z := by
  rw [I.rowAt_doubledApex_castSucc hLR hI (I.mem_below_of_gradedIndex_eq hLR hx _),
    doubledCell_old, doublingCell_faceCell_right]

end Seed

namespace GatedExtensionCounterexample

/-! ### The request data at `P` -/

/-- The donor cells requested `⊥`: the dead cells on the new point. -/
def selfZ : Finset (Fin 5) := {1, 2}

/-- The donor cells requested high: the two cells of full scope. -/
def selfT : Finset (Fin 5) := {3, 4}

/-- **The bottom class** of the private side: `⊥` exactly at the dead cells. -/
def InBottomClassP (sL : Fin 5 → Label.{u}) : Prop :=
  ∀ d, sL d = ⊥ ↔ d ∈ ({0, 1, 2} : Finset (Fin 5))

/-- **Capped correctness** of a state (`sL` on the private copy, `sR` on the donor copy) for the
cap `C`, the marker `a` and the marker offset `R`, at the threshold `N = 2`: the requested-`⊥` cells
are `⊥` below the cap, and the high cells lie at least at the replaced marker, below the cap. -/
def IsCapCorrectP (C a : Fin 5) (R : ℕ) (sL sR : Fin 5 → Label.{u}) : Prop :=
  (∀ z ∈ selfZ, min (sR z) (sL C) = ⊥) ∧
    ∀ y ∈ selfT, min (visibilityReplace 2 R (sL a)) (sL C) ≤ min (sR y) (sL C)

/-- **Admission**: a state is admitted when it is correct as soon as its private side is in the
bottom class. -/
def IsAdmittedP (C a : Fin 5) (R : ℕ) (sL sR : Fin 5 → Label.{u}) : Prop :=
  InBottomClassP sL → IsCapCorrectP C a R sL sR

variable {C a : Fin 5} {R : ℕ} {sL sR : Fin 5 → Label.{u}}

/-- **With the marker at the cap, correctness is the capped reading** of the high cells, when the
cap's value is self-visible at `N = 2`. -/
theorem isCapCorrectP_self_iff (hC : IsSelfVisible 2 (sL C)) :
    IsCapCorrectP C C R sL sR ↔
      (∀ z ∈ selfZ, min (sR z) (sL C) = ⊥) ∧ ∀ y ∈ selfT, sL C ≤ sR y := by
  rw [IsCapCorrectP, hC.visibilityReplace_eq, min_self]
  refine and_congr Iff.rfl (forall₂_congr fun y _ ↦ ?_)
  exact ⟨fun h ↦ (h.trans (min_le_left _ _)), fun h ↦ le_min h le_rfl⟩

/-- **The capped reading gives correctness** with every marker and offset. -/
theorem isCapCorrectP_of_le (hZ : ∀ z ∈ selfZ, min (sR z) (sL C) = ⊥)
    (hT : ∀ y ∈ selfT, sL C ≤ sR y) : IsCapCorrectP C a R sL sR :=
  ⟨hZ, fun y hy ↦ (min_le_right _ _).trans (le_min (hT y hy) le_rfl)⟩

/-! ### The rows of the full cells of `P` -/

/-- The row of the full cell `3` of `P`: `3` at itself, `2` at the other full cell, `⊥` at the dead
cells. -/
theorem rowAt_P_three {β : Ordinal.{u}} :
    (P β).rowAt (3 : Fin 5) = labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) := by
  funext (d : Fin 5)
  have hmem : d ∈ (P β).toCellScheme.below ((P β).toCellScheme.gradedIndex (3 : Fin 5)) := by
    change d ∈ cells.below (cells.gradedIndex 3)
    rw [CellScheme.mem_below, gradedIndex_cells, gradedIndex_cells]
    fin_cases d <;> decide
  rw [Scheme.rowAt_of_mem hmem]
  fin_cases d <;> rfl

/-- The row of the full cell `4` of `P`. -/
theorem rowAt_P_four {β : Ordinal.{u}} :
    (P β).rowAt (4 : Fin 5) = labelling ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) := by
  funext (d : Fin 5)
  have hmem : d ∈ (P β).toCellScheme.below ((P β).toCellScheme.gradedIndex (4 : Fin 5)) := by
    change d ∈ cells.below (cells.gradedIndex 4)
    rw [CellScheme.mem_below, gradedIndex_cells, gradedIndex_cells]
    fin_cases d <;> decide
  rw [Scheme.rowAt_of_mem hmem]
  fin_cases d <;> rfl

private theorem two_lt_three : ((2 : ℕ) : Label.{u}) < ((3 : ℕ) : Label.{u}) :=
  natCast_label_lt.mpr (by decide)

/-- The rows of the full cells are in the bottom class. -/
theorem inBottomClassP_labelling {x y : ℕ} :
    InBottomClassP (labelling ((x : ℕ) : Label.{u}) ((y : ℕ) : Label.{u})) := by
  intro d
  fin_cases d <;> simp [labelling]

/-- **The full cells defeat the uncapped reading**: the row of a full cell does not read both full
cells as it reads the cap. -/
theorem not_readsBoth_rowAt_P {β : Ordinal.{u}} {c C : Fin 5} (hc : cellGrade c = 2) :
    ¬ ((P β).rowAt c (3 : Fin 5) = (P β).rowAt c C ∧
      (P β).rowAt c (4 : Fin 5) = (P β).rowAt c C) := by
  rintro ⟨h3, h4⟩
  have h := h3.trans h4.symm
  have hc' : c = 3 ∨ c = 4 := by
    fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; revert hc; decide)
  rcases hc' with rfl | rfl
  · rw [rowAt_P_three] at h
    exact two_lt_three.ne' h
  · rw [rowAt_P_four] at h
    exact two_lt_three.ne h

private theorem selfZ_labelling {x y : ℕ} {c : Label.{u}} :
    ∀ z ∈ selfZ, min (labelling ((x : ℕ) : Label.{u}) ((y : ℕ) : Label.{u}) z) c = ⊥ := by
  intro z hz
  simp only [selfZ, mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl <;> simp [labelling]

/-- **The copy over the cap is not admitted when the marker is the cap**: it is in the bottom
class, and reads the other full cell at `2`, below its own value `3`. -/
theorem not_isAdmittedP_rowAt_self {β : Ordinal.{u}} (hC : C = 3 ∨ C = 4) :
    ¬ IsAdmittedP C C R ((P β).rowAt C) ((P β).rowAt C) := by
  intro h
  rcases hC with rfl | rfl
  · rw [rowAt_P_three] at h
    have hc := (isCapCorrectP_self_iff (by simp [labelling])).mp (h inBottomClassP_labelling)
    exact absurd (hc.2 4 (by simp [selfT])) (not_le.mpr two_lt_three)
  · rw [rowAt_P_four] at h
    have hc := (isCapCorrectP_self_iff (by simp [labelling])).mp (h inBottomClassP_labelling)
    exact absurd (hc.2 3 (by simp [selfT])) (not_le.mpr two_lt_three)

/-- **The copy over the cap is admitted when the marker is the other full cell**: the replaced
marker is `2`, at most every value of the row at the high cells. -/
theorem isAdmittedP_rowAt_self_of_ne {β : Ordinal.{u}} (hC : C = 3 ∨ C = 4)
    (ha : a = 3 ∨ a = 4) (haC : a ≠ C) :
    IsAdmittedP C a R ((P β).rowAt C) ((P β).rowAt C) := by
  intro _
  have hv : visibilityReplace 2 R ((2 : ℕ) : Label.{u}) = ((2 : ℕ) : Label.{u}) :=
    IsSelfVisible.visibilityReplace_eq (by simp) R
  have hle : ((2 : ℕ) : Label.{u}) ≤ (3 : ℕ) := two_lt_three.le
  rcases hC with rfl | rfl <;> rcases ha with rfl | rfl
  · exact absurd rfl haC
  · rw [rowAt_P_three]
    refine ⟨selfZ_labelling, fun y hy ↦ ?_⟩
    simp only [selfT, mem_insert, mem_singleton] at hy
    change min (visibilityReplace 2 R ((2 : ℕ) : Label.{u})) ((3 : ℕ) : Label.{u}) ≤
      min _ ((3 : ℕ) : Label.{u})
    rw [hv, min_eq_left hle]
    rcases hy with rfl | rfl
    · exact le_min hle hle
    · exact le_min le_rfl hle
  · rw [rowAt_P_four]
    refine ⟨selfZ_labelling, fun y hy ↦ ?_⟩
    simp only [selfT, mem_insert, mem_singleton] at hy
    change min (visibilityReplace 2 R ((2 : ℕ) : Label.{u})) ((3 : ℕ) : Label.{u}) ≤
      min _ ((3 : ℕ) : Label.{u})
    rw [hv, min_eq_left hle]
    rcases hy with rfl | rfl
    · exact le_min le_rfl hle
    · exact le_min hle hle
  · exact absurd rfl haC

/-- **The copy over the other full cell is admitted** for every marker and offset: its value at
the cap is `2`, and it reads both high cells at least at `2`. -/
theorem isAdmittedP_rowAt_other {β : Ordinal.{u}} {c : Fin 5} (hC : C = 3 ∨ C = 4)
    (hc : c = 3 ∨ c = 4) (hcC : c ≠ C) :
    IsAdmittedP C a R ((P β).rowAt c) ((P β).rowAt c) := by
  intro _
  have hle : ((2 : ℕ) : Label.{u}) ≤ (3 : ℕ) := two_lt_three.le
  rcases hC with rfl | rfl <;> rcases hc with rfl | rfl
  · exact absurd rfl hcC
  · rw [rowAt_P_four]
    refine isCapCorrectP_of_le selfZ_labelling fun y hy ↦ ?_
    simp only [selfT, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact le_rfl
    · exact hle
  · rw [rowAt_P_three]
    refine isCapCorrectP_of_le selfZ_labelling fun y hy ↦ ?_
    simp only [selfT, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hle
    · exact le_rfl
  · exact absurd rfl hcC

/-! ### Feasibility of an admitted reader at `P` -/

/-- **An admitted reader at `P`**, for the cap `3`: the state with private side `(⊥, ⊥, ⊥, 3, 2)`
and donor side `(⊥, ⊥, ⊥, 3, 3)` is lawful on each face, coded, agrees at the shared cell `0`, is
in the bottom class, is admitted for every marker and offset, and reads both high cells of the
donor exactly as the cap. -/
theorem exists_admitted_reader_P :
    ∃ sL sR : Fin 5 → Label.{u}, rows.{u}.IsLawful sL ∧ rows.{u}.IsLawful sR ∧ sL 0 = sR 0 ∧
      (∀ d, sL d < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) ∧
      (∀ d, sR d < ((ω ^ 2 : Ordinal.{u}) : Label.{u})) ∧ InBottomClassP sL ∧
      (∀ a R, IsAdmittedP 3 a R sL sR) ∧ sR 3 = sL 3 ∧ sR 4 = sL 3 := by
  have hR : rows.{u}.IsLawful fun d ↦ min (labelling (⊤ : Label.{u}) ⊤ d) ((3 : ℕ) : Label.{u}) :=
    isLawful_labelling_top_top.min_const_of_isSelfVisible (K := 2)
      (fun d ↦ by fin_cases d <;> decide) (by simp)
  have hRe : (fun d ↦ min (labelling (⊤ : Label.{u}) ⊤ d) ((3 : ℕ) : Label.{u})) =
      labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) := by
    funext d
    fin_cases d <;> simp [labelling]
  rw [hRe] at hR
  -- the values `2` and `3` are coded: they are values of the rows of `P`
  have h3 : ((3 : ℕ) : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
    isCoded_S.{u} (3 : Fin 5) ⟨(3 : Fin 5), by
      change (3 : Fin 5) ∈ cells.below (cells.gradedIndex 3)
      exact CellScheme.mem_below_gradedIndex _ _⟩
  have h2 : ((2 : ℕ) : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
    isCoded_S.{u} (3 : Fin 5) ⟨(4 : Fin 5), by
      change (4 : Fin 5) ∈ cells.below (cells.gradedIndex 3)
      rw [CellScheme.mem_below, gradedIndex_cells, gradedIndex_cells]; decide⟩
  have hbot : (⊥ : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := WithBot.bot_lt_coe _
  refine ⟨labelling (3 : ℕ) (2 : ℕ), labelling (3 : ℕ) (3 : ℕ), isLawful_labelling_three_two, hR,
    rfl, fun d ↦ ?_, fun d ↦ ?_, inBottomClassP_labelling, fun a R _ ↦ ?_, rfl, rfl⟩
  · fin_cases d <;> simp only [labelling] <;> first | exact hbot | exact h3 | exact h2
  · fin_cases d <;> simp only [labelling] <;> first | exact hbot | exact h3
  · refine isCapCorrectP_of_le selfZ_labelling fun y hy ↦ ?_
    simp only [selfT, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl <;> exact le_rfl

end GatedExtensionCounterexample

end VaughtConjecture
