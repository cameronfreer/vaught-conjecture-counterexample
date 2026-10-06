/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.MultiLayerStep
import VaughtConjecture.Extension.OrderedLayerTop
import VaughtConjecture.Extension.CrossedCouplingCounterexample

/-!
# The completed scheme of the crossed-coupling seed

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the multi-layer scheme of a seed whose coatom types are `TH` and `TG`, and its lawful
labellings); semantic contract, items 2–4.

Let `I` be a seed on five points whose coatom types are `TH` on `C = {0, 1, 2, 3}` and `TG` on
`D = {0, 1, 2, 4}` (`VaughtConjecture.Extension.CrossedCouplingTypes`), such as `seedHG`.

**Kinds.**  Each cell has a *kind* (`CellKind`): dead, `A_C` (the cells of grade `1` through the
point `3`), `A_D` (through the point `4`), `H`, `G`, or `top` (the cells of grade `4`).  On the old
cells it is read off the graded index (`kindOld`, which agrees with the kinds of `TH` along the
first coatom and of `TG` along the second: `kindOld_left`, `kindOld_right`).  The *labelling by
kinds* `kindLabel I A_C A_D H G Q` carries at each cell the value of its kind
(`CellKind.val`).  The grade of a cell is determined by its kind (`grade_of_cellKind`).

**The completed scheme** (`schemeHG I`): the multi-layer scheme
(`VaughtConjecture.Extension.MultiLayerStep`) with multiplicities `2, 1, 1, 1` (`multHG`).  Its
new cells are `cellAD` and `cellAC` at `(univ, 1)`, of kinds `A_D` and `A_C`, and `cellH`,
`cellG`, `cellT` at `(univ, 2)`, `(univ, 3)`, `(univ, 4)`.  Each new row is a labelling by kinds
(`rowsHG`):

* `cellAD` reads `A_C` at `1` and `A_D` at `ω + 2` (it reads `({3}, 1)` strictly below
  `({4}, 1)`), and `cellAC` the reverse: one cell for each of the two opposite forced separations
  of `CrossedCouplingCounterexample.exists_ne_seedHG`;
* `cellH` reads `A_C` and `H` at `ω + 2` and `A_D` at `1` (the row of the cell `15` of `TH` on the
  side of `C`, that of `TG` on the side of `D`);
* `cellG` reads `A_C` and `H` at `2` and `A_D` and `G` at `ω + 3` (the row of the cell `18` of
  `TH` on the side of `C`, that of `TG` on the side of `D`);
* `cellT` reads the cells of grade `4` at `ω + 4`.

**Lawful labellings by kinds** (`isLawful_kindLabel`).  For parameters `A_C`, `A_D`, `H`, `G`
self-visible at `1`, `1`, `2`, `3` with the couplings of both types (`H ≤ A_C`,
`min A_C G ≤ H`, `G ≤ A_D`), the labelling by kinds with `⊥` at the grade `4` is lawful: on the
amalgam it is `lab` along each coatom (`isLawful_amalgam_kindOld`, from
`isLawfulBelow_coatom_four`); at `cellAD` the witness is the strip shifter of `A_C` up to `A_D`, at
`cellAC` that of `A_D` up to `A_C`, at `cellH` that of `A_D` up to `H` (as for the cell `15` of
`TG`), and at `cellG` the strip shifter `strip3 A_C` up to `G` (as for the cell `18` of `TH`, the
coupling `G ≤ A_D` covering the side of `D`).  The labelling of a label `Ω` alone at the cells of
grade `4` is lawful (`isLawful_kindLabel_omega`), since the seed has bottom apexes
(`hasBottomApexes_HG`).

**Reading lawful labellings.**  Below `(C, k)` and `(D, k)`, `k ≤ 3`, the lawful labellings are
labellings by kinds with parameters coupled as in `TH` and `TG` (`exists_of_isLawfulBelow_C`,
`exists_of_isLawfulBelow_D`, from `exists_lab_of_comap`).  No cell below `(C, k)` has kind `A_D`
and no cell below `(D, k)` has kind `A_C` (`cellKind_ne_ad`, `cellKind_ne_ac`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.CrossedCouplingCounterexample

open Finset Label CellScheme OrderedLayer
open Ordinal hiding univ
open TwoFaceLiftCounterexample (cellScope cellGrade cells v1 v2 gradedIndex_cells stripShifter
  isWitness_stripShifter isWitness_stripShifter_one stripShifter_v1 stripShifter_v2)
open TwoFaceLiftExistsCounterexample (strip3 isWitness_strip3)

/-! ### Kinds of cells on five points -/

/-- The **kinds** of the cells of the completion: dead, the cells of grade `1` through the point
`3` (`ac`) or through the point `4` (`ad`), the cells of kind `H` and `G`, and the cells of grade
`4` (`top`). -/
inductive CellKind
  | dead
  | ac
  | ad
  | h
  | g
  | top
  deriving DecidableEq

/-- The value of a kind for the parameters `A_C`, `A_D`, `H`, `G` and the label `Q` of the cells
of grade `4`. -/
def CellKind.val (AC AD H G Q : Label.{u}) : CellKind → Label.{u}
  | .dead => ⊥
  | .ac => AC
  | .ad => AD
  | .h => H
  | .g => G
  | .top => Q

/-- The kind of a graded index of the amalgam on five points. -/
def kindOld (X : Finset (Fin 5) × ℕ) : CellKind :=
  if X.2 = 4 then .top
  else if kindC X = 1 then .ac
  else if kindD X = 1 then .ad
  else if kindC X = 2 ∨ kindD X = 2 then .h
  else if kindC X = 3 ∨ kindD X = 3 then .g
  else .dead

/-- The kind of a cell of `TH` read along the first coatom. -/
def leftKind : Fin 4 → CellKind := ![.dead, .ac, .h, .g]

/-- The kind of a cell of `TG` read along the second coatom. -/
def rightKind : Fin 4 → CellKind := ![.dead, .ad, .h, .g]

/-- The kind of a graded index of the first coatom is the kind of its cell. -/
theorem kindOld_left : ∀ c : Fin 19,
    kindOld (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex c)) =
      leftKind (kind c) := by
  decide +kernel

/-- The kind of a graded index of the second coatom is the kind of its cell. -/
theorem kindOld_right : ∀ c : Fin 19,
    kindOld (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c)) =
      rightKind (kind c) := by
  decide +kernel

/-- The value of the kind of a cell of `TH` is `lab`. -/
theorem val_leftKind (AC AD H G Q : Label.{u}) (c : Fin 19) :
    (leftKind (kind c)).val AC AD H G Q = lab AC H G c := by
  unfold lab
  generalize kind c = κ
  fin_cases κ <;> rfl

/-- The value of the kind of a cell of `TG` is `lab`. -/
theorem val_rightKind (AC AD H G Q : Label.{u}) (c : Fin 19) :
    (rightKind (kind c)).val AC AD H G Q = lab AD H G c := by
  unfold lab
  generalize kind c = κ
  fin_cases κ <;> rfl

/-- A graded index of kind `A` along the first coatom has grade `1` and contains the point `3`. -/
private theorem kindC_eq_one {X : Finset (Fin 5) × ℕ} (h : kindC X = 1) :
    X.2 = 1 ∧ (3 : Fin 5) ∈ X.1 := by
  unfold kindC at h
  split_ifs at h with h1 h2 h3
  · simp only [mem_insert, mem_singleton] at h1
    rcases h1 with rfl | rfl | rfl | rfl <;> decide
  all_goals exact absurd h (by decide)

/-- A graded index of kind `A` along the second coatom has grade `1` and contains the point
`4`. -/
private theorem kindD_eq_one {X : Finset (Fin 5) × ℕ} (h : kindD X = 1) :
    X.2 = 1 ∧ (4 : Fin 5) ∈ X.1 := by
  unfold kindD at h
  split_ifs at h with h1 h2 h3
  · simp only [mem_insert, mem_singleton] at h1
    rcases h1 with rfl | rfl | rfl | rfl <;> decide
  all_goals exact absurd h (by decide)

/-- A graded index of kind `H` along the first coatom has grade `2`. -/
private theorem kindC_eq_two {X : Finset (Fin 5) × ℕ} (h : kindC X = 2) : X.2 = 2 := by
  unfold kindC at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by decide)
  · simp only [mem_insert, mem_singleton] at h2
    rcases h2 with rfl | rfl <;> rfl
  all_goals exact absurd h (by decide)

/-- A graded index of kind `H` along the second coatom has grade `2`. -/
private theorem kindD_eq_two {X : Finset (Fin 5) × ℕ} (h : kindD X = 2) : X.2 = 2 := by
  unfold kindD at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by decide)
  · simp only [mem_insert, mem_singleton] at h2
    rcases h2 with rfl | rfl <;> rfl
  all_goals exact absurd h (by decide)

/-- A graded index of kind `G` along the first coatom has grade `3`. -/
private theorem kindC_eq_three {X : Finset (Fin 5) × ℕ} (h : kindC X = 3) : X.2 = 3 := by
  unfold kindC at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · simp only [mem_insert, mem_singleton] at h3
    rcases h3 with rfl | rfl <;> rfl
  · exact absurd h (by decide)

/-- A graded index of kind `G` along the second coatom has grade `3`. -/
private theorem kindD_eq_three {X : Finset (Fin 5) × ℕ} (h : kindD X = 3) : X.2 = 3 := by
  unfold kindD at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · simp only [mem_insert, mem_singleton] at h3
    rcases h3 with rfl | rfl <;> rfl
  · exact absurd h (by decide)

/-- The grades and points of the graded indices of each kind. -/
theorem kindOld_spec (X : Finset (Fin 5) × ℕ) :
    (kindOld X = .ac → X.2 = 1 ∧ (3 : Fin 5) ∈ X.1) ∧
      (kindOld X = .ad → X.2 = 1 ∧ (4 : Fin 5) ∈ X.1) ∧ (kindOld X = .h → X.2 = 2) ∧
      (kindOld X = .g → X.2 = 3) ∧ (kindOld X = .top ↔ X.2 = 4) := by
  unfold kindOld
  split_ifs with h4 h1 h2 h3 h5
  · simp [h4]
  · simp [kindC_eq_one h1]
  · simp [kindD_eq_one h2]
  · rcases h3 with h3 | h3
    · simp [kindC_eq_two h3]
    · simp [kindD_eq_two h3]
  · rcases h5 with h5 | h5
    · simp [kindC_eq_three h5]
    · simp [kindD_eq_three h5]
  · simp [h4]

/-! ### The cells of the completion -/

/-- The **multiplicities** of the completion: two new cells at `(univ, 1)`, one for each forced
separation, and one new cell at each of `(univ, 2)`, `(univ, 3)`, `(univ, 4)`. -/
def multHG : Fin 4 → ℕ := ![2, 1, 1, 1]

/-- The kinds of the new cells, in their order: the cell at `(univ, 1)` of kind `A_D`, the cell at
`(univ, 1)` of kind `A_C`, and the cells at `(univ, 2)`, `(univ, 3)`, `(univ, 4)`. -/
def newKind : ℕ → CellKind
  | 0 => .ad
  | 1 => .ac
  | 2 => .h
  | 3 => .g
  | _ => .top

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- The kind of a cell of the completion: an old cell by its graded index, a new cell by its
position. -/
def cellKind (z : Fin (multiCard I multHG)) : CellKind :=
  if h : (z : ℕ) < I.amalgam.card then kindOld (I.amalgam.toCellScheme.gradedIndex ⟨z, h⟩)
  else newKind (z - I.amalgam.card)

/-- The **labelling by kinds**: each cell carries the value of its kind. -/
def kindLabel (AC AD H G Q : Label.{u}) (z : Fin (multiCard I multHG)) : Label.{u} :=
  (cellKind I z).val AC AD H G Q

/-- The row value `ω + 4` at the cells of grade `4`. -/
noncomputable abbrev w4 : Label.{u} := gridPoint 4 1

/-- The **rows of the new cells**, each a labelling by kinds:

* the first cell at `(univ, 1)` (kind `A_D`) reads `A_C` at `1` and `A_D` at `ω + 2`;
* the second cell at `(univ, 1)` (kind `A_C`) reads `A_C` at `ω + 2` and `A_D` at `1`;
* the cell at `(univ, 2)` reads `A_C` and `H` at `ω + 2` and `A_D` at `1`;
* the cell at `(univ, 3)` reads `A_C` and `H` at `2` and `A_D` and `G` at `ω + 3`;
* the cell at `(univ, 4)` reads the cells of grade `4` at `ω + 4`. -/
noncomputable def rowsHG : MultiRows I multHG := fun k i z ↦
  match (k : ℕ), i with
  | 0, 0 => kindLabel I v1 v2 ⊥ ⊥ ⊥ z
  | 0, _ => kindLabel I v2 v1 ⊥ ⊥ ⊥ z
  | 1, _ => kindLabel I v2 v1 v2 ⊥ ⊥ z
  | 2, _ => kindLabel I w2 w3 w2 w3 ⊥ z
  | _, _ => kindLabel I ⊥ ⊥ ⊥ ⊥ w4 z

/-- The **completed scheme**: the amalgam with two new cells at `(univ, 1)` and one at each of
`(univ, 2)`, `(univ, 3)`, `(univ, 4)`. -/
noncomputable abbrev schemeHG : Scheme.{u} 5 := multiLayerScheme I multHG (rowsHG I)

/-- The first new cell at `(univ, 1)`, of kind `A_D`. -/
def cellAD : Fin (schemeHG I).card := multiNewCell I multHG 0 ⟨0, by decide⟩

/-- The second new cell at `(univ, 1)`, of kind `A_C`. -/
def cellAC : Fin (schemeHG I).card := multiNewCell I multHG 0 ⟨1, by decide⟩

/-- The new cell at `(univ, 2)`. -/
def cellH : Fin (schemeHG I).card := multiNewCell I multHG 1 ⟨0, by decide⟩

/-- The new cell at `(univ, 3)`. -/
def cellG : Fin (schemeHG I).card := multiNewCell I multHG 2 ⟨0, by decide⟩

/-- The new cell at `(univ, 4)`. -/
def cellT : Fin (schemeHG I).card := multiNewCell I multHG 3 ⟨0, by decide⟩

variable {I}

/-- The kind of an old cell is the kind of its graded index. -/
@[simp] theorem cellKind_multiOldCell (d : Fin I.amalgam.card) :
    cellKind I (multiOldCell I multHG d) = kindOld (I.amalgam.toCellScheme.gradedIndex d) := by
  exact dite_eq_left (show ((multiOldCell I multHG d : ℕ)) < I.amalgam.card from d.isLt)

/-- The new cells, by position. -/
private theorem multiNewCell_cases (k : Fin 4) (i : Fin (multHG k)) :
    multiNewCell I multHG k i = cellAD I ∨ multiNewCell I multHG k i = cellAC I ∨
      multiNewCell I multHG k i = cellH I ∨ multiNewCell I multHG k i = cellG I ∨
        multiNewCell I multHG k i = cellT I := by
  obtain ⟨i, hi⟩ := i
  fin_cases k
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by simp [multHG] at hi; omega
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · obtain rfl : i = 0 := by simp [multHG] at hi; omega
    exact .inr (.inr (.inl rfl))
  · obtain rfl : i = 0 := by simp [multHG] at hi; omega
    exact .inr (.inr (.inr (.inl rfl)))
  · obtain rfl : i = 0 := by simp [multHG] at hi; omega
    exact .inr (.inr (.inr (.inr rfl)))

/-- The kind of a new cell is read off its position. -/
private theorem cellKind_of_le {z : Fin (multiCard I multHG)} (h : I.amalgam.card ≤ z) :
    cellKind I z = newKind (z - I.amalgam.card) :=
  dite_eq_right (not_lt.mpr h)

/-- The position of the first new cell at `(univ, 1)`. -/
theorem val_cellAD : (cellAD I : ℕ) = I.amalgam.card + 0 := by simp [cellAD, multiNewCell]
/-- The position of the second new cell at `(univ, 1)`. -/
theorem val_cellAC : (cellAC I : ℕ) = I.amalgam.card + 1 := by simp [cellAC, multiNewCell]
/-- The position of the new cell at `(univ, 2)`. -/
theorem val_cellH : (cellH I : ℕ) = I.amalgam.card + 2 := by
  simp [cellH, multiNewCell, multHG]
/-- The position of the new cell at `(univ, 3)`. -/
theorem val_cellG : (cellG I : ℕ) = I.amalgam.card + 3 := by
  simp [cellG, multiNewCell, multHG]
/-- The position of the new cell at `(univ, 4)`. -/
theorem val_cellT : (cellT I : ℕ) = I.amalgam.card + 4 := by
  simp [cellT, multiNewCell, multHG]

/-- The kind of the first new cell at `(univ, 1)`. -/
@[simp] theorem cellKind_cellAD : cellKind I (cellAD I) = .ad := by
  rw [cellKind_of_le (by rw [val_cellAD]; omega), val_cellAD, Nat.add_sub_cancel_left]; rfl

/-- The kind of the second new cell at `(univ, 1)`. -/
@[simp] theorem cellKind_cellAC : cellKind I (cellAC I) = .ac := by
  rw [cellKind_of_le (by rw [val_cellAC]; omega), val_cellAC, Nat.add_sub_cancel_left]; rfl

/-- The kind of the new cell at `(univ, 2)`. -/
@[simp] theorem cellKind_cellH : cellKind I (cellH I) = .h := by
  rw [cellKind_of_le (by rw [val_cellH]; omega), val_cellH, Nat.add_sub_cancel_left]; rfl

/-- The kind of the new cell at `(univ, 3)`. -/
@[simp] theorem cellKind_cellG : cellKind I (cellG I) = .g := by
  rw [cellKind_of_le (by rw [val_cellG]; omega), val_cellG, Nat.add_sub_cancel_left]; rfl

/-- The kind of the new cell at `(univ, 4)`. -/
@[simp] theorem cellKind_cellT : cellKind I (cellT I) = .top := by
  rw [cellKind_of_le (by rw [val_cellT]; omega), val_cellT, Nat.add_sub_cancel_left]; rfl

/-! ### Grades and rows of the cells of the completion -/

/-- The graded index of the first new cell at `(univ, 1)`. -/
@[simp] theorem gradedIndex_cellAD :
    (schemeHG I).toCellScheme.gradedIndex (cellAD I) = ((univ : Finset (Fin 5)), 1) :=
  gradedIndex_multiNewCell (r := rowsHG I) 0 _

/-- The graded index of the second new cell at `(univ, 1)`. -/
@[simp] theorem gradedIndex_cellAC :
    (schemeHG I).toCellScheme.gradedIndex (cellAC I) = ((univ : Finset (Fin 5)), 1) :=
  gradedIndex_multiNewCell (r := rowsHG I) 0 _

/-- The graded index of the new cell at `(univ, 2)`. -/
@[simp] theorem gradedIndex_cellH :
    (schemeHG I).toCellScheme.gradedIndex (cellH I) = ((univ : Finset (Fin 5)), 2) :=
  gradedIndex_multiNewCell (r := rowsHG I) 1 _

/-- The graded index of the new cell at `(univ, 3)`. -/
@[simp] theorem gradedIndex_cellG :
    (schemeHG I).toCellScheme.gradedIndex (cellG I) = ((univ : Finset (Fin 5)), 3) :=
  gradedIndex_multiNewCell (r := rowsHG I) 2 _

/-- The graded index of the new cell at `(univ, 4)`. -/
@[simp] theorem gradedIndex_cellT :
    (schemeHG I).toCellScheme.gradedIndex (cellT I) = ((univ : Finset (Fin 5)), 4) :=
  gradedIndex_multiNewCell (r := rowsHG I) 3 _

/-- The grade of the first new cell at `(univ, 1)`. -/
@[simp] theorem grade_cellAD : (schemeHG I).toCellScheme.grade (cellAD I) = 1 :=
  congrArg Prod.snd gradedIndex_cellAD

/-- The grade of the second new cell at `(univ, 1)`. -/
@[simp] theorem grade_cellAC : (schemeHG I).toCellScheme.grade (cellAC I) = 1 :=
  congrArg Prod.snd gradedIndex_cellAC

/-- The grade of the new cell at `(univ, 2)`. -/
@[simp] theorem grade_cellH : (schemeHG I).toCellScheme.grade (cellH I) = 2 :=
  congrArg Prod.snd gradedIndex_cellH

/-- The grade of the new cell at `(univ, 3)`. -/
@[simp] theorem grade_cellG : (schemeHG I).toCellScheme.grade (cellG I) = 3 :=
  congrArg Prod.snd gradedIndex_cellG

/-- The grade of the new cell at `(univ, 4)`. -/
@[simp] theorem grade_cellT : (schemeHG I).toCellScheme.grade (cellT I) = 4 :=
  congrArg Prod.snd gradedIndex_cellT

/-- The scope of the first new cell at `(univ, 1)` is the ground set. -/
@[simp] theorem scope_cellAD : (schemeHG I).toCellScheme.scope (cellAD I) = univ :=
  congrArg Prod.fst gradedIndex_cellAD

/-- The scope of the second new cell at `(univ, 1)` is the ground set. -/
@[simp] theorem scope_cellAC : (schemeHG I).toCellScheme.scope (cellAC I) = univ :=
  congrArg Prod.fst gradedIndex_cellAC

/-- The scope of the new cell at `(univ, 2)` is the ground set. -/
@[simp] theorem scope_cellH : (schemeHG I).toCellScheme.scope (cellH I) = univ :=
  congrArg Prod.fst gradedIndex_cellH

/-- The scope of the new cell at `(univ, 3)` is the ground set. -/
@[simp] theorem scope_cellG : (schemeHG I).toCellScheme.scope (cellG I) = univ :=
  congrArg Prod.fst gradedIndex_cellG

/-- The scope of the new cell at `(univ, 4)` is the ground set. -/
@[simp] theorem scope_cellT : (schemeHG I).toCellScheme.scope (cellT I) = univ :=
  congrArg Prod.fst gradedIndex_cellT

/-- The row of the first new cell at `(univ, 1)`. -/
theorem row_cellAD (t : (schemeHG I).toCellScheme.below
    ((schemeHG I).toCellScheme.gradedIndex (cellAD I))) :
    (schemeHG I).rows.row (cellAD I) t = kindLabel I v1 v2 ⊥ ⊥ ⊥ t.1 :=
  row_multiNewCell (r := rowsHG I) 0 _ t

/-- The row of the second new cell at `(univ, 1)`. -/
theorem row_cellAC (t : (schemeHG I).toCellScheme.below
    ((schemeHG I).toCellScheme.gradedIndex (cellAC I))) :
    (schemeHG I).rows.row (cellAC I) t = kindLabel I v2 v1 ⊥ ⊥ ⊥ t.1 :=
  row_multiNewCell (r := rowsHG I) 0 _ t

/-- The row of the new cell at `(univ, 2)`. -/
theorem row_cellH (t : (schemeHG I).toCellScheme.below
    ((schemeHG I).toCellScheme.gradedIndex (cellH I))) :
    (schemeHG I).rows.row (cellH I) t = kindLabel I v2 v1 v2 ⊥ ⊥ t.1 :=
  row_multiNewCell (r := rowsHG I) 1 _ t

/-- The row of the new cell at `(univ, 3)`. -/
theorem row_cellG (t : (schemeHG I).toCellScheme.below
    ((schemeHG I).toCellScheme.gradedIndex (cellG I))) :
    (schemeHG I).rows.row (cellG I) t = kindLabel I w2 w3 w2 w3 ⊥ t.1 :=
  row_multiNewCell (r := rowsHG I) 2 _ t

/-- The row of the new cell at `(univ, 4)`. -/
theorem row_cellT (t : (schemeHG I).toCellScheme.below
    ((schemeHG I).toCellScheme.gradedIndex (cellT I))) :
    (schemeHG I).rows.row (cellT I) t = kindLabel I ⊥ ⊥ ⊥ ⊥ w4 t.1 :=
  row_multiNewCell (r := rowsHG I) 3 _ t

/-- Every cell of the completion is old or one of the five new cells. -/
theorem cell_casesHG (z : Fin (schemeHG I).card) :
    (∃ d, z = multiOldCell I multHG d) ∨ z = cellAD I ∨ z = cellAC I ∨ z = cellH I ∨
      z = cellG I ∨ z = cellT I := by
  rcases multiCell_cases (r := rowsHG I) z with h | ⟨k, i, rfl⟩
  · exact .inl h
  · exact .inr (multiNewCell_cases k i)

/-- **The grade of a cell is that of its kind.** -/
theorem grade_of_cellKind (z : Fin (schemeHG I).card) :
    (cellKind I z = .ac → (schemeHG I).toCellScheme.grade z = 1) ∧
      (cellKind I z = .ad → (schemeHG I).toCellScheme.grade z = 1) ∧
      (cellKind I z = .h → (schemeHG I).toCellScheme.grade z = 2) ∧
      (cellKind I z = .g → (schemeHG I).toCellScheme.grade z = 3) ∧
      (cellKind I z = .top ↔ (schemeHG I).toCellScheme.grade z = 4) := by
  rcases cell_casesHG z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · rw [cellKind_multiOldCell, grade_multiOldCell]
    obtain ⟨h1, h2, h3, h4, h5⟩ := kindOld_spec (I.amalgam.toCellScheme.gradedIndex d)
    exact ⟨fun h ↦ (h1 h).1, fun h ↦ (h2 h).1, h3, h4, h5⟩
  · rw [cellKind_cellAD, grade_cellAD]; decide
  · rw [cellKind_cellAC, grade_cellAC]; decide
  · rw [cellKind_cellH, grade_cellH]; decide
  · rw [cellKind_cellG, grade_cellG]; decide
  · rw [cellKind_cellT, grade_cellT]; decide

/-- A labelling by kinds at the first new cell at `(univ, 1)` is the value of its kind. -/
@[simp] theorem kindLabel_cellAD (AC AD H G Q : Label.{u}) :
    kindLabel I AC AD H G Q (cellAD I) = AD := by simp [kindLabel, CellKind.val]

/-- A labelling by kinds at the second new cell at `(univ, 1)` is the value of its kind. -/
@[simp] theorem kindLabel_cellAC (AC AD H G Q : Label.{u}) :
    kindLabel I AC AD H G Q (cellAC I) = AC := by simp [kindLabel, CellKind.val]

/-- A labelling by kinds at the new cell at `(univ, 2)` is the value of its kind. -/
@[simp] theorem kindLabel_cellH (AC AD H G Q : Label.{u}) :
    kindLabel I AC AD H G Q (cellH I) = H := by simp [kindLabel, CellKind.val]

/-- A labelling by kinds at the new cell at `(univ, 3)` is the value of its kind. -/
@[simp] theorem kindLabel_cellG (AC AD H G Q : Label.{u}) :
    kindLabel I AC AD H G Q (cellG I) = G := by simp [kindLabel, CellKind.val]

/-- A labelling by kinds at the new cell at `(univ, 4)` is the value of its kind. -/
@[simp] theorem kindLabel_cellT (AC AD H G Q : Label.{u}) :
    kindLabel I AC AD H G Q (cellT I) = Q := by simp [kindLabel, CellKind.val]

/-! ### Lawful labellings by kinds -/

variable {b : Bool} {A H G : Label.{u}}

/-- The labelling `lab A H G` of the nineteen cells, with `⊥` at the apex. -/
noncomputable def labApex (A H G : Label.{u}) : Fin 20 → Label.{u} :=
  Fin.snoc (α := fun _ ↦ Label.{u}) (lab A H G) ⊥

/-- The labelling `labApex` is `⊥` at the apex. -/
private theorem labApex_last : labApex A H G (Fin.last 19) = ⊥ :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

/-- The labelling `labApex` is `lab` at the nineteen cells. -/
private theorem labApex_castSucc (c : Fin 19) : labApex A H G c.castSucc = lab A H G c :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

/-- The labelling `lab A H G` with `⊥` at the apex is lawful for the type `crossType b`. -/
theorem isLawful_crossType_lab (hA : IsSelfVisible 1 A) (hH : IsSelfVisible 2 H)
    (hG : IsSelfVisible 3 G) (hc : Coupled b A H G) :
    (crossType b α).rows.IsLawful (labApex A H G) := by
  refine Scheme.isLawful_appendFullCell (S := (crossType₀ b α).toScheme) (j := 4)
    (r := StageType.apexRow isLegalBelowFullGrade_S) (h := isLegalBelowFullGrade_S.not_le)
    (v := labApex A H G) ?_ ?_ ?_ ?_
  · -- The old cells of the type are the nineteen cells, with the rows of `S b`.
    change (rows b).IsLawful fun d : Fin 19 ↦ labApex A H G d.castSucc
    simp only [labApex_castSucc]
    exact isLawful_lab hA hH hG hc
  · -- The apex is the last of the twenty cells.
    change IsSelfVisible 4 (labApex A H G (Fin.last 19))
    rw [labApex_last]; exact isSelfVisible_bot _
  · -- The target of the row of the apex, capped at its label `⊥`.
    change TransformsTo _ _ fun d : Fin 20 ↦ min (labApex A H G d) (labApex A H G (Fin.last 19))
    simp only [labApex_last, min_bot_right]
    exact TransformsTo.bot _ _
  · intro d hd
    exact absurd hd (isLegalBelowFullGrade_S.grade_lt d).ne

/-- A labelling of graded indices whose reading along `f` is `lab A H G`, and `⊥` at the apex, is
lawful below the coatom `univ.map f` at the grade `4`, for a stage type whose face along `f` is
`crossType b`. -/
theorem isLawfulBelow_coatom_four (hA : IsSelfVisible 1 A) (hH : IsSelfVisible 2 H)
    (hG : IsSelfVisible 3 G) (hc : Coupled b A H G) {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (crossType b α))
    {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (cells.gradedIndex d)) = lab A H G d)
    (hL4 : Lf (univ.map f, 4) = ⊥) :
    Am.rows.IsLawfulBelow (univ.map f, 4) (fun d ↦ Lf (Am.toCellScheme.gradedIndex d)) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (crossType b α).toScheme := congrArg StageType.toScheme he
  have hlaw : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (∀ i, x i = Lf (Prod.map (Finset.map f) id
        ((Am.toScheme.comap f).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 4) (fun i ↦ x i) := by
    rw [heq]
    intro x hx
    convert (isLawful_crossType_lab hA hH hG hc).isLawfulBelow ((univ : Finset (Fin 4)), 4)
      using 1
    funext d
    refine (hx _).trans ?_
    rcases cases_crossType (α := α) (b := b) d.1 with h | ⟨c, h⟩
    · rw [h, gradedIndex_crossType_last]
      exact hL4.trans labApex_last.symm
    · rw [h]
      exact (congrArg (fun X ↦ Lf (Prod.map (Finset.map f) id X))
        (gradedIndex_crossType_castSucc c)).trans ((hL c).trans (labApex_castSucc c).symm)
  exact (Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 4)), 4)
    fun d ↦ Lf (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg Lf (Am.toScheme.map_comap_gradedIndex f i).symm)

variable (hIL : I.left = TH α) (hIR : I.right = TG α)
include hIL hIR

/-- **The labelling by kinds is lawful on the amalgam**, for parameters coupled as in `TH` and
`TG`, with `⊥` at the apexes. -/
theorem isLawful_amalgam_kindOld {AC AD : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hAD : IsSelfVisible 1 AD) (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G)
    (hTH : Coupled true AC H G) (hTG : Coupled false AD H G) :
    I.amalgam.rows.IsLawful fun d ↦
      (kindOld (I.amalgam.toCellScheme.gradedIndex d)).val AC AD H G ⊥ := by
  have hC := isLawfulBelow_coatom_four hAC hH hG hTH (hIL ▸ I.restrictFace_left)
    (Lf := fun X ↦ (kindOld X).val AC AD H G ⊥)
    (fun c ↦ (congrArg (CellKind.val AC AD H G ⊥) (kindOld_left c)).trans (val_leftKind ..))
    (by simp [kindOld, CellKind.val])
  have hD := isLawfulBelow_coatom_four hAD hH hG hTG (hIR ▸ I.restrictFace_right)
    (Lf := fun X ↦ (kindOld X).val AC AD H G ⊥)
    (fun c ↦ (congrArg (CellKind.val AC AD H G ⊥) (kindOld_right c)).trans
      (val_rightKind ..)) (by simp [kindOld, CellKind.val])
  have hmem (d : Fin I.amalgam.card) :
      d ∈ I.amalgam.toCellScheme.below ((univ : Finset (Fin 5)), 4) :=
    ⟨subset_univ _, Nat.lt_succ_iff.mp (I.grade_lt d)⟩
  refine (Rows.IsLawfulBelow.glue (w := fun d ↦
    (kindOld (I.amalgam.toCellScheme.gradedIndex d)).val AC AD H G ⊥) hC hD fun d hd ↦ ?_).isLawful
    hmem
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d) with h | h
  · exact .inl ⟨by rw [← coatomC_eq]; exact h, hd.2⟩
  · exact .inr ⟨by rw [← coatomD_eq]; exact h, hd.2⟩


omit hIL hIR in
/-- A labelling by kinds is self-visible at the grade of each cell. -/
theorem isSelfVisible_kindLabel {AC AD Q : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hAD : IsSelfVisible 1 AD) (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G)
    (hQ : IsSelfVisible 4 Q) (z : Fin (schemeHG I).card) :
    IsSelfVisible ((schemeHG I).toCellScheme.grade z) (kindLabel I AC AD H G Q z) := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_cellKind z
  cases hk : cellKind I z with
  | dead => simp only [kindLabel, hk, CellKind.val]; exact isSelfVisible_bot _
  | ac => simp only [kindLabel, hk, CellKind.val]; rw [g1 hk]; exact hAC
  | ad => simp only [kindLabel, hk, CellKind.val]; rw [g2 hk]; exact hAD
  | h => simp only [kindLabel, hk, CellKind.val]; rw [g3 hk]; exact hH
  | g => simp only [kindLabel, hk, CellKind.val]; rw [g4 hk]; exact hG
  | top => simp only [kindLabel, hk, CellKind.val]; rw [g5.mp hk]; exact hQ

omit hIL hIR in
/-- **A row by kinds transforms to a labelling by kinds capped at `x`** when the witness does so
kind by kind, at the grade of each kind present below the cell. -/
theorem transformsTo_kindLabel {u : Fin (schemeHG I).card} {j : ℕ}
    (hu : (schemeHG I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), j))
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    {RAC RAD RH RG RQ AC AD Q x : Label.{u}}
    (hac : 1 ≤ j → min AC x = min (σ RAC) (g 1)) (had : 1 ≤ j → min AD x = min (σ RAD) (g 1))
    (hh : 2 ≤ j → min H x = min (σ RH) (g 2)) (hg : 3 ≤ j → min G x = min (σ RG) (g 3))
    (htop : 4 ≤ j → min Q x = min (σ RQ) (g 4)) :
    TransformsTo (fun t : (schemeHG I).toCellScheme.below
        ((schemeHG I).toCellScheme.gradedIndex u) ↦ (schemeHG I).toCellScheme.grade t)
      (fun t ↦ kindLabel I RAC RAD RH RG RQ t.1)
      (fun t ↦ min (kindLabel I AC AD H G Q t.1) x) := by
  refine ⟨g, σ, hw, fun t ↦ ?_⟩
  have htj : (schemeHG I).toCellScheme.grade t.1 ≤ j :=
    (le_of_le_of_eq (t.2 : (schemeHG I).toCellScheme.gradedIndex t.1 ≤ _) hu).2
  obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_cellKind t.1
  cases hk : cellKind I t.1 with
  | dead => simp only [kindLabel, hk, CellKind.val, hw.map_bot, bot_le, min_eq_left]
  | ac =>
    simp only [kindLabel, hk, CellKind.val]; rw [g1 hk]; exact hac (by have := g1 hk; omega)
  | ad =>
    simp only [kindLabel, hk, CellKind.val]; rw [g2 hk]; exact had (by have := g2 hk; omega)
  | h =>
    simp only [kindLabel, hk, CellKind.val]; rw [g3 hk]; exact hh (by have := g3 hk; omega)
  | g =>
    simp only [kindLabel, hk, CellKind.val]; rw [g4 hk]; exact hg (by have := g4 hk; omega)
  | top =>
    simp only [kindLabel, hk, CellKind.val]; rw [g5.mp hk]
    exact htop (by have := g5.mp hk; omega)

/-- **The labelling by kinds is lawful** on the completed scheme, for parameters self-visible at
`1`, `1`, `2`, `3` and coupled as in `TH` and `TG`, with `⊥` at the cells of grade `4`. -/
theorem isLawful_kindLabel {AC AD : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hAD : IsSelfVisible 1 AD) (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G)
    (hTH : Coupled true AC H G) (hTG : Coupled false AD H G) :
    (schemeHG I).rows.IsLawful (kindLabel I AC AD H G ⊥) := by
  obtain ⟨h1, h2⟩ : H ≤ AC ∧ min AC G ≤ H := by simpa [Coupled] using hTH
  have hGA : G ≤ AD := by simpa [Coupled] using hTG
  refine isLawful_multiLayerScheme_of ?_ (fun k i ↦ ?_) (fun k i ↦ ?_) (fun s k hs ↦ ?_)
  · have : (fun d ↦ kindLabel I AC AD H G ⊥ (multiOldCell I multHG d)) =
        fun d ↦ (kindOld (I.amalgam.toCellScheme.gradedIndex d)).val AC AD H G ⊥ :=
      funext fun d ↦ by rw [kindLabel, cellKind_multiOldCell]
    rw [this]
    exact isLawful_amalgam_kindOld hIL hIR hAC hAD hH hG hTH hTG
  · have := isSelfVisible_kindLabel hAC hAD hH hG (isSelfVisible_bot 4)
      (multiNewCell I multHG k i)
    rwa [grade_multiNewCell] at this
  · obtain ⟨i, hi⟩ := i
    fin_cases k
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by simp [multHG] at hi; omega
      · -- The cell of kind `A_D` at `(univ, 1)`: the strip shifter of `A_C`, up to `A_D`.
        refine transformsTo_kindLabel (j := 1) (gradedIndex_multiNewCell _ _)
          (isWitness_stripShifter_one (A := AC) hAD) (fun _ ↦ ?_) (fun _ ↦ ?_)
          (by omega) (by omega) (by omega)
        · -- The value of `cellAD` is the parameter of its kind.
          change min AC (kindLabel I AC AD H G ⊥ (cellAD I)) = _
          rw [kindLabel_cellAD, stripShifter_v1 hAC, constStepSuppressor_of_le _ le_rfl]
        · -- The value of `cellAD` is the parameter of its kind.
          change min AD (kindLabel I AC AD H G ⊥ (cellAD I)) = _
          rw [kindLabel_cellAD, stripShifter_v2, constStepSuppressor_of_le _ le_rfl, min_top_left,
            min_self]
      · -- The cell of kind `A_C` at `(univ, 1)`: the strip shifter of `A_D`, up to `A_C`.
        refine transformsTo_kindLabel (j := 1) (gradedIndex_multiNewCell _ _)
          (isWitness_stripShifter_one (A := AD) hAC) (fun _ ↦ ?_) (fun _ ↦ ?_)
          (by omega) (by omega) (by omega)
        · -- The value of `cellAC` is the parameter of its kind.
          change min AC (kindLabel I AC AD H G ⊥ (cellAC I)) = _
          rw [kindLabel_cellAC, stripShifter_v2, constStepSuppressor_of_le _ le_rfl, min_top_left,
            min_self]
        · -- The value of `cellAC` is the parameter of its kind.
          change min AD (kindLabel I AC AD H G ⊥ (cellAC I)) = _
          rw [kindLabel_cellAC, stripShifter_v1 hAD, constStepSuppressor_of_le _ le_rfl]
    · obtain rfl : i = 0 := by simp [multHG] at hi; omega
      -- The cell at `(univ, 2)`: the strip shifter of `A_D`, up to `H`.
      refine transformsTo_kindLabel (j := 2) (gradedIndex_multiNewCell _ _)
        (isWitness_stripShifter (A := AD) hH) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ ↦ ?_)
        (by omega) (by omega)
      · -- The value of `cellH` is the parameter of its kind.
        change min AC (kindLabel I AC AD H G ⊥ (cellH I)) = _
        rw [kindLabel_cellH, stripShifter_v2, constStepSuppressor_of_le _ (by omega), min_top_left,
          min_eq_right h1]
      · -- The value of `cellH` is the parameter of its kind.
        change min AD (kindLabel I AC AD H G ⊥ (cellH I)) = _
        rw [kindLabel_cellH, stripShifter_v1 hAD, constStepSuppressor_of_le _ (by omega)]
      · -- The value of `cellH` is the parameter of its kind.
        change min H (kindLabel I AC AD H G ⊥ (cellH I)) = _
        rw [kindLabel_cellH, stripShifter_v2, constStepSuppressor_of_le _ le_rfl, min_top_left,
          min_self]
    · obtain rfl : i = 0 := by simp [multHG] at hi; omega
      -- The cell at `(univ, 3)`: the strip shifter `strip3 A_C`, up to `G`.
      refine transformsTo_kindLabel (j := 3) (gradedIndex_multiNewCell _ _)
        (isWitness_strip3 (A := AC) hG) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ ↦ ?_)
        (by omega)
      · -- The value of `cellG` is the parameter of its kind.
        change min AC (kindLabel I AC AD H G ⊥ (cellG I)) = _
        rw [kindLabel_cellG, strip3_w2, constStepSuppressor_of_le _ (by omega)]
        exact min_visibilityReplace_A hH h1 h2
      · -- The value of `cellG` is the parameter of its kind.
        change min AD (kindLabel I AC AD H G ⊥ (cellG I)) = _
        rw [kindLabel_cellG, strip3_w3, constStepSuppressor_of_le _ (by omega), min_top_left,
          min_eq_right hGA]
      · -- The value of `cellG` is the parameter of its kind.
        change min H (kindLabel I AC AD H G ⊥ (cellG I)) = _
        rw [kindLabel_cellG, strip3_w2, constStepSuppressor_of_le _ (by omega)]
        exact min_visibilityReplace_H hH h1 h2
      · -- The value of `cellG` is the parameter of its kind.
        change min G (kindLabel I AC AD H G ⊥ (cellG I)) = _
        rw [kindLabel_cellG, strip3_w3, constStepSuppressor_of_le _ le_rfl, min_top_left, min_self]
    · obtain rfl : i = 0 := by simp [multHG] at hi; omega
      -- The cell at `(univ, 4)`: its label is `⊥`.
      rw [show multiNewCell I multHG _ ⟨0, hi⟩ = cellT I from rfl]
      simp only [kindLabel_cellT, min_bot_right]
      exact TransformsTo.bot _ _
  · -- Availability: every cell of grade `k + 1` is at most the new cell of its kind.
    obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_cellKind s
    cases hk : cellKind I s with
    | dead => exact ⟨⟨0, by fin_cases k <;> decide⟩, by simp [kindLabel, hk, CellKind.val]⟩
    | ac =>
      obtain rfl : k = 0 := Fin.ext (by have := (g1 hk).symm.trans hs; omega)
      exact ⟨⟨1, by decide⟩, by
        -- Both sides are values of kinds.
        change (cellKind I s).val AC AD H G ⊥ ≤ (cellKind I (cellAC I)).val AC AD H G ⊥
        rw [hk, cellKind_cellAC]⟩
    | ad =>
      obtain rfl : k = 0 := Fin.ext (by have := (g2 hk).symm.trans hs; omega)
      exact ⟨⟨0, by decide⟩, by
        -- Both sides are values of kinds.
        change (cellKind I s).val AC AD H G ⊥ ≤ (cellKind I (cellAD I)).val AC AD H G ⊥
        rw [hk, cellKind_cellAD]⟩
    | h =>
      obtain rfl : k = 1 := Fin.ext (by have := (g3 hk).symm.trans hs; omega)
      exact ⟨⟨0, by decide⟩, by
        -- Both sides are values of kinds.
        change (cellKind I s).val AC AD H G ⊥ ≤ (cellKind I (cellH I)).val AC AD H G ⊥
        rw [hk, cellKind_cellH]⟩
    | g =>
      obtain rfl : k = 2 := Fin.ext (by have := (g4 hk).symm.trans hs; omega)
      exact ⟨⟨0, by decide⟩, by
        -- Both sides are values of kinds.
        change (cellKind I s).val AC AD H G ⊥ ≤ (cellKind I (cellG I)).val AC AD H G ⊥
        rw [hk, cellKind_cellG]⟩
    | top => exact ⟨⟨0, by fin_cases k <;> decide⟩, by simp [kindLabel, hk, CellKind.val]⟩


/-- **A seed whose coatom types are `TH` and `TG` has bottom apexes.** -/
theorem hasBottomApexes_HG : I.HasBottomApexes :=
  Seed.hasBottomApexes_of_addApex isLegalBelowFullGrade_S isLegalBelowFullGrade_S
    (fun _ ↦ rfl) (fun _ ↦ rfl) hIL hIR

omit hIL hIR in
/-- The value of a kind with every parameter `⊥` and `Ω` at the grade `4`. -/
private theorem val_kindOld_omega (Ω : Label.{u}) (X : Finset (Fin 5) × ℕ) :
    (kindOld X).val ⊥ ⊥ ⊥ ⊥ Ω = if X.2 = 4 then Ω else ⊥ := by
  unfold kindOld
  split_ifs <;> rfl

/-- **The labelling of `Ω` alone is lawful**: `Ω` at the cells of grade `4` and `⊥` elsewhere, for
`Ω` self-visible at `4`; the rows of the cells of grade `4` are `⊥` exactly below the grade `4`. -/
theorem isLawful_kindLabel_omega {Ω : Label.{u}} (hΩ : IsSelfVisible 4 Ω) :
    (schemeHG I).rows.IsLawful (kindLabel I ⊥ ⊥ ⊥ ⊥ Ω) := by
  have hI := hasBottomApexes_HG hIL hIR
  refine isLawful_multiLayerScheme_of ?_ (fun k i ↦ ?_) (fun k i ↦ ?_) (fun s k hs ↦ ?_)
  · -- The amalgam: `Ω` at the apexes, `⊥` elsewhere.
    have hv : (fun d ↦ kindLabel I ⊥ ⊥ ⊥ ⊥ Ω (multiOldCell I multHG d)) =
        fun d ↦ if I.amalgam.toCellScheme.grade d = 4 then Ω else ⊥ :=
      funext fun d ↦ by rw [kindLabel, cellKind_multiOldCell, val_kindOld_omega]; rfl
    rw [hv]
    refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t _ hg ↦ ⟨t, rfl, by rw [hg]⟩⟩
    · split_ifs with h
      · rw [h]; exact hΩ
      · exact isSelfVisible_bot _
    · by_cases hs : I.amalgam.toCellScheme.grade s = 4
      · refine OrderedLayer.transformsTo_of_eq_bot_iff _ (K := 4)
          (fun d : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s) ↦
            Nat.lt_succ_iff.mp (I.grade_lt d.1)) hΩ _ _ fun d ↦ ?_
        rw [ite_eq_left hs]
        by_cases hd : I.amalgam.toCellScheme.grade d.1 = 4
        · rw [ite_eq_left hd, min_self, ite_eq_right fun h ↦ ((hI.row_apex hs d).mp h) hd]
        · rw [ite_eq_right hd, min_bot_left, ite_eq_left ((hI.row_apex hs d).mpr hd)]
      · simp only [ite_eq_right hs, min_bot_right]
        exact TransformsTo.bot _ _
  · have := isSelfVisible_kindLabel (I := I) (H := ⊥) (G := ⊥) (isSelfVisible_bot 1)
      (isSelfVisible_bot 1) (isSelfVisible_bot 2) (isSelfVisible_bot 3) hΩ
      (multiNewCell I multHG k i)
    rwa [grade_multiNewCell] at this
  · obtain ⟨i, hi⟩ := i
    fin_cases k
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by simp [multHG] at hi; omega
      · rw [show multiNewCell I multHG _ ⟨0, hi⟩ = cellAD I from rfl]
        simp only [kindLabel_cellAD, min_bot_right]
        exact TransformsTo.bot _ _
      · rw [show multiNewCell I multHG _ ⟨1, hi⟩ = cellAC I from rfl]
        simp only [kindLabel_cellAC, min_bot_right]
        exact TransformsTo.bot _ _
    · obtain rfl : i = 0 := by simp [multHG] at hi; omega
      rw [show multiNewCell I multHG _ ⟨0, hi⟩ = cellH I from rfl]
      simp only [kindLabel_cellH, min_bot_right]
      exact TransformsTo.bot _ _
    · obtain rfl : i = 0 := by simp [multHG] at hi; omega
      rw [show multiNewCell I multHG _ ⟨0, hi⟩ = cellG I from rfl]
      simp only [kindLabel_cellG, min_bot_right]
      exact TransformsTo.bot _ _
    · obtain rfl : i = 0 := by simp [multHG] at hi; omega
      -- The cell at `(univ, 4)`: the top shifter, up to `Ω`.
      refine transformsTo_kindLabel (j := 4) (gradedIndex_multiNewCell _ _)
        (isWitness_topShifter (antitone_constStepSuppressor 4 Ω)
          (isSelfVisible_constStepSuppressor hΩ)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ ↦ ?_)
        (fun _ ↦ ?_) (fun _ ↦ ?_)
      -- The value of the new cell at `(univ, 4)` is `Ω`.
      all_goals change min _ (kindLabel I ⊥ ⊥ ⊥ ⊥ Ω (cellT I)) = _
      all_goals rw [kindLabel_cellT]
      all_goals simp [topShifter, constStepSuppressor, w4, gridPoint_ne_bot]
  · cases hk : cellKind I s with
    | top =>
      obtain rfl : k = 3 := Fin.ext (by
        have := ((grade_of_cellKind s).2.2.2.2.mp hk).symm.trans hs; omega)
      exact ⟨⟨0, by decide⟩, by
        -- Both sides are values of kinds.
        change (cellKind I s).val ⊥ ⊥ ⊥ ⊥ Ω ≤ (cellKind I (cellT I)).val ⊥ ⊥ ⊥ ⊥ Ω
        rw [hk, cellKind_cellT]⟩
    | _ => exact ⟨⟨0, by fin_cases k <;> decide⟩, by simp [kindLabel, hk, CellKind.val]⟩


/-! ### Reading lawful labellings -/

omit hIL hIR in
/-- The cells at `(univ, 1)` are the two new cells of grade `1`. -/
theorem eq_cellAD_or_cellAC {u : Fin (schemeHG I).card}
    (hu : (schemeHG I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 1)) :
    u = cellAD I ∨ u = cellAC I := by
  rcases cell_casesHG u with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · exact absurd (congrArg Prod.fst ((gradedIndex_multiOldCell d).symm.trans hu))
      (I.scope_ne_univ d)
  · exact .inl rfl
  · exact .inr rfl
  · rw [gradedIndex_cellH] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellG] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellT] at hu; exact absurd (congrArg Prod.snd hu) (by decide)

omit hIL hIR in
/-- The cell at `(univ, 2)` is the new cell of grade `2`. -/
theorem eq_cellH {u : Fin (schemeHG I).card}
    (hu : (schemeHG I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 2)) :
    u = cellH I := by
  rcases cell_casesHG u with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · exact absurd (congrArg Prod.fst ((gradedIndex_multiOldCell d).symm.trans hu))
      (I.scope_ne_univ d)
  · rw [gradedIndex_cellAD] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellAC] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rfl
  · rw [gradedIndex_cellG] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellT] at hu; exact absurd (congrArg Prod.snd hu) (by decide)

omit hIL hIR in
/-- The cell at `(univ, 3)` is the new cell of grade `3`. -/
theorem eq_cellG {u : Fin (schemeHG I).card}
    (hu : (schemeHG I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 3)) :
    u = cellG I := by
  rcases cell_casesHG u with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · exact absurd (congrArg Prod.fst ((gradedIndex_multiOldCell d).symm.trans hu))
      (I.scope_ne_univ d)
  · rw [gradedIndex_cellAD] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellAC] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellH] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rfl
  · rw [gradedIndex_cellT] at hu; exact absurd (congrArg Prod.snd hu) (by decide)

omit hIL hIR in
/-- The cell at `(univ, 4)` is the new cell of grade `4`. -/
theorem eq_cellT {u : Fin (schemeHG I).card}
    (hu : (schemeHG I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 4)) :
    u = cellT I := by
  rcases cell_casesHG u with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · exact absurd (congrArg Prod.fst ((gradedIndex_multiOldCell d).symm.trans hu))
      (I.scope_ne_univ d)
  · rw [gradedIndex_cellAD] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellAC] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellH] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rw [gradedIndex_cellG] at hu; exact absurd (congrArg Prod.snd hu) (by decide)
  · rfl

omit hIL hIR in
/-- A cell whose graded index is below `(univ, k)` lies below every pair `(univ, j)` with
`k ≤ j`. -/
theorem mem_below_univ {z : Fin (schemeHG I).card} {k : ℕ}
    (h : (schemeHG I).toCellScheme.grade z ≤ k) :
    z ∈ (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), k) :=
  ⟨subset_univ _, h⟩

omit hIR in
/-- **Lawful labellings below `(C, k)`, `k ≤ 3`**, are labellings by kinds with parameters
coupled as in `TH`. -/
theorem exists_of_isLawfulBelow_C {k : ℕ} (hk : k ≤ 3) {p : Fin (schemeHG I).card → Label.{u}}
    (hp : (schemeHG I).rows.IsLawfulBelow (coatomC, k) fun z ↦ p z) :
    ∃ A H G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 H ∧ IsSelfVisible 3 G ∧
      Coupled true A H G ∧
      ∀ z ∈ (schemeHG I).toCellScheme.below (coatomC, k), p z = kindLabel I A ⊥ H G ⊥ z := by
  have hp' := (isLawfulBelow_multiOldCell_iff (by decide : coatomC ≠ univ)).mp hp
  rw [coatomC_eq] at hp'
  obtain ⟨A, H, G, hA, hH, hG, hc, hall⟩ :=
    exists_lab_of_comap (hIL ▸ I.restrictFace_left) hk (fun d ↦ p (multiOldCell I multHG d))
      hp'
  refine ⟨A, H, G, hA, hH, hG, hc, fun z hz ↦ ?_⟩
  obtain ⟨d, rfl⟩ := exists_eq_multiOldCell (r := rowsHG I) (z := z) fun h ↦
    (by decide : coatomC ≠ univ) (univ_subset_iff.mp (h ▸ hz.1))
  have hd : d ∈ I.amalgam.toCellScheme.below (univ.map (Coatom.left 3), k) := by
    rw [← coatomC_eq, CellScheme.mem_below, ← gradedIndex_multiOldCell (r := rowsHG I)]
    exact hz
  obtain ⟨c, hgc, hpc⟩ := hall d hd
  rw [hpc, kindLabel, cellKind_multiOldCell, hgc, kindOld_left, val_leftKind]

omit hIL in
/-- **Lawful labellings below `(D, k)`, `k ≤ 3`**, are labellings by kinds with parameters
coupled as in `TG`. -/
theorem exists_of_isLawfulBelow_D {k : ℕ} (hk : k ≤ 3) {p : Fin (schemeHG I).card → Label.{u}}
    (hp : (schemeHG I).rows.IsLawfulBelow (coatomD, k) fun z ↦ p z) :
    ∃ A H G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 H ∧ IsSelfVisible 3 G ∧
      Coupled false A H G ∧
      ∀ z ∈ (schemeHG I).toCellScheme.below (coatomD, k), p z = kindLabel I ⊥ A H G ⊥ z := by
  have hp' := (isLawfulBelow_multiOldCell_iff (by decide : coatomD ≠ univ)).mp hp
  rw [coatomD_eq] at hp'
  obtain ⟨A, H, G, hA, hH, hG, hc, hall⟩ :=
    exists_lab_of_comap (hIR ▸ I.restrictFace_right) hk (fun d ↦ p (multiOldCell I multHG d))
      hp'
  refine ⟨A, H, G, hA, hH, hG, hc, fun z hz ↦ ?_⟩
  obtain ⟨d, rfl⟩ := exists_eq_multiOldCell (r := rowsHG I) (z := z) fun h ↦
    (by decide : coatomD ≠ univ) (univ_subset_iff.mp (h ▸ hz.1))
  have hd : d ∈ I.amalgam.toCellScheme.below (univ.map (Coatom.right 3), k) := by
    rw [← coatomD_eq, CellScheme.mem_below, ← gradedIndex_multiOldCell (r := rowsHG I)]
    exact hz
  obtain ⟨c, hgc, hpc⟩ := hall d hd
  rw [hpc, kindLabel, cellKind_multiOldCell, hgc, kindOld_right, val_rightKind]

/-- The four cells of the amalgam that carry the parameters: `({3}, 1)`, `({4}, 1)`,
`({0, 1, 2}, 2)` and `({0, 1, 2}, 3)`. -/
theorem exists_paramCells : ∃ d₃ d₄ e₂ e₃ : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1) ∧
    I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1) ∧
    I.amalgam.toCellScheme.gradedIndex e₂ = (({0, 1, 2} : Finset (Fin 5)), 2) ∧
    I.amalgam.toCellScheme.gradedIndex e₃ = (({0, 1, 2} : Finset (Fin 5)), 3) := by
  obtain ⟨d₃, d₄, h₃, h₄⟩ := exists_cells hIL hIR
  obtain ⟨e₂, h₂⟩ := exists_cell (hIL ▸ I.restrictFace_left) 13
  obtain ⟨e₃, h₃'⟩ := exists_cell (hIL ▸ I.restrictFace_left) 16
  exact ⟨d₃, d₄, e₂, e₃, h₃, h₄, h₂.trans (by decide +kernel), h₃'.trans (by decide +kernel)⟩


omit hIL hIR in
/-- Two labellings by kinds agree at a cell when their parameters agree at its kind. -/
theorem kindLabel_congr {z : Fin (schemeHG I).card} {AC AD Q AC' AD' H' G' Q' : Label.{u}}
    (hac : cellKind I z = .ac → AC = AC') (had : cellKind I z = .ad → AD = AD')
    (hh : cellKind I z = .h → H = H') (hg : cellKind I z = .g → G = G')
    (htop : cellKind I z = .top → Q = Q') :
    kindLabel I AC AD H G Q z = kindLabel I AC' AD' H' G' Q' z := by
  cases hk : cellKind I z with
  | dead => simp only [kindLabel, hk, CellKind.val]
  | ac => simp only [kindLabel, hk, CellKind.val]; exact hac hk
  | ad => simp only [kindLabel, hk, CellKind.val]; exact had hk
  | h => simp only [kindLabel, hk, CellKind.val]; exact hh hk
  | g => simp only [kindLabel, hk, CellKind.val]; exact hg hk
  | top => simp only [kindLabel, hk, CellKind.val]; exact htop hk

omit hIL hIR in
/-- A cell below a coatom pair is old. -/
private theorem exists_eq_multiOldCell_of_mem_below {B : Finset (Fin 5)} (hB : B ≠ univ) {k : ℕ}
    {z : Fin (schemeHG I).card} (hz : z ∈ (schemeHG I).toCellScheme.below (B, k)) :
    ∃ d, z = multiOldCell I multHG d :=
  exists_eq_multiOldCell fun h ↦ hB (univ_subset_iff.mp (h ▸ hz.1))

omit hIL hIR in
/-- No cell below `(C, k)` has kind `A_D`. -/
theorem cellKind_ne_ad {k : ℕ} {z : Fin (schemeHG I).card}
    (hz : z ∈ (schemeHG I).toCellScheme.below (coatomC, k)) : cellKind I z ≠ .ad := by
  obtain ⟨d, rfl⟩ := exists_eq_multiOldCell_of_mem_below (by decide) hz
  intro h
  rw [cellKind_multiOldCell] at h
  have h4 := ((kindOld_spec _).2.1 h).2
  have hsub : I.amalgam.toCellScheme.scope d ⊆ coatomC := by
    have := hz.1; rwa [gradedIndex_multiOldCell] at this
  exact absurd (hsub h4) (by decide)

omit hIL hIR in
/-- No cell below `(D, k)` has kind `A_C`. -/
theorem cellKind_ne_ac {k : ℕ} {z : Fin (schemeHG I).card}
    (hz : z ∈ (schemeHG I).toCellScheme.below (coatomD, k)) : cellKind I z ≠ .ac := by
  obtain ⟨d, rfl⟩ := exists_eq_multiOldCell_of_mem_below (by decide) hz
  intro h
  rw [cellKind_multiOldCell] at h
  have h3 := ((kindOld_spec _).1 h).2
  have hsub : I.amalgam.toCellScheme.scope d ⊆ coatomD := by
    have := hz.1; rwa [gradedIndex_multiOldCell] at this
  exact absurd (hsub h3) (by decide)

end VaughtConjecture.CrossedCouplingCounterexample
