/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.Order
import VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample

/-!
# Two legal types on four points coupled crosswise to two parameters of a face

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the two coatom types of a seed with two opposite forcings, the input of the obstruction to the
ordered-layer step, `VaughtConjecture.Extension.OrderedLayerObstruction`); semantic contract,
items 2–4.

**The cells.**  Both types live on the nineteen cells of `TwoFaceLiftCounterexample.cells` (the
interval plan on four points, one cell at every graded face of grade at most `3`).  The cells have
four *kinds* (`kind`): the cells of grade `1` through the point `3` (the cells `3`, `6`, `8`, `9`,
kind `A`); the cells `({0, 1, 2}, 2)` and `(univ, 2)` (the cells `13` and `15`, kind `H`); the cells
`({0, 1, 2}, 3)` and `(univ, 3)` (the cells `16` and `18`, kind `G`); every other cell is dead.  The
labelling `lab A H G` carries the parameter of its kind at each live cell and `⊥` at the dead
cells.  On the face `{0, 1, 2}` the live cells are `13` (kind `H`) and `16` (kind `G`).

**The rows** (`rowVal b`, for `b = true` the type `TH` and `b = false` the type `TG`).  Dead cells
read `⊥`, and every cell reads the dead cells at `⊥`.  A cell of kind `A` reads the cells of kind
`A` at `1`; the cell `13` reads itself at `ω + 2`; the cell `16` reads `13` at `2` and itself at
`ω + 3` (through the strip shifter `strip3 H`, with no relation between `H` and `G`).  In `TH`,
the cell `15` reads all its live cells at `ω + 2` (forcing `H ≤ A`), and the cell `18` reads the
cells of kinds `A` and `H` at `2` and those of kind `G` at `ω + 3` (through `strip3 A`).  In `TG`,
the cell `15` reads the cells of kind `A` at `1` and those of kind `H` at `ω + 2` (as in `T4`), and
the cell `18` reads the cells of kind `H` at `2` and the others at `ω + 3` (forcing `G ≤ A`).

**The lawful labellings** (`isLawfulBelow_iff`).  Below every pair, the lawful labellings are the
restrictions of `lab A H G` with `A`, `H`, `G` self-visible at `1`, `2`, `3` and the coupling
`Coupled b A H G`: for `TH`, `H ≤ A` and `min A G ≤ H` (so `H` lies between `min A G` and `A`; in
particular `G` is free when `A = H`); for `TG`, `G ≤ A`.  So `TH` couples `A` to the parameter `H`
of the face and is free of `G` (`A = H = 2`, `G = ⊤` is lawful), and `TG` couples `A` to the
parameter `G` of the face and is free of `H` (`A = 2`, `H = ⊤`, `G = ⊥` is lawful).

**Legality** (`isLegal_TH`, `isLegal_TG`).  The rows are consistent, coded, and bountiful: every
pair lifts capped to every larger one (`cappedLift_all`).  The lift keeps the prescribed
parameters, keeps the ambient below the cap, and above the cap takes `⊤` or the cap; for `TH`, a
parameter `A` above the cap with `H` and `G` prescribed and `H < G` is set to `H`
(`liftParamsH`).  The types are the schemes with the apex added (`StageType.addApex`) to the
labels `⊥`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.CrossedCouplingCounterexample

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftCounterexample (cellScope cellGrade cells v1 v2 gradedIndex_cells
  gradedIndex_injective complete_below mem_below_of_le stripShifter isWitness_stripShifter
  stripShifter_bot stripShifter_v1 stripShifter_v2)
open TwoFaceLiftExistsCounterexample (strip3 strip3_natCast strip3_of_not_lt strip3_bot
  isWitness_strip3)

/-! ### The cells and their kinds -/

/-- The **kind** of a cell: `1` for the cells of grade `1` through the point `3`, `2` for the
cells `13` and `15`, `3` for the cells `16` and `18`, `0` (dead) otherwise. -/
def kind : Fin 19 → Fin 4 := ![0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 0, 2, 3, 0, 3]

/-- The row value `2`. -/
noncomputable abbrev w2 : Label.{u} := gridPoint 2 0

/-- The row value `ω + 3`. -/
noncomputable abbrev w3 : Label.{u} := gridPoint 3 1

/-- The labelling with `A`, `H`, `G` at the cells of kinds `A`, `H`, `G`, and `⊥` at the dead
cells. -/
noncomputable def lab (A H G : Label.{u}) (d : Fin 19) : Label.{u} := ![⊥, A, H, G] (kind d)

/-- The rows of the two types, `TH` for `b = true` and `TG` for `b = false`: they differ only at
the cells `15` and `18`. -/
noncomputable def rowVal (b : Bool) (s t : Fin 19) : Label.{u} :=
  if kind s = 0 ∨ kind t = 0 then ⊥
  else if s = 15 then (if b then v2 else if kind t = 1 then v1 else v2)
  else if s = 18 then
    (if b then (if kind t = 3 then w3 else w2) else (if kind t = 2 then w2 else w3))
  else if s = 16 then (if kind t = 2 then w2 else w3)
  else if s = 13 then v2
  else v1

/-- The rows of the type `TH` (`b = true`) or `TG` (`b = false`). -/
noncomputable def rows (b : Bool) : cells.Rows.{u} := ⟨fun s t ↦ rowVal b s t.1⟩

/-- The scheme on four points of the type `TH` (`b = true`) or `TG` (`b = false`). -/
noncomputable def S (b : Bool) : Scheme.{u} 4 := ⟨19, cells, rows b⟩

/-- The **coupling** of the parameters: for `TH`, `H ≤ A` and `min A G ≤ H`; for `TG`,
`G ≤ A`. -/
def Coupled (b : Bool) (A H G : Label.{u}) : Prop :=
  if b then H ≤ A ∧ min A G ≤ H else G ≤ A

/-! ### Facts on the nineteen cells -/

/-- Every cell is dead, of kind `A`, or one of the cells `13`, `15`, `16`, `18`. -/
theorem kind_cases : ∀ s : Fin 19,
    kind s = 0 ∨ kind s = 1 ∨ s = 13 ∨ s = 15 ∨ s = 16 ∨ s = 18 := by decide

/-- The cells of kind `A` have grade `1`. -/
theorem grade_of_kind_one : ∀ d : Fin 19, kind d = 1 → cellGrade d = 1 := by decide

/-- The cells of kind `H` are `13` and `15`. -/
theorem kind_two_cases : ∀ d : Fin 19, kind d = 2 → d = 13 ∨ d = 15 := by decide

/-- The cells of kind `G` are `16` and `18`. -/
theorem kind_three_cases : ∀ d : Fin 19, kind d = 3 → d = 16 ∨ d = 18 := by decide

/-- The four kinds. -/
theorem kind_live_cases : ∀ d : Fin 19, kind d = 0 ∨ kind d = 1 ∨ kind d = 2 ∨ kind d = 3 := by
  decide

/-- A live cell below a cell of kind `A` has kind `A`. -/
theorem kind_of_le_kind_one : ∀ s d : Fin 19, kind s = 1 → kind d ≠ 0 →
    cells.gradedIndex d ≤ cells.gradedIndex s → kind d = 1 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The only live cell below the cell `13` is `13`. -/
theorem eq_of_le_thirteen : ∀ d : Fin 19, kind d ≠ 0 →
    cells.gradedIndex d ≤ cells.gradedIndex 13 → d = 13 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The live cells below the cell `15` have kind `A` or `H`. -/
theorem kind_of_le_fifteen : ∀ d : Fin 19, kind d ≠ 0 →
    cells.gradedIndex d ≤ cells.gradedIndex 15 → kind d = 1 ∨ kind d = 2 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The live cells below the cell `16` are `13` and `16`. -/
theorem eq_of_le_sixteen : ∀ d : Fin 19, kind d ≠ 0 →
    cells.gradedIndex d ≤ cells.gradedIndex 16 → d = 13 ∨ d = 16 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The kinds are closed upward under inclusion of scopes at the same grade. -/
theorem kind_up : ∀ s t : Fin 19, kind s ≠ 0 → cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → kind t = kind s := by decide +kernel

/-- Every cell of kind `A` lies above the cell `3`, at `({3}, 1)`. -/
theorem three_le : ∀ d : Fin 19, kind d = 1 → cells.gradedIndex 3 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- Every cell of kind `H` lies above the cell `13`, at `({0, 1, 2}, 2)`. -/
theorem thirteen_le : ∀ d : Fin 19, kind d = 2 →
    cells.gradedIndex 13 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- Every cell of kind `G` lies above the cell `16`, at `({0, 1, 2}, 3)`. -/
theorem sixteen_le : ∀ d : Fin 19, kind d = 3 →
    cells.gradedIndex 16 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- A pair above the cells `3` and `13` is above the cell `15`. -/
theorem fifteen_mem_below {Y : Finset (Fin 4) × ℕ} (h3 : (3 : Fin 19) ∈ cells.below Y)
    (h13 : (13 : Fin 19) ∈ cells.below Y) : (15 : Fin 19) ∈ cells.below Y := by
  obtain ⟨B, k⟩ := Y
  have key : ∀ B : Finset (Fin 4), cellScope 3 ⊆ B → cellScope 13 ⊆ B →
      cellScope 15 ⊆ B := by decide +kernel
  exact ⟨key B h3.1 h13.1, h13.2⟩

/-- A pair above the cells `3` and `16` is above the cell `18`. -/
theorem eighteen_mem_below {Y : Finset (Fin 4) × ℕ} (h3 : (3 : Fin 19) ∈ cells.below Y)
    (h16 : (16 : Fin 19) ∈ cells.below Y) : (18 : Fin 19) ∈ cells.below Y := by
  obtain ⟨B, k⟩ := Y
  have key : ∀ B : Finset (Fin 4), cellScope 3 ⊆ B → cellScope 16 ⊆ B →
      cellScope 18 ⊆ B := by decide +kernel
  exact ⟨key B h3.1 h16.1, h16.2⟩

/-- A pair above the cell `16` is above the cell `13`. -/
theorem thirteen_mem_below {Y : Finset (Fin 4) × ℕ} (h16 : (16 : Fin 19) ∈ cells.below Y) :
    (13 : Fin 19) ∈ cells.below Y :=
  mem_below_of_le h16 (by simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel)

/-! ### The labelling and the rows, by kinds -/

variable {A H G : Label.{u}} {b : Bool}

/-- `lab` is `⊥` at the dead cells. -/
theorem lab_of_kind_zero {d : Fin 19} (h : kind d = 0) : lab A H G d = ⊥ := by
  simp [lab, h]

/-- `lab` is `A` at the cells of kind `A`. -/
theorem lab_of_kind_one {d : Fin 19} (h : kind d = 1) : lab A H G d = A := by
  simp [lab, h]

/-- `lab` is `H` at the cells of kind `H`. -/
theorem lab_of_kind_two {d : Fin 19} (h : kind d = 2) : lab A H G d = H := by
  simp [lab, h]

/-- `lab` is `G` at the cells of kind `G`. -/
theorem lab_of_kind_three {d : Fin 19} (h : kind d = 3) : lab A H G d = G := by
  simp [lab, h]

/-- The row of a dead cell is `⊥`. -/
theorem rowVal_of_kind_zero_left {s t : Fin 19} (h : kind s = 0) : rowVal.{u} b s t = ⊥ := by
  simp [rowVal, h]

/-- Every row reads the dead cells at `⊥`. -/
theorem rowVal_of_kind_zero_right {s t : Fin 19} (h : kind t = 0) : rowVal.{u} b s t = ⊥ := by
  simp [rowVal, h]

/-- A cell of kind `A` reads its live cells at `1`. -/
theorem rowVal_of_kind_one {s t : Fin 19} (hs : kind s = 1) (ht : kind t ≠ 0) :
    rowVal.{u} b s t = v1 := by
  have h15 : s ≠ 15 := by rintro rfl; exact absurd hs (by decide)
  have h18 : s ≠ 18 := by rintro rfl; exact absurd hs (by decide)
  have h16 : s ≠ 16 := by rintro rfl; exact absurd hs (by decide)
  have h13 : s ≠ 13 := by rintro rfl; exact absurd hs (by decide)
  simp [rowVal, hs, ht, h15, h18, h16, h13]

/-- The cell `13` reads its live cells at `ω + 2`. -/
theorem rowVal_thirteen {t : Fin 19} (ht : kind t ≠ 0) : rowVal.{u} b 13 t = v2 := by
  simp [rowVal, ht, show kind 13 = 2 from rfl]

/-- In `TH`, the cell `15` reads its live cells at `ω + 2`. -/
theorem rowVal_fifteen_true {t : Fin 19} (ht : kind t ≠ 0) : rowVal.{u} true 15 t = v2 := by
  simp [rowVal, ht, show kind 15 = 2 from rfl]

/-- In `TG`, the cell `15` reads the cells of kind `A` at `1`. -/
theorem rowVal_fifteen_false_one {t : Fin 19} (ht : kind t = 1) : rowVal.{u} false 15 t = v1 := by
  simp [rowVal, ht, show kind 15 = 2 from rfl]

/-- In `TG`, the cell `15` reads the cells of kind `H` at `ω + 2`. -/
theorem rowVal_fifteen_false_two {t : Fin 19} (ht : kind t = 2) : rowVal.{u} false 15 t = v2 := by
  simp [rowVal, ht, show kind 15 = 2 from rfl]

/-- The cell `16` reads the cell `13` at `2`. -/
theorem rowVal_sixteen_two {t : Fin 19} (ht : kind t = 2) : rowVal.{u} b 16 t = w2 := by
  simp [rowVal, ht, show kind 16 = 3 from rfl]

/-- The cell `16` reads itself at `ω + 3`. -/
theorem rowVal_sixteen_three {t : Fin 19} (ht : kind t = 3) : rowVal.{u} b 16 t = w3 := by
  simp [rowVal, ht, show kind 16 = 3 from rfl]

/-- In `TH`, the cell `18` reads the cells of kind `G` at `ω + 3`, the others at `2`. -/
theorem rowVal_eighteen_true {t : Fin 19} (ht : kind t ≠ 0) :
    rowVal.{u} true 18 t = if kind t = 3 then w3 else w2 := by
  simp [rowVal, ht, show kind 18 = 3 from rfl]

/-- In `TG`, the cell `18` reads the cells of kind `H` at `2`, the others at `ω + 3`. -/
theorem rowVal_eighteen_false {t : Fin 19} (ht : kind t ≠ 0) :
    rowVal.{u} false 18 t = if kind t = 2 then w2 else w3 := by
  simp [rowVal, ht, show kind 18 = 3 from rfl]

/-! ### Labels -/

/-- The row value `2` is the natural number `2`. -/
theorem w2_eq : (w2 : Label.{u}) = ((2 : ℕ) : Label.{u}) := by
  rw [natCast_label]; simp [w2, gridPoint]

/-- The strip shifter at the grade `3` sends `2` to the replacement with the value `2`. -/
theorem strip3_w2 (A : Label.{u}) : strip3 A w2 = visibilityReplace 3 2 A := by
  rw [w2_eq, strip3_natCast]; rfl

/-- The row value `ω + 3` is not a natural number. -/
theorem w3_not_lt : ¬ (w3 : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
  rw [not_lt, w3, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
  calc (ω : Ordinal.{u}) = ω * ((1 : ℕ) : Ordinal.{u}) := by simp
    _ ≤ _ := le_self_add

/-- The strip shifter at the grade `3` sends `ω + 3` to `⊤`. -/
theorem strip3_w3 (A : Label.{u}) : strip3 A w3 = ⊤ :=
  strip3_of_not_lt (gridPoint_ne_bot 3 1) w3_not_lt

/-- A label self-visible at `2` is fixed by visibility replacement at `3` with the value `2`. -/
theorem visibilityReplace_three_two_of_isSelfVisible {a : Label.{u}} (ha : IsSelfVisible 2 a) :
    visibilityReplace 3 2 a = a := by
  by_cases hb : a = ⊥
  · rw [hb]; simp
  by_cases ht : a = ⊤
  · rw [ht]; simp
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  have hn : 2 ≤ n := isSelfVisible_block.mp ha
  have hif : (if n < 3 then 2 else n) = n := by split_ifs <;> omega
  rw [visibilityReplace_block, hif]

/-- The coupling of `TH` at the cells of kind `A`, read by the cell `18`. -/
theorem min_visibilityReplace_A (hH : IsSelfVisible 2 H) (h1 : H ≤ A) (h2 : min A G ≤ H) :
    min A G = min (visibilityReplace 3 2 A) G := by
  have hle : A ≤ visibilityReplace 3 2 A := le_visibilityReplace (by omega) A
  rcases le_or_gt G H with hGH | hHG
  · rw [min_eq_right (hGH.trans h1), min_eq_right ((hGH.trans h1).trans hle)]
  · have hAH : A = H := le_antisymm (by order) h1
    rw [hAH, visibilityReplace_three_two_of_isSelfVisible hH]

/-- The coupling of `TH` at the cells of kind `H`, read by the cell `18`. -/
theorem min_visibilityReplace_H (hH : IsSelfVisible 2 H) (h1 : H ≤ A) (h2 : min A G ≤ H) :
    min H G = min (visibilityReplace 3 2 A) G := by
  rw [← min_visibilityReplace_A hH h1 h2]
  rcases le_or_gt G H with hGH | hHG
  · rw [min_eq_right hGH, min_eq_right (hGH.trans h1)]
  · have hAH : A = H := le_antisymm (by order) h1
    rw [hAH]

/-! ### The labellings `lab A H G` are lawful -/

/-- Each label of `lab A H G` is self-visible at the grade of its cell. -/
theorem isSelfVisible_lab (hA : IsSelfVisible 1 A) (hH : IsSelfVisible 2 H)
    (hG : IsSelfVisible 3 G) (d : Fin 19) : IsSelfVisible (cellGrade d) (lab A H G d) := by
  rcases kind_live_cases d with h | h | h | h
  · rw [lab_of_kind_zero h]; exact isSelfVisible_bot _
  · rw [lab_of_kind_one h, grade_of_kind_one d h]; exact hA
  · rw [lab_of_kind_two h]
    rcases kind_two_cases d h with rfl | rfl <;> exact hH
  · rw [lab_of_kind_three h]
    rcases kind_three_cases d h with rfl | rfl <;> exact hG

/-- A transformation of a row of `rows b` to `lab A H G` capped at the label of the cell, checked
cell by cell. -/
private theorem transformsTo_of_forall {s : Fin 19} {g : ℕ → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    (h : ∀ d, cells.gradedIndex d ≤ cells.gradedIndex s →
      min (lab A H G d) (lab A H G s) = min (σ (rowVal b s d)) (g (cellGrade d))) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) ((rows b).row s)
      (fun d ↦ min (lab A H G d) (lab A H G s)) :=
  ⟨g, σ, hw, fun d ↦ h d.1 d.2⟩

/-- At a dead cell below `s`, both sides of a transformation are `⊥`. -/
private theorem dead_case {σ : Label.{u} → Label.{u}} {g : ℕ → Label.{u}} (hw : IsWitness g σ)
    {s d : Fin 19} (hd : kind d = 0) (x : Label.{u}) :
    min (lab A H G d) x = min (σ (rowVal b s d)) (g (cellGrade d)) := by
  rw [lab_of_kind_zero hd, rowVal_of_kind_zero_right hd, hw.map_bot]; simp

/-- **`lab A H G` is lawful** for parameters self-visible at `1`, `2`, `3` with the coupling. -/
theorem isLawful_lab (hA : IsSelfVisible 1 A) (hH : IsSelfVisible 2 H) (hG : IsSelfVisible 3 G)
    (hc : Coupled b A H G) : (rows b).IsLawful (lab A H G) where
  orderly d := isSelfVisible_lab hA hH hG d
  locality s := by
    rcases kind_cases s with hs | hs | rfl | rfl | rfl | rfl
    · rw [show lab A H G s = ⊥ from lab_of_kind_zero hs]
      simp only [min_bot_right]
      exact TransformsTo.bot _ _
    · -- A cell of kind `A`: the top shifter, the suppressor `A` up to the grade `1`.
      have hw := isWitness_topShifter (antitone_constStepSuppressor 1 A)
        (isSelfVisible_constStepSuppressor hA)
      refine transformsTo_of_forall hw fun d hds ↦ ?_
      by_cases hd : kind d = 0
      · exact dead_case hw hd _
      have hd1 := kind_of_le_kind_one s d hs hd hds
      rw [lab_of_kind_one hd1, lab_of_kind_one hs, rowVal_of_kind_one hs hd, topShifter,
        ite_eq_right (gridPoint_ne_bot 1 0), constStepSuppressor,
        ite_eq_left (grade_of_kind_one d hd1).le, min_self, min_top_left]
    · -- The cell `13`: the top shifter, the suppressor `H` up to the grade `2`.
      have hw := isWitness_topShifter (antitone_constStepSuppressor 2 H)
        (isSelfVisible_constStepSuppressor hH)
      refine transformsTo_of_forall hw fun d hds ↦ ?_
      by_cases hd : kind d = 0
      · exact dead_case hw hd _
      obtain rfl := eq_of_le_thirteen d hd hds
      rw [rowVal_thirteen hd, topShifter, ite_eq_right (gridPoint_ne_bot 2 1),
        constStepSuppressor, ite_eq_left (by decide), min_top_left,
        lab_of_kind_two (by decide), min_self]
    · cases b
      · -- The cell `15` of `TG`: the strip shifter of `A`, the suppressor `H` up to `2`.
        refine transformsTo_of_forall (isWitness_stripShifter (A := A) hH) fun d hds ↦ ?_
        by_cases hd : kind d = 0
        · exact dead_case (isWitness_stripShifter hH) hd _
        rw [lab_of_kind_two (show kind 15 = 2 by decide)]
        rcases kind_of_le_fifteen d hd hds with hd1 | hd2
        · rw [lab_of_kind_one hd1, rowVal_fifteen_false_one hd1, stripShifter_v1 hA,
            constStepSuppressor, ite_eq_left (by rw [grade_of_kind_one d hd1]; omega)]
        · rw [lab_of_kind_two hd2, rowVal_fifteen_false_two hd2, stripShifter_v2,
            constStepSuppressor, ite_eq_left (by
              rcases kind_two_cases d hd2 with rfl | rfl <;> decide), min_self, min_top_left]
      · -- The cell `15` of `TH`: the top shifter, the suppressor `H` up to `2`.
        have hw := isWitness_topShifter (antitone_constStepSuppressor 2 H)
          (isSelfVisible_constStepSuppressor hH)
        refine transformsTo_of_forall hw fun d hds ↦ ?_
        by_cases hd : kind d = 0
        · exact dead_case hw hd _
        have hHA : H ≤ A := (by simpa [Coupled] using hc : H ≤ A ∧ min A G ≤ H).1
        rw [lab_of_kind_two (show kind 15 = 2 by decide), rowVal_fifteen_true hd, topShifter,
          ite_eq_right (gridPoint_ne_bot 2 1), min_top_left, constStepSuppressor,
          ite_eq_left (by
            rcases kind_of_le_fifteen d hd hds with h | h
            · rw [grade_of_kind_one d h]; omega
            · rcases kind_two_cases d h with rfl | rfl <;> decide)]
        rcases kind_of_le_fifteen d hd hds with hd1 | hd2
        · rw [lab_of_kind_one hd1, min_eq_right hHA]
        · rw [lab_of_kind_two hd2, min_self]
    · -- The cell `16`: the strip shifter `strip3 H`, the suppressor `G` up to `3`.
      refine transformsTo_of_forall (isWitness_strip3 (A := H) hG) fun d hds ↦ ?_
      by_cases hd : kind d = 0
      · exact dead_case (isWitness_strip3 hG) hd _
      rw [lab_of_kind_three (show kind 16 = 3 by decide)]
      rcases eq_of_le_sixteen d hd hds with rfl | rfl
      · rw [lab_of_kind_two (by decide), rowVal_sixteen_two (by decide), strip3_w2,
          visibilityReplace_three_two_of_isSelfVisible hH, constStepSuppressor,
          ite_eq_left (by decide)]
      · rw [lab_of_kind_three (by decide), rowVal_sixteen_three (by decide), strip3_w3,
          constStepSuppressor, ite_eq_left (by decide), min_self, min_top_left]
    · cases b
      · -- The cell `18` of `TG`: `strip3 H`, the suppressor `G` up to `3`; coupling `G ≤ A`.
        have hGA : G ≤ A := by simpa [Coupled] using hc
        refine transformsTo_of_forall (isWitness_strip3 (A := H) hG) fun d _ ↦ ?_
        by_cases hd : kind d = 0
        · exact dead_case (isWitness_strip3 hG) hd _
        rw [lab_of_kind_three (show kind 18 = 3 by decide), rowVal_eighteen_false hd,
          constStepSuppressor, ite_eq_left (CaseSplitCounterexample.grade_le_three d)]
        rcases kind_live_cases d with h | h | h | h
        · exact absurd h hd
        · rw [lab_of_kind_one h, ite_eq_right (by rw [h]; decide), strip3_w3, min_top_left,
            min_eq_right hGA]
        · rw [lab_of_kind_two h, ite_eq_left h, strip3_w2,
            visibilityReplace_three_two_of_isSelfVisible hH]
        · rw [lab_of_kind_three h, ite_eq_right (by rw [h]; decide), strip3_w3, min_top_left,
            min_self]
      · -- The cell `18` of `TH`: `strip3 A`, the suppressor `G` up to `3`.
        obtain ⟨h1, h2⟩ : H ≤ A ∧ min A G ≤ H := by simpa [Coupled] using hc
        refine transformsTo_of_forall (isWitness_strip3 (A := A) hG) fun d _ ↦ ?_
        by_cases hd : kind d = 0
        · exact dead_case (isWitness_strip3 hG) hd _
        rw [lab_of_kind_three (show kind 18 = 3 by decide), rowVal_eighteen_true hd,
          constStepSuppressor, ite_eq_left (CaseSplitCounterexample.grade_le_three d)]
        rcases kind_live_cases d with h | h | h | h
        · exact absurd h hd
        · rw [lab_of_kind_one h, ite_eq_right (by rw [h]; decide), strip3_w2]
          exact min_visibilityReplace_A hH h1 h2
        · rw [lab_of_kind_two h, ite_eq_right (by rw [h]; decide), strip3_w2]
          exact min_visibilityReplace_H hH h1 h2
        · rw [lab_of_kind_three h, ite_eq_left h, strip3_w3, min_top_left, min_self]
  availability s t hst hg := by
    refine ⟨t, rfl, ?_⟩
    by_cases hs : kind s = 0
    · rw [lab_of_kind_zero hs]; exact bot_le
    · rw [lab, lab, kind_up s t hs hst hg]

/-! ### The lawful labellings below a pair -/

/-- **The lawful labellings below a pair** are the restrictions of the labellings `lab A H G`
with `A`, `H`, `G` self-visible at `1`, `2`, `3` and the coupling `Coupled b A H G`. -/
theorem isLawfulBelow_iff {Y : Finset (Fin 4) × ℕ} {x : Fin 19 → Label.{u}} :
    (rows b).IsLawfulBelow Y (fun d ↦ x d) ↔ ∃ A H G : Label.{u}, IsSelfVisible 1 A ∧
      IsSelfVisible 2 H ∧ IsSelfVisible 3 G ∧ Coupled b A H G ∧
      ∀ d ∈ cells.below Y, x d = lab A H G d := by
  classical
  constructor
  · intro hx
    obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
    have hdead : ∀ d ∈ cells.below Y, kind d = 0 → x d = ⊥ := by
      intro d hd hdk
      have := (hl d hd).eq_bot (d := ⟨d, cells.mem_below_gradedIndex d⟩)
        (rowVal_of_kind_zero_left hdk)
      simpa using this
    have havail : ∀ s t, t ∈ cells.below Y → cellScope s ⊆ cellScope t →
        cellGrade s = cellGrade t → x s ≤ x t := by
      intro s t ht hst hg
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rwa [gradedIndex_injective hu] at hle
    have hle : ∀ s ∈ cells.below Y, ∀ d (hds : cells.gradedIndex d ≤ cells.gradedIndex s),
        rowVal.{u} b s s ≤ rowVal b s d → cellGrade d ≤ cellGrade s → x s ≤ x d := by
      intro s hs d hds hr hg
      have := (hl s hs).le_of_le (d := ⟨s, cells.mem_below_gradedIndex s⟩) (d' := ⟨d, hds⟩)
        hr hg
      simp only [min_self] at this
      exact this.trans (min_le_left _ _)
    -- The cells of kind `A` below `Y` carry the label of the cell `3`.
    have hA : ∀ d ∈ cells.below Y, kind d = 1 → x d = x 3 := by
      intro d hd hk
      have h3le := three_le d hk
      refine le_antisymm (hle d hd 3 h3le ?_ ?_) (havail 3 d hd h3le.1 ?_)
      · rw [rowVal_of_kind_one hk (by rw [hk]; decide),
          rowVal_of_kind_one hk (by decide)]
      · rw [grade_of_kind_one d hk]; decide
      · rw [grade_of_kind_one d hk]; rfl
    have h15 : (15 : Fin 19) ∈ cells.below Y → x 15 = x 13 := by
      intro h15m
      have h13le : cells.gradedIndex 13 ≤ cells.gradedIndex 15 := by
        simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel
      refine le_antisymm (hle 15 h15m 13 h13le ?_ (by decide)) (havail 13 15 h15m h13le.1 rfl)
      cases b
      · rw [rowVal_fifteen_false_two (by decide), rowVal_fifteen_false_two (by decide)]
      · rw [rowVal_fifteen_true (by decide), rowVal_fifteen_true (by decide)]
    have h18 : (18 : Fin 19) ∈ cells.below Y → x 18 = x 16 := by
      intro h18m
      have h16le : cells.gradedIndex 16 ≤ cells.gradedIndex 18 :=
        CaseSplitCounterexample.le_eighteen 16
      refine le_antisymm (hle 18 h18m 16 h16le ?_ (by decide)) (havail 16 18 h18m h16le.1 rfl)
      cases b
      · rw [rowVal_eighteen_false (by decide), rowVal_eighteen_false (by decide)]
        simp [show kind 18 = 3 from rfl, show kind 16 = 3 from rfl]
      · rw [rowVal_eighteen_true (by decide), rowVal_eighteen_true (by decide)]
        simp [show kind 18 = 3 from rfl, show kind 16 = 3 from rfl]
    set Hc : Label.{u} := if (13 : Fin 19) ∈ cells.below Y then x 13 else ⊥ with hHc
    set Gc : Label.{u} := if (16 : Fin 19) ∈ cells.below Y then x 16 else ⊥ with hGc
    set Ac : Label.{u} := if (3 : Fin 19) ∈ cells.below Y then x 3 else
      (if b then Hc else ⊤) with hAc
    have hsH : IsSelfVisible 2 Hc := by
      rw [hHc]; split_ifs with h
      · exact ho 13 h
      · exact isSelfVisible_bot 2
    have hsG : IsSelfVisible 3 Gc := by
      rw [hGc]; split_ifs with h
      · exact ho 16 h
      · exact isSelfVisible_bot 3
    have hsA : IsSelfVisible 1 Ac := by
      rw [hAc]; split_ifs with h
      · exact ho 3 h
      · exact hsH.mono (by omega)
      · exact isSelfVisible_top 1
    have hcpl : Coupled b Ac Hc Gc := by
      cases b
      · -- `TG`: the coupling `G ≤ A`, from locality at the cell `18`.
        simp only [Coupled, Bool.false_eq_true, ↓reduceIte]
        rw [hAc, hGc]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases h16 : (16 : Fin 19) ∈ cells.below Y
        · by_cases h3 : (3 : Fin 19) ∈ cells.below Y
          · have h18m := eighteen_mem_below h3 h16
            rw [ite_eq_left h16, ite_eq_left h3, ← h18 h18m]
            refine hle 18 h18m 3 (CaseSplitCounterexample.le_eighteen 3) ?_ (by decide)
            rw [rowVal_eighteen_false (by decide), rowVal_eighteen_false (by decide)]
            simp [show kind 18 = 3 from rfl, show kind 3 = 1 from rfl]
          · rw [ite_eq_right h3]; exact le_top
        · rw [ite_eq_right h16]; exact bot_le
      · simp only [Coupled, ↓reduceIte]
        rw [hAc, hHc, hGc]
        simp only [↓reduceIte]
        by_cases h3 : (3 : Fin 19) ∈ cells.below Y
        · rw [ite_eq_left h3]
          constructor
          · -- `H ≤ A`, from locality at the cell `15`.
            by_cases h13 : (13 : Fin 19) ∈ cells.below Y
            · rw [ite_eq_left h13]
              have h15m := fifteen_mem_below h3 h13
              have := (hl 15 h15m).le_of_le (d := ⟨13, by
                  simp only [CellScheme.mem_below, gradedIndex_cells, Prod.mk_le_mk]
                  decide +kernel⟩) (d' := ⟨3, by
                  simp only [CellScheme.mem_below, gradedIndex_cells, Prod.mk_le_mk]
                  decide +kernel⟩)
                (by change rowVal true 15 13 ≤ rowVal true 15 3
                    rw [rowVal_fifteen_true (by decide), rowVal_fifteen_true (by decide)])
                (by decide)
              simp only [h15 h15m] at this
              order
            · rw [ite_eq_right h13]; exact bot_le
          · -- `min A G ≤ H`, from locality at the cell `18`.
            by_cases h16 : (16 : Fin 19) ∈ cells.below Y
            · have h13 := thirteen_mem_below h16
              have h18m := eighteen_mem_below h3 h16
              rw [ite_eq_left h13, ite_eq_left h16, ← h18 h18m]
              obtain ⟨g, σ, hw, heq⟩ := hl 18 h18m
              have e3 := heq ⟨3, CaseSplitCounterexample.le_eighteen 3⟩
              have e13 := heq ⟨13, CaseSplitCounterexample.le_eighteen 13⟩
              have e18 := heq ⟨18, CaseSplitCounterexample.le_eighteen 18⟩
              change min (x 3) (x 18) = min (σ (rowVal true 18 3)) (g 1) at e3
              change min (x 13) (x 18) = min (σ (rowVal true 18 13)) (g 2) at e13
              change min (x 18) (x 18) = min (σ (rowVal true 18 18)) (g 3) at e18
              rw [rowVal_eighteen_true (by decide)] at e3 e13 e18
              simp only [show kind 3 = 1 from rfl, show kind 13 = 2 from rfl,
                show kind 18 = 3 from rfl, ↓reduceIte, min_self] at e3 e13 e18
              rw [ite_eq_right (by decide)] at e3 e13
              have hg32 : g 3 ≤ g 2 := hw.antitone (by omega)
              have hg21 : g 2 ≤ g 1 := hw.antitone (by omega)
              by_contra hcon
              rw [not_le] at hcon
              -- `σ 2` is the label of the cell `13`, below the suppressor.
              have hσ : σ w2 = x 13 := by
                rcases le_total (σ w2) (g 2) with h | h
                · rw [min_eq_left h] at e13; order
                · rw [min_eq_right h] at e13; order
              rw [hσ] at e3
              order
            · rw [ite_eq_right h16]; simp
        · rw [ite_eq_right h3]
          exact ⟨le_rfl, min_le_left _ _⟩
    refine ⟨Ac, Hc, Gc, hsA, hsH, hsG, hcpl, fun d hd ↦ ?_⟩
    rcases kind_live_cases d with hk | hk | hk | hk
    · rw [lab_of_kind_zero hk, hdead d hd hk]
    · have h3 : (3 : Fin 19) ∈ cells.below Y := mem_below_of_le hd (three_le d hk)
      rw [lab_of_kind_one hk, hAc, ite_eq_left h3, hA d hd hk]
    · have h13 : (13 : Fin 19) ∈ cells.below Y := mem_below_of_le hd (thirteen_le d hk)
      rw [lab_of_kind_two hk, hHc, ite_eq_left h13]
      rcases kind_two_cases d hk with rfl | rfl
      · rfl
      · exact h15 hd
    · have h16 : (16 : Fin 19) ∈ cells.below Y := mem_below_of_le hd (sixteen_le d hk)
      rw [lab_of_kind_three hk, hGc, ite_eq_left h16]
      rcases kind_three_cases d hk with rfl | rfl
      · rfl
      · exact h18 hd
  · rintro ⟨A, H, G, hA, hH, hG, hc, hx⟩
    have := (isLawful_lab hA hH hG hc).isLawfulBelow Y
    convert this using 1
    funext d
    exact hx d d.2

/-! ### The lifts of parameters -/

section Lift

open Classical in
/-- The lifted parameter of kind `G` (or `H`): prescribed when its cells meet the prescription;
otherwise, when its cells lie below the target, the ambient below the cap and the cap above it;
`⊥` when no cell of the kind lies below the target. -/
noncomputable def liftedGH (pX p : Prop) (xp xq c : Label.{u}) : Label.{u} :=
  if pX then xp else if p then (if xq < c then xq else c) else ⊥

open Classical in
/-- The lifted parameter of kind `A` for `TH`: prescribed when its cells meet the prescription;
otherwise, when its cells lie below the target, the ambient below the cap and above it `H_p`
when `H` and `G` are prescribed with `H_p < G_p`, and `⊤` otherwise; the lifted `H` when no cell
of kind `A` lies below the target. -/
noncomputable def liftedAH (aX a hX gX : Prop) (Ap Aq Hp Gp H' c : Label.{u}) : Label.{u} :=
  if aX then Ap else if a then
    (if Aq < c then Aq else if hX ∧ gX ∧ Hp < Gp then Hp else ⊤) else H'

open Classical in
/-- A lifted parameter that is prescribed, or else the ambient below the cap and `⊤` above. -/
noncomputable def liftedTop (pX : Prop) (xp xq c : Label.{u}) : Label.{u} :=
  if pX then xp else if xq < c then xq else ⊤

/-- **The lift of parameters of `TH`.**  The lifted parameters satisfy the coupling of `TH` and
agree with the ambient capped at `c` wherever their cells lie below the target. -/
theorem liftParamsH {a aX h hX g gX : Prop} (haX : aX → a) (hhX : hX → h) (hgX : gX → g)
    (hgh : g → h) (hghX : gX → hX) {Ap Hp Gp Aq Hq Gq c : Label.{u}}
    (hp1 : Hp ≤ Ap) (hp2 : min Ap Gp ≤ Hp) (hq1 : Hq ≤ Aq) (hq2 : min Aq Gq ≤ Hq)
    (ca : aX → min Aq c = min Ap c) (ch : hX → min Hq c = min Hp c)
    (cg : gX → min Gq c = min Gp c) :
    liftedGH hX h Hp Hq c ≤ liftedAH aX a hX gX Ap Aq Hp Gp (liftedGH hX h Hp Hq c) c ∧
      min (liftedAH aX a hX gX Ap Aq Hp Gp (liftedGH hX h Hp Hq c) c) (liftedGH gX g Gp Gq c) ≤
        liftedGH hX h Hp Hq c ∧
      (a → min (liftedAH aX a hX gX Ap Aq Hp Gp (liftedGH hX h Hp Hq c) c) c = min Aq c) ∧
      (h → min (liftedGH hX h Hp Hq c) c = min Hq c) ∧
      (g → min (liftedGH gX g Gp Gq c) c = min Gq c) := by
  unfold liftedGH liftedAH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    by_cases ha : a <;> by_cases haX' : aX <;> by_cases hh : h <;> by_cases hhX' : hX <;>
    by_cases hg : g <;> by_cases hgX' : gX <;>
    simp only [ha, haX', hh, hhX', hg, hgX', ↓reduceIte, true_implies, true_and, false_and,
      IsEmpty.forall_iff] at * <;>
    (try trivial) <;> (try split_ifs) <;> order

/-- **The lift of parameters of `TG`.**  The lifted parameters satisfy the coupling of `TG` and
agree with the ambient capped at `c` wherever their cells lie below the target. -/
theorem liftParamsG {aX g gX : Prop} (hgX : gX → g) {Ap Gp Aq Gq c : Label.{u}}
    (hp : Gp ≤ Ap) (hq : Gq ≤ Aq) (ca : aX → min Aq c = min Ap c)
    (cg : gX → min Gq c = min Gp c) :
    liftedGH gX g Gp Gq c ≤ liftedTop aX Ap Aq c ∧ min (liftedTop aX Ap Aq c) c = min Aq c ∧
      (g → min (liftedGH gX g Gp Gq c) c = min Gq c) := by
  unfold liftedGH liftedTop
  refine ⟨?_, ?_, ?_⟩ <;>
    by_cases haX' : aX <;> by_cases hg : g <;> by_cases hgX' : gX <;>
    simp only [haX', hg, hgX', ↓reduceIte, true_implies, IsEmpty.forall_iff] at * <;>
    (try trivial) <;> (try split_ifs) <;> order

/-- A lifted parameter of the form `liftedTop` agrees with the ambient capped at `c`. -/
theorem min_liftedTop {pX : Prop} {xp xq c : Label.{u}} (h : pX → min xq c = min xp c) :
    min (liftedTop pX xp xq c) c = min xq c := by
  unfold liftedTop
  by_cases hpX : pX <;> simp only [hpX, ↓reduceIte, true_implies, IsEmpty.forall_iff] at * <;>
    (try split_ifs) <;> order

end Lift

/-! ### Bountifulness -/

/-- The labelling with all parameters `⊥` is `⊥`. -/
theorem lab_bot (d : Fin 19) : lab (⊥ : Label.{u}) ⊥ ⊥ d = ⊥ := by
  unfold lab; generalize kind d = k; fin_cases k <;> rfl

/-- Two labellings `lab` agree capped at `c` at a cell below `Y` when their parameters do at the
kinds whose cells lie below `Y`. -/
private theorem min_lab_eq {Y : Finset (Fin 4) × ℕ} {A H G A' H' G' c : Label.{u}}
    (ha : (3 : Fin 19) ∈ cells.below Y → min A' c = min A c)
    (hh : (13 : Fin 19) ∈ cells.below Y → min H' c = min H c)
    (hg : (16 : Fin 19) ∈ cells.below Y → min G' c = min G c) {d : Fin 19}
    (hd : d ∈ cells.below Y) : min (lab A' H' G' d) c = min (lab A H G d) c := by
  rcases kind_live_cases d with hk | hk | hk | hk
  · rw [lab_of_kind_zero hk, lab_of_kind_zero hk]
  · rw [lab_of_kind_one hk, lab_of_kind_one hk]
    exact ha (mem_below_of_le hd (three_le d hk))
  · rw [lab_of_kind_two hk, lab_of_kind_two hk]
    exact hh (mem_below_of_le hd (thirteen_le d hk))
  · rw [lab_of_kind_three hk, lab_of_kind_three hk]
    exact hg (mem_below_of_le hd (sixteen_le d hk))

/-- Two labellings `lab` agree at a cell below `X` when their parameters do at the kinds whose
cells lie below `X`. -/
private theorem lab_eq {X : Finset (Fin 4) × ℕ} {A H G A' H' G' : Label.{u}}
    (ha : (3 : Fin 19) ∈ cells.below X → A' = A) (hh : (13 : Fin 19) ∈ cells.below X → H' = H)
    (hg : (16 : Fin 19) ∈ cells.below X → G' = G) {d : Fin 19} (hd : d ∈ cells.below X) :
    lab A' H' G' d = lab A H G d := by
  rcases kind_live_cases d with hk | hk | hk | hk
  · rw [lab_of_kind_zero hk, lab_of_kind_zero hk]
  · rw [lab_of_kind_one hk, lab_of_kind_one hk]
    exact ha (mem_below_of_le hd (three_le d hk))
  · rw [lab_of_kind_two hk, lab_of_kind_two hk]
    exact hh (mem_below_of_le hd (thirteen_le d hk))
  · rw [lab_of_kind_three hk, lab_of_kind_three hk]
    exact hg (mem_below_of_le hd (sixteen_le d hk))

/-- **Every pair lifts capped to every larger pair.**  For a prescription `lab A_p H_p G_p` below
`X` and an ambient `lab A_q H_q G_q` below `Y`, the lift is `lab A' H' G'` with the lifted
parameters of `liftParamsH` (for `TH`) or `liftParamsG` (for `TG`). -/
theorem cappedLift_all {X Y : Finset (Fin 4) × ℕ} (h : X ≤ Y) : (rows b).CappedLift.{u} h := by
  classical
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨Ap, Hp, Gp, hAp, hHp, hGp, hcp, hpx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨Aq, Hq, Gq, hAq, hHq, hGq, hcq, hqx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpd (d : cells.below X) : p d = lab Ap Hp Gp d := by
    rw [← hpx d d.2, Rows.extendBot_of_mem p d.2]
  have hqd (d : cells.below Y) : q d = lab Aq Hq Gq d := by
    rw [← hqx d d.2, Rows.extendBot_of_mem q d.2]
  have hcap (d : Fin 19) (hd : d ∈ cells.below X) :
      min (lab Aq Hq Gq d) c = min (lab Ap Hp Gp d) c := by
    have := hpq ⟨d, hd⟩
    rwa [hqd, hpd] at this
  have hcap3 (h3 : (3 : Fin 19) ∈ cells.below X) : min Aq c = min Ap c := by
    simpa [lab_of_kind_one (show kind 3 = 1 from rfl)] using hcap 3 h3
  have hcap13 (h13 : (13 : Fin 19) ∈ cells.below X) : min Hq c = min Hp c := by
    simpa [lab_of_kind_two (show kind 13 = 2 from rfl)] using hcap 13 h13
  have hcap16 (h16 : (16 : Fin 19) ∈ cells.below X) : min Gq c = min Gp c := by
    simpa [lab_of_kind_three (show kind 16 = 3 from rfl)] using hcap 16 h16
  have hXY {d : Fin 19} (hd : d ∈ cells.below X) : d ∈ cells.below Y := cells.below_mono h hd
  have hc2 (h13 : (13 : Fin 19) ∈ cells.below Y) : IsSelfVisible 2 c := hc.mono h13.2
  have hc3 (h16 : (16 : Fin 19) ∈ cells.below Y) : IsSelfVisible 3 c := hc.mono h16.2
  obtain ⟨A', H', G', hA', hH', hG', hc', ha, hh, hg, pa, ph, pg⟩ : ∃ A' H' G' : Label.{u},
      IsSelfVisible 1 A' ∧ IsSelfVisible 2 H' ∧ IsSelfVisible 3 G' ∧ Coupled b A' H' G' ∧
      ((3 : Fin 19) ∈ cells.below Y → min A' c = min Aq c) ∧
      ((13 : Fin 19) ∈ cells.below Y → min H' c = min Hq c) ∧
      ((16 : Fin 19) ∈ cells.below Y → min G' c = min Gq c) ∧
      ((3 : Fin 19) ∈ cells.below X → A' = Ap) ∧ ((13 : Fin 19) ∈ cells.below X → H' = Hp) ∧
      ((16 : Fin 19) ∈ cells.below X → G' = Gp) := by
    have hsGH {xp xq : Label.{u}} {k : ℕ} {e : Fin 19} (hxp : IsSelfVisible k xp)
        (hxq : IsSelfVisible k xq) (hce : e ∈ cells.below Y → IsSelfVisible k c) {eX : Prop} :
        IsSelfVisible k (liftedGH eX (e ∈ cells.below Y) xp xq c) := by
      unfold liftedGH
      split_ifs with h1 h2
      · exact hxp
      · exact hxq
      · exact hce h2
      · exact isSelfVisible_bot k
    have hsG' := hsGH (eX := (16 : Fin 19) ∈ cells.below X) hGp hGq hc3
    cases b
    · -- `TG`.
      have hcp' : Gp ≤ Ap := by simpa [Coupled] using hcp
      have hcq' : Gq ≤ Aq := by simpa [Coupled] using hcq
      obtain ⟨hGA, hmA, hmG⟩ := liftParamsG (aX := (3 : Fin 19) ∈ cells.below X)
        (fun h16 ↦ hXY h16) hcp' hcq' hcap3 hcap16
      refine ⟨liftedTop ((3 : Fin 19) ∈ cells.below X) Ap Aq c,
        liftedTop ((13 : Fin 19) ∈ cells.below X) Hp Hq c,
        liftedGH ((16 : Fin 19) ∈ cells.below X) ((16 : Fin 19) ∈ cells.below Y) Gp Gq c,
        ?_, ?_, hsG', by simp only [Coupled, Bool.false_eq_true, ↓reduceIte]; exact hGA,
        fun _ ↦ hmA,
        fun _ ↦ min_liftedTop hcap13, hmG, fun h3 ↦ by simp [liftedTop, h3],
        fun h13 ↦ by simp [liftedTop, h13], fun h16 ↦ by simp [liftedGH, h16]⟩
      · unfold liftedTop; split_ifs
        · exact hAp
        · exact hAq
        · exact isSelfVisible_top 1
      · unfold liftedTop; split_ifs
        · exact hHp
        · exact hHq
        · exact isSelfVisible_top 2
    · -- `TH`.
      obtain ⟨hp1, hp2⟩ : Hp ≤ Ap ∧ min Ap Gp ≤ Hp := by simpa [Coupled] using hcp
      obtain ⟨hq1, hq2⟩ : Hq ≤ Aq ∧ min Aq Gq ≤ Hq := by simpa [Coupled] using hcq
      have hsH' := hsGH (eX := (13 : Fin 19) ∈ cells.below X) hHp hHq hc2
      obtain ⟨c1, c2, ma, mh, mg⟩ := liftParamsH (a := (3 : Fin 19) ∈ cells.below Y)
        (aX := (3 : Fin 19) ∈ cells.below X) (h := (13 : Fin 19) ∈ cells.below Y)
        (hX := (13 : Fin 19) ∈ cells.below X) (g := (16 : Fin 19) ∈ cells.below Y)
        (gX := (16 : Fin 19) ∈ cells.below X) hXY hXY hXY thirteen_mem_below
        thirteen_mem_below hp1 hp2 hq1 hq2 hcap3 hcap13 hcap16
      refine ⟨_, _, _, ?_, hsH', hsG', by simp only [Coupled, ↓reduceIte]; exact ⟨c1, c2⟩, ma,
        mh, mg,
        fun h3 ↦ by simp [liftedAH, h3], fun h13 ↦ by simp [liftedGH, h13],
        fun h16 ↦ by simp [liftedGH, h16]⟩
      unfold liftedAH; split_ifs
      · exact hAp
      · exact hAq
      · exact hHp.mono (by omega)
      · exact isSelfVisible_top 1
      · exact hsH'.mono (by omega)
  refine ⟨fun d ↦ lab A' H' G' d,
    isLawfulBelow_iff.mpr ⟨A', H', G', hA', hH', hG', hc', fun _ _ ↦ rfl⟩,
    fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hqd]; exact min_lab_eq ha hh hg d.2
  · rw [hpd]; exact lab_eq pa ph pg d.2

/-- **The rows are bountiful.** -/
theorem isBountiful_rows : (rows.{u} b).IsBountiful := fun _ _ _ _ h ↦ cappedLift_all h

/-! ### Legality -/

/-- The row value `1` is self-visible at `1`. -/
theorem isSelfVisible_v1 : IsSelfVisible 1 (v1 : Label.{u}) := isSelfVisible_gridPoint 1 0
/-- The row value `ω + 2` is self-visible at `2`. -/
theorem isSelfVisible_v2 : IsSelfVisible 2 (v2 : Label.{u}) := isSelfVisible_gridPoint 2 1
/-- The row value `2` is self-visible at `2`. -/
theorem isSelfVisible_w2 : IsSelfVisible 2 (w2 : Label.{u}) := isSelfVisible_gridPoint 2 0
/-- The row value `ω + 3` is self-visible at `3`. -/
theorem isSelfVisible_w3 : IsSelfVisible 3 (w3 : Label.{u}) := isSelfVisible_gridPoint 3 1

/-- The row value `2` is below `ω + 3`. -/
theorem w2_le_w3 : (w2 : Label.{u}) ≤ w3 := by
  rw [w2, w3, gridPoint, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
  exact (omega0_mul_add_natCast_lt (by simp) _ _).le

/-- **The rows are consistent**: the row of each cell is the labelling `lab` of parameters
satisfying the coupling, below the cell. -/
theorem isConsistent_rows : (rows.{u} b).IsConsistent := by
  intro s
  obtain ⟨As, Hs, Gs, hA, hH, hG, hcpl, hrow⟩ : ∃ As Hs Gs : Label.{u}, IsSelfVisible 1 As ∧
      IsSelfVisible 2 Hs ∧ IsSelfVisible 3 Gs ∧ Coupled b As Hs Gs ∧
      ∀ t, cells.gradedIndex t ≤ cells.gradedIndex s → rowVal b s t = lab As Hs Gs t := by
    rcases kind_cases s with hs | hs | rfl | rfl | rfl | rfl
    · refine ⟨⊥, ⊥, ⊥, isSelfVisible_bot 1, isSelfVisible_bot 2, isSelfVisible_bot 3,
        by cases b <;> simp [Coupled], fun t _ ↦ ?_⟩
      rw [rowVal_of_kind_zero_left hs, lab_bot]
    · refine ⟨v1, ⊥, ⊥, isSelfVisible_v1, isSelfVisible_bot 2, isSelfVisible_bot 3,
        by cases b <;> simp [Coupled], fun t ht ↦ ?_⟩
      by_cases hk : kind t = 0
      · rw [rowVal_of_kind_zero_right hk, lab_of_kind_zero hk]
      · rw [rowVal_of_kind_one hs hk, lab_of_kind_one (kind_of_le_kind_one s t hs hk ht)]
    · refine ⟨v2, v2, ⊥, isSelfVisible_v2.mono (by omega), isSelfVisible_v2,
        isSelfVisible_bot 3, by cases b <;> simp [Coupled], fun t ht ↦ ?_⟩
      by_cases hk : kind t = 0
      · rw [rowVal_of_kind_zero_right hk, lab_of_kind_zero hk]
      · obtain rfl := eq_of_le_thirteen t hk ht
        rw [rowVal_thirteen hk, lab_of_kind_two (by decide)]
    · cases b
      · refine ⟨v1, v2, ⊥, isSelfVisible_v1, isSelfVisible_v2, isSelfVisible_bot 3,
          by simp [Coupled], fun t ht ↦ ?_⟩
        by_cases hk : kind t = 0
        · rw [rowVal_of_kind_zero_right hk, lab_of_kind_zero hk]
        rcases kind_of_le_fifteen t hk ht with h1 | h2
        · rw [rowVal_fifteen_false_one h1, lab_of_kind_one h1]
        · rw [rowVal_fifteen_false_two h2, lab_of_kind_two h2]
      · refine ⟨v2, v2, ⊥, isSelfVisible_v2.mono (by omega), isSelfVisible_v2,
          isSelfVisible_bot 3, by simp [Coupled], fun t ht ↦ ?_⟩
        by_cases hk : kind t = 0
        · rw [rowVal_of_kind_zero_right hk, lab_of_kind_zero hk]
        rcases kind_of_le_fifteen t hk ht with h1 | h2
        · rw [rowVal_fifteen_true hk, lab_of_kind_one h1]
        · rw [rowVal_fifteen_true hk, lab_of_kind_two h2]
    · refine ⟨if b then w2 else ⊤, w2, w3, ?_, isSelfVisible_w2, isSelfVisible_w3, ?_,
        fun t ht ↦ ?_⟩
      · cases b
        · exact isSelfVisible_top 1
        · exact isSelfVisible_w2.mono (by omega)
      · cases b
        · simp [Coupled]
        · simp only [Coupled, ↓reduceIte, min_eq_left w2_le_w3]; exact ⟨le_rfl, le_rfl⟩
      by_cases hk : kind t = 0
      · rw [rowVal_of_kind_zero_right hk, lab_of_kind_zero hk]
      rcases eq_of_le_sixteen t hk ht with rfl | rfl
      · rw [rowVal_sixteen_two (by decide), lab_of_kind_two (by decide)]
      · rw [rowVal_sixteen_three (by decide), lab_of_kind_three (by decide)]
    · cases b
      · refine ⟨w3, w2, w3, isSelfVisible_w3.mono (by omega), isSelfVisible_w2,
          isSelfVisible_w3, by simp [Coupled], fun t _ ↦ ?_⟩
        by_cases hk : kind t = 0
        · rw [rowVal_of_kind_zero_right hk, lab_of_kind_zero hk]
        rw [rowVal_eighteen_false hk]
        rcases kind_live_cases t with h | h | h | h
        · exact absurd h hk
        · rw [lab_of_kind_one h, ite_eq_right (by rw [h]; decide)]
        · rw [lab_of_kind_two h, ite_eq_left h]
        · rw [lab_of_kind_three h, ite_eq_right (by rw [h]; decide)]
      · refine ⟨w2, w2, w3, isSelfVisible_w2.mono (by omega), isSelfVisible_w2,
          isSelfVisible_w3, ?_, fun t _ ↦ ?_⟩
        · simp only [Coupled, ↓reduceIte, min_eq_left w2_le_w3]; exact ⟨le_rfl, le_rfl⟩
        by_cases hk : kind t = 0
        · rw [rowVal_of_kind_zero_right hk, lab_of_kind_zero hk]
        rw [rowVal_eighteen_true hk]
        rcases kind_live_cases t with h | h | h | h
        · exact absurd h hk
        · rw [lab_of_kind_one h, ite_eq_right (by rw [h]; decide)]
        · rw [lab_of_kind_two h, ite_eq_right (by rw [h]; decide)]
        · rw [lab_of_kind_three h, ite_eq_left h]
  exact (isLawfulBelow_iff (Y := cells.gradedIndex s) (x := fun t ↦ rowVal b s t)).mpr
    ⟨As, Hs, Gs, hA, hH, hG, hcpl, fun t ht ↦ hrow t ht⟩

/-- The scheme is well formed: the interval plan and the nineteen cells. -/
theorem isWellFormed_S : (S.{u} b).IsWellFormed where
  ground_eq := rfl
  isWellFormed := TwoFaceLiftCounterexample.isWellFormed_S.{u}.isWellFormed

/-- The rows are coded: every value is `⊥` or a grid point below `ω ^ 2`. -/
theorem isCoded_S : (S.{u} b).IsCoded := by
  intro s t
  change rowVal b s t.1 < _
  unfold rowVal
  split_ifs <;> first
    | exact WithBot.bot_lt_coe _
    | exact gridPoint_lt_omega0_sq _ _

/-- **The scheme is legal below the full grade.** -/
theorem isLegalBelowFullGrade_S : (S.{u} b).IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isConsistent := isConsistent_rows
  isBountiful := isBountiful_rows
  grade_lt d := (by decide : ∀ d : Fin 19, cellGrade d < 4) d
  exists_gradedIndex_eq X hX hX4 := by
    obtain ⟨d, hd1, hd2⟩ := complete_below X.1 hX.1 X.2 hX4 hX.2.1 hX.2.2
    exact ⟨d, Prod.ext hd1 hd2⟩

/-! ### The two types -/

/-- The stage type of `S b` with every label `⊥`. -/
noncomputable def crossType₀ (b : Bool) (α : Ordinal.{u}) : StageType.{u} α 4 where
  toScheme := S b
  label _ := ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- The legal type on four points `S b` with the apex added. -/
noncomputable def crossType (b : Bool) (α : Ordinal.{u}) : StageType.{u} α 4 :=
  (crossType₀ b α).addApex isLegalBelowFullGrade_S (by omega)

/-- **The type `TH`**, coupled to the parameter `H` of the face and free of `G`. -/
noncomputable abbrev TH (α : Ordinal.{u}) : StageType.{u} α 4 := crossType true α

/-- **The type `TG`**, coupled to the parameter `G` of the face and free of `H`. -/
noncomputable abbrev TG (α : Ordinal.{u}) : StageType.{u} α 4 := crossType false α

/-- **The two types are legal.** -/
theorem isLegal_crossType (b : Bool) (α : Ordinal.{u}) : (crossType b α).IsLegal :=
  StageType.isLegal_addApex _ _

/-- **`TH` is legal.** -/
theorem isLegal_TH (α : Ordinal.{u}) : (TH α).IsLegal := isLegal_crossType true α

/-- **`TG` is legal.** -/
theorem isLegal_TG (α : Ordinal.{u}) : (TG α).IsLegal := isLegal_crossType false α

end VaughtConjecture.CrossedCouplingCounterexample
