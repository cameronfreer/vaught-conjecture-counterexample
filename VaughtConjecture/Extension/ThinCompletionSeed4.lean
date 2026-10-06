/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerStep
import VaughtConjecture.Extension.ThinCompletion

/-!
# The ordered-layer step for the seeds of `T4` below the top grade

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the ordered-layer step of `VaughtConjecture.Extension.OrderedLayerStep` below the top grade, for
every seed whose two coatom types are `T4`, such as `seed4`); semantic contract, items 2–4.

Let `I` be a seed on five points whose coatom types are both `T4`
(`VaughtConjecture.Extension.TwoFaceLiftCounterexample`), with coatoms `C = {0, 1, 2, 3}` and
`D = {0, 1, 2, 4}`.  On each coatom the lawful labellings of `T4` are `labelling A F`: `A` at the
live cells of grade `1` (those through the last point), `F` at the coatom at the grade `2`, and
`⊥` elsewhere; in particular `T4` has no live cell of grade `3`.

**The layer rows** (`layerRows4`).  The cells have four *kinds* (`kind4`, values in `Fin 6` read by
`ThinCompletion.kindLabel`): the dead cells; the live cells of grade `1` of `C`, carrying `A_C`;
those of `D` and the new cell at `(univ, 1)`, carrying `A_D`; the live cells of grade `2` and the
new cell at `(univ, 2)`, carrying `F`.  The rows at `(univ, 1)` and `(univ, 2)` are the ordered
rows `ThinCompletion.thinRow 1`, `ThinCompletion.thinRow 2` read through these kinds (the live
cells of grade `1` of `C` at `1`, those of `D` at `ω + 1`, the live cells of grade `2` at
`ω·2 + 2`); the row at `(univ, 3)` is `⊥` everywhere, and the row at `(univ, 4)` is the top row
`OrderedLayer.topRow`.

**The lawful labellings below `(univ, 3)`** are exactly the labellings `layerLabel4 I A_C A_D F`
(each cell carries the parameter of its kind; `⊥` at the new cell at `(univ, 3)`) with
`ThinCompletion.IsThinLawfulBelow A_C A_D F ⊥`: `A_C`, `A_D` self-visible at `1`, `F` at `2`,
`A_C ≤ A_D`, and no collision (`isLawfulBelow_layerLabel4`, `exists_of_isLawfulBelow_three4`).

**The step below the top grade** (`orderedLayerStepBelowTop_of`): the rows are coded, each row
at `(univ, k)`, `k ≤ 3`, is the labelling of the parameters of `isThinLawfulBelow_row_one`,
`isThinLawfulBelow_row_two`, or `⊥`, and the capped lifts from `(C, k)` and `(D, k)` into
`(univ, k)` reduce to lifts at the grade `3` (`OrderedLayer.cappedLift_of_lift_three`), which are
the parameter lifts of `ThinCompletion.exists_thinLift` with `G` prescribed `⊥`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.OrderedLayer.Seed4

open Finset Label CellScheme
open ThinCompletion (kindLabel thinRow thinRow_lt transformsTo_rowOne transformsTo_rowTwo
  IsThinLawfulBelow exists_thinLift isThinLawfulBelow_row_one isThinLawfulBelow_row_two)
open TwoFaceLiftCounterexample (T4 cells labelling live cellGrade liveC liveD pairKind)

/-! ### Kinds -/

/-- The **kind** of a graded index on five points: at the full scope, `A_D` at the grade `1`, `F`
at the grade `2`, and dead otherwise; at another scope, the kind of `pairKind` with `F_C` and `F_D`
merged into `F`. -/
def kind4 (X : Finset (Fin 5) × ℕ) : Fin 6 :=
  if X.1 = univ then (if X.2 = 1 then 2 else if X.2 = 2 then 3 else 0)
  else ![0, 1, 3, 2, 3] (pairKind X)

/-- The labelling of graded indices with the parameters `A_C`, `A_D`, `F`. -/
noncomputable def kindLabel4 (AC AD F : Label.{u}) (X : Finset (Fin 5) × ℕ) : Label.{u} :=
  kindLabel AC AD F ⊥ ⊥ (kind4 X)

private theorem liveC_snd : ∀ Y ∈ liveC, Y.2 = 1 ∨ Y.2 = 2 := by decide
private theorem liveD_snd : ∀ Y ∈ liveD, Y.2 = 1 ∨ Y.2 = 2 := by decide
private theorem liveC_three : ∀ Y ∈ liveC, (3 : Fin 5) ∈ Y.1 := by decide
private theorem liveD_four : ∀ Y ∈ liveD, (4 : Fin 5) ∈ Y.1 := by decide

/-- A graded index of a live kind has the grade of its kind (`ThinCompletion.kindGrade`). -/
theorem snd_eq_kindGrade {X : Finset (Fin 5) × ℕ} (hX : kind4 X ≠ 0) :
    X.2 = ThinCompletion.kindGrade (kind4 X) := by
  unfold kind4 at hX ⊢
  split_ifs at hX ⊢ with h1 h2 h3
  · simp only [h2]; rfl
  · simp only [h3]; rfl
  · exact (hX rfl).elim
  unfold pairKind at hX ⊢
  split_ifs at hX ⊢ with hC hC1 hD hD1
  · exact hC1
  · exact (liveC_snd X hC).resolve_left hC1
  · exact hD1
  · exact (liveD_snd X hD).resolve_left hD1
  · exact (hX rfl).elim

/-- Every kind is at most `3`. -/
theorem kind4_le_three (X : Finset (Fin 5) × ℕ) : (kind4 X : ℕ) ≤ 3 := by
  unfold kind4
  split_ifs
  all_goals try decide
  generalize pairKind X = c
  fin_cases c <;> decide

/-- At a grade at most `1`, the kind is at most `2`. -/
theorem kind4_le_two {X : Finset (Fin 5) × ℕ} (hX : X.2 ≤ 1) : (kind4 X : ℕ) ≤ 2 := by
  by_cases h : kind4 X = 0
  · rw [h]; exact Nat.zero_le _
  have hg := snd_eq_kindGrade h
  have := kind4_le_three X
  generalize kind4 X = c at h hg this ⊢
  fin_cases c <;> simp_all [ThinCompletion.kindGrade]

/-- A graded index whose scope misses the point `4` (on the coatom `C`) is not of the kind
`A_D`. -/
theorem kind4_ne_two {X : Finset (Fin 5) × ℕ} (hX : (4 : Fin 5) ∉ X.1) : kind4 X ≠ 2 := by
  unfold kind4
  split_ifs with h1 h2 h3
  · exact absurd (h1 ▸ mem_univ _) hX
  all_goals try decide
  unfold pairKind
  split_ifs with hC hC1 hD hD1 <;> try decide
  · exact absurd (liveD_four X hD) hX

/-- A graded index whose scope misses the point `3` (on the coatom `D`) is not of the kind
`A_C`. -/
theorem kind4_ne_one {X : Finset (Fin 5) × ℕ} (hX : (3 : Fin 5) ∉ X.1) : kind4 X ≠ 1 := by
  unfold kind4
  split_ifs with h1 h2 h3 <;> try decide
  unfold pairKind
  split_ifs with hC hC1 hD hD1 <;> try decide
  · exact absurd (liveC_three X hC) hX

/-- The labelling of graded indices does not read `A_D` at a graded index of another kind. -/
theorem kindLabel4_congr_two {X : Finset (Fin 5) × ℕ} (hX : kind4 X ≠ 2)
    (AC AD AD' F : Label.{u}) : kindLabel4 AC AD F X = kindLabel4 AC AD' F X := by
  unfold kindLabel4
  generalize kind4 X = c at hX
  fin_cases c <;> first | rfl | exact (hX rfl).elim

/-- The labelling of graded indices does not read `A_C` at a graded index of another kind. -/
theorem kindLabel4_congr_one {X : Finset (Fin 5) × ℕ} (hX : kind4 X ≠ 1)
    (AC AC' AD F : Label.{u}) : kindLabel4 AC AD F X = kindLabel4 AC' AD F X := by
  unfold kindLabel4
  generalize kind4 X = c at hX
  fin_cases c <;> first | rfl | exact (hX rfl).elim

/-- Two labellings whose parameters agree capped at `c` agree capped at `c`. -/
theorem min_kindLabel4_eq {c AC AD F AC' AD' F' : Label.{u}}
    (hAC : min AC c = min AC' c) (hAD : min AD c = min AD' c) (hF : min F c = min F' c)
    (X : Finset (Fin 5) × ℕ) :
    min (kindLabel4 AC AD F X) c = min (kindLabel4 AC' AD' F' X) c := by
  unfold kindLabel4
  generalize kind4 X = k
  fin_cases k
  exacts [rfl, hAC, hAD, hF, rfl, rfl]

/-- The new cell at `(univ, 1)` is of the kind `A_D`. -/
@[simp] theorem kind4_univ_one : kind4 ((univ : Finset (Fin 5)), 1) = 2 := by simp [kind4]
/-- The new cell at `(univ, 2)` is of the kind `F`. -/
@[simp] theorem kind4_univ_two : kind4 ((univ : Finset (Fin 5)), 2) = 3 := by simp [kind4]
/-- The new cell at `(univ, 3)` is dead. -/
@[simp] theorem kind4_univ_three : kind4 ((univ : Finset (Fin 5)), 3) = 0 := by simp [kind4]

/-- At a graded index of grade `k ≤ 3`, the labelling is at most its value at `(univ, k)`, when
`A_C ≤ A_D`. -/
theorem kindLabel4_le {AC AD F : Label.{u}} (hle : AC ≤ AD) {X : Finset (Fin 5) × ℕ}
    {k : ℕ} (hX : X.2 = k) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    kindLabel4 AC AD F X ≤ kindLabel4 AC AD F ((univ : Finset (Fin 5)), k) := by
  unfold kindLabel4
  by_cases h : kind4 X = 0
  · rw [h]; exact bot_le
  have hg := snd_eq_kindGrade h
  rw [hX] at hg
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals
    simp only [kind4_univ_one, kind4_univ_two, kind4_univ_three]
    have h3 := kind4_le_three X
    generalize kind4 X = c at h hg h3
    fin_cases c <;> first | exact absurd hg (by decide) | exact (h rfl).elim | exact le_rfl | skip
  all_goals exact hle

/-! ### The layer rows -/

/-- **The layer rows** of a seed whose coatom types are `T4`: the ordered rows at `(univ, 1)` and
`(univ, 2)` read through `kind4`, `⊥` at `(univ, 3)`, and the top row at `(univ, 4)`. -/
noncomputable def layerRows4 : LayerRows.{u}
  | 3 => fun _ ↦ ⊥
  | 4 => topRow
  | k => fun X ↦ thinRow k (kind4 X)

/-- The row at `(univ, 4)` is the top row. -/
theorem layerRows4_four : layerRows4.{u} 4 = topRow := rfl

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

variable (I) in
/-- The **layer labelling** of the cells of the layer scheme with the parameters `A_C`, `A_D`,
`F`, read off their graded indices. -/
noncomputable def layerLabel4 (AC AD F : Label.{u})
    (z : Fin (layerScheme I layerRows4.{u}).card) : Label.{u} :=
  kindLabel4 AC AD F ((layerScheme I layerRows4).toCellScheme.gradedIndex z)

/-- The layer labelling at the new cell at `(univ, k)`. -/
theorem layerLabel4_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (AC AD F : Label.{u}) :
    layerLabel4 I AC AD F (newCell I layerRows4 k) =
      kindLabel4 AC AD F ((univ : Finset (Fin 5)), k) := by
  rw [layerLabel4, gradedIndex_newCell hk1 hk4]

/-- A cell below the new cell at `(univ, k)` has grade at most `k`. -/
theorem grade_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I layerRows4.{u}).toCellScheme.below
      ((layerScheme I layerRows4).toCellScheme.gradedIndex (newCell I layerRows4 k))) :
    (layerScheme I layerRows4).toCellScheme.grade t.1 ≤ k := by
  have h : (layerScheme I layerRows4).toCellScheme.gradedIndex t.1 ≤
      ((univ : Finset (Fin 5)), k) := gradedIndex_newCell hk1 hk4 ▸ t.2
  exact h.2

/-! ### Lawful labellings of `T4` along a coatom -/

private theorem cases_T4 (i : Fin (T4 α).card) :
    i = Fin.last 19 ∨ ∃ d : Fin 19, i = Fin.castSucc d := by
  -- The cells of `T4`: the nineteen cells of the scheme, then the apex.
  change Fin (19 + 1) at i
  induction i using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- **Lawful labellings of an amalgam below a coatom whose type is `T4`**, read on `T4`: each cell
carries the value of `labelling A F` at a cell of `T4` with the same graded index. -/
theorem exists_labelling_of_comap_T4 {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T4 α)) {k : ℕ} (hk : k ≤ 3)
    (p : Fin Am.card → Label.{u}) (hp : Am.rows.IsLawfulBelow (univ.map f, k) fun d ↦ p d) :
    ∃ A F : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧
      ∀ d ∈ Am.toCellScheme.below (univ.map f, k), ∃ c : Fin 19,
        Am.toCellScheme.gradedIndex d = Prod.map (Finset.map f) id (cells.gradedIndex c) ∧
        p d = labelling A F c := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T4 α).toScheme := congrArg StageType.toScheme he
  have hgen : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), k) (fun i ↦ x i) →
      ∃ A F : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧
        ∀ i ∈ (Am.toScheme.comap f).toCellScheme.below ((univ : Finset (Fin 4)), k),
          ∃ c : Fin 19, (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex c ∧
            x i = labelling A F c := by
    rw [heq]
    intro x hx
    have hx' := (TwoFaceLiftCounterexample.isLawfulBelow_T4_iff (α := α) (w := x) (fun h ↦ by
      have := h.2; simp only at this; omega)).mp hx
    obtain ⟨A, F, hA, hF, hAF⟩ :=
      (TwoFaceLiftCounterexample.isLawfulBelow_iff (x := fun e ↦ x (Fin.castSucc e))).mp hx'
    refine ⟨A, F, hA, hF, fun i hi ↦ ?_⟩
    rcases cases_T4 (α := α) i with rfl | ⟨c, rfl⟩
    · exfalso
      have h2 := hi.2
      rw [TwoFaceLiftCounterexample.gradedIndex_T4_last] at h2
      simp only at h2
      omega
    · refine ⟨c, TwoFaceLiftCounterexample.gradedIndex_T4_castSucc c, hAF c ?_⟩
      -- The graded index of `c` in the scheme, which `T4` keeps.
      change cells.gradedIndex c ≤ _
      rw [← TwoFaceLiftCounterexample.gradedIndex_T4_castSucc (α := α) c]
      exact hi
  obtain ⟨A, F, hA, hF, hall⟩ := hgen (fun i ↦ p (Am.toScheme.cellMap f i))
    ((Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f _ p).mpr hp)
  refine ⟨A, F, hA, hF, fun d hd ↦ ?_⟩
  have hd' : d ∈ Am.toScheme.cellMap f '' (Am.toScheme.comap f).toCellScheme.below
      ((univ : Finset (Fin 4)), k) := by
    rw [Am.toScheme.image_cellMap_below f]; exact hd
  obtain ⟨i, hi, rfl⟩ := hd'
  obtain ⟨c, hgi, hpc⟩ := hall i hi
  exact ⟨c, by rw [← Am.toScheme.map_comap_gradedIndex f i, hgi], hpc⟩

/-- A cell of `T4` carried into the amalgam along a coatom whose face is `T4`. -/
theorem exists_cell_T4 {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T4 α)) (d : Fin 19) :
    ∃ e : Fin Am.card, Am.toCellScheme.gradedIndex e =
      Prod.map (Finset.map f) id (cells.gradedIndex d) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T4 α).toScheme := congrArg StageType.toScheme he
  obtain ⟨i, hi⟩ : ∃ i : Fin (Am.toScheme.comap f).card,
      (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex d := by
    rw [heq]; exact ⟨Fin.castSucc d, TwoFaceLiftCounterexample.gradedIndex_T4_castSucc d⟩
  exact ⟨Am.toScheme.cellMap f i, by rw [← Am.toScheme.map_comap_gradedIndex f i, hi]⟩

/-- The live kind of a cell of `T4`: dead, grade `1`, or grade `2`. -/
private def liveKind (d : Fin 19) : Fin 3 :=
  if live d = true then (if cellGrade d = 1 then 1 else 2) else 0

private theorem labelling_eq_liveKind (A F : Label.{u}) (d : Fin 19) :
    labelling A F d = ![⊥, A, F] (liveKind d) := by
  unfold labelling liveKind
  split_ifs <;> rfl

private theorem kind4_left : ∀ d : Fin 19,
    kind4 (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex d)) =
      ![0, 1, 3] (liveKind d) := by
  decide +kernel

private theorem kind4_right : ∀ d : Fin 19,
    kind4 (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex d)) =
      ![0, 2, 3] (liveKind d) := by
  decide +kernel

/-- Read along the first coatom, the labelling of graded indices is `labelling A_C F`. -/
theorem kindLabel4_left (AC AD F : Label.{u}) (d : Fin 19) :
    kindLabel4 AC AD F (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex d)) =
      labelling AC F d := by
  rw [kindLabel4, kind4_left, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

/-- Read along the second coatom, the labelling of graded indices is `labelling A_D F`. -/
theorem kindLabel4_right (AC AD F : Label.{u}) (d : Fin 19) :
    kindLabel4 AC AD F (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex d)) =
      labelling AD F d := by
  rw [kindLabel4, kind4_right, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

section Coatoms

variable (hIL : I.left = T4 α) (hIR : I.right = T4 α)

include hIL in
/-- **Lawful labellings below `(C, 3)` in the layer scheme**: `layerLabel4 I A ⊥ F`. -/
theorem exists_of_isLawfulBelow_left {w : Fin (layerScheme I layerRows4.{u}).card → Label.{u}}
    (hw : (layerScheme I layerRows4).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z) :
    ∃ A F : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧
      ∀ z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomC, 3),
        w z = layerLabel4 I A ⊥ F z := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomC_eq] at hw'
  obtain ⟨A, F, hA, hF, hall⟩ :=
    exists_labelling_of_comap_T4 (hIL ▸ I.restrictFace_left) le_rfl
      (fun d ↦ w (oldCell I layerRows4 d)) hw'
  refine ⟨A, F, hA, hF, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ := (image_oldCell_below (I := I) (ρ := layerRows4)
    (X := (coatomC, 3)) (by decide)).symm ▸ hz
  rw [coatomC_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, layerLabel4, gradedIndex_oldCell, hgi, kindLabel4_left]

include hIR in
/-- **Lawful labellings below `(D, 3)` in the layer scheme**: `layerLabel4 I ⊥ A F`. -/
theorem exists_of_isLawfulBelow_right {w : Fin (layerScheme I layerRows4.{u}).card → Label.{u}}
    (hw : (layerScheme I layerRows4).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z) :
    ∃ A F : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧
      ∀ z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomD, 3),
        w z = layerLabel4 I ⊥ A F z := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomD_eq] at hw'
  obtain ⟨A, F, hA, hF, hall⟩ :=
    exists_labelling_of_comap_T4 (hIR ▸ I.restrictFace_right) le_rfl
      (fun d ↦ w (oldCell I layerRows4 d)) hw'
  refine ⟨A, F, hA, hF, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ := (image_oldCell_below (I := I) (ρ := layerRows4)
    (X := (coatomD, 3)) (by decide)).symm ▸ hz
  rw [coatomD_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, layerLabel4, gradedIndex_oldCell, hgi, kindLabel4_right]

include hIL in
/-- The old cell at a graded index of the first coatom. -/
theorem exists_oldCell_left (c : Fin 19) :
    ∃ d : Fin I.amalgam.card, I.amalgam.toCellScheme.gradedIndex d =
      Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex c) :=
  exists_cell_T4 (hIL ▸ I.restrictFace_left) c

include hIR in
/-- The old cell at a graded index of the second coatom. -/
theorem exists_oldCell_right (c : Fin 19) :
    ∃ d : Fin I.amalgam.card, I.amalgam.toCellScheme.gradedIndex d =
      Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex c) :=
  exists_cell_T4 (hIR ▸ I.restrictFace_right) c

/-! ### Sufficiency -/

include hIL hIR in
/-- **The layer labellings are lawful below the coatoms** at the grade `3`: read along each
coatom they are labellings of `T4`. -/
theorem isLawfulBelow_coatom_layerLabel4 {AC AD F : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hAD : IsSelfVisible 1 AD) (hF : IsSelfVisible 2 F) :
    (layerScheme I layerRows4).rows.IsLawfulBelow (coatomC, 3)
        (fun z ↦ layerLabel4 I AC AD F z) ∧
      (layerScheme I layerRows4).rows.IsLawfulBelow (coatomD, 3)
        (fun z ↦ layerLabel4 I AC AD F z) := by
  have hCD := TwoFaceLiftCounterexample.isLawfulBelow_pairLabelling (I := I) hIL hIR hAC hF hAD hF
  have key (d : Fin I.amalgam.card) :
      layerLabel4 I AC AD F (oldCell I layerRows4 d) =
        TwoFaceLiftCounterexample.pairLabelling AC F AD F
          (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [layerLabel4, gradedIndex_oldCell, kindLabel4, TwoFaceLiftCounterexample.pairLabelling,
      kind4,
      ite_eq_right (show (I.amalgam.toCellScheme.gradedIndex d).1 ≠ univ from I.scope_ne_univ d)]
    generalize pairKind (I.amalgam.toCellScheme.gradedIndex d) = c
    fin_cases c <;> rfl
  constructor
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomC, 3))
      fun d _ ↦ (key d).symm).mp hCD.1
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomD, 3))
      fun d _ ↦ (key d).symm).mp hCD.2

include hIL hIR in
/-- **Sufficiency**: the layer labelling of parameters satisfying `IsThinLawfulBelow A_C A_D F ⊥`
is lawful below `(univ, 3)`. -/
theorem isLawfulBelow_layerLabel4 {AC AD F : Label.{u}} (h : IsThinLawfulBelow AC AD F ⊥) :
    (layerScheme I layerRows4).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      (fun z ↦ layerLabel4 I AC AD F z) := by
  obtain ⟨hC, hD⟩ := isLawfulBelow_coatom_layerLabel4 hIL hIR h.svAC h.svAD h.svF
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hD
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hne : (layerScheme I layerRows4).toCellScheme.scope d = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hd.2
      rw [grade_newCell hj1 hj4, layerLabel4_newCell hj1 hj4]
      obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact h.svAD
      · exact h.svF
      · exact isSelfVisible_bot _
    · exact (mem_below_coatom_of_ne hd hne).elim (hoC d) (hoD d)
  · rcases cell_cases s with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
    · exact (mem_below_coatom_of_ne hs (scope_oldCell_ne d)).elim (hlC _) (hlD _)
    · rw [row_newCell_eq le_rfl (by omega), layerLabel4_newCell le_rfl (by omega)]
      exact transformsTo_rowOne _
        (fun t ↦ kind4 ((layerScheme I layerRows4).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell le_rfl (by omega))
        (fun t ↦ kind4_le_two (X := (layerScheme I layerRows4).toCellScheme.gradedIndex t.1)
          (grade_le_of_mem_below_newCell (I := I) le_rfl (by omega) t))
        h.svAC h.svAD h.le_AD
    · rw [row_newCell_eq (by omega) (by omega), layerLabel4_newCell (by omega) (by omega)]
      exact transformsTo_rowTwo _
        (fun t ↦ kind4 ((layerScheme I layerRows4).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega)) (fun t ↦ kind4_le_three _)
        h.svAC h.svAD h.svF h.le_AD h.noCollision
    · rw [layerLabel4_newCell (by omega) (by omega)]
      -- The label of the new cell at `(univ, 3)` is `kindLabel` at the kind `0`, which is `⊥`.
      change TransformsTo _ _ fun d ↦ min _ (kindLabel AC AD F ⊥ ⊥ 0)
      simp only [kindLabel, Matrix.cons_val_zero, min_bot_right]
      exact TransformsTo.bot _ _
    · have h4 : (layerScheme I layerRows4).toCellScheme.gradedIndex (newCell I layerRows4 4) ≤
          ((univ : Finset (Fin 5)), 3) := hs
      rw [gradedIndex_newCell (by omega) le_rfl] at h4
      exact absurd h4.2 (by decide)
  · by_cases hne : (layerScheme I layerRows4).toCellScheme.scope t = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le ht.2
      refine ⟨newCell I layerRows4 j, rfl, ?_⟩
      rw [layerLabel4_newCell hj1 hj4]
      exact kindLabel4_le h.le_AD (hg.trans (grade_newCell hj1 hj4)) hj1 hj3
    · exact (mem_below_coatom_of_ne ht hne).elim (haC s t · hst hg) (haD s t · hst hg)

/-! ### Necessity -/

/-- A cell below `(C, k)` misses the point `4`. -/
theorem four_notMem_of_mem_below {z : Fin (layerScheme I layerRows4.{u}).card} {k : ℕ}
    (hz : z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomC, k)) :
    (4 : Fin 5) ∉ ((layerScheme I layerRows4).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.last 4) univ) (hz.1 h)

/-- A cell below `(D, k)` misses the point `3`. -/
theorem three_notMem_of_mem_below {z : Fin (layerScheme I layerRows4.{u}).card} {k : ℕ}
    (hz : z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomD, k)) :
    (3 : Fin 5) ∉ ((layerScheme I layerRows4).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.castSucc (Fin.last 3)) univ) (hz.1 h)

/-- An old cell below the new cell at `(univ, k)`, of grade at most `k`. -/
theorem oldCell_mem_below_newCell {d : Fin I.amalgam.card} {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hd : I.amalgam.toCellScheme.grade d ≤ k) :
    oldCell I layerRows4.{u} d ∈ (layerScheme I layerRows4).toCellScheme.below
      ((layerScheme I layerRows4).toCellScheme.gradedIndex (newCell I layerRows4 k)) := by
  rw [gradedIndex_newCell hk1 hk4]
  exact oldCell_mem_below ⟨subset_univ _, hd⟩

/-- The new cell at `(univ, k)` is below itself. -/
theorem newCell_mem_below_self {k : ℕ} :
    newCell I layerRows4.{u} k ∈ (layerScheme I layerRows4).toCellScheme.below
      ((layerScheme I layerRows4).toCellScheme.gradedIndex (newCell I layerRows4 k)) :=
  (layerScheme I layerRows4).toCellScheme.mem_below_gradedIndex _

include hIL hIR in
/-- **Necessity**: every labelling lawful below `(univ, 3)` is a layer labelling, of parameters
satisfying `IsThinLawfulBelow A_C A_D F ⊥`.  On each coatom it is a labelling of `T4`; locality and
availability at the new cells identify `A_D` and `F` (on both coatoms) with their labels, and give
`A_C ≤ A_D`; the new cell at `(univ, 3)`, whose row is `⊥`, carries `⊥`; and the collision lemma at
the new cell at `(univ, 2)` gives the exclusion of collisions. -/
theorem exists_of_isLawfulBelow_three4 {w : Fin (layerScheme I layerRows4.{u}).card → Label.{u}}
    (hw : (layerScheme I layerRows4).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun z ↦ w z) :
    ∃ AC AD F : Label.{u}, IsThinLawfulBelow AC AD F ⊥ ∧
      ∀ z ∈ (layerScheme I layerRows4).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        w z = layerLabel4 I AC AD F z := by
  -- Step 1: below each coatom, `w` is a labelling of `T4`.
  have hC : (layerScheme I layerRows4).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z :=
    hw.mono (X := (coatomC, 3)) ⟨subset_univ _, le_rfl⟩
  have hD : (layerScheme I layerRows4).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z :=
    hw.mono (X := (coatomD, 3)) ⟨subset_univ _, le_rfl⟩
  obtain ⟨AC, FC, hAC, hFC, hC'⟩ := exists_of_isLawfulBelow_left hIL hC
  obtain ⟨AD, FD, hAD, hFD, hD'⟩ := exists_of_isLawfulBelow_right hIR hD
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  -- Step 2: the old cells used, one of each live kind, and their labels.
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hw₁ : w (oldCell I layerRows4 d₁) = AC := by
    rw [hC' _ (oldCell_mem_below (by rw [hd₁]; decide)), layerLabel4, gradedIndex_oldCell, hd₁]
    rfl
  have hwsC : w (oldCell I layerRows4 sC) = FC := by
    rw [hC' _ (oldCell_mem_below (by rw [hsC]; decide)), layerLabel4, gradedIndex_oldCell, hsC]
    rfl
  have hw₂ : w (oldCell I layerRows4 d₂) = AD := by
    rw [hD' _ (oldCell_mem_below (by rw [hd₂]; decide)), layerLabel4, gradedIndex_oldCell, hd₂]
    rfl
  have hwsD : w (oldCell I layerRows4 sD) = FD := by
    rw [hD' _ (oldCell_mem_below (by rw [hsD]; decide)), layerLabel4, gradedIndex_oldCell, hsD]
    rfl
  -- Step 3: locality and availability at the new cells at `(univ, 1)` and `(univ, 2)`.
  have hrow {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      (layerScheme I layerRows4).rows.row (newCell I layerRows4 k)
          ⟨oldCell I layerRows4 d, oldCell_mem_below_newCell hk1 (by omega) hd⟩ =
        thinRow k (kind4 (I.amalgam.toCellScheme.gradedIndex d)) := by
    rw [row_newCell hk1 (by omega), gradedIndex_oldCell]
    obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    all_goals rfl
  have hrowself {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
      (layerScheme I layerRows4).rows.row (newCell I layerRows4 k)
          ⟨newCell I layerRows4 k, newCell_mem_below_self⟩ =
        thinRow k (kind4 ((univ : Finset (Fin 5)), k)) := by
    rw [row_newCell hk1 (by omega), gradedIndex_newCell hk1 (by omega)]
    obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
    all_goals rfl
  have hle {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k)
      (hr : thinRow k (kind4 ((univ : Finset (Fin 5)), k)) ≤
        thinRow k (kind4 (I.amalgam.toCellScheme.gradedIndex d))) :
      w (newCell I layerRows4 k) ≤ w (oldCell I layerRows4 d) := by
    have := (hl _ (newCell_mem_below hk1 (by omega) (by omega : k ≤ 3))).le_of_le
      (d := ⟨newCell I layerRows4 k, newCell_mem_below_self⟩)
      (d' := ⟨oldCell I layerRows4 d, oldCell_mem_below_newCell hk1 (by omega) hd.le⟩)
      (by rw [hrowself hk1 hk2, hrow hk1 hk2 hd.le]; exact hr)
      (show (layerScheme I layerRows4).toCellScheme.grade (oldCell I layerRows4 d) ≤
          (layerScheme I layerRows4).toCellScheme.grade (newCell I layerRows4 k) by
        rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have hge {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k) :
      w (oldCell I layerRows4 d) ≤ w (newCell I layerRows4 k) := by
    obtain ⟨u, hu, hle⟩ := ha (oldCell I layerRows4 d) (newCell I layerRows4 k)
      (newCell_mem_below hk1 (by omega) hk3)
      (by rw [scope_newCell hk1 (by omega)]; exact subset_univ _)
      (by rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    rwa [eq_newCell hk1 (by omega) (hu.trans (gradedIndex_newCell hk1 (by omega)))] at hle
  have hn₁ : w (newCell I layerRows4 1) = AD := by
    rw [← hw₂]
    exact le_antisymm (hle le_rfl (by omega) (congrArg Prod.snd hd₂) (by rw [hd₂]; rfl))
      (hge le_rfl (by omega) (congrArg Prod.snd hd₂))
  have hn₂C : w (newCell I layerRows4 2) = FC := by
    rw [← hwsC]
    exact le_antisymm (hle (by omega) le_rfl (congrArg Prod.snd hsC) (by rw [hsC]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsC))
  have hn₂D : w (newCell I layerRows4 2) = FD := by
    rw [← hwsD]
    exact le_antisymm (hle (by omega) le_rfl (congrArg Prod.snd hsD) (by rw [hsD]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsD))
  have hACAD : AC ≤ AD := hw₁ ▸ hn₁ ▸ hge le_rfl (by omega) (congrArg Prod.snd hd₁)
  have hFCD : FC = FD := hn₂C.symm.trans hn₂D
  -- The new cell at `(univ, 3)` reads `⊥` at itself, so it carries `⊥`.
  have hn₃ : w (newCell I layerRows4 3) = ⊥ := by
    have hrow3 : (layerScheme I layerRows4).rows.row (newCell I layerRows4 3)
        ⟨newCell I layerRows4 3, newCell_mem_below_self⟩ = ⊥ := by
      rw [row_newCell (by omega) (by omega)]; rfl
    have := (hl _ (newCell_mem_below (by omega) (by omega) le_rfl)).eq_bot
      (d := ⟨newCell I layerRows4 3, newCell_mem_below_self⟩) hrow3
    simpa using this
  -- Step 4: no collision, by the collision lemma at the new cell at `(univ, 2)`.
  have hnc : AC = AD → AC < FC → IsSelfVisible 2 AC := by
    intro heq hlt
    by_contra hev
    have hg₁' : I.amalgam.toCellScheme.grade d₁ = 1 := congrArg Prod.snd hd₁
    have hg₂' : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
    have hg₁ : I.amalgam.toCellScheme.grade d₁ ≤ 2 := by omega
    have hg₂ : I.amalgam.toCellScheme.grade d₂ ≤ 2 := by omega
    have := Label.eq_of_transformsTo_collision
      (hl _ (newCell_mem_below (by omega) (by omega) (by omega)))
      (d₁ := ⟨oldCell I layerRows4 d₁, oldCell_mem_below_newCell (by omega) (by omega) hg₁⟩)
      (d₂ := ⟨oldCell I layerRows4 d₂, oldCell_mem_below_newCell (by omega) (by omega) hg₂⟩)
      (z := ⟨newCell I layerRows4 2, newCell_mem_below_self⟩)
      ((grade_oldCell d₁).trans hg₁') ((grade_oldCell d₂).trans hg₂')
      (grade_newCell (by omega) (by omega))
      (by rw [hrow (by omega) le_rfl hg₁, hd₁]; exact isSelfVisible_gridPoint 1 0)
      (by rw [hrow (by omega) le_rfl hg₂, hd₂]; exact isSelfVisible_gridPoint 1 1)
      (e := AC) (by simp only; rw [hw₁, hn₂C, min_eq_left hlt.le])
      (by simp only; rw [hw₂, hn₂C, ← heq, min_eq_left hlt.le]) hev
      (by simp only; rw [hn₂C, min_self]; exact hlt)
    rw [hrow (by omega) le_rfl hg₁, hrow (by omega) le_rfl hg₂, hd₁, hd₂] at this
    exact absurd this (gridPoint_lt_gridPoint.mpr (by omega)).ne
  -- Step 5: `w` is the layer labelling of these parameters.
  refine ⟨AC, AD, FC, ⟨hAC, hAD, hFC, isSelfVisible_bot 3, hACAD, bot_le, bot_le,
    fun h ↦ absurd h not_lt_bot, hnc⟩, fun z hz ↦ ?_⟩
  by_cases hne : (layerScheme I layerRows4).toCellScheme.scope z = univ
  · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
    have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hz.2
    rw [layerLabel4_newCell hj1 hj4]
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · exact hn₁
    · exact hn₂C
    · exact hn₃
  · rcases mem_below_coatom_of_ne hz hne with h | h
    · rw [hC' z h, layerLabel4, layerLabel4]
      exact kindLabel4_congr_two (kind4_ne_two (four_notMem_of_mem_below h)) _ _ _ _
    · rw [hD' z h, layerLabel4, layerLabel4, ← hFCD]
      exact kindLabel4_congr_one (kind4_ne_one (three_notMem_of_mem_below h)) _ _ _ _

/-! ### The lifts -/

/-- A property of `a` holds at every member of `some a`. -/
private theorem forall_mem_some {β : Type*} {a : β} {P : β → Prop} (h : P a) :
    ∀ b ∈ some a, P b :=
  fun _ hb ↦ (Option.some_inj.mp hb) ▸ h

/-- Every property holds at every member of `none`. -/
private theorem forall_mem_none {β : Type*} {P : β → Prop} : ∀ b ∈ (none : Option β), P b :=
  fun _ hb ↦ by cases hb

/-- `VisibilityReplaceFixedOfLT A ⊥` holds: nothing lies below `⊥`. -/
private theorem visibilityReplaceFixed_bot (A : Label.{u}) :
    TwoFaceLiftExistsCounterexample.VisibilityReplaceFixedOfLT A ⊥ :=
  fun h ↦ absurd h not_lt_bot

include hIL hIR in
/-- **The lift from `(C, 3)` to `(univ, 3)`** for labellings vanishing above a grade `k ≥ 1`, at a
cap self-visible at `k`: the parameters of the prescription (`T4`) and of the ambient are lifted
by `ThinCompletion.exists_thinLift`, with `A_D` unprescribed and `G` prescribed `⊥`. -/
theorem exists_lift_left {k : ℕ} (hk1 : 1 ≤ k) {c : Label.{u}} (hc : IsSelfVisible k c)
    {p q : Fin (layerScheme I layerRows4.{u}).card → Label.{u}}
    (hp : (layerScheme I layerRows4).rows.IsLawfulBelow (coatomC, 3) fun z ↦ p z)
    (hq : (layerScheme I layerRows4).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun z ↦ q z)
    (hpk : ∀ z, k < (layerScheme I layerRows4).toCellScheme.grade z → p z = ⊥)
    (hpq : ∀ z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomC, 3),
      min (q z) c = min (p z) c) :
    ∃ x : Fin (layerScheme I layerRows4).card → Label.{u},
      (layerScheme I layerRows4).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
        (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I layerRows4).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomC, 3), x z = p z := by
  obtain ⟨Ap, Fp, hAp, hFp, hp'⟩ := exists_of_isLawfulBelow_left hIL hp
  obtain ⟨qAC, qAD, qF, hq', hqz⟩ := exists_of_isLawfulBelow_three4 hIL hIR hq
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₁ : oldCell I layerRows4 d₁ ∈ (layerScheme I layerRows4).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hd₁]; decide)
  have hs : oldCell I layerRows4 sC ∈ (layerScheme I layerRows4).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hsC]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomC, 3)) :
      z ∈ (layerScheme I layerRows4).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  have hAq : min Ap c = min qAC c := by
    have := hpq _ h₁
    rw [hp' _ h₁, hqz _ (hmem h₁), layerLabel4, layerLabel4, gradedIndex_oldCell, hd₁] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), layerLabel4, layerLabel4, gradedIndex_oldCell, hsC] at this
    exact this.symm
  have hc2 : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    rcases (show 2 ≤ k ∨ k = 1 by omega) with h2 | rfl
    · exact .inl (hc.mono h2)
    · refine .inr (congrArg some ?_)
      have hg : I.amalgam.toCellScheme.grade sC = 2 := congrArg Prod.snd hsC
      have := hpk (oldCell I layerRows4 sC) (by rw [grade_oldCell (ρ := layerRows4), hg]; omega)
      rw [hp' _ hs, layerLabel4, gradedIndex_oldCell, hsC] at this
      exact this
  obtain ⟨xAC, xAD, xF, xG, hx, hxAC, hxAD, hxF, -, hpAC, -, hpF, hpG⟩ :=
    exists_thinLift (hc.mono hk1) (PAC := some Ap) (PAD := none) (PF := some Fp) (PG := some ⊥)
      hc2 (.inr rfl) hq' (forall_mem_some hAp) forall_mem_none (forall_mem_some hFp)
      (forall_mem_some (isSelfVisible_bot 3)) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some bot_le)) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some (visibilityReplaceFixed_bot Ap)))
      (forall_mem_some forall_mem_none)
      (forall_mem_some hAq) forall_mem_none (forall_mem_some hFq) (forall_mem_some rfl)
  obtain rfl := hpG ⊥ rfl
  refine ⟨layerLabel4 I xAC xAD xF, isLawfulBelow_layerLabel4 hIL hIR hx, fun z hz ↦ ?_,
    fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_kindLabel4_eq hxAC hxAD hxF _
  · rw [hp' z hz, layerLabel4, layerLabel4, hpAC Ap rfl, hpF Fp rfl]
    exact kindLabel4_congr_two (kind4_ne_two (four_notMem_of_mem_below hz)) _ _ _ _

include hIL hIR in
/-- **The lift from `(D, 3)` to `(univ, 3)`** for labellings vanishing above a grade `k ≥ 1`, at a
cap self-visible at `k`: as `exists_lift_left`, with `A_C` unprescribed. -/
theorem exists_lift_right {k : ℕ} (hk1 : 1 ≤ k) {c : Label.{u}} (hc : IsSelfVisible k c)
    {p q : Fin (layerScheme I layerRows4.{u}).card → Label.{u}}
    (hp : (layerScheme I layerRows4).rows.IsLawfulBelow (coatomD, 3) fun z ↦ p z)
    (hq : (layerScheme I layerRows4).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun z ↦ q z)
    (hpk : ∀ z, k < (layerScheme I layerRows4).toCellScheme.grade z → p z = ⊥)
    (hpq : ∀ z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomD, 3),
      min (q z) c = min (p z) c) :
    ∃ x : Fin (layerScheme I layerRows4).card → Label.{u},
      (layerScheme I layerRows4).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
        (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I layerRows4).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomD, 3), x z = p z := by
  obtain ⟨Ap, Fp, hAp, hFp, hp'⟩ := exists_of_isLawfulBelow_right hIR hp
  obtain ⟨qAC, qAD, qF, hq', hqz⟩ := exists_of_isLawfulBelow_three4 hIL hIR hq
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₂ : oldCell I layerRows4 d₂ ∈ (layerScheme I layerRows4).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hd₂]; decide)
  have hs : oldCell I layerRows4 sD ∈ (layerScheme I layerRows4).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hsD]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I layerRows4).toCellScheme.below (coatomD, 3)) :
      z ∈ (layerScheme I layerRows4).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  have hAq : min Ap c = min qAD c := by
    have := hpq _ h₂
    rw [hp' _ h₂, hqz _ (hmem h₂), layerLabel4, layerLabel4, gradedIndex_oldCell, hd₂] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), layerLabel4, layerLabel4, gradedIndex_oldCell, hsD] at this
    exact this.symm
  have hc2 : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    rcases (show 2 ≤ k ∨ k = 1 by omega) with h2 | rfl
    · exact .inl (hc.mono h2)
    · refine .inr (congrArg some ?_)
      have hg : I.amalgam.toCellScheme.grade sD = 2 := congrArg Prod.snd hsD
      have := hpk (oldCell I layerRows4 sD) (by rw [grade_oldCell (ρ := layerRows4), hg]; omega)
      rw [hp' _ hs, layerLabel4, gradedIndex_oldCell, hsD] at this
      exact this
  obtain ⟨xAC, xAD, xF, xG, hx, hxAC, hxAD, hxF, -, -, hpAD, hpF, hpG⟩ :=
    exists_thinLift (hc.mono hk1) (PAC := none) (PAD := some Ap) (PF := some Fp) (PG := some ⊥)
      hc2 (.inr rfl) hq' forall_mem_none (forall_mem_some hAp) (forall_mem_some hFp)
      (forall_mem_some (isSelfVisible_bot 3)) forall_mem_none
      (forall_mem_some (forall_mem_some bot_le)) (forall_mem_some (forall_mem_some bot_le))
      forall_mem_none forall_mem_none
      forall_mem_none (forall_mem_some hAq) (forall_mem_some hFq) (forall_mem_some rfl)
  obtain rfl := hpG ⊥ rfl
  refine ⟨layerLabel4 I xAC xAD xF, isLawfulBelow_layerLabel4 hIL hIR hx, fun z hz ↦ ?_,
    fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_kindLabel4_eq hxAC hxAD hxF _
  · rw [hp' z hz, layerLabel4, layerLabel4, hpAD Ap rfl, hpF Fp rfl]
    exact kindLabel4_congr_one (kind4_ne_one (three_notMem_of_mem_below hz)) _ _ _ _

/-! ### The ordered-layer step below the top grade -/

include hIL hIR in
/-- **The ordered-layer step below the top grade for the seeds of `T4`**: with the layer rows
`layerRows4`, the rows at `(univ, k)`, `k ≤ 3`, are coded and consistent, and the rows lift capped
from `(C, k)` and `(D, k)` into `(univ, k)`. -/
theorem orderedLayerStepBelowTop_of : I.OrderedLayerStepBelowTop layerRows4.{u} where
  row_lt k hk1 hk3 z _ := by
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact thinRow_lt 1 _
    · exact thinRow_lt 2 _
    · exact WithBot.bot_lt_coe _
  isLawfulBelow_row k hk1 hk3 := by
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact (isLawfulBelow_layerLabel4 hIL hIR isThinLawfulBelow_row_one).mono
        (X := ((univ : Finset (Fin 5)), 1)) ⟨subset_rfl, by omega⟩
    · exact (isLawfulBelow_layerLabel4 hIL hIR isThinLawfulBelow_row_two).mono
        (X := ((univ : Finset (Fin 5)), 2)) ⟨subset_rfl, by omega⟩
    · exact Rows.isLawfulBelow_const_bot _
  cappedLift_left k hk1 hk3 :=
    cappedLift_of_lift_three hk3 fun _ hc _ _ hp hq hpk _ hpq ↦
      exists_lift_left hIL hIR hk1 hc hp hq hpk hpq
  cappedLift_right k hk1 hk3 :=
    cappedLift_of_lift_three hk3 fun _ hc _ _ hp hq hpk _ hpq ↦
      exists_lift_right hIL hIR hk1 hc hp hq hpk hpq

end Coatoms

/-- **The ordered-layer step below the top grade for `seed4`.** -/
theorem orderedLayerStepBelowTop_seed4 (α : Ordinal.{u}) :
    (TwoFaceLiftCounterexample.seed4 α).OrderedLayerStepBelowTop layerRows4.{u} :=
  orderedLayerStepBelowTop_of rfl rfl

end VaughtConjecture.OrderedLayer.Seed4
