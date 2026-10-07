/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TwoFaceLiftCounterexample
import VaughtConjecture.Extension.TwoFaceLiftExists

/-!
# A legal seed outside the case split `2FL(j) ∨ DeadAt j`, with its completion

Roadmap, Layer 3, 3.1, (R6), checkpoints 2.6 and 2.7 (the recursion on the grade; here a legal
seed for which neither per-seed hypothesis of the library holds at the grade `2`, and its
completion through the existential two-face lift); semantic contract, items 2–4.

The step of the tower from the grade `j` to `j + 1` is proved under the two-face lift `2FL(j)`
(`Seed.towerInvariant_succ`) and when the old cells of the grade `j + 1` are dead
(`Seed.towerInvariant_succ_of_dead`); its hypothesis, stated exactly, is the existential two-face
lift `2FL∃(j)` (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`, for `j ≤ m` and under the
invariant at `j`; module `VaughtConjecture.Extension.TwoFaceLiftExists`).  This module shows that
the case split `2FL(j) ∨ Seed.DeadAt j` at the grades `2 ≤ j < m` does not cover every legal seed,
at every stage (`not_forall_twoFaceLift_or_deadAt`), and that the completion below the full grade
of the seed exhibited exists (`nonempty_completionBelowFullGrade_seed5`): the case split is refuted
as a statement of coverage, the completion is not.

**The legal type `T5`** (`T5`, `isLegal_T5`).  The scheme on four points has the cells of the type
`T4` of the module `VaughtConjecture.Extension.TwoFaceLiftCounterexample` (the interval plan and
one cell at every graded face of grade at most `3`, nineteen cells), and `T5` is it with the apex
added (`StageType.addApex`).  The *live* cells are those of `T4` (the cells of grade `1` whose scope
contains the point `3`, and the cell at `(univ, 2)`) together with the cells of grade `3` at
`{0, 1, 2}` and at `univ`; the other cells are *dead*.  The row of a dead cell is `⊥`; a live cell
of grade at most `2` reads as in `T4` (the live cells of grade `1` at the ordinal `1`, the live
cell of grade `2` at `ω + 2`, the dead cells at `⊥`); a live cell of grade `3` reads every live
cell below it at the ordinal `3`.

**The lawful labellings** (`isLawfulBelow_iff`).  Below every pair, the lawful labellings are the
restrictions of `labelling A F G`: `⊥` at the dead cells and `A`, `F`, `G` at the live cells of
grade `1`, `2`, `3`, for `A`, `F`, `G` self-visible at `1`, `2`, `3` with `G ≤ A` and `G ≤ F`.  The
coupling `G ≤ A`, `G ≤ F` is forced by locality at the cell at `(univ, 3)`, whose row reads every
live cell at one value.  Sufficiency uses at a live cell of grade `3` the top shifter with the
suppressor `G` up to the grade `3`, and at the live cell of grade `2` the *strip shifter* of `A`
(`TwoFaceLiftCounterexample.stripShifter`), which sends the natural numbers to the *strip* of `A`,
the labels `visibilityReplace 2 i A` for `i = 0, 1, 2`.  Every pair lifts capped to every larger
one (`cappedLift_all`), so `T5` is legal.

**The seed** (`seed5`).  The seed of `T5` with itself over its face `{0, 1, 2}`
(`Seed.ofCoatoms`) has coatoms `C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}` and common face
`E = {0, 1, 2}`, which carries one live cell, at `({0, 1, 2}, 3)`.  The labellings of the amalgam
used are read off graded indices (`tripleLabelling A_C F_C A_D F_D G`, lawful below both coatoms at
the grade `3` when `G` is at most each other parameter, `isLawfulBelow_tripleLabelling`).  The
statements are proved for every seed on five points whose two coatom types are `T5`
(`I.left = T5 α`, `I.right = T5 α`) and specialized to `seed5` by `rfl`.

**Neither per-seed hypothesis holds at the grade `2`.**

* `2FL(2)` fails (`not_twoFaceLift_two_of`, `not_twoFaceLift_two`): with `G = ⊥` the labellings
  `tripleLabelling` are the labellings `pairLabelling` of `T4`, and the argument for `T4`
  (`TwoFaceLiftCounterexample.not_twoFaceLift_two_of_isLawfulBelow_pairLabelling`), through the
  strip of a label at the grade `1`, applies verbatim.
* The old cells of the grade `3` are not dead (`not_deadAt_two`): `tripleLabelling ⊤ ⊤ ⊤ ⊤ ⊤` is
  lawful below `(C, 3)` and is `⊤` at the cell at `({0, 1, 2, 3}, 3)`.

So `2FL(2) ∨ Seed.DeadAt 2` fails for `seed5` (`not_twoFaceLift_or_deadAt`).

**The completion exists** (`raisedUnionFill_two`, `twoFaceLiftExists_two`, `towerInvariant_three`,
`nonempty_completionBelowFullGrade_of`, `nonempty_completionBelowFullGrade_seed5`).  The raised
union fill (`Seed.RaisedUnionFill`) holds at the grade `2`.  Let `a` be a labelling lawful below
both coatoms, `h` a positive cap self-visible at `3`, and `w_C` lawful below `(C, 3)` agreeing with
`a` capped at `h`; let `G_C` be the label of `w_C` at the cell of the common face of grade `3`.  The
cap is `c = max h G_C`: every cell of `C` where `a` reaches `h` is live, so `w_C` is at least `G_C`
there by the coupling on `C`.  A labelling `V` lawful below `(D, 2)` that agrees with `a` *raised to
`⊤` above `h`* (`Label.raise`: `⊤` where `a ≥ h`, and `a` elsewhere) capped at `c` is at least
`G_C` at the live cells of `D`: above the cap by the raising, and below it because `a` is at least
its label at the cell of the common face there, and that label is then `G_C`.  So `V` with `G_C`
at the live cells of grade `3` is lawful below `(D, 3)`.  With the invariant at the grade `2` this
gives `2FL∃(2)` (`Seed.twoFaceLiftExists_of_raisedUnionFill`), the step to the grade `3`, and the
completion.  So `2FL∃(2)` holds where `2FL(2)` and deadness both fail
(`twoFaceLiftExists_and_not_twoFaceLift_or_deadAt`); it holds also for the seed of `T4` with
itself, by deadness (`twoFaceLiftExists_two_seed4`).

The argument needs the coupling on `C`, which bounds `w_C` below by `G_C` where `a` reaches the
cap.  Without it `2FL∃(2)` can fail: for the seed whose first coatom type couples the parameter of
grade `3` to `F` only, and whose second is `T5`, it fails
(`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_seedL`, module
`VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample`).

## Placement

Checkpoints 2.6 and 2.7 of the completion of the coatom extension construction
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.CaseSplitCounterexample

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftCounterexample (cellScope cellGrade cells v1 v2 gradedIndex_cells
  gradedIndex_injective complete_below mem_below_of_le stripShifter isWitness_stripShifter
  stripShifter_bot stripShifter_v1 stripShifter_v2 liveC liveD pairKind pairLabelling)

/-! ### The scheme on four points -/

/-- The live cells: grade `1` through the point `3`, `(univ, 2)`, and the cells of grade `3` at
`{0, 1, 2}` and `univ`. -/
def live : Fin 19 → Bool :=
  ![false, false, false, true, false, false, true, false, true, true,
    false, false, false, false, false, true, true, false, true]

/-- The row value of the live cells of grade `3`: the ordinal `3`. -/
noncomputable abbrev v3 : Label.{u} := gridPoint 3 0

/-- The labelling with `⊥` at the dead cells, `A` at the live cells of grade `1`, `F` at the
live cell of grade `2`, and `G` at the live cells of grade `3`. -/
noncomputable def labelling (A F G : Label.{u}) (d : Fin 19) : Label.{u} :=
  if live d = true then (if cellGrade d = 1 then A else if cellGrade d = 2 then F else G) else ⊥

/-- The rows: a live cell of grade at most `2` reads the live cells of grade `1` at `v1` and the
other live cells at `v2`; a live cell of grade `3` reads every live cell at `v3`; every other
entry is `⊥`. -/
noncomputable def rows : cells.Rows.{u} :=
  ⟨fun s t ↦ if live s = true ∧ live t.1 = true then
    (if cellGrade s = 3 then v3 else if cellGrade t.1 = 1 then v1 else v2) else ⊥⟩

/-- The scheme on four points. -/
noncomputable def S : Scheme.{u} 4 := ⟨19, cells, rows⟩

theorem live_le_live : ∀ s d : Fin 19, live s = true → live d = true →
    cells.gradedIndex d ≤ cells.gradedIndex s →
      cellGrade d = cellGrade s ∨ (cellGrade d = 1 ∧ cellGrade s = 2) ∨ cellGrade s = 3 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The live cells are closed upward under inclusion of scopes at the same grade. -/
theorem live_up : ∀ s t : Fin 19, live s = true → cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → live t = true := by decide +kernel

theorem live_grade (d : Fin 19) (hd : live d = true) :
    cellGrade d = 1 ∨ cellGrade d = 2 ∨ cellGrade d = 3 := by
  revert d; decide +kernel

theorem grade_le_three (d : Fin 19) : cellGrade d ≤ 3 := by revert d; decide

/-! ### The labellings `labelling A F G` are lawful -/

theorem isSelfVisible_labelling {A F G : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hG : IsSelfVisible 3 G) (d : Fin 19) :
    IsSelfVisible (cellGrade d) (labelling A F G d) := by
  unfold labelling
  by_cases hl : live d = true
  · rcases live_grade d hl with h | h | h
    · simp [hl, h, hA]
    · simp [hl, h, hF]
    · simp [hl, h, hG]
  · simp [hl]

private theorem le_labelling_of_live {A F G : Label.{u}} (hGA : G ≤ A) (hGF : G ≤ F)
    {d : Fin 19} (hd : live d = true) : G ≤ labelling A F G d := by
  unfold labelling
  rw [ite_eq_left hd]
  split_ifs
  · exact hGA
  · exact hGF
  · exact le_rfl

/-- **`labelling A F G` is lawful** when `A`, `F`, `G` are self-visible at `1`, `2`, `3` and
`G ≤ A`, `G ≤ F`. -/
theorem isLawful_labelling {A F G : Label.{u}} (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F)
    (hG : IsSelfVisible 3 G) (hGA : G ≤ A) (hGF : G ≤ F) :
    rows.IsLawful (labelling A F G) where
  orderly d := isSelfVisible_labelling hA hF hG d
  locality s := by
    by_cases hs : live s = true
    · rcases live_grade s hs with hs1 | hs2 | hs3
      · -- A live cell of grade `1`: the top shifter, the suppressor `A` up to the grade `1`.
        refine ⟨constStepSuppressor 1 A, topShifter,
          isWitness_topShifter (antitone_constStepSuppressor _ _)
            (isSelfVisible_constStepSuppressor hA),
          fun d ↦ ?_⟩
        have hds : cells.gradedIndex d.1 ≤ cells.gradedIndex s := d.2
        change min (labelling A F G d.1) (labelling A F G s) =
          min (topShifter (if live s = true ∧ live d.1 = true then
            (if cellGrade s = 3 then v3 else if cellGrade d.1 = 1 then v1 else v2) else ⊥))
            (constStepSuppressor 1 A (cellGrade d.1))
        by_cases hd : live d.1 = true
        · have hd1 : cellGrade d.1 = 1 := by
            rcases live_le_live s d.1 hs hd hds with h | ⟨_, h⟩ | h <;> omega
          rw [ite_eq_left ⟨hs, hd⟩, ite_eq_right (by omega : ¬ cellGrade s = 3),
            ite_eq_left hd1, topShifter, ite_eq_right (gridPoint_ne_bot 1 0),
            constStepSuppressor, ite_eq_left hd1.le, min_top_left]
          simp [labelling, hs, hd, hd1, hs1]
        · have : labelling A F G d.1 = ⊥ := by simp [labelling, hd]
          rw [this, ite_eq_right (fun h ↦ hd h.2), topShifter, ite_eq_left rfl]
          simp
      · -- The live cell of grade `2`: the strip shifter, the suppressor `F` up to the grade `2`.
        refine ⟨constStepSuppressor 2 F, stripShifter A, isWitness_stripShifter hF, fun d ↦ ?_⟩
        have hds : cells.gradedIndex d.1 ≤ cells.gradedIndex s := d.2
        change min (labelling A F G d.1) (labelling A F G s) =
          min (stripShifter A (if live s = true ∧ live d.1 = true then
            (if cellGrade s = 3 then v3 else if cellGrade d.1 = 1 then v1 else v2) else ⊥))
            (constStepSuppressor 2 F (cellGrade d.1))
        have hlabs : labelling A F G s = F := by simp [labelling, hs, hs2]
        rw [hlabs]
        by_cases hd : live d.1 = true
        · rw [ite_eq_left ⟨hs, hd⟩, ite_eq_right (by omega : ¬ cellGrade s = 3)]
          rcases live_le_live s d.1 hs hd hds with h | ⟨h1, _⟩ | h
          · have hd2 : cellGrade d.1 = 2 := h.trans hs2
            rw [ite_eq_right (by omega), stripShifter_v2, constStepSuppressor,
              ite_eq_left hd2.le, min_top_left]
            simp [labelling, hd, hd2]
          · rw [ite_eq_left h1, stripShifter_v1 hA, constStepSuppressor, ite_eq_left (by omega)]
            simp [labelling, hd, h1]
          · omega
        · have : labelling A F G d.1 = ⊥ := by simp [labelling, hd]
          rw [this, ite_eq_right (fun h ↦ hd h.2), stripShifter_bot]
          simp
      · -- A live cell of grade `3`: the top shifter, the suppressor `G` up to the grade `3`.
        refine ⟨constStepSuppressor 3 G, topShifter,
          isWitness_topShifter (antitone_constStepSuppressor _ _)
            (isSelfVisible_constStepSuppressor hG),
          fun d ↦ ?_⟩
        change min (labelling A F G d.1) (labelling A F G s) =
          min (topShifter (if live s = true ∧ live d.1 = true then
            (if cellGrade s = 3 then v3 else if cellGrade d.1 = 1 then v1 else v2) else ⊥))
            (constStepSuppressor 3 G (cellGrade d.1))
        have hlabs : labelling A F G s = G := by simp [labelling, hs, hs3]
        rw [hlabs]
        by_cases hd : live d.1 = true
        · rw [ite_eq_left ⟨hs, hd⟩, ite_eq_left hs3, topShifter,
            ite_eq_right (gridPoint_ne_bot 3 0), constStepSuppressor,
            ite_eq_left (grade_le_three d.1), min_top_left]
          exact min_eq_right (le_labelling_of_live hGA hGF hd)
        · have : labelling A F G d.1 = ⊥ := by simp [labelling, hd]
          rw [this, ite_eq_right (fun h ↦ hd h.2), topShifter, ite_eq_left rfl]
          simp
    · have : labelling A F G s = ⊥ := by simp [labelling, hs]
      simp only [this, min_bot_right]
      exact TransformsTo.bot _ _
  availability s t hst hg := by
    refine ⟨t, rfl, ?_⟩
    by_cases hs : live s = true
    · have ht := live_up s t hs hst hg
      have hg' : cellGrade s = cellGrade t := hg
      simp [labelling, hs, ht, hg']
    · simp [labelling, hs]

/-! ### Cell facts -/

theorem labelling_dead {A F G : Label.{u}} {d : Fin 19} (hd : live d = false) :
    labelling A F G d = ⊥ := by
  simp [labelling, hd]

theorem labelling_one {A F G : Label.{u}} {d : Fin 19} (hd : live d = true)
    (hg : cellGrade d = 1) : labelling A F G d = A := by
  simp [labelling, hd, hg]

theorem labelling_two {A F G : Label.{u}} {d : Fin 19} (hd : live d = true)
    (hg : cellGrade d = 2) : labelling A F G d = F := by
  simp [labelling, hd, hg]

theorem labelling_three {A F G : Label.{u}} {d : Fin 19} (hd : live d = true)
    (hg : cellGrade d = 3) : labelling A F G d = G := by
  simp [labelling, hd, hg]

/-- Every live cell of grade `1` lies above the cell `3`, at `({3}, 1)`. -/
theorem three_le_of_grade_one : ∀ d : Fin 19, live d = true → cellGrade d = 1 →
    cells.gradedIndex 3 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The only live cell of grade `2` is the cell `15`, at `(univ, 2)`. -/
theorem eq_fifteen_of_grade_two : ∀ d : Fin 19, live d = true → cellGrade d = 2 →
    d = 15 := by decide +kernel

/-- The live cells of grade `3` are the cells `16`, at `({0, 1, 2}, 3)`, and `18`, at
`(univ, 3)`. -/
theorem grade_three_cases : ∀ d : Fin 19, live d = true → cellGrade d = 3 →
    d = 16 ∨ d = 18 := by decide +kernel

theorem le_eighteen : ∀ d : Fin 19, cells.gradedIndex d ≤ cells.gradedIndex 18 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

theorem sixteen_le_of_grade_three : ∀ d : Fin 19, live d = true → cellGrade d = 3 →
    cells.gradedIndex 16 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

theorem live_cases (d : Fin 19) :
    live d = false ∨ (live d = true ∧ cellGrade d = 1) ∨ (live d = true ∧ cellGrade d = 2) ∨
      (live d = true ∧ cellGrade d = 3) := by
  revert d; decide

/-- A pair above the cell `16` and above the cell `3` or `15` is above the cell `18`. -/
theorem eighteen_mem_below {Y : Finset (Fin 4) × ℕ} (h16 : (16 : Fin 19) ∈ cells.below Y)
    (h : (3 : Fin 19) ∈ cells.below Y ∨ (15 : Fin 19) ∈ cells.below Y) :
    (18 : Fin 19) ∈ cells.below Y := by
  obtain ⟨B, k⟩ := Y
  have key : ∀ B : Finset (Fin 4), cellScope 16 ⊆ B → (cellScope 3 ⊆ B ∨ cellScope 15 ⊆ B) →
      cellScope 18 ⊆ B := by decide +kernel
  exact ⟨key B h16.1 (h.imp (fun h3 ↦ h3.1) fun h15 ↦ h15.1), h16.2⟩

/-! ### The lawful labellings below a pair -/

/-- **The lawful labellings below a pair** are the restrictions of the labellings
`labelling A F G` with `A`, `F`, `G` self-visible at `1`, `2`, `3`, `G ≤ A` and `G ≤ F`. -/
theorem isLawfulBelow_iff {Y : Finset (Fin 4) × ℕ} {x : Fin 19 → Label.{u}} :
    rows.IsLawfulBelow Y (fun d ↦ x d) ↔ ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧
      IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧ G ≤ F ∧
      ∀ d ∈ cells.below Y, x d = labelling A F G d := by
  classical
  constructor
  · intro hx
    obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
    have hdead : ∀ d ∈ cells.below Y, live d = false → x d = ⊥ := by
      intro d hd hdl
      have := (hl d hd).eq_bot (d := ⟨d, cells.mem_below_gradedIndex d⟩)
        (by simp [rows, hdl])
      simpa using this
    have hloc : ∀ s ∈ cells.below Y, ∀ d, live s = true → live d = true →
        cellGrade s = 1 → cells.gradedIndex d ≤ cells.gradedIndex s → x s ≤ x d := by
      intro s hs d hsl hdl hs1 hds
      have hd1 : cellGrade d = 1 := by
        rcases live_le_live s d hsl hdl hds with h | ⟨_, h⟩ | h <;> omega
      have := (hl s hs).le_of_le (d := ⟨s, cells.mem_below_gradedIndex s⟩) (d' := ⟨d, hds⟩)
        (by simp [rows, hsl, hdl, hd1, hs1]) hds.2
      simp only [min_self] at this
      exact this.trans (min_le_left _ _)
    have havail : ∀ s t, t ∈ cells.below Y → cellScope s ⊆ cellScope t →
        cellGrade s = cellGrade t → x s ≤ x t := by
      intro s t ht hst hg
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rwa [gradedIndex_injective hu] at hle
    -- Locality at the cell `18`: every live cell carries at least its label.
    have h18 : (18 : Fin 19) ∈ cells.below Y → ∀ d, live d = true → x 18 ≤ x d := by
      intro h18 d hdl
      have hl18 : live 18 = true := rfl
      have hg18 : cellGrade 18 = 3 := rfl
      have := (hl 18 h18).le_of_le (d := ⟨18, cells.mem_below_gradedIndex 18⟩)
        (d' := ⟨d, le_eighteen d⟩) (by simp [rows, hdl, hl18, hg18]) (grade_le_three d)
      simp only [min_self] at this
      exact this.trans (min_le_left _ _)
    have h1618 : (18 : Fin 19) ∈ cells.below Y → x 16 = x 18 := fun h18m ↦
      le_antisymm (havail 16 18 h18m (by decide +kernel) rfl) (h18 h18m 16 rfl)
    set A : Label.{u} := if (3 : Fin 19) ∈ cells.below Y then x 3 else ⊤ with hA_def
    set F : Label.{u} := if (15 : Fin 19) ∈ cells.below Y then x 15 else ⊤ with hF_def
    set G : Label.{u} := if (16 : Fin 19) ∈ cells.below Y then x 16 else ⊥ with hG_def
    have hA : IsSelfVisible 1 A := by
      rw [hA_def]; split_ifs with h3
      · exact ho 3 h3
      · exact isSelfVisible_top 1
    have hF : IsSelfVisible 2 F := by
      rw [hF_def]; split_ifs with h15
      · exact ho 15 h15
      · exact isSelfVisible_top 2
    have hG : IsSelfVisible 3 G := by
      rw [hG_def]; split_ifs with h16
      · exact ho 16 h16
      · exact isSelfVisible_bot 3
    have hGA : G ≤ A := by
      rw [hG_def, hA_def]
      split_ifs with h16 h3
      · have h18m := eighteen_mem_below h16 (.inl h3)
        rw [h1618 h18m]; exact h18 h18m 3 rfl
      · exact le_top
      · exact bot_le
      · exact bot_le
    have hGF : G ≤ F := by
      rw [hG_def, hF_def]
      split_ifs with h16 h15
      · have h18m := eighteen_mem_below h16 (.inr h15)
        rw [h1618 h18m]; exact h18 h18m 15 rfl
      · exact le_top
      · exact bot_le
      · exact bot_le
    refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun d hd ↦ ?_⟩
    rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, hdead d hd hdl]
    · have h3 : (3 : Fin 19) ∈ cells.below Y :=
        mem_below_of_le hd (three_le_of_grade_one d hdl hg)
      rw [labelling_one hdl hg, hA_def, ite_eq_left h3]
      refine le_antisymm (hloc d hd 3 hdl rfl hg (three_le_of_grade_one d hdl hg)) ?_
      exact havail 3 d hd (three_le_of_grade_one d hdl hg).1 (hg ▸ rfl)
    · obtain rfl := eq_fifteen_of_grade_two d hdl hg
      rw [labelling_two hdl hg, hF_def, ite_eq_left hd]
    · have h16 : (16 : Fin 19) ∈ cells.below Y :=
        mem_below_of_le hd (sixteen_le_of_grade_three d hdl hg)
      rw [labelling_three hdl hg, hG_def, ite_eq_left h16]
      rcases grade_three_cases d hdl hg with rfl | rfl
      · rfl
      · exact (h1618 hd).symm
  · rintro ⟨A, F, G, hA, hF, hG, hGA, hGF, hx⟩
    have := (isLawful_labelling hA hF hG hGA hGF).isLawfulBelow Y
    convert this using 1
    funext d
    exact hx d d.2

/-! ### Bountifulness -/

/-- The lifted parameter of grade `3` is at most a lifted parameter of grade `1` or `2`. -/
theorem lift_le {Ap Aq Gp Gq c : Label.{u}} {P3 P16 b : Prop} [Decidable P3]
    [Decidable P16] [Decidable b] (hGAp : Gp ≤ Ap) (hGAq : Gq ≤ Aq)
    (h3 : P3 → min Aq c = min Ap c) (h16 : P16 → min Gq c = min Gp c) :
    (if P16 then Gp else if Gq < c then Gq else if b then c else ⊥) ≤
      (if P3 then Ap else if Aq < c then Aq else ⊤) := by
  by_cases hP16 : P16
  · rw [ite_eq_left hP16]
    by_cases hP3 : P3
    · rw [ite_eq_left hP3]; exact hGAp
    · rw [ite_eq_right hP3]
      split_ifs with hAq
      · have hm : min Gp c ≤ Aq := by
          rw [← h16 hP16]; exact (min_le_min_right c hGAq).trans (min_le_left _ _)
        by_cases hGc : c ≤ Gp
        · rw [min_eq_right hGc] at hm; exact absurd (hm.trans_lt hAq) (lt_irrefl _)
        · rwa [min_eq_left (not_le.mp hGc).le] at hm
      · exact le_top
  · rw [ite_eq_right hP16]
    by_cases hGq : Gq < c
    · rw [ite_eq_left hGq]
      by_cases hP3 : P3
      · rw [ite_eq_left hP3]
        calc Gq = min Gq c := (min_eq_left hGq.le).symm
          _ ≤ min Aq c := min_le_min_right c hGAq
          _ = min Ap c := h3 hP3
          _ ≤ Ap := min_le_left _ _
      · rw [ite_eq_right hP3]
        split_ifs
        · exact hGAq
        · exact le_top
    · rw [ite_eq_right hGq]
      by_cases hb : b
      · rw [ite_eq_left hb]
        by_cases hP3 : P3
        · rw [ite_eq_left hP3]
          have : min Ap c = c := by
            rw [← h3 hP3]; exact min_eq_right ((not_lt.mp hGq).trans hGAq)
          exact this ▸ min_le_left _ _
        · rw [ite_eq_right hP3]
          split_ifs with hAq
          · exact absurd (hAq.trans_le ((not_lt.mp hGq).trans hGAq)) (lt_irrefl _)
          · exact le_top
      · rw [ite_eq_right hb]; exact bot_le

/-- **Every pair lifts capped to every larger pair.**  For a prescription `labelling Ap Fp Gp`
below `X` and an ambient `labelling Aq Fq Gq` below `Y`, the lift is `labelling A' F' G'`: each
parameter prescribed when its cells meet `X`; otherwise `A'` and `F'` are the ambient below the cap
and `⊤` above, and `G'` the ambient below the cap and the cap above. -/
theorem cappedLift_all {X Y : Finset (Fin 4) × ℕ} (h : X ≤ Y) : rows.CappedLift.{u} h := by
  classical
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGAp, hGFp, hpx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨Aq, Fq, Gq, hAq, hFq, hGq, hGAq, hGFq, hqx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpd (d : cells.below X) : p d = labelling Ap Fp Gp d := by
    rw [← hpx d d.2, Rows.extendBot_of_mem p d.2]
  have hqd (d : cells.below Y) : q d = labelling Aq Fq Gq d := by
    rw [← hqx d d.2, Rows.extendBot_of_mem q d.2]
  have hcap3 (h3 : (3 : Fin 19) ∈ cells.below X) : min Aq c = min Ap c := by
    have := hpq ⟨3, h3⟩
    rwa [hqd, hpd] at this
  have hcap15 (h15 : (15 : Fin 19) ∈ cells.below X) : min Fq c = min Fp c := by
    have := hpq ⟨15, h15⟩
    rwa [hqd, hpd] at this
  have hcap16 (h16 : (16 : Fin 19) ∈ cells.below X) : min Gq c = min Gp c := by
    have := hpq ⟨16, h16⟩
    rwa [hqd, hpd] at this
  set A' : Label.{u} := if (3 : Fin 19) ∈ cells.below X then Ap else (if Aq < c then Aq else ⊤)
    with hA'
  set F' : Label.{u} := if (15 : Fin 19) ∈ cells.below X then Fp else (if Fq < c then Fq else ⊤)
    with hF'
  set G' : Label.{u} := if (16 : Fin 19) ∈ cells.below X then Gp else
    (if Gq < c then Gq else if 3 ≤ Y.2 then c else ⊥) with hG'
  have hSA : IsSelfVisible 1 A' := by
    rw [hA']; split_ifs
    · exact hAp
    · exact hAq
    · exact isSelfVisible_top 1
  have hSF : IsSelfVisible 2 F' := by
    rw [hF']; split_ifs
    · exact hFp
    · exact hFq
    · exact isSelfVisible_top 2
  have hSG : IsSelfVisible 3 G' := by
    rw [hG']; split_ifs with _ _ h3
    · exact hGp
    · exact hGq
    · exact hc.mono h3
    · exact isSelfVisible_bot 3
  have hGA' : G' ≤ A' := lift_le hGAp hGAq hcap3 hcap16
  have hGF' : G' ≤ F' := lift_le hGFp hGFq hcap15 hcap16
  refine ⟨fun d ↦ labelling A' F' G' d,
    isLawfulBelow_iff.mpr ⟨A', F', G', hSA, hSF, hSG, hGA', hGF', fun _ _ ↦ rfl⟩,
    fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hqd]
    change min (labelling A' F' G' d.1) c = min (labelling Aq Fq Gq d.1) c
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, labelling_dead hdl]
    · rw [labelling_one hdl hg, labelling_one hdl hg, hA']
      split_ifs with h3 hlt
      · exact (hcap3 h3).symm
      · rfl
      · rw [min_top_left, min_eq_right (not_lt.mp hlt)]
    · rw [labelling_two hdl hg, labelling_two hdl hg, hF']
      split_ifs with h15 hlt
      · exact (hcap15 h15).symm
      · rfl
      · rw [min_top_left, min_eq_right (not_lt.mp hlt)]
    · have hY3 : 3 ≤ Y.2 := by
        have h2 := d.2.2
        change cellGrade d.1 ≤ Y.2 at h2
        omega
      rw [labelling_three hdl hg, labelling_three hdl hg, hG']
      split_ifs with h16 hlt
      · exact (hcap16 h16).symm
      · rfl
      · rw [min_self, min_eq_right (not_lt.mp hlt)]
  · rw [hpd]
    change labelling A' F' G' d.1 = labelling Ap Fp Gp d.1
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, labelling_dead hdl]
    · have h3 : (3 : Fin 19) ∈ cells.below X :=
        mem_below_of_le d.2 (three_le_of_grade_one d.1 hdl hg)
      rw [labelling_one hdl hg, labelling_one hdl hg, hA', ite_eq_left h3]
    · have h15 : (15 : Fin 19) ∈ cells.below X := by
        rw [← eq_fifteen_of_grade_two d.1 hdl hg]; exact d.2
      rw [labelling_two hdl hg, labelling_two hdl hg, hF', ite_eq_left h15]
    · have h16 : (16 : Fin 19) ∈ cells.below X :=
        mem_below_of_le d.2 (sixteen_le_of_grade_three d.1 hdl hg)
      rw [labelling_three hdl hg, labelling_three hdl hg, hG', ite_eq_left h16]

theorem isBountiful_rows : rows.{u}.IsBountiful := fun _ _ _ _ h ↦ cappedLift_all h

/-! ### Legality -/

theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  have hv3 (k : ℕ) (hk : k ≤ 3) : IsSelfVisible k (v3 : Label.{u}) :=
    (isSelfVisible_gridPoint 3 0).mono hk
  set As : Label.{u} := if live s = true then (if cellGrade s = 3 then v3 else v1) else ⊥ with hAs
  set Fs : Label.{u} := if live s = true then (if cellGrade s = 3 then v3 else v2) else ⊥ with hFs
  set Gs : Label.{u} := if live s = true ∧ cellGrade s = 3 then v3 else ⊥ with hGs
  have hA : IsSelfVisible 1 As := by
    rw [hAs]; split_ifs
    · exact hv3 1 (by omega)
    · exact isSelfVisible_gridPoint 1 0
    · exact isSelfVisible_bot 1
  have hF : IsSelfVisible 2 Fs := by
    rw [hFs]; split_ifs
    · exact hv3 2 (by omega)
    · exact isSelfVisible_gridPoint 2 1
    · exact isSelfVisible_bot 2
  have hG : IsSelfVisible 3 Gs := by
    rw [hGs]; split_ifs
    · exact hv3 3 le_rfl
    · exact isSelfVisible_bot 3
  have hGA : Gs ≤ As := by
    rw [hGs, hAs]
    by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;> simp [hs, hs3]
  have hGF : Gs ≤ Fs := by
    rw [hGs, hFs]
    by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;> simp [hs, hs3]
  have := (isLawfulBelow_iff (Y := cells.gradedIndex s)
    (x := fun d ↦ if live s = true ∧ live d = true then
      (if cellGrade s = 3 then (v3 : Label.{u}) else if cellGrade d = 1 then v1 else v2)
      else ⊥)).mpr ⟨As, Fs, Gs, hA, hF, hG, hGA, hGF, fun d hd ↦ ?_⟩
  · exact this
  · have hds : cellGrade d ≤ cellGrade s := hd.2
    have hs3' := grade_le_three s
    rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · simp [labelling_dead hdl, hdl]
    · rw [labelling_one hdl hg, hAs]
      by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;> simp [hs, hdl, hg, hs3]
    · rw [labelling_two hdl hg, hFs]
      by_cases hs : live s = true <;> by_cases hs3 : cellGrade s = 3 <;> simp [hs, hdl, hg, hs3]
    · have hs3 : cellGrade s = 3 := by omega
      rw [labelling_three hdl hg, hGs]
      by_cases hs : live s = true <;> simp [hs, hdl, hs3]

theorem isWellFormed_S : S.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

theorem isCoded_S : S.{u}.IsCoded := by
  intro s t
  change (if live s = true ∧ live t.1 = true then
    (if cellGrade s = 3 then (v3 : Label.{u}) else if cellGrade t.1 = 1 then v1 else v2)
      else ⊥) < _
  split_ifs
  · exact gridPoint_lt_omega0_sq 3 0
  · exact gridPoint_lt_omega0_sq 1 0
  · exact gridPoint_lt_omega0_sq 2 1
  · exact WithBot.bot_lt_coe _

theorem isLegalBelowFullGrade_S : S.{u}.IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isConsistent := isConsistent_rows
  isBountiful := isBountiful_rows
  grade_lt d := (by decide : ∀ d : Fin 19, cellGrade d < 4) d
  exists_gradedIndex_eq X hX hX4 := by
    obtain ⟨d, hd1, hd2⟩ := complete_below X.1 hX.1 X.2 hX4 hX.2.1 hX.2.2
    exact ⟨d, Prod.ext hd1 hd2⟩

/-- The stage type of `S` with every label `⊥`. -/
noncomputable def T5₀ (α : Ordinal.{u}) : StageType.{u} α 4 where
  toScheme := S
  label _ := ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- **The legal type on four points**: `S` with the apex added. -/
noncomputable def T5 (α : Ordinal.{u}) : StageType.{u} α 4 :=
  (T5₀ α).addApex isLegalBelowFullGrade_S (by omega)

/-- **`T5` is legal**: `S` is legal below the full grade (`isLegalBelowFullGrade_S`; every pair
lifts capped to every larger one, `cappedLift_all`), and adding the apex to it gives a legal stage
type (`StageType.isLegal_addApex`). -/
theorem isLegal_T5 (α : Ordinal.{u}) : (T5 α).IsLegal :=
  StageType.isLegal_addApex _ _

section InT5

variable {α : Ordinal.{u}}

theorem gradedIndex_T5_castSucc (d : Fin 19) :
    (T5 α).toCellScheme.gradedIndex (Fin.castSucc d) = cells.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc S 4 d

theorem gradedIndex_T5_last :
    (T5 α).toCellScheme.gradedIndex (Fin.last 19) = ((univ : Finset (Fin 4)), 4) :=
  Scheme.appendFullCellScheme_gradedIndex_last S 4

/-- Below a pair not above the apex, lawfulness in `T5` is lawfulness in `S`. -/
theorem isLawfulBelow_T5_iff {X : Finset (Fin 4) × ℕ}
    (hX : ¬ ((univ : Finset (Fin 4)), 4) ≤ X) {w : Fin (T5 α).card → Label.{u}} :
    (T5 α).rows.IsLawfulBelow X (fun d ↦ w d) ↔
      rows.IsLawfulBelow X (fun d ↦ w (Fin.castSucc d.1)) :=
  Scheme.isLawfulBelow_appendFullCell_iff (h := isLegalBelowFullGrade_S.not_le) hX

/-- The face `{0, 1, 2}` of `T5` is a face. -/
theorem face_mem_T5 : univ.map (Coatom.face 3) ∈ (T5 α).toCellScheme.faces := by
  change univ.map (Coatom.face 3) ∈ Geometry.intervalPlan univ
  decide +kernel

end InT5

/-- The face of `T5` on `{0, 1, 2}`. -/
noncomputable def faceT5 (α : Ordinal.{u}) : StageType.{u} α 3 :=
  (T5 α).comap (Coatom.face 3) face_mem_T5

theorem restrictFace_T5 (α : Ordinal.{u}) :
    StageType.restrictFace (Coatom.face 3) (T5 α) = some (faceT5 α) :=
  StageType.restrictFace_of_mem _ _ face_mem_T5

/-- **The seed of `T5` with itself** on five points: the coatoms `{0, 1, 2, 3}` and
`{0, 1, 2, 4}`, with common face `{0, 1, 2}`. -/
noncomputable def seed5 (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_T5 α) (isLegal_T5 α) (restrictFace_T5 α) (restrictFace_T5 α)


/-! ### Labellings of the amalgam read off graded indices -/

section SeedLevel

variable {α : Ordinal.{u}}

/-- The live graded indices of grade `3`: the common face and the two coatoms. -/
def liveG : Finset (Finset (Fin 5) × ℕ) :=
  {({0, 1, 2}, 3), ({0, 1, 2, 3}, 3), ({0, 1, 2, 4}, 3)}

/-- The kind of a graded index: `1`/`2` for the live grade-`1`/grade-`2` indices of the first
coatom, `3`/`4` for those of the second, `5` for the live indices of grade `3`, `0` otherwise. -/
def tripleKind (X : Finset (Fin 5) × ℕ) : Fin 6 :=
  if X ∈ liveC then (if X.2 = 1 then 1 else 2)
  else if X ∈ liveD then (if X.2 = 1 then 3 else 4) else if X ∈ liveG then 5 else 0

/-- The labelling of graded indices with `A_C, F_C` on the first coatom's live indices of grade
at most `2`, `A_D, F_D` on the second's, and `G` on the live indices of grade `3`. -/
noncomputable def tripleLabelling (AC FC AD FD G : Label.{u}) (X : Finset (Fin 5) × ℕ) :
    Label.{u} :=
  ![⊥, AC, FC, AD, FD, G] (tripleKind X)

private def liveKind (d : Fin 19) : Fin 4 :=
  if live d = true then (if cellGrade d = 1 then 1 else if cellGrade d = 2 then 2 else 3) else 0

private theorem labelling_eq_liveKind (A F G : Label.{u}) (d : Fin 19) :
    labelling A F G d = ![⊥, A, F, G] (liveKind d) := by
  unfold labelling liveKind
  split_ifs <;> rfl

private theorem tripleKind_left : ∀ d : Fin 19,
    tripleKind (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex d)) =
      ![0, 1, 2, 5] (liveKind d) := by
  decide +kernel

private theorem tripleKind_right : ∀ d : Fin 19,
    tripleKind (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex d)) =
      ![0, 3, 4, 5] (liveKind d) := by
  decide +kernel

theorem tripleLabelling_left (AC FC AD FD G : Label.{u}) (d : Fin 19) :
    tripleLabelling AC FC AD FD G
        (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex d)) =
      labelling AC FC G d := by
  rw [tripleLabelling, tripleKind_left, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

theorem tripleLabelling_right (AC FC AD FD G : Label.{u}) (d : Fin 19) :
    tripleLabelling AC FC AD FD G
        (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex d)) =
      labelling AD FD G d := by
  rw [tripleLabelling, tripleKind_right, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

private theorem isLawfulBelow_T5_of_eq {A F G : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hG : IsSelfVisible 3 G) (hGA : G ≤ A) (hGF : G ≤ F)
    {f : Fin 4 ↪ Fin 5} {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (cells.gradedIndex d)) = labelling A F G d)
    {X : Finset (Fin 4) × ℕ} (hX : ¬ ((univ : Finset (Fin 4)), 4) ≤ X)
    (x : Fin (T5 α).toScheme.card → Label.{u})
    (hx : ∀ i, x i = Lf (Prod.map (Finset.map f) id ((T5 α).toScheme.toCellScheme.gradedIndex i))) :
    (T5 α).toScheme.rows.IsLawfulBelow X (fun i ↦ x i) := by
  refine (isLawfulBelow_T5_iff hX).mpr ?_
  convert (isLawful_labelling hA hF hG hGA hGF).isLawfulBelow X using 1
  funext d
  refine (hx _).trans ?_
  rw [gradedIndex_T5_castSucc]
  exact hL d.1

/-- A labelling of graded indices whose reading along `f` is `labelling A F G` is lawful below the
coatom `univ.map f` at the grade `3`, for a stage type whose face along `f` is `T5`. -/
theorem isLawfulBelow_coatom {A F G : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hG : IsSelfVisible 3 G) (hGA : G ≤ A) (hGF : G ≤ F)
    {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T5 α)) {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (cells.gradedIndex d)) = labelling A F G d) :
    Am.rows.IsLawfulBelow (univ.map f, 3) (fun d ↦ Lf (Am.toCellScheme.gradedIndex d)) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T5 α).toScheme := congrArg StageType.toScheme he
  have hlaw : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (∀ i, x i = Lf (Prod.map (Finset.map f) id
        ((Am.toScheme.comap f).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun i ↦ x i) := by
    rw [heq]
    exact fun x hx ↦ isLawfulBelow_T5_of_eq hA hF hG hGA hGF hL
      (fun h ↦ absurd h.2 (by decide)) x hx
  exact (Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 4)), 3)
    fun d ↦ Lf (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg Lf (Am.toScheme.map_comap_gradedIndex f i).symm)

/-- **`tripleLabelling` is lawful below both coatoms at the grade `3`**, on a seed on five points
whose two coatom types are `T5`, when `A_C`, `A_D` are self-visible at `1`, `F_C`, `F_D` at `2`,
`G` at `3`, and `G` is at most each of them. -/
theorem isLawfulBelow_tripleLabelling {I : Seed.{u} α 3} (hIL : I.left = T5 α)
    (hIR : I.right = T5 α) {AC FC AD FD G : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hFC : IsSelfVisible 2 FC) (hAD : IsSelfVisible 1 AD) (hFD : IsSelfVisible 2 FD)
    (hG : IsSelfVisible 3 G) (hGAC : G ≤ AC) (hGFC : G ≤ FC) (hGAD : G ≤ AD) (hGFD : G ≤ FD) :
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 4), 3)
        (fun d ↦ tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d)) ∧
      I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 3)
        (fun d ↦ tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d)) := by
  constructor
  · rw [← Coatom.univ_map_left]
    exact isLawfulBelow_coatom hAC hFC hG hGAC hGFC (hIL ▸ I.restrictFace_left)
      (tripleLabelling_left AC FC AD FD G)
  · rw [← Coatom.univ_map_right]
    exact isLawfulBelow_coatom hAD hFD hG hGAD hGFD (hIR ▸ I.restrictFace_right)
      (tripleLabelling_right AC FC AD FD G)

/-- A cell of `T5` carried into the amalgam along a coatom whose face is `T5`. -/
theorem exists_cell {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T5 α)) (d : Fin 19) :
    ∃ e : Fin Am.card, Am.toCellScheme.gradedIndex e =
      Prod.map (Finset.map f) id (cells.gradedIndex d) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T5 α).toScheme := congrArg StageType.toScheme he
  obtain ⟨i, hi⟩ : ∃ i : Fin (Am.toScheme.comap f).card,
      (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex d := by
    rw [heq]; exact ⟨Fin.castSucc d, gradedIndex_T5_castSucc d⟩
  exact ⟨Am.toScheme.cellMap f i, by rw [← Am.toScheme.map_comap_gradedIndex f i, hi]⟩

private theorem exists_d₁ {I : Seed.{u} α 3} (h : I.left = T5 α) : ∃ e : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex e = (({3} : Finset (Fin 5)), 1) := by
  obtain ⟨e, he⟩ := exists_cell (h ▸ I.restrictFace_left) 3
  exact ⟨e, he.trans (by decide +kernel)⟩

private theorem exists_d₂ {I : Seed.{u} α 3} (h : I.right = T5 α) : ∃ e : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex e = (({4} : Finset (Fin 5)), 1) := by
  obtain ⟨e, he⟩ := exists_cell (h ▸ I.restrictFace_right) 3
  exact ⟨e, he.trans (by decide +kernel)⟩

private theorem exists_s {I : Seed.{u} α 3} (h : I.right = T5 α) : ∃ e : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
  obtain ⟨e, he⟩ := exists_cell (h ▸ I.restrictFace_right) 15
  exact ⟨e, he.trans (by decide +kernel)⟩

/-- The cell at `({0, 1, 2, 3}, 3)`, the cell `18` of the first coatom. -/
private theorem exists_g {I : Seed.{u} α 3} (h : I.left = T5 α) : ∃ e : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2, 3} : Finset (Fin 5)), 3) := by
  obtain ⟨e, he⟩ := exists_cell (h ▸ I.restrictFace_left) 18
  exact ⟨e, he.trans (by decide +kernel)⟩

/-- **The old cells of the grade `3` are not dead**: `tripleLabelling ⊤ ⊤ ⊤ ⊤ ⊤` is lawful below
the first coatom at the grade `3` and is `⊤` at the cell `({0, 1, 2, 3}, 3)`. -/
theorem not_deadAt_two {I : Seed.{u} α 3} (hIL : I.left = T5 α) (hIR : I.right = T5 α) :
    ¬ I.DeadAt 2 := by
  intro H
  obtain ⟨g, hg⟩ := exists_g hIL
  have hlaw := (isLawfulBelow_tripleLabelling (AC := ⊤) (FC := ⊤) (AD := ⊤) (FD := ⊤) (G := ⊤)
    hIL hIR (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 1)
    (isSelfVisible_top 2) (isSelfVisible_top 3) le_rfl le_rfl le_rfl le_rfl).1
  have hmem : g ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.last (3 + 1)), 2 + 1) := by
    change I.amalgam.toCellScheme.gradedIndex g ≤ _
    rw [hg]; decide +kernel
  have hgr : I.amalgam.toCellScheme.grade g = 2 + 1 := congrArg Prod.snd hg
  have := H (Fin.last (3 + 1)) (by simp)
    (fun d ↦ tripleLabelling ⊤ ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d)) hlaw g hmem hgr
  have hk : tripleKind (({0, 1, 2, 3} : Finset (Fin 5)), 3) = 5 := by decide
  rw [hg, tripleLabelling, hk] at this
  exact top_ne_bot this

/-! ### The refutation -/

/-- With `G = ⊥`, the labelling `tripleLabelling` is the labelling `pairLabelling` of `T4`. -/
private theorem tripleLabelling_bot (AC FC AD FD : Label.{u}) :
    tripleLabelling AC FC AD FD ⊥ = pairLabelling AC FC AD FD := by
  funext X
  unfold tripleLabelling tripleKind pairLabelling pairKind
  split_ifs <;> rfl

/-- **`2FL(2)` fails on every seed on five points whose two coatom types are `T5`.**  With the
parameter `G = ⊥`, the labellings `tripleLabelling A_C F_C A_D F_D ⊥` are the labellings
`pairLabelling A_C F_C A_D F_D` of `T4`, lawful below both coatoms at the grade `3`; so the
argument for `T4` applies verbatim, with the cells `d₁ = ({3}, 1)`, `d₂ = ({4}, 1)` and
`s = ({0, 1, 2, 4}, 2)`
(`TwoFaceLiftCounterexample.not_twoFaceLift_two_of_isLawfulBelow_pairLabelling`): the strip of
`T4` at the grade `1` is unchanged by the live cells of grade `3`. -/
theorem not_twoFaceLift_two_of {I : Seed.{u} α 3} (hIL : I.left = T5 α) (hIR : I.right = T5 α) :
    ¬ I.TwoFaceLift 2 := by
  obtain ⟨d₁, hd₁⟩ := exists_d₁ hIL
  obtain ⟨d₂, hd₂⟩ := exists_d₂ hIR
  obtain ⟨sD, hsD⟩ := exists_s hIR
  refine TwoFaceLiftCounterexample.not_twoFaceLift_two_of_isLawfulBelow_pairLabelling hd₁ hd₂ hsD
    fun hAC hFC hAD hFD ↦ ?_
  simpa only [tripleLabelling_bot] using isLawfulBelow_tripleLabelling hIL hIR hAC hFC hAD hFD
    (isSelfVisible_bot 3) bot_le bot_le bot_le bot_le

/-- **`2FL(2)` fails for the seed of `T5` with itself.** -/
theorem not_twoFaceLift_two : ¬ (seed5 α).TwoFaceLift 2 :=
  not_twoFaceLift_two_of rfl rfl

/-- **Both per-seed hypotheses of the library fail for the seed of `T5` with itself at the grade
`2`**: `2FL(2)` fails and the old cells of the grade `3` are not dead. -/
theorem not_twoFaceLift_or_deadAt : ¬ ((seed5 α).TwoFaceLift 2 ∨ (seed5 α).DeadAt 2) :=
  fun h ↦ h.elim not_twoFaceLift_two (not_deadAt_two rfl rfl)

/-! ### The existential two-face lift for the seeds of `T5` -/

theorem cases_T5 (i : Fin (T5 α).card) :
    i = Fin.last 19 ∨ ∃ d : Fin 19, i = Fin.castSucc d := by
  change Fin (19 + 1) at i
  induction i using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- `T5` has one cell at each graded index. -/
theorem gradedIndex_injective_T5 : Function.Injective (T5 α).toCellScheme.gradedIndex := by
  have hlt : ∀ c : Fin 19, TwoFaceLiftCounterexample.cellGrade c ≠ 4 := by decide
  intro i i' h
  rcases cases_T5 i with rfl | ⟨c, rfl⟩ <;> rcases cases_T5 i' with rfl | ⟨c', rfl⟩
  · rfl
  · exact absurd (congrArg Prod.snd (gradedIndex_T5_last.symm.trans
      (h.trans (gradedIndex_T5_castSucc c')))).symm (hlt c')
  · exact absurd (congrArg Prod.snd ((gradedIndex_T5_castSucc c).symm.trans
      (h.trans gradedIndex_T5_last))) (hlt c)
  · rw [TwoFaceLiftCounterexample.gradedIndex_injective
      ((gradedIndex_T5_castSucc c).symm.trans (h.trans (gradedIndex_T5_castSucc c')))]

/-- Lawful labellings of an amalgam below a coatom whose type is `T5`, read on `T5`. -/
theorem exists_labelling_of_comap {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T5 α)) {k : ℕ} (hk : k ≤ 3)
    (p : Fin Am.card → Label.{u}) (hp : Am.rows.IsLawfulBelow (univ.map f, k) fun d ↦ p d) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧
      G ≤ F ∧ ∀ d ∈ Am.toCellScheme.below (univ.map f, k), ∃ c : Fin 19,
        Am.toCellScheme.gradedIndex d = Prod.map (Finset.map f) id (cells.gradedIndex c) ∧
        p d = labelling A F G c := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T5 α).toScheme := congrArg StageType.toScheme he
  have hgen : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), k) (fun i ↦ x i) →
      ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧
        G ≤ F ∧ ∀ i ∈ (Am.toScheme.comap f).toCellScheme.below ((univ : Finset (Fin 4)), k),
          ∃ c : Fin 19, (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex c ∧
            x i = labelling A F G c := by
    rw [heq]
    intro x hx
    have hx' := (isLawfulBelow_T5_iff (α := α) (w := x) (fun h ↦ by
      have := h.2; simp only at this; omega)).mp hx
    obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hAF⟩ :=
      (isLawfulBelow_iff (x := fun e ↦ x (Fin.castSucc e))).mp hx'
    refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun i hi ↦ ?_⟩
    rcases cases_T5 (α := α) i with rfl | ⟨c, rfl⟩
    · exfalso
      have h2 := hi.2
      rw [gradedIndex_T5_last] at h2
      simp only at h2
      omega
    · refine ⟨c, gradedIndex_T5_castSucc c, hAF c ?_⟩
      change cells.gradedIndex c ≤ _
      rw [← gradedIndex_T5_castSucc (α := α) c]
      exact hi
  obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hall⟩ := hgen (fun i ↦ p (Am.toScheme.cellMap f i))
    ((Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f _ p).mpr hp)
  refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun d hd ↦ ?_⟩
  have hd' : d ∈ Am.toScheme.cellMap f '' (Am.toScheme.comap f).toCellScheme.below
      ((univ : Finset (Fin 4)), k) := by
    rw [Am.toScheme.image_cellMap_below f]; exact hd
  obtain ⟨i, hi, rfl⟩ := hd'
  obtain ⟨c, hgi, hpc⟩ := hall i hi
  exact ⟨c, by rw [← Am.toScheme.map_comap_gradedIndex f i, hgi], hpc⟩

/-- **Lawful labellings of the amalgam below a coatom**, on a seed whose coatom types are `T5`:
`tripleLabelling A F A F G` read off graded indices. -/
private theorem exists_tripleLabelling {I : Seed.{u} α 3} (hIL : I.left = T5 α)
    (hIR : I.right = T5 α) {z : Fin (3 + 2)}
    (hz : z ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2))))
    {k : ℕ} (hk : k ≤ 3) (p : Fin I.amalgam.card → Label.{u})
    (hp : I.amalgam.rows.IsLawfulBelow (univ.erase z, k) fun d ↦ p d) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧
      G ≤ F ∧ ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase z, k),
        p d = tripleLabelling A F A F G (I.amalgam.toCellScheme.gradedIndex d) := by
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl
  · rw [← Coatom.univ_map_left] at hp ⊢
    obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hall⟩ :=
      exists_labelling_of_comap (hIL ▸ I.restrictFace_left) hk p hp
    refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun d hd ↦ ?_⟩
    obtain ⟨c, hgi, hpc⟩ := hall d hd
    rw [hpc, hgi, tripleLabelling_left]
  · rw [← Coatom.univ_map_right] at hp ⊢
    obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hall⟩ :=
      exists_labelling_of_comap (hIR ▸ I.restrictFace_right) hk p hp
    refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun d hd ↦ ?_⟩
    obtain ⟨c, hgi, hpc⟩ := hall d hd
    rw [hpc, hgi, tripleLabelling_right]

private theorem liveC_three : ∀ Y ∈ liveC, (3 : Fin 5) ∈ Y.1 ∧ Y.2 ≤ 2 := by decide
private theorem liveD_four : ∀ Y ∈ liveD, (4 : Fin 5) ∈ Y.1 ∧ Y.2 ≤ 2 := by decide
theorem liveG_three : ∀ Y ∈ liveG, Y.2 = 3 := by decide

/-- At a graded index of grade at most `2`, the parameter `G` is not read. -/
theorem tripleLabelling_eq_of_le_two {X : Finset (Fin 5) × ℕ} (hX : X.2 ≤ 2)
    (A F A' F' G G' : Label.{u}) :
    tripleLabelling A F A' F' G X = tripleLabelling A F A' F' G' X := by
  have hG : X ∉ liveG := fun h ↦ by have := liveG_three X h; omega
  unfold tripleLabelling tripleKind
  split_ifs <;> rfl

/-- At a graded index of grade at most `2`, `tripleLabelling A F A F G` is `⊥`, `A` or `F`. -/
private theorem tripleLabelling_cases {X : Finset (Fin 5) × ℕ} (hX : X.2 ≤ 2)
    (A F G : Label.{u}) :
    tripleLabelling A F A F G X = ⊥ ∨ tripleLabelling A F A F G X = A ∨
      tripleLabelling A F A F G X = F := by
  have hG : X ∉ liveG := fun h ↦ by have := liveG_three X h; omega
  unfold tripleLabelling tripleKind
  split_ifs
  all_goals first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr rfl)

/-- At a graded index of grade `3`, `tripleLabelling A F A' F' G` is `G` or `⊥`, by the index. -/
private theorem tripleLabelling_of_three {X : Finset (Fin 5) × ℕ} (hX : X.2 = 3)
    (A F A' F' G : Label.{u}) :
    tripleLabelling A F A' F' G X = if X ∈ liveG then G else ⊥ := by
  have hC : X ∉ liveC := fun h ↦ by have := (liveC_three X h).2; omega
  have hD : X ∉ liveD := fun h ↦ by have := (liveD_four X h).2; omega
  unfold tripleLabelling tripleKind
  rw [ite_eq_right hC, ite_eq_right hD]
  split_ifs <;> rfl

/-- On the common face, the parameters `A`, `F` are not read. -/
private theorem tripleLabelling_eq_of_subset {X : Finset (Fin 5) × ℕ}
    (hX : X.1 ⊆ ({0, 1, 2} : Finset (Fin 5))) (A F A' F' A₂ F₂ A₂' F₂' G : Label.{u}) :
    tripleLabelling A F A' F' G X = tripleLabelling A₂ F₂ A₂' F₂' G X := by
  have hC : X ∉ liveC := fun h ↦ by
    have := hX (liveC_three X h).1; revert this; decide
  have hD : X ∉ liveD := fun h ↦ by
    have := hX (liveD_four X h).1; revert this; decide
  unfold tripleLabelling tripleKind
  rw [ite_eq_right hC, ite_eq_right hD]
  split_ifs <;> rfl

private theorem erase_inter_erase_five {x y : Fin (3 + 2)}
    (hx : x ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2))))
    (hy : y ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2))))
    (hxy : x ≠ y) : univ.erase x ∩ univ.erase y = ({0, 1, 2} : Finset (Fin 5)) := by
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · decide
  · decide
  · exact absurd rfl hxy

/-- A cell of grade `1` of each coatom read as `A`. -/
private theorem exists_cell_A {I : Seed.{u} α 3} (hIL : I.left = T5 α) (hIR : I.right = T5 α)
    {z : Fin (3 + 2)}
    (hz : z ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2)))) :
    ∃ d ∈ I.amalgam.toCellScheme.below (univ.erase z, 2), ∀ A F G : Label.{u},
      tripleLabelling A F A F G (I.amalgam.toCellScheme.gradedIndex d) = A := by
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl
  · obtain ⟨d, hd⟩ := exists_d₁ hIL
    have hk : tripleKind (({3} : Finset (Fin 5)), 1) = 1 := by decide
    refine ⟨d, ?_, fun A F G ↦ ?_⟩
    · change I.amalgam.toCellScheme.gradedIndex d ≤ _
      rw [hd]; decide +kernel
    · simp only [tripleLabelling, hd, hk]; rfl
  · obtain ⟨d, hd⟩ := exists_d₂ hIR
    have hk : tripleKind (({4} : Finset (Fin 5)), 1) = 3 := by decide
    refine ⟨d, ?_, fun A F G ↦ ?_⟩
    · change I.amalgam.toCellScheme.gradedIndex d ≤ _
      rw [hd]; decide +kernel
    · simp only [tripleLabelling, hd, hk]; rfl

/-- The cell of grade `2` of each coatom, read as `F`. -/
private theorem exists_cell_F {I : Seed.{u} α 3} (hIL : I.left = T5 α) (hIR : I.right = T5 α)
    {z : Fin (3 + 2)}
    (hz : z ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2)))) :
    ∃ d ∈ I.amalgam.toCellScheme.below (univ.erase z, 2), ∀ A F G : Label.{u},
      tripleLabelling A F A F G (I.amalgam.toCellScheme.gradedIndex d) = F := by
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl
  · obtain ⟨d, hd⟩ := exists_cell (hIL ▸ I.restrictFace_left) 15
    have hd' : I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) :=
      hd.trans (by decide +kernel)
    have hk : tripleKind (({0, 1, 2, 3} : Finset (Fin 5)), 2) = 2 := by decide
    refine ⟨d, ?_, fun A F G ↦ ?_⟩
    · change I.amalgam.toCellScheme.gradedIndex d ≤ _
      rw [hd']; decide +kernel
    · simp only [tripleLabelling, hd', hk]; rfl
  · obtain ⟨d, hd⟩ := exists_s hIR
    have hk : tripleKind (({0, 1, 2, 4} : Finset (Fin 5)), 2) = 4 := by decide
    refine ⟨d, ?_, fun A F G ↦ ?_⟩
    · change I.amalgam.toCellScheme.gradedIndex d ≤ _
      rw [hd]; decide +kernel
    · simp only [tripleLabelling, hd, hk]; rfl

/-- The cell of grade `3` of the common face. -/
private theorem exists_cell_E {I : Seed.{u} α 3} (hIL : I.left = T5 α) :
    ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
  obtain ⟨d, hd⟩ := exists_cell (hIL ▸ I.restrictFace_left) 16
  exact ⟨d, hd.trans (by decide +kernel)⟩

private theorem mem_below_E {z : Fin (3 + 2)}
    (hz : z ∈ ({Fin.last (3 + 1), Fin.castSucc (Fin.last 3)} : Finset (Fin (3 + 2)))) :
    ((({0, 1, 2} : Finset (Fin 5)), 3) : Finset (Fin 5) × ℕ) ≤ (univ.erase z, 3) := by
  simp only [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl <;> decide +kernel

/-- **The raised union fill at the grade `2` holds on every seed on five points whose two coatom
types are `T5`.**  The cap is `max h G`, where `G` is the prescribed label of the cell of grade `3`
on the common face: every cell of `C` where `a` reaches `h` is live, hence carries at least `G`.  A
labelling `V` of the other coatom agreeing at that cap with `a` raised above `h` is at least `G` at
the live cells of grade `1` and `2` (above the cap by the raising, below it because `a` itself is
at least `G` there and then `G` is the label of `a`), so `V` with `G` at its live cells of grade
`3` is lawful below `(D, 3)`. -/
theorem raisedUnionFill_two {I : Seed.{u} α 3} (hIL : I.left = T5 α) (hIR : I.right = T5 α) :
    I.RaisedUnionFill 2 := by
  classical
  intro x hx y hy hxy a _ haD h hh _ hbot wC hwC hag
  obtain ⟨AC, FC, GC, -, -, hGC, hGAC, hGFC, hwCt⟩ :=
    exists_tripleLabelling hIL hIR hx (k := 2 + 1) (by omega) wC hwC
  obtain ⟨Aa, Fa, Ga, -, -, -, hGAa, hGFa, haDt⟩ :=
    exists_tripleLabelling hIL hIR hy (k := 2 + 1) (by omega) a haD
  -- The cell of grade `3` of the common face.
  obtain ⟨gE, hgE⟩ := exists_cell_E hIL
  have hgEx : gE ∈ I.amalgam.toCellScheme.below (univ.erase x, 2 + 1) := by
    change I.amalgam.toCellScheme.gradedIndex gE ≤ _; rw [hgE]; exact mem_below_E hx
  have hgEy : gE ∈ I.amalgam.toCellScheme.below (univ.erase y, 2 + 1) := by
    change I.amalgam.toCellScheme.gradedIndex gE ≤ _; rw [hgE]; exact mem_below_E hy
  have hkE : (({0, 1, 2} : Finset (Fin 5)), 3) ∈ liveG := by decide
  have hwgE : wC gE = GC := by
    rw [hwCt gE hgEx, hgE, tripleLabelling_of_three rfl, ite_eq_left hkE]
  have hagE : a gE = Ga := by
    rw [haDt gE hgEy, hgE, tripleLabelling_of_three rfl, ite_eq_left hkE]
  have hGCh : min GC h = min Ga h := by rw [← hwgE, ← hagE]; exact hag gE hgEx
  -- Where `a` is below the cap, so is `Ga`, and then `GC = Ga`.
  have hGCa (z : Label.{u}) (hGz : Ga ≤ z) (hz : z < h) : GC = Ga := by
    exact eq_of_min_eq_of_lt hGCh.symm (hGz.trans_lt hz)
  have hhc : h ≤ max h GC := le_max_left _ _
  have hGc : GC ≤ max h GC := le_max_right _ _
  refine ⟨max h GC, (hh.mono (by omega)).max (hGC.mono (by omega)), hhc,
    fun d hdC hle ↦ ?_, fun V hVD hVa _ ↦ ?_⟩
  · -- A cell of `C` where `a` reaches the cap carries at least `max h GC`.
    have hdC3 : d ∈ I.amalgam.toCellScheme.below (univ.erase x, 2 + 1) :=
      ⟨hdC.1, hdC.2.trans (by omega)⟩
    have hagd := hag d hdC3
    rw [min_eq_right hle] at hagd
    have hhw : h ≤ wC d := min_eq_right_iff.mp hagd
    have hGw : GC ≤ wC d := by
      rw [hwCt d hdC3]
      have hd2 : (I.amalgam.toCellScheme.gradedIndex d).2 ≤ 2 := hdC.2
      rcases tripleLabelling_cases hd2 AC FC GC with h0 | h0 | h0 <;> rw [h0]
      · rw [hwCt d hdC3, h0] at hhw; exact absurd (hbot.trans_le hhw) (lt_irrefl _)
      · exact hGAC
      · exact hGFC
    exact max_le hhw hGw
  -- The fill of the other coatom.
  obtain ⟨AV, FV, GV, hAV, hFV, -, -, -, hVt⟩ := exists_tripleLabelling hIL hIR hy (by omega) V hVD
  have hkey (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, 2))
      (hGd : Ga ≤ a d) : GC ≤ V d := by
    have hvd := hVa d hd
    by_cases hle : h ≤ a d
    · unfold raise at hvd
      rw [ite_eq_left hle, min_top_left] at hvd
      exact hGc.trans (min_eq_right_iff.mp hvd)
    · have hlt := not_le.mp hle
      unfold raise at hvd
      rw [ite_eq_right hle] at hvd
      rw [eq_of_min_eq_of_lt hvd.symm (hlt.trans_le hhc), hGCa _ hGd hlt]
      exact hGd
  obtain ⟨dA, hdA, hdAv⟩ := exists_cell_A hIL hIR hy
  obtain ⟨dF, hdF, hdFv⟩ := exists_cell_F hIL hIR hy
  have hdA3 : dA ∈ I.amalgam.toCellScheme.below (univ.erase y, 2 + 1) :=
    ⟨hdA.1, hdA.2.trans (by omega)⟩
  have hdF3 : dF ∈ I.amalgam.toCellScheme.below (univ.erase y, 2 + 1) :=
    ⟨hdF.1, hdF.2.trans (by omega)⟩
  have hGAV : GC ≤ AV := by
    have := hkey dA hdA (by rw [haDt dA hdA3, hdAv]; exact hGAa)
    rwa [hVt dA hdA, hdAv] at this
  have hGFV : GC ≤ FV := by
    have := hkey dF hdF (by rw [haDt dF hdF3, hdFv]; exact hGFa)
    rwa [hVt dF hdF, hdFv] at this
  set wD : Fin I.amalgam.card → Label.{u} := fun d ↦
    tripleLabelling AV FV AV FV GC (I.amalgam.toCellScheme.gradedIndex d) with hwD_def
  have hwDl : I.amalgam.rows.IsLawfulBelow (univ.erase y, 2 + 1) fun d ↦ wD d := by
    have hboth := isLawfulBelow_tripleLabelling (I := I) hIL hIR hAV hFV hAV hFV hGC hGAV hGFV
      hGAV hGFV
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hboth.1
    · exact hboth.2
  refine ⟨wD, hwDl, fun d hd ↦ ?_, fun d hdC hdD _ ↦ ?_, fun d hdD hdj ↦ ?_⟩
  · rw [hVt d hd]
    exact tripleLabelling_eq_of_le_two hd.2 _ _ _ _ _ _
  · -- On the common face, `wD` is the prescription.
    rw [hwCt d hdC]
    have hsc : (I.amalgam.toCellScheme.gradedIndex d).1 ⊆ ({0, 1, 2} : Finset (Fin 5)) := by
      rw [← erase_inter_erase_five hx hy hxy]
      exact subset_inter hdC.1 hdD.1
    exact tripleLabelling_eq_of_subset hsc _ _ _ _ _ _ _ _ _
  · -- At the cells of the grade `3`, `wD` agrees with `a` capped at `h`.
    have hd3 : (I.amalgam.toCellScheme.gradedIndex d).2 = 3 := by
      have h3 := hdD.2
      change I.amalgam.toCellScheme.grade d ≤ 2 + 1 at h3
      change I.amalgam.toCellScheme.grade d = 3
      omega
    rw [haDt d hdD, hwD_def]
    dsimp only
    rw [tripleLabelling_of_three hd3, tripleLabelling_of_three hd3]
    split_ifs
    · exact hGCh
    · rfl

/-- **`2FL∃(2)` holds on every seed on five points whose two coatom types are `T5`**: the raised
union fill (`raisedUnionFill_two`) and the invariant at the grade `2`. -/
theorem twoFaceLiftExists_two {I : Seed.{u} α 3} (hIL : I.left = T5 α) (hIR : I.right = T5 α) :
    I.TwoFaceLiftExists 2 :=
  I.twoFaceLiftExists_of_raisedUnionFill
    (I.towerInvariant_succ (by omega) I.towerInvariant_one I.twoFaceLift_one)
    (raisedUnionFill_two hIL hIR)

/-- **The invariant at the grade `3`** on a seed on five points whose two coatom types are `T5`,
although neither `2FL(2)` nor deadness holds there: the step under `2FL∃(2)`. -/
theorem towerInvariant_three {I : Seed.{u} α 3} (hIL : I.left = T5 α) (hIR : I.right = T5 α) :
    I.TowerInvariant 3 :=
  I.towerInvariant_succ_of_twoFaceLiftExists (j := 2) (by omega)
    (I.towerInvariant_succ (by omega) I.towerInvariant_one I.twoFaceLift_one)
    (twoFaceLiftExists_two hIL hIR)

/-- **A seed on five points whose two coatom types are `T5` has a completion below the full
grade**, through the tower: the only grade `2 ≤ j < 3` is `j = 2`, where `2FL∃(2)` holds
(`twoFaceLiftExists_two`). -/
theorem nonempty_completionBelowFullGrade_of {I : Seed.{u} α 3} (hIL : I.left = T5 α)
    (hIR : I.right = T5 α) : Nonempty (CompletionBelowFullGrade I) :=
  I.nonempty_completionBelowFullGrade_of_twoFaceLiftExists fun j hj hjm ↦ by
    obtain rfl : j = 2 := by omega
    exact twoFaceLiftExists_two hIL hIR

/-- **The seed of `T5` with itself has a completion below the full grade**, although the case
split `2FL(2) ∨ Seed.DeadAt 2` fails for it (`not_twoFaceLift_or_deadAt`). -/
theorem nonempty_completionBelowFullGrade_seed5 :
    Nonempty (CompletionBelowFullGrade (seed5 α)) :=
  nonempty_completionBelowFullGrade_of rfl rfl

/-- **`2FL∃(2)` holds where the case split `2FL(2) ∨ Seed.DeadAt 2` fails**: for the seed of `T5`
with itself.  On this seed each disjunct implies `2FL∃(2)` (`Seed.twoFaceLiftExists_of_twoFaceLift`,
which needs `2 ≤ m`, here `m = 3`; `Seed.twoFaceLiftExists_of_deadAt`, which needs the invariant at
the grade `2`, here from `Seed.twoFaceLift_one`), so on this seed the case split is strictly
stronger than the hypothesis of the step stated exactly. -/
theorem twoFaceLiftExists_and_not_twoFaceLift_or_deadAt :
    (seed5 α).TwoFaceLiftExists 2 ∧ ¬ ((seed5 α).TwoFaceLift 2 ∨ (seed5 α).DeadAt 2) :=
  ⟨twoFaceLiftExists_two rfl rfl, not_twoFaceLift_or_deadAt⟩

end SeedLevel

/-- **The case split `2FL(j) ∨ Seed.DeadAt j` at the grades `2 ≤ j < m` does not cover every
legal seed**, at every stage: it fails for `seed5` at `j = 2`.  This refutes the case split as a
statement of coverage, not the completion: `seed5` has a completion below the full grade
(`nonempty_completionBelowFullGrade_seed5`). -/
theorem not_forall_twoFaceLift_or_deadAt (α : Ordinal.{u}) :
    ¬ ∀ (m : ℕ) (I : Seed.{u} α m) (j : ℕ), 2 ≤ j → j < m → I.TwoFaceLift j ∨ I.DeadAt j :=
  fun h ↦ not_twoFaceLift_or_deadAt (h 3 (seed5 α) 2 le_rfl (by omega))

/-- **`2FL∃(2)` holds for `seed4`**, through deadness of its old cells of the grade `3` and the
invariant at the grade `2`. -/
theorem twoFaceLiftExists_two_seed4 (α : Ordinal.{u}) :
    (TwoFaceLiftCounterexample.seed4 α).TwoFaceLiftExists 2 :=
  (TwoFaceLiftCounterexample.seed4 α).twoFaceLiftExists_of_deadAt
    ((TwoFaceLiftCounterexample.seed4 α).towerInvariant_succ (by omega)
      (TwoFaceLiftCounterexample.seed4 α).towerInvariant_one
      (TwoFaceLiftCounterexample.seed4 α).twoFaceLift_one)
    (TwoFaceLiftCounterexample.deadAt_two rfl rfl)

end VaughtConjecture.CaseSplitCounterexample
