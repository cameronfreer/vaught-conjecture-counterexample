/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.DeadCellStep
import VaughtConjecture.Extension.TowerExamples
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Label.StepWitness

/-!
# A legal seed on which the two-face lift at the grade two fails

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here the negative
example for the two-face lift `2FL(j)` at `j ≥ 2`, and the completion for that seed by the step
from deadness, defined below); semantic contract, items 2–4.

The two-face lift `2FL(j)` (`Seed.TwoFaceLift`, module `VaughtConjecture.Extension.Tower`) holds
at `j = 1` for every seed (`Seed.twoFaceLift_one`).  This module shows that `2FL(2)` fails for a
legal seed on five points (`not_twoFaceLift_two`), so that `2FL(j)` at the grades `2 ≤ j < m` is
false as a statement about every seed, at every stage (`not_forall_twoFaceLift`).  The completion
below the full grade of that seed exists (`nonempty_completionBelowFullGrade_seed4`).

**The legal type `T4`** (`T4`, `isLegal_T4`).  The scheme `S` on four points has the interval
plan (faces `∅`, the singletons, `{0, 1}`, `{1, 2}`, `{2, 3}`, `{0, 1, 2}`, `{1, 2, 3}`, `univ`)
and one cell at every graded face of grade at most `3`, nineteen cells in all; `T4` is `S` with
the apex added (`StageType.addApex`).  The *live* cells are the cells of grade `1` whose scope
contains the point `3` (at `{3}`, `{2, 3}`, `{1, 2, 3}` and `univ`) and the cell at `(univ, 2)`;
the other cells, every cell of grade `3` among them, are *dead*.  The row of a dead cell is `⊥`;
the row of a live cell reads the live cells of grade `1` at the ordinal `1` and the live cell of
grade `2` at `ω + 2`, and the dead cells at `⊥`.

**The lawful labellings** (`isLawfulBelow_iff`).  Below every pair, the lawful labellings are the
restrictions of `labelling A F`: `⊥` at the dead cells, `A` at the live cells of grade `1` and `F`
at the live cell of grade `2`, for `A` self-visible at `1` and `F` self-visible at `2`, with no
relation between `A` and `F`.  Sufficiency at the live cell of grade `2` uses the *strip shifter*
of `A` (`stripShifter`, `isWitness_stripShifter`), a witness for the suppressor `F` up to the grade
`2`: it sends `⊥` to `⊥`, the natural numbers `0`, `1`, `≥ 2` to the *strip* of `A` (the labels
`visibilityReplace 2 i A` for `i = 0, 1, 2`, which replace a finite part of `A` below `2` by
`i`), and every label `≥ ω` to `⊤`.  Capped by the suppressor, it carries the row of that cell to
`min A F` at the live cells of grade `1` and to `F` at the cell itself.  Every pair lifts capped to
every larger one (`cappedLift_all`), so `T4` is legal.

**The seed** (`seed4`).  The seed of `T4` with itself over its face `{0, 1, 2}`
(`Seed.ofCoatoms`) has coatoms `C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}` and common face
`E = {0, 1, 2}`, which carries only dead cells.  The labellings of the amalgam used are read off
graded indices (`pairLabelling A_C F_C A_D F_D`, lawful below both coatoms at the grade `3` by
`isLawfulBelow_pairLabelling`).  The statements are proved for every seed on five points whose two
coatom types are `T4` (`I.left = T4 α`, `I.right = T4 α`) and specialized to `seed4` by `rfl`.

**The failure** (`not_twoFaceLift_two_of`, `not_twoFaceLift_two`).  Take `d₁` the cell at
`({3}, 1)` on `C`, `d₂` the cell at `({4}, 1)` on `D`, and `s` the cell at `({0, 1, 2, 4}, 2)`.  A
catalogue entry `b₀` of the layer at the grade `2` takes one value `β₁` at `d₁` and `d₂`, with
finite part `1` and strictly below its *strip cap* `h₂ = visibilityReplace 2 2 β₁`.  The catalogue
entry `a` at the grade `3` built from `b₀` reaches the cap `h` at a new cell of the layer at the
grade `2` only when the entry of that cell agrees with `b₀` capped at `h₂`, so that its row reads
`d₁` and `d₂` at the same value.  The prescription `w`, equal to `a` on `C` and to `⊤` at the live
cells of `D`, is lawful below both coatoms and agrees with `a` capped at `h`.  A two-face lift
would be `⊤` at `s`, hence, by availability, `⊤` at a new cell `u` at `(univ, 2)`; locality at `u`
would then force the prescriptions at `d₁` and `d₂` to be equal.  They are not.

**What this shows.**  The failure concerns the existence of the extension, not a method of
constructing it: no labelling with the three properties of `2FL(2)` exists for these `a`, `h` and
`w`.  The two cells `d₁` and `d₂` lie on different coatoms, are read at equal values of the row of
every new cell where `a` reaches the cap, and carry prescriptions that differ above the cap.  No
old cell reads both `d₁` and `d₂`: only the new cells at `(univ, 2)` see both coatoms, and their
labels are capped by `a`.  So the strip case of the alignment described in the module
`VaughtConjecture.Extension.TwoFaceLift` occurs, and in it no extension exists.

**The completion is not refuted** (`deadAt_two`, `towerInvariant_three`,
`nonempty_completionBelowFullGrade_of`, `nonempty_completionBelowFullGrade_seed4`).  Every cell of
grade `3` of `T4` is dead, so on these seeds the old cells of the grade `3` are dead
(`Seed.DeadAt 2`), and the step from deadness (`Seed.towerInvariant_succ_of_dead`, module
`VaughtConjecture.Extension.DeadCellStep`) gives the invariant at the grade `3` without `2FL(2)`.
With the step to the top grade the invariant holds at the grade `4`, and the tower is a completion
below the full grade.  So `seed4` has a completion below the full grade although `2FL(2)` fails
for it.

## Placement

Checkpoint 2.6 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.TwoFaceLiftCounterexample

open Finset Label CellScheme
open Ordinal hiding univ
open TowerExamples (Q)

/-! ### The scheme on four points -/

/-- The scopes of the nineteen cells. -/
def cellScope : Fin 19 → Finset (Fin 4) :=
  ![{0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {2, 3}, {0, 1, 2}, {1, 2, 3}, univ,
    {0, 1}, {1, 2}, {2, 3}, {0, 1, 2}, {1, 2, 3}, univ,
    {0, 1, 2}, {1, 2, 3}, univ]

/-- The grades of the nineteen cells. -/
def cellGrade : Fin 19 → ℕ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3]

/-- The live cells: grade `1` through the point `3`, and `(univ, 2)`. -/
def live : Fin 19 → Bool :=
  ![false, false, false, true, false, false, true, false, true, true,
    false, false, false, false, false, true, false, false, false]

/-- The cell scheme on four points with the interval plan. -/
def cells : CellScheme (Fin 19) (Fin 4) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

/-- The row value at the live cells of grade `1`: the ordinal `1`. -/
noncomputable abbrev v1 : Label.{u} := gridPoint 1 0

/-- The row value at the live cell of grade `2`: the ordinal `ω + 2`. -/
noncomputable abbrev v2 : Label.{u} := gridPoint 2 1

/-- The labelling with `⊥` at the dead cells, `A` at the live cells of grade `1`, and `F` at the
live cell of grade `2`. -/
noncomputable def labelling (A F : Label.{u}) (d : Fin 19) : Label.{u} :=
  if live d = true then (if cellGrade d = 1 then A else F) else ⊥

/-- The rows: a live cell reads `labelling v1 v2`; a dead cell reads `⊥`. -/
noncomputable def rows : cells.Rows.{u} :=
  ⟨fun s t ↦ if live s = true ∧ live t.1 = true then (if cellGrade t.1 = 1 then v1 else v2)
    else ⊥⟩

/-- The scheme on four points. -/
noncomputable def S : Scheme.{u} 4 := ⟨19, cells, rows⟩

theorem gradedIndex_cells (d : Fin 19) : cells.gradedIndex d = (cellScope d, cellGrade d) := rfl

theorem gradedIndex_injective : Function.Injective cells.gradedIndex := by
  intro a b h
  rw [gradedIndex_cells, gradedIndex_cells] at h
  revert a b; decide +kernel

/-- A live cell below a live cell of grade `1` has grade `1`; below a live cell of grade `2`,
grade `1` or `2`. -/
private theorem live_le_live : ∀ s d : Fin 19, live s = true → live d = true →
    cells.gradedIndex d ≤ cells.gradedIndex s →
      cellGrade d = cellGrade s ∨ (cellGrade d = 1 ∧ cellGrade s = 2) := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The live cells are closed upward under inclusion of scopes at the same grade. -/
private theorem live_up : ∀ s t : Fin 19, live s = true → cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → live t = true := by decide +kernel

private theorem live_grade (d : Fin 19) (hd : live d = true) :
    cellGrade d = 1 ∨ cellGrade d = 2 := by
  revert d; decide +kernel

/-! ### The shifters -/

/-- The **strip shifter** of `A`: `⊥ ↦ ⊥`; the natural numbers `0`, `1` and `≥ 2` go to the
replacements `visibilityReplace 2 i A` for `i = 0, 1, 2` (the *strip* of `A`: its values with
finite part below `2` replaced); every label `≥ ω` goes to `⊤`. -/
noncomputable def stripShifter (A x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else if x < ((ω : Ordinal.{u}) : Label.{u}) then
    (if x = 0 then visibilityReplace 2 0 A else if x = 1 then visibilityReplace 2 1 A
      else visibilityReplace 2 2 A)
  else ⊤

/-! ### Facts about labels -/

private theorem natCast_label (n : ℕ) : (n : Label.{u}) = ((n : Ordinal.{u}) : Label.{u}) := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast]

private theorem natCast_label_inj {n m : ℕ} : (n : Label.{u}) = m ↔ n = m := by
  rw [natCast_label, natCast_label, WithBot.coe_inj, WithTop.coe_inj, Nat.cast_inj]

private theorem natCast_label_le {n m : ℕ} : (n : Label.{u}) ≤ m ↔ n ≤ m := by
  rw [natCast_label, natCast_label, WithBot.coe_le_coe, WithTop.coe_le_coe, Nat.cast_le]

private theorem natCast_label_lt_omega (n : ℕ) :
    (n : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
  rw [natCast_label, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  exact natCast_lt_omega0 n

private theorem natCast_label_ne_bot (n : ℕ) : (n : Label.{u}) ≠ ⊥ := by
  rw [natCast_label]; exact WithBot.coe_ne_bot

/-- A label other than `⊥` below `ω` is a natural number. -/
private theorem exists_natCast_of_lt_omega {x : Label.{u}} (hx : x ≠ ⊥)
    (hxω : x < ((ω : Ordinal.{u}) : Label.{u})) : ∃ n : ℕ, x = n := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | top => exact absurd hxω (not_lt.mpr le_top)
  | coe o =>
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe] at hxω
    obtain ⟨n, rfl⟩ := lt_omega0.mp hxω
    exact ⟨n, (natCast_label n).symm⟩

/-- Visibility replacement keeps a label at or above `ω` at or above `ω`. -/
private theorem not_lt_omega_visibilityReplace {x : Label.{u}} (hx : x ≠ ⊥)
    (hxω : ¬ x < ((ω : Ordinal.{u}) : Label.{u})) (k i : ℕ) :
    ¬ visibilityReplace k i x < ((ω : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | top => rw [visibilityReplace_top]; exact not_lt.mpr le_top
  | coe o =>
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, not_lt] at hxω
    rw [visibilityReplace_coe, WithBot.coe_lt_coe, WithTop.coe_lt_coe, not_lt]
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    rw [Ordinal.visibilityReplace_omega0_mul_add_natCast]
    have hb : b ≠ 0 := by
      rintro rfl
      simp only [mul_zero, zero_add] at hxω
      exact absurd hxω (not_le.mpr (natCast_lt_omega0 n))
    calc ω = ω * 1 := (mul_one _).symm
      _ ≤ ω * b := by gcongr; exact Order.one_le_iff_ne_zero.mpr hb
      _ ≤ _ := le_self_add

/-- **Two replacements at thresholds at most `2`.** -/
private theorem visibilityReplace_visibilityReplace_two {k : ℕ} (hk : k ≤ 2) (i j : ℕ)
    (A : Label.{u}) :
    visibilityReplace k i (visibilityReplace 2 j A) =
      visibilityReplace 2 (if j < k then i else j) A := by
  induction A using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    have key : (if (if n < 2 then j else n) < k then i else (if n < 2 then j else n)) =
        (if n < 2 then (if j < k then i else j) else n) := by split_ifs <;> omega
    rw [visibilityReplace_coe, visibilityReplace_coe, visibilityReplace_coe,
      Ordinal.visibilityReplace_omega0_mul_add_natCast,
      Ordinal.visibilityReplace_omega0_mul_add_natCast,
      Ordinal.visibilityReplace_omega0_mul_add_natCast, key]

/-- Replacement at a larger value gives a larger label. -/
private theorem visibilityReplace_le_visibilityReplace {k i j : ℕ} (hij : i ≤ j)
    (A : Label.{u}) : visibilityReplace k i A ≤ visibilityReplace k j A := by
  induction A using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    simp only [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
      WithBot.coe_le_coe, WithTop.coe_le_coe]
    gcongr
    split_ifs <;> omega

/-- A label self-visible at `1` is fixed by replacement at threshold `2` with value `1`. -/
private theorem visibilityReplace_two_one {A : Label.{u}} (hA : IsSelfVisible 1 A) :
    visibilityReplace 2 1 A = A := by
  induction A using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le] at hA
    have key : (if n < 2 then 1 else n) = n := by split_ifs <;> omega
    rw [visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast, key]

/-! ### The strip shifter is a witness -/

private theorem stripShifter_natCast (A : Label.{u}) (n : ℕ) :
    stripShifter A (n : Label.{u}) = visibilityReplace 2 (min n 2) A := by
  unfold stripShifter
  rw [ite_eq_right (natCast_label_ne_bot n), ite_eq_left (natCast_label_lt_omega n)]
  have h0 : ((n : Label.{u}) = 0) ↔ n = 0 := by
    rw [show (0 : Label.{u}) = ((0 : ℕ) : Label.{u}) by simp]; exact natCast_label_inj
  have h1 : ((n : Label.{u}) = 1) ↔ n = 1 := by
    rw [show (1 : Label.{u}) = ((1 : ℕ) : Label.{u}) by simp]; exact natCast_label_inj
  by_cases hn0 : n = 0
  · rw [ite_eq_left (h0.mpr hn0), hn0]; rfl
  · rw [ite_eq_right (mt h0.mp hn0)]
    by_cases hn1 : n = 1
    · rw [ite_eq_left (h1.mpr hn1), hn1]; rfl
    · rw [ite_eq_right (mt h1.mp hn1)]
      congr 1; omega

private theorem stripShifter_of_not_lt {A x : Label.{u}} (hx : x ≠ ⊥)
    (hxω : ¬ x < ((ω : Ordinal.{u}) : Label.{u})) : stripShifter A x = ⊤ := by
  unfold stripShifter
  rw [ite_eq_right hx, ite_eq_right hxω]

private theorem stripShifter_bot (A : Label.{u}) : stripShifter A ⊥ = ⊥ := by
  unfold stripShifter; rw [ite_eq_left rfl]

private theorem monotone_stripShifter (A : Label.{u}) : Monotone (stripShifter A) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, stripShifter_bot]; exact bot_le
  have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
  by_cases hyω : y < ((ω : Ordinal.{u}) : Label.{u})
  · have hxω := hxy.trans_lt hyω
    obtain ⟨n, rfl⟩ := exists_natCast_of_lt_omega hx hxω
    obtain ⟨m, rfl⟩ := exists_natCast_of_lt_omega hy hyω
    rw [stripShifter_natCast, stripShifter_natCast]
    exact visibilityReplace_le_visibilityReplace (min_le_min_right 2 (natCast_label_le.mp hxy)) A
  · rw [stripShifter_of_not_lt hy hyω]; exact le_top

/-- **The strip shifter is a witness** for the suppressor `F` up to the grade `2`. -/
theorem isWitness_stripShifter {A F : Label.{u}} (hF : IsSelfVisible 2 F) :
    IsWitness (constStepSuppressor 2 F) (stripShifter A) where
  antitone := antitone_constStepSuppressor 2 F
  isSelfVisible := isSelfVisible_constStepSuppressor hF
  map_bot := stripShifter_bot A
  monotone := monotone_stripShifter A
  visibilityReplace_comm x k hx i hi := by
    by_cases hx0 : x = ⊥
    · rw [hx0, visibilityReplace_bot, stripShifter_bot, visibilityReplace_bot]
    by_cases hxω : x < ((ω : Ordinal.{u}) : Label.{u})
    · obtain ⟨n, rfl⟩ := exists_natCast_of_lt_omega hx0 hxω
      rw [Label.visibilityReplace_natCast]
      have hcast : ((if n < k then (i : Label.{u}) else n) : Label.{u}) =
          ((if n < k then i else n : ℕ) : Label.{u}) := by split_ifs <;> rfl
      rw [hcast, stripShifter_natCast, stripShifter_natCast]
      by_cases hk : k ≤ 2
      · rw [visibilityReplace_visibilityReplace_two hk]
        congr 1
        split_ifs <;> omega
      · -- Above the grade `2` the guard forces `A = ⊥`.
        rw [stripShifter_natCast, constStepSuppressor, ite_eq_right hk, le_bot_iff,
          visibilityReplace_eq_bot_iff] at hx
        rw [hx]; simp
    · rw [stripShifter_of_not_lt hx0 hxω, visibilityReplace_top,
        stripShifter_of_not_lt (by rwa [Ne, visibilityReplace_eq_bot_iff])
          (not_lt_omega_visibilityReplace hx0 hxω k i)]

private theorem v1_eq : (v1 : Label.{u}) = ((1 : ℕ) : Label.{u}) := by
  rw [natCast_label]; simp [v1, gridPoint]

private theorem stripShifter_v1 {A : Label.{u}} (hA : IsSelfVisible 1 A) :
    stripShifter A v1 = A := by
  rw [v1_eq, stripShifter_natCast]
  exact visibilityReplace_two_one hA

private theorem stripShifter_v2 (A : Label.{u}) : stripShifter A v2 = ⊤ := by
  refine stripShifter_of_not_lt (gridPoint_ne_bot 2 1) ?_
  simp only [v2, gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe, not_lt, Nat.cast_one,
    mul_one]
  exact le_self_add

/-! ### The labellings `labelling A F` are lawful -/

private theorem isSelfVisible_labelling {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (d : Fin 19) : IsSelfVisible (cellGrade d) (labelling A F d) := by
  unfold labelling
  by_cases hl : live d = true
  · rcases live_grade d hl with h | h
    · simp [hl, h, hA]
    · simp [hl, h, hF]
  · simp [hl]

/-- **`labelling A F` is lawful** when `A` is self-visible at `1` and `F` at `2`. -/
theorem isLawful_labelling {A F : Label.{u}} (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F) :
    rows.IsLawful (labelling A F) where
  orderly d := isSelfVisible_labelling hA hF d
  locality s := by
    by_cases hs : live s = true
    · rcases live_grade s hs with hs1 | hs2
      · -- A live cell of grade `1`: the top shifter, the suppressor `A` up to the grade `1`.
        refine ⟨constStepSuppressor 1 A, topShifter,
          isWitness_topShifter (antitone_constStepSuppressor _ _)
            (isSelfVisible_constStepSuppressor hA),
          fun d ↦ ?_⟩
        have hds : cells.gradedIndex d.1 ≤ cells.gradedIndex s := d.2
        change min (labelling A F d.1) (labelling A F s) =
          min (topShifter (if live s = true ∧ live d.1 = true then
            (if cellGrade d.1 = 1 then v1 else v2) else ⊥))
            (constStepSuppressor 1 A (cellGrade d.1))
        by_cases hd : live d.1 = true
        · have hd1 : cellGrade d.1 = 1 := by
            rcases live_le_live s d.1 hs hd hds with h | ⟨_, h⟩ <;> omega
          rw [ite_eq_left ⟨hs, hd⟩, ite_eq_left hd1, topShifter,
            ite_eq_right (gridPoint_ne_bot 1 0), constStepSuppressor, ite_eq_left hd1.le,
            min_top_left]
          simp [labelling, hs, hd, hd1, hs1]
        · have : labelling A F d.1 = ⊥ := by simp [labelling, hd]
          rw [this, ite_eq_right (fun h ↦ hd h.2), topShifter, ite_eq_left rfl]
          simp
      · -- The live cell of grade `2`: the strip shifter, the suppressor `F` up to the grade `2`.
        refine ⟨constStepSuppressor 2 F, stripShifter A, isWitness_stripShifter hF, fun d ↦ ?_⟩
        have hds : cells.gradedIndex d.1 ≤ cells.gradedIndex s := d.2
        change min (labelling A F d.1) (labelling A F s) =
          min (stripShifter A (if live s = true ∧ live d.1 = true then
            (if cellGrade d.1 = 1 then v1 else v2) else ⊥))
            (constStepSuppressor 2 F (cellGrade d.1))
        have hlabs : labelling A F s = F := by simp [labelling, hs, hs2]
        rw [hlabs]
        by_cases hd : live d.1 = true
        · rw [ite_eq_left ⟨hs, hd⟩]
          rcases live_le_live s d.1 hs hd hds with h | ⟨h1, _⟩
          · have hd2 : cellGrade d.1 = 2 := h.trans hs2
            rw [ite_eq_right (by omega), stripShifter_v2, constStepSuppressor, ite_eq_left hd2.le,
              min_top_left]
            simp [labelling, hd, hd2]
          · rw [ite_eq_left h1, stripShifter_v1 hA, constStepSuppressor, ite_eq_left (by omega)]
            simp [labelling, hd, h1]
        · have : labelling A F d.1 = ⊥ := by simp [labelling, hd]
          rw [this, ite_eq_right (fun h ↦ hd h.2), stripShifter_bot]
          simp
    · have : labelling A F s = ⊥ := by simp [labelling, hs]
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

private theorem labelling_dead {A F : Label.{u}} {d : Fin 19} (hd : live d = false) :
    labelling A F d = ⊥ := by
  simp [labelling, hd]

private theorem labelling_one {A F : Label.{u}} {d : Fin 19} (hd : live d = true)
    (hg : cellGrade d = 1) : labelling A F d = A := by
  simp [labelling, hd, hg]

private theorem labelling_two {A F : Label.{u}} {d : Fin 19} (hd : live d = true)
    (hg : cellGrade d = 2) : labelling A F d = F := by
  simp [labelling, hd, hg]

/-- Every live cell of grade `1` lies above the cell `3`, at `({3}, 1)`. -/
private theorem three_le_of_grade_one : ∀ d : Fin 19, live d = true → cellGrade d = 1 →
    cells.gradedIndex 3 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The only live cell of grade `2` is the cell `15`, at `(univ, 2)`. -/
private theorem eq_fifteen_of_grade_two : ∀ d : Fin 19, live d = true → cellGrade d = 2 →
    d = 15 := by decide +kernel

private theorem mem_below_of_le {Z : Finset (Fin 4) × ℕ} {d e : Fin 19} (hd : d ∈ cells.below Z)
    (h : cells.gradedIndex e ≤ cells.gradedIndex d) : e ∈ cells.below Z := le_trans h hd

private theorem live_cases (d : Fin 19) :
    live d = false ∨ (live d = true ∧ cellGrade d = 1) ∨ (live d = true ∧ cellGrade d = 2) := by
  revert d; decide

/-! ### The lawful labellings below a pair -/

/-- **The lawful labellings below a pair** are the restrictions of the labellings
`labelling A F` with `A` self-visible at `1` and `F` self-visible at `2`. -/
theorem isLawfulBelow_iff {Y : Finset (Fin 4) × ℕ} {x : Fin 19 → Label.{u}} :
    rows.IsLawfulBelow Y (fun d ↦ x d) ↔ ∃ A F : Label.{u}, IsSelfVisible 1 A ∧
      IsSelfVisible 2 F ∧ ∀ d ∈ cells.below Y, x d = labelling A F d := by
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
        rcases live_le_live s d hsl hdl hds with h | ⟨_, h⟩ <;> omega
      have := (hl s hs).le_of_le (d := ⟨s, cells.mem_below_gradedIndex s⟩) (d' := ⟨d, hds⟩)
        (by simp [rows, hsl, hdl, hd1, hs1]) hds.2
      simp only [min_self] at this
      exact this.trans (min_le_left _ _)
    have havail : ∀ s t, t ∈ cells.below Y → cellScope s ⊆ cellScope t →
        cellGrade s = cellGrade t → x s ≤ x t := by
      intro s t ht hst hg
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rwa [gradedIndex_injective hu] at hle
    have hA : IsSelfVisible 1 (if (3 : Fin 19) ∈ cells.below Y then x 3 else ⊤) := by
      split_ifs with h3
      · exact ho 3 h3
      · exact isSelfVisible_top 1
    have hF : IsSelfVisible 2 (if (15 : Fin 19) ∈ cells.below Y then x 15 else ⊥) := by
      split_ifs with h15
      · exact ho 15 h15
      · exact isSelfVisible_bot 2
    refine ⟨_, _, hA, hF, fun d hd ↦ ?_⟩
    rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, hdead d hd hdl]
    · have h3 : (3 : Fin 19) ∈ cells.below Y :=
        mem_below_of_le hd (three_le_of_grade_one d hdl hg)
      rw [labelling_one hdl hg, ite_eq_left h3]
      refine le_antisymm (hloc d hd 3 hdl rfl hg (three_le_of_grade_one d hdl hg)) ?_
      exact havail 3 d hd (three_le_of_grade_one d hdl hg).1 (hg ▸ rfl)
    · obtain rfl := eq_fifteen_of_grade_two d hdl hg
      rw [labelling_two hdl hg, ite_eq_left hd]
  · rintro ⟨A, F, hA, hF, hx⟩
    have := (isLawful_labelling hA hF).isLawfulBelow Y
    convert this using 1
    funext d
    exact hx d d.2

/-! ### Bountifulness -/

/-- **Every pair lifts capped to every larger pair.**  For a prescription `labelling Ap Fp` below
`X` and an ambient `labelling Aq Fq` below `Y`, the lift is `labelling A' F'`, each parameter
prescribed when its cells meet `X`, and otherwise the ambient one below the cap and `⊤` above. -/
theorem cappedLift_all {X Y : Finset (Fin 4) × ℕ} (h : X ≤ Y) : rows.CappedLift.{u} h := by
  classical
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨Ap, Fp, hAp, hFp, hpx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨Aq, Fq, hAq, hFq, hqx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpd (d : cells.below X) : p d = labelling Ap Fp d := by
    rw [← hpx d d.2, Rows.extendBot_of_mem p d.2]
  have hqd (d : cells.below Y) : q d = labelling Aq Fq d := by
    rw [← hqx d d.2, Rows.extendBot_of_mem q d.2]
  have hcap3 (h3 : (3 : Fin 19) ∈ cells.below X) : min Aq c = min Ap c := by
    have := hpq ⟨3, h3⟩
    rwa [hqd, hpd] at this
  have hcap15 (h15 : (15 : Fin 19) ∈ cells.below X) : min Fq c = min Fp c := by
    have := hpq ⟨15, h15⟩
    rwa [hqd, hpd] at this
  set A' : Label.{u} := if (3 : Fin 19) ∈ cells.below X then Ap else (if Aq < c then Aq else ⊤)
    with hA'
  set F' : Label.{u} := if (15 : Fin 19) ∈ cells.below X then Fp else (if Fq < c then Fq else ⊤)
    with hF'
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
  refine ⟨fun d ↦ labelling A' F' d,
    isLawfulBelow_iff.mpr ⟨A', F', hSA, hSF, fun _ _ ↦ rfl⟩, fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hqd]
    change min (labelling A' F' d.1) c = min (labelling Aq Fq d.1) c
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
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
  · rw [hpd]
    change labelling A' F' d.1 = labelling Ap Fp d.1
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, labelling_dead hdl]
    · have h3 : (3 : Fin 19) ∈ cells.below X :=
        mem_below_of_le d.2 (three_le_of_grade_one d.1 hdl hg)
      rw [labelling_one hdl hg, labelling_one hdl hg, hA', ite_eq_left h3]
    · have h15 : (15 : Fin 19) ∈ cells.below X := by
        rw [← eq_fifteen_of_grade_two d.1 hdl hg]; exact d.2
      rw [labelling_two hdl hg, labelling_two hdl hg, hF', ite_eq_left h15]

theorem isBountiful_rows : rows.{u}.IsBountiful := fun _ _ _ _ h ↦ cappedLift_all h

/-! ### Legality -/

theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  have hA : IsSelfVisible 1 (if live s = true then (v1 : Label.{u}) else ⊥) := by
    split_ifs
    · exact isSelfVisible_gridPoint 1 0
    · exact isSelfVisible_bot 1
  have hF : IsSelfVisible 2 (if live s = true then (v2 : Label.{u}) else ⊥) := by
    split_ifs
    · exact isSelfVisible_gridPoint 2 1
    · exact isSelfVisible_bot 2
  have := (isLawfulBelow_iff (Y := cells.gradedIndex s)
    (x := fun d ↦ if live s = true ∧ live d = true then
      (if cellGrade d = 1 then (v1 : Label.{u}) else v2) else ⊥)).mpr
    ⟨_, _, hA, hF, fun d _ ↦ ?_⟩
  · exact this
  · rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · simp [labelling_dead hdl, hdl]
    · rw [labelling_one hdl hg]; by_cases hs : live s = true <;> simp [hs, hdl, hg]
    · rw [labelling_two hdl hg]; by_cases hs : live s = true <;> simp [hs, hdl, hg]

theorem isWellFormed_S : S.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

theorem isCoded_S : S.{u}.IsCoded := by
  intro s t
  change (if live s = true ∧ live t.1 = true then
    (if cellGrade t.1 = 1 then (v1 : Label.{u}) else v2) else ⊥) < _
  split_ifs
  · exact gridPoint_lt_omega0_sq 1 0
  · exact gridPoint_lt_omega0_sq 2 1
  · exact WithBot.bot_lt_coe _

private theorem complete_below : ∀ B ∈ Geometry.intervalPlan (univ : Finset (Fin 4)), ∀ k < 4,
    0 < k → k ≤ #B → ∃ d : Fin 19, cellScope d = B ∧ cellGrade d = k := by
  decide +kernel

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
noncomputable def T4₀ (α : Ordinal.{u}) : StageType.{u} α 4 where
  toScheme := S
  label _ := ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- **The legal type on four points**: `S` with the apex added. -/
noncomputable def T4 (α : Ordinal.{u}) : StageType.{u} α 4 :=
  (T4₀ α).addApex isLegalBelowFullGrade_S (by omega)

theorem isLegal_T4 (α : Ordinal.{u}) : (T4 α).IsLegal :=
  StageType.isLegal_addApex _ _

section InT4

variable {α : Ordinal.{u}}

theorem gradedIndex_T4_castSucc (d : Fin 19) :
    (T4 α).toCellScheme.gradedIndex (Fin.castSucc d) = cells.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc S 4 d

theorem gradedIndex_T4_last :
    (T4 α).toCellScheme.gradedIndex (Fin.last 19) = ((univ : Finset (Fin 4)), 4) :=
  Scheme.appendFullCellScheme_gradedIndex_last S 4

/-- Below a pair not above the apex, lawfulness in `T4` is lawfulness in `S`. -/
theorem isLawfulBelow_T4_iff {X : Finset (Fin 4) × ℕ}
    (hX : ¬ ((univ : Finset (Fin 4)), 4) ≤ X) {w : Fin (T4 α).card → Label.{u}} :
    (T4 α).rows.IsLawfulBelow X (fun d ↦ w d) ↔
      rows.IsLawfulBelow X (fun d ↦ w (Fin.castSucc d.1)) :=
  Scheme.isLawfulBelow_appendFullCell_iff (h := isLegalBelowFullGrade_S.not_le) hX

/-- The face `{0, 1, 2}` of `T4` is a face. -/
theorem face_mem_T4 : univ.map (Coatom.face 3) ∈ (T4 α).toCellScheme.faces := by
  change univ.map (Coatom.face 3) ∈ Geometry.intervalPlan univ
  decide +kernel

end InT4

/-- The face of `T4` on `{0, 1, 2}`. -/
noncomputable def faceT4 (α : Ordinal.{u}) : StageType.{u} α 3 :=
  (T4 α).comap (Coatom.face 3) face_mem_T4

theorem restrictFace_T4 (α : Ordinal.{u}) :
    StageType.restrictFace (Coatom.face 3) (T4 α) = some (faceT4 α) :=
  StageType.restrictFace_of_mem _ _ face_mem_T4

/-- **The seed of `T4` with itself** on five points: the coatoms `{0, 1, 2, 3}` and
`{0, 1, 2, 4}`, with common face `{0, 1, 2}`. -/
noncomputable def seed4 (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_T4 α) (isLegal_T4 α) (restrictFace_T4 α) (restrictFace_T4 α)

/-! ### Labellings of the amalgam read off graded indices -/

section SeedLevel

variable {α : Ordinal.{u}}

/-- The live graded indices of the first coatom `{0, 1, 2, 3}`. -/
def liveC : Finset (Finset (Fin 5) × ℕ) :=
  {({3}, 1), ({2, 3}, 1), ({1, 2, 3}, 1), ({0, 1, 2, 3}, 1), ({0, 1, 2, 3}, 2)}

/-- The live graded indices of the second coatom `{0, 1, 2, 4}`. -/
def liveD : Finset (Finset (Fin 5) × ℕ) :=
  {({4}, 1), ({2, 4}, 1), ({1, 2, 4}, 1), ({0, 1, 2, 4}, 1), ({0, 1, 2, 4}, 2)}

/-- The kind of a graded index: `1`/`2` for the live grade-`1`/grade-`2` indices of the first
coatom, `3`/`4` for those of the second, `0` otherwise. -/
def pairKind (X : Finset (Fin 5) × ℕ) : Fin 5 :=
  if X ∈ liveC then (if X.2 = 1 then 1 else 2)
  else if X ∈ liveD then (if X.2 = 1 then 3 else 4) else 0

/-- The labelling of graded indices with `A_C, F_C` on the first coatom's live indices and
`A_D, F_D` on the second's. -/
noncomputable def pairLabelling (AC FC AD FD : Label.{u}) (X : Finset (Fin 5) × ℕ) : Label.{u} :=
  ![⊥, AC, FC, AD, FD] (pairKind X)

private def liveKind (d : Fin 19) : Fin 3 :=
  if live d = true then (if cellGrade d = 1 then 1 else 2) else 0

private theorem labelling_eq_liveKind (A F : Label.{u}) (d : Fin 19) :
    labelling A F d = ![⊥, A, F] (liveKind d) := by
  unfold labelling liveKind
  split_ifs <;> rfl

private theorem pairKind_left : ∀ d : Fin 19,
    pairKind (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex d)) =
      ![0, 1, 2] (liveKind d) := by
  decide +kernel

private theorem pairKind_right : ∀ d : Fin 19,
    pairKind (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex d)) =
      ![0, 3, 4] (liveKind d) := by
  decide +kernel

private theorem pairLabelling_left (AC FC AD FD : Label.{u}) (d : Fin 19) :
    pairLabelling AC FC AD FD (Prod.map (Finset.map (Coatom.left 3)) id (cells.gradedIndex d)) =
      labelling AC FC d := by
  rw [pairLabelling, pairKind_left, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

private theorem pairLabelling_right (AC FC AD FD : Label.{u}) (d : Fin 19) :
    pairLabelling AC FC AD FD (Prod.map (Finset.map (Coatom.right 3)) id (cells.gradedIndex d)) =
      labelling AD FD d := by
  rw [pairLabelling, pairKind_right, labelling_eq_liveKind]
  generalize liveKind d = c
  fin_cases c <;> rfl

private theorem isLawfulBelow_T4_of_eq {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) {f : Fin 4 ↪ Fin 5}
    {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (cells.gradedIndex d)) = labelling A F d)
    {X : Finset (Fin 4) × ℕ} (hX : ¬ ((univ : Finset (Fin 4)), 4) ≤ X)
    (x : Fin (T4 α).toScheme.card → Label.{u})
    (hx : ∀ i, x i = Lf (Prod.map (Finset.map f) id ((T4 α).toScheme.toCellScheme.gradedIndex i))) :
    (T4 α).toScheme.rows.IsLawfulBelow X (fun i ↦ x i) := by
  refine (isLawfulBelow_T4_iff hX).mpr ?_
  convert (isLawful_labelling hA hF).isLawfulBelow X using 1
  funext d
  refine (hx _).trans ?_
  rw [gradedIndex_T4_castSucc]
  exact hL d.1

/-- A labelling of graded indices whose reading along `f` is `labelling A F` is lawful below the
coatom `univ.map f` at the grade `3`, for a stage type whose face along `f` is `T4`. -/
private theorem isLawfulBelow_coatom {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T4 α)) {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (cells.gradedIndex d)) = labelling A F d) :
    Am.rows.IsLawfulBelow (univ.map f, 3) (fun d ↦ Lf (Am.toCellScheme.gradedIndex d)) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T4 α).toScheme := congrArg StageType.toScheme he
  have hlaw : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (∀ i, x i = Lf (Prod.map (Finset.map f) id
        ((Am.toScheme.comap f).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun i ↦ x i) := by
    rw [heq]
    exact fun x hx ↦ isLawfulBelow_T4_of_eq hA hF hL (fun h ↦ absurd h.2 (by decide)) x hx
  exact (Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 4)), 3)
    fun d ↦ Lf (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg Lf (Am.toScheme.map_comap_gradedIndex f i).symm)

/-- **`pairLabelling` is lawful below both coatoms at the grade `3`**, on a seed on five points
whose two coatom types are `T4` (such as `seed4 α`), when `A_C`, `A_D` are self-visible at `1` and
`F_C`, `F_D` at `2`: read along each coatom it is `labelling A F`. -/
theorem isLawfulBelow_pairLabelling {I : Seed.{u} α 3} (hIL : I.left = T4 α) (hIR : I.right = T4 α)
    {AC FC AD FD : Label.{u}} (hAC : IsSelfVisible 1 AC)
    (hFC : IsSelfVisible 2 FC) (hAD : IsSelfVisible 1 AD) (hFD : IsSelfVisible 2 FD) :
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 4), 3)
        (fun d ↦ pairLabelling AC FC AD FD (I.amalgam.toCellScheme.gradedIndex d)) ∧
      I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 3)
        (fun d ↦ pairLabelling AC FC AD FD (I.amalgam.toCellScheme.gradedIndex d)) := by
  constructor
  · rw [← Coatom.univ_map_left]
    exact isLawfulBelow_coatom hAC hFC (hIL ▸ I.restrictFace_left) (pairLabelling_left AC FC AD FD)
  · rw [← Coatom.univ_map_right]
    exact isLawfulBelow_coatom hAD hFD (hIR ▸ I.restrictFace_right)
      (pairLabelling_right AC FC AD FD)

/-- A cell of `T4` carried into the amalgam along a coatom whose face is `T4`. -/
private theorem exists_cell {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T4 α)) (d : Fin 19) :
    ∃ e : Fin Am.card, Am.toCellScheme.gradedIndex e =
      Prod.map (Finset.map f) id (cells.gradedIndex d) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T4 α).toScheme := congrArg StageType.toScheme he
  obtain ⟨i, hi⟩ : ∃ i : Fin (Am.toScheme.comap f).card,
      (Am.toScheme.comap f).toCellScheme.gradedIndex i = cells.gradedIndex d := by
    rw [heq]; exact ⟨Fin.castSucc d, gradedIndex_T4_castSucc d⟩
  exact ⟨Am.toScheme.cellMap f i, by rw [← Am.toScheme.map_comap_gradedIndex f i, hi]⟩

private theorem exists_d₁ {I : Seed.{u} α 3} (h : I.left = T4 α) : ∃ e : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex e = (({3} : Finset (Fin 5)), 1) := by
  obtain ⟨e, he⟩ := exists_cell (h ▸ I.restrictFace_left) 3
  exact ⟨e, he.trans (by decide +kernel)⟩

private theorem exists_d₂ {I : Seed.{u} α 3} (h : I.right = T4 α) : ∃ e : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex e = (({4} : Finset (Fin 5)), 1) := by
  obtain ⟨e, he⟩ := exists_cell (h ▸ I.restrictFace_right) 3
  exact ⟨e, he.trans (by decide +kernel)⟩

private theorem exists_s {I : Seed.{u} α 3} (h : I.right = T4 α) : ∃ e : Fin I.amalgam.card,
    I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
  obtain ⟨e, he⟩ := exists_cell (h ▸ I.restrictFace_right) 15
  exact ⟨e, he.trans (by decide +kernel)⟩

/-! ### A catalogue entry of the layer at the grade `2` -/

private theorem isSelfVisible_Q {k b f : ℕ} : IsSelfVisible k (Q.{u} b f) ↔ k ≤ f := by
  rw [Q, isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

private theorem Q_ne_bot (b f : ℕ) : Q.{u} b f ≠ ⊥ := WithBot.coe_ne_bot

/-- **A labelling lawful below both coatoms at the grade `2` is read by a catalogue entry of the
layer at the grade `2`**: extended through the layer at the grade `1`, glued with its old cells of
grade `2`, spliced with `⊥` above the grade `2`; the orbit code of the splice `t` is a catalogue
entry, and `t` is the labelling at the old cells of grade at most `2`. -/
private theorem exists_orbitCode_mem_catalogue_two {m : ℕ} (I : Seed.{u} α m)
    {w : Fin I.amalgam.card → Label.{u}}
    (hwC : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 2) fun d ↦ w d)
    (hwD : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 2)
      fun d ↦ w d) :
    ∃ t : Fin (I.tower 1).card → Label.{u}, orbitCode 2 t ∈ (I.tower 1).catalogue 2 ∧
      ∀ d, I.amalgam.toCellScheme.grade d ≤ 2 → t (I.towerEmbed 1 d) = w d := by
  classical
  have hcov (d : Fin I.amalgam.card) :
      I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last (m + 1)) ∨
        I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.castSucc (Fin.last m)) :=
    I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d) (I.scope_ne_univ d)
  have hwC1 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 1) fun d ↦ w d :=
    hwC.mono (X := (univ.erase (Fin.last (m + 1)), 1)) ⟨subset_rfl, by omega⟩
  have hwD1 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 1)
      fun d ↦ w d :=
    hwD.mono (X := (univ.erase (Fin.castSucc (Fin.last m)), 1)) ⟨subset_rfl, by omega⟩
  obtain ⟨r₁, hr₁, hr₁w⟩ := I.exists_isLawfulBelow_tower (w := w) hcov 1 hwC1 hwD1
  set W : Fin (I.tower 1).card → Label.{u} := Function.extend (I.towerEmbed 1) w (fun _ ↦ ⊥)
  have hWe (d : Fin I.amalgam.card) : W (I.towerEmbed 1 d) = w d :=
    (I.towerEmbed 1).injective.extend_apply _ _ _
  set g : Fin (I.tower 1).card → Label.{u} := fun e ↦
    if he : e ∈ (I.tower 1).toCellScheme.below (univ, 1) then r₁ ⟨e, he⟩ else W e
  have hgold (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      g (I.towerEmbed 1 d) = w d := by
    by_cases he : I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ, 1)
    · simp only [g, dite_eq_left he]
      exact hr₁w d (I.towerEmbed_mem_below_iff.mp he).2
    · simp only [g, dite_eq_right he]
      exact hWe d
  have hgb (e : Fin (I.tower 1).card)
      (he : e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 2) ∨
        e ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 2)) :
      g e = W e := by
    have hsc : (I.tower 1).toCellScheme.scope e ≠ univ := fun hu ↦ he.elim
      (fun h' ↦ Seed.ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1)))
      fun h' ↦ Seed.ne_univ_erase _ (univ_subset_iff.mp (hu.ge.trans h'.1))
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
    have hd : I.amalgam.toCellScheme.grade d ≤ 2 :=
      he.elim (fun h ↦ (I.towerEmbed_mem_below_iff.mp h).2)
        fun h ↦ (I.towerEmbed_mem_below_iff.mp h).2
    rw [hgold d hd, hWe]
  have hold (d : Fin I.amalgam.card)
      (he : I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ, 2)) :
      I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ.erase (Fin.last (m + 1)), 2) ∨
        I.towerEmbed 1 d ∈ (I.tower 1).toCellScheme.below (univ, 1) ∨
        I.towerEmbed 1 d ∈
          (I.tower 1).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last m)), 2) := by
    have hd : I.amalgam.toCellScheme.grade d ≤ 2 := (I.towerEmbed_mem_below_iff.mp he).2
    rcases hcov d with h | h
    · exact .inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
    · exact .inr (.inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))
  have hglaw : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun e ↦ g e := by
    refine Rows.IsLawfulBelow.glue₃ (U := (univ.erase (Fin.last (m + 1)), 2)) (V := (univ, 1))
      (W := (univ.erase (Fin.castSucc (Fin.last m)), 2)) ?_ ?_ ?_ ?_
    · have : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.last (m + 1)), 2) fun e ↦ W e := by
        rw [I.isLawfulBelow_tower_iff (Seed.ne_univ_erase _)]
        simpa only [hWe] using hwC
      convert this using 1
      exact funext fun e ↦ hgb e (.inl e.2)
    · convert hr₁ using 1
      exact funext fun e ↦ by simp only [g, dite_eq_left e.2]
    · have : (I.tower 1).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last m)), 2)
          fun e ↦ W e := by
        rw [I.isLawfulBelow_tower_iff (Seed.ne_univ_erase _)]
        simpa only [hWe] using hwD
      convert this using 1
      exact funext fun e ↦ hgb e (.inr e.2)
    · intro e he
      rcases I.tower_grade_le_or 1 e with h1 | hsc
      · by_cases hsu : (I.tower 1).toCellScheme.scope e = univ
        · exact .inr (.inl ⟨hsu ▸ subset_rfl, h1⟩)
        · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsu
          exact hold d he
      · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e hsc
        exact hold d he
  refine ⟨(I.tower 1).toCellScheme.splice 2 (fun _ ↦ ⊥) g,
    Scheme.orbitCode_splice_bot_mem_catalogue (S := I.tower 1) (k := 2) (p := g) hglaw,
    fun d hd ↦ ?_⟩
  rw [CellScheme.splice_of_le (by rw [Seed.grade_towerEmbed]; exact hd), hgold d hd]

/-! ### Label helpers -/

/-- A label other than `⊥` and `⊤`, self-visible at `1` and not at `2`, is `ω * b + 1`. -/
private theorem eq_omega_mul_add_one {x : Label.{u}} (h0 : x ≠ ⊥) (ht : x ≠ ⊤)
    (h1 : IsSelfVisible 1 x) (h2 : ¬ IsSelfVisible 2 x) :
    ∃ b : Ordinal.{u}, x = ((ω * b + ((1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl h0
  | top => exact absurd rfl ht
  | coe o =>
    obtain ⟨b, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le] at h1 h2
    obtain rfl : n = 1 := by omega
    exact ⟨b, rfl⟩

private theorem pairKind_eq_zero_of_two_lt {X : Finset (Fin 5) × ℕ} (hX : 2 < X.2) :
    pairKind X = 0 := by
  have hC : ∀ Y ∈ liveC, Y.2 ≤ 2 := by decide
  have hD : ∀ Y ∈ liveD, Y.2 ≤ 2 := by decide
  unfold pairKind
  rw [ite_eq_right (fun h ↦ absurd (hC X h) (by omega)),
    ite_eq_right (fun h ↦ absurd (hD X h) (by omega))]

private theorem pairLabelling_map {f : Label.{u} → Label.{u}} (hf : f ⊥ = ⊥)
    (AC FC AD FD : Label.{u}) (X : Finset (Fin 5) × ℕ) :
    f (pairLabelling AC FC AD FD X) = pairLabelling (f AC) (f FC) (f AD) (f FD) X := by
  unfold pairLabelling
  generalize pairKind X = c
  fin_cases c <;> simp [hf]

private theorem Q_le_Q {b f f' : ℕ} (h : f ≤ f') : Q.{u} b f ≤ Q b f' := by
  unfold Q
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe]
  gcongr

/-- Below `ω * b + 1`, a label self-visible at `1` has a smaller key at the grade `3`. -/
private theorem visibilityReplace_three_lt {y : Label.{u}} {b : Ordinal.{u}} (hy0 : y ≠ ⊥)
    (hy : IsSelfVisible 1 y)
    (hlt : y < ((ω * b + ((1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) :
    visibilityReplace 3 3 y <
      visibilityReplace 3 3 ((ω * b + ((1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  induction y using recBotCoeTop with
  | bot => exact absurd rfl hy0
  | top => exact absurd hlt (not_lt.mpr le_top)
  | coe o =>
    obtain ⟨c, n, rfl⟩ := exists_eq_omega0_mul_add_natCast o
    rw [isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le] at hy
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, ← not_le, omega0_mul_add_natCast_le_iff] at hlt
    have hc : c < b := by
      rcases lt_trichotomy c b with h | rfl | h
      · exact h
      · exact absurd (.inr ⟨rfl, hy⟩) hlt
      · exact absurd (.inl h) hlt
    rw [visibilityReplace_coe, visibilityReplace_coe,
      Ordinal.visibilityReplace_omega0_mul_add_natCast,
      Ordinal.visibilityReplace_omega0_mul_add_natCast, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    exact omega0_mul_add_natCast_lt hc _ _

/-! ### The refutation -/

/-- **`2FL(2)` fails on every seed on five points whose two coatom types are `T4`.**  With the
cells `d₁ = ({3}, 1)` on `C`, `d₂ = ({4}, 1)` on `D` and `s = ({0, 1, 2, 4}, 2)`:

1. a catalogue entry `b₀` of the layer at the grade `2` reading `ω + 1` at the live cells of grade
   `1` and `ω + 2` at the live cells of grade `2` (`exists_orbitCode_mem_catalogue_two`) takes one
   value `β₁` at `d₁` and `d₂`, with finite part `1`, below its strip cap `h₂`;
2. `b₀` is extended through the layer at the grade `2` at the cap `h₂`
   (`Scheme.exists_extension_fieldLayer`), and its orbit code at the grade `3`, spliced, is a
   catalogue entry `a`; the cap `h` is the grid point at the grade `3` just below the code of `β₁`,
   so that `a ≥ h` at a cell forces the extension to be at least `β₁` there;
3. the prescription `w` is `a` on `C` and `⊤` at the live cells of `D`;
4. a two-face lift `r` has `r s = ⊤`, so by availability some new cell `u` at `(univ, 2)` has
   `r u = ⊤`, hence `a u ≥ h`; then the entry of `u` agrees with `b₀` capped at `h₂`, so its row
   reads `d₁` and `d₂` at the same value `β₁`, and locality at `u` gives
   `⊤ = r d₂ ≤ r d₁ = a d₁`, while `a d₁ ≠ ⊤`. -/
theorem not_twoFaceLift_two_of {I : Seed.{u} α 3} (hIL : I.left = T4 α) (hIR : I.right = T4 α) :
    ¬ I.TwoFaceLift 2 := by
  classical
  intro H
  -- The cells `d₁ = ({3}, 1)`, `d₂ = ({4}, 1)` and `s = ({0, 1, 2, 4}, 2)`.
  obtain ⟨d₁, hd₁⟩ := exists_d₁ hIL
  obtain ⟨d₂, hd₂⟩ := exists_d₂ hIR
  obtain ⟨sD, hsD⟩ := exists_s hIR
  have hg₁ : I.amalgam.toCellScheme.grade d₁ = 1 := congrArg Prod.snd hd₁
  have hg₂ : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
  have hgs : I.amalgam.toCellScheme.grade sD = 2 := congrArg Prod.snd hsD
  have hk₁ : pairKind (({3} : Finset (Fin 5)), 1) = 1 := by decide
  have hk₂ : pairKind (({4} : Finset (Fin 5)), 1) = 3 := by decide
  have hks : pairKind (({0, 1, 2, 4} : Finset (Fin 5)), 2) = 4 := by decide
  -- The prescription `P`: `ω + 1` on the live cells of grade `1`, `ω + 2` on those of grade `2`.
  have hsv11 : IsSelfVisible 1 (Q.{u} 1 1) := isSelfVisible_Q.mpr le_rfl
  have hsv22 : IsSelfVisible 2 (Q.{u} 1 2) := isSelfVisible_Q.mpr le_rfl
  set P : Fin I.amalgam.card → Label.{u} := fun d ↦
    pairLabelling (Q 1 1) (Q 1 2) (Q 1 1) (Q 1 2) (I.amalgam.toCellScheme.gradedIndex d) with hP
  obtain ⟨hPC, hPD⟩ := isLawfulBelow_pairLabelling hIL hIR hsv11 hsv22 hsv11 hsv22
  have hPC2 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (3 + 1)), 2)
      fun d ↦ P d :=
    hPC.mono (X := (univ.erase (Fin.last 4), 2)) ⟨subset_rfl, by omega⟩
  have hPD2 : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 2)
      fun d ↦ P d :=
    hPD.mono (X := (univ.erase (Fin.castSucc (Fin.last 3)), 2)) ⟨subset_rfl, by omega⟩
  obtain ⟨t, hb₀, ht⟩ := exists_orbitCode_mem_catalogue_two I (w := P) hPC2 hPD2
  have hP₁ : P d₁ = Q 1 1 := by simp only [hP, pairLabelling, hd₁, hk₁]; rfl
  have hP₂ : P d₂ = Q 1 1 := by simp only [hP, pairLabelling, hd₂, hk₂]; rfl
  have hPs : P sD = Q 1 2 := by simp only [hP, pairLabelling, hsD, hks]; rfl
  -- The catalogue entry `b₀` at the grade `2`, and its value `β₁` at `d₁` and `d₂`.
  set b₀ := orbitCode 2 t with hb₀_def
  set β₁ := orbitMap 2 t (Q 1 1) with hβ₁_def
  have hb₀₁ : b₀ (I.towerEmbed 1 d₁) = β₁ := by rw [hb₀_def, orbitCode_apply, ht d₁ (by omega), hP₁]
  have hb₀₂ : b₀ (I.towerEmbed 1 d₂) = β₁ := by rw [hb₀_def, orbitCode_apply, ht d₂ (by omega), hP₂]
  have hb₀s : b₀ (I.towerEmbed 1 sD) = orbitMap 2 t (Q 1 2) := by
    rw [hb₀_def, orbitCode_apply, ht sD (by omega), hPs]
  have hb₀L := (Scheme.mem_catalogue.mp hb₀).1
  have hβ₁sv1 : IsSelfVisible 1 β₁ := by
    have := hb₀L.orderly (I.towerEmbed 1 d₁)
    rwa [Seed.grade_towerEmbed, hg₁, hb₀₁] at this
  have hkey2 : IsOrbitKey 2 t (Q 1 1) := by
    have := isOrbitKey_of_not_isSelfVisible (k := 2) (w := t) (d := I.towerEmbed 1 d₁)
      (by rw [ht d₁ (by omega), hP₁, isSelfVisible_Q]; omega)
    rwa [ht d₁ (by omega), hP₁] at this
  have hβ₁ne : β₁ ≠ ⊥ := by rw [hβ₁_def, Ne, orbitMap_eq_bot_iff]; exact Q_ne_bot 1 1
  have hβ₁sv2 : ¬ IsSelfVisible 2 β₁ := by
    rw [hβ₁_def, isSelfVisible_orbitMap_iff (Q_ne_bot 1 1), isSelfVisible_Q]
    push Not
    exact ⟨hkey2, by omega⟩
  set h₂ := visibilityReplace 2 2 β₁ with hh₂_def
  have hh₂ : h₂ = gridPoint 2 (codeBlock 2 t (Q 1 1)) := visibilityReplace_orbitMap (Q_ne_bot 1 1)
  have hβ₁h₂ : β₁ < h₂ :=
    lt_of_le_of_ne (le_visibilityReplace (by omega) β₁) (fun h ↦ hβ₁sv2 h.symm)
  -- The extension of `b₀` through the layer at the grade `2`, at the strip cap `h₂`.
  obtain ⟨r₂, hr₂, hr₂b, hr₂cap⟩ : ∃ r : (I.tower 2).toCellScheme.below (univ, 2) → Label.{u},
      (I.tower 2).rows.IsLawfulBelow (univ, 2) r ∧
      (∀ d (hd : (I.tower 1).toCellScheme.grade d ≤ 2),
        r ⟨Fin.castAdd _ d, Scheme.castAdd_mem_below (hS := I.not_univ_succ_le_tower 1) hd⟩ =
          b₀ d) ∧
      ∀ x, min (r x) h₂ = min ((I.tower 1).fieldRow 2 b₀ x.1) h₂ :=
    Scheme.exists_extension_fieldLayer (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) (p := b₀) (hb₀L.isLawfulBelow _) hb₀ (h := h₂)
    (by rw [hh₂]; exact isSelfVisible_gridPoint 2 _)
    (by rw [hh₂]; exact bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 2 _))
    (.inl (by rw [hh₂]; exact isShort_gridPoint 2 _)) (fun _ _ ↦ rfl)
  -- The catalogue entry `a` at the grade `3`: the orbit code of the extension, spliced.
  have hr₂L : (I.tower 2).rows.IsLawfulBelow (univ, 2) fun d ↦ Rows.extendBot (univ, 2) r₂ d :=
    Rows.isLawfulBelow_extendBot.mpr hr₂
  set a₀ := (I.tower 2).toCellScheme.splice 2 (fun _ ↦ ⊥) (Rows.extendBot (univ, 2) r₂)
    with ha₀_def
  have ha₀L : (I.tower 2).rows.IsLawful a₀ := Scheme.isLawful_splice_bot hr₂L
  set t₃ := (I.tower 2).toCellScheme.splice 3 (fun _ ↦ ⊥) a₀ with ht₃_def
  have ht₃L : (I.tower 2).rows.IsLawful t₃ :=
    Scheme.isLawful_splice_bot (k := 3) (ha₀L.isLawfulBelow _)
  set a := orbitCode 3 t₃ with ha_def
  have ha : a ∈ (I.tower 2).catalogue 3 :=
    Scheme.orbitCode_splice_bot_mem_catalogue (ha₀L.isLawfulBelow _)
  have haL := (Scheme.mem_catalogue.mp ha).1
  -- The values of `t₃` below `(univ, 2)`, above the grade `2`, and at the old cells.
  have ht₃below (x : Fin (I.tower 2).card) (hx : x ∈ (I.tower 2).toCellScheme.below (univ, 2)) :
      t₃ x = r₂ ⟨x, hx⟩ := by
    rw [ht₃_def, CellScheme.splice_of_le (hx.2.trans (by omega)), ha₀_def,
      CellScheme.splice_of_le hx.2, Rows.extendBot_of_mem r₂ hx]
  have ht₃high (x : Fin (I.tower 2).card) (hx : 2 < (I.tower 2).toCellScheme.grade x) :
      t₃ x = ⊥ := by
    rw [ht₃_def]
    by_cases h3 : (I.tower 2).toCellScheme.grade x ≤ 3
    · rw [CellScheme.splice_of_le h3, ha₀_def, CellScheme.splice_of_lt hx]
    · rw [CellScheme.splice_of_lt (not_le.mp h3)]
  have ht₃old (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      t₃ (I.towerEmbed 2 d) = b₀ (I.towerEmbed 1 d) := by
    rw [ht₃below _ (I.towerEmbed_mem_below hd)]
    exact hr₂b (I.towerEmbed 1 d) (by rw [Seed.grade_towerEmbed]; exact hd)
  -- The labels `A₃` and `F₃` of `a` at the live cells.
  set A₃ := orbitMap 3 t₃ β₁ with hA₃_def
  set F₃ := orbitMap 3 t₃ (orbitMap 2 t (Q 1 2)) with hF₃_def
  have haold (d : Fin I.amalgam.card) :
      a (I.towerEmbed 2 d) = pairLabelling A₃ F₃ A₃ F₃ (I.amalgam.toCellScheme.gradedIndex d) := by
    by_cases hd : I.amalgam.toCellScheme.grade d ≤ 2
    · rw [ha_def, orbitCode_apply, ht₃old d hd, hb₀_def, orbitCode_apply, ht d hd, hP]
      exact pairLabelling_map (f := fun x ↦ orbitMap 3 t₃ (orbitMap 2 t x)) (by simp) _ _ _ _ _
    · rw [ha_def, orbitCode_apply, ht₃high _ (by rw [Seed.grade_towerEmbed]; omega),
        orbitMap_bot, pairLabelling, pairKind_eq_zero_of_two_lt (by simpa using hd)]
      rfl
  have hA₃d₁ : a (I.towerEmbed 2 d₁) = A₃ := by
    rw [ha_def, orbitCode_apply, ht₃old d₁ (by omega), hb₀₁]
  have hF₃s : a (I.towerEmbed 2 sD) = F₃ := by
    rw [ha_def, orbitCode_apply, ht₃old sD (by omega), hb₀s]
  have hA₃sv : IsSelfVisible 1 A₃ := by
    have := haL.orderly (I.towerEmbed 2 d₁)
    rwa [Seed.grade_towerEmbed, hg₁, hA₃d₁] at this
  have hF₃sv : IsSelfVisible 2 F₃ := by
    have := haL.orderly (I.towerEmbed 2 sD)
    rwa [Seed.grade_towerEmbed, hgs, hF₃s] at this
  have hAF : A₃ ≤ F₃ := monotone_orbitMap 3 t₃ (monotone_orbitMap 2 t (Q_le_Q (by omega)))
  have hA₃top : A₃ ≠ ⊤ := orbitMap_ne_top _
  -- The block of `β₁`: `β₁ = ω * b' + 1` with `b' ≠ 0`.
  obtain ⟨b', hb'⟩ := eq_omega_mul_add_one hβ₁ne (orbitMap_ne_top _) hβ₁sv1 hβ₁sv2
  have hcb2 : 1 ≤ codeBlock 2 t (Q 1 1) := by
    have hnat : ¬ (IsOrbitKey 2 t (Q 1 1) ∧ visibilityReplace 2 2 (Q.{u} 1 1) = gridPoint 2 0) := by
      rintro ⟨-, h⟩
      rw [Q, gridPoint, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
        WithBot.coe_inj, WithTop.coe_inj] at h
      have := (omega0_mul_add_natCast_le_iff (a := ((1 : ℕ) : Ordinal.{u}))
        (b := ((0 : ℕ) : Ordinal.{u}))).mp h.le
      rcases this with h' | ⟨h', -⟩
      · exact absurd h' (by simp)
      · exact absurd h' (by simp)
    have h1 := le_codeBlock hnat
    have h2 := one_le_keyRank hkey2.isKey
    omega
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    have h := hh₂
    rw [hh₂_def, hb', gridPoint, visibilityReplace_coe,
      Ordinal.visibilityReplace_omega0_mul_add_natCast, WithBot.coe_inj, WithTop.coe_inj] at h
    have := (omega0_mul_add_natCast_le_iff (a := ((codeBlock 2 t (Q 1 1) : ℕ) : Ordinal.{u}))
      (b := (0 : Ordinal.{u}))).mp h.ge
    rcases this with h' | ⟨h', -⟩
    · exact absurd h' (by simp)
    · have : ((codeBlock 2 t (Q 1 1) : ℕ) : Ordinal.{u}) = ((0 : ℕ) : Ordinal.{u}) := by
        simpa using h'
      have := Nat.cast_injective this
      omega
  -- The orbit key of `β₁` at the grade `3`, its rank `ρ`, and the cap `h`.
  have hkey3 : IsOrbitKey 3 t₃ β₁ := by
    have := isOrbitKey_of_not_isSelfVisible (k := 3) (w := t₃) (d := I.towerEmbed 2 d₁)
      (by rw [ht₃old d₁ (by omega), hb₀₁]; exact fun h ↦ hβ₁sv2 (h.mono (by omega)))
    rwa [ht₃old d₁ (by omega), hb₀₁] at this
  have hnat3 : visibilityReplace 3 3 β₁ ≠ gridPoint 3 0 := by
    intro h
    rw [hb', gridPoint, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast,
      WithBot.coe_inj, WithTop.coe_inj] at h
    have := (omega0_mul_add_natCast_le_iff (a := b') (b := ((0 : ℕ) : Ordinal.{u}))).mp h.le
    rcases this with h' | ⟨h', -⟩
    · exact absurd h' (by simp)
    · exact hb'0 (by simpa using h')
  set ρ := keyRank 3 t₃ β₁ with hρ_def
  have hcb3 : codeBlock 3 t₃ β₁ = 2 * ρ := codeBlock_of_isOrbitKey hkey3 hnat3
  have hρ : 1 ≤ ρ := one_le_keyRank hkey3.isKey
  set h := gridPoint.{u} 3 (2 * ρ - 1) with hh_def
  have hhA : h ≤ A₃ := by
    rw [hA₃_def, orbitMap_of_isOrbitKey hkey3, hcb3, hb', gridPoint, moveToBlock_omega0_mul_add,
      hh_def, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff]
    exact .inl (by exact_mod_cast (by omega : 2 * ρ - 1 < 2 * ρ))
  -- Below the strip of `β₁`, the code at the grade `3` lies below the cap.
  have hlow (x : Fin (I.tower 2).card) (hx : t₃ x < β₁) : a x < h := by
    by_cases hx0 : t₃ x = ⊥
    · rw [ha_def, orbitCode_apply, hx0, orbitMap_bot]
      exact bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 3 _)
    have hsv : IsSelfVisible 1 (t₃ x) :=
      (ht₃L.orderly x).mono ((I.isWellFormed_tower 2 (by omega)).isWellFormed.grade_pos x)
    have hkx := visibilityReplace_three_lt hx0 hsv (hb' ▸ hx)
    rw [← hb'] at hkx
    have hr := keyRank_lt_keyRank hkey3.isKey hkx
    have hcb := codeBlock_le 3 t₃ (t₃ x)
    rw [ha_def, orbitCode_apply]
    calc orbitMap 3 t₃ (t₃ x) ≤ gridPoint 3 (codeBlock 3 t₃ (t₃ x)) := orbitMap_le_gridPoint _
      _ < h := gridPoint_lt_gridPoint.mpr (by rw [← hρ_def] at hr; omega)
  -- The prescription `w`: `a` on the first coatom, `⊤` on the live cells of the second.
  set w : Fin I.amalgam.card → Label.{u} := fun d ↦
    pairLabelling A₃ F₃ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) with hw_def
  obtain ⟨hwC, hwD⟩ := isLawfulBelow_pairLabelling hIL hIR hA₃sv hF₃sv (isSelfVisible_top 1)
    (isSelfVisible_top 2)
  have hag : ∀ d, I.amalgam.toCellScheme.grade d ≤ 2 + 1 →
      min (w d) h = min (a (I.towerEmbed 2 d)) h := by
    intro d _
    rw [haold, hw_def]
    simp only
    unfold pairLabelling
    generalize pairKind (I.amalgam.toCellScheme.gradedIndex d) = c
    fin_cases c <;> simp [min_eq_right hhA, min_eq_right (hhA.trans hAF)]
  have hwC' : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (3 + 1)), 2 + 1) fun d ↦ w d :=
    hwC
  have hwD' : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 2 + 1)
      fun d ↦ w d := hwD
  -- The two-face lift `r`.
  obtain ⟨r, hr, hrw, hra⟩ := H a ha h (isSelfVisible_gridPoint 3 _) (isShort_gridPoint 3 _)
    (bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 3 _)) w hwC' hwD' hag
  -- Availability at the old cell `s` of grade `2`, labelled `⊤`: a new cell `u` at `(univ, 2)`.
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp (Rows.isLawfulBelow_extendBot.mpr hr)
  obtain ⟨t0, ht0⟩ := I.exists_gradedIndex_eq_univ_tower 1
  have hsDm : I.towerEmbed 2 sD ∈ (I.tower 2).toCellScheme.below (univ, 2) :=
    I.towerEmbed_mem_below (by omega)
  have hwsD : Rows.extendBot (univ, 2) r (I.towerEmbed 2 sD) = ⊤ := by
    rw [Rows.extendBot_of_mem r hsDm, hrw sD (by omega), hw_def]
    simp only [pairLabelling, hsD, hks]
    rfl
  obtain ⟨u, hu, hle⟩ := havail (I.towerEmbed 2 sD) t0 ht0.le
    (by rw [show (I.tower 2).toCellScheme.scope t0 = univ from congrArg Prod.fst ht0]
        exact subset_univ _)
    (by rw [Seed.grade_towerEmbed, hgs]; exact (congrArg Prod.snd ht0).symm)
  have hu' : (I.tower 2).toCellScheme.gradedIndex u = (univ, 2) := hu.trans ht0
  have hum : u ∈ (I.tower 2).toCellScheme.below (univ, 2) := hu'.le
  have hRu : Rows.extendBot (univ, 2) r u = ⊤ := top_le_iff.mp (hwsD ▸ hle)
  have hru : r ⟨u, hum⟩ = ⊤ := (Rows.extendBot_of_mem r hum).symm.trans hRu
  -- The cap: `a` reaches `h` at `u`.
  have hau : h ≤ a u := by
    have := hra ⟨u, hum⟩
    rw [hru, min_top_left] at this
    exact min_eq_right_iff.mp this.symm
  -- So `t₃` is at least `β₁` at `u`, hence at least the strip cap `h₂`.
  have ht₃u : β₁ ≤ t₃ u := not_lt.mp fun hlt ↦ absurd hau (not_le.mpr (hlow u hlt))
  have hgu : (I.tower 2).toCellScheme.grade u = 2 := congrArg Prod.snd hu'
  have hsvu : IsSelfVisible 2 (t₃ u) := by
    have := ht₃L.orderly u
    rwa [hgu] at this
  have hh₂u : h₂ ≤ t₃ u := visibilityReplace_le_of_le le_rfl hsvu ht₃u
  -- `u` is a new cell of the layer at the grade `2`; its catalogue entry agrees with `b₀` capped
  -- at `h₂`.
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) (u := u) hu'
  have hcap := hr₂cap ⟨_, hum⟩
  rw [← ht₃below _ hum, Scheme.fieldRow_natAdd] at hcap
  have hah := le_of_min_eq_of_le hcap hh₂u
  obtain ⟨-, hagree⟩ := agreementHeight_spec (bot_mem_grid _ _) b₀
    ((I.tower 1).catalogueEntry 2 i)
  have hagree₂ (e : Fin (I.tower 1).card) :
      min (b₀ e) h₂ = min ((I.tower 1).catalogueEntry 2 i e) h₂ := by
    calc min (b₀ e) h₂ = min (min (b₀ e) (agreementHeight ((I.tower 1).fieldGrid 2) b₀
          ((I.tower 1).catalogueEntry 2 i))) h₂ := by rw [min_assoc, min_eq_right hah]
      _ = min (min ((I.tower 1).catalogueEntry 2 i e) (agreementHeight
          ((I.tower 1).fieldGrid 2) b₀ ((I.tower 1).catalogueEntry 2 i))) h₂ := by
          rw [hagree e]
      _ = _ := by rw [min_assoc, min_eq_right hah]
  -- The entry reads `d₁` and `d₂` equally: both at `β₁`, below the strip cap.
  have he₁ : (I.tower 1).catalogueEntry 2 i (I.towerEmbed 1 d₁) = β₁ :=
    eq_of_min_eq_of_lt (by rw [← hagree₂, hb₀₁]) hβ₁h₂
  have he₂ : (I.tower 1).catalogueEntry 2 i (I.towerEmbed 1 d₂) = β₁ :=
    eq_of_min_eq_of_lt (by rw [← hagree₂, hb₀₂]) hβ₁h₂
  -- Locality at `u`.
  have hrow (d : Fin I.amalgam.card)
      (hd : I.towerEmbed 2 d ∈ (I.tower 2).toCellScheme.below
        ((I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ i))) :
      (I.tower 2).rows.row (Fin.natAdd _ i) ⟨I.towerEmbed 2 d, hd⟩ =
        (I.tower 1).catalogueEntry 2 i (I.towerEmbed 1 d) := by
    have := Scheme.fieldLayer_row_natAdd (S := I.tower 1) (k := 2)
      (hS := I.not_univ_succ_le_tower 1) i ⟨I.towerEmbed 2 d, hd⟩
    exact this.trans (Scheme.fieldRow_castAdd _ _)
  have hm (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      I.towerEmbed 2 d ∈ (I.tower 2).toCellScheme.below
        ((I.tower 2).toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
    rw [hu']; exact I.towerEmbed_mem_below hd
  have hlocu := hloc _ hum
  have h21 := hlocu.le_of_le (d := ⟨I.towerEmbed 2 d₂, hm d₂ (by omega)⟩)
    (d' := ⟨I.towerEmbed 2 d₁, hm d₁ (by omega)⟩)
    (by rw [hrow, hrow, he₁, he₂])
    (by simp only [Seed.grade_towerEmbed, hg₁, hg₂, le_refl])
  simp only at h21
  have hle₁ : I.amalgam.toCellScheme.grade d₁ ≤ 2 := by omega
  have hle₂ : I.amalgam.toCellScheme.grade d₂ ≤ 2 := by omega
  rw [Rows.extendBot_of_mem r (I.towerEmbed_mem_below hle₂),
    Rows.extendBot_of_mem r (I.towerEmbed_mem_below hle₁),
    hRu, hrw d₂ (by omega), hrw d₁ (by omega), hw_def] at h21
  simp only [pairLabelling, hd₁, hd₂, hk₁, hk₂, min_top_right] at h21
  exact hA₃top (top_le_iff.mp h21)

/-- **`2FL(2)` fails for the seed of `T4` with itself.** -/
theorem not_twoFaceLift_two : ¬ (seed4 α).TwoFaceLift 2 :=
  not_twoFaceLift_two_of rfl rfl

end SeedLevel

/-! ### The completion for seeds whose coatom types are `T4` -/

section Completion

variable {α : Ordinal.{u}}

private theorem cases_T4 (i : Fin (T4 α).card) :
    i = Fin.last 19 ∨ ∃ d : Fin 19, i = Fin.castSucc d := by
  change Fin (19 + 1) at i
  induction i using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- In `T4`, every cell of grade `3` is dead: `⊥` in every labelling lawful below `(univ, 3)`. -/
private theorem eq_bot_of_grade_three_T4 (x : Fin (T4 α).toScheme.card → Label.{u})
    (hx : (T4 α).toScheme.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun i ↦ x i))
    (i : Fin (T4 α).toScheme.card) (hi : (T4 α).toScheme.toCellScheme.grade i = 3) : x i = ⊥ := by
  have hx' := (isLawfulBelow_T4_iff (α := α) (w := x) (fun h ↦ absurd h.2 (by decide))).mp hx
  obtain ⟨A, F, -, -, hAF⟩ := (isLawfulBelow_iff (x := fun e ↦ x (Fin.castSucc e))).mp hx'
  rcases cases_T4 (α := α) i with rfl | ⟨d, rfl⟩
  · have := congrArg Prod.snd (gradedIndex_T4_last (α := α))
    simp only at this
    exact absurd (hi.symm.trans this) (by decide)
  · have hg : cellGrade d = 3 :=
      (congrArg Prod.snd (gradedIndex_T4_castSucc (α := α) d)).symm.trans hi
    have hdead : ∀ d : Fin 19, cellGrade d = 3 → live d = false := by decide
    have := hAF d ⟨subset_univ _, hg.le⟩
    rw [labelling_dead (hdead d hg)] at this
    exact this

/-- The cells of grade `3` of an amalgam whose coatom type along `f` is `T4` are dead below
`(univ.map f, 3)`. -/
private theorem eq_bot_of_grade_three {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (T4 α)) (p : Fin Am.card → Label.{u})
    (hp : Am.rows.IsLawfulBelow (univ.map f, 3) fun d ↦ p d)
    (d : Fin Am.card) (hd : d ∈ Am.toCellScheme.below (univ.map f, 3))
    (hg : Am.toCellScheme.grade d = 3) : p d = ⊥ := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (T4 α).toScheme := congrArg StageType.toScheme he
  have hgen : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3)
        (fun i ↦ x i) →
      ∀ i, (Am.toScheme.comap f).toCellScheme.grade i = 3 → x i = ⊥ := by
    rw [heq]; exact eq_bot_of_grade_three_T4
  have hd' : d ∈ Am.toScheme.cellMap f '' (Am.toScheme.comap f).toCellScheme.below
      ((univ : Finset (Fin 4)), 3) := by
    rw [Am.toScheme.image_cellMap_below f]; exact hd
  obtain ⟨i, -, rfl⟩ := hd'
  exact hgen (fun i ↦ p (Am.toScheme.cellMap f i))
    ((Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f _ p).mpr hp) i
    ((congrArg Prod.snd (Am.toScheme.map_comap_gradedIndex f i)).trans hg)

/-- **The cells of grade `3` are dead** on a seed whose two coatom types are `T4`. -/
theorem deadAt_two {I : Seed.{u} α 3} (hIL : I.left = T4 α) (hIR : I.right = T4 α) :
    I.DeadAt 2 := by
  intro x hx p hp d hd hg
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · rw [← Coatom.univ_map_left] at hp hd
    exact eq_bot_of_grade_three (hIL ▸ I.restrictFace_left) p hp d hd hg
  · rw [← Coatom.univ_map_right] at hp hd
    exact eq_bot_of_grade_three (hIR ▸ I.restrictFace_right) p hp d hd hg

/-- **The invariant at the grade `3`** on a seed on five points whose two coatom types are `T4`,
although `2FL(2)` fails there (`not_twoFaceLift_two_of`): the invariant at the grade `2` from
`2FL(1)` (`Seed.twoFaceLift_one`), then the step from deadness of the cells of the grade `3`
(`Seed.towerInvariant_succ_of_dead`). -/
theorem towerInvariant_three {I : Seed.{u} α 3} (hIL : I.left = T4 α) (hIR : I.right = T4 α) :
    I.TowerInvariant 3 :=
  I.towerInvariant_succ_of_dead (j := 2) (by omega)
    (I.towerInvariant_succ (by omega) I.towerInvariant_one I.twoFaceLift_one)
    (deadAt_two hIL hIR)

/-- **A seed on five points whose two coatom types are `T4` has a completion below the full
grade**, through the tower: at the only grade `j = 2` with `2 ≤ j < 3` the old cells of the grade
`3` are dead (`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt`). -/
theorem nonempty_completionBelowFullGrade_of {I : Seed.{u} α 3} (hIL : I.left = T4 α)
    (hIR : I.right = T4 α) : Nonempty (CompletionBelowFullGrade I) :=
  I.nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt fun j hj hjm ↦ .inr <| by
    obtain rfl : j = 2 := by omega
    exact deadAt_two hIL hIR

/-- **The seed of `T4` with itself has a completion below the full grade**, although `2FL(2)`
fails for it (`not_twoFaceLift_two`): the completion is not refuted, only the two-face lift. -/
theorem nonempty_completionBelowFullGrade_seed4 :
    Nonempty (CompletionBelowFullGrade (seed4 α)) :=
  nonempty_completionBelowFullGrade_of rfl rfl

end Completion

/-- **`2FL(j)` at the grades `2 ≤ j < m` fails as a statement about every seed**, at every stage
`α`: the seed `seed4 α` of the legal type `T4` with itself (`Seed.ofCoatoms`), on five points,
fails `2FL(2)` (`not_twoFaceLift_two`). -/
theorem not_forall_twoFaceLift (α : Ordinal.{u}) :
    ¬ ∀ (m : ℕ) (I : Seed.{u} α m) (j : ℕ), 2 ≤ j → j < m → I.TwoFaceLift j :=
  fun h ↦ not_twoFaceLift_two (h 3 (seed4 α) 2 le_rfl (by omega))

end VaughtConjecture.TwoFaceLiftCounterexample
