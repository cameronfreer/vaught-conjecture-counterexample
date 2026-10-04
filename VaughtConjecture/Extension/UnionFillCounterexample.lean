/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.Seed
import VaughtConjecture.Extension.CanonicalCode
import VaughtConjecture.Geometry.IntervalPlan

/-!
# A legal seed on which the union fill fails

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here the negative
example for the step from the grade `j` to `j + 1`); semantic contract, items 2–4.

The **union fill** on the other coatom `D = univ.erase y` over a face `E` at the grade `j + 1`
(`UnionFill`, stated verbatim below) asks that a labelling lawful below `(E, j + 1)` and below
`(D, j)`, agreeing with a lawful `a` capped at a short positive cap `h` on their union, extend,
unchanged on the union, to one lawful below `(D, j + 1)` agreeing with `a` capped at `h`.  This
module shows that it fails, as a statement about every seed, for a legal seed on four points at
the grade `2` (`not_unionFill_seed`).  So the step from the grade `j` to `j + 1` of the tower
(module `VaughtConjecture.Extension.Tower`) is built on the two-face lift `2FL(j)`, which chooses
one labelling of the lower layers respecting both coatoms at once, not on the union fill.

**The legal type `T`** (`T`, `isLegal_T`).  The scheme `S` on three points has the interval plan
(faces `∅, {0}, {1}, {2}, {0, 1}, {1, 2}, univ`) and exactly one cell at every graded face of
grade at most `2`:

| cell  | 0   | 1   | 2   | 3      | 4      | 5    | 6      | 7      | 8    |
|-------|-----|-----|-----|--------|--------|------|--------|--------|------|
| scope | {0} | {1} | {2} | {0, 1} | {1, 2} | univ | {0, 1} | {1, 2} | univ |
| grade | 1   | 1   | 1   | 1      | 1      | 1    | 2      | 2      | 2    |
| live  |     |     | ✓   |        | ✓      | ✓    | ✓      |        | ✓    |

The row of a *live* cell is the ordinal `2` (`rowValue`) at every live cell below it and `⊥` at
every other cell; the row of a cell that is not live is constantly `⊥`.  So the row of the cell
at `(univ, 2)` has equal entries at the cell at `({0, 1}, 2)` and at the cell at `({2}, 1)`: a
row of the coatom coupling a cell of the common face at the grade `2` to a cell of grade `1` off
it.  The type `T` is `S` with the apex added (`StageType.addApex`).

**The lawful labellings** (`isLawfulBelow_iff`).  Below every pair, a labelling is lawful exactly
when it agrees there with `labelling A F` (the cells that are not live `⊥`, the live cells of
grade `1` labelled `A`, those of grade `2` labelled `F`) for some `A` self-visible at `1` and `F`
self-visible at `2` with `F ≤ A`.  Necessity is availability and locality at the unique cells;
sufficiency is the witness at each live cell whose shifter sends `⊥` to `⊥` and every other label
to `⊤`.  Every pair then lifts capped to every larger one (`cappedLift_all`), so `S` is legal
below the full grade and `T` is legal.

**The failure** (`not_unionFill_seed`).  The seed of `T` with itself along its face `{0, 1}` has
coatoms `{0, 1, 2}` and `{0, 1, 3}` and common face `{0, 1}`.  Take `y` the point `2`, so that
`D = {0, 1, 3}`, `E = {0, 1}`, `j = 1` and the cap `h = 2`.  The ambient is `labelling 2 2`; the
labelling `labelling 2 ⊤` is lawful below `(E, 2)` and below `(D, 1)` and agrees with it capped at
`2` everywhere.  A lawful extension below `(D, 2)` would have `F = ⊤ ≤ A = 2`.

**What this shows.**  It refutes the union fill as a universal statement about seeds, so no step
may assume it for every seed.  It does not refute the completion below the full grade, and it does
not make every conditional instance vacuous: the union fill still holds on particular seeds and
grades, for instance whenever the common face carries no cell of the grade (the lift within the
face of the tower's top grade).

The labelling `labelling 2 ⊤` of the failure is not lawful below the coatom `({0, 1, 3}, 2)`
(`not_isLawfulBelow_pairLabelling_top`): it is not a prescription of the two-face lift `2FL(1)`,
which holds for this seed (`Seed.twoFaceLift_one`).

## Placement

Checkpoint 2.6 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.UnionFillCounterexample

open Finset Label CellScheme

/-! ### The scheme on three points -/

/-- The scopes of the nine cells. -/
def cellScope : Fin 9 → Finset (Fin 3) :=
  ![{0}, {1}, {2}, {0, 1}, {1, 2}, univ, {0, 1}, {1, 2}, univ]

/-- The grades of the nine cells. -/
def cellGrade : Fin 9 → ℕ := ![1, 1, 1, 1, 1, 1, 2, 2, 2]

/-- The live cells. -/
def live : Fin 9 → Bool := ![false, false, true, false, true, true, true, false, true]

/-- The cell scheme on three points with the interval plan. -/
def cells : CellScheme (Fin 9) (Fin 3) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

/-- The row value at the live cells: the ordinal `2`. -/
noncomputable abbrev rowValue : Label.{u} := gridPoint 2 0

/-- The rows: the row value between live cells, `⊥` otherwise. -/
noncomputable def rows : cells.Rows.{u} :=
  ⟨fun s t ↦ if live s = true ∧ live t.1 = true then rowValue else ⊥⟩

/-- The scheme on three points. -/
noncomputable def S : Scheme.{u} 3 := ⟨9, cells, rows⟩

/-- The labelling with `⊥` at the cells that are not live, `A` at the live cells of grade `1`,
and `F` at the live cells of grade `2`. -/
noncomputable def labelling (A F : Label.{u}) (d : Fin 9) : Label.{u} :=
  if live d = true then (if cellGrade d = 1 then A else F) else ⊥

/-- The graded index of a cell is its scope and grade. -/
theorem gradedIndex_cells (d : Fin 9) : cells.gradedIndex d = (cellScope d, cellGrade d) := rfl

/-- Distinct cells have distinct graded indices. -/
theorem gradedIndex_injective : Function.Injective cells.gradedIndex := by
  intro a b h
  rw [gradedIndex_cells, gradedIndex_cells] at h
  revert a b; decide +kernel

/-- A live cell below a live cell has the same grade, or grade `1` below grade `2`. -/
private theorem live_le_live : ∀ s d : Fin 9, live s = true → live d = true →
    cells.gradedIndex d ≤ cells.gradedIndex s →
      cellGrade d = cellGrade s ∨ (cellGrade d = 1 ∧ cellGrade s = 2) := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- The live cells are closed upward under inclusion of scopes at the same grade. -/
private theorem live_up : ∀ s t : Fin 9, live s = true → cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → live t = true := by decide +kernel

private theorem grade_eq_one_or_two (d : Fin 9) : cellGrade d = 1 ∨ cellGrade d = 2 := by
  revert d; decide +kernel

/-! ### The labellings `labelling A F` are lawful -/

/-- The shifter sending `⊥` to `⊥` and every other label to `⊤`. -/
noncomputable def shifter (x : Label.{u}) : Label.{u} := if x = ⊥ then ⊥ else ⊤

private theorem isWitness_shifter {g : ℕ → Label.{u}} (hg : Antitone g)
    (hgv : ∀ n, IsSelfVisible n (g n)) : IsWitness g shifter where
  antitone := hg
  isSelfVisible := hgv
  map_bot := by simp [shifter]
  monotone := by
    intro x y hxy
    unfold shifter
    by_cases hx : x = ⊥
    · simp [hx]
    · have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
      simp [hx, hy]
  visibilityReplace_comm x k _ i _ := by
    unfold shifter
    by_cases hx : x = ⊥
    · simp [hx]
    · simp [hx]

/-- The suppressor equal to `a` up to the grade `K` and `⊥` above. -/
noncomputable def stepSuppressor (K : ℕ) (a : Label.{u}) (n : ℕ) : Label.{u} :=
  if n ≤ K then a else ⊥

private theorem antitone_stepSuppressor (K : ℕ) (a : Label.{u}) :
    Antitone (stepSuppressor K a) := by
  intro n m hnm
  unfold stepSuppressor
  split_ifs with hm hn <;> first | exact le_rfl | exact bot_le | omega

private theorem isSelfVisible_stepSuppressor {K : ℕ} {a : Label.{u}} (ha : IsSelfVisible K a)
    (n : ℕ) : IsSelfVisible n (stepSuppressor K a n) := by
  unfold stepSuppressor
  split_ifs with hn
  · exact ha.mono hn
  · exact isSelfVisible_bot n

private theorem isSelfVisible_labelling {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (d : Fin 9) : IsSelfVisible (cellGrade d) (labelling A F d) := by
  unfold labelling
  rcases grade_eq_one_or_two d with h | h
  · split_ifs <;> simp_all
  · split_ifs <;> simp_all

/-- **`labelling A F` is lawful** when `A` is self-visible at `1`, `F` at `2`, and `F ≤ A`. -/
theorem isLawful_labelling {A F : Label.{u}} (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F)
    (hFA : F ≤ A) : rows.IsLawful (labelling A F) where
  orderly d := isSelfVisible_labelling hA hF d
  locality s := by
    by_cases hs : live s = true
    · refine ⟨stepSuppressor (cellGrade s) (labelling A F s), shifter,
        isWitness_shifter (antitone_stepSuppressor _ _)
          (isSelfVisible_stepSuppressor (isSelfVisible_labelling hA hF s)), fun d ↦ ?_⟩
      have hds : cells.gradedIndex d.1 ≤ cells.gradedIndex s := d.2
      have hgd : cellGrade d.1 ≤ cellGrade s := hds.2
      -- The row of `s` at `d`, unfolded.
      change min (labelling A F d.1) (labelling A F s) =
        min (shifter (if live s = true ∧ live d.1 = true then rowValue else ⊥))
          (stepSuppressor _ _ (cellGrade d.1))
      by_cases hd : live d.1 = true
      · rw [ite_eq_left ⟨hs, hd⟩, shifter, ite_eq_right (gridPoint_ne_bot 2 0), stepSuppressor,
          ite_eq_left hgd, min_top_left, min_eq_right]
        rcases live_le_live s d.1 hs hd hds with h | ⟨h1, h2⟩
        · simp [labelling, hs, hd, h]
        · simp [labelling, hs, hd, h1, h2, hFA]
      · have : labelling A F d.1 = ⊥ := by simp [labelling, hd]
        rw [this, ite_eq_right (fun h ↦ hd h.2), shifter, ite_eq_left rfl]
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

private theorem labelling_dead {A F : Label.{u}} {d : Fin 9} (hd : live d = false) :
    labelling A F d = ⊥ := by
  simp [labelling, hd]

private theorem labelling_one {A F : Label.{u}} {d : Fin 9} (hd : live d = true)
    (hg : cellGrade d = 1) : labelling A F d = A := by
  simp [labelling, hd, hg]

private theorem labelling_two {A F : Label.{u}} {d : Fin 9} (hd : live d = true)
    (hg : cellGrade d = 2) : labelling A F d = F := by
  simp [labelling, hd, hg]

/-- Every live cell of grade `1` lies above the cell `2`, at `({2}, 1)`. -/
private theorem two_le_of_grade_one : ∀ d : Fin 9, live d = true → cellGrade d = 1 →
    cells.gradedIndex 2 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- Every live cell of grade `2` lies above the cell `6`, at `({0, 1}, 2)`. -/
private theorem six_le_of_grade_two : ∀ d : Fin 9, live d = true → cellGrade d = 2 →
    cells.gradedIndex 6 ≤ cells.gradedIndex d := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

private theorem mem_below_of_le {Z : Finset (Fin 3) × ℕ} {d e : Fin 9} (hd : d ∈ cells.below Z)
    (h : cells.gradedIndex e ≤ cells.gradedIndex d) : e ∈ cells.below Z := le_trans h hd

/-- A pair above the cells `2` and `6` lies above the cell `8`, at `(univ, 2)`. -/
private theorem eight_mem {Z : Finset (Fin 3) × ℕ} (h2 : (2 : Fin 9) ∈ cells.below Z)
    (h6 : (6 : Fin 9) ∈ cells.below Z) : (8 : Fin 9) ∈ cells.below Z := by
  refine ⟨fun z _ ↦ ?_, h6.2⟩
  have h2' : cellScope 2 ⊆ Z.1 := h2.1
  have h6' : cellScope 6 ⊆ Z.1 := h6.1
  fin_cases z
  · exact h6' (by decide)
  · exact h6' (by decide)
  · exact h2' (by decide)

private theorem live_cases (d : Fin 9) :
    live d = false ∨ (live d = true ∧ cellGrade d = 1) ∨ (live d = true ∧ cellGrade d = 2) := by
  revert d; decide

/-! ### The lawful labellings below a pair -/

/-- **The lawful labellings below a pair** are the restrictions of the labellings
`labelling A F` with `A` self-visible at `1`, `F` self-visible at `2`, and `F ≤ A`. -/
theorem isLawfulBelow_iff {Y : Finset (Fin 3) × ℕ} {x : Fin 9 → Label.{u}} :
    rows.IsLawfulBelow Y (fun d ↦ x d) ↔ ∃ A F : Label.{u}, IsSelfVisible 1 A ∧
      IsSelfVisible 2 F ∧ F ≤ A ∧ ∀ d ∈ cells.below Y, x d = labelling A F d := by
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
        cells.gradedIndex d ≤ cells.gradedIndex s → x s ≤ x d := by
      intro s hs d hsl hdl hds
      have := (hl s hs).le_of_le (d := ⟨s, cells.mem_below_gradedIndex s⟩) (d' := ⟨d, hds⟩)
        (by simp [rows, hsl, hdl]) hds.2
      simp only [min_self] at this
      exact this.trans (min_le_left _ _)
    have havail : ∀ s t, t ∈ cells.below Y → cellScope s ⊆ cellScope t →
        cellGrade s = cellGrade t → x s ≤ x t := by
      intro s t ht hst hg
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rwa [gradedIndex_injective hu] at hle
    have hA : IsSelfVisible 1 (if (2 : Fin 9) ∈ cells.below Y then x 2 else ⊤) := by
      split_ifs with h2
      · exact ho 2 h2
      · exact isSelfVisible_top 1
    have hF : IsSelfVisible 2 (if (6 : Fin 9) ∈ cells.below Y then x 6 else ⊥) := by
      split_ifs with h6
      · exact ho 6 h6
      · exact isSelfVisible_bot 2
    refine ⟨_, _, hA, hF, ?_, fun d hd ↦ ?_⟩
    · split_ifs with h6 h2 h2
      · have h8 := eight_mem h2 h6
        exact (havail 6 8 h8 (by decide) rfl).trans
          (hloc 8 h8 2 rfl rfl (by simp only [gradedIndex_cells, Prod.mk_le_mk]; decide))
      · exact le_top
      · exact bot_le
      · exact bot_le
    · rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
      · rw [labelling_dead hdl, hdead d hd hdl]
      · have h2 : (2 : Fin 9) ∈ cells.below Y := mem_below_of_le hd (two_le_of_grade_one d hdl hg)
        rw [labelling_one hdl hg, ite_eq_left h2]
        refine le_antisymm (hloc d hd 2 hdl rfl (two_le_of_grade_one d hdl hg)) ?_
        exact havail 2 d hd (two_le_of_grade_one d hdl hg).1 (hg ▸ rfl)
      · have h6 : (6 : Fin 9) ∈ cells.below Y :=
          mem_below_of_le hd (six_le_of_grade_two d hdl hg)
        rw [labelling_two hdl hg, ite_eq_left h6]
        refine le_antisymm (hloc d hd 6 hdl rfl (six_le_of_grade_two d hdl hg)) ?_
        exact havail 6 d hd (six_le_of_grade_two d hdl hg).1 (hg ▸ rfl)
  · rintro ⟨A, F, hA, hF, hFA, hx⟩
    have := (isLawful_labelling hA hF hFA).isLawfulBelow Y
    convert this using 1
    funext d
    exact hx d d.2

/-! ### Bountifulness: every pair lifts capped to every larger pair -/

/-- **Every pair lifts capped to every larger pair.**  For a prescription `labelling Ap Fp` below
`X` and an ambient `labelling Aq Fq` below `Y`, the lift is `labelling A' F'` with `A' = Ap` if
the cell `2` lies below `X`, and otherwise `Aq` below the cap and `⊤` above it; and `F' = Fp` if
the cell `6` lies below `X`, and otherwise `Fq` capped at the cap (or `⊥` below the grade `2`). -/
theorem cappedLift_all {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y) : rows.CappedLift.{u} h := by
  classical
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨Ap, Fp, hAp, hFp, hFAp, hpx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨Aq, Fq, hAq, hFq, hFAq, hqx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpd (d : cells.below X) : p d = labelling Ap Fp d := by
    rw [← hpx d d.2, Rows.extendBot_of_mem p d.2]
  have hqd (d : cells.below Y) : q d = labelling Aq Fq d := by
    rw [← hqx d d.2, Rows.extendBot_of_mem q d.2]
  -- The capped agreement at the cells `2` and `6`, when they lie below `X`.
  have hcap2 (h2 : (2 : Fin 9) ∈ cells.below X) : min Aq c = min Ap c := by
    have := hpq ⟨2, h2⟩
    rwa [hqd, hpd] at this
  have hcap6 (h6 : (6 : Fin 9) ∈ cells.below X) : min Fq c = min Fp c := by
    have := hpq ⟨6, h6⟩
    rwa [hqd, hpd] at this
  set A' : Label.{u} := if (2 : Fin 9) ∈ cells.below X then Ap else (if Aq < c then Aq else ⊤)
    with hA'
  set F' : Label.{u} :=
    if (6 : Fin 9) ∈ cells.below X then Fp else (if 2 ≤ Y.2 then min Fq c else ⊥) with hF'
  have hSA : IsSelfVisible 1 A' := by
    rw [hA']; split_ifs
    · exact hAp
    · exact hAq
    · exact isSelfVisible_top 1
  have hSF : IsSelfVisible 2 F' := by
    rw [hF']; split_ifs with _ hY
    · exact hFp
    · exact hFq.min (hc.mono hY)
    · exact isSelfVisible_bot 2
  have hFA : F' ≤ A' := by
    rw [hA', hF']
    by_cases h6 : (6 : Fin 9) ∈ cells.below X
    · rw [ite_eq_left h6]
      by_cases h2 : (2 : Fin 9) ∈ cells.below X
      · rw [ite_eq_left h2]; exact hFAp
      · rw [ite_eq_right h2]
        by_cases hlt : Aq < c
        · rw [ite_eq_left hlt]
          have : Fp = Fq := eq_of_min_eq_of_lt (hcap6 h6) (hFAq.trans_lt hlt)
          rw [this]; exact hFAq
        · rw [ite_eq_right hlt]; exact le_top
    · rw [ite_eq_right h6]
      by_cases hY : 2 ≤ Y.2
      · rw [ite_eq_left hY]
        by_cases h2 : (2 : Fin 9) ∈ cells.below X
        · rw [ite_eq_left h2]
          exact (min_le_min_right c hFAq).trans ((hcap2 h2).le.trans (min_le_left _ _))
        · rw [ite_eq_right h2]
          by_cases hlt : Aq < c
          · rw [ite_eq_left hlt]; exact (min_le_left _ _).trans hFAq
          · rw [ite_eq_right hlt]; exact le_top
      · rw [ite_eq_right hY]; exact bot_le
  refine ⟨fun d ↦ labelling A' F' d,
    isLawfulBelow_iff.mpr ⟨A', F', hSA, hSF, hFA, fun _ _ ↦ rfl⟩, fun d ↦ ?_, fun d ↦ ?_⟩
  · -- The capped agreement with the ambient.
    rw [hqd]
    -- both labellings read at the underlying cell `d.1`
    change min (labelling A' F' d.1) c = min (labelling Aq Fq d.1) c
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, labelling_dead hdl]
    · rw [labelling_one hdl hg, labelling_one hdl hg, hA']
      split_ifs with h2 hlt
      · exact (hcap2 h2).symm
      · rfl
      · rw [min_top_left, min_eq_right (not_lt.mp hlt)]
    · rw [labelling_two hdl hg, labelling_two hdl hg, hF']
      have hY : 2 ≤ Y.2 := hg ▸ d.2.2
      split_ifs with h6
      · exact (hcap6 h6).symm
      · rw [min_assoc, min_self]
  · -- The restriction to the prescription.
    rw [hpd]
    -- both labellings read at the underlying cell `d.1`
    change labelling A' F' d.1 = labelling Ap Fp d.1
    rcases live_cases d.1 with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · rw [labelling_dead hdl, labelling_dead hdl]
    · have h2 : (2 : Fin 9) ∈ cells.below X :=
        mem_below_of_le d.2 (two_le_of_grade_one d.1 hdl hg)
      rw [labelling_one hdl hg, labelling_one hdl hg, hA', ite_eq_left h2]
    · have h6 : (6 : Fin 9) ∈ cells.below X :=
        mem_below_of_le d.2 (six_le_of_grade_two d.1 hdl hg)
      rw [labelling_two hdl hg, labelling_two hdl hg, hF', ite_eq_left h6]

/-- The rows of `S` are bountiful. -/
theorem isBountiful_rows : rows.{u}.IsBountiful := fun _ _ _ _ h ↦ cappedLift_all h

/-! ### Legality -/

private theorem isSelfVisible_rowValue (k : ℕ) (hk : k ≤ 2) :
    IsSelfVisible k (rowValue : Label.{u}) :=
  (isSelfVisible_gridPoint 2 0).mono hk

/-- The rows of `S` are consistent: every row is a labelling `labelling A F`. -/
theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  have hA : IsSelfVisible 1 (if live s = true then (rowValue : Label.{u}) else ⊥) := by
    split_ifs
    · exact isSelfVisible_rowValue 1 (by omega)
    · exact isSelfVisible_bot 1
  have hF : IsSelfVisible 2 (if live s = true then (rowValue : Label.{u}) else ⊥) := by
    split_ifs
    · exact isSelfVisible_rowValue 2 le_rfl
    · exact isSelfVisible_bot 2
  have := (isLawfulBelow_iff (Y := cells.gradedIndex s)
    (x := fun d ↦ if live s = true ∧ live d = true then (rowValue : Label.{u}) else ⊥)).mpr
    ⟨_, _, hA, hF, le_rfl, fun d _ ↦ ?_⟩
  · exact this
  · rcases live_cases d with hdl | ⟨hdl, hg⟩ | ⟨hdl, hg⟩
    · simp [labelling_dead hdl, hdl]
    · rw [labelling_one hdl hg]; by_cases hs : live s = true <;> simp [hs, hdl]
    · rw [labelling_two hdl hg]; by_cases hs : live s = true <;> simp [hs, hdl]

/-- `S` is well formed. -/
theorem isWellFormed_S : S.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

/-- `S` is coded: its row values are `2` and `⊥`. -/
theorem isCoded_S : S.{u}.IsCoded := by
  intro s t
  -- The row of `s` at `t`, unfolded.
  change (if live s = true ∧ live t.1 = true then (rowValue : Label.{u}) else ⊥) < _
  split_ifs
  · exact gridPoint_lt_omega0_sq 2 0
  · exact WithBot.bot_lt_coe _

private theorem complete_below : ∀ B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)), ∀ k < 3,
    0 < k → k ≤ #B → ∃ d : Fin 9, cellScope d = B ∧ cellGrade d = k := by
  decide +kernel

/-- **`S` is legal below the full grade.** -/
theorem isLegalBelowFullGrade_S : S.{u}.IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isConsistent := isConsistent_rows
  isBountiful := isBountiful_rows
  grade_lt d := (by decide : ∀ d : Fin 9, cellGrade d < 3) d
  exists_gradedIndex_eq X hX hX3 := by
    obtain ⟨d, hd1, hd2⟩ := complete_below X.1 hX.1 X.2 hX3 hX.2.1 hX.2.2
    exact ⟨d, Prod.ext hd1 hd2⟩

/-- The stage type of `S` with every label `⊥`. -/
noncomputable def T₀ (α : Ordinal.{u}) : StageType.{u} α 3 where
  toScheme := S
  label _ := ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- **The legal type on three points**: `S` with the apex added. -/
noncomputable def T (α : Ordinal.{u}) : StageType.{u} α 3 :=
  (T₀ α).addApex isLegalBelowFullGrade_S (by omega)

/-- **`T` is legal**, at every stage. -/
theorem isLegal_T (α : Ordinal.{u}) : (T α).IsLegal :=
  StageType.isLegal_addApex _ _

/-! ### Lawfulness in `T` -/

section InT

variable {α : Ordinal.{u}}

/-- The cells of `S` keep their graded indices in `T`. -/
theorem gradedIndex_T_castSucc (d : Fin 9) :
    (T α).toCellScheme.gradedIndex (Fin.castSucc d) = cells.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc S 3 d

/-- The apex of `T` has graded index `(univ, 3)`. -/
theorem gradedIndex_T_last :
    (T α).toCellScheme.gradedIndex (Fin.last 9) = ((univ : Finset (Fin 3)), 3) :=
  Scheme.appendFullCellScheme_gradedIndex_last S 3

private theorem cases_T (i : Fin (T α).card) :
    i = Fin.last 9 ∨ ∃ d : Fin 9, i = Fin.castSucc d := by
  -- The cells of `T` are those of `S` and the apex.
  change Fin (9 + 1) at i
  induction i using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- Below a pair not above the apex, lawfulness in `T` is lawfulness in `S`. -/
theorem isLawfulBelow_T_iff {X : Finset (Fin 3) × ℕ}
    (hX : ¬ ((univ : Finset (Fin 3)), 3) ≤ X) {w : Fin (T α).card → Label.{u}} :
    (T α).rows.IsLawfulBelow X (fun d ↦ w d) ↔
      rows.IsLawfulBelow X (fun d ↦ w (Fin.castSucc d.1)) :=
  Scheme.isLawfulBelow_appendFullCell_iff (h := isLegalBelowFullGrade_S.not_le) hX

private theorem not_univ_three_le {k : ℕ} (hk : k < 3) {B : Finset (Fin 3)} :
    ¬ ((univ : Finset (Fin 3)), 3) ≤ (B, k) := fun h ↦ absurd h.2 (by simpa using hk)

end InT

/-! ### The seed of `T` with itself -/

section SeedLevel

variable {α : Ordinal.{u}}

/-- The **union fill** of `I.amalgam` on the coatom `univ.erase y` over a face `E` at the grade
`j + 1`, stated verbatim: at every cap `h` self-visible and short at `j + 1` with `⊥ < h`, along
every `a` lawful below `(univ.erase y, j + 1)`, every labelling `w` lawful below `(E, j + 1)` and
below `(univ.erase y, j)` that agrees with `a` capped at `h` on the union of the two extends,
unchanged on the union, to one lawful below `(univ.erase y, j + 1)` that agrees with `a` capped at
`h` everywhere.  It is refuted as a universal statement by `not_unionFill_seed`. -/
def UnionFill {m : ℕ} (I : Seed.{u} α m) (y : Fin (m + 2)) (E : Finset (Fin (m + 2))) (j : ℕ) :
    Prop :=
  ∀ h : Label.{u}, IsSelfVisible (j + 1) h → IsShort (j + 1) h → ⊥ < h →
  ∀ a : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) (fun d ↦ a d) →
  ∀ w : Fin I.amalgam.card → Label.{u},
    I.amalgam.rows.IsLawfulBelow (E, j + 1) (fun d ↦ w d) →
    I.amalgam.rows.IsLawfulBelow (univ.erase y, j) (fun d ↦ w d) →
    (∀ d, d ∈ I.amalgam.toCellScheme.below (E, j + 1) ∨
      d ∈ I.amalgam.toCellScheme.below (univ.erase y, j) → min (w d) h = min (a d) h) →
    ∃ v : I.amalgam.toCellScheme.below (univ.erase y, j + 1) → Label.{u},
      I.amalgam.rows.IsLawfulBelow (univ.erase y, j + 1) v ∧
      (∀ d : I.amalgam.toCellScheme.below (univ.erase y, j + 1),
        (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (E, j + 1) ∨
          (d : Fin I.amalgam.card) ∈ I.amalgam.toCellScheme.below (univ.erase y, j) →
            v d = w d) ∧
      ∀ d, min (v d) h = min (a d) h

/-- The face `{0, 1}` of `T` is a face. -/
theorem face_mem_T : univ.map (Coatom.face 2) ∈ (T α).toCellScheme.faces := by
  -- The faces of `T` are those of the interval plan.
  change univ.map (Coatom.face 2) ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The face of `T` on `{0, 1}`. -/
noncomputable def faceT (α : Ordinal.{u}) : StageType.{u} α 2 :=
  (T α).comap (Coatom.face 2) face_mem_T

/-- The face of `T` along `Coatom.face 2` is `faceT`. -/
theorem restrictFace_T : StageType.restrictFace (Coatom.face 2) (T α) = some (faceT α) :=
  StageType.restrictFace_of_mem _ _ face_mem_T

/-- **The seed of `T` with itself** on four points: the coatoms `{0, 1, 2}` and `{0, 1, 3}`, with
common face `{0, 1}`. -/
noncomputable def seed (α : Ordinal.{u}) : Seed.{u} α 2 :=
  Seed.ofCoatoms (isLegal_T α) (isLegal_T α) restrictFace_T restrictFace_T

/-- The graded indices of the live cells, carried to `Fin 4` along `Coatom.right 2`. -/
def livePairs : Finset (Finset (Fin 4) × ℕ) :=
  {({3}, 1), ({1, 3}, 1), ({0, 1, 3}, 1), ({0, 1}, 2), ({0, 1, 3}, 2)}

/-- The labelling `labelling A F` read off graded indices in `Fin 4`. -/
noncomputable def pairLabelling (A F : Label.{u}) (X : Finset (Fin 4) × ℕ) : Label.{u} :=
  if X ∈ livePairs then (if X.2 = 1 then A else F) else ⊥

private theorem mem_livePairs_iff : ∀ d : Fin 9,
    (Prod.map (Finset.map (Coatom.right 2)) id (cells.gradedIndex d) ∈ livePairs ↔
      live d = true) := by
  decide +kernel

private theorem pairLabelling_map (A F : Label.{u}) (d : Fin 9) :
    pairLabelling A F (Prod.map (Finset.map (Coatom.right 2)) id (cells.gradedIndex d)) =
      labelling A F d := by
  unfold pairLabelling labelling
  by_cases hl : live d = true
  · rw [ite_eq_left ((mem_livePairs_iff d).mpr hl), ite_eq_left hl]; rfl
  · rw [ite_eq_right (mt (mem_livePairs_iff d).mp hl), ite_eq_right hl]

/-- A labelling of `T` agreeing below `X` with `pairLabelling A F` read along `Coatom.right 2` is
lawful below `X`. -/
private theorem isLawfulBelow_of_eq_pairLabelling {A F : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hFA : F ≤ A) {X : Finset (Fin 3) × ℕ}
    (hX : ¬ ((univ : Finset (Fin 3)), 3) ≤ X) (x : Fin (T α).toScheme.card → Label.{u})
    (hx : ∀ i ∈ (T α).toScheme.toCellScheme.below X, x i = pairLabelling A F
      (Prod.map (Finset.map (Coatom.right 2)) id ((T α).toScheme.toCellScheme.gradedIndex i))) :
    (T α).toScheme.rows.IsLawfulBelow X (fun i ↦ x i) := by
  refine (isLawfulBelow_T_iff hX).mpr ?_
  convert (isLawful_labelling hA hF hFA).isLawfulBelow X using 1
  funext d
  refine (hx _ ?_).trans ?_
  · -- The graded index of a cell of `S` in `T`.
    change (T α).toCellScheme.gradedIndex (Fin.castSucc d.1) ≤ X
    rw [gradedIndex_T_castSucc]
    exact d.2
  · rw [gradedIndex_T_castSucc]
    exact pairLabelling_map A F d.1

/-- **The coupling in `T`**: below `(univ, 2)` the label of the cell at `({0, 1}, 2)` is at most
that of the cell at `({2}, 1)`. -/
private theorem le_of_isLawfulBelow_two (x : Fin (T α).toScheme.card → Label.{u})
    (hx : (T α).toScheme.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun i ↦ x i))
    (i j : Fin (T α).toScheme.card)
    (hi : (T α).toScheme.toCellScheme.gradedIndex i = (({0, 1} : Finset (Fin 3)), 2))
    (hj : (T α).toScheme.toCellScheme.gradedIndex j = (({2} : Finset (Fin 3)), 1)) :
    x i ≤ x j := by
  have hx' := (isLawfulBelow_T_iff (α := α) (w := x) (not_univ_three_le (by omega))).mp hx
  obtain ⟨A, F, -, -, hFA, hAF⟩ :=
    (isLawfulBelow_iff (x := fun e ↦ x (Fin.castSucc e))).mp hx'
  rcases cases_T (α := α) i with rfl | ⟨d, rfl⟩
  · exact absurd (gradedIndex_T_last (α := α) ▸ hi) (by decide)
  rcases cases_T (α := α) j with rfl | ⟨e, rfl⟩
  · exact absurd (gradedIndex_T_last (α := α) ▸ hj) (by decide)
  have hd : d = 6 := gradedIndex_injective (((gradedIndex_T_castSucc (α := α) d).symm.trans
    hi).trans rfl)
  have he : e = 2 := gradedIndex_injective (((gradedIndex_T_castSucc (α := α) e).symm.trans
    hj).trans rfl)
  subst hd he
  have h6 := hAF (6 : Fin 9) ⟨subset_univ _, le_rfl⟩
  have h2 := hAF (2 : Fin 9) ⟨subset_univ _, by decide⟩
  rw [labelling_two rfl rfl] at h6
  rw [labelling_one rfl rfl] at h2
  exact h6.trans_le (hFA.trans_eq h2.symm)

/-- The face of the amalgam of `seed α` along `Coatom.right 2` is `T`, as a scheme. -/
private theorem comap_seed_right :
    (seed α).amalgam.toScheme.comap (Coatom.right 2) = (T α).toScheme := by
  obtain ⟨hf, he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp (seed α).restrictFace_right
  exact congrArg StageType.toScheme he

/-- Lawfulness transported along the restriction to a face. -/
private theorem isLawfulBelow_comap_cellMap_iff {n m : ℕ} (S' : Scheme.{u} n) (f : Fin m ↪ Fin n)
    (X : Finset (Fin m) × ℕ) (x : Fin S'.card → Label.{u}) :
    (S'.comap f).rows.IsLawfulBelow X (fun i ↦ x (S'.cellMap f i)) ↔
      S'.rows.IsLawfulBelow (Prod.map (Finset.map f) id X) (fun d ↦ x d) :=
  CellScheme.Rows.isLawfulBelow_comap_iff (R := S'.rows) (S'.isLowerEmbedding_comap f)
    (S'.image_cellMap_below f X) (r := fun d ↦ x d)

private theorem map_right_commonFace :
    ({0, 1} : Finset (Fin 3)).map (Coatom.right 2) = ({0, 1} : Finset (Fin 4)) := by
  decide +kernel

private theorem pairLabelling_commonFace (A F : Label.{u}) {X : Finset (Fin 4) × ℕ}
    (hX : X ≤ (({0, 1} : Finset (Fin 4)), 2)) : pairLabelling A F X = pairLabelling ⊤ F X := by
  unfold pairLabelling
  by_cases hl : X ∈ livePairs
  · rw [ite_eq_left hl, ite_eq_left hl]
    by_cases h1 : X.2 = 1
    · exfalso
      have key : ∀ Y ∈ livePairs, Y.2 = 1 → (3 : Fin 4) ∈ Y.1 := by decide
      exact absurd (hX.1 (key X hl h1)) (by decide)
    · rw [ite_eq_right h1, ite_eq_right h1]
  · rw [ite_eq_right hl, ite_eq_right hl]

private theorem pairLabelling_one (A F : Label.{u}) {X : Finset (Fin 4) × ℕ} (hX : X.2 ≤ 1) :
    pairLabelling A F X = pairLabelling A ⊥ X := by
  unfold pairLabelling
  by_cases hl : X ∈ livePairs
  · rw [ite_eq_left hl, ite_eq_left hl]
    have key : ∀ Y ∈ livePairs, 1 ≤ Y.2 := by decide
    rw [ite_eq_left (le_antisymm hX (key X hl)), ite_eq_left (le_antisymm hX (key X hl))]
  · rw [ite_eq_right hl, ite_eq_right hl]

/-- **The union fill fails for the seed of `T` with itself**, on the coatom `{0, 1, 3}` (`y` the
point `2`), over the common face `{0, 1}`, at the grade `2` (`j = 1`), at the cap `2`: the
ambient `labelling 2 2` and the labelling `labelling 2 ⊤`, read along the second coatom, satisfy
its hypotheses, and a lawful extension below `({0, 1, 3}, 2)` would have `⊤ ≤ 2` by the coupling
row of the cell at `({0, 1, 3}, 2)`. -/
theorem not_unionFill_seed :
    ¬ UnionFill (seed α) (Fin.castSucc (Fin.last 2)) ({0, 1} : Finset (Fin 4)) 1 := by
  classical
  intro hU
  set Am := (seed α).amalgam with hAm
  have heq : Am.toScheme.comap (Coatom.right 2) = (T α).toScheme := comap_seed_right
  have hv1 : IsSelfVisible 1 (rowValue : Label.{u}) := isSelfVisible_rowValue 1 (by omega)
  have hv2 : IsSelfVisible 2 (rowValue : Label.{u}) := isSelfVisible_rowValue 2 le_rfl
  have hvtop : ¬ (⊤ : Label.{u}) ≤ rowValue := fun h ↦ gridPoint_ne_top 2 0 (top_le_iff.mp h)
  -- The graded indices of the amalgam along the second coatom.
  have hgi (i : Fin (Am.toScheme.comap (Coatom.right 2)).card) :
      Am.toCellScheme.gradedIndex (Am.toScheme.cellMap (Coatom.right 2) i) =
        Prod.map (Finset.map (Coatom.right 2)) id
          ((Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i) :=
    (Am.toScheme.map_comap_gradedIndex (Coatom.right 2) i).symm
  -- The facts about `T`, carried to the face of the amalgam.
  have hlaw : ∀ {A F : Label.{u}}, IsSelfVisible 1 A → IsSelfVisible 2 F → F ≤ A →
      ∀ {X : Finset (Fin 3) × ℕ}, ¬ ((univ : Finset (Fin 3)), 3) ≤ X →
      ∀ x : Fin (Am.toScheme.comap (Coatom.right 2)).card → Label.{u},
      (∀ i ∈ (Am.toScheme.comap (Coatom.right 2)).toCellScheme.below X, x i = pairLabelling A F
        (Prod.map (Finset.map (Coatom.right 2)) id
          ((Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap (Coatom.right 2)).rows.IsLawfulBelow X (fun i ↦ x i) := by
    rw [heq]; exact fun hA hF hFA _ hX x hx ↦ isLawfulBelow_of_eq_pairLabelling hA hF hFA hX x hx
  have hcoupling : ∀ x : Fin (Am.toScheme.comap (Coatom.right 2)).card → Label.{u},
      (Am.toScheme.comap (Coatom.right 2)).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun i ↦ x i) →
      ∀ i j, (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
          (({0, 1} : Finset (Fin 3)), 2) →
        (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex j =
          (({2} : Finset (Fin 3)), 1) → x i ≤ x j := by
    rw [heq]; exact le_of_isLawfulBelow_two
  have h6ex : ∃ i : Fin (Am.toScheme.comap (Coatom.right 2)).card,
      (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
        (({0, 1} : Finset (Fin 3)), 2) := by
    rw [heq]; exact ⟨Fin.castSucc (6 : Fin 9), gradedIndex_T_castSucc 6⟩
  have h2ex : ∃ i : Fin (Am.toScheme.comap (Coatom.right 2)).card,
      (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
        (({2} : Finset (Fin 3)), 1) := by
    rw [heq]; exact ⟨Fin.castSucc (2 : Fin 9), gradedIndex_T_castSucc 2⟩
  obtain ⟨i6, hi6⟩ := h6ex
  obtain ⟨i2, hi2⟩ := h2ex
  have hpair2 : Prod.map (Finset.map (Coatom.right 2)) id ((univ : Finset (Fin 3)), 2) =
      (univ.erase (Fin.castSucc (Fin.last 2)), 1 + 1) := Prod.ext Coatom.univ_map_right rfl
  have hpair1 : Prod.map (Finset.map (Coatom.right 2)) id ((univ : Finset (Fin 3)), 1) =
      (univ.erase (Fin.castSucc (Fin.last 2)), 1) := Prod.ext Coatom.univ_map_right rfl
  have hpairE : Prod.map (Finset.map (Coatom.right 2)) id (({0, 1} : Finset (Fin 3)), 2) =
      (({0, 1} : Finset (Fin 4)), 1 + 1) := Prod.ext map_right_commonFace rfl
  -- The ambient and the labelling on the union, read off graded indices.
  let a : Fin Am.card → Label.{u} := fun d ↦ pairLabelling rowValue rowValue
    (Am.toCellScheme.gradedIndex d)
  let w : Fin Am.card → Label.{u} := fun d ↦ pairLabelling rowValue ⊤
    (Am.toCellScheme.gradedIndex d)
  have ha : Am.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 1 + 1)
      (fun d ↦ a d) := by
    have := (isLawfulBelow_comap_cellMap_iff Am.toScheme (Coatom.right 2)
      ((univ : Finset (Fin 3)), 2) a).mp
      (hlaw hv1 hv2 le_rfl (not_univ_three_le (by omega))
        (fun i ↦ a (Am.toScheme.cellMap (Coatom.right 2) i)) fun i _ ↦ by
          -- `a` read at the image of the cell `i` under the cell map
          change pairLabelling rowValue rowValue
            (Am.toCellScheme.gradedIndex (Am.toScheme.cellMap (Coatom.right 2) i)) = _
          rw [hgi])
    rwa [hpair2] at this
  have hwE : Am.rows.IsLawfulBelow (({0, 1} : Finset (Fin 4)), 1 + 1) (fun d ↦ w d) := by
    have := (isLawfulBelow_comap_cellMap_iff Am.toScheme (Coatom.right 2)
      (({0, 1} : Finset (Fin 3)), 2) w).mp
      (hlaw (A := ⊤) (F := ⊤) (isSelfVisible_top 1) (isSelfVisible_top 2) le_rfl
        (not_univ_three_le (by omega)) (fun i ↦ w (Am.toScheme.cellMap (Coatom.right 2) i))
        fun i hi ↦ by
          -- `w` read at the image of the cell `i` under the cell map
          change pairLabelling rowValue ⊤
            (Am.toCellScheme.gradedIndex (Am.toScheme.cellMap (Coatom.right 2) i)) = _
          rw [hgi]
          refine pairLabelling_commonFace rowValue ⊤ ?_
          have hi' : (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i ≤
              (({0, 1} : Finset (Fin 3)), 2) := hi
          exact ⟨by rw [← map_right_commonFace]; exact Finset.map_subset_map.mpr hi'.1, hi'.2⟩)
    rwa [hpairE] at this
  have hwD : Am.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 1)
      (fun d ↦ w d) := by
    have := (isLawfulBelow_comap_cellMap_iff Am.toScheme (Coatom.right 2)
      ((univ : Finset (Fin 3)), 1) w).mp
      (hlaw (A := rowValue) (F := ⊥) hv1 (isSelfVisible_bot 2) bot_le
        (not_univ_three_le (by omega)) (fun i ↦ w (Am.toScheme.cellMap (Coatom.right 2) i))
        fun i hi ↦ by
          -- `w` read at the image of the cell `i` under the cell map
          change pairLabelling rowValue ⊤
            (Am.toCellScheme.gradedIndex (Am.toScheme.cellMap (Coatom.right 2) i)) = _
          rw [hgi]
          exact pairLabelling_one rowValue ⊤ hi.2)
    rwa [hpair1] at this
  have hcap : ∀ d, d ∈ Am.toCellScheme.below (({0, 1} : Finset (Fin 4)), 1 + 1) ∨
      d ∈ Am.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 2)), 1) →
      min (w d) rowValue = min (a d) rowValue := by
    intro d _
    -- `w` and `a` are `pairLabelling` read at the graded index of `d`
    change min (pairLabelling rowValue ⊤ _) rowValue = min (pairLabelling rowValue rowValue _) _
    unfold pairLabelling
    split_ifs <;> simp
  obtain ⟨x, hx, hxw, -⟩ := hU rowValue hv2 (isShort_gridPoint 2 0)
    (bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 2 0)) a ha w hwE hwD hcap
  -- Read `x` at the cells at `({0, 1}, 2)` and `({3}, 1)`, and compare them.
  set d6 := Am.toScheme.cellMap (Coatom.right 2) i6
  set d2 := Am.toScheme.cellMap (Coatom.right 2) i2
  have hd6 : Am.toCellScheme.gradedIndex d6 = (({0, 1} : Finset (Fin 4)), 2) := by
    rw [hgi, hi6]; exact Prod.ext map_right_commonFace rfl
  have hmap2 : ({2} : Finset (Fin 3)).map (Coatom.right 2) = ({3} : Finset (Fin 4)) := by
    decide +kernel
  have hd2 : Am.toCellScheme.gradedIndex d2 = (({3} : Finset (Fin 4)), 1) := by
    rw [hgi, hi2]; exact Prod.ext hmap2 rfl
  have hd6Y : d6 ∈ Am.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 2)), 1 + 1) := by
    -- membership below a pair is `≤` on graded indices
    change Am.toCellScheme.gradedIndex d6 ≤ _
    rw [hd6]
    exact ⟨by decide, le_rfl⟩
  have hd2Y : d2 ∈ Am.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 2)), 1 + 1) := by
    -- membership below a pair is `≤` on graded indices
    change Am.toCellScheme.gradedIndex d2 ≤ _
    rw [hd2]
    exact ⟨by decide, by omega⟩
  have hd6E : d6 ∈ Am.toCellScheme.below (({0, 1} : Finset (Fin 4)), 1 + 1) := by
    -- membership below a pair is `≤` on graded indices
    change Am.toCellScheme.gradedIndex d6 ≤ _
    rw [hd6]
  have hd2D : d2 ∈ Am.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 2)), 1) := by
    -- membership below a pair is `≤` on graded indices
    change Am.toCellScheme.gradedIndex d2 ≤ _
    rw [hd2]
    exact ⟨by decide, le_rfl⟩
  have hx6 : x ⟨d6, hd6Y⟩ = ⊤ := by
    rw [hxw ⟨d6, hd6Y⟩ (Or.inl hd6E)]
    -- the prescription `w` read at the cell `d6`
    change pairLabelling rowValue ⊤ (Am.toCellScheme.gradedIndex d6) = ⊤
    rw [hd6]
    unfold pairLabelling
    rw [ite_eq_left (by decide), ite_eq_right (by decide)]
  have hx2 : x ⟨d2, hd2Y⟩ = rowValue := by
    rw [hxw ⟨d2, hd2Y⟩ (Or.inr hd2D)]
    -- the prescription `w` read at the cell `d2`
    change pairLabelling rowValue ⊤ (Am.toCellScheme.gradedIndex d2) = rowValue
    rw [hd2]
    unfold pairLabelling
    rw [ite_eq_left (by decide), ite_eq_left rfl]
  have hxx := (isLawfulBelow_comap_cellMap_iff Am.toScheme (Coatom.right 2)
    ((univ : Finset (Fin 3)), 2) (Rows.extendBot _ x)).mpr (by
      rw [hpair2]
      exact Rows.isLawfulBelow_extendBot.mpr hx)
  have hle : Rows.extendBot _ x d6 ≤ Rows.extendBot _ x d2 :=
    hcoupling (fun i ↦ Rows.extendBot _ x (Am.toScheme.cellMap (Coatom.right 2) i)) hxx i6 i2
      hi6 hi2
  rw [Rows.extendBot_of_mem x hd6Y, Rows.extendBot_of_mem x hd2Y, hx6, hx2] at hle
  exact hvtop hle

/-- **The labelling of the failure is not lawful below the coatom `({0, 1, 3}, 2)`**: read along
the second coatom it is `labelling 2 ⊤`, and the coupling row of the cell at `({0, 1, 3}, 2)` asks
`⊤ ≤ 2`.  So it is not a prescription of the two-face lift `2FL(1)`, which asks lawfulness below
both coatoms at the grade `2`; the constraint `F ≤ A` that defeats the union fill is part of that
hypothesis. -/
theorem not_isLawfulBelow_pairLabelling_top :
    ¬ (seed α).amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 2)), 2)
      (fun d ↦ pairLabelling rowValue ⊤ ((seed α).amalgam.toCellScheme.gradedIndex d)) := by
  classical
  intro hw
  set Am := (seed α).amalgam
  have heq : Am.toScheme.comap (Coatom.right 2) = (T α).toScheme := comap_seed_right
  have hgi (i : Fin (Am.toScheme.comap (Coatom.right 2)).card) :
      Am.toCellScheme.gradedIndex (Am.toScheme.cellMap (Coatom.right 2) i) =
        Prod.map (Finset.map (Coatom.right 2)) id
          ((Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i) :=
    (Am.toScheme.map_comap_gradedIndex (Coatom.right 2) i).symm
  have hcoupling : ∀ x : Fin (Am.toScheme.comap (Coatom.right 2)).card → Label.{u},
      (Am.toScheme.comap (Coatom.right 2)).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
        (fun i ↦ x i) →
      ∀ i j, (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
          (({0, 1} : Finset (Fin 3)), 2) →
        (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex j =
          (({2} : Finset (Fin 3)), 1) → x i ≤ x j := by
    rw [heq]; exact le_of_isLawfulBelow_two
  obtain ⟨i6, hi6⟩ : ∃ i : Fin (Am.toScheme.comap (Coatom.right 2)).card,
      (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
        (({0, 1} : Finset (Fin 3)), 2) := by
    rw [heq]; exact ⟨Fin.castSucc (6 : Fin 9), gradedIndex_T_castSucc 6⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin (Am.toScheme.comap (Coatom.right 2)).card,
      (Am.toScheme.comap (Coatom.right 2)).toCellScheme.gradedIndex i =
        (({2} : Finset (Fin 3)), 1) := by
    rw [heq]; exact ⟨Fin.castSucc (2 : Fin 9), gradedIndex_T_castSucc 2⟩
  have hpair2 : Prod.map (Finset.map (Coatom.right 2)) id ((univ : Finset (Fin 3)), 2) =
      (univ.erase (Fin.castSucc (Fin.last 2)), 2) := Prod.ext Coatom.univ_map_right rfl
  let w : Fin Am.card → Label.{u} := fun d ↦ pairLabelling rowValue ⊤
    (Am.toCellScheme.gradedIndex d)
  have hw' : Am.rows.IsLawfulBelow
      (Prod.map (Finset.map (Coatom.right 2)) id ((univ : Finset (Fin 3)), 2)) (fun d ↦ w d) := by
    rw [hpair2]; exact hw
  have hle : w (Am.toScheme.cellMap (Coatom.right 2) i6) ≤
      w (Am.toScheme.cellMap (Coatom.right 2) i2) :=
    hcoupling (fun i ↦ w (Am.toScheme.cellMap (Coatom.right 2) i))
      ((isLawfulBelow_comap_cellMap_iff Am.toScheme (Coatom.right 2)
        ((univ : Finset (Fin 3)), 2) w).mpr hw') i6 i2 hi6 hi2
  -- `w` read at the images of the cells `i6` and `i2` under the cell map
  change pairLabelling rowValue ⊤
      (Am.toCellScheme.gradedIndex (Am.toScheme.cellMap (Coatom.right 2) i6)) ≤
    pairLabelling rowValue ⊤
      (Am.toCellScheme.gradedIndex (Am.toScheme.cellMap (Coatom.right 2) i2)) at hle
  have hmap2 : ({2} : Finset (Fin 3)).map (Coatom.right 2) = ({3} : Finset (Fin 4)) := by
    decide +kernel
  rw [hgi, hgi, hi6, hi2, Prod.map_apply, Prod.map_apply, map_right_commonFace, hmap2] at hle
  unfold pairLabelling at hle
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_left (by decide)] at hle
  exact gridPoint_ne_top 2 0 (top_le_iff.mp (hle.trans_eq (ite_eq_left rfl)))

end SeedLevel

end VaughtConjecture.UnionFillCounterexample
