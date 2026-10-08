/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Continuation.SourceGapSeparatedInstance
import VaughtConjecture.Continuation.SourceGapSeparationObstruction
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.CanonicalCode
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Label.StepWitness

/-!
# The squeeze type on three points (work file)

WORK FILE (branch `research/work-h2-squeeze`).  No `sorry`.

**The scheme `S`** (`SqueezeType.S`, legal below the full grade, `SqueezeType.isLegalBelow_S`).
On three points with the interval plan, one cell at every graded face of grade at most `2`:

| cell  | 0   | 1   | 2   | 3      | 4      | 5    | 6      | 7      | 8    |
|-------|-----|-----|-----|--------|--------|------|--------|--------|------|
| scope | {0} | {1} | {2} | {0, 1} | {1, 2} | univ | {0, 1} | {1, 2} | univ |
| grade | 1   | 1   | 1   | 1      | 1      | 1    | 2      | 2      | 2    |
| class | –   | –   | A   | B      | A      | B    | F      | –      | F    |

The cells without a class are dead.  The row of the cell `5` (of graded index `(univ, 1)`) reads
the cells of class `A` at `1` and those of class `B` at `ω + 2`; the row of every other live cell
reads every live cell below it at `2`; dead cells read `⊥`.

**The lawful labellings** (`SqueezeType.isLawfulBelow_iff`).  Below every pair a labelling is
lawful exactly when it agrees there with `lab a b F` (`⊥` at the dead cells, `a`, `b`, `F` at the
classes `A`, `B`, `F`) for some `a`, `b` self-visible at `1` and `F` self-visible at `2` with
`F ≤ a ≤ b`.  So the cell `6` at `({0, 1}, 2)` (class `F`) lies below the cell `2` at `({2}, 1)`
(class `A`), which lies below the cell `3` at `({0, 1}, 1)` (class `B`); at the grade `1` the
cells `2` and `3` are read differently (`a < b` is allowed).

**Legality.**  Every pair lifts capped to every larger one (`SqueezeType.cappedLift_all`): the
classes below the smaller pair keep the prescription, `B` is otherwise the ambient below the cap
and `⊤` above it, `F` the ambient capped, and `A` the larger of the new `F` and the ambient
capped.  The type on three points is `S` with a dead cell of graded index `(univ, 3)` appended
(`SqueezeType.Sq`, `SqueezeType.isLegal_Sq`).

## Placement

Work file of the h2 lane (Layer 3).
-/

universe u

namespace VaughtConjecture.SqueezeType

open Finset Label CellScheme
open SeparatedInstance (omegaAddTwo transformsTo_twoLevel)
open SeparationObstruction (low low_lt_omegaAddTwo)
open scoped Ordinal

/-! ### The scheme on three points -/

/-- The scopes of the nine cells. -/
def cellScope : Fin 9 → Finset (Fin 3) :=
  ![{0}, {1}, {2}, {0, 1}, {1, 2}, univ, {0, 1}, {1, 2}, univ]

/-- The grades of the nine cells. -/
def cellGrade : Fin 9 → ℕ := ![1, 1, 1, 1, 1, 1, 2, 2, 2]

/-- The classes of the cells: `0` dead, `1` the class `A`, `2` the class `B`, `3` the class `F`. -/
def cls : Fin 9 → Fin 4 := ![0, 0, 1, 2, 1, 2, 3, 0, 3]

/-- The cell scheme on three points with the interval plan. -/
def cells : CellScheme (Fin 9) (Fin 3) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

/-- The row of the cell `5` at its cells: `1` at the class `A`, `ω + 2` at the class `B`. -/
noncomputable def val5 (d : Fin 9) : Label.{u} :=
  if cls d = 1 then 1 else if cls d = 2 then omegaAddTwo else ⊥

/-- The row values. -/
noncomputable def rowValue (s d : Fin 9) : Label.{u} :=
  if s = 5 then val5 d else if cls s ≠ 0 ∧ cls d ≠ 0 then low else ⊥

/-- The rows. -/
noncomputable def rows : cells.Rows.{u} := ⟨fun s t ↦ rowValue s t.1⟩

/-- The scheme on three points below the full grade. -/
noncomputable abbrev S : Scheme.{u} 3 := ⟨9, cells, rows⟩

/-- The value of a class. -/
def classVal (a b F : Label.{u}) : Fin 4 → Label.{u} := ![⊥, a, b, F]

/-- The labelling with `⊥` at the dead cells and `a`, `b`, `F` at the classes `A`, `B`, `F`. -/
def lab (a b F : Label.{u}) (d : Fin 9) : Label.{u} := classVal a b F (cls d)

theorem gradedIndex_cells (d : Fin 9) : cells.gradedIndex d = (cellScope d, cellGrade d) := rfl

theorem gradedIndex_injective : Function.Injective cells.gradedIndex := by
  intro a b h
  rw [gradedIndex_cells, gradedIndex_cells] at h
  revert a b; decide +kernel

theorem cls_cases (d : Fin 9) : cls d = 0 ∨ cls d = 1 ∨ cls d = 2 ∨ cls d = 3 := by
  revert d; decide

theorem lab_dead {a b F : Label.{u}} {d : Fin 9} (h : cls d = 0) : lab a b F d = ⊥ := by
  simp [lab, h, classVal]

theorem lab_A {a b F : Label.{u}} {d : Fin 9} (h : cls d = 1) : lab a b F d = a := by
  simp [lab, h, classVal]

theorem lab_B {a b F : Label.{u}} {d : Fin 9} (h : cls d = 2) : lab a b F d = b := by
  simp [lab, h, classVal]

theorem lab_F {a b F : Label.{u}} {d : Fin 9} (h : cls d = 3) : lab a b F d = F := by
  simp [lab, h, classVal]

private theorem grade_of_cls {d : Fin 9} :
    (cls d = 1 ∨ cls d = 2 → cellGrade d = 1) ∧ (cls d = 3 → cellGrade d = 2) := by
  revert d; decide

private theorem grade_le_five : ∀ d : Fin 9, cells.gradedIndex d ≤ cells.gradedIndex 5 →
    cellGrade d = 1 := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

private theorem one_lt_omegaAddTwo : (1 : Label.{u}) < omegaAddTwo.{u} := by
  refine lt_of_le_of_lt ?_ low_lt_omegaAddTwo
  simp

private theorem isSelfVisible_omegaAddTwo : IsSelfVisible 1 omegaAddTwo.{u} :=
  isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega)

private theorem isSelfVisible_low (k : ℕ) (hk : k ≤ 2) : IsSelfVisible k low.{u} :=
  (isSelfVisible_natCast 2).mpr hk

/-! ### The labellings `lab a b F` are lawful -/

/-- The labels of `lab a b F` are self-visible at the grades. -/
private theorem isSelfVisible_lab {a b F : Label.{u}} (ha : IsSelfVisible 1 a)
    (hb : IsSelfVisible 1 b) (hF : IsSelfVisible 2 F) (d : Fin 9) :
    IsSelfVisible (cellGrade d) (lab a b F d) := by
  rcases cls_cases d with h | h | h | h
  · rw [lab_dead h]; exact isSelfVisible_bot _
  · rw [lab_A h, grade_of_cls.1 (.inl h)]; exact ha
  · rw [lab_B h, grade_of_cls.1 (.inr h)]; exact hb
  · rw [lab_F h, grade_of_cls.2 h]; exact hF

/-- The class order: below a live cell `s` other than `5`, every live cell has a class at least
that of `s` (`F` below `A` below `B`). -/
private theorem cls_le_of_le : ∀ s d : Fin 9, s ≠ 5 → cls s ≠ 0 → cls d ≠ 0 →
    cells.gradedIndex d ≤ cells.gradedIndex s →
      cls s = cls d ∨ (cls s = 3 ∧ cls d ≠ 3) ∨ (cls s = 1 ∧ cls d = 2) := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- Availability: a cell below another of the same grade has a class at most its class. -/
private theorem cls_le_of_avail : ∀ s t : Fin 9, cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → cls s = 0 ∨ cls s = cls t ∨ (cls s = 1 ∧ cls t = 2) := by
  decide +kernel

/-- **`lab a b F` is lawful** for `a`, `b` self-visible at `1`, `F` at `2`, and `F ≤ a ≤ b`. -/
theorem isLawful_lab {a b F : Label.{u}} (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hF : IsSelfVisible 2 F) (hFa : F ≤ a) (hab : a ≤ b) : rows.IsLawful (lab a b F) where
  orderly d := isSelfVisible_lab ha hb hF d
  locality s := by
    by_cases h5 : s = 5
    · subst h5
      refine transformsTo_twoLevel
        (fun d : cells.below (cells.gradedIndex 5) ↦ grade_le_five d.1 d.2)
        ha hb hab fun ⟨d, hd⟩ ↦ ?_
      change (val5 d = ⊥ ∧ min (lab a b F d) (lab a b F 5) = ⊥) ∨
        (val5 d = 1 ∧ min (lab a b F d) (lab a b F 5) = a) ∨
        (val5 d = omegaAddTwo ∧ min (lab a b F d) (lab a b F 5) = b)
      have h5B : lab a b F 5 = b := lab_B (by decide)
      rw [h5B]
      have hd' : cls d ≠ 3 := by
        have := grade_le_five d hd
        intro h3; have := grade_of_cls.2 h3; omega
      rcases cls_cases d with h | h | h | h
      · exact .inl ⟨by simp [val5, h], by rw [lab_dead h]; exact min_eq_left bot_le⟩
      · exact .inr (.inl ⟨by simp [val5, h], by rw [lab_A h]; exact min_eq_left hab⟩)
      · exact .inr (.inr ⟨by simp [val5, h], by rw [lab_B h]; exact min_self _⟩)
      · exact absurd h hd'
    by_cases hs : cls s = 0
    · rw [show (fun d : cells.below (cells.gradedIndex s) ↦ min (lab a b F d.1) (lab a b F s)) =
        fun _ ↦ ⊥ from funext fun _ ↦ by rw [lab_dead hs, min_bot_right]]
      exact TransformsTo.bot _ _
    have hsv : IsSelfVisible (cellGrade s) (lab a b F s) := isSelfVisible_lab ha hb hF s
    refine ⟨constStepSuppressor (cellGrade s) (lab a b F s), topShifter,
      isWitness_topShifter (antitone_constStepSuppressor _ _)
        (isSelfVisible_constStepSuppressor hsv), fun ⟨d, hd⟩ ↦ ?_⟩
    have hgd : cellGrade d ≤ cellGrade s := hd.2
    change min (lab a b F d) (lab a b F s) =
      min (topShifter (rowValue s d))
        (constStepSuppressor (cellGrade s) (lab a b F s) (cellGrade d))
    by_cases hd0 : cls d = 0
    · rw [lab_dead hd0]
      simp [rowValue, h5, hd0, topShifter]
    rw [show rowValue s d = low by simp [rowValue, h5, hs, hd0], topShifter,
      ite_eq_right (by simp [low]), constStepSuppressor, ite_eq_left hgd, min_top_left,
      min_eq_right]
    rcases cls_le_of_le s d h5 hs hd0 hd with e | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · simp only [lab, e, le_rfl]
    · rw [lab_F e1]
      rcases cls_cases d with h | h | h | h
      · exact absurd h hd0
      · rw [lab_A h]; exact hFa
      · rw [lab_B h]; exact hFa.trans hab
      · exact absurd h e2
    · rw [lab_A e1, lab_B e2]; exact hab
  availability s t hst hg := by
    refine ⟨t, rfl, ?_⟩
    rcases cls_le_of_avail s t hst hg with e | e | ⟨e1, e2⟩
    · rw [lab_dead e]; exact bot_le
    · simp only [lab, e, le_rfl]
    · rw [lab_A e1, lab_B e2]; exact hab

/-! ### The lawful labellings below a pair -/

private theorem mem_below_of_le {Z : Finset (Fin 3) × ℕ} {d e : Fin 9} (hd : d ∈ cells.below Z)
    (h : cells.gradedIndex e ≤ cells.gradedIndex d) : e ∈ cells.below Z := le_trans h hd

/-- A pair above the cells `2` and `3` lies above the cell `5`. -/
private theorem five_mem {Z : Finset (Fin 3) × ℕ} (h2 : (2 : Fin 9) ∈ cells.below Z)
    (h3 : (3 : Fin 9) ∈ cells.below Z) : (5 : Fin 9) ∈ cells.below Z := by
  refine ⟨fun z _ ↦ ?_, h3.2⟩
  have h2' : cellScope 2 ⊆ Z.1 := h2.1
  have h3' : cellScope 3 ⊆ Z.1 := h3.1
  fin_cases z
  · exact h3' (by decide)
  · exact h3' (by decide)
  · exact h2' (by decide)

/-- A pair above the cells `2` and `6` lies above the cell `8`. -/
private theorem eight_mem {Z : Finset (Fin 3) × ℕ} (h2 : (2 : Fin 9) ∈ cells.below Z)
    (h6 : (6 : Fin 9) ∈ cells.below Z) : (8 : Fin 9) ∈ cells.below Z := by
  refine ⟨fun z _ ↦ ?_, h6.2⟩
  have h2' : cellScope 2 ⊆ Z.1 := h2.1
  have h6' : cellScope 6 ⊆ Z.1 := h6.1
  fin_cases z
  · exact h6' (by decide)
  · exact h6' (by decide)
  · exact h2' (by decide)

/-- The representatives of the classes lie below their cells. -/
private theorem rep_le : ∀ d : Fin 9,
    (cls d = 1 → cells.gradedIndex 2 ≤ cells.gradedIndex d) ∧
    (cls d = 2 → cells.gradedIndex 3 ≤ cells.gradedIndex d) ∧
    (cls d = 3 → cells.gradedIndex 6 ≤ cells.gradedIndex d) := by
  simp only [gradedIndex_cells, Prod.mk_le_mk]; decide +kernel

/-- **The lawful labellings below a pair** are the restrictions of the labellings `lab a b F`
with `a`, `b` self-visible at `1`, `F` self-visible at `2`, and `F ≤ a ≤ b`. -/
theorem isLawfulBelow_iff {Y : Finset (Fin 3) × ℕ} {x : Fin 9 → Label.{u}} :
    rows.IsLawfulBelow Y (fun d ↦ x d) ↔ ∃ a b F : Label.{u}, IsSelfVisible 1 a ∧
      IsSelfVisible 1 b ∧ IsSelfVisible 2 F ∧ F ≤ a ∧ a ≤ b ∧
        ∀ d ∈ cells.below Y, x d = lab a b F d := by
  classical
  constructor
  · intro hx
    obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
    -- locality read at two cells below `s` whose row values compare
    have hloc (s : Fin 9) (hs : s ∈ cells.below Y) (d e : Fin 9)
        (hd : cells.gradedIndex d ≤ cells.gradedIndex s)
        (he : cells.gradedIndex e ≤ cells.gradedIndex s) (hr : rowValue s d ≤ rowValue s e)
        (hg : cellGrade e ≤ cellGrade d) : min (x d) (x s) ≤ min (x e) (x s) :=
      (hl s hs).le_of_le (d := ⟨d, hd⟩) (d' := ⟨e, he⟩) hr hg
    have hself (s : Fin 9) (hs : s ∈ cells.below Y) (e : Fin 9)
        (he : cells.gradedIndex e ≤ cells.gradedIndex s) (hr : rowValue s s ≤ rowValue s e) :
        x s ≤ x e := by
      have := hloc s hs s e le_rfl he hr he.2
      rw [min_self] at this
      exact this.trans (min_le_left _ _)
    have havail (s t : Fin 9) (ht : t ∈ cells.below Y) (hst : cellScope s ⊆ cellScope t)
        (hg : cellGrade s = cellGrade t) : x s ≤ x t := by
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rwa [gradedIndex_injective hu] at hle
    have hdead (d : Fin 9) (hd : d ∈ cells.below Y) (h0 : cls d = 0) : x d = ⊥ := by
      have := (hl d hd).eq_bot (d := ⟨d, cells.mem_below_gradedIndex d⟩) (by
        change rowValue d d = ⊥
        have : d ≠ 5 := by rintro rfl; exact absurd h0 (by decide)
        simp [rowValue, this, h0])
      simpa using this
    -- the equalities within the classes and the order between them
    have e42 (h4 : (4 : Fin 9) ∈ cells.below Y) : x 4 = x 2 :=
      le_antisymm (hself 4 h4 2 (by decide) (by simp [rowValue, cls]))
        (havail 2 4 h4 (by decide) rfl)
    have e53 (h5 : (5 : Fin 9) ∈ cells.below Y) : x 5 = x 3 :=
      le_antisymm (hself 5 h5 3 (by decide) (by simp [rowValue, val5, cls]))
        (havail 3 5 h5 (by decide) rfl)
    have e86 (h8 : (8 : Fin 9) ∈ cells.below Y) : x 8 = x 6 :=
      le_antisymm (hself 8 h8 6 (by decide) (by simp [rowValue, cls]))
        (havail 6 8 h8 (by decide) rfl)
    have l23 (h5 : (5 : Fin 9) ∈ cells.below Y) : x 2 ≤ x 3 := by
      have h := hloc 5 h5 2 3 (by decide) (by decide)
        (by simp only [rowValue, val5, cls]; simpa using one_lt_omegaAddTwo.le) le_rfl
      rw [min_eq_left (havail 2 5 h5 (by decide) rfl)] at h
      exact h.trans (min_le_left _ _)
    have l62 (h8 : (8 : Fin 9) ∈ cells.below Y) : x 6 ≤ x 2 :=
      (havail 6 8 h8 (by decide) rfl).trans (hself 8 h8 2 (by decide) (by simp [rowValue, cls]))
    have l63 (h6 : (6 : Fin 9) ∈ cells.below Y) : x 6 ≤ x 3 :=
      hself 6 h6 3 (by decide) (by simp [rowValue, cls])
    have m3of6 (h6 : (6 : Fin 9) ∈ cells.below Y) : (3 : Fin 9) ∈ cells.below Y :=
      mem_below_of_le h6 (by decide)
    set b : Label.{u} := if (3 : Fin 9) ∈ cells.below Y then x 3 else ⊤ with hbdef
    set a : Label.{u} := if (2 : Fin 9) ∈ cells.below Y then x 2 else b with hadef
    set F : Label.{u} := if (6 : Fin 9) ∈ cells.below Y then x 6 else ⊥ with hFdef
    have hb : IsSelfVisible 1 b := by
      rw [hbdef]; split_ifs with h3
      · exact ho 3 h3
      · exact isSelfVisible_top 1
    have ha' : IsSelfVisible 1 a := by
      rw [hadef]; split_ifs with h2
      · exact ho 2 h2
      · exact hb
    have hF : IsSelfVisible 2 F := by
      rw [hFdef]; split_ifs with h6
      · exact ho 6 h6
      · exact isSelfVisible_bot 2
    refine ⟨a, b, F, ha', hb, hF, ?_, ?_, fun d hd ↦ ?_⟩
    · rw [hFdef, hadef]
      by_cases h6 : (6 : Fin 9) ∈ cells.below Y
      · rw [ite_eq_left h6]
        by_cases h2 : (2 : Fin 9) ∈ cells.below Y
        · rw [ite_eq_left h2]; exact l62 (eight_mem h2 h6)
        · rw [ite_eq_right h2, hbdef, ite_eq_left (m3of6 h6)]; exact l63 h6
      · rw [ite_eq_right h6]; exact bot_le
    · rw [hadef]
      by_cases h2 : (2 : Fin 9) ∈ cells.below Y
      · rw [ite_eq_left h2, hbdef]
        by_cases h3 : (3 : Fin 9) ∈ cells.below Y
        · rw [ite_eq_left h3]; exact l23 (five_mem h2 h3)
        · rw [ite_eq_right h3]; exact le_top
      · rw [ite_eq_right h2]
    · obtain ⟨rA, rB, rF⟩ := rep_le d
      rcases cls_cases d with h | h | h | h
      · rw [lab_dead h, hdead d hd h]
      · have h2 := mem_below_of_le hd (rA h)
        rw [lab_A h, hadef, ite_eq_left h2]
        have key : ∀ d : Fin 9, cls d = 1 → d = 2 ∨ d = 4 := by decide
        rcases key d h with rfl | rfl
        · rfl
        · exact e42 hd
      · have h3 := mem_below_of_le hd (rB h)
        rw [lab_B h, hbdef, ite_eq_left h3]
        have key : ∀ d : Fin 9, cls d = 2 → d = 3 ∨ d = 5 := by decide
        rcases key d h with rfl | rfl
        · rfl
        · exact e53 hd
      · have h6 := mem_below_of_le hd (rF h)
        rw [lab_F h, hFdef, ite_eq_left h6]
        have key : ∀ d : Fin 9, cls d = 3 → d = 6 ∨ d = 8 := by decide
        rcases key d h with rfl | rfl
        · rfl
        · exact e86 hd
  · rintro ⟨a, b, F, ha, hb, hF, hFa, hab, hx⟩
    have := (isLawful_lab ha hb hF hFa hab).isLawfulBelow Y
    convert this using 1
    funext d
    exact hx d d.2

/-! ### Bountifulness: every pair lifts capped to every larger pair -/

/-- **Every pair lifts capped to every larger pair of positive grade.**  For a prescription
`lab ap bp Fp` below `X` and an ambient `lab aq bq Fq` below `Y`, the lift is `lab a' b' F'`: each
class with a cell below `X` keeps the prescription; otherwise `b'` is `bq` below the cap and `⊤`
above it, `F'` is `Fq` capped (or `⊥` below the grade `2`), and `a'` is the larger of `F'` and
`aq` capped. -/
theorem cappedLift_all {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y) (hY : 1 ≤ Y.2) :
    rows.CappedLift.{u} h := by
  classical
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨ap, bp, Fp, hap, hbp, hFp, hFap, habp, hpx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨aq, bq, Fq, haq, hbq, hFq, hFaq, habq, hqx⟩ :=
    isLawfulBelow_iff.mp (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpd (d : cells.below X) : p d = lab ap bp Fp d := by
    rw [← hpx d d.2, Rows.extendBot_of_mem p d.2]
  have hqd (d : cells.below Y) : q d = lab aq bq Fq d := by
    rw [← hqx d d.2, Rows.extendBot_of_mem q d.2]
  have hcap {e : Fin 9} (he : e ∈ cells.below X) :
      min (lab aq bq Fq e) c = min (lab ap bp Fp e) c := by
    have := hpq ⟨e, he⟩
    rwa [hqd, hpd] at this
  have c2 (h2 : (2 : Fin 9) ∈ cells.below X) : min aq c = min ap c := by
    have := hcap h2; rwa [lab_A (by decide), lab_A (by decide)] at this
  have c3 (h3 : (3 : Fin 9) ∈ cells.below X) : min bq c = min bp c := by
    have := hcap h3; rwa [lab_B (by decide), lab_B (by decide)] at this
  have c6 (h6 : (6 : Fin 9) ∈ cells.below X) : min Fq c = min Fp c := by
    have := hcap h6; rwa [lab_F (by decide), lab_F (by decide)] at this
  have m3of6 (h6 : (6 : Fin 9) ∈ cells.below X) : (3 : Fin 9) ∈ cells.below X :=
    mem_below_of_le h6 (by decide)
  have hc1 : IsSelfVisible 1 c := hc.mono hY
  set b' : Label.{u} :=
    if (3 : Fin 9) ∈ cells.below X then bp else (if bq < c then bq else ⊤) with hb'
  set F' : Label.{u} :=
    if (6 : Fin 9) ∈ cells.below X then Fp else (if 2 ≤ Y.2 then min Fq c else ⊥) with hF'
  set a' : Label.{u} :=
    if (2 : Fin 9) ∈ cells.below X then ap else max F' (min aq c) with ha'
  have hSb : IsSelfVisible 1 b' := by
    rw [hb']; split_ifs
    exacts [hbp, hbq, isSelfVisible_top 1]
  have hSF : IsSelfVisible 2 F' := by
    rw [hF']; split_ifs with _ hY2
    exacts [hFp, hFq.min (hc.mono hY2), isSelfVisible_bot 2]
  have hSa : IsSelfVisible 1 a' := by
    rw [ha']; split_ifs
    exacts [hap, (hSF.mono (by omega)).max (haq.min hc1)]
  -- the new `F` capped is at most `Fq` capped, and below `X` it is at most `Fq` capped
  have hF'c : min F' c ≤ min Fq c := by
    rw [hF']; split_ifs with h6 hY2
    · exact (c6 h6).ge
    · exact min_le_left _ _
    · simp
  have hF'n (h6 : (6 : Fin 9) ∉ cells.below X) : F' ≤ min Fq c := by
    rw [hF', ite_eq_right h6]; split_ifs
    exacts [le_rfl, bot_le]
  have hFa' : F' ≤ a' := by
    rw [ha']
    by_cases h2 : (2 : Fin 9) ∈ cells.below X
    · rw [ite_eq_left h2]
      by_cases h6 : (6 : Fin 9) ∈ cells.below X
      · rw [hF', ite_eq_left h6]; exact hFap
      · exact (hF'n h6).trans ((min_le_min_right c hFaq).trans ((c2 h2).le.trans
          (min_le_left _ _)))
    · rw [ite_eq_right h2]; exact le_max_left _ _
  have hab' : a' ≤ b' := by
    rw [ha', hb']
    by_cases h2 : (2 : Fin 9) ∈ cells.below X <;> by_cases h3 : (3 : Fin 9) ∈ cells.below X
    · rw [ite_eq_left h2, ite_eq_left h3]; exact habp
    · rw [ite_eq_left h2, ite_eq_right h3]
      split_ifs with hlt
      · have hlt' : aq < c := habq.trans_lt hlt
        rw [eq_of_min_eq_of_lt (c2 h2) hlt']
        exact habq
      · exact le_top
    · rw [ite_eq_right h2, ite_eq_left h3]
      refine max_le ?_ ((min_le_min_right c habq).trans ((c3 h3).le.trans (min_le_left _ _)))
      by_cases h6 : (6 : Fin 9) ∈ cells.below X
      · rw [hF', ite_eq_left h6]; exact hFap.trans habp
      · exact (hF'n h6).trans ((min_le_min_right c (hFaq.trans habq)).trans ((c3 h3).le.trans
          (min_le_left _ _)))
    · have h6 : (6 : Fin 9) ∉ cells.below X := fun h6 ↦ h3 (m3of6 h6)
      rw [ite_eq_right h2, ite_eq_right h3]
      have hup : min bq c ≤ if bq < c then bq else ⊤ := by
        split_ifs
        exacts [min_le_left _ _, le_top]
      exact max_le ((hF'n h6).trans ((min_le_min_right c (hFaq.trans habq)).trans hup))
        ((min_le_min_right c habq).trans hup)
  refine ⟨fun d ↦ lab a' b' F' d,
    isLawfulBelow_iff.mpr ⟨a', b', F', hSa, hSb, hSF, hFa', hab', fun _ _ ↦ rfl⟩,
    fun d ↦ ?_, fun d ↦ ?_⟩
  · -- the capped agreement with the ambient
    rw [hqd]
    change min (lab a' b' F' d.1) c = min (lab aq bq Fq d.1) c
    rcases cls_cases d.1 with e | e | e | e
    · rw [lab_dead e, lab_dead e]
    · rw [lab_A e, lab_A e, ha']
      split_ifs with h2
      · exact (c2 h2).symm
      · rw [min_max_distrib_right, min_assoc, min_self]
        exact max_eq_right (hF'c.trans (min_le_min_right c hFaq))
    · rw [lab_B e, lab_B e, hb']
      split_ifs with h3 hlt
      · exact (c3 h3).symm
      · rfl
      · rw [min_top_left, min_eq_right (not_lt.mp hlt)]
    · rw [lab_F e, lab_F e, hF']
      have hY2 : 2 ≤ Y.2 := (grade_of_cls.2 e) ▸ d.2.2
      split_ifs with h6
      · exact (c6 h6).symm
      · rw [min_assoc, min_self]
  · -- the restriction to the prescription
    rw [hpd]
    change lab a' b' F' d.1 = lab ap bp Fp d.1
    obtain ⟨rA, rB, rF⟩ := rep_le d.1
    rcases cls_cases d.1 with e | e | e | e
    · rw [lab_dead e, lab_dead e]
    · rw [lab_A e, lab_A e, ha', ite_eq_left (mem_below_of_le d.2 (rA e))]
    · rw [lab_B e, lab_B e, hb', ite_eq_left (mem_below_of_le d.2 (rB e))]
    · rw [lab_F e, lab_F e, hF', ite_eq_left (mem_below_of_le d.2 (rF e))]

/-- The rows of `S` are bountiful. -/
theorem isBountiful_rows : rows.{u}.IsBountiful := fun _ _ _ hY h ↦ cappedLift_all h hY.2.1

/-! ### Legality -/

/-- The rows of `S` are consistent: every row is a labelling `lab a b F`. -/
theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  change rows.IsLawfulBelow (cells.gradedIndex s) (fun d ↦ rowValue s d)
  have hl2 : IsSelfVisible 2 low.{u} := isSelfVisible_low 2 le_rfl
  have hl1 : IsSelfVisible 1 low.{u} := isSelfVisible_low 1 (by omega)
  by_cases h5 : s = 5
  · subst h5
    refine isLawfulBelow_iff.mpr ⟨1, omegaAddTwo, ⊥, isSelfVisible_one.mpr le_rfl,
      isSelfVisible_omegaAddTwo, isSelfVisible_bot 2, bot_le, one_lt_omegaAddTwo.le,
      fun d hd ↦ ?_⟩
    have hd3 : cls d ≠ 3 := by
      have := grade_le_five d hd
      intro h3; have := grade_of_cls.2 h3; omega
    rw [rowValue, ite_eq_left rfl]
    rcases cls_cases d with e | e | e | e
    · rw [lab_dead e]; simp [val5, e]
    · rw [lab_A e]; simp [val5, e]
    · rw [lab_B e]; simp [val5, e]
    · exact absurd e hd3
  by_cases hs : cls s = 0
  · refine isLawfulBelow_iff.mpr ⟨⊥, ⊥, ⊥, isSelfVisible_bot 1, isSelfVisible_bot 1,
      isSelfVisible_bot 2, le_rfl, le_rfl, fun d _ ↦ ?_⟩
    rcases cls_cases d with e | e | e | e <;>
      simp [rowValue, h5, hs, lab_dead, lab_A, lab_B, lab_F, e]
  · refine isLawfulBelow_iff.mpr ⟨low, low, low, hl1, hl1, hl2, le_rfl, le_rfl, fun d _ ↦ ?_⟩
    rcases cls_cases d with e | e | e | e <;>
      simp [rowValue, h5, hs, lab_dead, lab_A, lab_B, lab_F, e]

/-- `S` is well formed. -/
theorem isWellFormed_S : S.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

/-- `S` is coded: its row values are `⊥`, `1`, `2`, and `ω + 2`. -/
theorem isCoded_S : S.{u}.IsCoded := by
  intro s t
  have key : rowValue.{u} s t.1 = ⊥ ∨ rowValue.{u} s t.1 = 1 ∨ rowValue.{u} s t.1 = low ∨
      rowValue.{u} s t.1 = omegaAddTwo := by
    unfold rowValue val5
    split_ifs <;> simp
  change rowValue s t.1 < _
  rcases key with h | h | h | h <;> rw [h]
  · exact WithBot.bot_lt_coe _
  · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 1, by simp⟩)
  · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 2, by simp [low]⟩)
  · exact lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [omegaAddTwo]⟩)

private theorem complete_below : ∀ B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)), ∀ k < 3,
    0 < k → k ≤ #B → ∃ d : Fin 9, cellScope d = B ∧ cellGrade d = k := by
  decide +kernel

/-- **`S` is legal below the full grade.** -/
theorem isLegalBelow_S : S.{u}.IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isConsistent := isConsistent_rows
  isBountiful := isBountiful_rows
  grade_lt d := (by decide : ∀ d : Fin 9, cellGrade d < 3) d
  exists_gradedIndex_eq X hX hX3 := by
    obtain ⟨d, hd1, hd2⟩ := complete_below X.1 hX.1 X.2 hX3 hX.2.1 hX.2.2
    exact ⟨d, Prod.ext hd1 hd2⟩

/-- **The scheme on three points**: `S` with a dead cell of graded index `(univ, 3)` appended
(its row is `⊥`). -/
noncomputable abbrev Sq : Scheme.{u} 3 :=
  S.{u}.appendFullCell 3 (fun _ ↦ ⊥) isLegalBelow_S.{u}.not_le

/-- **The scheme on three points is legal.** -/
theorem isLegal_Sq : Sq.{u}.IsLegal where
  isWellFormed := Scheme.isWellFormed_appendFullCell isWellFormed_S.{u} (by omega) le_rfl
  isCoded := Scheme.isCoded_appendFullCell isCoded_S.{u} fun _ ↦ WithBot.bot_lt_coe _
  isConsistent :=
    Scheme.isConsistent_appendFullCell isConsistent_rows.{u} Rows.isLawful_const_bot
  isBountiful := Scheme.isBountiful_appendFullCell isBountiful_rows.{u}
  isComplete := Scheme.isComplete_appendFullCell isLegalBelow_S.{u}.exists_gradedIndex_eq

/-- **The squeeze type**: the scheme `Sq` with every label `⊥`. -/
noncomputable abbrev T (α : Ordinal.{u}) : StageType.{u} α 3 where
  toScheme := Sq
  label _ := ⊥
  isWellFormed := isLegal_Sq.isWellFormed
  isCoded := isLegal_Sq.isCoded
  isLawful := Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- **The squeeze type is legal.** -/
theorem isLegal_T (α : Ordinal.{u}) : (T α).IsLegal := isLegal_Sq

end VaughtConjecture.SqueezeType
