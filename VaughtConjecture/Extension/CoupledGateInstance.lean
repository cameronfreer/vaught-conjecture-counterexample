/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.CoupledGateExamples

/-!
# A coupled gated extension of `P α` with the donor labelled `⊤`

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate) and 3.4, row
(R1); the coupled gated extensions of `VaughtConjecture.Extension.GatedExtension`.

**The theorem** (`coupledGatedPinnedExtension_donor`).  The coupled gated pinned extension property
(`StageType.HasCoupledGatedPinnedExtensions`) holds at this instance:
* the private type `GatedExtensionCounterexample.P α` on two points;
* the empty root;
* the donor labelled `⊤` (`donor α`): one point, one cell of grade `1`, labelled `⊤`
  (`card_donor`, `label_donor`);
* either cell of `P α` of graded index `(univ, 2)` as the cap.

Every hypothesis of the property holds there, and a coupled gated extension whose cap carries the
label of the chosen cell exists (`exists_coupledGatedExtension_donor`).  The property holds at this
instance only.  Nothing is proved here about the property in general, which is open, or about
(R1).  The input at which the gated pinned extension property is refuted has the same private type
and root and a donor whose cell is labelled `⊥`
(`CoupledGateExamples.exists_coupledGatedExtension`).

**Cap lowering at this instance.**  The gate reads the donor cell at least as it reads the cap.
So in every lawful labelling of the display the donor cell bounds both full private cells
(`le_label_five`).  A lift from a face containing the new point that prescribes a value `v` below
`⊤` at the donor cell therefore lowers the cap, which the display labels `⊤`, to at most `v`.
For a cap `c ≤ v` self-visible at `2`, the labelling that is `c` at the full cells and their copies
and `v` at the donor cell and its copies is lawful and lies in the cap ball of the display at `c`
(`isLawful_capLowered`).  Cap lowering holds for every legal private type
(`StageType.IsLegal.capLowering`, in `VaughtConjecture.Extension.CapLowering`).

**The display `Q α`** (`Q`, `isLegal_Q`).  On three points with the interval plan, twelve cells.
A cell is **dead** when its kind is `0`, **live** otherwise; the cells of kind `3` are the
**donor class**.

| cell          | scope       | grade | kind |
|---------------|-------------|-------|------|
| 0, 1          | {0}, {1}    | 1     | 0    |
| 2             | {0, 1}      | 1     | 0    |
| 3 (`C₁`)      | {0, 1}      | 2     | 1    |
| 4 (`C₂`)      | {0, 1}      | 2     | 2    |
| 5 (the donor) | {2}         | 1     | 3    |
| 6             | {1, 2}      | 1     | 3    |
| 7             | {1, 2}      | 2     | 0    |
| 8             | univ        | 1     | 3    |
| 9             | univ        | 2     | 1    |
| 10            | univ        | 2     | 2    |
| 11            | univ        | 3     | 0    |

* **Rows.**  `⊥` at or from a dead cell, `2` between the kinds `1` and `2`, and `3` otherwise.
  On the private cells these are the rows of `P α` (`restrictFace_Q`).  The cells of kinds `1`
  and `2` read the donor class at `3`, as they read their own kind.
* **Labels.**  The display labels the live cells `⊤` and the dead ones `⊥`.  Its donor face `{2}`
  is the cell `5`, labelled `⊤`.
* **Lawful labellings.**  They are the labellings `lab a b x`: `a` at kind `1`, `b` at kind `2`,
  `x` at the donor class.  Here the pair `(a, b)` is lawful on `P α`, `x` is self-visible at `1`,
  and `a, b ≤ x`.  The cells `9` and `10` copy `C₁` and `C₂` (`eq_of_isLawfulBelow_univ_two`), as in
  `CoupledGateExamples.Q`.  The bound `a, b ≤ x` comes from the localities at `9` and `10`, which
  read the donor class as their own cell.

**Legality.**  By bountifulness at a fixed grade (`Rows.isBountiful_iff_forall_cappedLift_fst`),
there are five cases.
1. Lifts within a face.
2. Lifts from pairs below which every cell is dead: keep the ambient labelling.
3. The lift from `({0, 1}, 2)` to `(univ, 2)`.  Keep the prescribed full private cells and copy
   them to `9` and `10`.  Keep the ambient donor class when it is below the cap, and raise it to
   `⊤` otherwise.
4. The lift from `({1, 2}, 2)` to `(univ, 2)`.  Keep the prescribed donor class.  If it differs
   from the ambient one, it is at least the cap, and the full cells and their copies take the
   ambient labels capped at the cap (`CellScheme.Rows.IsLawful.min_const`).  This is where the
   cap is lowered.
5. The lifts at grade `1` from a face containing the new point, below which only the donor class
   is live: keep the prescribed donor class.

**The coupled gated extensions.**  The cap is `C₁` with gate `9` and twin `10`, or `C₂` with gate
`10` and twin `9`.  The twin reads the cap and the gate both at `2`, so the coupling
`CellScheme.Rows.TwinsReadGate` holds with equality.  The gate reads the donor cell at `3`, as it
reads the cap, which gives the reading `top` with the cap itself as the private cell.  The twin is
labelled `⊤`, as in every legal one-point extension of `P α`
(`GatedExtensionCounterexample.exists_twin_label_ne_bot`).

**What is not shown.**  Other donors of `P α`, such as donors with several cells; other private
types; nonempty roots.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.CoupledGateInstance

open Finset Label CellScheme

/-! ### The scheme -/

/-- The scopes of the twelve cells. -/
def cellScope : Fin 12 → Finset (Fin 3) :=
  ![{0}, {1}, {0, 1}, {0, 1}, {0, 1}, {2}, {1, 2}, {1, 2}, univ, univ, univ, univ]

/-- The grades of the twelve cells. -/
def cellGrade : Fin 12 → ℕ := ![1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3]

/-- `0`: dead; `1`: the full private cell `C₁` and its copy `9`; `2`: `C₂` and its copy `10`;
`3`: the donor cell `5` and its copies `6` and `8`. -/
def kind : Fin 12 → ℕ := ![0, 0, 0, 1, 2, 3, 3, 0, 3, 1, 2, 0]

/-- The cells, on the interval plan of the three points. -/
def cells : CellScheme (Fin 12) (Fin 3) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

private noncomputable def rowValue (s t : Fin 12) : Label.{u} :=
  if kind s = 0 ∨ kind t = 0 then ⊥
  else if kind s ≠ kind t ∧ kind s ≠ 3 ∧ kind t ≠ 3 then ((2 : ℕ) : Label.{u})
  else ((3 : ℕ) : Label.{u})

/-- The rows: `⊥` at or from a dead cell, `2` between the kinds `1` and `2`, `3` otherwise. -/
noncomputable def rows : cells.Rows.{u} := ⟨fun s t ↦ rowValue s t.1⟩

/-- The scheme of the display. -/
noncomputable def S : Scheme.{u} 3 := ⟨12, cells, rows⟩

/-- `a` at the kind-`1` cells, `b` at the kind-`2` cells, `x` at the kind-`3` cells, `⊥`
elsewhere. -/
noncomputable def lab (a b x : Label.{u}) (d : Fin 12) : Label.{u} :=
  if kind d = 1 then a else if kind d = 2 then b else if kind d = 3 then x else ⊥

/-! ### Finite facts -/

private theorem kind_cases (d : Fin 12) :
    kind d = 0 ∨ kind d = 1 ∨ kind d = 2 ∨ kind d = 3 := by
  revert d; decide +kernel

private theorem grade_of_kind_one_two :
    ∀ d : Fin 12, kind d = 1 ∨ kind d = 2 → cellGrade d = 2 := by
  decide +kernel

private theorem grade_of_kind_three : ∀ d : Fin 12, kind d = 3 → cellGrade d = 1 := by
  decide +kernel

private theorem kind_of_grade_le_one : ∀ d : Fin 12, cellGrade d ≤ 1 → kind d = 0 ∨ kind d = 3 := by
  decide +kernel

private theorem exists_partner : ∀ s t : Fin 12, cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → ∃ u, cellScope u = cellScope t ∧ cellGrade u = cellGrade t ∧
      (kind s = 0 ∨ kind u = kind s) := by
  decide +kernel

private theorem eq_of_gradedIndex_nine : ∀ u : Fin 12,
    (cellScope u, cellGrade u) = (cellScope 9, cellGrade 9) → u = 9 ∨ u = 10 := by
  decide +kernel

private theorem eq_of_gradedIndex_six : ∀ u : Fin 12,
    (cellScope u, cellGrade u) = (cellScope 6, cellGrade 6) → u = 6 := by
  decide +kernel

private theorem eq_of_gradedIndex_eight : ∀ u : Fin 12,
    (cellScope u, cellGrade u) = (cellScope 8, cellGrade 8) → u = 8 := by
  decide +kernel

private theorem eq_three_of_below : ∀ d : Fin 12, cellScope d ⊆ {0, 1} → kind d = 1 → d = 3 := by
  decide +kernel

private theorem eq_four_of_below : ∀ d : Fin 12, cellScope d ⊆ {0, 1} → kind d = 2 → d = 4 := by
  decide +kernel

private theorem eq_of_kind_one : ∀ d : Fin 12, kind d = 1 → d = 3 ∨ d = 9 := by decide +kernel

private theorem eq_of_kind_two : ∀ d : Fin 12, kind d = 2 → d = 4 ∨ d = 10 := by decide +kernel

private theorem eq_of_kind_three : ∀ d : Fin 12, kind d = 3 → d = 5 ∨ d = 6 ∨ d = 8 := by
  decide +kernel

private theorem eq_five_of_scope : ∀ d : Fin 12, cellScope d ⊆ {2} → d = 5 := by decide +kernel

/-- Every cell below `(A, k)` is dead. -/
private def AllDead (A : Finset (Fin 3)) (k : ℕ) : Prop :=
  ∀ d, cellScope d ⊆ A → cellGrade d ≤ k → kind d = 0

private instance (A : Finset (Fin 3)) (k : ℕ) : Decidable (AllDead A k) := by
  unfold AllDead; infer_instance

-- `decide +kernel` below needs a `Decidable` instance for nested quantifiers over finsets,
-- larger than the default bound of instance synthesis.
set_option synthInstance.maxSize 512 in
/-- Below a graded face of the plan, the lifts to a larger face at the same grade: within the
face, from a pair below which every cell is dead, from `({0, 1}, 2)` or `({1, 2}, 2)` to
`(univ, 2)`, or at grade `1` from a face containing the new point. -/
private theorem case_split : ∀ A B : Finset (Fin 3),
    A ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) →
    B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) → A ⊆ B → ∀ k : Fin 4, 0 < (k : ℕ) →
      (k : ℕ) ≤ #A → A = B ∨ AllDead A k ∨ (A = {0, 1} ∧ (k : ℕ) = 2 ∧ B = univ) ∨
        (A = {1, 2} ∧ (k : ℕ) = 2 ∧ B = univ) ∨ ((k : ℕ) = 1 ∧ 2 ∈ A) := by
  decide +kernel

private theorem exists_cell : ∀ B : Finset (Fin 3),
    B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) → ∀ k : Fin 4, 0 < (k : ℕ) → (k : ℕ) ≤ #B →
      ∃ d : Fin 12, cellScope d = B ∧ cellGrade d = k := by
  decide +kernel

/-! ### Labels and row values -/

variable {a b x : Label.{u}} {d s t : Fin 12}

private theorem lab_zero (h : kind d = 0) : lab a b x d = ⊥ := by simp [lab, h]

private theorem lab_one (h : kind d = 1) : lab a b x d = a := by simp [lab, h]

private theorem lab_two (h : kind d = 2) : lab a b x d = b := by simp [lab, h]

private theorem lab_three (h : kind d = 3) : lab a b x d = x := by simp [lab, h]

private theorem rowValue_zero_left (h : kind s = 0) : rowValue.{u} s t = ⊥ := by simp [rowValue, h]

private theorem rowValue_zero_right (h : kind t = 0) : rowValue.{u} s t = ⊥ := by simp [rowValue, h]

private theorem rowValue_two (hs : kind s ≠ 0) (ht : kind t ≠ 0)
    (h : kind s ≠ kind t ∧ kind s ≠ 3 ∧ kind t ≠ 3) :
    rowValue.{u} s t = ((2 : ℕ) : Label.{u}) := by
  unfold rowValue; split_ifs <;> simp_all

private theorem rowValue_three (hs : kind s ≠ 0) (ht : kind t ≠ 0)
    (h : ¬ (kind s ≠ kind t ∧ kind s ≠ 3 ∧ kind t ≠ 3)) :
    rowValue.{u} s t = ((3 : ℕ) : Label.{u}) := by
  unfold rowValue; split_ifs <;> simp_all

private theorem two_lt_three : ((2 : ℕ) : Label.{u}) < ((3 : ℕ) : Label.{u}) := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_lt_coe, ← WithTop.coe_natCast,
    ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  exact Nat.cast_lt.mpr (by decide)

private theorem sv_two : IsSelfVisible 2 ((2 : ℕ) : Label.{u}) := by simp

private theorem sv_three : IsSelfVisible 2 ((3 : ℕ) : Label.{u}) := by simp

private theorem sv_three_one : IsSelfVisible 1 ((3 : ℕ) : Label.{u}) := by simp

private theorem topShifter_natCast (n : ℕ) : topShifter ((n : ℕ) : Label.{u}) = ⊤ := by
  simp [topShifter]

/-! ### Lawful labellings `lab a b x` -/

/-- The two readings that make `lab a b x` local at the full cells on the private points. -/
private def Reads (a b : Label.{u}) : Prop :=
  (∃ g σ, IsWitness g σ ∧ a = min (σ ((3 : ℕ) : Label.{u})) (g 2) ∧
      min b a = min (σ ((2 : ℕ) : Label.{u})) (g 2)) ∧
  (∃ g σ, IsWitness g σ ∧ min a b = min (σ ((2 : ℕ) : Label.{u})) (g 2) ∧
      b = min (σ ((3 : ℕ) : Label.{u})) (g 2))

/-- The data of a lawful labelling `lab a b x`: self-visibility, the two readings, and the
domination of the two full private cells by the donor class. -/
private def LawfulTriple (a b x : Label.{u}) : Prop :=
  IsSelfVisible 2 a ∧ IsSelfVisible 2 b ∧ IsSelfVisible 1 x ∧ Reads a b ∧ a ≤ x ∧ b ≤ x

private theorem topWitness {K : ℕ} {a : Label.{u}} (ha : IsSelfVisible K a) :
    IsWitness (constStepSuppressor K a) topShifter :=
  isWitness_topShifter (antitone_constStepSuppressor _ _) (isSelfVisible_constStepSuppressor ha)

private theorem reads_self (ha : IsSelfVisible 2 a) : Reads a a :=
  ⟨⟨_, _, topWitness ha, by rw [topShifter_natCast]; simp [constStepSuppressor],
      by rw [topShifter_natCast]; simp [constStepSuppressor]⟩,
    ⟨_, _, topWitness ha, by rw [topShifter_natCast]; simp [constStepSuppressor],
      by rw [topShifter_natCast]; simp [constStepSuppressor]⟩⟩

private theorem reads_three_two : Reads ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) :=
  ⟨⟨_, id, IsWitness.id_top, (min_top_right _).symm, by
      rw [min_eq_left two_lt_three.le]; exact (min_top_right _).symm⟩,
    ⟨_, _, topWitness sv_two, by
      rw [min_eq_right two_lt_three.le, topShifter_natCast]; simp [constStepSuppressor],
      by rw [topShifter_natCast]; simp [constStepSuppressor]⟩⟩

private theorem reads_two_three : Reads ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) :=
  ⟨⟨_, _, topWitness sv_two, by rw [topShifter_natCast]; simp [constStepSuppressor], by
      rw [min_eq_right two_lt_three.le, topShifter_natCast]; simp [constStepSuppressor]⟩,
    ⟨_, id, IsWitness.id_top, by
      rw [min_eq_left two_lt_three.le]; exact (min_top_right _).symm,
      (min_top_right _).symm⟩⟩

/-- Locality at a cell of kind `1` or `2` from a reading `(g, σ)` of the cell's own label `a`:
the suppressor capped at `a` (`IsWitness.cap`) reads the donor class at `a`. -/
private theorem locality_full {a b' x : Label.{u}} {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) (ha2 : IsSelfVisible 2 a) (ha : a = min (σ ((3 : ℕ) : Label.{u})) (g 2))
    (hb : min b' a = min (σ ((2 : ℕ) : Label.{u})) (g 2)) (hax : a ≤ x)
    (s : Fin 12) (own other : ℕ) (hs : kind s = own) (hown : own = 1 ∨ own = 2)
    (hother : other = 3 - own) (f : Fin 12 → Label.{u})
    (hfo : ∀ d, kind d = own → f d = a) (hft : ∀ d, kind d = other → f d = b')
    (hf3 : ∀ d, kind d = 3 → f d = x) (hf0 : ∀ d, kind d = 0 → f d = ⊥) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.row s)
      (fun d ↦ min (f d) (f s)) := by
  have hfs : f s = a := hfo s hs
  have hag : a ≤ g 2 := ha ▸ min_le_right _ _
  have has : a ≤ σ ((3 : ℕ) : Label.{u}) := ha ▸ min_le_left _ _
  refine ⟨_, σ, hw.cap ha2, fun d ↦ ?_⟩
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (f d.1) (f s) = min (σ (rowValue s d.1))
    (if cellGrade d.1 ≤ 2 then min (g (cellGrade d.1)) a else ⊥)
  rw [hfs]
  rcases kind_cases d.1 with h0 | h1 | h2 | h3
  · rw [hf0 _ h0, rowValue_zero_right h0, hw.map_bot, min_eq_left bot_le, min_eq_left bot_le]
  · have hg := grade_of_kind_one_two d.1 (.inl h1)
    rw [hg, ite_eq_left (le_refl 2)]
    rcases hown with rfl | rfl
    · rw [hfo _ (h1.trans rfl), rowValue_three (by omega) (by omega) (by omega), min_self,
        ← min_assoc, ← ha, min_self]
    · rw [hft _ (by omega), rowValue_two (by omega) (by omega) (by omega), ← min_assoc, ← hb,
        min_assoc, min_self]
  · have hg := grade_of_kind_one_two d.1 (.inr h2)
    rw [hg, ite_eq_left (le_refl 2)]
    rcases hown with rfl | rfl
    · rw [hft _ (by omega), rowValue_two (by omega) (by omega) (by omega), ← min_assoc, ← hb,
        min_assoc, min_self]
    · rw [hfo _ (h2.trans rfl), rowValue_three (by omega) (by omega) (by omega), min_self,
        ← min_assoc, ← ha, min_self]
  · have hg := grade_of_kind_three d.1 h3
    rw [hg, ite_eq_left (by omega : 1 ≤ 2), hf3 _ h3, min_eq_right hax,
      rowValue_three (by omega) (by omega) (by omega)]
    have hg1 : a ≤ g 1 := hag.trans (hw.antitone (by omega))
    rw [min_eq_right hg1, min_eq_right has]

/-- **`lab a b x` is lawful** given the data `LawfulTriple a b x`. -/
private theorem isLawful_lab (h : LawfulTriple a b x) : rows.{u}.IsLawful (lab a b x) := by
  obtain ⟨ha, hb, hx, ⟨⟨g, σ, hw, ea, eb⟩, ⟨g', σ', hw', ec, ed⟩⟩, hax, hbx⟩ := h
  refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · -- At a live cell the grade is `cellGrade` (by definition).
    change IsSelfVisible (cellGrade d) (lab a b x d)
    rcases kind_cases d with h0 | h1 | h2 | h3
    · rw [lab_zero h0]; exact isSelfVisible_bot _
    · rw [lab_one h1, grade_of_kind_one_two d (.inl h1)]; exact ha
    · rw [lab_two h2, grade_of_kind_one_two d (.inr h2)]; exact hb
    · rw [lab_three h3, grade_of_kind_three d h3]; exact hx
  · rcases kind_cases s with h0 | h1 | h2 | h3
    · simp only [lab_zero h0, min_bot_right]
      exact TransformsTo.bot _ _
    · exact locality_full hw ha ea eb hax s 1 2 h1 (.inl rfl) rfl _ (fun _ h ↦ lab_one h)
        (fun _ h ↦ lab_two h) (fun _ h ↦ lab_three h) (fun _ h ↦ lab_zero h)
    · exact locality_full hw' hb ed ec hbx s 2 1 h2 (.inr rfl) rfl _ (fun _ h ↦ lab_two h)
        (fun _ h ↦ lab_one h) (fun _ h ↦ lab_three h) (fun _ h ↦ lab_zero h)
    · refine ⟨_, _, topWitness hx, fun d ↦ ?_⟩
      -- The rows are `rowValue` and the grades `cellGrade` (by definition).
      change min (lab a b x d.1) (lab a b x s) = min (topShifter (rowValue s d.1))
        (constStepSuppressor 1 x (cellGrade d.1))
      have hd : cellGrade d.1 ≤ 1 := by
        have := d.2.2; change cellGrade d.1 ≤ cellGrade s at this
        rw [grade_of_kind_three s h3] at this; exact this
      rw [lab_three h3]
      rcases kind_of_grade_le_one d.1 hd with d0 | d3
      · rw [lab_zero d0, rowValue_zero_right d0]; simp [topShifter]
      · rw [lab_three d3, rowValue_three (by omega) (by omega) (by omega), topShifter_natCast,
          min_self]
        simp [constStepSuppressor, hd]
  · obtain ⟨u, hu1, hu2, hk⟩ := exists_partner s t hst hg
    refine ⟨u, Prod.ext hu1 hu2, ?_⟩
    rcases hk with h0 | hk
    · rw [lab_zero h0]; exact bot_le
    · unfold lab; rw [hk]

/-! ### Every lawful labelling is a `lab a b x` -/

/-- Dead cells are `⊥` in every labelling lawful below a pair above them. -/
private theorem eq_bot_of_dead {X : Finset (Fin 3) × ℕ} {w : Fin 12 → Label.{u}}
    (hw : rows.IsLawfulBelow X (fun d ↦ w d)) {d : Fin 12} (hd : d ∈ cells.below X)
    (h0 : kind d = 0) : w d = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have h := (hl d hd).eq_bot (d := ⟨d, cells.mem_below_gradedIndex d⟩)
    (rowValue_zero_left (t := d) h0)
  simpa using h

private theorem mem_below_of {s d : Fin 12} (h1 : cellScope d ⊆ cellScope s)
    (h2 : cellGrade d ≤ cellGrade s) : d ∈ cells.below (cells.gradedIndex s) := ⟨h1, h2⟩

/-- The localities at the two full private cells give the two readings. -/
private theorem reads_of_localities {w : Fin 12 → Label.{u}}
    (h3 : TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.row 3)
      (fun d ↦ min (w d) (w 3)))
    (h4 : TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.row 4)
      (fun d ↦ min (w d) (w 4))) : Reads (w 3) (w 4) := by
  obtain ⟨g, σ, hw, heq⟩ := h3
  obtain ⟨g', σ', hw', heq'⟩ := h4
  have e33 := heq ⟨3, mem_below_of (s := 3) subset_rfl le_rfl⟩
  have e34 := heq ⟨4, mem_below_of (s := 3) (by decide) le_rfl⟩
  have e43 := heq' ⟨3, mem_below_of (s := 4) (by decide) le_rfl⟩
  have e44 := heq' ⟨4, mem_below_of (s := 4) subset_rfl le_rfl⟩
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (w 3) (w 3) = min (σ (rowValue 3 3)) (g 2) at e33
  change min (w 4) (w 3) = min (σ (rowValue 3 4)) (g 2) at e34
  change min (w 3) (w 4) = min (σ' (rowValue 4 3)) (g' 2) at e43
  change min (w 4) (w 4) = min (σ' (rowValue 4 4)) (g' 2) at e44
  rw [rowValue_three (s := 3) (t := 3) (by decide) (by decide) (by decide), min_self] at e33
  rw [rowValue_three (s := 4) (t := 4) (by decide) (by decide) (by decide), min_self] at e44
  rw [rowValue_two (s := 3) (t := 4) (by decide) (by decide) (by decide)] at e34
  rw [rowValue_two (s := 4) (t := 3) (by decide) (by decide) (by decide)] at e43
  exact ⟨⟨g, σ, hw, e33, e34⟩, ⟨g', σ', hw', e43, e44⟩⟩

/-- In a linear order: from `x ≤ a`, `y ≤ b`, the two minimum equations, and the two
dominations, `x = a` and `y = b`. -/
private theorem eq_and_eq_of_min_eq {L : Type*} [LinearOrder L] {a b x y : L} (hxa : x ≤ a)
    (hyb : y ≤ b)
    (h1 : min b x = min y x) (h2 : min a y = min x y) (ha : a ≤ x ∨ a ≤ y)
    (hb : b ≤ x ∨ b ≤ y) : x = a ∧ y = b := by
  constructor
  · rcases ha with h | h
    · exact le_antisymm hxa h
    · by_contra hne
      have hlt : x < a := lt_of_le_of_ne hxa hne
      rw [min_eq_left h, min_eq_left (hlt.le.trans h)] at h2
      exact hne h2.symm
  · rcases hb with h | h
    · by_contra hne
      have hlt : y < b := lt_of_le_of_ne hyb hne
      rw [min_eq_left h, min_eq_left (hlt.le.trans h)] at h1
      exact hne h1.symm
    · exact le_antisymm hyb h

/-- **Below `(univ, 2)` the gate and the twin copy the two full private cells**: every labelling
lawful below `(univ, 2)` has `w 9 = w 3` and `w 10 = w 4`. -/
theorem eq_of_isLawfulBelow_univ_two {w : Fin 12 → Label.{u}}
    (hw : rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ w d)) :
    w 9 = w 3 ∧ w 10 = w 4 := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hb : ∀ d : Fin 12, cellGrade d ≤ 2 → d ∈ cells.below ((univ : Finset (Fin 3)), 2) :=
    fun d hd ↦ ⟨subset_univ _, hd⟩
  obtain ⟨g, σ, -, heq⟩ := hl 9 (hb 9 le_rfl)
  obtain ⟨g', σ', -, heq'⟩ := hl 10 (hb 10 le_rfl)
  have e93 := heq ⟨3, mem_below_of (s := 9) (by decide) le_rfl⟩
  have e94 := heq ⟨4, mem_below_of (s := 9) (by decide) le_rfl⟩
  have e99 := heq ⟨9, mem_below_of (s := 9) subset_rfl le_rfl⟩
  have e910 := heq ⟨10, mem_below_of (s := 9) subset_rfl le_rfl⟩
  have e103 := heq' ⟨3, mem_below_of (s := 10) (by decide) le_rfl⟩
  have e104 := heq' ⟨4, mem_below_of (s := 10) (by decide) le_rfl⟩
  have e109 := heq' ⟨9, mem_below_of (s := 10) subset_rfl le_rfl⟩
  have e1010 := heq' ⟨10, mem_below_of (s := 10) subset_rfl le_rfl⟩
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (w 3) (w 9) = min (σ (rowValue 9 3)) (g 2) at e93
  change min (w 4) (w 9) = min (σ (rowValue 9 4)) (g 2) at e94
  change min (w 9) (w 9) = min (σ (rowValue 9 9)) (g 2) at e99
  change min (w 10) (w 9) = min (σ (rowValue 9 10)) (g 2) at e910
  change min (w 3) (w 10) = min (σ' (rowValue 10 3)) (g' 2) at e103
  change min (w 4) (w 10) = min (σ' (rowValue 10 4)) (g' 2) at e104
  change min (w 9) (w 10) = min (σ' (rowValue 10 9)) (g' 2) at e109
  change min (w 10) (w 10) = min (σ' (rowValue 10 10)) (g' 2) at e1010
  rw [rowValue_three (s := 9) (t := 3) (by decide) (by decide) (by decide)] at e93
  rw [rowValue_three (s := 9) (t := 9) (by decide) (by decide) (by decide)] at e99
  rw [rowValue_three (s := 10) (t := 4) (by decide) (by decide) (by decide)] at e104
  rw [rowValue_three (s := 10) (t := 10) (by decide) (by decide) (by decide)] at e1010
  rw [rowValue_two (s := 9) (t := 4) (by decide) (by decide) (by decide)] at e94
  rw [rowValue_two (s := 9) (t := 10) (by decide) (by decide) (by decide)] at e910
  rw [rowValue_two (s := 10) (t := 3) (by decide) (by decide) (by decide)] at e103
  rw [rowValue_two (s := 10) (t := 9) (by decide) (by decide) (by decide)] at e109
  rw [min_self] at e99 e1010
  rw [← e99] at e93
  rw [← e910] at e94
  rw [← e1010] at e104
  rw [← e109] at e103
  have hxa : w 9 ≤ w 3 := calc
    w 9 = min (w 3) (w 9) := e93.symm
    _ ≤ w 3 := min_le_left _ _
  have hyb : w 10 ≤ w 4 := calc
    w 10 = min (w 4) (w 10) := e104.symm
    _ ≤ w 4 := min_le_left _ _
  have av : ∀ s : Fin 12, cellScope s ⊆ cellScope 9 → cellGrade s = cellGrade 9 →
      w s ≤ w 9 ∨ w s ≤ w 10 := by
    intro s hs hg
    obtain ⟨u, hu, hle⟩ := ha s 9 (hb 9 le_rfl) hs hg
    rcases eq_of_gradedIndex_nine u hu with rfl | rfl
    · exact .inl hle
    · exact .inr hle
  exact eq_and_eq_of_min_eq hxa hyb e94 e103 (av 3 (by decide) rfl) (av 4 (by decide) rfl)

/-- A live cell `s` above the donor cell `5`, of grade at least that of `5`, reads `5` and itself
at `3`; so its locality bounds it by `5`: `w s ≤ w 5`. -/
private theorem le_five_of_locality {w : Fin 12 → Label.{u}} {s : Fin 12}
    (hl : TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.row s)
      (fun d ↦ min (w d) (w s)))
    (h5 : (5 : Fin 12) ∈ cells.below (cells.gradedIndex s)) (hs : kind s ≠ 0)
    (hg : cellGrade 5 ≤ cellGrade s) : w s ≤ w 5 := by
  obtain ⟨g, σ, hw, heq⟩ := hl
  have e5 := heq ⟨5, h5⟩
  have es := heq ⟨s, cells.mem_below_gradedIndex s⟩
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (w 5) (w s) = min (σ (rowValue s 5)) (g (cellGrade 5)) at e5
  change min (w s) (w s) = min (σ (rowValue s s)) (g (cellGrade s)) at es
  rw [rowValue_three (s := s) (t := 5) hs (by decide) (by
    have : kind (5 : Fin 12) = 3 := rfl; omega)] at e5
  rw [rowValue_three (s := s) (t := s) hs hs (by omega), min_self] at es
  have : w s ≤ min (w 5) (w s) := by
    rw [e5, es]; exact min_le_min_left _ (hw.antitone hg)
  exact this.trans (min_le_left _ _)

/-- **The donor class is constant**: in a labelling lawful below `Y`, every kind-`3` cell below
`Y` carries the label of the donor cell `5`. -/
private theorem eq_five {Y : Finset (Fin 3) × ℕ} {w : Fin 12 → Label.{u}}
    (hw : rows.IsLawfulBelow Y (fun d ↦ w d)) {d : Fin 12} (hd : d ∈ cells.below Y)
    (h3 : kind d = 3) : w d = w 5 := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  rcases eq_of_kind_three d h3 with rfl | rfl | rfl
  · rfl
  · refine le_antisymm (le_five_of_locality (hl 6 hd) ⟨by decide, le_rfl⟩ (by decide)
      le_rfl) ?_
    obtain ⟨u, hu, hle⟩ := ha 5 6 hd (by decide) rfl
    obtain rfl := eq_of_gradedIndex_six u hu
    exact hle
  · refine le_antisymm (le_five_of_locality (hl 8 hd) ⟨by decide, le_rfl⟩ (by decide)
      le_rfl) ?_
    obtain ⟨u, hu, hle⟩ := ha 5 8 hd (by decide) rfl
    obtain rfl := eq_of_gradedIndex_eight u hu
    exact hle

/-- **The donor class dominates the full cells**: in a labelling lawful below `(univ, 2)`, the
gate and the twin, hence the two full private cells, are at most the donor cell `5`. -/
private theorem le_five_of_isLawfulBelow_univ_two {w : Fin 12 → Label.{u}}
    (hw : rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ w d)) :
    w 3 ≤ w 5 ∧ w 4 ≤ w 5 := by
  obtain ⟨h9, h10⟩ := eq_of_isLawfulBelow_univ_two hw
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have m : ∀ d : Fin 12, cellGrade d ≤ 2 → d ∈ cells.below ((univ : Finset (Fin 3)), 2) :=
    fun d hd ↦ ⟨subset_univ _, hd⟩
  exact ⟨h9 ▸ le_five_of_locality (hl 9 (m 9 le_rfl)) ⟨by decide, by decide⟩ (by decide)
      (by decide),
    h10 ▸ le_five_of_locality (hl 10 (m 10 le_rfl)) ⟨by decide, by decide⟩ (by decide)
      (by decide)⟩

/-- **Every labelling lawful below `(univ, 2)` is `lab (w 3) (w 4) (w 5)`** there, with the data
`LawfulTriple (w 3) (w 4) (w 5)`. -/
private theorem lawfulTriple_of_isLawfulBelow_univ_two {w : Fin 12 → Label.{u}}
    (hw : rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ w d)) :
    LawfulTriple (w 3) (w 4) (w 5) ∧
      ∀ d ∈ cells.below ((univ : Finset (Fin 3)), 2), w d = lab (w 3) (w 4) (w 5) d := by
  obtain ⟨h9, h10⟩ := eq_of_isLawfulBelow_univ_two hw
  obtain ⟨h35, h45⟩ := le_five_of_isLawfulBelow_univ_two hw
  obtain ⟨ho, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have m : ∀ d : Fin 12, cellGrade d ≤ 2 → d ∈ cells.below ((univ : Finset (Fin 3)), 2) :=
    fun d hd ↦ ⟨subset_univ _, hd⟩
  refine ⟨⟨ho 3 (m 3 le_rfl), ho 4 (m 4 le_rfl), ho 5 (m 5 (by decide)),
    reads_of_localities (hl 3 (m 3 le_rfl)) (hl 4 (m 4 le_rfl)), h35, h45⟩, fun d hd ↦ ?_⟩
  rcases kind_cases d with h0 | h1 | h2 | h3
  · rw [eq_bot_of_dead hw hd h0, lab_zero h0]
  · rw [lab_one h1]
    rcases eq_of_kind_one d h1 with rfl | rfl
    · rfl
    · exact h9
  · rw [lab_two h2]
    rcases eq_of_kind_two d h2 with rfl | rfl
    · rfl
    · exact h10
  · rw [lab_three h3]; exact eq_five hw hd h3

/-! ### Legality -/

private theorem left_eq_of_min_eq_of_lt {a c v : Label.{u}} (h : min a c = v) (hv : v < c) :
    a = v :=
  ((min_eq_iff.mp h).resolve_right fun h' ↦ hv.ne' h'.1).1

private theorem kind_of_scope_zero_one : ∀ d : Fin 12, cellScope d ⊆ {0, 1} → kind d ≠ 3 := by
  decide +kernel

private theorem kind_of_scope_one_two : ∀ d : Fin 12, cellScope d ⊆ {1, 2} →
    kind d = 0 ∨ kind d = 3 := by
  decide +kernel

private theorem grade_le_two_or_dead : ∀ d : Fin 12, cellGrade d ≤ 2 ∨ kind d = 0 := by
  decide +kernel

/-- If every cell below `X` is dead, the rows lift capped from `X`: keep the ambient labelling. -/
private theorem cappedLift_of_dead {X Y : Finset (Fin 3) × ℕ}
    (hX : ∀ d ∈ cells.below X, kind d = 0) (h : X ≤ Y) : rows.{u}.CappedLift h := by
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c _ p q hp hq _ ↦
    ⟨q, hq, fun _ ↦ rfl, fun d ↦ ?_⟩
  have hq' := Rows.isLawfulBelow_extendBot.mpr hq
  have hp' := Rows.isLawfulBelow_extendBot.mpr hp
  have hdY : d.1 ∈ cells.below Y := cells.below_mono h d.2
  have e1 := eq_bot_of_dead hq' hdY (hX d d.2)
  have e2 := eq_bot_of_dead hp' d.2 (hX d d.2)
  rw [Rows.extendBot_of_mem _ hdY] at e1
  rw [Rows.extendBot_of_mem _ d.2] at e2
  exact e1.trans e2.symm

/-- **The lift from the private coatom** `({0, 1}, 2)` to `(univ, 2)`: keep the prescribed full
private cells, copy them to the gate and the twin, and keep the donor class, raised to `⊤` when it
is at least the cap. -/
private theorem cappedLift_private
    (h : (({0, 1} : Finset (Fin 3)), 2) ≤ ((univ : Finset (Fin 3)), 2)) :
    rows.{u}.CappedLift h := by
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c _ p q hp hq hpq ↦ ?_
  have hP' := Rows.isLawfulBelow_extendBot.mpr hp
  have hQ' := Rows.isLawfulBelow_extendBot.mpr hq
  obtain ⟨w, hw⟩ : ∃ w, Rows.extendBot ((({0, 1} : Finset (Fin 3)), 2)) p = w := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, Rows.extendBot (((univ : Finset (Fin 3)), 2)) q = v := ⟨_, rfl⟩
  rw [hw] at hP'
  rw [hv] at hQ'
  have hwp : ∀ d (hd : d ∈ cells.below (({0, 1} : Finset (Fin 3)), 2)), w d = p ⟨d, hd⟩ :=
    fun d hd ↦ hw ▸ Rows.extendBot_of_mem p hd
  have hvq : ∀ d (hd : d ∈ cells.below ((univ : Finset (Fin 3)), 2)), v d = q ⟨d, hd⟩ :=
    fun d hd ↦ hv ▸ Rows.extendBot_of_mem q hd
  have m3 : (3 : Fin 12) ∈ cells.below (({0, 1} : Finset (Fin 3)), 2) := ⟨by decide, le_rfl⟩
  have m4 : (4 : Fin 12) ∈ cells.below (({0, 1} : Finset (Fin 3)), 2) := ⟨by decide, le_rfl⟩
  obtain ⟨hor, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hP'
  have hr : Reads (w 3) (w 4) := reads_of_localities (hl 3 m3) (hl 4 m4)
  obtain ⟨⟨-, -, hv5, -, hv35, hv45⟩, hvlab⟩ := lawfulTriple_of_isLawfulBelow_univ_two hQ'
  have hc3 : min (v 3) c = min (w 3) c := by
    rw [hvq 3 (cells.below_mono h m3), hwp 3 m3]; exact hpq ⟨3, m3⟩
  have hc4 : min (v 4) c = min (w 4) c := by
    rw [hvq 4 (cells.below_mono h m4), hwp 4 m4]; exact hpq ⟨4, m4⟩
  -- The donor class: kept below the cap, raised to `⊤` at or above it.
  set x' : Label.{u} := if v 5 < c then v 5 else ⊤ with hx'
  have hsx : IsSelfVisible 1 x' := by
    rw [hx']; split_ifs
    · exact hv5
    · exact isSelfVisible_top 1
  have hle : ∀ {i : Fin 12}, min (v i) c = min (w i) c → v i ≤ v 5 → w i ≤ x' := by
    intro i hci hi5
    rw [hx']; split_ifs with hlt
    · have hlt' : v i < c := lt_of_le_of_lt hi5 hlt
      have hwi : w i = v i := left_eq_of_min_eq_of_lt (by rw [← hci, min_eq_left hlt'.le]) hlt'
      exact hwi ▸ hi5
    · exact le_top
  have hgood : LawfulTriple (w 3) (w 4) x' :=
    ⟨hor 3 m3, hor 4 m4, hsx, hr, hle hc3 hv35, hle hc4 hv45⟩
  refine ⟨fun d ↦ lab (w 3) (w 4) x' d, (isLawful_lab hgood).isLawfulBelow _, fun d ↦ ?_,
    fun d ↦ ?_⟩
  -- The lift at `d` is `lab (w 3) (w 4) x'` at the underlying cell (by definition).
  · change min (lab (w 3) (w 4) x' d.1) c = min (q d) c
    rw [← hvq d.1 d.2, hvlab d.1 d.2]
    rcases kind_cases d.1 with h0 | h1 | h2 | h3
    · rw [lab_zero h0, lab_zero h0]
    · rw [lab_one h1, lab_one h1]; exact hc3.symm
    · rw [lab_two h2, lab_two h2]; exact hc4.symm
    · rw [lab_three h3, lab_three h3, hx']
      split_ifs with hlt
      · rfl
      · rw [min_top_left, min_eq_right (not_lt.mp hlt)]
  · change lab (w 3) (w 4) x' d.1 = p d
    rw [← hwp d.1 d.2]
    rcases kind_cases d.1 with h0 | h1 | h2 | h3
    · rw [eq_bot_of_dead hP' d.2 h0, lab_zero h0]
    · obtain h' := eq_three_of_below d.1 d.2.1 h1
      rw [lab_one h1, h']
    · obtain h' := eq_four_of_below d.1 d.2.1 h2
      rw [lab_two h2, h']
    · exact absurd h3 (kind_of_scope_zero_one d.1 d.2.1)

/-- **The lift from the donor coatom** `({1, 2}, 2)` to `(univ, 2)`: keep the prescribed donor
class; if it differs from the ambient one, it is at least the cap, and the full private cells,
the gate and the twin are lowered to the ambient labels capped at the cap. -/
private theorem cappedLift_donor
    (h : (({1, 2} : Finset (Fin 3)), 2) ≤ ((univ : Finset (Fin 3)), 2)) :
    rows.{u}.CappedLift h := by
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  have hP' := Rows.isLawfulBelow_extendBot.mpr hp
  have hQ' := Rows.isLawfulBelow_extendBot.mpr hq
  obtain ⟨w, hw⟩ : ∃ w, Rows.extendBot ((({1, 2} : Finset (Fin 3)), 2)) p = w := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, Rows.extendBot (((univ : Finset (Fin 3)), 2)) q = v := ⟨_, rfl⟩
  rw [hw] at hP'
  rw [hv] at hQ'
  have hwp : ∀ d (hd : d ∈ cells.below (({1, 2} : Finset (Fin 3)), 2)), w d = p ⟨d, hd⟩ :=
    fun d hd ↦ hw ▸ Rows.extendBot_of_mem p hd
  have hvq : ∀ d (hd : d ∈ cells.below ((univ : Finset (Fin 3)), 2)), v d = q ⟨d, hd⟩ :=
    fun d hd ↦ hv ▸ Rows.extendBot_of_mem q hd
  have m5 : (5 : Fin 12) ∈ cells.below (({1, 2} : Finset (Fin 3)), 2) := ⟨by decide, by decide⟩
  obtain ⟨hor, -, -⟩ := Rows.isLawfulBelow_iff_forall.mp hP'
  have hw5 : IsSelfVisible 1 (w 5) := hor 5 m5
  obtain ⟨hgv, hvlab⟩ := lawfulTriple_of_isLawfulBelow_univ_two hQ'
  have hc5 : min (v 5) c = min (w 5) c := by
    rw [hvq 5 (cells.below_mono h m5), hwp 5 m5]; exact hpq ⟨5, m5⟩
  -- The ambient labelling capped at `c` is lawful, so its full private cells read each other.
  have hcap : rows.{u}.IsLawful fun d ↦ min (lab (v 3) (v 4) (v 5) d) c :=
    (isLawful_lab hgv).min_const fun d hd ↦ by
      rcases grade_le_two_or_dead d with hg | h0
      · exact hc.mono hg
      · rw [lab_zero h0, le_bot_iff] at hd; rw [hd]; exact isSelfVisible_bot _
  obtain ⟨⟨hca, hcb, -, hcr, -, -⟩, -⟩ :=
    lawfulTriple_of_isLawfulBelow_univ_two (w := fun d ↦ min (lab (v 3) (v 4) (v 5) d) c)
      (hcap.isLawfulBelow ((univ : Finset (Fin 3)), 2))
  simp only [lab_one (d := 3) rfl, lab_two (d := 4) rfl] at hca hcb hcr
  -- The new labels of the full cells: the ambient ones if the donor class is unchanged,
  -- otherwise the ambient ones capped at `c`.
  set a' : Label.{u} := if w 5 = v 5 then v 3 else min (v 3) c with ha'
  set b' : Label.{u} := if w 5 = v 5 then v 4 else min (v 4) c with hb'
  have hgood : LawfulTriple a' b' (w 5) := by
    rw [ha', hb']
    split_ifs with he
    · exact he ▸ hgv
    · have hcw : c ≤ w 5 := by
        by_contra hlt
        rw [not_le] at hlt
        exact he (left_eq_of_min_eq_of_lt (hc5.trans (min_eq_left hlt.le)) hlt).symm
      exact ⟨hca, hcb, hw5, hcr, (min_le_right _ _).trans hcw, (min_le_right _ _).trans hcw⟩
  have hca' : min a' c = min (v 3) c := by
    rw [ha']; split_ifs
    · rfl
    · rw [min_assoc, min_self]
  have hcb' : min b' c = min (v 4) c := by
    rw [hb']; split_ifs
    · rfl
    · rw [min_assoc, min_self]
  refine ⟨fun d ↦ lab a' b' (w 5) d, (isLawful_lab hgood).isLawfulBelow _, fun d ↦ ?_,
    fun d ↦ ?_⟩
  -- The lift at `d` is `lab a' b' (w 5)` at the underlying cell (by definition).
  · change min (lab a' b' (w 5) d.1) c = min (q d) c
    rw [← hvq d.1 d.2, hvlab d.1 d.2]
    rcases kind_cases d.1 with h0 | h1 | h2 | h3
    · rw [lab_zero h0, lab_zero h0]
    · rw [lab_one h1, lab_one h1]; exact hca'
    · rw [lab_two h2, lab_two h2]; exact hcb'
    · rw [lab_three h3, lab_three h3]; exact hc5.symm
  · change lab a' b' (w 5) d.1 = p d
    rw [← hwp d.1 d.2]
    rcases kind_of_scope_one_two d.1 d.2.1 with h0 | h3
    · rw [eq_bot_of_dead hP' d.2 h0, lab_zero h0]
    · rw [lab_three h3, eq_five hP' d.2 h3]

/-- **The lifts at grade `1`** from a face containing the new point: below such pairs every cell
is dead or of kind `3`; keep the prescribed donor class. -/
private theorem cappedLift_grade_one {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y)
    (h5 : (5 : Fin 12) ∈ cells.below X) (hY : ∀ d ∈ cells.below Y, kind d = 0 ∨ kind d = 3) :
    rows.{u}.CappedLift h := by
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c _ p q hp hq hpq ↦ ?_
  have hP' := Rows.isLawfulBelow_extendBot.mpr hp
  have hQ' := Rows.isLawfulBelow_extendBot.mpr hq
  obtain ⟨w, hw⟩ : ∃ w, Rows.extendBot X p = w := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, Rows.extendBot Y q = v := ⟨_, rfl⟩
  rw [hw] at hP'
  rw [hv] at hQ'
  have hwp : ∀ d (hd : d ∈ cells.below X), w d = p ⟨d, hd⟩ :=
    fun d hd ↦ hw ▸ Rows.extendBot_of_mem p hd
  have hvq : ∀ d (hd : d ∈ cells.below Y), v d = q ⟨d, hd⟩ :=
    fun d hd ↦ hv ▸ Rows.extendBot_of_mem q hd
  obtain ⟨hor, -, -⟩ := Rows.isLawfulBelow_iff_forall.mp hP'
  have hgood : LawfulTriple ⊥ ⊥ (w 5) :=
    ⟨isSelfVisible_bot _, isSelfVisible_bot _, hor 5 h5, reads_self (isSelfVisible_bot _),
      bot_le, bot_le⟩
  have h5Y : (5 : Fin 12) ∈ cells.below Y := cells.below_mono h h5
  have hc5 : min (v 5) c = min (w 5) c := by
    rw [hvq 5 h5Y, hwp 5 h5]; exact hpq ⟨5, h5⟩
  refine ⟨fun d ↦ lab ⊥ ⊥ (w 5) d, (isLawful_lab hgood).isLawfulBelow _, fun d ↦ ?_,
    fun d ↦ ?_⟩
  · change min (lab ⊥ ⊥ (w 5) d.1) c = min (q d) c
    rw [← hvq d.1 d.2]
    rcases hY d.1 d.2 with h0 | h3
    · rw [lab_zero h0, eq_bot_of_dead hQ' d.2 h0]
    · rw [lab_three h3, eq_five hQ' d.2 h3]; exact hc5.symm
  · change lab ⊥ ⊥ (w 5) d.1 = p d
    rw [← hwp d.1 d.2]
    rcases hY d.1 (cells.below_mono h d.2) with h0 | h3
    · rw [eq_bot_of_dead hP' d.2 h0, lab_zero h0]
    · rw [lab_three h3, eq_five hP' d.2 h3]

/-- The rows are bountiful: within a face, below pairs where every cell is dead, the lifts from
the two coatoms `({0, 1}, 2)` and `({1, 2}, 2)` to `(univ, 2)`, and the lifts at grade `1`. -/
theorem isBountiful_rows : rows.{u}.IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  have hk : X.2 < 4 := by
    have := hX.2.2; have := card_le_univ X.1; simp only [Fintype.card_fin] at this; omega
  rcases case_split X.1 Y.1 hX.1 hY.1 h.1 ⟨X.2, hk⟩ hX.2.1 hX.2.2 with
    heq | hdead | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Rows.cappedLift_of_fst_eq _ heq
  · exact cappedLift_of_dead (fun d hd ↦ hdead d hd.1 hd.2) _
  · obtain ⟨X1, X2⟩ := X
    obtain ⟨Y1, Y2⟩ := Y
    simp only at h1 h2 h3
    subst h1 h2 h3
    exact cappedLift_private _
  · obtain ⟨X1, X2⟩ := X
    obtain ⟨Y1, Y2⟩ := Y
    simp only at h1 h2 h3
    subst h1 h2 h3
    exact cappedLift_donor _
  · refine cappedLift_grade_one _ ⟨?_, ?_⟩ fun d hd ↦ kind_of_grade_le_one d ?_
    · change cellScope 5 ⊆ X.1
      rw [show cellScope 5 = {2} from rfl, singleton_subset_iff]; exact h2
    · change cellGrade 5 ≤ X.2
      simp only at h1; rw [h1]; rfl
    · have := hd.2; simp only at h1; change cellGrade d ≤ X.2 at this; omega

/-- The scheme is well formed. -/
theorem isWellFormed_S : S.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

private theorem natCast_lt_omega0_sq (n : ℕ) :
    ((n : ℕ) : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rw [← WithBot.coe_natCast, WithBot.coe_lt_coe, ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  refine (Ordinal.natCast_lt_omega0 n).trans_le ?_
  rw [pow_two]; exact Ordinal.le_mul_left _ Ordinal.omega0_pos

/-- The entries of the rows are `⊥`, `2` and `3`, all below `ω ^ 2`. -/
theorem isCoded_S : S.{u}.IsCoded := fun s t ↦ by
  -- The entries of the rows of `S` are `rowValue` (by definition).
  change rowValue s t.1 < _
  unfold rowValue
  split_ifs
  · exact WithBot.bot_lt_coe _
  · exact natCast_lt_omega0_sq 2
  · exact natCast_lt_omega0_sq 3

private theorem lawfulTriple_three_two_three :
    LawfulTriple ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) :=
  ⟨sv_three, sv_two, sv_three_one, reads_three_two, le_rfl, two_lt_three.le⟩

private theorem lawfulTriple_two_three_three :
    LawfulTriple ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) :=
  ⟨sv_two, sv_three, sv_three_one, reads_two_three, two_lt_three.le, le_rfl⟩

private theorem lawfulTriple_bot_bot_three : LawfulTriple (⊥ : Label.{u}) ⊥ ((3 : ℕ) : Label.{u}) :=
  ⟨isSelfVisible_bot _, isSelfVisible_bot _, sv_three_one, reads_self (isSelfVisible_bot _),
    bot_le, bot_le⟩

private theorem lawfulTriple_top : LawfulTriple (⊤ : Label.{u}) ⊤ ⊤ :=
  ⟨isSelfVisible_top _, isSelfVisible_top _, isSelfVisible_top _,
    reads_self (isSelfVisible_top _), le_rfl, le_rfl⟩

/-- The rows are consistent: they are `⊥`, `lab 3 2 3`, `lab 2 3 3` and, below the donor class,
`lab ⊥ ⊥ 3`. -/
theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  -- Consistency asks that the row of `s` be lawful below `s` (by definition).
  change rows.IsLawfulBelow _ (fun t ↦ rows.row s t)
  rcases kind_cases s with h0 | h1 | h2 | h3
  · have : (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) = fun _ ↦ ⊥ :=
      funext fun t ↦ rowValue_zero_left h0
    rw [this]; exact Rows.isLawfulBelow_const_bot _
  · have : (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) =
        fun t ↦ lab ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) t.1 :=
      funext fun (t : cells.below (cells.gradedIndex s)) ↦ by
        -- The row of `s` is `rowValue s` (by definition).
        change rowValue s t.1 = _
        rcases kind_cases t.1 with t0 | t1 | t2 | t3
        · rw [rowValue_zero_right t0, lab_zero t0]
        · rw [rowValue_three (by omega) (by omega) (by omega), lab_one t1]
        · rw [rowValue_two (by omega) (by omega) (by omega), lab_two t2]
        · rw [rowValue_three (by omega) (by omega) (by omega), lab_three t3]
    rw [this]; exact (isLawful_lab lawfulTriple_three_two_three).isLawfulBelow _
  · have : (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) =
        fun t ↦ lab ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) t.1 :=
      funext fun (t : cells.below (cells.gradedIndex s)) ↦ by
        -- The row of `s` is `rowValue s` (by definition).
        change rowValue s t.1 = _
        rcases kind_cases t.1 with t0 | t1 | t2 | t3
        · rw [rowValue_zero_right t0, lab_zero t0]
        · rw [rowValue_two (by omega) (by omega) (by omega), lab_one t1]
        · rw [rowValue_three (by omega) (by omega) (by omega), lab_two t2]
        · rw [rowValue_three (by omega) (by omega) (by omega), lab_three t3]
    rw [this]; exact (isLawful_lab lawfulTriple_two_three_three).isLawfulBelow _
  · have : (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) =
        fun t ↦ lab (⊥ : Label.{u}) ⊥ ((3 : ℕ) : Label.{u}) t.1 :=
      funext fun (t : cells.below (cells.gradedIndex s)) ↦ by
        -- The row of `s` is `rowValue s` (by definition).
        change rowValue s t.1 = _
        have ht : cellGrade t.1 ≤ 1 := by
          have := t.2.2; change cellGrade t.1 ≤ cellGrade s at this
          rw [grade_of_kind_three s h3] at this; exact this
        rcases kind_of_grade_le_one t.1 ht with t0 | t3
        · rw [rowValue_zero_right t0, lab_zero t0]
        · rw [rowValue_three (by omega) (by omega) (by omega), lab_three t3]
    rw [this]; exact (isLawful_lab lawfulTriple_bot_bot_three).isLawfulBelow _

/-- Every graded face of the plan carries a cell. -/
theorem isComplete_cells : cells.IsComplete := by
  intro X hX
  have hk : X.2 < 4 := by
    have := hX.2.2; have := card_le_univ X.1; simp only [Fintype.card_fin] at this; omega
  obtain ⟨d, hd1, hd2⟩ := exists_cell X.1 hX.1 ⟨X.2, hk⟩ hX.2.1 hX.2.2
  exact ⟨d, Prod.ext hd1 hd2⟩

/-! ### The display as a stage type, with literal faces -/

open StageType GatedExtensionExample

/-- **The display**: the scheme `S` labelled `⊤` at the live cells and `⊥` at the dead ones. -/
noncomputable def Q (α : Ordinal.{u}) : StageType.{u} α 3 where
  toScheme := S
  label := lab ⊤ ⊤ ⊤
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_lab lawfulTriple_top
  atStage d := by unfold lab; split_ifs <;> simp

/-- **The display is legal.** -/
theorem isLegal_Q (α : Ordinal.{u}) : (Q α).IsLegal :=
  StageType.isLegal_iff.mpr ⟨isConsistent_rows, isBountiful_rows, isComplete_cells⟩

/-- The cells of the display, by their index. -/
def cellQ (α : Ordinal.{u}) (i : Fin 12) : Fin (Q α).card := i

private theorem mem_faces_castSuccEmb (α : Ordinal.{u}) :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ (Q α).toCellScheme.faces := by
  -- The faces of the display are the interval plan (by definition).
  change _ ∈ Geometry.intervalPlan univ; decide +kernel

private theorem visible_castSuccEmb_iff : ∀ d : Fin 12,
    cellScope d ⊆ univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ↔ (d : ℕ) < 5 := by decide +kernel

private theorem faces_agree : ∀ C : Finset (Fin 2),
    C.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) ↔
      C ∈ Geometry.intervalPlan (univ : Finset (Fin 2)) := by decide +kernel

private theorem scope_agree : ∀ i : Fin 5,
    (cellScope (Fin.castLE (by decide : 5 ≤ 12) i)).preimage (Fin.castSuccEmb : Fin 2 ↪ Fin 3)
      Fin.castSuccEmb.injective.injOn = GatedExtensionCounterexample.cellScope i := by
  intro i
  ext x
  rw [Finset.mem_preimage]
  revert i x
  decide +kernel

private theorem grade_agree : ∀ i : Fin 5,
    cellGrade (Fin.castLE (by decide : 5 ≤ 12) i) = GatedExtensionCounterexample.cellGrade i := by
  decide +kernel

private theorem rows_agree (s t : Fin 5)
    (h : t ∈ GatedExtensionCounterexample.cells.below
      (GatedExtensionCounterexample.cells.gradedIndex s)) :
    rowValue.{u} (Fin.castLE (by decide : 5 ≤ 12) s) (Fin.castLE (by decide : 5 ≤ 12) t) =
      GatedExtensionCounterexample.rows.{u}.row s ⟨t, h⟩ := by
  revert h; fin_cases s <;> fin_cases t <;> intro h <;> rfl

private theorem labels_agree (j : Fin 5) :
    lab (⊤ : Label.{u}) ⊤ ⊤ (Fin.castLE (by decide : 5 ≤ 12) j) =
      GatedExtensionCounterexample.labelling ⊤ ⊤ j := by
  fin_cases j <;> rfl

/-- **The private face of the display is literally the private type `P α`** of
`VaughtConjecture.Extension.GatedExtensionCounterexample`. -/
theorem restrictFace_Q (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (Q α) = some (GatedExtensionCounterexample.P α) := by
  rw [restrictFace_eq_some_iff]
  refine ⟨mem_faces_castSuccEmb α, ?_⟩
  let e : Fin 5 → Fin (Q α).card := fun i ↦ Fin.castLE (by decide : 5 ≤ 12) i
  have he : StrictMono e := fun _ _ h ↦ h
  have hr : ∀ d, d ∈ Set.range e ↔ d ∈ (Q α).toScheme.visibleCells Fin.castSuccEmb := by
    intro d
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
    -- The scope of a cell of the display is `cellScope` (by definition).
    change _ ↔ cellScope d ⊆ _
    rw [visible_castSuccEmb_iff d]
    exact ⟨by rintro ⟨i, rfl⟩; exact i.2, fun h ↦ ⟨⟨d, h⟩, rfl⟩⟩
  have key : ∀ {i : Fin 5} {j : Fin ((Q α).toScheme.comap Fin.castSuccEmb).card},
      (i : ℕ) = j → e i = (Q α).toScheme.cellMap Fin.castSuccEmb j :=
    fun hij ↦ (Q α).toScheme.cellMap_eq_of_strictMono Fin.castSuccEmb he hr hij
  have hcard : ((Q α).toScheme.comap Fin.castSuccEmb).card = 5 :=
    (Q α).toScheme.card_visibleCells_eq_of_strictMono Fin.castSuccEmb he hr
  refine StageType.ext ?_ (fun i j hij ↦ ?_)
  · rw [StageType.comap_toScheme]
    refine Scheme.ext hcard ?_ ?_ (fun k i hki ↦ ?_) (fun k i hki ↦ ?_)
      (fun s s' t t' hs ht ↦ ?_)
    · rw [Scheme.comap_ground]
      -- The ground of the display is `univ` (by definition).
      change (univ : Finset (Fin 3)).preimage _ _ = univ
      simp
    · ext C
      rw [Scheme.mem_comap_faces]
      exact faces_agree C
    · rw [Scheme.comap_scope, ← key hki.symm]
      exact scope_agree i
    · rw [Scheme.comap_grade, ← key hki.symm]
      exact grade_agree i
    · rw [Scheme.comap_row]
      -- The rows of the display are `rowValue` (by definition).
      change rowValue ((Q α).toScheme.cellMap Fin.castSuccEmb s)
        ((Q α).toScheme.cellMap Fin.castSuccEmb t.1) = _
      rw [← key hs.symm, ← key ht.symm]
      exact rows_agree s' t'.1 t'.2
  -- The labels of the display are `lab ⊤ ⊤ ⊤`, and those of the face are its cells' labels
  -- (`comap_label`, by definition).
  · change lab ⊤ ⊤ ⊤ ((Q α).toScheme.cellMap Fin.castSuccEmb i) =
      GatedExtensionCounterexample.labelling ⊤ ⊤ j
    rw [← key hij.symm]
    exact labels_agree j

/-! ### The donor face and the root -/

private theorem univ_map_extendByLast_emptyRoot :
    univ.map (extendByLast emptyRoot) = ({2} : Finset (Fin 3)) := by
  rw [univ_map_extendByLast]; decide +kernel

/-- The donor face `{2}` is a face of the display. -/
theorem mem_faces_extendByLast (α : Ordinal.{u}) :
    univ.map (extendByLast emptyRoot) ∈ (Q α).toCellScheme.faces := by
  -- The faces of the display are the interval plan (by definition).
  rw [univ_map_extendByLast_emptyRoot]; change _ ∈ Geometry.intervalPlan univ; decide +kernel

/-- **The donor labelled `⊤`**: the face `{2}` of the display, one cell, labelled `⊤`. -/
noncomputable def donor (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (Q α).comap (extendByLast emptyRoot) (mem_faces_extendByLast α)

/-- The donor face of the display is the donor. -/
theorem restrictFace_donor (α : Ordinal.{u}) :
    restrictFace (extendByLast emptyRoot) (Q α) = some (donor α) := restrictFace_of_mem _ _ _

/-- The donor restricts to the type of the empty root. -/
theorem restrictFace_donor_castSuccEmb (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (donor α) = some (CoupledGateExamples.root α) := by
  rw [restrictFace_trans _ _ _ (restrictFace_donor α), castSuccEmb_trans_extendByLast,
    ← restrictFace_trans _ _ _ (restrictFace_Q α), CoupledGateExamples.restrictFace_root]

/-- The donor is legal, as a face of the legal display. -/
theorem isLegal_donor (α : Ordinal.{u}) : (donor α).IsLegal :=
  (isLegal_Q α).restrictFace _ (restrictFace_donor α)

private theorem range_extendByLast :
    Set.range (extendByLast emptyRoot) = (({2} : Finset (Fin 3)) : Set (Fin 3)) := by
  rw [← univ_map_extendByLast_emptyRoot]; simp

private theorem eq_five_of_visible (α : Ordinal.{u}) (e : Fin (Q α).card)
    (he : e ∈ (Q α).toCellScheme.visible (Set.range (extendByLast emptyRoot))) :
    e = cellQ α 5 := by
  -- A cell is visible when its scope lies in the range (by definition).
  change ((cellScope e : Finset (Fin 3)) : Set (Fin 3)) ⊆ _ at he
  rw [range_extendByLast, coe_subset] at he
  exact eq_five_of_scope e he

/-- **Every cell of the donor is labelled `⊤`**: its cells are the cell `5` of the display. -/
theorem label_donor (α : Ordinal.{u}) (j : Fin (donor α).card) : (donor α).label j = ⊤ := by
  -- The labels of the donor face are the labels of its cells (`comap_label`, by definition).
  change (Q α).label ((Q α).cellMap (extendByLast emptyRoot) j) = ⊤
  have hj := (Q α).cellMap_mem (extendByLast emptyRoot) j
  rw [Scheme.mem_visibleCells] at hj
  rw [eq_five_of_visible α _ hj]
  rfl

/-- The donor has exactly one cell. -/
theorem card_donor (α : Ordinal.{u}) : (donor α).card = 1 := by
  let e₁ : Fin 1 → Fin (Q α).card := fun _ ↦ cellQ α 5
  have he₁ : StrictMono e₁ := fun a b h ↦
    absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl _)
  have hr₁ : ∀ d, d ∈ Set.range e₁ ↔ d ∈ (Q α).toScheme.visibleCells (extendByLast emptyRoot) := by
    intro d
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
    -- The scope of a cell of the display is `cellScope` (by definition).
    change _ ↔ cellScope d ⊆ _
    rw [univ_map_extendByLast_emptyRoot]
    refine ⟨by rintro ⟨i, rfl⟩; exact (by decide : cellScope (5 : Fin 12) ⊆ {2}),
      fun h ↦ ⟨0, (eq_five_of_scope d h).symm⟩⟩
  exact (Q α).toScheme.card_visibleCells_eq_of_strictMono (extendByLast emptyRoot) he₁ hr₁

/-- The donor is anchored in `P α` below every cell, without anchors: its one cell is labelled
`⊤`. -/
theorem isAnchored_donor (α : Ordinal.{u}) (C : Fin (GatedExtensionCounterexample.P α).card) :
    (GatedExtensionCounterexample.P α).IsAnchored C (donor α) :=
  isAnchored_of_forall_label_eq_bot_or_top _ _ fun j _ ↦ .inr (label_donor α j)

/-! ### Cap lowering at this instance -/

/-- **The donor cell bounds the full private cells** in every lawful labelling of the display:
the gate reads the donor cell `5` at least as the cap. -/
theorem le_label_five {α : Ordinal.{u}} {q : Fin (Q α).card → Label.{u}}
    (hq : (Q α).rows.IsLawful q) : q (cellQ α 3) ≤ q (cellQ α 5) ∧ q (cellQ α 4) ≤ q (cellQ α 5) :=
  le_five_of_isLawfulBelow_univ_two (w := q) (hq.isLawfulBelow ((univ : Finset (Fin 3)), 2))

/-- **The caps are lowered**: for a cap `c` self-visible at `2` and a value `v ≥ c` self-visible at
`1` prescribed at the donor cell, the labelling `c` at the full cells, the gate and the twin, and
`v` at the donor cell and its copies, is lawful for the rows of the display, lies in the cap ball
of the display at `c`, and labels the private cap `c ≤ v`.  This is the labelling that the lift
from `({2}, 1)`, `({1, 2}, 1)` or `({1, 2}, 2)` gives at the prescription `v` when `v ≠ ⊤`. -/
theorem isLawful_capLowered (α : Ordinal.{u}) {c v : Label.{u}} (hc : IsSelfVisible 2 c)
    (hv : IsSelfVisible 1 v) (hcv : c ≤ v) :
    (Q α).rows.IsLawful (lab c c v) ∧ (∀ d, min (lab c c v d) c = min ((Q α).label d) c) ∧
      lab c c v (cellQ α 3) = c ∧ lab c c v (cellQ α 5) = v :=
  ⟨isLawful_lab ⟨hc, hc, hv, reads_self hc, hcv, hcv⟩, fun d ↦ by
    -- The labels of the display are `lab ⊤ ⊤ ⊤` (by definition).
    change min (lab c c v d) c = min (lab ⊤ ⊤ ⊤ d) c
    rcases kind_cases d with h0 | h1 | h2 | h3
    · rw [lab_zero h0, lab_zero h0]
    · rw [lab_one h1, lab_one h1, min_self, min_top_left]
    · rw [lab_two h2, lab_two h2, min_self, min_top_left]
    · rw [lab_three h3, lab_three h3, min_top_left, min_eq_right hcv], rfl, rfl⟩

/-! ### The coupled gated extensions -/

private theorem range_castSuccEmb :
    Set.range (Fin.castSuccEmb : Fin 2 ↪ Fin 3) = (({0, 1} : Finset (Fin 3)) : Set (Fin 3)) := by
  ext x; fin_cases x <;> simp [Fin.ext_iff]

private theorem mem_visible_castSuccEmb (α : Ordinal.{u}) (d : Fin 12)
    (hd : cellScope d ⊆ {0, 1}) :
    cellQ α d ∈ (Q α).toCellScheme.visible (Set.range Fin.castSuccEmb) := by
  -- A cell is visible when its scope lies in the range (by definition).
  change ((cellScope d : Finset (Fin 3)) : Set (Fin 3)) ⊆ Set.range Fin.castSuccEmb
  rw [range_castSuccEmb, coe_subset]; exact hd

/-- **A coupled gated extension of `P α`** over the empty root with the donor labelled `⊤`, with
cap the full private cell `C` (`3` or `4`) and gate its copy `G` (`9` or `10`). -/
private noncomputable def E (α : Ordinal.{u}) (C G : Fin 12) (hC : C = 3 ∧ G = 9 ∨ C = 4 ∧ G = 10) :
    StageType.CoupledGatedExtension (GatedExtensionCounterexample.P α) emptyRoot (donor α) where
  display := Q α
  isLegal := isLegal_Q α
  restrictFace_castSuccEmb := restrictFace_Q α
  restrictFace_extendByLast := restrictFace_donor α
  gate := cellQ α G
  cap := cellQ α C
  gradedIndex_gate := by
    -- The graded index of a cell is its scope and grade (by definition).
    change (cellScope G, cellGrade G) = _
    rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  gradedIndex_cap := by
    -- The graded index of a cell is its scope and grade (by definition).
    change (cellScope C, cellGrade C) = (univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3), 2)
    rcases hC with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide +kernel
  twinsReadGate := fun t _ _ ht htG ↦ by
    have ht' : (cellScope t, cellGrade t) = (cellScope 9, cellGrade 9) := by
      rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ht
      · exact ht.trans rfl
    -- The rows of the display are `rowValue` (by definition).
    change rowValue t C ≤ rowValue t G
    rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases eq_of_gradedIndex_nine t ht' with h | h <;>
      first
      | exact absurd h htG
      | (subst h
         rw [rowValue_two (by decide) (by decide) (by decide),
           rowValue_two (by decide) (by decide) (by decide)])
  isGate :=
    { cap_mem := by
        rcases hC with ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [mem_visible_castSuccEmb α 3 (by decide), mem_visible_castSuccEmb α 4 (by decide)]
      -- The scope of a cell of the display is `cellScope` (by definition).
      scope_cap_subset := by
        change cellScope C ⊆ cellScope G
        rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      grade_cap := by rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      -- The labels of the display are `lab ⊤ ⊤ ⊤` (by definition).
      cap_ne_bot := by
        change lab ⊤ ⊤ ⊤ C ≠ ⊥
        rcases hC with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [lab, kind]
      le_gate := fun e he ↦ by
        rw [eq_five_of_visible α e he]
        -- The graded index of a cell is its scope and grade (by definition).
        change (cellScope 5, cellGrade 5) ≤ (cellScope G, cellGrade G)
        rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨by decide, by decide⟩
      reads := fun e he _ ↦ by
        obtain rfl := eq_five_of_visible α e he
        -- The donor cell is labelled `⊤`, at least the cap: the row of the gate reads it at
        -- `3`, as it reads the cap.
        refine .top ⟨cellQ α C, ?_⟩ ?_ le_rfl ?_ ?_
        · change (cellScope C, cellGrade C) ≤ (cellScope G, cellGrade G)
          rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, le_rfl⟩
        · rcases hC with ⟨rfl, -⟩ | ⟨rfl, -⟩
          exacts [mem_visible_castSuccEmb α 3 (by decide), mem_visible_castSuccEmb α 4 (by decide)]
        · change lab ⊤ ⊤ ⊤ C ≤ lab ⊤ ⊤ ⊤ 5
          rw [lab_three (d := 5) rfl]; exact le_top
        · change rowValue G C ≤ rowValue G 5
          rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rw [rowValue_three (by decide) (by decide) (by decide),
              rowValue_three (by decide) (by decide) (by decide)] }

/-- **The coupled gated pinned extension property holds at this instance**: the private type
`P α`, the empty root, the donor labelled `⊤` (`donor α`), and either full private cell as the
cap. -/
theorem exists_coupledGatedExtension_donor (α : Ordinal.{u})
    (C : Fin (GatedExtensionCounterexample.P α).card)
    (hC : (GatedExtensionCounterexample.P α).toCellScheme.gradedIndex C = (univ, 2)) :
    ∃ E : StageType.CoupledGatedExtension (GatedExtensionCounterexample.P α) emptyRoot (donor α),
      E.display.label E.cap = (GatedExtensionCounterexample.P α).label C := by
  have key : ∀ C : Fin 5, (GatedExtensionCounterexample.cellScope C,
      GatedExtensionCounterexample.cellGrade C) = (univ, 2) → C = 3 ∨ C = 4 := by decide +kernel
  -- The graded index of a cell of `P α` is `(cellScope, cellGrade)` (by definition).
  rcases key C hC with h | h <;> rw [h]
  · exact ⟨E α 3 9 (.inl ⟨rfl, rfl⟩), rfl⟩
  · exact ⟨E α 4 10 (.inr ⟨rfl, rfl⟩), rfl⟩

/-- **The coupled gated pinned extension property holds at this instance**, every hypothesis
included: the private type `P α` is legal, the empty root has the type `root α`, the donor
labelled `⊤` is legal and restricts to `root α`, the arities satisfy `0 + 1 < 2`, and for each cell
`C` of `P α` of graded index `(univ, 2)` the label of `C` is not `⊥`, the donor is anchored below
`C`, and a coupled gated extension with cap labelled as `C` exists. -/
theorem coupledGatedPinnedExtension_donor (α : Ordinal.{u}) :
    (GatedExtensionCounterexample.P α).IsLegal ∧
      restrictFace emptyRoot (GatedExtensionCounterexample.P α) =
        some (CoupledGateExamples.root α) ∧
      (donor α).IsLegal ∧
      restrictFace Fin.castSuccEmb (donor α) = some (CoupledGateExamples.root α) ∧
      0 + 1 < 2 ∧
      ∀ C : Fin (GatedExtensionCounterexample.P α).card,
        (GatedExtensionCounterexample.P α).toCellScheme.gradedIndex C = (univ, 2) →
          (GatedExtensionCounterexample.P α).label C ≠ ⊥ ∧
          (GatedExtensionCounterexample.P α).IsAnchored C (donor α) ∧
          ∃ E : StageType.CoupledGatedExtension (GatedExtensionCounterexample.P α) emptyRoot
              (donor α),
            E.display.label E.cap = (GatedExtensionCounterexample.P α).label C := by
  refine ⟨GatedExtensionCounterexample.isLegal_P α, CoupledGateExamples.restrictFace_root α,
    isLegal_donor α, restrictFace_donor_castSuccEmb α, by decide, fun C hC ↦
      ⟨?_, isAnchored_donor α C, exists_coupledGatedExtension_donor α C hC⟩⟩
  have key : ∀ C : Fin 5, (GatedExtensionCounterexample.cellScope C,
      GatedExtensionCounterexample.cellGrade C) = (univ, 2) → C = 3 ∨ C = 4 := by decide +kernel
  -- The graded index of a cell of `P α` is `(cellScope, cellGrade)`, and its labels are
  -- `labelling ⊤ ⊤` (by definition).
  change GatedExtensionCounterexample.labelling ⊤ ⊤ C ≠ ⊥
  rcases key C hC with h | h <;> rw [h] <;> simp [GatedExtensionCounterexample.labelling]

end VaughtConjecture.CoupledGateInstance
