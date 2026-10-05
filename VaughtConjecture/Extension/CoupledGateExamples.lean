/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.GateExamples
import VaughtConjecture.Extension.GatedExtensionCounterexample

/-!
# A coupled gated extension of the refuting private type

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate) and 3.4, row
(R1); the coupled gated extensions of `VaughtConjecture.Extension.GatedExtension`.

**The theorem** (`exists_coupledGatedExtension_refutingInput`).  The coupled gated pinned
extension property (`StageType.HasCoupledGatedPinnedExtensions`) holds at the input at which the
gated pinned extension property fails (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`):
the private type `GatedExtensionCounterexample.P α`, the empty root, the donor `P α|{0}`, whose one
cell is labelled `⊥`, and the cap `3`.  So the obstruction of
`VaughtConjecture.Extension.GatedExtensionCounterexample`, which forces a twin of the gate not
labelled `⊥` in every legal one-point extension of `P α`, does not refute the coupled property.
Nothing more is proved about the coupled property, which is open: the donor labelled `⊤` on `P α`
(which needs the cap of `P α` lowered in the lift from `({1, 2}, 2)`, the open point (CL) of
`StageType.HasCoupledGatedPinnedExtensions`), donors with several new cells, and other private
types are not compiled (prospective).

**The display `Q α`** (`Q`, `isLegal_Q`).  On three points with the interval plan, twelve cells;
a cell is **dead** when its kind is `0`, **live** otherwise:

| cell        | scope       | grade | kind |
|-------------|-------------|-------|------|
| 0, 1        | {0}, {1}    | 1     | 0    |
| 2           | {0, 1}      | 1     | 0    |
| 3 (`C₁`)    | {0, 1}      | 2     | 1    |
| 4 (`C₂`)    | {0, 1}      | 2     | 2    |
| 5           | {2}         | 1     | 0    |
| 6, 7        | {1, 2}      | 1, 2  | 0    |
| 8           | univ        | 1     | 0    |
| 9 (`G`)     | univ        | 2     | 1    |
| 10 (`T`)    | univ        | 2     | 2    |
| 11          | univ        | 3     | 0    |

The rows are `⊥` at or from a dead cell; between live cells they are `3` for equal kinds and `2`
for different kinds.  So the gate `9` reads the private cells as the cap `C₁ = 3` does, the twin
`10` reads them as the other full cell `C₂ = 4` does, and the twin reads the cap and the gate both
at `2`: the coupling `CellScheme.Rows.TwinsReadGate` holds, with equality.  The gate reads the twin
at `2`, the entry of the cap at the private counterpart `C₂` of the twin.  The display is labelled
`⊤` at the live cells and `⊥` at the dead ones; its private face `{0, 1}` is literally
`GatedExtensionCounterexample.P α` (`restrictFace_Q`) and its donor face `{2}` is literally the
face `{0}` of `P α` (`donor_eq`).

**Legality.**  The rows are consistent: they are `⊥`, `lab 3 2` and `lab 2 3`.  Bountifulness
has three cases: lifts within a face; lifts from pairs below which every cell is dead, which keep
the ambient labelling; and the lift from `({0, 1}, 2)` to `(univ, 2)`, which copies the prescribed
values at `C₁` and `C₂` to the gate and the twin.  Every labelling lawful below `(univ, 2)` has
that form (`eq_of_isLawfulBelow_univ_two`), by locality at `9` and `10` and availability; in
particular the gate equals the cap in every lawful labelling (`gate_eq_cap`).  The refutation of
the gated pinned extension property does not apply: in the lift of the labelling `(⊤, 2)` of
`(C₁, C₂)` the gate is `⊤` and the twin `2`, and in the lift of `(2, ⊤)` the gate is `2` and the
twin `⊤`, so the twin serves availability for `C₂`.

**The regression** (`not_twinsReadGate_twin`).  The twin of the counterexamples
`GateExamples.twin_bottom_gate` and `GateExamples.twin_small_gate`, in which a lawful labelling
with the literal private face loses the gate inequality, reads the cap at `⊤` and the gate at `3`:
its rows do not satisfy the coupling, as they must not.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.CoupledGateExamples

open Finset Label CellScheme

/-! ### The scheme -/

/-- The scopes of the twelve cells. -/
def cellScope : Fin 12 → Finset (Fin 3) :=
  ![{0}, {1}, {0, 1}, {0, 1}, {0, 1}, {2}, {1, 2}, {1, 2}, univ, univ, univ, univ]

/-- The grades of the twelve cells. -/
def cellGrade : Fin 12 → ℕ := ![1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3]

/-- `0`: dead; `1`: the cap and its copy, the gate; `2`: the other full cell and its copy. -/
def kind : Fin 12 → ℕ := ![0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 2, 0]

/-- The cells, on the interval plan of the three points. -/
def cells : CellScheme (Fin 12) (Fin 3) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

private noncomputable def rowValue (s t : Fin 12) : Label.{u} :=
  if kind s = 0 ∨ kind t = 0 then ⊥
  else if kind s = kind t then ((3 : ℕ) : Label.{u}) else ((2 : ℕ) : Label.{u})

/-- The rows: `⊥` at or from a dead cell, `3` between live cells of equal kinds, `2` between
live cells of different kinds. -/
noncomputable def rows : cells.Rows.{u} := ⟨fun s t ↦ rowValue s t.1⟩

/-- The scheme of the display. -/
noncomputable def S : Scheme.{u} 3 := ⟨12, cells, rows⟩

/-- `a` at the kind-`1` cells, `b` at the kind-`2` cells, `⊥` elsewhere. -/
noncomputable def lab (a b : Label.{u}) (d : Fin 12) : Label.{u} :=
  if kind d = 1 then a else if kind d = 2 then b else ⊥

/-! ### Finite facts -/

private theorem kind_cases (d : Fin 12) : kind d = 0 ∨ kind d = 1 ∨ kind d = 2 := by
  revert d; decide +kernel

private theorem grade_of_kind_ne_zero : ∀ d : Fin 12, kind d ≠ 0 → cellGrade d = 2 := by
  decide +kernel

private theorem exists_partner : ∀ s t : Fin 12, cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → ∃ u, cellScope u = cellScope t ∧ cellGrade u = cellGrade t ∧
      (kind s = 0 ∨ kind u = kind s) := by
  decide +kernel

private theorem eq_of_gradedIndex_nine : ∀ u : Fin 12,
    (cellScope u, cellGrade u) = (cellScope 9, cellGrade 9) → u = 9 ∨ u = 10 := by
  decide +kernel

private theorem eq_three_of_below : ∀ d : Fin 12, cellScope d ⊆ {0, 1} → kind d = 1 → d = 3 := by
  decide +kernel

private theorem eq_four_of_below : ∀ d : Fin 12, cellScope d ⊆ {0, 1} → kind d = 2 → d = 4 := by
  decide +kernel

private theorem eq_of_kind_one : ∀ d : Fin 12, kind d = 1 → d = 3 ∨ d = 9 := by decide +kernel

private theorem eq_of_kind_two : ∀ d : Fin 12, kind d = 2 → d = 4 ∨ d = 10 := by decide +kernel

private theorem eq_five_of_scope : ∀ d : Fin 12, cellScope d ⊆ {2} → d = 5 := by decide +kernel

/-- Every cell below `(A, k)` is dead. -/
private def AllDead (A : Finset (Fin 3)) (k : ℕ) : Prop :=
  ∀ d, cellScope d ⊆ A → cellGrade d ≤ k → kind d = 0

private instance (A : Finset (Fin 3)) (k : ℕ) : Decidable (AllDead A k) := by
  unfold AllDead; infer_instance

set_option synthInstance.maxSize 512 in
/-- Below a graded face of the plan, either the face is that of the target, or every cell below is
dead, or the pair is `({0, 1}, 2)` under `(univ, 2)`. -/
private theorem case_split : ∀ A B : Finset (Fin 3),
    A ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) →
    B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) → A ⊆ B → ∀ k : Fin 4, 0 < (k : ℕ) →
      (k : ℕ) ≤ #A → A = B ∨ AllDead A k ∨ (A = {0, 1} ∧ (k : ℕ) = 2 ∧ B = univ) := by
  decide +kernel

private theorem exists_cell : ∀ B : Finset (Fin 3),
    B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) → ∀ k : Fin 4, 0 < (k : ℕ) → (k : ℕ) ≤ #B →
      ∃ d : Fin 12, cellScope d = B ∧ cellGrade d = k := by
  decide +kernel

/-! ### Labels and row values -/

variable {a b : Label.{u}} {d s t : Fin 12}

private theorem lab_zero (h : kind d = 0) : lab a b d = ⊥ := by simp [lab, h]

private theorem lab_one (h : kind d = 1) : lab a b d = a := by simp [lab, h]

private theorem lab_two (h : kind d = 2) : lab a b d = b := by simp [lab, h]

private theorem rowValue_zero_left (h : kind s = 0) : rowValue.{u} s t = ⊥ := by simp [rowValue, h]

private theorem rowValue_zero_right (h : kind t = 0) : rowValue.{u} s t = ⊥ := by simp [rowValue, h]

private theorem rowValue_eq (_hs : kind s ≠ 0) (ht : kind t ≠ 0) (h : kind s = kind t) :
    rowValue.{u} s t = ((3 : ℕ) : Label.{u}) := by simp [rowValue, ht, h]

private theorem rowValue_ne (hs : kind s ≠ 0) (ht : kind t ≠ 0) (h : kind s ≠ kind t) :
    rowValue.{u} s t = ((2 : ℕ) : Label.{u}) := by simp [rowValue, hs, ht, h]

private theorem two_lt_three : ((2 : ℕ) : Label.{u}) < ((3 : ℕ) : Label.{u}) := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_lt_coe, ← WithTop.coe_natCast,
    ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  exact Nat.cast_lt.mpr (by decide)

private theorem sv_two : IsSelfVisible 2 ((2 : ℕ) : Label.{u}) := by simp

private theorem sv_three : IsSelfVisible 2 ((3 : ℕ) : Label.{u}) := by simp

private theorem topShifter_natCast (n : ℕ) : topShifter ((n : ℕ) : Label.{u}) = ⊤ := by
  simp [topShifter]

/-! ### Lawful labellings `lab a b` -/

/-- The two readings that make `lab a b` local at the full cells. -/
private def Reads (a b : Label.{u}) : Prop :=
  (∃ g σ, IsWitness g σ ∧ a = min (σ ((3 : ℕ) : Label.{u})) (g 2) ∧
      min b a = min (σ ((2 : ℕ) : Label.{u})) (g 2)) ∧
  (∃ g σ, IsWitness g σ ∧ min a b = min (σ ((2 : ℕ) : Label.{u})) (g 2) ∧
      b = min (σ ((3 : ℕ) : Label.{u})) (g 2))

private theorem topWitness {a : Label.{u}} (ha : IsSelfVisible 2 a) :
    IsWitness (constStepSuppressor 2 a) topShifter :=
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

private theorem locality_lab (hr : Reads a b) (s : Fin 12) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.row s)
      (fun d ↦ min (lab a b d) (lab a b s)) := by
  rcases kind_cases s with h0 | h1 | h2
  · simp only [lab_zero h0, min_bot_right]
    exact TransformsTo.bot _ _
  · obtain ⟨g, σ, hw, ha, hb⟩ := hr.1
    refine ⟨g, σ, hw, fun d ↦ ?_⟩
    change min (lab a b d.1) (lab a b s) = min (σ (rowValue s d.1)) (g (cellGrade d.1))
    rw [lab_one h1]
    rcases kind_cases d.1 with d0 | d1 | d2
    · rw [lab_zero d0, rowValue_zero_right d0, hw.map_bot, min_eq_left bot_le,
        min_eq_left bot_le]
    · rw [lab_one d1, rowValue_eq (by omega) (by omega) (by omega),
        grade_of_kind_ne_zero _ (by omega), min_self]
      exact ha
    · rw [lab_two d2, rowValue_ne (by omega) (by omega) (by omega),
        grade_of_kind_ne_zero _ (by omega)]
      exact hb
  · obtain ⟨g, σ, hw, ha, hb⟩ := hr.2
    refine ⟨g, σ, hw, fun d ↦ ?_⟩
    change min (lab a b d.1) (lab a b s) = min (σ (rowValue s d.1)) (g (cellGrade d.1))
    rw [lab_two h2]
    rcases kind_cases d.1 with d0 | d1 | d2
    · rw [lab_zero d0, rowValue_zero_right d0, hw.map_bot, min_eq_left bot_le,
        min_eq_left bot_le]
    · rw [lab_one d1, rowValue_ne (by omega) (by omega) (by omega),
        grade_of_kind_ne_zero _ (by omega)]
      exact ha
    · rw [lab_two d2, rowValue_eq (by omega) (by omega) (by omega),
        grade_of_kind_ne_zero _ (by omega), min_self]
      exact hb

/-- **`lab a b` is lawful** given the two readings and self-visibility at `2`. -/
private theorem isLawful_lab (ha : IsSelfVisible 2 a) (hb : IsSelfVisible 2 b) (hr : Reads a b) :
    rows.{u}.IsLawful (lab a b) where
  orderly d := by
    rcases kind_cases d with h0 | h1 | h2
    · rw [lab_zero h0]; exact isSelfVisible_bot _
    · rw [lab_one h1]
      change IsSelfVisible (cellGrade d) a
      rw [grade_of_kind_ne_zero d (by omega)]; exact ha
    · rw [lab_two h2]
      change IsSelfVisible (cellGrade d) b
      rw [grade_of_kind_ne_zero d (by omega)]; exact hb
  locality := locality_lab hr
  availability s t hst hg := by
    obtain ⟨u, hu1, hu2, hk⟩ := exists_partner s t hst hg
    refine ⟨u, Prod.ext hu1 hu2, ?_⟩
    rcases hk with h0 | hk
    · rw [lab_zero h0]; exact bot_le
    · unfold lab; rw [hk]

/-- Dead cells are `⊥` in every labelling lawful below a pair above them. -/
private theorem eq_bot_of_dead {X : Finset (Fin 3) × ℕ} {w : Fin 12 → Label.{u}}
    (hw : rows.IsLawfulBelow X (fun d ↦ w d)) {d : Fin 12} (hd : d ∈ cells.below X)
    (h0 : kind d = 0) : w d = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have h := (hl d hd).eq_bot (d := ⟨d, cells.mem_below_gradedIndex d⟩)
    (rowValue_zero_left (t := d) h0)
  simpa using h

/-- The localities at the two full cells give the two readings. -/
private theorem reads_of_localities {w : Fin 12 → Label.{u}}
    (h3 : TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.row 3)
      (fun d ↦ min (w d) (w 3)))
    (h4 : TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.row 4)
      (fun d ↦ min (w d) (w 4))) : Reads (w 3) (w 4) := by
  obtain ⟨g, σ, hw, heq⟩ := h3
  obtain ⟨g', σ', hw', heq'⟩ := h4
  have m : ∀ s d : Fin 12, cellScope d ⊆ cellScope s → cellGrade d ≤ cellGrade s →
      d ∈ cells.below (cells.gradedIndex s) := fun _ _ h1 h2 ↦ ⟨h1, h2⟩
  have e33 := heq ⟨3, m 3 3 subset_rfl le_rfl⟩
  have e34 := heq ⟨4, m 3 4 (by decide) le_rfl⟩
  have e43 := heq' ⟨3, m 4 3 (by decide) le_rfl⟩
  have e44 := heq' ⟨4, m 4 4 subset_rfl le_rfl⟩
  change min (w 3) (w 3) = min (σ (rowValue 3 3)) (g 2) at e33
  change min (w 4) (w 3) = min (σ (rowValue 3 4)) (g 2) at e34
  change min (w 3) (w 4) = min (σ' (rowValue 4 3)) (g' 2) at e43
  change min (w 4) (w 4) = min (σ' (rowValue 4 4)) (g' 2) at e44
  rw [rowValue_eq (s := 3) (t := 3) (by decide) (by decide) rfl, min_self] at e33
  rw [rowValue_eq (s := 4) (t := 4) (by decide) (by decide) rfl, min_self] at e44
  rw [rowValue_ne (s := 3) (t := 4) (by decide) (by decide) (by decide)] at e34
  rw [rowValue_ne (s := 4) (t := 3) (by decide) (by decide) (by decide)] at e43
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

/-- **Below `(univ, 2)` the gate and the twin copy the two full cells**: every labelling lawful
below `(univ, 2)` has `w 9 = w 3` and `w 10 = w 4`. -/
theorem eq_of_isLawfulBelow_univ_two {w : Fin 12 → Label.{u}}
    (hw : rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ w d)) :
    w 9 = w 3 ∧ w 10 = w 4 := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hb : ∀ d : Fin 12, cellGrade d ≤ 2 → d ∈ cells.below ((univ : Finset (Fin 3)), 2) :=
    fun d hd ↦ ⟨subset_univ _, hd⟩
  have m : ∀ s d : Fin 12, cellScope d ⊆ cellScope s → cellGrade d ≤ cellGrade s →
      d ∈ cells.below (cells.gradedIndex s) := fun _ _ h1 h2 ↦ ⟨h1, h2⟩
  obtain ⟨g, σ, -, heq⟩ := hl 9 (hb 9 le_rfl)
  obtain ⟨g', σ', -, heq'⟩ := hl 10 (hb 10 le_rfl)
  have e93 := heq ⟨3, m 9 3 (by decide) le_rfl⟩
  have e94 := heq ⟨4, m 9 4 (by decide) le_rfl⟩
  have e99 := heq ⟨9, m 9 9 subset_rfl le_rfl⟩
  have e910 := heq ⟨10, m 9 10 subset_rfl le_rfl⟩
  have e103 := heq' ⟨3, m 10 3 (by decide) le_rfl⟩
  have e104 := heq' ⟨4, m 10 4 (by decide) le_rfl⟩
  have e109 := heq' ⟨9, m 10 9 subset_rfl le_rfl⟩
  have e1010 := heq' ⟨10, m 10 10 subset_rfl le_rfl⟩
  change min (w 3) (w 9) = min (σ (rowValue 9 3)) (g 2) at e93
  change min (w 4) (w 9) = min (σ (rowValue 9 4)) (g 2) at e94
  change min (w 9) (w 9) = min (σ (rowValue 9 9)) (g 2) at e99
  change min (w 10) (w 9) = min (σ (rowValue 9 10)) (g 2) at e910
  change min (w 3) (w 10) = min (σ' (rowValue 10 3)) (g' 2) at e103
  change min (w 4) (w 10) = min (σ' (rowValue 10 4)) (g' 2) at e104
  change min (w 9) (w 10) = min (σ' (rowValue 10 9)) (g' 2) at e109
  change min (w 10) (w 10) = min (σ' (rowValue 10 10)) (g' 2) at e1010
  rw [rowValue_eq (s := 9) (t := 3) (by decide) (by decide) rfl] at e93
  rw [rowValue_eq (s := 9) (t := 9) (by decide) (by decide) rfl] at e99
  rw [rowValue_eq (s := 10) (t := 4) (by decide) (by decide) rfl] at e104
  rw [rowValue_eq (s := 10) (t := 10) (by decide) (by decide) rfl] at e1010
  rw [rowValue_ne (s := 9) (t := 4) (by decide) (by decide) (by decide)] at e94
  rw [rowValue_ne (s := 9) (t := 10) (by decide) (by decide) (by decide)] at e910
  rw [rowValue_ne (s := 10) (t := 3) (by decide) (by decide) (by decide)] at e103
  rw [rowValue_ne (s := 10) (t := 9) (by decide) (by decide) (by decide)] at e109
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

/-! ### Legality -/

/-- If every cell below `X` is dead, the rows lift capped from `X`: keep the ambient labelling. -/
private theorem cappedLift_of_dead {X Y : Finset (Fin 3) × ℕ} (hX : ∀ d ∈ cells.below X, kind d = 0)
    (h : X ≤ Y) : rows.{u}.CappedLift h := by
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

/-- **The main lift**, from the private pair `({0, 1}, 2)` to `(univ, 2)`: copy the private full
cells to the gate and the twin. -/
private theorem cappedLift_main
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
  have hlaw := isLawful_lab (hor 3 m3) (hor 4 m4) hr
  have hwlab : ∀ d ∈ cells.below (({0, 1} : Finset (Fin 3)), 2), w d = lab (w 3) (w 4) d := by
    intro d hd
    rcases kind_cases d with h0 | h1 | h2
    · rw [eq_bot_of_dead hP' hd h0, lab_zero h0]
    · obtain rfl := eq_three_of_below d hd.1 h1
      rw [lab_one h1]
    · obtain rfl := eq_four_of_below d hd.1 h2
      rw [lab_two h2]
  obtain ⟨h9, h10⟩ := eq_of_isLawfulBelow_univ_two hQ'
  have hc3 : min (v 3) c = min (w 3) c := by
    rw [hvq 3 (cells.below_mono h m3), hwp 3 m3]; exact hpq ⟨3, m3⟩
  have hc4 : min (v 4) c = min (w 4) c := by
    rw [hvq 4 (cells.below_mono h m4), hwp 4 m4]; exact hpq ⟨4, m4⟩
  refine ⟨fun d ↦ lab (w 3) (w 4) d, hlaw.isLawfulBelow _, fun d ↦ ?_, fun d ↦ ?_⟩
  · change min (lab (w 3) (w 4) d.1) c = min (q d) c
    rw [← hvq d.1 d.2]
    rcases kind_cases d.1 with h0 | h1 | h2
    · rw [lab_zero h0, eq_bot_of_dead hQ' d.2 h0]
    · rw [lab_one h1]
      rcases eq_of_kind_one d.1 h1 with hd | hd <;> rw [hd]
      · exact hc3.symm
      · rw [h9]; exact hc3.symm
    · rw [lab_two h2]
      rcases eq_of_kind_two d.1 h2 with hd | hd <;> rw [hd]
      · exact hc4.symm
      · rw [h10]; exact hc4.symm
  · exact (hwlab d.1 d.2).symm.trans (hwp d.1 d.2)

/-- The rows are bountiful: within a face, below pairs where every cell is dead, and the lift
from `({0, 1}, 2)` to `(univ, 2)`, which copies the two full cells to the gate and the twin. -/
theorem isBountiful_rows : rows.{u}.IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  have hk : X.2 < 4 := by
    have := hX.2.2; have := card_le_univ X.1; simp only [Fintype.card_fin] at this; omega
  rcases case_split X.1 Y.1 hX.1 hY.1 h.1 ⟨X.2, hk⟩ hX.2.1 hX.2.2 with heq | hdead | ⟨h1, h2, h3⟩
  · exact Rows.cappedLift_of_fst_eq _ heq
  · exact cappedLift_of_dead (fun d hd ↦ hdead d hd.1 hd.2) _
  · obtain ⟨X1, X2⟩ := X
    obtain ⟨Y1, Y2⟩ := Y
    simp only at h1 h2 h3
    subst h1 h2 h3
    exact cappedLift_main _

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
  change rowValue s t.1 < _
  unfold rowValue
  split_ifs
  · exact WithBot.bot_lt_coe _
  · exact natCast_lt_omega0_sq 3
  · exact natCast_lt_omega0_sq 2

/-- The rows are consistent: they are `⊥`, `lab 3 2` and `lab 2 3`. -/
theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  change rows.IsLawfulBelow _ (fun t ↦ rows.row s t)
  rcases kind_cases s with h0 | h1 | h2
  · have : (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) = fun _ ↦ ⊥ :=
      funext fun t ↦ rowValue_zero_left h0
    rw [this]; exact Rows.isLawfulBelow_const_bot _
  · have : (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) =
        fun t ↦ lab ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) t.1 :=
      funext fun (t : cells.below (cells.gradedIndex s)) ↦ by
        change rowValue s t.1 = _
        rcases kind_cases t.1 with t0 | t1 | t2
        · rw [rowValue_zero_right t0, lab_zero t0]
        · rw [rowValue_eq (by omega) (by omega) (by omega), lab_one t1]
        · rw [rowValue_ne (by omega) (by omega) (by omega), lab_two t2]
    rw [this]; exact (isLawful_lab sv_three sv_two reads_three_two).isLawfulBelow _
  · have : (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) =
        fun t ↦ lab ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) t.1 :=
      funext fun (t : cells.below (cells.gradedIndex s)) ↦ by
        change rowValue s t.1 = _
        rcases kind_cases t.1 with t0 | t1 | t2
        · rw [rowValue_zero_right t0, lab_zero t0]
        · rw [rowValue_ne (by omega) (by omega) (by omega), lab_one t1]
        · rw [rowValue_eq (by omega) (by omega) (by omega), lab_two t2]
    rw [this]; exact (isLawful_lab sv_two sv_three reads_two_three).isLawfulBelow _

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
  label := lab ⊤ ⊤
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_lab (isSelfVisible_top 2) (isSelfVisible_top 2)
    (reads_self (isSelfVisible_top 2))
  atStage d := by unfold lab; split_ifs <;> simp

/-- **The display is legal.** -/
theorem isLegal_Q (α : Ordinal.{u}) : (Q α).IsLegal :=
  StageType.isLegal_iff.mpr ⟨isConsistent_rows, isBountiful_rows, isComplete_cells⟩

/-- The cells of the display, by their index. -/
def cellQ (α : Ordinal.{u}) (i : Fin 12) : Fin (Q α).card := i

private theorem mem_faces_castSuccEmb (α : Ordinal.{u}) :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ (Q α).toCellScheme.faces := by
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
    lab (⊤ : Label.{u}) ⊤ (Fin.castLE (by decide : 5 ≤ 12) j) =
      GatedExtensionCounterexample.labelling ⊤ ⊤ j := by
  fin_cases j <;> rfl

/-- **The private face of the display is literally the refuting private type `P α`.** -/
theorem restrictFace_Q (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (Q α) = some (GatedExtensionCounterexample.P α) := by
  rw [restrictFace_eq_some_iff]
  refine ⟨mem_faces_castSuccEmb α, ?_⟩
  let e : Fin 5 → Fin (Q α).card := fun i ↦ Fin.castLE (by decide : 5 ≤ 12) i
  have he : StrictMono e := fun _ _ h ↦ h
  have hr : ∀ d, d ∈ Set.range e ↔ d ∈ (Q α).toScheme.visibleCells Fin.castSuccEmb := by
    intro d
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
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
      change rowValue ((Q α).toScheme.cellMap Fin.castSuccEmb s)
        ((Q α).toScheme.cellMap Fin.castSuccEmb t.1) = _
      rw [← key hs.symm, ← key ht.symm]
      exact rows_agree s' t'.1 t'.2
  · change lab ⊤ ⊤ ((Q α).toScheme.cellMap Fin.castSuccEmb i) =
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
  rw [univ_map_extendByLast_emptyRoot]; change _ ∈ Geometry.intervalPlan univ; decide +kernel

/-- The donor: the face `{2}` of the display, one dead cell labelled `⊥`. -/
noncomputable def donor (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (Q α).comap (extendByLast emptyRoot) (mem_faces_extendByLast α)

/-- The empty root is a face of `P α`. -/
theorem mem_faces_emptyRoot (α : Ordinal.{u}) :
    univ.map emptyRoot ∈ (GatedExtensionCounterexample.P α).toCellScheme.faces := by
  change _ ∈ Geometry.intervalPlan univ; decide +kernel

/-- The type of the empty root. -/
noncomputable def root (α : Ordinal.{u}) : StageType.{u} α 0 :=
  (GatedExtensionCounterexample.P α).comap emptyRoot (mem_faces_emptyRoot α)

/-- The donor face of the display is the donor. -/
theorem restrictFace_donor (α : Ordinal.{u}) :
    restrictFace (extendByLast emptyRoot) (Q α) = some (donor α) := restrictFace_of_mem _ _ _

/-- The face of `P α` along the empty root is the type of the empty root. -/
theorem restrictFace_root (α : Ordinal.{u}) :
    restrictFace emptyRoot (GatedExtensionCounterexample.P α) = some (root α) :=
  restrictFace_of_mem _ _ _

/-- The donor restricts to the type of the empty root. -/
theorem restrictFace_donor_castSuccEmb (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (donor α) = some (root α) := by
  rw [restrictFace_trans _ _ _ (restrictFace_donor α), castSuccEmb_trans_extendByLast,
    ← restrictFace_trans _ _ _ (restrictFace_Q α), restrictFace_root]

private theorem range_extendByLast :
    Set.range (extendByLast emptyRoot) = (({2} : Finset (Fin 3)) : Set (Fin 3)) := by
  rw [← univ_map_extendByLast_emptyRoot]; simp

private theorem range_castSuccEmb :
    Set.range (Fin.castSuccEmb : Fin 2 ↪ Fin 3) = (({0, 1} : Finset (Fin 3)) : Set (Fin 3)) := by
  ext x; fin_cases x <;> simp [Fin.ext_iff]

private theorem eq_five_of_visible (α : Ordinal.{u}) (e : Fin (Q α).card)
    (he : e ∈ (Q α).toCellScheme.visible (Set.range (extendByLast emptyRoot))) :
    e = cellQ α 5 := by
  change ((cellScope e : Finset (Fin 3)) : Set (Fin 3)) ⊆ _ at he
  rw [range_extendByLast, coe_subset] at he
  exact eq_five_of_scope e he

/-- The donor is anchored in `P α` below `3`, vacuously: its one cell is labelled `⊥`. -/
theorem isAnchored_donor (α : Ordinal.{u}) :
    (GatedExtensionCounterexample.P α).IsAnchored (3 : Fin 5) (donor α) := by
  refine isAnchored_of_forall_label_eq_bot_or_top _ _ fun j _ ↦ .inl ?_
  change (Q α).label ((Q α).cellMap (extendByLast emptyRoot) j) = ⊥
  have hj := (Q α).cellMap_mem (extendByLast emptyRoot) j
  rw [Scheme.mem_visibleCells] at hj
  rw [eq_five_of_visible α _ hj]
  rfl

/-! ### The coupled gated extension -/

/-- **A coupled gated extension of `P α`** over the empty root with the `⊥` donor: gate `9`,
cap `3`, twin `10`. -/
private noncomputable def E (α : Ordinal.{u}) :
    StageType.CoupledGatedExtension (GatedExtensionCounterexample.P α) emptyRoot (donor α) where
  display := Q α
  isLegal := isLegal_Q α
  restrictFace_castSuccEmb := restrictFace_Q α
  restrictFace_extendByLast := restrictFace_donor α
  gate := cellQ α 9
  cap := cellQ α 3
  gradedIndex_gate := rfl
  gradedIndex_cap := by
    change (cellScope 3, cellGrade 3) = (univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3), 2)
    decide +kernel
  twinsReadGate := fun t _ _ ht htG ↦ by
    have ht' : (cellScope t, cellGrade t) = (cellScope 9, cellGrade 9) := ht
    rcases eq_of_gradedIndex_nine t ht' with h | h
    · exact absurd h htG
    · subst h
      change rowValue 10 3 ≤ rowValue 10 9
      rw [rowValue_ne (s := 10) (t := 3) (by decide) (by decide) (by decide),
        rowValue_ne (s := 10) (t := 9) (by decide) (by decide) (by decide)]
  isGate :=
    { cap_mem := by
        change ((cellScope 3 : Finset (Fin 3)) : Set (Fin 3)) ⊆ Set.range Fin.castSuccEmb
        rw [range_castSuccEmb, coe_subset]; decide
      scope_cap_subset := by change cellScope 3 ⊆ cellScope 9; decide
      grade_cap := rfl
      cap_ne_bot := by change lab ⊤ ⊤ 3 ≠ ⊥; simp [lab, kind]
      le_gate := fun e he ↦ by
        rw [eq_five_of_visible α e he]
        change (cellScope 5, cellGrade 5) ≤ (cellScope 9, cellGrade 9)
        exact ⟨by decide, by decide⟩
      reads := fun e he _ ↦ by
        obtain rfl := eq_five_of_visible α e he
        exact .bot rfl rfl }

/-- **Feasibility of the coupled gate on the refuting private type.**  Over the empty root, with
a legal one-point donor labelled `⊥` (anchored vacuously) and the cap `3`: no gated extension
exists (`GatedExtensionCounterexample.isEmpty_gatedExtension`), a coupled gated extension does,
its cap carries the label of `3`, and its gate has a twin not labelled `⊥`. -/
theorem exists_coupledGatedExtension (α : Ordinal.{u}) :
    ∃ (p : StageType.{u} α 0) (d : StageType.{u} α 1),
      restrictFace emptyRoot (GatedExtensionCounterexample.P α) = some p ∧ d.IsLegal ∧
      restrictFace Fin.castSuccEmb d = some p ∧
      (GatedExtensionCounterexample.P α).IsAnchored (3 : Fin 5) d ∧
      IsEmpty ((GatedExtensionCounterexample.P α).GatedExtension emptyRoot d) ∧
      ∃ E : StageType.CoupledGatedExtension (GatedExtensionCounterexample.P α) emptyRoot d,
        E.display.label E.cap = (GatedExtensionCounterexample.P α).label (3 : Fin 5) ∧
        ∃ t, E.display.toCellScheme.gradedIndex t = (univ, 2) ∧ t ≠ E.gate ∧
          E.display.label t ≠ ⊥ :=
  ⟨root α, donor α, restrictFace_root α, (isLegal_Q α).restrictFace _ (restrictFace_donor α),
    restrictFace_donor_castSuccEmb α, isAnchored_donor α,
    GatedExtensionCounterexample.isEmpty_gatedExtension _ _, E α, rfl, cellQ α 10, rfl,
    fun h ↦ absurd (congrArg Fin.val h) (by change (10 : ℕ) ≠ 9; decide),
    by change lab ⊤ ⊤ 10 ≠ ⊥; simp [lab, kind]⟩

/-- **The gate equals the cap** in every lawful labelling of the rows of the display: the gate
inequality of the coupling holds with equality here. -/
theorem gate_eq_cap (α : Ordinal.{u}) {q : Fin (Q α).card → Label.{u}}
    (hq : (Q α).rows.IsLawful q) : q (cellQ α 9) = q (cellQ α 3) :=
  (eq_of_isLawfulBelow_univ_two (hq.isLawfulBelow ((univ : Finset (Fin 3)), 2))).1

/-! ### The exact input of the refutation -/

/-- The donor face of the refutation: the face `{0}` of `P α`. -/
def g₁ : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

/-- The face `{0}` is a face of `P α`. -/
theorem mem_faces_g₁ (α : Ordinal.{u}) :
    univ.map g₁ ∈ (GatedExtensionCounterexample.P α).toCellScheme.faces := by
  change _ ∈ Geometry.intervalPlan univ; decide +kernel

private theorem visible_extendByLast_iff : ∀ d : Fin 12,
    cellScope d ⊆ univ.map (extendByLast emptyRoot) ↔ d = 5 := by
  rw [univ_map_extendByLast_emptyRoot]; decide +kernel

private theorem visible_g₁_iff : ∀ d : Fin 5,
    GatedExtensionCounterexample.cellScope d ⊆ univ.map g₁ ↔ d = 0 := by decide +kernel

private theorem scope_agree_donor : ∀ x : Fin 1,
    extendByLast emptyRoot x ∈ cellScope 5 ↔ g₁ x ∈ GatedExtensionCounterexample.cellScope 0 := by
  decide +kernel

private theorem rowP_dead : ∀ s : Fin 5, s ≠ 3 → s ≠ 4 →
    ∀ t : GatedExtensionCounterexample.cells.below
      (GatedExtensionCounterexample.cells.gradedIndex s),
      GatedExtensionCounterexample.rows.{u}.row s t = ⊥ := by
  intro s h3 h4 t
  obtain ⟨t, ht⟩ := t
  revert ht h3 h4
  fin_cases s <;> intro h3 h4 ht <;> first | rfl | exact absurd rfl h3 | exact absurd rfl h4

/-- **The donor is the donor of the refutation**: the face `{2}` of the display is literally the
face `{0}` of `P α`. -/
theorem donor_eq (α : Ordinal.{u}) :
    donor α = (GatedExtensionCounterexample.P α).comap g₁ (mem_faces_g₁ α) := by
  let e₁ : Fin 1 → Fin (Q α).card := fun _ ↦ cellQ α 5
  let e₂ : Fin 1 → Fin (GatedExtensionCounterexample.P α).card := fun _ ↦ (0 : Fin 5)
  have he₁ : StrictMono e₁ := fun a b h ↦
    absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl _)
  have he₂ : StrictMono e₂ := fun a b h ↦
    absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl _)
  have hr₁ : ∀ d, d ∈ Set.range e₁ ↔ d ∈ (Q α).toScheme.visibleCells (extendByLast emptyRoot) := by
    intro d
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
    change _ ↔ cellScope d ⊆ _
    rw [visible_extendByLast_iff d]
    exact ⟨by rintro ⟨i, rfl⟩; rfl, fun h ↦ ⟨0, h.symm⟩⟩
  have hr₂ : ∀ d, d ∈ Set.range e₂ ↔
      d ∈ (GatedExtensionCounterexample.P α).toScheme.visibleCells g₁ := by
    intro d
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
    change _ ↔ GatedExtensionCounterexample.cellScope d ⊆ _
    rw [visible_g₁_iff d]
    exact ⟨by rintro ⟨i, rfl⟩; rfl, fun h ↦ ⟨0, h.symm⟩⟩
  have hc₁ := (Q α).toScheme.card_visibleCells_eq_of_strictMono (extendByLast emptyRoot) he₁ hr₁
  have hc₂ := (GatedExtensionCounterexample.P α).toScheme.card_visibleCells_eq_of_strictMono g₁
    he₂ hr₂
  have key₁ : ∀ (j : Fin ((Q α).toScheme.comap (extendByLast emptyRoot)).card),
      (Q α).toScheme.cellMap (extendByLast emptyRoot) j = cellQ α 5 := fun j ↦
    ((Q α).toScheme.cellMap_eq_of_strictMono (extendByLast emptyRoot) he₁ hr₁
      (i := 0) (j := j) (by
        have h : (j : ℕ) < 1 := lt_of_lt_of_eq j.2 hc₁
        rw [Fin.val_zero]; omega)).symm
  have key₂ : ∀ (j : Fin ((GatedExtensionCounterexample.P α).toScheme.comap g₁).card),
      (GatedExtensionCounterexample.P α).toScheme.cellMap g₁ j = (0 : Fin 5) := fun j ↦
    ((GatedExtensionCounterexample.P α).toScheme.cellMap_eq_of_strictMono g₁ he₂ hr₂
      (i := 0) (j := j) (by
        have h : (j : ℕ) < 1 := lt_of_lt_of_eq j.2 hc₂
        rw [Fin.val_zero]; omega)).symm
  refine StageType.ext ?_ (fun i j _ ↦ ?_)
  · rw [donor, StageType.comap_toScheme, StageType.comap_toScheme]
    refine Scheme.ext (hc₁.trans hc₂.symm) ?_ ?_ (fun k i _ ↦ ?_) (fun k i _ ↦ ?_)
      (fun s s' t t' _ _ ↦ ?_)
    · rw [Scheme.comap_ground, Scheme.comap_ground]
      ext x
      rw [Finset.mem_preimage, Finset.mem_preimage, (Q α).isWellFormed.ground_eq,
        (GatedExtensionCounterexample.P α).isWellFormed.ground_eq]
      simp
    · ext C
      rw [Scheme.mem_comap_faces, Scheme.mem_comap_faces]
      change C.map _ ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) ↔
        C.map _ ∈ Geometry.intervalPlan (univ : Finset (Fin 2))
      revert C; decide +kernel
    · rw [Scheme.comap_scope, Scheme.comap_scope, key₁, key₂]
      ext x
      rw [Finset.mem_preimage, Finset.mem_preimage]
      exact scope_agree_donor x
    · rw [Scheme.comap_grade, Scheme.comap_grade, key₁, key₂]
      rfl
    · rw [Scheme.comap_row, Scheme.comap_row]
      change rowValue ((Q α).toScheme.cellMap (extendByLast emptyRoot) s)
          ((Q α).toScheme.cellMap (extendByLast emptyRoot) t.1) = _
      rw [key₁ s]
      exact (rowValue_zero_left (s := (5 : Fin 12)) (by decide)).trans
        (rowP_dead _ (by rw [key₂ s']; decide) (by rw [key₂ s']; decide) _).symm
  · change (Q α).label ((Q α).toScheme.cellMap (extendByLast emptyRoot) i) =
      (GatedExtensionCounterexample.P α).label
        ((GatedExtensionCounterexample.P α).toScheme.cellMap g₁ j)
    rw [key₁ i, key₂ j]
    rfl

/-- **The coupled gated pinned extension property holds at the input that refutes the gated
pinned extension property** (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`: the
private type `P α`, the empty root, the donor `P α|{0}`, the cap `3`).  This is the only input at
which `StageType.HasCoupledGatedPinnedExtensions` is proved. -/
theorem exists_coupledGatedExtension_refutingInput (α : Ordinal.{u}) :
    ∃ E : StageType.CoupledGatedExtension (GatedExtensionCounterexample.P α) emptyRoot
        ((GatedExtensionCounterexample.P α).comap g₁ (mem_faces_g₁ α)),
      E.display.label E.cap = (GatedExtensionCounterexample.P α).label (3 : Fin 5) :=
  donor_eq α ▸ ⟨E α, rfl⟩

/-! ### The twin counterexamples of `GateExamples` are not coupled -/

/-- **The twin of `GateExamples.twin_bottom_gate` and `GateExamples.twin_small_gate` is not
coupled to the gate**: it reads the cap at `⊤` and the gate at `3`.  Those counterexamples break
the gate inequality, which the coupling would give. -/
theorem not_twinsReadGate_twin :
    ¬ GateExamples.twinRows.TwinsReadGate (3 : Fin 5) (1 : Fin 5) := by
  intro h
  have := h 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide)
  change (⊤ : Label.{0}) ≤ 3 at this
  have h3 : (3 : Label.{0}) = ((3 : Ordinal.{0}) : Label.{0}) := rfl
  rw [h3] at this
  exact (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (3 : Ordinal.{0})))) this

end VaughtConjecture.CoupledGateExamples
