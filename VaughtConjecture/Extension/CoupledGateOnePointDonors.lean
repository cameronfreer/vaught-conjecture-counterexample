/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.CoupledGateInstance

/-!
# Coupled gated extensions of `P α` for every one-point donor

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate); the coupled
gated extensions of `VaughtConjecture.Extension.GatedExtension`.

**The theorem** (`coupledGatedPinnedExtension_P`).  The body of the coupled gated pinned extension
property (`StageType.HasCoupledGatedPinnedExtensions`) holds at the private type
`GatedExtensionCounterexample.P α` for every other input: every root `f` (the arities force the
empty root), every legal one-point donor `d`, every cell `C` of `P α` of graded index `(univ, 2)`,
under anchoring.  This establishes the property at these inputs only (the private type `P α`,
every root, every donor); in general it is false at every stage above `1`
(`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`, at a private type with
a proper anchor below the cap, which `P α` does not have).  Anchoring forces every label of `d` into
`{⊥, ⊤}` (`labels_mem_bot_top`): the labels of `P α` are `⊥` and `⊤`, fixed by visibility
replacement.

**The display** (`display`).  On three points with the interval plan, for a donor with `k` cells
(the cells `Cell k`, enumerated by `toFin`): the five cells of `P α`, first and in order; the
donor cells `don 0 j` at `({2}, 1)`, next and in order, so that the donor face is literally `d`,
with copies `don 1 j` at `({1, 2}, 1)` and `don 2 j` at `(univ, 1)`; a dead cell at
`({1, 2}, 2)`; the full cells `G₁`, `G₂` at `(univ, 2)`; a dead cell at `(univ, 3)`.  The rows are
those of `P α` on the private cells and those of `d` between donor cells; the full cells read
the private cells and each other by kinds (`3` at equal kinds, `2` otherwise) and a donor cell
at `3` or `⊥` as `d` labels it `⊤` or `⊥` (`gateRead`); every other entry is `⊥`.  The labels:
those of `P α` and of `d`, `⊤` at `G₁`, `G₂`, `⊥` at the dead cells.

**Lawful labellings** (`isLawful_iff`, `lawfulData_of_isLawfulBelow`): the labellings
`lab a b ρ` with `(a, b)` read by the private rows and copied to `G₁`, `G₂`, `ρ` lawful for the
rows of `d` (`donorLawful_iff`) and copied to every level, and the coupling `a, b ≤ ρ j` where
`d.label j = ⊤`, `min (ρ j) a = min (ρ j) b = ⊥` where `d.label j = ⊥`.

**Legality** (`isLegal_display`).  Coded and consistent rows, a cell at every graded face, and
bountifulness at a fixed grade (`Rows.isBountiful_iff_forall_cappedLift_fst`), in five cases:
lifts within a face; at grade `1` away from the new point, where every cell is dead; the private
coatom lift `({0, 1}, 2)` to `(univ, 2)` (keep the prescribed pair, copy it to `G₁`, `G₂`, and
take the labels of `d` on the donor cells if the cap is `⊥`, the ambient donor values raised to
`⊤` at or above the cap otherwise, `Label.isWitness_raise`); the forcing lift `({1, 2}, 2)` to
`(univ, 2)` (keep the prescribed donor values, cap the ambient pair at the cap); and the lifts at
grade `1` from a face containing the new point (copy the prescribed donor values).

**The coupled gated extensions** (`extension`): the cap `C₁` with the gate `G₁`, or `C₂` with
`G₂`.  The twin reads the cap and the gate both at `2`; the gate reads a donor cell labelled `⊥`
at `⊥` and a donor cell labelled `⊤` at `3`, as it reads the cap.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.CoupledGateOnePointDonors

open Finset Label CellScheme StageType

/-! ### The cells -/

/-- The cells of the display over a donor with `k` cells. -/
inductive Cell (k : ℕ) where
  /-- The cells of the private type, in their order. -/
  | priv (i : Fin 5)
  /-- The copy at level `l` of the donor cell `j`: scope `{2}`, `{1, 2}` or `univ`, grade `1`. -/
  | don (l : Fin 3) (j : Fin k)
  /-- The dead cell of graded index `({1, 2}, 2)`. -/
  | side
  /-- The full cells `G₁` (`i = 0`) and `G₂` (`i = 1`), of graded index `(univ, 2)`. -/
  | full (i : Fin 2)
  /-- The dead cell of graded index `(univ, 3)`. -/
  | apex
  deriving DecidableEq

variable {k : ℕ}

/-- The cells as a sum: the private cells, the donor cells with their levels, and the four cells
`side`, `full 0`, `full 1`, `apex`. -/
def Cell.toSum : Cell k → Fin 5 ⊕ (Fin 3 × Fin k) ⊕ Fin 4
  | .priv i => .inl i
  | .don l j => .inr (.inl (l, j))
  | .side => .inr (.inr 0)
  | .full i => .inr (.inr i.succ.castSucc)
  | .apex => .inr (.inr 3)

/-- The cells are equivalent to the sum `Fin 5 ⊕ (Fin 3 × Fin k) ⊕ Fin 4`. -/
def Cell.equivSum : Cell k ≃ Fin 5 ⊕ (Fin 3 × Fin k) ⊕ Fin 4 where
  toFun := Cell.toSum
  invFun
    | .inl i => .priv i
    | .inr (.inl (l, j)) => .don l j
    | .inr (.inr t) => if t = 0 then .side else if t = 3 then .apex else
        .full (if t = 1 then 0 else 1)
  left_inv c := by rcases c with _ | _ | _ | i | _ <;> (try fin_cases i) <;> rfl
  right_inv x := by rcases x with _ | ⟨_, _⟩ | t <;> (try fin_cases t) <;> rfl

/-- There are finitely many cells. -/
instance : Finite (Cell k) := Finite.of_equiv _ Cell.equivSum.symm

/-- The enumeration of the cells: the private cells first (`priv i ↦ i`), then the donor cells
of level `0` (`don 0 j ↦ 5 + j`), the other donor cells, and the four remaining cells. -/
def toFin : Cell k ≃ Fin (5 + (3 * k + 4)) :=
  Cell.equivSum.trans <| (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

private theorem val_toFin_priv (i : Fin 5) : (toFin (.priv i : Cell k) : ℕ) = i := by
  simp [toFin, Cell.equivSum, Cell.toSum]

private theorem val_toFin_don (j : Fin k) : (toFin (.don 0 j : Cell k) : ℕ) = 5 + j := by
  simp [toFin, Cell.equivSum, Cell.toSum]

/-! ### The scheme -/

/-- The scopes of the private cells, on the points `0` and `1`. -/
def privScope : Fin 5 → Finset (Fin 3) := ![{0}, {1}, {0, 1}, {0, 1}, {0, 1}]

/-- The grades of the private cells. -/
def privGrade : Fin 5 → ℕ := ![1, 1, 1, 2, 2]

/-- The kinds of the private cells: `0` (dead), `1` (`C₁`) and `2` (`C₂`). -/
def privKind : Fin 5 → ℕ := ![0, 0, 0, 1, 2]

/-- The scopes of the donor cells at the three levels. -/
def levelScope : Fin 3 → Finset (Fin 3) := ![{2}, {1, 2}, univ]

/-- The scope of a cell. -/
def cellScope : Cell k → Finset (Fin 3)
  | .priv i => privScope i
  | .don l _ => levelScope l
  | .side => {1, 2}
  | .full _ => univ
  | .apex => univ

/-- The grade of a cell. -/
def cellGrade : Cell k → ℕ
  | .priv i => privGrade i
  | .don _ _ => 1
  | .side => 2
  | .full _ => 2
  | .apex => 3

/-- The kind of a cell: `0` (dead), `1` (`C₁` and `G₁`), `2` (`C₂` and `G₂`), `3` (donor). -/
def kind : Cell k → ℕ
  | .priv i => privKind i
  | .don _ _ => 3
  | .side => 0
  | .full i => (i : ℕ) + 1
  | .apex => 0

/-- The cells, on the interval plan of the three points. -/
def cells : CellScheme (Cell k) (Fin 3) :=
  ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

/-- The row values between cells that are not donor cells: `⊥` at or from a dead cell, `3`
between equal kinds, `2` between the kinds `1` and `2`. -/
noncomputable def kindRow (a b : ℕ) : Label.{u} :=
  if a = 0 ∨ b = 0 ∨ a = 3 ∨ b = 3 then ⊥
  else if a = b then ((3 : ℕ) : Label.{u}) else ((2 : ℕ) : Label.{u})

variable {α : Ordinal.{u}} (d : StageType.{u} α 1)

open Classical in
/-- The rows of the donor, as a function of two cells. -/
noncomputable def donorRow (i j : Fin d.card) : Label.{u} :=
  if h : j ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex i) then d.rows.row i ⟨j, h⟩
  else ⊥

/-- How the full cells read the donor cell `j`: `⊥` if the donor labels it `⊥`, `3`
otherwise. -/
noncomputable def gateRead (j : Fin d.card) : Label.{u} :=
  if d.label j = ⊥ then ⊥ else ((3 : ℕ) : Label.{u})

/-- The row values: the rows of the donor between donor cells, `gateRead` from the full cells
to the donor cells, `kindRow` otherwise. -/
noncomputable def rowValue : Cell d.card → Cell d.card → Label.{u}
  | .don _ i, .don _ j => donorRow d i j
  | s, .don _ j => if kind s = 1 ∨ kind s = 2 then gateRead d j else ⊥
  | s, t => kindRow (kind s) (kind t)

/-- The rows of the display. -/
noncomputable def cellRows : (cells (k := d.card)).Rows.{u} := ⟨fun s t ↦ rowValue d s t.1⟩

/-- The labelling with `a` at the kind `1`, `b` at the kind `2`, `ρ j` at every copy of the
donor cell `j`, and `⊥` at the dead cells. -/
noncomputable def lab (a b : Label.{u}) (ρ : Fin k → Label.{u}) : Cell k → Label.{u}
  | .don _ j => ρ j
  | c => if kind c = 1 then a else if kind c = 2 then b else ⊥

/-! ### Finite facts -/

section Facts

variable {c s t : Cell k}

private theorem privKind_cases : ∀ i, privKind i = 0 ∨ privKind i = 1 ∨ privKind i = 2 := by
  decide

private theorem privGrade_of_kind : ∀ i, privKind i ≠ 0 → privGrade i = 2 ∧
    privScope i = {0, 1} := by decide

private theorem privKind_of_grade : ∀ i, privGrade i ≤ 1 → privKind i = 0 := by decide

private theorem privKind_one_two : ∀ i, (privKind i = 1 → i = 3) ∧ (privKind i = 2 → i = 4) := by
  decide

private theorem privScope_ne_univ : ∀ i, ¬ univ ⊆ privScope i := by decide

private theorem two_notMem_privScope : ∀ i, ¬ privScope i ⊆ {2} ∧ 2 ∉ privScope i := by decide

private theorem two_mem_levelScope : ∀ l, 2 ∈ levelScope l := by decide

private theorem privGrade_le_two : ∀ i, privGrade i ≤ 2 := by decide

private theorem levelScope_eq_zero : ∀ l, levelScope l ⊆ {2} → l = 0 := by decide

private theorem kind_cases (c : Cell k) : kind c = 0 ∨ kind c = 1 ∨ kind c = 2 ∨ kind c = 3 := by
  rcases c with i | _ | _ | i | _ <;> simp [kind] <;> try omega
  rcases privKind_cases i with h | h | h <;> simp [h]

private theorem kind_eq_three (h : kind c = 3) : ∃ l j, c = .don l j := by
  rcases c with i | ⟨l, j⟩ | _ | i | _ <;> simp [kind] at h <;> try omega
  · rcases privKind_cases i with h' | h' | h' <;> omega
  · exact ⟨l, j, rfl⟩

private theorem grade_of_kind_one_two (h : kind c = 1 ∨ kind c = 2) : cellGrade c = 2 := by
  rcases c with i | _ | _ | _ | _
  · exact (privGrade_of_kind i (by simp only [kind] at h; omega)).1
  all_goals simp [kind, cellGrade] at h ⊢

private theorem kind_of_grade_le_one (h : cellGrade c ≤ 1) : kind c = 0 ∨ kind c = 3 := by
  rcases c with i | _ | _ | _ | _
  · exact .inl (privKind_of_grade i h)
  all_goals simp [kind, cellGrade] at h ⊢

private theorem kind_of_scope_one_two (h : cellScope c ⊆ {1, 2}) : kind c = 0 ∨ kind c = 3 := by
  rcases c with i | _ | _ | i | _ <;> simp [kind, cellScope] at h ⊢ <;> try omega
  · by_contra hne
    rw [(privGrade_of_kind i (by omega)).2] at h
    exact absurd h (by decide)
  · exact absurd h (by decide)

private theorem eq_of_kind_one (h : kind c = 1) : c = .priv 3 ∨ c = .full 0 := by
  rcases c with i | _ | _ | i | _ <;> simp [kind] at h <;> try omega
  · rw [(privKind_one_two i).1 h]; exact .inl rfl
  · fin_cases i <;> simp_all

private theorem eq_of_kind_two (h : kind c = 2) : c = .priv 4 ∨ c = .full 1 := by
  rcases c with i | _ | _ | i | _ <;> simp [kind] at h <;> try omega
  · rw [(privKind_one_two i).2 h]; exact .inl rfl
  · fin_cases i <;> simp_all

private theorem eq_full_of_gradedIndex (h : cellScope c = univ) (hg : cellGrade c = 2) :
    c = .full 0 ∨ c = .full 1 := by
  rcases c with i | _ | _ | i | _ <;> simp [cellScope, cellGrade] at h hg <;> try omega
  · exact absurd h.ge (privScope_ne_univ i)
  · exact absurd h (by decide)
  · fin_cases i <;> simp

private theorem eq_don_of_gradedIndex {l : Fin 3} (h : cellScope c = levelScope l)
    (hg : cellGrade c = 1) : ∃ l' j', c = .don l' j' := by
  rcases c with i | ⟨l', j⟩ | _ | _ | _ <;> simp [cellScope, cellGrade] at h hg <;> try omega
  · exact absurd (h ▸ two_mem_levelScope l) (two_notMem_privScope i).2
  · exact ⟨l', j, rfl⟩

private theorem kind_dead_of_two_notMem {A : Finset (Fin 3)} (hA : 2 ∉ A) (h : cellScope c ⊆ A)
    (hg : cellGrade c ≤ 1) : kind c = 0 := by
  rcases c with i | ⟨l, j⟩ | _ | _ | _
  · exact privKind_of_grade i hg
  · exact absurd (h (two_mem_levelScope l)) hA
  all_goals simp [cellGrade] at hg

private theorem eq_don_zero_of_scope (h : cellScope c ⊆ {2}) : ∃ j, c = .don 0 j := by
  rcases c with i | ⟨l, j⟩ | _ | _ | _ <;> simp only [cellScope] at h
  · exact absurd h (two_notMem_privScope i).1
  · rw [levelScope_eq_zero l h]; exact ⟨j, rfl⟩
  all_goals exact absurd h (by decide)

private theorem eq_priv_of_scope (h : cellScope c ⊆ {0, 1}) : ∃ i, c = .priv i := by
  rcases c with i | ⟨l, j⟩ | _ | _ | _ <;> simp only [cellScope] at h
  · exact ⟨i, rfl⟩
  · exact absurd (h (two_mem_levelScope l)) (by decide)
  all_goals exact absurd h (by decide)

private theorem levelScope_zero_subset (l : Fin 3) : levelScope 0 ⊆ levelScope l := by
  revert l; decide

end Facts

/-! ### Row values and labels -/

section Values

variable {a b : Label.{u}} {ρ : Fin d.card → Label.{u}} {c s t : Cell d.card}

private theorem kindRow_bot {m n : ℕ} (h : m = 0 ∨ n = 0 ∨ m = 3 ∨ n = 3) :
    kindRow.{u} m n = ⊥ := by
  unfold kindRow; rw [ite_eq_left (by omega)]

private theorem kindRow_three {m n : ℕ} (hm : m = 1 ∨ m = 2) (h : m = n) :
    kindRow.{u} m n = ((3 : ℕ) : Label.{u}) := by
  unfold kindRow; rw [ite_eq_right (by omega), ite_eq_left h]

private theorem kindRow_two {m n : ℕ} (hm : m = 1 ∨ m = 2) (hn : n = 1 ∨ n = 2) (h : m ≠ n) :
    kindRow.{u} m n = ((2 : ℕ) : Label.{u}) := by
  unfold kindRow; rw [ite_eq_right (by omega), ite_eq_right h]

private theorem rowValue_kind (ht : kind t ≠ 3) : rowValue d s t = kindRow (kind s) (kind t) := by
  rcases s with i | ⟨l, j⟩ | _ | i | _ <;> rcases t with i' | ⟨l', j'⟩ | _ | i' | _ <;>
    first | rfl | exact absurd rfl ht

private theorem rowValue_don_right (hs : kind s ≠ 3) {l : Fin 3} {j : Fin d.card} :
    rowValue d s (.don l j) = if kind s = 1 ∨ kind s = 2 then gateRead d j else ⊥ := by
  rcases s with i | ⟨l, j⟩ | _ | i | _ <;> first | rfl | exact absurd rfl hs

private theorem rowValue_three (hs : kind s = 1 ∨ kind s = 2) (h : kind s = kind t) :
    rowValue d s t = ((3 : ℕ) : Label.{u}) := by
  rw [rowValue_kind d (by omega), kindRow_three hs h]

private theorem rowValue_two (hs : kind s = 1 ∨ kind s = 2) (ht : kind t = 1 ∨ kind t = 2)
    (h : kind s ≠ kind t) : rowValue d s t = ((2 : ℕ) : Label.{u}) := by
  rw [rowValue_kind d (by omega), kindRow_two hs ht h]

private theorem rowValue_dead (h : kind s = 0 ∨ kind t = 0) : rowValue d s t = ⊥ := by
  by_cases ht : kind t = 3
  · obtain ⟨l, j, rfl⟩ := kind_eq_three ht
    rw [rowValue_don_right d (by omega), ite_eq_right (by omega)]
  · rw [rowValue_kind d ht, kindRow_bot (by omega)]

private theorem lab_of_kind {ρ : Fin k → Label.{u}} {c : Cell k} (hc : kind c ≠ 3) :
    lab a b ρ c = if kind c = 1 then a else if kind c = 2 then b else ⊥ := by
  rcases c with i | ⟨l, j⟩ | _ | i | _ <;> first | rfl | exact absurd rfl hc

private theorem lab_zero {ρ : Fin k → Label.{u}} {c : Cell k} (h : kind c = 0) :
    lab a b ρ c = ⊥ := by
  rw [lab_of_kind (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem lab_one {ρ : Fin k → Label.{u}} {c : Cell k} (h : kind c = 1) :
    lab a b ρ c = a := by
  rw [lab_of_kind (by omega), ite_eq_left h]

private theorem lab_two {ρ : Fin k → Label.{u}} {c : Cell k} (h : kind c = 2) :
    lab a b ρ c = b := by
  rw [lab_of_kind (by omega), ite_eq_right (by omega), ite_eq_left h]

private theorem two_lt_three : ((2 : ℕ) : Label.{u}) < ((3 : ℕ) : Label.{u}) := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_lt_coe, ← WithTop.coe_natCast,
    ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  exact Nat.cast_lt.mpr (by decide)

private theorem sv_two : IsSelfVisible 2 ((2 : ℕ) : Label.{u}) := by simp

private theorem sv_three : IsSelfVisible 2 ((3 : ℕ) : Label.{u}) := by simp

private theorem sv_three_one : IsSelfVisible 1 ((3 : ℕ) : Label.{u}) := by simp

private theorem topShifter_natCast (n : ℕ) : topShifter ((n : ℕ) : Label.{u}) = ⊤ := by
  simp [topShifter]

end Values

/-! ### Lawful labellings -/

/-- A labelling `ρ` of the donor cells is **lawful for the rows of the donor**: every value is
self-visible at the grade `1`, and the row of every donor cell `j` transforms, at the grade `1`,
to `j' ↦ min (ρ j') (ρ j)`.  For a donor on one point this is lawfulness for its rows
(`donorLawful_iff`). -/
def DonorLawful (ρ : Fin d.card → Label.{u}) : Prop :=
  (∀ j, IsSelfVisible 1 (ρ j)) ∧
    ∀ j, TransformsTo (fun _ : Fin d.card ↦ 1) (donorRow d j) (fun j' ↦ min (ρ j') (ρ j))

/-- The two readings that make a labelling local at the full cells on the private points: the
row of `C₁` reads `(3, 2)` to `(a, min b a)`, the row of `C₂` reads `(2, 3)` to `(min a b, b)`. -/
def Reads (a b : Label.{u}) : Prop :=
  (∃ g σ, IsWitness g σ ∧ a = min (σ ((3 : ℕ) : Label.{u})) (g 2) ∧
      min b a = min (σ ((2 : ℕ) : Label.{u})) (g 2)) ∧
  (∃ g σ, IsWitness g σ ∧ min a b = min (σ ((2 : ℕ) : Label.{u})) (g 2) ∧
      b = min (σ ((3 : ℕ) : Label.{u})) (g 2))

/-- **The data of a lawful labelling** `lab a b ρ`: `a` and `b` self-visible at `2` and read by
the private rows, `ρ` lawful for the rows of the donor, and the coupling: at every donor cell
not labelled `⊥` the value of `ρ` bounds `a` and `b`, and at every donor cell labelled `⊥` it
meets `a` and `b` at `⊥`. -/
structure LawfulData (a b : Label.{u}) (ρ : Fin d.card → Label.{u}) : Prop where
  /-- The value at the kind `1` is self-visible at `2`. -/
  sv_a : IsSelfVisible 2 a
  /-- The value at the kind `2` is self-visible at `2`. -/
  sv_b : IsSelfVisible 2 b
  /-- The private rows read the pair. -/
  reads : Reads a b
  /-- The donor values are lawful for the rows of the donor. -/
  donorLawful : DonorLawful d ρ
  /-- The donor cells not labelled `⊥` bound the pair. -/
  le_of_ne_bot : ∀ j, d.label j ≠ ⊥ → a ≤ ρ j ∧ b ≤ ρ j
  /-- The donor cells labelled `⊥` meet the pair at `⊥`. -/
  min_eq_bot : ∀ j, d.label j = ⊥ → min (ρ j) a = ⊥ ∧ min (ρ j) b = ⊥

private theorem topWitness {K : ℕ} {a : Label.{u}} (ha : IsSelfVisible K a) :
    IsWitness (constStepSuppressor K a) topShifter :=
  isWitness_topShifter (antitone_constStepSuppressor _ _) (isSelfVisible_constStepSuppressor ha)

private theorem reads_self {a : Label.{u}} (ha : IsSelfVisible 2 a) : Reads a a :=
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

/-- Capping both values at a label self-visible at `2` keeps the readings. -/
private theorem Reads.min {a b c : Label.{u}} (h : Reads a b) (hc : IsSelfVisible 2 c) :
    Reads (min a c) (min b c) := by
  obtain ⟨⟨g, σ, hw, ea, eb⟩, ⟨g', σ', hw', ec, ed⟩⟩ := h
  refine ⟨⟨_, σ, hw.cap hc, ?_, ?_⟩, ⟨_, σ', hw'.cap hc, ?_, ?_⟩⟩ <;>
    simp only [le_refl, ite_true]
  · rw [ea, min_assoc]
  · rw [← min_assoc (σ _) (g 2) c, ← eb, min_min_min_comm, min_self]
  · rw [← min_assoc (σ' _) (g' 2) c, ← ec, min_min_min_comm, min_self]
  · rw [ed, min_assoc]

/-- Locality at a cell of kind `1` or `2` from a reading `(g, σ)` of the cell's own label `a`:
the suppressor capped at `a` (`IsWitness.cap`) reads the donor cells at `a` or `⊥`. -/
private theorem locality_full {a b' : Label.{u}} {ρ : Fin d.card → Label.{u}}
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    (ha2 : IsSelfVisible 2 a) (ha : a = min (σ ((3 : ℕ) : Label.{u})) (g 2))
    (hb : min b' a = min (σ ((2 : ℕ) : Label.{u})) (g 2))
    (hle : ∀ j, d.label j ≠ ⊥ → a ≤ ρ j) (hbot : ∀ j, d.label j = ⊥ → min (ρ j) a = ⊥)
    (s : Cell d.card) (own other : ℕ) (hs : kind s = own) (hown : own = 1 ∨ own = 2)
    (hother : other = 3 - own) (f : Cell d.card → Label.{u})
    (hfo : ∀ c, kind c = own → f c = a) (hft : ∀ c, kind c = other → f c = b')
    (hf3 : ∀ l j, f (.don l j) = ρ j) (hf0 : ∀ c, kind c = 0 → f c = ⊥) :
    TransformsTo (fun c : cells.below (cells.gradedIndex s) ↦ cells.grade c.1)
      ((cellRows d).row s) (fun c ↦ min (f c) (f s)) := by
  have hfs : f s = a := hfo s hs
  have hag : a ≤ g 2 := ha ▸ min_le_right _ _
  have has : a ≤ σ ((3 : ℕ) : Label.{u}) := ha ▸ min_le_left _ _
  have hsg : cellGrade s = 2 := grade_of_kind_one_two (by omega)
  refine ⟨_, σ, hw.cap ha2, fun c ↦ ?_⟩
  have hc2 : cellGrade c.1 ≤ 2 := hsg ▸ c.2.2
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (f c.1) (f s) = min (σ (rowValue d s c.1))
    (if cellGrade c.1 ≤ 2 then min (g (cellGrade c.1)) a else ⊥)
  rw [hfs, ite_eq_left hc2]
  rcases kind_cases c.1 with h0 | h1 | h2 | h3
  · rw [hf0 _ h0, rowValue_dead d (.inr h0), hw.map_bot, min_eq_left bot_le,
      min_eq_left bot_le]
  · rw [grade_of_kind_one_two (.inl h1)]
    rcases hown with rfl | rfl
    · rw [hfo _ h1, rowValue_three d (by omega) (by omega), min_self, ← min_assoc, ← ha,
        min_self]
    · rw [hft _ (by omega), rowValue_two d (by omega) (by omega) (by omega), ← min_assoc, ← hb,
        min_assoc, min_self]
  · rw [grade_of_kind_one_two (.inr h2)]
    rcases hown with rfl | rfl
    · rw [hft _ (by omega), rowValue_two d (by omega) (by omega) (by omega), ← min_assoc, ← hb,
        min_assoc, min_self]
    · rw [hfo _ h2, rowValue_three d (by omega) (by omega), min_self, ← min_assoc, ← ha,
        min_self]
  · obtain ⟨l, j, hc⟩ := kind_eq_three h3
    rw [hc, hf3, rowValue_don_right d (by omega), ite_eq_left (by omega)]
    change min (ρ j) a = min (σ (gateRead d j)) (min (g 1) a)
    have hg1 : a ≤ g 1 := hag.trans (hw.antitone (by omega))
    unfold gateRead
    split_ifs with hl
    · rw [hbot j hl, hw.map_bot, min_eq_left bot_le]
    · rw [min_eq_right (hle j hl), min_eq_right hg1, min_eq_right has]

/-- Locality at a copy of the donor cell `j`, from the locality of the donor rows at `j`. -/
private theorem locality_don {a b : Label.{u}} {ρ : Fin d.card → Label.{u}} {l : Fin 3}
    {j : Fin d.card}
    (hρ : TransformsTo (fun _ : Fin d.card ↦ 1) (donorRow d j) (fun j' ↦ min (ρ j') (ρ j))) :
    TransformsTo (fun c : cells.below (cells.gradedIndex (.don l j)) ↦ cells.grade c.1)
      ((cellRows d).row (.don l j)) (fun c ↦ min (lab a b ρ c) (lab a b ρ (.don l j))) := by
  obtain ⟨g, σ, hw, heq⟩ := hρ
  refine ⟨g, σ, hw, fun c ↦ ?_⟩
  have hc1 : cellGrade c.1 ≤ 1 := c.2.2
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (lab a b ρ c.1) (ρ j) = min (σ (rowValue d (.don l j) c.1)) (g (cellGrade c.1))
  rcases kind_of_grade_le_one hc1 with h0 | h3
  · rw [lab_zero h0, rowValue_dead d (.inr h0), hw.map_bot, min_eq_left bot_le,
      min_eq_left bot_le]
  · obtain ⟨l', j', hc⟩ := kind_eq_three h3
    rw [hc]
    exact heq j'

/-- A partner for availability: a cell with the graded index of `t` carrying the label of `s` in
every labelling `lab a b ρ`, unless `s` is dead. -/
private theorem exists_partner (s t : Cell k) (hst : cellScope s ⊆ cellScope t)
    (hg : cellGrade s = cellGrade t) :
    ∃ u, cellScope u = cellScope t ∧ cellGrade u = cellGrade t ∧
      (kind s = 0 ∨ ∀ (a b : Label.{u}) (ρ : Fin k → Label.{u}), lab a b ρ u = lab a b ρ s) := by
  by_cases h0 : kind s = 0
  · exact ⟨t, rfl, rfl, .inl h0⟩
  have hsame : ∀ u : Cell k, kind u = kind s → kind s ≠ 3 →
      ∀ (a b : Label.{u}) (ρ : Fin k → Label.{u}), lab a b ρ u = lab a b ρ s :=
    fun u hu hs3 a b ρ ↦ by rw [lab_of_kind (hu ▸ hs3), lab_of_kind hs3, hu]
  have hsup : ∀ i : Fin 5, ({0, 1} : Finset (Fin 3)) ⊆ privScope i → privScope i = {0, 1} := by
    decide
  rcases s with i | ⟨l, j⟩ | _ | i | _
  · simp only [kind] at h0
    obtain ⟨hgi, hsi⟩ := privGrade_of_kind i h0
    rcases t with i' | _ | _ | _ | _ <;> simp only [cellScope, cellGrade] at hst hg <;>
      rw [hsi] at hst <;> try omega
    · exact ⟨.priv i, by simp only [cellScope]; rw [hsi, hsup i' hst], hg, .inr fun _ _ _ ↦ rfl⟩
    · exact absurd hst (by decide)
    · refine ⟨.full (if privKind i = 1 then 0 else 1), rfl, rfl, .inr (hsame _ ?_ ?_)⟩ <;>
        simp only [kind] <;> rcases privKind_cases i with h | h | h <;> simp_all
  · rcases t with i' | ⟨l', j'⟩ | _ | _ | _ <;> simp only [cellScope, cellGrade] at hst hg <;>
      try omega
    · exact absurd (hst (two_mem_levelScope l)) (two_notMem_privScope i').2
    · exact ⟨.don l' j, rfl, rfl, .inr fun _ _ _ ↦ rfl⟩
  · exact absurd rfl h0
  · rcases t with i' | _ | _ | _ | _ <;> simp only [cellScope, cellGrade] at hst hg <;> try omega
    · exact absurd hst (privScope_ne_univ i')
    · exact absurd hst (by decide)
    · exact ⟨.full i, rfl, rfl, .inr fun _ _ _ ↦ rfl⟩
  · exact absurd rfl h0

/-- **`lab a b ρ` is lawful** given the data `LawfulData d a b ρ`. -/
theorem isLawful_lab {a b : Label.{u}} {ρ : Fin d.card → Label.{u}} (h : LawfulData d a b ρ) :
    (cellRows d).IsLawful (lab a b ρ) := by
  obtain ⟨ha, hb, ⟨⟨g, σ, hw, ea, eb⟩, ⟨g', σ', hw', ec, ed⟩⟩, ⟨hρv, hρl⟩, hle, hbot⟩ := h
  refine ⟨fun c ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · -- The grade of a cell is `cellGrade` (by definition).
    change IsSelfVisible (cellGrade c) (lab a b ρ c)
    rcases kind_cases c with h0 | h1 | h2 | h3
    · rw [lab_zero h0]; exact isSelfVisible_bot _
    · rw [lab_one h1, grade_of_kind_one_two (.inl h1)]; exact ha
    · rw [lab_two h2, grade_of_kind_one_two (.inr h2)]; exact hb
    · obtain ⟨l, j, rfl⟩ := kind_eq_three h3; exact hρv j
  · rcases kind_cases s with h0 | h1 | h2 | h3
    · simp only [lab_zero h0, min_bot_right]
      exact TransformsTo.bot _ _
    · exact locality_full d hw ha ea eb (fun j h ↦ (hle j h).1) (fun j h ↦ (hbot j h).1) s 1 2
        h1 (.inl rfl) rfl _ (fun _ h ↦ lab_one h) (fun _ h ↦ lab_two h) (fun _ _ ↦ rfl)
        (fun _ h ↦ lab_zero h)
    · exact locality_full d hw' hb ed ec (fun j h ↦ (hle j h).2) (fun j h ↦ (hbot j h).2) s 2 1
        h2 (.inr rfl) rfl _ (fun _ h ↦ lab_two h) (fun _ h ↦ lab_one h) (fun _ _ ↦ rfl)
        (fun _ h ↦ lab_zero h)
    · obtain ⟨l, j, rfl⟩ := kind_eq_three h3
      exact locality_don d (hρl j)
  · obtain ⟨u, hu1, hu2, hk⟩ := exists_partner s t hst hg
    refine ⟨u, Prod.ext hu1 hu2, ?_⟩
    rcases hk with h0 | hk
    · rw [lab_zero h0]; exact bot_le
    · rw [hk]

/-! ### Every lawful labelling is a `lab a b ρ` -/

section Necessity

variable {X Y : Finset (Fin 3) × ℕ} {w : Cell d.card → Label.{u}}

/-- Dead cells are `⊥` in every labelling lawful below a pair above them. -/
private theorem eq_bot_of_dead (hw : (cellRows d).IsLawfulBelow X (fun c ↦ w c))
    {c : Cell d.card} (hc : c ∈ cells.below X) (h0 : kind c = 0) : w c = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have h := (hl c hc).eq_bot (d := ⟨c, cells.mem_below_gradedIndex c⟩)
    (rowValue_dead d (t := c) (.inl h0))
  simpa using h

/-- **The copies of a donor cell agree**: in a labelling lawful below `Y`, every copy of the
donor cell `j` below `Y` carries the label of `don 0 j`. -/
private theorem don_eq (hw : (cellRows d).IsLawfulBelow Y (fun c ↦ w c)) {l : Fin 3}
    {j : Fin d.card} (hY : (.don l j : Cell d.card) ∈ cells.below Y) :
    w (.don l j) = w (.don 0 j) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨g, σ, -, heq⟩ := hl _ hY
  have e1 := heq ⟨.don 0 j, levelScope_zero_subset l, le_rfl⟩
  have e2 := heq ⟨_, cells.mem_below_gradedIndex (.don l j)⟩
  -- The rows between donor cells are `donorRow` and their grades `1` (by definition).
  change min (w (.don 0 j)) (w (.don l j)) = min (σ (donorRow d j j)) (g 1) at e1
  change min (w (.don l j)) (w (.don l j)) = min (σ (donorRow d j j)) (g 1) at e2
  rw [min_self, ← e1] at e2
  have hle : w (.don l j) ≤ w (.don 0 j) := e2.trans_le (min_le_left _ _)
  obtain ⟨u, hu, hu0⟩ := ha (.don 0 j) (.don l j) hY (levelScope_zero_subset l) rfl
  have huY : u ∈ cells.below Y := le_trans hu.le hY
  obtain ⟨l', j', rfl⟩ := eq_don_of_gradedIndex (l := l) (congrArg Prod.fst hu)
    (congrArg Prod.snd hu)
  have hll : levelScope l' = levelScope l := congrArg Prod.fst hu
  obtain ⟨g', σ', -, heq'⟩ := hl _ huY
  have f1 := heq' ⟨.don 0 j, show levelScope 0 ⊆ levelScope l' by
    rw [hll]; exact levelScope_zero_subset l, le_rfl⟩
  have f2 := heq' ⟨.don l j, show levelScope l ⊆ levelScope l' by rw [hll], le_rfl⟩
  change min (w (.don 0 j)) (w (.don l' j')) = min (σ' (donorRow d j' j)) (g' 1) at f1
  change min (w (.don l j)) (w (.don l' j')) = min (σ' (donorRow d j' j)) (g' 1) at f2
  rw [min_eq_left hu0, ← f2] at f1
  exact le_antisymm hle (f1.trans_le (min_le_left _ _))

private theorem below_univ_two {c : Cell d.card} (hc : cellGrade c ≤ 2) :
    c ∈ cells.below ((univ : Finset (Fin 3)), 2) := ⟨subset_univ _, hc⟩

/-- In a linear order: from `x ≤ a`, `y ≤ b`, the two minimum equations, and the two
dominations, `x = a` and `y = b`. -/
private theorem eq_and_eq_of_min_eq {L : Type*} [LinearOrder L] {a b x y : L} (hxa : x ≤ a)
    (hyb : y ≤ b) (h1 : min b x = min y x) (h2 : min a y = min x y) (ha : a ≤ x ∨ a ≤ y)
    (hb : b ≤ x ∨ b ≤ y) : x = a ∧ y = b := by
  refine ⟨ha.elim (le_antisymm hxa) fun h ↦ ?_, hb.elim (fun h ↦ ?_) (le_antisymm hyb)⟩
  · by_contra hne
    rw [min_eq_left h, min_eq_left ((lt_of_le_of_ne hxa hne).le.trans h)] at h2
    exact hne h2.symm
  · by_contra hne
    rw [min_eq_left h, min_eq_left ((lt_of_le_of_ne hyb hne).le.trans h)] at h1
    exact hne h1.symm

/-- The locality at a cell `s` of kind `1` or `2` below `X`, read at the cells of kind `1` and `2`
below `s`: one witness reads `3` at equal kinds and `2` at different kinds. -/
private theorem locality_kinds (hw : (cellRows d).IsLawfulBelow X (fun c ↦ w c))
    {s : Cell d.card} (hsX : s ∈ cells.below X) (hs : kind s = 1 ∨ kind s = 2) :
    ∃ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ ∧ ∀ t : Cell d.card,
      (kind t = 1 ∨ kind t = 2) → cellScope t ⊆ cellScope s → min (w t) (w s) = min
        (σ (if kind s = kind t then ((3 : ℕ) : Label.{u}) else ((2 : ℕ) : Label.{u}))) (g 2) := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨g, σ, hwit, heq⟩ := hl s hsX
  refine ⟨g, σ, hwit, fun t ht hts ↦ ?_⟩
  have e := heq ⟨t, hts, (grade_of_kind_one_two ht).trans (grade_of_kind_one_two hs).symm |>.le⟩
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (w t) (w s) = min (σ (rowValue d s t)) (g (cellGrade t)) at e
  rw [grade_of_kind_one_two ht] at e
  split_ifs with h
  · rwa [rowValue_three d hs h] at e
  · rwa [rowValue_two d hs ht h] at e

/-- **Below `(univ, 2)` the full cells copy the two full private cells**: every labelling
lawful below `(univ, 2)` has `w G₁ = w C₁` and `w G₂ = w C₂`. -/
private theorem full_eq (hw : (cellRows d).IsLawfulBelow ((univ : Finset (Fin 3)), 2)
    (fun c ↦ w c)) : w (.full 0) = w (.priv 3) ∧ w (.full 1) = w (.priv 4) := by
  obtain ⟨-, -, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨g, σ, -, E⟩ := locality_kinds d hw (s := .full 0) (below_univ_two d le_rfl) (.inl rfl)
  obtain ⟨g', σ', -, E'⟩ := locality_kinds d hw (s := .full 1) (below_univ_two d le_rfl)
    (.inr rfl)
  have e93 := E (.priv 3) (.inl rfl) (subset_univ _)
  have e94 := E (.priv 4) (.inr rfl) (subset_univ _)
  have e99 := E (.full 0) (.inl rfl) (subset_univ _)
  have e910 := E (.full 1) (.inr rfl) (subset_univ _)
  have e103 := E' (.priv 3) (.inl rfl) (subset_univ _)
  have e104 := E' (.priv 4) (.inr rfl) (subset_univ _)
  have e109 := E' (.full 0) (.inl rfl) (subset_univ _)
  have e1010 := E' (.full 1) (.inr rfl) (subset_univ _)
  simp +decide only [kind, privKind, Fin.isValue, Matrix.cons_val, Fin.val_zero, Fin.val_one,
    ite_true, ite_false, min_self] at e93 e94 e99 e910 e103 e104 e109 e1010
  rw [← e99] at e93
  rw [← e910] at e94
  rw [← e1010] at e104
  rw [← e109] at e103
  have hxa : w (.full 0) ≤ w (.priv 3) := e93 ▸ min_le_left _ _
  have hyb : w (.full 1) ≤ w (.priv 4) := e104 ▸ min_le_left _ _
  have av : ∀ s : Cell d.card, cellScope s ⊆ univ → cellGrade s = 2 →
      w s ≤ w (.full 0) ∨ w s ≤ w (.full 1) := by
    intro s hs hg
    obtain ⟨u, hu, hle⟩ := ha s (.full 0) (below_univ_two d le_rfl) hs hg
    rcases eq_full_of_gradedIndex (congrArg Prod.fst hu) (congrArg Prod.snd hu) with rfl | rfl
    · exact .inl hle
    · exact .inr hle
  exact eq_and_eq_of_min_eq hxa hyb e94 e103 (av _ (subset_univ _) rfl)
    (av _ (subset_univ _) rfl)

/-- The localities at the two full private cells give the two readings. -/
private theorem reads_of_isLawfulBelow (hw : (cellRows d).IsLawfulBelow X (fun c ↦ w c))
    (h3 : (.priv 3 : Cell d.card) ∈ cells.below X) (h4 : (.priv 4 : Cell d.card) ∈ cells.below X) :
    Reads (w (.priv 3)) (w (.priv 4)) := by
  obtain ⟨g, σ, hwit, E⟩ := locality_kinds d hw h3 (.inl rfl)
  obtain ⟨g', σ', hwit', E'⟩ := locality_kinds d hw h4 (.inr rfl)
  have e33 := E (.priv 3) (.inl rfl) subset_rfl
  have e34 := E (.priv 4) (.inr rfl) subset_rfl
  have e43 := E' (.priv 3) (.inl rfl) subset_rfl
  have e44 := E' (.priv 4) (.inr rfl) subset_rfl
  simp +decide only [kind, privKind, Fin.isValue, Matrix.cons_val, ite_true, ite_false,
    min_self] at e33 e34 e43 e44
  exact ⟨⟨g, σ, hwit, e33, e34⟩, ⟨g', σ', hwit', e43, e44⟩⟩

/-- The donor values of a labelling lawful below a pair above the donor cells of level `0` are
lawful for the rows of the donor. -/
private theorem donorLawful_of_isLawfulBelow (hw : (cellRows d).IsLawfulBelow Y (fun c ↦ w c))
    (hY : ∀ j, (.don 0 j : Cell d.card) ∈ cells.below Y) :
    DonorLawful d (fun j ↦ w (.don 0 j)) := by
  obtain ⟨ho, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  exact ⟨fun j ↦ ho _ (hY j), fun j ↦ (hl _ (hY j)).reindex fun j' : Fin d.card ↦
    (⟨.don 0 j', subset_rfl, le_rfl⟩ : cells.below (cells.gradedIndex (.don 0 j)))⟩

/-- The locality at a full cell `G` couples it to the donor cells: `w G` is at most every donor
value at a cell not labelled `⊥`, and meets every donor value at a cell labelled `⊥` at `⊥`. -/
private theorem coupled_of_locality {s : Cell d.card} (hs : s = .full 0 ∨ s = .full 1)
    (hl : TransformsTo (fun c : cells.below (cells.gradedIndex s) ↦ cells.grade c.1)
      ((cellRows d).row s) (fun c ↦ min (w c) (w s))) (j : Fin d.card) :
    (d.label j ≠ ⊥ → w s ≤ w (.don 0 j)) ∧ (d.label j = ⊥ → min (w (.don 0 j)) (w s) = ⊥) := by
  have hk : kind s = 1 ∨ kind s = 2 := by rcases hs with rfl | rfl <;> simp [kind]
  obtain ⟨g, σ, hw, heq⟩ := hl
  have es := heq ⟨s, cells.mem_below_gradedIndex s⟩
  have ej := heq ⟨.don 0 j, by
    rcases hs with rfl | rfl <;> exact ⟨subset_univ _, show 1 ≤ 2 by omega⟩⟩
  -- The rows are `rowValue` and the grades `cellGrade` (by definition).
  change min (w s) (w s) = min (σ (rowValue d s s)) (g (cellGrade s)) at es
  change min (w (.don 0 j)) (w s) = min (σ (rowValue d s (.don 0 j))) (g 1) at ej
  rw [min_self, rowValue_three d hk rfl, grade_of_kind_one_two hk] at es
  rw [rowValue_don_right d (by omega), ite_eq_left hk] at ej
  unfold gateRead at ej
  refine ⟨fun hne ↦ ?_, fun hbot ↦ by rwa [ite_eq_left hbot, hw.map_bot, min_bot_left] at ej⟩
  rw [ite_eq_right hne] at ej
  exact es.trans_le ((min_le_min_left _ (hw.antitone (by omega))).trans
    (ej.symm.trans_le (min_le_left _ _)))

/-- **Every labelling lawful below `(univ, 2)` is `lab (w C₁) (w C₂) ρ` there**, with `ρ` the
values at the donor cells of level `0`, and it has the data `LawfulData`. -/
theorem lawfulData_of_isLawfulBelow (hw : (cellRows d).IsLawfulBelow ((univ : Finset (Fin 3)), 2)
    (fun c ↦ w c)) :
    LawfulData d (w (.priv 3)) (w (.priv 4)) (fun j ↦ w (.don 0 j)) ∧
      ∀ c ∈ cells.below ((univ : Finset (Fin 3)), 2),
        w c = lab (w (.priv 3)) (w (.priv 4)) (fun j ↦ w (.don 0 j)) c := by
  obtain ⟨h0, h1⟩ := full_eq d hw
  obtain ⟨ho, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have c0 := coupled_of_locality d (.inl rfl) (hl _ (below_univ_two d le_rfl))
  have c1 := coupled_of_locality d (.inr rfl) (hl _ (below_univ_two d le_rfl))
  rw [h0] at c0; rw [h1] at c1
  refine ⟨⟨ho _ (below_univ_two d le_rfl), ho _ (below_univ_two d le_rfl),
    reads_of_isLawfulBelow d hw (below_univ_two d le_rfl) (below_univ_two d le_rfl),
    donorLawful_of_isLawfulBelow d hw fun _ ↦ below_univ_two d (show 1 ≤ 2 by omega),
    fun j hj ↦ ⟨(c0 j).1 hj, (c1 j).1 hj⟩, fun j hj ↦ ⟨(c0 j).2 hj, (c1 j).2 hj⟩⟩,
    fun c hc ↦ ?_⟩
  rcases kind_cases c with k0 | k1 | k2 | k3
  · rw [eq_bot_of_dead d hw hc k0, lab_zero k0]
  · rw [lab_one k1]; rcases eq_of_kind_one k1 with rfl | rfl; exacts [rfl, h0]
  · rw [lab_two k2]; rcases eq_of_kind_two k2 with rfl | rfl; exacts [rfl, h1]
  · obtain ⟨l, j, rfl⟩ := kind_eq_three k3
    exact don_eq d hw hc

private theorem grade_le_two_of_ne_apex {c : Cell k} (hc : c ≠ .apex) : cellGrade c ≤ 2 := by
  rcases c with i | _ | _ | _ | _ <;> simp only [cellGrade] <;> try omega
  exacts [privGrade_le_two i, absurd rfl hc]

/-- **The lawful labellings of the display rows** are the labellings `lab a b ρ` with the data
`LawfulData d a b ρ`: `G₁`, `G₂` copy `C₁`, `C₂`, every copy of a donor cell carries its value
`ρ j`, the dead cells are `⊥`, and the pair `(a, b)` is coupled to the donor values. -/
theorem isLawful_iff {w : Cell d.card → Label.{u}} :
    (cellRows d).IsLawful w ↔ ∃ a b ρ, LawfulData d a b ρ ∧ w = lab a b ρ := by
  refine ⟨fun hw ↦ ?_, fun ⟨a, b, ρ, h, hw⟩ ↦ hw ▸ isLawful_lab d h⟩
  obtain ⟨hd, hlab⟩ := lawfulData_of_isLawfulBelow d (hw.isLawfulBelow _)
  refine ⟨_, _, _, hd, funext fun c ↦ ?_⟩
  by_cases hc : c = .apex
  · subst hc; rw [lab_zero rfl]
    exact hw.eq_bot_of_row_self_eq_bot _ (rowValue_dead d (s := .apex) (t := .apex) (.inl rfl))
  · exact hlab c (below_univ_two d (grade_le_two_of_ne_apex hc))

end Necessity

/-! ### Donor labellings -/

/-- Every cell of a stage type on one point has full scope and grade `1`. -/
theorem scope_eq_univ_and_grade_eq_one (j : Fin d.card) :
    d.toCellScheme.scope j = univ ∧ d.toCellScheme.grade j = 1 := by
  have hw := d.isWellFormed.isWellFormed
  have h1 := hw.grade_pos j
  have h2 := hw.grade_le_card j
  have h3 : #(d.toCellScheme.scope j) ≤ 1 := by
    simpa using card_le_univ (d.toCellScheme.scope j)
  exact ⟨eq_univ_of_card _ (by simp only [Fintype.card_fin]; omega), by omega⟩

private theorem mem_below_donor (i j : Fin d.card) :
    j ∈ d.toCellScheme.below (d.toCellScheme.gradedIndex i) :=
  ⟨show d.toCellScheme.scope j ⊆ d.toCellScheme.scope i by
      rw [(scope_eq_univ_and_grade_eq_one d j).1, (scope_eq_univ_and_grade_eq_one d i).1],
    show d.toCellScheme.grade j ≤ d.toCellScheme.grade i by
      rw [(scope_eq_univ_and_grade_eq_one d j).2, (scope_eq_univ_and_grade_eq_one d i).2]⟩

private theorem donorRow_eq (i j : Fin d.card) :
    donorRow d i j = d.rows.row i ⟨j, mem_below_donor d i j⟩ :=
  dite_eq_left (mem_below_donor d i j)

/-- **`DonorLawful` is lawfulness for the rows of the donor.** -/
theorem donorLawful_iff {ρ : Fin d.card → Label.{u}} : DonorLawful d ρ ↔ d.rows.IsLawful ρ := by
  have hg := fun j ↦ (scope_eq_univ_and_grade_eq_one d j).2
  constructor
  · rintro ⟨hv, hl⟩
    refine ⟨fun j ↦ (hg j).symm ▸ hv j, fun s ↦ ?_, fun s t _ _ ↦ ⟨s, ?_, le_rfl⟩⟩
    · obtain ⟨g, σ, hw, heq⟩ := hl s
      refine ⟨g, σ, hw, fun t ↦ ?_⟩
      have := heq t.1
      rw [donorRow_eq] at this
      change min (ρ t.1) (ρ s) = min (σ (d.rows.row s t)) (g (d.toCellScheme.grade t.1))
      rwa [hg]
    · exact Prod.ext (show d.toCellScheme.scope s = d.toCellScheme.scope t by
        rw [(scope_eq_univ_and_grade_eq_one d s).1, (scope_eq_univ_and_grade_eq_one d t).1])
        (show d.toCellScheme.grade s = d.toCellScheme.grade t by rw [hg, hg])
  · intro h
    refine ⟨fun j ↦ hg j ▸ h.orderly j, fun j ↦ ?_⟩
    obtain ⟨g, σ, hw, heq⟩ := h.locality j
    refine ⟨g, σ, hw, fun j' ↦ ?_⟩
    have := heq ⟨j', mem_below_donor d j j'⟩
    simp only [hg] at this
    change min (ρ j') (ρ j) = min (σ (donorRow d j j')) (g 1)
    rwa [donorRow_eq]

private theorem donorLawful_label : DonorLawful d d.label := (donorLawful_iff d).mpr d.isLawful

private theorem donorLawful_row (hd : d.IsLegal) (j : Fin d.card) :
    DonorLawful d (donorRow d j) := by
  refine (donorLawful_iff d).mpr ?_
  have h := (hd.isConsistent j).isLawful (mem_below_donor d j)
  convert h using 1
  exact funext fun t ↦ donorRow_eq d j t

private theorem donorLawful_min {ρ : Fin d.card → Label.{u}} (hρ : DonorLawful d ρ)
    {c : Label.{u}} (hc : IsSelfVisible 1 c) : DonorLawful d (fun j ↦ min (ρ j) c) := by
  refine ⟨fun j ↦ (hρ.1 j).min hc, fun j ↦ ?_⟩
  obtain ⟨g, σ, hw, heq⟩ := hρ.2 j
  refine ⟨_, σ, hw.cap hc, fun j' ↦ ?_⟩
  have e := heq j'
  simp only at e
  simp only [le_refl, ite_true]
  rw [min_min_min_comm, min_self, e, min_assoc]

private theorem donorLawful_raise {ρ : Fin d.card → Label.{u}} (hρ : DonorLawful d ρ)
    {c : Label.{u}} (hc : IsSelfVisible 2 c) (hc0 : c ≠ ⊥) :
    DonorLawful d (fun j ↦ raise c (ρ j)) :=
  (donorLawful_iff d).mpr (((donorLawful_iff d).mp hρ).map_of_apply_eq_bot (K := 1)
    (fun j ↦ (scope_eq_univ_and_grade_eq_one d j).2.le)
    (isWitness_raise (K := 1) hc (bot_lt_iff_ne_bot.mpr hc0)) fun _ h ↦ eq_bot_of_raise_eq_bot h)

/-! ### Legality of the rows -/

section Legality

private theorem left_eq_of_min_eq_of_lt {a c v : Label.{u}} (h : min a c = v) (hv : v < c) :
    a = v :=
  ((min_eq_iff.mp h).resolve_right fun h' ↦ hv.ne' h'.1).1

private theorem le_raise {a a' x c : Label.{u}} (hca : min a c = min a' c) (ha : a ≤ x) :
    a' ≤ raise c x := by
  unfold raise
  split_ifs with hcx
  · exact le_top
  · have hxc : x < c := not_le.mp hcx
    have : a' = a := left_eq_of_min_eq_of_lt (hca.symm.trans (min_eq_left (ha.trans hxc.le)))
      (ha.trans_lt hxc)
    exact this ▸ ha

private theorem min_raise_eq_bot {a a' x c : Label.{u}} (hc0 : c ≠ ⊥)
    (hca : min a c = min a' c) (h : min x a = ⊥) : min (raise c x) a' = ⊥ := by
  rcases min_eq_bot.mp h with hx | ha
  · rw [hx, raise_bot (bot_lt_iff_ne_bot.mpr hc0), min_eq_left bot_le]
  · have : min a' c = ⊥ := by rw [← hca, ha, min_eq_left bot_le]
    rcases min_eq_bot.mp this with h' | h'
    · rw [h', min_eq_right bot_le]
    · exact absurd h' hc0

/-- Capped lifts from `X` to `Y`, stated with labellings of all cells (`Rows.extendBot`). -/
private theorem cappedLift_of_forall {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y)
    (H : ∀ c : Label.{u}, IsSelfVisible Y.2 c → ∀ w v : Cell d.card → Label.{u},
      (cellRows d).IsLawfulBelow X (fun e ↦ w e) → (cellRows d).IsLawfulBelow Y (fun e ↦ v e) →
      (∀ e ∈ cells.below X, min (v e) c = min (w e) c) →
      ∃ r : Cell d.card → Label.{u}, (cellRows d).IsLawfulBelow Y (fun e ↦ r e) ∧
        (∀ e ∈ cells.below Y, min (r e) c = min (v e) c) ∧ ∀ e ∈ cells.below X, r e = w e) :
    (cellRows d).CappedLift h := by
  refine (Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨r, hr, hrc, hrp⟩ := H c hc (Rows.extendBot X p) (Rows.extendBot Y q)
    (Rows.isLawfulBelow_extendBot.mpr hp) (Rows.isLawfulBelow_extendBot.mpr hq) fun e he ↦ by
      rw [Rows.extendBot_of_mem _ he, Rows.extendBot_of_mem _ (cells.below_mono h he)]
      exact hpq ⟨e, he⟩
  exact ⟨fun e ↦ r e, hr, fun e ↦ by rw [hrc e e.2, Rows.extendBot_of_mem _ e.2],
    fun e ↦ (hrp e.1 e.2).trans (Rows.extendBot_of_mem p e.2)⟩

/-- If every cell below `X` is dead, the rows lift capped from `X`: keep the ambient labelling. -/
private theorem cappedLift_of_dead {X Y : Finset (Fin 3) × ℕ}
    (hX : ∀ c ∈ cells.below X, kind (c : Cell d.card) = 0) (h : X ≤ Y) :
    (cellRows d).CappedLift h :=
  cappedLift_of_forall d h fun _ _ w v hw hv _ ↦ ⟨v, hv, fun _ _ ↦ rfl, fun e he ↦ by
    rw [eq_bot_of_dead d hv (cells.below_mono h he) (hX e he), eq_bot_of_dead d hw he (hX e he)]⟩

/-- **The private coatom lift** `({0, 1}, 2)` to `(univ, 2)`: keep the prescribed pair, copy it to
`G₁`, `G₂`; on the donor cells, `d.label` at the cap `⊥`, else the ambient values raised. -/
private theorem cappedLift_private (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤)
    (h : (({0, 1} : Finset (Fin 3)), 2) ≤ ((univ : Finset (Fin 3)), 2)) :
    (cellRows d).CappedLift h := by
  refine cappedLift_of_forall d h fun c hc w v hw hv hwv ↦ ?_
  have m3 : (.priv 3 : Cell d.card) ∈ cells.below ({0, 1}, 2) := ⟨subset_rfl, le_rfl⟩
  have m4 : (.priv 4 : Cell d.card) ∈ cells.below ({0, 1}, 2) := ⟨subset_rfl, le_rfl⟩
  obtain ⟨hor, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hr := reads_of_isLawfulBelow d hw m3 m4
  obtain ⟨hgv, hvlab⟩ := lawfulData_of_isLawfulBelow d hv
  have hc3 := hwv _ m3
  have hc4 := hwv _ m4
  set ρ' : Fin d.card → Label.{u} :=
    if c = ⊥ then d.label else fun j ↦ raise c (v (.don 0 j)) with hρ'
  have hgood : LawfulData d (w (.priv 3)) (w (.priv 4)) ρ' := by
    by_cases hc0 : c = ⊥
    · rw [hρ', ite_eq_left hc0]
      refine ⟨hor _ m3, hor _ m4, hr, donorLawful_label d, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
      · rw [(hℓ j).resolve_left hj]; exact ⟨le_top, le_top⟩
      · rw [hj]; exact ⟨min_eq_left bot_le, min_eq_left bot_le⟩
    · rw [hρ', ite_eq_right hc0]
      exact ⟨hor _ m3, hor _ m4, hr, donorLawful_raise d hgv.donorLawful hc hc0,
        fun j hj ↦ ⟨le_raise hc3 (hgv.le_of_ne_bot j hj).1, le_raise hc4 (hgv.le_of_ne_bot j hj).2⟩,
        fun j hj ↦ ⟨min_raise_eq_bot hc0 hc3 (hgv.min_eq_bot j hj).1,
          min_raise_eq_bot hc0 hc4 (hgv.min_eq_bot j hj).2⟩⟩
  refine ⟨lab (w (.priv 3)) (w (.priv 4)) ρ', (isLawful_lab d hgood).isLawfulBelow _,
    fun e he ↦ ?_, fun e he ↦ ?_⟩
  · rw [hvlab e he]
    rcases kind_cases e with h0 | h1 | h2 | h3
    · rw [lab_zero h0, lab_zero h0]
    · rw [lab_one h1, lab_one h1]; exact hc3.symm
    · rw [lab_two h2, lab_two h2]; exact hc4.symm
    · obtain ⟨l, j, rfl⟩ := kind_eq_three h3
      change min (ρ' j) c = min (v (.don 0 j)) c
      rw [hρ']
      split_ifs with hc0
      · rw [hc0, min_bot_right, min_bot_right]
      · exact min_raise c _
  · obtain ⟨i, rfl⟩ := eq_priv_of_scope he.1
    rcases privKind_cases i with h0 | h1 | h2
    · rw [lab_zero (c := .priv i) h0, eq_bot_of_dead d hw he h0]
    · rw [lab_one (c := .priv i) h1]; obtain rfl := (privKind_one_two i).1 h1; rfl
    · rw [lab_two (c := .priv i) h2]; obtain rfl := (privKind_one_two i).2 h2; rfl

/-- **The forcing lift** `({1, 2}, 2)` to `(univ, 2)`: keep the prescribed donor values on every
copy, and cap the ambient private pair, `G₁` and `G₂` at the cap. -/
private theorem cappedLift_forcing
    (h : (({1, 2} : Finset (Fin 3)), 2) ≤ ((univ : Finset (Fin 3)), 2)) :
    (cellRows d).CappedLift h := by
  refine cappedLift_of_forall d h fun c hc w v hw hv hwv ↦ ?_
  have hdon : ∀ j, (.don 0 j : Cell d.card) ∈ cells.below (({1, 2} : Finset (Fin 3)), 2) :=
    fun _ ↦ ⟨show levelScope 0 ⊆ {1, 2} by decide, show 1 ≤ 2 by omega⟩
  obtain ⟨hgv, hvlab⟩ := lawfulData_of_isLawfulBelow d hv
  have hc5 : ∀ j, min (v (.don 0 j)) c = min (w (.don 0 j)) c := fun j ↦ hwv _ (hdon j)
  have hgood : LawfulData d (min (v (.priv 3)) c) (min (v (.priv 4)) c)
      (fun j ↦ w (.don 0 j)) := by
    have hle : ∀ {j x}, x ≤ v (.don 0 j) → min x c ≤ w (.don 0 j) := fun {j _} hx ↦
      (min_le_min_right c hx).trans ((hc5 j).trans_le (min_le_left _ _))
    have hbot : ∀ {j x}, min (v (.don 0 j)) x = ⊥ → min (w (.don 0 j)) (min x c) = ⊥ :=
      fun {j _} hx ↦ by rw [← min_assoc, min_right_comm, ← hc5 j, min_right_comm, hx, min_bot_left]
    exact ⟨hgv.sv_a.min hc, hgv.sv_b.min hc, hgv.reads.min hc,
      donorLawful_of_isLawfulBelow d hw hdon,
      fun j hj ↦ ⟨hle (hgv.le_of_ne_bot j hj).1, hle (hgv.le_of_ne_bot j hj).2⟩,
      fun j hj ↦ ⟨hbot (hgv.min_eq_bot j hj).1, hbot (hgv.min_eq_bot j hj).2⟩⟩
  refine ⟨lab (min (v (.priv 3)) c) (min (v (.priv 4)) c) (fun j ↦ w (.don 0 j)),
    (isLawful_lab d hgood).isLawfulBelow _, fun e he ↦ ?_, fun e he ↦ ?_⟩
  · rw [hvlab e he]
    rcases kind_cases e with h0 | h1 | h2 | h3
    · rw [lab_zero h0, lab_zero h0]
    · rw [lab_one h1, lab_one h1, min_assoc, min_self]
    · rw [lab_two h2, lab_two h2, min_assoc, min_self]
    · obtain ⟨l, j, rfl⟩ := kind_eq_three h3
      exact (hc5 j).symm
  · rcases kind_of_scope_one_two he.1 with h0 | h3
    · rw [lab_zero h0, eq_bot_of_dead d hw he h0]
    · obtain ⟨l, j, rfl⟩ := kind_eq_three h3
      exact (don_eq d hw he).symm

/-- **The lifts at grade `1`** from a face containing the new point: below such pairs every cell
is dead or a donor cell; keep the prescribed donor values on every copy. -/
private theorem cappedLift_grade_one {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y)
    (h2 : 2 ∈ X.1) (hX : X.2 = 1) (hY2 : Y.2 = 1) :
    (cellRows d).CappedLift h := by
  refine cappedLift_of_forall d h fun c _ w v hw hv hwv ↦ ?_
  have hdon : ∀ j, (.don 0 j : Cell d.card) ∈ cells.below X := fun _ ↦
    ⟨show levelScope 0 ⊆ X.1 by
      rw [show levelScope 0 = {2} from rfl, singleton_subset_iff]; exact h2,
      show 1 ≤ X.2 by omega⟩
  have hY : ∀ e ∈ cells.below Y, kind (e : Cell d.card) = 0 ∨ kind e = 3 := fun e he ↦
    kind_of_grade_le_one (he.2.trans hY2.le)
  have hgood : LawfulData d ⊥ ⊥ (fun j ↦ w (.don 0 j)) :=
    ⟨isSelfVisible_bot _, isSelfVisible_bot _, reads_self (isSelfVisible_bot _),
      donorLawful_of_isLawfulBelow d hw hdon, fun _ _ ↦ ⟨bot_le, bot_le⟩,
      fun _ _ ↦ ⟨min_bot_right _, min_bot_right _⟩⟩
  refine ⟨lab ⊥ ⊥ (fun j ↦ w (.don 0 j)), (isLawful_lab d hgood).isLawfulBelow _,
    fun e he ↦ ?_, fun e he ↦ ?_⟩
  · rcases hY e he with h0 | h3
    · rw [lab_zero h0, eq_bot_of_dead d hv he h0]
    · obtain ⟨l, j, rfl⟩ := kind_eq_three h3
      rw [don_eq d hv he]
      exact (hwv _ (hdon j)).symm
  · rcases hY e (cells.below_mono h he) with h0 | h3
    · rw [lab_zero h0, eq_bot_of_dead d hw he h0]
    · obtain ⟨l, j, rfl⟩ := kind_eq_three h3
      exact (don_eq d hw he).symm

-- `decide +kernel` below needs a `Decidable` instance for nested quantifiers over finsets,
-- larger than the default bound of instance synthesis.
set_option synthInstance.maxSize 512 in
/-- The lifts between graded faces at a fixed grade: within a face, at grade `1` away from or
from a face containing the new point, and from `({0, 1}, 2)` or `({1, 2}, 2)` to `(univ, 2)`. -/
private theorem case_split : ∀ A B : Finset (Fin 3),
    A ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) →
    B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) → A ⊆ B → ∀ n : Fin 4, 0 < (n : ℕ) →
      (n : ℕ) ≤ #A → A = B ∨ ((n : ℕ) = 1 ∧ 2 ∉ A) ∨ (A = {0, 1} ∧ (n : ℕ) = 2 ∧ B = univ) ∨
        (A = {1, 2} ∧ (n : ℕ) = 2 ∧ B = univ) ∨ ((n : ℕ) = 1 ∧ 2 ∈ A) := by
  decide +kernel

/-- **The rows are bountiful**: within a face, below pairs where every cell is dead, the private
coatom lift, the forcing lift, and the lifts at grade `1`. -/
theorem isBountiful_cellRows (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) :
    (cellRows d).IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  have hk : X.2 < 4 := by
    have := hX.2.2; have := card_le_univ X.1; simp only [Fintype.card_fin] at this; omega
  rcases case_split X.1 Y.1 hX.1 hY.1 h.1 ⟨X.2, hk⟩ hX.2.1 hX.2.2 with
    heq | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Rows.cappedLift_of_fst_eq _ heq
  · have h1' : X.2 = 1 := h1
    exact cappedLift_of_dead d (fun e he ↦ kind_dead_of_two_notMem h2 he.1 (he.2.trans h1'.le)) _
  · obtain ⟨X1, X2⟩ := X
    obtain ⟨Y1, Y2⟩ := Y
    simp only at h1 h2 h3
    subst h1 h2 h3
    exact cappedLift_private d hℓ _
  · obtain ⟨X1, X2⟩ := X
    obtain ⟨Y1, Y2⟩ := Y
    simp only at h1 h2 h3
    subst h1 h2 h3
    exact cappedLift_forcing d _
  · exact cappedLift_grade_one d _ h2 h1 h1

/-- The row of a cell of kind `1` or `2` is a labelling `lab`. -/
private theorem rowValue_eq_lab {s t : Cell d.card} (hs : kind s = 1 ∨ kind s = 2) :
    rowValue d s t = lab (kindRow (kind s) 1) (kindRow (kind s) 2) (gateRead d) t := by
  by_cases ht : kind t = 3
  · obtain ⟨l, j, rfl⟩ := kind_eq_three ht
    rw [rowValue_don_right d (by omega), ite_eq_left hs]
    rfl
  · rw [rowValue_kind d ht, lab_of_kind ht]
    rcases kind_cases t with t0 | t1 | t2 | t3
    · rw [kindRow_bot (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_left t1, t1]
    · rw [ite_eq_right (by omega), ite_eq_left t2, t2]
    · exact absurd t3 ht

private theorem lawfulData_gate (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) {a b : Label.{u}}
    (ha : IsSelfVisible 2 a) (hb : IsSelfVisible 2 b) (hr : Reads a b)
    (ha3 : a ≤ ((3 : ℕ) : Label.{u})) (hb3 : b ≤ ((3 : ℕ) : Label.{u})) :
    LawfulData d a b (gateRead d) := by
  refine ⟨ha, hb, hr, ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · have : gateRead d = fun j ↦ min (d.label j) ((3 : ℕ) : Label.{u}) := funext fun j ↦ by
      unfold gateRead; rcases hℓ j with h | h <;> simp [h]
    rw [this]; exact donorLawful_min d (donorLawful_label d) sv_three_one
  · unfold gateRead; rw [ite_eq_right hj]; exact ⟨ha3, hb3⟩
  · unfold gateRead; rw [ite_eq_left hj]; exact ⟨min_bot_left _, min_bot_left _⟩

/-- **The rows are consistent**: the row of a cell of kind `1` is `lab 3 2 gateRead`, of kind `2`
`lab 2 3 gateRead`, of a donor cell `j` `lab ⊥ ⊥ (donorRow j)`, and of a dead cell `⊥`. -/
theorem isConsistent_cellRows (hd : d.IsLegal) (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) :
    (cellRows d).IsConsistent := by
  intro s
  -- Consistency asks that the row of `s` be lawful below `s` (by definition).
  change (cellRows d).IsLawfulBelow _ (fun t ↦ rowValue d s t.1)
  rcases kind_cases s with h0 | h1 | h2 | h3
  · simp only [rowValue_dead d (.inl h0)]
    exact Rows.isLawfulBelow_const_bot _
  · simp only [rowValue_eq_lab d (.inl h1), h1]
    rw [kindRow_three (by omega) rfl, kindRow_two (by omega) (by omega) (by omega)]
    exact (isLawful_lab d (lawfulData_gate d hℓ sv_three sv_two reads_three_two le_rfl
      two_lt_three.le)).isLawfulBelow _
  · simp only [rowValue_eq_lab d (.inr h2), h2]
    rw [kindRow_two (by omega) (by omega) (by omega), kindRow_three (by omega) rfl]
    exact (isLawful_lab d (lawfulData_gate d hℓ sv_two sv_three reads_two_three
      two_lt_three.le le_rfl)).isLawfulBelow _
  · obtain ⟨l, j, rfl⟩ := kind_eq_three h3
    have hrow : ∀ t : Cell d.card, rowValue d (.don l j) t = lab ⊥ ⊥ (donorRow d j) t := by
      intro t
      by_cases ht : kind t = 3
      · obtain ⟨l', j', rfl⟩ := kind_eq_three ht
        rfl
      · rw [rowValue_kind d ht, kindRow_bot (by omega), lab_of_kind ht]
        split_ifs <;> rfl
    simp only [hrow]
    exact (isLawful_lab d ⟨isSelfVisible_bot _, isSelfVisible_bot _,
      reads_self (isSelfVisible_bot _), donorLawful_row d hd j, fun _ _ ↦ ⟨bot_le, bot_le⟩,
      fun _ _ ↦ ⟨min_bot_right _, min_bot_right _⟩⟩).isLawfulBelow _

-- `decide +kernel` below needs a `Decidable` instance for nested quantifiers over finsets,
-- larger than the default bound of instance synthesis.
set_option synthInstance.maxSize 512 in
private theorem exists_cell_geom : ∀ B : Finset (Fin 3),
    B ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) → ∀ n : Fin 4, 0 < (n : ℕ) →
      (n : ℕ) ≤ #B → (∃ i : Fin 5, privScope i = B ∧ privGrade i = n) ∨
        (∃ l : Fin 3, levelScope l = B ∧ (n : ℕ) = 1) ∨ (B = {1, 2} ∧ (n : ℕ) = 2) ∨
        (B = univ ∧ (n : ℕ) = 2) ∨ (B = univ ∧ (n : ℕ) = 3) := by
  decide +kernel

/-- **Every graded face of the plan carries a cell**, for a donor with at least one cell. -/
theorem isComplete_cells (hk : 0 < k) : (cells (k := k)).IsComplete := by
  intro X hX
  have hn : X.2 < 4 := by
    have := hX.2.2; have := card_le_univ X.1; simp only [Fintype.card_fin] at this; omega
  rcases exists_cell_geom X.1 hX.1 ⟨X.2, hn⟩ hX.2.1 hX.2.2 with
    ⟨i, h1, h2⟩ | ⟨l, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  exacts [⟨.priv i, Prod.ext h1 h2⟩, ⟨.don l ⟨0, hk⟩, Prod.ext h1 h2.symm⟩,
    ⟨.side, Prod.ext h1.symm h2.symm⟩, ⟨.full 0, Prod.ext h1.symm h2.symm⟩,
    ⟨.apex, Prod.ext h1.symm h2.symm⟩]

/-- **The cells are well formed** on the interval plan of the three points. -/
theorem isWellFormed_cells : (cells (k := k)).IsWellFormed where
  finite := inferInstance
  isPlan := Geometry.isPlan_intervalPlan univ
  gradedIndex_mem c := by
    rcases c with i | ⟨l, j⟩ | _ | _ | _
    · revert i; exact show ∀ i : Fin 5, privScope i ∈ Geometry.intervalPlan univ ∧
        0 < privGrade i ∧ privGrade i ≤ #(privScope i) by decide
    · revert l; exact show ∀ l : Fin 3, levelScope l ∈ Geometry.intervalPlan univ ∧ 0 < 1 ∧
        1 ≤ #(levelScope l) by decide
    · exact show ({1, 2} : Finset (Fin 3)) ∈ Geometry.intervalPlan univ ∧ 0 < 2 ∧ 2 ≤ #{1, 2}
        by decide
    · exact show (univ : Finset (Fin 3)) ∈ Geometry.intervalPlan univ ∧ 0 < 2 ∧ 2 ≤ #univ
        by decide
    · exact show (univ : Finset (Fin 3)) ∈ Geometry.intervalPlan univ ∧ 0 < 3 ∧ 3 ≤ #univ
        by decide

private theorem natCast_lt_omega0_sq (n : ℕ) :
    ((n : ℕ) : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rw [← WithBot.coe_natCast, WithBot.coe_lt_coe, ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  refine (Ordinal.natCast_lt_omega0 n).trans_le ?_
  rw [pow_two]; exact Ordinal.le_mul_left _ Ordinal.omega0_pos

/-- **The rows are coded**: their values are `⊥`, `2`, `3` and the rows of the donor. -/
theorem rowValue_lt (s t : Cell d.card) :
    rowValue d s t < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have hb : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    WithBot.bot_lt_coe _
  by_cases ht : kind t = 3
  · obtain ⟨l, j, rfl⟩ := kind_eq_three ht
    by_cases hs : kind s = 3
    · obtain ⟨l', i, rfl⟩ := kind_eq_three hs
      change donorRow d i j < _
      unfold donorRow; split_ifs; exacts [d.isCoded _ _, hb]
    · rw [rowValue_don_right d hs]
      unfold gateRead; split_ifs <;> first | exact hb | exact natCast_lt_omega0_sq 3
  · rw [rowValue_kind d ht]
    unfold kindRow; split_ifs; exacts [hb, natCast_lt_omega0_sq 3, natCast_lt_omega0_sq 2]

end Legality

/-! ### The display and its faces -/

section Display

private theorem lawfulData_top (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) :
    LawfulData d ⊤ ⊤ d.label :=
  ⟨isSelfVisible_top _, isSelfVisible_top _, reads_self (isSelfVisible_top _),
    donorLawful_label d, fun j hj ↦ by rw [(hℓ j).resolve_left hj]; exact ⟨le_rfl, le_rfl⟩,
    fun j hj ↦ by rw [hj]; exact ⟨min_bot_left _, min_bot_left _⟩⟩

/-- **The display** over a donor `d` whose labels are `⊥` or `⊤`: the cells `cells`, enumerated by
`toFin`, with the rows `cellRows d`, labelled `⊤` at `C₁`, `C₂`, `G₁`, `G₂`, by the labels of the
donor at the copies of the donor cells, and `⊥` at the dead cells. -/
@[reducible] noncomputable def display (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) :
    StageType.{u} α 3 where
  card := 5 + (3 * d.card + 4)
  toCellScheme := cells.reindex toFin.symm
  rows := (cellRows d).comap (IsLowerEmbedding.reindex cells toFin.symm)
  label := lab ⊤ ⊤ d.label ∘ toFin.symm
  isWellFormed := ⟨rfl, isWellFormed_cells.reindex _⟩
  isCoded _ _ := rowValue_lt d _ _
  isLawful := (isLawful_lab d (lawfulData_top d hℓ)).comap
    (IsLowerEmbedding.reindex cells toFin.symm)
  atStage c := by
    change AtStage α (lab ⊤ ⊤ d.label (toFin.symm c))
    rcases kind_cases (toFin.symm c) with h0 | h1 | h2 | h3
    · rw [lab_zero h0]; exact atStage_bot
    · rw [lab_one h1]; exact atStage_top
    · rw [lab_two h2]; exact atStage_top
    · obtain ⟨l, j, hj⟩ := kind_eq_three h3
      rw [hj]; exact d.atStage j

/-- **The display is legal**, for a legal donor whose labels are `⊥` or `⊤`. -/
theorem isLegal_display (hd : d.IsLegal) (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) :
    (display d hℓ).IsLegal := by
  obtain ⟨j, -⟩ := hd.isComplete ((univ : Finset (Fin 1)), 1)
    ⟨d.univ_mem_faces, Nat.one_pos, by simp⟩
  exact StageType.isLegal_iff.mpr ⟨(isConsistent_cellRows d hd hℓ).comap
    (IsLowerEmbedding.reindex cells toFin.symm),
    (isBountiful_cellRows d hℓ).reindex _,
    (isComplete_cells (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)).reindex
      toFin.symm.surjective⟩

private theorem faces_agree : ∀ C : Finset (Fin 2),
    C.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) ↔
      C ∈ Geometry.intervalPlan (univ : Finset (Fin 2)) := by decide +kernel

private theorem scope_agree : ∀ i : Fin 5,
    (privScope i).preimage (Fin.castSuccEmb : Fin 2 ↪ Fin 3)
      Fin.castSuccEmb.injective.injOn = GatedExtensionCounterexample.cellScope i := by
  intro i
  ext x
  rw [Finset.mem_preimage]
  revert i x
  decide +kernel

private theorem grade_agree : ∀ i : Fin 5,
    privGrade i = GatedExtensionCounterexample.cellGrade i := by decide

private theorem rows_agree (s t : Fin 5)
    (h : t ∈ GatedExtensionCounterexample.cells.below
      (GatedExtensionCounterexample.cells.gradedIndex s)) :
    rowValue d (.priv s) (.priv t) = GatedExtensionCounterexample.rows.{u}.row s ⟨t, h⟩ := by
  revert h; fin_cases s <;> fin_cases t <;> intro h <;> rfl

private theorem scope_display (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤)
    (y : Fin (display d hℓ).card) :
    (display d hℓ).toCellScheme.scope y = cellScope (toFin.symm y) := rfl

private theorem privScope_subset : ∀ i : Fin 5, privScope i ⊆ {0, 1} := by decide

private theorem range_castSuccEmb :
    Set.range (Fin.castSuccEmb : Fin 2 ↪ Fin 3) = (({0, 1} : Finset (Fin 3)) : Set (Fin 3)) := by
  ext x; fin_cases x <;> simp [Fin.ext_iff]

/-- **A face of the display** along `g` is `T` when the cells `e i`, increasing under `toFin`, are
the cells visible through `g` and carry the scopes, grades, rows and labels of `T`. -/
private theorem restrictFace_display_eq (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) {m : ℕ}
    (g : Fin m ↪ Fin 3) (T : StageType.{u} α m)
    (hg : univ.map g ∈ Geometry.intervalPlan (univ : Finset (Fin 3)))
    (e : Fin T.card → Cell d.card) (he : StrictMono fun i ↦ (toFin (e i) : ℕ))
    (hr : ∀ c, (∃ i, e i = c) ↔ cellScope c ⊆ univ.map g) (hground : T.toCellScheme.ground = univ)
    (hfaces : ∀ C : Finset (Fin m),
      C.map g ∈ Geometry.intervalPlan (univ : Finset (Fin 3)) ↔ C ∈ T.toCellScheme.faces)
    (hscope : ∀ i, (cellScope (e i)).preimage g g.injective.injOn = T.toCellScheme.scope i)
    (hgrade : ∀ i, cellGrade (e i) = T.toCellScheme.grade i)
    (hrow : ∀ s t (h : t ∈ T.toCellScheme.below (T.toCellScheme.gradedIndex s)),
      rowValue d (e s) (e t) = T.rows.row s ⟨t, h⟩)
    (hlabel : ∀ i, lab ⊤ ⊤ d.label (e i) = T.label i) :
    restrictFace g (display d hℓ) = some T := by
  rw [restrictFace_eq_some_iff]
  have hg' : univ.map g ∈ (display d hℓ).toCellScheme.faces := hg
  refine ⟨hg', ?_⟩
  let e' : Fin T.card → Fin (display d hℓ).card := fun i ↦ toFin (e i)
  have hr' : ∀ x, x ∈ Set.range e' ↔ x ∈ (display d hℓ).toScheme.visibleCells g := by
    intro x
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
    -- The scope of a cell of the display is `cellScope` of its cell (by definition).
    change _ ↔ cellScope (toFin.symm x) ⊆ _
    rw [← hr]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (Equiv.symm_apply_apply _ _).symm⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, show toFin (e i) = x by rw [hi]; exact Equiv.apply_symm_apply _ _⟩
  have key : ∀ {i : Fin T.card} {j : Fin ((display d hℓ).toScheme.comap g).card},
      (i : ℕ) = j → e' i = (display d hℓ).toScheme.cellMap g j :=
    fun hij ↦ (display d hℓ).toScheme.cellMap_eq_of_strictMono g (fun _ _ h ↦ he h) hr' hij
  refine StageType.ext ?_ (fun i j hij ↦ ?_)
  · rw [StageType.comap_toScheme]
    refine Scheme.ext ((display d hℓ).toScheme.card_visibleCells_eq_of_strictMono g
      (fun _ _ h ↦ he h) hr') ?_ ?_ (fun a i hai ↦ ?_) (fun a i hai ↦ ?_)
      (fun s s' t t' hs ht ↦ ?_)
    · rw [Scheme.comap_ground, hground]
      exact eq_univ_of_forall fun _ ↦ by rw [mem_preimage]; exact mem_univ _
    · ext C
      rw [Scheme.mem_comap_faces]
      exact hfaces C
    · rw [Scheme.comap_scope, ← key hai.symm, ← hscope i]
      ext x
      rw [mem_preimage, mem_preimage, scope_display, Equiv.symm_apply_apply]
    · rw [Scheme.comap_grade, ← key hai.symm, ← hgrade i]
      exact congrArg cellGrade (Equiv.symm_apply_apply toFin (e i))
    · rw [Scheme.comap_row]
      -- The rows of the display are `rowValue` at the underlying cells (by definition).
      change rowValue d (toFin.symm ((display d hℓ).toScheme.cellMap g s))
        (toFin.symm ((display d hℓ).toScheme.cellMap g t.1)) = _
      rw [← key hs.symm, ← key ht.symm]
      simp only [e', Equiv.symm_apply_apply]
      exact hrow s' t'.1 t'.2
  -- The labels of the display are `lab ⊤ ⊤ ℓ` at the underlying cells (by definition).
  · change lab ⊤ ⊤ d.label (toFin.symm ((display d hℓ).toScheme.cellMap g i)) = _
    rw [← key hij.symm]
    simp only [e', Equiv.symm_apply_apply]
    exact hlabel j

/-- **The private face of the display is literally the private type `P α`**. -/
theorem restrictFace_castSuccEmb_display (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤) :
    restrictFace Fin.castSuccEmb (display d hℓ) = some (GatedExtensionCounterexample.P α) := by
  have hU : (univ : Finset (Fin 2)).map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) = {0, 1} := by decide
  refine restrictFace_display_eq d hℓ Fin.castSuccEmb _ (by rw [hU]; decide) Cell.priv
    (fun a b (h : (a : ℕ) < b) ↦
      (val_toFin_priv a).trans_lt (h.trans_eq (val_toFin_priv b).symm))
    (fun c ↦ ⟨?_, fun h ↦ ?_⟩) rfl
    faces_agree scope_agree grade_agree (rows_agree d) (fun j ↦ by fin_cases j <;> rfl)
  · rintro ⟨i, rfl⟩
    rw [hU]; exact privScope_subset i
  · rw [hU] at h
    obtain ⟨i, rfl⟩ := eq_priv_of_scope h
    exact ⟨i, rfl⟩

private theorem univ_map_extendByLast_zero (f : Fin 0 ↪ Fin 2) :
    univ.map (extendByLast f) = ({2} : Finset (Fin 3)) := by
  rw [univ_map_extendByLast, univ_eq_empty, map_empty, map_empty]
  rfl

/-- **The donor face of the display is literally the donor `d`**. -/
theorem restrictFace_extendByLast_display (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤)
    (f : Fin 0 ↪ Fin 2) :
    restrictFace (extendByLast f) (display d hℓ) = some d := by
  have hU := univ_map_extendByLast_zero f
  have hsc := scope_eq_univ_and_grade_eq_one d
  refine restrictFace_display_eq d hℓ (extendByLast f) d (by rw [hU]; decide) (Cell.don 0)
    (fun a b h ↦ by simp only [val_toFin_don]; omega) (fun c ↦ ⟨?_, fun h ↦ ?_⟩)
    d.isWellFormed.ground_eq (fun C ↦ ?_) (fun i ↦ ?_) (fun i ↦ (hsc i).2.symm)
    (fun s t _ ↦ donorRow_eq d s t) (fun _ ↦ rfl)
  · rintro ⟨i, rfl⟩
    rw [hU]; exact subset_rfl
  · rw [hU] at h
    obtain ⟨j, rfl⟩ := eq_don_zero_of_scope h
    exact ⟨j, rfl⟩
  · have hC : ∀ C : Finset (Fin 1), C = ∅ ∨ C = univ := by decide
    rcases hC C with rfl | rfl
    · rw [map_empty]
      exact iff_of_true (by decide) d.isPlan.empty_mem
    · rw [hU]
      exact iff_of_true (by decide) d.univ_mem_faces
  · rw [(hsc i).1]
    refine eq_univ_of_forall fun x ↦ ?_
    rw [mem_preimage, Subsingleton.elim (α := Fin 1) x (Fin.last 0), extendByLast_last]
    exact show Fin.last 2 ∈ levelScope 0 by decide

end Display

/-! ### The coupled gated extensions -/

section Extension

variable (hℓ : ∀ j, d.label j = ⊥ ∨ d.label j = ⊤)

private theorem scope_toFin (c : Cell d.card) :
    (display d hℓ).toCellScheme.scope (toFin c : Fin (display d hℓ).card) = cellScope c :=
  congrArg cellScope (Equiv.symm_apply_apply toFin c)

private theorem grade_toFin (c : Cell d.card) :
    (display d hℓ).toCellScheme.grade (toFin c : Fin (display d hℓ).card) = cellGrade c :=
  congrArg cellGrade (Equiv.symm_apply_apply toFin c)

private theorem gradedIndex_toFin (c : Cell d.card) :
    (display d hℓ).toCellScheme.gradedIndex (toFin c : Fin (display d hℓ).card) =
      cells.gradedIndex c :=
  Prod.ext (scope_toFin d hℓ c) (grade_toFin d hℓ c)

private theorem label_toFin (c : Cell d.card) :
    (display d hℓ).label (toFin c : Fin (display d hℓ).card) = lab ⊤ ⊤ d.label c :=
  congrArg (lab ⊤ ⊤ d.label) (Equiv.symm_apply_apply toFin c)

private theorem row_toFin (s c : Cell d.card) (h) :
    (display d hℓ).rows.row (toFin s : Fin (display d hℓ).card) ⟨toFin c, h⟩ =
      rowValue d s c := by
  change rowValue d (toFin.symm (toFin s)) (toFin.symm (toFin c)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private theorem mem_visible_toFin {c : Cell d.card} {S : Set (Fin 3)} :
    (toFin c : Fin (display d hℓ).card) ∈ (display d hℓ).toCellScheme.visible S ↔
      (cellScope c : Set (Fin 3)) ⊆ S := by
  change ((cellScope (toFin.symm (toFin c)) : Finset (Fin 3)) : Set (Fin 3)) ⊆ S ↔ _
  rw [Equiv.symm_apply_apply]

private theorem eq_don_of_visible (f : Fin 0 ↪ Fin 2) {c : Cell d.card}
    (hc : (toFin c : Fin (display d hℓ).card) ∈
      (display d hℓ).toCellScheme.visible (Set.range (extendByLast f))) :
    ∃ j, c = .don 0 j := by
  have hr : Set.range (extendByLast f) = (({2} : Finset (Fin 3)) : Set (Fin 3)) := by
    rw [← univ_map_extendByLast_zero f, coe_map, coe_univ, Set.image_univ]
  rw [mem_visible_toFin, hr, coe_subset] at hc
  exact eq_don_zero_of_scope hc

/-- The full private cell of the kind of the full cell `G`: `C₁` for `G₁`, `C₂` for `G₂`. -/
def capCell (G : Fin 2) : Cell k := .priv ⟨G + 3, by omega⟩

private theorem kind_capCell (G : Fin 2) : kind (capCell G : Cell k) = G + 1 := by
  fin_cases G <;> rfl

/-- **A coupled gated extension of `P α`** over a root `f : Fin 0 ↪ Fin 2`, with a legal donor
`d` whose labels are `⊥` or `⊤`: the display `display d hℓ`, the gate `G` (`G₁` or `G₂`), and the
cap the full private cell of the same kind (`C₁` or `C₂`). -/
noncomputable def extension (hd : d.IsLegal) (f : Fin 0 ↪ Fin 2) (G : Fin 2) :
    CoupledGatedExtension (GatedExtensionCounterexample.P α) f d where
  display := display d hℓ
  isLegal := isLegal_display d hd hℓ
  restrictFace_castSuccEmb := restrictFace_castSuccEmb_display d hℓ
  restrictFace_extendByLast := restrictFace_extendByLast_display d hℓ f
  gate := toFin (.full G)
  cap := toFin (capCell G)
  gradedIndex_gate := gradedIndex_toFin d hℓ _
  gradedIndex_cap := by
    rw [gradedIndex_toFin]; fin_cases G
    exacts [show (privScope 3, privGrade 3) = (univ.map Fin.castSuccEmb, 2) by decide,
      show (privScope 4, privGrade 4) = (univ.map Fin.castSuccEmb, 2) by decide]
  twinsReadGate t _ _ ht htG := by
    obtain ⟨c, rfl⟩ := toFin.surjective t
    rw [gradedIndex_toFin, gradedIndex_toFin] at ht
    have hne : c ≠ .full G := fun h ↦ htG (h ▸ rfl)
    rw [row_toFin, row_toFin]
    rcases eq_full_of_gradedIndex (congrArg Prod.fst ht) (congrArg Prod.snd ht) with rfl | rfl <;>
      fin_cases G <;> first | exact absurd rfl hne | exact le_of_eq rfl
  isGate :=
    { cap_mem := (mem_visible_toFin d hℓ).mpr (by
        rw [range_castSuccEmb, coe_subset]; exact privScope_subset _)
      scope_cap_subset := by rw [scope_toFin, scope_toFin]; exact subset_univ _
      grade_cap := by rw [grade_toFin, grade_toFin]; fin_cases G <;> rfl
      cap_ne_bot := by rw [label_toFin]; fin_cases G <;> exact top_ne_bot
      le_gate := fun e he ↦ by
        obtain ⟨c, rfl⟩ := toFin.surjective e
        obtain ⟨j, rfl⟩ := eq_don_of_visible d hℓ f he
        rw [gradedIndex_toFin, gradedIndex_toFin]
        exact ⟨subset_univ _, show 1 ≤ 2 by omega⟩
      reads := fun e he _ ↦ by
        obtain ⟨c, rfl⟩ := toFin.surjective e
        obtain ⟨j, rfl⟩ := eq_don_of_visible d hℓ f he
        have hk : kind (.full G : Cell d.card) = 1 ∨ kind (.full G : Cell d.card) = 2 := by
          fin_cases G <;> simp [kind]
        have hrow : rowValue d (.full G) (.don 0 j) = gateRead d j := by
          rw [rowValue_don_right d (by omega), ite_eq_left hk]
        have hg3 : gateRead d j = if d.label j = ⊥ then ⊥ else ((3 : ℕ) : Label.{u}) := rfl
        rcases hℓ j with hb | ht
        · exact .bot ((label_toFin d hℓ _).trans hb)
            ((row_toFin d hℓ _ _ _).trans (hrow.trans (hg3.trans (ite_eq_left hb))))
        · have hle : cells.gradedIndex (capCell G : Cell d.card) ≤
              cells.gradedIndex (.full G : Cell d.card) := ⟨subset_univ _,
            (grade_of_kind_one_two (c := (capCell G : Cell d.card))
              (by rw [kind_capCell]; have := G.isLt; omega)).le⟩
          refine .top ⟨toFin (capCell G), (gradedIndex_toFin d hℓ _).trans_le
            (hle.trans_eq (gradedIndex_toFin d hℓ _).symm)⟩
            ((mem_visible_toFin d hℓ).mpr (by
              rw [range_castSuccEmb, coe_subset]; exact privScope_subset _)) le_rfl
            (le_top.trans_eq ((label_toFin d hℓ (.don 0 j)).trans ht).symm) ?_
          refine ((row_toFin d hℓ _ _ _).trans
            (rowValue_three d hk (by rw [kind_capCell]; rfl))).trans_le ?_
          exact le_of_eq ((hg3.trans (ite_eq_right (by rw [ht]; exact top_ne_bot))).symm.trans
            ((row_toFin d hℓ _ _ _).trans hrow).symm) }

end Extension

/-! ### The theorem -/

private theorem eq_three_or_four : ∀ C : Fin 5, (GatedExtensionCounterexample.cellScope C,
    GatedExtensionCounterexample.cellGrade C) = (univ, 2) → C = 3 ∨ C = 4 := by decide +kernel

/-- **Anchored donors of `P α` are labelled `⊥` or `⊤`**: if a stage type `d` on one point is
anchored in `P α` below a cell `C` of graded index `(univ, 2)`, every cell of `d` is labelled `⊥`
or `⊤`.  The labels of `P α` are `⊥` and `⊤`, which visibility replacement fixes, and `C` is
labelled `⊤`, so a label of `d` other than `⊥` and `⊤` would need an anchor labelled neither. -/
theorem labels_mem_bot_top {α : Ordinal.{u}} {d : StageType.{u} α 1}
    {C : Fin (GatedExtensionCounterexample.P α).card}
    (hC : (GatedExtensionCounterexample.P α).toCellScheme.gradedIndex C = (univ, 2))
    (ha : (GatedExtensionCounterexample.P α).IsAnchored C d) (j : Fin d.card) :
    d.label j = ⊥ ∨ d.label j = ⊤ := by
  by_contra hj; rw [not_or] at hj
  have hPC : (GatedExtensionCounterexample.P α).label C = ⊤ := by
    -- The labels of `P α` are `labelling ⊤ ⊤` (by definition).
    change GatedExtensionCounterexample.labelling ⊤ ⊤ C = ⊤
    rcases eq_three_or_four C hC with h | h <;> rw [h] <;> rfl
  obtain ⟨z, i, -, hz⟩ := ha j (by rw [(scope_eq_univ_and_grade_eq_one d j).1]; exact mem_univ _)
    hj.1 (hPC ▸ lt_top_iff_ne_top.mpr hj.2)
  have hz' : GatedExtensionCounterexample.labelling (⊤ : Label.{u}) ⊤ z = ⊥ ∨
      GatedExtensionCounterexample.labelling (⊤ : Label.{u}) ⊤ z = ⊤ := by
    fin_cases z; exacts [.inl rfl, .inl rfl, .inl rfl, .inr rfl, .inr rfl]
  change d.label j = visibilityReplace 2 i (GatedExtensionCounterexample.labelling ⊤ ⊤ z) at hz
  rcases hz' with h | h <;> rw [h] at hz
  exacts [hj.1 (hz.trans (visibilityReplace_bot _ _)), hj.2 (hz.trans (visibilityReplace_top _ _))]

/-- **The coupled gated pinned extension property at the private type `P α`**: the body of
`StageType.HasCoupledGatedPinnedExtensions` with the private type fixed to
`GatedExtensionCounterexample.P α` and every other input arbitrary.  The arities force the empty
root; the donor's labels are `⊥` or `⊤` (`labels_mem_bot_top`); the display is `display d`, with
the cap the chosen full private cell and the gate its copy (`extension`). -/
theorem coupledGatedPinnedExtension_P (α : Ordinal.{u}) {m : ℕ} (f : Fin m ↪ Fin 2)
    (p : StageType.{u} α m) (d : StageType.{u} α (m + 1))
    (C : Fin (GatedExtensionCounterexample.P α).card)
    (_hP : (GatedExtensionCounterexample.P α).IsLegal)
    (hp : restrictFace f (GatedExtensionCounterexample.P α) = some p) (hd : d.IsLegal)
    (hdp : restrictFace Fin.castSuccEmb d = some p)
    (hC : (GatedExtensionCounterexample.P α).toCellScheme.gradedIndex C = (univ, 2))
    (hne : (GatedExtensionCounterexample.P α).label C ≠ ⊥) (hm : m + 1 < 2)
    (ha : (GatedExtensionCounterexample.P α).IsAnchored C d) :
    ∃ E : StageType.CoupledGatedExtension (GatedExtensionCounterexample.P α) f d,
      E.display.label E.cap = (GatedExtensionCounterexample.P α).label C := by
  -- The legality of `P α` is not needed: the display is legal for every donor.
  obtain rfl : m = 0 := by omega
  have hℓ := labels_mem_bot_top hC ha
  rcases eq_three_or_four C hC with rfl | rfl
  · exact ⟨extension d hℓ hd f 0, label_toFin d hℓ _⟩
  · exact ⟨extension d hℓ hd f 1, label_toFin d hℓ _⟩

end VaughtConjecture.CoupledGateOnePointDonors
