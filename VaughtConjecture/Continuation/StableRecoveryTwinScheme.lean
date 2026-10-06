/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCounterexample
import VaughtConjecture.Extension.OrderedRow
import VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample

/-!
# The twin scheme: a legal scheme reading the twins through a cap

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap, the reference cells and the decoder of (R4)); semantic contract, item 8.

**The question.**  (R4) follows from stable recovery schemes for the graded cap calibration at
every `ξ < ω₁` (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`), a finite statement
that is open.  The marker and cap calibration is refuted at the twin donors of
`VaughtConjecture.Continuation.StableRecoveryCounterexample`: the two lifts `twinDonor₁`,
`twinDonor₂` of the five-cell type, which order its twins both ways over one root.  This file
builds the scheme, on four points, that recovers either order through a cap of grade `3`; the
stage types (the context, the donors, the recovery) are in
`VaughtConjecture.Continuation.StableRecoveryTwin`.

**The scheme** (`twinScheme o`, for the order `o` of the twins).  Four points: `0`, `1` (private),
`2` (the root) and `3` (the new point); the faces are the intervals of `0 < 1 < 2 < 3`, so
`{0, 1, 2}` (the context) and `{2, 3}` (the root and the new point) are faces.  There is one cell
at each of the twenty graded faces, and a second one at `({2, 3}, 1)`, `({1, 2, 3}, 1)` and
`(univ, 1)`: twenty-three cells.  Each has a **kind** (`cellKind`):

* **dead** (row `⊥`, so labelled `⊥` in every lawful labelling): the cells at `({0}, 1)`,
  `({1}, 1)`, `({3}, 1)`, `({0, 1}, 1)`, every cell of grade `2`, `({1, 2, 3}, 3)` and
  `(univ, 4)`;
* the **root kind**: the root `({2}, 1)` and the cells at `({1, 2}, 1)`, `({0, 1, 2}, 1)`, reading
  the cells of the root kind at `ω + 2`;
* the two **twin kinds**: the twins at `({2, 3}, 1)` and the two cells at each of `({1, 2, 3}, 1)`
  and `(univ, 1)`, reading the root kind and their own kind at `ω + 2` and the other twin kind at
  `1` (the rows of the five-cell scheme);
* the **cap** `({0, 1, 2}, 3)`, reading the root kind at `2` and itself at `ω + 3`;
* the **reading cell** `(univ, 3)`, reading the root kind and the higher twin kind at `2`, the
  lower twin kind at `1`, and the cap and itself at `ω + 3` (`readRow`).  Its row is the only one
  that depends on the order `o` (`kindRow_of_ne`).

**Its lawful labellings** (`isLawful_twinLabel`, `exists_of_isLawfulBelow`).  Below every pair they
are exactly the labellings `twinLabel R A B C` (`⊥` at the dead cells, `R` at the root kind, `A`
and `B` at the twin kinds, `C` at the cap and the reading cell) of the **twin tuples**
(`IsTwinTuple`, with `H`, `L` the higher and the lower twin for the order `o`): `R`, `H`, `L`
self-visible at `1` and `C` at `3`; `H, L ≤ R ≤ max H L` (the five-cell scheme); the capped root
`min R C` of finite part `2` or at least `3` (the cap reads the root at `2`); and, below the cap,
the higher twin equal to the root and the lower twin equal to the root lowered to finite part `1`
(the reading cell, `reading_of_transformsTo`).  The cells of the root kind copy the root, and the
pairs at `({1, 2, 3}, 1)` and `(univ, 1)` copy the twins.  Absent twins are set to the root and to
the root lowered below the cap (`isTwinTuple_default`).  The witnesses are
`ThinCompletion.blockConst` (the root and twin kinds) and the strip shifter at the grade `3`
(`TwoFaceLiftExistsCounterexample.strip3`, at the cap and the reading cell).

**The cap decodes the twins** (`IsTwinTuple.twins_eq_of_lt`): with the cap above the root, the
higher twin is the root and the lower twin the root lowered to finite part `1`; with the root
`λ_ξ + 2` this is `(λ_ξ + 2, λ_ξ + 1)`, in the order `o`.

**Legality** (`isLegal_twinScheme`): well formed, coded, consistent (each row is the twin
labelling of a twin tuple), complete, and bountiful (`cappedLift_twinScheme`): the parameters
prescribed below the smaller pair are kept and the others lifted (`exists_isTwinTuple_lift`), an
unprescribed cap to the ambient cap capped at `c`, unprescribed twins by `exists_twinLift` (forced
below the cap, an ambient twin below `c` kept, the others raised to the root).  The lift rests on
two facts about caps self-visible at `3`: they do not separate finite parts below `3`
(`le_visibilityReplace_three_one`, `visibilityReplace_three_two_lt`).

**Where bountifulness constrains the reading** (informal; not compiled as necessity statements;
the scheme above meets both constraints, which are compiled as part of its legality).  A cell of
grade `1` held up by the root reads the twins in one order (or as equal); since every lawful
labelling of the twins below `({2, 3}, 1)` lifts (bountifulness at the cap `⊥`), every graded face
of grade `1` containing the twins carries a pair of cells reading them in both orders, here at
`({1, 2, 3}, 1)` and `(univ, 1)`.  And the reading cell forces the capped root to have finite part
`2` or at least `3`; a labelling of the context `({0, 1, 2}, 3)` without that constraint would not
lift to `(univ, 3)`, so the cap reads the root at `2` as the reading cell does.

## Implementation notes

The two orders of the twins are compared only through rows and values that do not depend on the
order (`baseRow`, `kindRow_of_ne`, `kindValue_of_ne`), and these two lemmas are proved by
`fin_cases` and `simp`.  A proof by `rfl` (or by `match` with `rfl` branches), like any `rfl`
between `twinScheme false` and `twinScheme true`, makes the kernel compare the tails of the `![…]`
rows by unfolding their ordinal labels, which takes minutes and gigabytes.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryTwin

open Finset Label StageType ThinCompletion CandidateCounterexamples StableRecoveryCounterexample
open TwoFaceLiftExistsCounterexample (strip3 strip3_natCast strip3_of_not_lt strip3_bot
  isWitness_strip3)
open Ordinal hiding univ

/-! ### Labels below a cap self-visible at `3` -/

section Labels

variable {x y c : Label.{u}}

/-- Visibility replacement at `3` with value `1` gives a label self-visible at `1`. -/
theorem isSelfVisible_visibilityReplace_three_one (x : Label.{u}) :
    IsSelfVisible 1 (visibilityReplace 3 1 x) := by
  by_cases hb : x = ⊥
  · rw [hb, visibilityReplace_bot]; exact isSelfVisible_bot _
  by_cases ht : x = ⊤
  · rw [ht, visibilityReplace_top]; exact isSelfVisible_top _
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  rw [visibilityReplace_block, isSelfVisible_block]
  split_ifs <;> omega

/-- Visibility replacement at `3` with value `1` does not raise a label self-visible at `1`. -/
theorem visibilityReplace_three_one_le (hx : IsSelfVisible 1 x) :
    visibilityReplace 3 1 x ≤ x := by
  by_cases hb : x = ⊥
  · rw [hb, visibilityReplace_bot]
  by_cases ht : x = ⊤
  · rw [ht, visibilityReplace_top]
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  have hn : 1 ≤ n := isSelfVisible_block.mp hx
  rw [visibilityReplace_block, WithBot.coe_le_coe, WithTop.coe_le_coe,
    omega0_mul_add_natCast_le_iff]
  exact .inr ⟨rfl, by split_ifs <;> omega⟩

/-- **A cap self-visible at `3` does not separate finite parts below `3`**: a label `c`
self-visible at `3` below `y` lies below `visibilityReplace 3 1 y`. -/
theorem le_visibilityReplace_three_one (hc : IsSelfVisible 3 c) (h : c ≤ y) :
    c ≤ visibilityReplace 3 1 y :=
  (hc.visibilityReplace_eq 1).symm.le.trans (monotone_visibilityReplace (by omega) h)

/-- **A cap self-visible at `3` above a label stays above its replacement at `2`**: for `c`
self-visible at `3` and `y < c`, `visibilityReplace 3 2 y < c`. -/
theorem visibilityReplace_three_two_lt (hc : IsSelfVisible 3 c) (h : y < c) :
    visibilityReplace 3 2 y < c := by
  by_cases hyb : y = ⊥
  · rw [hyb, visibilityReplace_bot]; exact hyb ▸ h
  by_cases hct : c = ⊤
  · rw [hct]
    refine lt_top_iff_ne_top.mpr fun h' ↦ ?_
    rw [visibilityReplace_eq_top_iff] at h'
    exact absurd (h' ▸ h) (not_lt.mpr le_top)
  have hyt : y ≠ ⊤ := fun h' ↦ absurd (h' ▸ h) (not_lt.mpr le_top)
  have hcb : c ≠ ⊥ := fun h' ↦ absurd (h' ▸ h) (not_lt.mpr bot_le)
  obtain ⟨q, n, rfl⟩ := exists_block hyb hyt
  obtain ⟨q', n', rfl⟩ := exists_block hcb hct
  have hn' : 3 ≤ n' := isSelfVisible_block.mp hc
  rw [visibilityReplace_block]
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe] at h ⊢
  rw [← not_le, omega0_mul_add_natCast_le_iff] at h ⊢
  push Not at h ⊢
  refine ⟨h.1, fun hq ↦ ?_⟩
  have := h.2 hq
  split_ifs <;> omega

end Labels

/-! ### The scheme -/

/-- The cells of the twin scheme on `Fin 4`, with faces the intervals of `0 < 1 < 2 < 3`: the
twenty graded faces, with two cells at each of `({2, 3}, 1)`, `({1, 2, 3}, 1)` and `(univ, 1)`.
In order: `({0}, 1)`, `({1}, 1)`, `({2}, 1)`, `({3}, 1)`, `({0, 1}, 1)`, `({1, 2}, 1)`, two at
`({2, 3}, 1)`, `({0, 1, 2}, 1)`, two at `({1, 2, 3}, 1)`, two at `(univ, 1)`, then `({0, 1}, 2)`,
`({1, 2}, 2)`, `({2, 3}, 2)`, `({0, 1, 2}, 2)`, `({1, 2, 3}, 2)`, `(univ, 2)`, `({0, 1, 2}, 3)`,
`({1, 2, 3}, 3)`, `(univ, 3)`, `(univ, 4)`. -/
def twinCells : CellScheme (Fin 23) (Fin 4) :=
  ⟨univ, Geometry.intervalPlan univ,
    ![{0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {2, 3}, {2, 3}, {0, 1, 2}, {1, 2, 3}, {1, 2, 3}, univ,
      univ, {0, 1}, {1, 2}, {2, 3}, {0, 1, 2}, {1, 2, 3}, univ, {0, 1, 2}, {1, 2, 3}, univ, univ],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4]⟩

/-- The kind of each cell: `0` dead, `1` the root `({2}, 1)` and the cells `({1, 2}, 1)`,
`({0, 1, 2}, 1)`, `2` the first twin and the first cells at `({1, 2, 3}, 1)` and `(univ, 1)`, `3`
the second twin and the second cells there, `4` the cap `({0, 1, 2}, 3)`, `5` the reading cell
`(univ, 3)`. -/
def cellKind : Fin 23 → Fin 6 :=
  ![0, 0, 1, 0, 0, 1, 2, 3, 1, 2, 3, 2, 3, 0, 0, 0, 0, 0, 0, 4, 0, 5, 0]

/-- The first of two values when `o`, the second otherwise: the value of the higher twin, for the
order `o` of the twins (`o = true`: the first twin above the second). -/
def twinHi {α : Type*} (o : Bool) (a b : α) : α := if o then a else b

/-- The second of two values when `o`, the first otherwise: the value of the lower twin. -/
def twinLo {α : Type*} (o : Bool) (a b : α) : α := if o then b else a

/-- For the order `true` the higher value is the first. -/
@[simp] theorem twinHi_true {α : Type*} (a b : α) : twinHi true a b = a := rfl

/-- For the order `false` the higher value is the second. -/
@[simp] theorem twinHi_false {α : Type*} (a b : α) : twinHi false a b = b := rfl

/-- For the order `true` the lower value is the second. -/
@[simp] theorem twinLo_true {α : Type*} (a b : α) : twinLo true a b = b := rfl

/-- For the order `false` the lower value is the first. -/
@[simp] theorem twinLo_false {α : Type*} (a b : α) : twinLo false a b = a := rfl

/-- The label `ω + 2`, the value of the five-cell scheme at its live cells. -/
noncomputable abbrev omegaTwo : Label.{u} :=
  ((ω + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

/-- The row of the reading cell, by the kind of the cell read: the root kind at `2`, the higher
twin kind at `2`, the lower at `1`, the cap and itself at `ω + 3`. -/
noncomputable def readRow (o : Bool) : Fin 6 → Label.{u} :=
  ![⊥, gridPoint 2 0, twinHi o (gridPoint 2 0) (gridPoint 1 0),
    twinLo o (gridPoint 2 0) (gridPoint 1 0), gridPoint 3 1, gridPoint 3 1]

/-- The rows, by the kind of the cell and the kind of the cell read.  The root kind reads itself
at `ω + 2`; a twin kind reads the root kind and itself at `ω + 2` and the other twin kind at `1`
(the rows of the five-cell scheme); the cap reads the root kind at `2` and itself at `ω + 3`; the
reading cell reads by `readRow o`. -/
noncomputable def kindRow (o : Bool) : Fin 6 → Fin 6 → Label.{u} :=
  ![fun _ ↦ ⊥,
    ![⊥, omegaTwo, ⊥, ⊥, ⊥, ⊥],
    ![⊥, omegaTwo, omegaTwo, 1, ⊥, ⊥],
    ![⊥, omegaTwo, 1, omegaTwo, ⊥, ⊥],
    ![⊥, gridPoint 2 0, ⊥, ⊥, gridPoint 3 1, ⊥],
    readRow o]

/-- The **twin scheme** for the order `o` of the twins: the cells `twinCells` with the rows
`kindRow o`. -/
noncomputable abbrev twinScheme (o : Bool) : Scheme.{u} 4 :=
  ⟨23, twinCells, ⟨fun s d ↦ kindRow o (cellKind s) (cellKind d.1)⟩⟩

/-- The rows of the kinds other than the reading cell, which do not depend on the order of the
twins. -/
noncomputable def baseRow : Fin 6 → Fin 6 → Label.{u} :=
  ![fun _ ↦ ⊥,
    ![⊥, omegaTwo, ⊥, ⊥, ⊥, ⊥],
    ![⊥, omegaTwo, omegaTwo, 1, ⊥, ⊥],
    ![⊥, omegaTwo, 1, omegaTwo, ⊥, ⊥],
    ![⊥, gridPoint 2 0, ⊥, ⊥, gridPoint 3 1, ⊥],
    fun _ ↦ ⊥]

/-- Away from the reading cell the rows do not depend on the order of the twins. -/
theorem kindRow_of_ne (o : Bool) {k : Fin 6} (hk : k ≠ 5) (k' : Fin 6) :
    kindRow.{u} o k k' = baseRow k k' := by
  fin_cases k <;> simp [kindRow, baseRow] at hk ⊢

/-- The cells of the twin scheme do not depend on the order of the twins. -/
@[simp] theorem twinScheme_toCellScheme (o : Bool) : (twinScheme.{u} o).toCellScheme = twinCells :=
  rfl

/-- The row of a cell of the twin scheme, by kinds. -/
theorem twinScheme_row (o : Bool) (s : Fin 23) (d) :
    (twinScheme.{u} o).rows.row s d = kindRow o (cellKind s) (cellKind d.1) :=
  rfl

/-! ### Twin tuples -/

/-- The labels of the kinds for the parameters `R` (the root kind), `A` (the first twin kind), `B`
(the second twin kind) and `C` (the cap and the reading cell). -/
noncomputable def kindValue (R A B C : Label.{u}) : Fin 6 → Label.{u} := ![⊥, R, A, B, C, C]

/-- The **twin labelling** of parameters `R`, `A`, `B`, `C`. -/
noncomputable def twinLabel (R A B C : Label.{u}) (d : Fin 23) : Label.{u} :=
  kindValue R A B C (cellKind d)

/-- Away from the twin kinds the labels do not depend on the twins. -/
theorem kindValue_of_ne {R A B A' B' C : Label.{u}} {k : Fin 6} (h2 : k ≠ 2) (h3 : k ≠ 3) :
    kindValue R A B C k = kindValue R A' B' C k := by
  fin_cases k <;> simp [kindValue] at h2 h3 ⊢

/-- A **twin tuple**: the parameters of a lawful twin labelling, with the higher twin `H` and the
lower twin `L`. -/
structure IsTwinTuple (R H L C : Label.{u}) : Prop where
  /-- The root is self-visible at `1`. -/
  isSelfVisible_root : IsSelfVisible 1 R
  /-- The higher twin is self-visible at `1`. -/
  isSelfVisible_hi : IsSelfVisible 1 H
  /-- The lower twin is self-visible at `1`. -/
  isSelfVisible_lo : IsSelfVisible 1 L
  /-- The cap is self-visible at `3`. -/
  isSelfVisible_cap : IsSelfVisible 3 C
  /-- The higher twin is at most the root. -/
  hi_le : H ≤ R
  /-- The lower twin is at most the root. -/
  lo_le : L ≤ R
  /-- The root is one of the twins. -/
  le_max : R ≤ max H L
  /-- The root, capped, has finite part `2` or at least `3` (the cap reads it at `2`). -/
  visibilityReplace_eq : visibilityReplace 3 2 (min R C) = min R C
  /-- The higher twin agrees with the root below the cap (the reading cell reads both at
  `2`). -/
  min_hi : min H C = min R C
  /-- The lower twin is the root lowered to finite part `1`, below the cap (the reading cell
  reads it at `1`). -/
  min_lo : min L C = min (visibilityReplace 3 1 (min R C)) C

/-- A twin tuple in the order `o`, read on the twins `A` and `B`: both at most the root, the root
one of them, and both self-visible at `1`. -/
theorem IsTwinTuple.twins {o : Bool} {R A B C : Label.{u}}
    (h : IsTwinTuple R (twinHi o A B) (twinLo o A B) C) :
    A ≤ R ∧ B ≤ R ∧ R ≤ max A B ∧ IsSelfVisible 1 A ∧ IsSelfVisible 1 B := by
  cases o
  · exact ⟨h.lo_le, h.hi_le, max_comm A B ▸ h.le_max, h.isSelfVisible_lo, h.isSelfVisible_hi⟩
  · exact ⟨h.hi_le, h.lo_le, h.le_max, h.isSelfVisible_hi, h.isSelfVisible_lo⟩

/-- The tuple of a root alone, with a cap: the higher twin at the root and the lower twin the root
lowered to finite part `1` below the cap. -/
theorem isTwinTuple_default {R C : Label.{u}} (hR : IsSelfVisible 1 R) (hC : IsSelfVisible 3 C)
    (hv : visibilityReplace 3 2 (min R C) = min R C) :
    IsTwinTuple R R (visibilityReplace 3 1 (min R C)) C := by
  refine ⟨hR, hR, isSelfVisible_visibilityReplace_three_one _, hC, le_rfl, ?_, le_max_left _ _,
    hv, rfl, rfl⟩
  rcases le_total R C with h | h
  · rw [min_eq_left h]; exact visibilityReplace_three_one_le hR
  · rw [min_eq_right h, hC.visibilityReplace_eq]; exact h

/-! ### Row values -/

section Values

/-- The label `ω + 2` is self-visible at `1`. -/
private theorem isSelfVisible_omegaTwo : IsSelfVisible 1 omegaTwo.{u} := by
  have : omegaTwo.{u} = ((ω * ((1 : ℕ) : Ordinal.{u}) + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) :
      Label.{u}) := by rw [Nat.cast_one, mul_one]
  rw [this, isSelfVisible_block]; omega

/-- `1 ≤ ω + 2`. -/
private theorem one_le_omegaTwo : (1 : Label.{u}) ≤ omegaTwo.{u} := by
  rw [show (1 : Label.{u}) = ((1 : Ordinal.{u}) : Label.{u}) from rfl, WithBot.coe_le_coe,
    WithTop.coe_le_coe]
  exact (one_lt_omega0).le.trans le_self_add

/-- `blockConst a b` sends `1` to `a`. -/
private theorem blockConst_one {a b : Label.{u}} : blockConst a b 1 = a := by
  unfold blockConst
  rw [ite_eq_right (by simp), ite_eq_left (by simp)]

/-- `blockConst a b` sends `ω + 2` to `b`. -/
private theorem blockConst_omegaTwo {a b : Label.{u}} : blockConst a b omegaTwo = b := by
  unfold blockConst
  rw [ite_eq_right WithBot.coe_ne_bot, ite_eq_right]
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, mul_one, not_lt]
  exact le_self_add

/-- `blockConst a b` fixes `⊥`. -/
private theorem blockConst_bot' {a b : Label.{u}} : blockConst a b ⊥ = ⊥ := by
  unfold blockConst; simp

/-- A grid point of the block `0` is a natural number. -/
private theorem gridPoint_zero_eq (k : ℕ) : gridPoint.{u} k 0 = (k : Label.{u}) := by
  rw [gridPoint, natCast_label]; simp

/-- The strip shifter at the grade `3` on the natural number `k ≤ 3`. -/
private theorem strip3_gridPoint_zero {x : Label.{u}} {k : ℕ} (hk : k ≤ 3) :
    strip3 x (gridPoint.{u} k 0) = visibilityReplace 3 k x := by
  rw [gridPoint_zero_eq, strip3_natCast, min_eq_left hk]

/-- The strip shifter at the grade `3` sends `ω + 3` to the formal top. -/
private theorem strip3_gridPoint_three_one {x : Label.{u}} : strip3 x (gridPoint.{u} 3 1) = ⊤ := by
  refine strip3_of_not_lt (gridPoint_ne_bot 3 1) ?_
  rw [gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe, not_lt, Nat.cast_one, mul_one]
  exact le_self_add

/-- Visibility replacement at `3` of a natural number below `3`. -/
private theorem visibilityReplace_gridPoint (k i : ℕ) (hk : k < 3) :
    visibilityReplace 3 i (gridPoint.{u} k 0) = gridPoint i 0 := by
  rw [gridPoint, visibilityReplace_block, ite_eq_left hk, gridPoint]

/-- `2 < ω + 3`. -/
private theorem gridPoint_two_lt_three : gridPoint.{u} 2 0 < gridPoint 3 1 := by
  rw [gridPoint, gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  exact omega0_mul_add_natCast_lt (by simp) 2 _

/-- `1 ≤ 2`, as grid points. -/
private theorem gridPoint_one_le_two : gridPoint.{u} 1 0 ≤ gridPoint 2 0 := by
  rw [gridPoint, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff]
  exact .inr ⟨rfl, by omega⟩

/-- The tuple read by the cap and the reading cell: root `2`, higher twin `2`, lower twin `1`, cap
`ω + 3`. -/
theorem isTwinTuple_read :
    IsTwinTuple (gridPoint.{u} 2 0) (gridPoint 2 0) (gridPoint 1 0) (gridPoint 3 1) := by
  have hm : min (gridPoint.{u} 2 0) (gridPoint 3 1) = gridPoint 2 0 :=
    min_eq_left gridPoint_two_lt_three.le
  refine ⟨(isSelfVisible_gridPoint 2 0).mono (by omega), (isSelfVisible_gridPoint 2 0).mono
    (by omega), isSelfVisible_gridPoint 1 0, isSelfVisible_gridPoint 3 1, le_rfl,
    gridPoint_one_le_two, le_max_left _ _, ?_, rfl, ?_⟩
  · rw [hm, visibilityReplace_gridPoint 2 2 (by omega)]
  · rw [hm, visibilityReplace_gridPoint 2 1 (by omega)]

/-- The tuple read by a twin: root and one twin at `ω + 2`, the other twin at `1`. -/
theorem isTwinTuple_twin : IsTwinTuple omegaTwo.{u} omegaTwo 1 ⊥ :=
  ⟨isSelfVisible_omegaTwo, isSelfVisible_omegaTwo, isSelfVisible_one.mpr le_rfl,
    isSelfVisible_bot _, le_rfl, one_le_omegaTwo, le_max_left _ _, by simp, by simp, by simp⟩

/-- The tuple read by the root kind: everything at `ω + 2`, no cap. -/
theorem isTwinTuple_root : IsTwinTuple omegaTwo.{u} omegaTwo omegaTwo ⊥ :=
  ⟨isSelfVisible_omegaTwo, isSelfVisible_omegaTwo, isSelfVisible_omegaTwo,
    isSelfVisible_bot _, le_rfl, le_rfl, le_max_left _ _, by simp, by simp, by simp⟩

end Values

/-! ### Lawful labellings -/

section Kinds

/-- The cells below a cell of the root kind are dead or of the root kind. -/
private theorem kind_below_root : ∀ s d : Fin 23, cellKind s = 1 →
    twinCells.gradedIndex d ≤ twinCells.gradedIndex s → cellKind d = 0 ∨ cellKind d = 1 := by
  decide

/-- The cells below a cell of a twin kind are dead, of the root kind or of a twin kind. -/
private theorem kind_below_twin : ∀ s d : Fin 23, (cellKind s = 2 ∨ cellKind s = 3) →
    twinCells.gradedIndex d ≤ twinCells.gradedIndex s → (cellKind d : ℕ) ≤ 3 := by
  decide

/-- The cells below the cap are dead, of the root kind, or the cap. -/
private theorem kind_below_cap : ∀ s d : Fin 23, cellKind s = 4 →
    twinCells.gradedIndex d ≤ twinCells.gradedIndex s →
      cellKind d = 0 ∨ cellKind d = 1 ∨ cellKind d = 4 := by
  decide

/-- The cells of the root kind and of the twin kinds have grade `1`; the cap and the reading cell
have grade `3`. -/
private theorem grade_of_kind : ∀ s : Fin 23,
    ((cellKind s : ℕ) ∈ ({1, 2, 3} : Finset ℕ) → twinCells.grade s = 1) ∧
      ((cellKind s : ℕ) ∈ ({4, 5} : Finset ℕ) → twinCells.grade s = 3) := by
  decide

/-- Availability, by kinds: a cell whose scope lies in that of `t`, of the same grade, is dead if
`t` is; dead or of the root kind if `t` is of the root kind; not the cap or the reading cell if
`t` is of a twin kind; and dead, the cap or the reading cell if `t` is the cap or the reading
cell. -/
private theorem kind_availability : ∀ s t : Fin 23, twinCells.scope s ⊆ twinCells.scope t →
    twinCells.grade s = twinCells.grade t →
      (cellKind t = 0 → cellKind s = 0) ∧ (cellKind t = 1 → cellKind s = 0 ∨ cellKind s = 1) ∧
      ((cellKind t = 2 ∨ cellKind t = 3) → (cellKind s : ℕ) ≤ 3) ∧
      (4 ≤ (cellKind t : ℕ) → cellKind s = 0 ∨ 4 ≤ (cellKind s : ℕ)) := by
  decide

/-- Every graded index of a twin kind carries a cell of each twin kind. -/
private theorem exists_twin_kinds : ∀ t : Fin 23, (cellKind t = 2 ∨ cellKind t = 3) →
    (∃ u, twinCells.gradedIndex u = twinCells.gradedIndex t ∧ cellKind u = 2) ∧
      ∃ u, twinCells.gradedIndex u = twinCells.gradedIndex t ∧ cellKind u = 3 := by
  decide

end Kinds

/-- Locality at `s` from a witness with the suppressor constant at `v` up to `K`, checked by the
kinds of the cells below `s`. -/
private theorem transformsTo_of_kinds {o : Bool} {s : Fin 23} {R A B C v : Label.{u}} {K : ℕ}
    {σ : Label.{u} → Label.{u}} (hv : twinLabel R A B C s = v)
    (hw : IsWitness (constStepSuppressor K v) σ) (hK : twinCells.grade s ≤ K)
    (h : ∀ d : Fin 23, twinCells.gradedIndex d ≤ twinCells.gradedIndex s →
      min (kindValue R A B C (cellKind d)) v = min (σ (kindRow o (cellKind s) (cellKind d))) v) :
    TransformsTo (fun d : twinCells.below (twinCells.gradedIndex s) ↦ twinCells.grade d)
      ((twinScheme.{u} o).rows.row s)
      (fun d ↦ min (twinLabel R A B C d) (twinLabel R A B C s)) :=
  ⟨_, σ, hw, fun d ↦ by
    -- the labelling of locality at `s`, and the suppressor at the grade of `d`
    change min (twinLabel R A B C d.1) (twinLabel R A B C s) =
      min (σ (kindRow o (cellKind s) (cellKind d.1))) (if twinCells.grade d.1 ≤ K then v else ⊥)
    rw [ite_eq_left (show twinCells.grade d.1 ≤ K from d.2.2.trans hK), hv]
    exact h d.1 d.2⟩

/-- **The twin labellings of twin tuples are lawful.**  At the root kind the shifter is constant at
the root; at a twin kind it is the other twin capped on the natural numbers and the twin above
(`ThinCompletion.blockConst`); at the cap and the reading cell it is the strip shifter at the grade
`3` of the capped root (`TwoFaceLiftExistsCounterexample.strip3`).  Availability: a cell of the
root kind has the root's label, a pair of twin kinds has the root as its larger label, and the
cap lies below the reading cell, with the same label. -/
theorem isLawful_twinLabel {o : Bool} {R A B C : Label.{u}}
    (h : IsTwinTuple R (twinHi o A B) (twinLo o A B) C) :
    (twinScheme.{u} o).rows.IsLawful (twinLabel R A B C) := by
  obtain ⟨hAR, hBR, hRAB, hA1, hB1⟩ := h.twins
  have hR1 := h.isSelfVisible_root
  have hC3 := h.isSelfVisible_cap
  refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · -- the order law, by kinds
    obtain ⟨g1, g3⟩ := grade_of_kind d
    simp only [twinLabel]
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    rw [hk] at g1 g3 ⊢
    fin_cases k
    · exact isSelfVisible_bot _
    · rw [g1 (by decide)]; exact hR1
    · rw [g1 (by decide)]; exact hA1
    · rw [g1 (by decide)]; exact hB1
    · rw [g3 (by decide)]; exact hC3
    · rw [g3 (by decide)]; exact hC3
  · -- locality, by the kind of `s`
    obtain ⟨k, hk⟩ : ∃ k, cellKind s = k := ⟨_, rfl⟩
    have hg := grade_of_kind s
    rw [hk] at hg
    have hv : twinLabel R A B C s = kindValue R A B C k := by rw [twinLabel, hk]
    fin_cases k
    · -- dead: the label is `⊥`
      convert TransformsTo.bot _ ((twinScheme.{u} o).rows.row s) using 1
      funext d
      rw [hv]
      simp [kindValue]
    · -- the root kind: the constant shifter `R`
      refine transformsTo_of_kinds hv (isWitness_blockConst hR1 hR1 le_rfl) (by simp at hg; omega)
        fun d hd ↦ ?_
      rcases kind_below_root s d hk hd with h0 | h0 <;> simp [hk, h0, kindValue, kindRow,
        blockConst_bot', blockConst_omegaTwo]
    · -- the first twin kind: `B ∧ A` on the natural numbers, `A` above
      refine transformsTo_of_kinds hv (isWitness_blockConst (hB1.min hA1) hA1 (min_le_right _ _))
        (by simp at hg; omega) fun d hd ↦ ?_
      have hd3 := kind_below_twin s d (.inl hk) hd
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj] at hd3 ⊢
      fin_cases j <;> simp at hd3 <;> simp [hk, kindValue, kindRow, blockConst_bot',
        blockConst_omegaTwo, blockConst_one, min_eq_right hAR]
    · -- the second twin kind: `A ∧ B` on the natural numbers, `B` above
      refine transformsTo_of_kinds hv (isWitness_blockConst (hA1.min hB1) hB1 (min_le_right _ _))
        (by simp at hg; omega) fun d hd ↦ ?_
      have hd3 := kind_below_twin s d (.inr hk) hd
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj] at hd3 ⊢
      fin_cases j <;> simp at hd3 <;> simp [hk, kindValue, kindRow, blockConst_bot',
        blockConst_omegaTwo, blockConst_one, min_eq_right hBR]
    · -- the cap: the strip shifter of `R ∧ C`
      refine transformsTo_of_kinds hv (isWitness_strip3 (A := min R C) hC3)
        (by simp at hg; omega) fun d hd ↦ ?_
      rcases kind_below_cap s d hk hd with h0 | h1 | h4
      · simp [hk, h0, kindValue, kindRow, strip3_bot]
      · simp only [hk, h1, kindValue, kindRow]
        simp [strip3_gridPoint_zero (by omega : 2 ≤ 3), h.visibilityReplace_eq]
      · simp [hk, h4, kindValue, kindRow, strip3_gridPoint_three_one]
    · -- the reading cell: the strip shifter of `R ∧ C`
      refine transformsTo_of_kinds hv (isWitness_strip3 (A := min R C) hC3)
        (by simp at hg; omega) fun d hd ↦ ?_
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj]
      have h2 := strip3_gridPoint_zero (x := min R C) (by omega : 2 ≤ 3)
      have h1 := strip3_gridPoint_zero (x := min R C) (by omega : 1 ≤ 3)
      rw [h.visibilityReplace_eq] at h2
      have hH := h.min_hi
      have hL := h.min_lo
      fin_cases j
      · simp [hk, kindValue, kindRow, readRow, strip3_bot]
      · simp [hk, kindValue, kindRow, readRow, h2]
      · cases o <;> simp_all [kindValue, kindRow, readRow]
      · cases o <;> simp_all [kindValue, kindRow, readRow]
      · simp [hk, kindValue, kindRow, readRow, strip3_gridPoint_three_one]
      · simp [hk, kindValue, kindRow, readRow, strip3_gridPoint_three_one]
  · -- availability, by the kind of `t`
    obtain ⟨h0, h1, h23, h45⟩ := kind_availability s t hst hg
    -- the twin labelling, by kinds
    change ∃ u, _ ∧ kindValue R A B C (cellKind s) ≤ kindValue R A B C (cellKind u)
    generalize cellKind s = j at h0 h1 h23 h45 ⊢
    obtain ⟨k, hk⟩ : ∃ k, cellKind t = k := ⟨_, rfl⟩
    rw [hk] at h0 h1 h23 h45
    have hsR : (j : ℕ) ≤ 3 → kindValue R A B C j ≤ R := fun hj ↦ by
      fin_cases j <;> simp_all [kindValue]
    have htwin : (cellKind t = 2 ∨ cellKind t = 3) → ∃ u,
        twinCells.gradedIndex u = twinCells.gradedIndex t ∧ R ≤ kindValue R A B C (cellKind u) :=
      fun h' ↦ by
        obtain ⟨⟨u, hu, hu2⟩, ⟨u', hu', hu3⟩⟩ := exists_twin_kinds t h'
        rcases le_total A B with hAB | hAB
        · exact ⟨u', hu', by rw [hu3]; exact hRAB.trans_eq (max_eq_right hAB)⟩
        · exact ⟨u, hu, by rw [hu2]; exact hRAB.trans_eq (max_eq_left hAB)⟩
    fin_cases k
    · exact ⟨t, rfl, by rw [h0 rfl]; simp [kindValue]⟩
    · refine ⟨t, rfl, ?_⟩
      rw [hk]
      rcases h1 rfl with rfl | rfl <;> simp [kindValue]
    · obtain ⟨u, hu, hRu⟩ := htwin (.inl hk)
      exact ⟨u, hu, (hsR (h23 (.inl rfl))).trans hRu⟩
    · obtain ⟨u, hu, hRu⟩ := htwin (.inr hk)
      exact ⟨u, hu, (hsR (h23 (.inr rfl))).trans hRu⟩
    · refine ⟨t, rfl, ?_⟩
      rw [hk]
      have := h45 (by simp)
      fin_cases j <;> simp_all [kindValue]
    · refine ⟨t, rfl, ?_⟩
      rw [hk]
      have := h45 (by simp)
      fin_cases j <;> simp_all [kindValue]

/-! ### The lift of parameters -/

section Lift

variable {R C qR qH qL qC c : Label.{u}}

/-- A label at most the root and the cap of a twin tuple is at most its higher twin. -/
private theorem le_hi_of_le (hq : IsTwinTuple qR qH qL qC) (hR : c ≤ qR) (hC : c ≤ qC) :
    c ≤ qH := by
  have : c ≤ min qH qC := hq.min_hi ▸ le_min hR hC
  exact this.trans (min_le_left _ _)

/-- A label self-visible at `3`, at most the root and the cap of a twin tuple, is at most its lower
twin. -/
private theorem le_lo_of_le (hq : IsTwinTuple qR qH qL qC) (hc : IsSelfVisible 3 c) (hR : c ≤ qR)
    (hC : c ≤ qC) : c ≤ qL := by
  have h1 : c ≤ visibilityReplace 3 1 (min qR qC) :=
    le_visibilityReplace_three_one hc (le_min hR hC)
  have : c ≤ min qL qC := hq.min_lo ▸ le_min h1 hC
  exact this.trans (min_le_left _ _)

/-- **The cap decodes the twins**: in a twin tuple with the cap above the root, the higher twin is
the root and the lower twin is the root lowered to finite part `1`. -/
theorem IsTwinTuple.twins_eq_of_lt (hq : IsTwinTuple qR qH qL qC) (h : qR < qC) :
    qH = qR ∧ qL = visibilityReplace 3 1 qR := by
  have hm : min qR qC = qR := min_eq_left h.le
  have hH := hq.min_hi
  rw [hm] at hH
  refine ⟨Label.eq_of_min_eq_of_lt (by rw [hH, min_eq_left h.le]) h, ?_⟩
  have hL := hq.min_lo
  rw [hm] at hL
  have hle : visibilityReplace 3 1 qR < qC :=
    (visibilityReplace_three_one_le hq.isSelfVisible_root).trans_lt h
  exact Label.eq_of_min_eq_of_lt hL.symm hle

/-- At or below the root, both twins lie above the cap. -/
private theorem le_twins_of_le (hq : IsTwinTuple qR qH qL qC) (h : qC ≤ qR) :
    qC ≤ qH ∧ qC ≤ qL := by
  have hm : min qR qC = qC := min_eq_right h
  have hH := hq.min_hi
  have hL := hq.min_lo
  rw [hm] at hH hL
  rw [hq.isSelfVisible_cap.visibilityReplace_eq, min_self] at hL
  exact ⟨min_eq_right_iff.mp hH, min_eq_right_iff.mp hL⟩

/-- **The lift of the twins.**  Given a root `R` and a cap `C` (self-visible at `1` and `3`, with
the capped root of finite part `2` or at least `3`) agreeing with a twin tuple `q` capped at `c`,
where `c` is self-visible at `3` unless the cap of `q` is `⊥`, some twins complete `R` and `C` to
a twin tuple agreeing with `q` capped at `c`.  Below the cap the twins are forced; at or above it
an ambient twin below `c` is kept and the others are raised to the root. -/
theorem exists_twinLift (hR1 : IsSelfVisible 1 R) (hC3 : IsSelfVisible 3 C)
    (hv : visibilityReplace 3 2 (min R C) = min R C) (hq : IsTwinTuple qR qH qL qC)
    (hc : IsSelfVisible 3 c ∨ qC = ⊥) (hRc : min R c = min qR c) (hCc : min C c = min qC c) :
    ∃ H L, IsTwinTuple R H L C ∧ min H c = min qH c ∧ min L c = min qL c := by
  rcases lt_or_ge R C with hRC | hCR
  · -- the cap above the root: the twins are forced
    have hm : min R C = R := min_eq_left hRC.le
    have hc3 : IsSelfVisible 3 c := by
      rcases hc with hc | hc
      · exact hc
      · have : min C c = ⊥ := by rw [hCc, hc, min_eq_left bot_le]
        rcases min_eq_iff.mp this with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd (h1 ▸ hRC) (not_lt.mpr bot_le)
        · rw [h1]; exact isSelfVisible_bot _
    refine ⟨R, visibilityReplace 3 1 R, ?_, ?_⟩
    · have := isTwinTuple_default hR1 hC3 hv
      rwa [hm] at this
    rcases le_or_gt c R with hcR | hRc'
    · -- the cap of the lift at most the root: everything is at least `c`
      have hqR : c ≤ qR := min_eq_right_iff.mp ((min_eq_right hcR).symm.trans hRc).symm
      have hqC : c ≤ qC := min_eq_right_iff.mp
        ((min_eq_right (hcR.trans hRC.le)).symm.trans hCc).symm
      rw [min_eq_right hcR, min_eq_right (le_hi_of_le hq hqR hqC),
        min_eq_right (le_visibilityReplace_three_one hc3 hcR),
        min_eq_right (le_lo_of_le hq hc3 hqR hqC)]
      exact ⟨rfl, rfl⟩
    · -- the root below `c`: the root of `q` is `R`, and its cap is above it
      have hqR : qR = R := Label.eq_of_min_eq_of_lt hRc hRc'
      have hqC : qR < qC := by
        have : R < min qC c := hCc ▸ lt_min hRC hRc'
        exact hqR ▸ this.trans_le (min_le_left _ _)
      obtain ⟨hH, hL⟩ := hq.twins_eq_of_lt hqC
      rw [hH, hL, hqR]
      exact ⟨rfl, rfl⟩
  · -- the cap at most the root
    have hm : min R C = C := min_eq_right hCR
    rcases le_or_gt c C with hcC | hCc'
    · -- everything at least `c`: both twins at the root
      have hqR : c ≤ qR := min_eq_right_iff.mp
        ((min_eq_right (hcC.trans hCR)).symm.trans hRc).symm
      have hqC : c ≤ qC := min_eq_right_iff.mp ((min_eq_right hcC).symm.trans hCc).symm
      have hc3 : IsSelfVisible 3 c := by
        rcases hc with hc | hc
        · exact hc
        · rw [hc, le_bot_iff] at hqC; rw [hqC]; exact isSelfVisible_bot _
      refine ⟨R, R, ⟨hR1, hR1, hR1, hC3, le_rfl, le_rfl, le_max_left _ _, hv, rfl, ?_⟩, ?_, ?_⟩
      · rw [hm, hC3.visibilityReplace_eq, min_self]
      · rw [min_eq_right (hcC.trans hCR), min_eq_right (le_hi_of_le hq hqR hqC)]
      · rw [min_eq_right (hcC.trans hCR), min_eq_right (le_lo_of_le hq hc3 hqR hqC)]
    · -- the cap below `c`: it is the cap of `q`
      have hqC : qC = C := Label.eq_of_min_eq_of_lt hCc hCc'
      rcases le_or_gt c R with hcR | hRc'
      · -- the root at least `c`: keep the twins of `q` below `c`, raise the others to the root
        have hqR : c ≤ qR := min_eq_right_iff.mp ((min_eq_right hcR).symm.trans hRc).symm
        have hCqR : qC ≤ qR := hqC ▸ hCc'.le.trans hqR
        obtain ⟨hqH, hqL⟩ := le_twins_of_le hq hCqR
        classical
        refine ⟨if qH < c then qH else R, if qL < c then qL else R, ⟨hR1, ?_, ?_, hC3, ?_, ?_, ?_,
          hv, ?_, ?_⟩, ?_, ?_⟩
        · split_ifs; exacts [hq.isSelfVisible_hi, hR1]
        · split_ifs; exacts [hq.isSelfVisible_lo, hR1]
        · split_ifs with h; exacts [h.le.trans hcR, le_rfl]
        · split_ifs with h; exacts [h.le.trans hcR, le_rfl]
        · split_ifs with h1 h2
          · exact absurd (hqR.trans hq.le_max) (not_le.mpr (max_lt h1 h2))
          all_goals simp
        · rw [hm]
          split_ifs
          · exact min_eq_right (hqC ▸ hqH)
          · exact min_eq_right hCR
        · rw [hm, hC3.visibilityReplace_eq, min_self]
          split_ifs
          · exact min_eq_right (hqC ▸ hqL)
          · exact min_eq_right hCR
        · split_ifs with h
          · rfl
          · rw [min_eq_right hcR, min_eq_right (not_lt.mp h)]
        · split_ifs with h
          · rfl
          · rw [min_eq_right hcR, min_eq_right (not_lt.mp h)]
      · -- the root and the cap below `c`: `q` itself
        have hqR : qR = R := Label.eq_of_min_eq_of_lt hRc hRc'
        subst hqR hqC
        exact ⟨qH, qL, hq, rfl, rfl⟩

variable {pR pH pL pC : Label.{u}}

/-- The capped cap of an ambient twin tuple is self-visible at `3`. -/
private theorem isSelfVisible_min_cap (hq : IsTwinTuple qR qH qL qC)
    (hc : IsSelfVisible 3 c ∨ qC = ⊥) : IsSelfVisible 3 (min qC c) := by
  rcases hc with hc | hc
  · exact hq.isSelfVisible_cap.min hc
  · rw [hc, min_eq_left bot_le]; exact isSelfVisible_bot _

/-- The capped cap of an ambient twin tuple, below `c`, is compatible with a root agreeing with
the ambient root capped at `c`. -/
private theorem visibilityReplace_min_cap (hq : IsTwinTuple qR qH qL qC)
    (hc : IsSelfVisible 3 c ∨ qC = ⊥) (hR : min pR c = min qR c) :
    visibilityReplace 3 2 (min pR (min qC c)) = min pR (min qC c) := by
  rcases le_or_gt (min qC c) pR with hb | hb
  · rw [min_eq_right hb]; exact (isSelfVisible_min_cap hq hc).visibilityReplace_eq 2
  · have hpc : pR < c := hb.trans_le (min_le_right _ _)
    have hqR : qR = pR := Label.eq_of_min_eq_of_lt hR hpc
    have hqC : qR < qC := hqR ▸ hb.trans_le (min_le_left _ _)
    have := hq.visibilityReplace_eq
    rw [min_eq_left hqC.le, hqR] at this
    rw [min_eq_left hb.le, this]

/-- **Prescribed root and twins, with the ambient cap capped**: the parameters `pR`, `pH`, `pL` of
a twin tuple agreeing with a twin tuple `q` capped at `c`, with the cap `min qC c`, form a twin
tuple.  Below the root the capped cap lies below both twins; above it the root and the twins are
those of `q`. -/
private theorem isTwinTuple_capped (hp : IsTwinTuple pR pH pL pC) (hq : IsTwinTuple qR qH qL qC)
    (hc : IsSelfVisible 3 c ∨ qC = ⊥) (hR : min pR c = min qR c) (hH : min pH c = min qH c)
    (hL : min pL c = min qL c) : IsTwinTuple pR pH pL (min qC c) := by
  have hb3 := isSelfVisible_min_cap hq hc
  have hv := visibilityReplace_min_cap hq hc hR
  rcases le_or_gt (min qC c) pR with hbR | hbR
  · -- the capped cap at most the root: it lies below both prescribed twins
    have hbqR : qR < qC → min qC c ≤ qR := fun hqC ↦ by
      by_cases hpc : pR < c
      · rw [Label.eq_of_min_eq_of_lt hR hpc]; exact hbR
      · exact (min_le_right _ _).trans (min_eq_right_iff.mp
          ((min_eq_right (not_lt.mp hpc)).symm.trans hR).symm)
    have key : ∀ T qT, min T c = min qT c → (T < c → min qC c ≤ qT) → min qC c ≤ T :=
      fun T qT hT h ↦ by
        by_cases hTc : T < c
        · rw [← Label.eq_of_min_eq_of_lt hT hTc]; exact h hTc
        · exact (min_le_right _ _).trans (not_lt.mp hTc)
    have hHb : min qC c ≤ pH := key pH qH hH fun _ ↦ by
      rcases le_or_gt qC qR with hCR | hRC
      · exact (min_le_left _ _).trans (le_twins_of_le hq hCR).1
      · rw [(hq.twins_eq_of_lt hRC).1]; exact hbqR hRC
    have hLb : min qC c ≤ pL := key pL qL hL fun _ ↦ by
      rcases le_or_gt qC qR with hCR | hRC
      · exact (min_le_left _ _).trans (le_twins_of_le hq hCR).2
      · rw [(hq.twins_eq_of_lt hRC).2]; exact le_visibilityReplace_three_one hb3 (hbqR hRC)
    refine ⟨hp.isSelfVisible_root, hp.isSelfVisible_hi, hp.isSelfVisible_lo, hb3, hp.hi_le,
      hp.lo_le, hp.le_max, hv, ?_, ?_⟩
    · rw [min_eq_right hbR, min_eq_right hHb]
    · rw [min_eq_right hbR, hb3.visibilityReplace_eq, min_self, min_eq_right hLb]
  · -- the capped cap above the root: root and twins are those of `q`
    have hpc : pR < c := hbR.trans_le (min_le_right _ _)
    have hqR : qR = pR := Label.eq_of_min_eq_of_lt hR hpc
    have hqC : qR < qC := hqR ▸ hbR.trans_le (min_le_left _ _)
    obtain ⟨hqH, hqL⟩ := hq.twins_eq_of_lt hqC
    have hpH : qH = pH := Label.eq_of_min_eq_of_lt hH (hp.hi_le.trans_lt hpc)
    have hpL : qL = pL := Label.eq_of_min_eq_of_lt hL (hp.lo_le.trans_lt hpc)
    refine ⟨hp.isSelfVisible_root, hp.isSelfVisible_hi, hp.isSelfVisible_lo, hb3, hp.hi_le,
      hp.lo_le, hp.le_max, hv, ?_, ?_⟩
    · rw [← hpH, hqH, hqR]
    · rw [← hpL, hqL, hqR, min_eq_left hbR.le]

/-- **The lift of parameters.**  Let `p` and `q` be twin tuples and `c` a cap, self-visible at `3`
unless the cap of `q` is `⊥`.  For the parameters prescribed by `p` (`xr` the root, `xt` the twins,
`xc` the cap; the twins and the cap only with the root), agreeing with `q` capped at `c`, some
twin tuple keeps the prescribed parameters and agrees with `q` capped at `c` at all four.  An
unprescribed cap is the ambient cap capped at `c` (`isTwinTuple_capped`); unprescribed twins are
lifted by `exists_twinLift`. -/
theorem exists_isTwinTuple_lift (hp : IsTwinTuple pR pH pL pC) (hq : IsTwinTuple qR qH qL qC)
    (hc : IsSelfVisible 3 c ∨ qC = ⊥) {xr xt xc : Prop} (htr : xt → xr) (hcr : xc → xr)
    (hR : xr → min pR c = min qR c) (hH : xt → min pH c = min qH c)
    (hL : xt → min pL c = min qL c) (hC : xc → min pC c = min qC c) :
    ∃ rR rH rL rC, IsTwinTuple rR rH rL rC ∧ (xr → rR = pR) ∧ (xt → rH = pH ∧ rL = pL) ∧
      (xc → rC = pC) ∧ min rR c = min qR c ∧ min rH c = min qH c ∧ min rL c = min qL c ∧
      min rC c = min qC c := by
  by_cases hxr : xr
  swap
  · exact ⟨qR, qH, qL, qC, hq, fun h ↦ absurd h hxr, fun h ↦ absurd (htr h) hxr,
      fun h ↦ absurd (hcr h) hxr, rfl, rfl, rfl, rfl⟩
  by_cases hxt : xt
  · by_cases hxc : xc
    · exact ⟨pR, pH, pL, pC, hp, fun _ ↦ rfl, fun _ ↦ ⟨rfl, rfl⟩, fun _ ↦ rfl, hR hxr, hH hxt,
        hL hxt, hC hxc⟩
    · exact ⟨pR, pH, pL, min qC c, isTwinTuple_capped hp hq hc (hR hxr) (hH hxt) (hL hxt),
        fun _ ↦ rfl, fun _ ↦ ⟨rfl, rfl⟩, fun h ↦ absurd h hxc, hR hxr, hH hxt, hL hxt,
        by rw [min_assoc, min_self]⟩
  · by_cases hxc : xc
    · obtain ⟨H, L, hT, hHc, hLc⟩ := exists_twinLift hp.isSelfVisible_root hp.isSelfVisible_cap
        hp.visibilityReplace_eq hq hc (hR hxr) (hC hxc)
      exact ⟨pR, H, L, pC, hT, fun _ ↦ rfl, fun h ↦ absurd h hxt, fun _ ↦ rfl, hR hxr, hHc, hLc,
        hC hxc⟩
    · obtain ⟨H, L, hT, hHc, hLc⟩ := exists_twinLift hp.isSelfVisible_root
        (isSelfVisible_min_cap hq hc) (visibilityReplace_min_cap hq hc (hR hxr)) hq hc (hR hxr)
        (by rw [min_assoc, min_self])
      exact ⟨pR, H, L, min qC c, hT, fun _ ↦ rfl, fun h ↦ absurd h hxt, fun h ↦ absurd h hxc,
        hR hxr, hHc, hLc, by rw [min_assoc, min_self]⟩

end Lift

/-! ### Lawful labellings below a pair -/

/-- **The reading at the grade `3`.**  Let `r` transform to `q`, with `a` of grade `1` read at `2`,
`q a = min R C`, and `b` of grade `3` with `q b = C` self-visible at `3`.  Then the capped root
`min R C` has finite part `2` or at least `3`, and every `e` of grade `1` read at `1` has
`q e = min (visibilityReplace 3 1 (min R C)) C`.  Below the cap the shifter sends `2` to the capped
root and commutes with visibility replacement there; at or above it, a value below the cap at `1`
would bring the value at `2` below the cap (`visibilityReplace_three_two_lt`). -/
theorem reading_of_transformsTo {D : Type*} {grade : D → ℕ} {r q : D → Label.{u}}
    (h : TransformsTo grade r q) {a b : D} (ga : grade a = 1) (gb : grade b = 3)
    (hra : r a = gridPoint 2 0) {R C : Label.{u}} (hC : IsSelfVisible 3 C)
    (hqa : q a = min R C) (hqb : q b = C) :
    visibilityReplace 3 2 (min R C) = min R C ∧
      ∀ e, grade e = 1 → r e = gridPoint 1 0 →
        q e = min (visibilityReplace 3 1 (min R C)) C := by
  obtain ⟨g, σ, hw, heq⟩ := h
  have hCg : C ≤ g 3 := by
    have := heq b
    rw [hqb, gb] at this
    rw [this]
    exact min_le_right _ _
  have hg31 : g 3 ≤ g 1 := hw.antitone (by omega)
  have ha := heq a
  rw [hqa, hra, ga] at ha
  rcases lt_or_ge (min R C) C with hxC | hCx
  · -- below the cap: the shifter sends `2` to the capped root
    have hσ : σ (gridPoint 2 0) = min R C := by
      rcases le_total (σ (gridPoint 2 0)) (g 1) with h1 | h1
      · rw [min_eq_left h1] at ha; exact ha.symm
      · rw [min_eq_right h1] at ha
        exact absurd (ha ▸ hxC) (not_lt.mpr (hCg.trans hg31))
    have hcomm := hw.visibilityReplace_comm (gridPoint 2 0) 3 (hσ ▸ hxC.le.trans hCg)
    have h2 := hcomm 2 (by omega)
    rw [visibilityReplace_gridPoint 2 2 (by omega), hσ] at h2
    refine ⟨h2.symm, fun e ge hre ↦ ?_⟩
    have h1 := hcomm 1 (by omega)
    rw [visibilityReplace_gridPoint 2 1 (by omega), hσ] at h1
    have hle : visibilityReplace 3 1 (min R C) ≤ min R C :=
      (visibilityReplace_le_visibilityReplace (by omega : 1 ≤ 2) _).trans_eq h2.symm
    rw [heq e, hre, ge, h1, min_eq_left (hle.trans (hxC.le.trans (hCg.trans hg31))),
      min_eq_left (hle.trans hxC.le)]
  · -- at or above the cap: the value at `1` is at least the cap
    have hx : min R C = C := le_antisymm (min_le_right _ _) hCx
    refine ⟨by rw [hx]; exact hC.visibilityReplace_eq 2, fun e ge hre ↦ ?_⟩
    rw [hx, hC.visibilityReplace_eq 1, min_self, heq e, hre, ge]
    rw [hx] at ha
    refine le_antisymm (ha ▸ min_le_min_right _ (hw.monotone gridPoint_one_le_two)) ?_
    refine le_min ?_ (hCg.trans hg31)
    by_contra hlt
    rw [not_le] at hlt
    have h2 := hw.visibilityReplace_comm (gridPoint 1 0) 3 (hlt.le.trans hCg) 2 (by omega)
    rw [visibilityReplace_gridPoint 1 2 (by omega)] at h2
    have : σ (gridPoint 2 0) < C := h2 ▸ visibilityReplace_three_two_lt hC hlt
    exact absurd (ha ▸ min_le_left _ _ : C ≤ σ (gridPoint 2 0)) (not_le.mpr this)

/-- **A pair of cells copying the twins**: if `a`, `b` are at most `R`, `a' ≤ a`, `b' ≤ b`, `R`
is at most the larger of `a'`, `b'`, and `a'` and `b'` see `b` and `a` as each other below
themselves, then `a' = a` and `b' = b`. -/
private theorem pair_eq {R a b a' b' : Label.{u}} (ha : a ≤ R) (hb : b ≤ R)
    (ha' : a' ≤ a) (hb' : b' ≤ b) (hR : R ≤ max a' b')
    (h1 : min b a' = min b' a') (h2 : min a b' = min a' b') : a' = a ∧ b' = b := by
  rcases le_total a' b' with h | h
  · rw [max_eq_right h] at hR
    have hbR : b' = R := le_antisymm (hb'.trans hb) hR
    rw [hbR, min_eq_left ha, min_eq_left (ha'.trans ha)] at h2
    exact ⟨h2.symm, le_antisymm hb' (hb.trans hR)⟩
  · rw [max_eq_left h] at hR
    have haR : a' = R := le_antisymm (ha'.trans ha) hR
    rw [haR, min_eq_left hb, min_eq_left (hb'.trans hb)] at h1
    exact ⟨le_antisymm ha' (ha.trans hR), h1.symm⟩

section Below

variable {o : Bool} {X : Finset (Fin 4) × ℕ}

/-- A cell below a cell below `X` is below `X`. -/
private theorem mem_below_of_le {d e : Fin 23} (hd : d ∈ twinCells.below X)
    (h : twinCells.gradedIndex e ≤ twinCells.gradedIndex d) : e ∈ twinCells.below X :=
  le_trans h hd

/-- A pair above the twins and the cap is above the reading cell. -/
private theorem mem_reading (h6 : (6 : Fin 23) ∈ twinCells.below X)
    (h19 : (19 : Fin 23) ∈ twinCells.below X) : (21 : Fin 23) ∈ twinCells.below X := by
  obtain ⟨S, j⟩ := X
  have key : ∀ S : Finset (Fin 4), ({2, 3} : Finset (Fin 4)) ⊆ S →
      ({0, 1, 2} : Finset (Fin 4)) ⊆ S → (univ : Finset (Fin 4)) ⊆ S := by decide
  exact ⟨key S h6.1 h19.1, h19.2⟩

/-- The cells of each kind. -/
private theorem cells_of_kind : ∀ d : Fin 23,
    (cellKind d = 1 → d = 2 ∨ d = 5 ∨ d = 8) ∧ (cellKind d = 2 → d = 6 ∨ d = 9 ∨ d = 11) ∧
      (cellKind d = 3 → d = 7 ∨ d = 10 ∨ d = 12) ∧ (cellKind d = 4 → d = 19) ∧
      (cellKind d = 5 → d = 21) := by
  decide

/-- **Every labelling lawful below a pair is a twin labelling** of a twin tuple, whose cap is `⊥`
when the cap `19` is not below the pair: for `r` lawful below `X` there are `R`, `A`, `B`, `C`
with `IsTwinTuple R (twinHi o A B) (twinLo o A B) C` and `r d = twinLabel R A B C d` at every cell
`d` below `X`.  The cells of the root kind copy the root (locality and availability); the pairs at
`({1, 2, 3}, 1)` and `(univ, 1)` copy the twins (`pair_eq`); the cap reads the root at `2`, and
the reading cell reads the root and the higher twin at `2` and the lower twin at `1`
(`reading_of_transformsTo`).  Absent twins are set to the root and to the root lowered to finite
part `1` below the cap (`isTwinTuple_default`). -/
theorem exists_of_isLawfulBelow {r : twinCells.below X → Label.{u}}
    (hr : (twinScheme.{u} o).rows.IsLawfulBelow X r) :
    ∃ R A B C, IsTwinTuple R (twinHi o A B) (twinLo o A B) C ∧
      (∀ d, r d = twinLabel R A B C d.1) ∧ ((19 : Fin 23) ∉ twinCells.below X → C = ⊥) := by
  classical
  -- `w`: `r` extended by `⊥` to all cells, lawful below `X`
  set w := CellScheme.Rows.extendBot X r with hw
  have hlaw : (twinScheme.{u} o).rows.IsLawfulBelow X (fun d ↦ w d) := by
    rw [hw, CellScheme.Rows.restrict_extendBot]
    exact hr
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hlaw
  have hout : ∀ d, d ∉ twinCells.below X → w d = ⊥ := fun d hd ↦ dite_eq_right hd
  have hsv : ∀ d, IsSelfVisible (twinCells.grade d) (w d) := fun d ↦ by
    by_cases hd : d ∈ twinCells.below X
    · exact ho d hd
    · rw [hout d hd]; exact isSelfVisible_bot _
  have self : ∀ d : Fin 23, d ∈ twinCells.below (twinCells.gradedIndex d) :=
    twinCells.mem_below_gradedIndex
  -- locality between two cells read by `s`, and availability into one cell or a pair
  have hloc : ∀ s ∈ twinCells.below X, ∀ a b : Fin 23,
      ∀ (ha : twinCells.gradedIndex a ≤ twinCells.gradedIndex s)
        (hb : twinCells.gradedIndex b ≤ twinCells.gradedIndex s),
      kindRow o (cellKind s) (cellKind a) ≤ kindRow o (cellKind s) (cellKind b) →
      twinCells.grade b ≤ twinCells.grade a → min (w a) (w s) ≤ min (w b) (w s) :=
    fun s hs a b ha hb hab hg ↦ (hl s hs).le_of_le (d := ⟨a, ha⟩) (d' := ⟨b, hb⟩) hab hg
  have hav1 : ∀ s t : Fin 23, t ∈ twinCells.below X → twinCells.scope s ⊆ twinCells.scope t →
      twinCells.grade s = twinCells.grade t →
      (∀ u, twinCells.gradedIndex u = twinCells.gradedIndex t → u = t) → w s ≤ w t :=
    fun s t ht hst hg huniq ↦ by
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rwa [huniq u hu] at hle
  have hav2 : ∀ s t t' : Fin 23, t ∈ twinCells.below X → twinCells.scope s ⊆ twinCells.scope t →
      twinCells.grade s = twinCells.grade t →
      (∀ u, twinCells.gradedIndex u = twinCells.gradedIndex t → u = t ∨ u = t') →
      w s ≤ max (w t) (w t') :=
    fun s t t' ht hst hg hpair ↦ by
      obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      rcases hpair u hu with rfl | rfl
      · exact hle.trans (le_max_left _ _)
      · exact hle.trans (le_max_right _ _)
  have hdead : ∀ d, cellKind d = 0 → w d = ⊥ := fun d h0 ↦ by
    by_cases hd : d ∈ twinCells.below X
    · have := (hl d hd).eq_bot (d := ⟨d, self d⟩) (by rw [twinScheme_row]; simp [h0, kindRow])
      simpa using this
    · exact hout d hd
  -- the cells `5` and `8` copy the root
  have hcopy : ∀ t : Fin 23, t ∈ twinCells.below X → cellKind t = 1 →
      twinCells.scope 2 ⊆ twinCells.scope t → twinCells.grade t = 1 →
      (∀ u, twinCells.gradedIndex u = twinCells.gradedIndex t → u = t) → w t = w 2 :=
    fun t ht hk hst hg huniq ↦ by
      have h1 := hloc t ht t 2 (self t) ⟨hst, show twinCells.grade 2 ≤ twinCells.grade t by
        rw [hg]; decide⟩ (by rw [hk]; exact le_rfl) (by rw [hg]; decide)
      rw [min_self] at h1
      exact le_antisymm (h1.trans (min_le_left _ _)) (hav1 2 t ht hst hg.symm huniq)
  -- the twins: at most the root, and the root is one of them
  have h67 : (6 : Fin 23) ∈ twinCells.below X →
      w 6 ≤ w 2 ∧ w 7 ≤ w 2 ∧ w 2 ≤ max (w 6) (w 7) := fun h6 ↦ by
    have h7 : (7 : Fin 23) ∈ twinCells.below X := mem_below_of_le h6 (by decide)
    have a6 := hloc 6 h6 6 2 (self 6) (by decide) le_rfl (by decide)
    have a7 := hloc 7 h7 7 2 (self 7) (by decide) le_rfl (by decide)
    rw [min_self] at a6 a7
    exact ⟨a6.trans (min_le_left _ _), a7.trans (min_le_left _ _),
      hav2 2 6 7 h6 (by decide) rfl (by decide)⟩
  -- a pair of twin kinds above the twins copies them
  have hpair : ∀ t t' : Fin 23, t ∈ twinCells.below X → cellKind t = 2 → cellKind t' = 3 →
      twinCells.gradedIndex t' = twinCells.gradedIndex t →
      twinCells.gradedIndex 6 ≤ twinCells.gradedIndex t → twinCells.scope 2 ⊆ twinCells.scope t →
      twinCells.grade t = 1 →
      (∀ u, twinCells.gradedIndex u = twinCells.gradedIndex t → u = t ∨ u = t') →
      w t = w 6 ∧ w t' = w 7 := fun t t' ht hk hk' htt' h6t h2t hg hpairs ↦ by
    have h6 := mem_below_of_le ht h6t
    have ht' : t' ∈ twinCells.below X := mem_below_of_le ht htt'.le
    have h7t : twinCells.gradedIndex 7 ≤ twinCells.gradedIndex t := h6t
    have hg' : twinCells.grade t' = 1 := (congrArg Prod.snd htt').trans hg
    have a1 := hloc t ht t 6 (self t) h6t (by rw [hk]; exact le_rfl) (by rw [hg]; decide)
    have a2 := hloc t' ht' t' 7 (self t') (htt' ▸ h7t) (by rw [hk']; exact le_rfl)
      (by rw [hg']; decide)
    rw [min_self] at a1 a2
    have e1 := le_antisymm
      (hloc t ht 7 t' h7t htt'.le (by rw [hk, hk']; exact le_rfl) (by rw [hg']; decide))
      (hloc t ht t' 7 htt'.le h7t (by rw [hk, hk']; exact le_rfl) (by rw [hg']; decide))
    have e2 := le_antisymm
      (hloc t' ht' 6 t (htt' ▸ h6t) htt'.ge (by rw [hk, hk']; exact le_rfl) (by rw [hg]; decide))
      (hloc t' ht' t 6 htt'.ge (htt' ▸ h6t) (by rw [hk, hk']; exact le_rfl) (by rw [hg]; decide))
    obtain ⟨b6, b7, bm⟩ := h67 h6
    exact pair_eq b6 b7 (a1.trans (min_le_left _ _)) (a2.trans (min_le_left _ _))
      (hav2 2 t t' ht h2t hg.symm hpairs) e1 e2
  -- the cap reads the root at `2`
  have h19 : (19 : Fin 23) ∈ twinCells.below X →
      visibilityReplace 3 2 (min (w 2) (w 19)) = min (w 2) (w 19) := fun h19 ↦
    (reading_of_transformsTo (hl 19 h19)
      (a := ⟨2, show twinCells.gradedIndex 2 ≤ twinCells.gradedIndex 19 by decide⟩)
      (b := ⟨19, self 19⟩) rfl rfl rfl (hsv 19) rfl (min_self _)).1
  -- the reading cell is the cap and reads the root and the twins
  have h21 : (21 : Fin 23) ∈ twinCells.below X → w 21 = w 19 ∧
      min (w (twinHi o 6 7)) (w 19) = min (w 2) (w 19) ∧
      min (w (twinLo o 6 7)) (w 19) =
        min (visibilityReplace 3 1 (min (w 2) (w 19))) (w 19) := fun h21 ↦ by
    have a1 := hloc 21 h21 21 19 (self 21) (by decide) le_rfl (by decide)
    rw [min_self] at a1
    have e21 : w 21 = w 19 :=
      le_antisymm (a1.trans (min_le_left _ _)) (hav1 19 21 h21 (by decide) rfl (by decide))
    have hhi : twinCells.gradedIndex (twinHi o 6 7) ≤ twinCells.gradedIndex 21 := by
      cases o <;> decide
    have hlo : twinCells.gradedIndex (twinLo o 6 7) ≤ twinCells.gradedIndex 21 := by
      cases o <;> decide
    have eh := le_antisymm
      (hloc 21 h21 (twinHi o 6 7) 2 hhi (by decide) (by cases o <;> exact le_rfl)
        (by cases o <;> decide))
      (hloc 21 h21 2 (twinHi o 6 7) (by decide) hhi (by cases o <;> exact le_rfl)
        (by cases o <;> decide))
    rw [e21] at eh
    have hrd := reading_of_transformsTo (hl 21 h21)
      (a := ⟨2, show twinCells.gradedIndex 2 ≤ twinCells.gradedIndex 21 by decide⟩)
      (b := ⟨21, self 21⟩)
      rfl rfl rfl (hsv 19) (R := w 2) (by rw [e21]) (by rw [min_self, e21])
    have el := hrd.2 ⟨twinLo o 6 7, hlo⟩ (by cases o <;> rfl) (by cases o <;> rfl)
    rw [e21] at el
    exact ⟨e21, eh, el⟩
  -- the tuple
  set L₀ := visibilityReplace 3 1 (min (w 2) (w 19)) with hL₀
  have hC : (19 : Fin 23) ∉ twinCells.below X → w 19 = ⊥ := hout 19
  refine ⟨w 2, if (6 : Fin 23) ∈ twinCells.below X then w 6 else twinHi o (w 2) L₀,
    if (6 : Fin 23) ∈ twinCells.below X then w 7 else twinLo o (w 2) L₀, w 19, ?_, ?_, hC⟩
  · by_cases h6 : (6 : Fin 23) ∈ twinCells.below X
    · simp only [h6, ite_true]
      obtain ⟨b6, b7, bm⟩ := h67 h6
      by_cases h21' : (21 : Fin 23) ∈ twinCells.below X
      · have hvr := h19 (mem_below_of_le h21' (by decide))
        obtain ⟨-, eh, el⟩ := h21 h21'
        cases o
        · exact ⟨hsv 2, hsv 7, hsv 6, hsv 19, b7, b6, max_comm (w 6) (w 7) ▸ bm, hvr, eh, el⟩
        · exact ⟨hsv 2, hsv 6, hsv 7, hsv 19, b6, b7, bm, hvr, eh, el⟩
      · have h0 : w 19 = ⊥ := hC fun h19' ↦ h21' (mem_reading h6 h19')
        rw [h0]
        cases o
        · exact ⟨hsv 2, hsv 7, hsv 6, isSelfVisible_bot _, b7, b6, max_comm (w 6) (w 7) ▸ bm,
            by simp, by simp, by simp⟩
        · exact ⟨hsv 2, hsv 6, hsv 7, isSelfVisible_bot _, b6, b7, bm, by simp, by simp, by simp⟩
    · simp only [h6, ite_false]
      have hvr : visibilityReplace 3 2 (min (w 2) (w 19)) = min (w 2) (w 19) := by
        by_cases h19' : (19 : Fin 23) ∈ twinCells.below X
        · exact h19 h19'
        · rw [hC h19']; simp
      have := isTwinTuple_default (hsv 2) (hsv 19) hvr
      cases o <;> exact this
  · -- the labelling, cell by cell
    rintro ⟨d, hd⟩
    rw [← CellScheme.Rows.extendBot_of_mem r hd]
    -- the left side is `w d`, the extension of `r` by `⊥` at a cell below `X`
    change w d = _
    obtain ⟨h1, h2, h3, h4, h5⟩ := cells_of_kind d
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    simp only [twinLabel, hk]
    fin_cases k
    · rw [hdead d hk]; rfl
    · rcases h1 hk with rfl | rfl | rfl
      · rfl
      · exact hcopy 5 hd rfl (by decide) rfl (by decide)
      · exact hcopy 8 hd rfl (by decide) rfl (by decide)
    · have h6 : (6 : Fin 23) ∈ twinCells.below X := by
        rcases h2 hk with rfl | rfl | rfl <;> exact mem_below_of_le hd (by decide)
      -- the first twin parameter
      change w d = if (6 : Fin 23) ∈ twinCells.below X then w 6 else _
      rw [ite_eq_left h6]
      rcases h2 hk with rfl | rfl | rfl
      · rfl
      · exact (hpair 9 10 hd rfl rfl (by decide) (by decide) (by decide) rfl (by decide)).1
      · exact (hpair 11 12 hd rfl rfl (by decide) (by decide) (by decide) rfl (by decide)).1
    · have h6 : (6 : Fin 23) ∈ twinCells.below X := by
        rcases h3 hk with rfl | rfl | rfl <;> exact mem_below_of_le hd (by decide)
      -- the second twin parameter
      change w d = if (6 : Fin 23) ∈ twinCells.below X then w 7 else _
      rw [ite_eq_left h6]
      rcases h3 hk with rfl | rfl | rfl
      · rfl
      · exact (hpair 9 10 (mem_below_of_le hd (by decide)) rfl rfl (by decide) (by decide)
          (by decide) rfl (by decide)).2
      · exact (hpair 11 12 (mem_below_of_le hd (by decide)) rfl rfl (by decide) (by decide)
          (by decide) rfl (by decide)).2
    · obtain rfl := h4 hk; rfl
    · obtain rfl := h5 hk; exact (h21 hd).1

end Below

/-! ### Legality -/

/-- The representative of each kind lies below the cells of that kind: the root below the root
kind, the first twin below the twin kinds, the cap below the cap and the reading cell. -/
private theorem rep_le_of_kind : ∀ d : Fin 23,
    (cellKind d = 1 → twinCells.gradedIndex 2 ≤ twinCells.gradedIndex d) ∧
      ((cellKind d = 2 ∨ cellKind d = 3) → twinCells.gradedIndex 6 ≤ twinCells.gradedIndex d) ∧
      ((cellKind d = 4 ∨ cellKind d = 5) → twinCells.gradedIndex 19 ≤ twinCells.gradedIndex d) := by
  decide

/-- The higher of the higher and the lower is the first. -/
@[simp] theorem twinHi_twinHi (o : Bool) {α : Type*} (a b : α) :
    twinHi o (twinHi o a b) (twinLo o a b) = a := by
  cases o <;> rfl

/-- The lower of the higher and the lower is the second. -/
@[simp] theorem twinLo_twinHi (o : Bool) {α : Type*} (a b : α) :
    twinLo o (twinHi o a b) (twinLo o a b) = b := by
  cases o <;> rfl

/-- **Every pair lifts capped**: the parameters prescribed below the smaller pair are kept, the
others lifted by `exists_isTwinTuple_lift`, and the twin labelling of the lifted parameters is
lawful. -/
theorem cappedLift_twinScheme {o : Bool} {X Y : Finset (Fin 4) × ℕ} (h : X ≤ Y) :
    (twinScheme.{u} o).rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨pR, pA, pB, pC, hpT, hpX, -⟩ := exists_of_isLawfulBelow hp
  obtain ⟨qR, qA, qB, qC, hqT, hqY, hq19⟩ := exists_of_isLawfulBelow hq
  have hagree {d : Fin 23} (hd : d ∈ twinCells.below X) :
      min (twinLabel pR pA pB pC d) c = min (twinLabel qR qA qB qC d) c := by
    have := hpq ⟨d, hd⟩
    rw [hpX, hqY] at this
    exact this.symm
  have hc3 : IsSelfVisible 3 c ∨ qC = ⊥ := by
    by_cases h19 : (19 : Fin 23) ∈ twinCells.below Y
    · exact .inl (hc.mono h19.2)
    · exact .inr (hq19 h19)
  have hAB : (6 : Fin 23) ∈ twinCells.below X →
      min pA c = min qA c ∧ min pB c = min qB c := fun h6 ↦
    ⟨hagree h6, hagree (mem_below_of_le (e := 7) h6 (by decide))⟩
  obtain ⟨rR, rH, rL, rC, hrT, hrR, hrT', hrC, hcR, hcH, hcL, hcC⟩ :=
    exists_isTwinTuple_lift hpT hqT hc3 (xr := (2 : Fin 23) ∈ twinCells.below X)
      (xt := (6 : Fin 23) ∈ twinCells.below X) (xc := (19 : Fin 23) ∈ twinCells.below X)
      (fun h6 ↦ mem_below_of_le h6 (by decide)) (fun h19 ↦ mem_below_of_le h19 (by decide))
      (fun h2 ↦ hagree h2) (fun h6 ↦ by cases o <;> simp [hAB h6])
      (fun h6 ↦ by cases o <;> simp [hAB h6]) (fun h19 ↦ hagree h19)
  have hT : IsTwinTuple rR (twinHi o (twinHi o rH rL) (twinLo o rH rL))
      (twinLo o (twinHi o rH rL) (twinLo o rH rL)) rC := by
    rwa [twinHi_twinHi, twinLo_twinHi]
  have hcA : min (twinHi o rH rL) c = min qA c := by cases o <;> simpa
  have hcB : min (twinLo o rH rL) c = min qB c := by cases o <;> simpa
  refine ⟨fun d ↦ twinLabel rR (twinHi o rH rL) (twinLo o rH rL) rC d.1,
    (isLawful_twinLabel hT).isLawfulBelow Y, fun d ↦ ?_, fun d ↦ ?_⟩
  · -- the capped observation of `q` below `Y`
    obtain ⟨d, hd⟩ := d
    rw [hqY]
    -- the restriction to `Y` at the cell `d`
    change min (twinLabel rR _ _ rC d) c = min (twinLabel qR qA qB qC d) c
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    simp only [twinLabel, hk]
    fin_cases k
    exacts [rfl, hcR, hcA, hcB, hcC, hcC]
  · -- the prescription below `X`
    obtain ⟨d, hd⟩ := d
    rw [hpX]
    -- the restriction to `X` at the cell `d`
    change twinLabel rR _ _ rC d = twinLabel pR pA pB pC d
    obtain ⟨h1, h23, h45⟩ := rep_le_of_kind d
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    rw [hk] at h1 h23 h45
    simp only [twinLabel, hk]
    fin_cases k
    · rfl
    · exact hrR (mem_below_of_le hd (h1 rfl))
    · obtain ⟨hH, hL⟩ := hrT' (mem_below_of_le hd (h23 (.inl rfl)))
      -- the first twin parameter of the lifted tuple
      change twinHi o rH rL = pA
      rw [hH, hL, twinHi_twinHi]
    · obtain ⟨hH, hL⟩ := hrT' (mem_below_of_le hd (h23 (.inr rfl)))
      -- the second twin parameter of the lifted tuple
      change twinLo o rH rL = pB
      rw [hH, hL, twinLo_twinHi]
    · exact hrC (mem_below_of_le hd (h45 (.inl rfl)))
    · exact hrC (mem_below_of_le hd (h45 (.inr rfl)))

/-- A tuple without cap is a twin tuple when the twins are at most the root and the root is one of
them. -/
private theorem isTwinTuple_of_bot {R H L : Label.{u}} (hR : IsSelfVisible 1 R)
    (hH : IsSelfVisible 1 H) (hL : IsSelfVisible 1 L) (hHR : H ≤ R) (hLR : L ≤ R)
    (hm : R ≤ max H L) : IsTwinTuple R H L ⊥ :=
  ⟨hR, hH, hL, isSelfVisible_bot _, hHR, hLR, hm, by simp, by simp, by simp⟩

/-- Each row value of the twin scheme is `⊥` or below `ω ^ 2`. -/
private theorem kindRow_lt (o : Bool) (k k' : Fin 6) :
    kindRow.{u} o k k' < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have h2 : omegaTwo.{u} < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
    lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by rw [Nat.cast_one, mul_one]⟩)
  have h1 : (1 : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
    lt_omega0_sq_iff.mpr (.inr ⟨0, 1, by simp⟩)
  have hb : (⊥ : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := WithBot.bot_lt_coe _
  fin_cases k <;> fin_cases k' <;> cases o <;>
    first | exact hb | exact h1 | exact h2 | exact gridPoint_lt_omega0_sq _ _

/-- **The twin scheme is legal**, for either order of the twins. -/
theorem isLegal_twinScheme (o : Bool) : (twinScheme.{u} o).IsLegal where
  -- well formed: the interval plan, each scope a face, each grade at most the size of the scope
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 23, twinCells.scope d ∈ twinCells.faces ∧
        0 < twinCells.grade d ∧ twinCells.grade d ≤ #(twinCells.scope d) := by decide
    exact key d⟩⟩
  isCoded s t := kindRow_lt o _ _
  -- consistent: each row is the twin labelling of a twin tuple
  isConsistent s := by
    have hrow {R A B C : Label.{u}} (hT : IsTwinTuple R (twinHi o A B) (twinLo o A B) C)
        (h : ∀ d : Fin 23, twinCells.gradedIndex d ≤ twinCells.gradedIndex s →
          kindRow o (cellKind s) (cellKind d) = kindValue R A B C (cellKind d)) :
        (twinScheme.{u} o).rows.IsLawfulBelow (twinCells.gradedIndex s)
          ((twinScheme.{u} o).rows.row s) := by
      have : (twinScheme.{u} o).rows.row s = fun d ↦ twinLabel R A B C d.1 :=
        funext fun d ↦ h d.1 d.2
      rw [this]
      exact (isLawful_twinLabel hT).isLawfulBelow _
    have hω := isSelfVisible_omegaTwo.{u}
    have h1 : IsSelfVisible 1 (1 : Label.{u}) := isSelfVisible_one.mpr le_rfl
    obtain ⟨k, hk⟩ : ∃ k, cellKind s = k := ⟨_, rfl⟩
    fin_cases k
    · refine hrow (A := ⊥) (B := ⊥) (isTwinTuple_of_bot (isSelfVisible_bot _)
        (by cases o <;> exact isSelfVisible_bot _) (by cases o <;> exact isSelfVisible_bot _)
        (by cases o <;> exact le_rfl) (by cases o <;> exact le_rfl) (by cases o <;> simp))
        fun d _ ↦ ?_
      rw [hk]
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj]; fin_cases j <;> rfl
    · refine hrow (A := omegaTwo) (B := omegaTwo) (isTwinTuple_of_bot hω
        (by cases o <;> exact hω) (by cases o <;> exact hω) (by cases o <;> exact le_rfl)
        (by cases o <;> exact le_rfl) (by cases o <;> simp)) fun d hd ↦ ?_
      rcases kind_below_root s d hk hd with h0 | h0 <;> rw [hk, h0] <;> rfl
    · refine hrow (A := omegaTwo) (B := 1) (isTwinTuple_of_bot hω
        (by cases o; exacts [h1, hω]) (by cases o; exacts [hω, h1])
        (by cases o; exacts [one_le_omegaTwo, le_rfl]) (by cases o; exacts [le_rfl,
          one_le_omegaTwo]) (by cases o <;> simp)) fun d hd ↦ ?_
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hk, hj]
      fin_cases j <;> rfl
    · refine hrow (A := 1) (B := omegaTwo) (isTwinTuple_of_bot hω
        (by cases o; exacts [hω, h1]) (by cases o; exacts [h1, hω])
        (by cases o; exacts [le_rfl, one_le_omegaTwo]) (by cases o; exacts [one_le_omegaTwo,
          le_rfl]) (by cases o <;> simp)) fun d hd ↦ ?_
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hk, hj]
      fin_cases j <;> rfl
    · refine hrow (A := twinHi o (gridPoint 2 0) (gridPoint 1 0))
        (B := twinLo o (gridPoint 2 0) (gridPoint 1 0))
        (by rw [twinHi_twinHi, twinLo_twinHi]; exact isTwinTuple_read) fun d hd ↦ ?_
      rcases kind_below_cap s d hk hd with h0 | h0 | h0 <;> rw [hk, h0] <;> rfl
    · refine hrow (A := twinHi o (gridPoint 2 0) (gridPoint 1 0))
        (B := twinLo o (gridPoint 2 0) (gridPoint 1 0))
        (by rw [twinHi_twinHi, twinLo_twinHi]; exact isTwinTuple_read) fun d _ ↦ ?_
      rw [hk]
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj]; fin_cases j <;> rfl
  isBountiful _ _ _ _ h := cappedLift_twinScheme h
  -- complete: a cell at each graded face
  isComplete X hX := by
    obtain ⟨S, j⟩ := X
    obtain ⟨hS, hj0, hjS⟩ := hX
    have hj4 : j ≤ 4 := hjS.trans (by simpa using card_le_univ S)
    have key : ∀ S : Finset (Fin 4), S ∈ twinCells.faces → ∀ j : Fin 5, 0 < (j : ℕ) →
        (j : ℕ) ≤ #S → ∃ d : Fin 23, twinCells.gradedIndex d = (S, (j : ℕ)) := by decide
    exact key S hS ⟨j, by omega⟩ hj0 hjS

end VaughtConjecture.Continuation.StableRecoveryTwin
