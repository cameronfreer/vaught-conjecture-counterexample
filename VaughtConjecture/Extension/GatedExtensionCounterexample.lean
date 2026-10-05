/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.GatedExtension
import VaughtConjecture.Extension.UnionFillCounterexample

/-!
# The gated pinned extension property fails at every stage

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate) and 3.4, row
(R1); the gated extensions of `VaughtConjecture.Extension.GatedExtension`.

**The theorem** (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`).  The gated pinned
extension property `StageType.HasGatedPinnedExtensions α` is false at every stage `α`, `ω`
included.  The input that defeats it is the smallest one the property allows: private arity
`n = 2`, the empty root (`m = 0`), and a donor whose new cell is labelled `⊥`, so that anchoring
holds vacuously (`StageType.isAnchored_of_forall_label_eq_bot_or_top`).  The failure is in the
legality of the display, not in the readings of the gate: of the clauses of a gated extension only
the legality of the display, its literal private face, the graded index of the gate, and the
labels `⊥` of the twins are used.

**The obstruction at the level of cell schemes** (`not_cappedLift_of_opposite`).  Let `w` be
lawful below a graded face `Y` and `⊥` at every cell of graded index `Y` other than a cell `G` of
that graded index, let `c ≠ ⊥` be a cap self-visible at the grade of `Y`, and let `C₁`, `C₂` be
cells below `X ≤ Y` with scopes inside that of `Y` and of the grade of `Y`.  If two labellings
lawful below `X`, both agreeing with `w` capped at `c`, order `C₁` and `C₂` oppositely, the rows
do not lift capped from `X` to `Y`.  A lift of either labelling into the cap ball of `w` at `c`
keeps every twin of `G` at `⊥`, since `min (r t) c = min ⊥ c = ⊥` and `c ≠ ⊥`; availability then
makes the gate dominate the larger of the two cells, and locality at `G`, at equal grades, forces
the row of `G` to order the two cells as the labelling does (`row_lt_of_cappedLift`).  One row
cannot order them both ways.

**The private type `P`** (`P`, `isLegal_P`).  On two points with the interval plan:

| cell  | 0   | 1   | 2    | 3 (`C₁`) | 4 (`C₂`) |
|-------|-----|-----|------|----------|----------|
| scope | {0} | {1} | univ | univ     | univ     |
| grade | 1   | 1   | 1    | 2        | 2        |

The cells of grade `1` are dead (their rows are `⊥`).  The row of `C₁` reads `(C₁, C₂)` as
`(3, 2)` and the row of `C₂` as `(2, 3)`; both read the dead cells as `⊥`.  The labelling
`labelling a b` is `⊥` at the dead cells, `a` at `C₁` and `b` at `C₂`; it is lawful for
`(a, b)` among `(3, 2)`, `(2, 3)`, `(⊤, ⊤)`, `(⊤, 2)` and `(2, ⊤)`, by the identity, the top
shifter with a constant step suppressor (`Label.topShifter`), and the collapse above `3`
(`TransformsTo.collapse`).  The rows are those of `labelling 3 2`, `labelling 2 3` and `⊥`, so
they are consistent; below a pair of grade `1` every lawful labelling is `⊥`, and a pair of grade
`2` is the whole set, so the rows are bountiful.  `P α` carries `labelling ⊤ ⊤`, at every stage.
The labellings `labelling ⊤ 2` and `labelling 2 ⊤` lie in the cap ball of `labelling ⊤ ⊤` at `2`
and order `C₁` and `C₂` oppositely.

**The stronger form** (`exists_twin_label_ne_bot`, `not_subsingleton_label_ne_bot`).  Let `Q` be
a legal stage type on three points whose face along `Fin.castSuccEmb` is literally `P α`.  Every
cell of `Q` of graded index `(univ, 2)` has a twin (another cell of that graded index) not
labelled `⊥`; so `Q` has at least two cells of graded index `(univ, 2)` not labelled `⊥`.  The two
labellings of `P` transfer to labellings lawful below `(univ.map Fin.castSuccEmb, 2)` in `Q`
(`Scheme.isLawfulBelow_comap_cellMap_iff`), and bountifulness of `Q` from that pair to
`(univ, 2)` contradicts the obstruction.  A gated extension labels the twins of its gate `⊥`
(`StageType.GatedExtension.label_twin`), so no gated extension of `P` exists, over any face, with
any donor (`isEmpty_gatedExtension`).

**What this does not refute.**  This refutes the universal gated extension hypothesis
`StageType.HasGatedPinnedExtensions`, not finite-cut receiving.  The structure
`StageType.GatedExtension` is inhabited: over the empty root, the display is `D₀.addApex`, the
scheme `S` on three points of `VaughtConjecture.Extension.UnionFillCounterexample`, labelled
`labelling ⊤ F`, with the apex added; the private type is its face `{0, 1}` and the donor its face
`{2}`, the gate is the cell at `(univ, 2)`, which has no twins, and the cap is the cell at
`({0, 1}, 2)` (`StageType.GatedExtension.instance_two_zero`); every hypothesis of the gated pinned
extension property holds for this input.  Gate recovery
(`VaughtConjecture.Realization.GateRecovery`), a statement about a given gated extension, and the
private context (`VaughtConjecture.Realization.PrivateContext`) stand.  Finite-cut receiving for all
models, (R1) of the table of Layer 3, is open in general; its form for the top-free witnesses
(`hasFiniteCutReceiving_reconstruct`) and the forms derived from finite-cut receiving are
unaffected.  The coupled gate replaces the labels `⊥` of the twins in the display by a condition on
rows, that every twin reads the gate at least as it reads the cap
(`CellScheme.Rows.TwinsReadGate`), which bounds the cap by the gate in every lawful labelling by
availability and locality alone (`CellScheme.Rows.cap_le_gate_of_twinsReadGate`).  At the input
used here such a display is legal (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`);
the coupled gated pinned extension property (`StageType.HasCoupledGatedPinnedExtensions`) is open
in general.  The private context of [Kni26, Lemma 8.1.1] also carries a marker, not used by the
gated extension; its role there is to be compared with this obstruction (prospective).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.GatedExtensionCounterexample

open Finset Label CellScheme

/-! ### The obstruction at the level of cell schemes -/

section Obstruction

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- **A capped lift orders the gate's row**: if the rows lift capped from `X` to `Y` at a cap
`c ≠ ⊥`, `w` is `⊥` at every twin of a cell `G` of graded index `Y`, and a labelling `p` lawful
below `X` and agreeing with `w` capped at `c` labels `B` below `A` (two cells below `X` of the
grade of `Y`, with scopes inside that of `Y`), then the row of `G` reads `B` below `A`. -/
theorem row_lt_of_cappedLift {X Y : Finset α × ℕ} (hXY : X ≤ Y) (hlift : R.CappedLift hXY)
    {G : ι} (hG : D.gradedIndex G = Y) {w : ι → Label.{u}} (hw : R.IsLawfulBelow Y (fun d ↦ w d))
    (htwin : ∀ t, D.gradedIndex t = Y → t ≠ G → w t = ⊥) {c : Label.{u}}
    (hc : IsSelfVisible Y.2 c) (hc0 : c ≠ ⊥) {A B : ι} (hA : A ∈ D.below X) (hB : B ∈ D.below X)
    (hsA : D.scope A ⊆ Y.1) (hgA : D.grade A = Y.2) (hsB : D.scope B ⊆ Y.1)
    (hgB : D.grade B = Y.2) {p : ι → Label.{u}} (hp : R.IsLawfulBelow X (fun d ↦ p d))
    (hpc : ∀ d ∈ D.below X, min (w d) c = min (p d) c) (hAB : p B < p A) :
    R.row G ⟨B, by rw [hG]; exact (D.gradedIndex_le_iff).mpr ⟨hsB, hgB.le⟩⟩ <
      R.row G ⟨A, by rw [hG]; exact (D.gradedIndex_le_iff).mpr ⟨hsA, hgA.le⟩⟩ := by
  obtain ⟨q', hq', hcap, hres⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp hlift c hc
    (fun d ↦ p d) (fun d ↦ w d) hp hw fun d ↦ hpc d d.2
  have hr : R.IsLawfulBelow Y (fun d ↦ Rows.extendBot Y q' d) :=
    Rows.isLawfulBelow_extendBot.mpr hq'
  have hrp : ∀ d (hd : d ∈ D.below X), Rows.extendBot Y q' d = p d := fun d hd ↦ by
    rw [Rows.extendBot_of_mem q' (D.below_mono hXY hd)]; exact hres ⟨d, hd⟩
  have hrw : ∀ d (hd : d ∈ D.below Y), min (Rows.extendBot Y q' d) c = min (w d) c :=
    fun d hd ↦ by rw [Rows.extendBot_of_mem q' hd]; exact hcap ⟨d, hd⟩
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hr
  have hGY : G ∈ D.below Y := by
    rw [CellScheme.mem_below, hG]
  have hsG : D.scope G = Y.1 := congrArg Prod.fst hG
  have hgG : D.grade G = Y.2 := congrArg Prod.snd hG
  -- The gate dominates `A`: the twins stay `⊥` in the lift.
  have hAG : Rows.extendBot Y q' A ≤ Rows.extendBot Y q' G := by
    obtain ⟨u, hu, hle⟩ := ha A G hGY (hsG ▸ hsA) (hgG ▸ hgA)
    rcases eq_or_ne u G with rfl | huG
    · exact hle
    · have huY : D.gradedIndex u = Y := hu.trans hG
      have hu' : u ∈ D.below Y := by rw [CellScheme.mem_below, huY]
      have h0 : min (Rows.extendBot Y q' u) c = ⊥ := by
        rw [hrw u hu', htwin u huY huG, min_eq_left bot_le]
      have hru : Rows.extendBot Y q' u = ⊥ := (min_eq_bot.mp h0).resolve_right hc0
      have : p A = ⊥ := by rw [← hrp A hA]; exact le_bot_iff.mp (hru ▸ hle)
      exact absurd (this ▸ hAB) not_lt_bot
  by_contra hnot
  rw [not_lt] at hnot
  have := (hl G hGY).le_of_le
    (d := ⟨A, by rw [hG]; exact (D.gradedIndex_le_iff).mpr ⟨hsA, hgA.le⟩⟩)
    (d' := ⟨B, by rw [hG]; exact (D.gradedIndex_le_iff).mpr ⟨hsB, hgB.le⟩⟩) hnot
    (by simp only; rw [hgA, hgB])
  simp only at this
  rw [min_eq_left hAG] at this
  have hAB' : p A ≤ p B := by
    rw [← hrp A hA, ← hrp B hB]; exact this.trans (min_le_left _ _)
  exact absurd hAB' (not_le.mpr hAB)

/-- **The obstruction.**  The rows do not lift capped from `X` to `Y` at a cap `c ≠ ⊥`
self-visible at the grade of `Y` when a labelling `w`, lawful below `Y`, is `⊥` at every twin of
a cell `G` of graded index `Y`, and two cells `C₁`, `C₂` below `X`, of the grade of `Y` and with
scopes inside that of `Y`, are ordered oppositely by two labellings lawful below `X` that agree
with `w` capped at `c`. -/
theorem not_cappedLift_of_opposite {X Y : Finset α × ℕ} (hXY : X ≤ Y)
    {G : ι} (hG : D.gradedIndex G = Y) {w : ι → Label.{u}} (hw : R.IsLawfulBelow Y (fun d ↦ w d))
    (htwin : ∀ t, D.gradedIndex t = Y → t ≠ G → w t = ⊥) {c : Label.{u}}
    (hc : IsSelfVisible Y.2 c) (hc0 : c ≠ ⊥) {C₁ C₂ : ι} (h₁ : C₁ ∈ D.below X)
    (h₂ : C₂ ∈ D.below X) (hs₁ : D.scope C₁ ⊆ Y.1) (hg₁ : D.grade C₁ = Y.2)
    (hs₂ : D.scope C₂ ⊆ Y.1) (hg₂ : D.grade C₂ = Y.2) {p p' : ι → Label.{u}}
    (hp : R.IsLawfulBelow X (fun d ↦ p d)) (hp' : R.IsLawfulBelow X (fun d ↦ p' d))
    (hpc : ∀ d ∈ D.below X, min (w d) c = min (p d) c)
    (hp'c : ∀ d ∈ D.below X, min (w d) c = min (p' d) c)
    (h12 : p C₂ < p C₁) (h21 : p' C₁ < p' C₂) : ¬ R.CappedLift hXY := fun hlift ↦
  lt_asymm
    (row_lt_of_cappedLift hXY hlift hG hw htwin hc hc0 h₁ h₂ hs₁ hg₁ hs₂ hg₂ hp hpc h12)
    (row_lt_of_cappedLift hXY hlift hG hw htwin hc hc0 h₂ h₁ hs₂ hg₂ hs₁ hg₁ hp' hp'c h21)

end Obstruction

/-! ### A legal type on two points whose two full cells lawful labellings order either way -/

/-- The scopes of the five cells: `{0}`, `{1}` and `univ` at grade `1`, and the two full cells. -/
def cellScope : Fin 5 → Finset (Fin 2) := ![{0}, {1}, univ, univ, univ]

/-- The grades of the five cells. -/
def cellGrade : Fin 5 → ℕ := ![1, 1, 1, 2, 2]

/-- The cell scheme on two points with the interval plan. -/
def cells : CellScheme (Fin 5) (Fin 2) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

/-- The row values: the row of `3` reads `(3, 2)` at the full cells, the row of `4` reads
`(2, 3)`, and every other entry is `⊥`. -/
private noncomputable def rowValue (s t : Fin 5) : Label.{u} :=
  if s = 3 then ![⊥, ⊥, ⊥, ((3 : ℕ) : Label.{u}), ((2 : ℕ) : Label.{u})] t
  else if s = 4 then ![⊥, ⊥, ⊥, ((2 : ℕ) : Label.{u}), ((3 : ℕ) : Label.{u})] t else ⊥

/-- The rows. -/
noncomputable def rows : cells.Rows.{u} := ⟨fun s t ↦ rowValue s t.1⟩

/-- The scheme on two points. -/
noncomputable def S : Scheme.{u} 2 := ⟨5, cells, rows⟩

/-- The labelling with `a` at the full cell `3`, `b` at the full cell `4`, and `⊥` at the dead
cells. -/
noncomputable def labelling (a b : Label.{u}) : Fin 5 → Label.{u} := ![⊥, ⊥, ⊥, a, b]

/-- The graded index of a cell is its scope and grade. -/
theorem gradedIndex_cells (d : Fin 5) : cells.gradedIndex d = (cellScope d, cellGrade d) := rfl

/-- The lawful labellings `labelling a b`, given the localities at the two full cells. -/
private theorem isLawful_labelling_of {a b : Label.{u}} (ha : IsSelfVisible 2 a)
    (hb : IsSelfVisible 2 b)
    (h3 : TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.row 3)
      (fun d ↦ min (labelling a b d) a))
    (h4 : TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.row 4)
      (fun d ↦ min (labelling a b d) b)) : rows.{u}.IsLawful (labelling a b) where
  orderly d := by
    fin_cases d <;> first | exact isSelfVisible_bot _ | exact ha | exact hb
  locality s := by
    fin_cases s
    · simpa [labelling] using TransformsTo.bot _ (rows.row 0)
    · simpa [labelling] using TransformsTo.bot _ (rows.row 1)
    · simpa [labelling] using TransformsTo.bot _ (rows.row 2)
    · simpa [labelling] using h3
    · simpa [labelling] using h4
  availability s t hst hg := by
    by_cases hs : s = 3 ∨ s = 4
    · refine ⟨s, ?_, le_rfl⟩
      have hg' : cellGrade s = cellGrade t := hg
      rw [gradedIndex_cells, gradedIndex_cells]
      rcases hs with rfl | rfl <;> fin_cases t <;> simp_all [cellGrade, cellScope]
    · refine ⟨t, rfl, ?_⟩
      push Not at hs
      fin_cases s <;> simp_all [labelling]

private theorem natCast_two_lt_three : ((2 : ℕ) : Label.{u}) < ((3 : ℕ) : Label.{u}) := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_lt_coe, ← WithTop.coe_natCast,
    ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  exact Nat.cast_lt.mpr (by decide)

private theorem not_three_le_two : ¬ (3 : Label.{u}) ≤ 2 := by
  have h := natCast_two_lt_three.{u}
  simp only [Nat.cast_ofNat] at h
  exact not_le.mpr h

private theorem natCast_two_lt_top : ((2 : ℕ) : Label.{u}) < ⊤ := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

private theorem isSelfVisible_two_two : IsSelfVisible 2 ((2 : ℕ) : Label.{u}) := by simp

private theorem isSelfVisible_two_three : IsSelfVisible 2 ((3 : ℕ) : Label.{u}) := by simp

private theorem natCast_two_ne_bot : ((2 : ℕ) : Label.{u}) ≠ ⊥ := by
  rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot

private theorem row_three (d : cells.below (cells.gradedIndex 3)) :
    rows.{u}.row 3 d = ![⊥, ⊥, ⊥, ((3 : ℕ) : Label.{u}), ((2 : ℕ) : Label.{u})] d.1 := by
  simp [rows, rowValue]

private theorem row_four (d : cells.below (cells.gradedIndex 4)) :
    rows.{u}.row 4 d = ![⊥, ⊥, ⊥, ((2 : ℕ) : Label.{u}), ((3 : ℕ) : Label.{u})] d.1 := by
  simp [rows, rowValue]

/-- The top shifter with a constant step suppressor at `v` reads the row of a full cell as `v` at
both full cells. -/
private theorem transformsTo_topShifter (s : Fin 5) (hs : s = 3 ∨ s = 4) {v : Label.{u}}
    (hv : IsSelfVisible 2 v) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.{u}.row s)
      (fun d ↦ labelling v v d.1) := by
  refine ⟨constStepSuppressor 2 v, topShifter,
    isWitness_topShifter (antitone_constStepSuppressor _ _)
      (isSelfVisible_constStepSuppressor hv), fun d ↦ ?_⟩
  obtain ⟨d, -⟩ := d
  rcases hs with rfl | rfl <;> fin_cases d <;>
    simp [rows, rowValue, labelling, topShifter, constStepSuppressor, cells, cellGrade]

/-- The identity reads a row as itself. -/
private theorem transformsTo_refl (s : Fin 5) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.{u}.row s)
      (rows.row s) :=
  TransformsTo.refl _ _

/-- The collapse above `3` reads the row of `3` as `(⊤, 2)`. -/
private theorem transformsTo_collapse_three :
    TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.{u}.row 3)
      (fun d ↦ labelling ⊤ ((2 : ℕ) : Label.{u}) d.1) := by
  have h := (transformsTo_refl.{u} 3).collapse (β := 0) (N := 3) (K := 2)
    Order.isSuccPrelimit_bot
    (fun d ↦ by obtain ⟨d, -⟩ := d; fin_cases d <;> simp [cells, cellGrade]) (by omega)
  convert h using 2 with d
  obtain ⟨d, -⟩ := d
  simp only [Function.comp_apply, row_three]
  fin_cases d <;>
    simp [labelling, Label.collapse, Label.reduce, not_three_le_two.{u}]

/-- The collapse above `3` reads the row of `4` as `(2, ⊤)`. -/
private theorem transformsTo_collapse_four :
    TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.{u}.row 4)
      (fun d ↦ labelling ((2 : ℕ) : Label.{u}) ⊤ d.1) := by
  have h := (transformsTo_refl.{u} 4).collapse (β := 0) (N := 3) (K := 2)
    Order.isSuccPrelimit_bot
    (fun d ↦ by obtain ⟨d, -⟩ := d; fin_cases d <;> simp [cells, cellGrade]) (by omega)
  convert h using 2 with d
  obtain ⟨d, -⟩ := d
  simp only [Function.comp_apply, row_four]
  fin_cases d <;>
    simp [labelling, Label.collapse, Label.reduce, not_three_le_two.{u}]

/-- The identity reads the row of `3` as `(3, 2)`. -/
private theorem transformsTo_refl_three :
    TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.{u}.row 3)
      (fun d ↦ labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) d.1) := by
  convert transformsTo_refl.{u} 3 using 2 with d; rw [row_three]; rfl

/-- The identity reads the row of `4` as `(2, 3)`. -/
private theorem transformsTo_refl_four :
    TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.{u}.row 4)
      (fun d ↦ labelling ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) d.1) := by
  convert transformsTo_refl.{u} 4 using 2 with d; rw [row_four]; rfl

private theorem min_labelling_left (a b : Label.{u}) :
    (fun d : Fin 5 ↦ min (labelling a b d) a) = labelling a (min b a) := by
  funext d; fin_cases d <;> simp [labelling]

private theorem min_labelling_right (a b : Label.{u}) :
    (fun d : Fin 5 ↦ min (labelling a b d) b) = labelling (min a b) b := by
  funext d; fin_cases d <;> simp [labelling]

private theorem isLawful_labelling_of' {a b : Label.{u}} (ha : IsSelfVisible 2 a)
    (hb : IsSelfVisible 2 b)
    (h3 : TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.row 3)
      (fun d ↦ labelling a (min b a) d.1))
    (h4 : TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.row 4)
      (fun d ↦ labelling (min a b) b d.1)) : rows.{u}.IsLawful (labelling a b) := by
  refine isLawful_labelling_of ha hb ?_ ?_
  · have := congrFun (min_labelling_left a b); simpa [this] using h3
  · have := congrFun (min_labelling_right a b); simpa [this] using h4

/-- `labelling 3 2` is lawful. -/
theorem isLawful_labelling_three_two :
    rows.{u}.IsLawful (labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u})) := by
  refine isLawful_labelling_of' isSelfVisible_two_three isSelfVisible_two_two ?_ ?_
  · rw [min_eq_left natCast_two_lt_three.le]; exact transformsTo_refl_three
  · rw [min_eq_right natCast_two_lt_three.le]
    exact transformsTo_topShifter 4 (.inr rfl) isSelfVisible_two_two

/-- `labelling 2 3` is lawful. -/
theorem isLawful_labelling_two_three :
    rows.{u}.IsLawful (labelling ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u})) := by
  refine isLawful_labelling_of' isSelfVisible_two_two isSelfVisible_two_three ?_ ?_
  · rw [min_eq_right natCast_two_lt_three.le]
    exact transformsTo_topShifter 3 (.inl rfl) isSelfVisible_two_two
  · rw [min_eq_left natCast_two_lt_three.le]; exact transformsTo_refl_four

/-- `labelling ⊤ ⊤` is lawful. -/
theorem isLawful_labelling_top_top : rows.{u}.IsLawful (labelling (⊤ : Label.{u}) ⊤) := by
  refine isLawful_labelling_of' (isSelfVisible_top 2) (isSelfVisible_top 2) ?_ ?_
  · rw [min_self]; exact transformsTo_topShifter 3 (.inl rfl) (isSelfVisible_top 2)
  · rw [min_self]; exact transformsTo_topShifter 4 (.inr rfl) (isSelfVisible_top 2)

/-- `labelling ⊤ 2` is lawful. -/
theorem isLawful_labelling_top_two :
    rows.{u}.IsLawful (labelling (⊤ : Label.{u}) ((2 : ℕ) : Label.{u})) := by
  refine isLawful_labelling_of' (isSelfVisible_top 2) isSelfVisible_two_two ?_ ?_
  · rw [min_eq_left le_top]; exact transformsTo_collapse_three
  · rw [min_eq_right le_top]; exact transformsTo_topShifter 4 (.inr rfl) isSelfVisible_two_two

/-- `labelling 2 ⊤` is lawful. -/
theorem isLawful_labelling_two_top :
    rows.{u}.IsLawful (labelling ((2 : ℕ) : Label.{u}) (⊤ : Label.{u})) := by
  refine isLawful_labelling_of' isSelfVisible_two_two (isSelfVisible_top 2) ?_ ?_
  · rw [min_eq_right le_top]; exact transformsTo_topShifter 3 (.inl rfl) isSelfVisible_two_two
  · rw [min_eq_left le_top]; exact transformsTo_collapse_four

/-! ### Legality of the type on two points -/

private theorem natCast_lt_omega0_sq (n : ℕ) :
    ((n : ℕ) : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rw [← WithBot.coe_natCast, WithBot.coe_lt_coe, ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  refine (Ordinal.natCast_lt_omega0 n).trans_le ?_
  rw [pow_two]; exact Ordinal.le_mul_left _ Ordinal.omega0_pos

/-- The scheme on two points is well formed. -/
theorem isWellFormed_S : S.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

private theorem rowValue_lt (s t : Fin 5) :
    rowValue.{u} s t < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have h2 := natCast_lt_omega0_sq.{u} 2
  have h3 := natCast_lt_omega0_sq.{u} 3
  have hbot : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    WithBot.bot_lt_coe _
  fin_cases s <;> fin_cases t <;> first | exact hbot | exact h2 | exact h3

/-- The scheme on two points is coded. -/
theorem isCoded_S : S.{u}.IsCoded := fun s t ↦ rowValue_lt s t.1

/-- **The rows are consistent**: they are `labelling 3 2`, `labelling 2 3`, and `⊥`. -/
theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  have hrow : ∀ s : Fin 5, (fun t : cells.below (cells.gradedIndex s) ↦ rows.{u}.row s t) =
      fun t ↦ (if s = 3 then labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u})
        else if s = 4 then labelling ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u})
        else fun _ ↦ ⊥) t.1 := by
    intro s; funext t
    -- The entries of the rows are the row values (`rows`, by definition).
    change rowValue s t.1 = _
    unfold rowValue labelling
    split_ifs <;> rfl
  -- Consistency at `s`: the row of `s` is lawful below its graded index (`IsConsistent`).
  change rows.IsLawfulBelow _ (fun t ↦ rows.row s t)
  rw [hrow s]
  split_ifs
  · exact isLawful_labelling_three_two.isLawfulBelow _
  · exact isLawful_labelling_two_three.isLawfulBelow _
  · exact Rows.isLawfulBelow_const_bot _

/-- Below a pair of grade `1`, every lawful labelling is `⊥`. -/
private theorem eq_bot_of_grade_one {X : Finset (Fin 2) × ℕ} (hX : X.2 = 1)
    {x : Fin 5 → Label.{u}} (hx : rows.IsLawfulBelow X (fun d ↦ x d)) (d : Fin 5)
    (hd : d ∈ cells.below X) : x d = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  have hgd : cellGrade d ≤ 1 := hX ▸ hd.2
  have hd3 : d ≠ 3 ∧ d ≠ 4 := by
    constructor <;> rintro rfl <;> simp [cellGrade] at hgd
  have := (hl d hd).eq_bot (d := ⟨d, cells.mem_below_gradedIndex d⟩) (by
    -- The diagonal entry of the row of `d` is `rowValue d d` (`rows`, by definition).
    change rowValue d d = ⊥
    unfold rowValue
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hd3.1),
      ite_eq_right_iff.mpr (fun h ↦ absurd h hd3.2)])
  simpa using this

/-- **The rows are bountiful**: below a pair of grade `1` every lawful labelling is `⊥`, and a
pair of grade `2` is the whole set. -/
theorem isBountiful_rows : rows.{u}.IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  have hcard : #X.1 ≤ 2 := (card_le_univ _).trans_eq (by simp)
  have hX2 : X.2 = 1 ∨ X.2 = 2 := by
    have h1 := hX.2.1; have h2 := hX.2.2
    omega
  rcases hX2 with h1 | h2
  · refine (Rows.cappedLift_iff_forall_exists _).mpr fun c _ p q hp hq _ ↦ ?_
    refine ⟨q, hq, fun _ ↦ rfl, fun d ↦ ?_⟩
    have hq' : rows.IsLawfulBelow (Y.1, X.2) (fun d ↦ Rows.extendBot (Y.1, X.2) q d) :=
      Rows.isLawfulBelow_extendBot.mpr hq
    have hp' : rows.IsLawfulBelow X (fun d ↦ Rows.extendBot X p d) :=
      Rows.isLawfulBelow_extendBot.mpr hp
    have hd' : d.1 ∈ cells.below (Y.1, X.2) :=
      cells.below_mono (show X ≤ (Y.1, X.2) from ⟨h.1, le_rfl⟩) d.2
    have e1 := eq_bot_of_grade_one (X := (Y.1, X.2)) h1 hq' d.1 hd'
    have e2 := eq_bot_of_grade_one h1 hp' d.1 d.2
    rw [Rows.extendBot_of_mem _ hd'] at e1
    rw [Rows.extendBot_of_mem _ d.2] at e2
    exact e1.trans e2.symm
  · -- At grade `2` the face is the whole set.
    have hX1 : X.1 = univ := by
      apply eq_univ_of_card
      have h2' := hX.2.2
      simp only [Fintype.card_fin]; omega
    have hY1 : Y.1 = univ := eq_univ_of_forall fun x ↦ h.1 (hX1 ▸ mem_univ x)
    obtain ⟨X1, X2⟩ := X
    obtain ⟨Y1, Y2⟩ := Y
    simp only at hX1 hY1 h2
    subst hX1 hY1 h2
    exact Rows.cappedLift_refl _

private theorem exists_cell_of_mem_intervalPlan :
    ∀ B ∈ Geometry.intervalPlan (univ : Finset (Fin 2)), ∀ k ≤ 2,
      0 < k → k ≤ #B → ∃ d : Fin 5, cellScope d = B ∧ cellGrade d = k := by
  decide +kernel

/-- The cell scheme on two points is complete. -/
theorem isComplete_cells : cells.IsComplete := by
  intro X hX
  obtain ⟨d, hd1, hd2⟩ := exists_cell_of_mem_intervalPlan X.1 hX.1 X.2
    (hX.2.2.trans ((card_le_univ _).trans_eq (by simp))) hX.2.1 hX.2.2
  exact ⟨d, Prod.ext hd1 hd2⟩

private theorem atStage_labelling_top_top {α : Ordinal.{u}} (d : Fin 5) :
    AtStage α (labelling (⊤ : Label.{u}) ⊤ d) := by
  fin_cases d <;> simp [labelling, atStage_top, atStage_bot]

/-- **The private type**: the type on two points labelled `⊤` at both full cells. -/
noncomputable def P (α : Ordinal.{u}) : StageType.{u} α 2 where
  toScheme := S
  label := labelling ⊤ ⊤
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_labelling_top_top
  atStage d := atStage_labelling_top_top d

/-- **The private type is legal.** -/
theorem isLegal_P (α : Ordinal.{u}) : (P α).IsLegal :=
  StageType.isLegal_iff.mpr ⟨isConsistent_rows, isBountiful_rows, isComplete_cells⟩

/-! ### The refutation -/

/-- Two cells of full scope and full grade of a stage type on two points, ordered oppositely by
two lawful labellings in the cap ball of its labelling at `2`. -/
private def HasOppositeCells {α : Ordinal.{u}} (T : StageType.{u} α 2) : Prop :=
  ∃ (C₁ C₂ : Fin T.card) (p p' : Fin T.card → Label.{u}),
    T.toCellScheme.gradedIndex C₁ = (univ, 2) ∧ T.toCellScheme.gradedIndex C₂ = (univ, 2) ∧
    T.rows.IsLawful p ∧ T.rows.IsLawful p' ∧
    (∀ i, min (T.label i) ((2 : ℕ) : Label.{u}) = min (p i) ((2 : ℕ) : Label.{u})) ∧
    (∀ i, min (T.label i) ((2 : ℕ) : Label.{u}) = min (p' i) ((2 : ℕ) : Label.{u})) ∧
    p C₂ < p C₁ ∧ p' C₁ < p' C₂

private theorem capBall_top_two (i : Fin 5) :
    min (labelling (⊤ : Label.{u}) ⊤ i) ((2 : ℕ) : Label.{u}) =
      min (labelling ⊤ ((2 : ℕ) : Label.{u}) i) ((2 : ℕ) : Label.{u}) := by
  fin_cases i <;> simp [labelling]

private theorem capBall_two_top (i : Fin 5) :
    min (labelling (⊤ : Label.{u}) ⊤ i) ((2 : ℕ) : Label.{u}) =
      min (labelling ((2 : ℕ) : Label.{u}) ⊤ i) ((2 : ℕ) : Label.{u}) := by
  fin_cases i <;> simp [labelling]

/-- The private type has two full cells ordered oppositely by `labelling ⊤ 2` and
`labelling 2 ⊤`, both in the cap ball of `labelling ⊤ ⊤` at `2`. -/
private theorem hasOppositeCells_P (α : Ordinal.{u}) : HasOppositeCells (P α) :=
  ⟨(3 : Fin 5), (4 : Fin 5), labelling ⊤ ((2 : ℕ) : Label.{u}), labelling ((2 : ℕ) : Label.{u}) ⊤,
    rfl, rfl, isLawful_labelling_top_two, isLawful_labelling_two_top,
    capBall_top_two, capBall_two_top,
    natCast_two_lt_top, natCast_two_lt_top⟩

/-- **Every cell of graded index `(univ, 2)` has a twin not labelled `⊥`**, in every legal stage
type on three points whose face along `Fin.castSuccEmb` is literally the private type `P α`. -/
theorem exists_twin_label_ne_bot {α : Ordinal.{u}} (Q : StageType.{u} α 3) (hQ : Q.IsLegal)
    (hQP : StageType.restrictFace Fin.castSuccEmb Q = some (P α)) (G : Fin Q.card)
    (hG : Q.toCellScheme.gradedIndex G = (univ, 2)) :
    ∃ t, Q.toCellScheme.gradedIndex t = (univ, 2) ∧ t ≠ G ∧ Q.label t ≠ ⊥ := by
  by_contra htwin
  push Not at htwin
  obtain ⟨hfQ, hQP⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hQP
  set Q' := Q.comap Fin.castSuccEmb hfQ with hQ'
  obtain ⟨C₁, C₂, p, p', hC₁, hC₂, hp, hp', hpc, hp'c, h12, h21⟩ : HasOppositeCells Q' := by
    rw [hQP]; exact hasOppositeCells_P α
  let φ := Q.toScheme.cellMap Fin.castSuccEmb
  -- The two labellings, extended by `⊥` to all cells of `Q`.
  let x : Fin Q.card → Label.{u} := Function.extend φ p fun _ ↦ ⊥
  let x' : Fin Q.card → Label.{u} := Function.extend φ p' fun _ ↦ ⊥
  have hxφ : ∀ i, x (φ i) = p i := fun i ↦ φ.injective.extend_apply _ _ i
  have hx'φ : ∀ i, x' (φ i) = p' i := fun i ↦ φ.injective.extend_apply _ _ i
  let X : Finset (Fin 3) × ℕ := (univ.map Fin.castSuccEmb, 2)
  let Y : Finset (Fin 3) × ℕ := (univ, 2)
  have hlaw : ∀ (y : Fin Q.card → Label.{u}) (q : Fin Q'.card → Label.{u}),
      (∀ i, y (φ i) = q i) → Q'.rows.IsLawful q → Q.rows.IsLawfulBelow X (fun d ↦ y d) :=
    fun y q hyq hq ↦ by
      refine (Q.toScheme.isLawfulBelow_comap_cellMap_iff Fin.castSuccEmb (univ, 2) y).mp ?_
      have h : (Q.toScheme.comap Fin.castSuccEmb).rows.IsLawfulBelow (univ, 2)
          (fun i ↦ q i.1) := hq.isLawfulBelow (univ, 2)
      have heq : (fun i : (Q.toScheme.comap Fin.castSuccEmb).toCellScheme.below (univ, 2) ↦
          y (Q.toScheme.cellMap Fin.castSuccEmb i)) = fun i ↦ q i.1 :=
        funext fun i ↦ hyq i.1
      rw [heq]; exact h
  have hX : X ∈ Q.toCellScheme.gradedFaces := ⟨hfQ, Nat.two_pos, by simp [X]⟩
  have hY : Y ∈ Q.toCellScheme.gradedFaces := ⟨Q.univ_mem_faces, Nat.two_pos, by simp [Y]⟩
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  have hgi : ∀ i, Q'.toCellScheme.gradedIndex i = (univ, 2) →
      Q.toCellScheme.gradedIndex (φ i) = X := fun i hi ↦ by
    rw [← Q.toScheme.map_comap_gradedIndex Fin.castSuccEmb i]
    -- `Q'` is the face of `Q` along `Fin.castSuccEmb`, by definition.
    change Prod.map (Finset.map Fin.castSuccEmb) id (Q'.toCellScheme.gradedIndex i) = X
    rw [hi]; rfl
  have hmem : ∀ i, Q'.toCellScheme.gradedIndex i = (univ, 2) →
      φ i ∈ Q.toCellScheme.below X := fun i hi ↦ by
    rw [CellScheme.mem_below, hgi i hi]
  have hcap : ∀ (y : Fin Q.card → Label.{u}) (q : Fin Q'.card → Label.{u}),
      (∀ i, y (φ i) = q i) →
      (∀ i, min (Q'.label i) ((2 : ℕ) : Label.{u}) = min (q i) ((2 : ℕ) : Label.{u})) →
      ∀ d ∈ Q.toCellScheme.below X, min (Q.label d) ((2 : ℕ) : Label.{u}) =
        min (y d) ((2 : ℕ) : Label.{u}) := fun y q hyq hq d hd ↦ by
    have hvis : d ∈ Q.toScheme.visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      have : Q.toCellScheme.scope d ⊆ univ.map Fin.castSuccEmb := hd.1
      intro z hz
      obtain ⟨a, -, rfl⟩ := mem_map.mp (this (mem_coe.mp hz))
      exact ⟨a, rfl⟩
    obtain ⟨i, rfl⟩ : d ∈ Set.range φ := by
      rw [Scheme.range_cellMap]; exact mem_coe.mpr hvis
    rw [hyq i]; exact hq i
  exact not_cappedLift_of_opposite hXY hG (Q.isLawful.isLawfulBelow Y) htwin
    (c := ((2 : ℕ) : Label.{u})) isSelfVisible_two_two natCast_two_ne_bot (hmem C₁ hC₁)
    (hmem C₂ hC₂) (subset_univ _) (congrArg Prod.snd (hgi C₁ hC₁)) (subset_univ _)
    (congrArg Prod.snd (hgi C₂ hC₂)) (hlaw x p hxφ hp) (hlaw x' p' hx'φ hp')
    (hcap x p hxφ hpc) (hcap x' p' hx'φ hp'c)
    ((hxφ C₂).trans_lt (h12.trans_eq (hxφ C₁).symm))
    ((hx'φ C₁).trans_lt (h21.trans_eq (hx'φ C₂).symm)) (hQ.isBountiful hX hY hXY)

/-- **At least two cells of graded index `(univ, 2)` are not labelled `⊥`** in every legal stage
type on three points whose face along `Fin.castSuccEmb` is literally the private type `P α`. -/
theorem not_subsingleton_label_ne_bot {α : Ordinal.{u}} (Q : StageType.{u} α 3)
    (hQ : Q.IsLegal) (hQP : StageType.restrictFace Fin.castSuccEmb Q = some (P α)) :
    ¬ {t | Q.toCellScheme.gradedIndex t = (univ, 2) ∧ Q.label t ≠ ⊥}.Subsingleton := by
  intro hsub
  obtain ⟨G₀, hG₀⟩ := hQ.isComplete (univ, 2) ⟨Q.univ_mem_faces, Nat.two_pos, by simp⟩
  by_cases hne : ∃ G, Q.toCellScheme.gradedIndex G = (univ, 2) ∧ Q.label G ≠ ⊥
  · obtain ⟨G, hG, hGne⟩ := hne
    obtain ⟨t, ht, htG, htne⟩ := exists_twin_label_ne_bot Q hQ hQP G hG
    exact htG (hsub ⟨ht, htne⟩ ⟨hG, hGne⟩)
  · obtain ⟨t, ht, -, htne⟩ := exists_twin_label_ne_bot Q hQ hQP G₀ hG₀
    exact hne ⟨t, ht, htne⟩

/-- **The private type has no gated extension**, over any face and with any donor: the display of
a gated extension labels the twins of its gate `⊥`. -/
theorem isEmpty_gatedExtension {α : Ordinal.{u}} {m : ℕ} (f : Fin m ↪ Fin 2)
    (d : StageType.{u} α (m + 1)) : IsEmpty (StageType.GatedExtension (P α) f d) :=
  ⟨fun E ↦ by
    obtain ⟨t, ht, htG, hne⟩ := exists_twin_label_ne_bot E.display E.isLegal
      E.restrictFace_castSuccEmb E.gate E.gradedIndex_gate
    exact hne (E.label_twin t ht htG)⟩

/-- The labels of `P` at the cells whose scope lies in `{0}` are `⊥`. -/
private theorem labelling_eq_bot_of_scope (x : Fin 5) (hx : cellScope x ⊆ {0}) :
    labelling (⊤ : Label.{u}) ⊤ x = ⊥ := by
  have h1 : cellScope x = univ → False := fun hy ↦ by
    have := hx (hy ▸ mem_univ (1 : Fin 2)); simp at this
  fin_cases x
  · rfl
  · rfl
  · rfl
  · exact (h1 rfl).elim
  · exact (h1 rfl).elim

/-- **The gated pinned extension property fails at every stage.**  It is applied to the private
type `P α`, the empty root, the face `{0}` of `P α` as donor (its new cell is labelled `⊥`, so it
is anchored), and the cell `3` as cap; the display of the gated extension it gives labels the
twins of its gate `⊥`, against `exists_twin_label_ne_bot` (`isEmpty_gatedExtension`). -/
theorem not_hasGatedPinnedExtensions (α : Ordinal.{u}) :
    ¬ StageType.HasGatedPinnedExtensions.{u} α := by
  intro hg
  let f : Fin 0 ↪ Fin 2 := ⟨Fin.elim0, fun a ↦ a.elim0⟩
  let g₁ : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩
  have hf : univ.map f ∈ (P α).toCellScheme.faces := by
    -- The faces of `P α` are the interval plan of `univ` (`cells`, by definition).
    change _ ∈ Geometry.intervalPlan univ; decide +kernel
  have hg₁ : univ.map g₁ ∈ (P α).toCellScheme.faces := by
    -- The faces of `P α` are the interval plan of `univ` (`cells`, by definition).
    change _ ∈ Geometry.intervalPlan univ; decide +kernel
  have hd : ((P α).comap g₁ hg₁).IsLegal := (isLegal_P α).comap g₁ hg₁
  have hdp : StageType.restrictFace Fin.castSuccEmb ((P α).comap g₁ hg₁) =
      some ((P α).comap f hf) := by
    rw [StageType.restrictFace_trans _ _ _ (StageType.restrictFace_of_mem _ _ hg₁)]
    have : Fin.castSuccEmb.trans g₁ = f := Function.Embedding.ext fun i ↦ i.elim0
    rw [this]; exact StageType.restrictFace_of_mem _ _ hf
  have hanc : (P α).IsAnchored (3 : Fin 5) ((P α).comap g₁ hg₁) := by
    refine StageType.isAnchored_of_forall_label_eq_bot_or_top _ _ fun j _ ↦ .inl ?_
    -- The labels of the face are those of its cells in `P α` (`comap_label`).
    change (P α).label ((P α).cellMap g₁ j) = ⊥
    have hj := (P α).cellMap_mem g₁ j
    rw [Scheme.mem_visibleCells] at hj
    refine labelling_eq_bot_of_scope _ fun y hy ↦ ?_
    obtain ⟨i, hi⟩ := hj (mem_coe.mpr hy)
    rw [← hi]; exact mem_singleton_self _
  -- The label of the cap `3` in `P α` is `labelling ⊤ ⊤ 3` (`P`, by definition).
  obtain ⟨E, -⟩ := hg (P α) f ((P α).comap f hf) ((P α).comap g₁ hg₁) (3 : Fin 5) (isLegal_P α)
    (StageType.restrictFace_of_mem _ _ hf) hd hdp rfl
    (by change labelling ⊤ ⊤ 3 ≠ ⊥; simp [labelling]) (by omega) hanc
  exact (isEmpty_gatedExtension f _).false E

end VaughtConjecture.GatedExtensionCounterexample

/-! ### An inhabited gated extension -/

namespace VaughtConjecture.GatedExtensionExample

open Finset Label CellScheme UnionFillCounterexample StageType

variable {α : Ordinal.{u}} {F : Label.{u}}

/-- The type on three points of `UnionFillCounterexample` below the full grade, labelled
`labelling ⊤ F`. -/
private noncomputable def D₀ (α : Ordinal.{u}) (F : Label.{u}) (hF : IsSelfVisible 2 F)
    (hFα : AtStage α F) : StageType.{u} α 3 where
  toScheme := S
  label := labelling ⊤ F
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_labelling (isSelfVisible_top 1) hF le_top
  atStage d := by
    unfold labelling
    split_ifs
    · exact atStage_top
    · exact hFα
    · exact atStage_bot

variable (hF : IsSelfVisible 2 F) (hFα : AtStage α F)

/-- The display: `D₀` with the apex added. -/
private noncomputable def Q : StageType.{u} α 3 :=
  (D₀ α F hF hFα).addApex isLegalBelowFullGrade_S (by omega)

/-- The display is legal. -/
private theorem isLegal_Q : (Q hF hFα).IsLegal := StageType.isLegal_addApex _ _

/-- The cells of the display below the apex, those of `D₀`. -/
private noncomputable def oldCell (d : Fin 9) : Fin (Q hF hFα).card := Fin.castSucc d

/-- The apex of the display. -/
private noncomputable def apexCell : Fin (Q hF hFα).card := Fin.last 9

private theorem faces_Q : (Q hF hFα).toCellScheme.faces = Geometry.intervalPlan univ := rfl

private theorem gradedIndex_oldCell (d : Fin 9) :
    (Q hF hFα).toCellScheme.gradedIndex (oldCell hF hFα d) = cells.gradedIndex d :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc S 3 d

private theorem gradedIndex_apexCell :
    (Q hF hFα).toCellScheme.gradedIndex (apexCell hF hFα) = ((univ : Finset (Fin 3)), 3) :=
  Scheme.appendFullCellScheme_gradedIndex_last S 3

private theorem scope_oldCell (d : Fin 9) :
    (Q hF hFα).toCellScheme.scope (oldCell hF hFα d) = cellScope d :=
  Scheme.appendFullCellScheme_scope_castSucc S 3 d

private theorem scope_apexCell : (Q hF hFα).toCellScheme.scope (apexCell hF hFα) = univ :=
  Scheme.appendFullCellScheme_scope_last S 3

private theorem label_oldCell (d : Fin 9) :
    (Q hF hFα).label (oldCell hF hFα d) = labelling ⊤ F d :=
  addApex_label_castSucc (t := D₀ α F hF hFα) isLegalBelowFullGrade_S (by omega) d

private theorem cases_Q (i : Fin (Q hF hFα).card) :
    i = apexCell hF hFα ∨ ∃ d : Fin 9, i = oldCell hF hFα d := by
  -- The cells of the display are those of `D₀` and the apex (`addApex`, by definition).
  change Fin ((D₀ α F hF hFα).toScheme.card + 1) at i
  induction i using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- The row of an old cell at an old cell is the row of `S`. -/
private theorem row_oldCell (s : Fin 9) (t : (Q hF hFα).toCellScheme.below
      ((Q hF hFα).toCellScheme.gradedIndex (oldCell hF hFα s))) (d : Fin 9)
    (ht : t.1 = oldCell hF hFα d) :
    (Q hF hFα).rows.row (oldCell hF hFα s) t =
      if live s = true ∧ live d = true then rowValue else ⊥ := by
  obtain ⟨t, ht'⟩ := t
  subst ht
  -- The rows of `addApex` at an old cell, unfolded (`Scheme.appendFullCell`, by definition).
  change (if hs : Fin.castSucc s = Fin.last _ then _ else _) = _
  exact (dite_eq_right_of_eq_false (eq_false (Fin.castSucc_ne_last s))).trans rfl

private theorem mem_faces_castSuccEmb :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ (Q hF hFα).toCellScheme.faces := by
  rw [faces_Q]; decide +kernel

/-- The empty root. -/
def emptyRoot : Fin 0 ↪ Fin 2 := ⟨Fin.elim0, fun a ↦ a.elim0⟩

private theorem univ_map_extendByLast_f :
    univ.map (extendByLast emptyRoot) = ({2} : Finset (Fin 3)) := by
  rw [univ_map_extendByLast]; decide +kernel

private theorem mem_faces_extendByLast :
    univ.map (extendByLast emptyRoot) ∈ (Q hF hFα).toCellScheme.faces := by
  rw [univ_map_extendByLast_f, faces_Q]; decide +kernel

/-- The private type: the face `{0, 1}` of the display. -/
private noncomputable def P : StageType.{u} α 2 :=
  (Q hF hFα).comap Fin.castSuccEmb (mem_faces_castSuccEmb hF hFα)

/-- The donor: the face `{2}` of the display. -/
private noncomputable def d : StageType.{u} α 1 :=
  (Q hF hFα).comap (extendByLast emptyRoot) (mem_faces_extendByLast hF hFα)

private theorem mem_faces_emptyRoot : univ.map emptyRoot ∈ (P hF hFα).toCellScheme.faces := by
  rw [P, map_univ_mem_comap_faces_iff, faces_Q]; decide +kernel

/-- The type of the root, on no points. -/
private noncomputable def p : StageType.{u} α 0 :=
  (P hF hFα).comap emptyRoot (mem_faces_emptyRoot hF hFα)

private theorem restrictFace_P : restrictFace Fin.castSuccEmb (Q hF hFα) = some (P hF hFα) :=
  restrictFace_of_mem _ _ _

private theorem restrictFace_d :
    restrictFace (extendByLast emptyRoot) (Q hF hFα) = some (d hF hFα) :=
  restrictFace_of_mem _ _ _

private theorem restrictFace_p : restrictFace emptyRoot (P hF hFα) = some (p hF hFα) :=
  restrictFace_of_mem _ _ _

private theorem restrictFace_d_castSuccEmb :
    restrictFace Fin.castSuccEmb (d hF hFα) = some (p hF hFα) := by
  rw [restrictFace_trans _ _ _ (restrictFace_d hF hFα), castSuccEmb_trans_extendByLast,
    ← restrictFace_trans _ _ _ (restrictFace_P hF hFα), restrictFace_p]

/-- The cells visible through the private face are the old cells with scope in `{0, 1}`. -/
private theorem mem_visible_castSuccEmb (d : Fin 9) :
    oldCell hF hFα d ∈
        (Q hF hFα).toCellScheme.visible (Set.range (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) ↔
      cellScope d ⊆ {0, 1} := by
  -- Visibility is containment of the scope (`CellScheme.visible`, by definition).
  change ((Q hF hFα).toCellScheme.scope (oldCell hF hFα d) : Set (Fin 3)) ⊆ _ ↔ _
  rw [scope_oldCell]
  have : Set.range (Fin.castSuccEmb : Fin 2 ↪ Fin 3) =
      (({0, 1} : Finset (Fin 3)) : Set (Fin 3)) := by
    ext x; fin_cases x <;> simp [Fin.ext_iff]
  rw [this, coe_subset]

/-- The only cell visible through the donor face is the cell `2`. -/
private theorem eq_of_mem_visible_extendByLast (e : Fin (Q hF hFα).card)
    (he : e ∈ (Q hF hFα).toCellScheme.visible (Set.range (extendByLast emptyRoot))) :
    e = oldCell hF hFα 2 := by
  have hr : Set.range (extendByLast emptyRoot) = (({2} : Finset (Fin 3)) : Set (Fin 3)) := by
    rw [← univ_map_extendByLast_f]; simp
  -- Visibility is containment of the scope (`CellScheme.visible`, by definition).
  change ((Q hF hFα).toCellScheme.scope e : Set (Fin 3)) ⊆ _ at he
  rw [hr, coe_subset] at he
  rcases cases_Q hF hFα e with rfl | ⟨d, rfl⟩
  · rw [scope_apexCell] at he
    exact absurd (he (mem_univ 0)) (by decide)
  · rw [scope_oldCell] at he
    congr 1
    revert d; decide +kernel

/-- The gated extension of the private type over the empty root with the donor `{2}`: the gate is
the cell at `(univ, 2)`, which has no twins, and the cap is the cell at `({0, 1}, 2)`. -/
private noncomputable def E (hF0 : F ≠ ⊥) : GatedExtension (P hF hFα) emptyRoot (d hF hFα) where
  display := Q hF hFα
  isLegal := isLegal_Q hF hFα
  restrictFace_castSuccEmb := restrictFace_P hF hFα
  restrictFace_extendByLast := restrictFace_d hF hFα
  gate := oldCell hF hFα 8
  cap := oldCell hF hFα 6
  gradedIndex_gate := by rw [gradedIndex_oldCell]; rfl
  gradedIndex_cap := by rw [gradedIndex_oldCell, gradedIndex_cells]; decide +kernel
  label_twin t ht htG := by
    rcases cases_Q hF hFα t with rfl | ⟨e, rfl⟩
    · rw [gradedIndex_apexCell] at ht
      exact absurd (congrArg Prod.snd ht) (by decide)
    · rw [gradedIndex_oldCell] at ht
      have : e = 8 := gradedIndex_injective (ht.trans rfl)
      exact absurd (congrArg (oldCell hF hFα) this) htG
  isGate :=
    { cap_mem := (mem_visible_castSuccEmb hF hFα 6).mpr (by decide)
      scope_cap_subset := by rw [scope_oldCell, scope_oldCell]; exact subset_univ _
      grade_cap := rfl
      cap_ne_bot := by
        rw [label_oldCell]
        simpa [labelling, live, cellGrade] using hF0
      le_gate := fun e he ↦ by
        rw [eq_of_mem_visible_extendByLast hF hFα e he, gradedIndex_oldCell,
          gradedIndex_oldCell]
        simp only [gradedIndex_cells, Prod.mk_le_mk]; decide
      reads := fun e he hnot ↦ by
        obtain rfl := eq_of_mem_visible_extendByLast hF hFα e he
        refine .top ⟨oldCell hF hFα 6, by
            -- Membership below the gate compares graded indices (`CellScheme.below`).
            change (Q hF hFα).toCellScheme.gradedIndex (oldCell hF hFα 6) ≤
              (Q hF hFα).toCellScheme.gradedIndex (oldCell hF hFα 8)
            rw [gradedIndex_oldCell, gradedIndex_oldCell]
            simp only [gradedIndex_cells, Prod.mk_le_mk]; decide⟩
          ((mem_visible_castSuccEmb hF hFα 6).mpr (by decide)) le_rfl ?_ ?_
        · rw [label_oldCell hF hFα 2]; simp [labelling, live, cellGrade]
        · rw [row_oldCell hF hFα 8 _ 6 rfl, row_oldCell hF hFα 8 _ 2 rfl]
          simp [live] }

/-- The gate of `E` has no twins. -/
private theorem eq_gate_of_gradedIndex (hF0 : F ≠ ⊥) (t : Fin (Q hF hFα).card)
    (ht : (Q hF hFα).toCellScheme.gradedIndex t = (univ, 2)) : t = (E hF hFα hF0).gate := by
  rcases cases_Q hF hFα t with rfl | ⟨e, rfl⟩
  · rw [gradedIndex_apexCell] at ht
    exact absurd (congrArg Prod.snd ht) (by decide)
  · rw [gradedIndex_oldCell] at ht
    exact congrArg (oldCell hF hFα) (gradedIndex_injective (ht.trans rfl))

end VaughtConjecture.GatedExtensionExample

namespace VaughtConjecture.StageType

open Finset Label GatedExtensionExample

/-- **The structure of a gated extension is inhabited** at private arity `2` over the empty root:
for every label `F ≠ ⊥` self-visible at `2` and at the stage `α`, there are a legal private type
`P` on two points, the type `p` of the empty root, a legal donor `d` on one point, and a cell `C`
of `P` of graded index `(univ, 2)` not labelled `⊥`, below which `d` is anchored, so that every
hypothesis of the gated pinned extension property holds for them, and a gated extension of `P`
over the empty root with donor `d` whose cap carries the label of `C` and whose gate has no
twins.  Here `P` has a unique cell of graded index `(univ, 2)`.  The private type
`GatedExtensionCounterexample.P α`, whose two such cells are ordered oppositely by two lawful
labellings in the cap ball of its labelling at `2`, has no gated extension
(`GatedExtensionCounterexample.isEmpty_gatedExtension`). -/
theorem GatedExtension.instance_two_zero {α : Ordinal.{u}} {F : Label.{u}}
    (hF : IsSelfVisible 2 F) (hFα : AtStage α F) (hF0 : F ≠ ⊥) :
    ∃ (P : StageType.{u} α 2) (p : StageType.{u} α 0) (d : StageType.{u} α 1) (C : Fin P.card),
      P.IsLegal ∧ restrictFace emptyRoot P = some p ∧ d.IsLegal ∧
      restrictFace Fin.castSuccEmb d = some p ∧ P.toCellScheme.gradedIndex C = (univ, 2) ∧
      P.label C ≠ ⊥ ∧ P.IsAnchored C d ∧
      ∃ E : GatedExtension P emptyRoot d, E.display.label E.cap = P.label C ∧
        ∀ t, E.display.toCellScheme.gradedIndex t = (univ, 2) → t = E.gate := by
  have h6 : oldCell hF hFα 6 ∈ Set.range ((Q hF hFα).cellMap Fin.castSuccEmb) := by
    rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]
    exact (mem_visible_castSuccEmb hF hFα 6).mpr (by decide)
  obtain ⟨C, hC⟩ := h6
  have hlab : (P hF hFα).label C = F := by
    -- The labels of the face `P` are those of its cells in the display (`comap_label`).
    change (Q hF hFα).label ((Q hF hFα).cellMap Fin.castSuccEmb C) = F
    rw [hC, label_oldCell]; simp [UnionFillCounterexample.labelling,
      UnionFillCounterexample.live, UnionFillCounterexample.cellGrade]
  refine ⟨P hF hFα, p hF hFα, d hF hFα, C,
    (isLegal_Q hF hFα).restrictFace _ (restrictFace_P hF hFα), restrictFace_p hF hFα,
    (isLegal_Q hF hFα).restrictFace _ (restrictFace_d hF hFα), restrictFace_d_castSuccEmb hF hFα,
    ?_, by rw [hlab]; exact hF0, ?_, E hF hFα hF0, ?_, eq_gate_of_gradedIndex hF hFα hF0⟩
  · -- The cap has full scope and grade `2` in the private type.
    have hsc : (P hF hFα).toCellScheme.scope C = univ := by
      -- The scope of a cell of `P` is the preimage of its scope in the display (`comap_scope`).
      change ((Q hF hFα).toCellScheme.scope ((Q hF hFα).cellMap Fin.castSuccEmb C)).preimage
        Fin.castSuccEmb (Fin.castSuccEmb.injective.injOn) = _
      rw [hC, scope_oldCell]
      ext x; fin_cases x <;> simp [UnionFillCounterexample.cellScope]
    have hgr : (P hF hFα).toCellScheme.grade C = 2 := by
      -- A cell of `P` has its grade in the display (`comap_grade`).
      change (Q hF hFα).toCellScheme.grade ((Q hF hFα).cellMap Fin.castSuccEmb C) = 2
      rw [hC]; rfl
    exact Prod.ext hsc hgr
  · -- Every donor label is `⊤`.
    refine isAnchored_of_forall_label_eq_bot_or_top _ _ fun j _ ↦ .inr ?_
    -- The labels of the donor are those of its cells in the display (`comap_label`).
    change (Q hF hFα).label ((Q hF hFα).cellMap (extendByLast emptyRoot) j) = ⊤
    have hj := (Q hF hFα).cellMap_mem (extendByLast emptyRoot) j
    rw [Scheme.mem_visibleCells] at hj
    rw [eq_of_mem_visible_extendByLast hF hFα _ hj, label_oldCell]
    simp [UnionFillCounterexample.labelling, UnionFillCounterexample.live,
      UnionFillCounterexample.cellGrade]
  · -- The cap of `E` is the old cell `6` of the display `Q` (`E`, by definition).
    change (Q hF hFα).label (oldCell hF hFα 6) = (P hF hFα).label C
    rw [hlab, label_oldCell]
    simp [UnionFillCounterexample.labelling, UnionFillCounterexample.live,
      UnionFillCounterexample.cellGrade]

end VaughtConjecture.StageType
