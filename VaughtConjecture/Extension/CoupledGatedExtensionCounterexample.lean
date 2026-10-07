/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.GatedExtensionCounterexample

/-!
# The coupled gated pinned extension property fails at every stage above `1`

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate) and 3.4, row
(R1); the coupled gated extensions of `VaughtConjecture.Extension.GatedExtension`.

**The theorem** (`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`).  The
coupled gated pinned extension property `StageType.HasCoupledGatedPinnedExtensions α` is false at
every stage `α > 1`.  The input that defeats it has private arity `n = 2`, the empty root
(`m = 0`), a donor on one point with two cells, and a private type with a **proper anchor**: a cell
`z₁` of grade `1` labelled `1`, which is not self-visible at the grade `2` of the gate, so that the
donor label `vr_2(1, 1) = 1` below the cap is read through `z₁`.  Every hypothesis of the property
holds there (legality, the faces, `0 + 1 < 2`, the cap not `⊥`, anchoring).  The failure is in
the legality of the display, at the lift from the private face `({0, 1}, 2)` to `(univ, 2)` at the
cap `⊥`, jointly with the readings of the gate; nothing is used about cap lowering (CL) or about
the lifts from faces containing the new point.

**The bottom transport condition** (`StageType.CarriesBottoms`, forced by every coupled gated
extension: `StageType.CoupledGatedExtension.carriesBottoms`).  Let `E` be a coupled gated extension
of `P` over `f` with donor `d`, and `a` a lawful labelling of `P` not `⊥` at the cells of `P` of
graded index `(univ, n)` labelled as the cap.
* By bountifulness of the display from its private face at the cap `⊥`, `a` is the private face of
  a lawful labelling `r` of the display (`Scheme.IsLegal.exists_isLawful_extend`).
* `r` is not `⊥` at the cap, so not at the gate (`StageType.CoupledGatedExtension.cap_le_gate`,
  from the twin–gate coupling).
* The locality of `r` at the gate has one witness `(g, σ)`, which decodes every cell below the
  gate up to `r G`.  A donor cell `e` labelled `vr_n(w z, i)` (`w` the display's labelling, `z` its
  anchor) is read by the row of the gate as `vr_n` of its reading of `z`, so
  `min (r e) (r G) = min (vr_n(r z, i)) (r G)` (`Label.IsWitness.min_apply_visibilityReplace`).
  Hence `r e = ⊥` when `r` is `⊥` at every possible anchor of `e`
  (`CellScheme.Rows.IsLawful.eq_bot_of_gateReads`), and `r e ≠ ⊥` when `r` is not `⊥` at any
  private cell that can serve the reading of `e` (`CellScheme.Rows.IsLawful.ne_bot_of_gateReads`).
* The donor face of `r` is a lawful labelling of `d`.

So the readings of the gate carry the bottom pattern of every lawful private labelling, at the
anchors, to a lawful labelling of the donor.  The coupled gated pinned extension property forces
the condition at each of its inputs (`StageType.HasCoupledGatedPinnedExtensions.carriesBottoms`).

**When the condition holds** (`StageType.carriesBottoms_of_row_mem_block`).  If the row of the cap
reads, for every donor label below the cap, an anchor of that label in the block of its reading of
the cap itself, then no lawful labelling of `P` that keeps the cap drops that anchor
(`CellScheme.Rows.IsLawful.ne_bot_of_row_mem_block`: a shifter sending the reading of the anchor to
`⊥` sends its whole block to `⊥`), and the donor's own labelling meets the condition.  The
condition is necessary for the property, not shown sufficient.  More generally, a lawful labelling
that keeps a cell `C` and drops a cell `x` that the row of `C` reads at an ordinal drops every
cell that the row of `C` reads below the end of the block of that reading
(`CellScheme.Rows.IsLawful.eq_bot_of_row_le_block`), so the row of `C` reads `C` above that block
(`CellScheme.Rows.IsLawful.lt_row_self_of_eq_bot`).  These concern cells read at ordinals: a cell
read as `⊥` has no block (the dead cells of the input below are read as `⊥`, and are `⊥` in every
lawful labelling that keeps the cap).

**The anchor readings at a positive cap**
(`CellScheme.Rows.IsLawful.min_eq_visibilityReplace_of_min_eq`).  Part 2 of the requirement named
in `VaughtConjecture.Extension.CapLowering` asks whether the readings of the donor cells or of the
anchors can force the gate below some `v < c` while the ambient gate is at least `c`.  For the
anchor readings they cannot: every labelling in the cap ball of the ambient at `c` satisfies
`min (q' e) c = min (vr_n(q' z, i)) c`, the reading at the gate value `c`.  The joint lawfulness of
such a lift (part 3) and the rows (part 4) are not decided in general; the property fails before
them, at the lift from the private face at the cap `⊥`.

**The input** (`P`, `donor`, `isLegal_P`, `isLegal_donor`).  The private type `P α` on two points
with the interval plan:

| cell       | scope | grade | label | code (the row of the full cell) |
|------------|-------|-------|-------|---------------------------------|
| 0, 1       | {0}, {1} | 1  | `⊥`   | `⊥` (dead)                      |
| 2 (`z₁`)   | univ  | 1     | `1`   | `1`                             |
| 3 (`z₂`)   | univ  | 1     | `⊤`   | `ω + 1`                         |
| 4 (`C`)    | univ  | 2     | `⊤`   | `ω + 2`                         |

The rows of `z₂` and `C` are the codes, the row of `z₁` reads `z₁` and `z₂` at `1`, and the dead
cells read `⊥`.  Its labelling `1, ⊤, ⊤` raises the codes at `3` and above to `⊤`
(`Label.raise`), and the labelling `⊥, ω + 1, ω + 2` sends the codes below `ω` to `⊥` (a witness
with the suppressor `⊤`, since visibility replacement keeps the block `[0, ω)`): it drops the
anchor `z₁` and keeps the cap (`isLawful_lab_bot_omegaAdd`).  Bountifulness holds because a lift
between two faces at the same grade starts below a dead cell.  The donor on one point has two cells
`e₁`, `e₂` labelled `1` and `⊤`; the row of `e₂` reads them at `1` and `2`, in one block, so a
shifter sending `1` to `⊥` sends `2 = vr_2(1, 2)` to `vr_2(⊥, 2) = ⊥`, the guard of the commutation
law holding at `⊥`: no lawful labelling of the donor is `⊥` at `e₁` and not at `e₂`
(`eq_bot_of_isLawful_donor`).  The donor's labelling `1, ⊤` is lawful (the row of `e₂` raised at
`2`).  The only possible anchor of `e₁` is `z₁` (label `1 = vr_2(1, 1)`; `z₁` is the only cell of
`P α` labelled in the block `[0, ω)`), and every private cell that can serve the reading of `e₂` is
labelled `⊤`.  So the bottom transport condition asks for a lawful labelling of the donor
`⊥` at `e₁` and not at `e₂` (`not_carriesBottoms`), and no coupled gated extension exists
(`isEmpty_coupledGatedExtension`).

**What this refutes and what it does not.**
* It refutes the universal hypothesis `StageType.HasCoupledGatedPinnedExtensions α` at every stage
  `α > 1`, whatever the display: only the clauses of `StageType.CoupledGatedExtension` are used
  (the legality of the display, its literal faces, the graded indices of the gate and the cap, the
  twin–gate coupling and the readings of the gate).  The identified obstruction survives the
  redesigns examined (the twins labelled `⊥`, and the twin–gate coupling); a redesign that weakens
  the legality of the display at the private coatom is not covered.  So the conditional (R1)
  (`Realization.IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions`,
  `Expansion.finiteCutReceiving_of_hasCoupledGatedPinnedExtensions`) is vacuous at those stages.
* It does not refute (R1), finite-cut receiving for all models: whether the private types that
  models acquire (`Realization.IsModel.exists_privateContext`) can carry such an anchor
  (a lawful labelling of the private type that is `⊥` at an anchor and not at the cap, with a donor
  whose rows read the transported pattern within one block) is not decided here.  The refuting
  input satisfies the finite stage-type and label conditions of the output of
  `Realization.IsModel.exists_privateContext` (with `N₀ ≤ 2`) and of its anchored form, at every
  floor (`exists_privateContext_not_carriesBottoms`), so those conditions alone do not give the
  bottom transport condition.  No occurrence of this input in an actual model is exhibited, and
  whether every model acquires a private context satisfying the condition
  (`Realization.AcquiresCarryingContexts`) is undecided.
* The refuting private type has a unique cell of full scope and full grade, and cells of grade
  `1` not labelled `⊥`; so neither of the conditions on private contexts asked about in
  `VaughtConjecture.Realization.CoupledFiniteCutReceiving` (question (M4)) excludes it.
* The input has a proper anchor below the cap.  When every donor label below the cap is `⊥`, the
  condition is met by the donor's own labelling (`StageType.carriesBottoms_of_forall_label`);
  the instances of the property compiled at the private type `GatedExtensionCounterexample.P α`,
  whose labels are `⊥` and `⊤`
  (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`,
  `CoupledGateInstance.coupledGatedPinnedExtension_donor`, and with every anchored legal one-point
  donor, `CoupledGateOnePointDonors.coupledGatedPinnedExtension_P`), have no proper anchor.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.CoupledGatedExtensionCounterexample

open Finset Label CellScheme Ordinal

/-! ### A witness sending the finite labels to `⊥` -/

/-- The labels below `ω` (the finite ones and `⊥`) go to `⊥`; the others are kept. -/
private noncomputable def dropFinite (x : Label.{u}) : Label.{u} :=
  if x < ((ω : Ordinal.{u}) : Label.{u}) then ⊥ else x

private theorem lt_omega_visibilityReplace {x : Label.{u}}
    (hx : x < ((ω : Ordinal.{u}) : Label.{u})) (k i : ℕ) :
    visibilityReplace k i x < ((ω : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => simp
  | coe o =>
    have ho : o < ω := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hx)
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ho
    have h : visibilityReplace k i ((n : Ordinal.{u}) : Label.{u}) =
        visibilityReplace k i (n : Label.{u}) := rfl
    rw [h, Label.visibilityReplace_natCast]
    split_ifs
    · exact natCast_label_lt_omega i
    · exact natCast_label_lt_omega n
  | top => exact absurd hx (not_lt.mpr le_top)

/-- Sending the labels below `ω` to `⊥` is a witness, with the suppressor `⊤`: visibility
replacement keeps a label below `ω` below `ω`, and one at least `ω` at least `ω`. -/
private theorem isWitness_dropFinite : IsWitness (fun _ ↦ (⊤ : Label.{u})) dropFinite where
  antitone := fun _ _ _ ↦ le_rfl
  isSelfVisible := fun n ↦ isSelfVisible_top n
  map_bot := by simp [dropFinite, WithBot.bot_lt_coe]
  monotone := by
    intro x y hxy
    unfold dropFinite
    split_ifs with hx hy hy
    · exact le_rfl
    · exact bot_le
    · exact absurd (hxy.trans_lt hy) hx
    · exact hxy
  visibilityReplace_comm x k _ i _ := by
    unfold dropFinite
    by_cases hx : x < ((ω : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left (lt_omega_visibilityReplace hx k i), ite_eq_left hx, visibilityReplace_bot]
    · have hx0 : x ≠ ⊥ := fun h ↦ hx (h ▸ WithBot.bot_lt_coe _)
      rw [ite_eq_right (not_lt_omega_visibilityReplace hx0 hx k i), ite_eq_right hx]

/-! ### Label arithmetic -/

/-- The label `ω + j`. -/
noncomputable def omegaAdd (j : ℕ) : Label.{u} := ((ω + j : Ordinal.{u}) : Label.{u})

private theorem isSuccPrelimit_omega0 : Order.IsSuccPrelimit (ω : Ordinal.{u}) :=
  Ordinal.isSuccLimit_omega0.isSuccPrelimit

private theorem isSelfVisible_omegaAdd {k j : ℕ} (h : k ≤ j) :
    IsSelfVisible k (omegaAdd.{u} j) :=
  isSelfVisible_coe_add isSuccPrelimit_omega0 h

private theorem omegaAdd_ne_bot (j : ℕ) : omegaAdd.{u} j ≠ ⊥ := WithBot.coe_ne_bot

private theorem omega_le_omegaAdd (j : ℕ) :
    ¬ omegaAdd.{u} j < ((ω : Ordinal.{u}) : Label.{u}) := by
  intro h
  have h' : ω + (j : Ordinal.{u}) < ω := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h)
  exact absurd h' (not_lt.mpr le_self_add)

private theorem omegaAdd_le_omegaAdd {i j : ℕ} (h : i ≤ j) : omegaAdd.{u} i ≤ omegaAdd j :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (add_le_add_right (Nat.cast_le.mpr h) _))

private theorem natCast_le_omegaAdd (n j : ℕ) : ((n : ℕ) : Label.{u}) ≤ omegaAdd j :=
  (natCast_label_lt_omega n).le.trans (not_lt.mp (omega_le_omegaAdd j))

private theorem natCast_lt_omegaAdd (n j : ℕ) : ((n : ℕ) : Label.{u}) < omegaAdd j :=
  (natCast_label_lt_omega n).trans_le (not_lt.mp (omega_le_omegaAdd j))

private theorem omegaAdd_lt_omega0_sq (j : ℕ) :
    omegaAdd.{u} j < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
  lt_omega0_sq_iff.mpr (.inr ⟨1, j, by simp [omegaAdd]⟩)

/-! ### The private type: two points, a proper anchor, and a full cell -/

/-- The scopes of the five cells: `{0}`, `{1}` (dead), `univ` (the cells `z₁ = 2`, `z₂ = 3` of
grade `1`) and `univ` (the full cell `4`). -/
def cellScope : Fin 5 → Finset (Fin 2) := ![{0}, {1}, univ, univ, univ]

/-- The grades of the five cells. -/
def cellGrade : Fin 5 → ℕ := ![1, 1, 1, 1, 2]

/-- The cell scheme on two points with the interval plan. -/
def cells : CellScheme (Fin 5) (Fin 2) := ⟨univ, Geometry.intervalPlan univ, cellScope, cellGrade⟩

/-- The codes `1`, `ω + 1`, `ω + 2` at the cells `2`, `3`, `4`, and `⊥` at the dead cells. -/
noncomputable def code : Fin 5 → Label.{u} :=
  ![⊥, ⊥, ((1 : ℕ) : Label.{u}), omegaAdd 1, omegaAdd 2]

private noncomputable def rowValue (s t : Fin 5) : Label.{u} :=
  if s = 2 then (if t = 2 ∨ t = 3 then ((1 : ℕ) : Label.{u}) else ⊥)
  else if s = 3 ∨ s = 4 then code t else ⊥

/-- The rows: the row of `z₁ = 2` reads `z₁` and `z₂` at `1`; the rows of `z₂ = 3` and of the
full cell `4` read the codes `1`, `ω + 1`, `ω + 2`; the dead cells read `⊥`. -/
noncomputable def rows : cells.Rows.{u} := ⟨fun s t ↦ rowValue s t.1⟩

/-- The scheme on two points. -/
noncomputable def S : Scheme.{u} 2 := ⟨5, cells, rows⟩

/-- The labelling `⊥, ⊥, x, y, w`. -/
noncomputable def lab (x y w : Label.{u}) : Fin 5 → Label.{u} := ![⊥, ⊥, x, y, w]


/-! ### Lawful labellings of the private type -/

/-- The graded index of a cell is its scope and grade. -/
theorem gradedIndex_cells (d : Fin 5) : cells.gradedIndex d = (cellScope d, cellGrade d) := rfl

private theorem availability_cases : ∀ s t : Fin 5, cellScope s ⊆ cellScope t →
    cellGrade s = cellGrade t → (s = 0 ∨ s = 1) ∨ (cellScope t = cellScope s ∧
      cellGrade t = cellGrade s) := by
  decide

/-- The labellings `lab x y w` are lawful once the localities at the three live cells hold. -/
private theorem isLawful_lab_of {x y w : Label.{u}} (hx : IsSelfVisible 1 x)
    (hy : IsSelfVisible 1 y) (hw : IsSelfVisible 2 w)
    (h2 : TransformsTo (fun d : cells.below (cells.gradedIndex 2) ↦ cells.grade d) (rows.row 2)
      (fun d ↦ min (lab x y w d) x))
    (h3 : TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.row 3)
      (fun d ↦ min (lab x y w d) y))
    (h4 : TransformsTo (fun d : cells.below (cells.gradedIndex 4) ↦ cells.grade d) (rows.row 4)
      (fun d ↦ min (lab x y w d) w)) : rows.{u}.IsLawful (lab x y w) where
  orderly d := by
    fin_cases d
    exacts [isSelfVisible_bot _, isSelfVisible_bot _, hx, hy, hw]
  locality s := by
    fin_cases s
    · simpa [lab] using TransformsTo.bot _ (rows.row 0)
    · simpa [lab] using TransformsTo.bot _ (rows.row 1)
    · exact h2
    · exact h3
    · exact h4
  availability s t hst hg := by
    rcases availability_cases s t hst hg with hs | ⟨h1, h2⟩
    · refine ⟨t, rfl, ?_⟩
      rcases hs with rfl | rfl <;> exact bot_le
    · exact ⟨s, Prod.ext h1.symm h2.symm, le_rfl⟩

/-- A locality from a witness, checked cell by cell. -/
private theorem transformsTo_of (s : Fin 5) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {F : Fin 5 → Label.{u}}
    (h : ∀ d : Fin 5, cells.gradedIndex d ≤ cells.gradedIndex s →
      F d = min (σ (rowValue s d)) (g (cellGrade d))) :
    TransformsTo (fun d : cells.below (cells.gradedIndex s) ↦ cells.grade d) (rows.row s)
      (fun d ↦ F d) :=
  ⟨g, σ, hw, fun d ↦ h d.1 d.2⟩

private theorem not_below_four_two : ¬ cells.gradedIndex (4 : Fin 5) ≤ cells.gradedIndex 2 := by
  decide

private theorem not_below_four_three :
    ¬ cells.gradedIndex (4 : Fin 5) ≤ cells.gradedIndex 3 := by
  decide

private theorem three_le_omegaAdd (j : ℕ) : ((3 : ℕ) : Label.{u}) ≤ omegaAdd j :=
  natCast_le_omegaAdd 3 j

private theorem not_three_le_one : ¬ ((3 : ℕ) : Label.{u}) ≤ ((1 : ℕ) : Label.{u}) :=
  not_le.mpr (natCast_label_lt.mpr (by decide))

private theorem one_lt_omegaAdd (j : ℕ) : ((1 : ℕ) : Label.{u}) < omegaAdd j :=
  natCast_lt_omegaAdd 1 j

private theorem dropFinite_bot : dropFinite (⊥ : Label.{u}) = ⊥ := isWitness_dropFinite.map_bot

private theorem dropFinite_one : dropFinite (1 : Label.{u}) = ⊥ := by
  have h : (1 : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by simp
  simp only [dropFinite, ite_eq_left h]

private theorem dropFinite_omegaAdd (j : ℕ) : dropFinite (omegaAdd.{u} j) = omegaAdd j := by
  simp only [dropFinite, ite_eq_right (omega_le_omegaAdd j)]

private theorem raise_one : raise (3 : Label.{u}) 1 = 1 := by
  have h : ¬ (3 : Label.{u}) ≤ 1 := by simp
  simp only [raise, ite_eq_right h]

private theorem raise_omegaAdd (j : ℕ) : raise (3 : Label.{u}) (omegaAdd j) = ⊤ := by
  have h : (3 : Label.{u}) ≤ omegaAdd j := by simpa using three_le_omegaAdd.{u} j
  simp only [raise, ite_eq_left h]

private theorem raise_bot' : raise (3 : Label.{u}) ⊥ = ⊥ :=
  raise_bot (bot_lt_iff_ne_bot.mpr (by simp))

private theorem isWitness_raise_three {K : ℕ} (hK : K ≤ 2) :
    IsWitness (stepSuppressor.{u} K) (raise (3 : Label.{u})) :=
  isWitness_raise (by simp; omega) (bot_lt_iff_ne_bot.mpr (by simp))

/-- **The labelling of the private type**, `⊥, ⊥, 1, ⊤, ⊤`, is lawful: raising the codes at `3`
and above to `⊤`. -/
theorem isLawful_lab_one_top_top :
    rows.{u}.IsLawful (lab (1 : Label.{u}) ⊤ ⊤) := by
  refine isLawful_lab_of (by simp) (isSelfVisible_top 1) (isSelfVisible_top 2) ?_ ?_ ?_
  · refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) | simp [lab, rowValue]
  · refine transformsTo_of 3 (F := fun d ↦ min (lab _ _ _ d) _)
      (isWitness_raise_three (K := 1) (by omega)) fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) |
      simp [lab, rowValue, code, cellGrade, raise_one, raise_omegaAdd, raise_bot']
  · refine transformsTo_of 4 (F := fun d ↦ min (lab _ _ _ d) _)
      (isWitness_raise_three (K := 2) le_rfl) fun d _ ↦ ?_
    fin_cases d <;> simp [lab, rowValue, code, cellGrade, raise_one, raise_omegaAdd, raise_bot']

/-- **A lawful labelling that drops the anchor `z₁`**: `⊥, ⊥, ⊥, ω + 1, ω + 2`, the codes with
the finite labels sent to `⊥`. -/
theorem isLawful_lab_bot_omegaAdd :
    rows.{u}.IsLawful (lab ⊥ (omegaAdd 1) (omegaAdd 2)) := by
  refine isLawful_lab_of (isSelfVisible_bot 1) (isSelfVisible_omegaAdd (by omega))
    (isSelfVisible_omegaAdd le_rfl) ?_ ?_ ?_
  · refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.bot_top fun d _ ↦ ?_
    fin_cases d <;> simp [lab]
  · refine transformsTo_of 3 (F := fun d ↦ min (lab _ _ _ d) _) isWitness_dropFinite fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) |
      simp [lab, rowValue, code, dropFinite_bot, dropFinite_one, dropFinite_omegaAdd]
  · refine transformsTo_of 4 (F := fun d ↦ min (lab _ _ _ d) _) isWitness_dropFinite fun d _ ↦ ?_
    fin_cases d <;> simp [lab, rowValue, code, dropFinite_bot, dropFinite_one,
      dropFinite_omegaAdd, omegaAdd_le_omegaAdd]


private theorem topShifter_one :
    TransformsTo (fun d : cells.below (cells.gradedIndex 3) ↦ cells.grade d) (rows.{u}.row 3)
      (fun d ↦ min (lab 1 1 ⊥ d.1) (1 : Label.{u})) := by
  refine ⟨constStepSuppressor 1 1, topShifter,
    isWitness_topShifter (antitone_constStepSuppressor _ _)
      (isSelfVisible_constStepSuppressor (by simp)), fun d ↦ ?_⟩
  obtain ⟨d, hd⟩ := d
  fin_cases d <;> first | exact absurd hd (by decide) |
    simp [lab, rows, rowValue, code, topShifter, constStepSuppressor, cells, cellGrade,
      omegaAdd_ne_bot]

/-- The row of `z₁ = 2` read as a labelling, `⊥, ⊥, 1, 1`, is lawful. -/
private theorem isLawful_lab_one_one_bot : rows.{u}.IsLawful (lab 1 1 ⊥) := by
  refine isLawful_lab_of (by simp) (by simp) (isSelfVisible_bot 2) ?_ topShifter_one ?_
  · refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) | simp [lab, rowValue]
  · refine transformsTo_of 4 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.bot_top fun d _ ↦ ?_
    fin_cases d <;> simp [lab]

/-- The codes read as a labelling, `⊥, ⊥, 1, ω + 1, ω + 2`, are lawful. -/
private theorem isLawful_code_lab (w : Label.{u}) (hw : w = ⊥ ∨ w = omegaAdd 2) :
    rows.{u}.IsLawful (lab 1 (omegaAdd 1) w) := by
  have hsv : IsSelfVisible 2 w := by
    rcases hw with rfl | rfl
    exacts [isSelfVisible_bot 2, isSelfVisible_omegaAdd le_rfl]
  refine isLawful_lab_of (by simp) (isSelfVisible_omegaAdd (by omega)) hsv ?_ ?_ ?_
  · refine transformsTo_of 2 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) |
      simp [lab, rowValue]
    simpa using (one_lt_omegaAdd.{u} 1).le
  · refine transformsTo_of 3 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top fun d hd ↦ ?_
    fin_cases d <;> first | exact absurd hd (by decide) |
      simp [lab, rowValue, code]
    simpa using (one_lt_omegaAdd.{u} 1).le
  · rcases hw with rfl | rfl
    · refine transformsTo_of 4 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.bot_top
        fun d _ ↦ ?_
      fin_cases d <;> simp [lab]
    · refine transformsTo_of 4 (F := fun d ↦ min (lab _ _ _ d) _) IsWitness.id_top
        fun d _ ↦ ?_
      fin_cases d <;> simp [lab, rowValue, code, omegaAdd_le_omegaAdd]
      simpa using (one_lt_omegaAdd.{u} 2).le


/-! ### Legality of the private type -/

/-- The scheme on two points is well formed. -/
theorem isWellFormed_S : S.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

private theorem rowValue_lt (s t : Fin 5) :
    rowValue.{u} s t < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have hbot : (⊥ : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := WithBot.bot_lt_coe _
  have h1 := natCast_label_lt_omega0_sq.{u} 1
  have h2 := omegaAdd_lt_omega0_sq.{u} 1
  have h3 := omegaAdd_lt_omega0_sq.{u} 2
  fin_cases s <;> fin_cases t <;> first | exact hbot | exact h1 | exact h2 | exact h3

/-- The scheme on two points is coded. -/
theorem isCoded_S : S.{u}.IsCoded := fun s t ↦ rowValue_lt s t.1

/-- **The rows are consistent**: they are `⊥`, `lab 1 1 ⊥` and the codes. -/
theorem isConsistent_rows : rows.{u}.IsConsistent := by
  intro s
  -- Consistency at `s`: the row of `s` is lawful below its graded index (`IsConsistent`).
  change rows.IsLawfulBelow _ (fun t ↦ rows.row s t)
  rcases (by decide : ∀ s : Fin 5, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4) s with
    rfl | rfl | rfl | rfl | rfl
  · exact Rows.isLawfulBelow_const_bot _
  · exact Rows.isLawfulBelow_const_bot _
  · convert isLawful_lab_one_one_bot.isLawfulBelow (cells.gradedIndex 2) using 1
    funext t
    obtain ⟨t, ht⟩ := t
    fin_cases t <;> first | exact absurd ((cells.mem_below).mp ht) (by decide) |
      simp [rows, rowValue, lab]
  · convert (isLawful_code_lab ⊥ (.inl rfl)).isLawfulBelow (cells.gradedIndex 3) using 1
    funext t
    obtain ⟨t, ht⟩ := t
    fin_cases t <;> first | exact absurd ((cells.mem_below).mp ht) (by decide) |
      simp [rows, rowValue, lab, code]
  · convert (isLawful_code_lab (omegaAdd 2) (.inr rfl)).isLawfulBelow (cells.gradedIndex 4)
      using 1
    funext t
    obtain ⟨t, -⟩ := t
    fin_cases t <;> simp [rows, rowValue, lab, code]

private theorem dead_of_ssubset : ∀ A B : Finset (Fin 2),
    A ∈ Geometry.intervalPlan (univ : Finset (Fin 2)) → A ⊆ B → A ≠ B → ∀ d : Fin 5,
      cellScope d ⊆ A → d = 0 ∨ d = 1 := by
  decide +kernel

/-- **The rows are bountiful**: a lift between two pairs of the same grade on different faces
starts from a pair below which every cell is dead, and keeps the ambient labelling. -/
theorem isBountiful_rows : rows.{u}.IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  by_cases hXY : X.1 = Y.1
  · exact Rows.cappedLift_of_fst_eq _ hXY
  refine Rows.cappedLift_of_forall_row_self_eq_bot (R := rows.{u})
    (X := X) (Y := (Y.1, X.2)) ⟨h.1, le_rfl⟩ ?_
  intro d hd
  have hdead := dead_of_ssubset X.1 Y.1 hX.1 h.1 hXY d hd.1
  -- The diagonal entry of the row of a dead cell is `⊥` (`rows`, by definition).
  change rowValue d d = ⊥
  rcases hdead with rfl | rfl <;> rfl

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

/-- **The private type** on two points: the dead cells `{0}`, `{1}`, the cells `z₁`, `z₂` of
graded index `(univ, 1)` labelled `1` and `⊤`, and the full cell labelled `⊤`.  The label `1` of
`z₁` is not self-visible at `2`: `z₁` is a proper anchor at the threshold `2`. -/
noncomputable def P (α : Ordinal.{u}) (hα : 1 < α) : StageType.{u} α 2 where
  toScheme := S
  label := lab 1 ⊤ ⊤
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_lab_one_top_top
  atStage d := by
    fin_cases d
    exacts [atStage_bot, atStage_bot, (Label.atStage_one.mpr hα), atStage_top, atStage_top]

/-- **The private type is legal.** -/
theorem isLegal_P (α : Ordinal.{u}) (hα : 1 < α) : (P α hα).IsLegal :=
  StageType.isLegal_iff.mpr ⟨isConsistent_rows, isBountiful_rows, isComplete_cells⟩


/-! ### The donor: one point, two cells read within one block -/

/-- The cells of the donor: two cells of graded index `(univ, 1)` on one point. -/
def donorCells : CellScheme (Fin 2) (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

private noncomputable def donorRowValue (s t : Fin 2) : Label.{u} :=
  if s = 0 then 1 else if t = 0 then 1 else 2

/-- The rows of the donor: the row of `e₁ = 0` reads `(1, 1)`, the row of `e₂ = 1` reads
`(1, 2)`; both values of the row of `e₂` lie in the block `[0, ω)`. -/
noncomputable def donorRows : donorCells.Rows.{u} := ⟨fun s t ↦ donorRowValue s t.1⟩

/-- The scheme of the donor. -/
noncomputable def donorScheme : Scheme.{u} 1 := ⟨2, donorCells, donorRows⟩

/-- The labelling `x₀, x₁` of the donor. -/
noncomputable def donorLab (x₀ x₁ : Label.{u}) : Fin 2 → Label.{u} := ![x₀, x₁]

/-- The labellings `donorLab x₀ x₁` are lawful once the two localities hold. -/
private theorem isLawful_donorLab_of {x₀ x₁ : Label.{u}} (h₀ : IsSelfVisible 1 x₀)
    (h₁ : IsSelfVisible 1 x₁)
    (l₀ : TransformsTo (fun d : donorCells.below (donorCells.gradedIndex 0) ↦ donorCells.grade d)
      (donorRows.row 0) (fun d ↦ min (donorLab x₀ x₁ d) x₀))
    (l₁ : TransformsTo (fun d : donorCells.below (donorCells.gradedIndex 1) ↦ donorCells.grade d)
      (donorRows.row 1) (fun d ↦ min (donorLab x₀ x₁ d) x₁)) :
    donorRows.{u}.IsLawful (donorLab x₀ x₁) where
  orderly d := by fin_cases d; exacts [h₀, h₁]
  locality s := by fin_cases s; exacts [l₀, l₁]
  availability s _ _ _ := ⟨s, rfl, le_rfl⟩

/-- A locality of the donor from a witness, checked cell by cell. -/
private theorem donorTransformsTo_of (s : Fin 2) {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {F : Fin 2 → Label.{u}}
    (h : ∀ d : Fin 2, F d = min (σ (donorRowValue s d)) (g 1)) :
    TransformsTo (fun d : donorCells.below (donorCells.gradedIndex s) ↦ donorCells.grade d)
      (donorRows.row s) (fun d ↦ F d) :=
  ⟨g, σ, hw, fun d ↦ h d.1⟩

private theorem raise_two_one : raise (2 : Label.{u}) 1 = 1 := by
  have h : ¬ (2 : Label.{u}) ≤ 1 := by simp
  simp only [raise, ite_eq_right h]

private theorem raise_two_two : raise (2 : Label.{u}) 2 = ⊤ := by
  simp only [raise, ite_eq_left le_rfl]

/-- **The labelling of the donor**, `1, ⊤`, is lawful: the row of `e₂` is raised at `2`. -/
theorem isLawful_donorLab_one_top : donorRows.{u}.IsLawful (donorLab 1 ⊤) := by
  refine isLawful_donorLab_of (by simp) (isSelfVisible_top 1) ?_ ?_
  · refine donorTransformsTo_of 0 (F := fun d ↦ min (donorLab _ _ d) _) IsWitness.id_top
      fun d ↦ ?_
    fin_cases d <;> simp [donorLab, donorRowValue]
  · refine donorTransformsTo_of 1 (F := fun d ↦ min (donorLab _ _ d) _)
      (isWitness_raise (K := 1) (h := (2 : Label.{u})) (by simp) (bot_lt_iff_ne_bot.mpr (by simp)))
      fun d ↦ ?_
    fin_cases d <;> simp [donorLab, donorRowValue, raise_two_one, raise_two_two]

/-- The row of `e₁` read as a labelling, `1, 1`, is lawful. -/
private theorem isLawful_donorLab_one_one : donorRows.{u}.IsLawful (donorLab 1 1) := by
  refine isLawful_donorLab_of (by simp) (by simp) ?_ ?_
  · refine donorTransformsTo_of 0 (F := fun d ↦ min (donorLab _ _ d) _) IsWitness.id_top
      fun d ↦ ?_
    fin_cases d <;> simp [donorLab, donorRowValue]
  · refine donorTransformsTo_of 1 (F := fun d ↦ min (donorLab _ _ d) _)
      (isWitness_topShifter (antitone_constStepSuppressor 1 1)
        (isSelfVisible_constStepSuppressor (by simp))) fun d ↦ ?_
    fin_cases d <;> simp [donorLab, donorRowValue, topShifter, constStepSuppressor]

/-- The row of `e₂` read as a labelling, `1, 2`, is lawful. -/
private theorem isLawful_donorLab_one_two : donorRows.{u}.IsLawful (donorLab 1 2) := by
  refine isLawful_donorLab_of (by simp) (by simp) ?_ ?_
  · refine donorTransformsTo_of 0 (F := fun d ↦ min (donorLab _ _ d) _) IsWitness.id_top
      fun d ↦ ?_
    fin_cases d <;> simp [donorLab, donorRowValue]
  · refine donorTransformsTo_of 1 (F := fun d ↦ min (donorLab _ _ d) _) IsWitness.id_top
      fun d ↦ ?_
    fin_cases d <;> simp [donorLab, donorRowValue]

/-- **The donor's rows forbid `⊥` at `e₁` with a label other than `⊥` at `e₂`**: locality at `e₂`
reads `e₁` and `e₂` at `1` and `2 = vr_2(1, 2)`; a shifter sending `1` to `⊥` sends `2` to
`vr_2(⊥, 2) = ⊥`, since the guard of the commutation law holds at `⊥`. -/
theorem eq_bot_of_isLawful_donor {ρ : Fin 2 → Label.{u}} (hρ : donorRows.IsLawful ρ)
    (h₀ : ρ 0 = ⊥) : ρ 1 = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := hρ.locality 1
  have h0 := heq ⟨0, (le_rfl : donorCells.gradedIndex 0 ≤ donorCells.gradedIndex 1)⟩
  have h1 := heq ⟨1, (le_rfl : donorCells.gradedIndex 1 ≤ donorCells.gradedIndex 1)⟩
  -- The row of `e₂` reads `1` at `e₁` and `2` at `e₂` (`donorRows`, by definition).
  change min (ρ 0) (ρ 1) = min (σ 1) (g 1) at h0
  change min (ρ 1) (ρ 1) = min (σ 2) (g 1) at h1
  rw [h₀, min_eq_left bot_le] at h0
  rw [min_self] at h1
  by_contra hne
  have hg : g 1 ≠ ⊥ := fun hg ↦ hne (by rw [h1, hg, min_eq_right bot_le])
  have hσ1 : σ 1 = ⊥ := (min_eq_bot.mp h0.symm).resolve_right hg
  have hσ2 : σ 2 = ⊥ := by
    have h := hw.visibilityReplace_comm 1 2 (by rw [hσ1]; exact bot_le) 2 le_rfl
    have hvr : visibilityReplace 2 2 (1 : Label.{u}) = 2 := by simp
    rw [hvr, hσ1, visibilityReplace_bot] at h
    exact h
  exact hne (by rw [h1, hσ2, min_eq_left bot_le])

/-- The donor's scheme is well formed. -/
theorem isWellFormed_donorScheme : donorScheme.{u}.IsWellFormed where
  ground_eq := rfl
  isWellFormed := ⟨inferInstance, Geometry.isPlan_intervalPlan univ, fun d ↦ by
    simp only [mem_gradedFaces]
    revert d; decide +kernel⟩

/-- The donor's scheme is coded. -/
theorem isCoded_donorScheme : donorScheme.{u}.IsCoded := fun s t ↦ by
  -- The row values are `1` and `2` (`donorRows`, by definition).
  change donorRowValue s t.1 < _
  have h1 := natCast_label_lt_omega0_sq.{u} 1
  have h2 := natCast_label_lt_omega0_sq.{u} 2
  simp only [Nat.cast_one, Nat.cast_ofNat] at h1 h2
  unfold donorRowValue; split_ifs <;> assumption

/-- The donor's rows are consistent. -/
theorem isConsistent_donorRows : donorRows.{u}.IsConsistent := by
  intro s
  -- Consistency at `s`: the row of `s` is lawful below its graded index (`IsConsistent`).
  change donorRows.IsLawfulBelow _ (fun t ↦ donorRows.row s t)
  rcases (by decide : ∀ s : Fin 2, s = 0 ∨ s = 1) s with rfl | rfl
  · convert isLawful_donorLab_one_one.isLawfulBelow (donorCells.gradedIndex 0) using 1
    funext t
    obtain ⟨t, -⟩ := t
    fin_cases t <;> simp [donorRows, donorRowValue, donorLab]
  · convert isLawful_donorLab_one_two.isLawfulBelow (donorCells.gradedIndex 1) using 1
    funext t
    obtain ⟨t, -⟩ := t
    fin_cases t <;> simp [donorRows, donorRowValue, donorLab]

private theorem univ_of_mem_intervalPlan_one :
    ∀ B ∈ Geometry.intervalPlan (Finset.univ : Finset (Fin 1)), 0 < #B → B = Finset.univ := by
  decide +kernel

/-- The donor's rows are bountiful: its graded faces all lie on the whole point. -/
theorem isBountiful_donorRows : donorRows.{u}.IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY _ ↦ ?_
  refine Rows.cappedLift_of_fst_eq _ ?_
  rw [univ_of_mem_intervalPlan_one X.1 hX.1 (hX.2.1.trans_le hX.2.2),
    univ_of_mem_intervalPlan_one Y.1 hY.1 (hY.2.1.trans_le hY.2.2)]

/-- The donor's cell scheme is complete. -/
theorem isComplete_donorCells : donorCells.IsComplete := by
  intro X hX
  have hX1 := univ_of_mem_intervalPlan_one X.1 hX.1 (hX.2.1.trans_le hX.2.2)
  have hX2 : X.2 = 1 := by
    have := hX.2.2; rw [hX1] at this; simp at this; have := hX.2.1; omega
  exact ⟨0, Prod.ext hX1.symm hX2.symm⟩

/-- **The donor** on one point: the cells `e₁`, `e₂` labelled `1` and `⊤`.  The label `1` of `e₁`
is `vr_2(1, 1)`, anchored at the cell `z₁` of the private type. -/
noncomputable def donor (α : Ordinal.{u}) (hα : 1 < α) : StageType.{u} α 1 where
  toScheme := donorScheme
  label := donorLab 1 ⊤
  isWellFormed := isWellFormed_donorScheme
  isCoded := isCoded_donorScheme
  isLawful := isLawful_donorLab_one_top
  atStage d := by fin_cases d; exacts [(Label.atStage_one.mpr hα), atStage_top]

/-- **The donor is legal.** -/
theorem isLegal_donor (α : Ordinal.{u}) (hα : 1 < α) : (donor α hα).IsLegal :=
  StageType.isLegal_iff.mpr ⟨isConsistent_donorRows, isBountiful_donorRows, isComplete_donorCells⟩


/-! ### The refutation -/

open StageType GatedExtensionExample

private theorem one_ne_top : (1 : Label.{u}) ≠ ⊤ :=
  ne_of_lt (by simpa using (natCast_label_lt_omega.{u} 1).trans_le le_top)

/-- A label other than `⊥` that is self-visible at `2` is not at most `1`. -/
private theorem not_le_one_of_isSelfVisible {c : Label.{u}} (hc : IsSelfVisible 2 c)
    (hc0 : c ≠ ⊥) : ¬ c ≤ 1 := by
  induction c using recBotCoeTop with
  | bot => exact absurd rfl hc0
  | coe o =>
    intro h
    have ho : o ≤ 1 := by
      have h' : ((o : Ordinal.{u}) : Label.{u}) ≤ ((1 : Ordinal.{u}) : Label.{u}) := by
        simpa using h
      exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h')
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp (ho.trans_lt (by simp))
    have hk : k ≤ 1 := by exact_mod_cast ho
    have hsv : IsSelfVisible 2 (k : Label.{u}) := hc
    rw [isSelfVisible_natCast] at hsv
    omega
  | top => exact not_le.mpr (by simpa using (natCast_label_lt_omega.{u} 1).trans_le le_top)

/-- **The bottom transport condition fails** for the private type, the donor, and every cap
label `c ≠ ⊥` self-visible at `2`.  The lawful labelling `⊥, ⊥, ⊥, ω + 1, ω + 2` of the private
type drops the only possible anchor `z₁` of the donor cell `e₁` and keeps every cell labelled `⊤`,
so the condition asks for a lawful labelling of the donor that is `⊥` at `e₁` and not at `e₂`;
the donor's rows forbid it (`eq_bot_of_isLawful_donor`). -/
theorem not_carriesBottoms (α : Ordinal.{u}) (hα : 1 < α) {c : Label.{u}}
    (hc : IsSelfVisible 2 c) (hc0 : c ≠ ⊥) : ¬ CarriesBottoms (P α hα) (donor α hα) c := by
  intro H
  have hc1 := not_le_one_of_isSelfVisible hc hc0
  obtain ⟨ρ, hρ, hj⟩ := H (lab ⊥ (omegaAdd 1) (omegaAdd 2)) isLawful_lab_bot_omegaAdd
    fun i hi _ ↦ by
      have h4 : ∀ i : Fin 5, (cellScope i, cellGrade i) = ((univ : Finset (Fin 2)), 2) →
          i = 4 := by decide
      rw [h4 i hi]; exact omegaAdd_ne_bot 2
  have h0 : ρ (0 : Fin 2) = ⊥ := by
    refine (hj (0 : Fin 2) (Finset.mem_univ _) (by
      change (1 : Label.{u}) ≠ ⊥; simp)).1 hc1
      fun i k _ hik ↦ ?_
    -- The labels of the private type and of the donor are `lab 1 ⊤ ⊤` and `donorLab 1 ⊤`.
    change (1 : Label.{u}) = visibilityReplace 2 k (lab 1 ⊤ ⊤ i) at hik
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change (1 : Label.{u}) = Label.visibilityReplace 2 k ⊤ at hik
      exact absurd hik (by rw [visibilityReplace_top]; exact one_ne_top)
    · change (1 : Label.{u}) = Label.visibilityReplace 2 k ⊤ at hik
      exact absurd hik (by rw [visibilityReplace_top]; exact one_ne_top)
  have h1 : ρ (1 : Fin 2) ≠ ⊥ := by
    refine (hj (1 : Fin 2) (Finset.mem_univ _) (by change (⊤ : Label.{u}) ≠ ⊥; simp)).2
      fun i hi ↦ ?_
    -- The labels of the private type and of the donor are `lab 1 ⊤ ⊤` and `donorLab 1 ⊤`.
    change (∃ k ≤ 2, (⊤ : Label.{u}) = visibilityReplace 2 k (lab 1 ⊤ ⊤ i)) ∨
      (c ≤ lab 1 ⊤ ⊤ i ∧ c ≤ ⊤) at hi
    fin_cases i
    · rcases hi with ⟨k, -, hk⟩ | ⟨hle, -⟩
      · change (⊤ : Label.{u}) = Label.visibilityReplace 2 k ⊥ at hk; simp at hk
      · exact absurd (le_bot_iff.mp hle) hc0
    · rcases hi with ⟨k, -, hk⟩ | ⟨hle, -⟩
      · change (⊤ : Label.{u}) = Label.visibilityReplace 2 k ⊥ at hk; simp at hk
      · exact absurd (le_bot_iff.mp hle) hc0
    · rcases hi with ⟨k, -, hk⟩ | ⟨hle, -⟩
      · change (⊤ : Label.{u}) = Label.visibilityReplace 2 k 1 at hk
        exact absurd (visibilityReplace_eq_top_iff.mp hk.symm) one_ne_top
      · exact absurd hle hc1
    · exact omegaAdd_ne_bot 1
    · exact omegaAdd_ne_bot 2
  exact h1 (eq_bot_of_isLawful_donor hρ h0)

/-- **The private type has no coupled gated extension with the donor**, over the empty face: the
cap of a coupled gated extension is not labelled `⊥` and is self-visible at `2`, so the bottom
transport condition it forces (`StageType.CoupledGatedExtension.carriesBottoms`) fails
(`not_carriesBottoms`). -/
theorem isEmpty_coupledGatedExtension (α : Ordinal.{u}) (hα : 1 < α) (f : Fin 0 ↪ Fin 2) :
    IsEmpty (CoupledGatedExtension (P α hα) f (donor α hα)) := by
  refine ⟨fun E ↦ ?_⟩
  have hgr : E.display.toCellScheme.grade E.cap = 2 := congrArg Prod.snd E.gradedIndex_cap
  have hc : IsSelfVisible 2 (E.display.label E.cap) := by
    have := E.display.isLawful.orderly E.cap
    rwa [hgr] at this
  exact not_carriesBottoms α hα hc E.isGate.cap_ne_bot (E.carriesBottoms rfl)

/-- **The coupled gated pinned extension property fails at every stage above `1`.**  It is
applied to the private type `P α`, the empty root, the donor `donor α` (anchored below the full
cell `4`: its cell labelled `1` has the anchor `z₁`, and its other cell is labelled `⊤`), and the
cap `4`; no coupled gated extension exists (`isEmpty_coupledGatedExtension`). -/
theorem not_hasCoupledGatedPinnedExtensions (α : Ordinal.{u}) (hα : 1 < α) :
    ¬ HasCoupledGatedPinnedExtensions.{u} α := by
  intro h
  have hf : univ.map emptyRoot ∈ (P α hα).toCellScheme.faces := by
    -- The faces of `P α` are the interval plan of `univ` (`cells`, by definition).
    change _ ∈ Geometry.intervalPlan univ; decide +kernel
  have hfd : univ.map (Fin.castSuccEmb : Fin 0 ↪ Fin 1) ∈ (donor α hα).toCellScheme.faces := by
    -- The faces of the donor are the interval plan of `univ` (`donorCells`, by definition).
    change _ ∈ Geometry.intervalPlan univ; decide +kernel
  have hdp : restrictFace Fin.castSuccEmb (donor α hα) = some ((P α hα).comap emptyRoot hf) := by
    rw [restrictFace_of_mem _ _ hfd]; exact congrArg some (StageType.eq_of_zero _ _)
  have hanc : (P α hα).IsAnchored (4 : Fin 5) (donor α hα) := by
    intro j _ _ hlt
    fin_cases j
    · -- The cell `e₁` is labelled `1 = vr_2(1, 1)`, the label of `z₁` (`P`, `donor`).
      refine ⟨(2 : Fin 5), 1, by omega, ?_⟩
      change (1 : Label.{u}) = Label.visibilityReplace 2 1 (1 : Label.{u})
      simp
    · -- The cell `e₂` is labelled `⊤`, not below the label `⊤` of the cap.
      exact absurd hlt (by change ¬ (⊤ : Label.{u}) < ⊤; exact lt_irrefl _)
  obtain ⟨E, -⟩ := h (P α hα) emptyRoot ((P α hα).comap emptyRoot hf) (donor α hα) (4 : Fin 5)
    (isLegal_P α hα) (restrictFace_of_mem _ _ hf) (isLegal_donor α hα) hdp rfl
    (by change (⊤ : Label.{u}) ≠ ⊥; simp) (by omega) hanc
  exact (isEmpty_coupledGatedExtension α hα emptyRoot).false E

/-! ### The refuting input meets the finite conditions of an acquired private context -/

/-- **The finite conditions of an acquired private context do not give the bottom transport
condition.**  The refuting input satisfies, with private arity `2` over the empty root, the finite
stage-type and label conditions of the output of `Realization.IsModel.exists_privateContext` and
of its anchored form (`y.type := P α`, at every floor `γ < α`, with `N₀ ≤ 2`): a legal private
type with the root as a literal face, a legal donor with the same root face, arity above `0 + 1`,
a cell `C = 4` of graded index `(univ, 2)` labelled above every `γ < α`, for every ordinal donor
label a reference cell (`z₁`, labelled `1 = vr_2(1, 1)`, not self-visible at `2`, below the label
of `C`), and anchoring below `C`; and the bottom transport condition fails there
(`not_carriesBottoms`).  This is a statement about stage types at one input: no occurrence of it
in an actual model is exhibited.  The row of `C` reads `z₁` at `1` and `C` itself at `ω + 2`, a
block higher (`CellScheme.Rows.IsLawful.lt_row_self_of_eq_bot`).  The existing acquisition proof
(uniformity, high-arity dominance, exact consistency) does not establish control of this row
jointly with the label of `C` above the floor; whether models acquire a private context
satisfying the condition from the full model axioms is undecided. -/
theorem exists_privateContext_not_carriesBottoms (α : Ordinal.{u}) (hα : 1 < α) :
    ∃ (P : StageType.{u} α 2) (f : Fin 0 ↪ Fin 2) (p : StageType.{u} α 0)
      (d : StageType.{u} α (0 + 1)) (C : Fin P.card),
      P.IsLegal ∧ restrictFace f P = some p ∧ d.IsLegal ∧
        restrictFace Fin.castSuccEmb d = some p ∧ 0 + 1 < 2 ∧
        P.toCellScheme.gradedIndex C = (Finset.univ, 2) ∧
        (∀ γ : Ordinal.{u}, γ < α → (γ : Label.{u}) < P.label C) ∧
        (∀ (j : Fin d.card) (o : Ordinal.{u}), d.label j = o →
          ∃ z, ∃ i < 2, d.label j = visibilityReplace 2 i (P.label z) ∧
            ¬ IsSelfVisible 2 (P.label z) ∧ P.label z < P.label C) ∧
        IsAnchored P C d ∧ ¬ CarriesBottoms P d (P.label C) := by
  have hf : univ.map emptyRoot ∈ (P α hα).toCellScheme.faces := by
    -- The faces of `P α` are the interval plan of `univ` (`cells`, by definition).
    change _ ∈ Geometry.intervalPlan univ; decide +kernel
  have hfd : univ.map (Fin.castSuccEmb : Fin 0 ↪ Fin 1) ∈ (donor α hα).toCellScheme.faces := by
    -- The faces of the donor are the interval plan of `univ` (`donorCells`, by definition).
    change _ ∈ Geometry.intervalPlan univ; decide +kernel
  have hdp : restrictFace Fin.castSuccEmb (donor α hα) = some ((P α hα).comap emptyRoot hf) := by
    rw [restrictFace_of_mem _ _ hfd]; exact congrArg some (StageType.eq_of_zero _ _)
  have h1 : (1 : Label.{u}) = Label.visibilityReplace 2 1 (1 : Label.{u}) := by simp
  refine ⟨P α hα, emptyRoot, (P α hα).comap emptyRoot hf, donor α hα, (4 : Fin 5),
    isLegal_P α hα, restrictFace_of_mem _ _ hf, isLegal_donor α hα, hdp, by omega, rfl,
    fun γ _ ↦ ?_, fun j o hj ↦ ?_, fun j _ _ hlt ↦ ?_, not_carriesBottoms α hα ?_ ?_⟩
  · -- The cell `4` is labelled `⊤`.
    change (γ : Label.{u}) < ⊤
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top γ)
  · fin_cases j
    · -- The cell `e₁` is labelled `1 = vr_2(1, 1)`, the label of `z₁` (`P`, `donor`).
      refine ⟨(2 : Fin 5), 1, by omega, h1, ?_, ?_⟩
      · -- The label of `z₁` is `1` (`P`).
        change ¬ IsSelfVisible 2 (1 : Label.{u})
        rw [← Nat.cast_one, isSelfVisible_natCast]; omega
      · -- The labels of `z₁` and of the cap are `1` and `⊤` (`P`).
        change (1 : Label.{u}) < ⊤
        exact lt_of_le_of_ne le_top one_ne_top
    · -- The cell `e₂` is labelled `⊤`, not an ordinal.
      exact absurd hj (by
        change (⊤ : Label.{u}) ≠ _
        exact fun h ↦ WithTop.top_ne_coe (WithBot.coe_injective h))
  · fin_cases j
    · exact ⟨(2 : Fin 5), 1, by omega, h1⟩
    · -- The cell `e₂` is labelled `⊤`, not below the label `⊤` of the cap.
      exact absurd hlt (by change ¬ (⊤ : Label.{u}) < ⊤; exact lt_irrefl _)
  · -- The cap is labelled `⊤` (`P`).
    change IsSelfVisible 2 (⊤ : Label.{u})
    exact isSelfVisible_top 2
  · -- The cap is labelled `⊤` (`P`).
    change (⊤ : Label.{u}) ≠ ⊥
    simp

end VaughtConjecture.CoupledGatedExtensionCounterexample
