/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Continuation.SourceGapDetermination
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Label.StepWitness

/-!
# A separated pinned extension of a source-gap context, and determination over it

Roadmap, Layer 3 ((R2) of the table of 3.4); the separated pinned extensions of
`VaughtConjecture.Continuation.SourceGapDetermination`.

**The display** (`SeparatedInstance.D α`, `SeparatedInstance.isLegal_D`).  On two points with the
interval plan, five cells:

| cell | scope    | grade | row on the cells `0`–`3`    | label |
|------|----------|-------|-----------------------------|-------|
| 0    | `{0}`    | 1     | `(1, ω + 2, 1, ω + 2)`      | `⊤`   |
| 1    | `{0}`    | 1     | the same                    | `⊤`   |
| 2    | `{1}`    | 1     | the same                    | `⊤`   |
| 3    | `univ`   | 1     | the same                    | `⊤`   |
| 4    | `univ`   | 2     | `⊥`                         | `⊥`   |

(each row is read at the cells below its cell).  Every row reads the cells `0` and `2` at `1` and
the cells `1` and `3` at `ω + 2`; the cell `4` is dead.  The labellings `(a, b, a, b, ⊥)` with
`a ≤ b` self-visible at `1` are lawful (`SeparatedInstance.isLawful_lab`), through the shifter
sending the labels below `ω` other than `⊥` to `a` and those at least `ω` to `b`
(`SeparatedInstance.isWitness_twoLevel`); conversely, in a labelling lawful below `(univ, 1)`,
availability puts every cell below the cell `3`, which reads `0` and `2` alike and `1` and `3`
alike, so `0` and `2` agree and `1` and `3` agree.  The
rows are these labellings; bountifulness reduces to the lifts from `({0}, 1)` and `({1}, 1)` to
`(univ, 1)`, which copy the prescription along the pairs `(0, 2)` and `(1, 3)`.

**The context and the donor.**  The face of the display on `{0}` (`SeparatedInstance.context α`,
cells `0` and `1`, both `⊤`) is a source-gap context of grade `1` along the empty root, with lost
point `0`, owner `1` and lost top `0`: the gap at the owner is `visibilityReplace 1 1 1 = 1 <
ω + 2`, and no top cell avoids the lost point.  The face on `{1}` (`SeparatedInstance.donor α`,
the cell `2`, `⊤`) is a legal one-point coface of the empty type with a new top.

**Separation and determination** (`SeparatedInstance.separatesThrough_D`,
`SeparatedInstance.isDeterminedWithin_donor`, compiled in this repository).  The display is a
legal one-point coface of the context with face the donor along the empty root followed by the new
point, and its only cell of graded index `(univ, 1)`, the cell `3`, reads the new top `2` as it
reads the lost top `0`.  So the conclusion of the separated pinned extension property
(`StageType.HasSeparatedPinnedExtensions`) holds at this context and this donor, and the donor is
determined over the context at every cutoff: every member of the receiving family of the display
with face the context has face the donor, the new top included.  This is one input, with the
empty root and grade `1`; the property itself is open.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.SeparatedInstance

open Finset Label CellScheme StageType
open scoped Ordinal

/-! ### A shifter with two values -/

/-- The label `ω + 2`. -/
noncomputable abbrev omegaAddTwo : Label.{u} :=
  ((ω + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

private theorem one_lt_coe_omega0 : (1 : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
  simp

private theorem not_omegaAddTwo_lt : ¬ omegaAddTwo.{u} < ((ω : Ordinal.{u}) : Label.{u}) :=
  fun h ↦ (not_lt.mpr le_self_add) (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h))

private theorem one_lt_omegaAddTwo : (1 : Label.{u}) < omegaAddTwo.{u} :=
  one_lt_coe_omega0.trans_le (not_lt.mp not_omegaAddTwo_lt)

private theorem isSelfVisible_omegaAddTwo : IsSelfVisible 1 omegaAddTwo.{u} :=
  isSelfVisible_coe_add Ordinal.isSuccLimit_omega0.isSuccPrelimit (by omega)

private theorem isSelfVisible_one' : IsSelfVisible 1 (1 : Label.{u}) := isSelfVisible_one.mpr le_rfl

/-- The shifter sending `⊥` to `⊥`, every other label below `ω` to `a`, and every label at least
`ω` to `b`. -/
noncomputable def twoLevel (a b x : Label.{u}) : Label.{u} :=
  if x < ((ω : Ordinal.{u}) : Label.{u}) then (if x = ⊥ then ⊥ else a) else b

/-- The shifter is invariant under visibility replacement. -/
private theorem twoLevel_visibilityReplace (a b x : Label.{u}) (k i : ℕ) :
    twoLevel a b (visibilityReplace k i x) = twoLevel a b x := by
  simp only [twoLevel, Label.visibilityReplace_lt_iff Ordinal.isSuccLimit_omega0.isSuccPrelimit,
    visibilityReplace_eq_bot_iff]

/-- **The two-valued shifter is a witness** with the step suppressor at `1`, for `a ≤ b`
self-visible at `1`. -/
theorem isWitness_twoLevel {a b : Label.{u}} (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hab : a ≤ b) : IsWitness (stepSuppressor 1) (twoLevel a b) where
  antitone := (IsWitness.id_step 1).antitone
  isSelfVisible := (IsWitness.id_step 1).isSelfVisible
  map_bot := by simp [twoLevel, WithBot.bot_lt_coe]
  monotone := by
    intro x y hxy
    simp only [twoLevel]
    by_cases hy : y < ((ω : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left (hxy.trans_lt hy), ite_eq_left hy]
      by_cases hx0 : x = ⊥
      · rw [ite_eq_left hx0]
        exact bot_le
      · rw [ite_eq_right hx0,
          ite_eq_right (show ¬ y = ⊥ from fun h ↦ hx0 (le_bot_iff.mp (h ▸ hxy)))]
    · rw [ite_eq_right hy]
      split_ifs <;> first | exact bot_le | exact hab | exact le_rfl
  visibilityReplace_comm x k hx i hi := by
    rw [twoLevel_visibilityReplace]
    have hsv : IsSelfVisible 1 (twoLevel a b x) := by
      simp only [twoLevel]
      split_ifs
      exacts [isSelfVisible_bot _, ha, hb]
    by_cases hk : k ≤ 1
    · exact ((hsv.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]

/-- Rows of grade `1` with values `⊥`, `1`, `ω + 2` transform to sections with values `⊥`, `a`,
`b` at the same cells. -/
theorem transformsTo_twoLevel {E : Type*} {grade : E → ℕ} (hg : ∀ d, grade d = 1)
    {r t : E → Label.{u}} {a b : Label.{u}} (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hab : a ≤ b)
    (h : ∀ d, (r d = ⊥ ∧ t d = ⊥) ∨ (r d = 1 ∧ t d = a) ∨ (r d = omegaAddTwo ∧ t d = b)) :
    TransformsTo grade r t :=
  ⟨_, _, isWitness_twoLevel ha hb hab, fun d ↦ by
    rw [hg d, stepSuppressor_of_le le_rfl, min_top_right]
    rcases h d with ⟨hr, ht⟩ | ⟨hr, ht⟩ | ⟨hr, ht⟩ <;> rw [hr, ht, twoLevel]
    · simp [WithBot.bot_lt_coe]
    · rw [ite_eq_left one_lt_coe_omega0, ite_eq_right (by simp)]
    · rw [ite_eq_right not_omegaAddTwo_lt]⟩

/-! ### The display -/

/-- The cells on `Fin 2`, with faces the intervals: `0`, `1` of scope `{0}`, `2` of scope `{1}`,
`3` of scope `univ`, all of grade `1`, and `4` of scope `univ` and grade `2`. -/
def cells : CellScheme (Fin 5) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, {0}, {1}, univ, univ], ![1, 1, 1, 1, 2]⟩

/-- The value read at a cell: `1` at `0` and `2`, `ω + 2` at `1` and `3`, `⊥` at `4`. -/
noncomputable def val : Fin 5 → Label.{u} := ![1, omegaAddTwo, 1, omegaAddTwo, ⊥]

/-- The rows: the dead cell `4` reads `⊥`; every other cell reads `val`. -/
noncomputable def rowValue (s t : Fin 5) : Label.{u} := if s = 4 then ⊥ else val t

/-- The scheme of the display. -/
noncomputable abbrev S : Scheme.{u} 2 := ⟨5, cells, ⟨fun s d ↦ rowValue s d.1⟩⟩

/-- The labelling `(a, b, a, b, ⊥)`. -/
noncomputable def lab (a b : Label.{u}) : Fin 5 → Label.{u} := ![a, b, a, b, ⊥]

/-- Every cell other than `4` has grade `1`. -/
private theorem grade_eq_one : ∀ d : Fin 5, d ≠ 4 → cells.grade d = 1 := by decide

/-- The cells below a cell other than `4` are among `0`–`3`. -/
private theorem ne_four_of_le : ∀ s d : Fin 5, s ≠ 4 → cells.gradedIndex d ≤ cells.gradedIndex s →
    d ≠ 4 := by decide

/-- **Lawful sections**: `(a, b, a, b, ⊥)` is lawful for `a ≤ b` self-visible at `1`. -/
theorem isLawful_lab {a b : Label.{u}} (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hab : a ≤ b) : S.{u}.rows.IsLawful (lab a b) where
  orderly d := by
    fin_cases d
    exacts [ha, hb, ha, hb, isSelfVisible_bot _]
  locality s := by
    by_cases hs : s = 4
    · subst hs
      convert TransformsTo.bot _ _ using 1
      funext d
      -- the transformed section at the dead cell `4`
      change min _ (lab a b 4) = ⊥
      simp [lab]
    · -- the label at `s`, `a` or `b`, caps the section below `s`
      have hcap : ∀ d : Fin 5, d ≠ 4 → cells.gradedIndex d ≤ cells.gradedIndex s →
          min (lab a b d) (lab a b s) = if val.{u} d = 1 then min a (lab a b s)
            else min b (lab a b s) := by
        intro d hd _
        fin_cases d <;> simp_all [lab, val, (one_lt_omegaAddTwo.{u}).ne']
      have hls : lab a b s = a ∨ lab a b s = b := by
        fin_cases s <;> simp_all [lab]
      rcases hls with hla | hlb
      · refine transformsTo_twoLevel (a := a) (b := a)
          (fun d : cells.below (cells.gradedIndex s) ↦ grade_eq_one d.1
            (ne_four_of_le s d.1 hs d.2)) ha ha le_rfl fun ⟨d, hd⟩ ↦ ?_
        have hd4 := ne_four_of_le s d hs hd
        have h := hcap d hd4 hd
        rw [hla, min_self, min_eq_right hab] at h
        right
        -- the row of `s` at `d` is `val d`
        change (rowValue s d = 1 ∧ _) ∨ (rowValue s d = omegaAddTwo ∧ _)
        simp only [rowValue, hs, ite_false]
        fin_cases d <;> simp_all [val]
      · refine transformsTo_twoLevel (a := a) (b := b)
          (fun d : cells.below (cells.gradedIndex s) ↦ grade_eq_one d.1
            (ne_four_of_le s d.1 hs d.2)) ha hb hab fun ⟨d, hd⟩ ↦ ?_
        have hd4 := ne_four_of_le s d hs hd
        have h := hcap d hd4 hd
        rw [hlb, min_eq_left hab, min_self] at h
        right
        -- the row of `s` at `d` is `val d`
        change (rowValue s d = 1 ∧ _) ∨ (rowValue s d = omegaAddTwo ∧ _)
        simp only [rowValue, hs, ite_false]
        fin_cases d <;> simp_all [val]
  availability s t hst hg := by
    have key : ∀ s t : Fin 5, cells.scope s ⊆ cells.scope t → cells.grade s = cells.grade t →
        ∃ u : Fin 5, cells.gradedIndex u = cells.gradedIndex t ∧
          (u = s ∨ (s ≠ 4 ∧ (u = 1 ∨ u = 3))) := by decide
    obtain ⟨u, hu, hu'⟩ := key s t hst hg
    refine ⟨u, hu, ?_⟩
    rcases hu' with rfl | ⟨h4, rfl | rfl⟩
    · exact le_rfl
    · fin_cases s <;> simp_all [lab]
    · fin_cases s <;> simp_all [lab]


/-- A lawful section gives lawful labellings below every pair. -/
private theorem isLawfulBelow_of_isLawful {w : Fin 5 → Label.{u}} (h : S.{u}.rows.IsLawful w)
    (X : Finset (Fin 2) × ℕ) : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d) :=
  CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun d _ ↦ h.orderly d, fun s _ ↦ h.locality s, fun s t _ hst hg ↦ h.availability s t hst hg⟩

/-- **Lawful sections below `({0}, 1)`**, necessary conditions: self-visible at `1` at `0` and `1`,
and `0` at most `1` (the cell `0` reads `0` at `1` and `1` at `ω + 2`). -/
private theorem conditions_zero {w : Fin 5 → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow (({0} : Finset (Fin 2)), 1) (fun d ↦ w d)) :
    IsSelfVisible 1 (w 0) ∧ IsSelfVisible 1 (w 1) ∧ w 0 ≤ w 1 := by
  obtain ⟨ho, hl, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  have m : ∀ i : Fin 5, i = 0 ∨ i = 1 → cells.gradedIndex i ≤ (({0} : Finset (Fin 2)), 1) := by
    decide
  refine ⟨ho 0 (m 0 (.inl rfl)), ho 1 (m 1 (.inr rfl)), ?_⟩
  have := (hl 0 (m 0 (.inl rfl))).le_of_le
    (d := ⟨0, show cells.gradedIndex 0 ≤ cells.gradedIndex 0 from le_rfl⟩)
    (d' := ⟨1, show cells.gradedIndex 1 ≤ cells.gradedIndex 0 by decide⟩)
    (by
      -- the row of `0` reads `0` at `1` and `1` at `ω + 2`
      change rowValue 0 0 ≤ rowValue 0 1
      simp only [rowValue, val]
      exact one_lt_omegaAddTwo.le) le_rfl
  simpa using this

/-- **Lawful sections below `(univ, 1)`**, necessary conditions: self-visible at `1` at `0`–`3`,
`0` and `2` equal, `1` and `3` equal, and `0` at most `1`.  Availability puts each of `0`–`3`
below the cell `3`, the only cell of graded index `(univ, 1)`, which reads `0`, `2` alike and `1`,
`3` alike. -/
private theorem conditions_univ {w : Fin 5 → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ w d)) :
    IsSelfVisible 1 (w 0) ∧ IsSelfVisible 1 (w 1) ∧ w 0 = w 2 ∧ w 1 = w 3 ∧ w 0 ≤ w 1 := by
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  have m : ∀ i : Fin 5, i ≠ 4 → cells.gradedIndex i ≤ ((univ : Finset (Fin 2)), 1) := by decide
  have only3 : ∀ u : Fin 5, cells.gradedIndex u = cells.gradedIndex 3 → u = 3 := by decide
  have below3 : ∀ i : Fin 5, i ≠ 4 → cells.gradedIndex i ≤ cells.gradedIndex 3 := by decide
  -- availability: every cell `i ≠ 4` lies below the cell `3`
  have hav (i : Fin 5) (hi : i ≠ 4) : w i ≤ w 3 := by
    obtain ⟨u, hu, hle⟩ := ha i 3 (m 3 (by decide)) ((below3 i hi).1) (by
      revert i; decide)
    rwa [only3 u hu] at hle
  -- locality at `3`: equal row values give equal capped labels
  have hloc (i j : Fin 5) (hi : i ≠ 4) (hj : j ≠ 4) (hv : val.{u} i = val.{u} j) :
      min (w i) (w 3) = min (w j) (w 3) := by
    have h1 := (hl 3 (m 3 (by decide))).le_of_le (d := ⟨i, below3 i hi⟩) (d' := ⟨j, below3 j hj⟩)
      (by
        -- the row of `3` is `val`
        change rowValue 3 i ≤ rowValue 3 j
        simp only [rowValue, show (3 : Fin 5) ≠ 4 by decide, ite_false, hv, le_refl])
      (by rw [grade_eq_one j hj, grade_eq_one i hi])
    have h2 := (hl 3 (m 3 (by decide))).le_of_le (d := ⟨j, below3 j hj⟩) (d' := ⟨i, below3 i hi⟩)
      (by
        -- the row of `3` is `val`
        change rowValue 3 j ≤ rowValue 3 i
        simp only [rowValue, show (3 : Fin 5) ≠ 4 by decide, ite_false, hv, le_refl])
      (by rw [grade_eq_one j hj, grade_eq_one i hi])
    exact le_antisymm h1 h2
  have h02 := hloc 0 2 (by decide) (by decide) rfl
  have h13 := hloc 1 3 (by decide) (by decide) rfl
  rw [min_eq_left (hav 0 (by decide)), min_eq_left (hav 2 (by decide))] at h02
  rw [min_eq_left (hav 1 (by decide)), min_self] at h13
  exact ⟨ho 0 (m 0 (by decide)), ho 1 (m 1 (by decide)), h02, h13,
    h13 ▸ hav 0 (by decide)⟩

/-- A section below `X`, extended by `⊥`, is lawful below `X`. -/
private theorem isLawfulBelow_extendBot {X : Finset (Fin 2) × ℕ} {q : cells.below X → Label.{u}}
    (hq : S.{u}.rows.IsLawfulBelow X q) :
    S.{u}.rows.IsLawfulBelow X (fun d ↦ CellScheme.Rows.extendBot X q d) := by
  convert hq using 1
  funext d
  exact CellScheme.Rows.extendBot_of_mem q d.2

/-- **The capped lift from `({0}, 1)` to `(univ, 1)`**: the prescription `(a, b)` at `0`, `1`
lifts to `(a, b, a, b, ⊥)`. -/
private theorem cappedLift_zero
    (h : (({0} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨-, -, hq02, hq13, -⟩ := conditions_univ (isLawfulBelow_extendBot hq)
  obtain ⟨hv0, hv1, h01⟩ := conditions_zero (isLawfulBelow_extendBot hp)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q
  set wp := CellScheme.Rows.extendBot (({0} : Finset (Fin 2)), 1) p
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have hpw : ∀ d, p d = wp d := fun d ↦ (CellScheme.Rows.extendBot_of_mem p d.2).symm
  have m0 : cells.gradedIndex 0 ≤ (({0} : Finset (Fin 2)), 1) := by decide
  have m1 : cells.gradedIndex 1 ≤ (({0} : Finset (Fin 2)), 1) := by decide
  have hc0 : min (wq 0) c = min (wp 0) c := by
    have := hpq ⟨0, m0⟩; rwa [hqw, hpw] at this
  have hc1 : min (wq 1) c = min (wp 1) c := by
    have := hpq ⟨1, m1⟩; rwa [hqw, hpw] at this
  refine ⟨fun d ↦ lab (wp 0) (wp 1) d, isLawfulBelow_of_isLawful (isLawful_lab hv0 hv1 h01) _,
    fun ⟨d, hd⟩ ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [hqw]
    have hd' : cells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · exact hc0.symm
    · exact hc1.symm
    · -- the lift at `2` is the prescription at `0`
      change min (wp 0) c = min (wq 2) c
      rw [← hq02, hc0]
    · -- the lift at `3` is the prescription at `1`
      change min (wp 1) c = min (wq 3) c
      rw [← hq13, hc1]
    · exact absurd hd' (by decide)
  · have hd' : cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 5, cells.gradedIndex d ≤ (({0} : Finset (Fin 2)), 1) → d = 0 ∨ d = 1 := by
      decide
    rw [hpw]
    rcases key d hd' with rfl | rfl <;> rfl

/-- **The capped lift from `({1}, 1)` to `(univ, 1)`**: the prescription `x` at `2` lifts to
`(x, max b x, x, max b x, ⊥)`, for `b` the ambient label at `1`. -/
private theorem cappedLift_one
    (h : (({1} : Finset (Fin 2)), 1) ≤ ((univ : Finset (Fin 2)), 1)) :
    S.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨-, hv1, hq02, hq13, hq01⟩ := conditions_univ (isLawfulBelow_extendBot hq)
  set wq := CellScheme.Rows.extendBot ((univ : Finset (Fin 2)), 1) q
  set wp := CellScheme.Rows.extendBot (({1} : Finset (Fin 2)), 1) p
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  have hpw : ∀ d, p d = wp d := fun d ↦ (CellScheme.Rows.extendBot_of_mem p d.2).symm
  have m2 : cells.gradedIndex 2 ≤ (({1} : Finset (Fin 2)), 1) := by decide
  have hv2 : IsSelfVisible 1 (wp 2) := by
    rw [← hpw ⟨2, m2⟩]; exact hp.orderly ⟨2, m2⟩
  have hc2 : min (wq 2) c = min (wp 2) c := by
    have := hpq ⟨2, m2⟩; rwa [hqw, hpw] at this
  -- the ambient label at `1`, raised to the prescription
  have hmax : min (max (wq 1) (wp 2)) c = min (wq 1) c := by
    rw [min_max_distrib_right, ← hc2, ← hq02, max_eq_left (min_le_min_right c hq01)]
  refine ⟨fun d ↦ lab (wp 2) (max (wq 1) (wp 2)) d,
    isLawfulBelow_of_isLawful (isLawful_lab hv2 (hv1.max hv2) (le_max_right _ _)) _,
    fun ⟨d, hd⟩ ↦ ?_, fun ⟨d, hd⟩ ↦ ?_⟩
  · rw [hqw]
    have hd' : cells.gradedIndex d ≤ ((univ : Finset (Fin 2)), 1) := hd
    fin_cases d
    · -- the lift at `0` is the prescription at `2`
      change min (wp 2) c = min (wq 0) c
      rw [hq02, hc2]
    · exact hmax
    · exact hc2.symm
    · -- the lift at `3` is the raised label at `1`
      change min (max (wq 1) (wp 2)) c = min (wq 3) c
      rw [← hq13, hmax]
    · exact absurd hd' (by decide)
  · have hd' : cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) := hd
    have key : ∀ d : Fin 5, cells.gradedIndex d ≤ (({1} : Finset (Fin 2)), 1) → d = 2 := by
      decide
    obtain rfl := key d hd'
    rw [hpw]
    rfl

/-- **The scheme of the display is legal.** -/
theorem isLegal_S : S.{u}.IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 5, cells.scope d ∈ cells.faces ∧ 0 < cells.grade d ∧
        cells.grade d ≤ #(cells.scope d) := by decide
    exact key d⟩⟩
  isCoded s t := by
    have key : ∀ s d : Fin 5, rowValue.{u} s d = ⊥ ∨ rowValue.{u} s d = 1 ∨
        rowValue.{u} s d = omegaAddTwo := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [rowValue, val]
    -- the rows of `S` are `rowValue`
    change rowValue s t.1 < _
    rcases key s t.1 with h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    · exact lt_omega0_sq_iff.mpr (.inr ⟨0, 1, by simp⟩)
    · exact lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [omegaAddTwo]⟩)
  isConsistent s := by
    by_cases hs : s = 4
    · subst hs
      have hrow : S.{u}.rows.row 4 = fun _ ↦ ⊥ := by
        funext d
        -- the row of the dead cell is `⊥`
        change rowValue 4 d.1 = ⊥
        simp [rowValue]
      -- consistency at `4` is lawfulness of its row below its graded index
      change S.{u}.rows.IsLawfulBelow (cells.gradedIndex 4) (S.{u}.rows.row 4)
      rw [hrow]
      exact CellScheme.Rows.isLawfulBelow_const_bot _
    · have hrow : S.{u}.rows.row s = fun d ↦ lab 1 omegaAddTwo d.1 := by
        funext ⟨d, hd⟩
        have hd4 := ne_four_of_le s d hs hd
        -- the row of `s` at `d` is `val d`
        change rowValue s d = _
        simp only [rowValue, hs, ite_false]
        fin_cases d <;> simp_all [val, lab]
      -- consistency at `s` is lawfulness of its row below its graded index
      change S.{u}.rows.IsLawfulBelow (cells.gradedIndex s) (S.{u}.rows.row s)
      rw [hrow]
      exact isLawfulBelow_of_isLawful
        (isLawful_lab isSelfVisible_one' isSelfVisible_omegaAddTwo one_lt_omegaAddTwo.le) _
  isBountiful := by
    refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
    obtain ⟨B, j⟩ := X
    obtain ⟨C, k⟩ := Y
    obtain ⟨-, hj0, hjB⟩ := hX
    obtain ⟨hBC, -⟩ := h
    have key : ∀ B C : Finset (Fin 2), B ⊆ C → B ≠ ∅ →
        B = C ∨ (B = {0} ∧ C = Finset.univ) ∨ (B = {1} ∧ C = Finset.univ) := by decide
    have hB : B ≠ ∅ := by
      rintro rfl
      simp at hjB
      omega
    rcases key B C hBC hB with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact CellScheme.Rows.cappedLift_of_fst_eq _ rfl
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_zero _
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact cappedLift_one _
  isComplete X hX := by
    obtain ⟨B, j⟩ := X
    obtain ⟨-, hj0, hjB⟩ := hX
    have hj2 : j ≤ 2 := hjB.trans (by simpa using card_le_univ B)
    have key : ∀ B : Finset (Fin 2), ∀ j : Fin 3, 0 < (j : ℕ) → (j : ℕ) ≤ #B →
        ∃ d : Fin 5, cells.gradedIndex d = (B, (j : ℕ)) := by decide
    exact key B ⟨j, by omega⟩ hj0 hjB


/-! ### The display as a stage type, its faces, and determination -/

/-- **The display**: the scheme `S` labelled `⊤` at the cells `0`–`3` and `⊥` at the dead cell. -/
noncomputable def D (α : Ordinal.{u}) : StageType.{u} α 2 where
  toScheme := S
  label := lab ⊤ ⊤
  isWellFormed := isLegal_S.isWellFormed
  isCoded := isLegal_S.isCoded
  isLawful := isLawful_lab (isSelfVisible_top 1) (isSelfVisible_top 1) le_rfl
  atStage d := by fin_cases d <;> simp [lab]

/-- The cells of the display, by their index. -/
abbrev cellD (α : Ordinal.{u}) (i : Fin 5) : Fin (D α).card := i

/-- **The display is legal.** -/
theorem isLegal_D (α : Ordinal.{u}) : (D α).IsLegal := isLegal_S

/-- The empty root on one point. -/
def emptyRoot : Fin 0 ↪ Fin 1 := ⟨Fin.elim0, fun a ↦ a.elim0⟩

/-- The face `{0}` is a face of the display. -/
theorem mem_faces_castSuccEmb (α : Ordinal.{u}) :
    univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (D α).toCellScheme.faces := by
  -- the faces of the display are the interval plan
  change _ ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The empty root followed by the new point spans `{1}`. -/
theorem univ_map_extendByLast : univ.map (extendByLast emptyRoot) = ({1} : Finset (Fin 2)) := by
  ext x
  simp only [mem_map, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    obtain rfl : i = Fin.last 0 := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [extendByLast_last]
    rfl
  · rintro rfl
    exact ⟨Fin.last 0, by rw [extendByLast_last]; rfl⟩

/-- The face `{1}`, the empty root followed by the new point, is a face of the display. -/
theorem mem_faces_extendByLast (α : Ordinal.{u}) :
    univ.map (extendByLast emptyRoot) ∈ (D α).toCellScheme.faces := by
  rw [univ_map_extendByLast]
  -- the faces of the display are the interval plan
  change _ ∈ Geometry.intervalPlan univ
  decide +kernel

/-- **The context**: the face `{0}` of the display, the cells `0` and `1`, both `⊤`. -/
noncomputable def context (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (D α).comap Fin.castSuccEmb (mem_faces_castSuccEmb α)

/-- **The donor**: the face `{1}` of the display, the cell `2`, `⊤`. -/
noncomputable def donor (α : Ordinal.{u}) : StageType.{u} α 1 :=
  (D α).comap (extendByLast emptyRoot) (mem_faces_extendByLast α)

theorem restrictFace_context (α : Ordinal.{u}) :
    restrictFace Fin.castSuccEmb (D α) = some (context α) := restrictFace_of_mem _ _ _

theorem restrictFace_donor (α : Ordinal.{u}) :
    restrictFace (extendByLast emptyRoot) (D α) = some (donor α) := restrictFace_of_mem _ _ _

/-- The empty root is a face of the context. -/
theorem mem_faces_emptyRoot (α : Ordinal.{u}) :
    univ.map emptyRoot ∈ (context α).toCellScheme.faces := by
  rw [show (context α).toCellScheme = ((D α).toScheme.comap Fin.castSuccEmb).toCellScheme from rfl,
    Scheme.mem_comap_faces]
  -- the faces of the display are the interval plan
  change _ ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The type of the empty root. -/
noncomputable def root (α : Ordinal.{u}) : StageType.{u} α 0 :=
  (context α).comap emptyRoot (mem_faces_emptyRoot α)

theorem restrictFace_root (α : Ordinal.{u}) :
    restrictFace emptyRoot (context α) = some (root α) := restrictFace_of_mem _ _ _

/-- **The donor is a legal one-point coface of the type of the empty root.** -/
theorem donor_mem_cofaces (α : Ordinal.{u}) : donor α ∈ (root α).cofaces := by
  refine ⟨(isLegal_D α).comap _ _, ?_⟩
  rw [restrictFace_trans _ _ _ (restrictFace_donor α), castSuccEmb_trans_extendByLast,
    ← restrictFace_trans _ _ _ (restrictFace_context α), restrictFace_root]

/-- The donor has top grade at most `1`. -/
theorem topGrade_donor_le (α : Ordinal.{u}) : (donor α).topGrade ≤ 1 :=
  topGrade_le_iff.mpr fun d _ ↦ (donor α).grade_le d

/-- The cells `0` and `1` of the display are cells of the context. -/
private theorem exists_context_cell (α : Ordinal.{u}) (i : Fin 5) (hi : i = 0 ∨ i = 1) :
    ∃ z, faceCell (restrictFace_context α) z = cellD α i := by
  refine exists_faceCell_eq_of_last_notMem (restrictFace_context α) ?_
  -- the scopes of the display are those of `cells`
  change Fin.last 1 ∉ cells.scope i
  rcases hi with rfl | rfl <;> decide

/-- **Rows on a face**: the row of a cell of a face at a cell of the face is the row of the
corresponding cells. -/
theorem rowAt_faceCell {α : Ordinal.{u}} {n m : ℕ} {E : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {t : StageType.{u} α m} (h : restrictFace f E = some t) (i j : Fin t.card) :
    t.rowAt i j = E.rowAt (faceCell h i) (faceCell h j) := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff E f).mp h
  have hle := E.toScheme.isLowerEmbedding_comap f
  -- the cells of a face are the cells of the cell map
  change (E.toScheme.comap f).rowAt i j = E.rowAt (E.toScheme.cellMap f i)
    (E.toScheme.cellMap f j)
  unfold Scheme.rowAt
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((hle.le_iff j i).mpr h1) h2
  · exact absurd ((hle.le_iff j i).mp h2) h1
  · rfl


/-- A cell of a stage type on one point has full scope. -/
private theorem scope_eq_univ {β : Ordinal.{u}} (t : StageType.{u} β 1) (z : Fin t.card) :
    t.toCellScheme.scope z = univ := by
  have hwf := t.isWellFormed.isWellFormed
  refine Finset.Nonempty.eq_univ (Finset.card_pos.mp ?_)
  exact (hwf.grade_pos z).trans_le (hwf.grade_le_card z)

/-- The row of the display at two of the cells `0`–`3`. -/
private theorem rowAt_D (α : Ordinal.{u}) (s d : Fin 5) (hs : s ≠ 4)
    (hd : cells.gradedIndex d ≤ cells.gradedIndex s) :
    (D α).rowAt (cellD α s) (cellD α d) = val d := by
  rw [Scheme.rowAt_of_mem (show cellD α d ∈ (D α).toCellScheme.below
    ((D α).toCellScheme.gradedIndex (cellD α s)) from hd)]
  -- the rows of the display are `rowValue`
  change rowValue s d = _
  simp [rowValue, hs]

/-- **The context is a source-gap context** of grade `1` along the empty root, with lost point `0`,
owner the cell `1` of the display and lost top the cell `0`. -/
theorem isSourceGapContextAt_context (α : Ordinal.{u}) {o r : Fin (context α).card}
    (ho : faceCell (restrictFace_context α) o = cellD α 1)
    (hr : faceCell (restrictFace_context α) r = cellD α 0) :
    (context α).IsSourceGapContextAt 1 emptyRoot 0 o r where
  notMem_range := fun ⟨i, _⟩ ↦ i.elim0
  topGrade_eq := by
    refine le_antisymm (topGrade_le_iff.mpr fun d _ ↦ (context α).grade_le d) ?_
    have := grade_le_topGrade (t := context α) (d := o) (by
      rw [← label_faceCell (restrictFace_context α), ho]; rfl)
    rwa [← grade_faceCell (restrictFace_context α), ho] at this
  scope_owner := scope_eq_univ _ o
  grade_owner := by rw [← grade_faceCell (restrictFace_context α), ho]; rfl
  label_owner := by rw [← label_faceCell (restrictFace_context α), ho]; rfl
  label_lost := by rw [← label_faceCell (restrictFace_context α), hr]; rfl
  mem_scope_lost := (scope_eq_univ _ r).symm ▸ mem_univ _
  gap_owner := by
    rw [rowAt_faceCell (restrictFace_context α), rowAt_faceCell (restrictFace_context α), ho, hr,
      rowAt_D α 1 0 (by decide) (by decide), rowAt_D α 1 1 (by decide) le_rfl]
    simpa [val] using one_lt_omegaAddTwo.{u}
  gap_retained a _ ha := absurd (scope_eq_univ _ a ▸ mem_univ _) ha

/-- **The display separates the new top through the lost top**: its only cell of graded index
`(univ, 1)`, the cell `3`, reads the new top `2` as it reads the lost top `0`. -/
theorem separatesThrough_D (α : Ordinal.{u}) {r : Fin (context α).card}
    (hr : faceCell (restrictFace_context α) r = cellD α 0) :
    SeparatesThrough (restrictFace_context α) emptyRoot 1 r := by
  intro x hx _ _ u hu
  have hx' : cells.scope x ⊆ {1} := by
    rw [← univ_map_extendByLast]
    exact (mem_filter.mp hx).2
  have key2 : ∀ y : Fin 5, cells.scope y ⊆ {1} → y = 2 := by decide
  have key3 : ∀ y : Fin 5, cells.gradedIndex y = (Finset.univ, 1) → y = 3 := by decide
  have hx2 : x = cellD α 2 := key2 x hx'
  have hu3 : u = cellD α 3 := key3 u hu
  rw [hr, hx2, hu3, rowAt_D α 3 0 (by decide) (by decide), rowAt_D α 3 2 (by decide) (by decide)]
  rfl

/-- **The conclusion of the separated pinned extension property at this input**: the display is a
legal one-point coface of the context with face the donor along the empty root followed by the new
point, separating its new top through the lost top. -/
theorem exists_separatesThrough (α : Ordinal.{u}) {r : Fin (context α).card}
    (hr : faceCell (restrictFace_context α) r = cellD α 0) :
    ∃ (D' : StageType.{u} α 2) (hD' : D' ∈ (context α).cofaces),
      restrictFace (extendByLast emptyRoot) D' = some (donor α) ∧
        SeparatesThrough hD'.2 emptyRoot 1 r :=
  ⟨D α, ⟨isLegal_D α, restrictFace_context α⟩, restrictFace_donor α, separatesThrough_D α hr⟩

/-- The donor has a new top: its only cell, the cell `2` of the display, is labelled `⊤`. -/
theorem not_isTopFree_donor (α : Ordinal.{u}) : ¬ (donor α).IsTopFree := by
  obtain ⟨z, hz⟩ : ∃ z, faceCell (restrictFace_donor α) z = cellD α 2 :=
    (D α).toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace (restrictFace_donor α))
      (mem_filter.mpr ⟨mem_univ _, by
        rw [univ_map_extendByLast]
        exact show cells.scope (2 : Fin 5) ⊆ {1} by decide⟩)
  intro h
  exact h z (by rw [← label_faceCell (restrictFace_donor α), hz]; rfl)

/-- **The donor is determined over the context** along the empty root within the receiving family
of the display at every ordinal cutoff: every member of the family whose face on `{0}` is the
context has face the donor on `{1}`, its new top included. -/
theorem isDeterminedWithin_donor (α : Ordinal.{u}) (δ : Ordinal.{u}) :
    IsDeterminedWithin (receivingFamily (D α) δ) (context α) emptyRoot (donor α) := by
  obtain ⟨o, ho⟩ := exists_context_cell α 1 (.inr rfl)
  obtain ⟨r, hr⟩ := exists_context_cell α 0 (.inl rfl)
  refine isDeterminedWithin_of_separatesThrough (isSourceGapContextAt_context α ho hr)
    ⟨isLegal_D α, restrictFace_context α⟩ (topGrade_donor_le α) (restrictFace_donor α)
    (separatesThrough_D α hr) fun j hj ↦ ?_
  -- the only label other than `⊤` is `⊥`, at the dead cell
  have : (D α).label j = ⊥ := by
    change lab ⊤ ⊤ j = ⊥
    change lab ⊤ ⊤ j ≠ ⊤ at hj
    fin_cases j <;> first | exact absurd rfl hj | rfl
  rw [this]
  exact WithBot.bot_lt_coe _

end VaughtConjecture.SeparatedInstance
