/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapReading
import VaughtConjecture.Continuation.SourceGapSeparationObstruction
import VaughtConjecture.Extension.CoupledGateExamples

/-!
# Reading each new top at the input refuting separation through the lost top

Roadmap, Layer 3 ((R2) of the table of 3.4); the reading pinned extensions of
`VaughtConjecture.Continuation.SourceGapReading`.

The input `SeparationObstruction.T α` (a legal source-gap context of grade `2` along the root
`{0}`, with the donor `T α` itself) has no coface separating its new tops through the lost top
(`SeparationObstruction.not_exists_separatesThrough`).  This file builds a legal one-point coface
of it that **reads each new top** through a private top chosen with it
(`ReadingInstance.exists_readsEachNewTop_T`, compiled in this repository).

**The display** (`ReadingInstance.E α`, `ReadingInstance.isLegal_E`).  On three points with the
plan `{∅, {0}, {1}, {2}, {0, 1}, {0, 2}, univ}`, thirteen cells, each of a **kind** (`Y`, `O`, `R`
or dead):

| cell | scope    | grade | kind |   | cell | scope    | grade | kind |
|------|----------|-------|------|---|------|----------|-------|------|
| 0    | `{0}`    | 1     | `Y`  |   | 7    | `{0, 2}` | 2     | `O`  |
| 1    | `{1}`    | 1     | dead |   | 8    | `{0, 2}` | 2     | `R`  |
| 2    | `{0, 1}` | 1     | `Y`  |   | 9    | `univ`   | 1     | `Y`  |
| 3    | `{0, 1}` | 2     | `O`  |   | 10   | `univ`   | 2     | `O`  |
| 4    | `{0, 1}` | 2     | `R`  |   | 11   | `univ`   | 2     | `R`  |
| 5    | `{2}`    | 1     | dead |   | 12   | `univ`   | 3     | dead |
| 6    | `{0, 2}` | 1     | `Y`  |   |      |          |       |      |

The row of a cell depends on its kind only: a `Y` cell reads the `Y` cells at `2`; an `O` cell
reads the `Y` and `O` cells at `ω + 2` and the `R` cells at `2`; an `R` cell reads the `Y` and `O`
cells at `2` and the `R` cells at `ω + 2`; dead cells read and are read at `⊥`.  The faces on
`{0, 1}` and on `{0, 2}` are literally `T α` (`ReadingInstance.restrictFace_castSuccEmb_E`,
`ReadingInstance.restrictFace_extendByLast_E`), the second being the donor along the root.

**Lawful labellings.**  The labellings constant on kinds, `(v, w, s)` on the `Y`, `O`, `R` cells
and `⊥` on the dead ones, are lawful when `v` is self-visible at `1`, `w` and `s` at `2`, `w ≤ v`
and `min v s = min w s` (`ReadingInstance.isLawful_lab`).  Conversely every labelling lawful below
`(univ, 2)` is of this form (`ReadingInstance.conditions_univ_two`): the two copies of `o` (the
cells `3`, `7`) are read alike by both cells of graded index `(univ, 2)`, one of which dominates
them, so they agree; likewise the copies of `r`; and the cells `10` and `11` are forced to the
values of `o` and `r` by their own localities and availability.  So bountifulness reduces, through
the coatoms `{0, 1}` and `{0, 2}` (`CellScheme.Rows.isBountiful_of_coatoms`), to lifts within the
faces (those of `T α`) and to the lifts from each coatom to the full face, which copy the values
of the face along the kinds.

**Reading each new top.**  The new tops of the donor face are the cells `6` (`Y`), `7` (`O`) and
`8` (`R`); each is read, by every cell of full scope of its grade, as the private cell of its kind
(`0`, `3`, `4`).  So the conclusion of the reading pinned extension property holds at this input
(`ReadingInstance.exists_readsEachNewTop_T`), and the donor is determined over the context at
every ordinal cutoff (`ReadingInstance.isDeterminedWithin_T`).  The property itself remains open.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ReadingInstance

open Finset Label CellScheme StageType
open scoped Ordinal

/-- The low row value `2`. -/
noncomputable abbrev L : Label.{u} := SeparationObstruction.low

/-- The high row value `ω + 2`. -/
noncomputable abbrev H : Label.{u} := SeparatedInstance.omegaAddTwo

/-- The plan on three points: `∅`, the singletons, `{0, 1}`, `{0, 2}` and `univ`. -/
def plan3 : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, univ}

theorem isPlan_plan3 : Geometry.IsPlan univ plan3 := by decide

/-- The kinds: `0` dead, `1` (`Y`), `2` (`O`), `3` (`R`). -/
def kind : Fin 13 → ℕ := ![1, 0, 1, 2, 3, 0, 1, 2, 3, 1, 2, 3, 0]

/-- The cells. -/
def cells : CellScheme (Fin 13) (Fin 3) :=
  ⟨univ, plan3, ![{0}, {1}, {0, 1}, {0, 1}, {0, 1}, {2}, {0, 2}, {0, 2}, {0, 2}, univ, univ, univ,
    univ], ![1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3]⟩

/-- The labelling `v` on the `Y` cells, `w` on the `O` cells, `s` on the `R` cells, `⊥` on the dead
cells. -/
noncomputable def lab (v w s : Label.{u}) (d : Fin 13) : Label.{u} :=
  if kind d = 1 then v else if kind d = 2 then w else if kind d = 3 then s else ⊥

/-- The rows, by the kind of the reading cell. -/
noncomputable def rowValue (c d : Fin 13) : Label.{u} :=
  if kind c = 1 then lab L ⊥ ⊥ d else if kind c = 2 then lab H H L d
  else if kind c = 3 then lab L L H d else ⊥

/-- The scheme on three points. -/
noncomputable abbrev S : Scheme.{u} 3 := ⟨13, cells, ⟨fun c d ↦ rowValue c d.1⟩⟩

theorem kind_cases (d : Fin 13) : kind d = 0 ∨ kind d = 1 ∨ kind d = 2 ∨ kind d = 3 := by
  revert d; decide

theorem lab_of_kind {v w s : Label.{u}} {d : Fin 13} :
    (kind d = 0 → lab v w s d = ⊥) ∧ (kind d = 1 → lab v w s d = v) ∧
      (kind d = 2 → lab v w s d = w) ∧ (kind d = 3 → lab v w s d = s) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩ <;> simp [lab, h]

theorem lab_congr {v w s : Label.{u}} {d e : Fin 13} (h : kind d = kind e) :
    lab v w s d = lab v w s e := by
  simp [lab, h]

/-- The grades by kind. -/
private theorem grade_kind : ∀ d : Fin 13, (kind d = 1 → cells.grade d = 1) ∧
    (kind d = 2 → cells.grade d = 2) ∧ (kind d = 3 → cells.grade d = 2) := by decide

/-- The cells below a `Y` cell are `Y` or dead. -/
private theorem below_Y : ∀ c d : Fin 13, kind c = 1 → cells.gradedIndex d ≤ cells.gradedIndex c →
    kind d = 0 ∨ kind d = 1 := by decide

/-- Every cell has grade at most `3`; the cells below a live cell have grade at most `2`. -/
private theorem grade_le_two : ∀ c d : Fin 13, kind c ≠ 0 →
    cells.gradedIndex d ≤ cells.gradedIndex c → cells.grade d ≤ 2 := by decide

private theorem isSelfVisible_L : IsSelfVisible 2 L.{u} := SeparationObstruction.isSelfVisible_low

private theorem isSelfVisible_H : IsSelfVisible 2 H.{u} :=
  SeparationObstruction.isSelfVisible_omegaAddTwo_two

private theorem L_le_H : L.{u} ≤ H.{u} := SeparationObstruction.low_lt_omegaAddTwo.le

/-- **Lawful labellings constant on kinds.** -/
theorem isLawful_lab {v w s : Label.{u}} (hv : IsSelfVisible 1 v) (hw : IsSelfVisible 2 w)
    (hs : IsSelfVisible 2 s) (hwv : w ≤ v) (hvs : min v s = min w s) :
    S.{u}.rows.IsLawful (lab v w s) where
  orderly d := by
    rcases kind_cases d with h | h | h | h
    · rw [lab_of_kind.1 h]; exact isSelfVisible_bot _
    · rw [lab_of_kind.2.1 h]
      -- the grade of a `Y` cell is `1`
      change IsSelfVisible (cells.grade d) _
      rw [(grade_kind d).1 h]; exact hv
    · rw [lab_of_kind.2.2.1 h]
      change IsSelfVisible (cells.grade d) _
      rw [(grade_kind d).2.1 h]; exact hw
    · rw [lab_of_kind.2.2.2 h]
      change IsSelfVisible (cells.grade d) _
      rw [(grade_kind d).2.2 h]; exact hs
  locality c := by
    rcases kind_cases c with hc | hc | hc | hc
    · convert TransformsTo.bot _ _ using 1
      funext d
      -- the transformed section at a dead cell is `⊥`
      rw [lab_of_kind.1 hc, min_bot_right]
    · refine SeparationObstruction.transformsTo_twoLevel_step (K := 1)
        (fun d : cells.below (cells.gradedIndex c) ↦ ?_) hv hv le_rfl fun ⟨d, hd⟩ ↦ ?_
      · exact d.2.2.trans ((grade_kind c).1 hc).le
      · -- the row of a `Y` cell is `lab L ⊥ ⊥`
        change (rowValue c d = ⊥ ∧ _) ∨ (rowValue c d = SeparationObstruction.low ∧ _) ∨ _
        simp only [rowValue, hc, ite_true]
        rcases below_Y c d hc hd with hd' | hd'
        · left
          rw [lab_of_kind.1 hd', lab_of_kind.1 hd', min_bot_left]
          exact ⟨rfl, rfl⟩
        · right; left
          rw [lab_of_kind.2.1 hd', lab_of_kind.2.1 hd', lab_of_kind.2.1 hc, min_self]
          exact ⟨rfl, rfl⟩
    · refine SeparationObstruction.transformsTo_twoLevel_step (K := 2)
        (fun d : cells.below (cells.gradedIndex c) ↦ grade_le_two c d.1 (by omega) d.2)
        (hs.min hw) hw (min_le_right _ _) fun ⟨d, hd⟩ ↦ ?_
      -- the row of an `O` cell is `lab H H L`
      change (rowValue c d = ⊥ ∧ _) ∨ (rowValue c d = SeparationObstruction.low ∧ _) ∨ _
      simp only [rowValue, hc, show ¬ (2 = 1) by omega, ite_true, ite_false]
      rw [lab_of_kind.2.2.1 hc]
      rcases kind_cases d with hd' | hd' | hd' | hd'
      · left; rw [lab_of_kind.1 hd', lab_of_kind.1 hd', min_bot_left]; exact ⟨rfl, rfl⟩
      · right; right; rw [lab_of_kind.2.1 hd', lab_of_kind.2.1 hd', min_eq_right hwv]
        exact ⟨rfl, rfl⟩
      · right; right; rw [lab_of_kind.2.2.1 hd', lab_of_kind.2.2.1 hd', min_self]
        exact ⟨rfl, rfl⟩
      · right; left; rw [lab_of_kind.2.2.2 hd', lab_of_kind.2.2.2 hd']; exact ⟨rfl, rfl⟩
    · refine SeparationObstruction.transformsTo_twoLevel_step (K := 2)
        (fun d : cells.below (cells.gradedIndex c) ↦ grade_le_two c d.1 (by omega) d.2)
        (hw.min hs) hs (min_le_right _ _) fun ⟨d, hd⟩ ↦ ?_
      -- the row of an `R` cell is `lab L L H`
      change (rowValue c d = ⊥ ∧ _) ∨ (rowValue c d = SeparationObstruction.low ∧ _) ∨ _
      simp only [rowValue, hc, show ¬ (3 = 1) by omega, show ¬ (3 = 2) by omega, ite_true,
        ite_false]
      rw [lab_of_kind.2.2.2 hc]
      rcases kind_cases d with hd' | hd' | hd' | hd'
      · left; rw [lab_of_kind.1 hd', lab_of_kind.1 hd', min_bot_left]; exact ⟨rfl, rfl⟩
      · right; left; rw [lab_of_kind.2.1 hd', lab_of_kind.2.1 hd', hvs]; exact ⟨rfl, rfl⟩
      · right; left; rw [lab_of_kind.2.2.1 hd', lab_of_kind.2.2.1 hd']; exact ⟨rfl, rfl⟩
      · right; right; rw [lab_of_kind.2.2.2 hd', lab_of_kind.2.2.2 hd', min_self]
        exact ⟨rfl, rfl⟩
  availability c t hct hg := by
    have key : ∀ c t : Fin 13, cells.scope c ⊆ cells.scope t → cells.grade c = cells.grade t →
        ∃ u : Fin 13, cells.gradedIndex u = cells.gradedIndex t ∧ (kind u = kind c ∨ kind c = 0)
        := by decide
    obtain ⟨u, hu, hk⟩ := key c t hct hg
    refine ⟨u, hu, ?_⟩
    rcases hk with hk | hk
    · exact (lab_congr hk.symm).le
    · rw [lab_of_kind.1 hk]; exact bot_le

/-! ### Legality -/

theorem isWellFormed_cells : cells.IsWellFormed :=
  ⟨inferInstance, isPlan_plan3, fun d ↦ by
    have key : ∀ d : Fin 13, cells.scope d ∈ cells.faces ∧ 0 < cells.grade d ∧
        cells.grade d ≤ #(cells.scope d) := by decide
    exact key d⟩

theorem isCoded_S : S.{u}.IsCoded := fun c t ↦ by
  -- the rows of `S` are `rowValue`
  change rowValue c t.1 < _
  have hL : L.{u} < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    natCast_label_lt_omega0_sq 2
  have hH : H.{u} < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    lt_omega0_sq_iff.mpr (.inr ⟨1, 2, by simp [H, SeparatedInstance.omegaAddTwo]⟩)
  have hB : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    WithBot.bot_lt_coe _
  unfold rowValue lab
  split_ifs <;> assumption

theorem isConsistent_S : S.{u}.rows.IsConsistent := by
  intro c
  -- consistency at `c` is lawfulness of its row below its graded index
  change S.{u}.rows.IsLawfulBelow (cells.gradedIndex c) (S.{u}.rows.row c)
  have hrow : ∀ v w s : Label.{u}, (∀ d, rowValue c d = lab v w s d) →
      S.{u}.rows.row c = fun d ↦ lab v w s d.1 := fun v w s h ↦ funext fun d ↦ h d.1
  rcases kind_cases c with hc | hc | hc | hc
  · rw [hrow ⊥ ⊥ ⊥ fun d ↦ by simp [rowValue, lab, hc]]
    exact CellScheme.Rows.IsLawful.isLawfulBelow
      (isLawful_lab (isSelfVisible_bot _) (isSelfVisible_bot _) (isSelfVisible_bot _) le_rfl rfl) _
  · rw [hrow L ⊥ ⊥ fun d ↦ by simp [rowValue, hc]]
    exact CellScheme.Rows.IsLawful.isLawfulBelow (isLawful_lab (isSelfVisible_L.mono (by omega))
      (isSelfVisible_bot _) (isSelfVisible_bot _) bot_le (by simp)) _
  · rw [hrow H H L fun d ↦ by simp [rowValue, hc]]
    exact CellScheme.Rows.IsLawful.isLawfulBelow (isLawful_lab (isSelfVisible_H.mono (by omega))
      isSelfVisible_H isSelfVisible_L le_rfl rfl) _
  · rw [hrow L L H fun d ↦ by simp [rowValue, hc]]
    exact CellScheme.Rows.IsLawful.isLawfulBelow (isLawful_lab (isSelfVisible_L.mono (by omega))
      isSelfVisible_L isSelfVisible_H le_rfl rfl) _

theorem isComplete_cells : cells.IsComplete := by
  intro X hX
  obtain ⟨B, j⟩ := X
  obtain ⟨hB, hj0, hjB⟩ := hX
  have hj3 : j ≤ 3 := hjB.trans (by simpa using card_le_univ B)
  have key : ∀ B ∈ plan3, ∀ j : Fin 4, 0 < (j : ℕ) → (j : ℕ) ≤ #B →
      ∃ d : Fin 13, cells.gradedIndex d = (B, (j : ℕ)) := by decide
  exact key B hB ⟨j, by omega⟩ hj0 hjB

/-! ### Lawful labellings below a pair: necessary conditions -/

section Necessity

variable {X : Finset (Fin 3) × ℕ} {w : Fin 13 → Label.{u}}

/-- Two cells read alike by a cell, of equal grades, have equal capped labels. -/
private theorem eq_at (hw : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d)) {c d d' : Fin 13}
    (hc : cells.gradedIndex c ≤ X) (hd : cells.gradedIndex d ≤ cells.gradedIndex c)
    (hd' : cells.gradedIndex d' ≤ cells.gradedIndex c) (hr : rowValue.{u} c d = rowValue c d')
    (hg : cells.grade d = cells.grade d') : min (w d) (w c) = min (w d') (w c) := by
  have hl := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 c hc
  exact le_antisymm (hl.le_of_le (d := ⟨d, hd⟩) (d' := ⟨d', hd'⟩) hr.le hg.symm.le)
    (hl.le_of_le (d := ⟨d', hd'⟩) (d' := ⟨d, hd⟩) hr.symm.le hg.le)

/-- A cell read as at least a cell of no larger grade by a cell has capped label at most it. -/
private theorem le_at (hw : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d)) {c d d' : Fin 13}
    (hc : cells.gradedIndex c ≤ X) (hd : cells.gradedIndex d ≤ cells.gradedIndex c)
    (hd' : cells.gradedIndex d' ≤ cells.gradedIndex c) (hr : rowValue.{u} c d ≤ rowValue c d')
    (hg : cells.grade d' ≤ cells.grade d) : min (w d) (w c) ≤ min (w d') (w c) :=
  ((CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 c hc).le_of_le (d := ⟨d, hd⟩)
    (d' := ⟨d', hd'⟩) hr hg

/-- A dead cell below `X` is `⊥`. -/
private theorem eq_bot_at (hw : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d)) {c : Fin 13}
    (hc : cells.gradedIndex c ≤ X) (hk : kind c = 0) : w c = ⊥ := by
  have := ((CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 c hc).eq_bot
    (d := ⟨c, CellScheme.mem_below_gradedIndex _ c⟩) (by simp [rowValue, hk])
  simpa using this

/-- Availability below `X` into the graded index of a cell `t`. -/
private theorem avail (hw : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d)) {c t : Fin 13}
    (ht : cells.gradedIndex t ≤ X) (hct : cells.scope c ⊆ cells.scope t)
    (hg : cells.grade c = cells.grade t) :
    ∃ u, cells.gradedIndex u = cells.gradedIndex t ∧ w c ≤ w u :=
  (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.2 c t ht hct hg

/-- The two `R`-readings at the `R` cell `c`, of the `Y` cell `a` and the `O` cell `b`, agree. -/
private theorem min_eq_min_at (hw : S.{u}.rows.IsLawfulBelow X (fun d ↦ w d)) {c a b : Fin 13}
    (hc : cells.gradedIndex c ≤ X) (hkc : kind c = 3) (hgc : cells.grade c = 2)
    (ha : cells.gradedIndex a ≤ cells.gradedIndex c) (hka : kind a = 1) (hga : cells.grade a = 1)
    (hb : cells.gradedIndex b ≤ cells.gradedIndex c) (hkb : kind b = 2) (hgb : cells.grade b = 2) :
    min (w a) (w c) = min (w b) (w c) := by
  obtain ⟨g, σ, hwit, heq⟩ := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).2.1 c hc
  have hcc := heq ⟨c, CellScheme.mem_below_gradedIndex _ c⟩
  have hca := heq ⟨a, ha⟩
  have hcb := heq ⟨b, hb⟩
  simp only [min_self] at hcc
  -- the row of `c` reads `a`, `b` at `2` and itself at `ω + 2`; the grades are `1`, `2`, `2`
  change w c = min (σ (rowValue c c)) (g (cells.grade c)) at hcc
  change min (w a) (w c) = min (σ (rowValue c a)) (g (cells.grade a)) at hca
  change min (w b) (w c) = min (σ (rowValue c b)) (g (cells.grade b)) at hcb
  have hra : rowValue.{u} c a = rowValue c b := by simp [rowValue, lab, hkc, hka, hkb]
  rw [hgc] at hcc
  rw [hga, hra] at hca
  rw [hgb] at hcb
  have hg : g 2 ≤ g 1 := hwit.antitone (by omega)
  have hs : w c ≤ g 2 := hcc ▸ min_le_right _ _
  have hA : min (w a) (w c) ≤ w c := min_le_right _ _
  have hB : min (w b) (w c) ≤ w c := min_le_right _ _
  rcases le_total (σ (rowValue c b)) (g 2) with h | h
  · rw [hca, hcb, min_eq_left h, min_eq_left (h.trans hg)]
  · have hB' : min (w b) (w c) = g 2 := hcb.trans (min_eq_right h)
    have hBs : min (w b) (w c) = w c := le_antisymm hB (hB' ▸ hs)
    refine le_antisymm (hA.trans hBs.symm.le) ?_
    rw [hca, hB']
    exact le_min h hg

/-- **Below `({0, 1}, 1)`**: `e₁ = ⊥` and `z₁ = y`. -/
private theorem conditions_face_one (hw : S.{u}.rows.IsLawfulBelow ({0, 1}, 1) (fun d ↦ w d)) :
    w 1 = ⊥ ∧ w 2 = w 0 ∧ IsSelfVisible 1 (w 0) := by
  have h2 : cells.gradedIndex 2 ≤ (({0, 1} : Finset (Fin 3)), 1) := by decide
  refine ⟨eq_bot_at hw (by decide) rfl, le_antisymm ?_ ?_,
    (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).1 0
      (show cells.gradedIndex 0 ≤ (({0, 1} : Finset (Fin 3)), 1) by decide)⟩
  · simpa using le_at hw h2 (d := 2) (d' := 0) le_rfl (by decide) (le_of_eq rfl) le_rfl
  · obtain ⟨u, hu, hle⟩ := avail hw h2 (c := 0) (by decide) rfl
    have key : ∀ u : Fin 13, cells.gradedIndex u = cells.gradedIndex 2 → u = 2 := by decide
    rwa [key u hu] at hle

/-- **Below `({0, 2}, 1)`**: `e₂ = ⊥` and `z₂ = y`. -/
private theorem conditions_face_one' (hw : S.{u}.rows.IsLawfulBelow ({0, 2}, 1) (fun d ↦ w d)) :
    w 5 = ⊥ ∧ w 6 = w 0 ∧ IsSelfVisible 1 (w 0) := by
  have h6 : cells.gradedIndex 6 ≤ (({0, 2} : Finset (Fin 3)), 1) := by decide
  refine ⟨eq_bot_at hw (by decide) rfl, le_antisymm ?_ ?_,
    (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).1 0
      (show cells.gradedIndex 0 ≤ (({0, 2} : Finset (Fin 3)), 1) by decide)⟩
  · simpa using le_at hw h6 (d := 6) (d' := 0) le_rfl (by decide) (le_of_eq rfl) le_rfl
  · obtain ⟨u, hu, hle⟩ := avail hw h6 (c := 0) (by decide) rfl
    have key : ∀ u : Fin 13, cells.gradedIndex u = cells.gradedIndex 6 → u = 6 := by decide
    rwa [key u hu] at hle

/-- **Below `({0, 1}, 2)`**: the face `T α` on `{0, 1}`; `e₁ = ⊥`, `z₁ = y`, `o₁ ≤ y`, and
`min y r₁ = min o₁ r₁`. -/
private theorem conditions_face_two (hw : S.{u}.rows.IsLawfulBelow ({0, 1}, 2) (fun d ↦ w d)) :
    w 1 = ⊥ ∧ w 2 = w 0 ∧ w 3 ≤ w 0 ∧ min (w 0) (w 4) = min (w 3) (w 4) ∧
      IsSelfVisible 1 (w 0) ∧ IsSelfVisible 2 (w 3) ∧ IsSelfVisible 2 (w 4) := by
  have hX : (({0, 1} : Finset (Fin 3)), 1) ≤ (({0, 1} : Finset (Fin 3)), 2) := by decide
  obtain ⟨h1, h2, hv⟩ := conditions_face_one (hw.mono hX)
  have ho := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).1
  refine ⟨h1, h2, ?_, min_eq_min_at hw (c := 4) (a := 0) (b := 3) (by decide) rfl rfl
    (by decide) rfl rfl (by decide) rfl rfl, hv,
    ho 3 (show cells.gradedIndex 3 ≤ (({0, 1} : Finset (Fin 3)), 2) by decide),
    ho 4 (show cells.gradedIndex 4 ≤ (({0, 1} : Finset (Fin 3)), 2) by decide)⟩
  simpa using le_at hw (c := 3) (d := 3) (d' := 0) (by decide) le_rfl (by decide)
    (le_of_eq rfl) (by decide)

/-- **Below `({0, 2}, 2)`**: the face `T α` on `{0, 2}`. -/
private theorem conditions_face_two' (hw : S.{u}.rows.IsLawfulBelow ({0, 2}, 2) (fun d ↦ w d)) :
    w 5 = ⊥ ∧ w 6 = w 0 ∧ w 7 ≤ w 0 ∧ min (w 0) (w 8) = min (w 7) (w 8) ∧
      IsSelfVisible 1 (w 0) ∧ IsSelfVisible 2 (w 7) ∧ IsSelfVisible 2 (w 8) := by
  have hX : (({0, 2} : Finset (Fin 3)), 1) ≤ (({0, 2} : Finset (Fin 3)), 2) := by decide
  obtain ⟨h5, h6, hv⟩ := conditions_face_one' (hw.mono hX)
  have ho := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hw).1
  refine ⟨h5, h6, ?_, min_eq_min_at hw (c := 8) (a := 0) (b := 7) (by decide) rfl rfl
    (by decide) rfl rfl (by decide) rfl rfl, hv,
    ho 7 (show cells.gradedIndex 7 ≤ (({0, 2} : Finset (Fin 3)), 2) by decide),
    ho 8 (show cells.gradedIndex 8 ≤ (({0, 2} : Finset (Fin 3)), 2) by decide)⟩
  simpa using le_at hw (c := 7) (d := 7) (d' := 0) (by decide) le_rfl (by decide)
    (le_of_eq rfl) (by decide)

/-- **Below `(univ, 2)` every lawful labelling is constant on kinds**: it is
`lab (w 0) (w 3) (w 4)` at every cell other than the cell `12` of grade `3`. -/
theorem conditions_univ_two (hw : S.{u}.rows.IsLawfulBelow (univ, 2) (fun d ↦ w d)) :
    (∀ d : Fin 13, d ≠ 12 → w d = lab (w 0) (w 3) (w 4) d) ∧ w 3 ≤ w 0 ∧
      min (w 0) (w 4) = min (w 3) (w 4) ∧ IsSelfVisible 1 (w 0) ∧ IsSelfVisible 2 (w 3) ∧
        IsSelfVisible 2 (w 4) := by
  obtain ⟨h1, h2, h30, h04, hv0, hv3, hv4⟩ :=
    conditions_face_two (hw.mono (show (({0, 1} : Finset (Fin 3)), 2) ≤ (univ, 2) by decide))
  obtain ⟨h5, h6, -, -, -, -, -⟩ :=
    conditions_face_two' (hw.mono (show (({0, 2} : Finset (Fin 3)), 2) ≤ (univ, 2) by decide))
  -- the `Y` cell of full scope
  have h9 : w 9 = w 0 := by
    refine le_antisymm ?_ ?_
    · simpa using le_at hw (c := 9) (d := 9) (d' := 0) (by decide) le_rfl (by decide)
        (le_of_eq rfl) le_rfl
    · obtain ⟨u, hu, hle⟩ := avail hw (c := 0) (t := 9) (by decide) (by decide) rfl
      have key : ∀ u : Fin 13, cells.gradedIndex u = cells.gradedIndex 9 → u = 9 := by decide
      rwa [key u hu] at hle
  -- the cells of graded index `(univ, 2)` are `10` and `11`
  have key2 : ∀ u : Fin 13, cells.gradedIndex u = cells.gradedIndex 10 → u = 10 ∨ u = 11 := by
    decide
  -- two cells read alike by `10` and by `11`, one of which dominates, agree
  have hcopy (a b : Fin 13) (ha : cells.gradedIndex a ≤ (univ, 2))
      (hb : cells.gradedIndex b ≤ (univ, 2)) (hsa : cells.scope a ⊆ univ)
      (hga : cells.grade a = 2) (hgb : cells.grade b = 2)
      (hr10 : rowValue.{u} 10 a = rowValue 10 b) (hr11 : rowValue.{u} 11 a = rowValue 11 b) :
      w a ≤ w b := by
    obtain ⟨u, hu, hle⟩ := avail hw (c := a) (t := 10) (by decide) hsa (by rw [hga]; rfl)
    have hab (c : Fin 13) (hc : c = 10 ∨ c = 11) (hr : rowValue.{u} c a = rowValue c b) :
        min (w a) (w c) = min (w b) (w c) := by
      rcases hc with rfl | rfl
      · exact eq_at hw (by decide) (le_trans ha (by decide)) (le_trans hb (by decide)) hr
          (hga.trans hgb.symm)
      · exact eq_at hw (by decide) (le_trans ha (by decide)) (le_trans hb (by decide)) hr
          (hga.trans hgb.symm)
    rcases key2 u hu with rfl | rfl
    · have := hab 10 (.inl rfl) hr10
      rw [min_eq_left hle] at this
      exact this.le.trans (min_le_left _ _)
    · have := hab 11 (.inr rfl) hr11
      rw [min_eq_left hle] at this
      exact this.le.trans (min_le_left _ _)
  have h7 : w 7 = w 3 := le_antisymm
    (hcopy 7 3 (by decide) (by decide) (subset_univ _) rfl rfl rfl rfl)
    (hcopy 3 7 (by decide) (by decide) (subset_univ _) rfl rfl rfl rfl)
  have h8 : w 8 = w 4 := le_antisymm
    (hcopy 8 4 (by decide) (by decide) (subset_univ _) rfl rfl rfl rfl)
    (hcopy 4 8 (by decide) (by decide) (subset_univ _) rfl rfl rfl rfl)
  -- the two cells of graded index `(univ, 2)` carry the values of `o` and `r`
  have hp : w 10 ≤ w 3 := by
    simpa using le_at hw (c := 10) (d := 10) (d' := 3) (by decide) le_rfl (by decide)
      (le_of_eq rfl) le_rfl
  have hq : w 11 ≤ w 4 := by
    simpa using le_at hw (c := 11) (d := 11) (d' := 4) (by decide) le_rfl (by decide)
      (le_of_eq rfl) le_rfl
  have hdom (a : Fin 13) (ha : cells.gradedIndex a ≤ (univ, 2)) (hga : cells.grade a = 2) :
      w a ≤ w 10 ∨ w a ≤ w 11 := by
    obtain ⟨u, hu, hle⟩ := avail hw (c := a) (t := 10) (by decide) (subset_univ _)
      (by rw [hga]; rfl)
    rcases key2 u hu with rfl | rfl
    exacts [.inl hle, .inr hle]
  obtain ⟨h10, h11⟩ := CoupledGateExamples.eq_and_eq_of_min_eq hp hq
    (eq_at hw (c := 10) (d := 4) (d' := 11) (by decide) (by decide) (by decide) rfl rfl)
    (eq_at hw (c := 11) (d := 3) (d' := 10) (by decide) (by decide) (by decide) rfl rfl)
    (hdom 3 (by decide) rfl) (hdom 4 (by decide) rfl)
  refine ⟨fun d hd ↦ ?_, h30, h04, hv0, hv3, hv4⟩
  fin_cases d
  · rfl
  · exact h1
  · exact h2
  · rfl
  · rfl
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact absurd rfl hd

/-- **Below `(univ, 1)`**: the dead cells are `⊥` and the `Y` cells equal `y`. -/
private theorem conditions_univ_one (hw : S.{u}.rows.IsLawfulBelow (univ, 1) (fun d ↦ w d)) :
    w 1 = ⊥ ∧ w 5 = ⊥ ∧ w 2 = w 0 ∧ w 6 = w 0 ∧ w 9 = w 0 := by
  obtain ⟨h1, h2, -⟩ :=
    conditions_face_one (hw.mono (show (({0, 1} : Finset (Fin 3)), 1) ≤ (univ, 1) by decide))
  obtain ⟨h5, h6, -⟩ :=
    conditions_face_one' (hw.mono (show (({0, 2} : Finset (Fin 3)), 1) ≤ (univ, 1) by decide))
  refine ⟨h1, h5, h2, h6, le_antisymm ?_ ?_⟩
  · simpa using le_at hw (c := 9) (d := 9) (d' := 0) (by decide) le_rfl (by decide)
      (le_of_eq rfl) le_rfl
  · obtain ⟨u, hu, hle⟩ := avail hw (c := 0) (t := 9) (by decide) (by decide) rfl
    have key : ∀ u : Fin 13, cells.gradedIndex u = cells.gradedIndex 9 → u = 9 := by decide
    rwa [key u hu] at hle

end Necessity

/-! ### Bountifulness -/

/-- Capped agreement of two labellings constant on kinds, from that of their values. -/
private theorem min_lab_congr {v w s v' w' s' c : Label.{u}} (hv : min v c = min v' c)
    (hw : min w c = min w' c) (hs : min s c = min s' c) (d : Fin 13) :
    min (lab v w s d) c = min (lab v' w' s' d) c := by
  rcases kind_cases d with h | h | h | h
  · rw [lab_of_kind.1 h, lab_of_kind.1 h]
  · rw [lab_of_kind.2.1 h, lab_of_kind.2.1 h, hv]
  · rw [lab_of_kind.2.2.1 h, lab_of_kind.2.2.1 h, hw]
  · rw [lab_of_kind.2.2.2 h, lab_of_kind.2.2.2 h, hs]

/-- A capped lift by a labelling constant on kinds. -/
private theorem cappedLift_of_lab {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y)
    (hlift : ∀ (c : Label.{u}) (wp wq : Fin 13 → Label.{u}),
      S.{u}.rows.IsLawfulBelow X (fun d ↦ wp d) → S.{u}.rows.IsLawfulBelow Y (fun d ↦ wq d) →
      (∀ d, cells.gradedIndex d ≤ X → min (wq d) c = min (wp d) c) →
      ∃ v w s : Label.{u}, S.{u}.rows.IsLawful (lab v w s) ∧
        (∀ d, cells.gradedIndex d ≤ X → lab v w s d = wp d) ∧
        ∀ d, cells.gradedIndex d ≤ Y → min (lab v w s d) c = min (wq d) c) :
    S.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c _ p q hp hq hpq ↦ ?_
  set wp := CellScheme.Rows.extendBot X p
  set wq := CellScheme.Rows.extendBot Y q
  have hpw : ∀ d, p d = wp d := fun d ↦ (CellScheme.Rows.extendBot_of_mem p d.2).symm
  have hqw : ∀ d, q d = wq d := fun d ↦ (CellScheme.Rows.extendBot_of_mem q d.2).symm
  obtain ⟨v, w, s, hl, hres, hcap⟩ := hlift c wp wq (CellScheme.Rows.isLawfulBelow_extendBot.mpr hp)
    (CellScheme.Rows.isLawfulBelow_extendBot.mpr hq) fun d hd ↦ by
      have := hpq ⟨d, hd⟩
      rwa [hqw, hpw] at this
  exact ⟨fun d ↦ lab v w s d, CellScheme.Rows.IsLawful.isLawfulBelow hl Y,
    fun d ↦ (hcap d.1 d.2).trans (by rw [hqw]), fun d ↦ (hres d.1 d.2).trans (hpw d).symm⟩

/-- The lift from a coatom at the grade `2` to the full face, along `y`, `o`, `r` of the coatom. -/
private theorem cappedLift_two {X : Finset (Fin 3) × ℕ} (h : X ≤ ((univ : Finset (Fin 3)), 2))
    (y o r : Fin 13) (hy : kind y = 1) (ho : kind o = 2) (hr : kind r = 3)
    (hyX : cells.gradedIndex y ≤ X) (hoX : cells.gradedIndex o ≤ X) (hrX : cells.gradedIndex r ≤ X)
    (hface : ∀ wp : Fin 13 → Label.{u}, S.{u}.rows.IsLawfulBelow X (fun d ↦ wp d) →
      S.{u}.rows.IsLawful (lab (wp y) (wp o) (wp r)) ∧
        ∀ d, cells.gradedIndex d ≤ X → lab (wp y) (wp o) (wp r) d = wp d) :
    S.{u}.rows.CappedLift h := by
  refine cappedLift_of_lab h fun c wp wq hp hq hpq ↦ ?_
  obtain ⟨hl, hres⟩ := hface wp hp
  obtain ⟨hq', -⟩ := conditions_univ_two hq
  have hne : ∀ d : Fin 13, cells.gradedIndex d ≤ ((univ : Finset (Fin 3)), 2) → d ≠ 12 := by
    decide
  have hlq : ∀ d, cells.gradedIndex d ≤ ((univ : Finset (Fin 3)), 2) →
      wq d = lab (wq 0) (wq 3) (wq 4) d := fun d hd ↦ hq' d (hne d hd)
  have hcy : min (wq y) c = min (wp y) c := hpq y hyX
  have hco : min (wq o) c = min (wp o) c := hpq o hoX
  have hcr : min (wq r) c = min (wp r) c := hpq r hrX
  rw [hlq y (hyX.trans h), lab_of_kind.2.1 hy] at hcy
  rw [hlq o (hoX.trans h), lab_of_kind.2.2.1 ho] at hco
  rw [hlq r (hrX.trans h), lab_of_kind.2.2.2 hr] at hcr
  exact ⟨wp y, wp o, wp r, hl, hres, fun d hd ↦ by
    rw [hlq d hd]; exact min_lab_congr hcy.symm hco.symm hcr.symm d⟩

/-- The lift from a face at the grade `1` along `y`, to a larger face of grade `1` whose lawful
labellings are `y` on the `Y` cells and `⊥` on the dead cells. -/
private theorem cappedLift_one {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y)
    (hy : cells.gradedIndex 0 ≤ X)
    (hface : ∀ wp : Fin 13 → Label.{u}, S.{u}.rows.IsLawfulBelow X (fun d ↦ wp d) →
      IsSelfVisible 1 (wp 0) ∧ ∀ d, cells.gradedIndex d ≤ X → lab (wp 0) ⊥ ⊥ d = wp d)
    (hamb : ∀ wq : Fin 13 → Label.{u}, S.{u}.rows.IsLawfulBelow Y (fun d ↦ wq d) →
      ∀ d, cells.gradedIndex d ≤ Y → wq d = lab (wq 0) ⊥ ⊥ d) :
    S.{u}.rows.CappedLift h := by
  refine cappedLift_of_lab h fun c wp wq hp hq hpq ↦ ?_
  obtain ⟨hv, hres⟩ := hface wp hp
  have hcy : min (wq 0) c = min (wp 0) c := hpq 0 hy
  exact ⟨wp 0, ⊥, ⊥, isLawful_lab hv (isSelfVisible_bot _) (isSelfVisible_bot _) bot_le
    (by simp), hres, fun d hd ↦ by
      rw [hamb wq hq d hd]; exact min_lab_congr hcy.symm rfl rfl d⟩

/-- The lift from a face at the grade `1` containing only a dead cell. -/
private theorem cappedLift_dead {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y)
    (hdead : ∀ d, cells.gradedIndex d ≤ X → kind d = 0)
    (hamb : ∀ wq : Fin 13 → Label.{u}, S.{u}.rows.IsLawfulBelow Y (fun d ↦ wq d) →
      IsSelfVisible 1 (wq 0) ∧ ∀ d, cells.gradedIndex d ≤ Y → wq d = lab (wq 0) ⊥ ⊥ d) :
    S.{u}.rows.CappedLift h := by
  refine cappedLift_of_lab h fun c wp wq hp hq hpq ↦ ?_
  obtain ⟨hv, hl⟩ := hamb wq hq
  exact ⟨wq 0, ⊥, ⊥, isLawful_lab hv (isSelfVisible_bot _) (isSelfVisible_bot _) bot_le
    (by simp), fun d hd ↦ by rw [lab_of_kind.1 (hdead d hd), eq_bot_at hp hd (hdead d hd)],
    fun d hd ↦ by rw [← hl d hd]⟩

/-- **The rows are bountiful**, through the coatoms `{0, 1}` and `{0, 2}`. -/
theorem isBountiful_S : S.{u}.rows.IsBountiful := by
  -- the faces below `({0, 1}, ·)` and `({0, 2}, ·)`, and below the full face
  have b01 : ∀ d : Fin 13, cells.gradedIndex d ≤ (({0, 1} : Finset (Fin 3)), 2) →
      d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by decide
  have b02 : ∀ d : Fin 13, cells.gradedIndex d ≤ (({0, 2} : Finset (Fin 3)), 2) →
      d = 0 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 := by decide
  have b01' : ∀ d : Fin 13, cells.gradedIndex d ≤ (({0, 1} : Finset (Fin 3)), 1) →
      d = 0 ∨ d = 1 ∨ d = 2 := by decide
  have b02' : ∀ d : Fin 13, cells.gradedIndex d ≤ (({0, 2} : Finset (Fin 3)), 1) →
      d = 0 ∨ d = 5 ∨ d = 6 := by decide
  have bu1 : ∀ d : Fin 13, cells.gradedIndex d ≤ ((univ : Finset (Fin 3)), 1) →
      d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 5 ∨ d = 6 ∨ d = 9 := by decide
  -- the lifts at the grade `1` within the coatoms and into the full face
  have amb01 : ∀ wq : Fin 13 → Label.{u},
      S.{u}.rows.IsLawfulBelow ({0, 1}, 1) (fun d ↦ wq d) →
      IsSelfVisible 1 (wq 0) ∧ ∀ d, cells.gradedIndex d ≤ (({0, 1} : Finset (Fin 3)), 1) →
        wq d = lab (wq 0) ⊥ ⊥ d := fun wq hq ↦ by
    obtain ⟨h1, h2, hv⟩ := conditions_face_one hq
    refine ⟨hv, fun d hd ↦ ?_⟩
    rcases b01' d hd with rfl | rfl | rfl
    exacts [rfl, h1, h2]
  have amb02 : ∀ wq : Fin 13 → Label.{u},
      S.{u}.rows.IsLawfulBelow ({0, 2}, 1) (fun d ↦ wq d) →
      IsSelfVisible 1 (wq 0) ∧ ∀ d, cells.gradedIndex d ≤ (({0, 2} : Finset (Fin 3)), 1) →
        wq d = lab (wq 0) ⊥ ⊥ d := fun wq hq ↦ by
    obtain ⟨h5, h6, hv⟩ := conditions_face_one' hq
    refine ⟨hv, fun d hd ↦ ?_⟩
    rcases b02' d hd with rfl | rfl | rfl
    exacts [rfl, h5, h6]
  have ambu : ∀ wq : Fin 13 → Label.{u}, S.{u}.rows.IsLawfulBelow (univ, 1) (fun d ↦ wq d) →
      ∀ d, cells.gradedIndex d ≤ ((univ : Finset (Fin 3)), 1) → wq d = lab (wq 0) ⊥ ⊥ d :=
    fun wq hq d hd ↦ by
      obtain ⟨h1, h5, h2, h6, h9⟩ := conditions_univ_one hq
      rcases bu1 d hd with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [rfl, h1, h2, h5, h6, h9]
  have l0 : ∀ C : Finset (Fin 3), (C = {0, 1} ∨ C = {0, 2}) →
      ∀ h : (({0} : Finset (Fin 3)), 1) ≤ (C, 1), S.{u}.rows.CappedLift h := by
    rintro C (rfl | rfl) h
    · refine cappedLift_one h (by decide) (fun wp hp ↦ ⟨(CellScheme.Rows.isLawfulBelow_iff_forall.mp
        hp).1 0 (show cells.gradedIndex 0 ≤ (({0} : Finset (Fin 3)), 1) by decide),
        fun d hd ↦ ?_⟩) fun wq hq ↦ (amb01 wq hq).2
      obtain rfl : d = 0 := by revert d; decide
      rfl
    · refine cappedLift_one h (by decide) (fun wp hp ↦ ⟨(CellScheme.Rows.isLawfulBelow_iff_forall.mp
        hp).1 0 (show cells.gradedIndex 0 ≤ (({0} : Finset (Fin 3)), 1) by decide),
        fun d hd ↦ ?_⟩) fun wq hq ↦ (amb02 wq hq).2
      obtain rfl : d = 0 := by revert d; decide
      rfl
  have l1 : ∀ h : (({1} : Finset (Fin 3)), 1) ≤ (({0, 1} : Finset (Fin 3)), 1),
      S.{u}.rows.CappedLift h := fun h ↦
    cappedLift_dead h (by decide) fun wq hq ↦ amb01 wq hq
  have l2 : ∀ h : (({2} : Finset (Fin 3)), 1) ≤ (({0, 2} : Finset (Fin 3)), 1),
      S.{u}.rows.CappedLift h := fun h ↦
    cappedLift_dead h (by decide) fun wq hq ↦ amb02 wq hq
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := 2) (b := 1) (mem_univ _)
    (mem_univ _) (by decide) (by decide) (by decide) (fun X Y hX hY h hYA ↦ ?_) ?_ ?_
  · -- lifts inside a coatom: first along the face at the grade of `X`, then within the face
    obtain ⟨B, j⟩ := X
    obtain ⟨C, k⟩ := Y
    obtain ⟨hB, hj0, hjB⟩ := hX
    obtain ⟨hC, -, -⟩ := hY
    obtain ⟨hBC, hjk⟩ := h
    refine (show S.{u}.rows.CappedLift (X := (B, j)) (Y := (C, j)) ⟨hBC, le_rfl⟩ from ?_).trans
      (CellScheme.Rows.cappedLift_of_fst_eq (X := (C, j)) (Y := (C, k)) ⟨Subset.rfl, hjk⟩ rfl)
    by_cases hBC' : B = C
    · subst hBC'; exact CellScheme.Rows.cappedLift_of_fst_eq _ rfl
    have hB0 : B ≠ ∅ := by rintro rfl; simp at hjB; omega
    have key : ∀ B ∈ plan3, ∀ C ∈ plan3, B ⊆ C → B ≠ C → C ≠ univ → B ≠ ∅ →
        (B = {0} ∧ (C = {0, 1} ∨ C = {0, 2})) ∨ (B = {1} ∧ C = {0, 1}) ∨
          (B = {2} ∧ C = {0, 2}) := by decide
    rcases key B hB C hC hBC hBC' hYA hB0 with ⟨rfl, hC'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact l0 C hC' _
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact l1 _
    · obtain rfl : j = 1 := by simp at hjB; omega
      exact l2 _
  · -- from the coatom `{0, 1}` to the full face
    intro j hj
    have hj' : j ≤ 2 := by simpa using hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact isWellFormed_cells.cappedLift _ (.inl rfl) _
    · refine cappedLift_one _ (by decide) (fun wp hp ↦ ?_) ambu
      obtain ⟨h1, h2, hv⟩ := conditions_face_one hp
      refine ⟨hv, fun d hd ↦ ?_⟩
      rcases b01' d hd with rfl | rfl | rfl
      exacts [rfl, h1.symm, h2.symm]
    · refine cappedLift_two _ 0 3 4 rfl rfl rfl (by decide) (by decide) (by decide)
        fun wp hp ↦ ?_
      obtain ⟨h1, h2, h30, h04, hv0, hv3, hv4⟩ := conditions_face_two hp
      refine ⟨isLawful_lab hv0 hv3 hv4 h30 h04, fun d hd ↦ ?_⟩
      rcases b01 d hd with rfl | rfl | rfl | rfl | rfl
      exacts [rfl, h1.symm, h2.symm, rfl, rfl]
  · -- from the coatom `{0, 2}` to the full face
    intro j hj
    have hj' : j ≤ 2 := by simpa using hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact isWellFormed_cells.cappedLift _ (.inl rfl) _
    · refine cappedLift_one _ (by decide) (fun wp hp ↦ ?_) ambu
      obtain ⟨h5, h6, hv⟩ := conditions_face_one' hp
      refine ⟨hv, fun d hd ↦ ?_⟩
      rcases b02' d hd with rfl | rfl | rfl
      exacts [rfl, h5.symm, h6.symm]
    · refine cappedLift_two _ 0 7 8 rfl rfl rfl (by decide) (by decide) (by decide)
        fun wp hp ↦ ?_
      obtain ⟨h5, h6, h70, h08, hv0, hv7, hv8⟩ := conditions_face_two' hp
      refine ⟨isLawful_lab hv0 hv7 hv8 h70 h08, fun d hd ↦ ?_⟩
      rcases b02 d hd with rfl | rfl | rfl | rfl | rfl
      exacts [rfl, h5.symm, h6.symm, rfl, rfl]

/-! ### The display, its faces, and the reading -/

/-- **The display**: `⊤` at the live cells, `⊥` at the dead ones. -/
noncomputable def E (α : Ordinal.{u}) : StageType.{u} α 3 where
  toScheme := S
  label := lab ⊤ ⊤ ⊤
  isWellFormed := ⟨rfl, isWellFormed_cells⟩
  isCoded := isCoded_S
  isLawful := isLawful_lab (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 2)
    le_rfl rfl
  atStage d := by unfold lab; split_ifs <;> simp

/-- **The display is legal.** -/
theorem isLegal_E (α : Ordinal.{u}) : (E α).IsLegal :=
  isLegal_iff.mpr ⟨isConsistent_S, isBountiful_S, isComplete_cells⟩

/-- A face of the display along `f` whose visible cells are enumerated by `e`, with the cells,
grades and kinds of `T α`, is `T α`, and its cells are those of `e`. -/
private theorem restrictFace_E_of (α : Ordinal.{u}) (f : Fin 2 ↪ Fin 3) (e : Fin 5 → Fin 13)
    (he : StrictMono e) (hf : univ.map f ∈ plan3)
    (hvis : ∀ d : Fin 13, cells.scope d ⊆ univ.map f ↔ d ∈ Set.range e)
    (hfaces : ∀ C : Finset (Fin 2), C.map f ∈ plan3 ↔ C ∈ Geometry.intervalPlan univ)
    (hscope : ∀ i : Fin 5, (cells.scope (e i)).preimage f f.injective.injOn =
      SeparationObstruction.cells.scope i)
    (hgrade : ∀ i : Fin 5, cells.grade (e i) = SeparationObstruction.cells.grade i)
    (hrow : ∀ c d : Fin 5, rowValue.{u} (e c) (e d) = SeparationObstruction.rowValue c d)
    (hlab : ∀ i : Fin 5, lab (⊤ : Label.{u}) ⊤ ⊤ (e i) = SeparationObstruction.lab ⊤ ⊤ ⊤ i) :
    ∃ h : restrictFace f (E α) = some (SeparationObstruction.T α),
      ∀ i : Fin 5, faceCell h i = e i := by
  have hr : ∀ d : Fin (E α).card, d ∈ Set.range (e : Fin 5 → Fin (E α).card) ↔
      d ∈ (E α).toScheme.visibleCells f := by
    intro d
    refine (hvis d).symm.trans ?_
    rw [Scheme.mem_visibleCells, ← Finset.coe_subset, Finset.coe_map, Finset.coe_univ,
      Set.image_univ]
    -- the scopes of the display are those of `cells`
    exact Iff.rfl
  have key : ∀ {i : Fin 5} {j : Fin ((E α).toScheme.comap f).card},
      (i : ℕ) = j → e i = (E α).toScheme.cellMap f j :=
    fun hij ↦ (E α).toScheme.cellMap_eq_of_strictMono f he hr hij
  have hcard : ((E α).toScheme.comap f).card = 5 :=
    (E α).toScheme.card_visibleCells_eq_of_strictMono f he hr
  have hmem : univ.map f ∈ (E α).toCellScheme.faces := hf
  have h : restrictFace f (E α) = some (SeparationObstruction.T α) := by
    rw [restrictFace_eq_some_iff]
    refine ⟨hmem, ?_⟩
    refine StageType.ext ?_ (fun i j hij ↦ ?_)
    · rw [StageType.comap_toScheme]
      refine Scheme.ext hcard ?_ ?_ (fun k i hki ↦ ?_) (fun k i hki ↦ ?_)
        (fun c c' t t' hc ht ↦ ?_)
      · rw [Scheme.comap_ground]
        ext x
        simp only [Finset.mem_preimage]
        -- the grounds are `univ`
        exact ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ Finset.mem_univ _⟩
      · ext C
        rw [Scheme.mem_comap_faces]
        exact hfaces C
      · rw [Scheme.comap_scope, ← key hki.symm]
        exact hscope i
      · rw [Scheme.comap_grade, ← key hki.symm]
        exact hgrade i
      · rw [Scheme.comap_row]
        -- the rows of the display are `rowValue`
        change rowValue ((E α).toScheme.cellMap f c) ((E α).toScheme.cellMap f t.1) = _
        rw [← key hc.symm, ← key ht.symm]
        exact hrow c' t'.1
    · -- the labels of the display are `lab ⊤ ⊤ ⊤`
      change lab ⊤ ⊤ ⊤ ((E α).toScheme.cellMap f i) = SeparationObstruction.lab ⊤ ⊤ ⊤ j
      rw [← key hij.symm]
      exact hlab j
  refine ⟨h, fun i ↦ ?_⟩
  -- the cell of a face is the cell map at its position
  unfold faceCell Scheme.faceCell
  exact (key rfl).symm

private theorem hrow_of_kind (e : Fin 5 → Fin 13) (hk : ∀ i, kind (e i) = ![1, 0, 1, 2, 3] i) :
    ∀ c d : Fin 5, rowValue.{u} (e c) (e d) = SeparationObstruction.rowValue c d := by
  intro c d
  fin_cases c <;> fin_cases d <;>
    simp [rowValue, lab, hk, SeparationObstruction.rowValue, L, H]

private theorem hlab_of_kind (e : Fin 5 → Fin 13) (hk : ∀ i, kind (e i) = ![1, 0, 1, 2, 3] i) :
    ∀ i : Fin 5, lab (⊤ : Label.{u}) ⊤ ⊤ (e i) = SeparationObstruction.lab ⊤ ⊤ ⊤ i := by
  intro i
  fin_cases i <;> simp [lab, hk, SeparationObstruction.lab]

/-- The enumeration of the cells on `{0, 1}`: `0`–`4`. -/
def e₁ : Fin 5 → Fin 13 := ![0, 1, 2, 3, 4]

/-- The enumeration of the cells on `{0, 2}`: `0`, `5`, `6`, `7`, `8`. -/
def e₂ : Fin 5 → Fin 13 := ![0, 5, 6, 7, 8]

/-- **The face of the display on `{0, 1}` is `T α`.** -/
theorem exists_restrictFace_castSuccEmb_E (α : Ordinal.{u}) :
    ∃ h : restrictFace (Fin.castSuccEmb : Fin 2 ↪ Fin 3) (E α) = some (SeparationObstruction.T α),
      ∀ i : Fin 5, faceCell h i = e₁ i := by
  have hk : ∀ i, kind (e₁ i) = ![1, 0, 1, 2, 3] i := by decide
  refine restrictFace_E_of α _ e₁ (Fin.strictMono_iff_lt_succ.mpr (by decide)) (by decide)
    (fun d ↦ ?_) (by decide) (fun i ↦ ?_) (by decide) (hrow_of_kind e₁ hk) (hlab_of_kind e₁ hk)
  · have key : ∀ d : Fin 13, cells.scope d ⊆ univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ↔
        ∃ i, e₁ i = d := by decide
    simpa [Set.mem_range] using key d
  · ext x
    rw [Finset.mem_preimage]
    revert i x
    decide

/-- **The face of the display on `{0, 2}`, the root `{0}` followed by the new point, is `T α`.** -/
theorem exists_restrictFace_extendByLast_E (α : Ordinal.{u}) :
    ∃ h : restrictFace (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) (E α) =
      some (SeparationObstruction.T α), ∀ i : Fin 5, faceCell h i = e₂ i := by
  have hk : ∀ i, kind (e₂ i) = ![1, 0, 1, 2, 3] i := by decide
  refine restrictFace_E_of α _ e₂ (Fin.strictMono_iff_lt_succ.mpr (by decide)) (by decide)
    (fun d ↦ ?_) (by decide) (fun i ↦ ?_) (by decide) (hrow_of_kind e₂ hk) (hlab_of_kind e₂ hk)
  · have key : ∀ d : Fin 13,
        cells.scope d ⊆ univ.map (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) ↔
          ∃ i, e₂ i = d := by decide
    simpa [Set.mem_range] using key d
  · ext x
    rw [Finset.mem_preimage]
    revert i x
    decide

/-- Two cells of one kind below a cell are read alike by it. -/
private theorem rowAt_E_congr (α : Ordinal.{u}) {c a b : Fin 13} (hk : kind a = kind b)
    (ha : cells.gradedIndex a ≤ cells.gradedIndex c)
    (hb : cells.gradedIndex b ≤ cells.gradedIndex c) :
    (E α).rowAt (c : Fin (E α).card) a = (E α).rowAt (c : Fin (E α).card) b := by
  rw [Scheme.rowAt_of_mem (show (a : Fin (E α).card) ∈ (E α).toCellScheme.below
      ((E α).toCellScheme.gradedIndex c) from ha),
    Scheme.rowAt_of_mem (show (b : Fin (E α).card) ∈ (E α).toCellScheme.below
      ((E α).toCellScheme.gradedIndex c) from hb)]
  -- the rows of the display are `rowValue`, which depends on the kind of the cell read
  change rowValue c a = rowValue c b
  unfold rowValue
  rw [lab_congr hk, lab_congr hk, lab_congr hk]

/-- **The display reads each new top of the donor face through the private top of its kind**, at
the input `T α` refuting separation through the lost top: one legal one-point coface of `T α`
with face `T α` along the root `{0}` followed by the new point, reading the new top `6` (`z`)
through `0` (`y`) at the grade `1`, and `7` (`o`), `8` (`r`) through `3`, `4` at the grade `2`. -/
theorem exists_readsEachNewTop_T (α : Ordinal.{u}) :
    ∃ (D' : StageType.{u} α 3) (hD' : D' ∈ (SeparationObstruction.T α).cofaces),
      restrictFace (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) D' =
        some (SeparationObstruction.T α) ∧
      ReadsEachNewTop hD'.2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∧
      ∀ j, D'.label j = ⊤ ∨ D'.label j = ⊥ := by
  obtain ⟨h₁, he₁⟩ := exists_restrictFace_castSuccEmb_E α
  obtain ⟨h₂, -⟩ := exists_restrictFace_extendByLast_E α
  refine ⟨E α, ⟨isLegal_E α, h₁⟩, h₂, fun x hx hxl hxt ↦ ?_, fun j ↦ ?_⟩
  swap
  · -- the labels of the display are `lab ⊤ ⊤ ⊤`
    change lab ⊤ ⊤ ⊤ j = ⊤ ∨ lab ⊤ ⊤ ⊤ j = ⊥
    unfold lab
    split_ifs <;> simp
  have hx' : cells.scope x ⊆ univ.map (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) := by
    rw [← Finset.coe_subset, Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact Scheme.mem_visibleCells.mp hx
  have hxk : kind x ≠ 0 := fun h0 ↦ by
    -- the labels of the display are `lab ⊤ ⊤ ⊤`
    change lab ⊤ ⊤ ⊤ x = ⊤ at hxt
    rw [lab_of_kind.1 h0] at hxt
    exact bot_ne_top hxt
  have key : ∀ x : Fin 13,
      cells.scope x ⊆ univ.map (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) →
        2 ∈ cells.scope x → kind x ≠ 0 → x = 6 ∨ x = 7 ∨ x = 8 := by decide
  have hu1 : ∀ u : Fin 13, cells.gradedIndex u = (univ, 1) → u = 9 := by decide
  have hu2 : ∀ u : Fin 13, cells.gradedIndex u = (univ, 2) → u = 10 ∨ u = 11 := by decide
  rcases key x hx' hxl hxk with rfl | rfl | rfl
  · refine ⟨SeparationObstruction.cellT α 0, SeparationObstruction.cellT α 0, rfl, rfl, le_rfl,
      le_rfl, fun u hu ↦ ?_⟩
    rw [he₁, hu1 u hu]
    exact (rowAt_E_congr α (c := 9) (a := 0) (b := 6) rfl (by decide) (by decide)).le
  · refine ⟨SeparationObstruction.cellT α 3, SeparationObstruction.cellT α 3, rfl, rfl, le_rfl,
      le_rfl, fun u hu ↦ ?_⟩
    rw [he₁]
    rcases hu2 u hu with rfl | rfl
    · exact (rowAt_E_congr α (c := 10) (a := 3) (b := 7) rfl (by decide) (by decide)).le
    · exact (rowAt_E_congr α (c := 11) (a := 3) (b := 7) rfl (by decide) (by decide)).le
  · refine ⟨SeparationObstruction.cellT α 4, SeparationObstruction.cellT α 4, rfl, rfl, le_rfl,
      le_rfl, fun u hu ↦ ?_⟩
    rw [he₁]
    rcases hu2 u hu with rfl | rfl
    · exact (rowAt_E_congr α (c := 10) (a := 4) (b := 8) rfl (by decide) (by decide)).le
    · exact (rowAt_E_congr α (c := 11) (a := 4) (b := 8) rfl (by decide) (by decide)).le

/-- **At the input refuting separation through the lost top, the donor is determined** over the
context along the root `{0}` within the receiving family of the display at every ordinal cutoff. -/
theorem isDeterminedWithin_T (α δ : Ordinal.{u}) :
    ∃ D' ∈ (SeparationObstruction.T α).cofaces,
      IsDeterminedWithin (receivingFamily D' δ) (SeparationObstruction.T α)
        (Fin.castSuccEmb : Fin 1 ↪ Fin 2) (SeparationObstruction.T α) := by
  obtain ⟨D', hD', hD'd, hrd, hlab⟩ := exists_readsEachNewTop_T α
  refine ⟨D', hD', hrd.isDeterminedWithin hD' hD'd fun j hj ↦ ?_⟩
  rw [(hlab j).resolve_left hj]
  exact WithBot.bot_lt_coe _

end VaughtConjecture.ReadingInstance
