/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Stage.Basic

/-!
# An undefined face with a defined subface; reduction at a successor stage

Roadmap, Layer 1 (exact partial face maps, preserving undefined faces; stage-reduction
coherence); semantic contract, item 4 (absence of a face is mathematical information).

**An undefined face with a defined subface.**  `bare` is a stage type on three points with no
cells whose faces form the interval plan on `Fin 3`.  The pair `{0, 2}` is not an interval, so the
face map along the embedding `outer` onto it is undefined (`restrictFace_outer`), while the face
map along the composite with the embedding onto `{0}` is defined
(`isSome_restrictFace_first_trans_outer`).  Composition of face maps is therefore guarded: it says
nothing when the intermediate face is undefined.

**Reduction at a successor stage.**  `succ` is a stage type at stage `3` on two points with two
cells, of scopes `{0}` and `{0, 1}` and grades `1` and `2`, whose rows take the value `1` at the
first cell and `2` at the second, and with labels `1` and `2`.  Its section is lawful, but its
reduction to the successor stage `2` (the labels `1` and `⊤`) is not
(`not_isLawful_reduce_two_succ`): stage reduction of lawful sections needs a stage that is zero or
a limit, and the hypothesis of `CellScheme.Rows.IsLawful.reduce` is necessary.
-/

namespace VaughtConjecture.StageType

open Finset

/-- A stage type on three points with no cells, whose faces are the intervals of `Fin 3`. -/
private def bare : StageType.{0} 0 3 where
  card := 0
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, Fin.elim0, Fin.elim0⟩
  rows := ⟨fun s ↦ s.elim0⟩
  label := Fin.elim0
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ d.elim0⟩⟩
  isCoded s := s.elim0
  isLawful := CellScheme.Rows.isLawful_of_isEmpty _
  atStage d := d.elim0

/-- The embedding of two points onto the pair `{0, 2}`. -/
private def outer : Fin 2 ↪ Fin 3 :=
  ⟨fun i ↦ ⟨2 * i, by omega⟩, fun a b h ↦ Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The embedding of one point onto the first of two points. -/
private def first : Fin 1 ↪ Fin 2 :=
  ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

/-- The pair `{0, 2}` is not an interval: the face map along `outer` is undefined. -/
private theorem restrictFace_outer : restrictFace outer bare = none := by
  rw [restrictFace_eq_none_iff]
  decide

/-- The subface `{0}` of the undefined face `{0, 2}` is defined. -/
private theorem isSome_restrictFace_first_trans_outer :
    (restrictFace (first.trans outer) bare).isSome := by
  rw [isSome_restrictFace_iff]
  decide

/-- Every natural number lies below `ω ^ 2`. -/
private theorem natCast_lt_omega0_sq (n : ℕ) : (n : Ordinal.{0}) < Ordinal.omega0 ^ 2 := by
  rw [pow_two]
  exact (Ordinal.natCast_lt_omega0 n).trans_le (Ordinal.le_mul_left _ Ordinal.omega0_pos)

/-- The cell scheme on two points with the cells `({0}, 1)` and `({0, 1}, 2)`, whose faces are the
intervals. -/
private def succCells : CellScheme (Fin 2) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, univ], ![1, 2]⟩

/-- The rows of `succCells`: the value `1` at the first cell and `2` at the second. -/
private noncomputable def succRows : succCells.Rows.{0} :=
  ⟨fun _ t ↦ if t.1 = 0 then 1 else 2⟩

/-- The labels `1` and `2` of the two cells. -/
private def succLabel : Fin 2 → Label.{0} := ![1, 2]

/-- The labels `1` and `2` are lawful for `succRows`. -/
private theorem isLawful_succLabel : succRows.IsLawful succLabel where
  orderly d := by fin_cases d <;> simp [succLabel, succCells]
  locality s := by
    refine ⟨fun _ ↦ ⊤, id, Label.IsWitness.id_top, fun d ↦ ?_⟩
    obtain ⟨d, hd⟩ := d
    fin_cases s <;> fin_cases d
    · simp [succRows, succLabel]
    · exfalso
      have := (CellScheme.mem_below _).mp hd
      simp [succCells, CellScheme.gradedIndex, Prod.le_def] at this
    · simp [succRows, succLabel]
    · simp [succRows, succLabel]
  availability s t hst hg := by
    refine ⟨t, rfl, ?_⟩
    fin_cases s <;> fin_cases t <;> simp_all [succLabel, succCells]

/-- A stage type at stage `3` on two points with the cells `({0}, 1)` and `({0, 1}, 2)`, rows taking
the value `1` at the first cell and `2` at the second, and the labels `1` and `2`. -/
private noncomputable def succ : StageType.{0} 3 2 where
  card := 2
  toCellScheme := succCells
  rows := succRows
  label := succLabel
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, by
    intro d; fin_cases d <;> simp [succCells, CellScheme.gradedIndex, Geometry.mem_intervalPlan]⟩⟩
  isCoded s t := by
    dsimp only [succRows]
    split_ifs
    · exact WithBot.coe_lt_coe.mpr
        (WithTop.coe_lt_coe.mpr (by exact_mod_cast natCast_lt_omega0_sq 1))
    · exact WithBot.coe_lt_coe.mpr
        (WithTop.coe_lt_coe.mpr (by exact_mod_cast natCast_lt_omega0_sq 2))
  isLawful := isLawful_succLabel
  atStage d := by
    fin_cases d
    · simp [succLabel]
    · simp only [succLabel, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Label.atStage_ofNat]
      exact_mod_cast (by norm_num : 2 < 3)

/-- **Reduction at a successor stage**: the reduction of the section of `succ` (the labels
`succLabel` for the rows `succRows`) to the successor stage `2` is not lawful, so stage reduction
of lawful sections needs a stage that is zero or a limit. -/
private theorem not_isLawful_reduce_two_succ :
    ¬ succRows.IsLawful (Label.reduce 2 ∘ succLabel) := by
  intro h
  obtain ⟨g, σ, hw, heq⟩ := h.locality 1
  have ha : (0 : Fin 2) ∈ succCells.below (succCells.gradedIndex 1) := by
    simp [succCells, CellScheme.gradedIndex, Prod.le_def]
  have h1 := heq ⟨0, ha⟩
  have h2 := heq ⟨1, succCells.mem_below_gradedIndex 1⟩
  have r1 : Label.reduce (2 : Ordinal.{0}) (1 : Label.{0}) = 1 :=
    Label.reduce_of_lt (by exact_mod_cast (show (1 : Ordinal.{0}) < 2 by norm_num))
  have r2 : Label.reduce (2 : Ordinal.{0}) (2 : Label.{0}) = ⊤ := Label.reduce_of_le le_rfl
  simp only [Function.comp_apply, succLabel, succRows, succCells, Matrix.cons_val_zero,
    Matrix.cons_val_one, r1, r2, min_top_right] at h1 h2
  simp only [↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one] at h1 h2
  -- `h1 : 1 = min (σ 1) (g 1)` and `h2 : ⊤ = min (σ 2) (g 2)`
  have hg2 : g 2 = ⊤ := top_le_iff.mp (h2.le.trans (min_le_right _ _))
  have hσ2 : σ 2 = ⊤ := top_le_iff.mp (h2.le.trans (min_le_left _ _))
  have hg1 : g 1 = ⊤ := top_le_iff.mp (hg2 ▸ hw.antitone (by norm_num : 1 ≤ 2))
  rw [hg1, min_top_right] at h1
  have key := hw.visibilityReplace_comm 1 2 (by rw [← h1, hg2]; exact le_top) 2 le_rfl
  rw [← h1, (by simp : Label.visibilityReplace 2 2 (1 : Label.{0}) = 2), hσ2] at key
  exact Label.not_isProper_top (key ▸ Label.isProper_ofNat 2)

end VaughtConjecture.StageType
