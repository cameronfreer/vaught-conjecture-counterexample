/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Stage.Legal

/-!
# A stage type that is not legal, and a legal one

Roadmap, Layer 1 (countable stage types); semantic contract, item 3.

**Not legal.**  `bare` is a stage type on three points with no cells whose faces form the interval
plan on `Fin 3` (the stage type of the same name in `VaughtConjecture.Stage.Examples`).  It is a
stage type, but it is not legal: the graded face `({0}, 1)` is the graded index of no cell, so the
scheme is not complete (`not_isLegal_bare`).  A `StageType` alone is the unrestricted structure.

**Legal.**  `point` is the stage type on one point with a single cell of scope `{0}` and grade
`1`, the faces `∅` and `{0}`, mute rows, and the bottom label: the one-point scheme with the mute
semantics of [Kni26, Lemma 4.2.2].  Mute rows are consistent and bountiful, and the only graded
face is `({0}, 1)`, so it is legal (`isLegal_point`).

## References

R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026) [Kni26].
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

/-- `bare` is not legal: the graded face `({0}, 1)` is the graded index of no cell. -/
private theorem not_isLegal_bare : ¬ bare.IsLegal := fun h ↦ by
  obtain ⟨d, -⟩ := h.isComplete ({0}, 1) ⟨by decide, by decide, by decide⟩
  exact d.elim0

/-- The one-point stage type: a single cell of scope `{0}` and grade `1`, the faces `∅` and
`{0}`, mute rows, and the bottom label. -/
private def point : StageType.{0} 0 1 where
  card := 1
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩
  rows := CellScheme.Rows.mute _
  label _ := ⊥
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun _ ↦ by
    simp [CellScheme.gradedIndex]⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isLawful := CellScheme.Rows.isLawful_bot
  atStage _ := Label.atStage_bot

/-- The one-point stage type with mute rows is legal. -/
private theorem isLegal_point : point.IsLegal :=
  isLegal_iff.mpr ⟨CellScheme.Rows.isConsistent_mute, CellScheme.Rows.isBountiful_mute,
    fun ⟨C, j⟩ ⟨_, hpos, hle⟩ ↦ ⟨(0 : Fin 1), by
      have hC : #C ≤ 1 := card_le_univ C
      have hC' : C = univ := (card_eq_iff_eq_univ C).mp (by simp only at hpos hle ⊢; simp; omega)
      simp only at hpos hle
      ext <;> simp [CellScheme.gradedIndex, point, hC']
      omega⟩⟩

end VaughtConjecture.StageType
