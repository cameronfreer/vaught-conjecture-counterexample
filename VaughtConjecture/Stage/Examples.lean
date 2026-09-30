/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Stage.Basic

/-!
# An undefined face with a defined subface

Roadmap, Layer 1 (exact partial face maps, preserving undefined faces); semantic contract, item 4
(absence of a face is mathematical information).

`bare` is a stage type on three points with no cells whose faces form the interval plan on
`Fin 3`.  The pair `{0, 2}` is not an interval, so the face map along the embedding `outer` onto it
is undefined (`restrictFace_outer`), while the face map along the composite with the embedding
onto `{0}` is defined (`isSome_restrictFace_first_trans_outer`).  Composition of face maps is
therefore guarded: it says nothing when the intermediate face is undefined.
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

end VaughtConjecture.StageType
