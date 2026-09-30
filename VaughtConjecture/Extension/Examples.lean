/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CoatomAmalgam
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Examples: the amalgam of two one-point types, and a face that is not closed

Roadmap, Layer 3 (the coatom extension construction; the exact pinned extension, row 6 of the
table of 3.4, with its base cases); semantic contract, item 4 (absence of a face is mathematical
information).

**The amalgam of two one-point types.**  `point` is the legal stage type on one point carried by
the one-point scheme `Scheme.onePoint` (a single cell of grade `1`, mute rows) with the bottom
label.  The amalgam of `point` with itself over the empty face is a stage type on two points whose
faces along the two coatoms are literally `point`, whose rows are consistent and bountiful, and
which is not complete, hence not legal: it has no cell of full scope.

**The face must be closed.**  `bare` is the stage type on three points with no cells whose faces
form the interval plan on `Fin 3`; it is a copy of the private stage type of the same name in
`VaughtConjecture.Stage.Examples`, which has no public counterpart.  The pair `{0, 2}` is not an
interval, so no stage type on four points restricts to `bare` along `Fin.castSuccEmb` and has a
face along the extension of the embedding onto `{0, 2}` by the new point.

## References

The one-point types are those of [Kni26, Lemma 4.2.2], and the amalgam is
[Kni26, Definition 4.3.1].
-/

namespace VaughtConjecture.StageType

open Finset

/-! ### The amalgam of two one-point types -/

/-- The one-point stage type at stage `0`: the one-point scheme with the bottom label. -/
private noncomputable abbrev point : StageType.{0} 0 1 :=
  Scheme.isLegal_onePoint.toStageType 0

/-- The one-point stage type is legal. -/
private theorem isLegal_point : point.IsLegal :=
  Scheme.isLegal_onePoint.isLegal_toStageType 0

/-- The face of `point` on no points. -/
private theorem restrictFace_point :
    ∃ p, restrictFace (Coatom.face 0) point = some p :=
  Option.isSome_iff_exists.mp (point.isSome_restrictFace_of_zero _)

/-- The amalgam of `point` with itself over the empty face has the two literal faces `point`,
bountiful rows, and no cell of full scope, so it is not complete, and not legal. -/
private example : ∃ t : StageType.{0} 0 2,
    restrictFace Fin.castSuccEmb t = some point ∧
    restrictFace (extendByLast Fin.castSuccEmb) t = some point ∧
    t.rows.IsConsistent ∧ t.rows.IsBountiful ∧ ¬ t.toCellScheme.IsComplete ∧ ¬ t.IsLegal := by
  obtain ⟨p, hp⟩ := restrictFace_point
  exact ⟨Coatom.amalgamType hp hp, Coatom.restrictFace_left_amalgamType hp hp,
    Coatom.restrictFace_right_amalgamType hp hp,
    Coatom.isConsistent_amalgamType hp hp isLegal_point isLegal_point,
    Coatom.isBountiful_amalgamType hp hp isLegal_point isLegal_point,
    Coatom.not_isComplete_amalgamType hp hp, Coatom.not_isLegal_amalgamType hp hp⟩

/-! ### The face must be closed -/

/-- A stage type on three points with no cells, whose faces are the intervals of `Fin 3` (a copy
of the private `bare` of `VaughtConjecture.Stage.Examples`). -/
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

/-- Regression: the face must be closed.  No stage type on four points restricts to `bare` along
`Fin.castSuccEmb` and has a face along the extension of `outer` by the new point. -/
private example : ¬ ∃ Q : StageType.{0} 0 4, restrictFace Fin.castSuccEmb Q = some bare ∧
    (restrictFace (extendByLast outer) Q).isSome := by
  rintro ⟨Q, hQ, hQf⟩
  have h := univ_map_mem_faces_of_isSome_restrictFace_extendByLast hQ hQf
  exact absurd h (by decide)

end VaughtConjecture.StageType
