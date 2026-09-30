/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Bountiful

/-!
# A two-cell example

Roadmap, Layer 1 (zero/bottom cases); semantic contract, item 3.

`twoCells` is a concrete well-formed scheme on the one-point ground set `{0}` with two cells of the
same graded index `({0}, 1)`, illustrating physical multiplicities (`twoCells_gradedIndex`,
`twoCells_isWellFormed`); with the mute rows it is consistent and bountiful
(`Rows.isConsistent_mute`, `Rows.isBountiful_mute`).
-/

namespace VaughtConjecture.CellScheme

/-- A scheme on the ground set `{0}` with two cells, both of scope `{0}` and grade `1`. -/
private def twoCells : CellScheme (Fin 2) ℕ where
  ground := {0}
  faces := {∅, {0}}
  scope _ := {0}
  grade _ := 1

/-- The two cells of `twoCells` share their graded index. -/
private theorem twoCells_gradedIndex (d : Fin 2) : twoCells.gradedIndex d = ({0}, 1) := rfl

/-- `twoCells` is a well-formed scheme; its plan law is decided. -/
private theorem twoCells_isWellFormed : twoCells.IsWellFormed :=
  ⟨inferInstance, by decide, fun _ ↦ by simp [twoCells]⟩

end VaughtConjecture.CellScheme
