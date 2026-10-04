/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Realization.GateRecovery

/-!
# The bottom pattern tests the gate and not the apex

`pair` is a stage type at stage `0` on `n + 1 = 2` points with two cells: one of graded index
`(univ, n) = (univ, 1)`, that of a gate, and one of graded index `(univ, n + 1) = (univ, 2)`, that
of an apex.  Its rows and labels are bottom.  The bottom-pattern family of a labelling tests the
first cell and not the second:

* `pair` is not in the bottom-pattern family of a labelling that is not bottom at the cell of
  grade `1` (`notMem_bottomPatternFamily_top_bot`, by
  `StageType.label_ne_bot_of_mem_bottomPatternFamily`): a gate that the labelling does not make
  bottom is not bottom in any member;
* `pair` is in the bottom-pattern family of a labelling that is bottom at the cell of grade `1` and
  not at the cell of grade `2`, where its own label is bottom (`mem_bottomPatternFamily_bot_top`):
  a cell of grade `n + 1` is not tested.

No gated extension is exhibited here: a gated extension is legal, and its construction is the
gated pinned extension property, a hypothesis still to be proved.
-/

namespace VaughtConjecture.StageType.GateRecoveryExamples

open Finset

/-- The cell scheme on two points with the cells `(univ, 1)` and `(univ, 2)`, whose faces are the
intervals. -/
def pairCells : CellScheme (Fin 2) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, ![1, 2]⟩

/-- The stage type at stage `0` on `pairCells` with bottom rows and bottom labels. -/
noncomputable def pair : StageType.{0} 0 2 where
  card := 2
  toCellScheme := pairCells
  rows := CellScheme.Rows.bot _
  label _ := ⊥
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, by
    intro d; fin_cases d <;> simp [pairCells, CellScheme.gradedIndex]⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isLawful := CellScheme.Rows.isLawful_const_bot
  atStage _ := Label.atStage_bot

/-- The cell of grade `n = 1` is tested: `pair`, bottom there, is not in the bottom-pattern family
of a labelling that is not bottom there. -/
theorem notMem_bottomPatternFamily_top_bot :
    pair ∉ bottomPatternFamily pair.toScheme ![⊤, ⊥] := fun h ↦
  label_ne_bot_of_mem_bottomPatternFamily h (0 : Fin 2) (0 : Fin 2) rfl
    (by simp [pair, pairCells]) (by simp) rfl

/-- The cell of grade `n + 1 = 2` is not tested: `pair` is in the bottom-pattern family of a
labelling that is not bottom there, while its own label there is bottom. -/
theorem mem_bottomPatternFamily_bot_top :
    pair ∈ bottomPatternFamily pair.toScheme ![⊥, ⊤] ∧ pair.label (1 : Fin 2) = ⊥ := by
  refine ⟨⟨rfl, fun i j hij hgr ↦ ?_⟩, rfl⟩
  obtain rfl := Fin.ext hij
  fin_cases i
  · simp [pair]
  · simp [pair, pairCells] at hgr

end VaughtConjecture.StageType.GateRecoveryExamples
