/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalMultiSchemeOriented
import VaughtConjecture.Extension.CanonicalMultiSchemeExamples
import VaughtConjecture.Extension.OrderedLayerExamples
import VaughtConjecture.Extension.ThinCompletionMirrorExamples
import VaughtConjecture.Extension.ThinCompletionTLTL

/-!
# The canonical multi-layer scheme with oriented rows at the compiled seeds

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: the
canonical multi-layer scheme has a step, with oriented copy rows, at the five seeds at which its
product clause fails; where oriented rows fail); semantic contract, items 2–4.

The canonical multi-layer scheme (`VaughtConjecture.Extension.CanonicalMultiScheme`) is defined
for every seed on five points; its product clause, a sufficient hypothesis for its step, fails at
the grades `2`, `3`, `4` for `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL`, for every copy rows
(`VaughtConjecture.Extension.CanonicalMultiSchemeCounterexample`).  The copy rows of this module
restrict the pairs instead: the oriented rows of the layer rows of an ordered-layer step
(`OrderedLayer.orientedRows`, `VaughtConjecture.Extension.CanonicalMultiSchemeOriented`), under
which the step of the family *is* the ordered-layer step (`Seed.canonicalMultiStep_oriented_iff`,
an exact reformulation: both copies of a grade read alike, so the family adds nothing to the layer
scheme).  The five seeds below were already completed by their ordered-layer steps
(`Seed.orderedLayerStep_seed4`, `…_seed5`, `…_seedL`, `…_seedLM`, `…_seedLL`); what is new here is
only that the canonical multi-layer scheme itself has a step at them.

**The orientations** (compiled): the layer rows of the ordered-layer steps of the five seeds are
oriented (`OrderedLayer.IsOriented`).

| seed | types | layer rows | oriented toward | theorem |
|---|---|---|---|---|
| `seed4` | `T4`, `T4` | `Seed4.layerRows4` | `D` | `OrderedLayer.isOriented_layerRows4` |
| `seed5` | `T5`, `T5` | `Seed5.rows5` | `D` | `OrderedLayer.isOriented_rows5` |
| `seedL` | `TL`, `T5` | `thinRows` | `D` | `OrderedLayer.isOriented_thinRows` |
| `seedLM` | `T5`, `TL` | `Mirror.rowsLM` | `C` | `OrderedLayer.isOriented_rowsLM` |
| `seedLL` | `TL`, `TL` | `SeedLL.rowsLL` | `D` | `OrderedLayer.isOriented_rowsLL` |

At `(univ, 1)` the rows of `seed4`, `seed5`, `seedL` read the parameter `A_C` at `1` and `A_D` at
`ω + 1`, those of `seedLM` read `A_D` at `1` and `A_C` at `ω + 1`, and those of `seedLL` read both
at `1`; at the grades `2`, `3`, `4` they read the full graded faces of the two coatoms at one value.

**The steps** (compiled): for every seed of the types of each row of the table, the canonical
multi-layer scheme with the oriented rows has the multi-layer step
(`Seed.canonicalMultiStep_oriented_of_T4`, `…_of_T5`, `…_of_TL_T5`, `…_of_T5_TL`, `…_of_TL_TL`),
each the ordered-layer step of that row transported through the iff.  So the five seeds have
completions below the full grade by the canonical multi-layer scheme
(`Seed.nonempty_completionBelowFullGrade_seed4_oriented` and its four companions), besides those
by their ordered-layer steps.  At the grade `4` the lifts come, through the layer scheme, from
those at the grade `3` (`OrderedLayer.cappedLift_four_of_oldCells` for `seed4`, `seed5`, `seedLM`,
`seedLL`, and the same argument in `VaughtConjecture.Extension.ThinCompletion` for `seedL`).

**Every compiled seed** (`Seed.hasCanonicalMultiStep_seed4_seed5_seedL_seedLM_seedLL_seedHG`): the
six seeds `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` (oriented rows) and `seedHG` (the rows of
the product clause below the top grade, `Seed.canonicalMultiStep_of_TH_TG`) each have a step of the
canonical multi-layer scheme for some copy rows.

**Where oriented rows fail** (compiled refutations of the oriented rows, not of the family and not
of a completion; each is a corollary, through the iff, of a refutation of the ordered-layer step):

* `seedHG`: no oriented layer rows give it a step of the family
  (`Seed.not_canonicalMultiStep_oriented_seedHG`, `Seed.not_hasOrientedLayerStep_seedHG`), since it
  has no ordered-layer step (`CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG`); the
  family has a step at it with other copy rows;
* `seedL` and `seedLM`: no oriented layer rows serve both
  (`Seed.not_exists_canonicalMultiStep_oriented_seedL_seedLM`), since no layer rows give both an
  ordered-layer step (`not_exists_orderedLayerStep_seedL_seedLM`): the orientation of the rows
  depends on the seed.

| seed | product clause at `2`, `3` | oriented layer step | step of the family |
|---|---|---|---|
| `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` | refuted (all rows) | holds | holds |
| `seedHG` | holds (`CanonicalHG.rowsHG`) | refuted (all rows) | holds |

So the canonical multi-layer scheme has a step at every compiled seed, and no seed refutes it; the
fibre product was refuted at the five seeds above and at the grade `4` of `seedHG`; oriented rows
are one choice of the copy rows, and neither of the two compiled sufficient clauses holds at every
compiled seed.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label OrderedLayer

namespace OrderedLayer

open ThinCompletion (thinRow thinKind)

/-- The rows of the thin completion at `(univ, 1)` read the parameter `A_C` below `A_D`. -/
private theorem gridPoint_one_le : gridPoint.{u} 1 0 ≤ gridPoint 1 1 :=
  gridPoint_le_gridPoint.mpr zero_le_one

/-- **The layer rows of the seeds of `T4` are oriented toward `D`.** -/
theorem isOriented_layerRows4 : IsOriented Seed4.layerRows4.{u} 1 where
  read k j hj1 hjk hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · obtain rfl : j = 1 := by omega
      exact congrArg (thinRow 1) (by decide)
    · obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
      · exact congrArg (thinRow 2) (by decide)
      · exact congrArg (thinRow 2) (by decide)
    · rfl
    · rfl
  le k i hk1 hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · fin_cases i
      · exact le_of_eq_of_le (congrArg (thinRow 1) (by decide : Seed4.kind4 (copyCoatom 0, 1) = 1))
          (le_of_le_of_eq gridPoint_one_le
            (congrArg (thinRow 1) (by decide : Seed4.kind4 (copyCoatom 1, 1) = 2)).symm)
      · exact le_rfl
    · exact (congrArg (thinRow 2) (by fin_cases i <;> decide)).le
    · exact le_rfl
    · exact le_rfl

/-- **The layer rows of the seeds of `T5` are oriented toward `D`.** -/
theorem isOriented_rows5 : IsOriented Seed5.rows5.{u} 1 where
  read k j hj1 hjk hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · obtain rfl : j = 1 := by omega
      exact congrArg (thinRow 1) (by decide)
    · obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
      · exact congrArg (thinRow 2) (by decide)
      · exact congrArg (thinRow 2) (by decide)
    · obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact congrArg Seed5.rowThree (by decide)
      · exact congrArg Seed5.rowThree (by decide)
      · exact congrArg Seed5.rowThree (by decide)
    · rfl
  le k i hk1 hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · fin_cases i
      · exact le_of_eq_of_le (congrArg (thinRow 1) (by decide : thinKind (copyCoatom 0, 1) = 1))
          (le_of_le_of_eq gridPoint_one_le
            (congrArg (thinRow 1) (by decide : thinKind (copyCoatom 1, 1) = 2)).symm)
      · exact le_rfl
    · exact (congrArg (thinRow 2) (by fin_cases i <;> decide)).le
    · exact (congrArg Seed5.rowThree (by fin_cases i <;> decide)).le
    · exact le_rfl

/-- **The ordered rows of the thin completion are oriented toward `D`.** -/
theorem isOriented_thinRows : IsOriented thinRows.{u} 1 where
  read k j hj1 hjk hk4 := by
    refine congrArg (thinRow k) ?_
    obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    all_goals decide
  le k i hk1 hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · fin_cases i
      · exact le_of_eq_of_le (congrArg (thinRow 1) (by decide : thinKind (copyCoatom 0, 1) = 1))
          (le_of_le_of_eq gridPoint_one_le
            (congrArg (thinRow 1) (by decide : thinKind (copyCoatom 1, 1) = 2)).symm)
      · exact le_rfl
    all_goals exact (congrArg (thinRow _) (by fin_cases i <;> decide)).le

/-- **The layer rows of the mirror seed are oriented toward `C`.** -/
theorem isOriented_rowsLM : IsOriented Mirror.rowsLM.{u} 0 where
  read k j hj1 hjk hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · obtain rfl : j = 1 := by omega
      exact congrArg (thinRow 1) (by decide)
    · obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
      · exact congrArg (thinRow 2) (by decide)
      · exact congrArg (thinRow 2) (by decide)
    · obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact congrArg (thinRow 3) (by decide)
      · exact congrArg (thinRow 3) (by decide)
      · exact congrArg (thinRow 3) (by decide)
    · rfl
  le k i hk1 hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · fin_cases i
      · exact le_rfl
      · exact le_of_eq_of_le
          (congrArg (thinRow 1) (by decide : Mirror.mirrorKind (copyCoatom 1, 1) = 1))
          (le_of_le_of_eq gridPoint_one_le
            (congrArg (thinRow 1) (by decide : Mirror.mirrorKind (copyCoatom 0, 1) = 2)).symm)
    · exact (congrArg (thinRow 2) (by fin_cases i <;> decide)).le
    · exact (congrArg (thinRow 3) (by fin_cases i <;> decide)).le
    · exact le_rfl

/-- **The layer rows of the seeds of `TL` with itself are oriented toward `D`** (they read the
parameters of grade `1` of the two coatoms at one value). -/
theorem isOriented_rowsLL : IsOriented SeedLL.rowsLL.{u} 1 where
  read k j hj1 hjk hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · obtain rfl : j = 1 := by omega
      exact congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by decide)
    · obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
      · exact congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by decide)
      · exact congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by decide)
    · obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by decide)
      · exact congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by decide)
      · exact congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by decide)
    · rfl
  le k i hk1 hk4 := by
    obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    · fin_cases i
      · exact (congrArg (ThinCompletion.kindLabel (gridPoint 1 0) (gridPoint 1 0) ⊥ ⊥ ⊥)
          (by decide : thinKind (copyCoatom 0, 1) = 1)).trans
          (congrArg (ThinCompletion.kindLabel (gridPoint 1 0) (gridPoint 1 0) ⊥ ⊥ ⊥)
            (by decide : thinKind (copyCoatom 1, 1) = 2)).symm |>.le
      · exact le_rfl
    · exact (congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by fin_cases i <;> decide)).le
    · exact (congrArg (ThinCompletion.kindLabel _ _ _ _ _) (by fin_cases i <;> decide)).le
    · exact le_rfl

end OrderedLayer

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

open TwoFaceLiftCounterexample (T4 seed4)
open CaseSplitCounterexample (T5 seed5)
open TwoFaceLiftExistsCounterexample (TL seedL)

/-! ### The steps -/

/-- **The canonical multi-layer scheme with oriented rows: seeds of `T4` with itself.** -/
theorem canonicalMultiStep_oriented_of_T4 (hIL : I.left = T4 α) (hIR : I.right = T4 α) :
    I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I Seed4.layerRows4)) :=
  canonicalMultiStep_of_orderedLayerStep (orderedLayerStep_of_T4 hIL hIR) isOriented_layerRows4

/-- **The canonical multi-layer scheme with oriented rows: seeds of `T5` with itself.** -/
theorem canonicalMultiStep_oriented_of_T5 (hIL : I.left = T5 α) (hIR : I.right = T5 α) :
    I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I Seed5.rows5)) :=
  canonicalMultiStep_of_orderedLayerStep (orderedLayerStep_of_T5 hIL hIR) isOriented_rows5

/-- **The canonical multi-layer scheme with oriented rows: seeds of `TL` and `T5`.** -/
theorem canonicalMultiStep_oriented_of_TL_T5 (hIL : I.left = TL α) (hIR : I.right = T5 α) :
    I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I thinRows)) :=
  canonicalMultiStep_of_orderedLayerStep (orderedLayerStep_thinRows hIL hIR) isOriented_thinRows

/-- **The canonical multi-layer scheme with oriented rows: seeds of `T5` and `TL`.** -/
theorem canonicalMultiStep_oriented_of_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α) :
    I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I Mirror.rowsLM)) :=
  canonicalMultiStep_of_orderedLayerStep (orderedLayerStep_of_T5_TL hIL hIR) isOriented_rowsLM

/-- **The canonical multi-layer scheme with oriented rows: seeds of `TL` with itself.** -/
theorem canonicalMultiStep_oriented_of_TL_TL (hIL : I.left = TL α) (hIR : I.right = TL α) :
    I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I SeedLL.rowsLL)) :=
  canonicalMultiStep_of_orderedLayerStep (orderedLayerStep_of_TL_TL hIL hIR) isOriented_rowsLL

/-! ### The five seeds -/

/-- **`seed4` has a completion below the full grade by the canonical multi-layer scheme**, with
the oriented rows of `Seed4.layerRows4`. -/
theorem nonempty_completionBelowFullGrade_seed4_oriented :
    Nonempty (CompletionBelowFullGrade (seed4 α)) :=
  (canonicalMultiStep_oriented_of_T4 rfl rfl).nonempty_completionBelowFullGrade

/-- **`seed5` has a completion below the full grade by the canonical multi-layer scheme**, with
the oriented rows of `Seed5.rows5`. -/
theorem nonempty_completionBelowFullGrade_seed5_oriented :
    Nonempty (CompletionBelowFullGrade (seed5 α)) :=
  (canonicalMultiStep_oriented_of_T5 rfl rfl).nonempty_completionBelowFullGrade

/-- **`seedL` has a completion below the full grade by the canonical multi-layer scheme**, with
the oriented rows of `thinRows`. -/
theorem nonempty_completionBelowFullGrade_seedL_oriented :
    Nonempty (CompletionBelowFullGrade (seedL α)) :=
  (canonicalMultiStep_oriented_of_TL_T5 rfl rfl).nonempty_completionBelowFullGrade

/-- **`seedLM` has a completion below the full grade by the canonical multi-layer scheme**, with
the oriented rows of `Mirror.rowsLM`. -/
theorem nonempty_completionBelowFullGrade_seedLM_oriented :
    Nonempty (CompletionBelowFullGrade (seedLM α)) :=
  (canonicalMultiStep_oriented_of_T5_TL rfl rfl).nonempty_completionBelowFullGrade

/-- **`seedLL` has a completion below the full grade by the canonical multi-layer scheme**, with
the oriented rows of `SeedLL.rowsLL`. -/
theorem nonempty_completionBelowFullGrade_seedLL_oriented :
    Nonempty (CompletionBelowFullGrade (seedLL α)) :=
  (canonicalMultiStep_oriented_of_TL_TL rfl rfl).nonempty_completionBelowFullGrade

/-- **Every compiled seed has a step of the canonical multi-layer scheme**: `seed4`, `seed5`,
`seedL`, `seedLM`, `seedLL` with oriented rows, and `seedHG` with the rows of the product clause
below the top grade. -/
theorem hasCanonicalMultiStep_seed4_seed5_seedL_seedLM_seedLL_seedHG :
    (seed4 α).HasCanonicalMultiStep ∧ (seed5 α).HasCanonicalMultiStep ∧
      (seedL α).HasCanonicalMultiStep ∧ (seedLM α).HasCanonicalMultiStep ∧
      (seedLL α).HasCanonicalMultiStep ∧
      (CrossedCouplingCounterexample.seedHG α).HasCanonicalMultiStep :=
  ⟨⟨_, canonicalMultiStep_oriented_of_T4 rfl rfl⟩, ⟨_, canonicalMultiStep_oriented_of_T5 rfl rfl⟩,
    ⟨_, canonicalMultiStep_oriented_of_TL_T5 rfl rfl⟩,
    ⟨_, canonicalMultiStep_oriented_of_T5_TL rfl rfl⟩,
    ⟨_, canonicalMultiStep_oriented_of_TL_TL rfl rfl⟩, ⟨_, canonicalMultiStep_of_TH_TG rfl rfl⟩⟩

/-! ### Where oriented rows fail -/

/-- **No oriented rows give `seedHG` a step of the canonical multi-layer scheme**: a corollary,
through `Seed.canonicalMultiStep_oriented_iff`, of
`CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG`.  This refutes the
oriented rows at `seedHG`, not the family: `seedHG` has a step of the family with other copy rows
(`Seed.canonicalMultiStep_of_TH_TG`). -/
theorem not_canonicalMultiStep_oriented_seedHG {ρ : LayerRows.{u}} {b : Fin 2}
    (hρ : IsOriented ρ b) :
    ¬ (CrossedCouplingCounterexample.seedHG α).MultiLayerStep canonicalMult
      (canonicalRows _ (orientedRows _ ρ)) := fun h ↦
  CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG
    ⟨ρ, (canonicalMultiStep_oriented_iff hρ).mp h⟩

/-- **`seedHG` has no oriented ordered-layer step**: a corollary of
`CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG`, forgetting the orientation. -/
theorem not_hasOrientedLayerStep_seedHG :
    ¬ (CrossedCouplingCounterexample.seedHG α).HasOrientedLayerStep := fun ⟨ρ, _, h, _⟩ ↦
  CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG ⟨ρ, h⟩

/-- **No oriented layer rows serve both `seedL` and `seedLM`**: a corollary, through
`Seed.canonicalMultiStep_oriented_iff`, of `not_exists_orderedLayerStep_seedL_seedLM` (no layer
rows, oriented or not, give both seeds an ordered-layer step).  So oriented rows are not uniform
in the seed. -/
theorem not_exists_canonicalMultiStep_oriented_seedL_seedLM :
    ¬ ∃ (ρ : LayerRows.{u}) (b b' : Fin 2), IsOriented ρ b ∧ IsOriented ρ b' ∧
      (seedL α).MultiLayerStep canonicalMult (canonicalRows _ (orientedRows _ ρ)) ∧
      (seedLM α).MultiLayerStep canonicalMult (canonicalRows _ (orientedRows _ ρ)) :=
  fun ⟨ρ, _, _, hρ, hρ', hL, hM⟩ ↦ not_exists_orderedLayerStep_seedL_seedLM α
    ⟨ρ, (canonicalMultiStep_oriented_iff hρ).mp hL, (canonicalMultiStep_oriented_iff hρ').mp hM⟩

end Seed

end VaughtConjecture
