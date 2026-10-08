/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Witness

/-!
# Strict inequalities under transformations (work file for `h3`)

Work file (placement later), for a tightened admission at a cap below the top grade.  A class
condition `s x < s w` is closed backward under a transformation `d ↦ min (σ (s d)) (g (grade d))`
when `grade x ≤ grade w` (the suppressor is antitone), and not otherwise.  Compiled in this
repository (theorem named):

* **Backward closure** (`Label.lt_of_transform_lt`): for a witness `(g, σ)` and
  `grade x ≤ grade w`, `min (σ a) (g (grade x)) < min (σ b) (g (grade w))` gives `a < b`.
* **Its failure in the other direction** (`Label.not_lt_of_transform_lt_step`): with the step
  suppressor at `1` and the identity, a cell of grade `2` read `1` and a cell of grade `1` read `1`
  are transformed to `⊥ < 1`, while `¬ 1 < 1`.  The same splice is the downward clause of the
  engine (`ProfileTower.hat` at a grade below the cell).  So the strict inequalities `s a < s y`
  for a cell `a` of the common face of grade at least `N` and a top `y` of grade below `N` are not
  closed backward under the witnesses the engine uses.
-/

universe u

namespace VaughtConjecture

namespace Label

/-- **Strict inequalities are closed backward under a transformation when the first cell has the
smaller grade.** -/
theorem lt_of_transform_lt {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    {a b : Label.{u}} {i j : ℕ} (hij : i ≤ j) (h : min (σ a) (g i) < min (σ b) (g j)) : a < b := by
  by_contra hab
  rw [not_lt] at hab
  exact absurd h (not_lt.mpr (min_le_min (hw.monotone hab) (hw.antitone hij)))

/-- **Strict inequalities are not closed backward when the first cell has the larger grade**: the
step suppressor at `1` with the identity sends a value `1` at a grade `2` to `⊥` and a value `1` at
the grade `1` to `1`. -/
theorem not_lt_of_transform_lt_step :
    min (id (1 : Label.{u})) (stepSuppressor.{u} 1 2) <
        min (id (1 : Label.{u})) (stepSuppressor.{u} 1 1) ∧
      IsWitness (stepSuppressor.{u} 1) id ∧ ¬ (1 : Label.{u}) < 1 := by
  refine ⟨?_, IsWitness.id_step 1, lt_irrefl _⟩
  rw [stepSuppressor_of_lt (by norm_num), stepSuppressor_of_le le_rfl, min_bot_right,
    min_top_right]
  exact WithBot.bot_lt_coe _

end Label

end VaughtConjecture
