/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform

/-!
# The top shifter and the step suppressors with a constant value

Roadmap, Layer 1 (the bounded transformations used by the construction); semantic contract,
item 3.

Two elementary witness components (`IsWitness`, module `VaughtConjecture.Label.Transform`), used
to show that explicit labellings are lawful:

* the *top shifter* `topShifter`, sending `⊥` to `⊥` and every other label to `⊤`; with every
  antitone suppressor whose values are self-visible at their grades it is a witness
  (`isWitness_topShifter`);
* the *step suppressor with value `a`* `constStepSuppressor K a`, equal to `a` at the grades
  `≤ K` and `⊥` above; it is antitone (`antitone_constStepSuppressor`), and its value at each
  grade `n` is self-visible at `n` when `a` is self-visible at `K`
  (`isSelfVisible_constStepSuppressor`).  The step suppressor `stepSuppressor K` is the case
  `a = ⊤`.
-/

universe u

namespace VaughtConjecture.Label

/-- The shifter sending `⊥` to `⊥` and every other label to `⊤`. -/
noncomputable def topShifter (x : Label.{u}) : Label.{u} := if x = ⊥ then ⊥ else ⊤

/-- The top shifter is a witness for every antitone suppressor whose values are self-visible at
their grades. -/
theorem isWitness_topShifter {g : ℕ → Label.{u}} (hg : Antitone g)
    (hgv : ∀ n, IsSelfVisible n (g n)) : IsWitness g topShifter where
  antitone := hg
  isSelfVisible := hgv
  map_bot := by simp [topShifter]
  monotone := by
    intro x y hxy
    unfold topShifter
    by_cases hx : x = ⊥
    · simp [hx]
    · have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
      simp [hx, hy]
  visibilityReplace_comm x k _ i _ := by
    unfold topShifter
    by_cases hx : x = ⊥
    · simp [hx]
    · simp [hx]

/-- The suppressor equal to `a` up to the grade `K` and `⊥` above. -/
noncomputable def constStepSuppressor (K : ℕ) (a : Label.{u}) (n : ℕ) : Label.{u} :=
  if n ≤ K then a else ⊥

/-- The step suppressor with value `a` is antitone. -/
theorem antitone_constStepSuppressor (K : ℕ) (a : Label.{u}) :
    Antitone (constStepSuppressor K a) := by
  intro n m hnm
  unfold constStepSuppressor
  split_ifs with hm hn <;> first | exact le_rfl | exact bot_le | omega

/-- The step suppressor with value `a` is self-visible at each grade when `a` is self-visible
at `K`. -/
theorem isSelfVisible_constStepSuppressor {K : ℕ} {a : Label.{u}} (ha : IsSelfVisible K a)
    (n : ℕ) : IsSelfVisible n (constStepSuppressor K a n) := by
  unfold constStepSuppressor
  split_ifs with hn
  · exact ha.mono hn
  · exact isSelfVisible_bot n

end VaughtConjecture.Label
