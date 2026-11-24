/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Row

/-!
# Grafting a high tail onto a lawful labelling

Process rank `ω₁`, the finite span of mutual rigidity: a local lemma on lawful labellings.

**The graft.**  Let `x` and `y` be lawful below a pair `X`, let `c` be a cap self-visible at the
grade of `X`, and let `x` and `y` have the same **high set** `{d | c ≤ x d} = {d | c ≤ y d}`.  The
graft `z` equal to `x` at the low cells and to `y` at the high cells is lawful below `X`
(`CellScheme.Rows.GraftHighTailTarget`, to be proved as `Rows.IsLawfulBelow.graftHighTail`).  At
the cap `⊥` every cell is high and `z = y`.  The intended proof:

* order and availability: a low availability witness of `x` stays low or becomes high, and a high
  witness of `y` stays high;
* locality at a low owner is that of `x`, since every high cell is read at the owner's label;
* locality at a high owner `o` of grade `k`: capped decoders `θ_x`, `θ_y` at `o` with the step
  suppressor at `k` (`Scheme.exists_cappedDecoder_below`); with `b` the largest replacement
  `vr k k` of the row entries of the low cells below `o`, the map equal to `min θ_x c` up to `b`
  and to `max θ_y c` above `b` is monotone and commutes with visibility replacement through the
  grade `k`, and reads every cell below `o` as `z` capped at `z o`.  It need not be a witness
  above `k`: interpolation off the zero set of `θ_x` (`Label.exists_isWitness_interpolation`)
  gives a witness with the same readings, since the required readings have exactly the bottom
  pattern of `θ_x`.

Only the statement is given here.
-/

universe u a b

namespace VaughtConjecture.CellScheme.Rows

open Label

/-- **Target: grafting a high tail.**  Two labellings `x` and `y` lawful below `X` with the same
high set at a cap `c` self-visible at the grade of `X` give a lawful labelling below `X`: `y` at
the high cells and `x` at the others.  Stated. -/
def GraftHighTailTarget : Prop :=
  ∀ ⦃ι : Type a⦄ ⦃κ : Type b⦄ ⦃D : CellScheme ι κ⦄ (R : D.Rows.{u}) (X : Finset κ × ℕ)
    (x y : D.below X → Label.{u}) (c : Label.{u}), R.IsLawfulBelow X x → R.IsLawfulBelow X y →
    IsSelfVisible X.2 c → (∀ d, c ≤ x d ↔ c ≤ y d) →
      R.IsLawfulBelow X fun d ↦ if c ≤ x d then y d else x d

end VaughtConjecture.CellScheme.Rows
