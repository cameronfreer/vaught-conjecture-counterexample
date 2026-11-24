/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CappedDecoder

/-!
# Grafting a high tail onto a lawful labelling

Process rank `ω₁`, the finite span of mutual rigidity: a local lemma on lawful labellings.

**The graft.**  Let `S` be a scheme (finitely many cells, indexed by `Fin S.card`), let `x` and
`y` be labellings of its cells lawful below a pair `X`, let `c` be a cap self-visible at the grade
of `X`, and let `x` and `y` have the same **high set** below `X`: `c ≤ x d ↔ c ≤ y d` for every
cell `d` below `X`.  The graft `z` equal to `x` at the low cells and to `y` at the high cells is
lawful below `X` (`Scheme.GraftHighTailTarget`).  The statement is for schemes, whose cells are
finite in number: the proof takes the largest of finitely many low readings and uses the capped
decoder of a scheme (`Scheme.exists_cappedDecoder_below`).  At
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

universe u

namespace VaughtConjecture.Scheme

open Label

/-- **Target: grafting a high tail.**  For a scheme `S`, two labellings `x` and `y` of its cells
lawful below `X` with the same high set below `X` at a cap `c` self-visible at the grade of `X`
give a labelling lawful below `X`: `y` at the high cells and `x` at the others.  Stated. -/
def GraftHighTailTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (S : Scheme.{u} n) (X : Finset (Fin n) × ℕ) (x y : Fin S.card → Label.{u})
    (c : Label.{u}), S.rows.IsLawfulBelow X (fun d ↦ x d) → S.rows.IsLawfulBelow X (fun d ↦ y d) →
    IsSelfVisible X.2 c → (∀ d ∈ S.toCellScheme.below X, c ≤ x d ↔ c ≤ y d) →
      S.rows.IsLawfulBelow X fun d ↦ if c ≤ x d then y d else x d

end VaughtConjecture.Scheme
