/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanAdmission
import VaughtConjecture.Stage.Legal

/-!
# The one-sided capped lift of two-sided states

Process rank `ω₁`, the finite span of mutual rigidity: the state step of the master levels.

**States.**  For a scheme `S` on `n` points (the common scheme of the two types), a **state** is a
labelling `P` of the fields `Fin S.card ⊕ Fin S.card` (`VaughtConjecture.ProcessRank`): the left
copy `Sum.inl d` and the right copy `Sum.inr d` of every cell.  The copy on the side `b`
(`ProcessRank.sideField`) is the left copy for `false` and the right copy for `true`.  A state is
**lawful at the grade `k`** (`ProcessRank.IsStateLawfulAt`) when both of its sides are lawful below
the pure cut `(univ, k)` of `S`.  The fields of grade above `k` are kept in the state and read by
the admission predicate; they are only required to be self-visible at the grade one.

**The one-sided capped lift** (`ProcessRank.OneSidedStateLiftTarget`).  Let `S` be legal, `T` a
set of cells of grade at most `K`, `P` a state lawful and admitted at the grade `k` with every value
self-visible at the grade one, `c` a cap self-visible at `k`, and `r` lawful below a graded face
`X ≤ (univ, k)` of `S`, agreeing capped at `c` with the side `b` of `P`.  Then some state `P'`,
lawful and admitted at `k` with every value self-visible at the grade one, equals `r` on the side
`b` below `X` and agrees with `P` capped at `c` at **every** field, those above the cut included.
The intended proof extends `r` on its side to the pure cut by bountifulness and chooses the other
side by three cases (for `k ≥ K`; below `K` the other side is kept):

1. `m(P) ≥ c`: cap the other side at `c`, its fields of higher grade included; an undesignated
   field at least `c` on one side and the capped designated fields on the other make the state
   inactive;
2. `m(P) < c` and `P` inactive: keep the other side; the low designated field witnessing
   inactivity and every low field are fixed by the cap agreement;
3. `m(P) < c` and `P` separated: both sides have the same high set (all designated fields
   matched in `P`, all undesignated fields low), and the high tail of the prescribed side is
   grafted onto the other side (`CellScheme.Rows.GraftHighTailTarget`); designated fields above the
   grade `k` do not occur since `k ≥ K`.

No prescription is made on both sides at once.  Only the statement is given here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label

variable {ι : Type*}

/-- The copy of a cell on the side `b`: the left copy for `false`, the right copy for `true`. -/
def sideField (b : Bool) (d : ι) : ι ⊕ ι := bif b then Sum.inr d else Sum.inl d

variable {n : ℕ}

/-- A state is **lawful at the grade `k`**: both of its sides are lawful below the pure cut
`(univ, k)`. -/
def IsStateLawfulAt (S : Scheme.{u} n) (k : ℕ) (P : Fin S.card ⊕ Fin S.card → Label.{u}) : Prop :=
  ∀ b : Bool, S.rows.IsLawfulBelow ((univ : Finset (Fin n)), k) fun d ↦ P (sideField b d)

/-- **Target: the one-sided capped lift of admitted states.**  For a legal scheme, a set `T` of
cells of grade at most `K`, a state `P` lawful and admitted at the grade `k` with every value
self-visible at the grade one, a cap `c` self-visible at `k`, and a labelling `r` lawful below a
graded face `X ≤ (univ, k)` agreeing capped at `c` with the side `b` of `P`, some state lawful and
admitted at `k`, with every value self-visible at the grade one, is `r` on the side `b` below `X`
and agrees with `P` capped at `c` at every field.  Stated. -/
def OneSidedStateLiftTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (S : Scheme.{u} n), S.IsLegal → ∀ (T : Set (Fin S.card)) (K k : ℕ),
    (∀ d ∈ T, S.toCellScheme.grade d ≤ K) → ∀ (b : Bool) (X : Finset (Fin n) × ℕ),
    X ∈ S.toCellScheme.gradedFaces → X ≤ ((univ : Finset (Fin n)), k) →
    ∀ (c : Label.{u}) (P : Fin S.card ⊕ Fin S.card → Label.{u})
      (r : S.toCellScheme.below X → Label.{u}),
      IsSelfVisible k c → IsStateLawfulAt S k P → (∀ x, IsSelfVisible 1 (P x)) →
      IsAdmitted T K k P → S.rows.IsLawfulBelow X r →
      (∀ d : S.toCellScheme.below X, min (P (sideField b d.1)) c = min (r d) c) →
      ∃ P' : Fin S.card ⊕ Fin S.card → Label.{u}, IsStateLawfulAt S k P' ∧
        (∀ x, IsSelfVisible 1 (P' x)) ∧ IsAdmitted T K k P' ∧
        (∀ d : S.toCellScheme.below X, P' (sideField b d.1) = r d) ∧
        ∀ x, min (P' x) c = min (P x) c

end VaughtConjecture.ProcessRank
