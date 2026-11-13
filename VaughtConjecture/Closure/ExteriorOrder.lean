/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.TwoGeneratorCardinality

/-!
# Closed sets above an infinite root and the exterior order (statements)

Let `c` be a closure operator on the finite subsets of `M` and `setClosure c` its
finite-character extension (InfinitaryLogic's `FiniteSupportClosure`).  This file states the
order-theoretic facts about closed sets of `setClosure c` that hold under **whole-hull
two-generation**, written inline as InfinitaryLogic writes it,
`∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S` (the hull of every finite input is the hull of at most two
of its points), and, where needed, finite anti-exchange:

* `ClosedSupersetsComparableTarget`: two closed sets containing a common infinite set are
  comparable by inclusion.
* `ClosedCutOrderTarget`: for an enumeration `z : I → M` of points outside an infinite set `B`,
  indexed by a partial order, whose lower cuts `B ∪ z '' Iic j` are all closed, membership of
  `z i` in the closure of `B` with `z j` added is `i ≤ j`.
* `ExteriorLinearOrderTarget`: above an infinite closed root `B`, the **exterior relation**
  "`x` lies in the closure of `B` with `y` added" is a linear order on the points outside `B`
  (`IsLinearOrder`, a `Prop`; no `LinearOrder` instance is declared).
* `ExteriorRootChangeTarget`, `RootBeforeExteriorTarget`: enlarging an infinite root `B` to a
  closed `D ⊇ B` does not change the closure of `D` with an outside point added, and puts every
  point of `D` strictly before every point outside `D` in the exterior relation of `B`.
* `CountableSetClosureTarget` (proved, `countableSetClosureTarget`, from InfinitaryLogic's
  `mk_setClosure_eq`; no generation hypothesis) and `CommonRootExteriorAgreementTarget`: the
  closure of a countable set is countable, and outside the closure of `B ∪ C`, for infinite `B`
  and `C`, the exterior relations of `B` and of `C` agree.

All targets are given-closure statements: they quantify over every closure operator satisfying
the hypotheses and assert no existence.  Except `CountableSetClosureTarget`, they are stated and
open.  No model theory is involved; the instances for the canonical closure of a realization are
in `VaughtConjecture.Realization.ClosureCardinality`.
-/

universe u v

namespace VaughtConjecture.Closure

open InfinitaryLogic.FiniteSupportClosure

/-! ### Comparability and closed cuts -/

/-- **Target: closed supersets of an infinite set are comparable.**  For a closure operator `c` on
the finite sets of `M` whose every hull is the hull of at most two of its points, two closed sets
containing a common infinite set are comparable by inclusion.  Anti-exchange is not a hypothesis.
Given-closure statement.  Stated; open. -/
def ClosedSupersetsComparableTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B C D : Set M⦄, B.Infinite → (setClosure c).IsClosed C → (setClosure c).IsClosed D →
      B ⊆ C → B ⊆ D → C ⊆ D ∨ D ⊆ C

/-- **Target: closed cuts recover the order of an exterior enumeration.**  Let `B` be infinite and
`z : I → M` injective with values outside `B`, indexed by any partial order `I`.  If every lower
cut `B ∪ z '' Iic j` is closed, then `z i` lies in the closure of `B` with `z j` added exactly when
`i ≤ j`.  Closedness of `B`, anti-exchange, linearity of `I` and exhaustion of `M` are not
hypotheses.  Given-closure statement.  Stated; open. -/
def ClosedCutOrderTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃I : Type v⦄ [PartialOrder I] ⦃B : Set M⦄ (z : I → M), B.Infinite →
      Function.Injective z → (∀ i, z i ∉ B) →
      (∀ j, (setClosure c).IsClosed (B ∪ z '' Set.Iic j)) →
        ∀ i j, z i ∈ setClosure c (insert (z j) B) ↔ i ≤ j

/-! ### The exterior order -/

/-- **Target: the exterior order above an infinite closed root is linear.**  Under two-generation
and anti-exchange of the finite hulls, for an infinite closed set `B`, the relation "`x` lies in
the closure of `B` with `y` added" is a linear order (reflexive, transitive, antisymmetric and
total) on the points outside `B`.  This is a `Prop`; no `LinearOrder` instance is declared.
Given-closure statement.  Stated; open. -/
def ExteriorLinearOrderTarget : Prop :=
  ∀ ⦃M : Type u⦄ [DecidableEq M] (c : ClosureOperator (Finset M)),
    (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    (∀ (S : Finset M) (x y : M), x ≠ y → x ∉ c S → x ∈ c (insert y S) → y ∉ c (insert x S)) →
      ∀ ⦃B : Set M⦄, (setClosure c).IsClosed B → B.Infinite →
        IsLinearOrder {x : M // x ∉ B} fun x y ↦ x.1 ∈ setClosure c (insert y.1 B)

/-! ### Changing the root -/

/-- **Target: changing the root.**  Let `B ⊆ D` with `B` infinite and `D` closed.  For a point `y`
outside `D`, the closure of `D` with `y` added is the closure of `B` with `y` added, so on the
points outside `D` the exterior relation of `D` is the restriction of that of `B`.  Closedness of
`B` and anti-exchange are not hypotheses.  Given-closure statement.  Stated; open. -/
def ExteriorRootChangeTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B D : Set M⦄, B.Infinite → (setClosure c).IsClosed D → B ⊆ D →
      ∀ ⦃y : M⦄, y ∉ D → setClosure c (insert y D) = setClosure c (insert y B)

/-- **Target: the enlarged root comes first.**  Let `B ⊆ D` with `B` infinite and `D` closed.  In
the exterior relation of `B`, every point of `D` lies strictly before every point outside `D`: it
lies in the closure of `B` with the outside point added, and the outside point does not lie in the
closure of `B` with it added.  Given-closure statement.  Stated; open. -/
def RootBeforeExteriorTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B D : Set M⦄, B.Infinite → (setClosure c).IsClosed D → B ⊆ D →
      ∀ ⦃x y : M⦄, x ∈ D → y ∉ D →
        x ∈ setClosure c (insert y B) ∧ y ∉ setClosure c (insert x B)

/-! ### A countable common root -/

/-- **Target: the closure of a countable set is countable.**  No generation hypothesis: the
closure of a finite set is a finite hull, and closing an infinite set keeps its cardinality
(InfinitaryLogic's `mk_setClosure_eq`).  Given-closure statement.  Proved
(`Closure.countableSetClosureTarget`). -/
def CountableSetClosureTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)) ⦃A : Set M⦄, A.Countable →
    (setClosure c A).Countable

/-- **The closure of a countable set is countable**, the target form. -/
theorem countableSetClosureTarget : CountableSetClosureTarget.{u} := by
  intro M c A hA
  rcases A.finite_or_infinite with hfin | hinf
  · lift A to Finset M using hfin
    rw [setClosure_finset]
    exact (c A).countable_toSet
  · rw [← Cardinal.le_aleph0_iff_set_countable, mk_setClosure_eq c hinf]
    exact Cardinal.le_aleph0_iff_set_countable.mpr hA

/-- **Target: exterior relations agree outside a common root.**  For infinite `B` and `C` and a
point `y` outside the closure of `B ∪ C`, a point lies in the closure of `B` with `y` added exactly
when it lies in the closure of `C` with `y` added.  With `CountableSetClosureTarget`, for countable
`B` and `C` the closure of `B ∪ C` is a countable closed common root above which the two exterior
relations coincide.  Given-closure statement.  Stated; open. -/
def CommonRootExteriorAgreementTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B C : Set M⦄, B.Infinite → C.Infinite → ∀ ⦃y : M⦄, y ∉ setClosure c (B ∪ C) →
      ∀ x : M, x ∈ setClosure c (insert y B) ↔ x ∈ setClosure c (insert y C)

end VaughtConjecture.Closure
