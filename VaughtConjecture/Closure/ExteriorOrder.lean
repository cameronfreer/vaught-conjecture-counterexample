/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.TwoGeneratorCardinality

/-!
# Closed sets above an infinite root and the exterior order

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
the hypotheses and assert no existence.  All are proved, each by the theorem of the same name in
lower camel case.  Comparability comes from InfinitaryLogic's pair lemma
`mem_pair_of_two_exclusions`; the other order facts follow from comparability, from closedness of
the cuts or of the enlarged root, and, for antisymmetry of the exterior relation, from
`setClosure_antiExchange`.  No model theory is involved; the instances for the canonical closure of
a realization are in `VaughtConjecture.Realization.ClosureCardinality`.
-/

universe u v

namespace VaughtConjecture.Closure

open InfinitaryLogic.FiniteSupportClosure

section Insert

variable {M : Type u} {c : ClosureOperator (Finset M)} {B : Set M} {x y : M}

/-- A point lies in the closure of `B` with it added. -/
theorem mem_setClosure_insert_self : y ∈ setClosure c (insert y B) :=
  (setClosure c).le_closure _ (Set.mem_insert y B)

/-- `B` lies in the closure of `B` with a point added. -/
theorem subset_setClosure_insert : B ⊆ setClosure c (insert y B) :=
  (Set.subset_insert y B).trans ((setClosure c).le_closure _)

/-- If `x` lies in the closure of `B` with `y` added, then so does the closure of `B` with `x`
added. -/
theorem setClosure_insert_subset_of_mem (h : x ∈ setClosure c (insert y B)) :
    setClosure c (insert x B) ⊆ setClosure c (insert y B) :=
  ClosureOperator.closure_min (Set.insert_subset h subset_setClosure_insert)
    ((setClosure c).isClosed_closure _)

end Insert

/-! ### Comparability and closed cuts -/

/-- **Target: closed supersets of an infinite set are comparable.**  For a closure operator `c` on
the finite sets of `M` whose every hull is the hull of at most two of its points, two closed sets
containing a common infinite set are comparable by inclusion.  Anti-exchange is not a hypothesis.
Given-closure statement.  Proved
(`Closure.closedSupersetsComparableTarget`). -/
def ClosedSupersetsComparableTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B C D : Set M⦄, B.Infinite → (setClosure c).IsClosed C → (setClosure c).IsClosed D →
      B ⊆ C → B ⊆ D → C ⊆ D ∨ D ⊆ C

/-- **Closed supersets of an infinite set are comparable**, the target form.  Points `x ∈ C \ D`
and `y ∈ D \ C` would put every `b ∈ B` into the finite hull of `{x, y}`: the hull of `{y, b}`
lies in `D` and misses `x`, the hull of `{x, b}` lies in `C` and misses `y`, so
`mem_pair_of_two_exclusions` applies. -/
theorem closedSupersetsComparableTarget : ClosedSupersetsComparableTarget.{u} := by
  intro M c hgen B C D hB hC hD hBC hBD
  classical
  by_contra h
  obtain ⟨x, hxC, hxD⟩ := Set.not_subset.mp fun hCD ↦ h (Or.inl hCD)
  obtain ⟨y, hyD, hyC⟩ := Set.not_subset.mp fun hDC ↦ h (Or.inr hDC)
  refine hB ((c {x, y}).finite_toSet.subset fun b hb ↦ ?_)
  refine mem_pair_of_two_exclusions c hgen (fun hx ↦ hxD ?_) (fun hy ↦ hyC ?_)
  · exact (setClosure_closed_iff c D).mp hD {y, b}
      (by simp [Set.insert_subset_iff, hyD, hBD hb]) hx
  · exact (setClosure_closed_iff c C).mp hC {x, b}
      (by simp [Set.insert_subset_iff, hxC, hBC hb]) hy

/-- **A closed set above an infinite root lies below every one-point enlargement leaving it.**
If `B ⊆ D` with `B` infinite and `D` closed, and `y ∉ D`, then `D` lies in the closure of `B` with
`y` added: the two closed sets are comparable and the second is not inside `D`. -/
theorem subset_setClosure_insert_of_notMem {M : Type u} {c : ClosureOperator (Finset M)}
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) {B D : Set M} (hB : B.Infinite)
    (hD : (setClosure c).IsClosed D) (hBD : B ⊆ D) {y : M} (hy : y ∉ D) :
    D ⊆ setClosure c (insert y B) := by
  rcases closedSupersetsComparableTarget c hgen hB ((setClosure c).isClosed_closure _) hD
    subset_setClosure_insert hBD with h | h
  · exact absurd (h mem_setClosure_insert_self) hy
  · exact h

/-- **Target: closed cuts recover the order of an exterior enumeration.**  Let `B` be infinite and
`z : I → M` injective with values outside `B`, indexed by any partial order `I`.  If every lower
cut `B ∪ z '' Iic j` is closed, then `z i` lies in the closure of `B` with `z j` added exactly when
`i ≤ j`.  Closedness of `B`, anti-exchange, linearity of `I` and exhaustion of `M` are not
hypotheses.  Given-closure statement.  Proved
(`Closure.closedCutOrderTarget`). -/
def ClosedCutOrderTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃I : Type v⦄ [PartialOrder I] ⦃B : Set M⦄ (z : I → M), B.Infinite →
      Function.Injective z → (∀ i, z i ∉ B) →
      (∀ j, (setClosure c).IsClosed (B ∪ z '' Set.Iic j)) →
        ∀ i j, z i ∈ setClosure c (insert (z j) B) ↔ i ≤ j

/-- **Closed cuts recover the order of an exterior enumeration**, the target form.  If `z i` lies
in the closure of `B` with `z j` added, it lies in the closed cut at `j`, hence `i ≤ j` by
injectivity.  Conversely the closures of `B` with `z i` and with `z j` added are comparable; if the
second lies in the first, then also `j ≤ i`, so `i = j`. -/
theorem closedCutOrderTarget : ClosedCutOrderTarget.{u, v} := by
  intro M c hgen I _ B z hB hz hzB hcut
  have hle (i j : I) (hi : z i ∈ setClosure c (insert (z j) B)) : i ≤ j := by
    have hsub : insert (z j) B ⊆ B ∪ z '' Set.Iic j :=
      Set.insert_subset (Or.inr ⟨j, le_rfl, rfl⟩) Set.subset_union_left
    rcases ClosureOperator.closure_min hsub (hcut j) hi with h | ⟨k, hk, hkz⟩
    · exact absurd h (hzB i)
    · obtain rfl := hz hkz
      exact hk
  intro i j
  refine ⟨hle i j, fun hij ↦ ?_⟩
  rcases closedSupersetsComparableTarget c hgen hB ((setClosure c).isClosed_closure _)
    ((setClosure c).isClosed_closure _) (subset_setClosure_insert (y := z i))
    (subset_setClosure_insert (y := z j)) with h | h
  · exact h mem_setClosure_insert_self
  · rw [le_antisymm hij (hle j i (h mem_setClosure_insert_self))]
    exact mem_setClosure_insert_self

/-! ### The exterior order -/

/-- **Target: the exterior order above an infinite closed root is linear.**  Under two-generation
and anti-exchange of the finite hulls, for an infinite closed set `B`, the relation "`x` lies in
the closure of `B` with `y` added" is a linear order (reflexive, transitive, antisymmetric and
total) on the points outside `B`.  This is a `Prop`; no `LinearOrder` instance is declared.
Given-closure statement.  Proved
(`Closure.exteriorLinearOrderTarget`). -/
def ExteriorLinearOrderTarget : Prop :=
  ∀ ⦃M : Type u⦄ [DecidableEq M] (c : ClosureOperator (Finset M)),
    (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    (∀ (S : Finset M) (x y : M), x ≠ y → x ∉ c S → x ∈ c (insert y S) → y ∉ c (insert x S)) →
      ∀ ⦃B : Set M⦄, (setClosure c).IsClosed B → B.Infinite →
        IsLinearOrder {x : M // x ∉ B} fun x y ↦ x.1 ∈ setClosure c (insert y.1 B)

/-- **The exterior order above an infinite closed root is linear**, the target form.
Reflexivity and transitivity hold for any closure; antisymmetry is anti-exchange at the closed set
`B` (`setClosure_antiExchange`); totality is comparability of the closures of `B` with one point
added. -/
theorem exteriorLinearOrderTarget : ExteriorLinearOrderTarget.{u} := by
  intro M _ c hgen ha B hB hBi
  refine { refl := fun _ ↦ mem_setClosure_insert_self,
           trans := fun _ _ _ hxy hyz ↦ setClosure_insert_subset_of_mem hyz hxy,
           antisymm := fun x y hxy hyx ↦ ?_,
           total := fun x y ↦ ?_ }
  · by_contra hne
    exact setClosure_antiExchange c ha hB.closure_eq (fun h ↦ hne (Subtype.ext h)) x.2 hxy hyx
  · rcases closedSupersetsComparableTarget c hgen hBi ((setClosure c).isClosed_closure _)
      ((setClosure c).isClosed_closure _) (subset_setClosure_insert (y := x.1))
      (subset_setClosure_insert (y := y.1)) with h | h
    · exact Or.inl (h mem_setClosure_insert_self)
    · exact Or.inr (h mem_setClosure_insert_self)

/-! ### Changing the root -/

/-- **Target: changing the root.**  Let `B ⊆ D` with `B` infinite and `D` closed.  For a point `y`
outside `D`, the closure of `D` with `y` added is the closure of `B` with `y` added, so on the
points outside `D` the exterior relation of `D` is the restriction of that of `B`.  Closedness of
`B` and anti-exchange are not hypotheses.  Given-closure statement.  Proved
(`Closure.exteriorRootChangeTarget`). -/
def ExteriorRootChangeTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B D : Set M⦄, B.Infinite → (setClosure c).IsClosed D → B ⊆ D →
      ∀ ⦃y : M⦄, y ∉ D → setClosure c (insert y D) = setClosure c (insert y B)

/-- **Changing the root**, the target form: `D` lies in the closure of `B` with `y` added
(`subset_setClosure_insert_of_notMem`), so that closure contains `D` with `y` added. -/
theorem exteriorRootChangeTarget : ExteriorRootChangeTarget.{u} := by
  intro M c hgen B D hB hD hBD y hy
  refine le_antisymm ?_ ((setClosure c).monotone (Set.insert_subset_insert hBD))
  exact ClosureOperator.closure_min (Set.insert_subset mem_setClosure_insert_self
    (subset_setClosure_insert_of_notMem hgen hB hD hBD hy)) ((setClosure c).isClosed_closure _)

/-- **Target: the enlarged root comes first.**  Let `B ⊆ D` with `B` infinite and `D` closed.  In
the exterior relation of `B`, every point of `D` lies strictly before every point outside `D`: it
lies in the closure of `B` with the outside point added, and the outside point does not lie in the
closure of `B` with it added.  Given-closure statement.  Proved
(`Closure.rootBeforeExteriorTarget`). -/
def RootBeforeExteriorTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B D : Set M⦄, B.Infinite → (setClosure c).IsClosed D → B ⊆ D →
      ∀ ⦃x y : M⦄, x ∈ D → y ∉ D →
        x ∈ setClosure c (insert y B) ∧ y ∉ setClosure c (insert x B)

/-- **The enlarged root comes first**, the target form: `D` lies in the closure of `B` with `y`
added (`subset_setClosure_insert_of_notMem`), and the closure of `B` with `x ∈ D` added lies in
the closed set `D`, which misses `y`. -/
theorem rootBeforeExteriorTarget : RootBeforeExteriorTarget.{u} := by
  intro M c hgen B D hB hD hBD x y hx hy
  exact ⟨subset_setClosure_insert_of_notMem hgen hB hD hBD hy hx,
    fun h ↦ hy (ClosureOperator.closure_min (Set.insert_subset hx hBD) hD h)⟩

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
relations coincide.  Given-closure statement.  Proved
(`Closure.commonRootExteriorAgreementTarget`). -/
def CommonRootExteriorAgreementTarget : Prop :=
  ∀ ⦃M : Type u⦄ (c : ClosureOperator (Finset M)), (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) →
    ∀ ⦃B C : Set M⦄, B.Infinite → C.Infinite → ∀ ⦃y : M⦄, y ∉ setClosure c (B ∪ C) →
      ∀ x : M, x ∈ setClosure c (insert y B) ↔ x ∈ setClosure c (insert y C)

/-- **Exterior relations agree outside a common root**, the target form: both closures are the
closure of `cl(B ∪ C)` with `y` added (`exteriorRootChangeTarget`). -/
theorem commonRootExteriorAgreementTarget : CommonRootExteriorAgreementTarget.{u} := by
  intro M c hgen B C hB hC y hy x
  have hD := (setClosure c).isClosed_closure (B ∪ C)
  rw [← exteriorRootChangeTarget c hgen hB hD
      (Set.subset_union_left.trans ((setClosure c).le_closure _)) hy,
    exteriorRootChangeTarget c hgen hC hD
      (Set.subset_union_right.trans ((setClosure c).le_closure _)) hy]

end VaughtConjecture.Closure
