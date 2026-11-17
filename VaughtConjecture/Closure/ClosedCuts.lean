/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Closure.ExteriorOrder

/-!
# Closed cuts over a root

Two consequences of closed lower cuts `D ∪ z '' Iic j` of an injective enumeration `z : I → M` of
points outside a set `D`:

* if `I` is nonempty without a least element, `D` itself is closed (`isClosed_of_isClosed_cuts`):
  a point of the closure of `D` lies in every cut, and a point `z i` is missed by the cut at any
  `j < i`;
* under whole-hull two-generation, for a closed `D` and an infinite `B ⊆ D`, the exterior relation
  of `B` on the enumerated points is the order of `I`
  (`mem_setClosure_insert_iff_of_isClosed_cuts`): `Closure.closedCutOrderTarget` at the root `D`,
  then root change (`Closure.exteriorRootChangeTarget`).

Both are given-closure statements, proved.  They are the order arguments of the blocks of the
`ℵ₁` companion construction (`VaughtConjecture.AlephOne.DescendingBlock`,
`VaughtConjecture.AlephOne.IntegerBlock`).

## Placement

This file belongs beside `VaughtConjecture.Closure.ExteriorOrder`.
-/

universe u v

namespace VaughtConjecture.Closure

open InfinitaryLogic.FiniteSupportClosure

/-- **A root below closed cuts without a least index is closed.**  If `z : I → M` is injective,
`I` is nonempty with no least element, and every cut `D ∪ z '' Iic j` is closed for a closure
operator, then `D` is closed. -/
theorem isClosed_of_isClosed_cuts {M : Type u} {c : ClosureOperator (Set M)} {I : Type v}
    [Preorder I] [NoMinOrder I] [Nonempty I] {D : Set M} {z : I → M}
    (hz : Function.Injective z) (hcut : ∀ j, c.IsClosed (D ∪ z '' Set.Iic j)) : c.IsClosed D := by
  rw [ClosureOperator.isClosed_iff_closure_le]
  intro x hx
  obtain ⟨j₀⟩ := ‹Nonempty I›
  rcases ClosureOperator.closure_min Set.subset_union_left (hcut j₀) hx with h | ⟨i, -, rfl⟩
  · exact h
  · obtain ⟨j, hj⟩ := exists_lt i
    rcases ClosureOperator.closure_min Set.subset_union_left (hcut j) hx with h | ⟨i', hi', hii'⟩
    · exact h
    · obtain rfl := hz hii'
      exact absurd (hj.trans_le hi') (lt_irrefl j)

/-- **Closed cuts give the exterior order over any infinite part of the root.**  Under whole-hull
two-generation, let `D` be closed, `B ⊆ D` infinite, and `z : I → M` injective with values outside
`D` and every cut `D ∪ z '' Iic j` closed.  Then `z i` lies in the closure of `B` with `z j` added
exactly when `i ≤ j`. -/
theorem mem_setClosure_insert_iff_of_isClosed_cuts {M : Type u} {c : ClosureOperator (Finset M)}
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) {I : Type v} [PartialOrder I] {B D : Set M}
    (z : I → M) (hB : B.Infinite) (hBD : B ⊆ D) (hD : (setClosure c).IsClosed D)
    (hz : Function.Injective z) (hzD : ∀ i, z i ∉ D)
    (hcut : ∀ j, (setClosure c).IsClosed (D ∪ z '' Set.Iic j)) (i j : I) :
    z i ∈ setClosure c (insert (z j) B) ↔ i ≤ j := by
  rw [← exteriorRootChangeTarget c hgen hB hD hBD (hzD j)]
  exact closedCutOrderTarget c hgen z (hB.mono hBD) hz hzD hcut i j

end VaughtConjecture.Closure
