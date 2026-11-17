/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Finite-interval equivalence in a linear order

Two points of a linear order are **finite-interval equivalent** (`Order.FiniteInterval`) when the
closed interval between them is finite.  This file proves that the relation is an equivalence
relation with order-convex classes, that order isomorphisms preserve it, and that on an
order-connected subset (for example an upper set) it is the restriction of the relation of the
ambient order.  In a lexicographic sum of copies of `ℕ` and `ℤ` its classes are the summands
(`VaughtConjecture.CodedOrder`), which is how the summands are recovered from the order alone.

All results are proved.
-/

universe u v

namespace VaughtConjecture.Order

variable {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β] {x y z : α}

/-- Two points are **finite-interval equivalent** when the closed interval between them is
finite. -/
def FiniteInterval (x y : α) : Prop := (Set.uIcc x y).Finite

theorem finiteInterval_refl (x : α) : FiniteInterval x x := by
  simp [FiniteInterval]

theorem FiniteInterval.symm (h : FiniteInterval x y) : FiniteInterval y x := by
  rwa [FiniteInterval, Set.uIcc_comm]

theorem FiniteInterval.trans (hxy : FiniteInterval x y) (hyz : FiniteInterval y z) :
    FiniteInterval x z :=
  (hxy.union hyz).subset Set.uIcc_subset_uIcc_union_uIcc

/-- Finite-interval equivalence is an equivalence relation. -/
theorem finiteInterval_equivalence : Equivalence (FiniteInterval (α := α)) :=
  ⟨finiteInterval_refl, FiniteInterval.symm, FiniteInterval.trans⟩

/-- The classes of finite-interval equivalence are order-convex: a point between two equivalent
points is equivalent to both. -/
theorem FiniteInterval.of_le_of_le (h : FiniteInterval x z) (hxy : x ≤ y) (hyz : y ≤ z) :
    FiniteInterval x y :=
  h.subset (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le hxy hyz))

/-- Order isomorphisms preserve finite-interval equivalence. -/
theorem _root_.OrderIso.finiteInterval_iff (e : α ≃o β) :
    FiniteInterval (e x) (e y) ↔ FiniteInterval x y := by
  have hpre : e ⁻¹' Set.uIcc (e x) (e y) = Set.uIcc x y := by
    ext w
    simp [Set.mem_uIcc]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [FiniteInterval, ← hpre]
    exact h.preimage e.injective.injOn
  · rw [FiniteInterval, ← hpre] at h
    exact Set.Finite.of_preimage h e.surjective

/-- On an order-connected subset, finite-interval equivalence is the restriction of finite-interval
equivalence in the ambient order. -/
theorem finiteInterval_subtype_iff {s : Set α} (hs : s.OrdConnected) {x y : s} :
    FiniteInterval x y ↔ FiniteInterval (x : α) y := by
  have hpre : Subtype.val ⁻¹' Set.uIcc (x : α) y = Set.uIcc x y := by
    ext w
    simp [Set.mem_uIcc]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (h.image Subtype.val).subset fun w hw ↦ ?_
    refine ⟨⟨w, hs.uIcc_subset x.2 y.2 hw⟩, ?_, rfl⟩
    rw [← hpre]
    exact hw
  · rw [FiniteInterval, ← hpre]
    exact h.preimage Subtype.val_injective.injOn

end VaughtConjecture.Order
