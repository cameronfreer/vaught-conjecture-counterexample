/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Powerset
import VaughtConjecture.Geometry.Plan

/-!
# Interval plans on linearly ordered finite sets

For a finite subset `A` of a linear order, the order-convex subsets of `A` form a plan
(`isPlan_intervalPlan`): deleting the least or the greatest point of `A` gives the two glued
subplans.  In particular there are plans on finite sets of every size.  The hull of two
points is the set of points of `A` between them (`hull_intervalPlan_pair`), so hulls of pairs
of points in interval plans can have any finite size (`VaughtConjecture.Geometry.Examples`).
Interval plans are only one family of plans: not every plan has this linear form.  See
`roadmap/SEMANTIC_CONTRACT.md`, item 2.
-/

namespace VaughtConjecture.Geometry

open Finset

variable {α : Type*} [LinearOrder α] {A B D : Finset α} {a b x : α}

/-- The interval plan on `A`: the subsets of `A` that are order-convex in `A`, i.e. contain
every point of `A` lying between two of their points. -/
def intervalPlan (A : Finset α) : Finset (Finset α) :=
  {B ∈ A.powerset | ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ A, x ≤ z → z ≤ y → z ∈ B}

/-- Membership in the interval plan: a subset of `A` containing every point of `A` between two
of its points. -/
@[simp, grind =]
theorem mem_intervalPlan :
    B ∈ intervalPlan A ↔ B ⊆ A ∧ ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ A, x ≤ z → z ≤ y → z ∈ B := by
  rw [intervalPlan, mem_filter, mem_powerset]

/-- The ground set is order-convex in itself. -/
@[simp high] theorem self_mem_intervalPlan : A ∈ intervalPlan A :=
  mem_intervalPlan.mpr ⟨Subset.rfl, fun _ _ _ _ _ hz _ _ ↦ hz⟩

/-- Order-convex subsets are closed under intersection. -/
theorem infClosed_intervalPlan : InfClosed (intervalPlan A : Set (Finset α)) := by
  intro B hB C hC
  rw [mem_coe] at hB hC ⊢
  rw [inf_eq_inter]
  obtain ⟨hBA, hB⟩ := mem_intervalPlan.mp hB
  obtain ⟨-, hC⟩ := mem_intervalPlan.mp hC
  refine mem_intervalPlan.mpr ⟨inter_subset_left.trans hBA, fun x hx y hy z hz hxz hzy ↦ ?_⟩
  rw [mem_inter] at hx hy ⊢
  exact ⟨hB x hx.1 y hy.1 z hz hxz hzy, hC x hx.2 y hy.2 z hz hxz hzy⟩

/-- Inside an order-convex subset `D` of `A`, order-convexity in `D` and in `A` agree. -/
theorem mem_intervalPlan_iff_of_mem (hD : D ∈ intervalPlan A) (hBD : B ⊆ D) :
    B ∈ intervalPlan D ↔ B ∈ intervalPlan A := by
  obtain ⟨hDA, hDc⟩ := mem_intervalPlan.mp hD
  simp only [mem_intervalPlan, hBD, hBD.trans hDA, true_and]
  exact ⟨fun h x hx y hy z hz hxz hzy ↦ h x hx y hy z (hDc x (hBD hx) y (hBD hy) z hz hxz hzy)
    hxz hzy, fun h x hx y hy z hz ↦ h x hx y hy z (hDA hz)⟩

/-- Deleting a lower bound of `A` leaves an order-convex subset. -/
theorem erase_mem_intervalPlan_of_le (h : ∀ z ∈ A, x ≤ z) : A.erase x ∈ intervalPlan A := by
  refine mem_intervalPlan.mpr ⟨erase_subset _ _, fun u hu v _ z hz huz _ ↦ mem_erase.mpr
    ⟨?_, hz⟩⟩
  rintro rfl
  exact (mem_erase.mp hu).1 (le_antisymm huz (h u (mem_erase.mp hu).2))

/-- Deleting an upper bound of `A` leaves an order-convex subset. -/
theorem erase_mem_intervalPlan_of_ge (h : ∀ z ∈ A, z ≤ x) : A.erase x ∈ intervalPlan A := by
  refine mem_intervalPlan.mpr ⟨erase_subset _ _, fun _ _ v hv z hz _ hzv ↦ mem_erase.mpr
    ⟨?_, hz⟩⟩
  rintro rfl
  exact (mem_erase.mp hv).1 (le_antisymm (h v (mem_erase.mp hv).2) hzv)

/-- The order-convex subsets of a finite subset of a linear order form a plan. -/
theorem isPlan_intervalPlan (A : Finset α) : IsPlan A (intervalPlan A) := by
  induction hn : #A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    subst hn
    rcases le_or_gt #A 1 with hA | hA
    · exact .of_card_le_one hA (fun _ hB ↦ (mem_intervalPlan.mp hB).1) (by simp)
        self_mem_intervalPlan
    -- Deleting the least point `a` or the greatest point `b` of `A` leaves an order-convex set.
    have hne : A.Nonempty := card_pos.mp (by omega)
    set a := A.min' hne
    set b := A.max' hne
    have hab : a ≠ b := (min'_lt_max'_of_card A hA).ne
    have haP : A.erase a ∈ intervalPlan A :=
      erase_mem_intervalPlan_of_le fun z hz ↦ min'_le A z hz
    have hbP : A.erase b ∈ intervalPlan A :=
      erase_mem_intervalPlan_of_ge fun z hz ↦ le_max' A z hz
    -- Every order-convex proper subset of `A` omits `a` or `b`.
    have he :
        intervalPlan A = insert A (intervalPlan (A.erase a) ∪ intervalPlan (A.erase b)) := by
      ext B
      simp only [mem_insert, mem_union]
      constructor
      · intro hB
        by_cases hBA : B = A
        · exact Or.inl hBA
        by_cases haB : a ∈ B
        · by_cases hbB : b ∈ B
          · refine absurd ((mem_intervalPlan.mp hB).1.antisymm fun z hz ↦ ?_) hBA
            exact (mem_intervalPlan.mp hB).2 a haB b hbB z hz (min'_le A z hz) (le_max' A z hz)
          · have hsub : B ⊆ A.erase b := fun z hz ↦
              mem_erase.mpr ⟨fun h ↦ hbB (h ▸ hz), (mem_intervalPlan.mp hB).1 hz⟩
            exact Or.inr (Or.inr ((mem_intervalPlan_iff_of_mem hbP hsub).mpr hB))
        · have hsub : B ⊆ A.erase a := fun z hz ↦
            mem_erase.mpr ⟨fun h ↦ haB (h ▸ hz), (mem_intervalPlan.mp hB).1 hz⟩
          exact Or.inr (Or.inl ((mem_intervalPlan_iff_of_mem haP hsub).mpr hB))
      · rintro (rfl | hB | hB)
        · exact self_mem_intervalPlan
        · exact (mem_intervalPlan_iff_of_mem haP (mem_intervalPlan.mp hB).1).mp hB
        · exact (mem_intervalPlan_iff_of_mem hbP (mem_intervalPlan.mp hB).1).mp hB
    -- Glue the interval plans on `A \ {a}` and `A \ {b}` along the common face `A \ {a, b}`.
    have hface : (A.erase a).erase b ∈ intervalPlan A :=
      (by rw [inter_erase, inter_eq_left.mpr (erase_subset _ _)] :
          A.erase a ∩ A.erase b = (A.erase a).erase b) ▸ infClosed_intervalPlan haP hbP
    have hsa : (A.erase a).erase b ⊆ A.erase a := erase_subset _ _
    have hsb : (A.erase a).erase b ⊆ A.erase b := erase_subset_erase b (erase_subset a A)
    rw [he]
    refine IsPlan.step (min'_mem A hne) (max'_mem A hne) hab
      (ih _ (card_erase_lt_of_mem (min'_mem A hne)) _ rfl)
      (ih _ (card_erase_lt_of_mem (max'_mem A hne)) _ rfl)
      ((mem_intervalPlan_iff_of_mem haP hsa).mpr hface) fun C hC ↦ ?_
    rw [mem_intervalPlan_iff_of_mem haP (hC.trans hsa),
      mem_intervalPlan_iff_of_mem hbP (hC.trans hsb)]

/-- In an interval plan the hull of two points `a ≤ b` of `A` is the set of points of `A`
between them. -/
theorem hull_intervalPlan_pair (ha : a ∈ A) (hb : b ∈ A) (hab : a ≤ b) :
    hull A (intervalPlan A) {a, b} = {z ∈ A | a ≤ z ∧ z ≤ b} := by
  have hI : {z ∈ A | a ≤ z ∧ z ≤ b} ∈ intervalPlan A := by
    refine mem_intervalPlan.mpr ⟨filter_subset _ _, fun x hx y hy z hz hxz hzy ↦ ?_⟩
    simp only [mem_filter] at hx hy ⊢
    exact ⟨hz, hx.2.1.trans hxz, hzy.trans hy.2.2⟩
  refine (hull_subset hI ?_).antisymm fun z hz ↦ mem_hull.mpr ⟨(mem_filter.mp hz).1, ?_⟩
  · simp [insert_subset_iff, ha, hb, hab]
  · intro B hB hsub
    simp only [insert_subset_iff, singleton_subset_iff] at hsub
    obtain ⟨hz, haz, hzb⟩ := mem_filter.mp hz
    exact (mem_intervalPlan.mp hB).2 a hsub.1 b hsub.2 z hz haz hzb

end VaughtConjecture.Geometry
