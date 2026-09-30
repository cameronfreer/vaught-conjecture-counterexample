/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.Basic
import VaughtConjecture.Geometry.IntervalPlan

/-!
# What two generators do not give

Every closed set of a plan is the hull of its at most two extreme points
(`IsConvexGeometry.hull_extremes`, `IsPlan.card_extremes_le_two`).
`roadmap/SEMANTIC_CONTRACT.md`, item 2, warns against reading more into this.  This file records
concrete witnesses.

* **Not every convex geometry is a plan.**  All subsets of `Fin 3` form a convex geometry
  (`isConvexGeometry_powerset_univ_fin_three`) that is not a plan
  (`not_isPlan_powerset_univ_fin_three`): its ground set has three extreme points.
* **No two-element closed root.**  The *star plan* `starPlan` on `Fin 4`, glued at `0` and `3`
  from the chain `3 – 1 – 2` on `{1, 2, 3}` and the chain `0 – 1 – 2` on `{0, 1, 2}`, is a plan
  (`isPlan_starPlan`) whose ground set has extremes `{0, 3}` (`extremes_starPlan`); these
  generate the whole ground set (`hull_starPlan`), yet `{0, 3}` is not closed
  (`pair_notMem_starPlan`).
* **No bound on hull sizes.**  Interval plans on `{0, …, n}` have a pair of points whose hull
  has `n + 1` points (`exists_isPlan_card_hull_pair`), so no bound on the size of the hull of a
  pair of points of the ground set holds for all plans (`not_exists_bound_card_hull_pair`).
* **No linear interval representation.**  In the star plan the point `1` lies in the three closed
  pairs `{0, 1}`, `{1, 2}`, `{1, 3}`, which is impossible for order-convex sets of a linear order;
  so under no injective relabelling into a linear order are the closed sets of the star plan even
  among the order-convex sets (`starPlan_image_not_subset_intervalPlan`).  In particular the star
  plan is not an interval plan.

All finite facts are checked by `decide`.
-/

namespace VaughtConjecture.Geometry

open Finset

/-- All subsets of `Fin 3` form a convex geometry. -/
theorem isConvexGeometry_powerset_univ_fin_three :
    IsConvexGeometry univ (univ : Finset (Fin 3)).powerset := by
  decide

/-- The convex geometry of all subsets of `Fin 3` is not a plan: its ground set has three
extreme points. -/
theorem not_isPlan_powerset_univ_fin_three : ¬ IsPlan univ (univ : Finset (Fin 3)).powerset := by
  decide

/-- The star plan on `Fin 4`: its closed pairs `{0, 1}`, `{1, 2}`, `{1, 3}` all contain `1`. -/
def starPlan : Finset (Finset (Fin 4)) :=
  {∅, {0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {1, 3}, {0, 1, 2}, {1, 2, 3}, univ}

/-- The star plan is a plan on `Fin 4`. -/
theorem isPlan_starPlan : IsPlan univ starPlan := by decide

/-- The extreme points of the ground set of the star plan are `0` and `3`. -/
theorem extremes_starPlan : extremes starPlan univ = {0, 3} := by decide

/-- The two extreme points `0` and `3` generate the whole ground set of the star plan. -/
theorem hull_starPlan : hull univ starPlan {0, 3} = univ := by decide

/-- The generating pair `{0, 3}` of the ground set of the star plan is not closed. -/
theorem pair_notMem_starPlan : ({0, 3} : Finset (Fin 4)) ∉ starPlan := by decide

/-- The star plan does not embed in an interval plan: under no injective relabelling into a
linear order are all its closed sets order-convex.  In particular it is not an interval plan. -/
theorem starPlan_image_not_subset_intervalPlan {β : Type*} [LinearOrder β] (f : Fin 4 → β)
    (hf : Function.Injective f) : ¬ starPlan.image (image f) ⊆ intervalPlan (univ.image f) := by
  intro h
  -- For `j ∈ {0, 2, 3}` the pair `{1, j}` is closed, so no other `f k` lies between `f 1`
  -- and `f j`.
  have key (j k : Fin 4) (hj : j ∈ ({0, 2, 3} : Finset (Fin 4))) (hk1 : k ≠ 1) (hkj : k ≠ j)
      (hbtw : f 1 ≤ f k ∧ f k ≤ f j ∨ f j ≤ f k ∧ f k ≤ f 1) : False := by
    have hpair : ({1, j} : Finset (Fin 4)) ∈ starPlan := by
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> decide
    have hmem : ({f 1, f j} : Finset β) ∈ intervalPlan (univ.image f) :=
      h (mem_image.mpr ⟨{1, j}, hpair, by simp⟩)
    have hconv := (mem_intervalPlan.mp hmem).2
    have hfk : f k ∉ ({f 1, f j} : Finset β) := by
      simp [hf.ne hk1, hf.ne hkj]
    have hk : f k ∈ univ.image f := mem_image_of_mem f (mem_univ k)
    rcases hbtw with hbtw | hbtw
    · exact hfk (hconv _ (by simp) _ (by simp) _ hk hbtw.1 hbtw.2)
    · exact hfk (hconv _ (by simp) _ (by simp) _ hk hbtw.1 hbtw.2)
  -- Hence no two of `f 0, f 2, f 3` lie on the same side of `f 1`: the nearer of the two would
  -- lie between `f 1` and the farther one.
  have side (j k : Fin 4) (hj : j ∈ ({0, 2, 3} : Finset (Fin 4)))
      (hk : k ∈ ({0, 2, 3} : Finset (Fin 4))) (hj1 : j ≠ 1) (hk1 : k ≠ 1) (hjk : j ≠ k)
      (hs : f j < f 1 ∧ f k < f 1 ∨ f 1 < f j ∧ f 1 < f k) : False := by
    rcases le_total (f j) (f k) with hle | hle <;> rcases hs with hs | hs
    · exact key j k hj hk1 hjk.symm (Or.inr ⟨hle, hs.2.le⟩)
    · exact key k j hk hj1 hjk (Or.inl ⟨hs.1.le, hle⟩)
    · exact key k j hk hj1 hjk (Or.inr ⟨hle, hs.1.le⟩)
    · exact key j k hj hk1 hjk.symm (Or.inl ⟨hs.2.le, hle⟩)
  -- But of three points distinct from `f 1`, two lie on the same side of it.
  rcases (hf.ne (by decide : (0 : Fin 4) ≠ 1)).lt_or_gt with h0 | h0 <;>
    rcases (hf.ne (by decide : (2 : Fin 4) ≠ 1)).lt_or_gt with h2 | h2 <;>
    rcases (hf.ne (by decide : (3 : Fin 4) ≠ 1)).lt_or_gt with h3 | h3
  all_goals first
    | exact side 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl ⟨h0, h2⟩)
    | exact side 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr ⟨h0, h2⟩)
    | exact side 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl ⟨h0, h3⟩)
    | exact side 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr ⟨h0, h3⟩)
    | exact side 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl ⟨h2, h3⟩)
    | exact side 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr ⟨h2, h3⟩)

/-- For every `n`, some plan has a pair of points of its ground set whose hull has `n + 1`
points: the interval plan on `{0, …, n}` and the pair `{0, n}`. -/
theorem exists_isPlan_card_hull_pair (n : ℕ) :
    ∃ (A : Finset ℕ) (P : Finset (Finset ℕ)), IsPlan A P ∧ 0 ∈ A ∧ n ∈ A ∧
      #(hull A P {0, n}) = n + 1 := by
  refine ⟨range (n + 1), intervalPlan (range (n + 1)), isPlan_intervalPlan _, by simp, by simp, ?_⟩
  rw [hull_intervalPlan_pair (by simp) (by simp) n.zero_le,
    filter_true_of_mem fun z hz ↦ ⟨z.zero_le, Nat.lt_succ_iff.mp (mem_range.mp hz)⟩, card_range]

/-- There is no uniform bound, over all plans, on the number of points in the hull of a pair of
points of the ground set. -/
theorem not_exists_bound_card_hull_pair :
    ¬ ∃ N : ℕ, ∀ (A : Finset ℕ) (P : Finset (Finset ℕ)), IsPlan A P →
      ∀ a ∈ A, ∀ b ∈ A, #(hull A P {a, b}) ≤ N := by
  rintro ⟨N, hN⟩
  obtain ⟨A, P, hP, h0, hN', hc⟩ := exists_isPlan_card_hull_pair N
  have := hN A P hP 0 h0 N hN'
  omega

end VaughtConjecture.Geometry
