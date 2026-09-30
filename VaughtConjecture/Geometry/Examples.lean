/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fintype.Basic
import VaughtConjecture.Geometry.IntervalPlan

/-!
# What two generators do not give

Every closed set of a plan is the hull of its two extreme points (`IsPlan.exists_generator`).
`roadmap/SEMANTIC_CONTRACT.md`, item 2, warns against reading more into this.  This file records
concrete witnesses.

* **No two-element closed root.**  The *star plan* `starPlan` on `Fin 4`, glued at `0` and `3`
  from the chain `3 – 1 – 2` on `{1, 2, 3}` and the chain `0 – 1 – 2` on `{0, 1, 2}`, is a plan
  (`isPlan_starPlan`) whose domain has extremes `{0, 3}` (`extremes_starPlan`); these generate the
  whole domain (`hull_starPlan`), yet `{0, 3}` is not closed (`pair_notMem_starPlan`).
* **No bound on hull sizes.**  Interval plans on `{0, …, n}` have a pair with an `(n+1)`-point
  hull (`exists_isPlan_card_hull_pair`), so no bound on the size of the hull of a pair holds for
  all plans (`not_exists_bound_card_hull_pair`).
* **No linear interval representation.**  In the star plan the point `1` lies in the three closed
  pairs `{0, 1}`, `{1, 2}`, `{1, 3}`, which is impossible in the interval plan of a linear order;
  so the star plan is not an interval plan under any relabelling by natural numbers
  (`starPlan_ne_intervalPlan`).

All finite facts are checked by `decide`.
-/

namespace VaughtConjecture.Geometry

open Finset

/-- The star plan on `Fin 4`: its closed pairs `{0, 1}`, `{1, 2}`, `{1, 3}` all contain `1`. -/
def starPlan : Finset (Finset (Fin 4)) :=
  {∅, {0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {1, 3}, {0, 1, 2}, {1, 2, 3}, univ}

/-- The star plan is a plan on `Fin 4`. -/
theorem isPlan_starPlan : IsPlan univ starPlan := by decide

/-- The extreme points of the domain of the star plan are `0` and `3`. -/
theorem extremes_starPlan : extremes starPlan univ = {0, 3} := by decide

/-- The two extreme points `0` and `3` generate the whole domain of the star plan. -/
theorem hull_starPlan : hull univ starPlan {0, 3} = univ := by decide

/-- The generating pair `{0, 3}` of the domain of the star plan is not closed. -/
theorem pair_notMem_starPlan : ({0, 3} : Finset (Fin 4)) ∉ starPlan := by decide

/-- The star plan is not the interval plan of a linear order: under no injective relabelling
by natural numbers does it become the family of order-convex subsets. -/
theorem starPlan_ne_intervalPlan (f : Fin 4 → ℕ) (hf : Function.Injective f) :
    starPlan.image (image f) ≠ intervalPlan (univ.image f) := by
  intro h
  have hpair : ∀ j ∈ ({0, 2, 3} : Finset (Fin 4)), ({1, j} : Finset (Fin 4)) ∈ starPlan := by
    decide
  have key (j : Fin 4) (hj : j ∈ ({0, 2, 3} : Finset (Fin 4))) (k : Fin 4) (hk1 : k ≠ 1)
      (hkj : k ≠ j) : ¬ (f 1 ≤ f k ∧ f k ≤ f j) ∧ ¬ (f j ≤ f k ∧ f k ≤ f 1) := by
    have hmem : ({f 1, f j} : Finset ℕ) ∈ intervalPlan (univ.image f) := by
      rw [← h]
      exact mem_image.mpr ⟨{1, j}, hpair j hj, by simp⟩
    have hconv := (mem_intervalPlan.mp hmem).2
    have hfk : f k ∉ ({f 1, f j} : Finset ℕ) := by
      simp [hf.ne hk1, hf.ne hkj]
    have hk : f k ∈ univ.image f := mem_image_of_mem f (mem_univ k)
    exact ⟨fun h ↦ hfk (hconv _ (by simp) _ (by simp) _ hk h.1 h.2),
      fun h ↦ hfk (hconv _ (by simp) _ (by simp) _ hk h.1 h.2)⟩
  have h02 := key 0 (by decide) 2 (by decide) (by decide)
  have h03 := key 0 (by decide) 3 (by decide) (by decide)
  have h20 := key 2 (by decide) 0 (by decide) (by decide)
  have h23 := key 2 (by decide) 3 (by decide) (by decide)
  have h30 := key 3 (by decide) 0 (by decide) (by decide)
  have h32 := key 3 (by decide) 2 (by decide) (by decide)
  have d10 : f 1 ≠ f 0 := hf.ne (by decide)
  have d12 : f 1 ≠ f 2 := hf.ne (by decide)
  have d13 : f 1 ≠ f 3 := hf.ne (by decide)
  omega

/-- For every `n`, some plan has a pair of points whose hull has `n + 1` points: the interval
plan on `{0, …, n}` and the pair `{0, n}`. -/
theorem exists_isPlan_card_hull_pair (n : ℕ) :
    ∃ (A : Finset ℕ) (P : Finset (Finset ℕ)), IsPlan A P ∧ #(hull A P {0, n}) = n + 1 := by
  refine ⟨range (n + 1), intervalPlan (range (n + 1)), isPlan_intervalPlan _, ?_⟩
  rw [hull_intervalPlan_pair (by simp) (by simp) n.zero_le,
    filter_true_of_mem fun z hz ↦ ⟨z.zero_le, Nat.lt_succ_iff.mp (mem_range.mp hz)⟩, card_range]

/-- Two generators do not bound the size of a hull: there is no uniform bound on the number of
points in the hull of a pair, over all plans. -/
theorem not_exists_bound_card_hull_pair :
    ¬ ∃ N : ℕ, ∀ (A : Finset ℕ) (P : Finset (Finset ℕ)), IsPlan A P →
      ∀ a b : ℕ, #(hull A P {a, b}) ≤ N := by
  rintro ⟨N, hN⟩
  obtain ⟨A, P, hP, hc⟩ := exists_isPlan_card_hull_pair N
  have := hN A P hP 0 N
  omega

end VaughtConjecture.Geometry
