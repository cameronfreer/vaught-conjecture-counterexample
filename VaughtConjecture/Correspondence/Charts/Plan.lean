/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.Plan

/-!
# The plans of [AFK26, Definition 4.1]

[AFK26, Definition 4.1] (numbered as in the draft of 10 October 2026): "A *plan* on a non-empty
set `A` is a finitary convex geometry `P ⊆ P_fin(A)` in which every closed set of size at least
`2` has precisely two extreme points.  In other words: `∅ ∈ P`, we have `⋃ P = A`, the geometry
`P` is closed under intersections, every finite set is contained in some closed set, and its
closure operator `cl_P` satisfies

* (Convexity) `(∀ B ∈ P)(∀ x, y ∈ A \ B) (x ≠ y) ∧ (x ∈ cl_P(B ∪ {y})) → (y ∉ cl_P(B ∪ {x}))`,
* (Extreme Points) `(∀ B ∈ P, |B| ≥ 2) |{b ∈ B : B \ {b} ∈ P}| = 2`."

`Geometry.IsTemplatePlan A P` states these clauses for a finite set `A` (a `Finset`), as the
underlying sets of templates are finite; the closure `cl_P(S)` of a finite `S ⊆ A` is
`Geometry.hull A P S`, the points of `A` in every closed superset of `S` (for a finite `A` some
closed set contains `S`, and `cl_P(S)` is the intersection of the closed supersets).  `B ∪ {y}` is
written `insert y B`.

**Comparison** (`Geometry.isTemplatePlan_iff`): for a finite `A`, `P` is a plan in the sense of
[AFK26, Definition 4.1] exactly when `Geometry.IsPlan A P` (the recursive plan of
[Kni26, Definition 2.1.1]) and `A` is nonempty.  The only difference is the empty set: the
recursive definition has the plan `{∅}` on `∅`, which [AFK26] excludes.  The proof goes through
`Geometry.isPlan_iff_isConvexGeometry_and_card_extremes`:

| Clause of [AFK26, Definition 4.1] | Field of `IsTemplatePlan` | `IsConvexGeometry` and `IsPlan` |
| --- | --- | --- |
| `A` non-empty | `nonempty` | (not part of `IsPlan`) |
| `P ⊆ P_fin(A)` | `subset` | `subset_of_mem` |
| `∅ ∈ P` | `empty_mem` | `empty_mem` |
| `⋃ P = A` | `biUnion_eq` | with the next clause, `ground_mem` |
| closed under intersections | `inter_mem` | `infClosed` |
| every finite set in some closed set | `exists_superset` | `ground_mem` (`A` is finite) |
| (Convexity) | `convexity` | `antiExchange` |
| (Extreme Points) | `extremePoints` | `#(extremes P B) = 2` for `1 < #B` |

## References

The recursive plan is [Kni26, Definition 2.1.1]; convex geometries are as in
`VaughtConjecture.Geometry.ConvexGeometry`.
-/

namespace VaughtConjecture.Geometry

open Finset

variable {α : Type*} [DecidableEq α] {A : Finset α} {P : Finset (Finset α)}

/-- **Plans** [AFK26, Definition 4.1] on a finite set `A`, clause by clause; the closure operator
`cl_P` is `Geometry.hull A P`. -/
structure IsTemplatePlan (A : Finset α) (P : Finset (Finset α)) : Prop where
  /-- `A` is non-empty. -/
  nonempty : A.Nonempty
  /-- `P ⊆ P_fin(A)`: the closed sets are finite subsets of `A`. -/
  subset : ∀ B ∈ P, B ⊆ A
  /-- `∅ ∈ P`. -/
  empty_mem : ∅ ∈ P
  /-- `⋃ P = A`. -/
  biUnion_eq : P.biUnion id = A
  /-- `P` is closed under intersections. -/
  inter_mem : ∀ B ∈ P, ∀ C ∈ P, B ∩ C ∈ P
  /-- Every finite set (of points of `A`) is contained in some closed set. -/
  exists_superset : ∀ S ⊆ A, ∃ B ∈ P, S ⊆ B
  /-- (Convexity) For `B ∈ P` and distinct `x, y ∈ A \ B`, if `x ∈ cl_P(B ∪ {y})` then
  `y ∉ cl_P(B ∪ {x})`. -/
  convexity : ∀ B ∈ P, ∀ x ∈ A \ B, ∀ y ∈ A \ B, x ≠ y →
    x ∈ hull A P (insert y B) → y ∉ hull A P (insert x B)
  /-- (Extreme Points) Every `B ∈ P` with `|B| ≥ 2` has `|{b ∈ B : B \ {b} ∈ P}| = 2`. -/
  extremePoints : ∀ B ∈ P, 2 ≤ #B → #{b ∈ B | B.erase b ∈ P} = 2

/-- **The plans of [AFK26, Definition 4.1] are the recursive plans on a nonempty set**: for a
finite set `A`, `P` is a plan in the sense of [AFK26, Definition 4.1] exactly when it is a plan
in the sense of `Geometry.IsPlan` and `A` is nonempty. -/
theorem isTemplatePlan_iff : IsTemplatePlan A P ↔ IsPlan A P ∧ A.Nonempty := by
  rw [isPlan_iff_isConvexGeometry_and_card_extremes]
  constructor
  · intro h
    have hA : A ∈ P := by
      obtain ⟨B, hB, hAB⟩ := h.exists_superset A Subset.rfl
      rwa [Subset.antisymm (h.subset B hB) hAB] at hB
    refine ⟨⟨⟨fun B hB ↦ h.subset B hB, h.empty_mem, hA, fun B hB C hC ↦ h.inter_mem B hB C hC,
      fun B hB x y hxy hxB hx ↦ ?_⟩, fun B hB hB2 ↦ h.extremePoints B hB hB2⟩, h.nonempty⟩
    intro hy
    have hxA : x ∈ A := (mem_hull.mp hx).1
    have hyA : y ∈ A := (mem_hull.mp hy).1
    by_cases hyB : y ∈ B
    · rw [insert_eq_of_mem hyB, hull_eq_self hB (h.subset B hB)] at hx
      exact hxB hx
    · exact h.convexity B hB x (mem_sdiff.mpr ⟨hxA, hxB⟩) y (mem_sdiff.mpr ⟨hyA, hyB⟩) hxy hx hy
  · rintro ⟨⟨hG, hE⟩, hne⟩
    refine ⟨hne, fun B hB ↦ hG.subset_of_mem hB, hG.empty_mem, ?_,
      fun B hB C hC ↦ hG.infClosed hB hC, fun S hS ↦ ⟨A, hG.ground_mem, hS⟩,
      fun B hB x hx y _ hxy ↦ hG.antiExchange hB hxy (mem_sdiff.mp hx).2,
      fun B hB hB2 ↦ hE B hB hB2⟩
    ext x
    simp only [mem_biUnion, id]
    exact ⟨fun ⟨B, hB, hxB⟩ ↦ hG.subset_of_mem hB hxB, fun hx ↦ ⟨A, hG.ground_mem, hx⟩⟩

end VaughtConjecture.Geometry
