/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max

/-!
# Finite convex geometries on a finite ground set

A family `P : Finset (Finset α)` of *closed sets* on a finite ground set `A : Finset α` is a
**convex geometry** (`IsConvexGeometry A P`) if its members are subsets of `A`, the empty set and
`A` are closed, closed sets are closed under intersection, and the hull operator satisfies
anti-exchange.  These are the standard closed-set axioms; singletons need not be closed in
general.

* `hull A P S` is the least closed superset of `S` (for `S ⊆ A`), computed as the points of `A`
  lying in every closed superset of `S`.
* `extremes P B` is the set of points `x ∈ B` such that `B \ {x}` is closed.  For a closed `B`
  in a convex geometry this is the usual notion of extreme point: `x ∉ hull (B \ {x})`
  (`IsConvexGeometry.mem_extremes_iff`).
* `restrict P B` is the family of closed sets contained in `B`; restriction to a closed face is
  again a convex geometry (`IsConvexGeometry.restrict`), with the same hulls and extremes.
* Anti-exchange is equivalent, for intersection-closed families, to one-point accessibility
  (`IsConvexGeometry.exists_insert_mem`, `IsConvexGeometry.of_accessible`).
* Every closed set is the hull of its extreme points (`IsConvexGeometry.hull_extremes`).

The subclass used by the construction (exactly two extreme points on every nonsingleton closed
set) and its recursive description are in `VaughtConjecture.Geometry.Plan`.  See
`roadmap/README.md`, Layer 1, and `roadmap/SEMANTIC_CONTRACT.md`, item 2.
-/

namespace VaughtConjecture.Geometry

open Finset

variable {α : Type*} [DecidableEq α] {A B C S T : Finset α} {P : Finset (Finset α)} {x y : α}

/-! ### Hulls, extremes, and restriction -/

/-- The hull of `S` in the family `P` on the ground set `A`: the points of `A` lying in every
member of `P` that contains `S`.  For a convex geometry and `S ⊆ A` it is the least closed
superset of `S` (`hull_mem`, `subset_hull`, `hull_subset`). -/
def hull (A : Finset α) (P : Finset (Finset α)) (S : Finset α) : Finset α :=
  {x ∈ A | ∀ B ∈ P, S ⊆ B → x ∈ B}

/-- The extreme points of `B` relative to `P`: the points whose removal from `B` leaves a
member of `P`. -/
def extremes (P : Finset (Finset α)) (B : Finset α) : Finset α :=
  {x ∈ B | B.erase x ∈ P}

/-- The restriction of `P` to `B`: the members of `P` contained in `B`. -/
def restrict (P : Finset (Finset α)) (B : Finset α) : Finset (Finset α) :=
  {C ∈ P | C ⊆ B}

/-- Membership in a hull: a point of the ground set lying in every closed superset. -/
theorem mem_hull : x ∈ hull A P S ↔ x ∈ A ∧ ∀ B ∈ P, S ⊆ B → x ∈ B := mem_filter

/-- Membership in the extremes: a point whose removal leaves a closed set. -/
theorem mem_extremes : x ∈ extremes P B ↔ x ∈ B ∧ B.erase x ∈ P := mem_filter

/-- Membership in a restriction: a closed set contained in the face. -/
theorem mem_restrict : C ∈ restrict P B ↔ C ∈ P ∧ C ⊆ B := mem_filter

/-- A hull lies in the ground set. -/
theorem hull_subset_domain : hull A P S ⊆ A := filter_subset _ _

/-- A subset of the ground set lies in its hull. -/
theorem subset_hull (hS : S ⊆ A) : S ⊆ hull A P S :=
  fun _ hx ↦ mem_hull.mpr ⟨hS hx, fun _ _ hSB ↦ hSB hx⟩

/-- A hull lies in every closed superset. -/
theorem hull_subset (hB : B ∈ P) (hSB : S ⊆ B) : hull A P S ⊆ B :=
  fun _ hx ↦ (mem_hull.mp hx).2 B hB hSB

/-- Hulls are monotone. -/
theorem hull_mono (hST : S ⊆ T) : hull A P S ⊆ hull A P T := fun _ hx ↦
  mem_hull.mpr ⟨(mem_hull.mp hx).1, fun B hB hTB ↦ (mem_hull.mp hx).2 B hB (hST.trans hTB)⟩

/-- A closed subset of the ground set is its own hull. -/
theorem hull_eq_self (hB : B ∈ P) (hBA : B ⊆ A) : hull A P B = B :=
  (hull_subset hB Subset.rfl).antisymm (subset_hull hBA)

/-- If the ground set is closed and closed sets are closed under intersection, every hull is
closed. -/
theorem hull_mem (hA : A ∈ P) (hinter : ∀ ⦃B C⦄, B ∈ P → C ∈ P → B ∩ C ∈ P) :
    hull A P S ∈ P := by
  have he : hull A P S = (insert A {B ∈ P | S ⊆ B}).inf' (insert_nonempty _ _) id := by
    ext x
    simp [mem_hull, mem_inf']
  rw [he]
  refine inf'_induction _ _ (fun _ hB _ hC ↦ hinter hB hC) fun B hB ↦ ?_
  rcases mem_insert.mp hB with rfl | hB
  · exact hA
  · exact (mem_filter.mp hB).1

/-- The extremes of a set are among its points. -/
theorem extremes_subset : extremes P B ⊆ B := filter_subset _ _

/-- The extremes of a hull are among the generators: removing a point outside `S` from the hull
of `S` never leaves a closed set. -/
theorem extremes_hull_subset (hS : S ⊆ A) : extremes P (hull A P S) ⊆ S := by
  intro x hx
  obtain ⟨hxH, hxP⟩ := mem_extremes.mp hx
  by_contra hxS
  have hsub : S ⊆ (hull A P S).erase x := fun y hy ↦
    mem_erase.mpr ⟨fun h ↦ hxS (h ▸ hy), subset_hull hS hy⟩
  exact notMem_erase x _ (hull_subset hxP hsub hxH)

/-- Restriction does not change the extremes of a subset of the face. -/
theorem extremes_restrict (hCB : C ⊆ B) : extremes (restrict P B) C = extremes P C := by
  ext x
  simp only [mem_extremes, mem_restrict]
  exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, (erase_subset _ _).trans hCB⟩⟩

/-- In an intersection-closed family, the hull of a subset of a closed face `B ⊆ A` is the same
whether computed in `A` or in the restriction to `B`. -/
theorem hull_restrict (hinter : ∀ ⦃B C⦄, B ∈ P → C ∈ P → B ∩ C ∈ P) (hB : B ∈ P)
    (hBA : B ⊆ A) (hSB : S ⊆ B) : hull B (restrict P B) S = hull A P S := by
  ext x
  simp only [mem_hull, mem_restrict]
  constructor
  · rintro ⟨hxB, h⟩
    refine ⟨hBA hxB, fun C hC hSC ↦ ?_⟩
    exact (mem_inter.mp (h _ ⟨hinter hC hB, inter_subset_right⟩ (subset_inter hSC hSB))).1
  · rintro ⟨-, h⟩
    exact ⟨h B hB hSB, fun C hC hSC ↦ h C hC.1 hSC⟩

/-! ### Convex geometries -/

/-- The closed-set axioms of a finite **convex geometry** on the ground set `A`: closed sets
are subsets of `A`, the empty set and `A` are closed, closed sets are closed under intersection,
and the hull satisfies anti-exchange (if `x ∉ B` lies in the hull of `B ∪ {y}` for a closed `B`
and `y ≠ x`, then `y` does not lie in the hull of `B ∪ {x}`). -/
structure IsConvexGeometry (A : Finset α) (P : Finset (Finset α)) : Prop where
  /-- Closed sets are subsets of the ground set. -/
  subset_of_mem ⦃B : Finset α⦄ : B ∈ P → B ⊆ A
  /-- The empty set is closed. -/
  empty_mem : ∅ ∈ P
  /-- The ground set is closed. -/
  domain_mem : A ∈ P
  /-- Closed sets are closed under intersection. -/
  inter_mem ⦃B C : Finset α⦄ : B ∈ P → C ∈ P → B ∩ C ∈ P
  /-- Anti-exchange at closed sets. -/
  antiExchange ⦃B : Finset α⦄ : B ∈ P → ∀ ⦃x y : α⦄, x ≠ y → x ∉ B →
    x ∈ hull A P (insert y B) → y ∉ hull A P (insert x B)

namespace IsConvexGeometry

variable (hP : IsConvexGeometry A P)
include hP

/-- Every hull in a convex geometry is closed. -/
theorem hull_mem : hull A P S ∈ P := Geometry.hull_mem hP.domain_mem hP.inter_mem

/-- A subset of the ground set is its own hull exactly when it is closed. -/
theorem hull_eq_self_iff (hS : S ⊆ A) : hull A P S = S ↔ S ∈ P :=
  ⟨fun h ↦ h ▸ hP.hull_mem, fun h ↦ hull_eq_self h hS⟩

/-- **Accessibility.**  A closed set strictly inside a closed set `C` can be enlarged by a
single point of `C` to a closed set.  The proof takes a smallest closed set strictly between and
uses anti-exchange to see that it has only one new point. -/
theorem exists_insert_mem (hB : B ∈ P) (hC : C ∈ P) (hBC : B ⊂ C) :
    ∃ x ∈ C, x ∉ B ∧ insert x B ∈ P := by
  obtain ⟨D, hD, hmin⟩ := exists_min_image {D ∈ P | B ⊂ D ∧ D ⊆ C} card
    ⟨C, mem_filter.mpr ⟨hC, hBC, Subset.rfl⟩⟩
  obtain ⟨hDP, hBD, hDC⟩ := mem_filter.mp hD
  have hDA := hP.subset_of_mem hDP
  have hull_eq {y : α} (hyD : y ∈ D) (hyB : y ∉ B) : hull A P (insert y B) = D := by
    have hyBD : insert y B ⊆ D := insert_subset hyD hBD.subset
    have hin : insert y B ⊆ hull A P (insert y B) := subset_hull (hyBD.trans hDA)
    have hHD := hull_subset hDP hyBD (A := A)
    refine eq_of_subset_of_card_le hHD (hmin _ (mem_filter.mpr ⟨hP.hull_mem, ?_, hHD.trans hDC⟩))
    refine Finset.ssubset_iff_subset_ne.mpr ⟨(subset_insert _ _).trans hin, fun he ↦ hyB ?_⟩
    exact he ▸ hin (mem_insert_self _ _)
  obtain ⟨x, hxD, hxB⟩ := exists_of_ssubset hBD
  refine ⟨x, hDC hxD, hxB, ?_⟩
  suffices he : insert x B = D from he ▸ hDP
  refine (insert_subset hxD hBD.subset).antisymm fun y hyD ↦ ?_
  by_contra hy
  obtain ⟨hyx, hyB⟩ : y ≠ x ∧ y ∉ B := by simpa using hy
  exact hP.antiExchange hB (Ne.symm hyx) hxB (hull_eq hyD hyB ▸ hxD) (hull_eq hxD hxB ▸ hyD)

/-- Restriction of a convex geometry to a closed face is a convex geometry on that face. -/
theorem restrict (hB : B ∈ P) : IsConvexGeometry B (Geometry.restrict P B) where
  subset_of_mem _ hC := (mem_restrict.mp hC).2
  empty_mem := mem_restrict.mpr ⟨hP.empty_mem, empty_subset _⟩
  domain_mem := mem_restrict.mpr ⟨hB, Subset.rfl⟩
  inter_mem C D hC hD := mem_restrict.mpr
    ⟨hP.inter_mem (mem_restrict.mp hC).1 (mem_restrict.mp hD).1,
      inter_subset_left.trans (mem_restrict.mp hC).2⟩
  antiExchange C hC x y hxy hxC hx := by
    obtain ⟨hCP, hCB⟩ := mem_restrict.mp hC
    by_cases hyB : y ∈ B
    · have hxB : x ∈ B := hull_subset_domain hx
      have hBA := hP.subset_of_mem hB
      rw [hull_restrict hP.inter_mem hB hBA (insert_subset hyB hCB)] at hx
      rw [hull_restrict hP.inter_mem hB hBA (insert_subset hxB hCB)]
      exact hP.antiExchange hCP hxy hxC hx
    · exact fun hy ↦ hyB (hull_subset_domain hy)

/-- Every closed set other than the ground set lies in a closed coatom `A \ {x}`, whose removed
point `x` is therefore an extreme point of `A`. -/
theorem exists_coatom (hB : B ∈ P) (hne : B ≠ A) : ∃ x ∈ extremes P A, B ⊆ A.erase x := by
  obtain ⟨C, hC, hmax⟩ := exists_max_image {C ∈ P | B ⊆ C ∧ C ≠ A} card
    ⟨B, mem_filter.mpr ⟨hB, Subset.rfl, hne⟩⟩
  obtain ⟨hCP, hBC, hCA⟩ := mem_filter.mp hC
  obtain ⟨x, hxA, hxC, hxP⟩ := hP.exists_insert_mem hCP hP.domain_mem
    (Finset.ssubset_iff_subset_ne.mpr ⟨hP.subset_of_mem hCP, hCA⟩)
  have he : insert x C = A := by
    by_contra hn
    have := hmax _ (mem_filter.mpr ⟨hxP, hBC.trans (subset_insert _ _), hn⟩)
    rw [card_insert_of_notMem hxC] at this
    omega
  have hCe : A.erase x = C := by rw [← he, erase_insert hxC]
  exact ⟨x, mem_extremes.mpr ⟨hxA, hCe ▸ hCP⟩, hCe ▸ hBC⟩

/-- **Krein–Milman for convex geometries.**  Every closed set is the hull of its extreme
points. -/
theorem hull_extremes (hB : B ∈ P) : hull A P (extremes P B) = B := by
  have hBA := hP.subset_of_mem hB
  have hHB : hull A P (extremes P B) ⊆ B := hull_subset hB extremes_subset
  by_contra hne
  have hH : hull A P (extremes P B) ∈ Geometry.restrict P B := mem_restrict.mpr ⟨hP.hull_mem, hHB⟩
  obtain ⟨x, hx, hsub⟩ := (hP.restrict hB).exists_coatom hH hne
  rw [extremes_restrict Subset.rfl] at hx
  exact notMem_erase x B (hsub (subset_hull (extremes_subset.trans hBA) hx))

/-- For a closed set, the extremes are exactly the points `x ∈ B` outside the hull of
`B \ {x}`, the standard closure-theoretic notion of extreme point. -/
theorem mem_extremes_iff (hB : B ∈ P) : x ∈ extremes P B ↔ x ∈ B ∧ x ∉ hull A P (B.erase x) := by
  have hBA := hP.subset_of_mem hB
  rw [mem_extremes]
  refine ⟨fun ⟨hxB, he⟩ ↦ ⟨hxB, by rw [hull_eq_self he ((erase_subset _ _).trans hBA)]; simp⟩,
    fun ⟨hxB, hn⟩ ↦ ⟨hxB, ?_⟩⟩
  have he : hull A P (B.erase x) = B.erase x := by
    refine Subset.antisymm (fun y hy ↦ mem_erase.mpr ⟨?_, hull_subset hB (erase_subset _ _) hy⟩)
      (subset_hull ((erase_subset _ _).trans hBA))
    rintro rfl
    exact hn hy
  exact he ▸ hP.hull_mem

end IsConvexGeometry

/-- Being a convex geometry is decidable: the axioms are bounded quantifications over the finite
data (the points in anti-exchange may be taken in the ground set). -/
instance : Decidable (IsConvexGeometry A P) :=
  decidable_of_iff ((∀ B ∈ P, B ⊆ A) ∧ ∅ ∈ P ∧ A ∈ P ∧ (∀ B ∈ P, ∀ C ∈ P, B ∩ C ∈ P) ∧
      ∀ B ∈ P, ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x ∉ B →
        x ∈ hull A P (insert y B) → y ∉ hull A P (insert x B))
    ⟨fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, fun B C hB hC ↦ h4 B hB C hC,
        fun B hB x y hxy hxB hx hy ↦
          h5 B hB x (hull_subset_domain hx) y (hull_subset_domain hy) hxy hxB hx hy⟩,
      fun h ↦ ⟨h.subset_of_mem, h.empty_mem, h.domain_mem, fun _ hB _ hC ↦ h.inter_mem hB hC,
        fun B hB x _ y _ ↦ @h.antiExchange B hB x y⟩⟩

/-- **Anti-exchange from accessibility.**  An intersection-closed family containing `∅` and `A`,
in which every closed set other than `A` can be enlarged by one point to a closed set, is a
convex geometry.  The proof takes a largest closed superset of `B` omitting both points. -/
theorem IsConvexGeometry.of_accessible (hsub : ∀ ⦃B⦄, B ∈ P → B ⊆ A) (h0 : ∅ ∈ P) (hA : A ∈ P)
    (hinter : ∀ ⦃B C⦄, B ∈ P → C ∈ P → B ∩ C ∈ P)
    (hacc : ∀ ⦃B⦄, B ∈ P → B ≠ A → ∃ x ∉ B, insert x B ∈ P) : IsConvexGeometry A P where
  subset_of_mem := hsub
  empty_mem := h0
  domain_mem := hA
  inter_mem := hinter
  antiExchange B hB x y hxy hxB hx hy := by
    have hyB : y ∉ B := by
      intro hyB
      rw [insert_eq_of_mem hyB] at hx
      exact hxB (hull_subset hB Subset.rfl hx)
    obtain ⟨C, hC, hmax⟩ := exists_max_image {C ∈ P | B ⊆ C ∧ x ∉ C ∧ y ∉ C} card
      ⟨B, mem_filter.mpr ⟨hB, Subset.rfl, hxB, hyB⟩⟩
    obtain ⟨hCP, hBC, hxC, hyC⟩ := mem_filter.mp hC
    obtain ⟨z, hzC, hzP⟩ := hacc hCP (by rintro rfl; exact hxC (hull_subset_domain hx))
    have hzx : z ≠ x := by
      rintro rfl
      have := hull_subset hzP (insert_subset_insert z hBC) hy
      exact hyC ((mem_insert.mp this).resolve_left (Ne.symm hxy))
    have hzy : z ≠ y := by
      rintro rfl
      have := hull_subset hzP (insert_subset_insert z hBC) hx
      exact hxC ((mem_insert.mp this).resolve_left hxy)
    have := hmax _ (mem_filter.mpr ⟨hzP, hBC.trans (subset_insert _ _),
      by simp [Ne.symm hzx, hxC], by simp [Ne.symm hzy, hyC]⟩)
    rw [card_insert_of_notMem hzC] at this
    omega

end VaughtConjecture.Geometry
