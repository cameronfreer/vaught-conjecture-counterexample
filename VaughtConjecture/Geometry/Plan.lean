/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.ConvexGeometry

/-!
# Recursive visible-face plans

A **plan** (an amalgamation plan) on a finite set `A` is a family `P` of subsets of `A`,
the *visible faces* or closed sets, built recursively (`IsPlan A P`):

* the plan on `∅` is `{∅}` and the plan on `{a}` is `{∅, {a}}`;
* for distinct `a, b ∈ A`, plans `Q` on `A \ {a}` and `R` on `A \ {b}` in which the common face
  `A \ {a, b}` is visible in `Q` and on whose subsets `Q` and `R` agree glue to the plan
  `insert A (Q ∪ R)` on `A`.

The main theorem `isPlan_iff_isConvexGeometry_and_card_extremes` identifies plans with the
finite convex geometries (`IsConvexGeometry`) in which every closed set with at least two points
has exactly two extreme points.  Not every convex geometry is a plan: all subsets of a
three-point set form a convex geometry whose ground set has three extreme points
(`not_isPlan_powerset_univ_fin_three` in `VaughtConjecture.Geometry.Examples`).  Consequences
developed here:

* closed sets are closed under intersection (`IsPlan.infClosed`), every singleton of the ground
  set is closed (`IsPlan.singleton_mem`), and plans restrict to plans on closed faces
  (`IsPlan.restrict`);
* the **two-generator property**: every closed set is the hull of its at most two extreme points
  (`IsConvexGeometry.hull_extremes`, `IsPlan.card_extremes_le_two`), so every hull is generated
  by at most two of its generators (`IsPlan.exists_subset_card_le_two_hull_eq`), and the
  generating pair of a hull is recovered as its extremes (`IsPlan.extremes_hull`).

The pair of extremes of a closed set need not itself be closed, and its hull need not be small;
see `VaughtConjecture.Geometry.Examples`.

See `roadmap/README.md`, Layer 1, `roadmap/EXPOSITIONS.md` §1, and
`roadmap/SEMANTIC_CONTRACT.md`, item 2.

## References

The recursive plan is Definition 2.1.1 ("amalgamation plan"), and restriction to a visible face
is Definition 2.1.5, of R. W. Knight, *A counterexample to Vaught's Conjecture using generalised
Stone spaces* (draft, 20 February 2026) [Kni26].  The reading of plans as convex geometries is
the formalization's own.
-/

namespace VaughtConjecture.Geometry

open Finset

variable {α : Type*} [DecidableEq α] {A B C S : Finset α} {P Q R : Finset (Finset α)} {x : α}

/-- `IsPlan A P`: the family `P` is a recursive visible-face plan on the finite set `A`.  The
base plans are `{∅}` on `∅` and `{∅, {a}}` on `{a}`.  A plan on `A` glues plans `Q` on
`A \ {a}` and `R` on `A \ {b}` for distinct `a, b ∈ A`, provided the common face `A \ {a, b}` is
visible in `Q` and `Q`, `R` have the same members below it; the result is `Q ∪ R` together with
`A` itself (the amalgamation plan of [Kni26, Definition 2.1.1]). -/
inductive IsPlan : Finset α → Finset (Finset α) → Prop
  /-- The plan on the empty set. -/
  | empty : IsPlan ∅ {∅}
  /-- The plan on a singleton. -/
  | singleton (a : α) : IsPlan {a} {∅, {a}}
  /-- Gluing two plans on one-point deletions that agree on their common face. -/
  | step {A : Finset α} {a b : α} {Q R : Finset (Finset α)} (ha : a ∈ A) (hb : b ∈ A)
      (hab : a ≠ b) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
      (hface : (A.erase a).erase b ∈ Q)
      (hagree : ∀ C ⊆ (A.erase a).erase b, C ∈ Q ↔ C ∈ R) :
      IsPlan A (insert A (Q ∪ R))

namespace IsPlan

/-- Every visible face is a subset of the ground set. -/
theorem subset_of_mem (hP : IsPlan A P) (hB : B ∈ P) : B ⊆ A := by
  induction hP generalizing B with
  | empty => simp_all
  | singleton a =>
    simp only [mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl <;> simp
  | step _ _ _ _ _ _ _ ihQ ihR =>
    rcases mem_insert.mp hB with rfl | hB
    · exact Subset.rfl
    rcases mem_union.mp hB with hB | hB
    · exact (ihQ hB).trans (erase_subset _ _)
    · exact (ihR hB).trans (erase_subset _ _)

/-- The ground set is a visible face. -/
theorem ground_mem (hP : IsPlan A P) : A ∈ P := by
  cases hP <;> simp

/-- The empty set is a visible face. -/
theorem empty_mem (hP : IsPlan A P) : ∅ ∈ P := by
  induction hP with
  | empty => simp
  | singleton a => simp
  | step _ _ _ _ _ _ _ ihQ _ => exact mem_insert_of_mem (mem_union_left _ ihQ)

/-- A subset of `(A \ {a}) \ {b}` lying in `A \ {a}` and `A \ {b}`. -/
private theorem subset_erase_erase {a b : α} (ha : S ⊆ A.erase a) (hb : S ⊆ A.erase b) :
    S ⊆ (A.erase a).erase b := fun _ hx ↦
  mem_erase.mpr ⟨(mem_erase.mp (hb hx)).1, ha hx⟩

/-- In a glued plan, the faces below the left deletion `A \ {a}` are exactly those of `Q`. -/
private theorem mem_step_left {a b : α} (ha : a ∈ A) (hQ : IsPlan (A.erase a) Q)
    (hR : IsPlan (A.erase b) R) (hagree : ∀ C ⊆ (A.erase a).erase b, C ∈ Q ↔ C ∈ R)
    (hS : S ⊆ A.erase a) : S ∈ insert A (Q ∪ R) ↔ S ∈ Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_insert_of_mem (mem_union_left _ h)⟩
  rcases mem_insert.mp h with rfl | h
  · exact absurd (hS ha) (notMem_erase a S)
  rcases mem_union.mp h with h | h
  · exact h
  · exact (hagree S (subset_erase_erase hS (hR.subset_of_mem h))).mpr h

/-- In a glued plan, the faces below the right deletion `A \ {b}` are exactly those of `R`. -/
private theorem mem_step_right {a b : α} (hb : b ∈ A) (hQ : IsPlan (A.erase a) Q)
    (hagree : ∀ C ⊆ (A.erase a).erase b, C ∈ Q ↔ C ∈ R)
    (hS : S ⊆ A.erase b) : S ∈ insert A (Q ∪ R) ↔ S ∈ R := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_insert_of_mem (mem_union_right _ h)⟩
  rcases mem_insert.mp h with rfl | h
  · exact absurd (hS hb) (notMem_erase b S)
  rcases mem_union.mp h with h | h
  · exact (hagree S (subset_erase_erase (hQ.subset_of_mem h) hS)).mp h
  · exact h

/-- Visible faces are closed under intersection. -/
theorem infClosed (hP : IsPlan A P) : InfClosed (P : Set (Finset α)) := by
  intro B hB C hC
  rw [mem_coe] at hB hC ⊢
  rw [inf_eq_inter]
  induction hP generalizing B C with
  | empty => simp_all
  | singleton a =>
    simp only [mem_insert, mem_singleton] at hB hC
    rcases hB with rfl | rfl <;> rcases hC with rfl | rfl <;> simp
  | @step A a b Q R ha hb hab hQ hR hface hagree ihQ ihR =>
    -- A face of `Q` meets a face of `R` inside the common face.
    have cross {U V : Finset α} (hU : U ∈ Q) (hV : V ∈ R) : U ∩ V ∈ R := by
      have hUc : U ∩ (A.erase a).erase b ∈ R :=
        (hagree _ inter_subset_right).mp (ihQ hU hface)
      have he : U ∩ (A.erase a).erase b ∩ V = U ∩ V := by
        rw [inter_right_comm, inter_eq_left.mpr]
        exact subset_erase_erase (inter_subset_left.trans (hQ.subset_of_mem hU))
          (inter_subset_right.trans (hR.subset_of_mem hV))
      exact he ▸ ihR hUc hV
    have hQA {U : Finset α} (hU : U ∈ Q) : U ⊆ A := (hQ.subset_of_mem hU).trans (erase_subset _ _)
    have hRA {U : Finset α} (hU : U ∈ R) : U ⊆ A := (hR.subset_of_mem hU).trans (erase_subset _ _)
    simp only [mem_insert, mem_union] at hB hC ⊢
    rcases hB with rfl | hB | hB <;> rcases hC with rfl | hC | hC
    · simp
    · exact Or.inr (Or.inl (by rwa [inter_eq_right.mpr (hQA hC)]))
    · exact Or.inr (Or.inr (by rwa [inter_eq_right.mpr (hRA hC)]))
    · exact Or.inr (Or.inl (by rwa [inter_eq_left.mpr (hQA hB)]))
    · exact Or.inr (Or.inl (ihQ hB hC))
    · exact Or.inr (Or.inr (cross hB hC))
    · exact Or.inr (Or.inr (by rwa [inter_eq_left.mpr (hRA hB)]))
    · exact Or.inr (Or.inr (inter_comm B C ▸ cross hC hB))
    · exact Or.inr (Or.inr (ihR hB hC))

/-- **Accessibility**: every visible face other than the ground set extends by one point to a
visible face. -/
theorem exists_insert_mem (hP : IsPlan A P) (hB : B ∈ P) (hne : B ≠ A) :
    ∃ x ∉ B, insert x B ∈ P := by
  induction hP generalizing B with
  | empty => simp_all
  | singleton a =>
    simp only [mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl
    · exact ⟨a, notMem_empty a, by simp⟩
    · exact absurd rfl hne
  | @step A a b Q R ha hb hab hQ hR hface hagree ihQ ihR =>
    have hA {c : α} (hc : c ∈ A) : insert c (A.erase c) = A := insert_erase hc
    rcases mem_insert.mp hB with rfl | hB
    · exact absurd rfl hne
    rcases mem_union.mp hB with hB | hB
    · by_cases he : B = A.erase a
      · exact ⟨a, he ▸ notMem_erase a A, by rw [he, hA ha]; exact mem_insert_self _ _⟩
      · obtain ⟨x, hx, hxQ⟩ := ihQ hB he
        exact ⟨x, hx, mem_insert_of_mem (mem_union_left _ hxQ)⟩
    · by_cases he : B = A.erase b
      · exact ⟨b, he ▸ notMem_erase b A, by rw [he, hA hb]; exact mem_insert_self _ _⟩
      · obtain ⟨x, hx, hxR⟩ := ihR hB he
        exact ⟨x, hx, mem_insert_of_mem (mem_union_right _ hxR)⟩

/-- In a glued plan on `A` at `a, b`, the extreme points of the ground set are exactly `a` and `b`:
the only visible one-point deletions of `A` are `A \ {a}` and `A \ {b}`. -/
private theorem extremes_step {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hQ : IsPlan (A.erase a) Q)
    (hR : IsPlan (A.erase b) R) : extremes (insert A (Q ∪ R)) A = {a, b} := by
  ext x
  simp only [mem_extremes, mem_insert, mem_union, mem_singleton]
  constructor
  · rintro ⟨hx, h | h | h⟩
    · exact absurd (h.symm ▸ hx) (notMem_erase x A)
    · refine Or.inl (by_contra fun hxa ↦ notMem_erase a A ?_)
      exact hQ.subset_of_mem h (mem_erase.mpr ⟨Ne.symm hxa, ha⟩)
    · refine Or.inr (by_contra fun hxb ↦ notMem_erase b A ?_)
      exact hR.subset_of_mem h (mem_erase.mpr ⟨Ne.symm hxb, hb⟩)
  · rintro (rfl | rfl)
    · exact ⟨ha, Or.inr (Or.inl hQ.ground_mem)⟩
    · exact ⟨hb, Or.inr (Or.inr hR.ground_mem)⟩

/-- Every visible face with at least two points has exactly two extreme points. -/
theorem card_extremes (hP : IsPlan A P) (hB : B ∈ P) (hcard : 1 < #B) :
    #(extremes P B) = 2 := by
  induction hP generalizing B with
  | empty => simp_all
  | singleton a =>
    simp only [mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl <;> simp at hcard
  | @step A a b Q R ha hb hab hQ hR hface hagree ihQ ihR =>
    rcases mem_insert.mp hB with rfl | hB
    · rw [extremes_step ha hb hQ hR, card_pair hab]
    rcases mem_union.mp hB with hB | hB
    · have he : extremes (insert A (Q ∪ R)) B = extremes Q B := by
        ext x
        simp only [mem_extremes]
        rw [mem_step_left ha hQ hR hagree
          ((erase_subset x B).trans (hQ.subset_of_mem hB))]
      exact he ▸ ihQ hB hcard
    · have he : extremes (insert A (Q ∪ R)) B = extremes R B := by
        ext x
        simp only [mem_extremes]
        rw [mem_step_right hb hQ hagree
          ((erase_subset x B).trans (hR.subset_of_mem hB))]
      exact he ▸ ihR hB hcard

/-- A plan is a convex geometry: anti-exchange follows from accessibility. -/
theorem isConvexGeometry (hP : IsPlan A P) : IsConvexGeometry A P :=
  .of_accessible (fun _ ↦ hP.subset_of_mem) hP.empty_mem hP.ground_mem hP.infClosed
    fun _ ↦ hP.exists_insert_mem

/-- On a ground set with at most one point, a family of subsets containing `∅` and the ground set
is a plan (the base plan `{∅}` or `{∅, {a}}`). -/
theorem of_card_le_one (hA : #A ≤ 1) (hsub : ∀ ⦃B⦄, B ∈ P → B ⊆ A) (h0 : ∅ ∈ P) (hAP : A ∈ P) :
    IsPlan A P := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · suffices he : P = {∅} from he ▸ IsPlan.empty
    ext B
    simp only [mem_singleton]
    exact ⟨fun hB ↦ subset_empty.mp (hsub hB), fun h ↦ h ▸ h0⟩
  · obtain ⟨a, rfl⟩ := card_eq_one.mp (le_antisymm hA hne.card_pos)
    suffices he : P = {∅, {a}} from he ▸ IsPlan.singleton a
    ext B
    simp only [mem_insert, mem_singleton]
    refine ⟨fun hB ↦ subset_singleton_iff.mp (hsub hB), ?_⟩
    rintro (rfl | rfl)
    · exact h0
    · exact hAP

end IsPlan

/-- A convex geometry in which every closed set with at least two points has exactly two
extreme points is a plan.  By strong induction on the ground set: its two extreme points `a, b`
give closed coatoms `A \ {a}`, `A \ {b}`, the restrictions to these are plans, and every other
closed set lies below one of them. -/
theorem IsConvexGeometry.isPlan (hP : IsConvexGeometry A P)
    (htwo : ∀ B ∈ P, 1 < #B → #(extremes P B) = 2) : IsPlan A P := by
  induction hn : #A using Nat.strong_induction_on generalizing A P with
  | _ n ih =>
    subst hn
    rcases le_or_gt #A 1 with hA | hA
    · exact .of_card_le_one hA hP.subset_of_mem hP.empty_mem hP.ground_mem
    -- The two extreme points `a, b` of `A` give the closed coatoms `A \ {a}` and `A \ {b}`.
    obtain ⟨a, b, hab, hext⟩ := card_eq_two.mp (htwo A hP.ground_mem hA)
    obtain ⟨haA, haP⟩ := mem_extremes.mp (by simp [hext] : a ∈ extremes P A)
    obtain ⟨hbA, hbP⟩ := mem_extremes.mp (by simp [hext] : b ∈ extremes P A)
    -- The restriction to a smaller closed set is a plan, by induction.
    have sub {C : Finset α} (hC : C ∈ P) (hlt : #C < #A) : IsPlan C (Geometry.restrict P C) := by
      refine ih _ hlt (hP.restrict hC) (fun B hB hcard ↦ ?_) rfl
      rw [extremes_restrict (mem_restrict.mp hB).2]
      exact htwo B (mem_restrict.mp hB).1 hcard
    -- Every closed set other than `A` lies in one of the two coatoms.
    have he :
        P = insert A (Geometry.restrict P (A.erase a) ∪ Geometry.restrict P (A.erase b)) := by
      ext C
      simp only [mem_insert, mem_union, mem_restrict]
      refine ⟨fun hC ↦ ?_, ?_⟩
      · by_cases hCA : C = A
        · exact Or.inl hCA
        obtain ⟨x, hx, hCx⟩ := hP.exists_coatom hC hCA
        rw [hext, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Or.inr (Or.inl ⟨hC, hCx⟩)
        · exact Or.inr (Or.inr ⟨hC, hCx⟩)
      · rintro (rfl | h | h)
        · exact hP.ground_mem
        · exact h.1
        · exact h.1
    -- Glue the two restrictions along the common face `A \ {a, b}`, which is closed.
    have hface : (A.erase a).erase b ∈ P :=
      (by rw [inter_erase, inter_eq_left.mpr (erase_subset _ _)] :
          A.erase a ∩ A.erase b = (A.erase a).erase b) ▸ hP.infClosed haP hbP
    rw [he]
    refine IsPlan.step haA hbA hab (sub haP (card_erase_lt_of_mem haA))
      (sub hbP (card_erase_lt_of_mem hbA)) (mem_restrict.mpr ⟨hface, erase_subset _ _⟩)
      fun C hC ↦ ?_
    simp only [mem_restrict]
    exact ⟨fun h ↦ ⟨h.1, hC.trans (erase_subset_erase b (erase_subset a A))⟩,
      fun h ↦ ⟨h.1, hC.trans (erase_subset _ _)⟩⟩

/-- **Plans are exactly the convex geometries with two extremes.**  A family is a recursive
visible-face plan on `A` iff it is a convex geometry on `A` in which every closed set with at
least two points has exactly two extreme points. -/
theorem isPlan_iff_isConvexGeometry_and_card_extremes :
    IsPlan A P ↔ IsConvexGeometry A P ∧ ∀ B ∈ P, 1 < #B → #(extremes P B) = 2 :=
  ⟨fun hP ↦ ⟨hP.isConvexGeometry, fun _ ↦ hP.card_extremes⟩, fun h ↦ h.1.isPlan h.2⟩

/-- Being a plan is decidable, through its characterization as a two-extreme convex
geometry. -/
instance : Decidable (IsPlan A P) :=
  decidable_of_iff _ isPlan_iff_isConvexGeometry_and_card_extremes.symm

namespace IsPlan

/-- The restriction of a plan to a visible face is a plan on that face. -/
theorem restrict (hP : IsPlan A P) (hB : B ∈ P) : IsPlan B (restrict P B) := by
  refine (hP.isConvexGeometry.restrict hB).isPlan fun C hC hcard ↦ ?_
  rw [extremes_restrict (mem_restrict.mp hC).2]
  exact hP.card_extremes (mem_restrict.mp hC).1 hcard

/-- Every visible face has at most two extreme points. -/
theorem card_extremes_le_two (hP : IsPlan A P) (hB : B ∈ P) : #(extremes P B) ≤ 2 := by
  rcases Nat.lt_or_ge 1 #B with h | h
  · exact (hP.card_extremes hB h).le
  · have := card_le_card (extremes_subset (P := P) (B := B))
    omega

/-- Every singleton of the ground set is a visible face: the hull of `{x}` has no extreme point
other than `x`, so it cannot have two points. -/
theorem singleton_mem (hP : IsPlan A P) (hx : x ∈ A) : {x} ∈ P := by
  have hH : hull A P {x} ∈ P := hP.isConvexGeometry.hull_mem
  have hxH : x ∈ hull A P {x} := subset_hull (singleton_subset_iff.mpr hx) (mem_singleton_self x)
  have h1 : #(hull A P {x}) ≤ 1 := by
    by_contra h
    have := card_le_card (extremes_hull_subset (P := P) (singleton_subset_iff.mpr hx))
    rw [hP.card_extremes hH (by omega), card_singleton] at this
    omega
  have he : hull A P {x} = {x} :=
    eq_singleton_iff_unique_mem.mpr ⟨hxH, fun y hy ↦ card_le_one.mp h1 y hy x hxH⟩
  exact he ▸ hH

/-- **Two generators.**  The hull of any subset of the ground set is the hull of at most two of
its points, namely the extreme points of the hull. -/
theorem exists_subset_card_le_two_hull_eq (hP : IsPlan A P) (hS : S ⊆ A) :
    ∃ T ⊆ S, #T ≤ 2 ∧ hull A P T = hull A P S :=
  ⟨extremes P (hull A P S), extremes_hull_subset hS,
    hP.card_extremes_le_two hP.isConvexGeometry.hull_mem,
    hP.isConvexGeometry.hull_extremes hP.isConvexGeometry.hull_mem⟩

/-- A set of at most two points of the ground set is recovered from its hull as the extreme points
of the hull.  In particular distinct such sets have distinct hulls. -/
@[simp] theorem extremes_hull (hP : IsPlan A P) (hS : S ⊆ A) (h2 : #S ≤ 2) :
    extremes P (hull A P S) = S := by
  rcases Nat.lt_or_ge 1 #S with h | h
  · refine eq_of_subset_of_card_le (extremes_hull_subset hS) ?_
    rw [hP.card_extremes hP.isConvexGeometry.hull_mem
      (h.trans_le (card_le_card (subset_hull hS)))]
    exact h2
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [hull_eq_self hP.empty_mem (empty_subset _)]
    exact subset_empty.mp extremes_subset
  obtain ⟨a, rfl⟩ := card_eq_one.mp (le_antisymm h hne.card_pos)
  rw [hull_eq_self (hP.singleton_mem (singleton_subset_iff.mp hS)) hS]
  ext x
  simp only [mem_extremes, mem_singleton]
  exact ⟨And.left, fun hx ↦ ⟨hx, by simpa [hx] using hP.empty_mem⟩⟩

end IsPlan

end VaughtConjecture.Geometry
