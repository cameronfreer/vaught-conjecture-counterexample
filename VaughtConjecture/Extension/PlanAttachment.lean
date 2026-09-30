/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Attaching a point to a plan over a closed face, and amalgamating plans

Roadmap, Layer 3 (the coatom extension construction and the exact pinned extension, row 6 of the
table of 3.4: their support geometry) and Layer 1 (recursive visible-face plans); semantic
contract, item 2.

This file is about the plans alone: it constructs families of closed faces, not cells, rows, or
labels.

* The glued family `insert A (Q ∪ R)` of the recursive step restricts literally to `Q` on the
  coatom `A \ {a}` and to `R` on the coatom `A \ {b}` (`IsPlan.restrict_step_left`,
  `IsPlan.restrict_step_right`).  These are the plans of the two coatoms of the amalgam of
  [Kni26, §4.3].
* Every proper closed face lies in a closed coatom (`IsPlan.exists_coatom`).
* **Gluing over a coatom** (`IsPlan.attach_coatom`): a plan `P` on `A` and a plan `Q` on
  `insert x (A \ {a})` that agree below the closed coatom `A \ {a}` glue to a plan on
  `insert x A` restricting to `P` and to `Q`.
* **One-point attachment over a closed face** (`IsPlan.attach_one_over_face`): given a plan `P`
  on `A`, a closed face `B`, a point `x ∉ A`, and a plan `Q` on `insert x B` in which `B` is closed
  and which agrees with `P` below `B`, there is a plan on `insert x A` whose restrictions to `A`
  and to `insert x B` are `P` and `Q`, literally.  It is built one coatom at a time, along a chain
  of closed coatoms from `A` down to `B`.
* **One-point extension** retaining the plan (`IsPlan.exists_insert`), with a prescribed closed
  face extended by the new point (`IsPlan.extend_one_over_face`).
* **Amalgamation of two plans over a common closed face** (`IsPlan.amalgamate`).
* **The face must be closed** (`IsPlan.mem_of_insert_mem`): in a plan on `insert x A` restricting
  to `P` on `A`, if `insert x B` is closed for some `B ⊆ A`, then `B` is closed in `P`.  An
  attachment over a set that is not closed is therefore impossible; for the interval plan on
  three points see the regression at the end of the file.

Each attachment depends on the prescribed face: the construction does not make every one-point
extension of every closed face closed in one common plan.

## References

The recursive plan is Definition 2.1.1 and its restriction to a closed face Definition 2.1.5 of
R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026) [Kni26]; the amalgam of §4.3 there is built on the glued plan of the recursive
step.
-/

namespace VaughtConjecture.Geometry

open Finset

variable {α : Type*} [DecidableEq α] {A B C : Finset α} {P Q R : Finset (Finset α)} {a b x : α}

/-- Restricting to `A` and then to `B ⊆ A` is restricting to `B`. -/
theorem restrict_restrict (hBA : B ⊆ A) : restrict (restrict P A) B = restrict P B := by
  ext C
  simp only [mem_restrict]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hBA⟩, h.2⟩⟩

namespace IsPlan

/-- A plan restricted to its ground set is the plan itself. -/
theorem restrict_self (hP : IsPlan A P) : Geometry.restrict P A = P := by
  ext C
  simp only [mem_restrict, and_iff_left_iff_imp]
  exact hP.subset_of_mem

/-- If a family restricts to a plan on `C`, then `C` is one of its members. -/
theorem mem_of_restrict_eq (hQ : IsPlan C Q) (h : Geometry.restrict R C = Q) : C ∈ R :=
  (mem_restrict.mp (h ▸ hQ.ground_mem : C ∈ Geometry.restrict R C)).1

/-- The glued plan of the recursive step restricts literally to the plan `Q` of the coatom
`A \ {a}`. -/
theorem restrict_step_left (ha : a ∈ A) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
    (hagree : ∀ C ⊆ (A.erase a).erase b, C ∈ Q ↔ C ∈ R) :
    Geometry.restrict (insert A (Q ∪ R)) (A.erase a) = Q := by
  ext C
  simp only [mem_restrict, mem_insert, mem_union]
  refine ⟨fun ⟨h, hC⟩ ↦ ?_, fun h ↦ ⟨Or.inr (Or.inl h), hQ.subset_of_mem h⟩⟩
  rcases h with rfl | h | h
  · exact absurd (hC ha) (notMem_erase a C)
  · exact h
  · refine (hagree C fun y hy ↦ mem_erase.mpr ⟨?_, hC hy⟩).mpr h
    exact (mem_erase.mp (hR.subset_of_mem h hy)).1

/-- The glued plan of the recursive step restricts literally to the plan `R` of the coatom
`A \ {b}`. -/
theorem restrict_step_right (hb : b ∈ A) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
    (hagree : ∀ C ⊆ (A.erase a).erase b, C ∈ Q ↔ C ∈ R) :
    Geometry.restrict (insert A (Q ∪ R)) (A.erase b) = R := by
  ext C
  simp only [mem_restrict, mem_insert, mem_union]
  refine ⟨fun ⟨h, hC⟩ ↦ ?_, fun h ↦ ⟨Or.inr (Or.inr h), hR.subset_of_mem h⟩⟩
  rcases h with rfl | h | h
  · exact absurd (hC hb) (notMem_erase b C)
  · refine (hagree C fun y hy ↦ mem_erase.mpr ⟨?_, hQ.subset_of_mem h hy⟩).mp h
    exact (mem_erase.mp (hC hy)).1
  · exact h

/-- Every proper closed face lies in a closed coatom `A \ {a}`. -/
theorem exists_coatom (hP : IsPlan A P) (hB : B ∈ P) (hne : B ≠ A) :
    ∃ a ∈ A, A.erase a ∈ P ∧ B ⊆ A.erase a := by
  obtain ⟨a, ha, hBa⟩ := hP.isConvexGeometry.exists_coatom hB hne
  exact ⟨a, (mem_extremes.mp ha).1, (mem_extremes.mp ha).2, hBa⟩

/-- **Gluing over a coatom.**  A plan `P` on `A` and a plan `Q` on `insert x (A \ {a})`, for a
new point `x`, that agree below the closed coatom `A \ {a}` glue to the plan
`insert (insert x A) (P ∪ Q)` on `insert x A`, the recursive step at the points `x` and `a`. -/
theorem attach_coatom (hP : IsPlan A P) (ha : a ∈ A) (hx : x ∉ A) (hface : A.erase a ∈ P)
    (hQ : IsPlan (insert x (A.erase a)) Q)
    (hres : Geometry.restrict Q (A.erase a) = Geometry.restrict P (A.erase a)) :
    IsPlan (insert x A) (insert (insert x A) (P ∪ Q)) ∧
      Geometry.restrict (insert (insert x A) (P ∪ Q)) A = P ∧
      Geometry.restrict (insert (insert x A) (P ∪ Q)) (insert x (A.erase a)) = Q := by
  have hax : a ≠ x := fun h ↦ hx (h ▸ ha)
  have hex : (insert x A).erase x = A := erase_insert hx
  have hea : (insert x A).erase a = insert x (A.erase a) := erase_insert_of_ne hax.symm
  have hP' : IsPlan ((insert x A).erase x) P := by rwa [hex]
  have hQ' : IsPlan ((insert x A).erase a) Q := by rwa [hea]
  have hagree : ∀ C ⊆ ((insert x A).erase x).erase a, C ∈ P ↔ C ∈ Q := fun C hC ↦ by
    rw [hex] at hC
    have h := congrArg (C ∈ ·) hres
    simp only [mem_restrict, hC, and_true, eq_iff_iff] at h
    exact h.symm
  refine ⟨.step (mem_insert_self x A) (mem_insert_of_mem ha) hax.symm hP' hQ' ?_ hagree, ?_, ?_⟩
  · rw [hex]
    exact hface
  · simpa only [hex] using restrict_step_left (mem_insert_self x A) hP' hQ' hagree
  · simpa only [hea] using restrict_step_right (mem_insert_of_mem ha) hP' hQ' hagree

/-- **One-point attachment over a closed face.**  Let `P` be a plan on `A`, `B` a closed face,
`x ∉ A` a new point, and `Q` a plan on `insert x B` that agrees with `P` below `B`.  Then some plan
on `insert x A` restricts literally to `P` on `A` and to `Q` on `insert x B`. -/
theorem attach_one_over_face (hP : IsPlan A P) (hB : B ∈ P) (hx : x ∉ A)
    (hQ : IsPlan (insert x B) Q) (hres : Geometry.restrict Q B = Geometry.restrict P B) :
    ∃ R, IsPlan (insert x A) R ∧ Geometry.restrict R A = P ∧
      Geometry.restrict R (insert x B) = Q := by
  induction A using Finset.strongInduction generalizing B P Q with
  | H A ih =>
    by_cases hBA : B = A
    · subst hBA
      exact ⟨Q, hQ, hres.trans hP.restrict_self, hQ.restrict_self⟩
    obtain ⟨a, ha, hface, hBa⟩ := hP.exists_coatom hB hBA
    obtain ⟨E, hE, hEa, hEB⟩ := ih (A.erase a) (erase_ssubset ha) (hP.restrict hface)
      (mem_restrict.mpr ⟨hB, hBa⟩) (fun h ↦ hx (mem_of_mem_erase h)) hQ
      (by rw [restrict_restrict hBa, hres])
    obtain ⟨hR, hRA, hRE⟩ := hP.attach_coatom ha hx hface hE
      hEa
    refine ⟨_, hR, hRA, ?_⟩
    rw [← restrict_restrict (insert_subset_insert x hBa), hRE, hEB]

/-- **One-point extension.**  Every plan on `A` is the restriction of a plan on `insert x A`, for a
new point `x`. -/
theorem exists_insert (hP : IsPlan A P) (hx : x ∉ A) :
    ∃ R, IsPlan (insert x A) R ∧ Geometry.restrict R A = P := by
  have hQ : IsPlan (insert x (∅ : Finset α)) {∅, {x}} := by
    simpa only [insert_empty] using IsPlan.singleton x
  have hres : Geometry.restrict ({∅, {x}} : Finset (Finset α)) ∅ = Geometry.restrict P ∅ := by
    ext C
    simp only [mem_restrict, subset_empty, mem_insert, mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩
      exact ⟨hP.empty_mem, rfl⟩
    · rintro ⟨-, rfl⟩
      exact ⟨Or.inl rfl, rfl⟩
  obtain ⟨R, hR, hRA, -⟩ := hP.attach_one_over_face hP.empty_mem hx hQ hres
  exact ⟨R, hR, hRA⟩

/-- One-point extension through a prescribed closed face: for a closed face `B` of a plan on `A`
and a new point `x`, some plan on `insert x A` restricts to the given plan on `A` and has
`insert x B` closed.  The plan depends on `B`. -/
theorem extend_one_over_face (hP : IsPlan A P) (hB : B ∈ P) (hx : x ∉ A) :
    ∃ R, IsPlan (insert x A) R ∧ Geometry.restrict R A = P ∧ insert x B ∈ R := by
  obtain ⟨Q, hQ, hQB⟩ := (hP.restrict hB).exists_insert fun h ↦ hx (hP.subset_of_mem hB h)
  obtain ⟨R, hR, hRA, hRB⟩ := hP.attach_one_over_face hB hx hQ
    hQB
  exact ⟨R, hR, hRA, hQ.mem_of_restrict_eq hRB⟩

/-- **Amalgamation of plans over a common closed face.**  Plans `P` on `A` and `Q` on `C` in
which `A ∩ C` is closed, and which agree below it, are the restrictions of one plan on
`A ∪ C`. -/
theorem amalgamate (hP : IsPlan A P) (hQ : IsPlan C Q) (hAP : A ∩ C ∈ P) (hCQ : A ∩ C ∈ Q)
    (hres : Geometry.restrict P (A ∩ C) = Geometry.restrict Q (A ∩ C)) :
    ∃ R, IsPlan (A ∪ C) R ∧ Geometry.restrict R A = P ∧ Geometry.restrict R C = Q := by
  induction C using Finset.strongInduction generalizing A P Q with
  | H C ih =>
    by_cases hCA : C ⊆ A
    · rw [inter_eq_right.mpr hCA] at hres
      refine ⟨P, by rwa [union_eq_left.mpr hCA], hP.restrict_self, ?_⟩
      rw [hres, hQ.restrict_self]
    have hne : A ∩ C ≠ C := fun he ↦ hCA (inter_eq_right.mp he)
    obtain ⟨x, hxC, hface, hsub⟩ := hQ.exists_coatom hCQ hne
    have hxA : x ∉ A := fun hxA ↦ notMem_erase x C (hsub (mem_inter.mpr ⟨hxA, hxC⟩))
    have hi : A ∩ C.erase x = A ∩ C := by
      rw [inter_erase, erase_eq_of_notMem fun h ↦ hxA (mem_inter.mp h).1]
    obtain ⟨R', hR', hR'A, hR'C⟩ := ih (C.erase x) (erase_ssubset hxC) hP
      (hQ.restrict hface) (hi ▸ hAP) (hi ▸ mem_restrict.mpr ⟨hCQ, hsub⟩)
      (by rw [hi, restrict_restrict hsub, hres])
    have hCx : insert x (C.erase x) = C := insert_erase hxC
    obtain ⟨S, hS, hSA, hSC⟩ := hR'.attach_one_over_face
      ((hQ.restrict hface).mem_of_restrict_eq hR'C) (by simp [hxA])
      (hCx.symm ▸ hQ) hR'C.symm
    have hu : insert x (A ∪ C.erase x) = A ∪ C := by
      rw [← union_insert, hCx]
    refine ⟨S, hu ▸ hS, ?_, hCx ▸ hSC⟩
    rw [← restrict_restrict subset_union_left, hSA, hR'A]

/-- **The attached face must be closed.**  If a plan on `insert x A`, with `x ∉ A`, restricts to
`P` on `A` and contains `insert x B` for some `B ⊆ A`, then `B` is closed in `P`. -/
theorem mem_of_insert_mem (hR : IsPlan (insert x A) R) (hx : x ∉ A)
    (hRA : Geometry.restrict R A = P)
    (hA : A ∈ R) (hBA : B ⊆ A) (hB : insert x B ∈ R) : B ∈ P := by
  have he : A ∩ insert x B = B := by
    rw [inter_insert_of_notMem hx, inter_eq_right.mpr hBA]
  rw [← hRA, mem_restrict]
  exact ⟨he ▸ hR.infClosed hA hB, hBA⟩

end IsPlan

/-! ### Examples -/

/-- One-point attachment over the closed face `{0}` of the interval plan on `{0, 1, 2}`. -/
private example : ∃ R, IsPlan (insert 3 {0, 1, 2}) R ∧
    Geometry.restrict R {0, 1, 2} = intervalPlan ({0, 1, 2} : Finset ℕ) ∧ insert 3 {0} ∈ R :=
  (isPlan_intervalPlan _).extend_one_over_face (by decide) (by decide)

/-- Regression: the face must be closed.  The set `{0, 2}` is not closed in the interval plan on
`{0, 1, 2}`, so no plan on `{0, 1, 2, 3}` restricting to that plan contains `{0, 2, 3}`. -/
private example : ¬ ∃ R, IsPlan (insert 3 {0, 1, 2}) R ∧
    Geometry.restrict R {0, 1, 2} = intervalPlan ({0, 1, 2} : Finset ℕ) ∧ insert 3 {0, 2} ∈ R := by
  rintro ⟨R, hR, hRA, hB⟩
  have h := hR.mem_of_insert_mem (by decide) hRA
    ((isPlan_intervalPlan _).mem_of_restrict_eq hRA) (by decide) hB
  exact absurd h (by decide)

end VaughtConjecture.Geometry
