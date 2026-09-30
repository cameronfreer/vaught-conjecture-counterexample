/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Closure.Equivariance
import VaughtConjecture.Realization.Hull
import VaughtConjecture.Realization.Transport

/-!
# The canonical closure of a realization

Roadmap, Layer 2 (canonical finite hulls; actual finite supports are precisely the finite closed
sets) and Layer 0, "Finite closure" (equivariance on finite hulls extends to the global closure);
semantic contract, item 2; the expositions, §1 ("the operator `cl(A) = ⋃ {h(F) : F ⊆ A finite}`
is a locally finite, finitary anti-exchange closure; its finite closed sets are exactly the
supports of actual charts; every individual closure membership has a witness involving at most
two elements").

For an exactly consistent covering realization `R`, the **canonical closure** `R.closure hR hc`
is InfinitaryLogic's finite-character extension `setClosure` of the canonical finite hull
(`Realization.hullClosure`).  It agrees with the finite hull on finite sets (`closure_coe`), so
it is locally finite (`finite_closure`), and:

* its finite closed sets are exactly the supports of occurrences (`isClosed_coe_iff`,
  `isClosed_iff_of_finite`);
* every membership `a ∈ cl(A)` has a witness `T ⊆ A` with at most two points
  (`mem_closure_iff_exists_card_le_two`).  This concerns single memberships: it does not say that
  an infinite closed set is the closure of a pair, nor that the hull of a pair is a two-point
  support;
* it satisfies anti-exchange at closed sets (`closure_antiExchange`, from
  `setClosure_antiExchange`);
* it is equivariant under transport along bijections of carriers (`finiteHull_map`,
  `image_closure`, from `Closure.image_setClosure`) and unchanged by stage reduction
  (`finiteHull_reduce`, `closure_reduce`), since reduction keeps every scheme.
-/

universe u v w

namespace VaughtConjecture.Realization

open Finset InfinitaryLogic.FiniteSupportClosure

variable {α β : Ordinal.{u}} {M : Type v} {N : Type w} {R : Realization.{u, v} α M}
  (hR : R.IsConsistent) (hc : R.IsCovering) {A : Set M} {a : M}

/-! ### The closure and its finite closed sets -/

/-- The **canonical closure** of an exactly consistent covering realization: a point is in the
closure of `A` if it lies in the canonical hull of a finite subset of `A`. -/
noncomputable def closure : ClosureOperator (Set M) :=
  setClosure (R.hullClosure hR hc)

/-- On a finite set the canonical closure is the canonical finite hull. -/
@[simp] theorem closure_coe (F : Finset M) : R.closure hR hc ↑F = ↑(R.finiteHull F) :=
  setClosure_finset _ F

/-- Membership in the canonical closure has a finite witness. -/
theorem mem_closure_iff : a ∈ R.closure hR hc A ↔ ∃ F : Finset M, ↑F ⊆ A ∧ a ∈ R.finiteHull F :=
  Iff.rfl

/-- **Two-point witnesses**: a point is in the canonical closure of `A` exactly when it is in the
canonical hull of a subset of `A` with at most two points. -/
theorem mem_closure_iff_exists_card_le_two :
    a ∈ R.closure hR hc A ↔ ∃ T : Finset M, ↑T ⊆ A ∧ #T ≤ 2 ∧ a ∈ R.finiteHull T := by
  refine ⟨fun ⟨F, hFA, ha⟩ ↦ ?_, fun ⟨T, hTA, _, ha⟩ ↦ ⟨T, hTA, ha⟩⟩
  obtain ⟨T, hTF, hT, he⟩ := exists_subset_card_le_two_finiteHull_eq hR hc F
  exact ⟨T, (coe_subset.mpr hTF).trans hFA, hT, he ▸ ha⟩

/-- The canonical closure is **locally finite**: the closure of a finite set is finite. -/
theorem finite_closure (hA : A.Finite) : (R.closure hR hc A).Finite := by
  lift A to Finset M using hA
  rw [closure_coe]
  exact finite_toSet _

/-- **Finite closed sets are supports**: a finite set is closed for the canonical closure exactly
when it is the support of an occurrence. -/
theorem isClosed_coe_iff (S : Finset M) :
    (R.closure hR hc).IsClosed ↑S ↔ R.IsSupport S := by
  rw [ClosureOperator.isClosed_iff]
  change R.closure hR hc ↑S = ↑S ↔ _
  rw [closure_coe, coe_inj, finiteHull_eq_self_iff hR hc]

/-- A finite set of points is closed for the canonical closure exactly when it is the set of
points of an occurrence. -/
theorem isClosed_iff_of_finite (hA : A.Finite) :
    (R.closure hR hc).IsClosed A ↔ ∃ x : R.Occurrence, ↑x.support = A := by
  lift A to Finset M using hA
  simp only [isClosed_coe_iff, IsSupport, coe_inj]

/-- **Anti-exchange** for the canonical closure at a closed set `A`: if `a ∉ A` lies in the
closure of `A` with `b ≠ a` added, then `b` does not lie in the closure of `A` with `a` added. -/
theorem closure_antiExchange (hA : R.closure hR hc A = A) {b : M} (hab : a ≠ b)
    (haA : a ∉ A) (ha : a ∈ R.closure hR hc (insert b A)) : b ∉ R.closure hR hc (insert a A) := by
  classical
  exact setClosure_antiExchange _ (fun S _ _ hxy hx ↦ finiteHull_antiExchange hR hc S hxy hx) hA
    hab haA ha

/-! ### Transport along bijections of carriers -/

/-- The support of a transported occurrence is the image of the support. -/
@[simp] theorem Occurrence.support_map (e : M ≃ N) (x : R.Occurrence) :
    (x.map e).support = x.support.map e.toEmbedding := by
  rw [Occurrence.support, Occurrence.support, Finset.map_map]
  rfl

/-- The hull inside a transported occurrence is the image of the hull. -/
theorem Occurrence.hull_map (e : M ≃ N) (x : R.Occurrence) (F : Finset M) :
    (x.map e).hull (F.map e.toEmbedding) = (x.hull F).map e.toEmbedding := by
  have hcoords : (x.map e).coords (F.map e.toEmbedding) = x.coords F := by
    refine Finset.ext fun (i : Fin x.arity) ↦ ((x.map e).mem_coords (i := i)).trans ?_
    exact mem_map_equiv.trans ((Iff.of_eq (congrArg (· ∈ F) (e.symm_apply_apply (x.tuple i)))).trans
      x.mem_coords.symm)
  change (Geometry.hull univ x.type.toCellScheme.faces ((x.map e).coords (F.map e.toEmbedding))).map
    (x.tuple.trans e.toEmbedding) = _
  rw [hcoords, ← Finset.map_map]
  rfl

include hR hc in
/-- **Equivariance of the canonical hull**: transport along a bijection of carriers carries the
canonical hull of `F` to the canonical hull of the image of `F`. -/
theorem finiteHull_map (e : M ≃ N) (F : Finset M) :
    (R.map e).finiteHull (F.map e.toEmbedding) = (R.finiteHull F).map e.toEmbedding := by
  obtain ⟨x, hx⟩ := hc.exists_subset_support F
  rw [finiteHull_eq hR hc x hx, finiteHull_eq (hR.map e) (hc.map e) (x.map e)
    (by simpa using (Finset.map_subset_map (f := e.toEmbedding)).mpr hx), Occurrence.hull_map]

/-- **Equivariance of the canonical closure**: transport along a bijection of carriers carries the
closure of `A` onto the closure of the image of `A`. -/
theorem image_closure (e : M ≃ N) (A : Set M) :
    e '' R.closure hR hc A = (R.map e).closure (hR.map e) (hc.map e) (e '' A) := by
  classical
  exact Closure.image_setClosure _ _ e fun F _ ↦ by
    simpa [map_eq_image] using (finiteHull_map hR hc e F).symm

/-! ### Stage reduction -/

/-- The hull inside a reduced occurrence is the hull inside the occurrence. -/
@[simp] theorem Occurrence.hull_reduce (hβ : Order.IsSuccPrelimit β) (x : R.Occurrence)
    (F : Finset M) : (x.reduce hβ).hull F = x.hull F :=
  rfl

include hR hc in
/-- **Stage reduction keeps the canonical hull.** -/
@[simp] theorem finiteHull_reduce (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).finiteHull = R.finiteHull := funext fun F ↦ by
  obtain ⟨x, hx⟩ := hc.exists_subset_support F
  rw [finiteHull_eq hR hc x hx, finiteHull_eq (hR.reduce hβ) (hc.reduce hβ) (x.reduce hβ) hx,
    Occurrence.hull_reduce]

/-- **Stage reduction keeps the canonical closure.** -/
theorem closure_reduce (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).closure (hR.reduce hβ) (hc.reduce hβ) = R.closure hR hc := by
  unfold closure
  congr 1
  exact ClosureOperator.ext _ _ fun F ↦ by simp [finiteHull_reduce hR hc hβ]

end VaughtConjecture.Realization
