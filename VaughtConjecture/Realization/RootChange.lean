/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Language.Structure
import VaughtConjecture.Order.Tail
import VaughtConjecture.Realization.ClosureCardinality

/-!
# The exterior order up to tail equivalence is a base-isomorphism invariant

For an exactly consistent covering realization `R` and an infinite closed set `B` of its canonical
closure, the **exterior relation** "`x` lies in the closure of `B` with `y` added" is a linear
order on the points outside `B` (`Realization.exteriorOrderIsLinearTarget`).  This file records
that relation, with no change, as a `LinearOrder` on `{x // x ∉ B}`
(`Realization.exteriorLinearOrder`), so that tail equivalence (`Order.TailEquivalent`) of two
exterior orders can be stated, and states and proves four targets:

* `ImageClosureOfBaseEquivTarget` (closure preservation): an isomorphism of the base structures
  (the structures of the reductions to `ω`) of two exactly consistent covering realizations with
  legal types, at any two stages, carries the canonical closure of every set onto the canonical
  closure of its image.  Route: `Realization.map_eq_of_equiv` on the reductions to `ω`, then
  `Realization.image_closure` and `Realization.closure_reduce`; no higher label is reconstructed.
* `ExteriorRootChangeOrderTarget` (root change): enlarging an infinite closed root `B` to a closed
  `D ⊇ B` makes the points outside `D` an upper set of the exterior order of `B`, on which the
  exterior orders of `B` and of `D` agree.  Route: `Closure.exteriorRootChangeTarget` and
  `Closure.rootBeforeExteriorTarget` at the canonical hull.
* `BaseEquivExteriorTailEquivalentTarget` (tail equivalence): if two such realizations on
  uncountable carriers have isomorphic base structures, then above countably infinite closed roots
  `B` and `C` their exterior orders are tail-equivalent.  With `e` the isomorphism and
  `D = cl(e '' B ∪ C)`, the witnesses are the points outside `e ⁻¹' D` and the points outside `D`,
  matched by `e`; `D` is countable (`Closure.countableSetClosureTarget`), so both sets are
  nonempty.
* `DensityExteriorTailEquivalentTarget`: the same for two models of the density sentence, with
  the canonical closures of their realizations.

All targets are given-model statements: they are about every realization (or every model of the
density sentence) satisfying their hypotheses, and assert no existence of models.  All are proved,
each by the theorem of the same name in lower camel case; the density-sentence form is derived
from the realization form.
-/

universe u v w

namespace VaughtConjecture.Realization

open FirstOrder Language

variable {α : Ordinal.{u}} {M : Type v}

/-- The **exterior order** of an exactly consistent covering realization above an infinite closed
set `B` of the canonical closure, as a linear order on the points outside `B`: `x ≤ y` when `x`
lies in the closure of `B` with `y` added.  The relation is the one of
`Realization.ExteriorOrderIsLinearTarget`, and its linearity is
`Realization.exteriorOrderIsLinearTarget`; no instance is declared. -/
@[instance_reducible]
noncomputable def exteriorLinearOrder (R : Realization.{u, v} α M) (hR : R.IsConsistent)
    (hc : R.IsCovering) {B : Set M} (hB : (R.closure hR hc).IsClosed B) (hBi : B.Infinite) :
    LinearOrder {x : M // x ∉ B} :=
  have h := exteriorOrderIsLinearTarget R hR hc hB hBi
  { le := fun x y ↦ x.1 ∈ R.closure hR hc (insert y.1 B)
    le_refl := h.refl
    le_trans := fun _ _ _ ↦ h.trans _ _ _
    le_antisymm := fun _ _ ↦ h.antisymm _ _
    le_total := h.total
    toDecidableLE := Classical.decRel _ }

/-- **Target: base isomorphisms carry closures to closures.**  Let `R` at stage `α` on `M` and
`S` at stage `β` on `N` be exactly consistent and covering, with legal types.  An isomorphism `e`
of their base structures (the structures of their reductions to `ω`) carries the canonical closure
in `R` of every set onto the canonical closure in `S` of its image.  No isomorphism of `R` and `S`
themselves is assumed.  Given-model statement.  Proved
(`Realization.imageClosureOfBaseEquivTarget`). -/
def ImageClosureOfBaseEquivTarget : Prop :=
  ∀ ⦃α β : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type w⦄ (R : Realization.{u, v} α M)
    (S : Realization.{u, w} β N) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hS : S.IsConsistent) (hcS : S.IsCovering), R.HasLegalTypes → S.HasLegalTypes →
    letI := (R.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
    letI := (S.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
    ∀ (e : M ≃[baseLanguage.{u}] N) (A : Set M),
      e '' R.closure hR hc A = S.closure hS hcS (e '' A)

/-- Equal realizations have equal canonical closures, whatever the consistency and covering proofs
given to them. -/
theorem closure_congr {R R' : Realization.{u, v} α M} (h : R = R') (hR : R.IsConsistent)
    (hc : R.IsCovering) (hR' : R'.IsConsistent) (hc' : R'.IsCovering) :
    R.closure hR hc = R'.closure hR' hc' := by
  subst h
  rfl

/-- **Base isomorphisms carry closures to closures**, the target form.  The isomorphism of the
base structures carries the reduction of `R` to `ω` onto the reduction of `S` to `ω`
(`Realization.map_eq_of_equiv`, legal types being kept by reduction); transport along a bijection
carries closures to closures (`Realization.image_closure`), and reduction keeps the canonical
closure (`Realization.closure_reduce`). -/
theorem imageClosureOfBaseEquivTarget : ImageClosureOfBaseEquivTarget.{u, v, w} := by
  intro α β M N R S hR hc hS hcS hlR hlS
  have hω : Order.IsSuccPrelimit (Ordinal.omega0.{u}) := Ordinal.isSuccLimit_omega0.isSuccPrelimit
  intro e A
  have hmap := map_eq_of_equiv (hlR.reduce hω) (hlS.reduce hω) e
  rw [← closure_reduce hR hc hω, ← closure_reduce hS hcS hω]
  refine (image_closure (hR.reduce hω) (hc.reduce hω) _ A).trans ?_
  rw [closure_congr hmap _ _ (hS.reduce hω) (hcS.reduce hω)]
  rfl

/-- **Target: changing the root of the exterior order.**  Let `R` be exactly consistent and
covering, `B` an infinite closed set and `D ⊇ B` a closed set.  In the exterior order of `B`, the
points outside `D` form an upper set, and on these points the exterior order of `B` agrees with the
exterior order of `D`.  Countability of `B` and `D` is not a hypothesis.  Given-model statement.
Proved (`Realization.exteriorRootChangeOrderTarget`). -/
def ExteriorRootChangeOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M) (hR : R.IsConsistent)
    (hc : R.IsCovering) ⦃B D : Set M⦄ (hB : (R.closure hR hc).IsClosed B) (hBi : B.Infinite)
    (hD : (R.closure hR hc).IsClosed D) (hBD : B ⊆ D),
    letI := R.exteriorLinearOrder hR hc hB hBi
    letI := R.exteriorLinearOrder hR hc hD (hBi.mono hBD)
    IsUpperSet {x : {x : M // x ∉ B} | x.1 ∉ D} ∧
      ∀ x y : {x : M // x ∉ D},
        x ≤ y ↔ (⟨x.1, fun h ↦ x.2 (hBD h)⟩ : {x : M // x ∉ B}) ≤ ⟨y.1, fun h ↦ y.2 (hBD h)⟩

/-- **Changing the root of the exterior order**, the target form, at the canonical hull, which is
generated by two points: a point of `D` lies strictly before a point outside `D`
(`Closure.rootBeforeExteriorTarget`), and the closure of `D` with an outside point added is the
closure of `B` with it added (`Closure.exteriorRootChangeTarget`). -/
theorem exteriorRootChangeOrderTarget : ExteriorRootChangeOrderTarget.{u, v} := by
  intro α M R hR hc B D hB hBi hD hBD
  have hgen := exists_subset_card_le_two_hullClosure_eq hR hc
  refine ⟨fun x y hxy hx hyD ↦ ?_, fun x y ↦ ?_⟩
  · exact (Closure.rootBeforeExteriorTarget (R.hullClosure hR hc) hgen hBi hD hBD hyD hx).2 hxy
  · exact Iff.of_eq (congrArg (x.1 ∈ ·)
      (Closure.exteriorRootChangeTarget (R.hullClosure hR hc) hgen hBi hD hBD y.2))

/-- **Target: base-isomorphic realizations have tail-equivalent exterior orders.**  Let `R` at
stage `α` on an uncountable `M` and `S` at stage `β` on `N` be exactly consistent and covering,
with legal types, and let their base structures (the structures of their reductions to `ω`) be
isomorphic.  For countably infinite closed sets `B` of `R` and `C` of `S`, the exterior order of
`R` above `B` and the exterior order of `S` above `C` are tail-equivalent.  Given-model
statement.  Proved (`Realization.baseEquivExteriorTailEquivalentTarget`). -/
def BaseEquivExteriorTailEquivalentTarget : Prop :=
  ∀ ⦃α β : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type w⦄ [Uncountable M] (R : Realization.{u, v} α M)
    (S : Realization.{u, w} β N) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hS : S.IsConsistent) (hcS : S.IsCovering), R.HasLegalTypes → S.HasLegalTypes →
    (letI := (R.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
     letI := (S.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
     Nonempty (M ≃[baseLanguage.{u}] N)) →
    ∀ ⦃B : Set M⦄ (hB : (R.closure hR hc).IsClosed B) (hBi : B.Infinite), B.Countable →
      ∀ ⦃C : Set N⦄ (hC : (S.closure hS hcS).IsClosed C) (hCi : C.Infinite), C.Countable →
        @Order.TailEquivalent {x : M // x ∉ B} {y : N // y ∉ C}
          (R.exteriorLinearOrder hR hc hB hBi) (S.exteriorLinearOrder hS hcS hC hCi)

/-- **Base-isomorphic realizations have tail-equivalent exterior orders**, the target form.  Let
`σ` be the bijection of a base isomorphism and `D` the closure in `S` of `σ '' B ∪ C`, a countable
closed set (`Closure.countableSetClosureTarget`) containing `C`.  Its preimage `σ ⁻¹' D` is closed
in `R` (`Realization.imageClosureOfBaseEquivTarget`) and contains `B`.  The points outside
`σ ⁻¹' D` and the points outside `D` are upper sets of the two exterior orders
(`Realization.exteriorRootChangeOrderTarget`), nonempty since `N` is uncountable and `D` is
countable, and `σ` matches them: by two changes of root (`Closure.exteriorRootChangeTarget`), the
comparison of `σ x` and `σ x'` above `C` is their comparison above `D`, which is the image under
`σ` of the comparison of `x` and `x'` above `σ ⁻¹' D`, which is their comparison above `B`. -/
theorem baseEquivExteriorTailEquivalentTarget :
    BaseEquivExteriorTailEquivalentTarget.{u, v, w} := by
  intro α β M N _ R S hR hc hS hcS hlR hlS he B hB hBi hBc C hC hCi hCc
  let := (R.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
  let := (S.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
  obtain ⟨e⟩ := he
  let σ : M ≃ N := e.toEquiv
  have himg : ∀ A, σ '' R.closure hR hc A = S.closure hS hcS (σ '' A) :=
    imageClosureOfBaseEquivTarget R S hR hc hS hcS hlR hlS e
  have : Uncountable N := σ.injective.uncountable
  -- the countable closed common root `D` in `N`, and its preimage in `M`
  set D := S.closure hS hcS (σ '' B ∪ C) with hDdef
  have hDcl : (S.closure hS hcS).IsClosed D := (S.closure hS hcS).isClosed_closure _
  have hDc : D.Countable :=
    Closure.countableSetClosureTarget (S.hullClosure hS hcS) ((hBc.image σ).union hCc)
  have hCD : C ⊆ D := Set.subset_union_right.trans ((S.closure hS hcS).le_closure _)
  have hBD' : B ⊆ σ ⁻¹' D := fun b hb ↦
    (S.closure hS hcS).le_closure _ (Or.inl ⟨b, hb, rfl⟩)
  have hD'cl : (R.closure hR hc).IsClosed (σ ⁻¹' D) := by
    refine (R.closure hR hc).isClosed_iff.mpr (?_ : R.closure hR hc (σ ⁻¹' D) = σ ⁻¹' D)
    rw [← σ.preimage_image (R.closure hR hc _), himg, σ.image_preimage, hDcl.closure_eq]
  obtain ⟨y₀, hy₀⟩ : ∃ y, y ∉ D := by
    by_contra h
    push Not at h
    exact not_countable (Set.countable_univ_iff.mp (hDc.mono fun y _ ↦ h y))
  have hgenR := exists_subset_card_le_two_hullClosure_eq hR hc
  have hgenS := exists_subset_card_le_two_hullClosure_eq hS hcS
  have hM : ∀ ⦃x⦄, x ∉ σ ⁻¹' D →
      R.closure hR hc (insert x (σ ⁻¹' D)) = R.closure hR hc (insert x B) :=
    Closure.exteriorRootChangeTarget (R.hullClosure hR hc) hgenR hBi hD'cl hBD'
  have hN : ∀ ⦃y⦄, y ∉ D → S.closure hS hcS (insert y D) = S.closure hS hcS (insert y C) :=
    Closure.exteriorRootChangeTarget (S.hullClosure hS hcS) hgenS hCi hDcl hCD
  refine ⟨{x | x.1 ∉ σ ⁻¹' D}, {y | y.1 ∉ D},
    (exteriorRootChangeOrderTarget R hR hc hB hBi hD'cl hBD').1,
    (exteriorRootChangeOrderTarget S hS hcS hC hCi hDcl hCD).1,
    ⟨⟨σ.symm y₀, fun h ↦ hy₀ (by simpa using hBD' h)⟩, by simpa using hy₀⟩,
    ⟨⟨y₀, fun h ↦ hy₀ (hCD h)⟩, hy₀⟩, ⟨?_⟩⟩
  refine
    { toFun := fun x ↦ ⟨⟨σ x.1.1, fun h ↦ x.2 (hCD h)⟩, x.2⟩
      invFun := fun y ↦ ⟨⟨σ.symm y.1.1, fun h ↦ y.2 (by simpa using hBD' h)⟩,
        fun h ↦ y.2 (by simpa using h)⟩
      left_inv := fun x ↦ by simp
      right_inv := fun y ↦ by simp
      map_rel_iff' := fun {x x'} ↦ ?_ }
  change σ x.1.1 ∈ S.closure hS hcS (insert (σ x'.1.1) C) ↔
    x.1.1 ∈ R.closure hR hc (insert x'.1.1 B)
  have hx' : σ x'.1.1 ∉ D := x'.2
  rw [← hN hx', ← hM x'.2, ← σ.injective.mem_set_image, himg, Set.image_insert_eq,
    σ.image_preimage]

/-- **Target: isomorphic models of the density sentence have tail-equivalent exterior orders.**
Let `M` and `N` be models of the density sentence, `M` uncountable, and let `M` and `N` be
isomorphic.  For countably infinite closed sets `B` and `C` of the canonical closures of their
realizations (`baseLanguage.toRealization`), the two exterior orders are tail-equivalent.  The
consistency and covering proofs are bound separately, as the canonical closure takes them as
arguments; they follow from the density sentence (`baseLanguage.realize_densitySentence_iff`).
Given-model statement.  Proved (`Realization.densityExteriorTailEquivalentTarget`). -/
def DensityExteriorTailEquivalentTarget : Prop :=
  ∀ ⦃M : Type v⦄ ⦃N : Type w⦄ [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]
    [Uncountable M], baseLanguage.densitySentence.{u}.Realize M →
    baseLanguage.densitySentence.{u}.Realize N → Nonempty (M ≃[baseLanguage.{u}] N) →
    ∀ (hR : (baseLanguage.toRealization M).IsConsistent)
      (hc : (baseLanguage.toRealization M).IsCovering)
      (hS : (baseLanguage.toRealization N).IsConsistent)
      (hcS : (baseLanguage.toRealization N).IsCovering) ⦃B : Set M⦄
      (hB : ((baseLanguage.toRealization M).closure hR hc).IsClosed B) (hBi : B.Infinite),
      B.Countable → ∀ ⦃C : Set N⦄
        (hC : ((baseLanguage.toRealization N).closure hS hcS).IsClosed C) (hCi : C.Infinite),
        C.Countable →
          @Order.TailEquivalent {x : M // x ∉ B} {y : N // y ∉ C}
            ((baseLanguage.toRealization M).exteriorLinearOrder hR hc hB hBi)
            ((baseLanguage.toRealization N).exteriorLinearOrder hS hcS hC hCi)

/-- **Isomorphic models of the density sentence have tail-equivalent exterior orders**, the target
form: `Realization.baseEquivExteriorTailEquivalentTarget` for the realizations of the two models at
stage `ω`, which have legal types (`baseLanguage.hasLegalTypes_toRealization`), are their own
reductions to `ω` (`Realization.reduce_self`), and have the given structures as their structures
(`baseLanguage.toStructure_toRealization`, a model of the density sentence being a type
assignment). -/
theorem densityExteriorTailEquivalentTarget : DensityExteriorTailEquivalentTarget.{u, v, w} := by
  intro M N _ _ _ hMΦ hNΦ ⟨e⟩ hR hc hS hcS B hB hBi hBc C hC hCi hCc
  have hω : Order.IsSuccPrelimit (Ordinal.omega0.{u}) := Ordinal.isSuccLimit_omega0.isSuccPrelimit
  have hsM : ((baseLanguage.toRealization M).reduce hω).toStructure = ‹_› := by
    rw [reduce_self, baseLanguage.toStructure_toRealization
      ((baseLanguage.realize_densitySentence_iff M).mp hMΦ).1]
  have hsN : ((baseLanguage.toRealization N).reduce hω).toStructure = ‹_› := by
    rw [reduce_self, baseLanguage.toStructure_toRealization
      ((baseLanguage.realize_densitySentence_iff N).mp hNΦ).1]
  refine baseEquivExteriorTailEquivalentTarget _ _ hR hc hS hcS
    baseLanguage.hasLegalTypes_toRealization baseLanguage.hasLegalTypes_toRealization ?_
    hB hBi hBc hC hCi hCc
  change Nonempty (@Language.Equiv baseLanguage.{u} M N
    ((baseLanguage.toRealization M).reduce hω).toStructure
    ((baseLanguage.toRealization N).reduce hω).toStructure)
  rw [hsM, hsN]
  exact ⟨e⟩

end VaughtConjecture.Realization
