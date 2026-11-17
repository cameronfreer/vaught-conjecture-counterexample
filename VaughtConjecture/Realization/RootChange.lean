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
exterior orders can be stated, and states four targets:

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
density sentence) satisfying their hypotheses, and assert no existence of models.  All are stated
and open.
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
themselves is assumed.  Given-model statement.  Stated; open. -/
def ImageClosureOfBaseEquivTarget : Prop :=
  ∀ ⦃α β : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type w⦄ (R : Realization.{u, v} α M)
    (S : Realization.{u, w} β N) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hS : S.IsConsistent) (hcS : S.IsCovering), R.HasLegalTypes → S.HasLegalTypes →
    letI := (R.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
    letI := (S.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
    ∀ (e : M ≃[baseLanguage.{u}] N) (A : Set M),
      e '' R.closure hR hc A = S.closure hS hcS (e '' A)

/-- **Target: changing the root of the exterior order.**  Let `R` be exactly consistent and
covering, `B` an infinite closed set and `D ⊇ B` a closed set.  In the exterior order of `B`, the
points outside `D` form an upper set, and on these points the exterior order of `B` agrees with the
exterior order of `D`.  Countability of `B` and `D` is not a hypothesis.  Given-model statement.
Stated; open. -/
def ExteriorRootChangeOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M) (hR : R.IsConsistent)
    (hc : R.IsCovering) ⦃B D : Set M⦄ (hB : (R.closure hR hc).IsClosed B) (hBi : B.Infinite)
    (hD : (R.closure hR hc).IsClosed D) (hBD : B ⊆ D),
    letI := R.exteriorLinearOrder hR hc hB hBi
    letI := R.exteriorLinearOrder hR hc hD (hBi.mono hBD)
    IsUpperSet {x : {x : M // x ∉ B} | x.1 ∉ D} ∧
      ∀ x y : {x : M // x ∉ D},
        x ≤ y ↔ (⟨x.1, fun h ↦ x.2 (hBD h)⟩ : {x : M // x ∉ B}) ≤ ⟨y.1, fun h ↦ y.2 (hBD h)⟩

/-- **Target: base-isomorphic realizations have tail-equivalent exterior orders.**  Let `R` at
stage `α` on an uncountable `M` and `S` at stage `β` on `N` be exactly consistent and covering,
with legal types, and let their base structures (the structures of their reductions to `ω`) be
isomorphic.  For countably infinite closed sets `B` of `R` and `C` of `S`, the exterior order of
`R` above `B` and the exterior order of `S` above `C` are tail-equivalent.  Given-model
statement.  Stated; open. -/
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

/-- **Target: isomorphic models of the density sentence have tail-equivalent exterior orders.**
Let `M` and `N` be models of the density sentence, `M` uncountable, and let `M` and `N` be
isomorphic.  For countably infinite closed sets `B` and `C` of the canonical closures of their
realizations (`baseLanguage.toRealization`), the two exterior orders are tail-equivalent.  The
consistency and covering proofs are bound separately, as the canonical closure takes them as
arguments; they follow from the density sentence (`baseLanguage.realize_densitySentence_iff`).
Given-model statement.  Stated; open. -/
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

end VaughtConjecture.Realization
