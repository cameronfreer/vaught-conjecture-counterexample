/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Receiving
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Realization.CapToModel

/-!
# Modelhood of the reconstructed realization of a classical limit

Roadmap, the section "The top-free witnesses: the finite age and its classical limit", step 7
(modelhood); Layer 3, 3.4 (the cap-to-model theorem); semantic contract, item 5 (the four
unchanged extension families) and item 11.

Throughout, `M` is a structure of the hull language `hullLanguage α` whose age is the age of
top-free charts and which is ultrahomogeneous, at a nonzero limit stage `α`.

**Modelhood** (`isModel_reconstruct`).  The reconstructed realization `reconstruct α M` has a
nonempty carrier, legal top-free types, and is exactly consistent and covering
(`reconstruct_of_age_eq`), and it has the finite-cut receiving property
(`hasFiniteCutReceiving_reconstruct`).  The cap-to-model theorem at a nonzero limit stage
(`Realization.isModel_of_hasFiniteCutReceiving`) then makes it a model, given the nonemptiness of
the uniformity and dominance instances over its occurrences.  Those occurrences have legal
top-free types (`isTopFree_of_reconstruct_eval`), so the two hypotheses are stated for legal
top-free types only.  The conclusion is `Realization.IsModel` with its four families; exact
extension within the age is used for receiving, and is not part of the conclusion.

**From the coatom extension property with apex** (`isModel_reconstruct_of_hasApexCoatomExtensions`).
The plain coatom extension property gives the uniformity instances
(`StageType.nonempty_cofaces_inter_uniformityFamily`), and the form with apex the dominance
instances (`StageType.nonempty_cofaces_inter_dominanceFamily`), at every legal type, top-free or
not.  Under the coatom extension property with apex at `α`, a Fraïssé limit of the age of top-free
charts exists (`exists_isFraisseLimit_topFreeAge`, for a countable limit stage `α`), and its
reconstructed realization is a model.

The proof is at the stage `α` itself.  Modelhood at `α` does not follow from the cap-to-model
theorem at `ω` applied to the reduction to `ω`: the labels at least `ω` become the formal top
there, and the uniformity and dominance clauses for `γ ≥ ω` are lost.  Nor does it follow from
modelhood of the reductions to the lower block stages, which for this realization are known to be
models only as reductions of a model at `α` (`Realization.IsModel.reduce`).

## Placement

This file belongs to the section on the top-free witnesses of `roadmap/README.md`.

## References

Models are [Kni26, Definition 3.2.1]; the nonemptiness of the uniformity and dominance instances is
[Kni26, Lemmas 4.4.2 and 4.4.3].
-/

universe u

namespace VaughtConjecture

open FirstOrder Language Realization StageType

variable {α : Ordinal.{u}} {M : Type} [(hullLanguage.{u} α).Structure M]

/-- **Modelhood of the reconstructed realization** (roadmap, the top-free witnesses, step 7): for a
structure whose age is the age of top-free charts and which is ultrahomogeneous, at a nonzero limit
stage, the reconstructed realization is a model, given the nonemptiness of the uniformity
instances (`hunif`) and of the dominance instances (`hdom`) over legal top-free stage types. -/
theorem isModel_reconstruct (hage : (hullLanguage.{u} α).age M = topFreeAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccLimit α)
    (hunif : ∀ ⦃n : ℕ⦄ (p : StageType.{u} α n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{u}, Order.IsSuccPrelimit γ → γ < α →
        (p.cofaces ∩ uniformityFamily γ).Nonempty)
    (hdom : ∀ ⦃n : ℕ⦄ (p : StageType.{u} α n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{u}, γ < α → (p.cofaces ∩ dominanceFamily γ).Nonempty) :
    (reconstruct α M).IsModel := by
  obtain ⟨hne, hc, hcov, hl, htf, -⟩ := reconstruct_of_age_eq hage
  exact isModel_of_hasFiniteCutReceiving hα hne hl hc hcov
    (hasFiniteCutReceiving_reconstruct hage hu hα.isSuccPrelimit)
    (fun x ↦ hunif x.type (hl _ _ x.eval_tuple) (htf _ _ x.eval_tuple))
    (fun x ↦ hdom x.type (hl _ _ x.eval_tuple) (htf _ _ x.eval_tuple))

/-- **Modelhood of the reconstructed realization of a Fraïssé limit** of the age of top-free
charts, at a nonzero limit stage, given the nonemptiness of the uniformity and dominance instances
over legal top-free stage types. -/
theorem isModel_reconstruct_of_isFraisseLimit
    [Countable (Σ l, (hullLanguage.{u} α).Functions l)] [Countable M]
    (hM : IsFraisseLimit (topFreeAge.{u} α) M) (hα : Order.IsSuccLimit α)
    (hunif : ∀ ⦃n : ℕ⦄ (p : StageType.{u} α n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{u}, Order.IsSuccPrelimit γ → γ < α →
        (p.cofaces ∩ uniformityFamily γ).Nonempty)
    (hdom : ∀ ⦃n : ℕ⦄ (p : StageType.{u} α n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{u}, γ < α → (p.cofaces ∩ dominanceFamily γ).Nonempty) :
    (reconstruct α M).IsModel :=
  isModel_reconstruct hM.age hM.ultrahomogeneous hα hunif hdom

/-- **Modelhood of the reconstructed realization from the coatom extension property with apex**:
for a structure whose age is the age of top-free charts and which is ultrahomogeneous, at a
nonzero limit stage, the reconstructed realization is a model.  The uniformity instances are
nonempty under the plain coatom extension property, the dominance instances under the form with
apex. -/
theorem isModel_reconstruct_of_hasApexCoatomExtensions (hext : HasApexCoatomExtensions.{u} α)
    (hage : (hullLanguage.{u} α).age M = topFreeAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccLimit α) :
    (reconstruct α M).IsModel :=
  isModel_reconstruct hage hu hα
    (fun _ _ hp _ _ _ hγα ↦ nonempty_cofaces_inter_uniformityFamily hext.hasCoatomExtensions
      hα.isSuccPrelimit hp hγα)
    (fun _ _ hp _ _ hγα ↦ nonempty_cofaces_inter_dominanceFamily hext hα.isSuccPrelimit hp hγα)

end VaughtConjecture
