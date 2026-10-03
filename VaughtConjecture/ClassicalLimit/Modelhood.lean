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
(modelhood, infinitude, and terminality); Layer 3, 3.4 (the cap-to-model theorem); semantic
contract, item 5 (the four unchanged extension families) and item 11.

For modelhood, `M` is a structure of the hull language `hullLanguage α` whose age is the age of
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

The proof is at the stage `α` itself.  Modelhood at `α` does not follow from the cap-to-model
theorem at `ω` applied to the reduction to `ω`: the labels at least `ω` become the formal top
there, and the uniformity and dominance clauses for `γ ≥ ω` are lost.  Nor does it follow from
modelhood of the reductions to the lower block stages, which for this realization are known to be
models only as reductions of a model at `α` (`Realization.IsModel.reduce`): that would be circular.

**From the coatom extension property with apex** (`isModel_reconstruct_of_hasApexCoatomExtensions`).
The plain coatom extension property gives the uniformity instances
(`StageType.nonempty_cofaces_inter_uniformityFamily`), and the form with apex the dominance
instances (`StageType.nonempty_cofaces_inter_dominanceFamily`), at every legal type, top-free or
not.  Under the coatom extension property with apex at `α`, a Fraïssé limit of the age of top-free
charts exists (`exists_isFraisseLimit_topFreeAge`, for a countable limit stage `α`), and its
reconstructed realization is a model.

**Infinitude.**  A model at a positive stage is infinite (`Realization.IsModel.infinite`).
Without the nonemptiness hypotheses, the plain coatom extension property gives a coface of every
legal type (`StageType.exists_extension`), and receiving it over a whole occurrence gives a new
point (`infinite_of_age_eq_of_hasCoatomExtensions`, from
`Realization.infinite_of_hasFiniteCutReceiving`).

**Terminality** (`reduce_ne_reconstruct`).  The reconstructed realization at a stage `α` that is
zero or a limit is not the reduction of a model at any higher stage `β > α`: the uniformity clause
of that model at `γ = α` realizes a label at least `α`, which becomes the formal top in the
reduction (`Realization.IsModel.exists_not_isTopFree_reduce`), while every reconstructed type is
top-free (`isTopFree_of_reconstruct_eval`).  This uses only top-freeness and that one clause of the
higher model: neither modelhood of the reconstructed realization nor any uniqueness of model
expansions.  It is a statement about the realization, not the statement that the base reduct has
no model expansion to a higher stage, which needs uniqueness of expansions at `α`.

**Not here.**  Placement of the witness in the loss `D_η \ D_{η+1}` of the expansion domains is
still to be proved.  Membership in `D_η` is to come from modelhood at the block stage `λ_η` and
transport of model expansions along an isomorphism with a code on `ℕ`; non-membership in
`D_{η+1}` from terminality and uniqueness of model expansions at `λ_η`, a named hypothesis (for
every `ξ + 1 ≤ η`, uniqueness of the extension of a model expansion from `λ_ξ` to `λ_{ξ+1}`; none
at `η = 0`).  Global termination, finite-cut receiving of every model, exact projected receiving,
and uniqueness of the Fraïssé limit are not assumed anywhere in this file.

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

/-- **Infinitude of the carrier from receiving** (roadmap, the top-free witnesses, step 7): for a
structure whose age is the age of top-free charts and which is ultrahomogeneous, at a positive
stage that is zero or a limit with the coatom extension property, the carrier is infinite.  Every
legal type has a coface (`StageType.exists_extension`), and receiving it over an occurrence gives
a new point.  Modelhood is not used. -/
theorem infinite_of_age_eq_of_hasCoatomExtensions (hext : HasCoatomExtensions.{u} α)
    (hage : (hullLanguage.{u} α).age M = topFreeAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccPrelimit α) (h0 : 0 < α) :
    Infinite M := by
  obtain ⟨-, hc, hcov, hl, -, -⟩ := reconstruct_of_age_eq hage
  refine (reconstruct α M).infinite_of_hasFiniteCutReceiving h0 hc hcov
    (hasFiniteCutReceiving_reconstruct hage hu hα) fun x ↦ ?_
  obtain ⟨Q, hQ, hQx⟩ := exists_extension hext (hl _ _ x.eval_tuple)
  exact ⟨Q, hQ, hQx⟩

/-- **Terminality of the reconstructed realization** (roadmap, the top-free witnesses, step 7): for
a structure whose age is contained in the age of top-free charts, at a stage `α` that is zero or a
limit, no model at a higher stage `β > α` reduces to the reconstructed realization.  Only
top-freeness of the reconstructed types and the uniformity clause of the higher model at `γ = α`
are used (`Realization.IsModel.exists_not_isTopFree_reduce`); no uniqueness of model expansions. -/
theorem reduce_ne_reconstruct (hage : (hullLanguage.{u} α).age M ⊆ topFreeAge α)
    (hα : Order.IsSuccPrelimit α) {β : Ordinal.{u}} (hαβ : α < β)
    {S : Realization.{u, 0} β M} (hS : S.IsModel) : S.reduce hα ≠ reconstruct α M := by
  intro h
  obtain ⟨n, t, p, ht, hp⟩ := hS.exists_not_isTopFree_reduce hα hαβ
  rw [h] at ht
  exact hp (isTopFree_of_reconstruct_eval hage ht)

end VaughtConjecture
