/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ModelExpansionDomains

/-!
# Examples for the expansion domains of the density sentence

Special cases of `VaughtConjecture.MainTheorem.ModelExpansionDomains`:

* the fields of `modelExpansionDomains`: the domain is the expansion domain, the first domain is
  every class, and the limit clause is an inclusion whose reverse is the downward closure;
* logical agreement from finite-cut receiving, with the representative hypothesis
  `fun _ _ _ hq ↦ hq`;
* the composition: `modelExpansionDomains hcap hu` with finite-cut receiving and countable and
  nonempty losses gives the thin `ℵ₁` spectrum of the density sentence.
* next-block uniqueness derived from finite-cut receiving and forcing donors
  (`NextBlockUniqueness.of_forcingDonors`) in place of `hu`.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion
open scoped Ordinal

variable (hcap : CapToModel.{0}) (hu : NextBlockUniqueness.{0})

/-! ### The fields -/

/-- The domain at `η` is the expansion domain at `η`. -/
example (η : Ordinal.{0}) : (modelExpansionDomains hcap hu).domain η = expansionDomain η :=
  rfl

/-- The first domain is every class. -/
example : expansionDomain 0 = Set.univ :=
  (modelExpansionDomains hcap hu).zero

/-- The limit clause is an inclusion; the reverse inclusion is the downward closure. -/
example {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hlω : l < ω₁) :
    (⋂ ξ < l, (modelExpansionDomains hcap hu).domain ξ) =
      (modelExpansionDomains hcap hu).domain l :=
  ((modelExpansionDomains hcap hu).limit l hl hlω).antisymm
    (Set.subset_iInter₂ fun _ hξ ↦ (modelExpansionDomains hcap hu).antitone hξ.le)

/-! ### Logical agreement -/

/-- Logical agreement from finite-cut receiving of models, through finite-extension receiving and
the representative hypothesis `fun _ _ _ hq ↦ hq`. -/
example (hrec : FiniteCutReceiving.{0}) :
    (modelExpansionDomains hcap hu).HasLogicalAgreement densityTruth :=
  ExpansionDomains.hasLogicalAgreement_of_modelExpansions hrec.finiteExtensionReceiving
    fun _ _ _ hq ↦ hq

/-! ### The composition -/

/-- The composition: the expansion domains with finite-cut receiving and countable and nonempty
losses give the thin `ℵ₁` spectrum, through the general composition. -/
example (hrec : FiniteCutReceiving.{0})
    (hc : (modelExpansionDomains hcap hu).HasCountableLosses)
    (hn : (modelExpansionDomains hcap hu).HasNonemptyLosses) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_expansionDomains (modelExpansionDomains hcap hu)
    (modelExpansionDomains_hasLogicalAgreement hcap hu hrec) hc hn

/-- The composition with the conditions on the losses stated on the expansion domains
themselves. -/
example (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable)
    (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_modelExpansions hcap hu hrec hc hn

/-- Thinness alone needs no lower bound. -/
example (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    densitySentence.{0}.IsThinOnNatModels :=
  densitySentence_isThinOnNatModels_of_modelExpansions hcap hu hrec hc

/-- The nonempty losses give a model of the density sentence on `ℕ`. -/
example (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    HasModelOnNat :=
  ExpansionDomains.HasNonemptyLosses.hasModelOnNat (D := modelExpansionDomains hcap hu) ⟨hn⟩

/-! ### Next-block uniqueness from forcing donors -/

/-- The composition with the expansion domains built from next-block uniqueness derived from
finite-cut receiving and forcing donors, through the general composition. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hc : (modelExpansionDomains hcap (.of_forcingDonors hrec hF)).HasCountableLosses)
    (hn : (modelExpansionDomains hcap (.of_forcingDonors hrec hF)).HasNonemptyLosses) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_expansionDomains _
    (modelExpansionDomains_hasLogicalAgreement hcap _ hrec) hc hn

/-- The theorem with forcing donors is the theorem with next-block uniqueness, applied to
`NextBlockUniqueness.of_forcingDonors`. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable)
    (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_forcingDonors hcap hrec hF hc hn

end VaughtConjecture.MainTheorem
