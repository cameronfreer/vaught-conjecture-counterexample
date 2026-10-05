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
  nonempty losses gives the thin `ℵ₁` spectrum of the density sentence;
* next-block uniqueness derived from finite-cut receiving and forcing donors
  (`NextBlockUniqueness.of_forcingDonors`) in place of `hu`; the theorems with forcing donors are
  the theorems with next-block uniqueness applied to it, by `rfl`;
* the continuation criterion from stable capped receiving: the theorems with (R4), the coatom
  extension property with apex at every next block, and stable lawfulness are the theorems with
  the continuation criterion applied to `ContinuationCriterion.of_hasApexCoatomExtensions`, by
  `rfl`; under the other inputs, the criterion is equivalent to stable lawfulness of the models
  in its domain; and the hypotheses of the spectrum theorem in this form.

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

/-- The spectrum theorem with forcing donors is the spectrum theorem with next-block uniqueness,
applied to `NextBlockUniqueness.of_forcingDonors`. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable)
    (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    densitySentence_hasThinAlephOneSpectrum_of_forcingDonors hcap hrec hF hc hn =
      densitySentence_hasThinAlephOneSpectrum_of_modelExpansions hcap
        (.of_forcingDonors hrec hF) hrec hc hn :=
  rfl

/-- The thinness theorem with forcing donors is the thinness theorem with next-block uniqueness,
applied to `NextBlockUniqueness.of_forcingDonors`. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    densitySentence_isThinOnNatModels_of_forcingDonors hcap hrec hF hc =
      densitySentence_isThinOnNatModels_of_modelExpansions hcap
        (.of_forcingDonors hrec hF) hrec hc :=
  rfl

/-! ### The continuation criterion from stable capped receiving -/

/-- The spectrum theorem from stable capped receiving is the spectrum theorem from the terminal
classification, applied to `ContinuationCriterion.of_hasApexCoatomExtensions`. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hR4 : StableCappedReceiving.{0})
    (hext : ∀ ξ < ω₁, StageType.HasApexCoatomExtensions.{0} (blockStage (ξ + 1)))
    (hlaw : ModelStableLawfulness.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    densitySentence_hasThinAlephOneSpectrum_of_stableCappedReceiving hcap hrec hF hR4 hext hlaw
        hres hhol hn =
      densitySentence_hasThinAlephOneSpectrum_of_terminalClassification hcap hrec hF
        (.of_hasApexCoatomExtensions hR4 hext hlaw) hres hhol hn :=
  rfl

/-- Under (R1), forcing donors, (R4) and the coatom extension property with apex at every next
block, the continuation criterion is equivalent to stable lawfulness of the models in its domain:
the hypothesis `hlaw` of the spectrum theorem below is the content of the criterion. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hR4 : StableCappedReceiving.{0})
    (hext : ∀ ξ < ω₁, StageType.HasApexCoatomExtensions.{0} (blockStage (ξ + 1))) :
    ContinuationCriterion.{0} ↔ ModelStableLawfulness.{0} :=
  continuationCriterion_iff_modelStableLawfulness hR4
    (fun ξ hξ ↦ .of_hasApexCoatomExtensions (hext ξ hξ)
      (isSuccLimit_blockStage (ξ + 1)).isSuccPrelimit) hF
    (fun _ _ R' hξ hR' ↦ hrec.finiteExtensionReceiving.receive (isSuccLimit_blockStage _)
      (blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).add_one_lt hξ)) R' hR')

/-- **The hypotheses of the spectrum theorem from stable capped receiving**, as printed by
`#check @densitySentence_hasThinAlephOneSpectrum_of_stableCappedReceiving`:
```
CapToModel →
  FiniteCutReceiving →
    (∀ ξ < Ordinal.omega 1, ForcingDonors ξ) →
      StableCappedReceiving →
        (∀ ξ < Ordinal.omega 1, StageType.HasApexCoatomExtensions (blockStage (ξ + 1))) →
          ModelStableLawfulness →
            Realization.ResidualReceiving →
              (Realization.HollowReceiving fun {α} {M} => Realization.IsCoverHollowAtBlock) →
                (∀ ξ < Ordinal.omega 1, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) →
                  HasThinAlephOneSpectrum densitySentence
```
No continuation criterion, no hypothesis on the countability of the losses, and no next-block
uniqueness; each hypothesis is still to be proved. -/
example : CapToModel.{0} → FiniteCutReceiving.{0} → (∀ ξ < ω₁, ForcingDonors.{0} ξ) →
    StableCappedReceiving.{0} →
    (∀ ξ < ω₁, StageType.HasApexCoatomExtensions.{0} (blockStage (ξ + 1))) →
    ModelStableLawfulness.{0} → Realization.ResidualReceiving.{0, 0} →
    Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock →
    (∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) →
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_stableCappedReceiving

end VaughtConjecture.MainTheorem
