/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Losses
import VaughtConjecture.Expansion.UniquenessOfForcing
import VaughtConjecture.MainTheorem.Assembly

/-!
# The expansion domains of the density sentence, and the main theorem for them, conditionally

Roadmap, the reduction of the main theorem to expansion domains (condition 1, and the
composition with conditions 2–4) and Layer 5; `IMPLEMENTATION.md`, checkpoint 5; semantic
contract, items 5 and 9.

**The expansion domains.**  `modelExpansionDomains hcap hu : ExpansionDomains DensityClass` is
the family of expansion domains whose domain at `η` is the actual expansion domain
`Expansion.expansionDomain η`: the classes with a code on `ℕ` whose structure has a model
expansion to the block stage `λ_η = ω + ω · η`.  It is defined conditionally on the cap-to-model
theorem and on next-block uniqueness of models, which enter its fields as follows:
* `zero`, conditional on the cap-to-model theorem at `ω` on `ℕ` (`Expansion.expansionDomain_zero`);
* `antitone` and the emptiness at and above `ω₁`, unconditional
  (`Expansion.expansionDomain_antitone`, `Expansion.expansionDomain_eq_empty`);
* `limit`, conditional on next-block uniqueness of models
  (`Expansion.biInter_expansionDomain_subset`, through uniqueness of model expansions and limit
  existence, with coherence derived from uniqueness).

**The main theorem for these domains, conditionally.**  With these domains, the representative
hypothesis of `ExpansionDomains.hasLogicalAgreement_of_modelExpansions` holds by the definition of
the domains, so logical agreement needs only finite-cut receiving of models.  The thinness of the
density sentence (`densitySentence_isThinOnNatModels_of_modelExpansions`) and its thin `ℵ₁`
spectrum (`densitySentence_hasThinAlephOneSpectrum_of_modelExpansions`) are then proved
conditional on the following hypotheses, **each still to be proved**:
* the cap-to-model theorem at `ω` on `ℕ` (`CapToModel.{0}`; Layer 3, 3.4; checkpoint 4);
* next-block uniqueness of models (`Expansion.NextBlockUniqueness.{0}`; a consequence of
  normalization, output 2 of higher-stage reconstruction, Layer 4; checkpoint 5);
* finite-cut receiving of models (`Expansion.FiniteCutReceiving.{0}`; (R1) of the table of
  Layer 3);
* countable losses of the expansion domains (condition 2 of the reduction; Layers 4–5);
* for the spectrum, nonempty losses of the expansion domains (condition 4 of the reduction;
  Layer 6).
The two conditions on the losses are stated on the family `Expansion.expansionDomain` itself, so
they do not depend on the other hypotheses.  These theorems are conditional; the main theorem of
the roadmap has none of these hypotheses.  The counterexample form
`vaughtCounterexample_of_expansionDomains` applied to `modelExpansionDomains hcap hu` additionally
needs the cap-to-model theorem on the carriers of the universe `w` (`CapToModel.{w}`), which is the
same hypothesis `hcap` when `w = 0`.

**Next-block uniqueness replaced by forcing donors.**  Next-block uniqueness of models follows
from finite-cut receiving of models and forcing donors at every countable block index
(`Expansion.NextBlockUniqueness.of_forcingDonors`).  Substituting it gives thinness
(`densitySentence_isThinOnNatModels_of_forcingDonors`) and the thin `ℵ₁` spectrum
(`densitySentence_hasThinAlephOneSpectrum_of_forcingDonors`) conditional on the cap-to-model
theorem, (R1), forcing donors (`ForcingDonors ξ`, `ξ < ω₁`; a finite statement about legal
stage types, to be proved by a finite construction of Layer 3) and the conditions on the losses,
with no hypothesis of uniqueness.

**Countable losses from the terminal classification.**  The countability of the successor losses
follows from (R1), the continuation criterion (output 3 of higher-stage reconstruction), and (R2)
and (R3) of the table of Layer 3 (`Expansion.expansionDomain_loss_countable`).  Substituting it
gives thinness (`densitySentence_isThinOnNatModels_of_terminalClassification`) and the thin `ℵ₁`
spectrum (`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`) with no hypothesis
on the countability of the losses.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure Set baseLanguage Expansion
open scoped Ordinal

/-- **The expansion domains of the density sentence**: the expansion domains on the classes of
the density sentence (`DensityClass`) whose domain at `η` is the actual expansion domain
`Expansion.expansionDomain η`.  The first domain is every class conditional on the cap-to-model
theorem (`hcap`; Layer 3, 3.4; checkpoint 4), and the limit clause is conditional on next-block
uniqueness of models (`hu`; Layer 4, output 2; checkpoint 5); both are still to be proved.  The
domains decrease and are empty at and above `ω₁` unconditionally. -/
def modelExpansionDomains (hcap : CapToModel.{0}) (hu : NextBlockUniqueness.{0}) :
    ExpansionDomains DensityClass where
  domain := expansionDomain
  zero := expansionDomain_zero fun R ↦ hcap.isModel R
  antitone := expansionDomain_antitone
  limit _ hl hlω := biInter_expansionDomain_subset hu hl hlω
  domain_eq_empty_of_omega_one_le _ h := expansionDomain_eq_empty h

/-- The domains of `modelExpansionDomains` are the expansion domains. -/
@[simp] theorem modelExpansionDomains_domain (hcap : CapToModel.{0})
    (hu : NextBlockUniqueness.{0}) : (modelExpansionDomains hcap hu).domain = expansionDomain :=
  rfl

/-- **Logical agreement of the expansion domains**, conditional on finite-cut receiving of models
(`hrec`; (R1) of the table of Layer 3, still to be proved): the representative hypothesis of
`ExpansionDomains.hasLogicalAgreement_of_modelExpansions` is the definition of the domains. -/
theorem modelExpansionDomains_hasLogicalAgreement (hcap : CapToModel.{0})
    (hu : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0}) :
    (modelExpansionDomains hcap hu).HasLogicalAgreement densityTruth :=
  ExpansionDomains.hasLogicalAgreement_of_modelExpansions hrec.finiteExtensionReceiving
    fun _ _ _ hq ↦ hq

/-- **Thinness for the expansion domains, conditionally on cap-to-model and next-block
uniqueness**: the density sentence has no perfect set of pairwise nonisomorphic models coded on
`ℕ`, conditional on the following hypotheses, each still to be proved: the cap-to-model theorem
(`hcap`; Layer 3, 3.4; checkpoint 4), next-block uniqueness of models (`hu`; Layer 4, output 2;
checkpoint 5), finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3), and
countable losses of the expansion domains (`hc`; condition 2 of the reduction, Layers 4–5).  The
lower bound is not used. -/
theorem densitySentence_isThinOnNatModels_of_modelExpansions (hcap : CapToModel.{0})
    (hu : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    densitySentence.{0}.IsThinOnNatModels :=
  densitySentence_isThinOnNatModels_of_expansionDomains (modelExpansionDomains hcap hu)
    (modelExpansionDomains_hasLogicalAgreement hcap hu hrec) ⟨hc⟩

/-- **The thin `ℵ₁` spectrum for the expansion domains, conditionally on cap-to-model and
next-block uniqueness**: the density sentence has exactly `ℵ₁` classes of models coded on `ℕ`
and no perfect set of pairwise nonisomorphic ones, conditional on the following hypotheses, each
still to be proved: the cap-to-model theorem (`hcap`; Layer 3, 3.4; checkpoint 4), next-block
uniqueness of models (`hu`; Layer 4, output 2; checkpoint 5), finite-cut receiving of models
(`hrec`; (R1) of the table of Layer 3), countable losses of the expansion domains (`hc`;
condition 2 of the reduction, Layers 4–5), and nonempty losses of the expansion domains (`hn`;
condition 4 of the reduction, Layer 6). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_modelExpansions (hcap : CapToModel.{0})
    (hu : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable)
    (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_expansionDomains (modelExpansionDomains hcap hu)
    (modelExpansionDomains_hasLogicalAgreement hcap hu hrec) ⟨hc⟩ ⟨hn⟩

/-- **Thinness for the expansion domains, conditionally on cap-to-model, (R1) and forcing
donors**: the density sentence has no perfect set of pairwise nonisomorphic models coded on `ℕ`,
conditional on the following hypotheses, each still to be proved: the cap-to-model theorem
(`hcap`; Layer 3, 3.4; checkpoint 4), finite-cut receiving of models (`hrec`; (R1) of the table
of Layer 3; used for next-block uniqueness and for logical agreement), forcing donors at every
countable block index (`hF`; a finite construction of Layer 3, awaiting the completion below the
full grade; used for next-block uniqueness), and countable losses of the expansion domains (`hc`;
condition 2 of the reduction, Layers 4–5).  Next-block uniqueness is derived
(`NextBlockUniqueness.of_forcingDonors`). -/
theorem densitySentence_isThinOnNatModels_of_forcingDonors (hcap : CapToModel.{0})
    (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    densitySentence.{0}.IsThinOnNatModels :=
  densitySentence_isThinOnNatModels_of_modelExpansions hcap
    (NextBlockUniqueness.of_forcingDonors hrec hF) hrec hc

/-- **The thin `ℵ₁` spectrum for the expansion domains, conditionally on cap-to-model, (R1) and
forcing donors**: the density sentence has exactly `ℵ₁` classes of models coded on `ℕ` and no
perfect set of pairwise nonisomorphic ones, conditional on the following hypotheses, each still
to be proved: the cap-to-model theorem (`hcap`; Layer 3, 3.4; checkpoint 4), finite-cut receiving
of models (`hrec`; (R1) of the table of Layer 3; used for next-block uniqueness and for logical
agreement), forcing donors at every countable block index (`hF`; a finite construction of
Layer 3, awaiting the completion below the full grade; used for next-block uniqueness), countable
losses of the expansion domains (`hc`; condition 2 of the reduction, Layers 4–5), and nonempty
losses of the expansion domains (`hn`; condition 4 of the reduction, Layer 6).  Next-block
uniqueness is derived (`NextBlockUniqueness.of_forcingDonors`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_forcingDonors (hcap : CapToModel.{0})
    (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable)
    (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_modelExpansions hcap
    (NextBlockUniqueness.of_forcingDonors hrec hF) hrec hc hn

/-- **Thinness for the expansion domains from the terminal classification**: the density
sentence has no perfect set of pairwise nonisomorphic models coded on `ℕ`, conditional on the
following hypotheses, each still to be proved:
* the cap-to-model theorem (`hcap`; Layer 3, 3.4; checkpoint 4): the first domain;
* finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3, which follows from the
  gated pinned extension property `StageType.HasGatedPinnedExtensions`): next-block uniqueness,
  logical agreement, and the rigid-core comparison;
* forcing donors at every countable block index (`hF`; a finite construction of Layer 3, awaiting
  the completion below the full grade): next-block uniqueness, for the limit clause;
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction, Layer 4): the
  cover of the terminal models;
* exact residual receiving (`hres`; (R2) of the table of Layer 3): the residual comparison;
* exact hollow-growth receiving for cover-hollowness at a block stage (`hhol`; (R3) of the table
  of Layer 3): the hollow comparison.
The countability of the losses is derived (`Expansion.expansionDomain_loss_countable`). -/
theorem densitySentence_isThinOnNatModels_of_terminalClassification (hcap : CapToModel.{0})
    (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock) :
    densitySentence.{0}.IsThinOnNatModels :=
  densitySentence_isThinOnNatModels_of_forcingDonors hcap hrec hF
    (expansionDomain_loss_countable hrec hcont hres hhol)

/-- **The thin `ℵ₁` spectrum for the expansion domains from the terminal classification**: the
density sentence has exactly `ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise
nonisomorphic ones, conditional on the hypotheses of
`densitySentence_isThinOnNatModels_of_terminalClassification`, each still to be proved, and on
nonempty losses of the expansion domains (`hn`; condition 4 of the reduction, Layer 6).  The
countability of the losses is derived (`Expansion.expansionDomain_loss_countable`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_terminalClassification
    (hcap : CapToModel.{0}) (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    (hn : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_forcingDonors hcap hrec hF
    (expansionDomain_loss_countable hrec hcont hres hhol) hn

end VaughtConjecture.MainTheorem
