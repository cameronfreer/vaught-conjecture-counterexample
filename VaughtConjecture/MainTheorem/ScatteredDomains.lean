/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ModelExpansionDomains

/-!
# Thinness in scatteredness form on the expansion-domain route, conditionally

Roadmap, Layer 6 (thinness in scatteredness form) and "Reduction of the main theorem to expansion
domains"; `IMPLEMENTATION.md`, "5. Unique expansions, domains, and the main theorem" (the
scatteredness form of thinness on the expansion-domain route) and "Upstream building blocks".

**The generic statement.**  If, for every `η < ω₁`, a set `S η` of isomorphism classes of coded
models of a sentence has countable complement and any two codes whose classes lie in `S η` are
back-and-forth equivalent at `η` (the library's `CodeBFEquiv η`), then the codes of models are
back-and-forth scattered (InfinitaryLogic's `BFScattered`; `bfScattered_of_countable_compl`, in
`VaughtConjecture.MainTheorem.Scatteredness`, through InfinitaryLogic's
`bfScattered_of_countable_bfObservations`).

**The expansion domains.**  For the density sentence, take `S η = Expansion.expansionDomain η`.
The two inputs are:
* *one back-and-forth class*: two codes whose structures have model expansions to `λ_η` are
  back-and-forth equivalent at `η` (`Expansion.bfEquiv_of_modelExpansions`, the back-and-forth form
  of condition 3), conditional on finite-cut receiving of models (R1);
* *countable complements*: countable successor losses, the first domain being every class, and the
  limit clause give countable complements below `ω₁` (`ExpansionDomains.compl_countable`, through
  InfinitaryLogic's `compl_countable_of_loss`), for the expansion domains
  `modelExpansionDomains hcap hu`, conditional on the cap-to-model theorem (the first domain) and
  next-block uniqueness of models (the limit clause).
The density sentence is then back-and-forth scattered
(`densitySentence_bfScattered_of_modelExpansions`), and thin by InfinitaryLogic's
`isThinOn_of_bfScattered` (`densitySentence_isThinOnNatModels_of_modelExpansions_bfScattered`),
conditional on the following hypotheses, **each still to be proved** except the cap-to-model theorem
and forcing donors where listed, which are compiled in this repository (theorem named)
(`MainTheorem.capToModel`, `forcingDonors_blockStage`):
* the cap-to-model theorem at `ω` on `ℕ` (`CapToModel.{0}`; Layer 3, 3.4; checkpoint 4);
* next-block uniqueness of models (`Expansion.NextBlockUniqueness.{0}`; Layer 4, output 2;
  checkpoint 5);
* finite-cut receiving of models (`Expansion.FiniteCutReceiving.{0}`; (R1) of the table of
  Layer 3);
* countable losses of the expansion domains (condition 2 of the reduction; Layers 4–5).
With next-block uniqueness from (R1) and forcing donors at every countable block index
(`NextBlockUniqueness.of_forcingDonors`) and the countable losses from (R1), the continuation
criterion, (R2) and (R3) (`Expansion.expansionDomain_loss_countable`), the hypotheses become
those of `densitySentence_isThinOnNatModels_of_terminalClassification`
(`densitySentence_bfScattered_of_terminalClassification`,
`densitySentence_isThinOnNatModels_of_terminalClassification_bfScattered`).

These theorems give a second proof of the thinness of the density sentence under the hypotheses of
the first: through uniform back-and-forth separation (InfinitaryLogic's
`exists_uniform_bfSeparation`, inside `isThinOn_of_bfScattered`), with neither sentence separation
nor López–Escobar, and with no use of the lower bound.  The conclusion `BFScattered` also implies
the hypothesis of the full-presentation route in scatteredness form: under it every family of full
presentations has scattered tails (`FullPresentations.HasScatteredTails.of_bfScattered`, in
`VaughtConjecture.MainTheorem.Assembly`).

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure Set baseLanguage Expansion
open scoped Ordinal

/-! ### The expansion domains of the density sentence -/

/-- **Two codes in an expansion domain are back-and-forth equivalent**: for `η < ω₁`, two codes of
models of the density sentence whose classes lie in `Expansion.expansionDomain η` are
back-and-forth equivalent at `η` (`Expansion.bfEquiv_of_modelExpansions`, read on codes through
`Expansion.mem_expansionDomain_iff`), conditional on finite-cut receiving of models (`hrec`; (R1)
of the table of Layer 3), still to be proved. -/
theorem codeBFEquiv_of_mem_expansionDomain (hrec : FiniteCutReceiving.{0}) {η : Ordinal.{0}}
    (hη : η < ω₁) (c d : ModelsOf densitySentence.{0})
    (hc : Quotient.mk _ c ∈ expansionDomain η) (hd : Quotient.mk _ d ∈ expansionDomain η) :
    CodeBFEquiv η c.1 d.1 :=
  -- `CodeBFEquiv η c.1 d.1` is, by definition, `BFEquiv` at `η` of the empty tuples
  @bfEquiv_of_modelExpansions ℕ ℕ c.1.toStructure d.1.toStructure hrec.finiteExtensionReceiving
    η hη ((mem_expansionDomain_iff c).mp hc) ((mem_expansionDomain_iff d).mp hd)

/-- **The density sentence is back-and-forth scattered, conditionally on cap-to-model and next-block
uniqueness**: for every `η < ω₁`, the codes of models of the density sentence fall into countably
many classes of `CodeBFEquiv η` (InfinitaryLogic's `BFScattered`), conditional on the following
hypotheses, each still to be proved except the cap-to-model theorem, forcing donors and the coatom
extension property with apex where listed, which are compiled in this repository (theorem named)
(`MainTheorem.capToModel`, `forcingDonors_blockStage`,
`StageType.hasApexCoatomExtensions_blockStage`): the cap-to-model theorem (`hcap`; Layer 3, 3.4;
checkpoint 4; the first domain), next-block uniqueness of models (`hu`; Layer 4, output 2;
checkpoint 5; the limit clause), finite-cut receiving of models (`hrec`; (R1) of the table of Layer
3; one back-and-forth class in each domain), and countable losses of the expansion domains (`hc`;
condition 2 of the reduction, Layers 4–5).  The countable complements of the domains are
`ExpansionDomains.compl_countable` for `modelExpansionDomains hcap hu`. -/
theorem densitySentence_bfScattered_of_modelExpansions (hcap : CapToModel.{0})
    (hu : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    BFScattered (ModelsOf densitySentence.{0}) :=
  bfScattered_of_countable_compl expansionDomain
    (fun _ hη ↦ (modelExpansionDomains hcap hu).compl_countable ⟨hc⟩ hη)
    fun _ hη ↦ codeBFEquiv_of_mem_expansionDomain hrec hη

/-- **Thinness for the expansion domains in scatteredness form, conditionally on cap-to-model and
next-block uniqueness**: the density sentence has no perfect set of pairwise nonisomorphic models
coded on `ℕ`, by InfinitaryLogic's `isThinOn_of_bfScattered` applied to
`densitySentence_bfScattered_of_modelExpansions`, conditional on its hypotheses, each still to be
proved except the cap-to-model theorem and forcing donors, which are compiled in this repository
(theorem named) (`MainTheorem.capToModel`, `forcingDonors_blockStage`): the cap-to-model theorem
(`hcap`; Layer 3, 3.4; checkpoint 4), next-block uniqueness of models (`hu`; Layer 4, output 2;
checkpoint 5), finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3), and countable
losses of the expansion domains (`hc`; condition 2 of the reduction, Layers 4–5).  The hypotheses
are those of `densitySentence_isThinOnNatModels_of_modelExpansions`; neither sentence separation nor
López–Escobar is used, and the lower bound is not used. -/
theorem densitySentence_isThinOnNatModels_of_modelExpansions_bfScattered (hcap : CapToModel.{0})
    (hu : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    densitySentence.{0}.IsThinOnNatModels :=
  isThinOn_of_bfScattered (densitySentence_bfScattered_of_modelExpansions hcap hu hrec hc)

/-- **The density sentence is back-and-forth scattered, from the terminal classification**:
`densitySentence_bfScattered_of_modelExpansions` with next-block uniqueness derived from (R1) and
forcing donors (`NextBlockUniqueness.of_forcingDonors`) and the countable losses derived from (R1),
the continuation criterion, (R2) and (R3) (`Expansion.expansionDomain_loss_countable`), conditional
on the following hypotheses, each still to be proved except the cap-to-model theorem, forcing donors
and the coatom extension property with apex where listed, which are compiled in this repository
(theorem named) (`MainTheorem.capToModel`, `forcingDonors_blockStage`,
`StageType.hasApexCoatomExtensions_blockStage`):
* the cap-to-model theorem (`hcap`; Layer 3, 3.4; checkpoint 4): the first domain;
* finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3): one back-and-forth class
  in each domain, next-block uniqueness, and the rigid-core comparison;
* forcing donors at every countable block index (`hF`; a finite construction of Layer 3): next-block
  uniqueness, for the limit clause;
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction, Layer 4): the cover
  of the terminal models;
* exact residual receiving (`hres`; (R2) of the table of Layer 3): the residual comparison;
* exact hollow-growth receiving for cover-hollowness at a block stage (`hhol`; (R3) of the table of
  Layer 3): the hollow comparison. -/
theorem densitySentence_bfScattered_of_terminalClassification (hcap : CapToModel.{0})
    (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock) :
    BFScattered (ModelsOf densitySentence.{0}) :=
  densitySentence_bfScattered_of_modelExpansions hcap (NextBlockUniqueness.of_forcingDonors hrec hF)
    hrec (expansionDomain_loss_countable hrec hcont hres hhol)

/-- **Thinness for the expansion domains in scatteredness form, from the terminal classification**:
the density sentence has no perfect set of pairwise nonisomorphic models coded on `ℕ`, by
InfinitaryLogic's `isThinOn_of_bfScattered` applied to
`densitySentence_bfScattered_of_terminalClassification`, conditional on its hypotheses, each still
to be proved except the cap-to-model theorem and forcing donors, which are compiled in this
repository (theorem named) (`MainTheorem.capToModel`, `forcingDonors_blockStage`): the cap-to-model
theorem (`hcap`), (R1) (`hrec`), forcing donors at every countable block index (`hF`), the
continuation criterion (`hcont`), (R2) (`hres`) and (R3) (`hhol`).  The hypotheses are those of
`densitySentence_isThinOnNatModels_of_terminalClassification`; neither sentence separation nor
López–Escobar is used, and the lower bound is not used. -/
theorem densitySentence_isThinOnNatModels_of_terminalClassification_bfScattered
    (hcap : CapToModel.{0}) (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock) :
    densitySentence.{0}.IsThinOnNatModels :=
  isThinOn_of_bfScattered
    (densitySentence_bfScattered_of_terminalClassification hcap hrec hF hcont hres hhol)

end VaughtConjecture.MainTheorem
