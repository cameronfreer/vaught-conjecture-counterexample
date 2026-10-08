/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Receiving
import VaughtConjecture.Extension.ForcingDonorsCoatom
import VaughtConjecture.MainTheorem.LowerBound
import VaughtConjecture.MainTheorem.ReceivingDomains

/-!
# The main theorem through receiving models

Roadmap, the reduction of the main theorem to expansion domains (conditions 1–4) and Layer 6
("Status: the hypotheses of the main theorem"), for the auxiliary class `𝒞_α` of receiving models
(`Realization.IsReceivingModel`); semantic contract, items 5, 8, 9 and 12.

The expansion domains are the receiving expansion domains
(`MainTheorem.receivingExpansionDomains`, in `VaughtConjecture.MainTheorem.ReceivingDomains`).
Finite-cut receiving is a clause of the class, so **(R1) of the table of Layer 3 is not a
hypothesis of any theorem here**.

**Existence of receiving models.**  At `λ_0 = ω`, the realization of every model of the density
sentence is a receiving model given the cap-to-model theorem
(`MainTheorem.isReceivingModel_toRealization`), and the top-free witnesses are receiving models
at every limit stage under the coatom extension property with apex there
(`MainTheorem.isReceivingModel_reconstruct_of_hasApexCoatomExtensions`).  At limits, coherent
families of receiving models glue (`Realization.IsReceivingModel.glue`), and receiving expansions
below a limit exist at the limit given next-block uniqueness of receiving models
(`ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt`); at successors, existence is the
continuation criterion for receiving models (`Expansion.ReceivingContinuationCriterion`, a
hypothesis).

**The lower bound** (`MainTheorem.nonempty_receivingLoss_of_hasApexCoatomExtensions`).  The
reconstructed realization of a countable Fraïssé limit of the age of top-free charts at `λ_η` is a
model under the coatom extension property with apex at `λ_η`
(`isModel_reconstruct_of_hasApexCoatomExtensions`) and receives with no hypothesis
(`hasFiniteCutReceiving_reconstruct`), so its class lies in the receiving domain at `η`.  It is
not in the receiving domain at `η + 1`: a receiving expansion to `λ_{η+1}` reduces to a receiving
expansion to `λ_η`, which is the reconstructed realization by uniqueness of receiving expansions
(`ModelExpansion.eq_of_hasFiniteCutReceiving`), and that is not the reduction of a model at a
higher stage (`reduce_ne_reconstruct`).

**Thinness** (`MainTheorem.densitySentence_isThinOnNatModels_of_receivingModels`), conditional on
the following hypotheses, each still to be proved here:
* the cap-to-model theorem at `ω` (`hcap`): the first domain;
* forcing donors at every countable block index (`hF`): next-block uniqueness of receiving models
  (`Expansion.ReceivingNextBlockUniqueness.of_forcingDonors`), for the limit clause;
* the coface instances at every next block stage (`hinst`) and (R4) for receiving models (`hR4`,
  `Expansion.ReceivingStableCappedReceiving`): the continuation criterion for receiving models
  (`Expansion.ReceivingContinuationCriterion.of_receivingStableCappedReceiving`);
* (R2) for receiving models (`hres`, `Realization.ReceivingResidualReceiving`) and (R3) for
  receiving models (`hhol`, `Realization.HollowReceiving` for
  `Realization.IsReceivingCoverHollowAtBlock`): the countable losses.
Logical agreement needs no further hypothesis.

**The thin `ℵ₁` spectrum**
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_receivingModels`), conditional on four
hypotheses: the coatom extension property with apex at every countable block
stage (`hext`), (R4) for receiving models (`hR4`), (R2) for receiving models (`hres`) and (R3) for
receiving models (`hhol`).  Derived from `hext`: the cap-to-model theorem
(`CapToModel.of_hasApexCoatomExtensions`), forcing donors
(`forcingDonors_of_forall_hasApexCoatomExtensions`), the coface instances
(`StageType.HasNonemptyCofaceInstances.of_hasApexCoatomExtensions`) and the lower bound.

**Comparison with the route through all models.**  (R4), (R2) and (R3) give their receiving forms
(`Expansion.StableCappedReceiving.receivingStableCappedReceiving`,
`Realization.ResidualReceiving.receiving`, `Realization.HollowReceiving.receiving`), so the
hypotheses here are implied by those of the route through all models with (R1) and the
continuation criterion replaced by (R4)
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_receivingModels_of_stableCappedReceiving`).

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion Realization StageType Ordinal

/-! ### Receiving models: the first block and the top-free witnesses -/

/-- **Receiving models at `λ_0 = ω`**: given the cap-to-model theorem, the realization of a model
of the density sentence is a receiving model; its receiving is the one the density sentence
provides (`realize_densitySentence_iff`), not (R1). -/
theorem isReceivingModel_toRealization (hcap : CapToModel.{w}) {M : Type w}
    [baseLanguage.{0}.Structure M] (h : densitySentence.{0}.Realize M) :
    (toRealization M).IsReceivingModel :=
  let ⟨_, hne, hcons, hcov, hr⟩ := (realize_densitySentence_iff M).mp h
  ⟨hcap.isModel _ hne hasLegalTypes_toRealization hcons hcov hr, hr⟩

/-- **The top-free witnesses are receiving models**: under the coatom extension property with apex
at a limit stage `α`, the reconstructed realization of a structure whose age is the age of
top-free charts and which is ultrahomogeneous is a model
(`isModel_reconstruct_of_hasApexCoatomExtensions`) and receives with no hypothesis
(`hasFiniteCutReceiving_reconstruct`). -/
theorem isReceivingModel_reconstruct_of_hasApexCoatomExtensions {α : Ordinal.{u}} {M : Type}
    [(hullLanguage.{u} α).Structure M] (hext : HasApexCoatomExtensions.{u} α)
    (hage : (hullLanguage.{u} α).age M = topFreeAge α)
    (hu : (hullLanguage.{u} α).IsUltrahomogeneous M) (hα : Order.IsSuccLimit α) :
    (reconstruct α M).IsReceivingModel :=
  ⟨isModel_reconstruct_of_hasApexCoatomExtensions hext hage hu hα,
    hasFiniteCutReceiving_reconstruct hage hu hα.isSuccPrelimit⟩

/-! ### The lower bound for the receiving domains -/

section Witness

variable {η : Ordinal.{0}} {M : Type} [(hullLanguage.{0} (blockStage η)).Structure M]

/-- **Membership of the class of the witness** in the receiving domain at its block: the
reconstructed realization, a model, receives (`hasFiniteCutReceiving_reconstruct`), and its
transport to a code isomorphic to the base reduct receives. -/
theorem mem_receivingExpansionDomain_of_topFreeWitness
    (hage : (hullLanguage.{0} (blockStage η)).age M = topFreeAge (blockStage η))
    (hu : (hullLanguage.{0} (blockStage η)).IsUltrahomogeneous M)
    (hmod : (reconstruct (blockStage η) M).IsModel)
    (c : ModelsOf densitySentence.{0}) (e : @Language.Equiv baseLanguage.{0} M ℕ
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      c.1.toStructure) :
    Quotient.mk _ c ∈ receivingExpansionDomain η :=
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  let := c.1.toStructure
  (mem_receivingExpansionDomain_iff c).mpr ⟨ModelExpansion.map ⟨_, hmod, rfl⟩ e,
    (ModelExpansion.hasFiniteCutReceiving_map_iff _ e).mpr
      (hasFiniteCutReceiving_reconstruct hage hu (isSuccPrelimit_blockStage η))⟩

/-- **Non-membership of the class of the witness** in the receiving domain at the next block,
given that every receiving model expansion of its base reduct to `λ_η` is the reconstructed
realization (`huniq`). -/
theorem notMem_receivingExpansionDomain_succ_of_topFreeWitness
    (hage : (hullLanguage.{0} (blockStage η)).age M ⊆ topFreeAge (blockStage η))
    (huniq : ∀ e : @ModelExpansion M
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage η), e.1.HasFiniteCutReceiving → e.1 = reconstruct (blockStage η) M)
    (c : ModelsOf densitySentence.{0}) (e : @Language.Equiv baseLanguage.{0} M ℕ
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      c.1.toStructure) :
    Quotient.mk _ c ∉ receivingExpansionDomain (η + 1) := by
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  let := c.1.toStructure
  intro hc
  obtain ⟨f, hf⟩ := (mem_receivingExpansionDomain_iff c).mp hc
  let S : ModelExpansion M (blockStage (η + 1)) := f.map e.symm
  have hS : S.1.HasFiniteCutReceiving :=
    (ModelExpansion.hasFiniteCutReceiving_map_iff f e.symm).mpr hf
  exact reduce_ne_reconstruct hage (isSuccPrelimit_blockStage η)
    (blockStage_lt_blockStage_add_one η) S.2.isModel
    (huniq (S.reduceBlock (Order.le_succ η))
      (ModelExpansion.hasFiniteCutReceiving_reduceBlock hS (Order.le_succ η)))

end Witness

/-- **The receiving loss at a countable block is nonempty**, under next-block uniqueness of
receiving models (`hu`) and the coatom extension property with apex at `λ_η` (`hext`). -/
theorem nonempty_receivingLoss_of_hasApexCoatomExtensions (hu : ReceivingNextBlockUniqueness.{0})
    {η : Ordinal.{0}} (hη : η < ω₁) (hext : HasApexCoatomExtensions.{0} (blockStage η)) :
    (receivingExpansionDomain η \ receivingExpansionDomain (η + 1)).Nonempty := by
  have hcount := Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hη)
  let := hullLanguage.countable_functions hcount
  obtain ⟨M, _, hM⟩ := exists_isFraisseLimit_topFreeAge hext.hasCoatomExtensions
    (isSuccPrelimit_blockStage η) (omega0_pos.trans_le (omega0_le_blockStage η)) hcount
  have hmod := isModel_reconstruct_of_hasApexCoatomExtensions hext hM.age hM.ultrahomogeneous
    (isSuccLimit_blockStage η)
  have hrw := hasFiniteCutReceiving_reconstruct hM.age hM.ultrahomogeneous
    (isSuccPrelimit_blockStage η)
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  obtain ⟨c, ⟨e⟩⟩ := exists_code_of_topFreeWitness hM.age hM.ultrahomogeneous hmod
  exact ⟨_, mem_receivingExpansionDomain_of_topFreeWitness hM.age hM.ultrahomogeneous hmod c e,
    notMem_receivingExpansionDomain_succ_of_topFreeWitness hM.age.subset
      (fun f hf ↦ congrArg Subtype.val
        (ModelExpansion.eq_of_hasFiniteCutReceiving hu hη (e' := ⟨_, hmod, rfl⟩) hf hrw)) c e⟩

/-- **Nonempty losses of the receiving expansion domains** (condition 4), under the coatom
extension property with apex at every countable block stage (`hext`) and next-block uniqueness of
receiving models (`hu`). -/
theorem receivingExpansionDomains_hasNonemptyLosses (hcap : CapToModel.{0})
    (hu : ReceivingNextBlockUniqueness.{0})
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    (receivingExpansionDomains hcap hu).HasNonemptyLosses :=
  ⟨fun η hη ↦ nonempty_receivingLoss_of_hasApexCoatomExtensions hu hη (hext η hη)⟩

/-! ### The main theorem through receiving models -/

/-- **Thinness through receiving models**: the density sentence has no perfect set of pairwise
nonisomorphic models coded on `ℕ`, conditional on the following hypotheses, each still to be
proved: the cap-to-model theorem at `ω` (`hcap`), forcing donors at every countable block index
(`hF`), the coface instances at every next block stage (`hinst`), (R4) for receiving models
(`hR4`), (R2) for receiving models (`hres`), and (R3) for receiving models (`hhol`).  (R1) is not
a hypothesis. -/
theorem densitySentence_isThinOnNatModels_of_receivingModels (hcap : CapToModel.{0})
    (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hinst : ∀ ξ < ω₁, HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    (hR4 : ReceivingStableCappedReceiving.{0}) (hres : ReceivingResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsReceivingCoverHollowAtBlock) :
    densitySentence.{0}.IsThinOnNatModels :=
  have hu := ReceivingNextBlockUniqueness.of_forcingDonors hF
  densitySentence_isThinOnNatModels_of_expansionDomains (receivingExpansionDomains hcap hu)
    (receivingExpansionDomains_hasLogicalAgreement hcap hu)
    ⟨receivingExpansionDomain_loss_countable
      (ReceivingContinuationCriterion.of_receivingStableCappedReceiving hR4 hinst) hres hhol⟩

/-- **The thin `ℵ₁` spectrum through receiving models**: the density sentence has exactly `ℵ₁`
classes of models coded on `ℕ` and no perfect set of pairwise nonisomorphic ones, conditional on
the following four hypotheses, each still to be proved:
* the coatom extension property with apex at every countable block stage (`hext`);
* (R4) for receiving models (`hR4`, `Expansion.ReceivingStableCappedReceiving`);
* (R2) for receiving models (`hres`, `Realization.ReceivingResidualReceiving`);
* (R3) for receiving models (`hhol`, `Realization.HollowReceiving` for
  `Realization.IsReceivingCoverHollowAtBlock`).
Derived, not assumed: the cap-to-model theorem at `ω`, forcing donors, next-block uniqueness of
receiving models, the coface instances, the continuation criterion for receiving models, logical
agreement, countable losses and nonempty losses.  (R1) is not a hypothesis. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_receivingModels
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η))
    (hR4 : ReceivingStableCappedReceiving.{0}) (hres : ReceivingResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsReceivingCoverHollowAtBlock) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  have hcap : CapToModel.{0} :=
    CapToModel.of_hasApexCoatomExtensions (hasApexCoatomExtensions_omega_of_forall_blockStage hext)
  have hu := ReceivingNextBlockUniqueness.of_forcingDonors
    (forcingDonors_of_forall_hasApexCoatomExtensions hext)
  have hinst : ∀ ξ < ω₁, HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)) := fun ξ hξ ↦
    .of_hasApexCoatomExtensions (hext (ξ + 1) ((Cardinal.isSuccLimit_omega 1).succ_lt hξ))
      (isSuccPrelimit_blockStage (ξ + 1))
  densitySentence_hasThinAlephOneSpectrum_of_expansionDomains (receivingExpansionDomains hcap hu)
    (receivingExpansionDomains_hasLogicalAgreement hcap hu)
    ⟨receivingExpansionDomain_loss_countable
      (ReceivingContinuationCriterion.of_receivingStableCappedReceiving hR4 hinst) hres hhol⟩
    (receivingExpansionDomains_hasNonemptyLosses hcap hu hext)

/-- **The receiving route from (R2), (R3) and (R4)**: the thin `ℵ₁` spectrum from the coatom
extension property with apex at every countable block stage, (R4), (R2), and (R3) for
cover-hollowness at a block stage, through their receiving forms.  No (R1) and no continuation
criterion for all models. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_receivingModels_of_stableCappedReceiving
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η))
    (hR4 : StableCappedReceiving.{0}) (hres : ResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels hext
    (Expansion.StableCappedReceiving.receivingStableCappedReceiving hR4) hres.receiving
    hhol.receiving

end VaughtConjecture.MainTheorem
