/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LastStage
import VaughtConjecture.MainTheorem.ReceivingRoute

/-!
# The last receiving stage of a class of the density sentence

Roadmap, "The persistent core"; `COMPANIONS.md`, "Further companion results", terminal
refinement, items 1 and 2, for the receiving expansion domains
(`Expansion.receivingExpansionDomain`, in `VaughtConjecture.MainTheorem.ReceivingDomains`).

A class `q` of models of the density sentence coded on `ℕ` lies in the **receiving expansion
domain** at `β` when the structure of a code of `q` has a model expansion to `λ_β` with the
finite-cut receiving property (a **receiving expansion**).  These are not the unrestricted
expansion domains `Expansion.expansionDomain` (a model expansion to `λ_β`, with no receiving
clause): the receiving domain is contained in the unrestricted one
(`Expansion.receivingExpansionDomain_subset`), no converse is claimed, and nothing below is about
unrestricted model expansions.

**The premise.**  The last-stage theorems for the classes of coded models
(`ExpansionDomains.mem_domain_iff_le_lastStage_of_classTruth` and its companions, in
`VaughtConjecture.MainTheorem.LastStage`) take expansion domains `D` with
* logical agreement for the truth of sentences on classes, `D.HasLogicalAgreement (classTruth φ)`,
* nonempty losses, `D.HasNonemptyLosses` (condition 4),
and use Scott isolation of every class (`exists_classTruth_iff_eq`).  For the receiving domains,
`receivingExpansionDomains hcap hu`, the first is
`MainTheorem.receivingExpansionDomains_hasLogicalAgreement` (stated for `densityTruth`, which is
`classTruth densitySentence` by definition), and the second is
`MainTheorem.receivingExpansionDomains_hasNonemptyLosses` under the coatom extension property
with apex at every countable block stage, compiled as
`StageType.hasApexCoatomExtensions_blockStage`.
The domain parameters are proofs too: the cap-to-model theorem is `MainTheorem.capToModel`, and
next-block uniqueness of receiving models follows from forcing donors
(`Expansion.ReceivingNextBlockUniqueness.of_forcingDonors`,
`forcingDonors_of_forall_hasApexCoatomExtensions`), giving `receivingNextBlockUniqueness`.  The
premise is `receivingExpansionDomains_hasLogicalAgreement_classTruth` and
`receivingExpansionDomains_hasNonemptyLosses'`; no hypothesis remains, and (R1) of the table of
Layer 3 (finite-cut receiving of every model) is not used.

**The last receiving stage.**  `receivingLastStage q` is the supremum of the stages `β` with
`q ∈ receivingExpansionDomain β`; it is `ExpansionDomains.lastStage` of the receiving domains for
any choice of their parameters (`receivingLastStage_eq_lastStage`).  With no hypothesis:
* existence: the receiving indices of `q` have a greatest element, and it is countable
  (`exists_isGreatest_receivingIndex`, `isGreatest_receivingLastStage`,
  `receivingLastStage_lt_omega_one`);
* maximality: `q` is in no receiving domain above its last receiving stage
  (`notMem_receivingExpansionDomain_of_receivingLastStage_lt`), in particular not at the next
  stage (`notMem_receivingExpansionDomain_receivingLastStage_add_one`);
* domain membership: `q ∈ receivingExpansionDomain β ↔ β ≤ receivingLastStage q` for every
  ordinal `β` (`mem_receivingExpansionDomain_iff_le_receivingLastStage`), in terms of a code
  (`exists_receivingExpansion_iff_le_receivingLastStage`), and the receiving loss at `β` is the
  fibre of the last receiving stage at `β` (`mem_receivingLoss_iff_receivingLastStage_eq`).

**Scope.**  The statements are about the receiving expansions of codes of models of the density
sentence on `ℕ`.  They say nothing about the unrestricted expansion domains, whose last-stage
theorems (`MainTheorem.mem_expansionDomain_iff_le_lastStage`) remain conditional on (R1) and
next-block uniqueness of models; nothing about every model at a higher stage; and nothing about
the classes of the manuscript.  The last receiving stage is not a Scott rank, and no receiving
expansion at the last receiving stage is constructed beyond the one given by membership.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

open Order Ordinal Set

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion StageType

/-! ### The premise of the last-stage theorems for the receiving domains -/

/-- **Next-block uniqueness of receiving models**, with no hypothesis: forcing donors at every
countable block index (`forcingDonors_of_forall_hasApexCoatomExtensions`, from
`StageType.hasApexCoatomExtensions_blockStage`) give it
(`Expansion.ReceivingNextBlockUniqueness.of_forcingDonors`).  (R1) is not used. -/
theorem receivingNextBlockUniqueness : ReceivingNextBlockUniqueness.{0} :=
  ReceivingNextBlockUniqueness.of_forcingDonors
    (forcingDonors_of_forall_hasApexCoatomExtensions fun η _ ↦
      hasApexCoatomExtensions_blockStage η)

/-- **Logical agreement of the receiving domains for the truth of sentences on classes**:
`MainTheorem.receivingExpansionDomains_hasLogicalAgreement`, read for `classTruth densitySentence`
(which `densityTruth` is by definition), the form taken by the last-stage theorems for the classes
of coded models. -/
theorem receivingExpansionDomains_hasLogicalAgreement_classTruth (hcap : CapToModel.{0})
    (hu : ReceivingNextBlockUniqueness.{0}) :
    (receivingExpansionDomains hcap hu).HasLogicalAgreement (classTruth densitySentence.{0}) :=
  receivingExpansionDomains_hasLogicalAgreement hcap hu

/-- **Nonempty losses of the receiving domains**, with no hypothesis beyond their parameters:
`MainTheorem.receivingExpansionDomains_hasNonemptyLosses` with the coatom extension property with
apex at every countable block stage given by `StageType.hasApexCoatomExtensions_blockStage`. -/
theorem receivingExpansionDomains_hasNonemptyLosses' (hcap : CapToModel.{0})
    (hu : ReceivingNextBlockUniqueness.{0}) :
    (receivingExpansionDomains hcap hu).HasNonemptyLosses :=
  receivingExpansionDomains_hasNonemptyLosses hcap hu fun η _ ↦
    hasApexCoatomExtensions_blockStage η

/-! ### The last receiving stage -/

/-- The **last receiving stage** of a class `q` of the density sentence: the supremum of the
stages `β` at which a code of `q` has a receiving model expansion to `λ_β`, that is, with
`q ∈ receivingExpansionDomain β`.  It concerns receiving expansions only, not unrestricted model
expansions.  It is not a Scott rank. -/
noncomputable def receivingLastStage (q : DensityClass) : Ordinal.{0} :=
  sSup {β | q ∈ receivingExpansionDomain β}

/-- The last receiving stage is the last stage of the receiving domains, for any choice of their
parameters. -/
theorem receivingLastStage_eq_lastStage (hcap : CapToModel.{0})
    (hu : ReceivingNextBlockUniqueness.{0}) (q : DensityClass) :
    receivingLastStage q = (receivingExpansionDomains hcap hu).lastStage q :=
  rfl

/-- **A class lies exactly in the receiving domains up to its last receiving stage**: for every
ordinal `β`, `q ∈ receivingExpansionDomain β ↔ β ≤ receivingLastStage q`.  No hypothesis; (R1)
is not used.  The proof is `ExpansionDomains.mem_domain_iff_le_lastStage_of_classTruth` on the
receiving domains. -/
theorem mem_receivingExpansionDomain_iff_le_receivingLastStage {q : DensityClass}
    {β : Ordinal.{0}} : q ∈ receivingExpansionDomain β ↔ β ≤ receivingLastStage q :=
  ExpansionDomains.mem_domain_iff_le_lastStage_of_classTruth
    (receivingExpansionDomains_hasLogicalAgreement_classTruth capToModel
      receivingNextBlockUniqueness)
    (receivingExpansionDomains_hasNonemptyLosses' capToModel receivingNextBlockUniqueness)

/-- **The last receiving stage is countable**.  No hypothesis; (R1) is not used. -/
theorem receivingLastStage_lt_omega_one (q : DensityClass) : receivingLastStage q < ω₁ :=
  ExpansionDomains.lastStage_lt_omega_one_of_classTruth
    (receivingExpansionDomains_hasLogicalAgreement_classTruth capToModel
      receivingNextBlockUniqueness)
    (receivingExpansionDomains_hasNonemptyLosses' capToModel receivingNextBlockUniqueness) q

/-- **The last receiving stage is the greatest receiving index**: the stages `β` with
`q ∈ receivingExpansionDomain β` have the greatest element `receivingLastStage q`.  No
hypothesis. -/
theorem isGreatest_receivingLastStage (q : DensityClass) :
    IsGreatest {β | q ∈ receivingExpansionDomain β} (receivingLastStage q) :=
  ⟨mem_receivingExpansionDomain_iff_le_receivingLastStage.2 le_rfl,
    fun _ ↦ mem_receivingExpansionDomain_iff_le_receivingLastStage.1⟩

/-- **Every class has a greatest countable receiving index** (existence): the stages `β` at which
a code of `q` has a receiving model expansion to `λ_β` have a greatest element `ρ`, and `ρ < ω₁`.
No hypothesis; (R1) is not used.  This is about receiving expansions; the unrestricted
expansion domains are not addressed. -/
theorem exists_isGreatest_receivingIndex (q : DensityClass) :
    ∃ ρ, IsGreatest {β | q ∈ receivingExpansionDomain β} ρ ∧ ρ < ω₁ :=
  ⟨receivingLastStage q, isGreatest_receivingLastStage q, receivingLastStage_lt_omega_one q⟩

/-- **Maximality of the last receiving stage**: a class is in no receiving domain at a stage above
its last receiving stage.  No hypothesis. -/
theorem notMem_receivingExpansionDomain_of_receivingLastStage_lt {q : DensityClass}
    {β : Ordinal.{0}} (h : receivingLastStage q < β) : q ∉ receivingExpansionDomain β :=
  fun hq ↦ (mem_receivingExpansionDomain_iff_le_receivingLastStage.1 hq).not_gt h

/-- **Maximality at the next stage**: a class is not in the receiving domain at the successor of
its last receiving stage.  No hypothesis. -/
theorem notMem_receivingExpansionDomain_receivingLastStage_add_one (q : DensityClass) :
    q ∉ receivingExpansionDomain (receivingLastStage q + 1) :=
  notMem_receivingExpansionDomain_of_receivingLastStage_lt (lt_add_one _)

/-- **Domain membership in terms of a code**: the structure of a code `c` has a receiving model
expansion to `λ_β` exactly when `β` is at most the last receiving stage of its class, for every
ordinal `β`.  No hypothesis; (R1) is not used. -/
theorem exists_receivingExpansion_iff_le_receivingLastStage (c : ModelsOf densitySentence.{0})
    {β : Ordinal.{0}} :
    (∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage β), e.1.HasFiniteCutReceiving) ↔
      β ≤ receivingLastStage (Quotient.mk _ c) :=
  (mem_receivingExpansionDomain_iff c).symm.trans
    mem_receivingExpansionDomain_iff_le_receivingLastStage

/-- **The receiving loss at `β` is the fibre of the last receiving stage at `β`**: a class lies in
`receivingExpansionDomain β \ receivingExpansionDomain (β + 1)` exactly when its last receiving
stage is `β`.  No hypothesis. -/
theorem mem_receivingLoss_iff_receivingLastStage_eq {q : DensityClass} {β : Ordinal.{0}} :
    q ∈ receivingExpansionDomain β \ receivingExpansionDomain (β + 1) ↔
      receivingLastStage q = β :=
  ExpansionDomains.mem_loss_iff_lastStage_eq_of_classTruth
    (receivingExpansionDomains_hasLogicalAgreement_classTruth capToModel
      receivingNextBlockUniqueness)
    (receivingExpansionDomains_hasNonemptyLosses' capToModel receivingNextBlockUniqueness)

end VaughtConjecture.MainTheorem
