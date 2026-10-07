/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.StableReceiving

/-!
# Examples: (R4) and the continuation criterion

Special cases of `VaughtConjecture.Expansion.StableReceiving`, each conditional only where stated:

* **The first block** `ξ = 0`: under (R1), forcing donors at `0` and the coface instances at
  `ω + ω`, (R4) at every occurrence of the candidate of a model at `ω` is the existence of a model
  at `ω + ω` reducing to it.
* **A cover-hollow model at the first block** has no model at `ω + ω` reducing to it, under (R1)
  and forcing donors at `0`: a model expansion would be the candidate, which is not a model.
* **Globally**: under (R1), forcing donors and the coface instances, (R4) and the continuation
  criterion are equivalent.
-/

namespace VaughtConjecture.Expansion.StableReceivingExamples

open Ordinal Realization

variable {M : Type} {R : Realization.{0, 0} (blockStage 0) M}

/-- At the first block, (R4) at one model is the existence of a model expansion to `ω + ω`. -/
example (hR : R.IsModel) (hrec : FiniteCutReceiving.{0}) (hF : ForcingDonors.{0} 0)
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (0 + 1))) :
    (∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, 0 < x.arity →
      ∀ D ∈ x.type.cofaces, ∀ γ < blockStage (0 + 1),
        R.StablyReceivesAt hR.isStablyLawful x D γ) ↔
      ∃ R' : Realization.{0, 0} (blockStage (0 + 1)) M, R'.IsModel ∧
        R'.reduce (isSuccPrelimit_blockStage 0) = R :=
  forall_stablyReceivesAt_iff_exists_model (omega0_pos.trans omega0_lt_omega_one) hR hrec hF hinst

/-- **A cover-hollow model at the first block has no model expansion**, under (R1) and forcing
donors at `0`: a model expansion is the candidate, which is not a model. -/
example (hh : R.IsCoverHollow) (hrec : FiniteCutReceiving.{0}) (hF : ForcingDonors.{0} 0)
    {R' : Realization.{0, 0} (blockStage (0 + 1)) M} (hR' : R'.IsModel) :
    R'.reduce (isSuccPrelimit_blockStage 0) ≠ R := fun hred ↦ by
  have hα := isSuccLimit_blockStage (0 + 1 : Ordinal.{0})
  have hαω := blockStage_lt_omega_one
    ((Cardinal.isSuccLimit_omega 1).succ_lt (omega0_pos.trans omega0_lt_omega_one))
  have heq := eq_stableCandidate_of_reduce_eq (hlaw := isStablyLawful_of_isCoverHollow hh) hF
    hR'.isConsistent hR'.hasLegalTypes
    ((hrec.receive hα hαω R' hR').hasFiniteExtensionReceiving hR'.isConsistent
      hα.isSuccPrelimit) hred
  exact not_isModel_stableCandidate_of_isCoverHollow hh _ (heq ▸ hR')

/-- Under (R1), forcing donors and the coface instances, (R4) is the continuation criterion. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hinst : ∀ ξ < ω₁, StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    StableCappedReceiving.{0} ↔ ContinuationCriterion.{0} :=
  stableCappedReceiving_iff_continuationCriterion hrec hF hinst

end VaughtConjecture.Expansion.StableReceivingExamples
