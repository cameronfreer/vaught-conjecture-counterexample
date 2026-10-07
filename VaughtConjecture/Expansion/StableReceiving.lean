/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableReceiving
import VaughtConjecture.Expansion.Agreement

/-!
# (R4) and the continuation criterion are equivalent under (R1), forcing donors and the coface
instances

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), with Layer 5
(the named hypotheses of the main theorem); semantic contract, item 8.

**At one model** (`Realization.forall_stablyReceivesAt_iff_exists_model`).  Let `R` be a model at
`λ_ξ`, `ξ < ω₁`.  Given (R1) of the table of Layer 3 (finite-cut receiving of models,
`Expansion.FiniteCutReceiving`), forcing donors at `ξ` (`ForcingDonors ξ`) and the coface
instances at `λ_{ξ+1}` (`StageType.HasNonemptyCofaceInstances`), (R4) at every occurrence of
positive arity of the candidate of `R`, every coface and every `γ < λ_{ξ+1}` holds exactly when
`R` is the reduction of a model at `λ_{ξ+1}`.

* From (R4) to a model expansion: (R4) and the amalgam over the empty face give finite-cut
  receiving of the candidate (`Realization.forall_stablyReceivesAt_iff_hasFiniteCutReceiving`),
  and with the uniformity and dominance instances the candidate is a model
  (`Realization.isModel_stableCandidate_of_hasFiniteCutReceiving`) reducing to `R`.
* From a model expansion `R'` to (R4): (R1) at `λ_{ξ+1}` gives finite-cut receiving of `R'`;
  forcing donors and normalization make `R'` the candidate
  (`Realization.eq_stableCandidate_of_reduce_eq`); finite-cut receiving of the candidate gives (R4)
  (`Realization.stablyReceivesAt_of_reduce_eq`).

Neither direction uses non-hollowness or unbounded growth: these are hypotheses of (R4) and of the
continuation criterion, and they enter only as such.

**Globally** (`Expansion.stableCappedReceiving_iff_continuationCriterion`).  Under (R1), forcing
donors at every `ξ < ω₁` and the coface instances at every `λ_{ξ+1}`, `ξ < ω₁`, (R4)
(`StableCappedReceiving`) is equivalent to the continuation criterion (`ContinuationCriterion`).
The direction from (R4) is `ContinuationCriterion.of_stableCappedReceiving`; the converse,
`Expansion.stableCappedReceiving_of_continuationCriterion`, uses (R1) and forcing donors only.

**What this says about (R4).**  (R4) is not a step towards the continuation criterion that is
weaker than it: under three named hypotheses of the main theorem's development ((R1), forcing
donors, and the coface instances, the last from the coatom extension property with apex), it is
the criterion.  A proof of (R4) is a proof of the criterion, and conversely.  The proof of (R4)
must therefore use the hypotheses of the criterion on `R` (non-hollowness and unbounded growth), as
the reduction `StableCappedReceiving.of_stableRecoveryContexts` does, through the acquisition of
calibrated contexts; and the class of models at which (R4) is proved here, the models with a
model expansion, is derived from the expansion and cannot be used to construct it.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal

namespace Realization

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **(R4) at one model is the existence of a model expansion**, under (R1) (`hrec`), forcing
donors at `ξ` (`hF`) and the coface instances at `λ_{ξ+1}` (`hinst`), each still to be proved:
for a model `R` at `λ_ξ`, `ξ < ω₁`, (R4) at every occurrence of positive arity of its candidate,
every coface and every `γ < λ_{ξ+1}` holds exactly when `R` is the reduction of a model at
`λ_{ξ+1}`.  Non-hollowness and unbounded growth are not used. -/
theorem forall_stablyReceivesAt_iff_exists_model (hξ : ξ < ω₁) (hR : R.IsModel)
    (hrec : Expansion.FiniteCutReceiving.{w}) (hF : ForcingDonors.{0} ξ)
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    (∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, 0 < x.arity →
      ∀ D ∈ x.type.cofaces, ∀ γ < blockStage (ξ + 1),
        R.StablyReceivesAt hR.isStablyLawful x D γ) ↔
      ∃ R' : Realization.{0, w} (blockStage (ξ + 1)) M, R'.IsModel ∧
        R'.reduce (isSuccPrelimit_blockStage ξ) = R := by
  refine ⟨fun h ↦ ⟨_, isModel_stableCandidate_of_hasFiniteCutReceiving hR hinst
      ((forall_stablyReceivesAt_iff_hasFiniteCutReceiving hR hinst.exists_amalgam_empty).mp h),
      stableCandidate_reduce⟩, fun ⟨R', hR', hred⟩ x _ D hD γ hγ ↦ ?_⟩
  have hα := isSuccLimit_blockStage (ξ + 1)
  have hαω := blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hξ)
  exact stablyReceivesAt_of_reduce_eq hF hR'.isConsistent hR'.hasLegalTypes
    (hrec.receive hα hαω R' hR') hred hD hγ

end Realization

namespace Expansion

/-- **(R4) from the continuation criterion**, under (R1) (`hrec`) and forcing donors at every
`ξ < ω₁` (`hF`), both still to be proved: the model expansion given by the criterion is the
candidate, whose finite-cut receiving is (R4). -/
theorem stableCappedReceiving_of_continuationCriterion (hcont : ContinuationCriterion.{w})
    (hrec : FiniteCutReceiving.{w}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ) :
    StableCappedReceiving.{w} :=
  stableCappedReceiving_iff_forall_stablyReceivesAt.mpr
    fun ξ _ R hξ hR hnh hgrow x _ D hD γ hγ ↦ by
      obtain ⟨R', hR', hred⟩ := hcont.exists_model R hξ hR hnh hgrow
      have hα := isSuccLimit_blockStage (ξ + 1)
      have hαω := blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hξ)
      exact Realization.stablyReceivesAt_of_reduce_eq (hF ξ hξ) hR'.isConsistent
        hR'.hasLegalTypes (hrec.receive hα hαω R' hR') hred hD hγ

/-- **(R4) is the continuation criterion**, under (R1) (`hrec`), forcing donors at every
`ξ < ω₁` (`hF`) and the coface instances at every `λ_{ξ+1}`, `ξ < ω₁` (`hinst`), each still to be
proved. -/
theorem stableCappedReceiving_iff_continuationCriterion (hrec : FiniteCutReceiving.{w})
    (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hinst : ∀ ξ < ω₁, StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    StableCappedReceiving.{w} ↔ ContinuationCriterion.{w} :=
  ⟨fun h ↦ ContinuationCriterion.of_stableCappedReceiving h hinst,
    fun h ↦ stableCappedReceiving_of_continuationCriterion h hrec hF⟩

end Expansion

end VaughtConjecture
