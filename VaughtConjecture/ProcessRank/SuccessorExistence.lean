/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthLevelRoute
import VaughtConjecture.ProcessRank.SuccessorSeparation

/-!
# The stable candidate at `ω₁ + ω` is a receiving successor

Companion programme over the density sentence: a receiving model at the block stage `λ_ξ` that is
not cover-hollow and has top-grade supremum `⊤` is the reduction of a receiving model at
`λ_{ξ+1}`, its stable candidate, at **every** block index `ξ`, in particular at `ξ = ω₁`.

The repository's statement of this continuation, `Expansion.ReceivingContinuationCriterion`, and
the receiving form of (R4), `Expansion.ReceivingStableCappedReceiving`, quantify over `ξ < ω₁`
only.  The local results they are assembled from carry no such bound:

* stable recovery schemes for the margin calibration at every `ξ`
  (`StageType.hasLadderGrowthCarriersStableAtSeed_levels`, transported by
  `StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable`, evaluated by
  `StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers ξ`, and
  `StageType.HasStableGrowthCarriers.hasStableRecoverySchemes`), all universe-polymorphic in the
  stage;
* acquisition of the margin calibration in the model
  (`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`), for any `ξ`;
* (R4) at one occurrence (`Realization.stablyReceivesAt_of_acquiresCalibratedContexts`), for any
  `ξ`;
* the coface instances at `λ_{ξ+1}` (`MainTheorem.hasNonemptyCofaceInstances_blockStage_add_one`),
  for any `ξ`;
* receiving over the empty root (`Realization.hasFiniteCutReceiving_of_pos`) and the cap-to-model
  theorem (`Realization.isModel_stableCandidate_of_hasFiniteCutReceiving`), for any
  `ξ : Ordinal.{0}`.

The bound `ξ < ω₁` enters only through the quantifier of `StableCappedReceiving.receive` (and its
receiving form), where the wrappers place it; the theorem below composes the local results
directly and has no bound.

**Results.**

* `ReceivingContinuationAtTarget` (proved, `receivingContinuationAtTarget`): the stable candidate
  of a receiving model at `λ_ξ`, not cover-hollow, with top-grade supremum `⊤`, is a receiving
  model, for every `ξ : Ordinal.{0}`.
* `OmegaOneNotReceivingTerminalTarget` (proved, `omegaOneNotReceivingTerminalTarget`): at
  `ξ = ω₁`, such a model is not receiving-terminal.
* `UnboundedNotHollowOrbitRankGtTarget` (stated): a receiving model expansion at `λ_{ω₁}`, not
  cover-hollow, with top-grade supremum `⊤`, has an orbit rank above `ω₁`; the composition of the
  previous target with `ReceivingNotTerminalOrbitRankGtTarget`.

## References

The stable candidate and its continuation are [Kni26, §4.3].
-/

universe w

namespace VaughtConjecture.ProcessRank

open Ordinal Order FirstOrder Language Label StageType Realization

/-- **Target: the stable candidate of a receiving model is a receiving model, at every block
index.**  For every `ξ : Ordinal.{0}` (no bound) and a receiving model `R` at `λ_ξ` that is not
cover-hollow and has top-grade supremum `⊤`, the stable candidate at `λ_{ξ+1}` is a receiving
model.  Given-model statement.  Proved (`receivingContinuationAtTarget`). -/
def ReceivingContinuationAtTarget : Prop :=
  ∀ ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M)
    (hR : R.IsReceivingModel), ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      (R.stableCandidate hR.1.isStablyLawful).IsReceivingModel

/-- The stable candidate of a receiving model is a receiving model at every block index: receiving
of the candidate over positive roots from (R4) at one occurrence, with the stable recovery schemes
of the margin calibration and its acquisition; over the empty root from the amalgam field of the
coface instances; modelhood from the cap-to-model theorem.  None of these carries a bound on `ξ`. -/
theorem receivingContinuationAtTarget : ReceivingContinuationAtTarget.{w} := by
  intro ξ M R hR hnh hgrow
  have hS := (hasLadderGrowthCarriersStableAtSeed_levels.hasLadderGrowthCarriersStable
    |>.hasStableGrowthCarriers ξ).hasStableRecoverySchemes
  have hA := hR.1.acquiresCalibratedContexts_gradedCapMargin hnh hgrow
  have hinst := MainTheorem.hasNonemptyCofaceInstances_blockStage_add_one ξ
  have hrec : (R.stableCandidate hR.1.isStablyLawful).HasFiniteCutReceiving := by
    refine hasFiniteCutReceiving_of_pos hR.1.nonempty
      (hasLegalTypes_stableCandidate hR.1.hasLegalTypes)
      (isConsistent_stableCandidate hR.1.isConsistent hR.1.isCovering)
      (isCovering_stableCandidate hR.1.isCovering) hinst.exists_amalgam_empty
      fun x hx D hD c hc ↦ ?_
    induction c using Label.recBotCoeTop with
    | bot => exact absurd hc not_isPermittedCutoff_bot
    | top => exact absurd hc not_isPermittedCutoff_top
    | coe γ =>
      obtain ⟨u, hu, Q, hQ, hQD, hl⟩ := stablyReceivesAt_of_acquiresCalibratedContexts hR.1 hS hA
        x hx D hD γ (isPermittedCutoff_coe.mp hc)
      exact ⟨u, hu, Q, mem_receivingFamily_of_capped hQD hl, hQ⟩
  exact ⟨isModel_stableCandidate_of_hasFiniteCutReceiving hR.1 hinst hrec, hrec⟩

/-- **Target: at `ω₁`, unbounded growth without cover-hollowness is not receiving-terminal.**  A
receiving model `R` at `λ_{ω₁}` that is not cover-hollow and has top-grade supremum `⊤` is not
receiving-terminal at `ω₁`: its stable candidate is a receiving model at `λ_{ω₁ + 1}` reducing to
it.  Given-model statement.  Proved (`omegaOneNotReceivingTerminalTarget`). -/
def OmegaOneNotReceivingTerminalTarget : Prop :=
  ∀ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ω₁) M), R.IsReceivingModel →
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ → ¬ R.IsReceivingTerminalAt ω₁

/-- At `ω₁`, unbounded growth without cover-hollowness is not receiving-terminal: the stable
candidate is a receiving model (`receivingContinuationAtTarget`) reducing to the given one
(`Realization.stableCandidate_reduce`). -/
theorem omegaOneNotReceivingTerminalTarget : OmegaOneNotReceivingTerminalTarget.{w} :=
  fun _ R hR hnh hgrow ht ↦
    ht _ (receivingContinuationAtTarget R hR hnh hgrow) stableCandidate_reduce

/-- **Target: unbounded growth without cover-hollowness at `ω₁` gives an orbit rank above `ω₁`.**
A receiving model expansion `R` of `M` at `λ_{ω₁}` that is not cover-hollow and has top-grade
supremum `⊤` has a tuple of orbit rank above `ω₁`, lifted to the carrier universe; so such `M`
does not have process rank `ω₁`.  Given-model statement.  Stated. -/
def UnboundedNotHollowOrbitRankGtTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage ω₁)),
    R.1.IsReceivingModel → ¬ R.1.IsCoverHollow → R.1.topGradeSup = ⊤ →
      ∃ (n : ℕ) (a : Fin n → M),
        Ordinal.lift.{w} (ω₁ : Ordinal.{0}) < orbitRank (L := baseLanguage.{0}) a

end VaughtConjecture.ProcessRank
