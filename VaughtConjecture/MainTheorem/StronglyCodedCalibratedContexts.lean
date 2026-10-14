/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.StronglyCodedUniformity
import VaughtConjecture.MainTheorem.CodedLadderCutoffRecovery

/-!
# Calibrated contexts in the strongly coded receiving class

Roadmap, Layer 3 ((R4), the acquisition and evaluation steps) and Correspondence, item 1 (the
strongly coded legal stage types).

The acquisition of calibrated contexts for the margin calibration
(`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`) assumes a model.  Its steps
use modelhood only for stable lawfulness, for reference cells by uniformity
(`Realization.IsModel.exists_extend_uniformity`), and for exact consistency and covering.  Here the
same acquisition is stated for a realization in the strongly coded receiving class: exactly
consistent and covering, with legal and strongly coded types and finite-cut receiving for the
cofaces with strongly coded rows.  Stable lawfulness is derived
(`Realization.isStablyLawful_of_hasLegalTypes`), and the reference cells come from strongly coded
receiving (`Realization.stronglyCodedReferenceCellsTarget`).

* `Realization.CalibratedContextAcquisitionTarget ξ M`: such a realization at `λ_ξ` that is not
  cover-hollow and has top-grade supremum `⊤` acquires calibrated contexts for the margin
  calibration (`Realization.AcquiresCalibratedContexts`, unchanged: every coface of the type of
  the occurrence, with no restriction on its rows).
* `Realization.StronglyCodedStablyReceivesAtTarget ξ M`: for such a realization, (R4) holds at
  every occurrence of the candidate of positive arity, every coface of its type with strongly coded
  rows and every `γ < λ_{ξ+1}`; the calibrated context is not a hypothesis.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label StageType

namespace Realization

variable (ξ : Ordinal.{u}) (M : Type v)

/-- **Target: acquisition of calibrated contexts in the strongly coded receiving class**.  Let `R`
be a realization at `λ_ξ` on `M` that is exactly consistent (`hR`) and covering (`hc`), with legal
types (`hl`), strongly coded types (`hsc`) and finite-cut receiving for the cofaces with strongly
coded rows (`hrec`), not cover-hollow and with top-grade supremum `⊤`.  Then `R`, stably lawful by
`Realization.isStablyLawful_of_hasLegalTypes`, acquires calibrated contexts for the margin
calibration `StageType.GradedCapMarginCalibration ξ`.  The cofaces quantified in
`Realization.AcquiresCalibratedContexts` are all cofaces of the type of the occurrence. -/
def CalibratedContextAcquisitionTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hl : R.HasLegalTypes),
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      AcquiresCalibratedContexts ξ (GradedCapMarginCalibration ξ) R
        (isStablyLawful_of_hasLegalTypes hR hc hl)

/-- **Target: (R4) for strongly coded cofaces in the strongly coded receiving class**.  For `R` as
in `Realization.CalibratedContextAcquisitionTarget` (exactly consistent, covering, with legal and
strongly coded types, finite-cut receiving for the cofaces with strongly coded rows, not
cover-hollow, top-grade supremum `⊤`), (R4) holds at every occurrence `x` of the candidate of
positive arity, every coface `D` of its type with strongly coded rows and every `γ < λ_{ξ+1}`.
The calibrated context is not a hypothesis. -/
def StronglyCodedStablyReceivesAtTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hl : R.HasLegalTypes),
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∀ x : (R.stableCandidate (isStablyLawful_of_hasLegalTypes hR hc hl)).Occurrence,
        0 < x.arity → ∀ D ∈ x.type.cofaces, D.rows.IsStronglyCoded →
          ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
            R.StablyReceivesAt (isStablyLawful_of_hasLegalTypes hR hc hl) x D γ

end Realization

end VaughtConjecture
