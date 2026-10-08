/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthExactCarrier
import VaughtConjecture.Continuation.GrowthStableCarrier
import VaughtConjecture.MainTheorem.ReceivingRoute

/-!
# The receiving route through growth carriers

Roadmap, Layer 6 ("Status: the hypotheses of the main theorem").

The first and third hypotheses of the three-hypothesis main theorem
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_receivingModels'`) as the two evaluations
of one growth construction (`GrowthCarrier`, in `VaughtConjecture.Realization.GrowthCarrier`):

* (R4) for receiving models, `Expansion.ReceivingStableCappedReceiving`, from stable growth carriers
  for the margin calibration (`StageType.HasStableGrowthCarriers`, evaluated by the stable labels;
  the acquisition is compiled);
* (R3) for receiving models, `HollowReceiving IsReceivingCoverHollowAtBlock`, from exact growth
  carriers for the hollow reference calibration (`StageType.HasExactGrowthCarriers` for
  `StageType.HollowReferenceCalibration`, evaluated by the actual labels; the acquisition is
  compiled).

Both finite statements are open.  The second hypothesis, (R2) for receiving models, is kept.
Neither (R3) nor (R4) is proved here: each is reduced to one finite statement about stage types.
-/

universe w

namespace VaughtConjecture

open Ordinal StageType Realization

/-- **(R4) for receiving models from stable growth carriers for the margin calibration**:
conditional on the finite statement
`StageType.HasStableGrowthCarriers ξ (StageType.GradedCapMarginCalibration ξ)` at every
`ξ < ω₁` (open). -/
theorem Expansion.ReceivingStableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin
    (h : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ)) :
    Expansion.ReceivingStableCappedReceiving.{w} :=
  StableCappedReceiving.receivingStableCappedReceiving
    (StableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin h)

namespace MainTheorem

open FirstOrder Language Structure baseLanguage Expansion

/-- **The thin `ℵ₁` spectrum from growth carriers**: the three-hypothesis receiving route with
(R4) replaced by stable growth carriers for the margin calibration at every `ξ < ω₁` (`hstab`)
and (R3) replaced by exact growth carriers for the hollow reference calibration (`hexact`); (R2)
for receiving models (`hres`) is kept.  The three hypotheses are open. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_growthCarriers
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hexact : HasExactGrowthCarriers.{0} HollowReferenceCalibration) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels'
    (Expansion.ReceivingStableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin hstab)
    hres (receivingHollowReceiving_of_hasExactGrowthCarriers_reference hexact)

end MainTheorem

end VaughtConjecture
