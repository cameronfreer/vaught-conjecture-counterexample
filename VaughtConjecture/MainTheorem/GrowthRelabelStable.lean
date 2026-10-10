/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthRelabelLadder

/-!
# The stable ladder contract from the seed position

Roadmap, Layer 3 ((R3) and (R4), the growth carrier at a calibrated context).

The ladder contract for requests calibrated on the class at the seed position
(`StageType.HasLadderGrowthCarriersStableAtSeed`) gives it at every context
(`StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable`): the root of
requests calibrated on the class is not onto, lies in the first coatom after a relabelling, and
the ladder carrier there is relabelled back with its controllers
(`StageType.hasLadderGrowthCarriersStable_of_seed`).  So the one constructor at the seed position
gives (R3) (`StageType.HasLadderGrowthCarriersStable.hasLadderGrowthCarriers`) and (R4)
(`StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers`), and the thin `ℵ₁` spectrum
with (R2) (`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed`).

The contract at the seed position is compiled with no hypotheses
(`StageType.hasLadderGrowthCarriersStableAtSeed_levels`, in
`VaughtConjecture.MainTheorem.LevelCarrierContract`; not yet reviewed); (R2) is proved by
`Realization.receivingResidualReceiving_of_padded`.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

/-- **The stable ladder contract at the seed position gives it at every context** (relabelling,
`StageType.hasLadderGrowthCarriersStable_of_seed`). -/
theorem HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable
    (h : HasLadderGrowthCarriersStableAtSeed.{u}) : HasLadderGrowthCarriersStable.{u} :=
  hasLadderGrowthCarriersStable_of_seed fun _ _ _ t' g p' hα ht' hp' p hte d hd hn Q hlab hQ
    hrel ↦ h t' g p' hα ht' hp' p hte d hd hn Q hlab hQ hrel

/-- **(R3) from the stable ladder contract at the seed position.** -/
theorem HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriers
    (h : HasLadderGrowthCarriersStableAtSeed.{u}) : HasLadderGrowthCarriers.{u} :=
  h.hasLadderGrowthCarriersStable.hasLadderGrowthCarriers

end StageType

namespace MainTheorem

open Ordinal Realization FirstOrder Language Structure baseLanguage Expansion StageType

/-- **The main theorem from the stable ladder contract at the seed position**: (R3) and (R4) both
from the one constructor; the hypothesis (R2) `hres` is kept (it is
`Realization.receivingResidualReceiving_of_padded`).  The contract `hlad` is
`StageType.hasLadderGrowthCarriersStableAtSeed_levels` (not yet reviewed). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed
    (hres : ReceivingResidualReceiving.{0, 0})
    (hlad : HasLadderGrowthCarriersStableAtSeed.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_stableLadderCarriers hres
    hlad.hasLadderGrowthCarriersStable

/-- **The main theorem through (R3) alone from the stable ladder contract at the seed position**,
with (R4) `hstab` and (R2) `hres` as hypotheses (`hres` is
`Realization.receivingResidualReceiving_of_padded`; `hstab` also follows from `hlad`,
`StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed_r3
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hlad : HasLadderGrowthCarriersStableAtSeed.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_ladderCarriers hstab hres hlad.hasLadderGrowthCarriers

end MainTheorem

end VaughtConjecture
