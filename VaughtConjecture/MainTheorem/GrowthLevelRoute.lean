/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelCarrierContract
import VaughtConjecture.MainTheorem.GrowthRelabelStable
import VaughtConjecture.MainTheorem.LowPaddedRoute

/-!
# The main theorem through the replicated levels

Roadmap, Layer 3 ((R3) and (R4)) and Layer 6 ("Status: the hypotheses of the main theorem").

These theorems were merged to `main` in the pull request "Growth carriers from re-rendered levels"
(commit `8030d62`), after review, with CI passing on the exact head commit and the standard-axiom
audit.  The route composes compiled statements only:

* the carrier contract at the seed position, `StageType.hasLadderGrowthCarriersStableAtSeed_levels`
  (`VaughtConjecture.MainTheorem.LevelCarrierContract`, from the replicated top level), with no
  hypothesis;
* its transport to every context,
  `StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable`, and (R3) from it,
  `StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriers`;
* (R3) for receiving models (`Realization.hollowReceiving_levels`), through recognition from the
  ladder (`StageType.HasLadderGrowthCarriers.hasRecognizingGrowthCarriers`), exact carriers
  (`StageType.HasRecognizingGrowthCarriers.hasExactGrowthCarriers`) and
  `Realization.receivingHollowReceiving_of_hasExactGrowthCarriers_pos`;
* (R4) for receiving models (`Expansion.receivingStableCappedReceiving_levels`), through
  `StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers` and
  `Expansion.ReceivingStableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin`;
* (R2) for receiving models from the padded tower
  (`Realization.receivingResidualReceiving_of_padded`, inside
  `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_padded`).

The thin `ℵ₁` spectrum of the density sentence is then
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels`, with no hypothesis.

**Dependency record.**  The review scope is the whole import closure of this module.  Along the
compiled chain:

| Declarations | Record |
| --- | --- |
| `StageType.hasLadderGrowthCarriersStableAtSeed_levels` | about the levels |
| `Seed.lvRep_isLegalBelowFullGrade_seedChoice'` (`SeedLevelTopFacts`) | about the levels |
| `Seed.hasExtendingLabelLevel_rep` (`LevelExtendingLabel`) | about the levels |
| `Seed.exists_lvRepCarrier` (`LevelCarrier`) | about the levels |
| `Seed.seedHeightLevel`, `Seed.seedBlockBound'` (`SeedLevelChoice`) | about the levels |
| `StageType.hasLadderGrowthCarriersStable_of_seed` (relabelling) | construction-free |
| `StageType.HasLadderGrowthCarriers.hasRecognizingGrowthCarriers` | construction-free |
| `StageType.HasRecognizingGrowthCarriers.hasExactGrowthCarriers` | construction-free |
| `Realization.receivingHollowReceiving_of_hasExactGrowthCarriers_pos` | construction-free |
| `StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers` | construction-free |
| `ReceivingStableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin` | construction-free |
| `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_padded` ((R2)) | construction-free |

"About the levels" means the statement or its proof names the replicated levels of
`VaughtConjecture.MainTheorem.ReplicatedLevel` and the modules above it; "construction-free" means
the statement quantifies over every carrier and the proof does not name a construction.  The
levels also use facts of the attachment from the earlier replicated scheme (the attachment cells
and admission predicate of `VaughtConjecture.MainTheorem.ReplicatedCompletion`, the compressed
labels of `VaughtConjecture.MainTheorem.ReplicatedLabel`, the mirror of
`VaughtConjecture.Extension.AttachmentMirror`, the lifts of
`VaughtConjecture.Extension.ReplicatedAttachedLift`).

## References

The growth construction is that of [Kni26, §4].
-/

universe u w

namespace VaughtConjecture

open StageType Realization MainTheorem FirstOrder Language baseLanguage

/-- **(R3) for receiving models through the replicated levels** (merged after review, commit
`8030d62`): the carrier contract at the seed position
(`StageType.hasLadderGrowthCarriersStableAtSeed_levels`) gives ladder carriers, hence recognizing
and exact carriers, hence (R3)
(`Realization.receivingHollowReceiving_of_hasExactGrowthCarriers_pos`). -/
theorem Realization.hollowReceiving_levels :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  receivingHollowReceiving_of_hasExactGrowthCarriers_pos
    (hasLadderGrowthCarriersStableAtSeed_levels.hasLadderGrowthCarriers
      |>.hasRecognizingGrowthCarriers |>.hasExactGrowthCarriers)

/-- **(R4) for receiving models through the replicated levels** (merged after review, commit
`8030d62`): the carrier contract at the seed position, transported to every context, gives stable
growth carriers at every block (`StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers`),
hence (R4)
(`Expansion.ReceivingStableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin`). -/
theorem Expansion.receivingStableCappedReceiving_levels :
    Expansion.ReceivingStableCappedReceiving.{w} :=
  Expansion.ReceivingStableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin fun ξ _ ↦
    hasLadderGrowthCarriersStableAtSeed_levels.hasLadderGrowthCarriersStable
      |>.hasStableGrowthCarriers ξ

/-- **The thin `ℵ₁` spectrum of the density sentence through the replicated levels** (merged after
review, commit `8030d62`): `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_padded` ((R2) for
receiving models from the padded tower) with (R4) `Expansion.receivingStableCappedReceiving_levels`
and (R3) `Realization.hollowReceiving_levels`. -/
theorem MainTheorem.densitySentence_hasThinAlephOneSpectrum_levels :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_padded Expansion.receivingStableCappedReceiving_levels
    Realization.hollowReceiving_levels

end VaughtConjecture
