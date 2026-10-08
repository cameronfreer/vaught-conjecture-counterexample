/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.RootBottomDetermination
import VaughtConjecture.MainTheorem.ReceivingRoute
import VaughtConjecture.MainTheorem.ReceivingDetermination
import VaughtConjecture.MainTheorem.CoatomDetermination

/-!
# The receiving route from cutoff determination at contexts respecting the root bottoms

Roadmap, Layer 6 ("Status: the hypotheses of the main theorem").

The hypothesis `HollowReceiving IsReceivingCoverHollowAtBlock` of the receiving route ((R3) for
receiving models) from hollow cutoff determination at the predicate
`TiedRootCapRelabel.MarkedCapContextBelow'`, which is acquired with no hypothesis
(`Realization.rootBottomAcquisition`).  Compiled in this repository (theorem named):

* `Realization.receivingHollowReceiving_of_cutoffDetermination`: hollow acquisition for
  cover-hollowness at a block stage and hollow cutoff determination, for one predicate, give
  `HollowReceiving IsReceivingCoverHollowAtBlock`
  (`Realization.hollowReceiving_of_hollowCutoffDetermination`).
* `Realization.receivingHollowReceiving_of_markedCapContextBelow'`: from
  `HollowCutoffDetermination MarkedCapContextBelow'`, with no other hypothesis.
* `Realization.receivingHollowReceiving_of_coatomCutoffDetermination`: from its coatom form
  (`Realization.HollowCoatomCutoffDetermination.hollowCutoffDetermination`).
* `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_markedCapContextBelow'`: the thin `ℵ₁`
  spectrum from (R4) and (R2) for receiving models and
  `HollowCutoffDetermination.{0} MarkedCapContextBelow'`.

(R3) is not proved here: hollow cutoff determination at `MarkedCapContextBelow'` is open.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace Realization

/-- **(R3) for receiving models from cutoff determination at the acquired predicate**, with no
other hypothesis. -/
theorem receivingHollowReceiving_of_markedCapContextBelow'
    (hdet : HollowCutoffDetermination.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h)) :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  receivingHollowReceiving_of_cutoffDetermination rootBottomAcquisition hdet

/-- **(R3) for receiving models from the coatom form at the acquired predicate**
(`Realization.HollowCoatomCutoffDetermination.hollowCutoffDetermination` with the route inputs). -/
theorem receivingHollowReceiving_of_coatomCutoffDetermination
    (h3' : HollowCoatomCutoffDetermination.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h)) :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  receivingHollowReceiving_of_markedCapContextBelow'
    (h3'.hollowCutoffDetermination (markedCapContextBelow'_routeInputs.{u, w}).2.1
      (markedCapContextBelow'_routeInputs.{u, w}).2.2)

end Realization

namespace MainTheorem

open FirstOrder Language Structure baseLanguage Expansion Realization StageType Ordinal

/-- **The thin `ℵ₁` spectrum from (R4), (R2) and cutoff determination at the acquired
predicate**: the three-hypothesis receiving route with (R3) for receiving models replaced by
`HollowCutoffDetermination` for `MarkedCapContextBelow'`
(`Realization.receivingHollowReceiving_of_markedCapContextBelow'`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_markedCapContextBelow'
    (hR4 : ReceivingStableCappedReceiving.{0}) (hres : ReceivingResidualReceiving.{0, 0})
    (hdet : HollowCutoffDetermination.{0}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h)) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels' hR4 hres
    (receivingHollowReceiving_of_markedCapContextBelow' hdet)

end MainTheorem

end VaughtConjecture
