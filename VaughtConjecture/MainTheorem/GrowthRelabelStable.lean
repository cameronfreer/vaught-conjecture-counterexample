/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.GrowthRelabelLadder
import VaughtConjecture.MainTheorem.SeedLadderInputs

/-!
# The stable ladder contract from the seed position

Roadmap, Layer 3 ((R3) and (R4), the growth carrier at a calibrated context).

The ladder contract for requests calibrated on the class at the seed position
(`StageType.HasLadderGrowthCarriersStableAtSeed`) asks the donor's top grade to be at most the
context's.  Relabelling (`StageType.ladderCarrierBody_of_seed_topGrade`) carries it to every
context with that bound (`StageType.HasLadderGrowthCarriersStableAtSeed.ladderCarrierBody`).

* **(R3)**: exact calibrated requests imply the bound
  (`StageType.GrowthRequests.topGrade_le_of_exact`), so the contract at the seed position gives
  the unrestricted ladder contract of (R3)
  (`StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriers`).
* **(R4)**: the stable hypotheses (the labels pair admitted, calibration on the class, the
  relative lift on the exact class) do not imply the bound, since a cap labelled other than `⊤`
  admits a donor labelled `⊤`.  The unrestricted stable contract
  `StageType.HasLadderGrowthCarriersStable` follows from the contract at the seed position asked
  without the bound (`StageType.hasLadderGrowthCarriersStable_of_seed`), or from the contract with
  the bound at the inputs that satisfy it.

These are implications; the contracts stay open.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset

namespace StageType

/-- **The stable ladder contract at the seed position gives the body at every context** whose
donor has top grade at most the context's. -/
theorem HasLadderGrowthCarriersStableAtSeed.ladderCarrierBody
    (h : HasLadderGrowthCarriersStableAtSeed.{u}) {α : Ordinal.{u}} {n k : ℕ}
    (t' : StageType.{u} α k) (e : Fin n ↪ Fin k) (hα : Order.IsSuccLimit α) (ht' : t'.IsLegal)
    (p : StageType.{u} α n) (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1))
    (hd : d ∈ p.cofaces) (hdK : d.topGrade ≤ t'.topGrade) (hn : 0 < n)
    (Q : GrowthRequests t' d.toScheme) (hlab : ∀ j, Q.CorrectAt t'.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    LadderCarrierBody t' e d Q :=
  ladderCarrierBody_of_seed_topGrade (fun _ _ _ t' g p' hα ht' hp' p hte d hd hdK hn Q hlab hQ
    hrel ↦ h t' g p' hα ht' hp' p hte d hd hdK hn Q hlab hQ hrel) t' e hα ht' p hte d hd hdK hn Q
    hlab hQ hrel

/-- **(R3) from the stable ladder contract at the seed position**: exact calibrated requests are
calibrated on the class, have the labels pair admitted, and bound the donor's top grade by the
context's (`StageType.GrowthRequests.topGrade_le_of_exact`). -/
theorem HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriers
    (h : HasLadderGrowthCarriersStableAtSeed.{u}) : HasLadderGrowthCarriers.{u} :=
  fun _ _ _ t' e hα ht' p hte d hd hn Q hex hQ hrel ↦
    h.ladderCarrierBody t' e hα ht' p hte d hd (GrowthRequests.topGrade_le_of_exact hex hQ) hn Q
      (fun j ↦ (hex j _).mpr rfl) (hQ.classCalibrated hte) hrel

end StageType

namespace MainTheorem

open Ordinal Realization FirstOrder Language Structure baseLanguage Expansion StageType

/-- **The main theorem from the stable ladder contract at the seed position**, through (R3); the
hypotheses (R4) `hstab` and (R2) `hres` stay open. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hlad : HasLadderGrowthCarriersStableAtSeed.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_ladderCarriers hstab hres hlad.hasLadderGrowthCarriers

end MainTheorem

end VaughtConjecture
