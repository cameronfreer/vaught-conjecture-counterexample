/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthStableTemplate
import VaughtConjecture.MainTheorem.GrowthAdmittedCarrier

/-!
# One ladder carrier for both evaluations

Roadmap, Layer 3 ((R3) and (R4), the growth carrier and its two evaluations).

The ladder carrier of (R3) (`StageType.HasLadderGrowthCarriers`) is asked for requests read
exactly at the labels of the context.  The construction does not need exactness: it needs the
requests calibrated on the class, the labels of the context and of the donor admitted, and the
relative lift on the exact class.  Stated so, **one** constructor serves both evaluations.

* `StageType.HasLadderGrowthCarriersStable` (open): at every legal context at a limit stage, for
  every requests calibrated on the class (`StageType.GrowthRequests.ClassCalibrated`), reading the
  donor's labels from the context's labels, with the relative lift on the exact class, a ladder
  carrier: a cell of full scope at the threshold, a field ladder, and every cell of full scope at
  the threshold a ladder controller.  The body is that of `StageType.HasLadderGrowthCarriers`.
* `StageType.HasLadderGrowthCarriersStable.hasLadderGrowthCarriers`: it gives the ladder carriers
  of (R3) (exact requests are admitted by the labels; calibrated requests are calibrated on the
  class).
* `StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers`, **the stable evaluation**:
  it gives the frozen (R4) contract `StageType.HasStableGrowthCarriers ξ
  (StageType.GradedCapMarginCalibration ξ)`.  The margin calibration gives stable reads
  (`StageType.GradedCapMarginCalibration.exists_stableReads`); they are calibrated on the class,
  admitted by the labels of `T⁺` and `D`, and have the relative lift on the exact class through
  the encoded template (`StageType.GrowthRequests.StableReads.hasRelativeLiftOnClass`); the
  ladder carrier recognizes (`GrowthCarrier.recognizes_of_ladder`) and so recovers the relation of
  the requests from the labels of `T⁺` (`GrowthCarrier.recovers_of_recognizes`), which is the
  capped relation (`StageType.GrowthRequests.StableReads.cappedRelation`).
* `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_stableLadderCarriers`: the thin `ℵ₁`
  spectrum from this one constructor and (R2).

The hypothesis `StageType.HasLadderGrowthCarriersStable` is open; so are (R3) and (R4) through it.
Stable modelhood is not used: the cap-to-model theorem gives it afterwards.

## References

The growth construction is that of [Kni26, §4]; the stable labels are those of the continuation
of a model at a limit stage, [Kni26, §4.3].
-/

universe u

namespace VaughtConjecture

open Finset StageType

namespace StageType

/-- **Ladder growth carriers for requests calibrated on the class** (open): at every legal context
`t'` at a limit stage, with root `e`, face `p` and a one-point coface `d` of `p` (`0 < n`), for
every requests `Q` calibrated on the class, reading the labels of `d` from the labels of `t'`, with
the relative lift on the exact class, some growth carrier with the schemes of `t'` and `d` as
literal faces has a cell of full scope at the threshold, a field ladder of height `H ≥ 1`, and
every cell of full scope at the threshold a ladder controller (`GrowthCarrier.IsLadderController`).
The body is that of `StageType.HasLadderGrowthCarriers`; only the hypotheses on `Q` are weaker. -/
def HasLadderGrowthCarriersStable : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (e : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ (p : StageType.{u} α n)
      (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces),
      0 < n → ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ G : GrowthCarrier t'.toScheme d.toScheme e,
          (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
          ∃ (Mb : Type) (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), 0 < H ∧
            (∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1)) ∧
            (∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = Label.ladderSource (i + 1) (i + 1)) ∧
            (∀ a, ∀ i < H, 0 < i →
              G.scheme.rowAt (r a i) (r a (i - 1)) = Label.ladderSource (i + 1) i) ∧
            ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
              ∃ (a : Mb) (F : ℕ → Label.{u}), G.IsLadderController Q (H := H) r u a F

/-- **The (R3) instance**: requests read exactly at the labels of `t'` are read by the labels of
`d`, and calibrated requests are calibrated on the class. -/
theorem HasLadderGrowthCarriersStable.hasLadderGrowthCarriers
    (h : HasLadderGrowthCarriersStable.{u}) : HasLadderGrowthCarriers.{u} :=
  fun _ _ _ t' e hα ht' p hte d hd hn Q hex hQ hrel ↦
    h t' e hα ht' p hte d hd hn Q (fun j ↦ (hex j _).mpr rfl) (hQ.classCalibrated hte) hrel

/-- **The stable evaluation of the ladder carrier** ((R4), the frozen contract): ladder carriers
for requests calibrated on the class give stable growth carriers for the margin calibration.  At
`T⁺`, `f`, `D` and `γ`, the stable reads of the calibration are admitted by the labels of `T⁺` and
`D`, calibrated on the class, and have the relative lift on the exact class; the ladder carrier
for them recognizes, hence recovers from the labels of `T⁺` the relation of the requests, which
gives the capped relation of `D` at `γ`. -/
theorem HasLadderGrowthCarriersStable.hasStableGrowthCarriers
    (h : HasLadderGrowthCarriersStable.{u}) (ξ : Ordinal.{u}) :
    HasStableGrowthCarriers ξ (GradedCapMarginCalibration ξ) := by
  intro m k Tp f P hT hk hP D hD γ _ hC
  obtain ⟨Q, hQ, hγN⟩ := hC.exists_stableReads hT
  have hcal := hQ.classCalibrated hP
  obtain ⟨G, hfull, Mb, H, r, hH, hr, hrd, hrp, hctrl⟩ :=
    h Tp f (isSuccLimit_blockStage (ξ + 1)) hT P hP D hD hk Q hQ.correctAt_label hcal
      (hQ.hasRelativeLiftOnClass hP hD.2 hT hD.1 hk)
  have hrecog : G.Recognizes Q := G.recognizes_of_ladder Q (by have := hcal.arity; omega) hfull
    (fun j ↦ by
      rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
      exact (D.grade_le j).trans hcal.arity) hH r hr hrd hrp hctrl
  have hrecov := G.recovers_of_recognizes Q hrecog
    (fun j hj ↦ ⟨Q.mem_below_cap hcal.scope_cap (hcal.ref j hj).1, (hcal.ref j hj).2.1⟩)
    ⟨Q.mem_below_cap hcal.scope_cap hcal.marker.1, hcal.marker.2.1⟩
    (σ := Tp.label) (fun _ _ ↦ Iff.rfl) hcal.label_cap
  exact ⟨G, GrowthCarrier.Recovers.mono G hrecov fun _ _ h ↦ hQ.cappedRelation hγN h⟩

end StageType

namespace MainTheorem

open Realization FirstOrder Language Structure baseLanguage Expansion

/-- **The thin `ℵ₁` spectrum from one ladder constructor**: ladder carriers for requests
calibrated on the class (`StageType.HasLadderGrowthCarriersStable`, open) give both (R4) (the
stable evaluation) and (R3) (the actual evaluation); with (R2) (`hres`, open) the density sentence
has a thin `ℵ₁` spectrum.  The two hypotheses are open. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_stableLadderCarriers
    (hres : ReceivingResidualReceiving.{0, 0}) (hlad : HasLadderGrowthCarriersStable.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_ladderCarriers
    (fun ξ _ ↦ hlad.hasStableGrowthCarriers ξ) hres hlad.hasLadderGrowthCarriers

end MainTheorem

end VaughtConjecture
