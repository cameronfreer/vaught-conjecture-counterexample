/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StronglyCodedStableCarrier
import VaughtConjecture.MainTheorem.CodedLadderStable

/-!
# Strongly coded cutoff stable recovery from the coded ladder carrier

Roadmap, Layer 3 ((R4), the evaluation step) and Correspondence, item 1 (the strongly coded legal
stage types).  All results here are native constructions of this repository.

The stable evaluation of the coded ladder carrier
(`StageType.HasCodedLadderGrowthCarriersStable.hasStableGrowthCarriers_stronglyCoded`) concludes
`StageType.HasStableGrowthCarriers`, which keeps the carrier and its recovery but not the strong
coding of its rows (`GrowthCarrier.CodedLadder.stronglyCoded`).  Here the same argument keeps it,
and the argument from stable growth carriers to cutoff stable recovery carries it to the carrier of
cutoff stable recovery.

* `StageType.HasCodedLadderGrowthCarriersStable.hasStronglyCodedStableGrowthCarriers`: coded ladder
  carriers for requests calibrated on the class give strongly coded stable growth carriers for the
  strongly coded margin calibration.
* `StageType.stronglyCodedStableGrowthCarriersTarget`: so strongly coded stable growth carriers
  exist at every stage (`StageType.hasCodedLadderGrowthCarriersStable_levels`).
* `StageType.hasStronglyCodedCutoffStableRecovery`: **the finite target
  `StageType.HasStronglyCodedCutoffStableRecovery ξ` holds at every `ξ`**, with its stated
  premises and no other; the recovery contract (`StageType.IsCutoffStableRecovery`) is unchanged,
  for every stage type whose reduction lies in the receiving family of the carrier.
* `Realization.stablyReceivesAt_of_gradedCapMarginCalibration_of_isStronglyCoded`: so the
  evaluation without modelhood
  (`Realization.stablyReceivesAt_of_hasStronglyCodedCutoffStableRecovery`) holds without the
  target as a hypothesis.  The calibrated context `w` is still a hypothesis: its acquisition in the
  strongly coded class is not addressed here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label StageType

namespace StageType

/-- **The stable evaluation of the coded ladder carrier, with the strong coding of the carrier**
((R4)): coded ladder carriers for requests calibrated on the class give strongly coded stable
growth carriers for the strongly coded margin calibration.  The argument is that of
`StageType.HasCodedLadderGrowthCarriersStable.hasStableGrowthCarriers_stronglyCoded`; the strong
coding of the carrier's rows is the field `GrowthCarrier.CodedLadder.stronglyCoded` of the coded
ladder carrier. -/
theorem HasCodedLadderGrowthCarriersStable.hasStronglyCodedStableGrowthCarriers
    (h : HasCodedLadderGrowthCarriersStable.{u}) (ξ : Ordinal.{u}) :
    HasStronglyCodedStableGrowthCarriers ξ (StronglyCodedMarginCalibration ξ) := by
  intro m k Tp f P hT hk hP D hD γ _ ⟨hsc, hdsc, hC⟩
  obtain ⟨Q, hQ, hγN⟩ := hC.exists_stableReads hT
  have hcal := hQ.classCalibrated hP
  obtain ⟨G, Mb, H, r, hL⟩ :=
    h Tp f (isSuccLimit_blockStage (ξ + 1)) hT hsc P hP D hD hdsc hk Q hQ.correctAt_label hcal
      (hQ.hasRelativeLiftOnClass hP hD.2 hT hD.1 hk)
  have hrecog : G.Recognizes Q := G.recognizes_of_codedLadder Q (by have := hcal.arity; omega)
    (fun j ↦ by
      rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
      exact (D.grade_le j).trans hcal.arity) hL
  have hrecov := G.recovers_of_recognizes Q hrecog
    (fun j hj ↦ ⟨Q.mem_below_cap hcal.scope_cap (hcal.ref j hj).1, (hcal.ref j hj).2.1⟩)
    ⟨Q.mem_below_cap hcal.scope_cap hcal.marker.1, hcal.marker.2.1⟩
    (σ := Tp.label) (fun _ _ ↦ Iff.rfl) hcal.label_cap
  exact ⟨G, hL.stronglyCoded,
    GrowthCarrier.Recovers.mono G hrecov fun _ _ h ↦ hQ.cappedRelation hγN h⟩

/-- **Strongly coded stable growth carriers at every stage** (native construction), from the
stable coded contract (`StageType.hasCodedLadderGrowthCarriersStable_levels`). -/
theorem stronglyCodedStableGrowthCarriersTarget : StronglyCodedStableGrowthCarriersTarget.{u} :=
  hasCodedLadderGrowthCarriersStable_levels.hasStronglyCodedStableGrowthCarriers

/-- **Strongly coded cutoff stable recovery for the margin calibration** (native construction):
the finite target `StageType.HasStronglyCodedCutoffStableRecovery ξ` holds at every `ξ`.  For a
strongly coded legal `T⁺` at `λ_{ξ+1}`, an embedding `f` of `k > 0` points with face `P`, a
strongly coded coface `D` of `P` and `γ < λ_{ξ+1}` with the margin calibration, the coded ladder
carrier gives a strongly coded stable recovery scheme, and its coface on the scheme is a strongly
coded carrier of cutoff stable recovery.  The recovery contract is unchanged: literal faces, and
recovery for every stage type whose reduction lies in the receiving family of the carrier. -/
theorem hasStronglyCodedCutoffStableRecovery (ξ : Ordinal.{u}) :
    HasStronglyCodedCutoffStableRecovery ξ :=
  (stronglyCodedStableGrowthCarriersTarget ξ).hasStronglyCodedCutoffStableRecovery

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Evaluation without modelhood at a strongly coded calibrated context** (native construction):
`Realization.stablyReceivesAt_of_hasStronglyCodedCutoffStableRecovery` with its target proved
(`StageType.hasStronglyCodedCutoffStableRecovery`).  Let `R` be exactly consistent and covering,
with legal types, strongly coded types (`hsc`), and finite-cut receiving for the strongly coded
cofaces (`hrec`).  Let `x` be an occurrence of the candidate of positive arity, `D` a strongly coded
coface of its type, `γ < λ_{ξ+1}`, and `w` an occurrence of `R` containing the tuple of `x` along
`f` whose stable type satisfies the margin calibration for `f`, `D` and `γ`.  Then (R4) holds at
`(x, D, γ)`.  The calibrated context `w` is a hypothesis: its acquisition in this class is not
addressed. -/
theorem stablyReceivesAt_of_gradedCapMarginCalibration_of_isStronglyCoded (hR : R.IsConsistent)
    (hc : R.IsCovering) (hl : R.HasLegalTypes)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    {x : (R.stableCandidate (isStablyLawful_of_hasLegalTypes hR hc hl)).Occurrence}
    (hx : 0 < x.arity) {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)}
    (hD : D ∈ x.type.cofaces) (hDs : D.rows.IsStronglyCoded) {γ : Ordinal.{u}}
    (hγ : γ < blockStage (ξ + 1)) (w : R.Occurrence) {f : Fin x.arity ↪ Fin w.arity}
    (hf : f.trans w.tuple = x.tuple)
    (hC : GradedCapMarginCalibration ξ
      (R.stableType (isStablyLawful_of_hasLegalTypes hR hc hl) w.tuple w.type w.eval_tuple) f D γ) :
    R.StablyReceivesAt (isStablyLawful_of_hasLegalTypes hR hc hl) x D γ :=
  stablyReceivesAt_of_hasStronglyCodedCutoffStableRecovery hR hc hl hsc hrec
    (hasStronglyCodedCutoffStableRecovery ξ) hx hD hDs hγ w hf hC

end Realization

end VaughtConjecture
