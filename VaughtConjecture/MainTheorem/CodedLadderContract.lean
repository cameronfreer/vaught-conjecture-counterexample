/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CodedLadderRecognition
import VaughtConjecture.MainTheorem.GrowthStableLadder

/-!
# The coded ladder carrier contract

Roadmap, Layer 3 ((R3) and (R4), the growth carrier) and Correspondence, item 1 (the strongly
coded legal stage types).  All results here are native constructions of this repository.

The ladder carrier contract (`StageType.HasLadderGrowthCarriers`,
`StageType.HasLadderGrowthCarriersStable`, `StageType.HasLadderGrowthCarriersStableAtSeed`, and
the conclusion of `Seed.exists_ladderCarrier_of_replicatedInputs`) asks for rungs reading
`Label.ladderSource`; no carrier with a second rung satisfying it is strongly coded
(`StageType.not_isStronglyCoded_of_secondRung`).  The coded contract asks instead for a coded
ladder carrier (`GrowthCarrier.CodedLadder`: coded rungs, ladder controllers, strongly coded rows):

* `Seed.HasCodedLadderCarrier`: the target of the coded levels at a seed, the counterpart of the
  conclusion of `Seed.exists_ladderCarrier_of_replicatedInputs`.
* `StageType.HasCodedLadderGrowthCarriers`, `StageType.HasCodedLadderGrowthCarriersStable`,
  `StageType.HasCodedLadderGrowthCarriersStableAtSeed`: the counterparts of the three contracts,
  with the same quantifiers and hypotheses.
* `StageType.HasCodedLadderGrowthCarriers.hasRecognizingGrowthCarriers`,
  `StageType.HasCodedLadderGrowthCarriersStable.hasStableGrowthCarriers`,
  `StageType.HasCodedLadderGrowthCarriersStable.hasCodedLadderGrowthCarriers`: the roles of the
  contracts, as for the old ones, through `GrowthCarrier.recognizes_of_codedLadder`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
  {d : StageType.{u} α (n + 1)}

/-- **A coded ladder carrier at a seed** (native construction): some growth carrier with the
first coatom type and the donor `d` as literal faces is a coded ladder carrier for `Q`
(`GrowthCarrier.CodedLadder`).  This is the target of the coded levels, the counterpart of the
conclusion of `Seed.exists_ladderCarrier_of_replicatedInputs`. -/
def HasCodedLadderCarrier (Q : GrowthRequests I.left d.toScheme) : Prop :=
  ∃ (G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb)) (Mb : Type) (H : ℕ)
    (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

end Seed

namespace StageType

/-- **Coded ladder growth carriers** (native construction): the counterpart of
`StageType.HasLadderGrowthCarriers`, whose body asks for a coded ladder carrier. -/
def HasCodedLadderGrowthCarriers : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (e : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ (p : StageType.{u} α n)
      (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces),
      0 < n → ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) → Q.Calibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ (G : GrowthCarrier t'.toScheme d.toScheme e) (Mb : Type) (H : ℕ)
          (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

/-- **Coded ladder growth carriers for requests calibrated on the class** (native construction):
the counterpart of `StageType.HasLadderGrowthCarriersStable`. -/
def HasCodedLadderGrowthCarriersStable : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (e : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ (p : StageType.{u} α n)
      (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces),
      0 < n → ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ (G : GrowthCarrier t'.toScheme d.toScheme e) (Mb : Type) (H : ℕ)
          (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

/-- **Coded ladder growth carriers at the seed position** (native construction): the counterpart
of `StageType.HasLadderGrowthCarriersStableAtSeed`. -/
def HasCodedLadderGrowthCarriersStableAtSeed : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal →
    restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces), 0 < n →
      ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ (G : GrowthCarrier t'.toScheme d.toScheme (g.trans Fin.castSuccEmb)) (Mb : Type)
          (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

/-- **Coded ladder growth carriers recognize**: `GrowthCarrier.recognizes_of_codedLadder`, the
threshold being at least the arity of the donor. -/
theorem HasCodedLadderGrowthCarriers.hasRecognizingGrowthCarriers
    (h : HasCodedLadderGrowthCarriers.{u}) : HasRecognizingGrowthCarriers.{u} := by
  intro α n k t' e hα ht' p hte d hd hn Q hex hQ hrel
  obtain ⟨G, Mb, H, r, hL⟩ := h t' e hα ht' p hte d hd hn Q hex hQ hrel
  refine ⟨G, G.recognizes_of_codedLadder Q (by have := hQ.arity; omega) (fun j ↦ ?_) hL⟩
  rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
  exact (d.grade_le j).trans hQ.arity

/-- **The (R3) instance of the coded contract**: requests read exactly at the labels of `t'` are
read by the labels of `d`, and calibrated requests are calibrated on the class. -/
theorem HasCodedLadderGrowthCarriersStable.hasCodedLadderGrowthCarriers
    (h : HasCodedLadderGrowthCarriersStable.{u}) : HasCodedLadderGrowthCarriers.{u} :=
  fun _ _ _ t' e hα ht' p hte d hd hn Q hex hQ hrel ↦
    h t' e hα ht' p hte d hd hn Q (fun j ↦ (hex j _).mpr rfl) (hQ.classCalibrated hte) hrel

/-- **The stable evaluation of the coded ladder carrier** ((R4)): coded ladder carriers for
requests calibrated on the class give stable growth carriers for the margin calibration, as in
`StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers`. -/
theorem HasCodedLadderGrowthCarriersStable.hasStableGrowthCarriers
    (h : HasCodedLadderGrowthCarriersStable.{u}) (ξ : Ordinal.{u}) :
    HasStableGrowthCarriers ξ (GradedCapMarginCalibration ξ) := by
  intro m k Tp f P hT hk hP D hD γ _ hC
  obtain ⟨Q, hQ, hγN⟩ := hC.exists_stableReads hT
  have hcal := hQ.classCalibrated hP
  obtain ⟨G, Mb, H, r, hL⟩ :=
    h Tp f (isSuccLimit_blockStage (ξ + 1)) hT P hP D hD hk Q hQ.correctAt_label hcal
      (hQ.hasRelativeLiftOnClass hP hD.2 hT hD.1 hk)
  have hrecog : G.Recognizes Q := G.recognizes_of_codedLadder Q (by have := hcal.arity; omega)
    (fun j ↦ by
      rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
      exact (D.grade_le j).trans hcal.arity) hL
  have hrecov := G.recovers_of_recognizes Q hrecog
    (fun j hj ↦ ⟨Q.mem_below_cap hcal.scope_cap (hcal.ref j hj).1, (hcal.ref j hj).2.1⟩)
    ⟨Q.mem_below_cap hcal.scope_cap hcal.marker.1, hcal.marker.2.1⟩
    (σ := Tp.label) (fun _ _ ↦ Iff.rfl) hcal.label_cap
  exact ⟨G, GrowthCarrier.Recovers.mono G hrecov fun _ _ h ↦ hQ.cappedRelation hγN h⟩

end StageType

end VaughtConjecture
