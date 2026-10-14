/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CodedLadderRecognition
import VaughtConjecture.Extension.StronglyCodedAmalgamation
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
ladder carrier (`GrowthCarrier.CodedLadder`: coded rungs, ladder controllers, strongly coded rows).

**Scope.**  A coded ladder carrier has a strongly coded context and donor
(`GrowthCarrier.CodedLadder.isStronglyCoded_context`,
`GrowthCarrier.CodedLadder.isStronglyCoded_donor`).  So every coded contract assumes the context
and the donor strongly coded.  At a seed, with the donor identified as a face of the amalgam, both
coatom types are assumed strongly coded, which is sufficient (not necessary) for the donor's
coding (`Seed.isStronglyCoded_donor_of_coatoms`).  The coded contracts deliver recognizing and
stable carriers only under these premises; they do not give the unrestricted ladder contracts.

* `Seed.HasCodedLadderCarrier`: the target of the coded levels at a seed with strongly coded
  coatom types, the counterpart of the conclusion of
  `Seed.exists_ladderCarrier_of_replicatedInputs`.
* `StageType.HasCodedLadderGrowthCarriers`, `StageType.HasCodedLadderGrowthCarriersStable`,
  `StageType.HasCodedLadderGrowthCarriersStableAtSeed`: the counterparts of the three contracts,
  with the same quantifiers and hypotheses and the strongly coded context and donor.
* `StageType.HasCodedLadderGrowthCarriers.exists_recognizes`,
  `StageType.HasCodedLadderGrowthCarriersStable.hasCodedLadderGrowthCarriers`,
  `StageType.HasCodedLadderGrowthCarriersStable.hasStableGrowthCarriers_stronglyCoded`: the
  restricted deliveries, through `GrowthCarrier.recognizes_of_codedLadder`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
  {d : StageType.{u} α (n + 1)}

/-- **The donor of a seed with strongly coded coatom types is strongly coded** (native
construction): it is a face of the amalgam (`Seed.isStronglyCoded_amalgam`). -/
theorem isStronglyCoded_donor_of_coatoms
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (hl : I.left.rows.IsStronglyCoded) (hr : I.right.rows.IsStronglyCoded) :
    d.rows.IsStronglyCoded :=
  StageType.isStronglyCoded_of_restrictFace hd (I.isStronglyCoded_amalgam hl hr)

/-- **A coded ladder carrier at a seed** (native construction): when the donor `d` is the face of
the amalgam along the root followed by the new point and both coatom types of the seed are
strongly coded, some growth carrier with the first coatom type and the donor `d` as literal faces is
a coded ladder carrier for `Q` (`GrowthCarrier.CodedLadder`).  This is the target of the coded
levels, the counterpart of the conclusion of `Seed.exists_ladderCarrier_of_replicatedInputs`.  A
coded ladder carrier needs a strongly coded context and donor
(`GrowthCarrier.CodedLadder.isStronglyCoded_context`,
`GrowthCarrier.CodedLadder.isStronglyCoded_donor`); strong coding of the first coatom type is the
first of these, and strong coding of both coatom types is sufficient (not necessary) for the
second, through that face (`Seed.isStronglyCoded_donor_of_coatoms`). -/
def HasCodedLadderCarrier (Q : GrowthRequests I.left d.toScheme) : Prop :=
  restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d →
    I.left.rows.IsStronglyCoded → I.right.rows.IsStronglyCoded →
    ∃ (G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb)) (Mb : Type)
      (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

end Seed

namespace StageType

/-- **Coded ladder growth carriers** (native construction): the counterpart of
`StageType.HasLadderGrowthCarriers` for a strongly coded context `t'` and a strongly coded donor
`d`, whose body asks for a coded ladder carrier. -/
def HasCodedLadderGrowthCarriers : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (e : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → t'.rows.IsStronglyCoded → ∀ (p : StageType.{u} α n)
      (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces),
      d.rows.IsStronglyCoded → 0 < n → ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) → Q.Calibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ (G : GrowthCarrier t'.toScheme d.toScheme e) (Mb : Type) (H : ℕ)
          (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

/-- **Coded ladder growth carriers for requests calibrated on the class** (native construction):
the counterpart of `StageType.HasLadderGrowthCarriersStable` for a strongly coded context and
donor. -/
def HasCodedLadderGrowthCarriersStable : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (e : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → t'.rows.IsStronglyCoded → ∀ (p : StageType.{u} α n)
      (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces),
      d.rows.IsStronglyCoded → 0 < n → ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ (G : GrowthCarrier t'.toScheme d.toScheme e) (Mb : Type) (H : ℕ)
          (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

/-- **Coded ladder growth carriers at the seed position** (native construction): the counterpart
of `StageType.HasLadderGrowthCarriersStableAtSeed` for a strongly coded context and donor. -/
def HasCodedLadderGrowthCarriersStableAtSeed : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n m : ℕ⦄ (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m)
    (p' : StageType.{u} α m), Order.IsSuccLimit α → t'.IsLegal → t'.rows.IsStronglyCoded →
    restrictFace Fin.castSuccEmb t' = some p' → ∀ (p : StageType.{u} α n)
      (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
      (hd : d ∈ p.cofaces), d.rows.IsStronglyCoded → 0 < n →
      ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j, Q.CorrectAt t'.label j (d.label j)) → Q.ClassCalibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ (G : GrowthCarrier t'.toScheme d.toScheme (g.trans Fin.castSuccEmb)) (Mb : Type)
          (H : ℕ) (r : Mb → ℕ → Fin G.scheme.card), G.CodedLadder Q H r

/-- **Coded ladder growth carriers recognize, over strongly coded faces**: at a legal, strongly
coded context and a strongly coded donor, with the hypotheses of
`StageType.HasRecognizingGrowthCarriers`, some growth carrier recognizes admitted states
(`GrowthCarrier.recognizes_of_codedLadder`, the threshold being at least the arity of the
donor). -/
theorem HasCodedLadderGrowthCarriers.exists_recognizes (h : HasCodedLadderGrowthCarriers.{u})
    {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k) (e : Fin n ↪ Fin k)
    (hα : Order.IsSuccLimit α) (ht' : t'.IsLegal) (hsc : t'.rows.IsStronglyCoded)
    (p : StageType.{u} α n) (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1))
    (hd : d ∈ p.cofaces) (hdsc : d.rows.IsStronglyCoded) (hn : 0 < n)
    (Q : GrowthRequests t' d.toScheme) (hex : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j)
    (hQ : Q.Calibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    ∃ G : GrowthCarrier t'.toScheme d.toScheme e, G.Recognizes Q := by
  obtain ⟨G, Mb, H, r, hL⟩ := h t' e hα ht' hsc p hte d hd hdsc hn Q hex hQ hrel
  refine ⟨G, G.recognizes_of_codedLadder Q (by have := hQ.arity; omega) (fun j ↦ ?_) hL⟩
  rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
  exact (d.grade_le j).trans hQ.arity

/-- **The (R3) instance of the coded contract**: requests read exactly at the labels of `t'` are
read by the labels of `d`, and calibrated requests are calibrated on the class; the strongly coded
premises are kept. -/
theorem HasCodedLadderGrowthCarriersStable.hasCodedLadderGrowthCarriers
    (h : HasCodedLadderGrowthCarriersStable.{u}) : HasCodedLadderGrowthCarriers.{u} :=
  fun _ _ _ t' e hα ht' hsc p hte d hd hdsc hn Q hex hQ hrel ↦
    h t' e hα ht' hsc p hte d hd hdsc hn Q (fun j ↦ (hex j _).mpr rfl) (hQ.classCalibrated hte)
      hrel

/-- **The stable evaluation of the coded ladder carrier, over strongly coded faces** ((R4)):
coded ladder carriers for requests calibrated on the class give stable growth carriers for the
margin calibration restricted to a strongly coded context `Tp` and a strongly coded donor `D`, as
in `StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers`. -/
theorem HasCodedLadderGrowthCarriersStable.hasStableGrowthCarriers_stronglyCoded
    (h : HasCodedLadderGrowthCarriersStable.{u}) (ξ : Ordinal.{u}) :
    HasStableGrowthCarriers ξ fun _ _ Tp f D γ ↦ Tp.rows.IsStronglyCoded ∧
      D.rows.IsStronglyCoded ∧ GradedCapMarginCalibration ξ Tp f D γ := by
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
  exact ⟨G, GrowthCarrier.Recovers.mono G hrecov fun _ _ h ↦ hQ.cappedRelation hγN h⟩

end StageType

end VaughtConjecture
