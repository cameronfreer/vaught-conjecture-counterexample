/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Band
import VaughtConjecture.MainTheorem.H3Witness
import VaughtConjecture.Continuation.FullTopSaturation

/-!
# `h3` at the contexts with the cap at the top grade (work file)

Work file (placement later).  (R3) for receiving models and the thin `ℵ₁` spectrum through the
contexts with the cap at the top grade (`TiedRootCapRelabel.MarkedCapContextBelowTop'`), with no
`sorry`, from three named hypotheses:

* `Realization.HollowFullTopSaturation` (assumed): **a clause on hollow models that is not a
  clause of `IsModel`**: every model at a limit stage, cover-hollow at a block stage, with
  unbounded growth, realizes over every occurrence a member of every full-top family
  (`Realization.fullTopFamily S ρ`: scheme `S`, `⊤` at the cells of full grade where `ρ` is `⊤`)
  containing a one-point coface of its type.  It gives the acquisition
  (`Realization.hollowAcquisition_markedCapContextBelowTop'`).
* `H3.TopRootLowBound` (assumed): at a context with the cap at the top grade, over every coface
  `tb` of the coatom face with face `d`, every prescription lawful below the private coatom at the
  top cut grade, not `⊥` at the cap and at the marker, and not `⊥` at the cells of the class below
  the private coatom, has a lower bound at the root (`H3.RootLowBound`: some `c₀ ≠ ⊥`,
  self-visible at `n + 1`, below its values at the root cells with ordinal labels, capped at its
  root cap).  It gives the donor raise over the gluing coface
  (`H3.exists_raiseCoface_of_rootLowBound`).
* `H3.TopBandGap` (assumed): at such a context and coface, the gap of the band below the top cut
  grade (`CapRequests.BandGapBelowAt` at `k`: for every datum of the band some `c`, self-visible
  at `k`, at least `h` and at least the marker value, with no value of the prescription in
  `[h, c)` on the common face below the grade `k`).  It gives the band
  (`H3.exists_classCompletion_top_of_gap`).

The lift provisions from the donor coatom (`H3.donorLiftProvisions_of_lt`) and the domination
of the donor tops (`H3.donorTopsDominate_of_lt`) are compiled at the top grade.

* `H3.hollowCoatomCutoffDeterminationExists_top`, `H3.receivingHollowReceiving_top`,
  `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_markedCapContextBelowTop'`.
-/

universe u w

namespace VaughtConjecture

open Finset Label StageType ProfileTower

namespace H3

/-- **The lower bound at the root at the contexts with the cap at the top grade** (a named
hypothesis): over every coface `tb` of the coatom face with face `d`, every prescription lawful
below the private coatom at the top cut grade, not `⊥` at the cap and at the marker, and in the
class, has a lower bound at the root (`H3.RootLowBound`). -/
def TopRootLowBound : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    (tb : StageType.{u} α (k + 1)) (htb : tb ∈ p.cofaces) (g : Fin n ↪ Fin k)
    (t : StageType.{u} α n) (hpt : restrictFace g p = some t) (d : StageType.{u} α (n + 1))
    (_hd : d ∈ t.cofaces) (htbd : restrictFace (extendByLast g) tb = some d)
    (c r : Fin t'.card), t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r →
      k < t'.toCellScheme.grade c →
      ∀ f : Prof (seed ht' hp htb),
        (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), k + 1)
          (fun e ↦ f e) →
        f (faceCell (restrictFace_left_seed ht' hp htb) c) ≠ ⊥ →
        f (faceCell (restrictFace_left_seed ht' hp htb) r) ≠ ⊥ →
        (∀ e ∈ classCells ht' hp htb htbd, e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
          (univ.erase (Fin.last (k + 1)), k + 1) → f e ≠ ⊥) →
        RootLowBound n ht' hp htb hpt c r f

/-- **The gap of the band at the contexts with the cap at the top grade** (a named hypothesis):
over every coface `tb` of the coatom face with face `d`, the gap of the band below the top cut
grade (`CapRequests.BandGapBelowAt` at `k`). -/
def TopBandGap : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    (tb : StageType.{u} α (k + 1)) (htb : tb ∈ p.cofaces) (g : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) (htbd : restrictFace (extendByLast g) tb = some d)
    (c r : Fin t'.card) (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r),
      k < t'.toCellScheme.grade c →
      CapRequests.BandGapBelowAt
        (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
        (Fin.castSucc (Fin.last k)) k

/-- **The existential coatom form at the contexts with the cap at the top grade**, from the lower
bound at the root and the gap of the band (assumed): the gluing coface carries the donor raise
(`H3.exists_raiseCoface_of_rootLowBound`); the completion with rows admitted in the class from the
raise and the gap (`H3.exists_classCompletion_top_of_gap`, the donor provisions compiled at the
top grade); determination from it (`H3.isDeterminedWithin_of_classRows`). -/
theorem hollowCoatomCutoffDeterminationExists_top (hlow : TopRootLowBound.{u})
    (hgap : TopBandGap.{u}) :
    Realization.HollowCoatomCutoffDeterminationExists.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelowTop' t' h) where
  exists_coface α n k t' g p hα ht' hP hp t ht d hd := by
    obtain ⟨⟨c, r, hctx, hoff, hbot⟩, htopg⟩ := hP
    have hkN : k < t'.toCellScheme.grade c := by
      rw [hctx.1.grade_eq_topGrade, htopg]
      omega
    obtain ⟨tb, htb, htbd, hpt, hraise⟩ :=
      exists_raiseCoface_of_rootLowBound hα ht' hp ht hd hctx hoff hbot
    have hraise' : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        CapRequests.DonorRaiseBotAtIn
          (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' :=
      fun k' hk' hkm ↦ hraise k' hk' hkm fun f hf hcap hm hcl ↦ by
        obtain rfl : k' = k + 1 := by omega
        exact hlow t' p ht' hp tb htb g t hpt d hd htbd c r hctx hkN f hf hcap hm hcl
    obtain ⟨F, hF⟩ := exists_classCompletion_top_of_gap ht' hp htb htbd hctx hkN hraise'
      (hgap t' p ht' hp tb htb g d htbd c r hctx hkN)
    obtain ⟨δ, hδ, hdet⟩ := isDeterminedWithin_of_classRows ht' hp htb hα htbd hctx.1
      hctx.2.1 hctx.2.2.1 F hF
    exact ⟨tb, htb, htbd, F.completion hα.isSuccPrelimit,
      ⟨F.isLegal_completion _, F.restrictFace_left_completion _⟩,
      F.restrictFace_right_completion _, δ, hδ, hdet⟩

/-- **(R3) for receiving models through the contexts with the cap at the top grade**,
conditional on `HollowFullTopSaturation` (a clause on hollow models that is not a clause of
`IsModel`), the lower bound at the root and the gap of the band (assumed). -/
theorem receivingHollowReceiving_top (hsat : Realization.HollowFullTopSaturation.{u, w})
    (hlow : TopRootLowBound.{u}) (hgap : TopBandGap.{u}) :
    Realization.HollowReceiving.{u, w} Realization.IsReceivingCoverHollowAtBlock :=
  Realization.receivingHollowReceiving_of_cutoffDetermination
    (Realization.markedCapContextBelowTop'_routeInputs hsat).1
    ((hollowCoatomCutoffDeterminationExists_top hlow hgap).hollowCutoffDetermination
      (Realization.markedCapContextBelowTop'_routeInputs.{u, w} hsat).2.1
      (Realization.markedCapContextBelowTop'_routeInputs.{u, w} hsat).2.2)

end H3

namespace MainTheorem

open FirstOrder Language Structure baseLanguage Expansion Realization Ordinal

/-- **The thin `ℵ₁` spectrum through the contexts with the cap at the top grade**: the
three-hypothesis receiving route with (R3) for receiving models replaced by
`HollowFullTopSaturation` (a clause on hollow models that is not a clause of `IsModel`), the
lower bound at the root, and the gap of the band (assumed). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_markedCapContextBelowTop'
    (hR4 : ReceivingStableCappedReceiving.{0}) (hres : ReceivingResidualReceiving.{0, 0})
    (hsat : HollowFullTopSaturation.{0, 0}) (hlow : H3.TopRootLowBound.{0})
    (hgap : H3.TopBandGap.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels' hR4 hres
    (H3.receivingHollowReceiving_top hsat hlow hgap)

end MainTheorem

end VaughtConjecture
