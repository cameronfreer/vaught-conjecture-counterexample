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
  the private coatom, has the weakened lower bound at the root (`H3.RootLowBound'`: the
  prescription is at least `n + 1` at every root cell with an ordinal label, or the low truncation
  of `d` at the root blocks, `⊥` at the labels other than `⊤` below the block start of every
  ordinal root label, is lawful on `d`).  It is implied by the earlier form `H3.RootLowBound`
  (`H3.rootLowBound'_of_rootLowBound`).  It gives the donor raise over the gluing coface
  (`H3.exists_raiseCoface_of_rootLowBound'`).
* `H3.TopBand` (assumed): at such a context and coface, the band of the requests at the top cut
  grade (`CapRequests.CapFillPosBandAt` at `k + 1`).  It is implied by the gap of the band
  (`H3.TopBandGap`: `CapRequests.BandGapBelowAt` at `k`, for every datum of the band some `c`,
  self-visible at `k`, at least `h` and at least the marker value, with no value of the
  prescription in `[h, c)` on the common face below the grade `k`; `H3.topBand_of_topBandGap`).
  The gap as stated fails at every such context whose common face has a cell with an ordinal label
  at least `k + 1` (`H3.not_bandGapBelowAt_of_label`), while the band can still hold there; so
  the band is the hypothesis.

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
class, has the weakened lower bound at the root (`H3.RootLowBound'`: the floor at the root, or the
low truncation of `d` at the root blocks is lawful). -/
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
        RootLowBound' n ht' hp htb hpt d f

/-- **The gap of the band at the contexts with the cap at the top grade**: over every coface `tb`
of the coatom face with face `d`, the gap of the band below the top cut grade
(`CapRequests.BandGapBelowAt` at `k`).  It fails at every such context whose common face has a
cell with an ordinal label at least `k + 1` (`H3.not_bandGapBelowAt_of_label`); it gives the band
(`H3.topBand_of_topBandGap`), which is the hypothesis of the route. -/
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

/-- **The band at the contexts with the cap at the top grade** (a named hypothesis).  Quantifier
order: for every context (a legal `t'` on `k + 1` points with coatom face `p`, root face `t` along
`g`, and a marked cap `c` with marker `r` at the top grade, `k < grade c`), then for every coface
`tb` of `p` with face `d` along `extendByLast g`, then for every datum of the band at the top cut
grade `k + 1` (a cap `h ≠ ⊥`, self-visible at `k + 1` and short, a cut-lawful profile `P` with
correct requests, and a prescription `f` lawful below the private coatom, agreeing with `P` capped
at `h`, with `h < f cap`), some cut-lawful `W` extends `f`, agrees with `P` capped at `h`, and has
correct requests (`CapRequests.CapFillPosBandAt` at `k + 1`).  The route uses it at the gluing
coface only; from it one completion of the seed is built (`H3.exists_classCompletion_of_fills₀`)
before the members of the receiving family are quantified in the determination.  Exceptional
case: at a context whose common face has a cell with an ordinal label at least `k + 1`, the gap
(`H3.TopBandGap`) fails (`H3.not_bandGapBelowAt_of_label`) while the band can hold (the labels of
the amalgam are a fill there), so the band, not the gap, is the hypothesis. -/
def TopBand : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    (tb : StageType.{u} α (k + 1)) (htb : tb ∈ p.cofaces) (g : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) (htbd : restrictFace (extendByLast g) tb = some d)
    (c r : Fin t'.card) (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r),
      k < t'.toCellScheme.grade c →
      CapRequests.CapFillPosBandAt
        (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1)) (k + 1)

/-- **The band at a cap of the top grade from the gap**: the gap of the band below `k` gives the
band at `k + 1` (`H3.capFillPosBandAt_of_gap`), the top grade of the donor coatom extending
freely (`CapRequests.donorTopLiftAt_of_face`), the common face having `k` points. -/
theorem capFillPosBandAt_top_of_gap {α : Ordinal.{u}} {n k : ℕ} {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)} (ht' : t'.IsLegal)
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces) {g : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hkN : k < t'.toCellScheme.grade c)
    (hgap : CapRequests.BandGapBelowAt
        (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)) (Fin.last (k + 1))
        (Fin.castSucc (Fin.last k)) k) :
    CapRequests.CapFillPosBandAt (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega))
      (Fin.last (k + 1)) (k + 1) := by
  have hn := hctx.2.2.1
  have hck : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
  have hk0 : 0 < k := by omega
  refine capFillPosBandAt_of_gap ht' hp htb hd hctx (by omega) le_rfl hgap ?_
  refine CapRequests.donorTopLiftAt_of_face (by simp) hk0 le_rfl fun e he ↦ ?_
  obtain ⟨-, hOcard⟩ := ProfileTower.inter_props (I := seed ht' hp htb)
    (x := Fin.last (k + 1)) (y := Fin.castSucc (Fin.last k)) (by simp) (by simp)
    Seed.last_ne_castSucc
  have h1 := (seed ht' hp htb).amalgam.isWellFormed.isWellFormed.grade_le_card e
  have h2 := card_le_card he
  omega

/-- **The gap of the band gives the band** at the contexts with the cap at the top grade
(`H3.capFillPosBandAt_top_of_gap`). -/
theorem topBand_of_topBandGap (hgap : TopBandGap.{u}) : TopBand.{u} :=
  fun _ _ _ t' p ht' hp tb htb g d htbd c r hctx hkN ↦
    capFillPosBandAt_top_of_gap ht' hp htb htbd hctx hkN
      (hgap t' p ht' hp tb htb g d htbd c r hctx hkN)

/-- **The existential coatom form at the contexts with the cap at the top grade**, from the
weakened lower bound at the root and the band (assumed): the gluing coface carries the donor raise
(`H3.exists_raiseCoface_of_rootLowBound'`); the completion with rows in the class from the
raise and the band (`H3.exists_classCompletion_of_fills₀`, the donor provisions compiled at the
top grade, `H3.donorLiftProvisions_of_lt`); determination from it
(`H3.isDeterminedWithin_of_classRows`). -/
theorem hollowCoatomCutoffDeterminationExists_top (hlow : TopRootLowBound.{u})
    (hband : TopBand.{u}) :
    Realization.HollowCoatomCutoffDeterminationExists.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelowTop' t' h) where
  exists_coface α n k t' g p hα ht' hP hp t ht d hd := by
    obtain ⟨⟨c, r, hctx, hoff, hbot⟩, htopg⟩ := hP
    have hkN : k < t'.toCellScheme.grade c := by
      rw [hctx.1.grade_eq_topGrade, htopg]
      omega
    obtain ⟨tb, htb, htbd, hpt, hraise⟩ :=
      exists_raiseCoface_of_rootLowBound' hα ht' hp ht hd hctx hoff hbot
    have hraise' : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        CapRequests.DonorRaiseBotAtIn
          (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' :=
      fun k' hk' hkm ↦ hraise k' hk' hkm fun f hf hcap hm hcl ↦ by
        obtain rfl : k' = k + 1 := by omega
        exact hlow t' p ht' hp tb htb g t hpt d hd htbd c r hctx hkN f hf hcap hm hcl
    obtain ⟨F, hF⟩ := exists_classCompletion_of_fills₀ ht' hp htb htbd hctx
      (donorLiftProvisions_of_lt ht' hp htb htbd hctx hkN) hraise' fun k' hk' hkm ↦ by
        obtain rfl : k' = k + 1 := by omega
        exact hband t' p ht' hp tb htb g d htbd c r hctx hkN
    obtain ⟨δ, hδ, hdet⟩ := isDeterminedWithin_of_classRows ht' hp htb hα htbd hctx.1
      hctx.2.1 hctx.2.2.1 F hF
    exact ⟨tb, htb, htbd, F.completion hα.isSuccPrelimit,
      ⟨F.isLegal_completion _, F.restrictFace_left_completion _⟩,
      F.restrictFace_right_completion _, δ, hδ, hdet⟩

/-- **(R3) for receiving models through the contexts with the cap at the top grade**,
conditional on `HollowFullTopSaturation` (a clause on hollow models that is not a clause of
`IsModel`), the weakened lower bound at the root and the band (assumed). -/
theorem receivingHollowReceiving_top (hsat : Realization.HollowFullTopSaturation.{u, w})
    (hlow : TopRootLowBound.{u}) (hband : TopBand.{u}) :
    Realization.HollowReceiving.{u, w} Realization.IsReceivingCoverHollowAtBlock :=
  Realization.receivingHollowReceiving_of_cutoffDetermination
    (Realization.markedCapContextBelowTop'_routeInputs hsat).1
    ((hollowCoatomCutoffDeterminationExists_top hlow hband).hollowCutoffDetermination
      (Realization.markedCapContextBelowTop'_routeInputs.{u, w} hsat).2.1
      (Realization.markedCapContextBelowTop'_routeInputs.{u, w} hsat).2.2)

end H3

namespace MainTheorem

open FirstOrder Language Structure baseLanguage Expansion Realization Ordinal

/-- **The thin `ℵ₁` spectrum through the contexts with the cap at the top grade**: the
three-hypothesis receiving route with (R3) for receiving models replaced by
`HollowFullTopSaturation` (a clause on hollow models that is not a clause of `IsModel`), the
weakened lower bound at the root, and the band (assumed). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_markedCapContextBelowTop'
    (hR4 : ReceivingStableCappedReceiving.{0}) (hres : ReceivingResidualReceiving.{0, 0})
    (hsat : HollowFullTopSaturation.{0, 0}) (hlow : H3.TopRootLowBound.{0})
    (hband : H3.TopBand.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels' hR4 hres
    (H3.receivingHollowReceiving_top hsat hlow hband)

end MainTheorem

end VaughtConjecture
