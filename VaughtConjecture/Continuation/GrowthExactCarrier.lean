/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRootBottom
import VaughtConjecture.MainTheorem.ReceivingDetermination
import VaughtConjecture.Realization.GrowthCarrier

/-!
# (R3) as the actual evaluation of a growth carrier

Roadmap, Layer 3 ((R3), the evaluation by actual labels).  The growth engine
(`GrowthCarrier.exists_recovered`, in `VaughtConjecture.Realization.GrowthCarrier`) is evaluated by
the **actual labels** of a model.  If a growth carrier over an acquired context recovers the
labels of a one-point coface `d` **exactly** from the labels of the context, the formal top
included, then generalized saturation receives `d` exactly over the root
(`GrowthCarrier.exists_eval_eq_of_recovers_eq`).  No finite-cut receiving of the model is used:
the realization is a clause of the model.

## Main definitions

* `StageType.HasExactGrowthCarriers C`, a **finite** statement about stage types (open): over every
  legal context `t'` at a limit stage with `C t' h d`, for a one-point coface `d` of the face of
  `t'` along `h`, some growth carrier, with a coface of `t'` on it, recovers the labels of `d`
  exactly from the labels of `t'`.  The calibration `C` may depend on the donor `d`.
* `Realization.HollowGrowthAcquisition H C`, a statement about models: every cover in a model
  satisfying `H` with unbounded top-grade growth extends, for each one-point coface `d` of its
  type, to a cover of a context `t'` with `C t' h d`.

## Main statements

* `Realization.hollowReceiving_of_hasExactGrowthCarriers`: `HollowReceiving H` from acquisition
  and exact growth carriers for one calibration.
* `Realization.HollowGrowthAcquisition.of_hollowAcquisition`: an acquisition that does not depend
  on the donor is a growth acquisition; with `Realization.rootBottomAcquisition` (compiled, no
  hypothesis) this gives `Realization.hollowReceiving_of_hasExactGrowthCarriers_markedCap`: (R3) for
  cover-hollowness at a block stage, hence its receiving form
  `HollowReceiving IsReceivingCoverHollowAtBlock`, from exact growth carriers over the marked-cap
  contexts respecting the root bottoms alone.
* `StageType.HasExactGrowthCarriers.schemeDetermination`: for a calibration not depending on the
  donor, exact growth carriers give scheme determination (`Realization.SchemeDetermination`): every
  stage type on the carrier with face `t'` is a lawful section of its rows.

The marked-cap contexts carry no reference cell for the blocks of the proper labels of `d`; a
calibration with such cells (as for (R4), `StageType.GradedCapMarginCalibration`) is the expected
input of a construction of exact carriers, and
`Realization.hollowReceiving_of_hasExactGrowthCarriers` takes any calibration.

## References

Generalized saturation is [Kni26, Definition 3.2.1, clause 4(a)i]; the hollow case of the
continuation of a model is [Kni26, §4].
-/

universe u w

namespace VaughtConjecture

open Finset Label StageType

namespace StageType

/-- **Exact growth carriers** for a calibration `C` on contexts and donors, a finite statement
about stage types (no realization), open: over every legal `t'` at a limit stage, for every
one-point coface `d` of the face `t` of `t'` along `h` with `C t' h d`, some growth carrier over
the scheme of `t'` with donor scheme that of `d` along `h` has a coface of `t'` on it and recovers
the labels of `d` exactly, the formal top included, from the labels of `t'`. -/
def HasExactGrowthCarriers
    (C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ t : StageType.{u} α n, restrictFace h t' = some t →
      ∀ d ∈ t.cofaces, C t' h d → ∃ G : GrowthCarrier t'.toScheme d.toScheme h,
        (t'.cofaces ∩ saturationFamily G.scheme).Nonempty ∧
          G.Recovers t'.label fun j ℓ ↦ ℓ = d.label j

/-- **A carrier with exact recovery determines the donor**: every stage type on the carrier with
face `t'` along the first points has face `d` along `h` followed by the new point. -/
theorem _root_.VaughtConjecture.GrowthCarrier.isDeterminedWithin {α : Ordinal.{u}} {n k : ℕ}
    {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
    (G : GrowthCarrier t'.toScheme d.toScheme h)
    (hrec : G.Recovers t'.label fun j ℓ ↦ ℓ = d.label j) :
    IsDeterminedWithin (saturationFamily G.scheme) t' h d := by
  intro q hq hface
  obtain ⟨S, lab, hwf, hcod, hlaw, hst⟩ := q
  change S = G.scheme at hq
  subst hq
  set q : StageType.{u} α (k + 1) := ⟨G.scheme, lab, hwf, hcod, hlaw, hst⟩
  have hc : univ.map Fin.castSuccEmb ∈ q.toCellScheme.faces := G.context_mem
  have hctx : q.comap Fin.castSuccEmb hc = t' := by
    rw [restrictFace_of_mem q _ hc] at hface
    exact Option.some_injective _ hface
  rw [restrictFace_of_mem q _ G.donor_mem]
  exact congrArg some (StageType.ext G.comap_donor fun i j hij ↦
    hrec lab hlaw (fun i' j' hij' ↦ StageType.label_congr hctx hij') i j hij)

/-- **Exact growth carriers give scheme determination** for a calibration that does not depend
on the donor. -/
theorem HasExactGrowthCarriers.schemeDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hcar : HasExactGrowthCarriers fun t' h _ ↦ P t' h) :
    Realization.SchemeDetermination.{u} P where
  exists_coface _ _ _ t' h hα ht' hP t ht d hd := by
    obtain ⟨G, ⟨D', hD', hD'E⟩, hrec⟩ := hcar t' h hα ht' t ht d hd hP
    exact ⟨D', hD', hD'E ▸ G.isDeterminedWithin hrec⟩

end StageType

namespace Realization

/-- **Hollow growth acquisition** for a calibration `C`, a statement about models: in every model
at a limit stage satisfying `H` with top-grade supremum `⊤`, every cover `c` of a stage type `t`
extends, for each one-point coface `d` of `t`, to a cover `c'` of some `t'` along some `h`
(`c' ∘ h = c`) with `C t' h d`. -/
structure HollowGrowthAcquisition
    (H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop)
    (C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop where
  /-- Every cover extends, for each coface, to a cover of a calibrated context. -/
  exists_context ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ :
    Order.IsSuccLimit α → R.IsModel → H R → R.topGradeSup = ⊤ →
      ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c → ∀ d ∈ t.cofaces,
        ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
          R.Covers t' c' ∧ c' ∘ h = c ∧ C t' h d

/-- A hollow acquisition, which does not depend on the donor, is a hollow growth acquisition. -/
theorem HollowGrowthAcquisition.of_hollowAcquisition
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hacq : HollowAcquisition.{u, w} H P) : HollowGrowthAcquisition.{u, w} H fun t' h _ ↦ P t' h :=
  ⟨fun _ _ _ hα hR hH htop _ t c hc _ _ ↦ hacq.exists_context hα hR hH htop t c hc⟩

/-- **(R3) from hollow growth acquisition and exact growth carriers**, for one calibration `C`:
over the acquired context the carrier is realized by generalized saturation and read with the
actual labels; the donor is received exactly over the root, the formal top included.  No
finite-cut receiving is used. -/
theorem hollowReceiving_of_hasExactGrowthCarriers
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    {C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hacq : HollowGrowthAcquisition.{u, w} H C) (hcar : HasExactGrowthCarriers.{u} C) :
    HollowReceiving.{u, w} H where
  exists_covers α M R hα hR hH htop n t c hc d hd := by
    obtain ⟨k, t', c', h, hc', hcc', hC⟩ := hacq.exists_context hα hR hH htop t c hc d hd
    let x : R.Occurrence := ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩
    obtain ⟨G, hsat, hrec⟩ := hcar t' h hα (hR.isLegal _ _ hc'.eval_eq) t
      (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd hC
    obtain ⟨u, hu, -, hev⟩ := GrowthCarrier.exists_eval_eq_of_recovers_eq hR x G hsat hrec
    refine ⟨u (Fin.last n), ?_⟩
    have hfun : Fin.snoc c (u (Fin.last n)) = ⇑u := by
      funext i
      induction i using Fin.lastCases with
      | last => simp
      | cast i =>
        rw [Fin.snoc_castSucc, ← hcc']
        exact (DFunLike.congr_fun hu i).symm
    rw [hfun]
    exact covers_of_eval u hev

/-- **(R3) from exact growth carriers over the acquired marked-cap contexts**: exact growth
carriers for the marked-cap contexts with root offsets below the cap that respect the root
bottoms (`TiedRootCapRelabel.MarkedCapContextBelow'`), a finite statement about stage types
(open), give (R3) for cover-hollowness at a block stage; the acquisition is compiled
(`Realization.rootBottomAcquisition`). -/
theorem hollowReceiving_of_hasExactGrowthCarriers_markedCap
    (hcar : HasExactGrowthCarriers.{u}
      fun t' h _ ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) :
    HollowReceiving.{u, w} IsCoverHollowAtBlock :=
  hollowReceiving_of_hasExactGrowthCarriers
    (HollowGrowthAcquisition.of_hollowAcquisition rootBottomAcquisition) hcar

/-- **(R3) for receiving models from exact growth carriers over the acquired marked-cap
contexts**: the third hypothesis of the three-hypothesis main theorem, conditional on the finite
statement of `hollowReceiving_of_hasExactGrowthCarriers_markedCap` (open). -/
theorem receivingHollowReceiving_of_hasExactGrowthCarriers_markedCap
    (hcar : HasExactGrowthCarriers.{u}
      fun t' h _ ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  (hollowReceiving_of_hasExactGrowthCarriers_markedCap hcar).receiving

end Realization

end VaughtConjecture
