/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRootBottom
import VaughtConjecture.Realization.GrowthCarrier
import VaughtConjecture.MainTheorem.ReceivingDomains

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
  `t'` along `h`, some growth carrier recovers the labels of `d`
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

* `StageType.HollowReferenceCalibration` and its acquisition
  `Realization.hollowGrowthAcquisition_reference` (compiled, no hypothesis): the marked-cap
  contexts along an enlarged root carrying a reference cell in the block of every ordinal label of
  the donor; so `Realization.hollowReceiving_of_hasExactGrowthCarriers_reference` reduces (R3)
  for cover-hollowness at a block stage to exact growth carriers for this calibration alone.

The marked-cap contexts alone carry no reference cell for the blocks of the proper labels of `d`;
the reference calibration adds them, as the margin calibration does for (R4)
(`StageType.GradedCapMarginCalibration`).

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
the scheme of `t'` with donor scheme that of `d` along `h` recovers the labels of `d` exactly, the
formal top included, from the labels of `t'`.  A coface of `t'` on the carrier is automatic
(`GrowthCarrier.nonempty_cofaces_inter_saturationFamily_of_isSuccPrelimit`). -/
def HasExactGrowthCarriers
    (C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ t : StageType.{u} α n, restrictFace h t' = some t →
      ∀ d ∈ t.cofaces, C t' h d → ∃ G : GrowthCarrier t'.toScheme d.toScheme h,
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
    obtain ⟨G, hrec⟩ := hcar t' h hα ht' t ht d hd hP
    obtain ⟨D', hD', hD'E⟩ :=
      G.nonempty_cofaces_inter_saturationFamily_of_isSuccPrelimit hα.isSuccPrelimit rfl
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
    obtain ⟨G, hrec⟩ := hcar t' h hα (hR.isLegal _ _ hc'.eval_eq) t
      (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd hC
    obtain ⟨u, hu, -, hev⟩ := GrowthCarrier.exists_eval_eq_of_recovers_eq hR x G
      (G.nonempty_cofaces_inter_saturationFamily_of_isSuccPrelimit hα.isSuccPrelimit rfl) hrec
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

/-! ### The reference calibration -/

namespace StageType

/-- The **hollow reference calibration** of a context `t'` along `h` for a donor `d`: `h` factors
through an enlarged root `g` along which `t'` is a marked-cap context with root offsets below the
cap that respects the root bottoms (`TiedRootCapRelabel.MarkedCapContextBelow'`), and every
ordinal label `o = μ + m` of `d`, `μ` zero or a limit, has a **reference cell** of the enlarged
root in its block: a cell visible through `g` labelled `μ + r` for some `r : ℕ`. -/
def HollowReferenceCalibration {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k)
    (h : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1)) : Prop :=
  ∃ (j : ℕ) (g : Fin j ↪ Fin k) (h₀ : Fin n ↪ Fin j), h₀.trans g = h ∧
    TiedRootCapRelabel.MarkedCapContextBelow' t' g ∧
    ∀ (i : Fin d.card) (o : Ordinal.{u}), d.label i = o →
      ∃ (μ : Ordinal.{u}) (m r : ℕ) (a : Fin t'.card), Order.IsSuccPrelimit μ ∧ o = μ + m ∧
        a ∈ t'.visibleCells g ∧ t'.label a = ((μ + r : Ordinal.{u}) : Label.{u})

/-- At a limit stage every label of a stage type lies in a block below the stage: an ordinal
label is `μ + m` with `μ` zero or a limit below the stage. -/
theorem exists_block {α : Ordinal.{u}} {n : ℕ} (hα : Order.IsSuccLimit α)
    (d : StageType.{u} α n) (i : Fin d.card) :
    ∃ μ : Ordinal.{u}, (Order.IsSuccPrelimit μ ∧ μ < α) ∧
      ∀ o : Ordinal.{u}, d.label i = o → ∃ m : ℕ, o = μ + m := by
  have hpos : (0 : Ordinal.{u}) < α := hα.bot_lt
  rcases atStage_iff.mp (d.atStage i) with h | ⟨o, ho, h⟩ | h
  · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, fun o ho ↦ by simp [h] at ho⟩
  · obtain ⟨m, hm⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
      (Ordinal.mul_div_le o Ordinal.omega0)
      (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
    refine ⟨Ordinal.omega0 * (o / Ordinal.omega0),
      ⟨Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
        (Ordinal.mul_div_le o Ordinal.omega0).trans_lt ho⟩, fun o' ho' ↦ ⟨m, ?_⟩⟩
    rw [← h] at ho'
    exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hm
  · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, hpos⟩, fun o ho ↦ by simp [h] at ho⟩

end StageType

namespace Realization

/-- **Acquisition of the hollow reference calibration**, with no hypothesis: in a model at a
limit stage that is cover-hollow at a block stage with top-grade supremum `⊤`, every cover `c` of
`t` extends, for each one-point coface `d` of `t`, to a cover of a context calibrated for `d`.
Uniformity gives an occurrence `y` containing `c` with a reference cell in the block of every
ordinal label of `d` (`Realization.IsModel.exists_extend_uniformity`); the acquisition of
marked-cap contexts (`Realization.rootBottomAcquisition`) over the cover `y` gives the context,
along an enlarged root through which the reference cells are visible with their labels. -/
theorem hollowGrowthAcquisition_reference :
    HollowGrowthAcquisition.{u, w} IsCoverHollowAtBlock StageType.HollowReferenceCalibration where
  exists_context α M R hα hR hH htop n t c hc d _ := by
    choose ν hν hνo using StageType.exists_block hα d
    let x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
    obtain ⟨y, fy, K, B, hfy, -, -, href⟩ :=
      hR.exists_extend_uniformity x hα.bot_lt (List.ofFn ν) fun μ hμ ↦ by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hμ
        exact hν i
    obtain ⟨k, t', c', g, hc', hcg, hP⟩ := rootBottomAcquisition.exists_context hα hR hH htop
      y.type y.tuple (covers_of_eval _ y.eval_tuple)
    have hface : restrictFace g t' = some y.type :=
      restrictFace_of_covers hR.isConsistent (covers_of_eval _ y.eval_tuple) hc' hcg
    refine ⟨k, t', c', fy.trans g, hc', ?_, y.arity, g, fy, rfl, hP, fun i o ho ↦ ?_⟩
    · funext i
      change (c' ∘ g) (fy i) = c i
      rw [hcg]
      exact DFunLike.congr_fun hfy i
    · obtain ⟨m, hm⟩ := hνo i o ho
      obtain ⟨z, r, -, hz, -⟩ := href (ν i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
      obtain ⟨z', -, hz'l, -⟩ := exists_cellMap_of_restrictFace_eq hface z
      exact ⟨ν i, m, r, t'.cellMap g z', (hν i).1, hm, t'.cellMap_mem g z', hz'l.trans hz⟩

/-- **(R3) from exact growth carriers for the hollow reference calibration**: exact growth
carriers over the contexts of `StageType.HollowReferenceCalibration`, a finite statement about
stage types (open), give (R3) for cover-hollowness at a block stage; the acquisition is compiled
(`Realization.hollowGrowthAcquisition_reference`). -/
theorem hollowReceiving_of_hasExactGrowthCarriers_reference
    (hcar : HasExactGrowthCarriers.{u} StageType.HollowReferenceCalibration) :
    HollowReceiving.{u, w} IsCoverHollowAtBlock :=
  hollowReceiving_of_hasExactGrowthCarriers hollowGrowthAcquisition_reference hcar

/-- **(R3) for receiving models from exact growth carriers for the hollow reference
calibration**: the third hypothesis of the three-hypothesis main theorem, conditional on the
finite statement of `hollowReceiving_of_hasExactGrowthCarriers_reference` (open). -/
theorem receivingHollowReceiving_of_hasExactGrowthCarriers_reference
    (hcar : HasExactGrowthCarriers.{u} StageType.HollowReferenceCalibration) :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  (hollowReceiving_of_hasExactGrowthCarriers_reference hcar).receiving

end Realization

end VaughtConjecture
