/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthControllerRecovery
import VaughtConjecture.Continuation.GrowthRecognition
import VaughtConjecture.Continuation.GrowthTemplate
import VaughtConjecture.MainTheorem.GrowthPadding
import VaughtConjecture.MainTheorem.GrowthRoute

/-!
# Exact growth carriers from admitted carriers

Roadmap, Layer 3 ((R3), the growth carrier at a calibrated context).

At a legal context `t'` calibrated along its root `e` for a legal donor `d` with a nonempty root
(`StageType.HollowReferenceCalibration'`, `0 < n`), the requests of
`StageType.HollowReferenceCalibration'.exists_relativeLift` are read exactly at the labels of `t'`,
are calibrated, and have the relative lift on the donor.  What is left of the exact growth carrier
is one finite construction, stated here as a named hypothesis:

* **Admitted growth carriers** (`StageType.HasAdmittedGrowthCarriers`, open): for such requests, a
  growth carrier with literal context and donor faces, with a cell of full scope at the threshold,
  every such cell a controller admitted on the class
  (`GrowthCarrier.IsClassAdmittedController`).

The recovery is then compiled: availability at the cap gives an admitted controller, and its row
transfers to every lawful section (`GrowthCarrier.recovers_of_classAdmittedControllers`); the
requests read exactly at the labels of `t'` give exact recovery
(`StageType.HasAdmittedGrowthCarriers.hasExactGrowthCarriers`) for the calibration with a nonempty
root (`StageType.HollowReferenceCalibrationPos`).

The empty root is not needed: (R3) over covers of positive arity gives (R3) over every cover by
padding (`Realization.HollowReceiving.of_pos`), so exact growth carriers for the calibration with
a nonempty root give (R3) (`Realization.hollowReceiving_of_hasExactGrowthCarriers_pos`), and the
main theorem holds with the hypothesis `hexact` restricted to nonempty roots
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_growthCarriers_pos`) or replaced by
admitted growth carriers
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_admittedCarriers`).
These are implications; the hypotheses stay open.

**Recognizing growth carriers** (`StageType.HasRecognizingGrowthCarriers`, open) replace the
admitted carriers: no good level continues a layer whose cells at the threshold are all admitted
(`ProfileTower.Lvl.Good.not_forall_admitted`).  The catalogue states are admitted on the exact class
(`StageType.GrowthRequests.AdmitsOnClass`), and every lawful section, capped at a label above its
cap value, is recognized as the image of such a state (`GrowthCarrier.Recognizes`); recovery
follows (`GrowthCarrier.recovers_of_recognizes`), hence exact growth carriers at nonempty roots
(`StageType.HasRecognizingGrowthCarriers.hasExactGrowthCarriers`) and the main theorem
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_recognizingCarriers`).

## References

The growth construction is that of [Kni26, §4]; the controllers of the growth step are those of
[Kni26, §4].
-/

universe u w

namespace VaughtConjecture

open Finset StageType

namespace StageType

/-- The **hollow reference calibration with a nonempty root**. -/
def HollowReferenceCalibrationPos {α : Ordinal.{u}} {n k : ℕ} (t' : StageType.{u} α k)
    (e : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1)) : Prop :=
  HollowReferenceCalibration' t' e d ∧ 0 < n

/-- **Admitted growth carriers** (open): at every legal context `t'` at a limit stage, with root
`e`, face `p` and a one-point coface `d` of `p` (`0 < n`), for every requests `Q` read exactly at
the labels of `t'`, calibrated and with the relative lift on the donor, some growth carrier with
the schemes of `t'` and `d` as literal faces has a cell of full scope at the threshold, and every
such cell is a controller admitted on the class. -/
def HasAdmittedGrowthCarriers : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (e : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ (p : StageType.{u} α n)
      (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces),
      0 < n → ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) → Q.Calibrated hte →
        Q.HasRelativeLift hte hd.2 →
        ∃ G : GrowthCarrier t'.toScheme d.toScheme e,
          (∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold)) ∧
          ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
            G.IsClassAdmittedController Q u

/-- **Exact recovery from an admitted carrier**: a growth carrier for requests read exactly at the
labels of `t'` and calibrated, with a cell of full scope at the threshold, every such cell a
controller admitted on the class, recovers the labels of `d` exactly from the labels of `t'`. -/
theorem GrowthRequests.recovers_eq_of_admitted {α : Ordinal.{u}} {n k : ℕ}
    {t' : StageType.{u} α k} {e : Fin n ↪ Fin k} {p : StageType.{u} α n}
    {hte : restrictFace e t' = some p} {d : StageType.{u} α (n + 1)}
    {Q : GrowthRequests t' d.toScheme} (hex : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j)
    (hQ : Q.Calibrated hte) (G : GrowthCarrier t'.toScheme d.toScheme e)
    (hfull : ∃ w, G.scheme.toCellScheme.gradedIndex w = (univ, Q.threshold))
    (hadm : ∀ u, G.scheme.toCellScheme.gradedIndex u = (univ, Q.threshold) →
      G.IsClassAdmittedController Q u) :
    G.Recovers t'.label fun j ℓ ↦ ℓ = d.label j := by
  have hdon (j : Fin d.card) : G.scheme.toCellScheme.grade (G.donorCell j) ≤ Q.threshold := by
    rw [GrowthCarrier.donorCell, Scheme.grade_faceCell]
    exact (d.grade_le j).trans hQ.arity
  have hrec := G.recovers_of_classAdmittedControllers Q hfull hadm hdon
    (fun j hj ↦ ⟨(hQ.ref j hj).1, (hQ.ref j hj).2.1⟩) ⟨hQ.marker.1, hQ.marker.2.1⟩
    (σ := t'.label) (fun _ _ h ↦ h) hQ.label_cap
  intro v hv hctx i j hij
  exact (hex j _).mp (hrec v hv hctx i j hij)

/-- **Exact growth carriers for the calibration with a nonempty root from admitted growth
carriers**: the requests of `StageType.HollowReferenceCalibration'.exists_relativeLift` and the
admitted carrier for them recover the donor exactly
(`StageType.GrowthRequests.recovers_eq_of_admitted`). -/
theorem HasAdmittedGrowthCarriers.hasExactGrowthCarriers (h : HasAdmittedGrowthCarriers.{u}) :
    HasExactGrowthCarriers.{u} HollowReferenceCalibrationPos := by
  intro α n k t' e hα ht' p hte d hd hC
  obtain ⟨hC, hn⟩ := hC
  obtain ⟨Q, hex, hQ, hrel⟩ := hC.exists_relativeLift ht' hte hd.2 hd.1 hn
  obtain ⟨G, hfull, hadm⟩ := h t' e hα ht' p hte d hd hn Q hex hQ hrel
  exact ⟨G, GrowthRequests.recovers_eq_of_admitted hex hQ G hfull hadm⟩

/-- **Recognizing growth carriers** (open): at every legal context `t'` at a limit stage, with root
`e`, face `p` and a one-point coface `d` of `p` (`0 < n`), for every requests `Q` read exactly at
the labels of `t'`, calibrated and with the relative lift on the exact class, some growth carrier
with the schemes of `t'` and `d` as literal faces recognizes admitted states in its lawful
sections (`GrowthCarrier.Recognizes`).  This replaces `StageType.HasAdmittedGrowthCarriers`, whose
"every cell of full scope at the threshold admitted" no good level can continue
(`ProfileTower.Lvl.Good.not_forall_admitted`). -/
def HasRecognizingGrowthCarriers : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (e : Fin n ↪ Fin k),
    Order.IsSuccLimit α → t'.IsLegal → ∀ (p : StageType.{u} α n)
      (hte : restrictFace e t' = some p) (d : StageType.{u} α (n + 1)) (hd : d ∈ p.cofaces),
      0 < n → ∀ Q : GrowthRequests t' d.toScheme,
        (∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j) → Q.Calibrated hte →
        Q.HasRelativeLiftOnClass hte hd.2 →
        ∃ G : GrowthCarrier t'.toScheme d.toScheme e, G.Recognizes Q

/-- **Exact recovery from a recognizing carrier** for calibrated requests read exactly at the
labels of `t'`: the labels of `t'` have exactly their own bottom pattern and the cap labelled other
than `⊥` (`GrowthCarrier.recovers_of_recognizes`). -/
theorem GrowthRequests.recovers_eq_of_recognizes {α : Ordinal.{u}} {n k : ℕ}
    {t' : StageType.{u} α k} {e : Fin n ↪ Fin k} {p : StageType.{u} α n}
    {hte : restrictFace e t' = some p} {d : StageType.{u} α (n + 1)}
    {Q : GrowthRequests t' d.toScheme} (hex : ∀ j ℓ, Q.CorrectAt t'.label j ℓ ↔ ℓ = d.label j)
    (hQ : Q.Calibrated hte) (G : GrowthCarrier t'.toScheme d.toScheme e)
    (hrec : G.Recognizes Q) : G.Recovers t'.label fun j ℓ ↦ ℓ = d.label j := by
  have hrecov := G.recovers_of_recognizes Q hrec
    (fun j hj ↦ ⟨Q.mem_below_cap hQ.scope_cap (hQ.ref j hj).1, (hQ.ref j hj).2.1⟩)
    ⟨Q.mem_below_cap hQ.scope_cap hQ.marker.1, hQ.marker.2.1⟩
    (σ := t'.label) (fun _ _ ↦ Iff.rfl) hQ.label_cap
  intro v hv hctx i j hij
  exact (hex j _).mp (hrecov v hv hctx i j hij)

/-- **Exact growth carriers for the calibration with a nonempty root from recognizing growth
carriers**: the requests of `StageType.HollowReferenceCalibration'.exists_relativeLift` have the
relative lift on the exact class
(`StageType.GrowthRequests.hasRelativeLiftOnClass_of_hasRelativeLift`), and the recognizing
carrier for them recovers the donor exactly. -/
theorem HasRecognizingGrowthCarriers.hasExactGrowthCarriers
    (h : HasRecognizingGrowthCarriers.{u}) :
    HasExactGrowthCarriers.{u} HollowReferenceCalibrationPos := by
  intro α n k t' e hα ht' p hte d hd hC
  obtain ⟨hC, hn⟩ := hC
  obtain ⟨Q, hex, hQ, hrel⟩ := hC.exists_relativeLift ht' hte hd.2 hd.1 hn
  obtain ⟨G, hrec⟩ := h t' e hα ht' p hte d hd hn Q hex hQ
    (GrowthRequests.hasRelativeLiftOnClass_of_hasRelativeLift hte hd.2 hex hQ hd.1 hn hrel)
  exact ⟨G, GrowthRequests.recovers_eq_of_recognizes hex hQ G hrec⟩

end StageType

namespace Realization

/-- **(R3) from exact growth carriers with a nonempty root**: over covers of positive arity the
acquired context has a nonempty root, so exact growth carriers for `C` restricted to nonempty roots
receive every one-point coface exactly (as `Realization.hollowReceiving_of_hasExactGrowthCarriers`);
padding (`Realization.HollowReceiving.of_pos`) gives every cover. -/
theorem hollowReceiving_of_hasExactGrowthCarriers_pos
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    {C : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hacq : HollowGrowthAcquisition.{u, w} H C)
    (hcar : HasExactGrowthCarriers.{u} fun {_ n _} t' h d ↦ C t' h d ∧ 0 < n) :
    HollowReceiving.{u, w} H :=
  HollowReceiving.of_pos ⟨fun α M R hα hR hH htop n hn t c hc d hd ↦ by
    obtain ⟨k, t', c', h, hc', hcc', hC⟩ := hacq.exists_context hα hR hH htop t c hc d hd
    let x : R.Occurrence := ⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩
    obtain ⟨G, hrec⟩ := hcar t' h hα (hR.isLegal _ _ hc'.eval_eq) t
      (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd ⟨hC, hn⟩
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
    exact covers_of_eval u hev⟩

/-- The receiving form of (R3) from exact growth carriers for the reference calibration with a
nonempty root (open). -/
theorem receivingHollowReceiving_of_hasExactGrowthCarriers_pos
    (hcar : HasExactGrowthCarriers.{u} HollowReferenceCalibrationPos) :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  (hollowReceiving_of_hasExactGrowthCarriers_pos hollowGrowthAcquisition_reference' hcar).receiving

end Realization

namespace MainTheorem

open Ordinal Realization FirstOrder Language Structure baseLanguage Expansion

/-- **The thin `ℵ₁` spectrum from growth carriers with a nonempty root**: as
`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_growthCarriers`, with `hexact` asked only
at nonempty roots.  The three hypotheses are open. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_growthCarriers_pos
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hexact : HasExactGrowthCarriers.{0} HollowReferenceCalibrationPos) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels'
    (Expansion.ReceivingStableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin hstab)
    hres (Realization.receivingHollowReceiving_of_hasExactGrowthCarriers_pos hexact)

/-- **The thin `ℵ₁` spectrum from admitted growth carriers**: (R3) from the admitted carriers
(`StageType.HasAdmittedGrowthCarriers`, open) through the compiled template, relative lift and
recovery.  The three hypotheses are open. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_admittedCarriers
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hadm : HasAdmittedGrowthCarriers.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_growthCarriers_pos hstab hres
    hadm.hasExactGrowthCarriers

/-- **The thin `ℵ₁` spectrum from recognizing growth carriers**: (R3) from the recognizing carriers
(`StageType.HasRecognizingGrowthCarriers`, open) through the compiled template, relative lift on
the exact class and recovery by recognition.  The three hypotheses are open. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_recognizingCarriers
    (hstab : ∀ ξ < ω₁, HasStableGrowthCarriers.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (hres : ReceivingResidualReceiving.{0, 0})
    (hrec : HasRecognizingGrowthCarriers.{0}) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_growthCarriers_pos hstab hres
    hrec.hasExactGrowthCarriers

end MainTheorem

end VaughtConjecture
