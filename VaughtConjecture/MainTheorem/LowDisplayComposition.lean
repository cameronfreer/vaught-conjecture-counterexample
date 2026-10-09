/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowFullGradeAll
import VaughtConjecture.Continuation.LowStateStepBase
import VaughtConjecture.MainTheorem.LowStateFrontierRoute
import VaughtConjecture.MainTheorem.LowStateRoute
import VaughtConjecture.MainTheorem.LowDisplayRoute

/-!
# LOW displays for every LOW family, from the steps of the state tower above the controllers

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

The owner of a LOW family `(t', tb)` on `k + 1` points has grade `K ≤ k + 1`.  The three cases are
compiled separately:

* `K = k + 1` (the owner of full grade): LOW displays for every family
  (`StageType.hasLowDisplaysOn_fullGradeAll`, no hypothesis);
* `K = k`: LOW displays for every family (`StageType.hasLowDisplaysOn_lowBotAll`; there is no grade
  in `(K, k]`, so the faces are vacuously `⊥` there; no hypothesis);
* `K < k`: LOW displays from the lifts of the state tower (`StageType.hasLowDisplaysOn_stateLifts`,
  hypothesis `StageType.StateTowerLifts`), or from the steps for states on the amalgam
  (`StageType.hasLowDisplaysOn_stateAmalgam`, hypothesis `StageType.StateAmalgamSteps`), whose
  step at the grade `K` of the controllers is compiled for every LOW family
  (`ProfileTower.stateCatStep_low_seed`).

**The composition** (compiled in this repository):

* `StageType.hasLowDisplays_of_stateTowerLifts`: `StageType.HasLowDisplays` from
  `StageType.StateTowerLifts K t' tb p o r` at every LOW family with `K < k`, that is: for every
  decomposition `K = g + 1`, `k = g + J + 2`,
  `ProfileTower.STowerLifts (ProfileTower.lvlZero I g)
  (ProfileTower.lowPred (g + 1) (lowN I (g + 1)) (lowT I) o r) (J + 2)` on the seed `I` of the
  family, where
  `ProfileTower.STowerLifts L A J₀ := ∀ J < J₀, ∀ x ∈ Pts, ((sTower L A J).sS (sCat I (g + J + 1)
  A)).rows.CappedLift (X := (univ.erase x, g + J + 1)) (Y := (univ, g + J + 1))`: every layer of
  the state tower of the LOW clause, from the controllers at `K` to the grade `k`, lifts capped from
  the two coatoms into the full face at its grade.
* `StageType.hasLowDisplays_of_stateStepsAbove`: `StageType.HasLowDisplays` from the steps for
  states on the amalgam **above the controllers only** (`StageType.StateStepsAbove`: at the grades
  `K + 1, …, k`, for `K < k`): the step at the grade `K` is `ProfileTower.stateCatStep_low_seed`.

**Not claimed.**  `StageType.HasLowDisplays` is not proved: the lifts of the state tower
(`StageType.StateTowerLifts`) are open, and so are the steps for states above the controllers
(`StageType.StateStepsAbove`).

## References

The LOW construction is that of [AFK26]; the displays and generalized saturation are those of
[Kni26, §4.3].
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {k : ℕ}

/-- **The steps for states above the controllers of a LOW family** (a hypothesis): for every
decomposition `K = g + 1`, `k = g + J + 2`, the step for states on the amalgam of the seed of the
family (`ProfileTower.StateCatStep`), for the LOW clause at `K`, at every grade `K + 1, …, k`, from
the two coatoms.  The step at `K` itself is `ProfileTower.stateCatStep_low_seed`. -/
def StateStepsAbove (K : ℕ) (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card) : Prop :=
  ∀ (hF : IsLowFamily K t' tb p o r) (g J : ℕ) (hK : K = g + 1) (hk : k = g + J + 2), by
    subst hK hk
    exact ∀ J', 1 ≤ J' → J' < J + 2 → ∀ x ∈ (ProfileTower.Pts : Finset (Fin (g + J + 2 + 2))),
      ProfileTower.StateCatStep
        (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
        (g + J' + 1)
        (ProfileTower.lowPred (g + 1) (ProfileTower.lowN _ (g + 1)) (ProfileTower.lowT _)
          (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
            hF.face_donor).restrictFace_left o)
          (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
            hF.face_donor).restrictFace_left r)) x

/-- **The steps for states on the amalgam from the steps above the controllers**: at the grade `K`
of the controllers the step holds for every LOW family (`ProfileTower.stateCatStep_low_seed`). -/
theorem StateStepsAbove.stateAmalgamSteps {K : ℕ} {t' tb : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {o r : Fin t'.card} (h : StateStepsAbove K t' tb p o r) :
    StateAmalgamSteps K t' tb p o r := by
  intro hF g J hK hk
  subst hK hk
  intro J' hJ' x hx
  rcases J' with _ | J'
  · exact ProfileTower.stateCatStep_low_seed (by omega) hF.isSourceGapContextAt
      hF.topGrade_donor hx
  · exact h hF g J rfl rfl (J' + 1) (by omega) hJ' x hx

/-- **The owner of a LOW family has grade at most `k + 1`.** -/
theorem IsLowFamily.grade_le_succ {K : ℕ} {t' tb : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {o r : Fin t'.card} (hF : IsLowFamily K t' tb p o r) : K ≤ k + 1 :=
  hF.isSourceGapContextAt.grade_owner ▸ t'.grade_le o

/-- **LOW displays at `K = k`, for every family**: there is no grade in `(K, k]`
(`StageType.hasLowDisplaysOn_lowBotAll`). -/
theorem hasLowDisplaysOn_eq : HasLowDisplaysOn.{u} fun _ K k _ _ _ _ _ ↦ K = k := by
  intro α K k t' tb p o r hα hF hKk
  subst hKk
  exact hasLowDisplaysOn_lowBotAll t' tb p o r hα hF
    ⟨le_rfl, fun _ h1 h2 ↦ absurd (h1.trans_le h2) (lt_irrefl _),
      fun _ h1 h2 ↦ absurd (h1.trans_le h2) (lt_irrefl _)⟩

/-- **LOW displays at `K ≥ k`, for every family** (`K = k + 1`:
`StageType.hasLowDisplaysOn_fullGradeAll`; `K = k`: `StageType.hasLowDisplaysOn_eq`). -/
theorem hasLowDisplaysOn_ge : HasLowDisplaysOn.{u} fun _ K k _ _ _ _ _ ↦ k ≤ K := by
  intro α K k t' tb p o r hα hF hkK
  rcases Nat.lt_or_eq_of_le (hF.grade_le_succ) with hlt | heq
  · exact hasLowDisplaysOn_eq t' tb p o r hα hF (by omega)
  · exact hasLowDisplaysOn_fullGradeAll t' tb p o r hα hF heq

/-- **The composition: LOW displays for every LOW family from the lifts of the state tower**.
Every LOW family has `K = k + 1`, `K = k` (both compiled with no hypothesis) or `K < k`, where the
lifts of the state tower (`StageType.StateTowerLifts K t' tb p o r`: for every decomposition
`K = g + 1`, `k = g + J + 2`, `ProfileTower.STowerLifts (lvlZero I g) (lowPred (g + 1) (lowN I
(g + 1)) (lowT I) o r) (J + 2)` on the seed `I` of the family, i.e. every layer of the state tower
at a grade `g + J' + 1`, `J' < J + 2`, lifts capped from the two coatoms into `(univ, g + J' + 1)`)
give LOW displays (`StageType.hasLowDisplaysOn_stateLifts`).  The hypothesis is open, so
`StageType.HasLowDisplays` stays open. -/
theorem hasLowDisplays_of_stateTowerLifts
    (h : ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
      (o r : Fin t'.card), K < k → StateTowerLifts K t' tb p o r) :
    HasLowDisplays.{u} := by
  intro α K k t' tb p o r hα hF
  rcases lt_or_ge K k with hlt | hge
  · exact hasLowDisplaysOn_stateLifts t' tb p o r hα hF ⟨hlt, h t' tb p o r hlt⟩
  · exact hasLowDisplaysOn_ge t' tb p o r hα hF hge

/-- **The composition from the steps above the controllers**: LOW displays for every LOW family,
from the steps for states on the amalgam at the grades `K + 1, …, k` when `K < k`
(`StageType.StateStepsAbove`; the step at `K` is `ProfileTower.stateCatStep_low_seed`).  The
hypothesis is open, so `StageType.HasLowDisplays` stays open. -/
theorem hasLowDisplays_of_stateStepsAbove
    (habove : ∀ ⦃α : Ordinal.{u}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{u} α (k + 1))
      (p : StageType.{u} α k) (o r : Fin t'.card), K < k → StateStepsAbove K t' tb p o r) :
    HasLowDisplays.{u} := by
  intro α K k t' tb p o r hα hF
  rcases lt_or_ge K k with hlt | hge
  · exact hasLowDisplaysOn_stateAmalgam t' tb p o r hα hF
      ⟨hlt, (habove t' tb p o r hlt).stateAmalgamSteps⟩
  · exact hasLowDisplaysOn_ge t' tb p o r hα hF hge

end VaughtConjecture.StageType

namespace VaughtConjecture.MainTheorem

open FirstOrder Language baseLanguage Realization StageType Expansion

/-- **The thin `ℵ₁` spectrum with (R2) from the lifts of the state tower**
(`StageType.hasLowDisplays_of_stateTowerLifts`): conditional on (R4) for receiving models (`hR4`),
the lifts of the state tower at every LOW family with `K < k` (`hlift`), and (R3) for receiving
models (`hhol`); none of the three is proved here. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_stateTowerLifts
    (hR4 : ReceivingStableCappedReceiving.{0})
    (hlift : ∀ ⦃α : Ordinal.{0}⦄ ⦃K k : ℕ⦄ (t' tb : StageType.{0} α (k + 1))
      (p : StageType.{0} α k) (o r : Fin t'.card), K < k → StateTowerLifts K t' tb p o r)
    (hhol : HollowReceiving.{0, 0} IsReceivingCoverHollowAtBlock) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_lowDisplays hR4
    (hasLowDisplays_of_stateTowerLifts hlift) hhol

end VaughtConjecture.MainTheorem
