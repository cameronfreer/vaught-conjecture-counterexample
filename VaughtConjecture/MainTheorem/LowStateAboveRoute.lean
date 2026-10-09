/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStepBase
import VaughtConjecture.MainTheorem.LowStateFrontierRoute

/-!
# LOW displays from the steps for states above the controllers

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

**The layer of controllers lifts** (`StageType.stateAmalgamSteps_of_above`, compiled in this
repository).  At the grade `K` of the controllers the step for states on the amalgam is a theorem
for every LOW family (`ProfileTower.stateCatStep_low_seed`), so the lift of the layer of
controllers of the state tower holds with no hypothesis (`ProfileTower.sTowerLifts_of_amalgam`,
`ProfileTower.SLvl.sCatStep_of_amalgam`).

**LOW displays from the steps above `K`** (`StageType.hasLowLayersOn_stateAbove`,
`StageType.hasLowDisplaysOn_stateAbove`, compiled in this repository).  On the class
`StageType.StateAboveClass` of the LOW families with `K < k` having the step for states on the
amalgam at every grade in `(K, k]` (`StageType.StateAboveSteps`), LOW layers and LOW displays exist,
with no condition on the labels of the faces above `K`.

**Not claimed.**  `StageType.HasLowDisplays` is not proved.  The steps for states above `K` are
proved in the lower-top lane only at the states whose labels at the cells of grade in `(K, j]` lie
below the cap (`ProfileTower.stateCatStep_low_seed_of_lt_cap`); the lift needs them at every state
of the catalogue.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {k : ℕ}

/-- **The steps for states above the controllers** (a hypothesis): for every decomposition
`K = g + 1`, `k = g + J + 2`, the step for states on the amalgam of the seed of the family, for
the LOW clause at `K`, at every grade in `(K, k]`, from the two coatoms. -/
def StateAboveSteps (K : ℕ) (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card) : Prop :=
  ∀ (hF : IsLowFamily K t' tb p o r) (g J : ℕ) (hK : K = g + 1) (hk : k = g + J + 2), by
    subst hK hk
    exact ∀ j, g + 1 < j → j ≤ g + J + 2 → ∀ x ∈ (ProfileTower.Pts : Finset (Fin (_ + 2))),
      ProfileTower.StateCatStep
        (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor) j
        (ProfileTower.lowPred (g + 1) (ProfileTower.lowN _ (g + 1)) (ProfileTower.lowT _)
          (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
            hF.face_donor).restrictFace_left o)
          (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
            hF.face_donor).restrictFace_left r)) x

/-- **The class of the steps above the controllers**: the LOW families with `K < k` with the
steps for states on the amalgam at every grade in `(K, k]`. -/
def StateAboveClass (α : Ordinal.{u}) (K k : ℕ) (t' tb : StageType.{u} α (k + 1))
    (p : StageType.{u} α k) (o r : Fin t'.card) : Prop :=
  K < k ∧ StateAboveSteps K t' tb p o r

/-- **The steps above the controllers give the steps of the state tower**: at the grade `K` the
step for states is `ProfileTower.stateCatStep_low_seed`. -/
theorem stateAmalgamSteps_of_above {K : ℕ} {t' tb : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {o r : Fin t'.card} (hKk : K < k)
    (h : StateAboveSteps K t' tb p o r) : StateAmalgamSteps K t' tb p o r := by
  intro hF g J hK hk
  subst hK hk
  intro J' hJ' x hx
  rcases J' with _ | J'
  · exact ProfileTower.stateCatStep_low_seed (by omega) hF.isSourceGapContextAt
      hF.topGrade_donor hx
  · exact h hF g J rfl rfl (g + (J' + 1) + 1) (by omega) (by omega) x hx

/-- **LOW layers on the class of the steps above the controllers**: no condition on the labels of
the faces above `K`. -/
theorem hasLowLayersOn_stateAbove : HasLowLayersOn.{u} StateAboveClass :=
  fun _ _ _ t' tb p o r hα hF ⟨hKk, h⟩ ↦
    hasLowLayersOn_stateAmalgam t' tb p o r hα hF ⟨hKk, stateAmalgamSteps_of_above hKk h⟩

/-- **LOW displays on the class of the steps above the controllers.** -/
theorem hasLowDisplaysOn_stateAbove : HasLowDisplaysOn.{u} StateAboveClass :=
  hasLowLayersOn_stateAbove.hasLowDisplaysOn

end VaughtConjecture.StageType
