/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateLift
import VaughtConjecture.MainTheorem.LowStateRoute

/-!
# LOW displays from the frontier steps of the state tower

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

**The frontier steps of a LOW family** (`StageType.StateFrontierSteps`, a hypothesis).  For a LOW
family at `K = g + 1` with `K < k = g + J + 2`, the frontier step
(`ProfileTower.SLvl.SFrontierStep`) from the two coatoms at every layer of the state tower of the
LOW clause over the levels from the grade `0` at `g`: at the layer of controllers `K` and at
every grade above, up to `k`.

**LOW layers on the class of the frontier steps** (`StageType.hasLowLayersOn_stateFrontier`,
`StageType.hasLowDisplaysOn_stateFrontier`, compiled in this repository).  The frontier steps give
the lifts of the state tower (`ProfileTower.sTowerLifts_of_frontier`: the base level, a canonical
next level, is readable at the canonical states, `ProfileTower.Lvl.Good.readableS_toS_next`), hence
LOW layers and LOW displays (`ProfileTower.readsActualOn_sTower`), with no condition on the face
labels above `K`.

**From the steps for states on the amalgam** (`StageType.StateAmalgamSteps`,
`StageType.hasLowDisplaysOn_stateAmalgam`, compiled in this repository): the same with the state
step stated on amalgam labellings below the coatom with an uncoded conclusion
(`ProfileTower.SLvl.sCatStep_of_amalgam`; the orbit code over all fields keeps the LOW clause), the
form in which the LOW step for states at `K` is proved for every LOW family of top grade at most
`K` in the lower-top lane (`ProfileTower.stateCatStep_low_seed`); there the grades above `K` remain.

**Not claimed.**  `StageType.HasLowDisplays` is not proved.  The frontier steps are not proved
here.  At the layer of controllers the frontier step is what the LOW steps of the catalogue layer
(`ProfileTower.Lvl.Good.lowStep_donor`, `ProfileTower.Lvl.Good.lowStep_private`) build before they
code the cutoff, for a state normalized over all fields in place of a profile normalized on its
amalgam part; above `K` it is the LOW step at each grade.  The families with `K ≥ k` are outside the
class; `K = 1` is included (the level at the grade `0` is readable at the canonical states,
`ProfileTower.readableS_base₀`).

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {k : ℕ}

/-- **The frontier steps of the state tower of a LOW family** (a hypothesis): for every
decomposition `K = g + 1`, `k = g + J + 2`, the frontier step from the two coatoms at every layer
of the state tower of the LOW clause over the levels from the grade `0` at `g`, on the seed of the
family. -/
def StateFrontierSteps (K : ℕ) (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card) : Prop :=
  ∀ (hF : IsLowFamily K t' tb p o r) (g J : ℕ) (hK : K = g + 1) (hk : k = g + J + 2), by
    subst hK hk
    exact ProfileTower.STowerFrontier
      (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
      (ProfileTower.lvlZero _ g) (g + 1) (ProfileTower.lowN _ (g + 1)) (ProfileTower.lowT _)
      (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
        hF.face_donor).restrictFace_left o)
      (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
        hF.face_donor).restrictFace_left r) (J + 2)

/-- **The class of the frontier steps**: the LOW families with `K < k` whose state tower has
the frontier steps. -/
def StateFrontierClass (α : Ordinal.{u}) (K k : ℕ) (t' tb : StageType.{u} α (k + 1))
    (p : StageType.{u} α k) (o r : Fin t'.card) : Prop :=
  K < k ∧ StateFrontierSteps K t' tb p o r

/-- **LOW layers on the class of the frontier steps**: no condition on the labels of the faces
above `K`. -/
theorem hasLowLayersOn_stateFrontier : HasLowLayersOn.{u} StateFrontierClass := by
  intro α K k t' tb p o r hα hF ⟨hKk, hfr⟩
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨J, rfl⟩ : ∃ J, k = g + J + 2 := ⟨k - (g + 2), by omega⟩
  have hs := hF.isSourceGapContextAt
  have htb := hF.topGrade_donor
  set I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor
  have hF' := ProfileTower.fieldsLE_low (I := I) hs htb
  have hr := (ProfileTower.lost_copy (I := I) hs).2
  have hNi : Sum.inr () ∉ ProfileTower.lowN I (g + 1) := fun h ↦ by
    obtain ⟨t, -, ht⟩ := mem_image.mp h
    cases ht
  have hTi : Sum.inr () ∉ ProfileTower.lowT I := fun h ↦ by
    obtain ⟨t, -, ht⟩ := h
    cases ht
  have hL := ProfileTower.lvlZero_good (I := I) g (by omega)
  have hRL := ProfileTower.readableS_lvlZero (I := I) g (by omega)
  exact ProfileTower.readsActualOn_sTower hα.isSuccPrelimit hs htb
    (ProfileTower.sTowerLifts_of_frontier hL hRL le_rfl hNi hTi
      (fun j hj P h ↦ ProfileTower.lowPred_scode hF' hr hj h) (J + 2) (by omega)
      (hfr hF g J rfl rfl))

/-- **LOW displays on the class of the frontier steps.** -/
theorem hasLowDisplaysOn_stateFrontier : HasLowDisplaysOn.{u} StateFrontierClass :=
  hasLowLayersOn_stateFrontier.hasLowDisplaysOn


/-- **The steps for states on the amalgam of a LOW family** (a hypothesis): for every
decomposition `K = g + 1`, `k = g + J + 2`, the step for states on the amalgam of the seed of the
family, for the LOW clause at `K`, at every grade from `K` to `k`, from the two coatoms (the
form of `ProfileTower.StateCatStep` of the lower-top lane). -/
def StateAmalgamSteps (K : ℕ) (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card) : Prop :=
  ∀ (hF : IsLowFamily K t' tb p o r) (g J : ℕ) (hK : K = g + 1) (hk : k = g + J + 2), by
    subst hK hk
    exact ProfileTower.STowerAmalgamSteps
      (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
      g (ProfileTower.lowPred (g + 1) (ProfileTower.lowN _ (g + 1)) (ProfileTower.lowT _)
        (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
          hF.face_donor).restrictFace_left o)
        (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
          hF.face_donor).restrictFace_left r)) (J + 2)

/-- **The class of the steps for states on the amalgam**: the LOW families with `K < k` with
the steps for states on the amalgam at every grade from `K` to `k`. -/
def StateAmalgamClass (α : Ordinal.{u}) (K k : ℕ) (t' tb : StageType.{u} α (k + 1))
    (p : StageType.{u} α k) (o r : Fin t'.card) : Prop :=
  K < k ∧ StateAmalgamSteps K t' tb p o r

/-- **LOW layers on the class of the steps for states on the amalgam**: no condition on the labels
of the faces above `K` (`ProfileTower.sTowerLifts_of_amalgam`,
`ProfileTower.readsActualOn_sTower`). -/
theorem hasLowLayersOn_stateAmalgam : HasLowLayersOn.{u} StateAmalgamClass := by
  intro α K k t' tb p o r hα hF ⟨hKk, hst⟩
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨J, rfl⟩ : ∃ J, k = g + J + 2 := ⟨k - (g + 2), by omega⟩
  have hs := hF.isSourceGapContextAt
  have htb := hF.topGrade_donor
  set I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor
  have hF' := ProfileTower.fieldsLE_low (I := I) hs htb
  have hr := (ProfileTower.lost_copy (I := I) hs).2
  have hL := ProfileTower.lvlZero_good (I := I) g (by omega)
  have hRL := ProfileTower.readableS_lvlZero (I := I) g (by omega)
  exact ProfileTower.readsActualOn_sTower hα.isSuccPrelimit hs htb
    (ProfileTower.sTowerLifts_of_amalgam hL hRL (fun W ↦ ProfileTower.lowPred_withCut_bot W)
      (fun j hj P h ↦ ProfileTower.lowPred_scode hF' hr hj h)
      (fun j hj V h ↦ h.map (isWitness_orbitMap j V) (stepSuppressor_of_le hj)) (J + 2)
      (by omega) (hst hF g J rfl rfl))

/-- **LOW displays on the class of the steps for states on the amalgam.** -/
theorem hasLowDisplaysOn_stateAmalgam : HasLowDisplaysOn.{u} StateAmalgamClass :=
  hasLowLayersOn_stateAmalgam.hasLowDisplaysOn

end VaughtConjecture.StageType
