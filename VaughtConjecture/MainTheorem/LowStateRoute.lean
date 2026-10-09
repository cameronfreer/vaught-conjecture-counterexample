/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateReading
import VaughtConjecture.MainTheorem.LowDisplayReadingRoute

/-!
# LOW displays from the lifts of the state tower

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

**The lifts of the state tower of a LOW family** (`StageType.StateTowerLifts`, a hypothesis).  For
a LOW family `(t', tb)` at `K = g + 1` with `K < k = g + J + 2`, the state tower of the LOW clause
(`ProfileTower.sTower`) over the levels from the grade `0` at `g` (`ProfileTower.lvlZero`) on the
seed of the family lifts capped from the two coatoms into the full face at every grade from `K` to
`k` (`ProfileTower.STowerLifts`): at `K` the lift of the layer of controllers on the state catalogue
of the LOW clause, above `K` the LOW step at each grade.

**LOW layers on the class of the state lifts** (`StageType.hasLowLayersOn_stateLifts`,
`StageType.hasLowDisplaysOn_stateLifts`, compiled in this repository).  On the class
`StageType.StateLiftsClass` of the LOW families with `K < k` whose state tower lifts, LOW layers and
LOW displays exist (`ProfileTower.readsActualOn_sTower`), with no condition on the labels of the two
faces above `K`: the display reads every controller through the cutoff of the state of each cell
of full scope above `K`, so the separator is labelled `⊤` while the faces carry their own labels.

**Status.**  `StageType.HasLowDisplays` is proved (`StageType.hasLowDisplays_of_padded`, in
`VaughtConjecture.MainTheorem.LowPaddedRoute`, through the padded tower).  The lifts of the state
tower are not proved here: at `K` the lift of the state catalogue (the analogue of
`ProfileTower.Lvl.Good.cappedLift_lowS_seed` for states not normalized by the orbit code of the
amalgam part), above `K` the LOW step at each grade.  The families with `K = k` are covered by
`StageType.hasLowDisplaysOn_lowBot` when they have a donor top of grade `K`; `K = k + 1` is not
treated.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {k : ℕ}

/-- **The lifts of the state tower of a LOW family** (a hypothesis): for every decomposition
`K = g + 1`, `k = g + J + 2`, the state tower of the LOW clause over the levels from the grade `0`
at `g`, on the seed of the family, lifts from the two coatoms at every grade from `K` to `k`. -/
def StateTowerLifts (K : ℕ) (t' tb : StageType.{u} α (k + 1)) (p : StageType.{u} α k)
    (o r : Fin t'.card) : Prop :=
  ∀ (hF : IsLowFamily K t' tb p o r) (g J : ℕ) (hK : K = g + 1) (hk : k = g + J + 2), by
    subst hK hk
    exact ProfileTower.STowerLifts
      (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
      (ProfileTower.lvlZero _ g)
      (ProfileTower.lowPred (g + 1) (ProfileTower.lowN _ (g + 1)) (ProfileTower.lowT _)
        (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
          hF.face_donor).restrictFace_left o)
        (StageType.faceCell (Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private
          hF.face_donor).restrictFace_left r)) (J + 2)

/-- **The class of the state lifts**: the LOW families with `K < k` whose state tower lifts. -/
def StateLiftsClass (α : Ordinal.{u}) (K k : ℕ) (t' tb : StageType.{u} α (k + 1))
    (p : StageType.{u} α k) (o r : Fin t'.card) : Prop :=
  K < k ∧ StateTowerLifts K t' tb p o r

/-- **LOW layers on the class of the state lifts** (`ProfileTower.readsActualOn_sTower`): no
condition on the labels of the faces above `K`. -/
theorem hasLowLayersOn_stateLifts : HasLowLayersOn.{u} StateLiftsClass := by
  intro α K k t' tb p o r hα hF ⟨hKk, hlift⟩
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨J, rfl⟩ : ∃ J, k = g + J + 2 := ⟨k - (g + 2), by omega⟩
  exact ProfileTower.readsActualOn_sTower hα.isSuccPrelimit hF.isSourceGapContextAt
    hF.topGrade_donor (hlift hF g J rfl rfl)

/-- **LOW displays on the class of the state lifts.** -/
theorem hasLowDisplaysOn_stateLifts : HasLowDisplaysOn.{u} StateLiftsClass :=
  hasLowLayersOn_stateLifts.hasLowDisplaysOn

end VaughtConjecture.StageType
