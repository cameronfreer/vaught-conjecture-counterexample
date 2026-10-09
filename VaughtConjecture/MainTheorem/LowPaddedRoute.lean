/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowPaddedReading
import VaughtConjecture.MainTheorem.LowDisplayComposition

/-!
# LOW displays for every LOW family, through the padded tower

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3) and Layer 6 ("Status:
the hypotheses of the main theorem"); semantic contract, items 4, 5 and 8.

**LOW layers and LOW displays at `K < k`** (`StageType.hasLowLayersOn_lt`,
`StageType.hasLowDisplaysOn_lt`, compiled in this repository).  For a LOW family `(t', tb)` with
`K = g + 1 < k = g + J + 2`, the padded tower of the LOW clause over the proper donor fields of
every grade, over the levels from the grade `0` at `g` on the seed of the family, reads the actual
state (`ProfileTower.readsActualOn_pTower`): its lifts are the steps for states at every grade
from `K` to `k` (`ProfileTower.stateCatStep_lowAll_seed`).  The display is legal, its faces are
the private context and the donor with their labels, and its LOW layer at `K` has a separator
labelled by a proper label and `⊤`.

**LOW displays for every LOW family** (`StageType.hasLowDisplays_of_padded`, compiled in this
repository): `K < k` by the padded tower, `K ≥ k` by `StageType.hasLowDisplaysOn_ge`.  The
statement is `StageType.HasLowDisplays`, with no hypothesis.

**The main theorem with (R2) from the padded tower**
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_padded`, compiled in this repository):
conditional on (R4) for receiving models and (R3) for receiving models, which are not proved here.

## References

The LOW construction is that of [AFK26]; the displays and generalized saturation are those of
[Kni26, §4.3].
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

/-- **LOW layers on the LOW families with `K < k`** (`ProfileTower.readsActualOn_pTower` on the
seed of the family), with no condition on the labels of the faces above `K`. -/
theorem hasLowLayersOn_lt : HasLowLayersOn.{u} fun _ K k _ _ _ _ _ ↦ K < k := by
  intro α K k t' tb p o r hα hF hKk
  have hK0 := hF.grade_pos
  obtain ⟨g, rfl⟩ : ∃ g, K = g + 1 := ⟨K - 1, by omega⟩
  obtain ⟨J, rfl⟩ : ∃ J, k = g + J + 2 := ⟨k - (g + 2), by omega⟩
  exact ProfileTower.readsActualOn_pTower
    (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
    hα.isSuccPrelimit hF.isSourceGapContextAt hF.topGrade_donor

/-- **LOW displays on the LOW families with `K < k`.** -/
theorem hasLowDisplaysOn_lt : HasLowDisplaysOn.{u} fun _ K k _ _ _ _ _ ↦ K < k :=
  hasLowLayersOn_lt.hasLowDisplaysOn

/-- **LOW displays for every LOW family**: `K < k` through the padded tower
(`StageType.hasLowDisplaysOn_lt`), `K ≥ k` by `StageType.hasLowDisplaysOn_ge`. -/
theorem hasLowDisplays_of_padded : HasLowDisplays.{u} := by
  intro α K k t' tb p o r hα hF
  rcases lt_or_ge K k with hlt | hge
  · exact hasLowDisplaysOn_lt t' tb p o r hα hF hlt
  · exact hasLowDisplaysOn_ge t' tb p o r hα hF hge

end VaughtConjecture.StageType

namespace VaughtConjecture.MainTheorem

open FirstOrder Language baseLanguage Realization StageType Expansion

/-- **The thin `ℵ₁` spectrum with (R2) from the padded tower**
(`StageType.hasLowDisplays_of_padded`): conditional on (R4) for receiving models (`hR4`) and (R3)
for receiving models (`hhol`); neither is proved here. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_padded
    (hR4 : ReceivingStableCappedReceiving.{0})
    (hhol : HollowReceiving.{0, 0} IsReceivingCoverHollowAtBlock) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_lowDisplays hR4 hasLowDisplays_of_padded hhol

end VaughtConjecture.MainTheorem
