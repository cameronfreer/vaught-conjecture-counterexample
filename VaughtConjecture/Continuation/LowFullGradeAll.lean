/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowFullGradeDisplay
import VaughtConjecture.Continuation.LowStepLowRoute

/-!
# LOW displays at the full grade, for every donor

Roadmap, Layer 3 ((R2), the LOW construction at the grade `K = k + 1`).

The tie case of the LOW step holds at every LOW family (`StageType.IsLowFamily.lowStepTie`: the
tops of the donor raised through a cell labelled `⊤` at their largest grade), so the LOW layer at
the grade `k + 1` needs no donor top of that grade:

* `ProfileTower.Lvl.Good.cappedLift_lowS_seed_top'`: the capped lift from either coatom into the
  LOW layer at the grade `m + 1` for the seed's designations, for every donor;
* `ProfileTower.Lvl.Good.lowNext_top'`: that layer is a good level;
* `StageType.LowFullGradeAllClass` (`K = k + 1`, no other condition),
  `StageType.hasLowLayersOn_fullGradeAll`, `StageType.hasLowDisplaysOn_fullGradeAll`: (R2) for
  every LOW family whose owner has full grade.

## References

The LOW layer is the step of [AFK26] at the owner's grade; the display is that of [Kni26, §4.3].
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The capped lift from either coatom into the LOW layer at the grade `m + 1`, for the LOW
designations of the seed, for every donor** (`ProfileTower.Lvl.Good.cappedLift_lowS_of_tie_top`
with the tie case of every LOW family, `StageType.IsLowFamily.lowStepTie`). -/
theorem Lvl.Good.cappedLift_lowS_seed_top' {L : Lvl I m} (hL : L.Good)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS (lowCat I (m + 1) (lowN I (m + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).rows.CappedLift
      (X := (univ.erase x, m + 1)) (Y := ((univ : Finset (Fin (m + 2))), m + 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  refine hL.cappedLift_lowS_of_tie_top hs htb
    (StageType.IsLowFamily.lowStepTie (hF := ⟨I.isLegal_left, I.isLegal_right,
      I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    exact ⟨_, rfl, faceCell_right_mem_below (mem_filter.mp ht).2.2⟩
  · rintro f ⟨t, ht, rfl⟩
    exact ⟨_, rfl, faceCell_right_mem_below (StageType.topGrade_le_iff.mp htb t ht)⟩
  · intro i hi hl hit
    obtain ⟨y, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_left hl
    rw [StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right
      I.restrictFace_face_left I.restrictFace_face_right y]
    refine mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · rw [StageType.label_faceCell, ← StageType.label_faceCell I.restrictFace_face_left y]
      exact hit
    · rw [StageType.grade_faceCell, ← StageType.grade_faceCell I.restrictFace_face_left y]
      exact hi
  · exact fun f hf ↦ hf
  · exact fun t ht ↦ ⟨t, ht, rfl⟩
  · exact fun t ht htK ↦ mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, ht, htK⟩, rfl⟩

/-- **The LOW layer at the grade `m + 1` is a good level, for every donor**
(`ProfileTower.Lvl.Good.catNext_succ`, `ProfileTower.Lvl.Good.cappedLift_lowS_seed_top'`). -/
theorem Lvl.Good.lowNext_top' {L : Lvl I m} (hL : L.Good) {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (m + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ m + 1) :
    (L.catNext (lowPred (m + 1) (lowN I (m + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).Good :=
  hL.catNext_succ le_rfl lowPred_withCut_bot fun _ hx ↦ hL.cappedLift_lowS_seed_top' hs htb hx

end VaughtConjecture.ProfileTower

namespace VaughtConjecture.StageType

open Finset

variable (α : Ordinal.{u}) in
/-- **The class of the full grade, for every donor**: the LOW families with `K = k + 1`. -/
def LowFullGradeAllClass (K k : ℕ) (t' _ : StageType.{u} α (k + 1)) (_ : StageType.{u} α k)
    (_ _ : Fin t'.card) : Prop :=
  K = k + 1

/-- **LOW layers on the class of the full grade, for every donor**
(`ProfileTower.exists_isLowLayer_top` over the good level at the grade `k`, its LOW layer good by
`ProfileTower.Lvl.Good.lowNext_top'`). -/
theorem hasLowLayersOn_fullGradeAll : HasLowLayersOn.{u} LowFullGradeAllClass := by
  intro α K k t' tb p o r hα hF hKk
  subst hKk
  exact ProfileTower.exists_isLowLayer_top
    (I := Seed.ofCoatoms hF.isLegal_private hF.isLegal_donor hF.face_private hF.face_donor)
    hα.isSuccPrelimit (ProfileTower.lvlZero_good k le_rfl) hF.isSourceGapContextAt
    hF.topGrade_donor ((ProfileTower.lvlZero_good k le_rfl).lowNext_top' hF.isSourceGapContextAt
      hF.topGrade_donor)

/-- **LOW displays on the class of the full grade, for every donor**: (R2) for every LOW family
whose owner has full grade. -/
theorem hasLowDisplaysOn_fullGradeAll : HasLowDisplaysOn.{u} LowFullGradeAllClass :=
  hasLowLayersOn_fullGradeAll.hasLowDisplaysOn

end VaughtConjecture.StageType
