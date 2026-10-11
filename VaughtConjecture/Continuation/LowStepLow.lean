/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStepTie
import VaughtConjecture.Continuation.LowTowerLevel
import VaughtConjecture.Continuation.H2General

/-!
# The tie case of the LOW step for every donor

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the LOW step from the
private coatom at the tie); semantic contract, items 3, 4 and 8.

The tie case `StageType.LowStepTie` holds for every LOW family; in particular
`StageType.LowStepTieLow` (the donors whose tops all have grades below `K`) holds.

**The donor face for every LOW family, with no tie premise**
(`StageType.IsLowFamily.exists_raised_of_gap`, in `VaughtConjecture.Continuation.LowGapRaise`).
The ambient donor face, with the gap at the cap, is raised at the frontier through a top cell of the
largest grade of a donor top and spliced with itself above that grade (raising below a gap,
`H2.lawfulAt_raise_below`; the raise of the tops, `StageType.exists_raised_tops`); the capped lift
at the frontier from the root of the private face with this ambient is literal on the root, agrees
with the ambient donor face capped at the cap, and reads every donor top off the root at least at
the frontier.  A LOW family bounds the top grade of the donor by `K`; the tie premise is not used.

**The tie case for every LOW family** (`StageType.IsLowFamily.lowStepTie`,
`StageType.IsLowFamily.lowStepTieLow`, compiled in this repository): from the donor face above.

**The capped lift into the LOW layer, and the LOW level, for every donor**
(`ProfileTower.Lvl.Good.cappedLift_lowS_seed'`, `ProfileTower.Lvl.Good.lowNext'`, compiled in this
repository): the statements of `ProfileTower.Lvl.Good.cappedLift_lowS_seed` and
`ProfileTower.Lvl.Good.lowNext` without the donor top of grade `g + 1`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

variable {α : Ordinal.{u}} {k K : ℕ} {t' tb : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
  {o r : Fin t'.card}

/-- **The tie case holds at every LOW family**: `StageType.IsLowFamily.exists_raised_of_gap`,
which does not use the tie premise. -/
theorem IsLowFamily.lowStepTie (hF : IsLowFamily K t' tb p o r) :
    LowStepTie K t' tb hF.face_private hF.face_donor o r :=
  fun _ hb hhc _ _ hR hf hag hc htop hlow _ ↦
    hF.exists_raised_of_gap hb hhc hR hf hag hlow hc htop

/-- **The case of a donor without a top of grade `K` holds** at every LOW family
(`StageType.IsLowFamily.lowStepTie`). -/
theorem IsLowFamily.lowStepTieLow (hF : IsLowFamily K t' tb p o r) :
    LowStepTieLow K t' tb hF.face_private hF.face_donor o r :=
  fun _ ↦ hF.lowStepTie

end VaughtConjecture.StageType

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The capped lift from either coatom into the LOW layer for the seed's designations, for every
donor**: `ProfileTower.Lvl.Good.cappedLift_lowS_seed` without a donor top of grade `g + 1`, by
`ProfileTower.Lvl.Good.cappedLift_lowS_seed_of_low` and `StageType.IsLowFamily.lowStepTieLow`. -/
theorem Lvl.Good.cappedLift_lowS_seed' {g : ℕ} {L : Lvl I g} (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    (L.lowS (lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).rows.CappedLift
      (X := (univ.erase x, g + 1)) (Y := ((univ : Finset (Fin (m + 2))), g + 1))
      ⟨erase_subset _ _, le_rfl⟩ :=
  hL.cappedLift_lowS_seed_of_low hgm hs htb
    (StageType.IsLowFamily.lowStepTieLow (hF := ⟨I.isLegal_left, I.isLegal_right,
      I.restrictFace_face_left, I.restrictFace_face_right, hs, htb⟩)) hx

/-- **The LOW layer over a good level is a good level, for every donor**:
`ProfileTower.Lvl.Good.lowNext` without a donor top of grade `g + 1`, from
`ProfileTower.Lvl.Good.cappedLift_lowS_seed'`. -/
theorem Lvl.Good.lowNext' {g : ℕ} {L : Lvl I g} (hL : L.Good) (hgm : g + 1 ≤ m)
    {o' r' : Fin I.left.card}
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o' r')
    (htb : I.right.topGrade ≤ g + 1) :
    (L.catNext (lowPred (g + 1) (lowN I (g + 1)) (lowT I)
      (StageType.faceCell I.restrictFace_left o')
      (StageType.faceCell I.restrictFace_left r'))).Good :=
  hL.catNext hgm lowPred_withCut_bot fun _ hx ↦ hL.cappedLift_lowS_seed' hgm hs htb hx

end VaughtConjecture.ProfileTower
