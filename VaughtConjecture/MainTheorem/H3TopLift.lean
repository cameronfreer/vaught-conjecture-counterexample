/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Band

/-!
# The top grade of the donor coatom (work file for `h3`)

Work file (branch `research/work-toplift`, placement later).  On the named condition
`CapRequests.DonorTopLiftAt` of the band (module `VaughtConjecture.MainTheorem.H3Band`): the lift
into the donor coatom at the cut grade `K + 1` from the common face at `K + 1` together with the
donor coatom at `K`.

* **At the cut grade `1`** (`CapRequests.donorTopLiftAt_zero`): the donor coatom has no cell of
  grade `0`, so the lift is from the common face alone, the capped lift of the amalgam
  (bountifulness).  Every arity.
* **On three points** (`CapRequests.donorTopLiftAt_three`): at every cut grade `K + 1 ≤ 2` (all the
  cut grades of the band there); at `K = 1` the common face, of one point, has no cell of grade
  `2` (`CapRequests.donorTopLiftAt_of_face`).  No two-coatom lift is needed.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

/-- **The top grade of the donor coatom at the cut grade `1`**: the donor coatom has no cell of
grade `0`, so the lift is from the common face at the grade `1` into the donor coatom, the capped
lift of the amalgam along `P` at the cap `h` (bountifulness). -/
theorem donorTopLiftAt_zero (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) (hm : 1 ≤ m) :
    DonorTopLiftAt r xp xd 0 := by
  classical
  intro h hh _ _ P hP _ f hf hfP _ v _ _ _
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hxp hxd hne.symm
  set X : Finset (Fin (m + 2)) × ℕ := (univ.erase xp ∩ univ.erase xd, 1) with hXdef
  set Y : Finset (Fin (m + 2)) × ℕ := (univ.erase xd, 1) with hYdef
  have hXf : X ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨hOf, one_pos, by simp only [hXdef]; rw [hOcard]; exact hm⟩
  have hYf : Y ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hxd, one_pos, by simp only [hYdef]; rw [Seed.card_erase]; omega⟩
  have hXY : X ≤ Y := ⟨inter_subset_right, le_rfl⟩
  have hXC : X ≤ (univ.erase xp, 0 + 1) := ⟨inter_subset_left, le_rfl⟩
  obtain ⟨q, hq, hqP, hqf⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (I.isBountiful hXf hYf hXY) h hh (fun d ↦ f d) (fun d ↦ P d) (hf.mono (X := X) hXC)
    (hP.erase hxd) fun d ↦ (hfP d.1 (I.amalgam.toCellScheme.below_mono hXC d.2)).symm
  set v' : Prof I := fun d ↦ if hd : d ∈ I.amalgam.toCellScheme.below Y then q ⟨d, hd⟩ else P d
    with hv'def
  have hv'Y (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below Y) :
      v' d = q ⟨d, hd⟩ := dite_eq_left hd
  refine ⟨v', ?_, fun d hd ↦ ?_, fun d hdC hdD ↦ ?_, fun d ↦ ?_⟩
  · convert hq using 1
    exact funext fun d ↦ hv'Y d.1 d.2
  · exact absurd (hd.2.trans_lt' (I.amalgam.isWellFormed.isWellFormed.grade_pos d))
      (lt_irrefl 0)
  · rw [hv'Y d hdD]
    exact hqf ⟨d, ⟨subset_inter hdC.1 hdD.1, hdD.2⟩⟩
  · by_cases hd : d ∈ I.amalgam.toCellScheme.below Y
    · rw [hv'Y d hd]; exact hqP ⟨d, hd⟩
    · exact congrArg (min · h) (dite_eq_right hd)

/-- **The top grade of the donor coatom on three points**, at both cut grades of the band: at the
cut grade `1` by `CapRequests.donorTopLiftAt_zero`, at the cut grade `2` since the common face,
of one point, has no cell of grade `2` (`CapRequests.donorTopLiftAt_of_face`). -/
theorem donorTopLiftAt_three {I : Seed.{u} α 1} {r : CapRequests (Fin I.amalgam.card)}
    {xp xd : Fin 3} (hxp : xp ∈ (Pts : Finset (Fin 3))) (hxd : xd ∈ (Pts : Finset (Fin 3)))
    (hne : xd ≠ xp) {K : ℕ} (hK : K ≤ 1) : DonorTopLiftAt r xp xd K := by
  rcases (show K = 0 ∨ K = 1 by omega) with rfl | rfl
  · exact donorTopLiftAt_zero hxp hxd hne le_rfl
  · refine donorTopLiftAt_of_face hxd one_pos le_rfl fun d hd ↦ ?_
    have hcard := (inter_props (I := I) hxp hxd hne.symm).2
    exact (I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans
      ((card_le_card hd).trans hcard.le)

end CapRequests

end VaughtConjecture
