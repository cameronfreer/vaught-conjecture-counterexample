/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Raise
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Extension.TwoFaceLift

/-!
# Completions that extend every labelling of the cut (work file for `h3`)

Work file (placement later), for the input (S2) of `VaughtConjecture.MainTheorem.H3Class`.
Compiled in this repository (theorem named):

* **Extension of the cut** (`CompletionBelowFullGrade.ExtendsCut`, `Seed.exists_extendsCut`):
  every seed has a completion below the full grade through which every profile lawful on the cut
  at the grade `m + 1` extends to a lawful labelling, unchanged at the old cells.  At `m ≤ 2` the
  completion of the tower (`Seed.exists_isLawfulBelow_tower`); at `m ≥ 3` the levels of
  rank-normalized profiles with the top field layer
  (`ProfileTower.Lvl.Good.extendsFromBoundary_bot_top`).
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- A completion **extends the cut**: every profile lawful on the cut at the grade `m + 1` extends
to a lawful labelling of the completed scheme, unchanged at the old cells. -/
def ExtendsCut (F : CompletionBelowFullGrade I) : Prop :=
  ∀ W : Prof I, IsCutLawful I (m + 1) W →
    ∃ r : Fin F.scheme.card → Label.{u}, F.scheme.rows.IsLawful r ∧ ∀ e, r (F.embed e) = W e

end CompletionBelowFullGrade

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {N : Lvl I m}

/-- **The completion over a good level extends the cut** (the argument of
`ProfileTower.Lvl.Good.exists_isLawful_top`, for any profile lawful on the cut). -/
theorem Lvl.Good.extendsCut_completion (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m) :
    (hN.completion hB hm).ExtendsCut := by
  classical
  intro W hW
  set w : Fin N.top.card → Label.{u} := Function.extend N.topEmbed W fun _ ↦ ⊥ with hw
  have hwe (d : Fin I.amalgam.card) : w (N.topEmbed d) = W d :=
    N.topEmbed.injective.extend_apply _ _ d
  have hlaw (z : Fin (m + 2)) (hz : z ∈ (Pts : Finset (Fin (m + 2)))) :
      N.top.rows.IsLawfulBelow (univ.erase z, m + 1) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff (S := N.S) (k := m + 1)
      (r := fun i ↦ N.S.fieldRow (m + 1) (N.S.catalogueEntry (m + 1) i))
      (h := N.not_le) (v := w)
      (fun h' ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h'.1))).mpr ?_
    refine (hN.isLawfulBelow_old_iff (w := fun e ↦ w (Fin.castAdd _ e))
      (Seed.ne_univ_erase z)).mpr ?_
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase z, m + 1))
      (w := W) (w' := fun d ↦ w (Fin.castAdd _ (N.embed d)))
      fun d _ ↦ (hwe d).symm).mp (hW.erase hz)
  obtain ⟨r, hr, hrw, -⟩ := hN.extendsFromBoundary_bot_top hB (x := Fin.last (m + 1))
    (y := Fin.castSucc (Fin.last m)) (by simp) (by simp) Seed.last_ne_castSucc w
    (hlaw _ (by simp)) (hlaw _ (by simp)) fun _ _ ↦ by simp
  have hall (z : Fin N.top.card) : z ∈ N.top.toCellScheme.below (univ, m + 1) :=
    ⟨subset_univ _, by
      have := hN.grade_top_lt z
      change N.top.toCellScheme.grade z ≤ m + 1
      omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_⟩
  change r ⟨N.topEmbed d, hall _⟩ = W d
  rw [← hwe d]
  refine hrw ⟨N.topEmbed d, hall _⟩ ?_
  rcases I.scope_subset_or (x := Fin.last (m + 1)) (y := Fin.castSucc (Fin.last m)) (by simp)
    (by simp) Seed.last_ne_castSucc d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, hN.gradedIndex_topEmbed]
    exact ⟨h, by have := (hall (N.topEmbed d)).2; rwa [hN.gradedIndex_topEmbed] at this⟩
  · refine .inr ?_
    rw [CellScheme.mem_below, hN.gradedIndex_topEmbed]
    exact ⟨h, by have := (hall (N.topEmbed d)).2; rwa [hN.gradedIndex_topEmbed] at this⟩

end ProfileTower

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- **The completion of the tower extends the cut** (`Seed.exists_isLawfulBelow_tower`). -/
theorem extendsCut_tower (hinv : I.TowerInvariant (m + 1)) :
    (I.completionBelowFullGradeOfTowerInvariant hinv).ExtendsCut := by
  intro W hW
  obtain ⟨r, hr, hrw⟩ := I.exists_isLawfulBelow_tower
    (fun d ↦ I.scope_subset_or (x := Fin.last (m + 1)) (y := Fin.castSucc (Fin.last m))
      (by simp) (by simp) Seed.last_ne_castSucc d) (m + 1) hW.1 hW.2
  have hall (z : Fin (I.tower (m + 1)).card) :
      z ∈ (I.tower (m + 1)).toCellScheme.below (univ, m + 1) :=
    ⟨subset_univ _, by
      have := I.grade_tower_lt le_rfl z
      change (I.tower (m + 1)).toCellScheme.grade z ≤ m + 1
      omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_⟩
  exact hrw d (by have := I.grade_lt d; omega)

/-- **Every seed has a completion below the full grade that extends the cut.** -/
theorem exists_extendsCut : ∃ F : CompletionBelowFullGrade I, F.ExtendsCut := by
  rcases le_or_gt m 2 with hm | hm
  · exact ⟨_, I.extendsCut_tower (I.towerInvariant_of_twoFaceLift
      (I.forall_twoFaceLift_of_two_le fun j hj hjm ↦ absurd hjm (by omega)) (m + 1) le_rfl)⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    have hL := lvl_good (I := I) (by omega) j (by omega)
    exact ⟨_, (hL.next (by omega)).extendsCut_completion hL.hasBotExtension_next (by omega)⟩

end Seed

end VaughtConjecture
