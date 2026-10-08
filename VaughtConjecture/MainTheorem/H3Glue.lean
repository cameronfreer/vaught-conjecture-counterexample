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

namespace Scheme

/-- **The bottom label at an appended cell**: a lawful labelling of a scheme whose grades are below
`j`, extended by `⊥` at a cell of full scope and grade `j`, is lawful. -/
theorem isLawful_appendFullCell_bot {n j : ℕ} {S : Scheme.{u} n}
    {row : Fin (S.card + 1) → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}
    (hS : ∀ d, S.toCellScheme.grade d < j) {r : Fin S.card → Label.{u}}
    (hr : S.rows.IsLawful r) :
    (S.appendFullCell j row h).rows.IsLawful
      (Fin.lastCases (motive := fun _ ↦ Label.{u}) ⊥ r) := by
  refine isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (hS d).ne
  · have e : (Fin.lastCases (motive := fun _ ↦ Label.{u}) ⊥ r) ∘ Fin.castSucc = r :=
      funext fun d ↦ Fin.lastCases_castSucc _
    rw [e]
    exact hr
  · rw [Fin.lastCases_last]
    exact isSelfVisible_bot _
  · refine ⟨fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, fun d ↦ ?_⟩
    simp

end Scheme

namespace StageType

variable {α : Ordinal.{u}}

/-- **A labelling lawful on a face, read on the cells of the face, is lawful below the graded
face.** -/
theorem isLawfulBelow_of_faceCell {n m : ℕ} {D : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {t : StageType.{u} α m} (h : restrictFace f D = some t) {x : Fin D.card → Label.{u}}
    (hx : t.rows.IsLawful fun i ↦ x (faceCell h i)) :
    D.rows.IsLawfulBelow ((univ : Finset (Fin m)).map f, m) fun z ↦ x z := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  exact (Scheme.isLawfulBelow_comap_cellMap_iff (S := D.toScheme) f
    ((univ : Finset (Fin m)), m) x).mp (hx.isLawfulBelow _)

/-- **Gluing over a pinned extension**: `Q` is a one-point extension of `P` whose face along
`extendByLast f` is `d`, over the common face `p`.  Every lawful labelling of `P` and every lawful
labelling of `d` agreeing on `p` are the readings on the two faces of one lawful labelling of
`Q`. -/
def GluesAt {k m' : ℕ} {Q : StageType.{u} α (k + 1)} {P : StageType.{u} α k}
    {f : Fin m' ↪ Fin k} {p : StageType.{u} α m'} {d : StageType.{u} α (m' + 1)}
    (h₁ : restrictFace Fin.castSuccEmb Q = some P) (h₂ : restrictFace (extendByLast f) Q = some d)
    (hPf : restrictFace f P = some p) (hdp : restrictFace Fin.castSuccEmb d = some p) : Prop :=
  ∀ wP : Fin P.card → Label.{u}, P.rows.IsLawful wP → ∀ wd : Fin d.card → Label.{u},
    d.rows.IsLawful wd → (∀ i, wP (faceCell hPf i) = wd (faceCell hdp i)) →
    ∃ w : Fin Q.card → Label.{u}, Q.rows.IsLawful w ∧ (∀ x, w (faceCell h₁ x) = wP x) ∧
      ∀ y, w (faceCell h₂ y) = wd y

/-- **The coatom extension with gluing**: at a stage that is zero or a limit, two legal stage types
on `m + 1` points with the same face along the first `m` points are the faces of one legal stage
type on `m + 2` points, over which their lawful labellings agreeing on the common face glue: the
completion of the seed that extends the cut (`Seed.exists_extendsCut`), with the apex at `⊥`. -/
theorem exists_gluingCoatomExtension (hα : Order.IsSuccPrelimit α) {m : ℕ}
    {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m} (hla : ta.IsLegal)
    (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
    (hpb : restrictFace Fin.castSuccEmb tb = some p) :
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧
      ∃ (h₁ : restrictFace Fin.castSuccEmb t = some ta)
        (h₂ : restrictFace (extendByLast Fin.castSuccEmb) t = some tb), GluesAt h₁ h₂ hpa hpb := by
  classical
  set I := Seed.ofCoatoms hla hlb hpa hpb
  obtain ⟨F, hF⟩ := I.exists_extendsCut
  have h₁ : restrictFace Fin.castSuccEmb (F.completion hα) = some ta :=
    F.restrictFace_left_completion hα
  have h₂ : restrictFace (extendByLast Fin.castSuccEmb) (F.completion hα) = some tb :=
    F.restrictFace_right_completion hα
  refine ⟨F.completion hα, F.isLegal_completion hα, h₁, h₂, ?_⟩
  intro wa hwa wb hwb hagree
  have hL : restrictFace (Coatom.left m) I.amalgam = some ta := I.restrictFace_left
  have hR : restrictFace (Coatom.right m) I.amalgam = some tb := I.restrictFace_right
  set W : Prof I := fun e ↦ if hz : ∃ x, faceCell hL x = e then wa hz.choose else
    faceExtend hR wb e with hWdef
  have hWL (x : Fin ta.card) : W (faceCell hL x) = wa x := by
    rw [hWdef]
    dsimp only
    split_ifs with hz
    · exact congrArg wa (I.amalgam.toScheme.faceCell_injective
        (comap_toScheme_of_restrictFace hL) hz.choose_spec)
    · exact absurd ⟨x, rfl⟩ hz
  have hWR (y : Fin tb.card) : W (faceCell hR y) = wb y := by
    by_cases hz : ∃ x, faceCell hL x = faceCell hR y
    · obtain ⟨x, hx⟩ := hz
      rw [← hx, hWL]
      have hlast : Fin.last m ∉ tb.toCellScheme.scope y := by
        intro hm
        have hmem : Fin.last (m + 1) ∈ I.amalgam.toCellScheme.scope (faceCell hR y) := by
          rw [scope_faceCell]
          exact mem_map.mpr ⟨Fin.last m, hm, by simp [Coatom.right]⟩
        rw [← hx, scope_faceCell] at hmem
        obtain ⟨z, -, hz⟩ := mem_map.mp hmem
        exact Fin.castSucc_ne_last z hz
      obtain ⟨i, rfl⟩ := exists_faceCell_eq_of_last_notMem hpb hlast
      have hxi : x = faceCell hpa i := by
        refine I.amalgam.toScheme.faceCell_injective (comap_toScheme_of_restrictFace hL) ?_
        exact hx.trans (faceCell_faceCell (h := Fin.castSuccEmb) hL hR hpa hpb i).symm
      rw [hxi]
      exact hagree i
    · rw [hWdef]
      dsimp only
      rw [dite_eq_right hz]
      exact faceExtend_faceCell hR wb y
  have hWC : I.amalgam.rows.IsLawfulBelow (coatC, m + 1) fun e ↦ W e := by
    have h := isLawfulBelow_of_faceCell hL (x := W) (by simpa only [hWL] using hwa)
    rwa [Coatom.univ_map_left] at h
  have hWD : I.amalgam.rows.IsLawfulBelow (coatD, m + 1) fun e ↦ W e := by
    have h := isLawfulBelow_of_faceCell hR (x := W) (by simpa only [hWR] using hwb)
    rwa [Coatom.univ_map_right] at h
  obtain ⟨r, hr, hrW⟩ := hF W ⟨hWC, hWD⟩
  have hwlaw := Scheme.isLawful_appendFullCell_bot (S := (F.truncate hα).toScheme)
    (row := StageType.apexRow (t := F.truncate hα) F.isLegalBelowFullGrade)
    (h := F.isLegalBelowFullGrade.not_le) (fun d ↦ F.isLegalBelowFullGrade.grade_lt d) hr
  set w : Fin ((F.truncate hα).card + 1) → Label.{u} :=
    Fin.lastCases (motive := fun _ ↦ Label.{u}) ⊥ r with hw
  have hwcast (z : Fin F.scheme.card) : w (Fin.castSucc z) = r z := Fin.lastCases_castSucc _
  refine ⟨w, hwlaw, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [F.faceCell_completion hα Coatom.univ_map_left_ne h₁ hL x]
    exact (hwcast _).trans ((hrW _).trans (hWL x))
  · rw [F.faceCell_completion hα Coatom.univ_map_right_ne h₂ hR y]
    exact (hwcast _).trans ((hrW _).trans (hWR y))

end StageType

end VaughtConjecture
