/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CompletionBelowFullGrade

/-!
# Examples: the seed of two one-point types, and its completion

Roadmap, Layer 3 (the coatom extension construction, from a seed through its completion below the
full grade and the addition of the apex), checkpoint 2.1.

`point` is the legal stage type on one point carried by the one-point scheme `Scheme.onePoint` (a
single cell of grade `1`, mute rows) with the bottom label; it is a copy of the private `point`
of `VaughtConjecture.Extension.Examples`.  The amalgam of `point` with itself over the empty face
has two cells, of scopes `{0}` and `{1}` and grade `1`, and mute rows; it is a seed
(`Seed.ofCoatoms`).  Appending one cell of full scope `{0, 1}` and grade `1`, with mute row and
bottom label, gives a completion below the full grade by hand: its rows are mute, hence consistent
and bountiful, and its only graded faces of grade `1` are `({0}, 1)`, `({1}, 1)`, and
`({0, 1}, 1)`.  At the stage `0`, which is zero, its completion (truncation to the stage, then
adding the apex) is a legal stage type on two points whose faces along the two coatoms are literally
`point`, with an apex of graded index `({0, 1}, 2)` labelled with the formal top.
-/

namespace VaughtConjecture

open Finset

/-- The one-point stage type at stage `0`: the one-point scheme with the bottom label. -/
private noncomputable abbrev point : StageType.{0} 0 1 :=
  Scheme.isLegal_onePoint.toStageType 0

/-- The one-point stage type is legal. -/
private theorem isLegal_point : point.IsLegal :=
  Scheme.isLegal_onePoint.isLegal_toStageType 0

/-- The face of `point` on no points. -/
private theorem restrictFace_point :
    ∃ p, StageType.restrictFace (Coatom.face 0) point = some p :=
  Option.isSome_iff_exists.mp (point.isSome_restrictFace_of_zero _)

/-- The seed of `point` with itself over the empty face: their amalgam. -/
private noncomputable def seed : Seed.{0} 0 0 :=
  Seed.ofCoatoms isLegal_point isLegal_point restrictFace_point.choose_spec
    restrictFace_point.choose_spec

/-- The rows of the amalgamated cell scheme of `point` with itself are mute, row by row. -/
private theorem amalgamRows_row_eq_bot :
    ∀ (x : Coatom.AmalgamCell (Coatom.comap_eq_of_restrictFace restrictFace_point.choose_spec
      restrictFace_point.choose_spec)) y,
      (Coatom.amalgamRows (Coatom.comap_eq_of_restrictFace restrictFace_point.choose_spec
        restrictFace_point.choose_spec)).row x y = ⊥ := by
  rintro (i | ⟨j, hj⟩) y <;> rfl

/-- The rows of the amalgam of `point` with itself are mute. -/
private theorem rows_seed : seed.amalgam.rows = CellScheme.Rows.mute _ := by
  ext s t
  exact amalgamRows_row_eq_bot _ _

/-- The labels of the amalgam of `point` with itself are bottom. -/
private theorem label_seed : seed.amalgam.label = fun _ ↦ ⊥ := by
  have h := seed.amalgam.isLawful
  rw [rows_seed] at h
  exact CellScheme.Rows.isLawful_mute_iff.mp h

/-- The amalgam with one cell of full scope and grade `1`, with mute row. -/
private noncomputable abbrev completedScheme : Scheme.{0} 2 :=
  seed.amalgam.toScheme.appendFullCell 1 (fun _ ↦ ⊥) (seed.not_univ_le 1)

/-- The rows of the completed scheme are mute. -/
private theorem rows_completedScheme : completedScheme.rows = CellScheme.Rows.mute _ := by
  ext s t
  induction s using Fin.lastCases with
  | last => exact Scheme.appendFullCell_row_last t
  | cast s =>
    refine (dite_eq_right (Fin.castSucc_ne_last s)).trans ?_
    rw [rows_seed]
    rfl

/-- The amalgam with one cell of full scope is legal below the full grade `2`. -/
private theorem isLegalBelowFullGrade_completedScheme : completedScheme.IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_appendFullCell seed.amalgam.isWellFormed one_pos
    (by omega)
  isCoded := Scheme.isCoded_appendFullCell seed.amalgam.isCoded fun _ ↦ WithBot.bot_lt_coe _
  isConsistent := by
    rw [rows_completedScheme]
    exact CellScheme.Rows.isConsistent_mute
  isBountiful := by
    rw [rows_completedScheme]
    exact CellScheme.Rows.isBountiful_mute
  grade_lt d := by
    induction d using Fin.lastCases with
    | last => exact (Scheme.appendFullCellScheme_grade_last _ _).trans_lt one_lt_two
    | cast d => exact (Scheme.appendFullCellScheme_grade_castSucc _ _ d).trans_lt (seed.grade_lt d)
  exists_gradedIndex_eq X hX hX2 := by
    by_cases hXu : X.1 = univ
    · refine ⟨Fin.last _, (Scheme.appendFullCellScheme_gradedIndex_last _ _).trans
        (Prod.ext hXu.symm ?_)⟩
      have := hX.2.1
      omega
    · obtain ⟨d, hd⟩ := seed.exists_gradedIndex_eq X hX hXu
      exact ⟨d.castSucc, (Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ d).trans hd⟩

/-- **The completion below the full grade of the seed of `point` with itself**, by hand. -/
private noncomputable def completionBelow : CompletionBelowFullGrade seed where
  scheme := completedScheme
  embed := Fin.castSuccOrderEmb
  isLowerEmbedding := Scheme.isLowerEmbedding_castSucc 1 _ _
  scope_embed := Scheme.appendFullCellScheme_scope_castSucc _ _
  comap_rows := Scheme.comap_rows_castSucc
  mem_range_embed z hz := by
    induction z using Fin.lastCases with
    | last => exact absurd (Scheme.appendFullCellScheme_scope_last _ _) hz
    | cast z => exact ⟨z, rfl⟩
  faces_eq := rfl
  isLegalBelowFullGrade := isLegalBelowFullGrade_completedScheme
  label _ := ⊥
  isLawful := by
    rw [rows_completedScheme]
    exact CellScheme.Rows.isLawful_bot
  label_embed d := (congrFun label_seed d).symm

/-- The completion of the seed at the stage `0`: a legal stage type on two points whose faces along
the two coatoms are literally `point`, with an apex of full scope and full grade labelled with the
largest label. -/
example : ∃ t : StageType.{0} 0 2, t.IsLegal ∧
    StageType.restrictFace Fin.castSuccEmb t = some point ∧
    StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some point ∧
    ∃ d, t.toCellScheme.gradedIndex d = (univ, 2) ∧ ∀ e, t.label e ≤ t.label d :=
  completionBelow.exists_coatomExtension Ordinal.isSuccPrelimit_zero

/-- The same conclusion without truncation: the labels of the completion below the full grade are
bottom, hence already at the stage `0`. -/
example : ∃ t : StageType.{0} 0 2, t.IsLegal ∧
    StageType.restrictFace Fin.castSuccEmb t = some point ∧
    StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some point ∧
    ∃ d, t.toCellScheme.gradedIndex d = (univ, 2) ∧ ∀ e, t.label e ≤ t.label d :=
  completionBelow.exists_coatomExtension_of_atStage fun _ ↦ Label.atStage_bot

end VaughtConjecture
