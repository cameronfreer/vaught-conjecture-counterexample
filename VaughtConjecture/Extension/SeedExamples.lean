/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CoatomExtensionOfSeed

/-!
# Examples: a seed of the amalgam of two one-point types

Roadmap, Layer 3 (the coatom extension construction, from a seed through the apex layer).

`point` is the legal stage type on one point carried by the one-point scheme `Scheme.onePoint` (a
single cell of grade `1`, mute rows) with the bottom label; it is a copy of the private `point`
of `VaughtConjecture.Extension.Examples`.  The amalgam of `point` with itself over the empty face
has two cells, of scopes `{0}` and `{1}` and grade `1`, and mute rows.  Appending one cell of full
scope `{0, 1}` and grade `1`, with mute row and bottom label, gives a seed by hand: its rows are
mute, hence consistent and bountiful, and its only graded faces of grade `1` are `({0}, 1)`,
`({1}, 1)`, and `({0, 1}, 1)`.  Its completion is a legal stage type on two points whose faces
along the two coatoms are literally `point`, with an apex of graded index `({0, 1}, 2)` labelled
with the formal top.
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

/-- The completion input of the amalgam of `point` with itself over the empty face. -/
private noncomputable def input : CompletionInput.{0} 0 0 :=
  CompletionInput.ofCoatoms isLegal_point isLegal_point restrictFace_point.choose_spec
    restrictFace_point.choose_spec

/-- The rows of the amalgam of `point` with itself are mute. -/
private theorem amalgamRows_row_eq_bot :
    ∀ (x : Coatom.AmalgamCell (Coatom.comap_eq_of_restrictFace restrictFace_point.choose_spec
      restrictFace_point.choose_spec)) y,
      (Coatom.amalgamRows (Coatom.comap_eq_of_restrictFace restrictFace_point.choose_spec
        restrictFace_point.choose_spec)).row x y = ⊥ := by
  rintro (i | ⟨j, hj⟩) y <;> rfl

/-- The rows of the amalgam of `point` with itself are mute. -/
private theorem rows_input : input.amalgam.rows = CellScheme.Rows.mute _ := by
  ext s t
  exact amalgamRows_row_eq_bot _ _

/-- The labels of the amalgam of `point` with itself are bottom. -/
private theorem label_input : input.amalgam.label = fun _ ↦ ⊥ := by
  have h := input.amalgam.isLawful
  rw [rows_input] at h
  exact CellScheme.Rows.isLawful_mute_iff.mp h

/-- The amalgam with one cell of full scope and grade `1`, with mute row. -/
private noncomputable abbrev seedScheme : Scheme.{0} 2 :=
  input.amalgam.toScheme.appendFullCell 1 (fun _ ↦ ⊥) (input.not_univ_le 1)

/-- The rows of the seed are mute. -/
private theorem rows_seedScheme : seedScheme.rows = CellScheme.Rows.mute _ := by
  ext s t
  induction s using Fin.lastCases with
  | last => exact Scheme.appendFullCell_row_last t
  | cast s =>
    refine (dite_eq_right (Fin.castSucc_ne_last s)).trans ?_
    rw [rows_input]
    rfl

/-- **A seed of the amalgam of `point` with itself**, by hand. -/
private noncomputable def seed : input.Seed where
  scheme := seedScheme
  embed := Fin.castSuccOrderEmb
  isLowerEmbedding := Scheme.isLowerEmbedding_castSucc 1 _ _
  scope_embed := Scheme.appendFullCellScheme_scope_castSucc _ _
  comap_rows := Scheme.comap_rows_castSucc
  mem_range_embed z hz := by
    induction z using Fin.lastCases with
    | last => exact absurd (Scheme.appendFullCellScheme_scope_last _ _) hz
    | cast z => exact ⟨z, rfl⟩
  faces_eq := rfl
  grade_le d := by
    induction d using Fin.lastCases with
    | last => exact (Scheme.appendFullCellScheme_grade_last _ _).le
    | cast d => exact (Scheme.appendFullCellScheme_grade_castSucc _ _ d).trans_le (input.grade_le d)
  isWellFormed := Scheme.isWellFormed_appendFullCell input.amalgam.isWellFormed one_pos
    (by omega)
  isCoded := Scheme.isCoded_appendFullCell input.amalgam.isCoded fun _ ↦ WithBot.bot_lt_coe _
  isConsistent := by
    rw [rows_seedScheme]
    exact CellScheme.Rows.isConsistent_mute
  isBountiful := by
    rw [rows_seedScheme]
    exact CellScheme.Rows.isBountiful_mute
  isComplete X hX hX1 := by
    by_cases hXu : X.1 = univ
    · refine ⟨Fin.last _, (Scheme.appendFullCellScheme_gradedIndex_last _ _).trans
        (Prod.ext hXu.symm ?_)⟩
      exact le_antisymm hX.2.1 hX1
    · obtain ⟨d, hd⟩ := input.exists_gradedIndex_eq X hX hXu
      exact ⟨d.castSucc, (Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ d).trans hd⟩
  label _ := ⊥
  isLawful := by
    rw [rows_seedScheme]
    exact CellScheme.Rows.isLawful_bot
  atStage _ := Label.atStage_bot
  label_embed d := (congrFun label_input d).symm

/-- The completion of the seed: a legal stage type on two points whose faces along the two coatoms
are literally `point`, with an apex of full scope and full grade labelled with the largest
label. -/
example : ∃ t : StageType.{0} 0 2, t.IsLegal ∧
    StageType.restrictFace Fin.castSuccEmb t = some point ∧
    StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some point ∧
    ∃ d, t.toCellScheme.gradedIndex d = (univ, 2) ∧ ∀ e, t.label e ≤ t.label d :=
  seed.exists_coatomExtension

end VaughtConjecture
