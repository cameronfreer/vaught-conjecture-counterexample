/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.BaseLadderTower
import VaughtConjecture.ProcessRank.SpanK2Attachment

/-!
# The grade-one ladder of the attachment of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the attachment `ProcessRank.k2Attachment`
as ladder base data (`ProcessRank.k2AttachmentBase`), its padded grade-one base at the height `8`
over the unrestricted rank members (`ProcessRank.k2Ladder`), and the extension of the labels
`k2Left`, `k2Right` to it (`ProcessRank.k2LadderLabel`, the state extension).

* The rows of the attachment are consistent: the attachment row `attRow` is a lawful section
  (`ProcessRank.isLawful_attRow`, identity witness), since a cell below another copies a test cell
  below the copied one, and the test row increases along the test scheme
  (`ProcessRank.testRow_le_of_mem_below`).
* The ladder is consistent (`Scheme.LadderBaseData.isConsistent_ladderBase`) and the extended
  labels are lawful (`Scheme.LadderBaseData.isLawful_stateExt`); with them the ladder is a stage
  type at the stage `ω ^ 2` (`ProcessRank.k2LadderType`).
* Its faces along the embeddings onto `{0, 1}` and `{2, 3}` are still the test types with `k2Left`
  and `k2Right` (`ProcessRank.exists_restrictFace_k2Ladder_left`,
  `ProcessRank.exists_restrictFace_k2Ladder_right`): the ladder points have full scope.

Open: the controllers of grades two to four, legality and completeness of a master scheme over the
attachment (this ladder has no cells on the mixed faces), and the four-point span of mutual
rigidity of the test pair.  None of these is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- A cell of the attachment below another copies a test cell below the copied one. -/
theorem attCell_mem_below {s d : Fin 8}
    (h : attScope d ⊆ attScope s ∧ attGrade d ≤ attGrade s) :
    testScope (attCell d) ⊆ testScope (attCell s) ∧ testGrade (attCell d) ≤ testGrade (attCell s) :=
  (by decide : ∀ s d : Fin 8, attScope d ⊆ attScope s ∧ attGrade d ≤ attGrade s →
    testScope (attCell d) ⊆ testScope (attCell s) ∧
      testGrade (attCell d) ≤ testGrade (attCell s)) s d h

/-- **The attachment row increases along the attachment.** -/
theorem attRow_le_of_mem_below {s d : Fin 8}
    (h : attScope d ⊆ attScope s ∧ attGrade d ≤ attGrade s) : attRow.{u} d ≤ attRow s :=
  testRow_le_of_mem_below (attCell_mem_below h)

/-- **The attachment row is a lawful section of the attachment**, by the identity witness. -/
theorem isLawful_attRow : k2Attachment.{u}.rows.IsLawful attRow where
  orderly d := by
    have h := isSelfVisible_testRow.{u} (attCell d)
    rwa [(by decide : ∀ d : Fin 8, testGrade (attCell d) = attGrade d) d] at h
  locality s := ⟨fun _ ↦ ⊤, id, IsWitness.id_top, fun d ↦ by
    simp only [id, min_top_right]
    exact min_eq_left (attRow_le_of_mem_below d.2)⟩
  availability s t hst hg := ⟨t, rfl, attRow_le_of_mem_below ⟨hst, hg.le⟩⟩

/-- **The attachment as ladder base data**: no cell of full scope, well formed, consistent rows
(the attachment row is lawful), coded. -/
noncomputable def k2AttachmentBase : Scheme.LadderBaseData.{u} 4 where
  S := k2Attachment
  noFull d := (by decide : ∀ d : Fin 8,
    ¬ ((univ : Finset (Fin 4)), 1) ≤ (attScope d, attGrade d)) d
  wf := isWellFormed_k2Attachment
  cons _ := isLawful_attRow.isLawfulBelow _
  coded := isCoded_k2Attachment

/-- **The grade-one ladder at the height `8`**: the attachment with the ladder points of the
unrestricted rank members at `({0, 1, 2, 3}, 1)`. -/
noncomputable abbrev k2Ladder : Scheme.{u} 4 := k2AttachmentBase.ladderBase 8

/-- **The labels on the ladder**: the state extension of the labels `k2Left`, `k2Right` of the
attachment. -/
noncomputable def k2LadderLabel : Fin k2Ladder.{u}.card → Label.{u} :=
  k2AttachmentBase.stateExt 8 k2AttLabel

/-- **The rows of the ladder are consistent.** -/
theorem isConsistent_k2Ladder : k2Ladder.{u}.rows.IsConsistent :=
  k2AttachmentBase.isConsistent_ladderBase (H := 8) (by decide)

/-- **The extended labels are lawful on the ladder.** -/
theorem isLawful_k2LadderLabel : k2Ladder.{u}.rows.IsLawful k2LadderLabel :=
  Scheme.LadderBaseData.isLawful_stateExt (B := k2AttachmentBase) isLawful_k2AttLabel (by decide)
    le_rfl

/-- The extended labels on the attachment cells are the labels of the attachment. -/
theorem k2LadderLabel_castAdd (d : Fin k2Attachment.{u}.card) :
    k2LadderLabel (Fin.castAdd _ d) = k2AttLabel d :=
  Scheme.LadderBaseData.stateExt_castAdd (B := k2AttachmentBase) isLawful_k2AttLabel le_rfl d

/-- The extended labels are `⊥`, `1`, or labels of the attachment. -/
theorem k2LadderLabel_cases (t : Fin k2Ladder.{u}.card) :
    k2LadderLabel t = ⊥ ∨ k2LadderLabel t = 1 ∨ ∃ e, k2LadderLabel t = k2AttLabel e := by
  unfold k2LadderLabel
  rw [Scheme.LadderBaseData.stateExt_of_isLawful (B := k2AttachmentBase) (H := 8)
    isLawful_k2AttLabel (by decide)]
  induction t using Fin.addCases with
  | left d => exact .inr (.inr ⟨d, Fin.append_left _ _ d⟩)
  | right j =>
    erw [Fin.append_right]
    exact Label.posTable_eq _

/-- **The ladder as a stage type** at the stage `ω ^ 2`, with the extended labels. -/
noncomputable def k2LadderType : StageType.{u} (ω ^ 2) 4 where
  toScheme := k2Ladder
  label := k2LadderLabel
  isWellFormed := k2AttachmentBase.isWellFormed_ladderBase (H := 8) (by decide)
  isCoded := k2AttachmentBase.isCoded_ladderBase 8
  isLawful := isLawful_k2LadderLabel
  atStage t := by
    rcases k2LadderLabel_cases t with h | h | ⟨e, h⟩ <;> rw [h]
    · exact atStage_bot
    · simp
    · exact k2AttachmentType.atStage e

/-- **The faces of the ladder type along a pure embedding are those of the attachment type**:
the ladder points have full scope, so no ladder point is visible through an embedding missing a
point. -/
theorem restrictFace_k2LadderType {f : Fin 2 ↪ Fin 4} (hf : ∃ x, x ∉ Set.range f) :
    StageType.restrictFace f k2LadderType.{u} = StageType.restrictFace f k2AttachmentType.{u} := by
  refine StageType.restrictFace_eq_of_strictMono (s := k2AttachmentType) (t := k2LadderType)
    (φ := Fin.castAdd _) f (Fin.strictMono_castAdd _)
    (Scheme.isLowerEmbedding_castAdd (S := k2Attachment) 1 _ _ k2AttachmentBase.noFull)
    (fun d ↦ Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d)
    (Scheme.comap_rows_castAdd (h := k2AttachmentBase.noFull)) rfl rfl
    (fun d ↦ k2LadderLabel_castAdd d) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := hf
  induction z using Fin.addCases with
  | left d => exact ⟨d, rfl⟩
  | right j =>
    exfalso
    have hs : k2LadderType.{u}.toCellScheme.scope (Fin.natAdd _ j) = univ :=
      Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j
    rw [hs, coe_univ] at hz
    exact hx (hz (Set.mem_univ x))

/-- **The face of the ladder type on `{0, 1}` is the test type with `k2Left`.** -/
theorem exists_restrictFace_k2Ladder_left :
    ∃ p, StageType.restrictFace leftEmb k2LadderType.{u} = some p ∧ IsTestType p k2Left := by
  rw [restrictFace_k2LadderType ⟨3, by
    rintro ⟨i, hi⟩
    fin_cases i <;> exact absurd (congrArg Fin.val hi) (by decide)⟩]
  exact exists_restrictFace_leftEmb

/-- **The face of the ladder type on `{2, 3}` is the test type with `k2Right`.** -/
theorem exists_restrictFace_k2Ladder_right :
    ∃ p, StageType.restrictFace rightEmb k2LadderType.{u} = some p ∧ IsTestType p k2Right := by
  rw [restrictFace_k2LadderType ⟨0, by
    rintro ⟨i, hi⟩
    fin_cases i <;> exact absurd (congrArg Fin.val hi) (by decide)⟩]
  exact exists_restrictFace_rightEmb

end VaughtConjecture.ProcessRank
