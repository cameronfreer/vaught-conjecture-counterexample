/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerShape
import VaughtConjecture.Continuation.AvailableTopDeterminationCounterexample
import VaughtConjecture.Extension.CoupledGatedExtensionCounterexample

/-!
# A context with distinct labels at the grade `1`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The clause of `TowerProfile.exists_coface_of_addApex_shape` is not vacuous at contexts without a
tie at the grade `1`.

* **The context** (`TieFreeContext.contextFour`, defined here): a completion below the full grade
  (`Seed.nonempty_completionBelowFullGrade_of_le_two`) of the seed of `faceT5` (labelled `⊥`) and a
  legal type on three points whose new point carries the donor of
  `CoupledGatedExtensionCounterexample` (two cells labelled `1` and `⊤`;
  `AvailableTopDeterminationCounterexample.exists_pinned_extension_of_le_three`), labelled by the
  truncated labels at the grade `1` and `⊥` above, with the apex added.  Everything is obtained
  generically; no catalogue or card is computed.
* **Distinct labels** (`TieFreeContext.label_donorCell`, `TieFreeContext.not_tie_one`, compiled):
  two cells of grade `1` through the point `3` are labelled `1` and `⊤`, so the field `tie_one` of
  `TowerProfile.LeftTie` fails.
* **The clause** (`TieFreeContext.exists_coface_contextFour`, compiled; feasibility at one
  context): the context has the shape (the face off `3` and the grades `2`, `3` labelled `⊥`), and
  at the empty root its donor at the point `3`, which carries the cell labelled `⊤`, is determined
  at a permitted cutoff in a coface.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace TieFreeContext

open TowerProfile TopReadingApexExample

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

include hα in
/-- The cells of `faceT5` are labelled `⊥`. -/
theorem label_faceT5 (z : Fin (CaseSplitCounterexample.faceT5 α).card) :
    (CaseSplitCounterexample.faceT5 α).label z = ⊥ := by
  have h := label_faceCell (restrictFace_oneType hα) z
  refine h.symm.trans ?_
  refine label_eq_bot_of_mem_visibleCells hα (g := Function.Embedding.refl (Fin 3)) ?_
  exact (oneType hα).toScheme.faceCell_mem_visibleCells _ z

theorem isLegal_faceT5 : (CaseSplitCounterexample.faceT5 α).IsLegal :=
  (isLegal_rightType α).restrictFace _ (restrictFace_rightType α)

theorem exists_face_faceT5 :
    ∃ p, restrictFace (Fin.castSuccEmb : Fin 2 ↪ Fin 3) (CaseSplitCounterexample.faceT5 α) =
      some p := by
  refine Option.isSome_iff_exists.mp ?_
  rw [restrictFace_trans _ _ _ (restrictFace_rightType α), isSome_restrictFace_iff]
  have hm : univ.map ((Fin.castSuccEmb : Fin 2 ↪ Fin 3).trans (Coatom.face 3)) =
      TwoFaceLiftCounterexample.cellScope (4 : Fin 19) := by decide
  rw [hm]
  exact scope_mem_faces_rightType (α := α) (toS 4)

/-- The face of `faceT5` on its first two points. -/
noncomputable def faceTwo (α : Ordinal.{u}) : StageType.{u} α 2 :=
  (exists_face_faceT5 (α := α)).choose

theorem restrictFace_faceTwo :
    restrictFace (Fin.castSuccEmb : Fin 2 ↪ Fin 3) (CaseSplitCounterexample.faceT5 α) =
      some (faceTwo α) :=
  (exists_face_faceT5 (α := α)).choose_spec

theorem isLegal_faceTwo : (faceTwo α).IsLegal :=
  isLegal_faceT5.restrictFace _ restrictFace_faceTwo

include hα in
theorem one_lt : (1 : Ordinal.{u}) < α := by
  simpa using hα.add_one_lt hα.bot_lt

/-- The empty root of the first two points. -/
def rootNil : Fin 0 ↪ Fin 2 := Function.Embedding.ofIsEmpty

include hα in
/-- **A legal type on three points whose new point carries the cells labelled `1` and `⊤`**: a
one-point coface of `faceTwo` whose face at the new point is the donor of
`CoupledGatedExtensionCounterexample`
(`AvailableTopDeterminationCounterexample.exists_pinned_extension_of_le_three`). -/
theorem exists_threeType : ∃ Q : StageType.{u} α 3, Q.IsLegal ∧
    restrictFace Fin.castSuccEmb Q = some (faceTwo α) ∧
    restrictFace (extendByLast rootNil) Q =
      some (CoupledGatedExtensionCounterexample.donor α (one_lt hα)) := by
  obtain ⟨p₀, hp₀⟩ := Option.isSome_iff_exists.mp (isSome_restrictFace_of_zero (faceTwo α) rootNil)
  obtain ⟨q₀, hq₀⟩ := Option.isSome_iff_exists.mp (isSome_restrictFace_of_zero
    (CoupledGatedExtensionCounterexample.donor α (one_lt hα)) Fin.castSuccEmb)
  rw [eq_of_zero q₀ p₀] at hq₀
  exact AvailableTopDeterminationCounterexample.exists_pinned_extension_of_le_three
    hα.isSuccPrelimit (by omega) isLegal_faceTwo hp₀
    (CoupledGatedExtensionCounterexample.isLegal_donor α (one_lt hα)) hq₀

/-- The type on three points. -/
noncomputable def threeType : StageType.{u} α 3 := (exists_threeType hα).choose

theorem threeType_spec : (threeType hα).IsLegal ∧
    restrictFace Fin.castSuccEmb (threeType hα) = some (faceTwo α) ∧
    restrictFace (extendByLast rootNil) (threeType hα) =
      some (CoupledGatedExtensionCounterexample.donor α (one_lt hα)) :=
  (exists_threeType hα).choose_spec

/-- **The seed on four points**: `faceT5` (labelled `⊥`) and the type on three points. -/
noncomputable def seedFour : Seed.{u} α 2 :=
  Seed.ofCoatoms isLegal_faceT5 (threeType_spec hα).1 restrictFace_faceTwo (threeType_spec hα).2.1

/-- A completion of the seed below the full grade
(`Seed.nonempty_completionBelowFullGrade_of_le_two`). -/
noncomputable def completionFour : CompletionBelowFullGrade (seedFour hα) :=
  ((seedFour hα).nonempty_completionBelowFullGrade_of_le_two le_rfl).some

/-- The labelling of the completed scheme: the truncated labels at the grade `1`, `⊥` above. -/
noncomputable def labelFour : Fin (completionFour hα).scheme.card → Label.{u} :=
  (completionFour hα).scheme.toCellScheme.splice 1 (fun _ ↦ ⊥)
    ((completionFour hα).truncate hα.isSuccPrelimit).label

theorem isLawful_labelFour : (completionFour hα).scheme.rows.IsLawful (labelFour hα) :=
  Scheme.isLawful_splice_bot
    (((completionFour hα).truncate hα.isSuccPrelimit).isLawful.isLawfulBelow _)

theorem atStage_labelFour (d : Fin (completionFour hα).scheme.card) :
    AtStage α (labelFour hα d) := by
  unfold labelFour
  by_cases hd : (completionFour hα).scheme.toCellScheme.grade d ≤ 1
  · exact Eq.mpr (congrArg (AtStage α) (CellScheme.splice_of_le hd))
      (((completionFour hα).truncate hα.isSuccPrelimit).atStage d)
  · exact Eq.mpr (congrArg (AtStage α) (CellScheme.splice_of_lt (not_le.mp hd))) atStage_bot

/-- The type on four points below the full grade. -/
noncomputable def baseFour : StageType.{u} α 4 :=
  (completionFour hα).withLabel (isLawful_labelFour hα) (atStage_labelFour hα)

/-- **The context**: the apex type of `baseFour`. -/
noncomputable abbrev contextFour : StageType.{u} α 4 :=
  apexOf (t₀ := baseFour hα) (completionFour hα).isLegalBelowFullGrade

theorem cases_contextFour (z : Fin (contextFour hα).card) :
    z = Fin.last _ ∨ ∃ w : Fin (completionFour hα).scheme.card, z = Fin.castSucc w := by
  change Fin ((completionFour hα).scheme.card + 1) at z
  induction z using Fin.lastCases with
  | last => exact .inl rfl
  | cast w => exact .inr ⟨w, rfl⟩

theorem label_contextFour_castSucc (w : Fin (completionFour hα).scheme.card) :
    (contextFour hα).label (Fin.castSucc w) = labelFour hα w :=
  StageType.addApex_label_castSucc (t := baseFour hα) _ _ w

theorem scope_contextFour_castSucc (w : Fin (completionFour hα).scheme.card) :
    (contextFour hα).toCellScheme.scope (Fin.castSucc w) =
      (completionFour hα).scheme.toCellScheme.scope w :=
  Scheme.appendFullCellScheme_scope_castSucc _ _ w

theorem grade_contextFour_castSucc (w : Fin (completionFour hα).scheme.card) :
    (contextFour hα).toCellScheme.grade (Fin.castSucc w) =
      (completionFour hα).scheme.toCellScheme.grade w :=
  Scheme.appendFullCellScheme_grade_castSucc _ _ w

theorem grade_contextFour_last : (contextFour hα).toCellScheme.grade (Fin.last _) = 4 :=
  congrArg Prod.snd (StageType.addApex_gradedIndex_last (t := baseFour hα)
    (completionFour hα).isLegalBelowFullGrade (by omega))

theorem labelFour_of_one_lt {w : Fin (completionFour hα).scheme.card}
    (hw : 1 < (completionFour hα).scheme.toCellScheme.grade w) : labelFour hα w = ⊥ :=
  CellScheme.splice_of_lt hw

theorem labelFour_embed {d : Fin (seedFour hα).amalgam.card}
    (hd : (seedFour hα).amalgam.toCellScheme.grade d ≤ 1) :
    labelFour hα ((completionFour hα).embed d) = (seedFour hα).amalgam.label d := by
  have hg : (completionFour hα).scheme.toCellScheme.grade ((completionFour hα).embed d) ≤ 1 := by
    rw [(completionFour hα).isLowerEmbedding.grade_eq d]; exact hd
  exact (CellScheme.splice_of_le hg).trans
    ((completionFour hα).truncate_label_embed hα.isSuccPrelimit d)

/-- **The face off the point `3` is labelled `⊥`**: its cells are old cells of the left coatom,
labelled as `faceT5`. -/
theorem label_contextFour_of_notMem (z : Fin (contextFour hα).card)
    (hz : Fin.last 3 ∉ (contextFour hα).toCellScheme.scope z) : (contextFour hα).label z = ⊥ := by
  rcases cases_contextFour hα z with rfl | ⟨w, rfl⟩
  · exact absurd (Eq.mpr (congrArg (Fin.last 3 ∈ ·) (StageType.addApex_scope_last
      (t := baseFour hα) (completionFour hα).isLegalBelowFullGrade (by omega))) (mem_univ _)) hz
  · refine (label_contextFour_castSucc hα w).trans ?_
    have hz := (scope_contextFour_castSucc hα w).symm ▸ hz
    have hne : (completionFour hα).scheme.toCellScheme.scope w ≠ univ := fun h ↦ hz (h ▸ mem_univ _)
    obtain ⟨d, rfl⟩ := (completionFour hα).mem_range_embed w hne
    rw [(completionFour hα).scope_embed] at hz
    obtain ⟨z', hz'⟩ := exists_faceCell_eq_of_last_notMem (seedFour hα).restrictFace_left hz
    by_cases hg : (seedFour hα).amalgam.toCellScheme.grade d ≤ 1
    · rw [labelFour_embed hα hg, ← hz', label_faceCell]
      exact label_faceT5 hα z'
    · exact labelFour_of_one_lt hα (by rw [(completionFour hα).isLowerEmbedding.grade_eq d]; omega)

/-- The cells of grade at least `2` are labelled `⊥`, except the apex. -/
theorem label_contextFour_of_grade {z : Fin (contextFour hα).card}
    (h2 : 2 ≤ (contextFour hα).toCellScheme.grade z)
    (h3 : (contextFour hα).toCellScheme.grade z ≤ 3) :
    (contextFour hα).label z = ⊥ := by
  rcases cases_contextFour hα z with rfl | ⟨w, rfl⟩
  · have := grade_contextFour_last hα
    omega
  · refine (label_contextFour_castSucc hα w).trans ?_
    have h2 := (grade_contextFour_castSucc hα w).symm ▸ h2
    exact labelFour_of_one_lt hα (by omega)

/-! ### The cells labelled `1` and `⊤` at the grade `1` -/

/-- A cell of the donor. -/
abbrev dcell (e : Fin 2) : Fin (CoupledGatedExtensionCounterexample.donor α (one_lt hα)).card := e

/-- A cell of the donor, in the context. -/
noncomputable def donorCell (e : Fin 2) : Fin (contextFour hα).card :=
  Fin.castSucc ((completionFour hα).embed (faceCell (seedFour hα).restrictFace_right
    (faceCell (threeType_spec hα).2.2 (dcell hα e))))

theorem amalgam_donorCell (e : Fin 2) :
    (seedFour hα).amalgam.toCellScheme.scope (faceCell (seedFour hα).restrictFace_right
      (faceCell (threeType_spec hα).2.2 (dcell hα e))) = {Fin.last 3} ∧
    (seedFour hα).amalgam.toCellScheme.grade (faceCell (seedFour hα).restrictFace_right
      (faceCell (threeType_spec hα).2.2 (dcell hα e))) = 1 ∧
    (seedFour hα).amalgam.label (faceCell (seedFour hα).restrictFace_right
      (faceCell (threeType_spec hα).2.2 (dcell hα e))) =
        CoupledGatedExtensionCounterexample.donorLab 1 ⊤ e := by
  refine ⟨?_, ?_, ?_⟩
  · refine (scope_faceCell (seedFour hα).restrictFace_right _).trans ?_
    refine (congrArg (·.map (Coatom.right 2))
      (scope_faceCell (threeType_spec hα).2.2 (dcell hα e))).trans ?_
    change ((univ : Finset (Fin 1)).map (extendByLast rootNil)).map
      (extendByLast (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) = _
    rw [show (univ : Finset (Fin 1)) = {Fin.last 0} by decide, map_singleton, map_singleton,
      extendByLast_last, extendByLast_last]
  · exact (grade_faceCell (seedFour hα).restrictFace_right _).trans
      ((grade_faceCell (threeType_spec hα).2.2 (dcell hα e)).trans rfl)
  · exact (label_faceCell (seedFour hα).restrictFace_right _).trans
      ((label_faceCell (threeType_spec hα).2.2 (dcell hα e)).trans rfl)

theorem donorCell_spec (e : Fin 2) :
    (contextFour hα).toCellScheme.scope (donorCell hα e) = {Fin.last 3} ∧
    (contextFour hα).toCellScheme.grade (donorCell hα e) = 1 ∧
    (contextFour hα).label (donorCell hα e) =
      CoupledGatedExtensionCounterexample.donorLab 1 ⊤ e := by
  obtain ⟨h1, h2, h3⟩ := amalgam_donorCell hα e
  refine ⟨(scope_contextFour_castSucc hα _).trans (((completionFour hα).scope_embed _).trans h1),
    (grade_contextFour_castSucc hα _).trans
      (((completionFour hα).isLowerEmbedding.grade_eq _).trans h2),
    (label_contextFour_castSucc hα _).trans ((labelFour_embed hα h2.le).trans h3)⟩

/-- **The context carries the labels `1` and `⊤` at two cells of grade `1` through the point
`3`.** -/
theorem label_donorCell :
    (contextFour hα).label (donorCell hα 0) = 1 ∧ (contextFour hα).label (donorCell hα 1) = ⊤ :=
  ⟨(donorCell_spec hα 0).2.2, (donorCell_spec hα 1).2.2⟩

/-- **No tie at the grade `1`**: no cell `z₁` has every lawful labelling take its value at every
cell of grade `1` not labelled `⊥` (the field `tie_one` of `TowerProfile.LeftTie` fails): the
labelling of the context itself takes the values `1` and `⊤` there. -/
theorem not_tie_one : ¬ ∃ z₁ : Fin (contextFour hα).card, ∀ q : Fin (contextFour hα).card →
    Label.{u}, (contextFour hα).rows.IsLawful q → ∀ z, (contextFour hα).toCellScheme.grade z = 1 →
      (contextFour hα).label z ≠ ⊥ → q z = q z₁ := by
  rintro ⟨z₁, h⟩
  have h0 := h _ (contextFour hα).isLawful (donorCell hα 0) (donorCell_spec hα 0).2.1
    (by rw [(label_donorCell hα).1]; exact (WithBot.coe_ne_bot))
  have h1 := h _ (contextFour hα).isLawful (donorCell hα 1) (donorCell_spec hα 1).2.1
    (by rw [(label_donorCell hα).2]; exact top_ne_bot)
  have := h0.trans h1.symm
  rw [(label_donorCell hα).1, (label_donorCell hα).2] at this
  exact absurd this (ne_of_lt (by simpa using (natCast_label_lt_omega.{u} 1).trans_le le_top))

/-! ### The clause at the context -/

/-- The empty root of the common face. -/
def rootEmpty : Fin 0 ↪ Fin 3 := Function.Embedding.ofIsEmpty

/-- The new tops of the context: its cells of scope `{3}` labelled `⊤`. -/
noncomputable def topsFour : Finset (Fin (contextFour hα).card) :=
  (univ : Finset (Fin (contextFour hα).card)).filter fun z ↦
    (contextFour hα).toCellScheme.scope z ⊆ {Fin.last 3} ∧
      (3 : Fin 4) ∈ (contextFour hα).toCellScheme.scope z ∧ (contextFour hα).label z = ⊤

theorem rightOneTops_topsFour : RightOneTops (contextFour hα) (topsFour hα) where
  mem_scope z hz := (mem_filter.mp hz).2.2.1
  grade_eq z hz := by
    obtain ⟨hs, h3, -⟩ := (mem_filter.mp hz).2
    have h1 := (contextFour hα).isWellFormed.isWellFormed.grade_le_card z
    have h2 := (contextFour hα).isWellFormed.isWellFormed.grade_pos z
    have h3' : #((contextFour hα).toCellScheme.scope z) ≤ 1 :=
      (card_le_card hs).trans (by simp)
    omega
  label_eq z hz := (mem_filter.mp hz).2.2.2

theorem univ_map_rootEmpty :
    univ.map (extendByLast rootEmpty) = ({Fin.last 3} : Finset (Fin 4)) := by
  rw [show (univ : Finset (Fin 1)) = {Fin.last 0} by decide, map_singleton, extendByLast_last]

/-- **The clause of hollow coatom cutoff determination at a context without a tie at the grade
`1`** (feasibility, one context): the context `contextFour` carries the labels `1` and `⊤` at two
cells of grade `1` through the point `3` (`TieFreeContext.label_donorCell`), so no tie at the
grade `1` holds there (`TieFreeContext.not_tie_one`); it is an apex context of the shape
(`TowerProfile.exists_coface_of_addApex_shape`), and at the empty root, with itself as the
coface, its donor at the point `3` (which carries the cell labelled `⊤`) is determined at a
permitted cutoff in a coface. -/
theorem exists_coface_contextFour :
    ∃ p, restrictFace Fin.castSuccEmb (contextFour hα) = some p ∧
      ∃ d : StageType.{u} α 1, restrictFace (extendByLast rootEmpty) (contextFour hα) = some d ∧
        ∃ D' ∈ (contextFour hα).cofaces,
          restrictFace (extendByLast Fin.castSuccEmb) D' = some (contextFour hα) ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) (contextFour hα)
              (rootEmpty.trans Fin.castSuccEmb) d := by
  have hfaces : (contextFour hα).toCellScheme.faces = (seedFour hα).amalgam.toCellScheme.faces :=
    (completionFour hα).faces_eq
  obtain ⟨p, hpa⟩ : ∃ p, restrictFace Fin.castSuccEmb (contextFour hα) = some p := by
    refine Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr ?_)
    rw [hfaces]
    exact ((restrictFace_eq_some_iff _ _).mp (seedFour hα).restrictFace_left).1
  obtain ⟨d, hd⟩ : ∃ d, restrictFace (extendByLast rootEmpty) (contextFour hα) = some d := by
    refine Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr ?_)
    rw [univ_map_rootEmpty, ← (donorCell_spec hα 0).1]
    exact (contextFour hα).isWellFormed.isWellFormed.scope_mem _
  -- a cell of grade `2`
  obtain ⟨w₂, hw₂⟩ := (completionFour hα).isLegalBelowFullGrade.exists_gradedIndex_eq
    ((univ : Finset (Fin 4)), 2)
    ⟨(completionFour hα).isLegalBelowFullGrade.isWellFormed.univ_mem_faces,
      by omega, by simp⟩ (by omega)
  have hg₂ : (contextFour hα).toCellScheme.grade (Fin.castSucc w₂) = 2 :=
    (grade_contextFour_castSucc hα w₂).trans (congrArg Prod.snd hw₂)
  have hz₂ : (contextFour hα).label (Fin.castSucc w₂) = ⊥ :=
    label_contextFour_of_grade hα (by omega) (by omega)
  refine ⟨p, hpa, d, hd, exists_coface_of_addApex_shape hα
    (completionFour hα).isLegalBelowFullGrade hpa (label_contextFour_of_notMem hα) hg₂
    (fun q _ z hz hl ↦ absurd (label_contextFour_of_grade hα hz.ge
      (hz.le.trans (by decide : (2 : ℕ) ≤ 3))) hl)
    (fun hl ↦ absurd hz₂ hl)
    (fun z hz ↦ label_contextFour_of_grade hα (hz.ge.trans' (by decide : (2 : ℕ) ≤ 3)) hz.le)
    ⟨StageType.isLegal_addApex _ _, hpa⟩ (rightOneTops_topsFour hα) rootEmpty (by omega) hd
    fun j hj hjt ↦ ?_⟩
  refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, (label_faceCell hd j).trans hjt⟩
  · rw [scope_faceCell, ← univ_map_rootEmpty]
    exact map_subset_map.mpr (subset_univ _)
  · rw [scope_faceCell]
    exact mem_map.mpr ⟨_, hj, extendByLast_last _⟩

end TieFreeContext

end VaughtConjecture
