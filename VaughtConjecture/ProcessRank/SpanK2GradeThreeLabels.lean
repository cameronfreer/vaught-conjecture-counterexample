/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeThreeControllers

/-!
# The prescribed labels on the grade-three scheme of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the labels `k2Left`, `k2Right` of the
attachment, extended to the grade-three scheme `ProcessRank.k2Grade3`.

Let `P` be the labels of the attachment (`ProcessRank.k2AttLabel`) and `C` their orbit code at the
grade three (`ProcessRank.k2Code3`, a state of the grade-three catalogue by
`ProcessRank.k2Code3_mem`).  The labels on the grade-three scheme are the upper decoder of `P`, at
the grade three with cap grade four and block bound `16`, applied to the row of `C`
(`ProcessRank.k2Grade3Label`).  Compiled here (theorem named):
* they are lawful (`ProcessRank.isLawful_k2Grade3Label`): the row is lawful and the upper decoder
  is a witness bounded by the grade three sending only `⊥` to `⊥`;
* each is `⊤` or below `ω ^ 2` (`ProcessRank.atStage_k2Grade3Label`), by the stage bound of the
  upper decoder (`ProcessRank.atStage_upperDecoderAt`) at a row in `codeGrid 3 16`;
* on the attachment cells they are the prescribed labels (`ProcessRank.k2Grade3Label_att`), and on
  every cell of the ladder they are the labels of the ladder (`ProcessRank.k2Grade3Label_ladder`,
  through `Scheme.LadderBaseData.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne` at the
  grades two and three), hence the grade-two labels there
  (`ProcessRank.k2Grade3Label_castAdd_castAdd`);
* with them the grade-three scheme is a stage type at the stage `ω ^ 2`
  (`ProcessRank.k2Grade3Type`), whose faces on `{0, 1}` and `{2, 3}` are the test types with
  `k2Left` and `k2Right` (`ProcessRank.exists_restrictFace_k2Grade3_left`,
  `ProcessRank.exists_restrictFace_k2Grade3_right`): its faces along a pure embedding are those of
  the ladder type (`ProcessRank.restrictFace_k2Grade3Type`), every controller having full scope.

The grade-three labels do not extend the grade-two labels on the grade-two controllers: decoding
at the cap grade four reads a gap of the code at a label self-visible at the grade four, where the
grade-two labels read one self-visible at the grade three.  By direct calculation (not compiled
here), at the controller of the separated admitted state (`ProcessRank.k2SepCell`), which the code
of the attachment labels reads as `ω + 2`, the grade-two label is `3` and the grade-three label is
`4`.  So the comparison with the grade-two type is made on the ladder only.

Open: the mirror conditions at the grade three, the grade four, legality of the completed scheme,
the four-point span of mutual rigidity of the test pair, and the countable upper bound on the Scott
classes.  None of these is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- The **labels on the grade-three scheme**: the upper decoder of the attachment labels, at the
grade three with cap grade four and block bound `16`, applied to the row of the code at the grade
three of the attachment labels. -/
noncomputable def k2Grade3Label (z : Fin k2Grade3.{u}.card) : Label.{u} :=
  upperDecoderAt 3 4 16 (fun e : Fin k2AttachmentBase.{u}.S.card ↦ k2AttLabel e) (k2Phi3 k2Code3 z)

/-- **The labels on the grade-three scheme are lawful**: the row of the code is lawful and the
upper decoder is a witness bounded by the grade three sending only `⊥` to `⊥`. -/
theorem isLawful_k2Grade3Label : k2Grade3.{u}.rows.IsLawful k2Grade3Label :=
  (isLawful_k2Phi3 k2Code3_mem).map_of_apply_eq_bot k2Grade3_grade_le
    (isWitness_upperDecoderAt (by decide)) fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot

/-- **The stage bound**: each label on the grade-three scheme is `⊤` or below `ω ^ 2`. -/
theorem atStage_k2Grade3Label (z : Fin k2Grade3.{u}.card) : AtStage (ω ^ 2) (k2Grade3Label z) :=
  atStage_upperDecoderAt atStage_k2AttLabel
    (.inl (lt_omega0_sq_of_mem_codeGrid (k2Phi3_mem_codeGrid k2Code3_mem z)))

/-- **On the attachment cells the labels are the prescribed labels.** -/
theorem k2Grade3Label_att (e : Fin k2AttachmentBase.{u}.S.card) :
    k2Grade3Label (Fin.castAdd _ (k2Att e)) = k2AttLabel e := by
  unfold k2Grade3Label
  rw [k2Phi3_castAdd, k2Sec3_att k2Code3_mem e]
  exact upperDecoderAt_orbitCode e

/-- **On the cells of the ladder the labels are those of the ladder**: the upper decoder at the
grade two reads the extension of the code at the grade two of `k2Code3` as the extension of
`k2Code3`, and the upper decoder at the grade three reads that as the extension of the attachment
labels (`Scheme.LadderBaseData.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne`). -/
theorem k2Grade3Label_ladder (t : Fin k2Ladder.{u}.card) :
    k2Grade3Label (Fin.castAdd _ (Fin.castAdd _ t)) = k2LadderLabel t := by
  have hl : k2AttachmentBase.{u}.S.rows.IsLawful fun e ↦ k2AttLabel e := isLawful_k2AttLabel
  have hR := hl.isLawfulBelow ((univ : Finset (Fin 4)), 1)
  obtain ⟨-, hCl, hCv, -, -⟩ := mem_k2Cat3.mp (k2Code3_mem.{u})
  have hC1 : k2AttachmentBase.{u}.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1)
      fun d ↦ k2Code3 d := hCl.mono (X := ((univ : Finset (Fin 4)), 1)) ⟨subset_rfl, by decide⟩
  have hC2 : k2AttachmentBase.{u}.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1)
      fun d ↦ orbitCode 2 k2Code3 d := hC1.orbitCode fun d ↦ d.2.2.trans one_le_two
  have htop : k2AttLabel.{u} (0 : Fin 8) ≠ ⊥ := by simp [k2AttLabel, attCell, k2Left]
  have hpos3 : ∃ d : Fin k2AttachmentBase.{u}.S.card, k2Code3.{u} d ≠ ⊥ :=
    ⟨(0 : Fin 8), fun h ↦ htop (orbitCode_eq_bot_iff.mp h)⟩
  have hinner := k2AttachmentBase.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne k2_card_le
    (K := 3) (B' := 16) le_rfl hC1 hC2 hCv hpos3 t
  have houter := k2AttachmentBase.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne k2_card_le
    (K := 4) (B' := 16) (by decide) hR hC1 (k2AttachmentBase.isSelfVisible_one_of_isLawful hl)
    ⟨(0 : Fin 8), htop⟩ t
  unfold k2Grade3Label
  rw [k2Phi3_castAdd]
  unfold k2Sec3
  rw [k2Phi_castAdd, k2ControllerRow_of_isLawfulBelow hC2, hinner]
  exact houter.trans (congrFun (k2AttachmentBase.stateExtOf_eq_stateExt k2_card_le hl) t)

/-- **On the cells of the ladder the grade-three labels are the grade-two labels.** -/
theorem k2Grade3Label_castAdd_castAdd (t : Fin k2Ladder.{u}.card) :
    k2Grade3Label (Fin.castAdd _ (Fin.castAdd _ t)) = k2Grade2Label (Fin.castAdd _ t) :=
  (k2Grade3Label_ladder t).trans (k2Grade2Label_castAdd t).symm

/-! ### The grade-three stage type -/

/-- **The grade-three stage type** at the stage `ω ^ 2`: the grade-three scheme with the decoded
labels.  The mirror conditions at the grade three, the grade four, legality of the completed
scheme, the four-point span of mutual rigidity and the countable upper bound on the Scott classes
stay open. -/
noncomputable def k2Grade3Type : StageType.{u} (ω ^ 2) 4 where
  toScheme := k2Grade3
  label := k2Grade3Label
  isWellFormed := Scheme.isWellFormed_appendFullCells k2Grade2Type.isWellFormed (by decide)
    (by decide)
  isCoded := Scheme.isCoded_appendFullCells k2Grade2Type.isCoded fun i d ↦
    lt_omega0_sq_of_mem_codeGrid (k2Phi3_mem_codeGrid (k2Cat3.equivFin.symm i).2 d)
  isLawful := isLawful_k2Grade3Label
  atStage := atStage_k2Grade3Label

/-- The old cells of the ladder in the grade-three scheme form a lower embedding. -/
theorem isLowerEmbedding_k2Ladder_k2Grade3 :
    k2Ladder.{u}.toCellScheme.IsLowerEmbedding k2Grade3.{u}.toCellScheme
      (Fin.castAdd k2Cat3.{u}.card ∘ Fin.castAdd k2Cat2.{u}.card) :=
  (Scheme.isLowerEmbedding_castAdd (S := k2Grade2.{u}) 3 _
    (fun i ↦ k2Phi3 (k2Cat3.equivFin.symm i).1) k2Grade2_not_le_three).comp
    (Scheme.isLowerEmbedding_castAdd (S := k2Ladder.{u}) 2 _
      (fun i ↦ k2Phi (k2Cat2.equivFin.symm i).1) k2Ladder_not_le)

/-- The rows of the grade-three scheme pull back to those of the ladder. -/
theorem comap_rows_k2Ladder_k2Grade3 :
    k2Grade3.{u}.rows.comap isLowerEmbedding_k2Ladder_k2Grade3 = k2Ladder.{u}.rows := by
  have h := CellScheme.Rows.comap_comap k2Grade3.{u}.rows
    (Scheme.isLowerEmbedding_castAdd (S := k2Grade2.{u}) 3 _
      (fun i ↦ k2Phi3 (k2Cat3.equivFin.symm i).1) k2Grade2_not_le_three)
    (Scheme.isLowerEmbedding_castAdd (S := k2Ladder.{u}) 2 _
      (fun i ↦ k2Phi (k2Cat2.equivFin.symm i).1) k2Ladder_not_le)
  rw [Scheme.comap_rows_castAdd (S := k2Grade2.{u}) (k := 3) (M := k2Cat3.{u}.card)
    (r := fun i ↦ k2Phi3 (k2Cat3.equivFin.symm i).1) (h := k2Grade2_not_le_three),
    Scheme.comap_rows_castAdd (S := k2Ladder.{u}) (k := 2) (M := k2Cat2.{u}.card)
    (r := fun i ↦ k2Phi (k2Cat2.equivFin.symm i).1) (h := k2Ladder_not_le)] at h
  exact h.symm

/-- The cells of the grade-three scheme outside the ladder have full scope. -/
theorem k2Grade3_scope_of_not_mem {z : Fin k2Grade3.{u}.card}
    (hz : z ∉ Set.range (Fin.castAdd k2Cat3.{u}.card ∘ Fin.castAdd k2Cat2.{u}.card)) :
    k2Grade3.{u}.toCellScheme.scope z = univ := by
  induction z using Fin.addCases with
  | right j => exact Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j
  | left z =>
    induction z using Fin.addCases with
    | left d => exact absurd ⟨d, rfl⟩ hz
    | right j =>
      exact (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j)

/-- **The faces of the grade-three type along a pure embedding are those of the ladder type**: the
grade-two and grade-three controllers have full scope, so none is visible through an embedding
missing a point, and the labels on the ladder are those of the ladder. -/
theorem restrictFace_k2Grade3Type {f : Fin 2 ↪ Fin 4} (hf : ∃ x, x ∉ Set.range f) :
    StageType.restrictFace f k2Grade3Type.{u} = StageType.restrictFace f k2LadderType.{u} := by
  obtain ⟨x, hx⟩ := hf
  refine StageType.restrictFace_eq_of_strictMono (s := k2LadderType) (t := k2Grade3Type)
    (φ := Fin.castAdd k2Cat3.{u}.card ∘ Fin.castAdd k2Cat2.{u}.card) f
    ((Fin.strictMono_castAdd _).comp (Fin.strictMono_castAdd _))
    isLowerEmbedding_k2Ladder_k2Grade3
    (fun d ↦ (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
      (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d)) comap_rows_k2Ladder_k2Grade3 rfl rfl
    (fun d ↦ k2Grade3Label_ladder d) fun z hz ↦ ?_
  by_contra hzr
  have hs : k2Grade3.{u}.toCellScheme.scope z = univ := k2Grade3_scope_of_not_mem hzr
  change ((k2Grade3.{u}.toCellScheme.scope z : Finset (Fin 4)) : Set (Fin 4)) ⊆ _ at hz
  rw [hs, coe_univ] at hz
  exact hx (hz (Set.mem_univ x))

/-- **The left face of the grade-three type is the test type with `k2Left`.** -/
theorem exists_restrictFace_k2Grade3_left :
    ∃ p, StageType.restrictFace leftEmb k2Grade3Type.{u} = some p ∧ IsTestType p k2Left := by
  rw [restrictFace_k2Grade3Type ⟨3, by
    rintro ⟨i, hi⟩
    fin_cases i <;> exact absurd (congrArg Fin.val hi) (by decide)⟩]
  exact exists_restrictFace_k2Ladder_left

/-- **The right face of the grade-three type is the test type with `k2Right`.** -/
theorem exists_restrictFace_k2Grade3_right :
    ∃ q, StageType.restrictFace rightEmb k2Grade3Type.{u} = some q ∧ IsTestType q k2Right := by
  rw [restrictFace_k2Grade3Type ⟨0, by
    rintro ⟨i, hi⟩
    fin_cases i <;> exact absurd (congrArg Fin.val hi) (by decide)⟩]
  exact exists_restrictFace_k2Ladder_right

end VaughtConjecture.ProcessRank
