/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelRecovery
import VaughtConjecture.ProcessRank.SpanK2GradeTwoControllers

/-!
# The prescribed labels on the grade-two scheme of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the labels `k2Left`, `k2Right` of the
attachment, extended to the grade-two scheme `ProcessRank.k2Grade2`.

Let `P` be the labels of the attachment (`ProcessRank.k2AttLabel`) and `C` their orbit code at the
grade two (`ProcessRank.k2Code`).  Compiled here (theorem named):
* `C` is a state of the grade-two catalogue (`ProcessRank.k2Code_mem`); its two copies of each top
  cell read `⊤` (`ProcessRank.isAdmitted_k2AttLabel`).
* The labels on the grade-two scheme are the upper decoder of `P`, at the grade two with cap grade
  three and block bound `16`, applied to the row of `C` (`ProcessRank.k2Grade2Label`).  They are
  lawful (`ProcessRank.isLawful_k2Grade2Label`): the row is lawful and the upper decoder is a
  witness bounded by the grade two sending only `⊥` to `⊥`.
* On the old cells of the ladder they are the labels of the ladder
  (`ProcessRank.k2Grade2Label_castAdd`, from
  `Scheme.LadderBaseData.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne`).
* Each is `⊤` or below `ω ^ 2` (`ProcessRank.atStage_k2Grade2Label`).  The decoder restores the
  prescribed tops, so this is not read off the code grid: it is the stage bound of the upper
  decoder (`ProcessRank.atStage_upperDecoderAt`), for a labelling with values `⊤` or below `ω ^ 2`
  at a label `⊤` or below `ω ^ 2`.
* With them the grade-two scheme is a stage type at the stage `ω ^ 2`
  (`ProcessRank.k2Grade2Type`), whose faces on `{0, 1}` and `{2, 3}` are the test types with
  `k2Left` and `k2Right` (`ProcessRank.exists_restrictFace_k2Grade2_left`,
  `ProcessRank.exists_restrictFace_k2Grade2_right`): the controllers have full scope, so none is
  visible through an embedding missing a point (`ProcessRank.restrictFace_k2Grade2Type`).

Open: the common-shadow and twin conditions, the grades three and four, the four-point span of
mutual rigidity of the test pair, and the countable upper bound on the Scott classes.  None of these
is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-! ### The stage bound of the upper decoder -/

/-- `ω ^ 2` is zero or a limit. -/
theorem isSuccPrelimit_omega0_sq : Order.IsSuccPrelimit (ω ^ 2 : Ordinal.{u}) :=
  Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_pow_self ω two_ne_zero)

/-- The maximum of two labels at a stage is at that stage. -/
theorem atStage_max {α : Ordinal.{u}} {x y : Label.{u}} (hx : AtStage α x) (hy : AtStage α y) :
    AtStage α (max x y) := by
  rcases max_choice x y with h | h <;> rwa [h]

/-- A label at most a label below a stage is at that stage. -/
theorem atStage_of_le_lt {α : Ordinal.{u}} {x y : Label.{u}} (hxy : x ≤ y) (hy : y < α) :
    AtStage α x :=
  .inl (hxy.trans_lt hy)

/-- Grid points lie below `ω ^ 2`. -/
theorem gridPoint_lt_omega0_sq (k b : ℕ) :
    gridPoint.{u} k b < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (omega0_mul_add_lt_omega0_sq b k))

/-- Members of a code grid lie below `ω ^ 2`. -/
theorem lt_omega0_sq_of_mem_codeGrid {k B : ℕ} {x : Label.{u}} (hx : x ∈ codeGrid k B) :
    x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases mem_codeGrid.mp hx with rfl | ⟨b, -, f, -, rfl⟩
  · exact WithBot.bot_lt_coe _
  · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (omega0_mul_add_lt_omega0_sq b f))

/-- The block index of a label at the stage `ω ^ 2` is below `ω` (it is `0` at `⊤`). -/
theorem blockIndex_lt {y : Label.{u}} (hy : AtStage (ω ^ 2) y) : blockIndex y < ω := by
  induction y using recBotCoeTop with
  | bot => simp [blockIndex]
  | top =>
    change (0 : Ordinal.{u}) / ω < ω
    rw [Ordinal.zero_div]
    exact Ordinal.omega0_pos
  | coe o =>
    change o / ω < ω
    rw [← Ordinal.lt_mul_iff_div_lt Ordinal.omega0_ne_zero, ← pow_two]
    exact atStage_coe.mp hy

/-- The block move to a label at the stage `ω ^ 2` keeps the stage `ω ^ 2`. -/
theorem atStage_moveToBlock {y x : Label.{u}} (hy : AtStage (ω ^ 2) y) (hx : AtStage (ω ^ 2) x) :
    AtStage (ω ^ 2) (moveToBlock y x) := by
  induction x using recBotCoeTop with
  | bot => exact atStage_bot
  | top => exact .inr rfl
  | coe o =>
    change AtStage _ ((ω * blockIndex y + o % ω : Ordinal.{u}) : Label.{u})
    have h := Label.omega0_mul_add_lt (Ordinal.mod_lt o Ordinal.omega0_ne_zero) (blockIndex_lt hy) 0
    rw [add_zero, ← pow_two] at h
    exact atStage_coe.mpr h

/-- Visibility replacement keeps the stage `ω ^ 2`. -/
theorem atStage_visibilityReplace (k i : ℕ) {y : Label.{u}} (hy : AtStage (ω ^ 2) y) :
    AtStage (ω ^ 2) (visibilityReplace k i y) := by
  rcases hy with h | rfl
  · exact .inl ((Label.visibilityReplace_lt_iff isSuccPrelimit_omega0_sq).mpr h)
  · exact .inr rfl

/-- **The stage bound of the upper decoder**: for a labelling with values at the stage `ω ^ 2`, the
upper decoder sends a label at the stage `ω ^ 2` to a label at the stage `ω ^ 2`.  The formal top
comes back only through the readings of the cells labelled `⊤`, the remaining values staying at
most a grid point or a value of the labelling, or in the block of one. -/
theorem atStage_upperDecoderAt {ι : Type*} [Fintype ι] {k K B : ℕ} {w : ι → Label.{u}}
    (hw : ∀ d, AtStage (ω ^ 2) (w d)) {x : Label.{u}} (hx : AtStage (ω ^ 2) x) :
    AtStage (ω ^ 2) (upperDecoderAt k K B w x) := by
  classical
  refine atStage_max ?_ (atStage_of_le_lt (gapValueAt_le_gridPoint x) (gridPoint_lt_omega0_sq K B))
  refine atStage_max (hx.min (.inl (gridPoint_lt_omega0_sq k 0))) ?_
  refine Finset.sup_induction atStage_bot (fun _ ha _ hb ↦ atStage_max ha hb) fun d _ ↦ ?_
  unfold cellReading
  split_ifs
  · exact atStage_bot
  · exact atStage_moveToBlock (hw d) hx
  · exact atStage_visibilityReplace k k (hw d)

/-! ### The code of the attachment labels -/

/-- The labels of the attachment are at the stage `ω ^ 2`. -/
theorem atStage_k2AttLabel (e : Fin k2AttachmentBase.{u}.S.card) :
    AtStage (ω ^ 2) (k2AttLabel.{u} e) :=
  k2AttachmentType.atStage e

/-- The labels of the attachment at the fields: the two copies of each top cell read `⊤`. -/
theorem isAdmitted_k2AttLabel : IsAdmitted k2Tops 2 2 fun x ↦ k2AttLabel.{u} (attField x) := by
  intro _ _ d hd
  rcases hd with rfl | rfl | rfl <;> rfl

/-- The **code of the attachment labels** at the grade two. -/
noncomputable def k2Code : Fin k2AttachmentBase.{u}.S.card → Label.{u} :=
  orbitCode 2 fun e ↦ k2AttLabel e

/-- **The code of the attachment labels lies in the grade-two catalogue.** -/
theorem k2Code_mem : k2Code.{u} ∈ k2Cat2 := by
  have hl : k2AttachmentBase.{u}.S.rows.IsLawful fun e ↦ k2AttLabel e := isLawful_k2AttLabel
  refine mem_k2Cat2.mpr ⟨fun e ↦ orbitMap_mem_codeGrid (by decide) _, ?_, fun e ↦ ?_,
    orbitCode_orbitCode, ?_⟩
  · exact (hl.isLawfulBelow _).orbitCode fun d ↦ d.2.2
  · exact isSelfVisible_one_orbitCode (by decide) (k2AttachmentBase.isSelfVisible_one_of_isLawful
      hl e)
  · exact (isAdmitted_iff_of_le_iff (fun _ _ ↦ orbitCode_le_iff) fun _ ↦ orbitCode_eq_bot_iff).mpr
      isAdmitted_k2AttLabel

/-! ### The decoded labels -/

/-- The **labels on the grade-two scheme**: the upper decoder of the attachment labels, at the grade
two with cap grade three and block bound `16`, applied to the row of the code of the attachment
labels. -/
noncomputable def k2Grade2Label (z : Fin k2Grade2.{u}.card) : Label.{u} :=
  upperDecoderAt 2 3 16 (fun e : Fin k2AttachmentBase.{u}.S.card ↦ k2AttLabel e) (k2Phi k2Code z)

/-- **The labels on the grade-two scheme are lawful**: the row of the code is lawful and the upper
decoder is a witness bounded by the grade two sending only `⊥` to `⊥`. -/
theorem isLawful_k2Grade2Label : k2Grade2.{u}.rows.IsLawful k2Grade2Label :=
  (isLawful_k2Phi k2Code_mem).map_of_apply_eq_bot k2Grade2_grade_le
    (isWitness_upperDecoderAt (by decide)) fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot

/-- **On the old cells the labels are those of the ladder**: the upper decoder reads the extension
of the code to the ladder as the extension of the attachment labels
(`Scheme.LadderBaseData.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne`). -/
theorem k2Grade2Label_castAdd (z : Fin k2Ladder.{u}.card) :
    k2Grade2Label (Fin.castAdd _ z) = k2LadderLabel z := by
  have hl : k2AttachmentBase.{u}.S.rows.IsLawful fun e ↦ k2AttLabel e := isLawful_k2AttLabel
  have hR := hl.isLawfulBelow ((univ : Finset (Fin 4)), 1)
  have hC : k2AttachmentBase.{u}.S.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 1)
      fun d ↦ k2Code d := hR.orbitCode fun d ↦ d.2.2.trans one_le_two
  have h := k2AttachmentBase.upperDecoderAt_stateExtOf_orbitCode_ofLawfulBelowOne k2_card_le
    (K := 3) (B' := 16) le_rfl hR hC (k2AttachmentBase.isSelfVisible_one_of_isLawful hl)
    ⟨(0 : Fin 8), by simp [k2AttLabel, attCell, k2Left]⟩ z
  unfold k2Grade2Label
  rw [k2Phi_castAdd, k2ControllerRow_of_isLawfulBelow hC]
  exact h.trans (congrFun (k2AttachmentBase.stateExtOf_eq_stateExt k2_card_le hl) z)

/-- **The stage bound**: each label on the grade-two scheme is `⊤` or below `ω ^ 2`.  The upper
decoder restores the prescribed tops, so this does not follow from the code grid; it follows from
the stage bound of the upper decoder (`ProcessRank.atStage_upperDecoderAt`). -/
theorem atStage_k2Grade2Label (z : Fin k2Grade2.{u}.card) : AtStage (ω ^ 2) (k2Grade2Label z) :=
  atStage_upperDecoderAt atStage_k2AttLabel
    (.inl (lt_omega0_sq_of_mem_codeGrid (k2Phi_mem_codeGrid k2Code_mem z)))

/-! ### The grade-two stage type -/

/-- **The grade-two stage type** at the stage `ω ^ 2`: the grade-two scheme with the decoded
labels.  The common-shadow and twin conditions, the grades three and four, the four-point span of
mutual rigidity and the countable upper bound on Scott classes stay open. -/
noncomputable def k2Grade2Type : StageType.{u} (ω ^ 2) 4 where
  toScheme := k2Grade2
  label := k2Grade2Label
  isWellFormed := Scheme.isWellFormed_appendFullCells k2LadderType.isWellFormed (by decide)
    (by decide)
  isCoded := Scheme.isCoded_appendFullCells k2LadderType.isCoded fun i d ↦
    lt_omega0_sq_of_mem_codeGrid (k2Phi_mem_codeGrid (k2Cat2.equivFin.symm i).2 d)
  isLawful := isLawful_k2Grade2Label
  atStage := atStage_k2Grade2Label

/-- **The faces of the grade-two type along a pure embedding are those of the ladder type**: the
controllers have full scope, so no controller is visible through an embedding missing a point. -/
theorem restrictFace_k2Grade2Type {f : Fin 2 ↪ Fin 4} (hf : ∃ x, x ∉ Set.range f) :
    StageType.restrictFace f k2Grade2Type.{u} = StageType.restrictFace f k2LadderType.{u} := by
  refine StageType.restrictFace_eq_of_strictMono (s := k2LadderType) (t := k2Grade2Type)
    (φ := Fin.castAdd _) f (Fin.strictMono_castAdd _)
    (Scheme.isLowerEmbedding_castAdd (S := k2Ladder) 2 _ (fun i ↦ k2Phi (k2Cat2.equivFin.symm i).1)
      k2Ladder_not_le)
    (fun d ↦ Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d)
    (Scheme.comap_rows_castAdd (S := k2Ladder.{u}) (k := 2) (M := k2Cat2.{u}.card)
      (r := fun i ↦ k2Phi (k2Cat2.equivFin.symm i).1) (h := k2Ladder_not_le)) rfl rfl
    (fun d ↦ k2Grade2Label_castAdd d) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := hf
  induction z using Fin.addCases with
  | left d => exact ⟨d, rfl⟩
  | right j =>
    exfalso
    have hs : k2Grade2Type.{u}.toCellScheme.scope (Fin.natAdd _ j) = univ :=
      Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j
    rw [hs, coe_univ] at hz
    exact hx (hz (Set.mem_univ x))

/-- **The left face of the grade-two type is the test type with `k2Left`.** -/
theorem exists_restrictFace_k2Grade2_left :
    ∃ p, StageType.restrictFace leftEmb k2Grade2Type.{u} = some p ∧ IsTestType p k2Left := by
  rw [restrictFace_k2Grade2Type ⟨3, by
    rintro ⟨i, hi⟩
    fin_cases i <;> exact absurd (congrArg Fin.val hi) (by decide)⟩]
  exact exists_restrictFace_k2Ladder_left

/-- **The right face of the grade-two type is the test type with `k2Right`.** -/
theorem exists_restrictFace_k2Grade2_right :
    ∃ q, StageType.restrictFace rightEmb k2Grade2Type.{u} = some q ∧ IsTestType q k2Right := by
  rw [restrictFace_k2Grade2Type ⟨0, by
    rintro ⟨i, hi⟩
    fin_cases i <;> exact absurd (congrArg Fin.val hi) (by decide)⟩]
  exact exists_restrictFace_k2Ladder_right

end VaughtConjecture.ProcessRank
