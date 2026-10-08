/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2OneTop

/-!
# Top grade `1` at two points: the completion (work file)

WORK FILE (branch `research/work-twolift`).

For a seed `I` on three points and an admission of states `Adm` at the grade `1` reading only the
cells of grade at most `1`, holding at the labels of the two coatom types: the admitted layer at
grade `1` over the amalgam (`Seed.layerOne`), then the canonical layer at grade `2` over it
(`Seed.layerTwo`, the admitted field layer at `2` of the constant `True`), is legal below the full
grade (`Seed.isLegalBelowFullGrade_layerTwo`), carries the labels of the amalgam
(`Seed.exists_isLawful_layerTwo`), and is a completion below the full grade
(`Seed.oneCompletion`).  **Recognition at grade `1`** (`Seed.adm_of_isLawful_oneCompletion`): in
every lawful labelling with a cell of grade `1` of the first copy at `⊤`, the copies satisfy the
admission (availability gives a field cell at `(univ, 1)` at `⊤`, whose row reads an admitted
entry; `Scheme.exists_admitted_image_le`, the recognition of
`Scheme.exists_admitted_image` on the cells of grade at most the grade of the layer).

**h2 at top grade `1`** (`H2.exists_completion_recProp_one_of`): the shape of
`H2.exists_completion_recProp_one`, from donor raising (`H2.DonorRaisingV`) and owner lowering
(`FieldAdmission.OwnerLowering`) at the grade `1`, with the designated cells below the top read on
their cells of grade `1`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label CellScheme

/-- **Recognition at a reader, on the cells of grade at most `k`**: as
`Scheme.exists_admitted_image`, without asking every cell of `S` to have grade at most `k`; the
conclusion is read on the cells of grade at most `k`. -/
theorem exists_admitted_image_le {n k : ℕ} {S : Scheme.{u} n} {A : (Fin S.card → Label.{u}) → Prop}
    {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}
    (hA0 : A fun _ ↦ ⊥)
    {q : Fin (S.admittedFieldLayer k A hS).card → Label.{u}}
    (hq : (S.admittedFieldLayer k A hS).rows.IsLawfulBelow ((univ : Finset (Fin n)), k)
      (fun x ↦ q x))
    {x₀ : Fin S.card} (hx₀ : S.toCellScheme.grade x₀ = k) (hqx : q (Fin.castAdd _ x₀) = ⊤) :
    ∃ a, S.rows.IsLawful a ∧ A a ∧ ∃ σ : Label.{u} → Label.{u}, Monotone σ ∧ σ ⊥ = ⊥ ∧
      (∀ x, σ (visibilityReplace k k x) = visibilityReplace k k (σ x)) ∧
      ∀ e, S.toCellScheme.grade e ≤ k → q (Fin.castAdd _ e) = σ (a e) := by
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hq
  obtain ⟨t, ht⟩ := exists_gradedIndex_eq_admittedFieldLayer (hS := hS) hA0
  obtain ⟨u, hu, hle⟩ := havail (Fin.castAdd _ x₀) t ((mem_below _).mpr ht.le)
    (by rw [show (S.admittedFieldLayer k A hS).toCellScheme.scope t = univ from
          congrArg Prod.fst ht]
        exact subset_univ _)
    (by rw [show (S.admittedFieldLayer k A hS).toCellScheme.grade t = k from
          congrArg Prod.snd ht, appendFullCellsScheme_grade_castAdd, hx₀])
  rw [hqx, top_le_iff] at hle
  rw [ht] at hu
  obtain ⟨a, ha, hA, hrow⟩ := exists_admitted_row_admittedFieldLayer hu
  obtain ⟨g, σ, hw, he⟩ := hloc u ((mem_below _).mpr hu.le)
  have hgk : g k = ⊤ := by
    have h := he ⟨u, mem_below_gradedIndex _ u⟩
    simp only [hle, min_self] at h
    have h2 : (S.admittedFieldLayer k A hS).toCellScheme.grade u = k := congrArg Prod.snd hu
    rw [h2] at h
    exact top_le_iff.mp (h ▸ min_le_right _ _)
  refine ⟨a, (mem_catalogue.mp ha).1, hA, σ, hw.monotone, hw.map_bot,
    fun x ↦ hw.visibilityReplace_comm x k (by rw [hgk]; exact le_top) k le_rfl, fun e hge₀ ↦ ?_⟩
  have hd : Fin.castAdd _ e ∈ (S.admittedFieldLayer k A hS).toCellScheme.below
      ((S.admittedFieldLayer k A hS).toCellScheme.gradedIndex u) := by
    refine (mem_below _).mpr ?_
    rw [hu, appendFullCellsScheme_gradedIndex_castAdd]
    exact ⟨subset_univ _, hge₀⟩
  have h := he ⟨_, hd⟩
  change min (q (Fin.castAdd _ e)) (q u) =
    min (σ ((S.admittedFieldLayer k A hS).rows.row u ⟨_, hd⟩)) _ at h
  rw [hle, min_top_right] at h
  rw [h, hrow e hd]
  have hge : (S.admittedFieldLayer k A hS).toCellScheme.grade (Fin.castAdd _ e) ≤ k := by
    rw [appendFullCellsScheme_grade_castAdd]; exact hge₀
  have hg' : g ((S.admittedFieldLayer k A hS).toCellScheme.grade (Fin.castAdd _ e)) = ⊤ :=
    top_le_iff.mp (by rw [← hgk]; exact hw.antitone hge)
  exact min_eq_left (le_of_le_of_eq le_top hg'.symm)

end VaughtConjecture.Scheme

namespace VaughtConjecture.Seed

open Finset Label CellScheme StageType H2

variable {α : Ordinal.{u}} {I : Seed.{u} α 1}
variable {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}

/-! ### The layer at grade `2` -/

variable (I Adm) in
/-- **The layer at grade `2`** over the admitted layer at grade `1`. -/
noncomputable abbrev layerTwo : Scheme.{u} 3 :=
  (I.layerOne Adm).admittedFieldLayer 2 (fun _ ↦ True) not_univ_two_le_layerOne

theorem isWellFormed_layerOne : (I.layerOne Adm).IsWellFormed :=
  Scheme.isWellFormed_fieldLayerOn (hS := I.not_univ_le 1) (C := catOne I Adm)
    I.amalgam.isWellFormed one_pos (by omega)

theorem isConsistent_layerOne : (I.layerOne Adm).rows.IsConsistent :=
  Scheme.isConsistent_admittedFieldLayer (S := I.amalgam.toScheme) I.isConsistent

theorem exists_gradedIndex_layerOne_left :
    ∃ c, (I.layerOne Adm).toCellScheme.gradedIndex c = (univ.erase (Fin.last 2), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.last 2), 2)
    ⟨I.erase_last_mem_faces, two_pos, by decide⟩ (erase_ne_univ₁ _)
  exact ⟨oldOne Adm d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

theorem exists_gradedIndex_layerOne_right :
    ∃ c, (I.layerOne Adm).toCellScheme.gradedIndex c =
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    ⟨I.erase_castSucc_mem_faces, two_pos, by decide⟩ (erase_ne_univ₁ _)
  exact ⟨oldOne Adm d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

section Engine

variable (hS : IsStateAdmission (rootL (I := I)) rootR 1 I.left.rows.IsLawful
  I.right.rows.IsLawful Adm) (hloc : ReadsOne I Adm) (hst : Adm I.left.label I.right.label)

include hS hloc hst in
theorem cappedLift_layerTwo_left :
    (I.layerTwo Adm).rows.CappedLift (X := (univ.erase (Fin.last 2), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := not_univ_two_le_layerOne)
    isConsistent_layerOne trivial (erase_ne_univ₁ _) exists_gradedIndex_layerOne_left
    (cappedLift_layerOne_left hS hloc hst)
    (fun f hf ↦ by
      obtain ⟨W, hW, hWf, -⟩ := liftTwo_left hS hloc hst (isSelfVisible_bot 2)
        (a := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _) hf (fun d _ ↦ by simp)
      exact ⟨W, hW, hWf, trivial⟩)
    (fun _ hh _ _ _ ha _ _ hf hfa ↦ by
      obtain ⟨W, hW, hWf, hWa⟩ := liftTwo_left hS hloc hst hh (ha.isLawfulBelow _) hf hfa
      exact ⟨W, hW, hWf, fun d _ ↦ hWa d, trivial⟩)

include hS hloc hst in
theorem cappedLift_layerTwo_right :
    (I.layerTwo Adm).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := not_univ_two_le_layerOne)
    isConsistent_layerOne trivial (erase_ne_univ₁ _) exists_gradedIndex_layerOne_right
    (cappedLift_layerOne_right hS hloc hst)
    (fun f hf ↦ by
      obtain ⟨W, hW, hWf, -⟩ := liftTwo_right hS hloc hst (isSelfVisible_bot 2)
        (a := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _) hf (fun d _ ↦ by simp)
      exact ⟨W, hW, hWf, trivial⟩)
    (fun _ hh _ _ _ ha _ _ hf hfa ↦ by
      obtain ⟨W, hW, hWf, hWa⟩ := liftTwo_right hS hloc hst hh (ha.isLawfulBelow _) hf hfa
      exact ⟨W, hW, hWf, fun d _ ↦ hWa d, trivial⟩)

variable (I Adm) in
/-- The old cells of the admitted layer at grade `1` in the layer at grade `2`. -/
theorem isLowerEmbedding_layerTwo :
    (I.layerOne Adm).toCellScheme.IsLowerEmbedding (I.layerTwo Adm).toCellScheme
      (Fin.castAdd _) :=
  Scheme.isLowerEmbedding_castAdd (S := I.layerOne Adm) 2
    ((I.layerOne Adm).admittedCatalogue 2 (fun _ ↦ True)).card
    (fun i ↦ (I.layerOne Adm).fieldRowOn 2 ((I.layerOne Adm).admittedCatalogue 2 (fun _ ↦ True))
      (Scheme.entryOn _ i)) not_univ_two_le_layerOne

variable (I Adm) in
theorem isLowerEmbedding_layerOne :
    I.amalgam.toCellScheme.IsLowerEmbedding (I.layerOne Adm).toCellScheme (Fin.castAdd _) :=
  Scheme.isLowerEmbedding_castAdd (S := I.amalgam.toScheme) 1 (catOne I Adm).card
    (fun i ↦ I.amalgam.toScheme.fieldRowOn 1 (catOne I Adm) (Scheme.entryOn _ i)) (I.not_univ_le 1)

theorem comap_rows_layerTwo :
    (I.layerTwo Adm).rows.comap (isLowerEmbedding_layerTwo I Adm) = (I.layerOne Adm).rows :=
  Scheme.comap_rows_castAdd (S := I.layerOne Adm) (k := 2)
    (M := ((I.layerOne Adm).admittedCatalogue 2 (fun _ ↦ True)).card)
    (r := fun i ↦ (I.layerOne Adm).fieldRowOn 2
      ((I.layerOne Adm).admittedCatalogue 2 (fun _ ↦ True)) (Scheme.entryOn _ i))
    (h := not_univ_two_le_layerOne)

theorem comap_rows_layerOne :
    (I.layerOne Adm).rows.comap (isLowerEmbedding_layerOne I Adm) = I.amalgam.rows :=
  Scheme.comap_rows_castAdd (S := I.amalgam.toScheme) (k := 1) (M := (catOne I Adm).card)
    (r := fun i ↦ I.amalgam.toScheme.fieldRowOn 1 (catOne I Adm) (Scheme.entryOn _ i))
    (h := I.not_univ_le 1)

theorem isWellFormed_layerTwo : (I.layerTwo Adm).IsWellFormed :=
  Scheme.isWellFormed_fieldLayerOn (hS := not_univ_two_le_layerOne) isWellFormed_layerOne two_pos
    (by omega)

include hS hloc hst in
/-- **Bountifulness of the layer at grade `2`.** -/
theorem isBountiful_layerTwo : (I.layerTwo Adm).rows.IsBountiful := by
  have hemb := isLowerEmbedding_layerTwo I Adm
  have hlow := isLowerEmbedding_layerOne I Adm
  have hsp1 : (I.layerOne Adm).toCellScheme.IsSourcePrefix (I.layerTwo Adm).toCellScheme
      (Fin.castAdd _) ((univ : Finset (Fin 3)), 1) :=
    ⟨hemb, Scheme.appendFullCellsScheme_scope_castAdd _ _ _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below (fun h ↦ absurd h.2 (by omega)) hd⟩, rfl⟩⟩
  have hone (U : Finset (Fin 3)) (hU : (I.layerOne Adm).rows.CappedLift (X := (U, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩) :
      (I.layerTwo Adm).rows.CappedLift (X := (U, 1)) (Y := ((univ : Finset (Fin 3)), 1))
        ⟨subset_univ _, le_rfl⟩ := by
    refine (hsp1.cappedLift_iff _ le_rfl).mp ?_
    change ((I.layerTwo Adm).rows.comap hemb).CappedLift _
    rw [comap_rows_layerTwo]
    exact hU
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ 2 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  have hwf : (I.layerTwo Adm).IsWellFormed := isWellFormed_layerTwo
  have hfull (z : Fin 3) (hlift1 : (I.layerOne Adm).rows.CappedLift (X := (univ.erase z, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩)
      (hlift2 : (I.layerTwo Adm).rows.CappedLift (X := (univ.erase z, 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) (j : ℕ) (hj : j ≤ 2) :
      (I.layerTwo Adm).rows.CappedLift (X := (univ.erase z, j))
        (Y := ((univ : Finset (Fin 3)), j)) ⟨erase_subset _ _, le_rfl⟩ := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact hwf.isWellFormed.cappedLift _ (Or.inl rfl) _
    · exact hone _ hlift1
    · exact hlift2
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces (fun X Y hX hY hXY hYne ↦ ?_)
    (fun j hj ↦ hfull _ (cappedLift_layerOne_left hS hloc hst)
      (cappedLift_layerTwo_left hS hloc hst) j (hle _ j hj))
    (fun j hj ↦ hfull _ (cappedLift_layerOne_right hS hloc hst)
      (cappedLift_layerTwo_right hS hloc hst) j (hle _ j hj))
  have h : I.amalgam.toCellScheme.IsSourcePrefix (I.layerTwo Adm).toCellScheme
      (fun d ↦ Fin.castAdd _ (Fin.castAdd _ d)) Y := by
    refine ⟨hemb.comp hlow, fun t ↦
        (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _), fun d hd ↦ ?_⟩
    have hsc : (I.layerTwo Adm).toCellScheme.scope d ≠ univ := fun he ↦
      hYne (subset_antisymm (subset_univ _) (he ▸ hd.1))
    induction d using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hsc
    | left d =>
      induction d using Fin.addCases with
      | right i =>
        exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hsc
      | left a => exact ⟨a, rfl⟩
  refine h.cappedLift_of_isBountiful ?_ hX hY hXY le_rfl
  have hc : (I.layerTwo Adm).rows.comap h.isLowerEmbedding = I.amalgam.rows := by
    change (((I.layerTwo Adm).rows.comap hemb).comap hlow) = _
    rw [comap_rows_layerTwo, comap_rows_layerOne]
  rw [hc]
  exact I.isBountiful

include hS hloc hst in
/-- **Legality below the full grade of the layer at grade `2`.** -/
theorem isLegalBelowFullGrade_layerTwo : (I.layerTwo Adm).IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_layerTwo
  isCoded := Scheme.isCoded_admittedFieldLayer
    (Scheme.isCoded_admittedFieldLayer (S := I.amalgam.toScheme) I.amalgam.isCoded)
  isConsistent := Scheme.isConsistent_admittedFieldLayer isConsistent_layerOne
  isBountiful := isBountiful_layerTwo hS hloc hst
  grade_lt d := by
    induction d using Fin.addCases with
    | left e =>
      exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_lt
        ((layerOne_grade_le e).trans_lt (by omega))
    | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    have hj0 : 0 < j := hX.2.1
    by_cases hC : C = univ
    · subst hC
      rcases (show j = 1 ∨ j = 2 by simp only at hX2; omega) with rfl | rfl
      · obtain ⟨u, hu⟩ := Scheme.exists_gradedIndex_eq_admittedFieldLayer
          (S := I.amalgam.toScheme) (k := 1) (A := AdmA I Adm) (hS := I.not_univ_le 1) hS.bot
        exact ⟨Fin.castAdd _ u, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans hu⟩
      · exact Scheme.exists_gradedIndex_eq_admittedFieldLayer trivial
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨Fin.castAdd _ (Fin.castAdd _ d),
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
          ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd)⟩

theorem mem_below_layerTwo (d : Fin (I.layerTwo Adm).card) :
    d ∈ (I.layerTwo Adm).toCellScheme.below ((univ : Finset (Fin 3)), 2) := by
  refine ⟨subset_univ _, ?_⟩
  induction d using Fin.addCases with
  | left e =>
    exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_le (layerOne_grade_le e)
  | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

include hS hloc hst in
/-- **A lawful labelling of the layer at grade `2` extending the labels of the amalgam.** -/
theorem exists_isLawful_layerTwo :
    ∃ q : Fin (I.layerTwo Adm).card → Label.{u}, (I.layerTwo Adm).rows.IsLawful q ∧
      ∀ d, q (Fin.castAdd _ (oldOne Adm d)) = I.amalgam.label d := by
  have hAl : AdmA I Adm I.amalgam.label := by
    change Adm (fun z ↦ I.amalgam.label (StageType.faceCell I.restrictFace_left z))
      (fun z ↦ I.amalgam.label (StageType.faceCell I.restrictFace_right z))
    simpa only [StageType.label_faceCell] using hst
  obtain ⟨v, hv, hvp⟩ := Scheme.exists_lift_bot_admittedFieldLayer (S := I.amalgam.toScheme)
    (k := 1) (A := AdmA I Adm) (hS := I.not_univ_le 1) (I.amalgam.isLawful.isLawfulBelow _)
    (admA_code hS hloc hAl)
  set W1 : Fin (I.layerOne Adm).card → Label.{u} :=
    Fin.addCases (motive := fun _ ↦ Label.{u}) (fun d ↦ I.amalgam.label d)
      (fun i ↦ v (Fin.natAdd _ i)) with hW1_def
  have hW1old (d : Fin I.amalgam.card) : W1 (oldOne Adm d) = I.amalgam.label d :=
    Fin.addCases_left d
  have hW1v {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1)) :
      W1 x = v x := by
    induction x using Fin.addCases with
    | left d =>
      refine (hW1old d).trans (hvp d ?_).symm
      exact (castAdd_mem_below_layerOne_iff (Adm := Adm)).mp hx |>.2
    | right i => exact Fin.addCases_right i
  have hW1 : (I.layerOne Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2)
      (fun x ↦ W1 x) := by
    refine Rows.IsLawfulBelow.glue₃ (U := (univ.erase (Fin.last 2), 2))
      (V := ((univ : Finset (Fin 3)), 1)) (W := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      ?_ ?_ ?_ (fun x _ ↦ layerOne_cover x)
    · refine (layerOne_left_iff 2).mpr ?_
      convert I.left.isLawful.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
      exact funext fun z ↦ (hW1old _).trans (StageType.label_faceCell _ _)
    · convert hv using 1
      exact funext fun x ↦ hW1v x.2
    · refine (layerOne_right_iff 2).mpr ?_
      convert I.right.isLawful.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
      exact funext fun z ↦ (hW1old _).trans (StageType.label_faceCell _ _)
  obtain ⟨v2, hv2, hv2p⟩ := Scheme.exists_lift_bot_admittedFieldLayer (S := I.layerOne Adm)
    (k := 2) (A := fun _ ↦ True) (hS := not_univ_two_le_layerOne) hW1 trivial
  exact ⟨v2, CellScheme.Rows.isLawful_of_isLawfulBelow_of_forall hv2 mem_below_layerTwo,
    fun d ↦ (hv2p _ (layerOne_grade_le _)).trans (hW1old d)⟩

theorem exists_old_layerTwo {d : Fin (I.layerTwo Adm).card}
    (hd : (I.layerTwo Adm).toCellScheme.scope d ≠ univ) :
    ∃ a, Fin.castAdd _ (oldOne Adm a) = d := by
  induction d using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hd
  | left d =>
    induction d using Fin.addCases with
    | right i =>
      exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hd
    | left a => exact ⟨a, rfl⟩

/-- **The completion at top grade `1`**: the layer at grade `2` over the admitted layer at grade
`1`, with a lawful labelling extending the labels of the amalgam. -/
noncomputable def oneCompletion : CompletionBelowFullGrade I where
  scheme := I.layerTwo Adm
  embed := (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)
  isLowerEmbedding := (isLowerEmbedding_layerTwo I Adm).comp (isLowerEmbedding_layerOne I Adm)
  scope_embed d := (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)
  comap_rows := by
    change (((I.layerTwo Adm).rows.comap (isLowerEmbedding_layerTwo I Adm)).comap
      (isLowerEmbedding_layerOne I Adm)) = _
    rw [comap_rows_layerTwo, comap_rows_layerOne]
  mem_range_embed z hz := by
    obtain ⟨a, rfl⟩ := exists_old_layerTwo hz
    exact ⟨a, rfl⟩
  faces_eq := rfl
  isLegalBelowFullGrade := isLegalBelowFullGrade_layerTwo hS hloc hst
  label := Classical.choose (exists_isLawful_layerTwo hS hloc hst)
  isLawful := (Classical.choose_spec (exists_isLawful_layerTwo hS hloc hst)).1
  label_embed d := (Classical.choose_spec (exists_isLawful_layerTwo hS hloc hst)).2 d

omit hS hloc hst in
include hS hloc in
/-- **Recognition in the layer at grade `2`**: in every lawful labelling with a cell of grade `1`
of the first copy at `⊤`, the copies satisfy the admission. -/
theorem adm_of_isLawful_layerTwo {o : Fin I.left.card} (ho : I.left.toCellScheme.grade o = 1)
    {q : Fin (I.layerTwo Adm).card → Label.{u}} (hq : (I.layerTwo Adm).rows.IsLawful q)
    (hqo : q (Fin.castAdd _ (oldOne Adm (StageType.faceCell I.restrictFace_left o))) = ⊤) :
    Adm (fun z ↦ q (Fin.castAdd _ (oldOne Adm (StageType.faceCell I.restrictFace_left z))))
      (fun z ↦ q (Fin.castAdd _ (oldOne Adm (StageType.faceCell I.restrictFace_right z)))) := by
  have hq1 : (I.layerOne Adm).rows.IsLawful (fun x ↦ q (Fin.castAdd _ x)) :=
    comap_rows_layerTwo (I := I) (Adm := Adm) ▸ hq.comap (isLowerEmbedding_layerTwo I Adm)
  obtain ⟨a, -, hAa, σ, hσ, hσ0, hc, hold⟩ := Scheme.exists_admitted_image_le
    (S := I.amalgam.toScheme) (k := 1) (A := AdmA I Adm) (hS := I.not_univ_le 1)
    (q := fun x ↦ q (Fin.castAdd _ x)) hS.bot (hq1.isLawfulBelow _)
    (x₀ := StageType.faceCell I.restrictFace_left o) ((StageType.grade_faceCell _ o).trans ho) hqo
  refine hloc (fun z hz ↦ ?_) (fun z hz ↦ ?_) (hS.comp hσ hσ0 hc hAa)
  · exact (hold _ ((StageType.grade_faceCell _ z).trans_le hz)).symm
  · exact (hold _ ((StageType.grade_faceCell _ z).trans_le hz)).symm

end Engine

end VaughtConjecture.Seed

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission Seed

variable {α : Ordinal.{u}}

/-- **The state-level provisions at grade `1`, refined form**: from the refined donor raising
(`H2.DonorRaisingV`) and owner lowering at the grade `1` (both hypotheses), as
`H2.stateAdmission_two`. -/
theorem stateAdmission_oneV {t' : StageType.{u} α 2} {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hDR : DonorRaisingV (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) Lo Tops)
    (hOL : OwnerLowering (StageType.faceCell hp) (StageType.faceCell htbp) o r 1
      t'.rows.IsLawful tb.rows.IsLawful) :
    IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful (SelfLowG o r 1 Lo Tops) := by
  refine selfLow_isStateAdmissionV (rootTops hp l) (fun f hf ↦ ?_) (fun f hf a ha ↦ ?_) hDR hOL
  · have := hf.orderly o
    rwa [hs.grade_owner] at this
  · exact hs.frontier_le hf ((StageType.label_faceCell hp a).trans ha.1) ha.2

/-- **h2 at two points, top grade `1`, from the provisions at grade `1`**: the conclusion of
`H2.exists_completion_recProp_one`, from refined donor raising at the grade `1` for the designated
cells below the top of grade `1`, and owner lowering at the grade `1` (both hypotheses).  The
completion is `Seed.oneCompletion`: the admitted layer at grade `1` over the amalgam, on the
clause read on the copies, then the layer at grade `2`. -/
theorem exists_completion_recProp_one_of {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)}
    (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ 1 ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb)
    (hDR : DonorRaisingV (StageType.faceCell hp) (StageType.faceCell htbp) 1 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1) Tops)
    (hOL : OwnerLowering (StageType.faceCell hp) (StageType.faceCell htbp) o r 1
      t'.rows.IsLawful tb.rows.IsLawful) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r 1 Lo Tops := by
  set Lo1 := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ 1 with hLo1
  have hS := stateAdmission_oneV hs hp htbp (Lo := Lo1) hDR hOL
  have hr1 : t'.toCellScheme.grade r ≤ 1 := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hloc : ReadsOne (Seed.ofCoatoms hleg htbleg hp htbp) (SelfLowG o r 1 Lo1 Tops) := by
    intro L L' R R' hL hR h t ht hlt
    have hRt : R' t = R t := (hR t (hTops t ht).2.1).symm
    have hsup : Lo1.sup R' = Lo1.sup R :=
      Finset.sup_congr rfl fun x hx ↦ (hR x (Finset.mem_filter.mp hx).2).symm
    have hfr : frontierAt o r 1 L' = frontierAt o r 1 L := by
      unfold frontierAt
      rw [← hL o hs.grade_owner.le, ← hL r hr1]
    have h' := h t ht ((congrArg (visibilityReplace 1 1) hsup.symm).trans_lt (hlt.trans_eq hRt))
    exact (le_of_eq hfr).trans (h'.trans_eq hRt.symm)
  have hst : SelfLowG o r 1 Lo1 Tops t'.label tb.label := fun t ht _ ↦ (hTops t ht).1.symm ▸ le_top
  refine ⟨oneCompletion hS hloc hst, fun q hq hqo t ht hlt ↦ ?_⟩
  have hadm := adm_of_isLawful_layerTwo hS hloc (o := o) hs.grade_owner hq hqo
  refine hadm t ht (lt_of_le_of_lt ?_ hlt)
  exact monotone_visibilityReplace le_rfl (Finset.sup_mono (Finset.filter_subset _ _))

end VaughtConjecture.H2
