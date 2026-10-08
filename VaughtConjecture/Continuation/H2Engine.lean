/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2ArityOne
import VaughtConjecture.Continuation.StableRecoveryDonorLive

/-!
# The admitted completion at the arity one for an admission of states (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`; the two-coatom lift on the lower layer
(`Seed.HasTwoCoatomLift`, the open hypothesis of the (R4) lane) is a hypothesis.

For a seed `I` on three points and a predicate `A` on labellings of the canonical lower layer
(`Seed.lowerFieldLayer`), the admitted layer at grade `2` (`Seed.admLayer I A`) is legal below the
full grade from the two coatom lifts (`Seed.isLegalBelowFullGrade_admLayer`; the assembly of
`Seed.isLegalBelowFullGrade_donorLayer`, for any `A`).  For an admission of states `Adm` (pairs of
faces sharing the common face, `H2.IsStateAdmission`), read on the copies (`Seed.AdmL`), the lift
provisions of `Scheme.cappedLift_admittedFieldLayer` follow from the state-level provisions, the
gluing `Seed.exists_isLawful_lower_two` (cap `⊥`) and the two-coatom lift (positive caps).
-/

universe u

namespace VaughtConjecture.Seed

open Finset Label CellScheme StageType H2

variable {α : Ordinal.{u}} {I : Seed.{u} α 1}

/-! ### The common face -/

private theorem hxyH : (Fin.last 2 : Fin 3) ≠ Fin.castSucc (Fin.last 1) := by decide
private theorem hxH : (Fin.last 2 : Fin 3) ≠ 0 := by decide
private theorem hyH : (Fin.castSucc (Fin.last 1) : Fin 3) ≠ 0 := by decide

/-- The cells of the common face, as cells of the context type. -/
noncomputable abbrev rootL (x : Fin I.face.card) : Fin I.left.card :=
  StageType.faceCell I.restrictFace_face_left x

/-- The cells of the common face, as cells of the donor type. -/
noncomputable abbrev rootR (x : Fin I.face.card) : Fin I.right.card :=
  StageType.faceCell I.restrictFace_face_right x

/-- The copies of a cell of the common face through either coatom are one cell. -/
theorem faceCell_rootL (x : Fin I.face.card) :
    StageType.faceCell I.restrictFace_left (rootL x) =
      StageType.faceCell I.restrictFace_right (rootR x) :=
  StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right I.restrictFace_face_left
    I.restrictFace_face_right x

/-- **A cell on both coatoms is a cell of the common face.** -/
theorem exists_root_of_eq {zT : Fin I.left.card} {zD : Fin I.right.card}
    (h : StageType.faceCell I.restrictFace_left zT = StageType.faceCell I.restrictFace_right zD) :
    ∃ x, zT = rootL x ∧ zD = rootR x := by
  have hs := congrArg (fun d ↦ I.amalgam.toCellScheme.scope d) h
  simp only [StageType.scope_faceCell] at hs
  have hvis : zT ∈ I.left.toScheme.visibleCells (Coatom.face 1) := by
    refine Scheme.mem_visibleCells.mpr fun y hy ↦ ?_
    have hm : Coatom.left 1 y ∈ (I.right.toCellScheme.scope zD).map (Coatom.right 1) :=
      hs ▸ mem_map_of_mem _ (mem_coe.mp hy)
    obtain ⟨x, -, hx⟩ := mem_map.mp hm
    have key : ∀ x y : Fin 2, Coatom.right 1 x = Coatom.left 1 y → y = 0 := by decide
    have hy0 : y = 0 := key x y hx
    exact ⟨0, by rw [hy0]; rfl⟩
  obtain ⟨x, rfl⟩ := Scheme.exists_faceCell_eq
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_face_left) hvis
  refine ⟨x, rfl, ?_⟩
  have e : StageType.faceCell I.restrictFace_right zD =
      StageType.faceCell I.restrictFace_right (rootR x) := h.symm.trans (faceCell_rootL x)
  exact faceCell_injective' I.restrictFace_right e

/-- Root agreement from agreement at the cells of the common face. -/
theorem rootAgree_of {sT : Fin I.left.card → Label.{u}} {sD : Fin I.right.card → Label.{u}}
    (h : ∀ x, sT (rootL x) = sD (rootR x)) : I.RootAgree sT sD := by
  intro zT zD hz
  obtain ⟨x, rfl, rfl⟩ := exists_root_of_eq hz
  exact h x

/-- Agreement at the cells of the common face from root agreement. -/
theorem root_of_rootAgree {sT : Fin I.left.card → Label.{u}} {sD : Fin I.right.card → Label.{u}}
    (h : I.RootAgree sT sD) (x : Fin I.face.card) : sT (rootL x) = sD (rootR x) :=
  h _ _ (faceCell_rootL x)

/-! ### The admitted layer for any predicate -/

variable {A : (Fin I.lowerFieldLayer.card → Label.{u}) → Prop}

variable (I A) in
/-- **The admitted layer** at the grade `2` over the canonical lower layer. -/
noncomputable abbrev admLayer : Scheme.{u} 3 :=
  I.lowerFieldLayer.admittedFieldLayer 2 A I.not_univ_two_le_lowerFieldLayer

private theorem erase_ne_univH (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

private theorem exists_gradedIndex_left_twoH :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c = (univ.erase (Fin.last 2), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.last 2), 2)
    ⟨I.erase_last_mem_faces, two_pos, by decide⟩ (erase_ne_univH _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

private theorem exists_gradedIndex_right_twoH :
    ∃ c, I.lowerFieldLayer.toCellScheme.gradedIndex c =
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    ⟨I.erase_castSucc_mem_faces, two_pos, by decide⟩ (erase_ne_univH _)
  exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

/-- **Bountifulness of the admitted layer**, from the two coatom lifts at grade `2`. -/
theorem isBountiful_admLayer
    (hL : (I.admLayer A).rows.CappedLift (X := (univ.erase (Fin.last 2), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩)
    (hR : (I.admLayer A).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) :
    (I.admLayer A).rows.IsBountiful := by
  have hemb := Scheme.isLowerEmbedding_castAdd (S := I.lowerFieldLayer) 2
    (I.lowerFieldLayer.admittedCatalogue 2 A).card
    (fun i ↦ I.lowerFieldLayer.fieldRowOn 2 (I.lowerFieldLayer.admittedCatalogue 2 A)
      (Scheme.entryOn _ i)) I.not_univ_two_le_lowerFieldLayer
  have hlow := Scheme.isLowerEmbedding_fieldLayer I.amalgam.toScheme 1 (I.not_univ_le 1)
  have e1 : (I.admLayer A).rows.comap hemb = I.lowerFieldLayer.rows :=
    Scheme.comap_rows_castAdd (S := I.lowerFieldLayer) (k := 2)
      (M := (I.lowerFieldLayer.admittedCatalogue 2 A).card)
      (r := fun i ↦ I.lowerFieldLayer.fieldRowOn 2
        (I.lowerFieldLayer.admittedCatalogue 2 A) (Scheme.entryOn _ i))
      (h := I.not_univ_two_le_lowerFieldLayer)
  have e2 : I.lowerFieldLayer.rows.comap hlow = I.amalgam.rows := Scheme.comap_rows_fieldLayer
  have hsp1 : I.lowerFieldLayer.toCellScheme.IsSourcePrefix (I.admLayer A).toCellScheme
      (Fin.castAdd _) ((univ : Finset (Fin 3)), 1) :=
    ⟨hemb, Scheme.appendFullCellsScheme_scope_castAdd _ _ _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below (fun h ↦ absurd h.2 (by omega)) hd⟩, rfl⟩⟩
  have hone (U : Finset (Fin 3)) (hU : I.lowerFieldLayer.rows.CappedLift (X := (U, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩) :
      (I.admLayer A).rows.CappedLift (X := (U, 1)) (Y := ((univ : Finset (Fin 3)), 1))
        ⟨subset_univ _, le_rfl⟩ := by
    refine (hsp1.cappedLift_iff _ le_rfl).mp ?_
    change ((I.admLayer A).rows.comap hemb).CappedLift _
    rw [e1]
    exact hU
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ 2 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  have hwf : (I.admLayer A).IsWellFormed :=
    Scheme.isWellFormed_fieldLayerOn (hS := I.not_univ_two_le_lowerFieldLayer)
      I.isWellFormed_lowerFieldLayer two_pos (by omega)
  have hfull (z : Fin 3) (hlift1 : I.lowerFieldLayer.rows.CappedLift (X := (univ.erase z, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩)
      (hlift2 : (I.admLayer A).rows.CappedLift (X := (univ.erase z, 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) (j : ℕ) (hj : j ≤ 2) :
      (I.admLayer A).rows.CappedLift (X := (univ.erase z, j)) (Y := ((univ : Finset (Fin 3)), j))
        ⟨erase_subset _ _, le_rfl⟩ := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact hwf.isWellFormed.cappedLift _ (Or.inl rfl) _
    · exact hone _ hlift1
    · exact hlift2
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces (fun X Y hX hY hXY hYne ↦ ?_)
    (fun j hj ↦ hfull _ (I.cappedLift_lowerFieldLayer hxyH hxH hyH) hL j (hle _ j hj))
    (fun j hj ↦ hfull _ (I.cappedLift_lowerFieldLayer hxyH.symm hyH hxH) hR j (hle _ j hj))
  have h : I.amalgam.toCellScheme.IsSourcePrefix (I.admLayer A).toCellScheme
      (fun d ↦ Fin.castAdd _ (Fin.castAdd _ d)) Y := by
    refine ⟨hemb.comp hlow, fun t ↦
        (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _), fun d hd ↦ ?_⟩
    have hsc : (I.admLayer A).toCellScheme.scope d ≠ univ := fun he ↦
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
  have hc : (I.admLayer A).rows.comap h.isLowerEmbedding = I.amalgam.rows := by
    change (((I.admLayer A).rows.comap hemb).comap hlow) = _
    rw [e1, e2]
  rw [hc]
  exact I.isBountiful

/-- **Legality below the full grade of the admitted layer**, from the two coatom lifts. -/
theorem isLegalBelowFullGrade_admLayer (hA0 : A fun _ ↦ ⊥)
    (hL : (I.admLayer A).rows.CappedLift (X := (univ.erase (Fin.last 2), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩)
    (hR : (I.admLayer A).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) :
    (I.admLayer A).IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_fieldLayerOn (hS := I.not_univ_two_le_lowerFieldLayer)
    I.isWellFormed_lowerFieldLayer two_pos (by omega)
  isCoded := Scheme.isCoded_admittedFieldLayer (Scheme.isCoded_fieldLayer I.amalgam.isCoded)
  isConsistent := Scheme.isConsistent_admittedFieldLayer I.isConsistent_lowerFieldLayer
  isBountiful := isBountiful_admLayer hL hR
  grade_lt d := by
    induction d using Fin.addCases with
    | left e =>
      exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_lt
        ((I.lowerFieldLayer_grade_le e).trans_lt (by omega))
    | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    have hj0 : 0 < j := hX.2.1
    by_cases hC : C = univ
    · subst hC
      rcases (show j = 1 ∨ j = 2 by simp only at hX2; omega) with rfl | rfl
      · obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
          (S := I.amalgam.toScheme) (k := 1) (p := fun _ ↦ ⊥)
          (CellScheme.Rows.isLawfulBelow_const_bot _))
        exact ⟨Fin.castAdd _ (Fin.natAdd _ i),
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
            (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)⟩
      · exact Scheme.exists_gradedIndex_eq_admittedFieldLayer hA0
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨Fin.castAdd _ (Fin.castAdd _ d),
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
          ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd)⟩

/-! ### An admission of states, read on the copies -/

variable {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}

variable (I Adm) in
/-- **The admission on labellings of the lower layer**: the copies of the two coatom types. -/
def AdmL (e : Fin I.lowerFieldLayer.card → Label.{u}) : Prop :=
  Adm (fun z ↦ e (I.privCell z)) (fun z ↦ e (I.donCell z))

variable (I) in
/-- The labels of the two coatom types agree at the cells of the common face. -/
theorem label_rootL (x : Fin I.face.card) : I.left.label (rootL x) = I.right.label (rootR x) :=
  (StageType.label_faceCell I.restrictFace_face_left x).trans
    (StageType.label_faceCell I.restrictFace_face_right x).symm

/-- The copies of a cell of the common face are one cell of the lower layer. -/
theorem privCell_rootL (x : Fin I.face.card) : I.privCell (rootL x) = I.donCell (rootR x) :=
  congrArg (Fin.castAdd _) (faceCell_rootL x)

/-- **The admission passes to the orbit code.** -/
theorem admL_code
    (hS : IsStateAdmission (rootL (I := I)) rootR 2 I.left.rows.IsLawful I.right.rows.IsLawful
      Adm) {W : Fin I.lowerFieldLayer.card → Label.{u}} (hW : AdmL I Adm W) :
    AdmL I Adm (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsp : I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W = W :=
    funext fun d ↦ CellScheme.splice_of_le (I.lowerFieldLayer_grade_le d)
  rw [hsp]
  have hw := isWitness_orbitMap 2 W
  exact hS.comp hw.monotone hw.map_bot (fun x ↦ hw.visibilityReplace_comm x 2
    (by rw [stepSuppressor_of_le le_rfl]; exact le_top) 2 le_rfl) hW

section Provisions

variable (hS : IsStateAdmission (rootL (I := I)) rootR 2 I.left.rows.IsLawful
  I.right.rows.IsLawful Adm)
include hS

/-- **The provision at the cap `⊥` from the context coatom.** -/
theorem botProvisionL_leftH (hst : Adm I.left.label I.right.label)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      AdmL I Adm (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsT := isLawful_privOf hf
  obtain ⟨sD, hsD, hroot, -, hadm⟩ := hS.context (isSelfVisible_bot 2) I.left.isLawful
    I.right.isLawful (label_rootL I) hst hsT (fun _ ↦ by simp)
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_lower_two hsT hsD
    (rootAgree_of fun x ↦ (hroot x).symm)
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, admL_code hS ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
      (Coatom.univ_map_left (m := 1)) hd
    exact hWT z
  · change Adm (fun z ↦ W (I.privCell z)) (fun z ↦ W (I.donCell z))
    rw [funext hWT, funext hWD]
    exact hadm

/-- **The provision at the cap `⊥` from the donor coatom.** -/
theorem botProvisionL_rightH (hst : Adm I.left.label I.right.label)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d)) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      AdmL I Adm (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsD := isLawful_donOf hf
  obtain ⟨sT, hsT, hroot, -, hadm⟩ := hS.donor (isSelfVisible_bot 2) I.left.isLawful
    I.right.isLawful (label_rootL I) hst hsD (fun _ ↦ by simp)
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_lower_two hsT hsD (rootAgree_of hroot)
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, admL_code hS ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_right
      (Coatom.univ_map_right (m := 1)) hd
    exact hWD z
  · change Adm (fun z ↦ W (I.privCell z)) (fun z ↦ W (I.donCell z))
    rw [funext hWT, funext hWD]
    exact hadm

/-- **The provision at a positive cap from the context coatom**, through the two-coatom lift. -/
theorem capProvisionL_leftH (htwo : I.HasTwoCoatomLift) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    (hbh : ⊥ < h) {a : Fin I.lowerFieldLayer.card → Label.{u}}
    (ha : I.lowerFieldLayer.rows.IsLawful a) (hA : AdmL I Adm a)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d))
    (hfa : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      (∀ d, I.lowerFieldLayer.toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      AdmL I Adm (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsT := isLawful_privOf hf
  have hL := isLawful_privOf (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hR := isLawful_donOf (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2))
  have hy (x : Fin I.face.card) : a (I.privCell (rootL x)) = a (I.donCell (rootR x)) := by
    rw [privCell_rootL]
  have hagT (z : Fin I.left.card) : min (f (I.privCell z)) h = min (a (I.privCell z)) h :=
    hfa _ (privCell_mem_below z)
  obtain ⟨sD, hsD, hroot, hsDa, hadm⟩ := hS.context hh hL hR hy hA hsT hagT
  obtain ⟨W, hW, hWT, hWD, hWa⟩ := htwo h hh hbh _ sD hsT hsD
    (rootAgree_of fun x ↦ (hroot x).symm) a ha hagT hsDa
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ hWa d, admL_code hS ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_left
      (Coatom.univ_map_left (m := 1)) hd
    exact hWT z
  · change Adm (fun z ↦ W (I.privCell z)) (fun z ↦ W (I.donCell z))
    rw [funext hWT, funext hWD]
    exact hadm

/-- **The provision at a positive cap from the donor coatom**, through the two-coatom lift. -/
theorem capProvisionL_rightH (htwo : I.HasTwoCoatomLift) {h : Label.{u}} (hh : IsSelfVisible 2 h)
    (hbh : ⊥ < h) {a : Fin I.lowerFieldLayer.card → Label.{u}}
    (ha : I.lowerFieldLayer.rows.IsLawful a) (hA : AdmL I Adm a)
    {f : Fin I.lowerFieldLayer.card → Label.{u}}
    (hf : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      (∀ d, I.lowerFieldLayer.toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      AdmL I Adm (orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsD := isLawful_donOf hf
  have hL := isLawful_privOf (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hR := isLawful_donOf (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2))
  have hy (x : Fin I.face.card) : a (I.privCell (rootL x)) = a (I.donCell (rootR x)) := by
    rw [privCell_rootL]
  have hagD (z : Fin I.right.card) : min (f (I.donCell z)) h = min (a (I.donCell z)) h :=
    hfa _ (donCell_mem_below z)
  obtain ⟨sT, hsT, hroot, hsTa, hadm⟩ := hS.donor hh hL hR hy hA hsD hagD
  obtain ⟨W, hW, hWT, hWD, hWa⟩ := htwo h hh hbh sT _ hsT hsD (rootAgree_of hroot) a ha hsTa hagD
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, fun d _ ↦ hWa d, admL_code hS ?_⟩
  · obtain ⟨z, rfl⟩ := exists_faceCell_of_mem_below I.restrictFace_right
      (Coatom.univ_map_right (m := 1)) hd
    exact hWD z
  · change Adm (fun z ↦ W (I.privCell z)) (fun z ↦ W (I.donCell z))
    rw [funext hWT, funext hWD]
    exact hadm

end Provisions

/-! ### The admitted completion -/

section Completion

variable (hS : IsStateAdmission (rootL (I := I)) rootR 2 I.left.rows.IsLawful
  I.right.rows.IsLawful Adm) (hst : Adm I.left.label I.right.label) (htwo : I.HasTwoCoatomLift)

include hS hst htwo in
/-- **Legality below the full grade of the admitted layer of an admission of states.** -/
theorem isLegalBelowFullGrade_admLayerL : (I.admLayer (AdmL I Adm)).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_admLayer hS.bot
    (Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_lowerFieldLayer)
      I.isConsistent_lowerFieldLayer hS.bot (erase_ne_univH _) exists_gradedIndex_left_twoH
      (I.cappedLift_lowerFieldLayer hxyH hxH hyH) (fun _ hf ↦ botProvisionL_leftH hS hst hf)
      (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionL_leftH hS htwo hh hbh ha hA hf hfa))
    (Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_lowerFieldLayer)
      I.isConsistent_lowerFieldLayer hS.bot (erase_ne_univH _) exists_gradedIndex_right_twoH
      (I.cappedLift_lowerFieldLayer hxyH.symm hyH hxH) (fun _ hf ↦ botProvisionL_rightH hS hst hf)
      (fun _ hh _ hbh _ ha hA _ hf hfa ↦ capProvisionL_rightH hS htwo hh hbh ha hA hf hfa))

/-- Every cell of the admitted layer lies below `(univ, 2)`. -/
theorem mem_below_admLayer (d : Fin (I.admLayer A).card) :
    d ∈ (I.admLayer A).toCellScheme.below ((univ : Finset (Fin 3)), 2) := by
  refine ⟨subset_univ _, ?_⟩
  induction d using Fin.addCases with
  | left e =>
    refine (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ e).trans_le ?_
    exact I.lowerFieldLayer_grade_le e
  | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

include hS hst in
/-- **A lawful labelling of the admitted layer extending the glued labels.** -/
theorem exists_isLawful_admLayerL :
    ∃ q : Fin (I.admLayer (AdmL I Adm)).card → Label.{u},
      (I.admLayer (AdmL I Adm)).rows.IsLawful q ∧
      ∀ d, q (Fin.castAdd _ (Fin.castAdd _ d)) = I.amalgam.label d := by
  obtain ⟨r, hr, hrp⟩ := Scheme.exists_isLawful_fieldLayer (S := I.amalgam.toScheme) (k := 1)
    (hS := I.not_univ_le 1) I.amalgam.isLawful
  have hAr : AdmL I Adm r := by
    change Adm (fun z ↦ r (I.privCell z)) (fun z ↦ r (I.donCell z))
    have e1 : (fun z ↦ r (I.privCell z)) = I.left.label :=
      funext fun z ↦ (hrp _).trans (StageType.label_faceCell _ z)
    have e2 : (fun z ↦ r (I.donCell z)) = I.right.label :=
      funext fun z ↦ (hrp _).trans (StageType.label_faceCell _ z)
    rw [e1, e2]
    exact hst
  have hb : orbitCode 2 (I.lowerFieldLayer.toCellScheme.splice 2 (fun _ ↦ ⊥) r) ∈
      I.lowerFieldLayer.admittedCatalogue 2 (AdmL I Adm) :=
    Scheme.mem_admittedCatalogue.mpr ⟨Scheme.orbitCode_splice_bot_mem_catalogue
      (hr.isLawfulBelow _), admL_code hS hAr⟩
  obtain ⟨q, hq, hqp⟩ := Scheme.exists_isLawfulBelow_fieldLayerOn
    (hS := I.not_univ_two_le_lowerFieldLayer) Scheme.admittedCatalogue_subset hb
  refine ⟨fun d ↦ q ⟨d, mem_below_admLayer d⟩,
    CellScheme.Rows.isLawful_of_isLawfulBelow_of_forall (X := ((univ : Finset (Fin 3)), 2))
      hq mem_below_admLayer, fun d ↦ ?_⟩
  exact (hqp _ (I.lowerFieldLayer_grade_le _)).trans (hrp d)

theorem exists_old_eq_admLayer {d : Fin (I.admLayer A).card}
    (hd : (I.admLayer A).toCellScheme.scope d ≠ univ) :
    ∃ a, Fin.castAdd _ (Fin.castAdd _ a) = d := by
  induction d using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hd
  | left d =>
    induction d using Fin.addCases with
    | right i =>
      exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hd
    | left a => exact ⟨a, rfl⟩

/-- **The admitted completion of an admission of states.** -/
noncomputable def admCompletion : CompletionBelowFullGrade I where
  scheme := I.admLayer (AdmL I Adm)
  embed := (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)
  isLowerEmbedding := (Scheme.isLowerEmbedding_castAdd (S := I.lowerFieldLayer) 2 _
      (fun i ↦ I.lowerFieldLayer.fieldRowOn 2 _ (Scheme.entryOn _ i))
      I.not_univ_two_le_lowerFieldLayer).comp
    (Scheme.isLowerEmbedding_fieldLayer I.amalgam.toScheme 1 (I.not_univ_le 1))
  scope_embed d := (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)
  comap_rows := by
    have hle2 := Scheme.isLowerEmbedding_castAdd (S := I.lowerFieldLayer) 2 _
      (fun i ↦ I.lowerFieldLayer.fieldRowOn 2
        (I.lowerFieldLayer.admittedCatalogue 2 (AdmL I Adm)) (Scheme.entryOn _ i))
      I.not_univ_two_le_lowerFieldLayer
    have hle1 := Scheme.isLowerEmbedding_fieldLayer I.amalgam.toScheme 1 (I.not_univ_le 1)
    have e1 : (I.admLayer (AdmL I Adm)).rows.comap hle2 = I.lowerFieldLayer.rows :=
      Scheme.comap_rows_castAdd (S := I.lowerFieldLayer) (k := 2)
        (M := (I.lowerFieldLayer.admittedCatalogue 2 (AdmL I Adm)).card)
        (r := fun i ↦ I.lowerFieldLayer.fieldRowOn 2
          (I.lowerFieldLayer.admittedCatalogue 2 (AdmL I Adm)) (Scheme.entryOn _ i))
        (h := I.not_univ_two_le_lowerFieldLayer)
    have e2 : I.lowerFieldLayer.rows.comap hle1 = I.amalgam.rows := Scheme.comap_rows_fieldLayer
    change ((I.admLayer (AdmL I Adm)).rows.comap hle2).comap hle1 = _
    rw [e1, e2]
  mem_range_embed z hz := by
    obtain ⟨a, rfl⟩ := exists_old_eq_admLayer hz
    exact ⟨a, rfl⟩
  faces_eq := rfl
  isLegalBelowFullGrade := isLegalBelowFullGrade_admLayerL hS hst htwo
  label := Classical.choose (exists_isLawful_admLayerL hS hst)
  isLawful := (Classical.choose_spec (exists_isLawful_admLayerL hS hst)).1
  label_embed d := (Classical.choose_spec (exists_isLawful_admLayerL hS hst)).2 d

/-- **Recognition in the admitted completion**: in every lawful labelling with an old cell of
grade `2` of the context copy at `⊤`, the copies satisfy the admission. -/
theorem admL_of_isLawful {o : Fin I.left.card} (ho : I.left.toCellScheme.grade o = 2)
    {q : Fin (admCompletion hS hst htwo).scheme.card → Label.{u}}
    (hq : (admCompletion hS hst htwo).scheme.rows.IsLawful q)
    (hqo : q ((admCompletion hS hst htwo).embed (StageType.faceCell I.restrictFace_left o)) = ⊤) :
    Adm (fun z ↦ q ((admCompletion hS hst htwo).embed (StageType.faceCell I.restrictFace_left z)))
      (fun z ↦ q ((admCompletion hS hst htwo).embed
        (StageType.faceCell I.restrictFace_right z))) := by
  have hx₀ : I.lowerFieldLayer.toCellScheme.grade (I.privCell o) = 2 := by
    rw [Scheme.appendFullCellsScheme_grade_castAdd, StageType.grade_faceCell]
    exact ho
  obtain ⟨a, -, hAa, σ, hσ, hσ0, hc, hold⟩ :=
    Scheme.exists_admitted_image (hS := I.not_univ_two_le_lowerFieldLayer) (A := AdmL I Adm)
      hS.bot I.lowerFieldLayer_grade_le (hq.isLawfulBelow _) hx₀ hqo
  have h := hS.comp hσ hσ0 hc hAa
  have e1 : (fun z ↦ σ (a (I.privCell z))) =
      fun z ↦ q ((admCompletion hS hst htwo).embed (StageType.faceCell I.restrictFace_left z)) :=
    funext fun z ↦ (hold _).symm
  have e2 : (fun z ↦ σ (a (I.donCell z))) =
      fun z ↦ q ((admCompletion hS hst htwo).embed (StageType.faceCell I.restrictFace_right z)) :=
    funext fun z ↦ (hold _).symm
  change Adm (fun z ↦ σ (a (I.privCell z))) (fun z ↦ σ (a (I.donCell z))) at h
  rw [e1, e2] at h
  exact h

end Completion

end VaughtConjecture.Seed
