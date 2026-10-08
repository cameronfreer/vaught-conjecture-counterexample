/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2One

/-!
# Top grade `1` at two points: the admitted layer at grade `1` (work file)

WORK FILE (branch `research/work-twolift`).

For a seed `I` on three points and an admission of states `Adm` at the grade `1`
(`H2.IsStateAdmission … 1 …`) reading only the cells of grade at most `1` (`Seed.ReadsOne`), the
admitted field layer at grade `1` over the amalgam, on the admission read on the copies
(`Seed.AdmA`), lifts capped from each coatom to `(univ, 1)` (`Seed.cappedLift_layerOne_left`,
`Seed.cappedLift_layerOne_right`).  The provisions are those of the admission, applied to the
splices at `1` with bottom (the cells of grade `2` at `⊥`), glued on the amalgam.
-/

universe u

namespace VaughtConjecture.Seed

open Finset Label CellScheme StageType H2

variable {α : Ordinal.{u}} {I : Seed.{u} α 1}

/-! ### Transfers between the amalgam and the coatom types -/

theorem amalgam_left_iff (k : ℕ) {w : Fin I.amalgam.card → Label.{u}} :
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 2), k) (fun d ↦ w d) ↔
      I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), k)
        (fun i ↦ w (StageType.faceCell I.restrictFace_left i)) := by
  have hpair : ((univ.erase (Fin.last 2), k) : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.left 1)) id ((univ : Finset (Fin 2)), k) := by
    simp only [Prod.map, id, Coatom.univ_map_left]
  rw [hpair]
  exact (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) (univ, k) w).symm

theorem amalgam_right_iff (k : ℕ) {w : Fin I.amalgam.card → Label.{u}} :
    I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), k) (fun d ↦ w d) ↔
      I.right.rows.IsLawfulBelow ((univ : Finset (Fin 2)), k)
        (fun i ↦ w (StageType.faceCell I.restrictFace_right i)) := by
  have hpair : ((univ.erase (Fin.castSucc (Fin.last 1)), k) : Finset (Fin 3) × ℕ) =
      Prod.map (Finset.map (Coatom.right 1)) id ((univ : Finset (Fin 2)), k) := by
    simp only [Prod.map, id, Coatom.univ_map_right]
  rw [hpair]
  exact (Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_right) (univ, k) w).symm

/-- A cell of the amalgam below the first coatom is a copy of a cell of the first type. -/
theorem exists_left_of_mem_below {k : ℕ} {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.last 2), k)) :
    ∃ z, StageType.faceCell I.restrictFace_left z = d := by
  refine Scheme.exists_faceCell_eq
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)
    (Scheme.mem_visibleCells.mpr fun y hy ↦ ?_)
  have hy' : y ∈ univ.map (Coatom.left 1) := by
    rw [Coatom.univ_map_left]
    exact hd.1 (mem_coe.mp hy)
  obtain ⟨b, -, hb⟩ := mem_map.mp hy'
  exact ⟨b, hb⟩

/-- A cell of the amalgam below the second coatom is a copy of a cell of the second type. -/
theorem exists_right_of_mem_below {k : ℕ} {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), k)) :
    ∃ z, StageType.faceCell I.restrictFace_right z = d := by
  refine Scheme.exists_faceCell_eq
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_right)
    (Scheme.mem_visibleCells.mpr fun y hy ↦ ?_)
  have hy' : y ∈ univ.map (Coatom.right 1) := by
    rw [Coatom.univ_map_right]
    exact hd.1 (mem_coe.mp hy)
  obtain ⟨b, -, hb⟩ := mem_map.mp hy'
  exact ⟨b, hb⟩

/-- A copy of a cell of the first type lies below the first coatom at its grade. -/
theorem left_mem_below {k : ℕ} {z : Fin I.left.card} (hz : I.left.toCellScheme.grade z ≤ k) :
    StageType.faceCell I.restrictFace_left z ∈
      I.amalgam.toCellScheme.below (univ.erase (Fin.last 2), k) := by
  exact ⟨(StageType.scope_faceCell I.restrictFace_left z).trans_subset
    ((map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_left (m := 1)).subset),
    (StageType.grade_faceCell _ z).trans_le hz⟩

/-- A copy of a cell of the second type lies below the second coatom at its grade. -/
theorem right_mem_below {k : ℕ} {z : Fin I.right.card} (hz : I.right.toCellScheme.grade z ≤ k) :
    StageType.faceCell I.restrictFace_right z ∈
      I.amalgam.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), k) := by
  exact ⟨(StageType.scope_faceCell I.restrictFace_right z).trans_subset
    ((map_subset_map.mpr (subset_univ _)).trans (Coatom.univ_map_right (m := 1)).subset),
    (StageType.grade_faceCell _ z).trans_le hz⟩

/-- The cells of the common face have grade at most `1`. -/
theorem grade_rootL_le (x : Fin I.face.card) : I.left.toCellScheme.grade (rootL x) ≤ 1 :=
  (StageType.grade_faceCell _ x).trans_le (I.face.grade_le x)

theorem grade_rootR_le (x : Fin I.face.card) : I.right.toCellScheme.grade (rootR x) ≤ 1 :=
  (StageType.grade_faceCell _ x).trans_le (I.face.grade_le x)

/-! ### The splice at `1` -/

/-- The splice at `1` with bottom of a labelling of a coatom type. -/
noncomputable abbrev spl (E : StageType.{u} α 2) (p : Fin E.card → Label.{u}) :
    Fin E.card → Label.{u} :=
  E.toCellScheme.splice 1 (fun _ ↦ ⊥) p

theorem spl_of_le {E : StageType.{u} α 2} {p : Fin E.card → Label.{u}} {z : Fin E.card}
    (hz : E.toCellScheme.grade z ≤ 1) : spl E p z = p z :=
  CellScheme.splice_of_le hz

theorem spl_of_lt {E : StageType.{u} α 2} {p : Fin E.card → Label.{u}} {z : Fin E.card}
    (hz : ¬ E.toCellScheme.grade z ≤ 1) : spl E p z = ⊥ :=
  CellScheme.splice_of_lt (not_le.mp hz)

theorem isLawful_spl {E : StageType.{u} α 2} {p : Fin E.card → Label.{u}}
    (hp : E.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1) (fun d ↦ p d)) :
    E.rows.IsLawful (spl E p) :=
  Scheme.isLawful_splice_bot (S := E.toScheme) hp

/-- The splice of the first side of a labelling of the amalgam lawful below the first coatom at
grade `1`. -/
theorem isLawful_spl_left {f : Fin I.amalgam.card → Label.{u}}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 2), 1) (fun d ↦ f d)) :
    I.left.rows.IsLawful (spl I.left fun z ↦ f (StageType.faceCell I.restrictFace_left z)) :=
  isLawful_spl (E := I.left) (p := fun z ↦ f (StageType.faceCell I.restrictFace_left z))
    ((amalgam_left_iff 1).mp hf)

/-- The splice of the second side of a labelling of the amalgam lawful below the second coatom at
grade `1`. -/
theorem isLawful_spl_right {f : Fin I.amalgam.card → Label.{u}}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 1)
      (fun d ↦ f d)) :
    I.right.rows.IsLawful (spl I.right fun z ↦ f (StageType.faceCell I.restrictFace_right z)) :=
  isLawful_spl (E := I.right) (p := fun z ↦ f (StageType.faceCell I.restrictFace_right z))
    ((amalgam_right_iff 1).mp hf)

/-! ### The admission on the amalgam -/

variable {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}

variable (I Adm) in
/-- **The admission read on the copies** of a labelling of the amalgam. -/
def AdmA (e : Fin I.amalgam.card → Label.{u}) : Prop :=
  Adm (fun z ↦ e (StageType.faceCell I.restrictFace_left z))
    (fun z ↦ e (StageType.faceCell I.restrictFace_right z))

variable (I Adm) in
/-- **The admission reads only the cells of grade at most `1`.** -/
def ReadsOne : Prop :=
  ∀ ⦃L L' : Fin I.left.card → Label.{u}⦄ ⦃R R' : Fin I.right.card → Label.{u}⦄,
    (∀ z, I.left.toCellScheme.grade z ≤ 1 → L z = L' z) →
    (∀ z, I.right.toCellScheme.grade z ≤ 1 → R z = R' z) → Adm L R → Adm L' R'

section Admission

variable (hS : IsStateAdmission (rootL (I := I)) rootR 1 I.left.rows.IsLawful
  I.right.rows.IsLawful Adm) (hloc : ReadsOne I Adm)
include hS hloc

/-- **The admission passes to the orbit code at `1` of the splice.** -/
theorem admA_code {W : Fin I.amalgam.card → Label.{u}} (hW : AdmA I Adm W) :
    AdmA I Adm (orbitCode 1 (I.amalgam.toCellScheme.splice 1 (fun _ ↦ ⊥) W)) := by
  set t := I.amalgam.toCellScheme.splice 1 (fun _ ↦ ⊥) W
  have ht : AdmA I Adm t := by
    refine hloc (fun z hz ↦ ?_) (fun z hz ↦ ?_) hW
    · exact (CellScheme.splice_of_le ((StageType.grade_faceCell _ z).trans_le hz)).symm
    · exact (CellScheme.splice_of_le ((StageType.grade_faceCell _ z).trans_le hz)).symm
  have hw := isWitness_orbitMap 1 t
  exact hS.comp hw.monotone hw.map_bot (fun x ↦ hw.visibilityReplace_comm x 1
    (by rw [stepSuppressor_of_le le_rfl]; exact le_top) 1 le_rfl) ht

end Admission

/-! ### The provisions at grade `1` -/

section Provisions

variable (hS : IsStateAdmission (rootL (I := I)) rootR 1 I.left.rows.IsLawful
  I.right.rows.IsLawful Adm) (hloc : ReadsOne I Adm)

private theorem erase_ne_univ' (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

include hS hloc in
/-- **The provision at the cap `⊥` from the first coatom, at grade `1`.** -/
theorem botOne_left (hst : Adm I.left.label I.right.label) {f : Fin I.amalgam.card → Label.{u}}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 2), 1) (fun d ↦ f d)) :
    ∃ W : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 1) (fun d ↦ W d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.last 2), 1), W d = f d) ∧
      AdmA I Adm (orbitCode 1 (I.amalgam.toCellScheme.splice 1 (fun _ ↦ ⊥) W)) := by
  have hsT := isLawful_spl_left ( hf)
  obtain ⟨sD, hsD, hroot, -, hadm⟩ := hS.context (isSelfVisible_bot 1) I.left.isLawful
    I.right.isLawful (label_rootL I) hst hsT (fun _ ↦ by simp)
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_glue₂ hsT hsD
    (rootAgree_of fun x ↦ (hroot x).symm)
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, admA_code hS hloc ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_below hd
    rw [hWT, spl_of_le ((StageType.grade_faceCell _ z).symm.trans_le hd.2)]
  · change Adm (fun z ↦ W _) (fun z ↦ W _)
    rw [funext hWT, funext hWD]
    exact hadm

include hS hloc in
/-- **The provision at the cap `⊥` from the second coatom, at grade `1`.** -/
theorem botOne_right (hst : Adm I.left.label I.right.label) {f : Fin I.amalgam.card → Label.{u}}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 1)
      (fun d ↦ f d)) :
    ∃ W : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 1) (fun d ↦ W d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 1),
        W d = f d) ∧
      AdmA I Adm (orbitCode 1 (I.amalgam.toCellScheme.splice 1 (fun _ ↦ ⊥) W)) := by
  have hsD := isLawful_spl_right ( hf)
  obtain ⟨sT, hsT, hroot, -, hadm⟩ := hS.donor (isSelfVisible_bot 1) I.left.isLawful
    I.right.isLawful (label_rootL I) hst hsD (fun _ ↦ by simp)
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_glue₂ hsT hsD (rootAgree_of hroot)
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, admA_code hS hloc ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_below hd
    rw [hWD, spl_of_le ((StageType.grade_faceCell _ z).symm.trans_le hd.2)]
  · change Adm (fun z ↦ W _) (fun z ↦ W _)
    rw [funext hWT, funext hWD]
    exact hadm

/-- The splices of the two sides of a labelling of the amalgam agree at the common face. -/
theorem spl_root (a : Fin I.amalgam.card → Label.{u}) (x : Fin I.face.card) :
    spl I.left (fun z ↦ a (StageType.faceCell I.restrictFace_left z)) (rootL x) =
      spl I.right (fun z ↦ a (StageType.faceCell I.restrictFace_right z)) (rootR x) := by
  rw [spl_of_le (grade_rootL_le x), spl_of_le (grade_rootR_le x)]
  exact congrArg a (faceCell_rootL x)

include hloc in
/-- The admission of a labelling of the amalgam passes to the splices of its sides. -/
theorem adm_spl {a : Fin I.amalgam.card → Label.{u}} (hA : AdmA I Adm a) :
    Adm (spl I.left (fun z ↦ a (StageType.faceCell I.restrictFace_left z)))
      (spl I.right (fun z ↦ a (StageType.faceCell I.restrictFace_right z))) :=
  hloc (fun _ hz ↦ (spl_of_le hz).symm) (fun _ hz ↦ (spl_of_le hz).symm) hA

include hS hloc in
/-- **The provision at a positive cap from the first coatom, at grade `1`.** -/
theorem capOne_left {h : Label.{u}} (hh : IsSelfVisible 1 h)
    {a : Fin I.amalgam.card → Label.{u}} (ha : I.amalgam.rows.IsLawful a) (hA : AdmA I Adm a)
    {f : Fin I.amalgam.card → Label.{u}}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 2), 1) (fun d ↦ f d))
    (hfa : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.last 2), 1),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 1) (fun d ↦ W d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.last 2), 1), W d = f d) ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → min (W d) h = min (a d) h) ∧
      AdmA I Adm (orbitCode 1 (I.amalgam.toCellScheme.splice 1 (fun _ ↦ ⊥) W)) := by
  have hsT := isLawful_spl_left ( hf)
  have hL := isLawful_spl_left ( (ha.isLawfulBelow (univ.erase (Fin.last 2), 1)))
  have hR := isLawful_spl_right (
    (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 1)))
  have hfL (z : Fin I.left.card) :
      min (spl I.left (fun z ↦ f (StageType.faceCell I.restrictFace_left z)) z) h =
        min (spl I.left (fun z ↦ a (StageType.faceCell I.restrictFace_left z)) z) h := by
    by_cases hz : I.left.toCellScheme.grade z ≤ 1
    · rw [spl_of_le hz, spl_of_le hz]
      exact hfa _ (left_mem_below hz)
    · rw [spl_of_lt hz, spl_of_lt hz]
  obtain ⟨sD, hsD, hroot, hsDR, hadm⟩ :=
    hS.context hh hL hR (spl_root a) (adm_spl hloc hA) hsT hfL
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_glue₂ hsT hsD
    (rootAgree_of fun x ↦ (hroot x).symm)
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, fun d hd ↦ ?_, admA_code hS hloc ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_below hd
    rw [hWT, spl_of_le ((StageType.grade_faceCell _ z).symm.trans_le hd.2)]
  · rcases I.mem_visibleCells_or d with hv | hv
    · obtain ⟨z, rfl⟩ := Scheme.exists_faceCell_eq
        (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) hv
      have hz : I.left.toCellScheme.grade z ≤ 1 :=
        (StageType.grade_faceCell I.restrictFace_left z).symm.trans_le hd
      change min (W (StageType.faceCell I.restrictFace_left z)) h = _
      rw [hWT, spl_of_le hz]
      exact hfa _ (left_mem_below hz)
    · obtain ⟨z, rfl⟩ := Scheme.exists_faceCell_eq
        (StageType.comap_toScheme_of_restrictFace I.restrictFace_right) hv
      have hz : I.right.toCellScheme.grade z ≤ 1 :=
        (StageType.grade_faceCell I.restrictFace_right z).symm.trans_le hd
      change min (W (StageType.faceCell I.restrictFace_right z)) h = _
      rw [hWD, hsDR z, spl_of_le hz]
      rfl
  · change Adm (fun z ↦ W _) (fun z ↦ W _)
    rw [funext hWT, funext hWD]
    exact hadm

include hS hloc in
/-- **The provision at a positive cap from the second coatom, at grade `1`.** -/
theorem capOne_right {h : Label.{u}} (hh : IsSelfVisible 1 h)
    {a : Fin I.amalgam.card → Label.{u}} (ha : I.amalgam.rows.IsLawful a) (hA : AdmA I Adm a)
    {f : Fin I.amalgam.card → Label.{u}}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 1)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 1),
      min (f d) h = min (a d) h) :
    ∃ W : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin 3)), 1) (fun d ↦ W d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 1),
        W d = f d) ∧
      (∀ d, I.amalgam.toCellScheme.grade d ≤ 1 → min (W d) h = min (a d) h) ∧
      AdmA I Adm (orbitCode 1 (I.amalgam.toCellScheme.splice 1 (fun _ ↦ ⊥) W)) := by
  have hsD := isLawful_spl_right ( hf)
  have hL := isLawful_spl_left ( (ha.isLawfulBelow (univ.erase (Fin.last 2), 1)))
  have hR := isLawful_spl_right (
    (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 1)))
  have hfR (z : Fin I.right.card) :
      min (spl I.right (fun z ↦ f (StageType.faceCell I.restrictFace_right z)) z) h =
        min (spl I.right (fun z ↦ a (StageType.faceCell I.restrictFace_right z)) z) h := by
    by_cases hz : I.right.toCellScheme.grade z ≤ 1
    · rw [spl_of_le hz, spl_of_le hz]
      exact hfa _ (right_mem_below hz)
    · rw [spl_of_lt hz, spl_of_lt hz]
  obtain ⟨sT, hsT, hroot, hsTL, hadm⟩ :=
    hS.donor hh hL hR (spl_root a) (adm_spl hloc hA) hsD hfR
  obtain ⟨W, hW, hWT, hWD⟩ := exists_isLawful_glue₂ hsT hsD (rootAgree_of hroot)
  refine ⟨W, hW.isLawfulBelow _, fun d hd ↦ ?_, fun d hd ↦ ?_, admA_code hS hloc ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_below hd
    rw [hWD, spl_of_le ((StageType.grade_faceCell _ z).symm.trans_le hd.2)]
  · rcases I.mem_visibleCells_or d with hv | hv
    · obtain ⟨z, rfl⟩ := Scheme.exists_faceCell_eq
        (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) hv
      have hz : I.left.toCellScheme.grade z ≤ 1 :=
        (StageType.grade_faceCell I.restrictFace_left z).symm.trans_le hd
      change min (W (StageType.faceCell I.restrictFace_left z)) h = _
      rw [hWT, hsTL z, spl_of_le hz]
      rfl
    · obtain ⟨z, rfl⟩ := Scheme.exists_faceCell_eq
        (StageType.comap_toScheme_of_restrictFace I.restrictFace_right) hv
      have hz : I.right.toCellScheme.grade z ≤ 1 :=
        (StageType.grade_faceCell I.restrictFace_right z).symm.trans_le hd
      change min (W (StageType.faceCell I.restrictFace_right z)) h = _
      rw [hWD, spl_of_le hz]
      exact hfa _ (right_mem_below hz)
  · change Adm (fun z ↦ W _) (fun z ↦ W _)
    rw [funext hWT, funext hWD]
    exact hadm

/-! ### The admitted layer at grade `1` and its coatom lifts -/

variable (I Adm) in
/-- **The admitted layer at grade `1`** over the amalgam. -/
noncomputable abbrev layerOne : Scheme.{u} 3 :=
  I.amalgam.toScheme.admittedFieldLayer 1 (AdmA I Adm) (I.not_univ_le 1)

include hS hloc in
theorem cappedLift_layerOne_left (hst : Adm I.left.label I.right.label) :
    (I.layerOne Adm).rows.CappedLift (X := (univ.erase (Fin.last 2), 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 0) (hS := I.not_univ_le 1) I.isConsistent hS.bot
    (erase_ne_univ' _) (I.exists_gradedIndex_eq _ ⟨I.erase_last_mem_faces, one_pos, by decide⟩
      (erase_ne_univ' _))
    (I.amalgam.isWellFormed.isWellFormed.cappedLift _ (Or.inl rfl) _)
    (fun _ hf ↦ botOne_left hS hloc hst hf)
    (fun _ hh _ _ _ ha hA _ hf hfa ↦ capOne_left hS hloc hh ha hA hf hfa)

include hS hloc in
theorem cappedLift_layerOne_right (hst : Adm I.left.label I.right.label) :
    (I.layerOne Adm).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 0) (hS := I.not_univ_le 1) I.isConsistent hS.bot
    (erase_ne_univ' _)
    (I.exists_gradedIndex_eq _ ⟨I.erase_castSucc_mem_faces, one_pos, by decide⟩
      (erase_ne_univ' _))
    (I.amalgam.isWellFormed.isWellFormed.cappedLift _ (Or.inl rfl) _)
    (fun _ hf ↦ botOne_right hS hloc hst hf)
    (fun _ hh _ _ _ ha hA _ hf hfa ↦ capOne_right hS hloc hh ha hA hf hfa)

end Provisions

end VaughtConjecture.Seed
