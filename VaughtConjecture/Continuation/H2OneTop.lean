/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2OneLayer

/-!
# Top grade `1` at two points: the step to grade `2` over the admitted layer

Roadmap, Layer 3 ((R2) of the table of 3.4: coatom cutoff determination at source-gap contexts,
`Realization.CoatomCutoffDetermination`, written **h2** in the names of this family of modules).
Every declaration is proved; the admission of states at the grade `1` is a hypothesis.

Over the admitted layer at grade `1` (`Seed.layerOne`), a labelling prescribed below one coatom at
grade `2` and agreeing there with an ambient capped at `c` (self-visible at `2`) extends to one
lawful below `(univ, 2)` agreeing with the ambient capped at `c` everywhere
(`Seed.liftTwo_left`, `Seed.liftTwo_right`): first the capped lift of the admitted layer from the
coatom to `(univ, 1)` (`Seed.cappedLift_layerOne_left`), then, on the other coatom type, the
capped lift from `(univ, 1)` to `(univ, 2)` (bountifulness of the legal coatom type), glued over
`(C, 2)`, `(univ, 1)` and `(D, 2)`.  No encoding is needed: the admission is met at grade `1` by
the lift of the admitted layer itself.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Seed

open Finset Label CellScheme StageType H2

variable {α : Ordinal.{u}} {I : Seed.{u} α 1}
variable {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}

theorem erase_ne_univ₁ (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

/-! ### The admitted layer at grade `1`: cells -/

variable (I Adm) in
/-- The catalogue of the admitted layer at grade `1`. -/
noncomputable abbrev catOne : Finset (Fin I.amalgam.card → Label.{u}) :=
  I.amalgam.toScheme.admittedCatalogue 1 (AdmA I Adm)

variable (Adm) in
/-- An old cell of the admitted layer at grade `1`. -/
noncomputable abbrev oldOne (d : Fin I.amalgam.card) : Fin (I.layerOne Adm).card :=
  Fin.castAdd (catOne I Adm).card d


theorem not_univ_two_le_layerOne (d : Fin (I.layerOne Adm).card) :
    ¬ ((univ : Finset (Fin 3)), 2) ≤ (I.layerOne Adm).toCellScheme.gradedIndex d := by
  induction d using Fin.addCases with
  | left d =>
    rw [show (I.layerOne Adm).toCellScheme.gradedIndex (Fin.castAdd _ d) =
      I.amalgam.toCellScheme.gradedIndex d from
        Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d]
    exact I.not_univ_le 2 d
  | right i =>
    rw [show (I.layerOne Adm).toCellScheme.gradedIndex (Fin.natAdd _ i) = (univ, 1) from
      Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i]
    exact fun h ↦ absurd h.2 (by decide)

theorem layerOne_grade_le (d : Fin (I.layerOne Adm).card) :
    (I.layerOne Adm).toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left d =>
    exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ d).trans_le (I.grade_le_two d)
  | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).trans_le (by decide)

theorem layerOne_grade_natAdd (i : Fin (catOne I Adm).card) :
    (I.layerOne Adm).toCellScheme.grade (Fin.natAdd _ i) = 1 :=
  Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i

theorem castAdd_mem_below_layerOne_iff {X : Finset (Fin 3) × ℕ} {d : Fin I.amalgam.card} :
    oldOne Adm d ∈ (I.layerOne Adm).toCellScheme.below X ↔
      d ∈ I.amalgam.toCellScheme.below X := by
  rw [CellScheme.mem_below, CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]

theorem exists_castAdd_of_scope_ne {x : Fin (I.layerOne Adm).card}
    (hx : (I.layerOne Adm).toCellScheme.scope x ≠ univ) : ∃ d, oldOne Adm d = x := by
  induction x using Fin.addCases with
  | left d => exact ⟨d, rfl⟩
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hx

theorem layerOne_left_iff (k : ℕ) {v : Fin (I.layerOne Adm).card → Label.{u}} :
    (I.layerOne Adm).rows.IsLawfulBelow (univ.erase (Fin.last 2), k) (fun d ↦ v d) ↔
      I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), k)
        (fun i ↦ v (oldOne Adm (StageType.faceCell I.restrictFace_left i))) := by
  have h1 := Scheme.isLawfulBelow_appendFullCells_iff (S := I.amalgam.toScheme) (k := 1)
    (M := (catOne I Adm).card)
    (r := fun i ↦ I.amalgam.toScheme.fieldRowOn 1 (catOne I Adm) (Scheme.entryOn _ i))
    (h := I.not_univ_le 1) (X := (univ.erase (Fin.last 2), k))
    (fun h ↦ erase_ne_univ₁ _ (univ_subset_iff.mp h.1)) (v := v)
  rw [h1]
  exact amalgam_left_iff k (w := fun d ↦ v (oldOne Adm d))

theorem layerOne_right_iff (k : ℕ) {v : Fin (I.layerOne Adm).card → Label.{u}} :
    (I.layerOne Adm).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), k)
      (fun d ↦ v d) ↔
      I.right.rows.IsLawfulBelow ((univ : Finset (Fin 2)), k)
        (fun i ↦ v (oldOne Adm (StageType.faceCell I.restrictFace_right i))) := by
  have h1 := Scheme.isLawfulBelow_appendFullCells_iff (S := I.amalgam.toScheme) (k := 1)
    (M := (catOne I Adm).card)
    (r := fun i ↦ I.amalgam.toScheme.fieldRowOn 1 (catOne I Adm) (Scheme.entryOn _ i))
    (h := I.not_univ_le 1) (X := (univ.erase (Fin.castSucc (Fin.last 1)), k))
    (fun h ↦ erase_ne_univ₁ _ (univ_subset_iff.mp h.1)) (v := v)
  rw [h1]
  exact amalgam_right_iff k (w := fun d ↦ v (oldOne Adm d))

/-- Every cell below `(univ, 2)` lies below a coatom at grade `2` or below `(univ, 1)`. -/
theorem layerOne_cover (x : Fin (I.layerOne Adm).card) :
    x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 2) ∨
      x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1) ∨
        x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2) := by
  induction x using Fin.addCases with
  | right i => exact .inr (.inl ⟨subset_univ _, (layerOne_grade_natAdd i).le⟩)
  | left d =>
    rw [castAdd_mem_below_layerOne_iff, castAdd_mem_below_layerOne_iff,
      castAdd_mem_below_layerOne_iff]
    rcases I.scope_subset_or (x := Fin.last 2) (y := Fin.castSucc (Fin.last 1))
      (mem_insert_self _ _) (mem_insert_of_mem (mem_singleton_self _)) (by decide) d with h | h
    · exact .inl ⟨h, I.grade_le_two d⟩
    · exact .inr (.inr ⟨h, I.grade_le_two d⟩)

/-- A copy of a cell of the second type below the first coatom is a cell of the common face. -/
theorem exists_root_of_right_mem {z : Fin I.right.card} {k : ℕ}
    (hz : StageType.faceCell I.restrictFace_right z ∈
      I.amalgam.toCellScheme.below (univ.erase (Fin.last 2), k)) :
    ∃ x, z = rootR x ∧ StageType.faceCell I.restrictFace_left (rootL x) =
      StageType.faceCell I.restrictFace_right z := by
  obtain ⟨zT, hzT⟩ := exists_left_of_mem_below hz
  obtain ⟨x, rfl, rfl⟩ := exists_root_of_eq hzT
  exact ⟨x, rfl, hzT⟩

/-- A copy of a cell of the first type below the second coatom is a cell of the common face. -/
theorem exists_root_of_left_mem {z : Fin I.left.card} {k : ℕ}
    (hz : StageType.faceCell I.restrictFace_left z ∈
      I.amalgam.toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), k)) :
    ∃ x, z = rootL x ∧ StageType.faceCell I.restrictFace_left z =
      StageType.faceCell I.restrictFace_right (rootR x) := by
  obtain ⟨zD, hzD⟩ := exists_right_of_mem_below hz
  obtain ⟨x, rfl, rfl⟩ := exists_root_of_eq hzD.symm
  exact ⟨x, rfl, hzD.symm⟩

/-! ### The step to grade `2` -/

section Step

variable (hS : IsStateAdmission (rootL (I := I)) rootR 1 (LawfulOne I.left)
  (LawfulOne I.right) Adm) (hloc : ReadsOne I Adm)

include hS hloc in
/-- **The step to grade `2` from the first coatom.**  A labelling of the admitted layer at grade `1`
lawful below the first coatom at grade `2`, agreeing there with an ambient lawful below `(univ, 2)`
capped at `c` (self-visible at `2`), extends unchanged there to a labelling lawful below
`(univ, 2)` agreeing with the ambient capped at `c` everywhere. -/
theorem liftTwo_left (hst : Adm I.left.label I.right.label) {c : Label.{u}}
    (hc : IsSelfVisible 2 c) {a : Fin (I.layerOne Adm).card → Label.{u}}
    (ha : (I.layerOne Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ a d))
    {f : Fin (I.layerOne Adm).card → Label.{u}}
    (hf : (I.layerOne Adm).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d))
    (hfa : ∀ d ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 2),
      min (f d) c = min (a d) c) :
    ∃ W : Fin (I.layerOne Adm).card → Label.{u},
      (I.layerOne Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      ∀ d, min (W d) c = min (a d) c := by
  classical
  have hle1 : ((univ.erase (Fin.last 2), 1) : Finset (Fin 3) × ℕ) ≤ (univ.erase (Fin.last 2), 2) :=
    ⟨subset_rfl, by omega⟩
  have hle2 : (((univ : Finset (Fin 3)), 1) : Finset (Fin 3) × ℕ) ≤ ((univ : Finset (Fin 3)), 2) :=
    ⟨subset_rfl, by omega⟩
  -- the lift of the admitted layer from the coatom to `(univ, 1)`
  obtain ⟨q', hq', hq'a, hq'f⟩ := (Rows.cappedLift_iff_forall_exists _).mp
    (cappedLift_layerOne_left hS hloc hst) c (hc.mono (by omega))
    (fun d ↦ f d) (fun d ↦ a d) (by exact hf.mono hle1) (by exact ha.mono hle2)
    (fun d ↦ (hfa d ((I.layerOne Adm).toCellScheme.below_mono hle1 d.2)).symm)
  set Q : Fin (I.layerOne Adm).card → Label.{u} :=
    Rows.extendBot ((univ : Finset (Fin 3)), 1) q' with hQ_def
  have hQ : (I.layerOne Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 1) (fun d ↦ Q d) :=
    Rows.isLawfulBelow_extendBot.mpr hq'
  have hQmem {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1)) :
      Q x = q' ⟨x, hx⟩ := Rows.extendBot_of_mem q' hx
  have hQa {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1)) :
      min (Q x) c = min (a x) c := by rw [hQmem hx]; exact hq'a _
  have hQf {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 1)) :
      Q x = f x := by
    rw [hQmem (((I.layerOne Adm).toCellScheme.below_mono
      (show ((univ.erase (Fin.last 2), 1) : Finset (Fin 3) × ℕ) ≤ ((univ : Finset (Fin 3)), 1)
        from ⟨subset_univ _, le_rfl⟩)) hx)]
    exact hq'f ⟨x, hx⟩
  -- the second coatom type, lifted from `(univ, 1)` to `(univ, 2)`
  have hleD : (((univ : Finset (Fin 2)), 1) : Finset (Fin 2) × ℕ) ≤ ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_rfl, by omega⟩
  have hlD : I.right.rows.CappedLift hleD :=
    I.isLegal_right.isBountiful ⟨I.right.univ_mem_faces, one_pos, by simp⟩
      ⟨I.right.univ_mem_faces, two_pos, by simp⟩ hleD
  have hpD : I.right.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1)
      (fun i ↦ Q (oldOne Adm (StageType.faceCell I.restrictFace_right i))) :=
    (layerOne_right_iff 1).mp
      (by exact hQ.mono (X := (univ.erase (Fin.castSucc (Fin.last 1)), 1)) ⟨subset_univ _, le_rfl⟩)
  have hqD : I.right.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2)
      (fun i ↦ a (oldOne Adm (StageType.faceCell I.restrictFace_right i))) :=
    (layerOne_right_iff 2).mp
      (by exact ha.mono (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2)) ⟨subset_univ _, le_rfl⟩)
  have hmemR {z : Fin I.right.card} (hz : I.right.toCellScheme.grade z ≤ 1) :
      oldOne Adm (StageType.faceCell I.restrictFace_right z) ∈
        (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1) :=
    castAdd_mem_below_layerOne_iff.mpr ⟨subset_univ _, (StageType.grade_faceCell _ z).trans_le hz⟩
  obtain ⟨rD, hrD, hrDa, hrDp⟩ := (Rows.cappedLift_iff_forall_exists hleD).mp hlD c hc
    (fun z ↦ Q (oldOne Adm (StageType.faceCell I.restrictFace_right z)))
    (fun z ↦ a (oldOne Adm (StageType.faceCell I.restrictFace_right z))) hpD hqD
    (fun z ↦ (hQa (hmemR z.2.2)).symm)
  have hallD (z : Fin I.right.card) : z ∈ I.right.toCellScheme.below ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_univ _, I.right.grade_le z⟩
  set sD : Fin I.right.card → Label.{u} := fun z ↦ rD ⟨z, hallD z⟩ with hsD_def
  have hsD : I.right.rows.IsLawful sD := hrD.isLawful hallD
  have hsDQ {z : Fin I.right.card} (hz : I.right.toCellScheme.grade z ≤ 1) :
      sD z = Q (oldOne Adm (StageType.faceCell I.restrictFace_right z)) :=
    hrDp ⟨z, subset_univ _, hz⟩
  have hsDa (z : Fin I.right.card) :
      min (sD z) c = min (a (oldOne Adm (StageType.faceCell I.restrictFace_right z))) c :=
    hrDa ⟨z, hallD z⟩
  -- the assembled labelling
  set W : Fin (I.layerOne Adm).card → Label.{u} := fun x ↦
    if x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 2) then f x
    else if hx : ∃ z, oldOne Adm (StageType.faceCell I.restrictFace_right z) = x then
      sD hx.choose else Q x with hW_def
  have hWf {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 2)) :
      W x = f x := ite_eq_left hx
  have hWD (z : Fin I.right.card) :
      W (oldOne Adm (StageType.faceCell I.restrictFace_right z)) = sD z := by
    by_cases hC : oldOne Adm (StageType.faceCell I.restrictFace_right z) ∈
        (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 2)
    · rw [hWf hC]
      obtain ⟨x, rfl, hx⟩ := exists_root_of_right_mem (castAdd_mem_below_layerOne_iff.mp hC)
      rw [hsDQ (grade_rootR_le x), ← hx]
      exact (hQf (castAdd_mem_below_layerOne_iff.mpr (left_mem_below (grade_rootL_le x)))).symm
    · have hex : ∃ z', oldOne Adm (StageType.faceCell I.restrictFace_right z') =
          oldOne Adm (StageType.faceCell I.restrictFace_right z) := ⟨z, rfl⟩
      refine (ite_eq_right hC).trans ((dite_eq_left hex).trans (congrArg sD ?_))
      exact faceCell_injective' I.restrictFace_right (Fin.castAdd_injective _ _ hex.choose_spec)
  have hWQ {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1)) :
      W x = Q x := by
    by_cases hC : x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.last 2), 2)
    · rw [hWf hC, hQf ⟨hC.1, hx.2⟩]
    · by_cases hex : ∃ z, oldOne Adm (StageType.faceCell I.restrictFace_right z) = x
      · obtain ⟨z, rfl⟩ := hex
        have hz : I.right.toCellScheme.grade z ≤ 1 := by
          have := (castAdd_mem_below_layerOne_iff.mp hx).2
          exact (StageType.grade_faceCell I.restrictFace_right z).symm.trans_le this
        rw [hWD, hsDQ hz]
      · exact (ite_eq_right hC).trans (dite_eq_right hex)
  refine ⟨W, Rows.IsLawfulBelow.glue₃ (U := (univ.erase (Fin.last 2), 2))
    (V := ((univ : Finset (Fin 3)), 1)) (W := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
    ?_ ?_ ?_ (fun x _ ↦ layerOne_cover x), fun x hx ↦ hWf hx, fun x ↦ ?_⟩
  · convert hf using 1
    exact funext fun x ↦ hWf x.2
  · convert hQ using 1
    exact funext fun x ↦ hWQ x.2
  · refine (layerOne_right_iff 2).mpr ?_
    convert hsD.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
    exact funext fun z ↦ hWD z.1
  · rcases layerOne_cover x with hx | hx | hx
    · rw [hWf hx]
      exact hfa x hx
    · rw [hWQ hx]
      exact hQa hx
    · obtain ⟨d, rfl⟩ := exists_castAdd_of_scope_ne (x := x) fun he ↦ by
        have h1 : (I.layerOne Adm).toCellScheme.scope x ⊆ univ.erase (Fin.castSucc (Fin.last 1)) :=
          hx.1
        rw [he] at h1
        exact erase_ne_univ₁ _ (univ_subset_iff.mp h1)
      obtain ⟨z, rfl⟩ := exists_right_of_mem_below (castAdd_mem_below_layerOne_iff.mp hx)
      rw [hWD]
      exact hsDa z

include hS hloc in
/-- **The step to grade `2` from the second coatom** (as `Seed.liftTwo_left`). -/
theorem liftTwo_right (hst : Adm I.left.label I.right.label) {c : Label.{u}}
    (hc : IsSelfVisible 2 c) {a : Fin (I.layerOne Adm).card → Label.{u}}
    (ha : (I.layerOne Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ a d))
    {f : Fin (I.layerOne Adm).card → Label.{u}}
    (hf : (I.layerOne Adm).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
      min (f d) c = min (a d) c) :
    ∃ W : Fin (I.layerOne Adm).card → Label.{u},
      (I.layerOne Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2),
        W d = f d) ∧
      ∀ d, min (W d) c = min (a d) c := by
  classical
  have hle1 : ((univ.erase (Fin.castSucc (Fin.last 1)), 1) : Finset (Fin 3) × ℕ) ≤
      (univ.erase (Fin.castSucc (Fin.last 1)), 2) := ⟨subset_rfl, by omega⟩
  have hle2 : (((univ : Finset (Fin 3)), 1) : Finset (Fin 3) × ℕ) ≤ ((univ : Finset (Fin 3)), 2) :=
    ⟨subset_rfl, by omega⟩
  obtain ⟨q', hq', hq'a, hq'f⟩ := (Rows.cappedLift_iff_forall_exists _).mp
    (cappedLift_layerOne_right hS hloc hst) c (hc.mono (by omega))
    (fun d ↦ f d) (fun d ↦ a d) (by exact hf.mono hle1) (by exact ha.mono hle2)
    (fun d ↦ (hfa d ((I.layerOne Adm).toCellScheme.below_mono hle1 d.2)).symm)
  set Q : Fin (I.layerOne Adm).card → Label.{u} :=
    Rows.extendBot ((univ : Finset (Fin 3)), 1) q' with hQ_def
  have hQ : (I.layerOne Adm).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 1) (fun d ↦ Q d) :=
    Rows.isLawfulBelow_extendBot.mpr hq'
  have hQmem {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1)) :
      Q x = q' ⟨x, hx⟩ := Rows.extendBot_of_mem q' hx
  have hQa {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1)) :
      min (Q x) c = min (a x) c := by rw [hQmem hx]; exact hq'a _
  have hQf {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 1)) :
      Q x = f x := by
    rw [hQmem (((I.layerOne Adm).toCellScheme.below_mono
      (show ((univ.erase (Fin.castSucc (Fin.last 1)), 1) : Finset (Fin 3) × ℕ) ≤
        ((univ : Finset (Fin 3)), 1) from ⟨subset_univ _, le_rfl⟩)) hx)]
    exact hq'f ⟨x, hx⟩
  have hleT : (((univ : Finset (Fin 2)), 1) : Finset (Fin 2) × ℕ) ≤ ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_rfl, by omega⟩
  have hlT : I.left.rows.CappedLift hleT :=
    I.isLegal_left.isBountiful ⟨I.left.univ_mem_faces, one_pos, by simp⟩
      ⟨I.left.univ_mem_faces, two_pos, by simp⟩ hleT
  have hpT : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 1)
      (fun i ↦ Q (oldOne Adm (StageType.faceCell I.restrictFace_left i))) :=
    (layerOne_left_iff 1).mp
      (by exact hQ.mono (X := (univ.erase (Fin.last 2), 1)) ⟨subset_univ _, le_rfl⟩)
  have hqT : I.left.rows.IsLawfulBelow ((univ : Finset (Fin 2)), 2)
      (fun i ↦ a (oldOne Adm (StageType.faceCell I.restrictFace_left i))) :=
    (layerOne_left_iff 2).mp
      (by exact ha.mono (X := (univ.erase (Fin.last 2), 2)) ⟨subset_univ _, le_rfl⟩)
  have hmemL {z : Fin I.left.card} (hz : I.left.toCellScheme.grade z ≤ 1) :
      oldOne Adm (StageType.faceCell I.restrictFace_left z) ∈
        (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1) :=
    castAdd_mem_below_layerOne_iff.mpr ⟨subset_univ _, (StageType.grade_faceCell _ z).trans_le hz⟩
  obtain ⟨rT, hrT, hrTa, hrTp⟩ := (Rows.cappedLift_iff_forall_exists hleT).mp hlT c hc
    (fun z ↦ Q (oldOne Adm (StageType.faceCell I.restrictFace_left z)))
    (fun z ↦ a (oldOne Adm (StageType.faceCell I.restrictFace_left z))) hpT hqT
    (fun z ↦ (hQa (hmemL z.2.2)).symm)
  have hallT (z : Fin I.left.card) : z ∈ I.left.toCellScheme.below ((univ : Finset (Fin 2)), 2) :=
    ⟨subset_univ _, I.left.grade_le z⟩
  set sT : Fin I.left.card → Label.{u} := fun z ↦ rT ⟨z, hallT z⟩ with hsT_def
  have hsT : I.left.rows.IsLawful sT := hrT.isLawful hallT
  have hsTQ {z : Fin I.left.card} (hz : I.left.toCellScheme.grade z ≤ 1) :
      sT z = Q (oldOne Adm (StageType.faceCell I.restrictFace_left z)) :=
    hrTp ⟨z, subset_univ _, hz⟩
  have hsTa (z : Fin I.left.card) :
      min (sT z) c = min (a (oldOne Adm (StageType.faceCell I.restrictFace_left z))) c :=
    hrTa ⟨z, hallT z⟩
  set W : Fin (I.layerOne Adm).card → Label.{u} := fun x ↦
    if x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2) then f x
    else if hx : ∃ z, oldOne Adm (StageType.faceCell I.restrictFace_left z) = x then
      sT hx.choose else Q x with hW_def
  have hWf {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2)) :
      W x = f x := ite_eq_left hx
  have hWT (z : Fin I.left.card) :
      W (oldOne Adm (StageType.faceCell I.restrictFace_left z)) = sT z := by
    by_cases hD : oldOne Adm (StageType.faceCell I.restrictFace_left z) ∈
        (I.layerOne Adm).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    · rw [hWf hD]
      obtain ⟨x, rfl, hx⟩ := exists_root_of_left_mem (castAdd_mem_below_layerOne_iff.mp hD)
      rw [hsTQ (grade_rootL_le x)]
      rw [hx]
      exact (hQf (castAdd_mem_below_layerOne_iff.mpr (right_mem_below (grade_rootR_le x)))).symm
    · have hex : ∃ z', oldOne Adm (StageType.faceCell I.restrictFace_left z') =
          oldOne Adm (StageType.faceCell I.restrictFace_left z) := ⟨z, rfl⟩
      refine (ite_eq_right hD).trans ((dite_eq_left hex).trans (congrArg sT ?_))
      exact faceCell_injective' I.restrictFace_left (Fin.castAdd_injective _ _ hex.choose_spec)
  have hWQ {x : Fin (I.layerOne Adm).card}
      (hx : x ∈ (I.layerOne Adm).toCellScheme.below ((univ : Finset (Fin 3)), 1)) :
      W x = Q x := by
    by_cases hD : x ∈ (I.layerOne Adm).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    · rw [hWf hD, hQf ⟨hD.1, hx.2⟩]
    · by_cases hex : ∃ z, oldOne Adm (StageType.faceCell I.restrictFace_left z) = x
      · obtain ⟨z, rfl⟩ := hex
        have hz : I.left.toCellScheme.grade z ≤ 1 := by
          have := (castAdd_mem_below_layerOne_iff.mp hx).2
          exact (StageType.grade_faceCell I.restrictFace_left z).symm.trans_le this
        rw [hWT, hsTQ hz]
      · exact (ite_eq_right hD).trans (dite_eq_right hex)
  refine ⟨W, Rows.IsLawfulBelow.glue₃ (U := (univ.erase (Fin.last 2), 2))
    (V := ((univ : Finset (Fin 3)), 1)) (W := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
    ?_ ?_ ?_ (fun x _ ↦ layerOne_cover x), fun x hx ↦ hWf hx, fun x ↦ ?_⟩
  · refine (layerOne_left_iff 2).mpr ?_
    convert hsT.isLawfulBelow ((univ : Finset (Fin 2)), 2) using 1
    exact funext fun z ↦ hWT z.1
  · convert hQ using 1
    exact funext fun x ↦ hWQ x.2
  · convert hf using 1
    exact funext fun x ↦ hWf x.2
  · by_cases hD : x ∈ (I.layerOne Adm).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2)
    · rw [hWf hD]
      exact hfa x hD
    · rcases layerOne_cover x with hx | hx | hx
      · obtain ⟨d, rfl⟩ := exists_castAdd_of_scope_ne (x := x) fun he ↦ by
          have h1 : (I.layerOne Adm).toCellScheme.scope x ⊆ univ.erase (Fin.last 2) := hx.1
          rw [he] at h1
          exact erase_ne_univ₁ _ (univ_subset_iff.mp h1)
        obtain ⟨z, rfl⟩ := exists_left_of_mem_below (castAdd_mem_below_layerOne_iff.mp hx)
        rw [hWT]
        exact hsTa z
      · rw [hWQ hx]
        exact hQa hx
      · exact absurd hx hD

end Step

end VaughtConjecture.Seed
