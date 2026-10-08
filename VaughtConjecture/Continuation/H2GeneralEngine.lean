/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralTwo
import VaughtConjecture.Extension.AdmittedTower
import VaughtConjecture.Extension.LevelOn

/-!
# h2 at every arity: the engine at the full grade (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`.

**The engine at the full grade** (`H2.admittedCompletionsAt_full`): for a context on `k + 1 ≥ 3`
points of top grade `K = k + 1`, an admission of states of the clause between the lawful faces
gives a completion with the reading property, through the completion on the catalogues of the
clause from the grade `k + 1` (`Seed.exists_rowCompletion`):
* the states read the clause on their two coatom faces (`H2.stateAdm`); the clause depends only on
  the order and on the replacement at `K`, so it passes to the codes (orbit maps are witnesses
  bounded by the grade);
* the lift provisions at the grade `k + 1` from the first coatom are the context provision of the
  admission, and from the second coatom its donor provision; the two faces are glued along the
  common face (`H2.exists_glue`);
* the reading (`H2.recProp_of_hasAdmittedRows`): availability from the owner gives a cell of full
  scope and grade `K` at `⊤`, and locality there presents the old cells as a monotone image of
  its admitted row, commuting with the replacement at `K`.

**The open inputs** (`H2.coatomCutoffDeterminationLast_of_open`): owner lowering below the
designated tops below the full grade (`H2.OwnerLoweringBelowAt`, every arity), the engine on one
point (`H2.AdmittedCompletionsAt 0`), and the engine below the full grade on at least three points
(`H2.AdmittedCompletionsBelowAt`): there the rows at the grades above `K` are read on faces of
grade above `K`, which the admission between the grade-`K` faces does not reach.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission ProfileTower CellScheme

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-! ### The common face and gluing -/

/-- The cells of the common face, as cells of the first coatom type. -/
noncomputable abbrev rootLm (x : Fin I.face.card) : Fin I.left.card :=
  StageType.faceCell I.restrictFace_face_left x

/-- The cells of the common face, as cells of the second coatom type. -/
noncomputable abbrev rootRm (x : Fin I.face.card) : Fin I.right.card :=
  StageType.faceCell I.restrictFace_face_right x

variable {I}

/-- The copies of a cell of the common face through either coatom are one cell of the amalgam. -/
theorem ctx_rootLm (x : Fin I.face.card) : ctx I (rootLm I x) = don I (rootRm I x) :=
  StageType.faceCell_faceCell I.restrictFace_left I.restrictFace_right I.restrictFace_face_left
    I.restrictFace_face_right x

/-- The cells of the second coatom type map injectively into the amalgam. -/
theorem don_injective : Function.Injective (don I) :=
  I.amalgam.toScheme.faceCell_injective
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_right)

/-- The cells of the first coatom type map injectively into the amalgam. -/
theorem ctx_injective : Function.Injective (ctx I) :=
  I.amalgam.toScheme.faceCell_injective
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)

/-- **A cell on both coatoms is a cell of the common face.** -/
theorem exists_root_of_eq {zT : Fin I.left.card} {zD : Fin I.right.card}
    (h : ctx I zT = don I zD) : ∃ x, zT = rootLm I x ∧ zD = rootRm I x := by
  have hs := congrArg (fun d ↦ I.amalgam.toCellScheme.scope d) h
  simp only [StageType.scope_faceCell] at hs
  have hsub : (I.left.toCellScheme.scope zT).map (Coatom.left m) ⊆
      univ.map (Coatom.right m) := hs ▸ map_subset_map.mpr (subset_univ _)
  have hface := Coatom.map_left_subset_univ_map_right_iff.mp hsub
  have hvis : zT ∈ I.left.toScheme.visibleCells (Coatom.face m) := by
    refine Scheme.mem_visibleCells.mpr fun y hy ↦ ?_
    obtain ⟨i, -, hi⟩ := mem_map.mp (hface (mem_coe.mp hy))
    exact ⟨i, hi⟩
  obtain ⟨x, rfl⟩ := Scheme.exists_faceCell_eq
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_face_left) hvis
  exact ⟨x, rfl, don_injective (h.symm.trans (ctx_rootLm x))⟩

/-- **Every cell of the amalgam lies on one of the two coatoms.** -/
theorem ctx_or_don (d : Fin I.amalgam.card) : (∃ z, ctx I z = d) ∨ ∃ z, don I z = d := by
  have hf := I.amalgam.isWellFormed.isWellFormed.scope_mem d
  rcases I.subset_or_subset _ hf (I.scope_ne_univ d) with h | h
  · refine .inl (Scheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)
      (Scheme.mem_visibleCells.mpr fun y hy ↦ ?_))
    rw [← Coatom.univ_map_left] at h
    obtain ⟨i, -, hi⟩ := mem_map.mp (h (mem_coe.mp hy))
    exact ⟨i, hi⟩
  · refine .inr (Scheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_right)
      (Scheme.mem_visibleCells.mpr fun y hy ↦ ?_))
    rw [← Coatom.univ_map_right] at h
    obtain ⟨i, -, hi⟩ := mem_map.mp (h (mem_coe.mp hy))
    exact ⟨i, hi⟩

/-- **Gluing two coatom labellings agreeing on the common face** into a state. -/
theorem exists_glue {sL : Fin I.left.card → Label.{u}} {sR : Fin I.right.card → Label.{u}}
    (hroot : ∀ x, sL (rootLm I x) = sR (rootRm I x)) :
    ∃ w : I.State, (∀ z, w (ctx I z) = sL z) ∧ ∀ z, w (don I z) = sR z := by
  classical
  refine ⟨fun d ↦ if hd : ∃ z, ctx I z = d then sL hd.choose
    else if hd' : ∃ z, don I z = d then sR hd'.choose else ⊥, fun z ↦ ?_, fun z ↦ ?_⟩
  · have hd : ∃ z', ctx I z' = ctx I z := ⟨z, rfl⟩
    simp only [hd, dite_true]
    rw [ctx_injective hd.choose_spec]
  · by_cases hd : ∃ z', ctx I z' = don I z
    · simp only [hd, dite_true]
      obtain ⟨x, h1, h2⟩ := exists_root_of_eq hd.choose_spec
      rw [h1, hroot, ← h2]
    · have hd' : ∃ z', don I z' = don I z := ⟨z, rfl⟩
      simp only [hd, hd', dite_false, dite_true]
      rw [don_injective hd'.choose_spec]

/-- **Lawful on the grade-`j` cut** exactly when the two coatom faces are lawful below
`(univ, j)`. -/
theorem isCutLawful_iff (j : ℕ) (w : I.State) :
    IsCutLawful I j w ↔
      I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) (fun z ↦ w (ctx I z)) ∧
      I.right.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) (fun z ↦ w (don I z)) := by
  have hL := Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)
    ((univ : Finset (Fin (m + 1))), j) w
  have hR := Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_right)
    ((univ : Finset (Fin (m + 1))), j) w
  simp only [Prod.map, id] at hL hR
  rw [Coatom.univ_map_left] at hL
  rw [Coatom.univ_map_right] at hR
  exact ⟨fun h ↦ ⟨hL.mpr h.1, hR.mpr h.2⟩, fun h ↦ ⟨hL.mp h.1, hR.mp h.2⟩⟩

/-- A cell of the amalgam below the first coatom is a cell of the first coatom type. -/
theorem exists_ctx_of_mem_below {j : ℕ} {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (coatC, j)) : ∃ z, ctx I z = d :=
  Scheme.exists_faceCell_eq (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)
    (Scheme.mem_visibleCells.mpr fun y hy ↦ by
      have hy' : y ∈ univ.map (Coatom.left m) := by
        rw [Coatom.univ_map_left]; exact hd.1 (mem_coe.mp hy)
      obtain ⟨i, -, hi⟩ := mem_map.mp hy'
      exact ⟨i, hi⟩)

/-- A cell of the amalgam below the second coatom is a cell of the second coatom type. -/
theorem exists_don_of_mem_below {j : ℕ} {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (coatD, j)) : ∃ z, don I z = d :=
  Scheme.exists_faceCell_eq (StageType.comap_toScheme_of_restrictFace I.restrictFace_right)
    (Scheme.mem_visibleCells.mpr fun y hy ↦ by
      have hy' : y ∈ univ.map (Coatom.right m) := by
        rw [Coatom.univ_map_right]; exact hd.1 (mem_coe.mp hy)
      obtain ⟨i, -, hi⟩ := mem_map.mp hy'
      exact ⟨i, hi⟩)

/-- A cell of the first coatom type lies below the first coatom at its grade. -/
theorem ctx_mem_below {j : ℕ} (z : Fin I.left.card) (hz : I.left.toCellScheme.grade z ≤ j) :
    ctx I z ∈ I.amalgam.toCellScheme.below (coatC, j) := by
  refine (CellScheme.mem_below _).mpr ⟨?_, ?_⟩
  · change I.amalgam.toCellScheme.scope (ctx I z) ⊆ univ.erase (Fin.last (m + 1))
    rw [StageType.scope_faceCell, ← Coatom.univ_map_left]
    exact map_subset_map.mpr (subset_univ _)
  · change I.amalgam.toCellScheme.grade (ctx I z) ≤ j
    rw [StageType.grade_faceCell]; exact hz

/-- A cell of the second coatom type lies below the second coatom at its grade. -/
theorem don_mem_below {j : ℕ} (z : Fin I.right.card) (hz : I.right.toCellScheme.grade z ≤ j) :
    don I z ∈ I.amalgam.toCellScheme.below (coatD, j) := by
  refine (CellScheme.mem_below _).mpr ⟨?_, ?_⟩
  · change I.amalgam.toCellScheme.scope (don I z) ⊆ univ.erase (Fin.castSucc (Fin.last m))
    rw [StageType.scope_faceCell, ← Coatom.univ_map_right]
    exact map_subset_map.mpr (subset_univ _)
  · change I.amalgam.toCellScheme.grade (don I z) ≤ j
    rw [StageType.grade_faceCell]; exact hz

/-! ### The clause on states -/

variable (I) in
/-- A state **satisfies the clause** on its two coatom faces. -/
def stateAdm (Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop)
    (s : I.State) : Prop :=
  Adm (fun z ↦ s (ctx I z)) (fun z ↦ s (don I z))

/-- At the grades at least `m + 1` the splice of a state is the state. -/
theorem hat_full {k : ℕ} (hk : m + 1 ≤ k) (s : I.State) : hat I k s = s :=
  funext fun d ↦ hat_of_le ((Nat.lt_succ_iff.mp (I.grade_lt d)).trans hk)

variable {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}
  {C : (Fin I.left.card → Label.{u}) → Prop} {D : (Fin I.right.card → Label.{u}) → Prop}

/-- **The clause passes to images under witnesses bounded by a grade at least `m + 1`.** -/
theorem stateAdm_comp (hS : IsStateAdmission (rootLm I) (rootRm I) (m + 1) C D Adm) {k : ℕ}
    (hk : m + 1 ≤ k) {σ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor k) σ)
    {s : I.State} (hs : stateAdm I Adm s) : stateAdm I Adm fun d ↦ σ (s d) :=
  hS.comp hσ.monotone hσ.map_bot (fun x ↦ hσ.visibilityReplace_comm x (m + 1)
    (by rw [stepSuppressor_of_le hk]; exact le_top) (m + 1) le_rfl) hs

/-- **The code of a state with the clause has the clause**, at a grade at least `m + 1`. -/
theorem code_mem_rowCat_of (hS : IsStateAdmission (rootLm I) (rootRm I) (m + 1) C D Adm)
    {k : ℕ} (hk : m + 1 ≤ k) {w : I.State} (hw : IsCutLawful I k w) (ha : stateAdm I Adm w) :
    code k w ∈ rowCat (stateAdm I Adm) k := by
  refine mem_rowCat.mpr ⟨code_mem_cat_of_isCutLawful hw, ?_⟩
  have e : hat I k (code k w) = fun d ↦ orbitMap k (hat I k w) (w d) := by
    rw [hat_full hk]
    funext d
    change orbitCode k (hat I k w) d = _
    rw [orbitCode_apply, hat_full hk]
  rw [e]
  exact stateAdm_comp hS hk (isWitness_orbitMap k _) ha

/-- **The orbit code of a state with the clause has the clause**, at a grade at least `m + 1`. -/
theorem orbitCode_mem_rowCat_of (hS : IsStateAdmission (rootLm I) (rootRm I) (m + 1) C D Adm)
    {k : ℕ} (hk : m + 1 ≤ k) {w : I.State} (hw : IsCutLawful I k w) (ha : stateAdm I Adm w) :
    orbitCode k w ∈ rowCat (stateAdm I Adm) k := by
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hw.1.orbitCode fun d ↦ d.2.2,
    hw.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, ?_⟩
  rw [hat_full hk]
  exact stateAdm_comp hS hk (isWitness_orbitMap k w) ha

/-! ### The lift provisions at the full grade -/

/-- The first coatom face of a state is lawful below `(univ, j)` exactly when the state is lawful
below the first coatom at `j`. -/
theorem ctx_isLawfulBelow_iff (j : ℕ) (w : I.State) :
    I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) (fun z ↦ w (ctx I z)) ↔
      I.amalgam.rows.IsLawfulBelow (coatC, j) (fun d ↦ w d) := by
  have hL := Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)
    ((univ : Finset (Fin (m + 1))), j) w
  simp only [Prod.map, id] at hL
  rw [Coatom.univ_map_left] at hL
  exact hL

/-- The second coatom face of a state is lawful below `(univ, j)` exactly when the state is lawful
below the second coatom at `j`. -/
theorem don_isLawfulBelow_iff (j : ℕ) (w : I.State) :
    I.right.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) (fun z ↦ w (don I z)) ↔
      I.amalgam.rows.IsLawfulBelow (coatD, j) (fun d ↦ w d) := by
  have hR := Scheme.isLawfulBelow_faceCell_iff
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_right)
    ((univ : Finset (Fin (m + 1))), j) w
  simp only [Prod.map, id] at hR
  rw [Coatom.univ_map_right] at hR
  exact hR

/-- A state glued from two lawful coatom faces is lawful on the cut at the grade `m + 1`. -/
theorem isCutLawful_of_faces {w : I.State} (hL : I.left.rows.IsLawful fun z ↦ w (ctx I z))
    (hR : I.right.rows.IsLawful fun z ↦ w (don I z)) : IsCutLawful I (m + 1) w :=
  ⟨(ctx_isLawfulBelow_iff (m + 1) w).mp (hL.isLawfulBelow _),
    (don_isLawfulBelow_iff (m + 1) w).mp (hR.isLawfulBelow _)⟩

/-- The first coatom face of a state lawful below the first coatom at `m + 1` is lawful. -/
theorem isLawful_ctx_of {f : I.State}
    (hf : I.amalgam.rows.IsLawfulBelow (coatC, m + 1) fun d ↦ f d) :
    I.left.rows.IsLawful fun z ↦ f (ctx I z) :=
  ((ctx_isLawfulBelow_iff (m + 1) f).mpr hf).isLawful fun d ↦ ⟨subset_univ _, I.left.grade_le d⟩

/-- The second coatom face of a state lawful below the second coatom at `m + 1` is lawful. -/
theorem isLawful_don_of {f : I.State}
    (hf : I.amalgam.rows.IsLawfulBelow (coatD, m + 1) fun d ↦ f d) :
    I.right.rows.IsLawful fun z ↦ f (don I z) :=
  ((don_isLawfulBelow_iff (m + 1) f).mpr hf).isLawful fun d ↦ ⟨subset_univ _, I.right.grade_le d⟩

section Provisions

variable (hS : IsStateAdmission (rootLm I) (rootRm I) (m + 1) I.left.rows.IsLawful
  I.right.rows.IsLawful Adm)
include hS

/-- **The lift provision at `⊥` from the first coatom** (the context provision at `⊥`). -/
theorem botLift_left : BotLiftProvisionOf (stateAdm I Adm) (m + 1) (Fin.last (m + 1)) := by
  intro f hf
  have hfL := isLawful_ctx_of hf
  obtain ⟨WR, hWR, hWRr, -, hA⟩ := hS.context (isSelfVisible_bot _)
    CellScheme.Rows.isLawful_const_bot CellScheme.Rows.isLawful_const_bot (fun _ ↦ rfl) hS.bot
    hfL (fun _ ↦ by simp)
  obtain ⟨w, hwL, hwR⟩ := exists_glue (sL := fun z ↦ f (ctx I z)) (sR := WR)
    fun x ↦ (hWRr x).symm
  have eL : (fun z ↦ w (ctx I z)) = fun z ↦ f (ctx I z) := funext hwL
  have eR : (fun z ↦ w (don I z)) = WR := funext hwR
  have hcut : IsCutLawful I (m + 1) w := isCutLawful_of_faces (by rw [eL]; exact hfL)
    (by rw [eR]; exact hWR)
  refine ⟨w, hcut, fun d hd ↦ ?_, code_mem_rowCat_of hS le_rfl hcut ?_⟩
  · obtain ⟨z, rfl⟩ := exists_ctx_of_mem_below hd
    exact hwL z
  · unfold stateAdm
    rw [eL, eR]
    exact hA

/-- **The lift provision at `⊥` from the second coatom** (the donor provision at `⊥`). -/
theorem botLift_right :
    BotLiftProvisionOf (stateAdm I Adm) (m + 1) (Fin.castSucc (Fin.last m)) := by
  intro f hf
  have hfR := isLawful_don_of hf
  obtain ⟨WL, hWL, hWLr, -, hA⟩ := hS.donor (isSelfVisible_bot _)
    CellScheme.Rows.isLawful_const_bot CellScheme.Rows.isLawful_const_bot (fun _ ↦ rfl) hS.bot
    hfR (fun _ ↦ by simp)
  obtain ⟨w, hwL, hwR⟩ := exists_glue (sL := WL) (sR := fun z ↦ f (don I z)) hWLr
  have eL : (fun z ↦ w (ctx I z)) = WL := funext hwL
  have eR : (fun z ↦ w (don I z)) = fun z ↦ f (don I z) := funext hwR
  have hcut : IsCutLawful I (m + 1) w := isCutLawful_of_faces (by rw [eL]; exact hWL)
    (by rw [eR]; exact hfR)
  refine ⟨w, hcut, fun d hd ↦ ?_, code_mem_rowCat_of hS le_rfl hcut ?_⟩
  · obtain ⟨z, rfl⟩ := exists_don_of_mem_below hd
    exact hwR z
  · unfold stateAdm
    rw [eL, eR]
    exact hA

/-- **The lift provision at the positive caps from the first coatom** (the context provision). -/
theorem capLift_left : CapLiftProvisionOf (stateAdm I Adm) (m + 1) (Fin.last (m + 1)) := by
  intro h hh _ _ P hP f hf hfP
  obtain ⟨hPcat, hPA⟩ := mem_rowCat.mp hP
  rw [hat_full le_rfl] at hPA
  have hPcut := (mem_cat.mp hPcat).1
  have hfL := isLawful_ctx_of hf
  obtain ⟨WR, hWR, hWRr, hWRh, hA⟩ := hS.context hh (isLawful_ctx_of hPcut.1)
    (isLawful_don_of hPcut.2) (fun x ↦ congrArg P (ctx_rootLm x)) hPA hfL
    (fun z ↦ hfP _ (ctx_mem_below z (I.left.grade_le z)))
  obtain ⟨w, hwL, hwR⟩ := exists_glue (sL := fun z ↦ f (ctx I z)) (sR := WR)
    fun x ↦ (hWRr x).symm
  have eL : (fun z ↦ w (ctx I z)) = fun z ↦ f (ctx I z) := funext hwL
  have eR : (fun z ↦ w (don I z)) = WR := funext hwR
  have hcut : IsCutLawful I (m + 1) w := isCutLawful_of_faces (by rw [eL]; exact hfL)
    (by rw [eR]; exact hWR)
  refine ⟨w, hcut, fun d hd ↦ ?_, fun d ↦ ?_, orbitCode_mem_rowCat_of hS le_rfl hcut ?_⟩
  · obtain ⟨z, rfl⟩ := exists_ctx_of_mem_below hd
    exact hwL z
  · rcases ctx_or_don d with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · rw [hwL]
      exact hfP _ (ctx_mem_below z (I.left.grade_le z))
    · rw [hwR]
      exact hWRh z
  · unfold stateAdm
    rw [eL, eR]
    exact hA

/-- **The lift provision at the positive caps from the second coatom** (the donor provision). -/
theorem capLift_right :
    CapLiftProvisionOf (stateAdm I Adm) (m + 1) (Fin.castSucc (Fin.last m)) := by
  intro h hh _ _ P hP f hf hfP
  obtain ⟨hPcat, hPA⟩ := mem_rowCat.mp hP
  rw [hat_full le_rfl] at hPA
  have hPcut := (mem_cat.mp hPcat).1
  have hfR := isLawful_don_of hf
  obtain ⟨WL, hWL, hWLr, hWLh, hA⟩ := hS.donor hh (isLawful_ctx_of hPcut.1)
    (isLawful_don_of hPcut.2) (fun x ↦ congrArg P (ctx_rootLm x)) hPA hfR
    (fun z ↦ hfP _ (don_mem_below z (I.right.grade_le z)))
  obtain ⟨w, hwL, hwR⟩ := exists_glue (sL := WL) (sR := fun z ↦ f (don I z)) hWLr
  have eL : (fun z ↦ w (ctx I z)) = WL := funext hwL
  have eR : (fun z ↦ w (don I z)) = fun z ↦ f (don I z) := funext hwR
  have hcut : IsCutLawful I (m + 1) w := isCutLawful_of_faces (by rw [eL]; exact hWL)
    (by rw [eR]; exact hfR)
  refine ⟨w, hcut, fun d hd ↦ ?_, fun d ↦ ?_, orbitCode_mem_rowCat_of hS le_rfl hcut ?_⟩
  · obtain ⟨z, rfl⟩ := exists_don_of_mem_below hd
    exact hwR z
  · rcases ctx_or_don d with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · rw [hwL]
      exact hWLh z
    · rw [hwR]
      exact hfP _ (don_mem_below z (I.right.grade_le z))
  · unfold stateAdm
    rw [eL, eR]
    exact hA

/-- **The completion with the clause on the rows at the full grade**: the completion on the
catalogue of the clause from the grade `m + 1` (`Seed.exists_rowCompletion`), for `m ≥ 2`. -/
theorem exists_completion_full (hm : 2 ≤ m) (hst : Adm I.left.label I.right.label) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows (m + 1) (stateAdm I Adm) := by
  refine I.exists_rowCompletion hm (N := m + 1) (by omega) (fun k hk hkm x hx ↦ ?_)
    (fun k hk hkm x hx ↦ ?_) (fun k hk R hR ↦ ?_) (fun _ ↦ ?_)
  · obtain rfl : k = m + 1 := le_antisymm hkm hk
    simp only [Pts, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [botLift_left hS, botLift_right hS]
  · obtain rfl : k = m + 1 := le_antisymm hkm hk
    simp only [Pts, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [capLift_left hS, capLift_right hS]
  · obtain ⟨hRcat, hRA⟩ := mem_rowCat.mp hR
    rw [hat_full (by omega)] at hRA
    have hc := (mem_cat.mp hRcat).1
    exact code_mem_rowCat_of hS hk ⟨hc.1.mono (X := (_, k)) ⟨subset_rfl, by omega⟩,
      hc.2.mono (X := (_, k)) ⟨subset_rfl, by omega⟩⟩ hRA
  · have hcut : IsCutLawful I (m + 1) fun d ↦ I.amalgam.label d :=
      ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
    have hA : stateAdm I Adm fun d ↦ I.amalgam.label d := by
      unfold stateAdm
      have eL : (fun z ↦ I.amalgam.label (ctx I z)) = I.left.label :=
        funext fun z ↦ StageType.label_faceCell _ z
      have eR : (fun z ↦ I.amalgam.label (don I z)) = I.right.label :=
        funext fun z ↦ StageType.label_faceCell _ z
      rw [eL, eR]
      exact hst
    exact (mem_rowCat.mp (code_mem_rowCat_of hS le_rfl hcut hA)).2

/-- **The reading at the full grade**: in a completion whose rows of full scope at the grade
`m + 1` have the clause, every lawful labelling with an old cell of grade `m + 1` of the first
coatom at `⊤` has the clause on its old cells.  Availability gives a cell of `(univ, m + 1)` at
`⊤`; locality there presents the old cells as a monotone image of its row, which commutes with
the replacement at `m + 1`. -/
theorem adm_of_hasAdmittedRows {F : CompletionBelowFullGrade I}
    (hF : F.HasAdmittedRows (m + 1) (stateAdm I Adm)) {o : Fin I.left.card}
    (ho : I.left.toCellScheme.grade o = m + 1) {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawful q) (hqo : q (F.embed (ctx I o)) = ⊤) :
    Adm (fun x ↦ q (F.embed (ctx I x))) (fun x ↦ q (F.embed (don I x))) := by
  have hL := F.isLegalBelowFullGrade
  have hY : ((univ : Finset (Fin (m + 2))), m + 1) ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨hL.isWellFormed.univ_mem_faces, by omega, by simp⟩
  obtain ⟨u₀, hu₀⟩ := hL.exists_gradedIndex_eq _ hY (by simp)
  have hsc : F.scheme.toCellScheme.scope (F.embed (ctx I o)) ⊆
      F.scheme.toCellScheme.scope u₀ := by
    have : F.scheme.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
    rw [this]
    exact subset_univ _
  have hg : F.scheme.toCellScheme.grade (F.embed (ctx I o)) =
      F.scheme.toCellScheme.grade u₀ := by
    rw [F.isLowerEmbedding.grade_eq, StageType.grade_faceCell, ho]
    exact (congrArg Prod.snd hu₀).symm
  obtain ⟨u, hu, hle⟩ := hq.availability _ u₀ hsc hg
  have hu' : F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), m + 1) :=
    hu.trans hu₀
  have hqu : q u = ⊤ := top_le_iff.mp (hqo ▸ hle)
  obtain ⟨g, σ, hw, heq⟩ := hq.locality u
  have hgu : F.scheme.toCellScheme.grade u = m + 1 := congrArg Prod.snd hu'
  have hgK : g (m + 1) = ⊤ := by
    have e := heq ⟨u, CellScheme.mem_below_gradedIndex _ u⟩
    change min (q u) (q u) = min (σ _) (g (F.scheme.toCellScheme.grade u)) at e
    rw [hqu, min_self, hgu] at e
    exact (min_eq_top.mp e.symm).2
  have hbelow (d : Fin I.amalgam.card) :
      F.embed d ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, F.gradedIndex_embed, hu']
    exact ⟨subset_univ _, Nat.lt_succ_iff.mp (I.grade_lt d)⟩
  have hval (d : Fin I.amalgam.card) : q (F.embed d) = σ (F.rowState u d) := by
    have e := heq ⟨F.embed d, hbelow d⟩
    change min (q (F.embed d)) (q u) = min (σ _) (g (F.scheme.toCellScheme.grade (F.embed d)))
      at e
    have hgd : g (F.scheme.toCellScheme.grade (F.embed d)) = ⊤ := by
      refine top_le_iff.mp (hgK ▸ hw.antitone ?_)
      rw [F.isLowerEmbedding.grade_eq]
      exact Nat.lt_succ_iff.mp (I.grade_lt d)
    rw [hqu, min_top_right, hgd, min_top_right] at e
    rw [e, CompletionBelowFullGrade.rowState, Scheme.rowAt_of_mem (hbelow d)]
  have hA := hS.comp hw.monotone hw.map_bot (fun x ↦ hw.visibilityReplace_comm x (m + 1)
    (by rw [hgK]; exact le_top) (m + 1) le_rfl) (hF hu' le_rfl)
  have eL : (fun x ↦ q (F.embed (ctx I x))) = fun x ↦ σ (F.rowState u (ctx I x)) :=
    funext fun x ↦ hval _
  have eR : (fun x ↦ q (F.embed (don I x))) = fun x ↦ σ (F.rowState u (don I x)) :=
    funext fun x ↦ hval _
  rw [eL, eR]
  exact hA

end Provisions

/-! ### The engine at the full grade, and the open inputs -/

/-- **The engine below the full grade** (`K ≤ k`), at a source-gap context on `k + 1` points with
the lost point last (a named input): `H2.AdmittedCompletionsAt` restricted to `K ≤ k`. -/
def AdmittedCompletionsBelowAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)) (hleg : t'.IsLegal)
    (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r → K ≤ k →
    ∀ {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)} (htbleg : tb.IsLegal)
      (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x ∈ Lo, tb.label x ≠ ⊤) →
      (∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) →
      IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) K (LawfulAt t' K)
        (LawfulAt tb K) (SelfLowG o r K (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops) →
      ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
        RecProp F o r K Lo Tops

/-- **The engine on `k + 1 ≥ 3` points from the engine below the full grade**: at the full grade
`K = k + 1` the grade-`K` faces are the lawful labellings, and the completion on the catalogue of
the clause (`H2.exists_completion_full`) reads the clause (`H2.adm_of_hasAdmittedRows`). -/
theorem admittedCompletionsAt_of_below {k : ℕ} (hk : 2 ≤ k)
    (h : AdmittedCompletionsBelowAt.{u} k) : AdmittedCompletionsAt.{u} k := by
  intro α K n t' hleg g o r hs p hp tb htbleg htbp Lo Tops hLo hTops hS
  have hKk : K ≤ k + 1 := hs.grade_owner ▸ t'.grade_le o
  rcases Nat.lt_or_ge K (k + 1) with hlt | hge
  · exact h t' hleg g hs (by omega) hp htbleg htbp hLo hTops hS
  obtain rfl : K = k + 1 := le_antisymm hKk hge
  have hLo2 : (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ k + 1) = Lo :=
    filter_true_of_mem fun x _ ↦ tb.grade_le x
  rw [hLo2] at hS
  have hS' := isStateAdmission_congr (fun _ ↦ lawfulAt_iff_isLawful t'.grade_le)
    (fun _ ↦ lawfulAt_iff_isLawful tb.grade_le) hS
  have hst : SelfLowG o r (k + 1) Lo Tops t'.label tb.label :=
    fun t ht _ ↦ (hTops t ht).1.symm ▸ le_top
  obtain ⟨F, hF⟩ := exists_completion_full (I := Seed.ofCoatoms hleg htbleg hp htbp) hS' hk hst
  exact ⟨F, fun q hq hqo ↦ adm_of_hasAdmittedRows hS' hF hs.grade_owner hq hqo⟩

/-- **h2 with the lost point last at every arity from the open inputs**: owner lowering below the
designated tops (below the full grade, every arity), the engine on one point, and the engine below
the full grade on at least three points.  The engine on two points is
`H2.admittedCompletionsAt_one`, and at the full grade on at least three points it is
`H2.admittedCompletionsAt_of_below`. -/
theorem coatomCutoffDeterminationLast_of_open (hOL : ∀ k, OwnerLoweringBelowAt.{u} k)
    (hEN0 : AdmittedCompletionsAt.{u} 0) (hEN : ∀ k, 2 ≤ k → AdmittedCompletionsBelowAt.{u} k) :
    CoatomCutoffDeterminationLast.{u} := by
  refine coatomCutoffDeterminationLast_of_below_engine hOL fun k ↦ ?_
  rcases k with _ | _ | k
  · exact hEN0
  · exact admittedCompletionsAt_one
  · exact admittedCompletionsAt_of_below (by omega) (hEN _ (by omega))

end VaughtConjecture.H2
