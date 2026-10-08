/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedLift

/-!
# An admitted completion with the reading grade at the top

Roadmap, Layer 3, 3.1, (R6), the completion below the full grade with a restricted catalogue at the
reading grades; the admitted completion when the only reading grade is the top grade `m + 1`.

Let `I` be a seed on `m + 2 ≥ 4` points and `L` the good level of the tower of rank-normalized
profiles at the grade `m` (`ProfileTower.lvl`).  **The admitted top**
(`ProfileTower.Lvl.Good.admittedTopCompletion`) is the admitted layer at the grade `m + 1` over `L`
(`ProfileTower.Lvl.admittedNextS`: one cell of full scope and grade `m + 1` per admitted profile,
with the row labelling of its profile).  Under

* the lift provisions at the grade `m + 1` for both coatoms (`ProfileTower.BotLiftProvision`,
  `ProfileTower.CapLiftProvision`), and
* the admission of the code of the glued labelling of the amalgam at `m + 1`,

it is a completion below the full grade whose rows of full scope at the grades `≥ m + 1` are
admitted (`Seed.exists_admittedCompletion_top`):

* legality below the full grade: well formed, coded, consistent (the layer on a sub-catalogue),
  complete (the cell of the code of the glued labelling at `(univ, m + 1)`), and bountiful
  (`CellScheme.Rows.isBountiful_of_coatoms`: off the ground set the lifts of the amalgam, from
  either coatom at the grades `j ≤ m` the lifts of the level, at `m + 1` the lift into the admitted
  layer, `ProfileTower.Lvl.Good.cappedLift_admittedNextS`);
* the lawful labelling extending the glued labelling: the extension at `⊥` of the glued labelling
  through its admitted code (`ProfileTower.Lvl.Good.exists_extensionOn_bot`);
* admitted rows: the row of a cell of full scope at `m + 1` is the splice of its profile, a reading
  row (`ProfileTower.Lvl.Good.row_rowAt_admittedNextS`).

The trivial admission (`Seed.Admission.all`) has the lift provisions at `m + 1`
(`ProfileTower.botLiftProvision_all_top`, `ProfileTower.capLiftProvision_all_top`: the fill of the
other coatom from the common face at the grade `m`, then within it from `m` to `m + 1`,
`Seed.exists_lift_union_of_le`), and admits every code; so every seed on at least four points has a
completion below the full grade whose top layer is a layer of rank-normalized profiles
(`Seed.nonempty_completionBelowFullGrade_of_all`).

Admitted layers at grades `≤ m` followed by further layers are not assembled here: the invariant of
a good level (`ProfileTower.Lvl.Good.lawful`) asks the section operator to be lawful at every
profile lawful on the cut, and after an admitted layer the section of a profile is the decoded row
labelling of its code, a lawful section only when the code is admitted.

## Placement

The engine of the restricted catalogue at the reading grades (`roadmap/README.md`, Layer 3, 3.1,
under "(R6)"); third and fourth pieces, at the top grade.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The fill of the other coatom at the top grade -/

/-- **The fill of the other coatom at the top grade `m + 1`**, for `0 < m`: a profile `f` lawful
below a coatom `(C, m + 1)`, agreeing below it with a profile `P` lawful on the cut capped at `h`
(self-visible at `m + 1`), agrees below `(C, m + 1)` with a profile lawful on the cut that agrees
with `P` capped at `h` everywhere.  The other coatom `D` is filled at the grade `m` by the capped
lift of the amalgam from `(C ∩ D, m)` to `(D, m)` at the ambient `P`, then from `m` to `m + 1`
within `D` (`Seed.exists_lift_union_of_le`: the common face carries no cell of the grade
`m + 1`). -/
theorem exists_isCutLawful_of_coatom_top (hm : 0 < m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {h : Label.{u}} (hh : IsSelfVisible (m + 1) h)
    {P : Prof I} (hP : IsCutLawful I (m + 1) P) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ f d)
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1), min (f d) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I (m + 1) W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1), W d = f d) ∧
      ∀ d, min (W d) h = min (P d) h := by
  classical
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hx hy hxy
  have hXf : ((univ.erase x ∩ univ.erase y, m) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces := ⟨hOf, hm, by simp only; rw [hOcard]⟩
  have hYf : ((univ.erase y, m) : Finset (Fin (m + 2)) × ℕ) ∈
      I.amalgam.toCellScheme.gradedFaces :=
    ⟨I.erase_mem_faces hy, hm, by simp only; rw [Seed.card_erase]; omega⟩
  have hXY : ((univ.erase x ∩ univ.erase y, m) : Finset (Fin (m + 2)) × ℕ) ≤ (univ.erase y, m) :=
    ⟨inter_subset_right, le_rfl⟩
  have hXC : ((univ.erase x ∩ univ.erase y, m) : Finset (Fin (m + 2)) × ℕ) ≤
      (univ.erase x, m + 1) := ⟨inter_subset_left, Nat.le_succ m⟩
  have hDD : ((univ.erase y, m) : Finset (Fin (m + 2)) × ℕ) ≤ (univ.erase y, m + 1) :=
    ⟨subset_rfl, Nat.le_succ m⟩
  -- The fill of the other coatom at the grade `m`.
  obtain ⟨v₁, hv₁, hv₁P, hv₁f⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (I.isBountiful hXf hYf hXY) h (hh.mono (Nat.le_succ m)) (fun d ↦ f d) (fun d ↦ P d)
    (hf.mono (X := (univ.erase x ∩ univ.erase y, m)) hXC)
    ((hP.erase hy).mono (X := (univ.erase y, m)) hDD)
    fun d ↦ (hfP d.1 (CellScheme.below_mono _ hXC d.2)).symm
  set w : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1) then f d
    else Rows.extendBot (univ.erase y, m) v₁ d with hw_def
  have hwv (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m)) : w d = v₁ ⟨d, hd⟩ := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)
    · rw [hw_def]
      simp only [hdC, ite_true]
      exact (hv₁f ⟨d, ⟨subset_inter hdC.1 hd.1, hd.2⟩⟩).symm
    · rw [hw_def]
      simp only [hdC, ite_false]
      exact Rows.extendBot_of_mem v₁ hd
  have hw : I.amalgam.rows.IsLawfulBelow (univ.erase y, m) fun d ↦ w d := by
    convert hv₁ using 1
    exact funext fun d ↦ hwv d d.2
  -- The fill within the other coatom from `m` to `m + 1`.
  obtain ⟨v, hv, hvw, hvP⟩ := I.exists_lift_union_of_le hx hy hxy (j := m) le_rfl hh
    (a := fun d ↦ P d) (hP.erase hy) hw fun d hd ↦ by rw [hwv d hd]; exact hv₁P ⟨d, hd⟩
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1) then f d
    else if hD : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1) then v ⟨d, hD⟩ else P d
    with hW
  have hWC (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)) : W d = f d :=
    ite_eq_left hd
  have hWD (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1)) :
      W d = v ⟨d, hd⟩ := by
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)
    · rw [hWC d hdC, hvw ⟨d, hd⟩ (.inl ⟨subset_inter hdC.1 hd.1, hd.2⟩), hw_def]
      simp only [hdC, ite_true]
    · rw [hW]
      simp only [hdC, hd, ite_false, dite_true]
  have hlC : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr fun d hd ↦ (hWC d hd).symm).mp hf
  have hlD : I.amalgam.rows.IsLawfulBelow (univ.erase y, m + 1) fun d ↦ W d := by
    convert hv using 1
    exact funext fun d ↦ hWD d d.2
  refine ⟨W, lawful_pair hx hy hxy hlC hlD, hWC, fun d ↦ ?_⟩
  by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1)
  · rw [hWC d hdC]; exact hfP d hdC
  by_cases hdD : d ∈ I.amalgam.toCellScheme.below (univ.erase y, m + 1)
  · rw [hWD d hdD]; exact hvP ⟨d, hdD⟩
  · rw [hW]
    simp only [hdC, hdD, ite_false, dite_false]

/-- **The trivial admission has the lift provision at `⊥` at the top grade.** -/
theorem botLiftProvision_all_top (N : ℕ) (hm : 0 < m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    BotLiftProvision (Seed.Admission.all I N) (m + 1) x := fun f hf ↦ by
  obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_top hm hx (isSelfVisible_bot _)
    (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
    fun _ _ ↦ by simp
  have hh := isCutLawful_hat hW
  refine ⟨W, hW, hWf, mem_admittedCat.mpr ⟨mem_cat.mpr ⟨⟨hh.1.orbitCode fun d ↦ d.2.2,
    hh.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, Seed.Admission.row_all N _⟩⟩

/-- **The trivial admission has the lift provision at the positive caps at the top grade.** -/
theorem capLiftProvision_all_top (N : ℕ) (hm : 0 < m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    CapLiftProvision (Seed.Admission.all I N) (m + 1) x := fun h hh _ _ P hP f hf hfP ↦ by
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom_top hm hx hh
    (mem_cat.mp (mem_admittedCat.mp hP).1).1 hf hfP
  exact ⟨W, hW, hWf, hWP, mem_admittedCat.mpr ⟨mem_cat.mpr ⟨⟨hW.1.orbitCode fun d ↦ d.2.2,
    hW.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, Seed.Admission.row_all N _⟩⟩

/-! ### The admitted top over the level at the grade `m` -/

section Top

variable {L : Lvl I m} {D : ℕ → Finset (Prof I)} (Rw : I.State → Prop)

/-- The old cells of the admitted top form a lower embedding of the amalgam. -/
theorem Lvl.GoodOn.isLowerEmbedding_nextSOn (hL : L.GoodOn D) (C : Finset (Prof I)) :
    I.amalgam.toCellScheme.IsLowerEmbedding (L.nextSOn C).toCellScheme (L.embedOn C) :=
  (Scheme.isLowerEmbedding_castAdd (S := L.S) (m + 1) C.card
    (fun i ↦ L.ΦOn C (entryOn C i)) L.not_le).comp hL.lowerEmb

/-- The rows of the admitted top pull back to those of the amalgam. -/
theorem Lvl.GoodOn.comap_rows_nextSOn (hL : L.GoodOn D) (C : Finset (Prof I)) :
    (L.nextSOn C).rows.comap (hL.isLowerEmbedding_nextSOn C) = I.amalgam.rows := by
  have h := Rows.comap_comap (L.nextSOn C).rows
    (Scheme.isLowerEmbedding_castAdd (S := L.S) (m + 1) C.card
      (fun i ↦ L.ΦOn C (entryOn C i)) L.not_le) hL.lowerEmb
  rw [Scheme.comap_rows_castAdd, hL.comap_rows] at h
  exact h.symm

/-- Every cell of the layer on `C` of scope other than the ground set is old. -/
theorem Lvl.GoodOn.mem_range_embedOn (hL : L.GoodOn D) {C : Finset (Prof I)}
    (z : Fin (L.nextSOn C).card) (hz : (L.nextSOn C).toCellScheme.scope z ≠ univ) :
    z ∈ Set.range (L.embedOn C) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  | left z =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hz
    obtain ⟨d, rfl⟩ := hL.mem_range z hz
    exact ⟨d, rfl⟩

/-- Every cell of the layer on `C` at the grade `m + 1` has grade below `m + 2`. -/
theorem Lvl.GoodOn.grade_nextSOn_lt (hL : L.GoodOn D) {C : Finset (Prof I)}
    (z : Fin (L.nextSOn C).card) : (L.nextSOn C).toCellScheme.grade z < m + 2 := by
  induction z using Fin.addCases with
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  | left z => rw [Scheme.appendFullCellsScheme_grade_castAdd]; exact hL.grade_lt z

/-- **Completeness below the full grade** of the layer on `C` at the grade `m + 1`, when `C` is
not empty. -/
theorem Lvl.GoodOn.exists_gradedIndex_eq_nextSOn (hL : L.GoodOn D) {C : Finset (Prof I)}
    (hC : C.Nonempty) (X : Finset (Fin (m + 2)) × ℕ)
    (hX : X ∈ (L.nextSOn C).toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ d, (L.nextSOn C).toCellScheme.gradedIndex d = X := by
  obtain ⟨B, j⟩ := X
  have hgi (e : Fin L.S.card) :
      (L.nextSOn C).toCellScheme.gradedIndex (Fin.castAdd _ e) = L.S.toCellScheme.gradedIndex e :=
    Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _
  by_cases hB : B = univ
  · subst hB
    have hj0 : 0 < j := hX.2.1
    simp only at hX2
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · obtain ⟨t, ht⟩ := hL.complete j hj0 (by omega)
      exact ⟨_, (hgi t).trans ht⟩
    · obtain rfl : j = m + 1 := by omega
      obtain ⟨R, hR⟩ := hC
      obtain ⟨i₀, -⟩ := exists_entryOn_eq hR
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩
  · have hfaces : (L.nextSOn C).toCellScheme.faces = I.amalgam.toCellScheme.faces := hL.faces
    obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (B, j) ⟨hfaces ▸ hX.1, hX.2⟩ hB
    exact ⟨Fin.castAdd _ (L.embed d), (hgi _).trans ((hL.gradedIndex_embed d).trans hd)⟩

/-- **The admitted top is bountiful**, under the lift provisions at `m + 1` for both coatoms
(`CellScheme.Rows.isBountiful_of_coatoms`). -/
theorem Lvl.GoodOn.isBountiful_admittedNextS (hL : L.GoodOn D)
    (hdown : ∀ R ∈ rowCat Rw (m + 1), code m R ∈ D m)
    (hbot : ∀ x ∈ (Pts : Finset (Fin (m + 2))), BotLiftProvisionOf Rw (m + 1) x)
    (hcap : ∀ x ∈ (Pts : Finset (Fin (m + 2))), CapLiftProvisionOf Rw (m + 1) x) :
    (L.nextSOn (rowCat Rw (m + 1))).rows.IsBountiful := by
  have hfull {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
      (j : ℕ) (hj : j ≤ #(univ.erase x)) :
      (L.nextSOn (rowCat Rw (m + 1))).rows.CappedLift (X := (univ.erase x, j))
        (Y := ((univ : Finset (Fin (m + 2))), j)) ⟨erase_subset _ _, le_rfl⟩ := by
    rw [Seed.card_erase] at hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact (Lvl.cappedLift_nextSOn_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr
        (hL.lift x hx j (by omega))
    · exact hL.cappedLift_nextSOn_rowCat Rw hdown le_rfl hx (hbot x hx) (hcap x hx)
  have hfaces : (L.nextSOn (rowCat Rw (m + 1))).toCellScheme.faces =
      I.amalgam.toCellScheme.faces := hL.faces
  have hgf : (L.nextSOn (rowCat Rw (m + 1))).toCellScheme.gradedFaces =
      I.amalgam.toCellScheme.gradedFaces := by
    unfold CellScheme.gradedFaces
    rw [hfaces]
  exact Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last (m + 1))
    (b := Fin.castSucc (Fin.last m)) (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ I.subset_or_subset B (hfaces ▸ hB) hne)
    (hfaces ▸ I.erase_last_mem_faces)
    (hfaces ▸ I.erase_castSucc_mem_faces)
    (fun X Y hX hY h hYne ↦ (Lvl.cappedLift_nextSOn_iff h fun h' ↦
      hYne (univ_subset_iff.mp h'.1)).mpr (hL.cappedLift_old (hgf ▸ hX) (hgf ▸ hY) hYne h))
    (hfull (by simp)) (hfull (by simp))

/-- **The admitted top is legal below the full grade.** -/
theorem Lvl.GoodOn.isLegalBelowFullGrade_admittedNextS (hL : L.GoodOn D)
    (hdown : ∀ R ∈ rowCat Rw (m + 1), code m R ∈ D m)
    (hbot : ∀ x ∈ (Pts : Finset (Fin (m + 2))), BotLiftProvisionOf Rw (m + 1) x)
    (hcap : ∀ x ∈ (Pts : Finset (Fin (m + 2))), CapLiftProvisionOf Rw (m + 1) x)
    (hne : (rowCat Rw (m + 1)).Nonempty) :
    (L.nextSOn (rowCat Rw (m + 1))).IsLegalBelowFullGrade where
  isWellFormed := hL.isWellFormed_nextSOn (by omega)
  isCoded := hL.isCoded_nextSOn (rowCat_subset Rw _)
  isConsistent := hL.isConsistent_nextSOn (rowCat_subset Rw _) hdown
  isBountiful := hL.isBountiful_admittedNextS Rw hdown hbot hcap
  grade_lt := hL.grade_nextSOn_lt
  exists_gradedIndex_eq := hL.exists_gradedIndex_eq_nextSOn hne

/-- **The glued labelling extends to a lawful section of the admitted top**, unchanged at the old
cells, when its code at `m + 1` is admitted (`ProfileTower.Lvl.Good.exists_extensionOn_bot`). -/
theorem Lvl.GoodOn.exists_isLawful_admittedNextS (hL : L.GoodOn D)
    (hdown : ∀ R ∈ rowCat Rw (m + 1), code m R ∈ D m)
    (hlab : code (m + 1) (fun d ↦ I.amalgam.label d) ∈ rowCat Rw (m + 1)) :
    ∃ q : Fin (L.nextSOn (rowCat Rw (m + 1))).card → Label.{u},
      (L.nextSOn (rowCat Rw (m + 1))).rows.IsLawful q ∧
      ∀ d, q (L.embedOn (rowCat Rw (m + 1)) d) = I.amalgam.label d := by
  obtain ⟨r, hr, hrW⟩ := hL.exists_extensionOn_bot (rowCat_subset Rw _) hdown hlab
  have hall (z : Fin (L.nextSOn (rowCat Rw (m + 1))).card) :
      z ∈ (L.nextSOn (rowCat Rw (m + 1))).toCellScheme.below
        ((univ : Finset (Fin (m + 2))), m + 1) :=
    ⟨subset_univ _, by
      have : (L.nextSOn (rowCat Rw (m + 1))).toCellScheme.grade z < m + 2 := hL.grade_nextSOn_lt z
      -- The second component of the graded index is the grade.
      change (L.nextSOn (rowCat Rw (m + 1))).toCellScheme.grade z ≤ m + 1
      omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_⟩
  have hd : I.amalgam.toCellScheme.grade d ≤ m + 1 := by have := I.grade_lt d; omega
  exact hrW d hd

/-- **The admitted top completion**: the admitted layer at the grade `m + 1` over a good level at
the grade `m`, with the glued labelling extended through its admitted code. -/
noncomputable def Lvl.GoodOn.admittedTopCompletion (hL : L.GoodOn D)
    (hdown : ∀ R ∈ rowCat Rw (m + 1), code m R ∈ D m)
    (hbot : ∀ x ∈ (Pts : Finset (Fin (m + 2))), BotLiftProvisionOf Rw (m + 1) x)
    (hcap : ∀ x ∈ (Pts : Finset (Fin (m + 2))), CapLiftProvisionOf Rw (m + 1) x)
    (hlab : code (m + 1) (fun d ↦ I.amalgam.label d) ∈ rowCat Rw (m + 1)) :
    CompletionBelowFullGrade I where
  scheme := L.nextSOn (rowCat Rw (m + 1))
  embed := L.embedOn (rowCat Rw (m + 1))
  isLowerEmbedding := hL.isLowerEmbedding_nextSOn _
  scope_embed d := congrArg Prod.fst (hL.gradedIndex_embedOn d)
  comap_rows := hL.comap_rows_nextSOn _
  mem_range_embed := hL.mem_range_embedOn
  faces_eq := hL.faces
  isLegalBelowFullGrade := hL.isLegalBelowFullGrade_admittedNextS Rw hdown hbot hcap ⟨_, hlab⟩
  label := (hL.exists_isLawful_admittedNextS Rw hdown hlab).choose
  isLawful := (hL.exists_isLawful_admittedNextS Rw hdown hlab).choose_spec.1
  label_embed := (hL.exists_isLawful_admittedNextS Rw hdown hlab).choose_spec.2

/-- **The admitted top completion has admitted rows from every grade `N ≥ m + 1`**: its cells of
full scope at the grades `≥ m + 1` are the new cells, whose rows are reading rows. -/
theorem Lvl.GoodOn.hasAdmittedRows_admittedTopCompletion (hL : L.GoodOn D)
    (hdown : ∀ R ∈ rowCat Rw (m + 1), code m R ∈ D m)
    (hbot : ∀ x ∈ (Pts : Finset (Fin (m + 2))), BotLiftProvisionOf Rw (m + 1) x)
    (hcap : ∀ x ∈ (Pts : Finset (Fin (m + 2))), CapLiftProvisionOf Rw (m + 1) x)
    (hlab : code (m + 1) (fun d ↦ I.amalgam.label d) ∈ rowCat Rw (m + 1))
    {N : ℕ} (hN : m + 1 ≤ N) :
    (hL.admittedTopCompletion Rw hdown hbot hcap hlab).HasAdmittedRows N Rw := by
  intro u j hu hj
  have hgu : (L.nextSOn (rowCat Rw (m + 1))).toCellScheme.grade u = j := congrArg Prod.snd hu
  have hlt : (L.nextSOn (rowCat Rw (m + 1))).toCellScheme.grade u < m + 2 := hL.grade_nextSOn_lt u
  obtain rfl : j = m + 1 := by omega
  obtain ⟨R, hR, hrow⟩ := hL.rowAt_nextSOn hu
  change Rw fun d ↦ (L.nextSOn (rowCat Rw (m + 1))).rowAt u (L.embedOn (rowCat Rw (m + 1)) d)
  rw [funext hrow]
  exact (mem_rowCat.mp hR).2

end Top

end VaughtConjecture.ProfileTower

namespace VaughtConjecture

open Finset Label ProfileTower

/-- **An admitted completion with the reading grade at the top**: for a seed on `m + 2 ≥ 4` points
and an admission `A` from a grade `A.N ≥ m + 1`, with the lift provisions at `m + 1` for both
coatoms and the code of the glued labelling admitted, some completion below the full grade has
admitted rows from `A.N` (the admitted top over the level at the grade `m`). -/
theorem Seed.exists_admittedCompletion_top {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    (hm : 2 ≤ m) (A : I.Admission) (hN : m + 1 ≤ A.N)
    (hbot : ∀ x ∈ (Pts : Finset (Fin (m + 2))), BotLiftProvision A (m + 1) x)
    (hcap : ∀ x ∈ (Pts : Finset (Fin (m + 2))), CapLiftProvision A (m + 1) x)
    (hlab : code (m + 1) (fun d ↦ I.amalgam.label d) ∈ admittedCat A (m + 1)) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows A.N A.Adm := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hL := lvl_good (I := I) hm j le_rfl
  have hL' := hL.toGoodOn fun k ↦ cat I k
  have hdown : ∀ R ∈ rowCat A.Row (j + 2 + 1), code (j + 2) R ∈ cat I (j + 2) :=
    fun R hR ↦ code_mem_cat_of_mem_cat (rowCat_subset _ _ hR)
  exact ⟨hL'.admittedTopCompletion A.Row hdown hbot hcap hlab, fun _ _ hu hj ↦
    (hL'.hasAdmittedRows_admittedTopCompletion A.Row hdown hbot hcap hlab hN hu hj).adm⟩

/-- **An admitted completion from an admission with the lift provisions**, from the grade
`A.N = m + 1`: the lift provisions are the fields of `Seed.LiftAdmission`. -/
theorem Seed.exists_admittedCompletion_of_liftAdmission {α : Ordinal.{u}} {m : ℕ}
    (I : Seed.{u} α m) (hm : 2 ≤ m) (A : I.LiftAdmission) (hN : A.N = m + 1)
    (hlab : code (m + 1) (fun d ↦ I.amalgam.label d) ∈ admittedCat A.toAdmission (m + 1)) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows A.N A.Adm :=
  I.exists_admittedCompletion_top hm A.toAdmission hN.ge
    (fun _ hx ↦ A.botLiftProvision hN.le le_rfl hx)
    (fun _ hx ↦ A.capLiftProvision hN.le le_rfl hx) hlab

/-- **Every seed on at least four points has a completion below the full grade whose top layer is
a layer of rank-normalized profiles**: the admitted top of the trivial admission. -/
theorem Seed.nonempty_completionBelowFullGrade_of_all {α : Ordinal.{u}} {m : ℕ}
    (I : Seed.{u} α m) (hm : 2 ≤ m) : Nonempty (CompletionBelowFullGrade I) := by
  have hlab : code (m + 1) (fun d ↦ I.amalgam.label d) ∈
      admittedCat (Seed.Admission.all I (m + 1)) (m + 1) := by
    have hW : IsCutLawful I (m + 1) fun d ↦ I.amalgam.label d :=
      ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
    have hh := isCutLawful_hat hW
    exact mem_admittedCat.mpr ⟨mem_cat.mpr ⟨⟨hh.1.orbitCode fun d ↦ d.2.2,
      hh.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, Seed.Admission.row_all _ _⟩
  obtain ⟨F, -⟩ := I.exists_admittedCompletion_top hm (Seed.Admission.all I (m + 1)) le_rfl
    (fun _ hx ↦ botLiftProvision_all_top _ (by omega) hx)
    (fun _ hx ↦ capLiftProvision_all_top _ (by omega) hx) hlab
  exact ⟨F⟩

end VaughtConjecture
