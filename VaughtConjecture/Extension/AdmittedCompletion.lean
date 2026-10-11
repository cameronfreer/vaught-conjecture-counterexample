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
(`ProfileTower.Lvl.GoodOn.admittedTopCompletion`) is the admitted layer at the grade `m + 1` over
`L` (`ProfileTower.Lvl.admittedNextS`: one cell of full scope and grade `m + 1` per admitted
profile, with the row labelling of its profile).  Under

* the lift provisions at the grade `m + 1` for both coatoms (`ProfileTower.BotLiftProvision`,
  `ProfileTower.CapLiftProvision`), and
* the admission of the code of the glued labelling of the amalgam at `m + 1`,

it is a completion below the full grade whose rows of full scope at the grades `≥ m + 1` are
admitted (`ProfileTower.Lvl.GoodOn.hasAdmittedRows_admittedTopCompletion`):

* legality below the full grade: well formed, coded, consistent (the layer on a sub-catalogue),
  complete (the cell of the code of the glued labelling at `(univ, m + 1)`), and bountiful
  (`CellScheme.Rows.isBountiful_of_coatoms`: off the ground set the lifts of the amalgam, from
  either coatom at the grades `j ≤ m` the lifts of the level, at `m + 1` the lift into the admitted
  layer, `ProfileTower.Lvl.GoodOn.cappedLift_admittedNextS`);
* the lawful labelling extending the glued labelling: the extension at `⊥` of the glued labelling
  through its admitted code (`ProfileTower.Lvl.GoodOn.exists_extensionOn_bot`);
* admitted rows: the row of a cell of full scope at `m + 1` is the splice of its profile, a reading
  row (`ProfileTower.Lvl.GoodOn.row_rowAt_admittedNextS`).

The whole catalogue at the top grade has the lift provisions
(`ProfileTower.botLiftProvisionIn_cat_top`, `ProfileTower.capLiftProvisionIn_cat_top` in
`VaughtConjecture.Extension.AdmittedTower`), from
the fill of the other coatom at the top grade (`ProfileTower.exists_isCutLawful_of_coatom_top`).
The levels below the top on sub-catalogues, good relative to a family (`ProfileTower.Lvl.GoodOn`),
are assembled in `VaughtConjecture.Extension.RowCompletionZero`.

## Placement

The completion below the full grade with admitted rows at the reading grades
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The fill of the other coatom at the top grade -/

/-- **The fill of the other coatom at the top grade `m + 1`**, for `0 < m`: a profile `f` lawful
below a coatom `(C, m + 1)`, agreeing below it with a profile `P` lawful on the cut capped at `h`
(self-visible at `m + 1`), agrees below `(C, m + 1)` with a profile lawful on the cut that agrees
with `P` capped at `h` everywhere (`ProfileTower.exists_isCutLawful_of_coatom_succ`, which holds
for every `m`). -/
theorem exists_isCutLawful_of_coatom_top (hm : 0 < m) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {h : Label.{u}} (hh : IsSelfVisible (m + 1) h)
    {P : Prof I} (hP : IsCutLawful I (m + 1) P) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ f d)
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1), min (f d) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I (m + 1) W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, m + 1), W d = f d) ∧
      ∀ d, min (W d) h = min (P d) h :=
  have _ := hm
  exists_isCutLawful_of_coatom_succ hx hh hP hf hfP

/-! ### The admitted top over the level at the grade `m` -/

section Top

variable {L : Lvl I m} {D : ℕ → Finset (Prof I)} (Rw : I.State → Prop)

/-- The old cells of the layer on `C` form a lower embedding of the amalgam. -/
theorem Lvl.GoodOn.isLowerEmbedding_nextSOn (hL : L.GoodOn D) (C : Finset (Prof I)) :
    I.amalgam.toCellScheme.IsLowerEmbedding (L.nextSOn C).toCellScheme (L.embedOn C) :=
  (Scheme.isLowerEmbedding_castAdd (S := L.S) (m + 1) C.card
    (fun i ↦ L.ΦOn C (entryOn C i)) L.not_le).comp hL.lowerEmb

/-- The rows of the layer on `C` pull back to those of the amalgam. -/
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
cells, when its code at `m + 1` is admitted (`ProfileTower.Lvl.GoodOn.exists_extensionOn_bot`). -/
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

end VaughtConjecture
