/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubledCompletion
import VaughtConjecture.Extension.AdmittedFieldLayerLift

/-!
# The admitted field layer over the doubled lower layer

Roadmap, Layer 3, 3.1, (R6) (the completion below the full grade with a restricted catalogue at the
reading grades).

The engine of the admitted field layer at the arity one, for a seed on one point with equal coatom
types: the doubled lower layer (`Seed.doubledLower`) is consistent, well formed and coded
(`Seed.isConsistent_doubledLower`, `Seed.isWellFormed_doubledLower`, `Seed.isCoded_doubledLower`);
the admitted layer at the grade `2` over it is bountiful from the lifts of the lower layer at the
grade `1` and the two coatom lifts at the grade `2` (`Seed.isBountiful_admittedDoubledLower`), and
then legal below the full grade when the admission holds at `⊥`
(`Seed.isLegalBelowFullGrade_admittedDoubledLower`).  The coatom lifts come from the lift into an
admitted field layer (`Scheme.cappedLift_admittedFieldLayer`, in
`VaughtConjecture.Extension.AdmittedFieldLayerLift`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

/-! ### The admitted layer over the doubled lower layer, for a seed with equal coatom types -/

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right)
  {A : (Fin (I.doubledLower hLR).card → Label.{u}) → Prop}

/-- The doubled lower layer is consistent. -/
theorem isConsistent_doubledLower (hI : I.left.IsLegal) : (I.doubledLower hLR).rows.IsConsistent :=
  Scheme.isConsistent_appendFullCells I.isConsistent fun i ↦
    (I.isDoubling_doubledLower hLR).isLawful_comp
      (Scheme.isLawful_rowAt hI.isConsistent (Scheme.gradedIndex_fullCell 1 i))

/-- The doubled lower layer is well formed. -/
theorem isWellFormed_doubledLower : (I.doubledLower hLR).IsWellFormed :=
  Scheme.isWellFormed_appendFullCells I.amalgam.isWellFormed one_pos (by omega)

/-- The doubled lower layer is coded. -/
theorem isCoded_doubledLower : (I.doubledLower hLR).IsCoded :=
  Scheme.isCoded_appendFullCells I.amalgam.isCoded fun _ _ ↦ I.left.isCoded.rowAt_lt _ _

/-- The admitted layer over the doubled lower layer is well formed. -/
theorem isWellFormed_admittedDoubledLower :
    ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).IsWellFormed :=
  Scheme.isWellFormed_fieldLayerOn (I.isWellFormed_doubledLower hLR) two_pos (by omega)

/-- **Bountifulness of the admitted layer over the doubled lower layer**, from the lifts of the
lower layer at the grade `1` and the lifts from the two coatoms at the grade `2`: off the full face
by the amalgam (a source prefix), and from either coatom into the full face at every grade. -/
theorem isBountiful_admittedDoubledLower
    (h1L : (I.doubledLower hLR).rows.CappedLift (X := (univ.erase (Fin.last 2), 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩)
    (h1R : (I.doubledLower hLR).rows.CappedLift
      (X := (univ.erase (Fin.castSucc (Fin.last 1)), 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩)
    (hL : ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.CappedLift
        (X := (univ.erase (Fin.last 2), 2)) (Y := ((univ : Finset (Fin 3)), 2))
          ⟨erase_subset _ _, le_rfl⟩)
    (hR : ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2)) (Y := ((univ : Finset (Fin 3)), 2))
          ⟨erase_subset _ _, le_rfl⟩) :
    ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.IsBountiful := by
  set F := (I.doubledLower hLR).admittedFieldLayer 2 A (I.not_univ_two_le_doubledLower hLR)
  have hemb := Scheme.isLowerEmbedding_castAdd (S := I.doubledLower hLR) 2
    ((I.doubledLower hLR).admittedCatalogue 2 A).card
    (fun i ↦ (I.doubledLower hLR).fieldRowOn 2 ((I.doubledLower hLR).admittedCatalogue 2 A)
      (Scheme.entryOn _ i)) (I.not_univ_two_le_doubledLower hLR)
  have hlow := Scheme.isLowerEmbedding_castAdd (S := I.amalgam.toScheme) 1 (I.nFull 1)
    (I.lowerRow hLR) (I.not_univ_le 1)
  have e1 : F.rows.comap hemb = (I.doubledLower hLR).rows :=
    Scheme.comap_rows_castAdd (S := I.doubledLower hLR) (k := 2)
      (M := ((I.doubledLower hLR).admittedCatalogue 2 A).card)
      (r := fun i ↦ (I.doubledLower hLR).fieldRowOn 2 ((I.doubledLower hLR).admittedCatalogue 2 A)
        (Scheme.entryOn _ i)) (h := I.not_univ_two_le_doubledLower hLR)
  have e2 : (I.doubledLower hLR).rows.comap hlow = I.amalgam.rows :=
    Scheme.comap_rows_castAdd (S := I.amalgam.toScheme) (k := 1) (M := I.nFull 1)
      (r := I.lowerRow hLR) (h := I.not_univ_le 1)
  -- the lower layer is a source prefix below `(univ, 1)`
  have hsp1 : (I.doubledLower hLR).toCellScheme.IsSourcePrefix F.toCellScheme (Fin.castAdd _)
      ((univ : Finset (Fin 3)), 1) :=
    ⟨hemb, Scheme.appendFullCellsScheme_scope_castAdd _ _ _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below (fun h ↦ absurd h.2 (by omega)) hd⟩, rfl⟩⟩
  have hone (U : Finset (Fin 3)) (hU : (I.doubledLower hLR).rows.CappedLift (X := (U, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩) : F.rows.CappedLift
        (X := (U, 1)) (Y := ((univ : Finset (Fin 3)), 1)) ⟨subset_univ _, le_rfl⟩ := by
    refine (hsp1.cappedLift_iff _ le_rfl).mp ?_
    change (F.rows.comap hemb).CappedLift _
    rw [e1]
    exact hU
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ 2 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  have hfull (z : Fin 3) (hlift1 : (I.doubledLower hLR).rows.CappedLift (X := (univ.erase z, 1))
      (Y := ((univ : Finset (Fin 3)), 1)) ⟨erase_subset _ _, le_rfl⟩)
      (hlift2 : F.rows.CappedLift (X := (univ.erase z, 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩) (j : ℕ) (hj : j ≤ 2) :
      F.rows.CappedLift (X := (univ.erase z, j)) (Y := ((univ : Finset (Fin 3)), j))
        ⟨erase_subset _ _, le_rfl⟩ := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact (I.isWellFormed_admittedDoubledLower hLR).isWellFormed.cappedLift _ (Or.inl rfl) _
    · exact hone _ hlift1
    · exact hlift2
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces (fun X Y hX hY hXY hYne ↦ ?_)
    (fun j hj ↦ hfull _ h1L hL j (hle _ j hj)) (fun j hj ↦ hfull _ h1R hR j (hle _ j hj))
  -- off the full face: the amalgam is a source prefix
  have h : I.amalgam.toCellScheme.IsSourcePrefix F.toCellScheme
      (fun d ↦ Fin.castAdd _ (Fin.castAdd _ d)) Y := by
    refine ⟨hemb.comp hlow, fun t ↦
        (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _), fun d hd ↦ ?_⟩
    have hsc : F.toCellScheme.scope d ≠ univ := fun he ↦
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
  have hc : F.rows.comap h.isLowerEmbedding = I.amalgam.rows := by
    change ((F.rows.comap hemb).comap hlow) = _
    rw [e1, e2]
  rw [hc]
  exact I.isBountiful

/-- **Legality below the full grade of the admitted layer over the doubled lower layer**, when it
is bountiful and the constant `⊥` is admitted. -/
theorem isLegalBelowFullGrade_admittedDoubledLower (hI : I.left.IsLegal) (hA0 : A fun _ ↦ ⊥)
    (hb : ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).rows.IsBountiful) :
    ((I.doubledLower hLR).admittedFieldLayer 2 A
      (I.not_univ_two_le_doubledLower hLR)).IsLegalBelowFullGrade where
  isWellFormed := I.isWellFormed_admittedDoubledLower hLR
  isCoded := Scheme.isCoded_admittedFieldLayer (I.isCoded_doubledLower hLR)
  isConsistent := Scheme.isConsistent_admittedFieldLayer (I.isConsistent_doubledLower hLR hI)
  isBountiful := hb
  grade_lt d := by
    induction d using Fin.addCases with
    | left e =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      induction e using Fin.addCases with
      | left a =>
        rw [Scheme.appendFullCellsScheme_grade_castAdd]
        exact I.grade_lt a
      | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
    | right i =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd]
      omega
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    by_cases hC : C = univ
    · subst hC
      have hj0 : 0 < j := hX.2.1
      have hj3 : j < 3 := hX2
      rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
      · obtain ⟨c, hc⟩ := hI.isComplete ((univ : Finset (Fin 2)), 1)
          ⟨I.left.univ_mem_faces, one_pos, by simp⟩
        obtain ⟨i₀, -⟩ := Scheme.exists_fullCell_eq hc
        exact ⟨Fin.castAdd _ (Fin.natAdd _ i₀),
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
            (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀)⟩
      · exact Scheme.exists_gradedIndex_eq_admittedFieldLayer hA0
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨Fin.castAdd _ (Fin.castAdd _ d),
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _)).trans hd⟩

end Seed

end VaughtConjecture
