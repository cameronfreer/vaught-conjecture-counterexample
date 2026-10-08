/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubledAmalgam
import VaughtConjecture.Extension.SourcePrefix

/-!
# The doubled completion at the arity one

Roadmap, Layer 3 ((R2) of the table of 3.4, the reading of the new tops at the cells labelled `⊤`);
the doublings of `VaughtConjecture.Continuation.SourceGapDoubling` and the amalgam of a type with
itself (`VaughtConjecture.Continuation.SourceGapDoubledAmalgam`).

Let `I : Seed α 1` be a seed on three points whose two coatom types are equal (`I.left = I.right`,
a legal stage type `T` on two points).  **The doubled completion** appends to the amalgam two
layers of cells of full scope:

* at grade `1`, one cell for each cell of `T` of graded index `(univ, 1)`
  (`Seed.doubledLower`);
* at grade `2`, one cell for each cell of `T` of graded index `(univ, 2)` (`Seed.doubled`);

the row of each new cell is the row of its cell of `T`, read through the cell map of the doubling
(`Seed.doubledCell`: the amalgam through `Seed.doublingCell`, a new cell at its cell of `T`).
There is no other cell of full scope: the cells of full scope at the reading grade are exactly the
copies of the cells of `T` of full scope, not a catalogue of all lawful labellings below them.

**Results** (compiled in this repository).

* `Seed.isDoubling_doubled`: the doubled completion is a doubling of `T`.
* `Seed.cappedLift_doubled_left`, `Seed.cappedLift_doubled_right`: the lifts from each coatom to the
  full face at every grade, by the symmetric fill (`Scheme.IsDoubling.cappedLift_coatom`).
* `Seed.isLegalBelowFullGrade_doubled`: legal below the full grade — well formed, coded,
  consistent (the new rows are pullbacks of lawful rows of `T`), bountiful (the lifts off the full
  face are those of the amalgam; from each coatom by the symmetric fill), of grades below `3`, and
  complete below the full grade (`T` is complete at `(univ, 1)` and `(univ, 2)`).
* `Seed.doubledCompletion`: the completion below the full grade, with the labelling of `T`
  through the cell map; its labels lie at the stage.
* `Seed.eq_of_isLawfulBelow_doubled` (the exclusion of the mixed labelling): every labelling lawful
  below `(univ, j)` takes one value on the cells over one cell of `T`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Scheme

variable {n : ℕ} (T : Scheme.{u} n)

/-- The cells of `T` of graded index `(univ, j)`. -/
noncomputable def fullCells (j : ℕ) : Finset (Fin T.card) :=
  univ.filter fun c ↦ T.toCellScheme.gradedIndex c = (univ, j)

/-- The enumeration of the cells of `T` of graded index `(univ, j)`. -/
noncomputable def fullCell (j : ℕ) (i : Fin (T.fullCells j).card) : Fin T.card :=
  ((T.fullCells j).equivFin.symm i).1

variable {T}

theorem gradedIndex_fullCell (j : ℕ) (i : Fin (T.fullCells j).card) :
    T.toCellScheme.gradedIndex (T.fullCell j i) = (univ, j) :=
  (mem_filter.mp ((T.fullCells j).equivFin.symm i).2).2

theorem exists_fullCell_eq {j : ℕ} {c : Fin T.card}
    (hc : T.toCellScheme.gradedIndex c = (univ, j)) : ∃ i, T.fullCell j i = c :=
  ⟨(T.fullCells j).equivFin ⟨c, mem_filter.mpr ⟨mem_univ _, hc⟩⟩, by simp [fullCell]⟩

/-- **A row is a lawful section**, for consistent rows: the row of a cell of graded index
`(univ, j)`, read at every cell, is lawful. -/
theorem isLawful_rowAt (hS : T.rows.IsConsistent) {c : Fin T.card} {j : ℕ}
    (hc : T.toCellScheme.gradedIndex c = (univ, j)) : T.rows.IsLawful (T.rowAt c) := by
  have h := T.isLawful_splice_bot (isLawfulBelow_rowAt hS hc)
  convert h using 1
  funext d
  by_cases hd : T.toCellScheme.grade d ≤ j
  · rw [CellScheme.splice_of_le hd]
  · rw [CellScheme.splice_of_lt (not_le.mp hd), rowAt_of_notMem]
    rw [CellScheme.mem_below, hc]
    exact fun h ↦ hd h.2

end Scheme

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1) (hLR : I.left = I.right)

/-- The number of cells of `T` of graded index `(univ, j)`. -/
noncomputable abbrev nFull (j : ℕ) : ℕ := (I.left.toScheme.fullCells j).card

/-- The cell map of the lower layer. -/
noncomputable def lowerCell : Fin (I.amalgam.card + I.nFull 1) → Fin I.left.card :=
  Fin.append (I.doublingCell hLR) (I.left.toScheme.fullCell 1)

/-- The rows of the lower layer: the rows of the cells of `T` of graded index `(univ, 1)`. -/
noncomputable def lowerRow (i : Fin (I.nFull 1)) (x : Fin (I.amalgam.card + I.nFull 1)) :
    Label.{u} :=
  I.left.rowAt (I.left.toScheme.fullCell 1 i) (I.lowerCell hLR x)

/-- **The lower layer** of the doubled completion: the copies at grade `1` of the cells of `T` of
graded index `(univ, 1)`. -/
noncomputable abbrev doubledLower : Scheme.{u} 3 :=
  I.amalgam.toScheme.appendFullCells 1 (I.nFull 1) (I.lowerRow hLR) (I.not_univ_le 1)

/-- No cell of the lower layer lies above `(univ, 2)`. -/
theorem not_univ_two_le_doubledLower (d : Fin (I.doubledLower hLR).card) :
    ¬ ((univ : Finset (Fin 3)), 2) ≤ (I.doubledLower hLR).toCellScheme.gradedIndex d := by
  induction d using Fin.addCases with
  | left d =>
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact I.not_univ_le 2 d
  | right i =>
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact fun h ↦ absurd h.2 (by decide)

/-- The cell map of the doubled completion. -/
noncomputable def doubledCell :
    Fin ((I.doubledLower hLR).card + I.nFull 2) → Fin I.left.card :=
  Fin.append (I.lowerCell hLR) (I.left.toScheme.fullCell 2)

/-- The rows of the layer at grade `2`: the rows of the cells of `T` of graded index `(univ, 2)`. -/
noncomputable def upperRow (i : Fin (I.nFull 2))
    (x : Fin ((I.doubledLower hLR).card + I.nFull 2)) : Label.{u} :=
  I.left.rowAt (I.left.toScheme.fullCell 2 i) (I.doubledCell hLR x)

/-- **The doubled completion**: the copies at grade `2` of the cells of `T` of graded index
`(univ, 2)` over the lower layer. -/
noncomputable abbrev doubled : Scheme.{u} 3 :=
  (I.doubledLower hLR).appendFullCells 2 (I.nFull 2) (I.upperRow hLR)
    (I.not_univ_two_le_doubledLower hLR)

/-- The lower layer is a doubling of `T`. -/
theorem isDoubling_doubledLower :
    (I.doubledLower hLR).IsDoubling I.left.toScheme (I.lowerCell hLR) :=
  (I.isDoubling_amalgam hLR).appendFullCells (Scheme.gradedIndex_fullCell 1)
    (fun _ hc ↦ Scheme.exists_fullCell_eq hc) fun _ _ ↦ rfl

/-- **The doubled completion is a doubling of `T`.** -/
theorem isDoubling_doubled :
    (I.doubled hLR).IsDoubling I.left.toScheme (I.doubledCell hLR) :=
  (I.isDoubling_doubledLower hLR).appendFullCells (Scheme.gradedIndex_fullCell 2)
    (fun _ hc ↦ Scheme.exists_fullCell_eq hc) fun _ _ ↦ rfl

/-! ### The old cells and the copies along the coatoms -/

/-- The old cells of the doubled completion. -/
noncomputable abbrev old (d : Fin I.amalgam.card) : Fin (I.doubled hLR).card :=
  Fin.castAdd _ (Fin.castAdd _ d)

theorem gradedIndex_old (d : Fin I.amalgam.card) :
    (I.doubled hLR).toCellScheme.gradedIndex (I.old hLR d) =
      I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _)

theorem doubledCell_old (d : Fin I.amalgam.card) :
    I.doubledCell hLR (I.old hLR d) = I.doublingCell hLR d := by
  rw [doubledCell, Fin.append_left, lowerCell, Fin.append_left]

/-- A cell of the doubled completion of scope other than the ground set is old. -/
theorem exists_old_eq {d : Fin (I.doubled hLR).card}
    (hd : (I.doubled hLR).toCellScheme.scope d ≠ univ) : ∃ a, I.old hLR a = d := by
  induction d using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hd
  | left d =>
    induction d using Fin.addCases with
    | right i =>
      exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
        (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hd
    | left a => exact ⟨a, rfl⟩

/-- The doubled completion is well formed. -/
theorem isWellFormed_doubled : (I.doubled hLR).IsWellFormed :=
  Scheme.isWellFormed_appendFullCells
    (Scheme.isWellFormed_appendFullCells I.amalgam.isWellFormed one_pos (by omega)) two_pos
    (by omega)

/-- Every cell of the doubled completion has positive grade. -/
theorem grade_pos_doubled (d : Fin (I.doubled hLR).card) :
    0 < (I.doubled hLR).toCellScheme.grade d :=
  ((I.isWellFormed_doubled hLR).isWellFormed.gradedIndex_mem d).2.1

/-- **The cells of full scope of the doubled completion**: one at each grade `1` and `2`, by the
completeness of `T`. -/
theorem exists_full_doubled (hI : I.left.IsLegal) {i : ℕ} (hi : 0 < i) (hi2 : i ≤ 2) :
    ∃ a, (I.doubled hLR).toCellScheme.gradedIndex a = ((univ : Finset (Fin 3)), i) := by
  obtain ⟨c, hc⟩ := hI.isComplete ((univ : Finset (Fin 2)), i)
    ⟨I.left.univ_mem_faces, hi, by simpa using hi2⟩
  obtain ⟨k, rfl⟩ := Scheme.exists_fullCell_eq hc
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · exact ⟨Fin.castAdd _ (Fin.natAdd _ k),
      (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
        (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ k)⟩
  · exact ⟨Fin.natAdd _ k, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ k⟩

/-- **The lift from the first coatom to the full face**, at every grade, by the symmetric fill. -/
theorem cappedLift_doubled_left (hI : I.left.IsLegal) {j : ℕ} (hj : j ≤ 2) :
    (I.doubled hLR).rows.CappedLift (X := (univ.erase (Fin.last 2), j))
      (Y := ((univ : Finset (Fin 3)), j)) ⟨erase_subset _ _, le_rfl⟩ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact (I.isWellFormed_doubled hLR).isWellFormed.cappedLift _ (Or.inl rfl) _
  have hL := I.restrictFace_left
  have h := (I.isDoubling_doubled hLR).cappedLift_coatom (f := Coatom.left 1) collapseLast_left
    (cp := fun z ↦ I.old hLR (StageType.faceCell hL z))
    (fun z ↦ by rw [doubledCell_old, doublingCell_faceCell_left])
    (fun z ↦ by
      rw [gradedIndex_old]
      exact Prod.ext (StageType.scope_faceCell _ _) (StageType.grade_faceCell _ _))
    (fun d hd ↦ by
      obtain ⟨a, rfl⟩ := I.exists_old_eq hLR (d := d) fun he ↦
        Coatom.univ_map_left_ne (subset_antisymm (subset_univ _) (he ▸ hd))
      have ha : I.amalgam.toCellScheme.scope a ⊆ univ.map (Coatom.left 1) := by
        have h1 : (I.doubled hLR).toCellScheme.scope (I.old hLR a) =
            I.amalgam.toCellScheme.scope a := congrArg Prod.fst (I.gradedIndex_old hLR a)
        rw [← h1]
        exact hd
      simp only
      rw [doubledCell_old, I.faceCell_left_of_subset hLR ha])
    (fun i hi hij ↦ I.exists_full_doubled hLR hI hi (hij.trans hj)) (I.grade_pos_doubled hLR)
  rw [Coatom.univ_map_left] at h
  exact h

/-- **The lift from the second coatom to the full face**, at every grade, by the symmetric
fill. -/
theorem cappedLift_doubled_right (hI : I.left.IsLegal) {j : ℕ} (hj : j ≤ 2) :
    (I.doubled hLR).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), j))
      (Y := ((univ : Finset (Fin 3)), j)) ⟨erase_subset _ _, le_rfl⟩ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact (I.isWellFormed_doubled hLR).isWellFormed.cappedLift _ (Or.inl rfl) _
  have hR := I.restrictFace_right_left hLR
  have h := (I.isDoubling_doubled hLR).cappedLift_coatom (f := Coatom.right 1) collapseLast_right
    (cp := fun z ↦ I.old hLR (StageType.faceCell hR z))
    (fun z ↦ by rw [doubledCell_old, doublingCell_faceCell_right])
    (fun z ↦ by
      rw [gradedIndex_old]
      exact Prod.ext (StageType.scope_faceCell _ _) (StageType.grade_faceCell _ _))
    (fun d hd ↦ by
      obtain ⟨a, rfl⟩ := I.exists_old_eq hLR (d := d) fun he ↦
        Coatom.univ_map_right_ne (subset_antisymm (subset_univ _) (he ▸ hd))
      have ha : I.amalgam.toCellScheme.scope a ⊆ univ.map (Coatom.right 1) := by
        have h1 : (I.doubled hLR).toCellScheme.scope (I.old hLR a) =
            I.amalgam.toCellScheme.scope a := congrArg Prod.fst (I.gradedIndex_old hLR a)
        rw [← h1]
        exact hd
      simp only
      rw [doubledCell_old, I.faceCell_right_of_subset hLR ha])
    (fun i hi hij ↦ I.exists_full_doubled hLR hI hi (hij.trans hj)) (I.grade_pos_doubled hLR)
  rw [Coatom.univ_map_right] at h
  exact h

/-- The old cells form a lower embedding of the amalgam. -/
theorem isLowerEmbedding_old :
    I.amalgam.toCellScheme.IsLowerEmbedding (I.doubled hLR).toCellScheme (I.old hLR) :=
  (Scheme.isLowerEmbedding_castAdd 2 _ _ _).comp (Scheme.isLowerEmbedding_castAdd 1 _ _ _)

/-- The rows pull back to those of the amalgam along the old cells. -/
theorem comap_rows_old :
    (I.doubled hLR).rows.comap (I.isLowerEmbedding_old hLR) = I.amalgam.rows := by
  change ((I.doubled hLR).rows.comap (Scheme.isLowerEmbedding_castAdd 2 _ _ _)).comap
    (Scheme.isLowerEmbedding_castAdd 1 _ _ _) = _
  rw [Scheme.comap_rows_castAdd, Scheme.comap_rows_castAdd]

/-- **Lifts off the full face** are those of the amalgam. -/
theorem cappedLift_doubled_of_ne_univ {X Y : Finset (Fin 3) × ℕ}
    (hX : X ∈ (I.doubled hLR).toCellScheme.gradedFaces)
    (hY : Y ∈ (I.doubled hLR).toCellScheme.gradedFaces) (hXY : X ≤ Y) (hYne : Y.1 ≠ univ) :
    (I.doubled hLR).rows.CappedLift hXY := by
  have h : I.amalgam.toCellScheme.IsSourcePrefix (I.doubled hLR).toCellScheme (I.old hLR) Y :=
    ⟨I.isLowerEmbedding_old hLR, fun t ↦ congrArg Prod.fst (I.gradedIndex_old hLR t),
      fun d hd ↦ I.exists_old_eq hLR (d := d) fun he ↦ hYne
        (subset_antisymm (subset_univ _) (he ▸ hd.1))⟩
  refine h.cappedLift_of_isBountiful ?_ hX hY hXY le_rfl
  rw [show (I.doubled hLR).rows.comap h.isLowerEmbedding = I.amalgam.rows from
    I.comap_rows_old hLR]
  exact I.isBountiful

/-- **The doubled completion is bountiful**, by the coatoms. -/
theorem isBountiful_doubled (hI : I.left.IsLegal) : (I.doubled hLR).rows.IsBountiful := by
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j ≤ 2 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simpa using hj
  exact Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces
    (fun X Y hX hY hXY hYne ↦ I.cappedLift_doubled_of_ne_univ hLR hX hY hXY hYne)
    (fun j hj ↦ I.cappedLift_doubled_left hLR hI (hle _ j hj))
    (fun j hj ↦ I.cappedLift_doubled_right hLR hI (hle _ j hj))

/-- **The doubled completion is consistent**: the new rows are pullbacks of lawful rows of `T`. -/
theorem isConsistent_doubled (hI : I.left.IsLegal) : (I.doubled hLR).rows.IsConsistent :=
  Scheme.isConsistent_appendFullCells
    (Scheme.isConsistent_appendFullCells I.isConsistent fun i ↦
      (I.isDoubling_doubledLower hLR).isLawful_comp
        (Scheme.isLawful_rowAt hI.isConsistent (Scheme.gradedIndex_fullCell 1 i)))
    fun i ↦ (I.isDoubling_doubled hLR).isLawful_comp
      (Scheme.isLawful_rowAt hI.isConsistent (Scheme.gradedIndex_fullCell 2 i))

/-- **The doubled completion is legal below the full grade.** -/
theorem isLegalBelowFullGrade_doubled (hI : I.left.IsLegal) :
    (I.doubled hLR).IsLegalBelowFullGrade where
  isWellFormed := I.isWellFormed_doubled hLR
  isCoded := Scheme.isCoded_appendFullCells
    (Scheme.isCoded_appendFullCells I.amalgam.isCoded fun _ _ ↦ I.left.isCoded.rowAt_lt _ _)
    fun _ _ ↦ I.left.isCoded.rowAt_lt _ _
  isConsistent := I.isConsistent_doubled hLR hI
  isBountiful := I.isBountiful_doubled hLR hI
  grade_lt d := by
    induction d using Fin.addCases with
    | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
    | left d =>
      induction d using Fin.addCases with
      | right i =>
        rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_grade_natAdd]
        omega
      | left a =>
        rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_grade_castAdd]
        exact I.grade_lt a
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    by_cases hC : C = univ
    · subst hC
      exact I.exists_full_doubled hLR hI hX.2.1 (by simp only at hX2; omega)
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨I.old hLR d, (I.gradedIndex_old hLR d).trans hd⟩

/-- **The doubled completion below the full grade**, with the labelling of `T` through the cell
map. -/
noncomputable def doubledCompletion (hI : I.left.IsLegal) : CompletionBelowFullGrade I where
  scheme := I.doubled hLR
  embed := (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)
  isLowerEmbedding := I.isLowerEmbedding_old hLR
  scope_embed d := congrArg Prod.fst (I.gradedIndex_old hLR d)
  comap_rows := I.comap_rows_old hLR
  mem_range_embed z hz := by
    obtain ⟨a, rfl⟩ := I.exists_old_eq hLR hz
    exact ⟨a, rfl⟩
  faces_eq := rfl
  isLegalBelowFullGrade := I.isLegalBelowFullGrade_doubled hLR hI
  label := I.left.label ∘ I.doubledCell hLR
  isLawful := (I.isDoubling_doubled hLR).isLawful_comp I.left.isLawful
  label_embed d := by
    change I.left.label (I.doubledCell hLR (I.old hLR d)) = _
    rw [doubledCell_old, I.label_amalgam hLR]

/-- The labels of the doubled completion lie at the stage. -/
theorem atStage_doubledCompletion (hI : I.left.IsLegal)
    (d : Fin (I.doubledCompletion hLR hI).scheme.card) :
    AtStage α ((I.doubledCompletion hLR hI).label d) :=
  I.left.atStage _

/-- **The exclusion of the mixed labelling**: a labelling lawful below `(univ, j)`, `j ≤ 2`, takes
one value on the cells over one cell of `T`; in particular on the two copies of a cell of `T` along
the two coatoms. -/
theorem eq_of_isLawfulBelow_doubled (hI : I.left.IsLegal) {j : ℕ} (hj : j ≤ 2)
    {w : Fin (I.doubled hLR).card → Label.{u}}
    (hw : (I.doubled hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), j) fun d ↦ w d)
    {d d' : Fin (I.doubled hLR).card}
    (hd : d ∈ (I.doubled hLR).toCellScheme.below ((univ : Finset (Fin 3)), j))
    (hd' : d' ∈ (I.doubled hLR).toCellScheme.below ((univ : Finset (Fin 3)), j))
    (hπ : I.doubledCell hLR d = I.doubledCell hLR d') : w d = w d' :=
  (I.isDoubling_doubled hLR).eq_of_isLawfulBelow hw
    (fun e he ↦ I.exists_full_doubled hLR hI (I.grade_pos_doubled hLR e) (he.2.trans hj)) hd hd' hπ

end Seed

end VaughtConjecture
