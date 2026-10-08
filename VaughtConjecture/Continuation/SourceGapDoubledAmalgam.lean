/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapDoubling
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Extension.SmallArities

/-!
# The amalgam of a type with itself is a doubling

Roadmap, Layer 3 ((R2) of the table of 3.4, the reading of the new tops at the cells labelled `⊤`);
the doublings of `VaughtConjecture.Continuation.SourceGapDoubling`.

**The symmetry hypothesis.**  A seed `I : Seed α m` whose two coatom types are **equal**,
`I.left = I.right`: the same stage type `T` on `m + 1` points is the face of the amalgam along the
first coatom (`Coatom.left m`, the points other than `m + 1`) and along the second
(`Coatom.right m`, the points other than `m`, with `m + 1` in the place of `m`).  So the point
`m + 1` of the second coatom plays the part of the point `m` of the first: the donor is the context
itself.

**The cell map** (`Seed.doublingCell`): a cell of the amalgam lies in one of the two coatoms
(`Seed.subset_or_subset`), and is the cell of the face `T` along that coatom at a cell of `T`.  A
cell in both coatoms (its scope avoids `m` and `m + 1`) is the same cell of `T` through both faces
(`Seed.faceCell_right_eq_left`, from `StageType.faceCell_faceCell`: both are the cell of the
common face).  The amalgam is a doubling of `T` along this map (`Seed.isDoubling_amalgam`,
compiled in this repository): grades are kept, scopes collapse, rows are those of `T` (the rows of
a face), and the copies of a cell of `T` along the two coatoms (`Seed.faceCell_left`,
`Seed.faceCell_right` of the faces) give the targets of availability.  The copies along each
coatom are the only cells over their cell inside that coatom (`Seed.faceCell_left_doublingCell`,
`Seed.faceCell_right_doublingCell`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- The face of the amalgam along the second coatom is the first coatom type, when the two coatom
types are equal. -/
theorem restrictFace_right_left (hLR : I.left = I.right) :
    StageType.restrictFace (Coatom.right m) I.amalgam = some I.left :=
  hLR ▸ I.restrictFace_right

/-- **Rows on a face**: the row of a cell of a face at a cell of the face is the row of the
corresponding cells. -/
private theorem rowAt_faceCell' {n k : ℕ} {E : StageType.{u} α n} {f : Fin k ↪ Fin n}
    {t : StageType.{u} α k} (h : StageType.restrictFace f E = some t) (i j : Fin t.card) :
    t.rowAt i j = E.rowAt (StageType.faceCell h i) (StageType.faceCell h j) := by
  obtain ⟨hf, rfl⟩ := (StageType.restrictFace_eq_some_iff E f).mp h
  have hle := E.toScheme.isLowerEmbedding_comap f
  -- the cells of a face are the cells of the cell map
  change (E.toScheme.comap f).rowAt i j = E.rowAt (E.toScheme.cellMap f i)
    (E.toScheme.cellMap f j)
  unfold Scheme.rowAt
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((hle.le_iff j i).mpr h1) h2
  · exact absurd ((hle.le_iff j i).mp h2) h1
  · rfl

variable (hLR : I.left = I.right)

/-- A cell of the amalgam visible through a face is a cell of that face. -/
private theorem exists_faceCell {n k : ℕ} {E : StageType.{u} α n} {f : Fin k ↪ Fin n}
    {t : StageType.{u} α k} (h : StageType.restrictFace f E = some t) {d : Fin E.card}
    (hd : d ∈ E.toScheme.visibleCells f) : ∃ z, StageType.faceCell h z = d :=
  E.toScheme.exists_faceCell_eq _ hd

/-- Every cell of the amalgam lies in one of the two coatoms. -/
theorem mem_visibleCells_or (d : Fin I.amalgam.card) :
    d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m) ∨
      d ∈ I.amalgam.toScheme.visibleCells (Coatom.right m) := by
  have h := I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.gradedIndex_mem d).1
    (I.scope_ne_univ d)
  rw [← Coatom.univ_map_left, ← Coatom.univ_map_right] at h
  simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]
  exact h

open Classical in
/-- **The cell map of the doubling**: the cell of `T = I.left` of which a cell of the amalgam is the
copy, through the first coatom when the cell lies in it, and through the second otherwise. -/
noncomputable def doublingCell (d : Fin I.amalgam.card) : Fin I.left.card :=
  if hd : d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m) then
    (exists_faceCell I.restrictFace_left hd).choose
  else
    (exists_faceCell (I.restrictFace_right_left hLR)
      ((I.mem_visibleCells_or d).resolve_left hd)).choose

theorem faceCell_left_doublingCell {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m)) :
    StageType.faceCell I.restrictFace_left (I.doublingCell hLR d) = d := by
  rw [doublingCell, dite_eq_left hd]
  exact (exists_faceCell I.restrictFace_left hd).choose_spec

/-- **The cells of the common face are the same through both coatoms.** -/
theorem faceCell_right_eq_left {z : Fin I.left.card}
    (hz : StageType.faceCell I.restrictFace_left z ∈
      I.amalgam.toScheme.visibleCells (Coatom.right m)) :
    StageType.faceCell (I.restrictFace_right_left hLR) z =
      StageType.faceCell I.restrictFace_left z := by
  have hlast : Fin.last m ∉ I.left.toCellScheme.scope z := by
    intro hm
    have h := Scheme.mem_visibleCells.mp hz
    have hmem : (Fin.last m).castSucc ∈ I.amalgam.toCellScheme.scope
        (StageType.faceCell I.restrictFace_left z) := by
      rw [StageType.scope_faceCell]
      exact mem_map_of_mem _ hm
    obtain ⟨y, hy⟩ := h hmem
    induction y using Fin.lastCases with
    | last =>
      rw [Coatom.right, extendByLast_last] at hy
      have h' := congrArg Fin.val hy
      simp at h'
    | cast y =>
      rw [Coatom.right, extendByLast_castSucc] at hy
      have h' := congrArg Fin.val hy
      simp at h'
      omega
  obtain ⟨i, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_face_left hlast
  exact (StageType.faceCell_faceCell (h := Fin.castSuccEmb) I.restrictFace_left
    (I.restrictFace_right_left hLR) I.restrictFace_face_left I.restrictFace_face_left i).symm

theorem faceCell_right_doublingCell {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toScheme.visibleCells (Coatom.right m)) :
    StageType.faceCell (I.restrictFace_right_left hLR) (I.doublingCell hLR d) = d := by
  by_cases hl : d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m)
  · have h := I.faceCell_left_doublingCell hLR hl
    rw [I.faceCell_right_eq_left hLR (h.symm ▸ hd), h]
  · rw [doublingCell, dite_eq_right hl]
    exact (exists_faceCell (I.restrictFace_right_left hLR)
      ((I.mem_visibleCells_or d).resolve_left hl)).choose_spec

/-- The cell map at a copy along the first coatom. -/
theorem doublingCell_faceCell_left (z : Fin I.left.card) :
    I.doublingCell hLR (StageType.faceCell I.restrictFace_left z) = z :=
  I.amalgam.toScheme.faceCell_injective _
    (I.faceCell_left_doublingCell hLR
      (I.amalgam.toScheme.faceCell_mem_visibleCells _ z))

/-- The cell map at a copy along the second coatom. -/
theorem doublingCell_faceCell_right (z : Fin I.left.card) :
    I.doublingCell hLR (StageType.faceCell (I.restrictFace_right_left hLR) z) = z :=
  I.amalgam.toScheme.faceCell_injective _
    (I.faceCell_right_doublingCell hLR
      (I.amalgam.toScheme.faceCell_mem_visibleCells _ z))

/-- The collapse is a retraction of the first coatom. -/
theorem collapseLast_left (i : Fin (m + 1)) : Scheme.collapseLast m (Coatom.left m i) = i :=
  Scheme.collapseLast_castSucc i

/-- The collapse is a retraction of the second coatom. -/
theorem collapseLast_right (i : Fin (m + 1)) : Scheme.collapseLast m (Coatom.right m i) = i :=
  Scheme.collapseLast_extendByLast i

/-- The scope of a cell of the amalgam is the image of the scope of its cell of `T` along the
coatom through which it is read. -/
theorem scope_eq_map (d : Fin I.amalgam.card) :
    (d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m) ∧
      I.amalgam.toCellScheme.scope d =
        (I.left.toCellScheme.scope (I.doublingCell hLR d)).map (Coatom.left m)) ∨
    (d ∈ I.amalgam.toScheme.visibleCells (Coatom.right m) ∧
      I.amalgam.toCellScheme.scope d =
        (I.left.toCellScheme.scope (I.doublingCell hLR d)).map (Coatom.right m)) := by
  rcases I.mem_visibleCells_or d with hd | hd
  · refine .inl ⟨hd, ?_⟩
    conv_lhs => rw [← I.faceCell_left_doublingCell hLR hd]
    exact StageType.scope_faceCell _ _
  · refine .inr ⟨hd, ?_⟩
    conv_lhs => rw [← I.faceCell_right_doublingCell hLR hd]
    exact StageType.scope_faceCell _ _

/-- **The amalgam of a type with itself is a doubling of the type.** -/
theorem isDoubling_amalgam :
    I.amalgam.toScheme.IsDoubling I.left.toScheme (I.doublingCell hLR) where
  grade_eq d := by
    rcases I.mem_visibleCells_or d with hd | hd
    · conv_rhs => rw [← I.faceCell_left_doublingCell hLR hd]
      exact (StageType.grade_faceCell _ _).symm
    · conv_rhs => rw [← I.faceCell_right_doublingCell hLR hd]
      exact (StageType.grade_faceCell _ _).symm
  scope_eq d := by
    rcases I.scope_eq_map hLR d with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h, Scheme.image_collapseLast_map collapseLast_left]
    · rw [h, Scheme.image_collapseLast_map collapseLast_right]
  rowAt_eq a d hd := by
    have hsub : I.amalgam.toCellScheme.scope d ⊆ I.amalgam.toCellScheme.scope a := hd.1
    by_cases ha : a ∈ I.amalgam.toScheme.visibleCells (Coatom.left m)
    · have hd' : d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m) := by
        simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and] at ha ⊢
        exact hsub.trans ha
      rw [rowAt_faceCell' I.restrictFace_left, I.faceCell_left_doublingCell hLR ha,
        I.faceCell_left_doublingCell hLR hd']
    · have ha' := (I.mem_visibleCells_or a).resolve_left ha
      have hd' : d ∈ I.amalgam.toScheme.visibleCells (Coatom.right m) := by
        simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and] at ha' ⊢
        exact hsub.trans ha'
      rw [rowAt_faceCell' (I.restrictFace_right_left hLR), I.faceCell_right_doublingCell hLR ha',
        I.faceCell_right_doublingCell hLR hd']
  exists_lift c e hc := by
    rcases I.scope_eq_map hLR e with ⟨he, hs⟩ | ⟨he, hs⟩
    · have hsc : I.left.toCellScheme.scope c =
          I.left.toCellScheme.scope (I.doublingCell hLR e) := by
        have h1 : I.left.toCellScheme.scope c = _ := congrArg Prod.fst hc
        rw [h1, hs, Scheme.image_collapseLast_map collapseLast_left]
      refine ⟨StageType.faceCell I.restrictFace_left c, I.doublingCell_faceCell_left hLR c, ?_⟩
      refine Prod.ext ?_ ?_
      · change I.amalgam.toCellScheme.scope _ = I.amalgam.toCellScheme.scope e
        rw [StageType.scope_faceCell, hs, hsc]
      · change I.amalgam.toCellScheme.grade _ = I.amalgam.toCellScheme.grade e
        rw [StageType.grade_faceCell]
        exact congrArg Prod.snd hc
    · have hsc : I.left.toCellScheme.scope c =
          I.left.toCellScheme.scope (I.doublingCell hLR e) := by
        have h1 : I.left.toCellScheme.scope c = _ := congrArg Prod.fst hc
        rw [h1, hs, Scheme.image_collapseLast_map collapseLast_right]
      refine ⟨StageType.faceCell (I.restrictFace_right_left hLR) c,
        I.doublingCell_faceCell_right hLR c, ?_⟩
      refine Prod.ext ?_ ?_
      · change I.amalgam.toCellScheme.scope _ = I.amalgam.toCellScheme.scope e
        rw [StageType.scope_faceCell, hs, hsc]
      · change I.amalgam.toCellScheme.grade _ = I.amalgam.toCellScheme.grade e
        rw [StageType.grade_faceCell]
        exact congrArg Prod.snd hc

/-- The copies along the first coatom are the only cells over their cells inside it. -/
theorem faceCell_left_of_subset {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.scope d ⊆ univ.map (Coatom.left m)) :
    StageType.faceCell I.restrictFace_left (I.doublingCell hLR d) = d :=
  I.faceCell_left_doublingCell hLR (by
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]; exact hd)

/-- The copies along the second coatom are the only cells over their cells inside it. -/
theorem faceCell_right_of_subset {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.scope d ⊆ univ.map (Coatom.right m)) :
    StageType.faceCell (I.restrictFace_right_left hLR) (I.doublingCell hLR d) = d :=
  I.faceCell_right_doublingCell hLR (by
    simp only [Scheme.visibleCells, mem_filter, mem_univ, true_and]; exact hd)

/-- The labels of the amalgam are those of `T` through the cell map. -/
theorem label_amalgam (d : Fin I.amalgam.card) :
    I.amalgam.label d = I.left.label (I.doublingCell hLR d) := by
  rcases I.mem_visibleCells_or d with hd | hd
  · conv_lhs => rw [← I.faceCell_left_doublingCell hLR hd]
    exact StageType.label_faceCell _ _
  · conv_lhs => rw [← I.faceCell_right_doublingCell hLR hd]
    exact StageType.label_faceCell _ _

end Seed

end VaughtConjecture
