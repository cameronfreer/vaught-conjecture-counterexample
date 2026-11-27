/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeThreeLocality

/-!
# The grade-three controllers of the attachment of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: one cell at `(univ, 3)` for each state of
the grade-three catalogue `ProcessRank.k2Cat3`, appended to the grade-two scheme
`ProcessRank.k2Grade2` (`ProcessRank.k2Grade3`), at the block bound `16`.

**The rows** (`ProcessRank.k2Phi3`).  The controller of a state `P` reads an old cell `z` of the
grade-two scheme as the section `k2Sec3 P z` (`ProcessRank.k2Grade3_rowAt_natAdd_castAdd`), and
the controller of a catalogue state `Q` as the agreement height `agreementHeight (grid 3 16) P Q`
(`ProcessRank.k2Grade3_rowAt_natAdd_natAdd`).  Every value lies in `codeGrid 3 16`
(`ProcessRank.k2Phi3_mem_codeGrid`).

**Lawfulness and consistency** (`ProcessRank.isLawful_k2Phi3`, `ProcessRank.isConsistent_k2Grade3`).
For a catalogue state the row is lawful on the enlarged scheme:
* every old cell lies below `(univ, 2)`, where the row is the section, lawful on the grade-two
  scheme (`ProcessRank.isLawful_k2Sec3`);
* at a new cell, of the catalogue state `Q`, the witness is the identity with the suppressor equal
  to `κ = agreementHeight (grid 3 16) P Q` up to the grade three: the sections agree capped at `κ`
  on the old cells (`ProcessRank.min_k2Sec3_eq`), and the agreement heights compare among the new
  cells by `Label.agreementHeight_tri`;
* availability at a new cell is witnessed by the controller of `P` itself, which reads the top
  `gridPoint 3 16` of the grid.
Consistency of the enlarged scheme is `Scheme.isConsistent_appendFullCells`.

Open: the extension of the prescribed top labels to the enlarged scheme, the mirror conditions at
the grade three (one-member reading, common shadows and twins of the new cells), the grade four,
legality of the completed scheme, the four-point span of mutual rigidity of the test pair, and the
countable upper bound on the Scott classes.  None of these is claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- **The row of the grade-three controller of a state**: the section on the old cells of the
grade-two scheme, the agreement heights in `grid 3 16` with the catalogue states on the new
cells. -/
noncomputable def k2Phi3 (P : Fin k2AttachmentBase.{u}.S.card → Label.{u}) :
    Fin (k2Grade2.{u}.card + k2Cat3.{u}.card) → Label.{u} :=
  Fin.append (k2Sec3 P) fun i ↦ agreementHeight (grid 3 16) P (k2Cat3.equivFin.symm i).1

theorem k2Phi3_castAdd (P : Fin k2AttachmentBase.{u}.S.card → Label.{u})
    (z : Fin k2Grade2.{u}.card) : k2Phi3 P (Fin.castAdd _ z) = k2Sec3 P z :=
  Fin.append_left _ _ z

theorem k2Phi3_natAdd (P : Fin k2AttachmentBase.{u}.S.card → Label.{u})
    (i : Fin k2Cat3.{u}.card) :
    k2Phi3 P (Fin.natAdd _ i) = agreementHeight (grid 3 16) P (k2Cat3.equivFin.symm i).1 :=
  Fin.append_right _ _ i

/-- **No cell of the grade-two scheme lies above `(univ, 3)`**: every cell has grade at most two. -/
theorem k2Grade2_not_le_three (z : Fin k2Grade2.{u}.card) :
    ¬ ((univ : Finset (Fin 4)), 3) ≤ k2Grade2.{u}.toCellScheme.gradedIndex z :=
  fun h ↦ absurd (le_trans h.2 (k2Grade2_grade_le z)) (by decide)

/-- **The grade-three scheme**: the grade-two scheme with one cell at `(univ, 3)` for each state of
the grade-three catalogue, reading through the row of that state. -/
noncomputable abbrev k2Grade3 : Scheme.{u} 4 :=
  k2Grade2.appendFullCells 3 k2Cat3.card (fun i ↦ k2Phi3 (k2Cat3.equivFin.symm i).1)
    k2Grade2_not_le_three

/-- Every cell of the grade-three scheme has grade at most three. -/
theorem k2Grade3_grade_le (z : Fin k2Grade3.{u}.card) : k2Grade3.{u}.toCellScheme.grade z ≤ 3 :=
  grade_appendFullCells_le (fun d ↦ (k2Grade2_grade_le d).trans (by decide)) le_rfl z

/-- Every cell of the grade-three scheme lies below `(univ, 3)`. -/
theorem k2Grade3_mem_below (z : Fin k2Grade3.{u}.card) :
    z ∈ k2Grade3.{u}.toCellScheme.below ((univ : Finset (Fin 4)), 3) :=
  ⟨subset_univ _, k2Grade3_grade_le z⟩

/-- The sections take values in the code grid of the grade three. -/
theorem k2Sec3_mem_codeGrid {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3)
    (z : Fin k2Grade2.{u}.card) : k2Sec3 P z ∈ codeGrid 3 16 :=
  upperDecoderAt_mem_codeGrid_of_mem (by decide) (mem_k2Cat3.mp hP).1
    (k2Phi_mem_codeGrid (orbitCode_mem_k2Cat2 hP) z)

/-- **The row of a grade-three catalogue state takes values in the code grid** `codeGrid 3 16`. -/
theorem k2Phi3_mem_codeGrid {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3)
    (z : Fin (k2Grade2.{u}.card + k2Cat3.{u}.card)) : k2Phi3 P z ∈ codeGrid 3 16 := by
  induction z using Fin.addCases with
  | left z =>
    rw [k2Phi3_castAdd]
    exact k2Sec3_mem_codeGrid hP z
  | right i =>
    rw [k2Phi3_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- **The row of a grade-three catalogue state is lawful below `(univ, 3)` on the grade-three
scheme.** -/
theorem isLawfulBelow_k2Phi3 {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3) :
    k2Grade3.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) fun z ↦ k2Phi3 P z := by
  classical
  have hold : k2Grade3.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2)
      fun z ↦ k2Phi3 P z := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff fun h ↦ absurd h.2 (by decide)).mpr ?_
    exact (CellScheme.Rows.isLawfulBelow_congr (w := fun d ↦ k2Sec3 P d)
      (w' := fun d ↦ k2Phi3 P (Fin.castAdd _ d)) fun d _ ↦ (k2Phi3_castAdd P d).symm).mp
        ((isLawful_k2Sec3 hP).isLawfulBelow _)
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hold
  have hcases (e : Fin k2Grade2.{u}.card) :
      Fin.castAdd k2Cat3.card e ∈ k2Grade3.{u}.toCellScheme.below ((univ : Finset (Fin 4)), 2) := by
    have hg : k2Grade3.{u}.toCellScheme.gradedIndex (Fin.castAdd k2Cat3.card e) =
        k2Grade2.{u}.toCellScheme.gradedIndex e :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e
    rw [CellScheme.mem_below, hg]
    exact k2Grade2_mem_below e
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (k2Cat3.equivFin.symm i₀).1 = P :=
    ⟨k2Cat3.equivFin ⟨P, hP⟩, by simp⟩
  refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun z _ ↦ ?_, fun s _ ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e => exact ho _ (hcases e)
    | right i =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, k2Phi3_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · induction s using Fin.addCases with
    | left e => exact hl _ (hcases e)
    | right i =>
      set κ := agreementHeight (grid 3 16) P (k2Cat3.equivFin.symm i).1 with hκ
      have hκm : κ ∈ grid 3 16 := (agreementHeight_spec (bot_mem_grid _ _) _ _).1
      have hκv : IsSelfVisible 3 κ := isSelfVisible_of_mem_grid hκm
      have hQ := (k2Cat3.equivFin.symm i).2
      refine ⟨constStepSuppressor 3 κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : k2Grade3.{u}.toCellScheme.grade t ≤ 3 := k2Grade3_grade_le t
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id, k2Phi3_natAdd,
        ← hκ]
      obtain ⟨t, -⟩ := t
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [k2Phi3_castAdd, k2Phi3_castAdd]
        exact min_k2Sec3_eq hP hQ e
      | right i' =>
        rw [k2Phi3_natAdd, k2Phi3_natAdd]
        exact agreementHeight_tri (bot_mem_grid _ _) _ _ _
  · induction t using Fin.addCases with
    | left e => exact ha s _ (hcases e) hst hg
    | right i =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [k2Phi3_natAdd, hi₀, agreementHeight_self (gridPoint_mem_grid le_rfl)
        (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
      exact le_gridPoint_of_mem_codeGrid (k2Phi3_mem_codeGrid hP s)

/-- **The row of a grade-three catalogue state is a lawful section of the grade-three scheme.** -/
theorem isLawful_k2Phi3 {P : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hP : P ∈ k2Cat3) :
    k2Grade3.{u}.rows.IsLawful fun z ↦ k2Phi3 P z :=
  (isLawfulBelow_k2Phi3 hP).isLawful k2Grade3_mem_below

/-- **The grade-three scheme has consistent rows** (`Scheme.isConsistent_appendFullCells`). -/
theorem isConsistent_k2Grade3 : k2Grade3.{u}.rows.IsConsistent :=
  Scheme.isConsistent_appendFullCells isConsistent_k2Grade2 fun i ↦
    isLawful_k2Phi3 (k2Cat3.equivFin.symm i).2

/-! ### The row equations -/

/-- **The row of a grade-three controller**: the controller of the `i`-th catalogue state reads
every cell of the grade-three scheme through the row of that state. -/
theorem k2Grade3_rowAt_natAdd (i : Fin k2Cat3.{u}.card) (z : Fin k2Grade3.{u}.card) :
    k2Grade3.{u}.rowAt (Fin.natAdd _ i) z = k2Phi3 (k2Cat3.equivFin.symm i).1 z := by
  have hz : z ∈ k2Grade3.{u}.toCellScheme.below
      (k2Grade3.{u}.toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact k2Grade3_mem_below z
  rw [Scheme.rowAt_of_mem hz, Scheme.appendFullCells_row_natAdd]

/-- **The old-cell equation**: a grade-three controller reads an old cell of the grade-two scheme
through the section of its state. -/
theorem k2Grade3_rowAt_natAdd_castAdd (i : Fin k2Cat3.{u}.card) (z : Fin k2Grade2.{u}.card) :
    k2Grade3.{u}.rowAt (Fin.natAdd _ i) (Fin.castAdd _ z) =
      k2Sec3 (k2Cat3.equivFin.symm i).1 z := by
  rw [k2Grade3_rowAt_natAdd, k2Phi3_castAdd]

/-- **The new-controller equation**: a grade-three controller reads another as the agreement
height in `grid 3 16` of their states. -/
theorem k2Grade3_rowAt_natAdd_natAdd (i i' : Fin k2Cat3.{u}.card) :
    k2Grade3.{u}.rowAt (Fin.natAdd _ i) (Fin.natAdd _ i') =
      agreementHeight (grid 3 16) (k2Cat3.equivFin.symm i).1 (k2Cat3.equivFin.symm i').1 := by
  rw [k2Grade3_rowAt_natAdd, k2Phi3_natAdd]

end VaughtConjecture.ProcessRank
