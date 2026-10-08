/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerCross

/-!
# A legal seed whose cells below the top grade are all dead

Roadmap, Layer 3 ((R4) of the table of 3.4): a test of the cross separation of the profile tower
(`ProfileTower.CrossSeparating`).

**The low scheme** (`ProfileTowerDeadSeed.lowScheme n`): the interval plan on `n` points, one cell
for each of its graded faces of grade below `n`, and the bottom rows.  It is legal below the full
grade (`ProfileTowerDeadSeed.isLegalBelowFullGrade_lowScheme`).  **The type `D4`**: the low scheme
on four points with every label `⊥`, with the apex added (`StageType.addApex`).  It is legal; every
cell of grade at most `3` reads itself as `⊥` (its row is the bottom row), and the apex reads itself
other than `⊥` (`StageType.row_addApex`).

**The seed** (`ProfileTowerDeadSeed.deadSeed α`): the seed of `D4` with itself over its face
`{0, 1, 2}` (`Seed.ofCoatoms`), on five points.  Every cell of grade at most `3` of its amalgam is
dead, and the apex of the first coatom, of grade `4` with scope avoiding the last point, is live.
So cross separation from the grade `3` to the grade `4` fails at it
(`ProfileTowerDeadSeed.not_crossSeparating_deadSeed`, from
`ProfileTower.not_crossSeparating_of_dead`).  This refutes cross separation as a condition on every
seed; it refutes neither cross-layer non-domination nor (R4).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTowerDeadSeed

open Finset Label CellScheme

/-! ### The low scheme -/

/-- The graded faces of the interval plan on `Fin n` of grade below `n`. -/
noncomputable def lowGradedFaces (n : ℕ) : Finset (Finset (Fin n) × ℕ) :=
  {X ∈ Geometry.intervalPlan univ ×ˢ range n | 0 < X.2 ∧ X.2 ≤ #X.1}

/-- **The low scheme** on `n` points: the interval plan on `Fin n`, one cell for each of its graded
faces of grade below `n`, and the bottom rows. -/
noncomputable def lowScheme (n : ℕ) : Scheme.{u} n where
  card := #(lowGradedFaces n)
  toCellScheme := ⟨univ, Geometry.intervalPlan univ,
    fun d ↦ ((lowGradedFaces n).equivFin.symm d).1.1,
    fun d ↦ ((lowGradedFaces n).equivFin.symm d).1.2⟩
  rows := CellScheme.Rows.bot _

/-- **The low scheme is legal below the full grade**: the bottom rows are consistent and
bountiful, and every graded face of grade below `n` is the graded index of a cell. -/
theorem isLegalBelowFullGrade_lowScheme (n : ℕ) :
    (lowScheme.{u} n).IsLegalBelowFullGrade where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have h := ((lowGradedFaces n).equivFin.symm d).2
    simp only [lowGradedFaces, mem_filter, mem_product] at h
    exact ⟨h.1.1, h.2⟩⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isConsistent := CellScheme.Rows.isConsistent_bot
  isBountiful := CellScheme.Rows.isBountiful_bot
  grade_lt d := by
    have h := ((lowGradedFaces n).equivFin.symm d).2
    simp only [lowGradedFaces, mem_filter, mem_product, mem_range] at h
    exact h.1.2
  exists_gradedIndex_eq X hX hXn := by
    have hX' : X ∈ lowGradedFaces n := by
      obtain ⟨h₁, h₂, h₃⟩ := hX
      simp only [lowGradedFaces, mem_filter, mem_product, mem_range]
      exact ⟨⟨h₁, hXn⟩, h₂, h₃⟩
    exact ⟨(lowGradedFaces n).equivFin ⟨X, hX'⟩, by
      simp [CellScheme.gradedIndex, lowScheme]⟩

/-! ### The type `D4` -/

variable {α : Ordinal.{u}}

/-- The low scheme on four points with every label `⊥`. -/
noncomputable def D4₀ (α : Ordinal.{u}) : StageType.{u} α 4 :=
  ⟨lowScheme 4, fun _ ↦ ⊥, (isLegalBelowFullGrade_lowScheme 4).isWellFormed,
    (isLegalBelowFullGrade_lowScheme 4).isCoded, CellScheme.Rows.isLawful_const_bot,
    fun _ ↦ atStage_bot⟩

theorem isLegalBelowFullGrade_D4₀ (α : Ordinal.{u}) : (D4₀ α).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_lowScheme 4

/-- **The type `D4`**: the low scheme on four points with the apex added. -/
noncomputable def D4 (α : Ordinal.{u}) : StageType.{u} α 4 :=
  (D4₀ α).addApex (isLegalBelowFullGrade_D4₀ α) (by omega)

theorem isLegal_D4 (α : Ordinal.{u}) : (D4 α).IsLegal :=
  StageType.isLegal_addApex _ _

/-- The rows of `D4`: a cell of grade below `4` has the bottom row, and the row of a cell of grade
`4` is `⊥` exactly at the cells of grade below `4`. -/
theorem row_D4 (s : Fin (D4 α).card)
    (i : (D4 α).toCellScheme.below ((D4 α).toCellScheme.gradedIndex s)) :
    ((D4 α).toCellScheme.grade s ≤ 3 → (D4 α).rows.row s i = ⊥) ∧
      ((D4 α).toCellScheme.grade s = 4 →
        ((D4 α).rows.row s i = ⊥ ↔ (D4 α).toCellScheme.grade i ≠ 4)) := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ StageType.row_addApex _ _ (fun _ ↦ rfl) s hs i⟩
  change Fin ((D4₀ α).card + 1) at s
  induction s using Fin.lastCases with
  | last =>
    have h : (D4 α).toCellScheme.grade (Fin.last _) = 4 :=
      Scheme.appendFullCellScheme_grade_last _ _
    omega
  | cast d =>
    change dite _ _ _ = ⊥
    split
    · exact absurd ‹_› (Fin.castSucc_ne_last d)
    · rfl

theorem face_mem_D4 : univ.map (Coatom.face 3) ∈ (D4 α).toCellScheme.faces := by
  change univ.map (Coatom.face 3) ∈ Geometry.intervalPlan univ
  decide +kernel

/-- The face of `D4` on `{0, 1, 2}`. -/
noncomputable def faceD4 (α : Ordinal.{u}) : StageType.{u} α 3 :=
  (D4 α).comap (Coatom.face 3) face_mem_D4

theorem restrictFace_D4 (α : Ordinal.{u}) :
    StageType.restrictFace (Coatom.face 3) (D4 α) = some (faceD4 α) :=
  StageType.restrictFace_of_mem _ _ face_mem_D4

/-! ### The seed -/

/-- **The seed of `D4` with itself** on five points: the coatoms `{0, 1, 2, 3}` and
`{0, 1, 2, 4}`, with common face `{0, 1, 2}`. -/
noncomputable def deadSeed (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_D4 α) (isLegal_D4 α) (restrictFace_D4 α) (restrictFace_D4 α)

/-- The rows of the amalgam of `deadSeed` are those of `D4`. -/
theorem row_deadSeed (s : Fin (deadSeed α).amalgam.card)
    (i : (deadSeed α).amalgam.toCellScheme.below
      ((deadSeed α).amalgam.toCellScheme.gradedIndex s)) :
    ((deadSeed α).amalgam.toCellScheme.grade s ≤ 3 → (deadSeed α).amalgam.rows.row s i = ⊥) ∧
      ((deadSeed α).amalgam.toCellScheme.grade s = 4 →
        ((deadSeed α).amalgam.rows.row s i = ⊥ ↔
          (deadSeed α).amalgam.toCellScheme.grade i ≠ 4)) := by
  have hP := fun (s : Fin (D4 α).card)
    (i : (D4 α).toCellScheme.below ((D4 α).toCellScheme.gradedIndex s)) ↦ row_D4 s i
  rcases (deadSeed α).subset_or_subset _
    ((deadSeed α).amalgam.isWellFormed.isWellFormed.scope_mem s)
    ((deadSeed α).scope_ne_univ s) with h | h
  · exact StageType.row_of_restrictFace (deadSeed α).restrictFace_left
      (fun a b r ↦ (a ≤ 3 → r = ⊥) ∧ (a = 4 → (r = ⊥ ↔ b ≠ 4))) hP
      ((coe_subset.mpr (Coatom.univ_map_left ▸ h)).trans (coe_map_subset_range _ _)) i
  · exact StageType.row_of_restrictFace (deadSeed α).restrictFace_right
      (fun a b r ↦ (a ≤ 3 → r = ⊥) ∧ (a = 4 → (r = ⊥ ↔ b ≠ 4))) hP
      ((coe_subset.mpr (Coatom.univ_map_right ▸ h)).trans (coe_map_subset_range _ _)) i

/-- **Every cell of grade at most `3` of `deadSeed` is dead.** -/
theorem rowAt_deadSeed_of_le (d : Fin (deadSeed α).amalgam.card)
    (hd : (deadSeed α).amalgam.toCellScheme.grade d ≤ 3) :
    (deadSeed α).amalgam.toScheme.rowAt d d = ⊥ := by
  rw [Scheme.rowAt_of_mem ((deadSeed α).amalgam.toCellScheme.mem_below_gradedIndex _)]
  exact (row_deadSeed d _).1 hd

/-- **A live cell of grade `4` avoiding the last point**: the apex of the first coatom. -/
theorem exists_live_deadSeed :
    ∃ a : Fin (deadSeed α).amalgam.card, (deadSeed α).amalgam.toCellScheme.grade a = 4 ∧
      (deadSeed α).amalgam.toScheme.rowAt a a ≠ ⊥ ∧
      Fin.last 4 ∉ (deadSeed α).amalgam.toCellScheme.scope a := by
  have hC : ((univ.erase (Fin.last 4) : Finset (Fin 5)), 4) ∈
      (deadSeed α).amalgam.toCellScheme.gradedFaces :=
    ⟨(deadSeed α).erase_mem_faces (by simp), by omega, by simp⟩
  obtain ⟨a, ha⟩ := (deadSeed α).exists_gradedIndex_eq _ hC (by simp [Finset.ext_iff])
  have hg : (deadSeed α).amalgam.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  refine ⟨a, hg, ?_, ?_⟩
  · rw [Scheme.rowAt_of_mem ((deadSeed α).amalgam.toCellScheme.mem_below_gradedIndex _)]
    exact fun h ↦ ((row_deadSeed a _).2 hg).mp h hg
  · rw [show (deadSeed α).amalgam.toCellScheme.scope a = univ.erase (Fin.last 4) from
      congrArg Prod.fst ha]
    simp

/-- **Cross separation from the grade `3` to the grade `4` fails at `deadSeed`**: its cells of
grade at most `3` are dead and the apex of its first coatom is live
(`ProfileTower.not_crossSeparating_of_dead`). -/
theorem not_crossSeparating_deadSeed (α : Ordinal.{u}) :
    ¬ ProfileTower.CrossSeparating (deadSeed α) 3 4 := by
  obtain ⟨a, ha, hlive, hlast⟩ := exists_live_deadSeed (α := α)
  exact ProfileTower.not_crossSeparating_of_dead (by omega) rowAt_deadSeed_of_le ha hlive hlast

end VaughtConjecture.ProfileTowerDeadSeed
