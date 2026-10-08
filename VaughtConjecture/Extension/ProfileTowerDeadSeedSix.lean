/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerDeadSeed
import VaughtConjecture.Extension.OrderedLayerTop

/-!
# A legal seed on six points whose cells below the grade `4` are dead

Roadmap, Layer 3 ((R4) of the table of 3.4): a test of cross-layer non-domination in the
completion of the profile tower, at a live old cell below the top grade.

**The completion of `deadSeed`** (`ProfileTowerDeadSeedSix.T6 α hα`).  The seed
`ProfileTowerDeadSeed.deadSeed` has bottom apexes (`Seed.hasBottomApexes_of_addApex`), and the
layer rows `ρ` that are `⊥` at the grades `k ≤ 3` and the top row at the grade `4` give the
ordered-layer step below the top grade: every cell below `(univ, k)`, `k ≤ 3`, is dead, so every
lawful labelling there is `⊥` and every capped lift is trivial.  So the ordered-layer step holds
(`Seed.OrderedLayerStepBelowTop.orderedLayerStep`), and its completion with the apex added is a
legal stage type `T6` on five points with face `D4` along the first four points.  Its cells of
grade at most `3` are dead and its cells of grade `4` read each other other than `⊥`.

**The seed** (`ProfileTowerDeadSeedSix.seedSix α hα`): the seed of `T6` with itself, on six
points.  Its cells of grade at most `3` are dead (`rowAt_seedSix_of_le`), and the cell of graded
index `(univ.erase 5, 4)`, of grade `4` and avoiding the last point, is live
(`exists_live_seedSix`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTowerDeadSeedSix

open Finset Label CellScheme OrderedLayer ProfileTowerDeadSeed

variable {α : Ordinal.{u}}

/-! ### The ordered-layer step of `deadSeed` -/

/-- The layer rows: `⊥` at the grades `k ≤ 3`, the top row at the grade `4`. -/
noncomputable def ρ : LayerRows.{u} := fun k X ↦ if k = 4 then topRow X else ⊥

theorem ρ_of_ne {k : ℕ} (hk : k ≠ 4) (X : Finset (Fin 5) × ℕ) : ρ.{u} k X = ⊥ :=
  ite_eq_right_iff.mpr fun h ↦ absurd h hk

theorem hasBottomApexes_deadSeed : (deadSeed α).HasBottomApexes :=
  Seed.hasBottomApexes_of_addApex (isLegalBelowFullGrade_D4₀ α) (isLegalBelowFullGrade_D4₀ α)
    (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

/-- **The rows of the layer scheme of `deadSeed` at the cells of grade at most `3` are `⊥`.** -/
theorem row_layerScheme_of_le (s : Fin (layerScheme (deadSeed α) ρ).card)
    (t : (layerScheme (deadSeed α) ρ).toCellScheme.below
      ((layerScheme (deadSeed α) ρ).toCellScheme.gradedIndex s))
    (hs : (layerScheme (deadSeed α) ρ).toCellScheme.grade s ≤ 3) :
    (layerScheme (deadSeed α) ρ).rows.row s t = ⊥ := by
  rcases cell_cases s with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨t, ht⟩ := t
    obtain ⟨d', rfl, hd'⟩ := exists_oldCell_of_mem_below ht
    rw [row_oldCell d d' ht hd']
    have hg : (deadSeed α).amalgam.toCellScheme.grade d ≤ 3 :=
      (congrArg Prod.snd (gradedIndex_oldCell (ρ := ρ) d)).symm.trans_le hs
    exact (row_deadSeed d _).1 hg
  · rw [row_newCell le_rfl (by omega), ρ_of_ne (by omega)]
  · rw [row_newCell (by omega) (by omega), ρ_of_ne (by omega)]
  · rw [row_newCell (by omega) (by omega), ρ_of_ne (by omega)]
  · rw [grade_newCell (by omega) le_rfl] at hs
    omega

/-- **The cells of grade `4` of the layer scheme of `deadSeed` read each other other than `⊥`.** -/
theorem row_layerScheme_four (s : Fin (layerScheme (deadSeed α) ρ).card)
    (t : (layerScheme (deadSeed α) ρ).toCellScheme.below
      ((layerScheme (deadSeed α) ρ).toCellScheme.gradedIndex s))
    (hs : (layerScheme (deadSeed α) ρ).toCellScheme.grade s = 4)
    (ht : (layerScheme (deadSeed α) ρ).toCellScheme.grade t.1 = 4) :
    (layerScheme (deadSeed α) ρ).rows.row s t ≠ ⊥ := by
  rcases cell_cases s with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨t, ht'⟩ := t
    obtain ⟨d', rfl, hd'⟩ := exists_oldCell_of_mem_below ht'
    rw [row_oldCell d d' ht' hd']
    have hg : (deadSeed α).amalgam.toCellScheme.grade d = 4 :=
      (congrArg Prod.snd (gradedIndex_oldCell (ρ := ρ) d)).symm.trans hs
    have hg' : (deadSeed α).amalgam.toCellScheme.grade d' = 4 :=
      (congrArg Prod.snd (gradedIndex_oldCell (ρ := ρ) d')).symm.trans ht
    exact fun h ↦ ((row_deadSeed d _).2 hg).mp h hg'
  · rw [grade_newCell le_rfl (by omega)] at hs; omega
  · rw [grade_newCell (by omega) (by omega)] at hs; omega
  · rw [grade_newCell (by omega) (by omega)] at hs; omega
  · rw [row_newCell (by omega) le_rfl]
    change (if (4 : ℕ) = 4 then topRow _ else ⊥) ≠ ⊥
    rw [ite_eq_left rfl, topRow]
    split
    · exact gridPoint_ne_bot 4 1
    · exact absurd ht ‹_›

/-- **The ordered-layer step below the top grade** for `deadSeed` and `ρ`: below `(univ, k)`,
`k ≤ 3`, every cell is dead, so every lawful labelling is `⊥`. -/
theorem orderedLayerStepBelowTop_deadSeed : (deadSeed α).OrderedLayerStepBelowTop ρ := by
  have hzero {k : ℕ} (hk : k ≤ 3) {X : Finset (Fin 5) × ℕ} (hXk : X.2 ≤ k)
      {p : (layerScheme (deadSeed α) ρ).toCellScheme.below X → Label.{u}}
      (hp : (layerScheme (deadSeed α) ρ).rows.IsLawfulBelow X p) (z) : p z = ⊥ :=
    CellScheme.Rows.IsLawful.eq_bot_of_row_self_eq_bot hp z
      (row_layerScheme_of_le z.1 _
        ((z.2 : (layerScheme (deadSeed α) ρ).toCellScheme.gradedIndex z.1 ≤ X).2.trans
          (hXk.trans hk)))
  refine ⟨fun k hk1 hk3 z _ ↦ ?_, fun k hk1 hk3 ↦ ?_, fun k hk1 hk3 ↦ ?_, fun k hk1 hk3 ↦ ?_⟩
  · rw [ρ_of_ne (by omega)]
    exact WithBot.bot_lt_coe _
  · simp only [ρ_of_ne (show k ≠ 4 by omega)]
    exact Rows.isLawfulBelow_const_bot _
  · refine (Rows.cappedLift_iff_forall_exists _).mpr fun c _ p q hp hq _ ↦
      ⟨q, hq, fun _ ↦ rfl, fun d ↦ ?_⟩
    rw [hzero hk3 le_rfl hq, hzero hk3 le_rfl hp]
  · refine (Rows.cappedLift_iff_forall_exists _).mpr fun c _ p q hp hq _ ↦
      ⟨q, hq, fun _ ↦ rfl, fun d ↦ ?_⟩
    rw [hzero hk3 le_rfl hq, hzero hk3 le_rfl hp]

theorem orderedLayerStep_deadSeed : (deadSeed α).OrderedLayerStep ρ :=
  orderedLayerStepBelowTop_deadSeed.orderedLayerStep hasBottomApexes_deadSeed
    (fun _ ↦ ite_eq_left rfl)

/-! ### The type `T6` -/

/-- **The type `T6`**: the completion of `deadSeed` from its ordered-layer step, with the apex. -/
noncomputable def T6 (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) : StageType.{u} α 5 :=
  (orderedLayerStep_deadSeed (α := α)).completion.completion hα

theorem isLegal_T6 (hα : Order.IsSuccPrelimit α) : (T6 α hα).IsLegal :=
  CompletionBelowFullGrade.isLegal_completion _ hα

theorem restrictFace_T6 (hα : Order.IsSuccPrelimit α) :
    StageType.restrictFace (Coatom.face 4) (T6 α hα) = some (D4 α) :=
  (StageType.restrictFace_addApex _ (Nat.succ_pos _) (Coatom.left 3)
    Coatom.univ_map_left_ne).trans
    ((orderedLayerStep_deadSeed (α := α)).completion.restrictFace_left_truncate hα)

/-- The rows of `T6`: `⊥` at the cells of grade at most `3`, and other than `⊥` between cells of
grade `4`. -/
theorem row_T6 (hα : Order.IsSuccPrelimit α) (s : Fin (T6 α hα).card)
    (i : (T6 α hα).toCellScheme.below ((T6 α hα).toCellScheme.gradedIndex s)) :
    ((T6 α hα).toCellScheme.grade s ≤ 3 → (T6 α hα).rows.row s i = ⊥) ∧
      ((T6 α hα).toCellScheme.grade s = 4 → (T6 α hα).toCellScheme.grade i = 4 →
        (T6 α hα).rows.row s i ≠ ⊥) := by
  change Fin ((layerScheme (deadSeed α) ρ).card + 1) at s
  induction s using Fin.lastCases with
  | last =>
    have h : (T6 α hα).toCellScheme.grade (Fin.last (layerScheme (deadSeed α) ρ).card) = 5 :=
      Scheme.appendFullCellScheme_grade_last _ _
    exact ⟨fun hs ↦ by omega, fun hs ↦ by omega⟩
  | cast z =>
    have hgz : (T6 α hα).toCellScheme.grade z.castSucc =
        (layerScheme (deadSeed α) ρ).toCellScheme.grade z :=
      Scheme.appendFullCellScheme_grade_castSucc _ _ z
    obtain ⟨i, hi⟩ := i
    change Fin ((layerScheme (deadSeed α) ρ).card + 1) at i
    induction i using Fin.lastCases with
    | last =>
      exfalso
      have h1 : (T6 α hα).toCellScheme.grade (Fin.last (layerScheme (deadSeed α) ρ).card) = 5 :=
        Scheme.appendFullCellScheme_grade_last _ _
      have h2 : (T6 α hα).toCellScheme.grade (Fin.last (layerScheme (deadSeed α) ρ).card) ≤
          (T6 α hα).toCellScheme.grade z.castSucc :=
        (hi : (T6 α hα).toCellScheme.gradedIndex (Fin.last (layerScheme (deadSeed α) ρ).card) ≤
          (T6 α hα).toCellScheme.gradedIndex z.castSucc).2
      have h3 := grade_le_four (I := deadSeed α) (ρ := ρ) z
      omega
    | cast w =>
      have hw : w ∈ (layerScheme (deadSeed α) ρ).toCellScheme.below
          ((layerScheme (deadSeed α) ρ).toCellScheme.gradedIndex z) :=
        (Scheme.appendFullCellScheme_gradedIndex_castSucc
          ((orderedLayerStep_deadSeed (α := α)).completion.truncate hα).toScheme 5 w).symm.trans_le
          (le_of_le_of_eq hi (Scheme.appendFullCellScheme_gradedIndex_castSucc
            ((orderedLayerStep_deadSeed (α := α)).completion.truncate hα).toScheme 5 z))
      have hgw : (T6 α hα).toCellScheme.grade w.castSucc =
          (layerScheme (deadSeed α) ρ).toCellScheme.grade w :=
        Scheme.appendFullCellScheme_grade_castSucc _ _ w
      have key : (T6 α hα).rows.row z.castSucc ⟨w.castSucc, hi⟩ =
          (layerScheme (deadSeed α) ρ).rows.row z ⟨w, hw⟩ := by
        have h1 : (T6 α hα).toScheme.rowAt z.castSucc w.castSucc =
            (layerScheme (deadSeed α) ρ).rowAt z w :=
          Scheme.rowAt_appendFullCell_castSucc
            (S := ((orderedLayerStep_deadSeed (α := α)).completion.truncate hα).toScheme)
            (j := 5) (r := StageType.apexRow
              (t := (orderedLayerStep_deadSeed (α := α)).completion.truncate hα)
              (orderedLayerStep_deadSeed (α := α)).completion.isLegalBelowFullGrade)
            (h := (orderedLayerStep_deadSeed (α := α)).completion.isLegalBelowFullGrade.not_le) z w
        rw [Scheme.rowAt_of_mem hi, Scheme.rowAt_of_mem hw] at h1
        exact h1
      rw [key, hgz]
      refine ⟨fun hs ↦ row_layerScheme_of_le z _ hs, fun hs ht ↦ ?_⟩
      rw [hgw] at ht
      exact row_layerScheme_four z ⟨w, hw⟩ hs ht

/-! ### The seed on six points -/

/-- **The seed of `T6` with itself** on six points: the coatoms `{0, 1, 2, 3, 4}` and
`{0, 1, 2, 3, 5}`, with common face `D4` on `{0, 1, 2, 3}`. -/
noncomputable def seedSix (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) : Seed.{u} α 4 :=
  Seed.ofCoatoms (isLegal_T6 hα) (isLegal_T6 hα) (restrictFace_T6 hα) (restrictFace_T6 hα)

/-- The rows of the amalgam of `seedSix` are those of `T6`. -/
theorem row_seedSix (hα : Order.IsSuccPrelimit α) (s : Fin (seedSix α hα).amalgam.card)
    (i : (seedSix α hα).amalgam.toCellScheme.below
      ((seedSix α hα).amalgam.toCellScheme.gradedIndex s)) :
    ((seedSix α hα).amalgam.toCellScheme.grade s ≤ 3 →
        (seedSix α hα).amalgam.rows.row s i = ⊥) ∧
      ((seedSix α hα).amalgam.toCellScheme.grade s = 4 →
        (seedSix α hα).amalgam.toCellScheme.grade i = 4 →
          (seedSix α hα).amalgam.rows.row s i ≠ ⊥) := by
  have hP := fun (s : Fin (T6 α hα).card)
    (i : (T6 α hα).toCellScheme.below ((T6 α hα).toCellScheme.gradedIndex s)) ↦ row_T6 hα s i
  rcases (seedSix α hα).subset_or_subset _
    ((seedSix α hα).amalgam.isWellFormed.isWellFormed.scope_mem s)
    ((seedSix α hα).scope_ne_univ s) with h | h
  · exact StageType.row_of_restrictFace (seedSix α hα).restrictFace_left
      (fun a b r ↦ (a ≤ 3 → r = ⊥) ∧ (a = 4 → b = 4 → r ≠ ⊥)) hP
      ((coe_subset.mpr (Coatom.univ_map_left ▸ h)).trans (coe_map_subset_range _ _)) i
  · exact StageType.row_of_restrictFace (seedSix α hα).restrictFace_right
      (fun a b r ↦ (a ≤ 3 → r = ⊥) ∧ (a = 4 → b = 4 → r ≠ ⊥)) hP
      ((coe_subset.mpr (Coatom.univ_map_right ▸ h)).trans (coe_map_subset_range _ _)) i

/-- **Every cell of grade at most `3` of `seedSix` is dead.** -/
theorem rowAt_seedSix_of_le (hα : Order.IsSuccPrelimit α) (d : Fin (seedSix α hα).amalgam.card)
    (hd : (seedSix α hα).amalgam.toCellScheme.grade d ≤ 3) :
    (seedSix α hα).amalgam.toScheme.rowAt d d = ⊥ := by
  rw [Scheme.rowAt_of_mem ((seedSix α hα).amalgam.toCellScheme.mem_below_gradedIndex _)]
  exact (row_seedSix hα d _).1 hd

/-- **A live cell of grade `4` avoiding the last point**: the cell at `(univ.erase 5, 4)`. -/
theorem exists_live_seedSix (hα : Order.IsSuccPrelimit α) :
    ∃ a : Fin (seedSix α hα).amalgam.card, (seedSix α hα).amalgam.toCellScheme.grade a = 4 ∧
      (seedSix α hα).amalgam.toScheme.rowAt a a ≠ ⊥ ∧
      Fin.last 5 ∉ (seedSix α hα).amalgam.toCellScheme.scope a := by
  have hC : ((univ.erase (Fin.last 5) : Finset (Fin 6)), 4) ∈
      (seedSix α hα).amalgam.toCellScheme.gradedFaces :=
    ⟨(seedSix α hα).erase_mem_faces (by simp), by omega, by simp⟩
  obtain ⟨a, ha⟩ := (seedSix α hα).exists_gradedIndex_eq _ hC (by simp [Finset.ext_iff])
  have hg : (seedSix α hα).amalgam.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  refine ⟨a, hg, ?_, ?_⟩
  · rw [Scheme.rowAt_of_mem ((seedSix α hα).amalgam.toCellScheme.mem_below_gradedIndex _)]
    exact (row_seedSix hα a _).2 hg hg
  · rw [show (seedSix α hα).amalgam.toCellScheme.scope a = univ.erase (Fin.last 5) from
      congrArg Prod.fst ha]
    simp

end VaughtConjecture.ProfileTowerDeadSeedSix
