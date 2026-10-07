/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CrossedCouplingCounterexample
import VaughtConjecture.Extension.ProfileCatalogue

/-!
# The grade-`1` profile catalogue of `seedHG` separates both ways

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the profile catalogue of `VaughtConjecture.Extension.ProfileCatalogue` at the seed with two
opposite forced separations); semantic contract, items 2–4.

The legal seed `CrossedCouplingCounterexample.seedHG` (coatom types `TH` and `TG`) has two opposite
forced separations at the grade `1`: every completion below the full grade of it has two
different cells at `(univ, 1)`, one reading `({3}, 1)` strictly below `({4}, 1)` and one the
reverse (`CrossedCouplingCounterexample.exists_ne_seedHG`, from
`CompletionBelowFullGrade.exists_ne_of_forcesTop`), so one new cell per graded face of full scope
does not suffice.  The profile catalogue at the grade `1` has one new cell per normalized profile
lawful on the grade-`1` cut, so its multiplicity at `(univ, 1)` depends on the seed.  The profile
`profileD` (`1` at the cells of the kind `A` of `D`, the cells of grade `1` through the point `4`,
and `⊥` elsewhere) and the profile `profileC` (the same on `C`) are in the catalogue at the grade
`1` (`profileD_mem`, `profileC_mem`), and their two new cells are different and read `({3}, 1)` and
`({4}, 1)` in the two orders (`exists_separating_cells_seedHG`, compiled in this repository
(theorem named)): the two separations that `exists_ne_seedHG` asks of every completion.  This is a
statement about the cells and rows of the profile scheme of `seedHG`; its lifts are not studied
here (prospective).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ProfileCatalogue

open Finset Label CellScheme OrderedLayer
open CrossedCouplingCounterexample (TH TG seedHG kindC kindD labC labD labC_left labD_right
  isLawfulBelow_coatom exists_cells)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The graded indices of the kind `A` of the first coatom have grade `1` and contain `3`. -/
private theorem kindC_eq_one {X : Finset (Fin 5) × ℕ} (h : kindC X = 1) :
    X.2 = 1 ∧ (3 : Fin 5) ∈ X.1 := by
  unfold kindC at h
  split_ifs at h with h1
  · exact (by decide : ∀ Y ∈ ({({3}, 1), ({2, 3}, 1), ({1, 2, 3}, 1), ({0, 1, 2, 3}, 1)} :
      Finset (Finset (Fin 5) × ℕ)), Y.2 = 1 ∧ (3 : Fin 5) ∈ Y.1) X h1
  all_goals exact absurd h (by decide)

/-- The graded indices of the kind `A` of the second coatom have grade `1` and contain `4`. -/
private theorem kindD_eq_one {X : Finset (Fin 5) × ℕ} (h : kindD X = 1) :
    X.2 = 1 ∧ (4 : Fin 5) ∈ X.1 := by
  unfold kindD at h
  split_ifs at h with h1
  · exact (by decide : ∀ Y ∈ ({({4}, 1), ({2, 4}, 1), ({1, 2, 4}, 1), ({0, 1, 2, 4}, 1)} :
      Finset (Finset (Fin 5) × ℕ)), Y.2 = 1 ∧ (4 : Fin 5) ∈ Y.1) X h1
  all_goals exact absurd h (by decide)

/-- `![⊥, x, ⊥, ⊥] c` is `x` at the kind `1` and `⊥` elsewhere. -/
private theorem vec_eq (x : Label.{u}) (c : Fin 4) :
    (![⊥, x, ⊥, ⊥] : Fin 4 → Label.{u}) c = if c = 1 then x else ⊥ := by
  fin_cases c <;> rfl

variable (I) in
/-- The profile `1` at the cells of the kind `A` of the first coatom and `⊥` elsewhere. -/
noncomputable def profileC : Profile I :=
  fun d ↦ labC (gridPoint 1 0) ⊥ ⊥ (I.amalgam.toCellScheme.gradedIndex d)

variable (I) in
/-- The profile `1` at the cells of the kind `A` of the second coatom and `⊥` elsewhere. -/
noncomputable def profileD : Profile I :=
  fun d ↦ labD (gridPoint 1 0) ⊥ ⊥ (I.amalgam.toCellScheme.gradedIndex d)

/-- **`profileC` is in the catalogue at the grade `1`**, for a seed whose coatom types are `TH`
and `TG`. -/
theorem profileC_mem (hIL : I.left = TH α) (N : ℕ) : profileC I ∈ catalogue I N 1 := by
  refine mem_catalogue.mpr ⟨fun d ↦ ?_, ?_, ?_⟩
  · rw [profileC, labC, vec_eq]
    split_ifs with h
    · rw [show I.amalgam.toCellScheme.grade d = 1 from (kindC_eq_one h).1]
      exact gridPoint_mem_grid (Nat.zero_le N)
    · exact bot_mem_grid _ _
  · have h : I.amalgam.rows.IsLawfulBelow (coatomC, 3) fun d ↦ profileC I d := by
      rw [coatomC_eq]
      exact isLawfulBelow_coatom (isSelfVisible_gridPoint 1 0) (isSelfVisible_bot 2)
        (isSelfVisible_bot 3) (by simp [CrossedCouplingCounterexample.Coupled])
        (hIL ▸ I.restrictFace_left) (labC_left _ _ _)
    exact h.mono (X := (coatomC, 1)) ⟨subset_rfl, by omega⟩
  · refine (Rows.isLawfulBelow_congr (w' := fun _ ↦ ⊥) fun d hd ↦ ?_).mpr
      (Rows.isLawfulBelow_const_bot (coatomD, 1))
    rw [profileC, labC, vec_eq, ite_eq_right fun h ↦ ?_]
    exact absurd (hd.1 (kindC_eq_one h).2) (by decide)

/-- **`profileD` is in the catalogue at the grade `1`**, for a seed whose coatom types are `TH`
and `TG`. -/
theorem profileD_mem (hIR : I.right = TG α) (N : ℕ) : profileD I ∈ catalogue I N 1 := by
  refine mem_catalogue.mpr ⟨fun d ↦ ?_, ?_, ?_⟩
  · rw [profileD, labD, vec_eq]
    split_ifs with h
    · rw [show I.amalgam.toCellScheme.grade d = 1 from (kindD_eq_one h).1]
      exact gridPoint_mem_grid (Nat.zero_le N)
    · exact bot_mem_grid _ _
  · refine (Rows.isLawfulBelow_congr (w' := fun _ ↦ ⊥) fun d hd ↦ ?_).mpr
      (Rows.isLawfulBelow_const_bot (coatomC, 1))
    rw [profileD, labD, vec_eq, ite_eq_right fun h ↦ ?_]
    exact absurd (hd.1 (kindD_eq_one h).2) (by decide)
  · have h : I.amalgam.rows.IsLawfulBelow (coatomD, 3) fun d ↦ profileD I d := by
      rw [coatomD_eq]
      exact isLawfulBelow_coatom (isSelfVisible_gridPoint 1 0) (isSelfVisible_bot 2)
        (isSelfVisible_bot 3) (by simp [CrossedCouplingCounterexample.Coupled])
        (hIR ▸ I.restrictFace_right) (labD_right _ _ _)
    exact h.mono (X := (coatomD, 1)) ⟨subset_rfl, by omega⟩

/-- **The grade-`1` profile catalogue of `seedHG` separates both ways.**  In the profile scheme
of `seedHG` with top layer `J ≥ 1`, at every inventory bound `N`, two different new cells at
`(univ, 1)`, of the profiles `profileD` and `profileC`, read `({3}, 1)` strictly below `({4}, 1)`
and `({4}, 1)` strictly below `({3}, 1)` (the row of the `i`-th new cell of grade `1` is
`rows (seedHG α) N J 0 i`, `OrderedLayer.row_multiNewCell`). -/
theorem exists_separating_cells_seedHG (N J : ℕ) (hJ : 1 ≤ J) :
    ∃ (d₁ d₂ : Fin (seedHG α).amalgam.card) (i i' : Fin (mult (seedHG α) N J 0)),
      (seedHG α).amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      (seedHG α).amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧ i ≠ i' ∧
      rows (seedHG α) N J 0 i (multiOldCell _ _ d₁) <
        rows (seedHG α) N J 0 i (multiOldCell _ _ d₂) ∧
      rows (seedHG α) N J 0 i' (multiOldCell _ _ d₂) <
        rows (seedHG α) N J 0 i' (multiOldCell _ _ d₁) := by
  obtain ⟨d₁, d₂, hd₁, hd₂⟩ := exists_cells (I := seedHG α) rfl rfl
  obtain ⟨i, hi, he⟩ := exists_entry_eq (profileD_mem (I := seedHG α) rfl N)
  obtain ⟨i', hi', he'⟩ := exists_entry_eq (profileC_mem (I := seedHG α) rfl N)
  have hm : mult (seedHG α) N J 0 = (catalogue (seedHG α) N 1).card := mult_of_lt (by simpa)
  have hD₁ : profileD (seedHG α) d₁ = ⊥ := by rw [profileD, hd₁]; rfl
  have hD₂ : profileD (seedHG α) d₂ = gridPoint 1 0 := by rw [profileD, hd₂]; rfl
  have hC₁ : profileC (seedHG α) d₁ = gridPoint 1 0 := by rw [profileC, hd₁]; rfl
  have hC₂ : profileC (seedHG α) d₂ = ⊥ := by rw [profileC, hd₂]; rfl
  have hpos : (⊥ : Label.{u}) < gridPoint 1 0 := bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 1 0)
  refine ⟨d₁, d₂, ⟨i, hm ▸ hi⟩, ⟨i', hm ▸ hi'⟩, hd₁, hd₂, fun h ↦ ?_, ?_, ?_⟩
  · have h' : i = i' := congrArg Fin.val h
    subst h'
    have := congrFun (he.symm.trans he') d₁
    rw [hD₁, hC₁] at this
    exact gridPoint_ne_bot 1 0 this.symm
  · rw [rows_multiOldCell, rows_multiOldCell]
    -- The grade of the new cells is `0 + 1 = 1`.
    change entry (seedHG α) N 1 i d₁ < entry (seedHG α) N 1 i d₂
    rw [he, hD₁, hD₂]
    exact hpos
  · rw [rows_multiOldCell, rows_multiOldCell]
    -- The grade of the new cells is `0 + 1 = 1`.
    change entry (seedHG α) N 1 i' d₂ < entry (seedHG α) N 1 i' d₁
    rw [he', hC₁, hC₂]
    exact hpos

end VaughtConjecture.ProfileCatalogue
