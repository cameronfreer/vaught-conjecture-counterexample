/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TopReadingLift

/-!
# Raising an isolated cell to `⊤`, and the separating fill at an apex marker

Roadmap, Layer 3 ((R3) of the table of 3.4).

`TowerProfile.exists_top_reads_lt_markedTop_of_raise` reduces the separating fill at the marked
top to a raise of the marker `r` within a coatom at the grade `4`.  This file proves the raise when
`r` is **isolated**: it is the only cell at or above its graded index below the coatom, and its row
reads every other cell below it as `⊥` and itself not as `⊥` (the shape of an apex added to a type
labelled `⊥`, `StageType.addApex`).

* **Raising an isolated cell** (`CellScheme.Rows.IsLawfulBelow.update_top`, compiled in this
  repository (theorem named)): a labelling lawful below `X` and not `⊥` at an isolated cell `r`
  stays lawful below `X` when its value at `r` is replaced by `⊤`.  Locality at `r` reads only
  `r`, and the labelling is `⊥` at the other cells below `r` (locality of the given labelling, not
  `⊥` at `r`); no other row reads `r`; availability at the graded index of `r` is served by `r`.
* **The separating fill at an isolated marker**
  (`TowerProfile.exists_top_reads_lt_markedTop_of_isolated`, compiled in this repository (theorem
  named)): for every marked specification of every seed on five
  points, every lawful section of the marked top that labels an isolated cell `r` of the grade `4`
  of a coatom with `⊤`, and every cell `x` of grade at most `3`, some new cell labelled `⊤` has an
  entry reading `x` strictly below `r`.  The new cell labelled `⊤` given by availability at `r`
  either reads `x` below `r` already, or its entry raised to `⊤` at `r` is the raise
  (`TowerProfile.exists_top_reads_lt_markedTop_of_raise`).  No fill hypothesis remains.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

open Scheme

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (D : MarkedSpec I)

/-- **The separating fill at an isolated marker.**  For every marked specification `D`, every lawful
section `q` of the marked top labelling `⊤` a cell `r` of the profile layer of the grade `4` below
the coatom `(univ.erase z₁, 4)`, isolated there (the only cell below the coatom at or above its
graded index, read by its own row only at itself, and there not as `⊥`), and every cell `x` of grade
at most `3`, some new cell labelled `⊤` has an entry reading `x` strictly below `r`. -/
theorem exists_top_reads_lt_markedTop_of_isolated {q : Fin (markedTop I D).card → Label.{u}}
    (hq : (markedTop I D).rows.IsLawful q) {x r : Fin (scheme I).card}
    (hgr : (scheme I).toCellScheme.grade r = 4) (hgx : (scheme I).toCellScheme.grade x ≤ 3)
    (hqr : q (Fin.castAdd _ r) = ⊤) {z₁ z₂ : Fin 5}
    (hz₁ : z₁ ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hz₂ : z₂ ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hz : z₁ ≠ z₂)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase z₁, 4))
    (huniq : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase z₁, 4),
      (scheme I).toCellScheme.gradedIndex r ≤ (scheme I).toCellScheme.gradedIndex y → y = r)
    (hrow : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
      y ≠ r → (scheme I).rows.row r ⟨y, hy⟩ = ⊥)
    (hrr : (scheme I).rows.row r ⟨r, (scheme I).toCellScheme.mem_below_gradedIndex r⟩ ≠ ⊥) :
    ∃ j, q (Fin.natAdd _ j) = ⊤ ∧
      (scheme I).markedEntry 4 D.marks j x < (scheme I).markedEntry 4 D.marks j r := by
  classical
  have hε := markedEntry_mem_spec D
  -- a new cell labelled `⊤`, by availability at `r`
  obtain ⟨i₀, -⟩ := exists_catalogueEntry_eq (orbitCode_splice_bot_mem_catalogue
    (S := scheme I) (k := 4) (p := fun _ ↦ ⊥) (CellScheme.Rows.isLawfulBelow_const_bot _))
  obtain ⟨v, hv, hle⟩ := hq.availability (Fin.castAdd _ r) (Fin.natAdd _ (Fin.castAdd _ i₀))
    (by rw [appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    (by rw [appendFullCellsScheme_grade_natAdd, appendFullCellsScheme_grade_castAdd, hgr])
  obtain ⟨j, rfl⟩ := exists_natAdd_eq_sheetLayer (hS := not_univ_four_le)
    (hv.trans (appendFullCellsScheme_gradedIndex_natAdd _ _ _ _))
  have hqj : q (Fin.natAdd _ j) = ⊤ := top_le_iff.mp (hqr ▸ hle)
  obtain ⟨e, he_def⟩ : ∃ e, e = (scheme I).markedEntry 4 D.marks j := ⟨_, rfl⟩
  by_cases hread : e r ≤ e x
  swap
  · exact ⟨j, hqj, he_def ▸ not_le.mp hread⟩
  -- the entry is not `⊥` at `r`, by locality at `j`
  have hτ : ⊥ < e r := by
    refine bot_lt_iff_ne_bot.mpr fun h ↦ ?_
    have hmem : Fin.castAdd _ r ∈ (markedTop I D).toCellScheme.below
        ((markedTop I D).toCellScheme.gradedIndex (Fin.natAdd _ j)) := by
      rw [appendFullCellsScheme_gradedIndex_natAdd]
      exact castAdd_mem_below_sheetLayer (hS := not_univ_four_le) hgr.le
    have hrow0 : (markedTop I D).rows.row (Fin.natAdd _ j) ⟨_, hmem⟩ = ⊥ := by
      rw [sheetLayer_row_natAdd (hS := not_univ_four_le), sheetRow_castAdd, ← he_def]
      exact h
    have := (hq.locality (Fin.natAdd _ j)).eq_bot hrow0
    -- locality reads `min (q r) (q j)` at the old cell `r`
    change min (q (Fin.castAdd _ r)) (q (Fin.natAdd _ j)) = ⊥ at this
    rw [hqr, hqj, min_self] at this
    exact top_ne_bot this
  have he : (scheme I).rows.IsLawful e := he_def ▸ (Scheme.mem_catalogue.mp (hε j)).1
  have hxr : x ≠ r := fun h ↦ by rw [h, hgr] at hgx; omega
  have hr3 : r ∉ (scheme I).toCellScheme.below (univ, 3) := fun h ↦ by
    have := h.2
    change (scheme I).toCellScheme.grade r ≤ 3 at this
    omega
  have hwU : (scheme I).rows.IsLawfulBelow (univ.erase z₁, 4) fun d ↦ Function.update e r ⊤ d :=
    (he.isLawfulBelow _).update_top hrC huniq hrow hrr hτ.ne'
  have hwV : (scheme I).rows.IsLawfulBelow (univ, 3) fun d ↦ Function.update e r ⊤ d :=
    (CellScheme.Rows.isLawfulBelow_congr (w := Function.update e r ⊤) (w' := e) fun d hd ↦
      Function.update_of_ne (fun hdr ↦ hr3 (by rw [← hdr]; exact hd)) _ _).mpr
        (he.isLawfulBelow _)
  subst he_def
  refine exists_top_reads_lt_markedTop_of_raise D hq hgr hgx hqj hqr hread hτ hz₁ hz₂ hz hrC hwU
    hwV (fun d _ ↦ ?_) ?_
  · by_cases hdr : d = r
    · rw [hdr, Function.update_self, min_eq_right le_top, min_self]
    · rw [Function.update_of_ne hdr]
  · rw [Function.update_of_ne hxr, Function.update_self]
    exact lt_top_iff_ne_top.mpr
      (ne_top_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue (hε j) x))

end TowerProfile

end VaughtConjecture
