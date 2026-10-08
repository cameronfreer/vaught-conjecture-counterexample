/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTower

/-!
# Readers in a layer of the profile tower

Roadmap, Layer 3, 3.1, (R6); the rows of the cells of one layer of the profile tower
(`ProfileTower.Lvl.nextS`) at one another.

The cell of a profile `R` of the catalogue at the grade `g + 1` reads an old cell `d` at `R d`
(the section is literal at the old cells) and the cell of another profile `R'` at the agreement
height of `R` and `R'`.  Compiled in this repository (theorem named):

* **Agreement below a larger value** (`Label.agreementHeight_lt_of_lt`): if `b d < a d`, the
  agreement height of `a` and `b` lies strictly below `a d`.
* **A reader above a cell of its layer** (`ProfileTower.Lvl.Good.rowAt_nextS_natAdd_lt`): if
  `R' d < R d` at an old cell `d` of grade at most `g + 1`, the cell of `R` reads the cell of `R'`
  strictly below `d`.  So, within one layer, the cell of `R'` is not read at least as `d` by every
  cell of its graded index as soon as some profile of the catalogue is larger than `R'` at `d`:
  this is the non-domination of `StageType.CapNonDominating` at the grade of the cap, for a cap
  that is a cell of the layer (`ProfileTower.Lvl.Good.exists_reader_lt`).  The profiles of the
  catalogue are orbit codes, with values in the code grid (never `⊤`), so the condition fails when
  the profile of the cap is largest at `d` among the profiles of the catalogue.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Label

variable {ι : Type*} [Fintype ι] {G : Finset Label.{u}} {a b : ι → Label.{u}}

/-- **Agreement below a larger value**: if `b d < a d`, the agreement height of `a` and `b` lies
strictly below `a d`. -/
theorem agreementHeight_lt_of_lt (hG : ⊥ ∈ G) {d : ι} (h : b d < a d) :
    agreementHeight G a b < a d := by
  by_contra hle
  rw [not_lt] at hle
  have hspec := (agreementHeight_spec hG a b).2 d
  rw [min_eq_left hle] at hspec
  exact not_le.mpr h (hspec.trans_le (min_le_left _ _))

end Label

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {L : Lvl I g}

/-- **A reader above a cell of its layer**: in the next level, if two profiles of the catalogue at
`g + 1` satisfy `R' d < R d` at an old cell `d` of grade at most `g + 1`, the cell of `R` reads the
cell of `R'` strictly below `d`. -/
theorem Lvl.Good.rowAt_nextS_natAdd_lt (hL : L.Good) (i i' : Fin (cat I (g + 1)).card)
    {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ g + 1)
    (h : entry I (g + 1) i' d < entry I (g + 1) i d) :
    L.nextS.rowAt (Fin.natAdd _ i) (Fin.natAdd _ i') <
      L.nextS.rowAt (Fin.natAdd _ i) (Fin.castAdd _ (L.embed d)) := by
  have hi' : Fin.natAdd L.S.card i' ∈ L.nextS.toCellScheme.below
      (L.nextS.toCellScheme.gradedIndex (Fin.natAdd L.S.card i)) := by
    rw [CellScheme.mem_below]
    change (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _ ≤
      (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
      Scheme.appendFullCellsScheme_gradedIndex_natAdd]
  have hd' : Fin.castAdd (cat I (g + 1)).card (L.embed d) ∈ L.nextS.toCellScheme.below
      (L.nextS.toCellScheme.gradedIndex (Fin.natAdd L.S.card i)) := by
    rw [CellScheme.mem_below]
    change (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _ ≤
      (L.S.appendFullCellsScheme (g + 1) (cat I (g + 1)).card).gradedIndex _
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_natAdd, hL.gradedIndex_embed]
    exact ⟨subset_univ _, hd⟩
  rw [Scheme.rowAt_of_mem hi', Scheme.rowAt_of_mem hd', Scheme.appendFullCells_row_natAdd,
    Scheme.appendFullCells_row_natAdd]
  change L.Φ (entry I (g + 1) i) (Fin.natAdd _ i') <
    L.Φ (entry I (g + 1) i) (Fin.castAdd _ (L.embed d))
  rw [Lvl.Φ_natAdd, hL.Φ_old]
  exact agreementHeight_lt_of_lt (bot_mem_grid _ _) h

/-- **A cell of the layer is not dominated at a separable old cell**: if some profile of the
catalogue at `g + 1` is larger than the profile of a cell `i'` of the layer at an old cell `d` of
grade at most `g + 1`, some cell of the layer (of graded index `(univ, g + 1)`) reads the cell `i'`
strictly below `d`. -/
theorem Lvl.Good.exists_reader_lt (hL : L.Good) (i' : Fin (cat I (g + 1)).card)
    {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ g + 1)
    (hsep : ∃ R ∈ cat I (g + 1), entry I (g + 1) i' d < R d) :
    ∃ u : Fin L.nextS.card,
      L.nextS.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1) ∧
      L.nextS.rowAt u (Fin.natAdd _ i') < L.nextS.rowAt u (Fin.castAdd _ (L.embed d)) := by
  obtain ⟨R, hR, hlt⟩ := hsep
  obtain ⟨i, rfl⟩ := exists_entry_eq hR
  exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i,
    hL.rowAt_nextS_natAdd_lt i i' hd hlt⟩

end ProfileTower

end VaughtConjecture
