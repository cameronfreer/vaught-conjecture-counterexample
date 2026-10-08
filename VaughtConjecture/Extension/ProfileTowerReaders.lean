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
open scoped Ordinal

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

/-- **Agreement below a value where two labellings disagree capped**: if `a` and `b` do not agree
capped at `a e`, their agreement height lies strictly below `a e`. -/
theorem agreementHeight_lt_of_not_agree (hG : ⊥ ∈ G) {e : ι}
    (h : ¬ ∀ d, min (a d) (a e) = min (b d) (a e)) : agreementHeight G a b < a e := by
  by_contra hle
  rw [not_lt] at hle
  refine h fun d ↦ ?_
  have hspec := (agreementHeight_spec hG a b).2 d
  calc min (a d) (a e) = min (min (a d) (agreementHeight G a b)) (a e) := by
        rw [min_assoc, min_eq_right hle]
    _ = min (min (b d) (agreementHeight G a b)) (a e) := by rw [hspec]
    _ = min (b d) (a e) := by rw [min_assoc, min_eq_right hle]

/-- **`x` lies in a block strictly below `y`**: `x < y`, and if `x` is an ordinal `μ + i` (`μ` zero
or a limit) then the whole block `[μ, μ + ω)` lies below `y`.  The zero sets of witnesses are unions
of whole blocks, so a transformation may send `x` to `⊥` and keep `y` only in this case. -/
def LowerBlock (x y : Label.{u}) : Prop :=
  x < y ∧ ∀ (μ : Ordinal.{u}) (i j : ℕ), Order.IsSuccPrelimit μ →
    x = ((μ + i : Ordinal.{u}) : Label.{u}) → ((μ + j : Ordinal.{u}) : Label.{u}) < y

/-- **Below a multiple of `ω`**: a label below `ω * β`, itself at most `y`, lies in a block strictly
below `y`. -/
theorem lowerBlock_of_lt_omega0_mul {x y : Label.{u}} {β : Ordinal.{u}}
    (hx : x < ((ω * β : Ordinal.{u}) : Label.{u})) (hy : ((ω * β : Ordinal.{u}) : Label.{u}) ≤ y) :
    LowerBlock x y := by
  refine ⟨hx.trans_le hy, fun μ i j hμ hxe ↦ ?_⟩
  obtain ⟨c, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ
  rw [hxe] at hx
  have hlt : ω * c + i < ω * β := by exact_mod_cast hx
  have hcβ : c < β :=
    (mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mp ((le_self_add).trans_lt hlt)
  have hle : ω * Order.succ c ≤ ω * β := by
    gcongr
    exact Order.succ_le_of_lt hcβ
  rw [Ordinal.mul_succ] at hle
  have hj : ω * c + j < ω * β :=
    (add_lt_add_right (Ordinal.natCast_lt_omega0 j) _).trans_le hle
  exact (show ((ω * c + j : Ordinal.{u}) : Label.{u}) < ((ω * β : Ordinal.{u}) : Label.{u}) by
    exact_mod_cast hj).trans_le hy

/-- **Agreement below a value separating two labellings**: if `b d < z ≤ a d`, the agreement height
of `a` and `b` lies strictly below `z`. -/
theorem agreementHeight_lt_of_lt_le (hG : ⊥ ∈ G) {d : ι} {z : Label.{u}} (hb : b d < z)
    (ha : z ≤ a d) : agreementHeight G a b < z := by
  by_contra hle
  rw [not_lt] at hle
  have hspec := (agreementHeight_spec hG a b).2 d
  have h1 : z ≤ min (a d) (agreementHeight G a b) := le_min ha hle
  rw [hspec] at h1
  exact not_le.mpr hb (h1.trans (min_le_left _ _))

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

/-- **A reader above a cell of its layer, at a separating profile**: if the profile of a cell `i`
of the layer does not agree with that of a cell `i'` capped at its own value at an old cell `d` of
grade at most `g + 1`, the cell `i` reads the cell `i'` strictly below `d`. -/
theorem Lvl.Good.rowAt_nextS_natAdd_lt_of_not_agree (hL : L.Good)
    (i i' : Fin (cat I (g + 1)).card) {d : Fin I.amalgam.card}
    (hd : I.amalgam.toCellScheme.grade d ≤ g + 1)
    (h : ¬ ∀ e, min (entry I (g + 1) i e) (entry I (g + 1) i d) =
      min (entry I (g + 1) i' e) (entry I (g + 1) i d)) :
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
  exact agreementHeight_lt_of_not_agree (bot_mem_grid _ _) h

/-- **A reader separating the blocks**: if the profile of a cell `i` of the layer is at least
`ω * β` at an old cell `d` of grade at most `g + 1`, where the profile of a cell `i'` is below
`ω * β`, the cell `i` reads the cell `i'` in a block strictly below its reading of `d`. -/
theorem Lvl.Good.lowerBlock_rowAt_nextS (hL : L.Good) (i i' : Fin (cat I (g + 1)).card)
    {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) {β : Ordinal.{u}}
    (hlow : entry I (g + 1) i' d < ((ω * β : Ordinal.{u}) : Label.{u}))
    (hhigh : ((ω * β : Ordinal.{u}) : Label.{u}) ≤ entry I (g + 1) i d) :
    LowerBlock (L.nextS.rowAt (Fin.natAdd _ i) (Fin.natAdd _ i'))
      (L.nextS.rowAt (Fin.natAdd _ i) (Fin.castAdd _ (L.embed d))) := by
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
  change LowerBlock (L.Φ (entry I (g + 1) i) (Fin.natAdd _ i'))
    (L.Φ (entry I (g + 1) i) (Fin.castAdd _ (L.embed d)))
  rw [Lvl.Φ_natAdd, hL.Φ_old]
  exact lowerBlock_of_lt_omega0_mul (agreementHeight_lt_of_lt_le (bot_mem_grid _ _) hlow hhigh)
    hhigh

end ProfileTower

end VaughtConjecture
