/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelBountiful

/-!
# The twin of a controller one grade below, in the re-rendered levels

Roadmap, Layer 3 ((R3) and (R4), testing the mixed lifts of the replicated scheme on the levels).

The lifts into the mixed faces of the replicated scheme over the height-set tower dominate the
readings of the cells of the attachment by a controller through its **twin**: a cell of full scope
at every lower grade read by the controller at the top of the height set
(`Scheme.LadderBaseData.exists_controller_twin_ladderTower`, used by `Seed.min_decode_eq_decode`).
In the re-rendered levels the catalogues are not nested, so the twin is the cell of the orbit code
of the controller's state one grade below, and the controller reads it through the upper decoder.

* **The upper decoder at the top grid point** (`Label.le_upperDecoderAt_gridPoint`): when every
  code block lies below `B` (`2 · #cells < B`), the upper decoder of `w` at `ω * B + k` is at least
  every value of `w`: every cell with a value other than `⊥` reads it as the visibility replacement
  of its value.
* **The twin one grade below** (`Seed.lvLevel_twin`): with `2 · #cells < B`, a cell of full scope
  at the grade `k + 3`, born in the level at that grade, reads the cell of the orbit code at
  `k + 2` of its state (its twin, at `(univ, k + 2)`) at least as high as every cell of the
  attachment.  So the domination step of the twin holds at the next lower grade.

Not proved here: the twins at the grades further below (the controller reads them through two or
more decoders), and the remaining steps of `Seed.min_decode_eq_decode` and
`Seed.cappedLift_mixed_face` for the levels.

## References

The controllers of the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Label

open Classical in
/-- **The upper decoder at the top grid point dominates the labelling** when every code block lies
below `B`. -/
theorem le_upperDecoderAt_gridPoint {ι : Type*} [Fintype ι] {k K B' : ℕ}
    (hB : 2 * Fintype.card ι < B') (w : ι → Label.{u}) (d : ι) :
    w d ≤ upperDecoderAt k K B' w (gridPoint k B') := by
  by_cases hd : w d = ⊥
  · rw [hd]; exact bot_le
  have hcode : visibilityReplace k k (orbitCode k w d) = gridPoint k (codeBlock k w (w d)) := by
    rw [orbitCode_apply, visibilityReplace_orbitMap hd]
  have hblk : codeBlock k w (w d) < B' :=
    (codeBlock_le k w (w d)).trans_lt (by have := keyRank_le_card k w (w d); omega)
  have hmem : d ∈ ({e | gridPoint k 0 ≤ visibilityReplace k k (orbitCode k w e)} : Finset ι) := by
    rw [Finset.mem_filter, hcode]
    exact ⟨Finset.mem_univ _, gridPoint_le_gridPoint.mpr (Nat.zero_le _)⟩
  have hlt : gridPoint.{u} k (codeBlock k w (w d)) < gridPoint k B' :=
    gridPoint_lt_gridPoint_iff_lex.mpr (.inl hblk)
  have hread : cellReading k w d (gridPoint k B') = visibilityReplace k k (w d) := by
    unfold cellReading
    rw [isSelfVisible_gridPoint k B', hcode, ite_eq_right (not_lt.mpr hlt.le),
      ite_eq_right fun h ↦ hlt.ne h.1.symm]
  calc w d ≤ visibilityReplace k k (w d) := le_visibilityReplace (by omega) _
    _ = cellReading k w d (gridPoint k B') := hread.symm
    _ ≤ orbitDecoder k w (gridPoint k 0) (gridPoint k B') :=
      le_max_of_le_right (Finset.le_sup (f := fun e ↦ cellReading k w e (gridPoint k B')) hmem)
    _ ≤ upperDecoderAt k K B' w (gridPoint k B') := le_max_left _ _

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **The twin one grade below**: with `2 · #cells < B`, a cell of full scope at the grade `k + 3`
born in the level at that grade (the cell of the state `R`) reads the cell of the orbit code of
`R` at `k + 2` (its twin, of graded index `(univ, k + 2)`) at least as high as every cell of the
attachment. -/
theorem lvLevel_twin (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card < B) (k : ℕ)
    (hkm : k + 3 ≤ m + 1) (i : Fin (I.lvCat g B hd Q (k + 3)).card) :
    ∃ e : Fin ((I.lvLevel g H B hd Q (k + 1)).nS B (I.lvCat g B hd Q (k + 3))).card,
      ((I.lvLevel g H B hd Q (k + 1)).nS B (I.lvCat g B hd Q (k + 3))).toCellScheme.gradedIndex e =
        ((univ : Finset (Fin (m + 2))), k + 2) ∧
      ∀ c : Fin (I.attachment g).card,
        ((I.lvLevel g H B hd Q (k + 1)).nS B (I.lvCat g B hd Q (k + 3))).rowAt (Fin.natAdd _ i)
            (Fin.castAdd _ ((I.lvLevel g H B hd Q (k + 1)).attEmb c)) ≤
          ((I.lvLevel g H B hd Q (k + 1)).nS B (I.lvCat g B hd Q (k + 3))).rowAt
            (Fin.natAdd _ i) e := by
  classical
  have hgood := lvLevel_good (B := B) (hd := hd) hH hcard hQ (by omega) (k + 1) (by omega)
  rw [lvLevel_succ] at hgood ⊢
  obtain ⟨-, hRl, hRv, -, hRA⟩ := mem_lvCat.mp ((I.lvCat g B hd Q (k + 3)).equivFin.symm i).2
  have hcB : 2 * Fintype.card (Fin (I.attachment g).card) ≤ B := by
    simp only [Fintype.card_fin]; omega
  have hR2 := hRl.mono (X := ((univ : Finset (Fin (m + 2))), k + 2)) ⟨subset_rfl, by omega⟩
  have hR1 := hRl.mono (X := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_rfl, by omega⟩
  have hP : orbitCode (k + 2) ((I.lvCat g B hd Q (k + 3)).equivFin.symm i).1 ∈
      I.lvCat g B hd Q (k + 2) := mem_lvCat.mpr ⟨fun e ↦ orbitMap_mem_codeGrid hcB _,
    hR2.orbitCode fun e ↦ e.2.2, fun e ↦ isSelfVisible_one_orbitCode (by omega) (hRv e),
    orbitCode_orbitCode, attachAdmits_orbitCode hQ (attachAdmits_pred hRA)⟩
  -- the row of the new cell at an old cell below it
  have hbelow (z : Fin ((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).S.card)
      (hz : (Fin.castAdd _ z : Fin (_ + (I.lvCat g B hd Q (k + 3)).card)) ∈
        (((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
          (I.lvCat g B hd Q (k + 3))).toCellScheme.below
          ((((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
            (I.lvCat g B hd Q (k + 3))).toCellScheme.gradedIndex (Fin.natAdd _ i))) :
      (((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
          (I.lvCat g B hd Q (k + 3))).rowAt (Fin.natAdd _ i) (Fin.castAdd _ z) =
        ((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).σ
          ((I.lvCat g B hd Q (k + 3)).equivFin.symm i).1 z := by
    rw [Scheme.rowAt_of_mem hz, Scheme.appendFullCells_row_natAdd]
    exact ALvl.Φ_castAdd _ _ _
  -- the twin: the cell of the orbit code at `k + 2` of the state, born one level below
  obtain ⟨z, hz, hσz⟩ :
      ∃ z : Fin ((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).S.card,
      ((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).S.toCellScheme.gradedIndex z =
        ((univ : Finset (Fin (m + 2))), k + 2) ∧
      ((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).σ
          ((I.lvCat g B hd Q (k + 3)).equivFin.symm i).1 z =
        upperDecoderAt (k + 2) (k + 3) B ((I.lvCat g B hd Q (k + 3)).equivFin.symm i).1
          (gridPoint (k + 2) B) := by
    refine ⟨Fin.natAdd _ ((I.lvCat g B hd Q (k + 2)).equivFin ⟨_, hP⟩),
      Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _, ?_⟩
    change upperDecoderAt (k + 2) (k + 3) B _
      ((I.lvLevel g H B hd Q k).Φ B (I.lvCat g B hd Q (k + 2)) (orbitCode (k + 2) _)
        (Fin.natAdd _ ((I.lvCat g B hd Q (k + 2)).equivFin ⟨_, hP⟩))) = _
    rw [ALvl.Φ_natAdd, Equiv.symm_apply_apply]
    exact congrArg _
      (agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx) _)
  have he1 : (((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
      (I.lvCat g B hd Q (k + 3))).toCellScheme.gradedIndex (Fin.castAdd _ z) =
      ((univ : Finset (Fin (m + 2))), k + 2) :=
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ z).trans hz
  have he2 : (((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
      (I.lvCat g B hd Q (k + 3))).toCellScheme.gradedIndex (Fin.natAdd _ i) =
      ((univ : Finset (Fin (m + 2))), k + 3) :=
    Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i
  have hemem : (Fin.castAdd _ z : Fin (_ + (I.lvCat g B hd Q (k + 3)).card)) ∈
      (((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
        (I.lvCat g B hd Q (k + 3))).toCellScheme.below
        ((((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
          (I.lvCat g B hd Q (k + 3))).toCellScheme.gradedIndex (Fin.natAdd _ i)) :=
    (le_of_eq he1).trans ((show ((univ : Finset (Fin (m + 2))), k + 2) ≤
      ((univ : Finset (Fin (m + 2))), k + 3) from ⟨subset_rfl, by omega⟩).trans (le_of_eq he2.symm))
  refine ⟨Fin.castAdd _ z, he1, fun c ↦ ?_⟩
  rw [hbelow _ hemem, hσz]
  by_cases hc : (Fin.castAdd _ (((I.lvLevel g H B hd Q k).next B
      (I.lvCat g B hd Q (k + 2))).attEmb c) : Fin (_ + (I.lvCat g B hd Q (k + 3)).card)) ∈
      (((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
        (I.lvCat g B hd Q (k + 3))).toCellScheme.below
        ((((I.lvLevel g H B hd Q k).next B (I.lvCat g B hd Q (k + 2))).nS B
          (I.lvCat g B hd Q (k + 3))).toCellScheme.gradedIndex (Fin.natAdd _ i))
  · rw [hbelow _ hc, hgood.literal _ hR1 c]
    exact le_upperDecoderAt_gridPoint (by simpa using hB) _ c
  · rw [Scheme.rowAt_of_notMem hc]
    exact bot_le

end Seed

end VaughtConjecture
