/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.BaseLadderTower
import VaughtConjecture.Extension.LayerTowerTwins

/-!
# The twins of a controller in the ladder tower

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

In the ladder tower over a base (`Scheme.LadderBaseData.ladderTower`) with decreasing predicates,
the catalogues decrease, so every cell of full scope at a grade `k + 2` is the cell of a state `R`
whose row reads `R` on the cells of the base, its positive table on the ladder
(`Scheme.LadderBaseData.exists_controller_ladderTower`), and, at every lower grade `k' + 2`, a cell
of full scope at the top `gridPoint (k' + 2) B'` of the grid (its twin,
`Scheme.LadderBaseData.exists_controller_twin_ladderTower`).

## References

Agreement heights and field rows are those of the coatom extension construction [Kni26, §4.4].
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

/-- The top of the grid at the grade `k` is its grid point of block `B`. -/
theorem sup_grid (k B : ℕ) : (grid k B).sup id = (gridPoint k B : Label.{u}) :=
  le_antisymm (Finset.sup_le fun _ hx ↦ le_gridPoint_of_mem_grid hx)
    (Finset.le_sup (f := id) (gridPoint_mem_grid le_rfl))

namespace LadderBaseData

variable {n : ℕ} {B : LadderBaseData.{u} n} {H : ℕ} {Γ : Finset Label.{u}}
  {A : ℕ → (Fin B.S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The catalogues of the ladder tower decrease along the grades. -/
theorem towerCat_mono (hA : ∀ k R, A (k + 3) R → A (k + 2) R) {k' k : ℕ} (hk : k' ≤ k) :
    B.towerCat Γ A (k + 2) ⊆ B.towerCat Γ A (k' + 2) := by
  induction k, hk using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih => exact (towerCat_succ_subset hA k).trans ih

/-- **A controller of the ladder tower and its twins**: at every height `K ≥ k + 1`, a cell of full
scope at the grade `k + 2` is the cell of a lawful state `R` of the catalogue at `k + 2`, whose row
reads `R` at the cells of the base of grade at most `k + 2`, the positive table of `R` at the base
indices of its rank member on the ladder, and, at every grade `k' + 2 ≤ k + 2`, some cell of full
scope at the top of the grid. -/
theorem exists_controller_twin_ladderTower (hcard : B.S.card ≤ H)
    (hA : ∀ k R, A (k + 3) R → A (k + 2) R) (k K : ℕ) (hK : k + 1 ≤ K)
    (u : Fin (B.ladderTower H Γ A B' K).S.card)
    (hu : (B.ladderTower H Γ A B' K).S.toCellScheme.gradedIndex u =
      ((univ : Finset (Fin n)), k + 2)) :
    ∃ R ∈ B.towerCat Γ A (k + 2), ∃ hR : B.S.rows.IsLawful R,
      (∀ d : Fin B.S.card, B.S.toCellScheme.grade d ≤ k + 2 →
        (B.ladderTower H Γ A B' K).S.rowAt u (B.towerEmb K (Fin.castAdd _ d)) = R d) ∧
      (∀ p, (B.ladderTower H Γ A B' K).S.rowAt u
          (B.towerEmb K (Fin.natAdd _ (ladderEquiv _ _ H p))) =
        posTable R (baseIndex H (rankProf B.S H)
          (RankMember.ofLawful B.wf hcard hR)
          (Fin.natAdd _ (ladderEquiv _ _ H p)))) ∧
      ∀ k' ≤ k, ∃ e : Fin (B.ladderTower H Γ A B' K).S.card,
        (B.ladderTower H Γ A B' K).S.toCellScheme.gradedIndex e =
          ((univ : Finset (Fin n)), k' + 2) ∧
        (B.ladderTower H Γ A B' K).S.rowAt u e = gridPoint (k' + 2) B' := by
  obtain ⟨R, hRC, hrow, htwin⟩ := exists_layerTower_controller_twin (B := B.towerBase H)
    (C := B.towerCat Γ A) (G := fun k ↦ grid k B') k K hK u hu
  have hRl := (mem_towerCat.mp hRC).2.1
  refine ⟨R, hRC, hRl, fun d hd ↦ ?_, fun p ↦ ?_, fun k' hk' ↦ ?_⟩
  · have h := hrow (Fin.castAdd _ d) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.castAdd _ d) ≤ k + 2
      rw [appendFullCellsScheme_grade_castAdd]; exact hd)
    exact h.trans (stateExt_castAdd hRl hcard d)
  · have h := hrow (Fin.natAdd _ (ladderEquiv _ _ H p)) (by
      change (B.S.appendFullCellsScheme 1 _).grade (Fin.natAdd _ _) ≤ k + 2
      rw [appendFullCellsScheme_grade_natAdd]; omega)
    exact h.trans
      (stateExt_of_grade_one hRl hcard _ (appendFullCellsScheme_grade_natAdd _ _ _ _))
  · obtain ⟨e, he, hv⟩ := htwin k' hk' (towerCat_mono hA hk' hRC)
    exact ⟨e, he, hv.trans (sup_grid (k' + 2) B')⟩

end LadderBaseData

end VaughtConjecture.Scheme
