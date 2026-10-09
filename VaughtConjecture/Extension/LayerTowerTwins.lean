/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LayerTower

/-!
# The twins of a controller in a tower of catalogue layers

Roadmap, Layer 3 ((R3) and (R4), the mixed-coatom lift of the replicated carrier).

In a tower of catalogue layers with decreasing catalogues, a state of the catalogue at the grade
`k + 2` is also an entry of every lower layer: it has a **twin** there, the cell of its own writing
(`Scheme.exists_layerTower_twin`: the writing of the state is the top of the grid at its twin, the
agreement height of the writing with itself).

**A controller reads its twins at the top** (`Scheme.exists_layerTower_controller_twin`): at every
height `K ≥ k + 1`, a cell of full scope at the grade `k + 2` is the cell of a state `R` of the
catalogue at `k + 2`, whose row reads `R` at the cells of the base of grade at most `k + 2` (as in
`Scheme.exists_layerTower_controller`) and reads, at every lower grade `k' + 2` at which `R` is in
the catalogue, some cell of full scope (the twin) at the top of the grid at `k' + 2`.

## References

Agreement heights and catalogue layers are those of the coatom extension construction
[Kni26, §4.4].
-/

universe u v

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {σ : Type v} {B : LayerTower.{u} n σ 0} {C : ℕ → Finset σ}
  {G : ℕ → Finset Label.{u}}

/-- The agreement height of a labelling with itself is the top of the grid. -/
theorem agreementHeight_self {ι : Type*} [Fintype ι] (G' : Finset Label.{u}) (a : ι → Label.{u}) :
    agreementHeight G' a a = G'.sup id := by
  unfold agreementHeight
  rw [filter_true_of_mem fun _ _ _ ↦ rfl]

/-- **The twin of a state**: for a state `R` of the catalogue at the grade `k' + 2`, at every height
`K ≥ k' + 1` some cell of full scope at the grade `k' + 2` carries, in the writing of `R`, the top
of the grid. -/
theorem exists_layerTower_twin (k' : ℕ) {R : σ} (hR : R ∈ C (k' + 2)) :
    ∀ K, k' + 1 ≤ K → ∃ e : Fin (layerTower B C G K).S.card,
      (layerTower B C G K).S.toCellScheme.gradedIndex e = ((univ : Finset (Fin n)), k' + 2) ∧
        (layerTower B C G K).v R e = (G (k' + 2)).sup id := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    classical
    set T := layerTower B C G k' with hT
    obtain ⟨i, hi⟩ := exists_layerEntry_eq (C := T.entries (C (k' + 2))) (mem_image_of_mem T.v hR)
    refine ⟨Fin.natAdd _ i, ?_, ?_⟩
    · change (T.S.appendFullCellsScheme (k' + 2) _).gradedIndex (Fin.natAdd _ i) = _
      exact appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
    · change layerRow T.S (fun d ↦ d) (G (k' + 2)) (T.entries (C (k' + 2))) (T.v R)
        (Fin.natAdd _ i) = _
      rw [layerRow_natAdd, hi, agreementHeight_self]
  | succ K hK ih =>
    obtain ⟨e, he, hv⟩ := ih
    refine ⟨Fin.castAdd _ e, ?_, ?_⟩
    · change ((layerTower B C G K).S.appendFullCellsScheme (K + 2) _).gradedIndex
        (Fin.castAdd _ e) = _
      rw [appendFullCellsScheme_gradedIndex_castAdd]
      exact he
    · change layerRow (layerTower B C G K).S (fun d ↦ d) (G (K + 2))
        ((layerTower B C G K).entries (C (K + 2))) ((layerTower B C G K).v R)
        (Fin.castAdd _ e) = _
      rw [layerRow_castAdd]
      exact hv

/-- **A controller reads its twins at the top.**  At every height `K ≥ k + 1`, a cell `u` of full
scope at the grade `k + 2` is the cell of a state `R` of `C (k + 2)` whose row reads the writing of
`R` in the base at every cell of the base of grade at most `k + 2`, and, at every grade `k' + 2`
with `k' ≤ k` and `R ∈ C (k' + 2)`, some cell of full scope at that grade at the top of the grid. -/
theorem exists_layerTower_controller_twin (k : ℕ) :
    ∀ K, k + 1 ≤ K → ∀ u : Fin (layerTower B C G K).S.card,
      (layerTower B C G K).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k + 2) →
      ∃ R ∈ C (k + 2), (∀ t : Fin B.S.card, B.S.toCellScheme.grade t ≤ k + 2 →
          (layerTower B C G K).S.rowAt u (layerTowerEmb K t) = B.v R t) ∧
        ∀ k' ≤ k, R ∈ C (k' + 2) → ∃ e : Fin (layerTower B C G K).S.card,
          (layerTower B C G K).S.toCellScheme.gradedIndex e = ((univ : Finset (Fin n)), k' + 2) ∧
            (layerTower B C G K).S.rowAt u e = (G (k' + 2)).sup id := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro u hu
    set T := layerTower B C G k with hT
    classical
    obtain ⟨i, rfl⟩ := exists_eq_natAdd_of_gradedIndex_catalogueLayer (S := T.S) (k := k + 2)
      (read := fun d ↦ d) (G := G (k + 2)) (C := T.entries (C (k + 2))) (hS := T.not_le) hu
    obtain ⟨R, hR, hRe⟩ := mem_image.mp (layerEntry_mem (C := T.entries (C (k + 2))) i)
    refine ⟨R, hR, fun t ht ↦ ?_, fun k' hk' hRk' ↦ ?_⟩
    · have hgt : T.S.toCellScheme.grade (layerTowerEmb k t) ≤ k + 2 := by
        have := congrArg Prod.snd (gradedIndex_layerTowerEmb (B := B) (C := C) (G := G) t k)
        change T.S.toCellScheme.grade (layerTowerEmb k t) = B.S.toCellScheme.grade t at this
        omega
      change (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
        T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ (layerTowerEmb k t)) = _
      rw [rowAt_catalogueLayer_castAdd i hgt, ← hRe]
      exact layerTower_v_emb R t k
    · rcases hk'.lt_or_eq with hlt | rfl
      · -- a twin in a lower layer
        obtain ⟨e, he, hv⟩ := exists_layerTower_twin (B := B) (C := C) (G := G) k' hRk' k
          (by omega)
        have hge : T.S.toCellScheme.grade e ≤ k + 2 := by
          have := congrArg Prod.snd he
          change T.S.toCellScheme.grade e = k' + 2 at this
          omega
        refine ⟨Fin.castAdd _ e, ?_, ?_⟩
        · change (T.S.appendFullCellsScheme (k + 2) _).gradedIndex (Fin.castAdd _ e) = _
          rw [appendFullCellsScheme_gradedIndex_castAdd]
          exact he
        · change (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
            T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ e) = _
          rw [rowAt_catalogueLayer_castAdd i hge, ← hRe]
          exact hv
      · -- the cell itself
        refine ⟨Fin.natAdd _ i, appendFullCellsScheme_gradedIndex_natAdd _ _ _ _, ?_⟩
        have hmem : Fin.natAdd T.S.card i ∈ (T.S.catalogueLayer (k' + 2) (fun d ↦ d) (G (k' + 2))
            (T.entries (C (k' + 2))) T.not_le).toCellScheme.below
              ((T.S.catalogueLayer (k' + 2) (fun d ↦ d) (G (k' + 2)) (T.entries (C (k' + 2)))
                T.not_le).toCellScheme.gradedIndex (Fin.natAdd T.S.card i)) :=
          CellScheme.mem_below_gradedIndex _ _
        change (T.S.catalogueLayer (k' + 2) (fun d ↦ d) (G (k' + 2)) (T.entries (C (k' + 2)))
          T.not_le).rowAt (Fin.natAdd _ i) (Fin.natAdd _ i) = _
        rw [rowAt_of_mem hmem, appendFullCells_row_natAdd_eq]
        change layerRow T.S (fun d ↦ d) (G (k' + 2)) (T.entries (C (k' + 2)))
          (layerEntry (T.entries (C (k' + 2))) i) (Fin.natAdd _ i) = _
        rw [layerRow_natAdd, agreementHeight_self]
  | succ K hK ih =>
    intro u hu
    set T := layerTower B C G K with hT
    have hu' : ∃ u', u = Fin.castAdd _ u' := by
      induction u using Fin.addCases with
      | left u' => exact ⟨u', rfl⟩
      | right i =>
        exfalso
        have h := congrArg Prod.snd hu
        change (T.S.appendFullCellsScheme (K + 2) _).grade (Fin.natAdd _ i) = k + 2 at h
        rw [appendFullCellsScheme_grade_natAdd] at h
        omega
    obtain ⟨u', rfl⟩ := hu'
    have hu'' : T.S.toCellScheme.gradedIndex u' = ((univ : Finset (Fin n)), k + 2) := by
      have h := hu
      change (T.S.appendFullCellsScheme (K + 2) _).gradedIndex (Fin.castAdd _ u') = _ at h
      rwa [appendFullCellsScheme_gradedIndex_castAdd] at h
    obtain ⟨R, hR, hrow, htwin⟩ := ih u' hu''
    refine ⟨R, hR, fun t ht ↦ ?_, fun k' hk' hRk' ↦ ?_⟩
    · change (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
        T.not_le).rowAt (Fin.castAdd _ u') (Fin.castAdd _ (layerTowerEmb K t)) = _
      rw [rowAt_appendFullCells_castAdd]
      exact hrow t ht
    · obtain ⟨e, he, hv⟩ := htwin k' hk' hRk'
      refine ⟨Fin.castAdd _ e, ?_, ?_⟩
      · change (T.S.appendFullCellsScheme (K + 2) _).gradedIndex (Fin.castAdd _ e) = _
        rw [appendFullCellsScheme_gradedIndex_castAdd]
        exact he
      · change (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
          T.not_le).rowAt (Fin.castAdd _ u') (Fin.castAdd _ e) = _
        rw [rowAt_appendFullCells_castAdd]
        exact hv

end VaughtConjecture.Scheme
