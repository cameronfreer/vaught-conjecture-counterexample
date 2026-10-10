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

**Scope.**  Not used by the main theorem through the levels
(`VaughtConjecture.MainTheorem.GrowthLevelRoute`); kept as reusable mathematics.

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

/-! ### Writings at the cells of a lower layer -/

/-- **The writing of a state at a cell of a layer agrees with the cell's entry**: at every height
`K ≥ k + 1`, a cell `u` of full scope at the grade `k + 2` is the cell of a state `R` of
`C (k + 2)` (reading `R` on the base as a controller) such that, for every state `R'`, the
writing of `R'` at `u` caps a common value of the writings of `R'` and `R` at every cell of the
base: `min (B.v R' t) w = min (B.v R t) w` with `w` the writing of `R'` at `u` (an agreement
height). -/
theorem exists_layerTower_layerCell (hG0 : ∀ k, ⊥ ∈ G (k + 2)) (k : ℕ) :
    ∀ K, k + 1 ≤ K → ∀ u : Fin (layerTower B C G K).S.card,
      (layerTower B C G K).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k + 2) →
      ∃ R ∈ C (k + 2), (∀ t : Fin B.S.card, B.S.toCellScheme.grade t ≤ k + 2 →
          (layerTower B C G K).S.rowAt u (layerTowerEmb K t) = B.v R t) ∧
        ∀ R' : σ, ∀ t : Fin B.S.card,
          min (B.v R' t) ((layerTower B C G K).v R' u) =
            min (B.v R t) ((layerTower B C G K).v R' u) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro u hu
    set T := layerTower B C G k with hT
    classical
    obtain ⟨i, rfl⟩ := exists_eq_natAdd_of_gradedIndex_catalogueLayer (S := T.S) (k := k + 2)
      (read := fun d ↦ d) (G := G (k + 2)) (C := T.entries (C (k + 2))) (hS := T.not_le) hu
    obtain ⟨R, hR, hRe⟩ := mem_image.mp (layerEntry_mem (C := T.entries (C (k + 2))) i)
    refine ⟨R, hR, fun t ht ↦ ?_, fun R' t ↦ ?_⟩
    · have hgt : T.S.toCellScheme.grade (layerTowerEmb k t) ≤ k + 2 := by
        have := congrArg Prod.snd (gradedIndex_layerTowerEmb (B := B) (C := C) (G := G) t k)
        change T.S.toCellScheme.grade (layerTowerEmb k t) = B.S.toCellScheme.grade t at this
        omega
      change (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
        T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ (layerTowerEmb k t)) = _
      rw [rowAt_catalogueLayer_castAdd i hgt, ← hRe]
      exact layerTower_v_emb R t k
    · change min (B.v R' t) (layerRow T.S (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
        (T.v R') (Fin.natAdd _ i)) = min (B.v R t) (layerRow T.S (fun d ↦ d) (G (k + 2))
        (T.entries (C (k + 2))) (T.v R') (Fin.natAdd _ i))
      rw [layerRow_natAdd, ← hRe, ← layerTower_v_emb R' t k, ← layerTower_v_emb R t k]
      exact (agreementHeight_spec (hG0 k) _ _).2 _
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
    obtain ⟨R, hR, hrow, hagr⟩ := ih u' hu''
    refine ⟨R, hR, fun t ht ↦ ?_, fun R' t ↦ ?_⟩
    · change (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
        T.not_le).rowAt (Fin.castAdd _ u') (Fin.castAdd _ (layerTowerEmb K t)) = _
      rw [rowAt_appendFullCells_castAdd]
      exact hrow t ht
    · change min (B.v R' t) (layerRow T.S (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
        (T.v R') (Fin.castAdd _ u')) = min (B.v R t) (layerRow T.S (fun d ↦ d) (G (K + 2))
        (T.entries (C (K + 2))) (T.v R') (Fin.castAdd _ u'))
      rw [layerRow_castAdd]
      exact hagr R' t

/-- **A controller reads a cell of a layer at a cap of agreement**: at every height `N ≥ K + 1`,
for cells `f` of full scope at the grade `K + 2` and `u` at a grade `k + 2 ≤ K + 2`, there are
states `R_f` and `R_u` read on the base by `f` and by `u` such that the row of `f` at `u` caps a
common value of their writings at every cell of the base. -/
theorem exists_layerTower_controller_agree (hG0 : ∀ k, ⊥ ∈ G (k + 2)) (k K : ℕ) (hkK : k ≤ K) :
    ∀ N, K + 1 ≤ N → ∀ f u : Fin (layerTower B C G N).S.card,
      (layerTower B C G N).S.toCellScheme.gradedIndex f = ((univ : Finset (Fin n)), K + 2) →
      (layerTower B C G N).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k + 2) →
      ∃ Rf ∈ C (K + 2), ∃ Ru ∈ C (k + 2),
        (∀ t : Fin B.S.card, B.S.toCellScheme.grade t ≤ K + 2 →
          (layerTower B C G N).S.rowAt f (layerTowerEmb N t) = B.v Rf t) ∧
        (∀ t : Fin B.S.card, B.S.toCellScheme.grade t ≤ k + 2 →
          (layerTower B C G N).S.rowAt u (layerTowerEmb N t) = B.v Ru t) ∧
        ∀ t : Fin B.S.card, min (B.v Rf t) ((layerTower B C G N).S.rowAt f u) =
          min (B.v Ru t) ((layerTower B C G N).S.rowAt f u) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    intro f u hf hu
    set T := layerTower B C G K with hT
    classical
    obtain ⟨i, rfl⟩ := exists_eq_natAdd_of_gradedIndex_catalogueLayer (S := T.S) (k := K + 2)
      (read := fun d ↦ d) (G := G (K + 2)) (C := T.entries (C (K + 2))) (hS := T.not_le) hf
    obtain ⟨Rf, hRf, hRfe⟩ := mem_image.mp (layerEntry_mem (C := T.entries (C (K + 2))) i)
    have hrowf (t : Fin B.S.card) (ht : B.S.toCellScheme.grade t ≤ K + 2) :
        (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
          T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ (layerTowerEmb K t)) = B.v Rf t := by
      have hgt : T.S.toCellScheme.grade (layerTowerEmb K t) ≤ K + 2 := by
        have := congrArg Prod.snd (gradedIndex_layerTowerEmb (B := B) (C := C) (G := G) t K)
        change T.S.toCellScheme.grade (layerTowerEmb K t) = B.S.toCellScheme.grade t at this
        omega
      rw [rowAt_catalogueLayer_castAdd i hgt, ← hRfe]
      exact layerTower_v_emb Rf t K
    rcases hkK.lt_or_eq with hlt | rfl
    · -- `u` is an old cell
      have hu' : ∃ u', u = Fin.castAdd _ u' := by
        induction u using Fin.addCases with
        | left u' => exact ⟨u', rfl⟩
        | right j =>
          exfalso
          have h := congrArg Prod.snd hu
          change (T.S.appendFullCellsScheme (K + 2) _).grade (Fin.natAdd _ j) = k + 2 at h
          rw [appendFullCellsScheme_grade_natAdd] at h
          omega
      obtain ⟨u', rfl⟩ := hu'
      have hu'' : T.S.toCellScheme.gradedIndex u' = ((univ : Finset (Fin n)), k + 2) := by
        have h := hu
        change (T.S.appendFullCellsScheme (K + 2) _).gradedIndex (Fin.castAdd _ u') = _ at h
        rwa [appendFullCellsScheme_gradedIndex_castAdd] at h
      obtain ⟨Ru, hRu, hrowu, hagr⟩ := exists_layerTower_layerCell (B := B) (C := C) (G := G)
        hG0 k K (by omega) u' hu''
      have hgu : T.S.toCellScheme.grade u' ≤ K + 2 := by
        have := congrArg Prod.snd hu''
        change T.S.toCellScheme.grade u' = k + 2 at this
        omega
      have hfu : (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
          T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ u') = T.v Rf u' := by
        rw [rowAt_catalogueLayer_castAdd i hgu, ← hRfe]
      refine ⟨Rf, hRf, Ru, hRu, hrowf, fun t ht ↦ ?_, fun t ↦ ?_⟩
      · change (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
          T.not_le).rowAt (Fin.castAdd _ u') (Fin.castAdd _ (layerTowerEmb K t)) = _
        rw [rowAt_appendFullCells_castAdd]
        exact hrowu t ht
      · change min (B.v Rf t) ((T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2))
          (T.entries (C (K + 2))) T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ u')) =
          min (B.v Ru t) ((T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2))
          (T.entries (C (K + 2))) T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ u'))
        rw [hfu]
        exact hagr Rf t
    · -- `u` is in the same layer
      obtain ⟨j, rfl⟩ := exists_eq_natAdd_of_gradedIndex_catalogueLayer (S := T.S) (k := k + 2)
        (read := fun d ↦ d) (G := G (k + 2)) (C := T.entries (C (k + 2))) (hS := T.not_le) hu
      obtain ⟨Ru, hRu, hRue⟩ := mem_image.mp (layerEntry_mem (C := T.entries (C (k + 2))) j)
      have hmem : Fin.natAdd T.S.card j ∈ (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2))
          (T.entries (C (k + 2))) T.not_le).toCellScheme.below
            ((T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
              T.not_le).toCellScheme.gradedIndex (Fin.natAdd T.S.card i)) := by
        rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd,
          appendFullCellsScheme_gradedIndex_natAdd]
      have hfu : (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
          T.not_le).rowAt (Fin.natAdd _ i) (Fin.natAdd _ j) =
          agreementHeight (G (k + 2)) (T.v Rf) (T.v Ru) := by
        rw [rowAt_of_mem hmem, appendFullCells_row_natAdd_eq]
        change layerRow T.S (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
          (layerEntry (T.entries (C (k + 2))) i) (Fin.natAdd _ j) = _
        rw [layerRow_natAdd, hRfe, hRue]
      have hrowu (t : Fin B.S.card) (ht : B.S.toCellScheme.grade t ≤ k + 2) :
          (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
            T.not_le).rowAt (Fin.natAdd _ j) (Fin.castAdd _ (layerTowerEmb k t)) =
            B.v Ru t := by
        have hgt : T.S.toCellScheme.grade (layerTowerEmb k t) ≤ k + 2 := by
          have := congrArg Prod.snd (gradedIndex_layerTowerEmb (B := B) (C := C) (G := G) t k)
          change T.S.toCellScheme.grade (layerTowerEmb k t) = B.S.toCellScheme.grade t at this
          omega
        rw [rowAt_catalogueLayer_castAdd j hgt, ← hRue]
        exact layerTower_v_emb Ru t k
      refine ⟨Rf, hRf, Ru, hRu, hrowf, hrowu, fun t ↦ ?_⟩
      change min (B.v Rf t) ((T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2))
        (T.entries (C (k + 2))) T.not_le).rowAt (Fin.natAdd _ i) (Fin.natAdd _ j)) =
        min (B.v Ru t) ((T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2))
        (T.entries (C (k + 2))) T.not_le).rowAt (Fin.natAdd _ i) (Fin.natAdd _ j))
      rw [hfu, ← layerTower_v_emb Rf t k, ← layerTower_v_emb Ru t k]
      exact (agreementHeight_spec (hG0 k) _ _).2 _
  | succ N hN ih =>
    intro f u hf hu
    set T := layerTower B C G N with hT
    have hcast (z : Fin (layerTower B C G (N + 1)).S.card) (k₀ : ℕ) (hk₀ : k₀ ≤ K)
        (hz : (layerTower B C G (N + 1)).S.toCellScheme.gradedIndex z =
          ((univ : Finset (Fin n)), k₀ + 2)) :
        ∃ z', z = Fin.castAdd _ z' ∧
          T.S.toCellScheme.gradedIndex z' = ((univ : Finset (Fin n)), k₀ + 2) := by
      induction z using Fin.addCases with
      | left z' =>
        refine ⟨z', rfl, ?_⟩
        have h := hz
        change (T.S.appendFullCellsScheme (N + 2) _).gradedIndex (Fin.castAdd _ z') = _ at h
        rwa [appendFullCellsScheme_gradedIndex_castAdd] at h
      | right i =>
        exfalso
        have h := congrArg Prod.snd hz
        change (T.S.appendFullCellsScheme (N + 2) _).grade (Fin.natAdd _ i) = k₀ + 2 at h
        rw [appendFullCellsScheme_grade_natAdd] at h
        omega
    obtain ⟨f', rfl, hf'⟩ := hcast f K le_rfl hf
    obtain ⟨u', rfl, hu'⟩ := hcast u k hkK hu
    obtain ⟨Rf, hRf, Ru, hRu, hrowf, hrowu, hagr⟩ := ih f' u' hf' hu'
    have hrow (a b : Fin T.S.card) :
        (layerTower B C G (N + 1)).S.rowAt (Fin.castAdd _ a) (Fin.castAdd _ b) =
          T.S.rowAt a b := by
      change (T.S.catalogueLayer (N + 2) (fun d ↦ d) (G (N + 2)) (T.entries (C (N + 2)))
        T.not_le).rowAt (Fin.castAdd _ a) (Fin.castAdd _ b) = _
      exact rowAt_appendFullCells_castAdd _ _
    refine ⟨Rf, hRf, Ru, hRu, fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ↦ ?_⟩
    · exact (hrow _ _).trans (hrowf t ht)
    · exact (hrow _ _).trans (hrowu t ht)
    · rw [hrow]
      exact hagr t

end VaughtConjecture.Scheme
