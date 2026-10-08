/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CatalogueLayer

/-!
# A tower of catalogue layers carrying written states

Roadmap, Layer 3 ((R3) and (R4), the one-scope full layers of the recognizing growth carrier).

A **layer tower** at height `k` (`Scheme.LayerTower`) is a scheme with every cell of grade at most
`k + 1` or of scope other than the ground set, together with a **writing** `v` of states (elements
of an arbitrary type) as labellings of its cells.  Its **next layer**
(`Scheme.LayerTower.next`) appends at the grade `k + 2` the catalogue layer
(`Scheme.catalogueLayer`) whose entries are the writings of a finite set `C` of states, read on all
the old cells, with agreement heights in a finite set `G` of labels; the writing of a state in the
next layer is the layer row of its old writing.  **The tower** (`Scheme.layerTower`) iterates this
from a base at height `0`, with catalogues `C (k + 2)` and label sets `G (k + 2)` at the grade
`k + 2`.

* **Laws** (`Scheme.isWellFormed_layerTower`, `Scheme.layerTower_lawful`,
  `Scheme.isCoded_layerTower`): well formed up to the number of points; consistent, with the
  writing of every state of the catalogue at the next grade lawful and bounded, when the catalogues
  decrease, the label sets contain `⊥`, are self-visible at their grade, have increasing tops
  bounding them, and the base writes the states of the first catalogue lawfully below the first
  top; coded when everything lies below `ω ^ 2`.
* **Completeness** (`Scheme.exists_gradedIndex_layerTower`): with nonempty catalogues, every graded
  face of the base kind, or of full scope and grade between `2` and `k + 1`, is the graded index of
  a cell.
* **The old cells** (`Scheme.layerTower_embed`, `Scheme.layerTower_v_embed`,
  `Scheme.rowAt_layerTower_embed`): the cells of the base embed in every height, keeping their
  writings and their rows.
* **The controllers** (`Scheme.exists_layerTower_controller`): every cell of full scope at the grade
  `k + 2` of the tower at height `k + 1` is the cell of a state `R` of `C (k + 2)` whose row reads,
  at every old cell of grade at most `k + 2`, the writing of `R`.

## References

Agreement heights and field rows are those of the coatom extension construction [Kni26, §4.4].
-/

universe u v

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {σ : Type v}

/-- A **layer tower** at height `k`: a scheme with every cell of grade at most `k + 1` or of scope
other than the ground set, and a writing of states as labellings of its cells. -/
structure LayerTower (n : ℕ) (σ : Type v) (k : ℕ) where
  /-- The scheme. -/
  S : Scheme.{u} n
  /-- The writing of the states. -/
  v : σ → Fin S.card → Label.{u}
  /-- Every cell has grade at most `k + 1` or scope other than the ground set. -/
  inv : ∀ d, S.toCellScheme.grade d ≤ k + 1 ∨ S.toCellScheme.scope d ≠ univ

namespace LayerTower

variable {k : ℕ} (T : LayerTower.{u} n σ k)

/-- No cell of a layer tower at height `k` lies above `(univ, k + 2)`. -/
theorem not_le (d : Fin T.S.card) :
    ¬ ((univ : Finset (Fin n)), k + 2) ≤ T.S.toCellScheme.gradedIndex d := fun h ↦ by
  rcases T.inv d with hd | hd
  · have := h.2; change k + 2 ≤ T.S.toCellScheme.grade d at this; omega
  · exact hd (univ_subset_iff.mp h.1)

open Classical in
/-- The **entries** of the next layer: the writings of the states of `C`. -/
noncomputable def entries (C : Finset σ) : Finset (Fin T.S.card → Label.{u}) := C.image T.v

/-- **The next layer**: the catalogue layer at the grade `k + 2` of the writings of the states of
`C`, with agreement heights in `G`; a state is written by the layer row of its writing. -/
noncomputable def next (C : Finset σ) (G : Finset Label.{u}) : LayerTower.{u} n σ (k + 1) where
  S := T.S.catalogueLayer (k + 2) (fun d ↦ d) G (T.entries C) T.not_le
  v R := layerRow T.S (fun d ↦ d) G (T.entries C) (T.v R)
  inv d := by
    induction d using Fin.addCases with
    | left d =>
      rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_scope_castAdd]
      exact (T.inv d).imp_left fun h ↦ h.trans (Nat.le_succ _)
    | right i => exact .inl (appendFullCellsScheme_grade_natAdd _ _ _ i).le

end LayerTower

/-- **The tower** of catalogue layers over a base, with catalogues `C (k + 2)` and label sets
`G (k + 2)` at the grade `k + 2`. -/
noncomputable def layerTower (B : LayerTower.{u} n σ 0) (C : ℕ → Finset σ)
    (G : ℕ → Finset Label.{u}) : (k : ℕ) → LayerTower.{u} n σ k
  | 0 => B
  | k + 1 => (layerTower B C G k).next (C (k + 2)) (G (k + 2))

variable (B : LayerTower.{u} n σ 0) (C : ℕ → Finset σ) (G : ℕ → Finset Label.{u})

@[simp] theorem layerTower_zero : layerTower B C G 0 = B := rfl

theorem layerTower_succ (k : ℕ) :
    layerTower B C G (k + 1) = (layerTower B C G k).next (C (k + 2)) (G (k + 2)) := rfl

/-! ### Laws -/

variable {B C G}

/-- **The tower is well formed** up to the number of points. -/
theorem isWellFormed_layerTower (hB : B.S.IsWellFormed) :
    ∀ k, k + 1 ≤ n → (layerTower B C G k).S.IsWellFormed
  | 0, _ => hB
  | k + 1, hk => by
    rw [layerTower_succ]
    exact isWellFormed_catalogueLayer (hS := (layerTower B C G k).not_le)
      (isWellFormed_layerTower hB k (by omega)) (by omega) hk

/-- **The tower is consistent, and writes the states of the next catalogue lawfully**, bounded by
the top of the next label set. -/
theorem layerTower_lawful (hCdec : ∀ k, C (k + 3) ⊆ C (k + 2)) (hG0 : ∀ k, ⊥ ∈ G (k + 2))
    (hGv : ∀ k, ∀ x ∈ G (k + 2), IsSelfVisible (k + 2) x) {y : ℕ → Label.{u}}
    (hy : ∀ k, y (k + 2) ∈ G (k + 2)) (hymax : ∀ k, ∀ x ∈ G (k + 2), x ≤ y (k + 2))
    (hymono : ∀ k, y (k + 2) ≤ y (k + 3)) (hBcons : B.S.rows.IsConsistent)
    (hBC : ∀ R ∈ C 2, B.S.rows.IsLawful (B.v R) ∧ ∀ x, B.v R x ≤ y 2) :
    ∀ k, (layerTower B C G k).S.rows.IsConsistent ∧ ∀ R ∈ C (k + 2),
      (layerTower B C G k).S.rows.IsLawful ((layerTower B C G k).v R) ∧
        ∀ x, (layerTower B C G k).v R x ≤ y (k + 2)
  | 0 => ⟨hBcons, hBC⟩
  | k + 1 => by
    obtain ⟨hcons, hlaw⟩ := layerTower_lawful hCdec hG0 hGv hy hymax hymono hBcons hBC k
    set T := layerTower B C G k with hT
    have hent : ∀ a ∈ T.entries (C (k + 2)), T.S.rows.IsLawful (fun d ↦ a d) ∧
        ∀ f, a f ≤ y (k + 2) := by
      intro a ha
      classical
      obtain ⟨R, hR, rfl⟩ := mem_image.mp ha
      exact hlaw R hR
    rw [layerTower_succ]
    refine ⟨isConsistent_catalogueLayer (hS := T.not_le) hcons (hG0 k) (hGv k) (hy k) (hymax k)
      hent,
      fun R hR ↦ ⟨?_, fun x ↦ ?_⟩⟩
    · classical
      have hR' := hCdec k hR
      exact isLawful_layerRow (hS := T.not_le) (hG0 k) (hGv k) (hy k) (hymax k)
        (mem_image_of_mem T.v hR') (hlaw R hR').1 (hlaw R hR').2
    · change layerRow T.S (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2))) (T.v R) x ≤
        y (k + 1 + 2)
      induction x using Fin.addCases with
      | left d =>
        rw [layerRow_castAdd]
        exact ((hlaw R (hCdec k hR)).2 d).trans (hymono k)
      | right j =>
        rw [layerRow_natAdd]
        exact (hymax k _ (agreementHeight_spec (hG0 k) _ _).1).trans (hymono k)

/-- **The tower is coded** when the base, its writing of the first catalogue and the label sets
lie below `ω ^ 2`. -/
theorem isCoded_layerTower (hCdec : ∀ k, C (k + 3) ⊆ C (k + 2)) (hG0 : ∀ k, ⊥ ∈ G (k + 2))
    (hGω : ∀ k, ∀ x ∈ G (k + 2), x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hBc : B.S.IsCoded)
    (hBω : ∀ R ∈ C 2, ∀ x, B.v R x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    ∀ k, (layerTower B C G k).S.IsCoded ∧ ∀ R ∈ C (k + 2), ∀ x,
      (layerTower B C G k).v R x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})
  | 0 => ⟨hBc, hBω⟩
  | k + 1 => by
    obtain ⟨hc, hω⟩ := isCoded_layerTower hCdec hG0 hGω hBc hBω k
    set T := layerTower B C G k with hT
    rw [layerTower_succ]
    refine ⟨isCoded_catalogueLayer (hS := T.not_le) hc (hG0 k) (hGω k) fun a ha f ↦ ?_,
      fun R hR x ↦ ?_⟩
    · classical
      obtain ⟨R, hR, rfl⟩ := mem_image.mp ha
      exact hω R hR f
    · change layerRow T.S (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2))) (T.v R) x < _
      induction x using Fin.addCases with
      | left d => rw [layerRow_castAdd]; exact hω R (hCdec k hR) d
      | right j => rw [layerRow_natAdd]; exact hGω k _ (agreementHeight_spec (hG0 k) _ _).1

/-- **Completeness of the tower**: with nonempty catalogues, every graded face that the base
completes, and every graded face of full scope at a grade between `2` and `k + 1`, is the graded
index of a cell. -/
theorem exists_gradedIndex_layerTower
    (hBcomp : ∀ X ∈ B.S.toCellScheme.gradedFaces, (X.2 ≤ 1 ∨ X.1 ≠ univ) →
      ∃ d, B.S.toCellScheme.gradedIndex d = X)
    (hne : ∀ k, (C (k + 2)).Nonempty) :
    ∀ k, ∀ X ∈ (layerTower B C G k).S.toCellScheme.gradedFaces, (X.2 ≤ k + 1 ∨ X.1 ≠ univ) →
      ∃ d, (layerTower B C G k).S.toCellScheme.gradedIndex d = X
  | 0 => hBcomp
  | k + 1 => by
    intro X hX hX2
    set T := layerTower B C G k with hT
    rw [layerTower_succ] at hX ⊢
    by_cases hlow : X.2 ≤ k + 1 ∨ X.1 ≠ univ
    · obtain ⟨d, hd⟩ := exists_gradedIndex_layerTower hBcomp hne k X hX hlow
      refine ⟨Fin.castAdd _ d, ?_⟩
      change (T.S.appendFullCellsScheme (k + 2) (T.entries (C (k + 2))).card).gradedIndex
        (Fin.castAdd _ d) = X
      rw [appendFullCellsScheme_gradedIndex_castAdd]
      exact hd
    · push Not at hlow
      have hX2' : X.2 = k + 2 := by
        rcases hX2 with h | h
        · omega
        · exact absurd hlow.2 h
      classical
      obtain ⟨R, hR⟩ := hne k
      obtain ⟨d, hd⟩ := exists_gradedIndex_eq_catalogueLayer (S := T.S) (k := k + 2)
        (read := fun d ↦ d) (G := G (k + 2)) (hS := T.not_le) ⟨_, mem_image_of_mem T.v hR⟩
      exact ⟨d, hd.trans (Prod.ext hlow.2.symm hX2'.symm)⟩

/-! ### The old cells -/

/-- The cells of the base in the tower at height `k`. -/
noncomputable def layerTowerEmb : (k : ℕ) → Fin B.S.card → Fin (layerTower B C G k).S.card
  | 0 => fun t ↦ t
  | k + 1 => fun t ↦ Fin.castAdd _ (layerTowerEmb k t)

/-- The cells of the base keep their graded indices in the tower. -/
theorem gradedIndex_layerTowerEmb (t : Fin B.S.card) :
    ∀ k, (layerTower B C G k).S.toCellScheme.gradedIndex
      (layerTowerEmb (B := B) (C := C) (G := G) k t) = B.S.toCellScheme.gradedIndex t
  | 0 => rfl
  | k + 1 => by
    change ((layerTower B C G k).S.appendFullCellsScheme (k + 2)
      ((layerTower B C G k).entries (C (k + 2))).card).gradedIndex
        (Fin.castAdd _ (layerTowerEmb k t)) = _
    rw [appendFullCellsScheme_gradedIndex_castAdd]
    exact gradedIndex_layerTowerEmb t k

/-- **The tower keeps the writing at the cells of the base.** -/
theorem layerTower_v_emb (R : σ) (t : Fin B.S.card) :
    ∀ k, (layerTower B C G k).v R (layerTowerEmb (B := B) (C := C) (G := G) k t) = B.v R t
  | 0 => rfl
  | k + 1 => by
    change layerRow (layerTower B C G k).S (fun d ↦ d) (G (k + 2))
      ((layerTower B C G k).entries (C (k + 2))) ((layerTower B C G k).v R)
        (Fin.castAdd _ (layerTowerEmb k t)) = _
    rw [layerRow_castAdd]
    exact layerTower_v_emb R t k

/-- **The controllers.**  At every height `K ≥ k + 1`, every cell of full scope at the grade
`k + 2` is a cell of a state `R` of `C (k + 2)` whose row reads, at every cell of the base of
grade at most `k + 2`, the writing of `R` in the base. -/
theorem exists_layerTower_controller (k : ℕ) :
    ∀ K, k + 1 ≤ K → ∀ u : Fin (layerTower B C G K).S.card,
      (layerTower B C G K).S.toCellScheme.gradedIndex u = ((univ : Finset (Fin n)), k + 2) →
      ∃ R ∈ C (k + 2), ∀ t : Fin B.S.card, B.S.toCellScheme.grade t ≤ k + 2 →
        (layerTower B C G K).S.rowAt u (layerTowerEmb K t) = B.v R t := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    intro u hu
    set T := layerTower B C G k with hT
    classical
    obtain ⟨i, rfl⟩ := exists_eq_natAdd_of_gradedIndex_catalogueLayer (S := T.S) (k := k + 2)
      (read := fun d ↦ d) (G := G (k + 2)) (C := T.entries (C (k + 2))) (hS := T.not_le) hu
    obtain ⟨R, hR, hRe⟩ := mem_image.mp (layerEntry_mem (C := T.entries (C (k + 2))) i)
    refine ⟨R, hR, fun t ht ↦ ?_⟩
    have hgt : T.S.toCellScheme.grade (layerTowerEmb k t) ≤ k + 2 := by
      have := congrArg Prod.snd (gradedIndex_layerTowerEmb (B := B) (C := C) (G := G) t k)
      change T.S.toCellScheme.grade (layerTowerEmb k t) = B.S.toCellScheme.grade t at this
      omega
    change (T.S.catalogueLayer (k + 2) (fun d ↦ d) (G (k + 2)) (T.entries (C (k + 2)))
      T.not_le).rowAt (Fin.natAdd _ i) (Fin.castAdd _ (layerTowerEmb k t)) = _
    rw [rowAt_catalogueLayer_castAdd i hgt, ← hRe]
    exact layerTower_v_emb R t k
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
    obtain ⟨R, hR, hrow⟩ := ih u' hu''
    refine ⟨R, hR, fun t ht ↦ ?_⟩
    change (T.S.catalogueLayer (K + 2) (fun d ↦ d) (G (K + 2)) (T.entries (C (K + 2)))
      T.not_le).rowAt (Fin.castAdd _ u') (Fin.castAdd _ (layerTowerEmb K t)) = _
    rw [rowAt_appendFullCells_castAdd]
    exact hrow t ht

end VaughtConjecture.Scheme
