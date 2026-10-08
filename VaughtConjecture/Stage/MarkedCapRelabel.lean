/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.MarkedCap

/-!
# The marked-cap context under relabelling

Roadmap, Layer 3 ((R3) of the table of 3.4: the marked-cap context of the hollow carrier).

Reindexing a stage type along a bijection `σ` of its points keeps every cell
(`Scheme.surjective_cellMap_equiv`), with its label, its grade, and the rows between cells
(`StageType.rowAt_reindex`).  So the marked-cap context (`StageType.IsMarkedCapContext`) is
invariant under relabelling, with the root relabelled along
(`StageType.IsMarkedCapContext.reindex`).  Each item is compiled in this repository (theorem
named).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Rows under reindexing**: the row of a cell of `t.reindex σ` at a cell is the row of the
corresponding cells of `t`. -/
theorem rowAt_reindex (t : StageType.{u} α k) (σ : Equiv.Perm (Fin k))
    (i j : Fin (t.reindex σ).card) :
    (t.reindex σ).rowAt i j =
      t.rowAt (t.toScheme.cellMap σ.toEmbedding i) (t.toScheme.cellMap σ.toEmbedding j) := by
  have hle := t.toScheme.isLowerEmbedding_comap σ.toEmbedding
  change (t.toScheme.comap σ.toEmbedding).rowAt i j = t.rowAt _ _
  unfold Scheme.rowAt
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((hle.le_iff j i).mpr h1) h2
  · exact absurd ((hle.le_iff j i).mp h2) h1
  · rfl

/-- **Below under reindexing**: a cell of `t.reindex σ` lies below another exactly when the
corresponding cells of `t` do. -/
theorem mem_below_reindex_iff (t : StageType.{u} α k) (σ : Equiv.Perm (Fin k))
    (i j : Fin (t.reindex σ).card) :
    j ∈ (t.reindex σ).toCellScheme.below ((t.reindex σ).toCellScheme.gradedIndex i) ↔
      t.toScheme.cellMap σ.toEmbedding j ∈
        t.toCellScheme.below (t.toCellScheme.gradedIndex (t.toScheme.cellMap σ.toEmbedding i)) :=
  ((t.toScheme.isLowerEmbedding_comap σ.toEmbedding).le_iff j i).symm

/-- **The marked-cap context is invariant under relabelling**: if `t'` is a marked-cap context
along `h`, then `t'.reindex σ` is one along `h.trans σ⁻¹`.  The top cap, the marker and the cells
of the root correspond through the cell map of `σ`. -/
theorem IsMarkedCapContext.reindex {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : t'.IsMarkedCapContext h) (σ : Equiv.Perm (Fin k)) :
    (t'.reindex σ).IsMarkedCapContext (h.trans σ.symm.toEmbedding) := by
  obtain ⟨c, r, ⟨hcs, hcl, hcg⟩, ⟨hrl, hrb, hrm⟩, hn, hroot⟩ := ht
  have hsurj := t'.toScheme.surjective_cellMap_equiv σ
  obtain ⟨c', rfl⟩ := hsurj c
  obtain ⟨r', rfl⟩ := hsurj r
  refine ⟨c', r', ⟨?_, hcl, fun x hx ↦ hcg _ hx⟩,
    ⟨hrl, (mem_below_reindex_iff t' σ c' r').mpr hrb, fun x hx hxb ↦ ?_⟩, hn, fun a ha hat ↦ ?_⟩
  · -- the scope of a cell of the reindexed type is the preimage of the scope of its cell
    change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding c')).preimage
      σ.toEmbedding σ.toEmbedding.injective.injOn = univ
    rw [hcs]
    exact Finset.preimage_univ _
  · exact (rowAt_reindex t' σ c' r').trans_le
      ((hrm _ hx ((mem_below_reindex_iff t' σ c' x).mp hxb)).trans_eq
        (rowAt_reindex t' σ c' x).symm)
  · have hvis : t'.toScheme.cellMap σ.toEmbedding a ∈ t'.visibleCells h := by
      rw [Scheme.mem_visibleCells] at ha ⊢
      intro y hy
      have hy' : σ.symm y ∈ ((t'.reindex σ).toCellScheme.scope a : Set (Fin k)) := by
        change σ.symm y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding a)).preimage
          σ.toEmbedding σ.toEmbedding.injective.injOn
        simpa using hy
      obtain ⟨i, hi⟩ := ha hy'
      exact ⟨i, by simpa using congrArg σ hi⟩
    exact (congrArg (visibilityReplace _ (n + 1)) (rowAt_reindex t' σ c' r')).trans_le
      ((hroot _ hvis hat).trans_eq (rowAt_reindex t' σ c' a).symm)

end StageType

end VaughtConjecture
