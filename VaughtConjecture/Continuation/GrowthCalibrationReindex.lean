/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthReferenceCalibration
import VaughtConjecture.Continuation.RootBottomDetermination

/-!
# The reference calibration under relabelling

Roadmap, Layer 3 ((R3), the growth carrier at a calibrated context).

The hollow reference calibration with bounded donor offsets
(`StageType.HollowReferenceCalibration'`) is invariant under relabelling the points of the
context (`StageType.HollowReferenceCalibration'.reindex`): the enlarged root, the cap, the marker
and the reference cells correspond through the cell map of the permutation, with their labels,
grades and rows (`StageType.rowAt_reindex`, `StageType.mem_below_reindex_iff`), as for the marked
cap contexts (`TiedRootCapRelabel.MarkedCapContextBelow'.reindex`).  So a chosen point of the
context, such as an extreme point off the root, may be put last.

## References

Reindexing of stage types is [Kni26, Definition 3.1.2].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- Visibility through a root after reindexing: a cell of `t'.reindex σ` is visible through
`g.trans σ.symm` exactly when the corresponding cell of `t'` is visible through `g`. -/
theorem mem_visibleCells_reindex_iff (t' : StageType.{u} α k) (σ : Equiv.Perm (Fin k))
    {j : ℕ} (g : Fin j ↪ Fin k) (a : Fin (t'.reindex σ).card) :
    a ∈ (t'.reindex σ).visibleCells (g.trans σ.symm.toEmbedding) ↔
      t'.toScheme.cellMap σ.toEmbedding a ∈ t'.visibleCells g := by
  constructor
  · intro ha
    rw [Scheme.mem_visibleCells] at ha ⊢
    intro y hy
    have hy' : σ.symm y ∈ ((t'.reindex σ).toCellScheme.scope a : Set (Fin k)) := by
      change σ.symm y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding a)).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn
      simpa using hy
    obtain ⟨i, hi⟩ := ha hy'
    exact ⟨i, by simpa using congrArg σ hi⟩
  · intro ha
    rw [Scheme.mem_visibleCells] at ha ⊢
    intro y hy
    have hy' : σ y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding a) :
        Set (Fin k)) := by
      have : y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding a)).preimage
          σ.toEmbedding σ.toEmbedding.injective.injOn := hy
      simpa using this
    obtain ⟨i, hi⟩ := ha hy'
    exact ⟨i, by simp [hi]⟩

/-- **The reference calibration is invariant under relabelling**: the enlarged root, the cap, the
marker and the reference cells correspond through the cell map of `σ`, with their labels, grades
and rows. -/
theorem HollowReferenceCalibration'.reindex {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hC : HollowReferenceCalibration' t' h d)
    (σ : Equiv.Perm (Fin k)) :
    HollowReferenceCalibration' (t'.reindex σ) (h.trans σ.symm.toEmbedding) d := by
  obtain ⟨j, g, h₀, c, r, hh, hmc, hoff, hbot, href⟩ := hC
  have hsurj := t'.toScheme.surjective_cellMap_equiv σ
  obtain ⟨c', rfl⟩ := hsurj c
  obtain ⟨r', rfl⟩ := hsurj r
  have hvis (a : Fin (t'.reindex σ).card)
      (ha : a ∈ (t'.reindex σ).visibleCells (g.trans σ.symm.toEmbedding)) :
      t'.toScheme.cellMap σ.toEmbedding a ∈ t'.visibleCells g :=
    (mem_visibleCells_reindex_iff t' σ g a).mp ha
  refine ⟨j, g.trans σ.symm.toEmbedding, h₀, c', r', ?_, ?_, fun a ha μ f hμ hf ↦
    hoff _ (hvis a ha) μ f hμ hf, fun a ha hab ↦ (rowAt_reindex t' σ c' a).trans
      (hbot _ (hvis a ha) hab), fun i o ho ↦ ?_⟩
  · rw [← hh]
    rfl
  · obtain ⟨⟨hcs, hcl, hcg⟩, ⟨hrl, hrb, hrm⟩, hn, hroot⟩ := hmc
    refine ⟨⟨?_, hcl, fun x hx ↦ hcg _ hx⟩, ⟨hrl, (mem_below_reindex_iff t' σ c' r').mpr hrb,
      fun x hx hxb ↦ ?_⟩, hn, fun a ha hat ↦ ?_⟩
    · change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding c')).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn = univ
      rw [hcs]
      exact Finset.preimage_univ _
    · exact (rowAt_reindex t' σ c' r').trans_le
        ((hrm _ hx ((mem_below_reindex_iff t' σ c' x).mp hxb)).trans_eq
          (rowAt_reindex t' σ c' x).symm)
    · exact (congrArg (visibilityReplace _ (j + 1)) (rowAt_reindex t' σ c' r')).trans_le
        ((hroot _ (hvis a ha) hat).trans_eq (rowAt_reindex t' σ c' a).symm)
  · obtain ⟨μ, m, r'', a, hμ, hom, hmN, ha, hal⟩ := href i o ho
    obtain ⟨a', rfl⟩ := hsurj a
    exact ⟨μ, m, r'', a', hμ, hom, hmN, (mem_visibleCells_reindex_iff t' σ g a').mpr ha, hal⟩

end StageType

end VaughtConjecture
