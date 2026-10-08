/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapContext
import VaughtConjecture.Stage.MarkedCapRelabel

/-!
# The source-gap context under relabelling

Roadmap, Layer 3 ((R2) of the table of 3.4: the source-gap context of the residual carrier).

Reindexing a stage type along a bijection `σ` of its points keeps every cell
(`Scheme.surjective_cellMap_equiv`), with its label, its grade, the rows between cells
(`StageType.rowAt_reindex`), and its top grade (`StageType.topGrade_reindex`).  So the source-gap
context (`StageType.IsSourceGapContextAt`, `StageType.IsSourceGapContext`) is invariant under
relabelling, with the root and the lost point relabelled along
(`StageType.IsSourceGapContextAt.reindex`, `StageType.IsSourceGapContext.reindex`).  Each item is
compiled in this repository (theorem named).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **The top grade under reindexing**: reindexing along a bijection keeps the cells labelled `⊤`
with their grades. -/
theorem topGrade_reindex (t : StageType.{u} α k) (σ : Equiv.Perm (Fin k)) :
    (t.reindex σ).topGrade = t.topGrade := by
  have hsurj := t.toScheme.surjective_cellMap_equiv σ
  refine le_antisymm (topGrade_le_iff.mpr fun d hd ↦ grade_le_topGrade (t := t) hd)
    (topGrade_le_iff.mpr fun d hd ↦ ?_)
  obtain ⟨d', rfl⟩ := hsurj d
  exact grade_le_topGrade (t := t.reindex σ) (d := d') hd

/-- **The source-gap clauses are invariant under relabelling**: if `t'` satisfies them along `h`
at the lost point `l`, the owner `o` and the lost top `r`, then `t'.reindex σ` satisfies them along
`h.trans σ⁻¹` at the lost point `σ⁻¹ l` and at the cells corresponding to `o` and `r`. -/
theorem IsSourceGapContextAt.reindex {K : ℕ} {t' : StageType.{u} α k} {σ : Equiv.Perm (Fin k)}
    {h : Fin n ↪ Fin k} {l : Fin k} {o' r' : Fin (t'.reindex σ).card}
    (hs : t'.IsSourceGapContextAt K h l (t'.toScheme.cellMap σ.toEmbedding o')
      (t'.toScheme.cellMap σ.toEmbedding r')) :
    (t'.reindex σ).IsSourceGapContextAt K (h.trans σ.symm.toEmbedding) (σ.symm l) o' r' := by
  have hscope (x : Fin (t'.reindex σ).card) (y : Fin k) :
      y ∈ (t'.reindex σ).toCellScheme.scope x ↔
        σ y ∈ t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding x) := by
    change y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding x)).preimage
      σ.toEmbedding σ.toEmbedding.injective.injOn ↔ _
    rw [Finset.mem_preimage]
    rfl
  refine
    { notMem_range := fun ⟨i, hi⟩ ↦ hs.notMem_range ⟨i, by simpa using congrArg σ hi⟩
      topGrade_eq := (topGrade_reindex t' σ).trans hs.topGrade_eq
      scope_owner := Finset.eq_univ_of_forall fun y ↦ (hscope o' y).mpr
        (hs.scope_owner ▸ Finset.mem_univ _)
      grade_owner := hs.grade_owner
      label_owner := hs.label_owner
      label_lost := hs.label_lost
      mem_scope_lost := (hscope r' _).mpr (by simpa using hs.mem_scope_lost)
      gap_owner := (congrArg (visibilityReplace K K) (rowAt_reindex t' σ o' r')).trans_lt
        (hs.gap_owner.trans_eq (rowAt_reindex t' σ o' o').symm)
      gap_retained := fun a ha hla ↦
        (congrArg (visibilityReplace K K) (rowAt_reindex t' σ o' r')).trans_lt
          ((hs.gap_retained _ ha fun hm ↦ hla ((hscope a _).mpr (by simpa using hm))).trans_eq
            (rowAt_reindex t' σ o' a).symm) }

/-- **The source-gap context is invariant under relabelling**: if `t'` is a source-gap context of
grade `K` along `h`, then `t'.reindex σ` is one along `h.trans σ⁻¹`. -/
theorem IsSourceGapContext.reindex {K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (hs : t'.IsSourceGapContext K h) (σ : Equiv.Perm (Fin k)) :
    (t'.reindex σ).IsSourceGapContext K (h.trans σ.symm.toEmbedding) := by
  obtain ⟨l, o, r, hs⟩ := hs
  have hsurj := t'.toScheme.surjective_cellMap_equiv σ
  obtain ⟨o', rfl⟩ := hsurj o
  obtain ⟨r', rfl⟩ := hsurj r
  exact ⟨σ.symm l, o', r', hs.reindex⟩

end StageType

end VaughtConjecture
