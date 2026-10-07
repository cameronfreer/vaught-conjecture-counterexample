/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapContext
import VaughtConjecture.Extension.GatedExtensionCounterexample

/-!
# A legal source-gap context

Roadmap, Layer 3 ((R2) of the table of 3.4); the source-gap contexts of
`VaughtConjecture.Continuation.SourceGapContext`.

**The private type `P α` is a source-gap context** (`GatedExtensionCounterexample.
isSourceGapContextAt_P`, compiled in this repository).  The legal stage type
`GatedExtensionCounterexample.P α` on two points (at every stage `α`) has two cells of full scope
and grade `2`, the cells `3` and `4`, both labelled `⊤`, and every other cell labelled `⊥`; the
row of `3` reads `(3, 4)` as `(3, 2)`.  Along any root avoiding the point `1`, it is a source-gap
context of grade `2`, with lost point `1`, owner `3`, and lost top `4`:

* its top grade is `2`;
* the gap at the owner is `visibilityReplace 2 2 2 = 2 < 3`;
* no top cell avoids the point `1` (the only top cells have full scope), so there is no retained
  top cell and the gaps at retained cells hold vacuously.

The roots include the empty root and the root `{0}` along `Fin.castSuccEmb`; the face of `P α`
on `{0}` is top-free.

**So the vacuity argument for (R2) is ruled out**
(`Realization.not_forall_not_isSourceGapContext`): some legal stage type is a source-gap context,
so the hypothesis of `Realization.residualReceiving_of_forall_not_isSourceGapContext` is false.
This rules out that argument only, not (R2): (R2) may still be proved by another argument.  It
says nothing about whether `P α` is acquired in a residual model, nor about cutoff determination
over it.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace GatedExtensionCounterexample

/-- Every cell of `P α` lies below the full cell `3`. -/
private theorem mem_below_three (α : Ordinal.{u}) (d : Fin (P α).card) :
    d ∈ (P α).toCellScheme.below ((P α).toCellScheme.gradedIndex (3 : Fin 5)) :=
  (CellScheme.gradedIndex_le_iff _).mpr ⟨subset_univ _, (P α).grade_le d⟩

/-- **The private type `P α` is a source-gap context** of grade `2` along every root avoiding the
point `1`, with lost point `1`, owner `3` and lost top `4`. -/
theorem isSourceGapContextAt_P (α : Ordinal.{u}) {n : ℕ} (h : Fin n ↪ Fin 2)
    (hh : (1 : Fin 2) ∉ Set.range h) :
    (P α).IsSourceGapContextAt 2 h 1 (3 : Fin 5) (4 : Fin 5) where
  notMem_range := hh
  topGrade_eq := le_antisymm (topGrade_le_iff.mpr fun d _ ↦ (P α).grade_le d)
    (grade_le_topGrade (t := P α) (d := (3 : Fin 5)) rfl :)
  scope_owner := rfl
  grade_owner := rfl
  label_owner := rfl
  label_lost := rfl
  mem_scope_lost := mem_univ _
  gap_owner := by
    rw [Scheme.rowAt_of_mem (mem_below_three α (4 : Fin 5)),
      Scheme.rowAt_of_mem (mem_below_three α (3 : Fin 5))]
    -- the row of `3` reads `4` as `2` and `3` as `3` (`rows`, by definition)
    change visibilityReplace 2 2 ((2 : ℕ) : Label.{u}) < ((3 : ℕ) : Label.{u})
    simpa using natCast_label_lt.{u}.mpr (by decide : 2 < 3)
  gap_retained a ha hla := by
    exfalso
    -- the cells of `P α` are the five cells of `cells`
    change Fin 5 at a
    fin_cases a
    · exact absurd ha (by simp [P, labelling])
    · exact absurd ha (by simp [P, labelling])
    · exact absurd ha (by simp [P, labelling])
    · exact hla (mem_univ _)
    · exact hla (mem_univ _)

/-- **`P α` is a source-gap context along the root `{0}`**, whose face is top-free. -/
theorem isSourceGapContext_P (α : Ordinal.{u}) :
    (P α).IsSourceGapContext 2 (Fin.castSuccEmb : Fin 1 ↪ Fin 2) :=
  ⟨1, _, _, isSourceGapContextAt_P α _ fun ⟨i, hi⟩ ↦ (Fin.castSucc_lt_last i).ne hi⟩

end GatedExtensionCounterexample

namespace Realization

/-- **Some legal stage type is a source-gap context**: the hypothesis of
`residualReceiving_of_forall_not_isSourceGapContext` is false, at every universe level.  This
rules out the vacuity argument for (R2), not (R2) itself. -/
theorem not_forall_not_isSourceGapContext :
    ¬ ∀ ⦃α : Ordinal.{u}⦄ ⦃n k K : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      t'.IsLegal → ¬ t'.IsSourceGapContext K h :=
  fun h ↦ h _ _ (GatedExtensionCounterexample.isLegal_P 0)
    (GatedExtensionCounterexample.isSourceGapContext_P 0)

end Realization

end VaughtConjecture
