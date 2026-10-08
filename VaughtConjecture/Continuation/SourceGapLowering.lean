/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapContext

/-!
# The lowering below the owner of a source-gap context

Roadmap, Layer 3 ((R2) of the table of 3.4); the source-gap contexts of
`VaughtConjecture.Continuation.SourceGapContext`.

A source-gap context is stated through one row, that of the owner.  This file shows that the row
carries a lawful labelling that lowers the lost top and keeps the owner and the retained top cells
at `⊤`.

**The collapse of a lawful section.**  For `β` zero or a limit and `N` above every grade, the
collapse above `β + N` (`Label.collapse β N`, stage reduction to `β + N`: labels at least `β + N`
go to `⊤`) of a lawful section is lawful (`CellScheme.Rows.IsLawful.collapse`, compiled in this
repository), by `Label.TransformsTo.collapse` at each locality, monotonicity at availability, and
`Label.IsSelfVisible.reduce` at the order law; the same holds below a pair whose grade is below `N`
(`CellScheme.Rows.IsLawfulBelow.collapse`).

**The lowering below the owner** (`StageType.IsSourceGapContextAt.exists_isLawfulBelow`, compiled
in this repository).  In a legal source-gap context with owner `o` and lost top `r`, the row of `o`
is lawful below `o` (consistency), and it reads `r` at an ordinal `μ + j` (`μ` zero or a limit; not
`⊥`, since `o` and `r` are labelled `⊤`).  Its replacement at the top grade `K` is `μ + max j K`, so
the strict gaps put the row at the owner and at every retained top cell at or above
`μ + (max j K + 1)`.  The collapse of the row above that ordinal is lawful below `o`, `⊤` at the
owner and at every retained top cell, and equal to the row value `μ + j` at the lost top.  So the
row condition defining a source-gap context gives, below the owner, a lawful labelling separating
the lost top from the retained ones: the lowering that an admissible top support provides in the
acquisition (`Realization.exists_covers_isSourceGapContextAt`), here recovered from the rows alone,
below the owner.  Its extension to all cells (by bountifulness, from the graded index of the owner
to that of full scope and full grade) is not compiled here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The collapse of a lawful section -/

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {p : ι → Label.{u}}

/-- **The collapse of a lawful section is lawful**: for `β` zero or a limit and every grade at most
`K < N`, the collapse above `β + N` of a lawful section is lawful. -/
theorem IsLawful.collapse {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) {K N : ℕ}
    (hK : ∀ d, D.grade d ≤ K) (hKN : K < N) (h : R.IsLawful p) :
    R.IsLawful fun d ↦ Label.collapse β N (p d) where
  orderly d := (h.orderly d).reduce _
  locality s := by
    have := (h.locality s).collapse hβ (fun d : D.below (D.gradedIndex s) ↦ hK d.1) hKN
    convert this using 2 with d
    exact ((monotone_reduce _).map_min).symm
  availability s t hst hg :=
    let ⟨u, hu, hle⟩ := h.availability s t hst hg
    ⟨u, hu, monotone_reduce _ hle⟩

/-- **The collapse of a labelling lawful below a pair is lawful below it**, for `β` zero or a limit
and `N` above the grade of the pair. -/
theorem IsLawfulBelow.collapse {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) {N : ℕ}
    {X : Finset α × ℕ} (hXN : X.2 < N) {q : D.below X → Label.{u}} (h : R.IsLawfulBelow X q) :
    R.IsLawfulBelow X fun d ↦ Label.collapse β N (q d) :=
  IsLawful.collapse hβ (K := X.2) (fun d : D.below X ↦ ((D.gradedIndex_le_iff).mp d.2).2) hXN h

end CellScheme.Rows

/-! ### The lowering below the owner -/

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ} {K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
  {l : Fin k} {o r : Fin t'.card}

/-- In a source-gap context, every top cell lies below the owner. -/
theorem IsSourceGapContextAt.mem_below (hs : t'.IsSourceGapContextAt K h l o r) {a : Fin t'.card}
    (ha : t'.label a = ⊤) : a ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) := by
  rw [CellScheme.mem_below, CellScheme.gradedIndex_le_iff]
  refine ⟨?_, ?_⟩
  · -- the graded index of the owner is its scope and grade
    change _ ⊆ t'.toCellScheme.scope o
    rw [hs.scope_owner]
    exact subset_univ _
  · -- the graded index of the owner is its scope and grade
    change _ ≤ t'.toCellScheme.grade o
    rw [hs.grade_owner, ← hs.topGrade_eq]
    exact grade_le_topGrade ha

/-- **The lowering below the owner**: in a legal source-gap context with owner `o` and lost top
`r`, some labelling lawful below `o` is `⊤` at the owner and at every top cell avoiding the lost
point, and equal to the row of the owner at the lost top, which is not `⊤`.  It is the collapse of
the row of the owner above `μ + (max j K + 1)`, where the row reads the lost top at `μ + j`. -/
theorem IsSourceGapContextAt.exists_isLawfulBelow (ht' : t'.IsLegal)
    (hs : t'.IsSourceGapContextAt K h l o r) :
    ∃ q : t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) → Label.{u},
      t'.rows.IsLawfulBelow (t'.toCellScheme.gradedIndex o) q ∧
      q ⟨o, t'.toCellScheme.mem_below_gradedIndex o⟩ = ⊤ ∧
      (∀ a : t'.toCellScheme.below (t'.toCellScheme.gradedIndex o), t'.label a = ⊤ →
        l ∉ t'.toCellScheme.scope a → q a = ⊤) ∧
      q ⟨r, hs.mem_below hs.label_lost⟩ = t'.rowAt o r ∧ t'.rowAt o r ≠ ⊤ := by
  have hrb := hs.mem_below hs.label_lost
  have hrow : t'.rowAt o r = t'.rows.row o ⟨r, hrb⟩ := Scheme.rowAt_of_mem hrb
  -- the row of the owner reads the lost top at an ordinal
  have hne_bot : t'.rows.row o ⟨r, hrb⟩ ≠ ⊥ := fun h0 ↦ by
    have := t'.isLawful.label_eq_bot_of_reading hrb h0 (by rw [hs.label_owner]; exact top_ne_bot)
    rw [hs.label_lost] at this
    exact top_ne_bot this
  have hne_top : t'.rows.row o ⟨r, hrb⟩ ≠ ⊤ := fun h1 ↦ by
    have := ht'.isCoded o ⟨r, hrb⟩
    rw [h1] at this
    exact not_top_lt this
  obtain ⟨x, hx⟩ := isProper_iff_ne.mpr ⟨hne_bot, hne_top⟩
  obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit x
  set N := max j K + 1 with hN
  -- the replaced value at the lost top is `μ + max j K`
  have hvr : visibilityReplace K K (t'.rowAt o r) = ((μ + (max j K : ℕ) : Ordinal.{u}) : Label.{u})
      := by
    rw [hrow, ← hx, visibilityReplace_coe_add hμ]
    split_ifs with hj
    · rw [max_eq_right hj.le]
    · rw [max_eq_left (not_lt.mp hj)]
  -- the strict gaps put every retained value at or above `μ + N`
  have hge {y : Label.{u}} (hy : visibilityReplace K K (t'.rowAt o r) < y) :
      ((μ + N : Ordinal.{u}) : Label.{u}) ≤ y := by
    rw [hvr] at hy
    have h1 : ((μ + N : Ordinal.{u}) : Label.{u}) = ((μ + (max j K : ℕ) + 1 : Ordinal.{u}) :
        Label.{u}) := by
      rw [hN, Nat.cast_add_one, add_assoc]
    rw [h1]
    exact not_lt.mp fun h2 ↦ (lt_coe_add_one_iff.mp h2).not_gt hy
  have hNK : (t'.toCellScheme.gradedIndex o).2 < N := by
    change t'.toCellScheme.grade o < N
    rw [hs.grade_owner, hN]
    omega
  have hcons := ht'.isConsistent o
  refine ⟨fun d ↦ Label.collapse μ N (t'.rows.row o d), hcons.collapse hμ hNK, ?_, ?_, ?_, ?_⟩
  · -- the owner
    refine reduce_of_le (hge ?_)
    have := hs.gap_owner
    rwa [Scheme.rowAt_of_mem (t'.toCellScheme.mem_below_gradedIndex o)] at this
  · -- the retained top cells
    intro a ha hla
    refine reduce_of_le (hge ?_)
    have := hs.gap_retained a ha hla
    rwa [Scheme.rowAt_of_mem a.2] at this
  · -- the lost top: the collapse is stage reduction to `μ + N`
    change Label.reduce (μ + N) (t'.rows.row o ⟨r, hrb⟩) = _
    rw [hrow, ← hx]
    refine reduce_of_lt ?_
    exact_mod_cast (add_lt_add_iff_left μ).mpr (by rw [hN]; exact_mod_cast (by omega : j < N))
  · rw [hrow]
    exact hne_top

end StageType

end VaughtConjecture
