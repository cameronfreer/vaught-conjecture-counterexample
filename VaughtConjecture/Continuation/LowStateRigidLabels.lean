/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateStepPin

/-!
# The labels of a stage type at a reader pinning a top

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: whether a legal LOW
family realizes the rigid reading that refutes the lifts of the state tower); semantic contract,
items 3, 4 and 8.

The rigid configuration refuting the lifts of the state tower
(`ProfileTower.not_sTowerLifts_of_rigid`) asks the cells of one graded index of the donor to read
a donor top `t` at the replacement at the grade `j` of their reading of a cell `d`.  The type's
own labels are a lawful labelling, and `t` is labelled `⊤`, so the pin
(`CellScheme.Rows.le_visibilityReplace_of_row_le`) constrains them.

**A reader pinning a top is labelled at most the replacement of the proper reading**
(`StageType.label_le_of_row_le`, compiled in this repository): if the row of `w` reads a cell
labelled `⊤` at most the replacement at `k ≤ grade w` of its reading of a cell `d` not labelled
`⊤`, then `label w ≤ R_k (label d)`.  With availability
(`StageType.label_le_of_row_le_of_availability`): a cell `u` of the grade of `w` with scope in that
of `w`, when every cell of the graded index of `w` pins the top, has `label u ≤ R_k (label d)`.

So in a legal family realizing the rigid configuration with `d` a proper cell, every reader at the
graded index and every cell available to it (in particular the prescribed cell `u` of the
configuration) carry type labels at most `R_j (label d)`: the configuration is a statement about
lawful labellings far above the type's own labels at those cells, which legality alone does not
forbid.  Whether a legal family realizes it is not decided here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset Label

variable {α : Ordinal.{u}} {n : ℕ}

/-- **A reader pinning a top is labelled at most the replacement of the proper reading.**  In a
stage type `t`, if the row of `w` reads a cell `t₀` labelled `⊤` at most the replacement at
`k ≤ grade w` of its reading of a cell `d` not labelled `⊤`, then
`t.label w ≤ visibilityReplace k k (t.label d)`. -/
theorem label_le_of_row_le {t : StageType.{u} α n} {w t₀ d : Fin t.card} {k : ℕ}
    (hk : k ≤ t.toCellScheme.grade w)
    (ht₀ : t₀ ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex w))
    (hd : d ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex w))
    (hrow : t.rowAt w t₀ ≤ visibilityReplace k k (t.rowAt w d)) (htop : t.label t₀ = ⊤)
    (hdne : t.label d ≠ ⊤) : t.label w ≤ visibilityReplace k k (t.label d) := by
  by_contra hlt
  rw [Scheme.rowAt_of_mem ht₀, Scheme.rowAt_of_mem hd] at hrow
  have h := CellScheme.Rows.le_visibilityReplace_of_row_le (t.isLawful.locality w) hk
    (d := ⟨t₀, ht₀⟩) (y := ⟨d, hd⟩) hrow (not_le.mp hlt)
  rw [htop, top_le_iff, visibilityReplace_eq_top_iff] at h
  exact hdne h

/-- **Availability carries the bound**: if every cell of the graded index of `w₀` reads `t₀`
(labelled `⊤`) at most the replacement at `k ≤ grade w₀` of its reading of `d` (not labelled `⊤`),
every cell `u` of the grade of `w₀` with scope in that of `w₀` has
`t.label u ≤ visibilityReplace k k (t.label d)`. -/
theorem label_le_of_row_le_of_availability {t : StageType.{u} α n} {w₀ t₀ d u : Fin t.card}
    {k : ℕ} (hk : k ≤ t.toCellScheme.grade w₀)
    (ht₀ : t₀ ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex w₀))
    (hd : d ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex w₀))
    (hrow : ∀ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex w₀ →
      t.rowAt w t₀ ≤ visibilityReplace k k (t.rowAt w d))
    (htop : t.label t₀ = ⊤) (hdne : t.label d ≠ ⊤)
    (hus : t.toCellScheme.scope u ⊆ t.toCellScheme.scope w₀)
    (hug : t.toCellScheme.grade u = t.toCellScheme.grade w₀) :
    t.label u ≤ visibilityReplace k k (t.label d) := by
  obtain ⟨w, hw, hle⟩ := t.isLawful.availability u w₀ hus hug
  have hgw : t.toCellScheme.grade w = t.toCellScheme.grade w₀ := congrArg Prod.snd hw
  exact hle.trans (label_le_of_row_le (hgw ▸ hk) (hw ▸ ht₀) (hw ▸ hd) (hrow w hw) htop hdne)

end VaughtConjecture.StageType
