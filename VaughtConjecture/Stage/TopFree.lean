/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Basic

/-!
# Top-free stage types

A stage type is **top-free** (`StageType.IsTopFree`) when no cell carries the label `⊤`: every
label is proper or bottom.  Top-free stage types are closed under restriction to closed faces and
reindexing (`StageType.IsTopFree.comap`, `StageType.IsTopFree.restrictFace`,
`StageType.IsTopFree.reindex`), and every stage type on no points is top-free, having no cells
(`StageType.isTopFree_of_zero`).

Top-freeness is the conclusion of the top-free pinned extension, statement (R5) of the table of
roadmap, Layer 3, 3.4, and it defines the age of top-free charts
(`VaughtConjecture.ClassicalLimit.Age`).

## Placement

This file belongs to Layer 1 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.StageType

open Finset

variable {α : Ordinal.{u}} {n m : ℕ}

/-- A stage type is **top-free** when no cell carries the label `⊤`. -/
def IsTopFree (t : StageType.{u} α n) : Prop :=
  ∀ d, t.label d ≠ ⊤

variable {t : StageType.{u} α n}

/-- The restriction of a top-free stage type to a closed face is top-free: its labels are labels
of the stage type. -/
theorem IsTopFree.comap (ht : t.IsTopFree) {f : Fin m ↪ Fin n}
    (hf : univ.map f ∈ t.toCellScheme.faces) : (t.comap f hf).IsTopFree :=
  fun _ ↦ ht _

/-- A face of a top-free stage type is top-free. -/
theorem IsTopFree.restrictFace (ht : t.IsTopFree) {f : Fin m ↪ Fin n} {u : StageType.{u} α m}
    (hu : restrictFace f t = some u) : u.IsTopFree := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  exact ht.comap hf

/-- A reindexing of a top-free stage type is top-free. -/
theorem IsTopFree.reindex (ht : t.IsTopFree) (e : Fin m ≃ Fin n) : (t.reindex e).IsTopFree :=
  ht.comap _

/-- A stage type on no points is top-free: it has no cells, since a cell has a positive grade at
most the size of its scope, which is empty. -/
theorem isTopFree_of_zero (t : StageType.{u} α 0) : t.IsTopFree := fun d ↦ by
  have hle := t.isWellFormed.isWellFormed.grade_le_card d
  have hpos := t.isWellFormed.isWellFormed.grade_pos d
  rw [eq_empty_of_isEmpty (t.toCellScheme.scope d), card_empty] at hle
  omega

end VaughtConjecture.StageType
