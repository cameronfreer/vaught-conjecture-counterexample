/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedFieldLayer

/-!
# Coding, consistency and the full cell of the admitted field layer

Roadmap, Layer 3, 3.1, under "(R6)": three facts about the admitted field layer
(`Scheme.admittedFieldLayer`) used by the continuation modules, stated for the admitted catalogue
from the corresponding facts of the field layer on a sub-catalogue
(`Scheme.isConsistent_fieldLayerOn`, `Scheme.isCoded_fieldLayerOn`, `Scheme.exists_entryOn_eq`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {S : Scheme.{u} n} {k : ℕ}
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}
  {A : (Fin S.card → Label.{u}) → Prop}

/-- **The admitted field layer is consistent.** -/
theorem isConsistent_admittedFieldLayer (hcons : S.rows.IsConsistent) :
    (S.admittedFieldLayer k A hS).rows.IsConsistent :=
  isConsistent_fieldLayerOn hcons admittedCatalogue_subset

/-- **The admitted field layer is coded.** -/
theorem isCoded_admittedFieldLayer (hc : S.IsCoded) : (S.admittedFieldLayer k A hS).IsCoded :=
  isCoded_fieldLayerOn hc admittedCatalogue_subset

/-- **The admitted field layer carries a cell at `(univ, k)`** when `A` holds at the constant `⊥`.
-/
theorem exists_gradedIndex_eq_admittedFieldLayer (hA : A fun _ ↦ ⊥) :
    ∃ u, (S.admittedFieldLayer k A hS).toCellScheme.gradedIndex u = (univ, k) := by
  obtain ⟨i, -⟩ := exists_entryOn_eq (bot_mem_admittedCatalogue (S := S) (k := k) hA)
  exact ⟨Fin.natAdd _ i, appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩

end VaughtConjecture.Scheme
