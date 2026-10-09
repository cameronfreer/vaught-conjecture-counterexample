/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Legal

/-!
# A scheme restricted to a lower set of its cells

Roadmap, Layer 3 ((R3) and (R4), the attachment under the replicated carrier).

For a scheme `S` and a **lower set** `L` of its cells (every cell below a cell of `L` is in `L`),
the **restriction** (`Scheme.restrictLower S L hL`) has the cells of `L` in their order, with
their scopes, grades and rows, and the ground set and faces of `S`.  The inclusion of the cells is a
lower embedding keeping scopes along which the rows pull back (`Scheme.isLowerEmbedding_lowerEmb`);
well-formedness, coding and consistency pass to the restriction
(`Scheme.isWellFormed_restrictLower`, `Scheme.isCoded_restrictLower`,
`Scheme.isConsistent_restrictLower`).

The intended instance is the **attachment** of a donor to a context: the cells of the amalgam of a
seed whose scope lies in the context face or in the donor face, with the plan of the amalgam; its
mixed faces carry no cell, and receive the copies of the cells of full scope.

## References

Lawful sections and consistency are [Kni26, Definitions 2.5.4 and 2.5.12].
-/

universe u

namespace VaughtConjecture.Scheme

open Finset

variable {n : ℕ} (S : Scheme.{u} n) (L : Finset (Fin S.card))
  (hL : ∀ c ∈ L, ∀ d, S.toCellScheme.gradedIndex d ≤ S.toCellScheme.gradedIndex c → d ∈ L)

/-- The enumeration in increasing order of the cells of `L`. -/
noncomputable def lowerEmb : Fin #L ↪o Fin S.card := L.orderEmbOfFin rfl

include hL in
/-- **The inclusion of a lower set is a lower embedding.** -/
theorem isLowerEmbedding_lowerEmb :
    (S.toCellScheme.reindex (S.lowerEmb L)).IsLowerEmbedding S.toCellScheme (S.lowerEmb L) where
  injective := (S.lowerEmb L).injective
  grade_eq _ := rfl
  le_iff _ _ := Iff.rfl
  mem_range t d hd := by
    have hdL := hL _ (L.orderEmbOfFin_mem rfl t) d hd
    have h := (L.range_orderEmbOfFin rfl).symm ▸ (Finset.mem_coe.mpr hdL)
    exact h

/-- **The restriction of a scheme to a lower set of its cells.** -/
noncomputable def restrictLower : Scheme.{u} n where
  card := #L
  toCellScheme := S.toCellScheme.reindex (S.lowerEmb L)
  rows := S.rows.comap (S.isLowerEmbedding_lowerEmb L hL)

theorem restrictLower_scope (i : Fin (S.restrictLower L hL).card) :
    (S.restrictLower L hL).toCellScheme.scope i = S.toCellScheme.scope (S.lowerEmb L i) := rfl

theorem restrictLower_grade (i : Fin (S.restrictLower L hL).card) :
    (S.restrictLower L hL).toCellScheme.grade i = S.toCellScheme.grade (S.lowerEmb L i) := rfl

theorem restrictLower_faces :
    (S.restrictLower L hL).toCellScheme.faces = S.toCellScheme.faces := rfl

variable {S L hL}

theorem isWellFormed_restrictLower (hS : S.IsWellFormed) :
    (S.restrictLower L hL).IsWellFormed :=
  ⟨hS.ground_eq, hS.isWellFormed.reindex _⟩

theorem isCoded_restrictLower (hS : S.IsCoded) : (S.restrictLower L hL).IsCoded :=
  fun _ _ ↦ hS _ _

theorem isConsistent_restrictLower (hS : S.rows.IsConsistent) :
    (S.restrictLower L hL).rows.IsConsistent :=
  hS.comap (S.isLowerEmbedding_lowerEmb L hL)

/-- A lawful section of `S` restricts to a lawful section of the restriction. -/
theorem isLawful_restrictLower {v : Fin S.card → Label.{u}} (hv : S.rows.IsLawful v) :
    (S.restrictLower L hL).rows.IsLawful (v ∘ S.lowerEmb L) :=
  hv.comap (S.isLowerEmbedding_lowerEmb L hL)

end VaughtConjecture.Scheme
