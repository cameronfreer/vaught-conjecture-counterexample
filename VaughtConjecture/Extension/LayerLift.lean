/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing

/-!
# Lifting into a layer of full scope from a coatom face

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the scheme over the private context and the
donor, its layer of cells of full scope at the full grade of the private context) and Layer 1
(bountifulness); semantic contract, item 3.

Everything here holds for arbitrary semantic rows `R` of a cell scheme `D` on a ground set with a
full face `A` and a face `S ⊆ A`, `S ≠ A` (in (R1): the private face, of `N` points, inside the
`N + 1` points of the scheme).

**Bountifulness from the lifts below the layer and the lifts from the large faces**
(`CellScheme.Rows.isBountiful_of_cappedLift_full`).  On a ground set `A` whose faces other than
`A` have at most `N` elements, rows that lift capped between graded faces at every target that is
a proper face or has grade below `N`, and that lift capped from `(B, N)` to `(A, N)` for every face
`B ≠ A` of `N` elements, are bountiful: by the reduction to equal grades
(`CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst`), every other lift is between pairs on
the face `A`.  In (R1) the faces of `N` elements other than `A` are the two coatoms of the plan:
the private face and the coatom through the new point.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Extension.Gluing`.

## References

Lawful sections are [Kni26, Definition 2.5.4] and bountifulness [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Finset Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- **Bountifulness from the lifts below the layer and the lifts from the large faces.**  If every
face other than `A` has at most `N` elements, the rows lift capped between graded faces at every
target that is a proper face or has grade below `N`, and they lift capped from `(B, N)` to `(A, N)`
for every face `B ≠ A` of `N` elements, then they are bountiful. -/
theorem isBountiful_of_cappedLift_full {A : Finset α} {N : ℕ} (hle : ∀ B ∈ D.faces, B ⊆ A)
    (hcard : ∀ B ∈ D.faces, B ≠ A → #B ≤ N)
    (hproper : ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ h : X ≤ Y, Y.1 ≠ A ∨ Y.2 < N → R.CappedLift h)
    (hfull : ∀ (B : Finset α) (hB : B ∈ D.faces), B ≠ A → #B = N →
      R.CappedLift (X := (B, N)) (Y := (A, N)) ⟨hle B hB, le_rfl⟩) : R.IsBountiful := by
  refine isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  have hY' : (Y.1, X.2) ∈ D.gradedFaces := ⟨hY.1, hX.2.1, hX.2.2.trans (card_le_card h.1)⟩
  by_cases hlow : Y.1 ≠ A ∨ X.2 < N
  · exact hproper hX hY' ⟨h.1, le_rfl⟩ hlow
  push Not at hlow
  obtain ⟨hYA, hNX⟩ := hlow
  obtain ⟨B, j⟩ := X
  obtain ⟨C, k⟩ := Y
  simp only at hYA hNX h ⊢
  subst hYA
  by_cases hBA : B = C
  · subst hBA
    exact cappedLift_of_fst_eq _ rfl
  have hB := hcard B hX.1 hBA
  obtain rfl : j = N := le_antisymm (hX.2.2.trans hB) hNX
  exact hfull B hX.1 hBA (le_antisymm hB hX.2.2)

end VaughtConjecture.CellScheme.Rows
