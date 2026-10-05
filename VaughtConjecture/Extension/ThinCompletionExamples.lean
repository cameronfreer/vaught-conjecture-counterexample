/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ThinCompletion

/-!
# The thin completion of the asymmetric seed: the coatom extension, and what it imposes

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the recursion on the grade; here the consequences of
the thin completion of `seedL`, `VaughtConjecture.Extension.ThinCompletion`); semantic contract,
items 2–4.

* **The coatom extension of `TL` and `T5` with apex** (`exists_coatomExtension_seedL`): at every
  stage `α`, a legal stage type on five points whose faces along the two coatoms are literally
  `TL` and `T5`, labels included, with a cell of full scope and full grade carrying the largest
  label.  It is the completion of the thin completion with the apex added
  (`CompletionBelowFullGrade.exists_coatomExtension_of_atStage`): the labels of the thin completion
  are `⊥` and `⊤`, which lie at every stage, so no truncation and no hypothesis on the stage is
  needed.  So `seedL` is not a counterexample to `StageType.HasApexCoatomExtensions` at `m = 3`;
  the property itself is still to be proved in general.
* **The separating cell of the thin completion** (`row_newCell_two_lt`): the row of its only cell
  at `(univ, 2)` reads the cell `({3}, 1)` at `1`, strictly below the cell `({4}, 1)`, read at
  `ω + 1`.  So the thin completion meets the necessary condition of
  `VaughtConjecture.Extension.SeparatingCell` (`exists_separating_cell_seedL`), which the tower of
  the step does not meet.
* **The lawful labellings of the thin completion are not all labellings of the amalgam**
  (`le_and_eq_of_isLawfulBelow_three`, `exists_not_restriction`).  Every labelling lawful below
  `(univ, 3)` has `A_C ≤ A_D` (its label at `({3}, 1)` is at most its label at `({4}, 1)`) and
  `F_C = F_D` (equal labels at `(C, 2)` and `(D, 2)`).  The labelling of the amalgam with
  `A_C = ω + 1`, `A_D = 1` and `⊥` elsewhere is lawful below both coatoms at the grade `3`, and it
  is the restriction of no labelling of the thin completion lawful below `(univ, 3)`.  This does
  not affect bountifulness: no pair of graded faces below a coatom sees both coatoms, and a lift
  into a pair of full scope starts from one coatom.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ThinCompletionExamples

open Finset Label CellScheme ThinCompletion
open TwoFaceLiftExistsCounterexample

/-- **The coatom extension of `TL` and `T5` with apex**, at every stage: the thin completion of
`seedL` with the apex added.  Its labels are `⊥` and `⊤`, which lie at every stage. -/
theorem exists_coatomExtension_seedL (α : Ordinal.{u}) :
    ∃ t : StageType.{u} α 5, t.IsLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some (TL α) ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t =
        some (CaseSplitCounterexample.T5 α) ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, 5) ∧ ∀ e, t.label e ≤ t.label d :=
  have h (z : Fin (thinScheme (seedL α)).card) :
      AtStage α (thinLabelling (seedL α) ⊥ ⊥ ⊥ ⊥ ⊤ z) := by
    rw [thinLabelling_omega]
    split_ifs
    · exact atStage_top
    · exact atStage_bot
  (thinCompletion (I := seedL α) rfl rfl).exists_coatomExtension_of_atStage fun d ↦ h d

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The cell of the thin completion at `(univ, 2)` separates**: its row reads `({3}, 1)` at `1`,
strictly below `({4}, 1)`, read at `ω + 1`. -/
theorem row_newCell_two_lt {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1))
    (h₁ : oldCell I d₁ ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I 2)))
    (h₂ : oldCell I d₂ ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I 2))) :
    (thinScheme I).rows.row (newCell I 2) ⟨oldCell I d₁, h₁⟩ <
      (thinScheme I).rows.row (newCell I 2) ⟨oldCell I d₂, h₂⟩ := by
  rw [row_newCell (by omega) (by omega), row_newCell (by omega) (by omega)]
  change thinRow 2 (thinKind ((thinScheme I).toCellScheme.gradedIndex (oldCell I d₁))) <
    thinRow 2 (thinKind ((thinScheme I).toCellScheme.gradedIndex (oldCell I d₂)))
  rw [gradedIndex_oldCell, gradedIndex_oldCell, hd₁, hd₂]
  exact gridPoint_lt_gridPoint.mpr (by omega)

variable (hIL : I.left = TL α) (hIR : I.right = CaseSplitCounterexample.T5 α)

include hIL hIR in
/-- **The thin completion imposes `A_C ≤ A_D` and `F_C = F_D`**: every labelling lawful below
`(univ, 3)` is at most its label at `({4}, 1)` at the cell `({3}, 1)`, and has equal labels at the
cells `(C, 2)` and `(D, 2)`. -/
theorem le_and_eq_of_isLawfulBelow_three {w : Fin (thinScheme I).card → Label.{u}}
    (hw : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ w z)
    {d₁ d₂ sC sD : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1))
    (hsC : I.amalgam.toCellScheme.gradedIndex sC = (({0, 1, 2, 3} : Finset (Fin 5)), 2))
    (hsD : I.amalgam.toCellScheme.gradedIndex sD = (({0, 1, 2, 4} : Finset (Fin 5)), 2)) :
    w (oldCell I d₁) ≤ w (oldCell I d₂) ∧ w (oldCell I sC) = w (oldCell I sD) := by
  obtain ⟨AC, AD, F, G, h, hz⟩ := exists_of_isLawfulBelow_three hIL hIR hw
  rw [hz _ (oldCell_mem_below (by rw [hd₁]; decide)),
    hz _ (oldCell_mem_below (by rw [hd₂]; decide)),
    hz _ (oldCell_mem_below (by rw [hsC]; decide)),
    hz _ (oldCell_mem_below (by rw [hsD]; decide)), thinLabelling, thinLabelling,
    thinLabelling, thinLabelling, gradedIndex_oldCell, gradedIndex_oldCell, gradedIndex_oldCell,
    gradedIndex_oldCell, hd₁, hd₂, hsC, hsD]
  exact ⟨h.le_AD, rfl⟩

include hIL hIR in
/-- **A labelling of the amalgam lawful below both coatoms that the thin completion excludes**:
`A_C = ω + 1`, `A_D = 1`, and `⊥` elsewhere, is lawful below both coatoms at the grade `3`, and no
labelling of the thin completion lawful below `(univ, 3)` restricts to it. -/
theorem exists_not_restriction :
    ∃ x : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawfulBelow (coatomC, 3) (fun d ↦ x d) ∧
      I.amalgam.rows.IsLawfulBelow (coatomD, 3) (fun d ↦ x d) ∧
      ∀ w : Fin (thinScheme I).card → Label.{u},
        (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ w z) →
        ¬ ∀ d, w (oldCell I d) = x d := by
  obtain ⟨hC, hD⟩ := isLawfulBelow_tripleLabelling (I := I) hIL hIR
    (AC := gridPoint 1 1) (FC := ⊥) (AD := gridPoint 1 0) (FD := ⊥) (G := ⊥)
    (isSelfVisible_gridPoint 1 1) (isSelfVisible_bot 2) (isSelfVisible_gridPoint 1 0)
    (isSelfVisible_bot 2) (isSelfVisible_bot 3) le_rfl
    (fun h ↦ absurd h (not_lt.mpr bot_le)) bot_le le_rfl
  refine ⟨fun d ↦ CaseSplitCounterexample.tripleLabelling (gridPoint 1 1) ⊥ (gridPoint 1 0) ⊥ ⊥
    (I.amalgam.toCellScheme.gradedIndex d), hC, hD, fun w hw hwx ↦ ?_⟩
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₃, hd₃⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₄, hd₄⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hle := (le_and_eq_of_isLawfulBelow_three hIL hIR hw hd₁ hd₂ hd₃ hd₄).1
  rw [hwx, hwx] at hle
  dsimp only at hle
  rw [hd₁, hd₂] at hle
  exact absurd hle (not_le.mpr (gridPoint_lt_gridPoint.mpr (by omega)))

end VaughtConjecture.ThinCompletionExamples
