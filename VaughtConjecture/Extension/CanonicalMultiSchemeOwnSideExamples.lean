/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalMultiSchemeOwnSide
import VaughtConjecture.Extension.CanonicalMultiSchemeExamples
import VaughtConjecture.Extension.ThinCompletionMirrorExamples

/-!
# Own-side copy rows at the compiled seeds, and the orientations forced on the copies

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: the
own-side rows of the canonical multi-layer scheme at the compiled seeds, and the orientations every
step of the scheme has at four of them); semantic contract, items 2–4.

Write `d₀` for the cell at `({0}, 1)` (on the common face), `d₃` for the cell at `({3}, 1)` (on
`C`) and `d₄` for the cell at `({4}, 1)` (on `D`).  Each seed below has a forcing (`Seed.ForcesTop`)
from one coatom `B`, through a parameter of the common face coupled to the parameter of grade `1` of
the other coatom.  The prescription is `⊤` at the original of each copy listed in the table below:
at `(B, 2)` and `(B, 3)` for `seedL`, `seedLM` and the seeds of coatom types `T5`, `T5`; at `(D, 2)`
only for the forcing of `seedHG` from `D` (the prescription `labD 2 ⊤ ⊥` is `⊥` at `(D, 3)`); and
at `(C, 3)` only for the forcing of `seedHG` from `C` (the prescription `labC 2 2 ⊤` is `2` at
`(C, 2)`).  So the listed copies carry `⊤` in the lift of the prescription, and every step of the
canonical multi-layer scheme, for every copy rows `R`, reads them with the forced orientation
(`Seed.MultiLayerStep.copyRows_lt_of_forcesTop`).

**The orientations forced on the copies** (compiled, for every copy rows of a step):

| seed | forcing from | prescription | copies | forced reading |
|---|---|---|---|---|
| `seedHG` | `D` | `A_D = 2`, `H = ⊤`, `G = ⊥` | `(D, 2)` | `d₄` below `d₃` |
| `seedHG` | `C` | `A_C = H = 2`, `G = ⊤` | `(C, 3)` | `d₃` below `d₄` |
| `seedL` | `C` | `A_C = 1`, `F_C = G = ⊤` | `(C, 2)`, `(C, 3)` | `d₃` below `d₄` |
| `seedLM` | `D` | `A_D = 1`, `F_D = G = ⊤` | `(D, 2)`, `(D, 3)` | `d₄` below `d₃` |
| `T5`, `T5` (`seed5`) | `D` | all parameters `⊤` | `(D, 2)`, `(D, 3)` | `d₀` below `d₃` |

(`Seed.copyRows_lt_two_of_TH_TG`, `Seed.copyRows_lt_three_of_TH_TG`, `Seed.copyRows_lt_of_TL_T5`,
`Seed.copyRows_lt_of_T5_TL`, `Seed.copyRows_lt_of_T5_T5`.)  In each row the copy reads a cell of
its own coatom below the cell of the other: the copy of `(D, 2)` at `seedHG` must be oriented toward
`C`, the copy of `(C, 3)` toward `D`.  The rows `CanonicalHG.rowsHG` meet these orientations (both
copies of the grade `2` read `A_D` at `1` below `A_C` at `ω + 2`, both of the grade `3` read `A_C`
at `2` below `A_D` at `ω + 3`), and so do the oriented rows of `seedL` and `seedLM` (toward `D`
and toward `C`).

**The own-side rows fail at `seedHG`, `seedL` and `seedLM`** (`Seed.not_ownSideStep_of_TH_TG`,
`Seed.not_ownSideStep_of_TL_T5`, `Seed.not_ownSideStep_of_T5_TL`, and `…_seedHG`, `…_seedL`,
`…_seedLM`): their copy of the forcing coatom reads its own cell above the other's.  This refutes
the own-side rows at these seeds, not the canonical multi-layer scheme and not a completion: the
scheme has a step at each of them with other copy rows
(`Seed.hasCanonicalMultiStep_seed4_seed5_seedL_seedLM_seedLL_seedHG`).

**Comparison with `rowsHG` at the grade `1`** (`OrderedLayer.ownSideRows_zero_lt_of_TH`,
`OrderedLayer.CanonicalHG.rowsHG_zero_lt`): at `seedHG` both read `d₄` below `d₃` at the copy of
`(C, 1)` (own side above), and at the grade `2` they differ at the copy of `(D, 2)`, where `rowsHG`
has the forced orientation and the own-side rows the opposite.

**The other three seeds.**  At `seed5` the forcings of `T5` (`Seed.forcesTop_of_TL_T5`,
`Seed.forcesTop_of_T5_TL`) apply, and they do constrain the copies: every step reads the dead common
cell `d₀` below `d₃` at the copies of `(D, 2)` and `(D, 3)` (`Seed.copyRows_lt_of_T5_T5`, last row
of the table).  But they apply only with `P d₁ = ⊥` at the cells `d₁` of grade `1` of the forcing
coatom with `P d₁ ≠ ⊤` (argued, not formalized: they prescribe `G = ⊤`, and a lawful prescription
at `T5` has `G ≤ A`), so `Seed.not_ownSideStep_of_forcesTop`, which needs `P d₁ ∉ {⊥, ⊤}`, does not
apply.  The own-side rows read `d₀` at `⊥`, as the rows of `T5` read their dead cells, and so meet
this orientation (argued, not formalized).  At `seed4` and `seedLL` there is no forcing of this
kind (argued, not formalized: the common face of `seed4` carries no parameter; `TL` couples nothing
to `⊤`).  Whether the own-side rows give these three seeds a step is not decided here.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme OrderedLayer

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- A cell with a given graded index lies below a pair when the graded index does. -/
private theorem mem_below_of_gradedIndex {d : Fin I.amalgam.card} {X Y : Finset (Fin 5) × ℕ}
    (hd : I.amalgam.toCellScheme.gradedIndex d = X) (hXY : X ≤ Y) :
    d ∈ I.amalgam.toCellScheme.below Y := by
  rw [CellScheme.mem_below, hd]; exact hXY

/-- A cell with a given graded index has its grade. -/
private theorem grade_eq {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ}
    (hd : I.amalgam.toCellScheme.gradedIndex d = X) : I.amalgam.toCellScheme.grade d = X.2 :=
  congrArg Prod.snd hd

/-- A cell with a given graded index does not lie below a pair when the graded index does not. -/
private theorem not_mem_below_of_gradedIndex {d : Fin I.amalgam.card} {X Y : Finset (Fin 5) × ℕ}
    (hd : I.amalgam.toCellScheme.gradedIndex d = X) (hXY : ¬ X ≤ Y) :
    d ∉ I.amalgam.toCellScheme.below Y := by
  rw [CellScheme.mem_below, hd]; exact hXY

/-! ### The crossed-coupling seed -/

section HG

open CrossedCouplingCounterexample (TH TG seedHG labC labD w2 isLawfulBelow_labC
  isLawfulBelow_labD forcesTop_left forcesTop_right exists_cells)

variable (hIL : I.left = TH α) (hIR : I.right = TG α)
include hIL hIR

/-- **The copy of `(D, 2)` is oriented toward `C`** in every step of the canonical multi-layer
scheme of a seed whose coatom types are `TH` and `TG`: it reads `({4}, 1)` strictly below
`({3}, 1)`.  The prescription `A_D = 2`, `H = ⊤`, `G = ⊥` below `(D, 3)` forces `⊤` at
`({3}, 1)` (the coupling `H ≤ A_C` of `TH`) and is `⊤` at `(D, 2)`. -/
theorem copyRows_lt_two_of_TH_TG {R : CopyRows I}
    (h : I.MultiLayerStep canonicalMult (canonicalRows I R)) {d₃ d₄ : Fin I.amalgam.card}
    (hd₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (hd₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1)) :
    R 1 1 d₄ < R 1 1 d₃ := by
  refine h.copyRows_lt_of_forcesTop (j := 1) (i := 1) (k := 3) (by decide) (by decide)
    (P := fun d ↦ labD w2 ⊤ ⊥ (I.amalgam.toCellScheme.gradedIndex d)) ?_
    (mem_below_of_gradedIndex hd₄ (by decide)) (mem_below_of_gradedIndex hd₃ (by decide))
    ((grade_eq hd₃).trans (grade_eq hd₄).symm).ge ?_ ?_ ?_
  · exact isLawfulBelow_labD hIR
  · rw [hd₄]; exact gridPoint_ne_top 2 0
  · rw [gradedIndex_copyOrig]; rfl
  · exact forcesTop_right hIL hd₃

/-- **The copy of `(C, 3)` is oriented toward `D`** in every step of the canonical multi-layer
scheme of a seed whose coatom types are `TH` and `TG`: it reads `({3}, 1)` strictly below
`({4}, 1)`.  The prescription `A_C = H = 2`, `G = ⊤` below `(C, 3)` forces `⊤` at `({4}, 1)` (the
coupling `G ≤ A_D` of `TG`) and is `⊤` at `(C, 3)`. -/
theorem copyRows_lt_three_of_TH_TG {R : CopyRows I}
    (h : I.MultiLayerStep canonicalMult (canonicalRows I R)) {d₃ d₄ : Fin I.amalgam.card}
    (hd₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (hd₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1)) :
    R 2 0 d₃ < R 2 0 d₄ := by
  refine h.copyRows_lt_of_forcesTop (j := 2) (i := 0) (k := 3) (by decide) (by decide)
    (P := fun d ↦ labC w2 w2 ⊤ (I.amalgam.toCellScheme.gradedIndex d)) ?_
    (mem_below_of_gradedIndex hd₃ (by decide)) (mem_below_of_gradedIndex hd₄ (by decide))
    ((grade_eq hd₃).trans (grade_eq hd₄).symm).le ?_ ?_ ?_
  · exact isLawfulBelow_labC hIL
  · rw [hd₃]; exact gridPoint_ne_top 2 0
  · rw [gradedIndex_copyOrig]; rfl
  · exact forcesTop_left hIR hd₄

/-- **The own-side rows give no step** to a seed whose coatom types are `TH` and `TG`: the
own-side copy of `(D, 2)` reads `({4}, 1)` above `({3}, 1)`, against the orientation forced on
it. -/
theorem not_ownSideStep_of_TH_TG : ¬ I.OwnSideStep := by
  obtain ⟨d₃, d₄, hd₃, hd₄⟩ := exists_cells hIL hIR
  refine not_ownSideStep_of_forcesTop (j := 1) (i := 1) (k := 3) (by decide) (by decide)
    (P := fun d ↦ labD w2 ⊤ ⊥ (I.amalgam.toCellScheme.gradedIndex d)) (isLawfulBelow_labD hIR)
    (mem_below_of_gradedIndex hd₄ (by decide)) (mem_below_of_gradedIndex hd₃ (by decide))
    (not_mem_below_of_gradedIndex hd₃ (by decide))
    ((grade_eq hd₃).trans (grade_eq hd₄).symm).ge ?_ ?_ ?_ (forcesTop_right hIL hd₃)
  · rw [hd₄]; exact gridPoint_ne_top 2 0
  · rw [hd₄]; exact WithBot.coe_ne_bot
  · rw [gradedIndex_copyOrig]; rfl

end HG

/-- **The crossed-coupling seed has no own-side step.** -/
theorem not_ownSideStep_seedHG : ¬ (CrossedCouplingCounterexample.seedHG α).OwnSideStep :=
  not_ownSideStep_of_TH_TG rfl rfl

/-! ### The asymmetric seed and its mirror -/

section L

open TwoFaceLiftExistsCounterexample (TL VisibilityReplaceFixedOfLT exists_cell_TL seedL)
open CaseSplitCounterexample (T5 tripleLabelling)

/-- The finite part `1` is fixed by visibility replacement below the cap `⊤`. -/
private theorem visibilityReplaceFixedOfLT_v1 :
    VisibilityReplaceFixedOfLT (TwoFaceLiftCounterexample.v1 : Label.{u}) ⊤ := fun _ ↦ by
  rw [TwoFaceLiftCounterexample.v1_eq, Label.visibilityReplace_natCast]; simp

/-- The two cells `({3}, 1)` and `({4}, 1)` of a seed whose coatom types are `TL` and `T5`. -/
private theorem exists_cells_TL_T5 (hIL : I.left = TL α) (hIR : I.right = T5 α) :
    ∃ d₃ d₄ : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1) ∧
        I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1) := by
  obtain ⟨d₃, h₃⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₄, h₄⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
  exact ⟨d₃, d₄, h₃.trans (by decide +kernel), h₄.trans (by decide +kernel)⟩

/-- The two cells `({3}, 1)` and `({4}, 1)` of a seed whose coatom types are `T5` and `TL`. -/
private theorem exists_cells_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α) :
    ∃ d₃ d₄ : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1) ∧
        I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1) := by
  obtain ⟨d₃, h₃⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 3
  obtain ⟨d₄, h₄⟩ := exists_cell_TL (hIR ▸ I.restrictFace_right) 3
  exact ⟨d₃, d₄, h₃.trans (by decide +kernel), h₄.trans (by decide +kernel)⟩

/-- The prescription `(A_C, F_C, G) = (1, ⊤, ⊤)` of `TL` is lawful below `(C, 3)`. -/
private theorem isLawfulBelow_left_TL_T5 (hIL : I.left = TL α) (hIR : I.right = T5 α) :
    I.amalgam.rows.IsLawfulBelow (copyCoatom 0, 3) fun d ↦
      tripleLabelling TwoFaceLiftCounterexample.v1 ⊤ ⊤ ⊤ ⊤
        (I.amalgam.toCellScheme.gradedIndex d) :=
  (TwoFaceLiftExistsCounterexample.isLawfulBelow_tripleLabelling hIL hIR
    (isSelfVisible_gridPoint 1 0) (isSelfVisible_top 2) (isSelfVisible_top 1)
    (isSelfVisible_top 2) (isSelfVisible_top 3) le_rfl visibilityReplaceFixedOfLT_v1 le_rfl
    le_rfl).1

/-- The prescription `(A_D, F_D, G) = (1, ⊤, ⊤)` of `TL` is lawful below `(D, 3)`. -/
private theorem isLawfulBelow_right_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α) :
    I.amalgam.rows.IsLawfulBelow (copyCoatom 1, 3) fun d ↦
      tripleLabelling ⊤ ⊤ TwoFaceLiftCounterexample.v1 ⊤ ⊤
        (I.amalgam.toCellScheme.gradedIndex d) :=
  (OrderedLayer.Mirror.isLawfulBelow_tripleLabelling hIL hIR (isSelfVisible_top 1)
    (isSelfVisible_top 2) (isSelfVisible_gridPoint 1 0) (isSelfVisible_top 2)
    (isSelfVisible_top 3) le_rfl le_rfl le_rfl visibilityReplaceFixedOfLT_v1).2

/-- **The copies of `(C, 2)` and `(C, 3)` are oriented toward `D`** in every step of the canonical
multi-layer scheme of a seed whose coatom types are `TL` and `T5`: they read `({3}, 1)` strictly
below `({4}, 1)`.  The prescription `(A_C, F_C, G) = (1, ⊤, ⊤)` below `(C, 3)` forces `⊤` at
`({4}, 1)` (the coupling `G ≤ A_D` of `T5`) and is `⊤` at `(C, 2)` and `(C, 3)`. -/
theorem copyRows_lt_of_TL_T5 (hIL : I.left = TL α) (hIR : I.right = T5 α) {R : CopyRows I}
    (h : I.MultiLayerStep canonicalMult (canonicalRows I R)) {d₃ d₄ : Fin I.amalgam.card}
    (hd₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (hd₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1))
    (j : Fin 4) (hj1 : 1 ≤ (j : ℕ)) (hj2 : (j : ℕ) ≤ 2) : R j 0 d₃ < R j 0 d₄ := by
  obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
  all_goals
    refine h.copyRows_lt_of_forcesTop (i := 0) (k := 3) (by decide) (by decide)
      (isLawfulBelow_left_TL_T5 hIL hIR)
      (mem_below_of_gradedIndex hd₃ (by decide)) (mem_below_of_gradedIndex hd₄ (by decide))
      ((grade_eq hd₃).trans (grade_eq hd₄).symm).le ?_ ?_
      (Seed.forcesTop_of_TL_T5 hIR _ hd₄)
  all_goals first
    | (rw [hd₃]; exact gridPoint_ne_top 1 0)
    | (rw [gradedIndex_copyOrig]; rfl)

/-- **The copies of `(D, 2)` and `(D, 3)` are oriented toward `C`** in every step of the canonical
multi-layer scheme of a seed whose coatom types are `T5` and `TL`: they read `({4}, 1)` strictly
below `({3}, 1)`. -/
theorem copyRows_lt_of_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α) {R : CopyRows I}
    (h : I.MultiLayerStep canonicalMult (canonicalRows I R)) {d₃ d₄ : Fin I.amalgam.card}
    (hd₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (hd₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1))
    (j : Fin 4) (hj1 : 1 ≤ (j : ℕ)) (hj2 : (j : ℕ) ≤ 2) : R j 1 d₄ < R j 1 d₃ := by
  obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
  all_goals
    refine h.copyRows_lt_of_forcesTop (i := 1) (k := 3) (by decide) (by decide)
      (isLawfulBelow_right_T5_TL hIL hIR)
      (mem_below_of_gradedIndex hd₄ (by decide)) (mem_below_of_gradedIndex hd₃ (by decide))
      ((grade_eq hd₃).trans (grade_eq hd₄).symm).ge ?_ ?_
      (Seed.forcesTop_of_T5_TL hIL _ hd₃)
  all_goals first
    | (rw [hd₄]; exact gridPoint_ne_top 1 0)
    | (rw [gradedIndex_copyOrig]; rfl)

/-- **The copies of `(D, 2)` and `(D, 3)` read the dead common cell below `({3}, 1)`** in every step
of the canonical multi-layer scheme of a seed whose coatom types are `T5` and `T5` (`seed5`): the
prescription with every parameter `⊤` below `(D, 3)` forces `⊤` at `({3}, 1)` (the coupling
`G ≤ A_C` of `T5`), is `⊤` at `(D, 2)` and `(D, 3)`, and is `⊥` at `({0}, 1)`. -/
theorem copyRows_lt_of_T5_T5 (hIL : I.left = T5 α) (hIR : I.right = T5 α) {R : CopyRows I}
    (h : I.MultiLayerStep canonicalMult (canonicalRows I R)) {d₀ d₃ : Fin I.amalgam.card}
    (hd₀ : I.amalgam.toCellScheme.gradedIndex d₀ = (({0} : Finset (Fin 5)), 1))
    (hd₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (j : Fin 4) (hj1 : 1 ≤ (j : ℕ)) (hj2 : (j : ℕ) ≤ 2) : R j 1 d₀ < R j 1 d₃ := by
  have hP : I.amalgam.rows.IsLawfulBelow (copyCoatom 1, 3) fun d ↦
      tripleLabelling ⊤ ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) :=
    (CaseSplitCounterexample.isLawfulBelow_tripleLabelling hIL hIR (isSelfVisible_top 1)
      (isSelfVisible_top 2) (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 3)
      le_rfl le_rfl le_rfl le_rfl).2
  obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
  all_goals
    refine h.copyRows_lt_of_forcesTop (i := 1) (k := 3) (by decide) (by decide) hP
      (mem_below_of_gradedIndex hd₀ (by decide)) (mem_below_of_gradedIndex hd₃ (by decide))
      ((grade_eq hd₀).trans (grade_eq hd₃).symm).le ?_ ?_
      (Seed.forcesTop_of_T5_TL hIL _ hd₃)
  all_goals first
    | (rw [hd₀]; exact bot_ne_top)
    | (rw [gradedIndex_copyOrig]; rfl)

/-- **The own-side rows give no step** to a seed whose coatom types are `TL` and `T5`: the own-side
copy of `(C, 2)` reads `({3}, 1)` above `({4}, 1)`, against the orientation forced on it. -/
theorem not_ownSideStep_of_TL_T5 (hIL : I.left = TL α) (hIR : I.right = T5 α) :
    ¬ I.OwnSideStep := by
  obtain ⟨d₃, d₄, hd₃, hd₄⟩ := exists_cells_TL_T5 hIL hIR
  refine not_ownSideStep_of_forcesTop (j := 1) (i := 0) (k := 3) (by decide) (by decide)
    (isLawfulBelow_left_TL_T5 hIL hIR)
    (mem_below_of_gradedIndex hd₃ (by decide)) (mem_below_of_gradedIndex hd₄ (by decide))
    (not_mem_below_of_gradedIndex hd₄ (by decide))
    ((grade_eq hd₃).trans (grade_eq hd₄).symm).le ?_ ?_ ?_
    (Seed.forcesTop_of_TL_T5 hIR _ hd₄)
  · rw [hd₃]; exact gridPoint_ne_top 1 0
  · rw [hd₃]; exact WithBot.coe_ne_bot
  · rw [gradedIndex_copyOrig]; rfl

/-- **The own-side rows give no step** to a seed whose coatom types are `T5` and `TL`: the own-side
copy of `(D, 2)` reads `({4}, 1)` above `({3}, 1)`, against the orientation forced on it. -/
theorem not_ownSideStep_of_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α) :
    ¬ I.OwnSideStep := by
  obtain ⟨d₃, d₄, hd₃, hd₄⟩ := exists_cells_T5_TL hIL hIR
  refine not_ownSideStep_of_forcesTop (j := 1) (i := 1) (k := 3) (by decide) (by decide)
    (isLawfulBelow_right_T5_TL hIL hIR)
    (mem_below_of_gradedIndex hd₄ (by decide)) (mem_below_of_gradedIndex hd₃ (by decide))
    (not_mem_below_of_gradedIndex hd₃ (by decide))
    ((grade_eq hd₃).trans (grade_eq hd₄).symm).ge ?_ ?_ ?_
    (Seed.forcesTop_of_T5_TL hIL _ hd₃)
  · rw [hd₄]; exact gridPoint_ne_top 1 0
  · rw [hd₄]; exact WithBot.coe_ne_bot
  · rw [gradedIndex_copyOrig]; rfl

/-- **The asymmetric seed has no own-side step.** -/
theorem not_ownSideStep_seedL : ¬ (seedL α).OwnSideStep :=
  not_ownSideStep_of_TL_T5 rfl rfl

/-- **The mirror of the asymmetric seed has no own-side step.** -/
theorem not_ownSideStep_seedLM : ¬ (seedLM α).OwnSideStep :=
  not_ownSideStep_of_T5_TL rfl rfl

end L

end Seed

/-! ### Comparison with the rows of the crossed-coupling seed at the grade `1` -/

namespace OrderedLayer

open CrossedCouplingCounterexample (TH TG labC w2 isLawfulBelow_labC)
open TwoFaceLiftCounterexample (v1 v2)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **At the grade `1` the own-side rows read the own side above**: at a seed whose first coatom
type is `TH`, the own-side copy of `(C, 1)` reads `({4}, 1)` strictly below `({3}, 1)`. -/
theorem ownSideRows_zero_lt_of_TH (hIL : I.left = TH α) {d₃ d₄ : Fin I.amalgam.card}
    (hd₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (hd₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1)) :
    ownSideRows I 0 0 d₄ < ownSideRows I 0 0 d₃ := by
  have hmem (d : Fin I.amalgam.card) {X Y : Finset (Fin 5) × ℕ}
      (hd : I.amalgam.toCellScheme.gradedIndex d = X) (hXY : X ≤ Y) :
      d ∈ I.amalgam.toCellScheme.below Y := by
    rw [CellScheme.mem_below, hd]; exact hXY
  refine ownSideRows_lt (hmem d₃ hd₃ (by decide)) (by rw [CellScheme.mem_below, hd₄]; decide)
    (row_ne_bot_of_isLawfulBelow (X := (coatomC, 3))
      (P := fun d ↦ labC w2 w2 ⊤ (I.amalgam.toCellScheme.gradedIndex d)) (isLawfulBelow_labC hIL)
      (hmem _ (gradedIndex_copyOrig I 0 0) (by decide)) ?_)
  rw [hd₃, gradedIndex_copyOrig]
  exact ne_of_gt (lt_min (WithBot.bot_lt_coe _) (WithBot.bot_lt_coe _))

/-- **At the grade `1` the rows of the crossed-coupling seed read the own side above**: the copy of
`(C, 1)` reads `({4}, 1)` at `1`, strictly below `({3}, 1)` at `ω + 2`. -/
theorem CanonicalHG.rowsHG_zero_lt {d₃ d₄ : Fin I.amalgam.card}
    (hd₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (hd₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1)) :
    CanonicalHG.rowsHG I 0 0 d₄ < CanonicalHG.rowsHG I 0 0 d₃ := by
  have hrow : CanonicalHG.rowsHG I 0 0 = CanonicalHG.kindVal I v2 v1 ⊥ ⊥ ⊥ := rfl
  rw [hrow, CanonicalHG.kindVal, CanonicalHG.kindVal, hd₃, hd₄,
    show CrossedCouplingCounterexample.kindOld (({3} : Finset (Fin 5)), 1) = .ac by decide,
    show CrossedCouplingCounterexample.kindOld (({4} : Finset (Fin 5)), 1) = .ad by decide]
  rw [TwoFaceLiftCounterexample.v1_eq]
  refine WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ?_)
  simp only [Nat.cast_one, Nat.cast_ofNat, mul_one]
  exact Ordinal.one_lt_omega0.trans_le le_self_add

end OrderedLayer

end VaughtConjecture
