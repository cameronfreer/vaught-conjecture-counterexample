/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerTop
import VaughtConjecture.Extension.ThinCompletion

/-!
# The ordered-layer step for the asymmetric seed, and the separating rows it forces

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the ordered-layer step at `m = 3`: the asymmetric
seed `seedL` as an instance, and the constraint on the rows of every ordered-layer step of it);
semantic contract, items 2–4.

* **The asymmetric seed** (`Seed.orderedLayerStep_thinRows`, `Seed.orderedLayerStep_seedL`): for
  every seed whose coatom types are `TL` and `T5`, the layer rows `thinRows`
  (`thinRow k ∘ thinKind`, the ordered rows of `VaughtConjecture.Extension.OrderedRow`) satisfy the
  ordered-layer step.  The layer scheme of these rows is the thin scheme, by definition
  (`layerScheme_thinRows`), and the step is its legality below the full grade
  (`ThinCompletion.isLegalBelowFullGrade_thinScheme`) with the labelling of `⊤` at the cells of
  grade `4` alone, through `Seed.orderedLayerStep_iff`.  The seed also has bottom apexes
  (`Seed.hasBottomApexes_of_TL_T5`).
* **Which separating rows exist** (`Seed.OrderedLayerStep.thinRow_lt_of_TL_T5`): every
  ordered-layer step of a seed whose coatom types are `TL` and `T5`, for any layer rows, reads
  `({3}, 1)` strictly below `({4}, 1)` at each grade `k = 1, 2, 3`: the necessary condition of
  `VaughtConjecture.Extension.SeparatingCell` applied to its completion, whose only cell at
  `(univ, k)` is the new cell.  So the orientation `C` before `D` is forced on the rows of the
  layers `1`, `2`, `3`; at the layer `4` it is not (the top row reads both at `⊥`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme OrderedLayer
open TwoFaceLiftExistsCounterexample

namespace OrderedLayer

/-- The **ordered rows** of the thin completion as layer rows: the row at `(univ, k)` reads the
kind of each graded index by `thinRow k`. -/
noncomputable def thinRows : LayerRows.{u} := fun k X ↦ ThinCompletion.thinRow k
  (ThinCompletion.thinKind X)

/-- **The layer scheme of the ordered rows is the thin scheme**, by definition. -/
theorem layerScheme_thinRows {α : Ordinal.{u}} (I : Seed.{u} α 3) :
    layerScheme I thinRows = ThinCompletion.thinScheme I := rfl

end OrderedLayer

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **A seed whose coatom types are `TL` and `T5` has bottom apexes.** -/
theorem hasBottomApexes_of_TL_T5 (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) : I.HasBottomApexes :=
  hasBottomApexes_of_addApex isLegalBelowFullGrade_SL
    CaseSplitCounterexample.isLegalBelowFullGrade_S (fun _ ↦ rfl) (fun _ ↦ rfl) hIL hIR

/-- **The ordered-layer step of a seed whose coatom types are `TL` and `T5`**, with the ordered
rows of the thin completion. -/
theorem orderedLayerStep_thinRows (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) : I.OrderedLayerStep thinRows :=
  orderedLayerStep_iff.mpr ⟨ThinCompletion.isLegalBelowFullGrade_thinScheme hIL hIR,
    ThinCompletion.thinLabelling I ⊥ ⊥ ⊥ ⊥ ⊤,
    (ThinCompletion.isLawfulBelow_omega hIL hIR (isSelfVisible_top 4)).isLawful
      ThinCompletion.mem_below_univ_four,
    fun d ↦ by
      -- The old cells of the layer scheme are those of the thin scheme.
      change ThinCompletion.thinLabelling I ⊥ ⊥ ⊥ ⊥ ⊤ (ThinCompletion.oldCell I d) = _
      rw [ThinCompletion.thinLabelling_omega, ThinCompletion.grade_oldCell,
        ThinCompletion.amalgam_label hIL hIR]⟩

/-- **The asymmetric seed has an ordered-layer step.** -/
theorem orderedLayerStep_seedL : (seedL α).OrderedLayerStep thinRows :=
  orderedLayerStep_thinRows rfl rfl

/-- **The asymmetric seed has an ordered-layer step**, for some layer rows. -/
theorem hasOrderedLayerStep_seedL : (seedL α).HasOrderedLayerStep :=
  ⟨thinRows, orderedLayerStep_seedL⟩

/-- **Every ordered-layer step of a seed whose coatom types are `TL` and `T5` separates**: for any
layer rows `ρ` with an ordered-layer step, the row at `(univ, k)`, `k = 1, 2, 3`, reads `({3}, 1)`
strictly below `({4}, 1)`.  The completion from the step has only the new cell at `(univ, k)`
(`OrderedLayer.eq_newCell`), and every completion has a separating cell there
(`ThinCompletion.exists_separating_cell_of_completion_of_le_three`). -/
theorem OrderedLayerStep.thinRow_lt_of_TL_T5 (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) {ρ : LayerRows.{u}}
    (h : I.OrderedLayerStep ρ) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    ρ k (({3} : Finset (Fin 5)), 1) < ρ k (({4} : Finset (Fin 5)), 1) := by
  obtain ⟨d₁, d₂, u, hd₁, hd₂, hu, hsep⟩ :=
    ThinCompletion.exists_separating_cell_of_completion_of_le_three hIL hIR h.completion hk1 hk3
  -- The cell `u` of the completion at `(univ, k)` is the new cell of the layer scheme.
  change Fin (layerScheme I ρ).card at u
  change (layerScheme I ρ).toCellScheme.gradedIndex u = _ at hu
  obtain rfl := eq_newCell hk1 (by omega) hu
  have hmem {d : Fin I.amalgam.card} {B : Finset (Fin 5)}
      (hd : I.amalgam.toCellScheme.gradedIndex d = (B, 1)) :
      h.completion.embed d ∈ h.completion.scheme.toCellScheme.below
        (h.completion.scheme.toCellScheme.gradedIndex (newCell I ρ k)) := by
    change oldCell I ρ d ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ k))
    rw [gradedIndex_newCell hk1 (by omega)]
    exact oldCell_mem_below (hd ▸ ⟨subset_univ _, hk1⟩)
  have := hsep (hmem hd₁) (hmem hd₂)
  change (layerScheme I ρ).rows.row (newCell I ρ k) ⟨oldCell I ρ d₁, hmem hd₁⟩ <
    (layerScheme I ρ).rows.row (newCell I ρ k) ⟨oldCell I ρ d₂, hmem hd₂⟩ at this
  rwa [row_newCell hk1 (by omega), row_newCell hk1 (by omega), gradedIndex_oldCell,
    gradedIndex_oldCell, hd₁, hd₂] at this

end Seed

end VaughtConjecture
