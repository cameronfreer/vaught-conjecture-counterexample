/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Realization.Partial

/-!
# No model at a successor stage, and a consistent covering realization that is not a model

Roadmap, Layer 2 (the four unchanged extension families); semantic contract, item 5.

**No model at a successor stage.**  At the successor stage `1` no stage type on `n + 1` points has
a label in the block `[0, ω)` (`uniformityFamily_zero_eq_empty`): such a label would be the ordinal
`0`, which is self-visible only at grade `0`, while every cell has positive grade.  So no
realization at stage `1` realizes a member of this family over any tuple
(`not_realizesOver_uniformityFamily_zero`), although `0` is a limit-or-zero ordinal below the stage
`1`.  The uniformity clause of `Realization.IsModel` at `γ = 0` asks for such a member over every
occurrence, so no realization at stage `1` with an occurrence is a model; since every model has an
occurrence, there is no model at stage `1` (`not_isModel_of_stage_one`).  The source defines
models only at limit stages [Kni26, Definition 3.2.1].

**Consistency and covering are not modelhood.**  The face realization of a stage type `q` on `k`
points (`StageType.faceRealization`) is the realization on `Fin k` whose evaluation is the face map
of `q`.  It is exactly consistent and covering, by the composition and identity laws of face maps,
and its types are legal when `q` is.  The face realization of the face `pointOfPair` of the legal
two-point stage type `pair` along the initial segment lives on the nonempty carrier `Fin 1` and
satisfies every law of a model except existential closure.  It is not a model
(`not_isModel_faceRealization_pointOfPair`): `pair` is a coface of `pointOfPair` with its own
scheme, so the saturation instance of that scheme is nonempty, but no tuple on two points of
`Fin 1` exists.

## References

Models are [Kni26, Definition 3.2.1], for R. W. Knight, *A counterexample to Vaught's Conjecture
using generalised Stone spaces* (draft, 20 February 2026).
-/

namespace VaughtConjecture.Realization

open Finset Label StageType

/-! ### No model at a successor stage -/

/-- At the successor stage `1` no stage type on `n + 1` points has a label in `[0, ω)`. -/
private theorem uniformityFamily_zero_eq_empty (n : ℕ) :
    (uniformityFamily 0 : Set (StageType.{0} 1 (n + 1))) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun q ⟨d, h0, h1⟩ ↦ ?_
  have hsv := q.isLawful.orderly d
  have hpos := q.isWellFormed.isWellFormed.grade_pos d
  have hat := q.atStage d
  induction h : q.label d using recBotCoeTop with
  | bot => rw [h] at h0; exact absurd h0 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe o =>
    rw [h] at hat hsv
    obtain rfl : o = 0 := Order.lt_one_iff.mp (atStage_coe.mp hat)
    rw [isSelfVisible_coe, Ordinal.zero_mod] at hsv
    exact hpos.ne' (by exact_mod_cast nonpos_iff_eq_zero.mp hsv)
  | top => rw [h] at h1; exact absurd h1 (not_lt.mpr le_top)

/-- No realization at stage `1` realizes a label in `[0, ω)` over any tuple. -/
private theorem not_realizesOver_uniformityFamily_zero {M : Type} (R : Realization.{0, 0} 1 M)
    {n : ℕ} (t : Fin n ↪ M) : ¬ R.RealizesOver t (uniformityFamily 0) := by
  rintro ⟨-, -, q, hq, -⟩
  rw [uniformityFamily_zero_eq_empty] at hq
  exact hq

/-- **No model at stage `1`**: over an occurrence of a model, the uniformity clause at `γ = 0` would
realize a label in `[0, ω)`. -/
private theorem not_isModel_of_stage_one {M : Type} (R : Realization.{0, 0} 1 M) : ¬ R.IsModel :=
  fun h ↦ h.nonempty_occurrence.elim fun x ↦ not_realizesOver_uniformityFamily_zero R x.tuple
    (h.uniformity x 0 Ordinal.isSuccPrelimit_zero zero_lt_one)

/-! ### A legal stage type on two points -/

/-- The cell scheme on two points with one cell for each graded face of the interval plan: the
cells `({0}, 1)`, `({1}, 1)`, `({0, 1}, 1)`, and `({0, 1}, 2)`. -/
private def pairCells : CellScheme (Fin 4) (Fin 2) :=
  ⟨univ, Geometry.intervalPlan univ, ![{0}, {1}, univ, univ], ![1, 1, 1, 2]⟩

/-- The stage type at stage `0` on two points with the cells `pairCells`, the bottom rows, and the
bottom label. -/
private def pair : StageType.{0} 0 2 where
  card := 4
  toCellScheme := pairCells
  rows := CellScheme.Rows.bot _
  label _ := ⊥
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    fin_cases d <;> simp [pairCells, CellScheme.gradedIndex, Geometry.mem_intervalPlan]⟩⟩
  isCoded _ _ := WithBot.bot_lt_coe _
  isLawful := CellScheme.Rows.isLawful_const_bot
  atStage _ := atStage_bot

/-- Every graded face of `pairCells` is the graded index of a cell. -/
private theorem isComplete_pairCells : pairCells.IsComplete := by
  rintro ⟨C, j⟩ ⟨hC, hpos, hle⟩
  have hj : j ≤ 2 := hle.trans (card_le_univ C)
  simp only at hpos hle
  interval_cases j <;> revert C <;> decide

/-- `pair` is legal: the bottom rows are consistent and bountiful, and `pairCells` is complete. -/
private theorem isLegal_pair : pair.IsLegal :=
  isLegal_iff.mpr ⟨CellScheme.Rows.isConsistent_bot, CellScheme.Rows.isBountiful_bot,
    isComplete_pairCells⟩

/-- The initial segment `{0}` is a closed face of `pair`. -/
private theorem castSucc_mem_faces_pair :
    univ.map Fin.castSuccEmb ∈ pair.toCellScheme.faces := by
  decide

/-- The face of `pair` along the initial segment: a legal stage type on one point. -/
private noncomputable def pointOfPair : StageType.{0} 0 1 :=
  pair.comap Fin.castSuccEmb castSucc_mem_faces_pair

/-- `pair` is a coface of its face `pointOfPair`. -/
private theorem pair_mem_cofaces : pair ∈ pointOfPair.cofaces :=
  ⟨isLegal_pair, restrictFace_of_mem _ _ castSucc_mem_faces_pair⟩

/-- The occurrence of `pointOfPair` in its face realization: the identity tuple. -/
private noncomputable def pointOccurrence : pointOfPair.faceRealization.Occurrence :=
  ⟨1, Function.Embedding.refl _, pointOfPair, restrictFace_refl _⟩

/-- The face realization of `pointOfPair` satisfies every law of a model except existential
closure. -/
private theorem faceRealization_pointOfPair_laws :
    Nonempty (Fin 1) ∧ (∀ ⦃n : ℕ⦄ (t : Fin n ↪ Fin 1) (p : StageType.{0} 0 n),
      pointOfPair.faceRealization.eval t = some p → p.IsLegal) ∧
      pointOfPair.faceRealization.IsConsistent ∧ pointOfPair.faceRealization.IsCovering :=
  ⟨inferInstance, hasLegalTypes_faceRealization (isLegal_pair.comap _ castSucc_mem_faces_pair),
    isConsistent_faceRealization, isCovering_faceRealization⟩

/-- **Consistency and covering are not modelhood**: the face realization of `pointOfPair` is not a
model.  Its saturation instance for the scheme of `pair` is nonempty, but a realizing tuple would
embed two points into `Fin 1`. -/
private theorem not_isModel_faceRealization_pointOfPair :
    ¬ pointOfPair.faceRealization.IsModel := fun h ↦ by
  obtain ⟨u, -⟩ := h.saturation pointOccurrence pair.toScheme ⟨pair, pair_mem_cofaces, rfl⟩
  have h2 := Fintype.card_le_of_embedding u
  rw [Fintype.card_fin, Fintype.card_fin] at h2
  simp [pointOccurrence] at h2

end VaughtConjecture.Realization
