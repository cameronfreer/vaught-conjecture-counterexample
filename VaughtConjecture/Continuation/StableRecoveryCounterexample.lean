/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecovery
import VaughtConjecture.Continuation.CandidateCounterexamples

/-!
# Stable recovery schemes for the marker and cap calibration do not exist

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the calibrated data of the recovery statement of (R4)); semantic contract, item 8.

**The statement refuted.**
`StageType.HasStableRecoverySchemes ξ (StageType.MarkerCapCalibration ξ)` asks, for every legal
`T⁺` at `λ_{ξ+1}` with a cell labelled `λ_ξ + i` (a marker) and a cell labelled at least `λ_ξ` and
above `γ` (a cap), every embedding `f` of positive length, every coface `D` of the face of `T⁺`
along `f` and every `γ < λ_{ξ+1}`, for a stable recovery scheme.  It is false at every `ξ`
(`not_hasStableRecoverySchemes_markerCap`), so the hypothesis
`∀ ξ < ω₁, HasStableRecoverySchemes ξ (MarkerCapCalibration ξ)` of
`StableCappedReceiving.of_hasStableRecoverySchemes_markerCap` is false
(`not_forall_hasStableRecoverySchemes_markerCap`).  This refutes that finite hypothesis; it does
not refute (R4) (`StableCappedReceiving`) or output 3.

**The smallest instance.**  The scheme is the five-cell scheme on two points of
`VaughtConjecture.Continuation.CandidateCounterexamples` (`fiveCellScheme`): cell `0` of scope
`{0}`, cell `1` of scope `{1}`, the twins `2` and `3` of scope `univ`, all of grade `1`, and cell
`4` of scope `univ` and grade `2`.  The donors `twinDonor₁` and `twinDonor₂` are its labellings at
`λ_{ξ+1}` `(λ_ξ + 2, ⊥, λ_ξ + 2, λ_ξ + 1, ⊥)` and `(λ_ξ + 2, ⊥, λ_ξ + 1, λ_ξ + 2, ⊥)`, the twins in
both orders.  Both have the same face along the first point, the **root** `twinRoot`: one point and
one cell, labelled `λ_ξ + 2` (`restrictFace_twinDonor₂`).  Take `T⁺` the root itself (`m = k = 1`,
`f` the identity, no private point), `D = twinDonor₁` and `γ = λ_ξ`.  The root's cell is a marker
(`λ_ξ + 2`) and a cap (`λ_ξ + 2 > λ_ξ`), so the marker and cap calibration holds
(`markerCapCalibration_twinRoot`).  Over the whole occurrence a stable recovery scheme is the scheme
of `D` and recovery is rigidity of `D` (`StageType.IsStableRecoveryScheme.eq_toScheme_of_refl`,
`StageType.IsStableRecoveryScheme.label_eq_of_refl`); `twinDonor₂` lies on that scheme with the same
face and differs from `D` at the twin `2`, where `D` is `λ_ξ + 2`, not the formal top.  Twins of one
type of scope `univ` are never separated by the face along the first point: only a cell above both,
whose row reads them differently, separates them.

**What the calibration lacks.**  A stable recovery scheme is obtained from a cell `s` of grade
`N`, the grade of a cap, whose scope contains the scope of the cap, with every new cell of `D`
below the graded index of `s` and every cell of that graded index reading the new cells of `D`
through the cap and reference cells (`StageType.IsStableRecoveryScheme.of_readsThroughCap`, in
`VaughtConjecture.Continuation.StableRecovery`): availability against the cap holds the label of
one of them up, and the decoder at it recovers `D`
(`CellScheme.Rows.IsLawful.label_eq_of_reading`).  Here no such cell exists: over the whole
occurrence the scheme is the scheme of `D`, and the twins have nothing above them but the cell `4`,
whose row is `⊥`.  (Informal; not compiled: that recovery at a new cell needs such a cell.)  The
data missing from the marker and cap calibration are a cap of grade above the arity of the root
(hence a private point), above the marker offset and the finite parts of the labels of `D`,
labelled at least `λ_ξ` plus its grade, and reference cells of grade at most that of the cap: the
graded cap calibration (`StageType.GradedCapCalibration`), which excludes this instance
(`not_gradedCapCalibration_twinRoot`) and is acquired in every model that is not cover-hollow and
has top-grade supremum `⊤` (`Realization.IsModel.acquiresCalibratedContexts_gradedCap`).  Stable
recovery schemes for the graded cap calibration are open; one input with such a scheme is
compiled (`Continuation.StableRecoveryReading.exists_isStableRecoveryScheme_gradedCap`).  At this
root and these donors the graded cap calibration needs a context of at least three points (the
finite part `2` of a label of `D` is below the grade `N` of the cap, and `N` is at most the number
of points: `Continuation.StableRecoveryTwin.three_le_of_gradedCapCalibration`), and with a context
of three points it holds for both donors, each with a stable recovery scheme
(`Continuation.StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors`, in
`VaughtConjecture.Continuation.StableRecoveryTwin`); no scheme serves both donors
(`Continuation.StableRecoveryTwin.not_isStableRecoveryScheme_twinDonor₁_and_twinDonor₂`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryCounterexample

open Finset Ordinal Label StageType CandidateCounterexamples

variable (ξ : Ordinal.{u})

/-! ### The donors and the root -/

/-- The first donor: the five-cell scheme at `λ_{ξ+1}` labelled `(λ_ξ + 2, ⊥, λ_ξ + 2, λ_ξ + 1, ⊥)`,
the second twin below the first. -/
noncomputable def twinDonor₁ : StageType.{u} (blockStage (ξ + 1)) 2 where
  toScheme := fiveCellScheme
  label := fiveCellLift₁ (blockStage ξ)
  isWellFormed := isLegal_fiveCellScheme.isWellFormed
  isCoded := isLegal_fiveCellScheme.isCoded
  isLawful := isLawful_fiveCellLift₁ (isSuccPrelimit_blockStage ξ)
  atStage d := blockStage_add_one ξ ▸ atStage_fiveCellLift₁ d

/-- The second donor: the five-cell scheme at `λ_{ξ+1}` labelled
`(λ_ξ + 2, ⊥, λ_ξ + 1, λ_ξ + 2, ⊥)`, the first twin below the second. -/
noncomputable def twinDonor₂ : StageType.{u} (blockStage (ξ + 1)) 2 where
  toScheme := fiveCellScheme
  label := fiveCellLift₂ (blockStage ξ)
  isWellFormed := isLegal_fiveCellScheme.isWellFormed
  isCoded := isLegal_fiveCellScheme.isCoded
  isLawful := isLawful_fiveCellLift₂ (isSuccPrelimit_blockStage ξ)
  atStage d := blockStage_add_one ξ ▸ atStage_fiveCellLift₂ d

/-- The first point spans a closed face of the five-cell scheme. -/
theorem map_castSuccEmb_mem_faces_fiveCells :
    univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ fiveCells.faces := by
  decide

/-- The only cell of the five-cell scheme visible through the first point is the cell `0`. -/
theorem eq_zero_of_mem_visibleCells_fiveCellScheme {d : Fin 5}
    (hd : d ∈ fiveCellScheme.{u}.visibleCells (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) : d = 0 := by
  have key : ∀ d : Fin 5, fiveCells.scope d ⊆ univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) →
      d = 0 := by decide
  exact key d (Finset.mem_filter.mp hd).2

/-- The root: the face of the first donor along the first point, a single cell labelled
`λ_ξ + 2`. -/
noncomputable def twinRoot : StageType.{u} (blockStage (ξ + 1)) 1 :=
  (twinDonor₁ ξ).comap Fin.castSuccEmb map_castSuccEmb_mem_faces_fiveCells

/-- Every cell of the root is the cell `0` of the five-cell scheme. -/
theorem cellMap_twinRoot (i : Fin (twinRoot ξ).card) :
    fiveCellScheme.{u}.cellMap (Fin.castSuccEmb : Fin 1 ↪ Fin 2) i = 0 :=
  eq_zero_of_mem_visibleCells_fiveCellScheme (fiveCellScheme.cellMap_mem _ i)

/-- Every cell of the root is labelled `λ_ξ + 2`. -/
theorem twinRoot_label (i : Fin (twinRoot ξ).card) :
    (twinRoot ξ).label i = ((blockStage ξ + (2 : ℕ) : Ordinal.{u}) : Label.{u}) := by
  -- the labels of the root are those of the first donor at the visible cells
  change fiveCellLift₁ (blockStage ξ) (fiveCellScheme.cellMap Fin.castSuccEmb i) = _
  rw [cellMap_twinRoot]
  rfl

/-- The root has a cell. -/
theorem nonempty_fin_card_twinRoot : Nonempty (Fin (twinRoot ξ).card) := by
  have h0 : (0 : Fin 5) ∈ Set.range (fiveCellScheme.{u}.cellMap
      (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) := by
    rw [Scheme.range_cellMap, mem_coe]
    refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
    decide
  obtain ⟨i, -⟩ := h0
  exact ⟨i⟩

/-- The root is legal. -/
theorem isLegal_twinRoot : (twinRoot ξ).IsLegal :=
  IsLegal.comap (t := twinDonor₁ ξ) Fin.castSuccEmb isLegal_fiveCellScheme _

/-- The first donor is a coface of the root. -/
theorem twinDonor₁_mem_cofaces : twinDonor₁ ξ ∈ (twinRoot ξ).cofaces :=
  ⟨isLegal_fiveCellScheme, restrictFace_of_mem _ _ map_castSuccEmb_mem_faces_fiveCells⟩

/-- The face of the second donor along the first point is the root. -/
theorem restrictFace_twinDonor₂ :
    restrictFace Fin.castSuccEmb (twinDonor₂ ξ) = some (twinRoot ξ) := by
  rw [restrictFace_of_mem _ _ map_castSuccEmb_mem_faces_fiveCells]
  refine congrArg some (StageType.ext rfl fun i j hij ↦ ?_)
  obtain rfl : i = j := Fin.ext hij
  -- the labels of both faces are those of the donors at the visible cells
  change fiveCellLift₂ (blockStage ξ) (fiveCellScheme.cellMap Fin.castSuccEmb i) =
    fiveCellLift₁ (blockStage ξ) (fiveCellScheme.cellMap Fin.castSuccEmb i)
  rw [cellMap_twinRoot ξ i]
  rfl

/-- **The root satisfies the marker and cap calibration** at `γ = λ_ξ`, for the identity of its
point and the first donor: its cell, labelled `λ_ξ + 2`, is both the marker and the cap. -/
theorem markerCapCalibration_twinRoot :
    MarkerCapCalibration ξ (twinRoot ξ) (Function.Embedding.refl (Fin 1)) (twinDonor₁ ξ)
      (blockStage ξ) := by
  obtain ⟨a⟩ := nonempty_fin_card_twinRoot ξ
  refine ⟨⟨a, 2, twinRoot_label ξ a⟩, a, ?_, ?_⟩
  · rw [twinRoot_label]
    exact_mod_cast (lt_add_iff_pos_right _).mpr (by simp)
  · rw [twinRoot_label]
    exact Label.coe_le_coe_add _ _

/-! ### The refutation -/

/-- **Stable recovery schemes for the marker and cap calibration do not exist, at every `ξ`.**
At the root `twinRoot` (one point, one cell labelled `λ_ξ + 2`, which is both the marker and the
cap), the identity of its point, the donor `twinDonor₁` and `γ = λ_ξ`, a stable recovery scheme
would be the five-cell scheme (`IsStableRecoveryScheme.eq_toScheme_of_refl`), and every stage type
on it with face the root would agree with `twinDonor₁` at its twins
(`IsStableRecoveryScheme.label_eq_of_refl`); `twinDonor₂` has the same face and the twins in the
opposite order. -/
theorem not_hasStableRecoverySchemes_markerCap :
    ¬ HasStableRecoverySchemes ξ (MarkerCapCalibration ξ) := fun h ↦ by
  obtain ⟨E, hE⟩ := h (twinRoot ξ) (Function.Embedding.refl (Fin 1)) (twinRoot ξ)
    (isLegal_twinRoot ξ) one_pos (restrictFace_refl _) (twinDonor₁ ξ) (twinDonor₁_mem_cofaces ξ)
    (blockStage ξ) (blockStage_lt_blockStage_add_one ξ) (markerCapCalibration_twinRoot ξ)
  have h2 := hE.label_eq_of_refl (twinDonor₂ ξ) rfl (restrictFace_twinDonor₂ ξ)
    (2 : Fin 5) (2 : Fin 5) rfl (by
      -- the label of the first donor at the twin `2`
      change fiveCellLift₁ (blockStage ξ) 2 ≠ ⊤
      exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne)
  exact not_labelAdd_two_le_one h2.symm.le

/-- **The finite hypothesis of the reduction of (R4) through the marker and cap calibration is
false**: stable recovery schemes for that calibration fail at `ξ = 0`, so the hypothesis
`∀ ξ < ω₁, HasStableRecoverySchemes ξ (MarkerCapCalibration ξ)` of
`StableCappedReceiving.of_hasStableRecoverySchemes_markerCap` does not hold.  This refutes that
hypothesis, not (R4) and not output 3. -/
theorem not_forall_hasStableRecoverySchemes_markerCap :
    ¬ ∀ ξ < ω₁, HasStableRecoverySchemes.{0} ξ (MarkerCapCalibration.{0} ξ) := fun h ↦
  not_hasStableRecoverySchemes_markerCap 0 (h 0 (Ordinal.omega_pos 1))

/-- **The graded cap calibration excludes this instance**: it asks for a cap of grade above the
arity `1` of the root, and the root has one point
(`StageType.GradedCapCalibration.lt`). -/
theorem not_gradedCapCalibration_twinRoot (f : Fin 1 ↪ Fin 1) (γ : Ordinal.{u}) :
    ¬ GradedCapCalibration ξ (twinRoot ξ) f (twinDonor₁ ξ) γ := fun h ↦
  (lt_irrefl 1) h.lt

/-- At the first block: no stable recovery scheme for the marker and cap calibration over the
root `twinRoot 0`, the identity of its point, the donor `twinDonor₁ 0` and `γ = ω`. -/
example : ¬ ∃ E, (twinRoot.{0} 0).IsStableRecoveryScheme (Function.Embedding.refl (Fin 1))
    (twinDonor₁ 0) ω E := by
  rintro ⟨E, hE⟩
  have h2 := hE.label_eq_of_refl (twinDonor₂ 0) rfl (restrictFace_twinDonor₂ 0)
    (2 : Fin 5) (2 : Fin 5) rfl (by
      -- the label of the first donor at the twin `2`
      change fiveCellLift₁ (blockStage 0) 2 ≠ ⊤
      exact (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)).ne)
  exact not_labelAdd_two_le_one h2.symm.le

end VaughtConjecture.Continuation.StableRecoveryCounterexample
