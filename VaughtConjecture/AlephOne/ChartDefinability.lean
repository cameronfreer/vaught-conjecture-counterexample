/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Definability.ReceivingBlockFormulas
import VaughtConjecture.Extension.ForcingDonorsCoatom
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Realization.ReceivingLimit

/-!
# Chart definability in receiving models at `ω₁`

Companion programme over the density sentence: the chart predicates of a receiving model
expansion at stage `ω₁` are defined, at every countable block stage, by the base-language formulas
of `VaughtConjecture.Definability.BlockFormulas` built from the forcing thresholds; a top-free chart
at `ω₁` is defined by such a formula of countable quantifier rank.  This is the input of the upper
bound on orbit ranks.

**Why no hypothesis on other models is needed.**  The general correctness theorem
(`realize_blockFormula_iff`) assumes block determination at every model expansion; receiving of the
given expansion does not give that.  Its recursion, however, uses block determination only at the
reductions of the given expansion to the block stages `λ_{ξ+1}` (`CoverThresholds.DeterminesAt`,
`RealizeBlockFormulaOfDeterminesAtTarget`).  For a receiving model expansion `R` at `ω₁` these
reductions are receiving models (`Realization.IsReceivingModel.reduce`), at limit stages, hence
have finite-extension receiving, hence block determination for the forcing thresholds
(`forcingThresholds_determinesAt`, with forcing donors at every block index).

**Top-free recovery.**  A top-free stage type `p` at `ω₁` has finitely many labels, all below
`ω₁`, hence all below some countable block stage `λ_η`.  Its reduction to `λ_η` has no formal top,
and any stage type with the same reduction is `p` (`StageType.eq_of_reduce_eq_of_isTopFree`).  So
the covers of `p` in `R` are the covers of `p↓λ_η` in the reduction of `R`, defined by a formula of
rank at most `ω · η`; a selection of their coordinates is defined by the extension formula
(`extendFormula`), of rank at most `ω · η + m`.

**Results.**

* `StageType.eq_of_reduce_eq_of_isTopFree` (proved).
* `RealizeBlockFormulaOfIsReceivingModelTarget` (proved; also for a realization with its own base
  structure, `Realization.IsReceivingModel.realize_blockFormula_iff`): the formulas of the forcing
  thresholds at `λ_η`, `η < ω₁`, hold of exactly the covers in the reduction to `λ_η` of a receiving
  model expansion at `ω₁`.  Given-model statement.
* `ExistsIsTopFreeReduceBlockStageTarget` (proved): a top-free type at `ω₁` has a top-free
  reduction to some countable block stage.
* `ChartSelectionFormulaTarget` (stated; open): for a top-free `p` at `ω₁` and a selector `f`, one
  base formula of rank `< ω₁` defines the selections along `f` of the covers of `p`, in every
  receiving model expansion at `ω₁`.  The formula is chosen before the model.

No statement here uses top-free types of the model; the upper bound on orbit ranks will use them
(every tuple is a selection of a cover of a top-free type).
-/

universe u w

namespace VaughtConjecture

open Ordinal Order FirstOrder Language

/-- **A stage type is recovered from a top-free reduction**: if the reduction of `t` to a stage
`β` (zero or a limit) has no formal top, every stage type with the same reduction is `t`.  The
labels of the reduction are below `β`, so reduction did not change them. -/
theorem StageType.eq_of_reduce_eq_of_isTopFree {α β : Ordinal.{u}} {n : ℕ}
    (hβ : IsSuccPrelimit β) {s t : StageType.{u} α n} (h : s.reduce hβ = t.reduce hβ)
    (ht : (t.reduce hβ).IsTopFree) : s = t := by
  have key (x : Label.{u}) (hx : Label.reduce β x ≠ ⊤) : Label.reduce β x = x := by
    by_cases hxβ : x < (β : Label.{u})
    · exact Label.reduce_of_lt hxβ
    · exact absurd (Label.reduce_of_le (not_lt.mp hxβ)) hx
  refine StageType.ext (by simpa using congrArg StageType.toScheme h) fun i j hij ↦ ?_
  have hl : Label.reduce β (s.label i) = Label.reduce β (t.label j) :=
    StageType.label_congr h hij
  have hj : Label.reduce β (t.label j) ≠ ⊤ := ht j
  rw [← key _ hj, ← hl, key _ (hl ▸ hj)]

/-- **Target: chart definability in a receiving model expansion at `ω₁`.**  For a base structure
`M` and a model expansion `R` of `M` to `ω₁` that is a receiving model, at every countable block
index `η`, the formula of the forcing thresholds of a stage type `t` at `λ_η` holds of a tuple
exactly when the tuple covers `t` in the reduction of `R` to `λ_η`.  No hypothesis on other models.
Given-model statement.  Proved (`realizeBlockFormulaOfIsReceivingModelTarget`). -/
def RealizeBlockFormulaOfIsReceivingModelTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃η : Ordinal.{0}⦄ (hη : η < ω₁) ⦃k : ℕ⦄ (t : StageType.{0} (blockStage η) k) (c : Fin k → M),
      (blockFormula forcingThresholds η hη t).Realize c ↔
        (R.1.reduce (isSuccPrelimit_blockStage η)).Covers t c

/-- Chart definability in a receiving model expansion at `ω₁`: the general correctness at a given
expansion (`realize_blockFormula_iff_of_determinesAt`) for the reduction of `R` to `λ_η`, whose
reductions to `λ_{ξ+1}` are reductions of `R` (`Realization.reduce_reduce`), hence receiving models
(`Realization.IsReceivingModel.reduce`) with finite-extension receiving at a limit stage, hence have
block determination for the forcing thresholds (`forcingThresholds_determinesAt`, with forcing
donors from the coatom extension property with apex at `λ_{ξ+1}`). -/
theorem realizeBlockFormulaOfIsReceivingModelTarget :
    RealizeBlockFormulaOfIsReceivingModelTarget.{w} := by
  intro M _ R hR η hη k t c
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  refine realize_blockFormula_iff_of_determinesAt forcingThresholds hη
    (R.reduce hω.isSuccPrelimit (isSuccLimit_blockStage η) (omega0_le_blockStage η)
      (blockStage_lt_omega_one hη).le) (fun ξ hξ ↦ ?_) t c
  rw [ModelExpansion.reduce_val, Realization.reduce_reduce _ _ _
    (blockStage_mono (Order.add_one_le_of_lt hξ))]
  have hS := hR.reduce hω.isSuccPrelimit (isSuccLimit_blockStage (ξ + 1))
    (blockStage_lt_omega_one (hω.succ_lt (hξ.trans hη))).le
  exact forcingThresholds_determinesAt hS.1.isConsistent hS.1.hasLegalTypes
    (hS.2.hasFiniteExtensionReceiving hS.1.isConsistent (isSuccPrelimit_blockStage (ξ + 1)))
    (forcingDonors_of_hasApexCoatomExtensions
      (StageType.hasApexCoatomExtensions (isSuccPrelimit_blockStage (ξ + 1))))

/-- **Chart definability in a receiving model at `ω₁` with its own base structure**: the base
structure of a realization `R` at `ω₁` is the structure of its reduction to `ω`; for a receiving
model, the formula of the forcing thresholds of `t` at `λ_η`, `η < ω₁`, holds in that structure of
exactly the covers of `t` in the reduction of `R` to `λ_η`. -/
theorem Realization.IsReceivingModel.realize_blockFormula_iff {M : Type w}
    {R : Realization.{0, w} ω₁ M} (hR : R.IsReceivingModel) {η : Ordinal.{0}} (hη : η < ω₁)
    {k : ℕ} (t : StageType.{0} (blockStage η) k) (c : Fin k → M) :
    letI := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
    (blockFormula forcingThresholds η hη t).Realize c ↔
      (R.reduce (isSuccPrelimit_blockStage η)).Covers t c :=
  letI := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  realizeBlockFormulaOfIsReceivingModelTarget ⟨R, hR.1, rfl⟩ hR hη t c

/-- **Target: a top-free type at `ω₁` has a top-free reduction to a countable block stage.**
Proved (`existsIsTopFreeReduceBlockStageTarget`). -/
def ExistsIsTopFreeReduceBlockStageTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω₁ n), p.IsTopFree →
    ∃ η < (ω₁ : Ordinal.{0}), (p.reduce (isSuccPrelimit_blockStage η)).IsTopFree

/-- A top-free type at `ω₁` has a top-free reduction to a countable block stage: each label is
below `ω₁`, hence below some countable block stage (`Label.exists_lt_blockStage_of_lt`), and the
largest of these finitely many block indices serves for all cells. -/
theorem existsIsTopFreeReduceBlockStageTarget : ExistsIsTopFreeReduceBlockStageTarget := by
  intro n p hp
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have h (d : Fin p.card) : ∃ ξ < (ω₁ : Ordinal.{0}), p.label d < (blockStage ξ : Label.{0}) := by
    have hd : p.label d < ((ω₁ : Ordinal.{0}) : Label.{0}) := (p.atStage d).resolve_right (hp d)
    exact Label.exists_lt_blockStage_of_lt hω (hd.trans_le (by exact_mod_cast le_blockStage _))
  choose ξ hξ hlt using h
  refine ⟨Finset.univ.sup ξ, (Finset.sup_lt_iff hω.bot_lt).mpr fun d _ ↦ hξ d, fun d ↦ ?_⟩
  change Label.reduce _ (p.label d) ≠ ⊤
  rw [Label.reduce_of_lt ((hlt d).trans_le ?_)]
  · exact hp d
  · exact_mod_cast blockStage_mono (Finset.le_sup (f := ξ) (Finset.mem_univ d))

/-- **Target: the selections of a top-free chart at `ω₁` are defined by one formula of countable
rank.**  For a top-free stage type `p` at `ω₁` on `m` points and a selector `f : Fin n → Fin m`
(not necessarily injective), some base-language formula of quantifier rank below `ω₁` holds of a
tuple `b`, in every receiving model expansion at `ω₁`, exactly when `b` is the selection along `f`
of a cover of `p`.  The formula is chosen before the model.  Given-model statement (uniform in the
model).  Stated; open. -/
def ChartSelectionFormulaTarget : Prop :=
  ∀ ⦃m : ℕ⦄ (p : StageType.{0} ω₁ m), p.IsTopFree → ∀ ⦃n : ℕ⦄ (f : Fin n → Fin m),
    ∃ φ : baseLanguage.{0}.Formulaω (Fin n), φ.qrank < ω₁ ∧
      ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁),
        R.1.IsReceivingModel → ∀ b : Fin n → M,
          (φ.Realize b ↔ ∃ a : Fin m → M, R.1.Covers p a ∧ a ∘ f = b)

end VaughtConjecture
