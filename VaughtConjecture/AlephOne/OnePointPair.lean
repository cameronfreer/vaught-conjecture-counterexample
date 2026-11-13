/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Comparison
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Realization.BlockStages
import VaughtConjecture.Realization.ReceivingLimit

/-!
# A pair of one-point types with equal reductions

Companion programme over the density sentence: the input of the lower bound on orbit ranks.  For a
cutoff `β` below a stage `α` (both zero or limits), two legal top-free stage types on one point with
the same scheme, distinct, with the same reduction to `β`; in a receiving model at a limit stage
both occur.

**The pair.**  The one-point apex type (`StageType.onePointApex`, the construction of
`StageType.exists_onePoint_label`) capped at two distinct labels `c₁, c₂ ∈ [β, α)` self-visible at
`1` (`StageType.cap`).  The scheme of a capped type is the scheme of the type, so both have the
scheme of the one-point apex type; their single cells carry `c₁` and `c₂`, so they differ; both
labels reduce to the formal top at `β`, so the reductions agree.  No uniformity clause is used.

**Occurrence.**  In a receiving model at a limit stage, every legal top-free stage type on one
point is the type of a point: exact receiving of the legal top-free types
(`Realization.exactReceivingWithin_isTopFree`) over the cover of the stage type on no points by the
empty tuple (`Realization.IsModel.exists_covers_zero`).

**Results (all proved).**

* `onePointPairTarget`: legality, top-freeness, equal schemes, unequal types and equal reductions
  of the capped pair, for given labels.
* `existsOnePointPairTarget`: such a pair exists above every cutoff.
* `Realization.IsReceivingModel.exists_covers_onePoint`: occurrence of a legal top-free one-point
  type in a receiving model at a limit stage.  Given-model statement.
* `onePointPairOccursTarget`: at `ω₁`, above every countable block stage `λ_ξ`, a pair as above
  both of whose types occur in a given receiving model.  Given-model statement.

Not claimed here: that the two points are back-and-forth equivalent at `ξ`, or not equivalent at
every level; those are the uses of this pair in the lower bound.
-/

universe u v w

namespace VaughtConjecture

open Ordinal Order Label

/-- **Target: the capped one-point pair.**  For a cutoff `β` (zero or a limit) and two distinct
ordinals `c₁, c₂` with `β ≤ cᵢ < α`, self-visible at `1`, the one-point apex type capped at `c₁`
and at `c₂` are legal and top-free, have the same scheme, are distinct, and have the same reduction
to `β`. -/
def OnePointPairTarget : Prop :=
  ∀ ⦃α β c₁ c₂ : Ordinal.{u}⦄ (hβ : IsSuccPrelimit β) (hc₁ : IsSelfVisible 1 (c₁ : Label.{u}))
    (hc₂ : IsSelfVisible 1 (c₂ : Label.{u})) (h₁ : c₁ < α) (h₂ : c₂ < α), β ≤ c₁ → β ≤ c₂ →
    c₁ ≠ c₂ →
      ((StageType.onePointApex (α := α)).cap c₁ hc₁ h₁).IsLegal ∧
      ((StageType.onePointApex (α := α)).cap c₂ hc₂ h₂).IsLegal ∧
      ((StageType.onePointApex (α := α)).cap c₁ hc₁ h₁).IsTopFree ∧
      ((StageType.onePointApex (α := α)).cap c₂ hc₂ h₂).IsTopFree ∧
      ((StageType.onePointApex (α := α)).cap c₁ hc₁ h₁).toScheme =
        ((StageType.onePointApex (α := α)).cap c₂ hc₂ h₂).toScheme ∧
      (StageType.onePointApex (α := α)).cap c₁ hc₁ h₁ ≠
        (StageType.onePointApex (α := α)).cap c₂ hc₂ h₂ ∧
      ((StageType.onePointApex (α := α)).cap c₁ hc₁ h₁).reduce hβ =
        ((StageType.onePointApex (α := α)).cap c₂ hc₂ h₂).reduce hβ

/-- The capped one-point pair: legal, top-free, one scheme, distinct, equal reductions. -/
theorem onePointPairTarget : OnePointPairTarget.{u} := by
  intro α β c₁ c₂ hβ hc₁ hc₂ h₁ h₂ hβ₁ hβ₂ hne
  refine ⟨StageType.isLegal_cap.mpr StageType.isLegal_onePointApex,
    StageType.isLegal_cap.mpr StageType.isLegal_onePointApex, StageType.isTopFree_cap,
    StageType.isTopFree_cap, rfl, fun h ↦ hne ?_, StageType.ext rfl fun i j hij ↦ ?_⟩
  · have hl := StageType.label_congr h (i := ⟨0, by simp⟩) (j := ⟨0, by simp⟩) rfl
    rw [StageType.onePointApex_cap_label, StageType.onePointApex_cap_label] at hl
    exact_mod_cast hl
  · -- both cells reduce to the formal top (`StageType.reduce_label`, by definition)
    exact ((congrArg (Label.reduce β) (StageType.onePointApex_cap_label hc₁ h₁ i)).trans
      (Label.reduce_of_le (by exact_mod_cast hβ₁))).trans
      ((congrArg (Label.reduce β) (StageType.onePointApex_cap_label hc₂ h₂ j)).trans
        (Label.reduce_of_le (by exact_mod_cast hβ₂))).symm

/-- **Target: a one-point pair above every cutoff.**  For stages `β < α`, both zero or limits, some
two legal top-free stage types on one point at `α` have the same scheme, are distinct, and have the
same reduction to `β`. -/
def ExistsOnePointPairTarget : Prop :=
  ∀ ⦃α β : Ordinal.{u}⦄, IsSuccPrelimit α → ∀ hβ : IsSuccPrelimit β, β < α →
    ∃ d₁ d₂ : StageType.{u} α 1, d₁.IsLegal ∧ d₂.IsLegal ∧ d₁.IsTopFree ∧ d₂.IsTopFree ∧
      d₁.toScheme = d₂.toScheme ∧ d₁ ≠ d₂ ∧ d₁.reduce hβ = d₂.reduce hβ

/-- A one-point pair above every cutoff: the capped pair at `β + 2` and `β + 4`. -/
theorem existsOnePointPairTarget : ExistsOnePointPairTarget.{u} := by
  intro α β hα hβ hβα
  obtain ⟨c₁, hβc₁, hc₁α, hc₁⟩ := exists_lt_lt_isSelfVisible hα hβα 1
  obtain ⟨c₂, hc₁c₂, hc₂α, hc₂⟩ := exists_lt_lt_isSelfVisible hα hc₁α 1
  obtain ⟨hl₁, hl₂, ht₁, ht₂, hs, hne, hr⟩ := onePointPairTarget hβ hc₁ hc₂ hc₁α hc₂α hβc₁.le
    (hβc₁.trans hc₁c₂).le hc₁c₂.ne
  exact ⟨_, _, hl₁, hl₂, ht₁, ht₂, hs, hne, hr⟩

namespace Realization

variable {α : Ordinal.{u}} {M : Type v}

/-- **Occurrence of a top-free one-point type**: in a receiving model at a limit stage, every legal
top-free stage type on one point is the type of a point.  Exact receiving of the legal top-free
types over the cover of the stage type on no points by the empty tuple. -/
theorem IsReceivingModel.exists_covers_onePoint {R : Realization.{u, v} α M}
    (hR : R.IsReceivingModel) (hα : IsSuccLimit α) {d : StageType.{u} α 1} (hd : d.IsLegal)
    (hdt : d.IsTopFree) : ∃ a : M, R.Covers d ![a] := by
  obtain ⟨t₀, ht₀⟩ := hR.1.exists_covers_zero
  have hrec := hR.2.hasFiniteExtensionReceiving hR.1.isConsistent hα.isSuccPrelimit
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (d.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  obtain ⟨u, hu, -⟩ := exactReceivingWithin_isTopFree hR.1.isConsistent hα hrec t₀ ![] ht₀ d
    Function.Embedding.ofIsEmpty ⟨hd, hdt⟩ (hq.trans (congrArg some (StageType.eq_of_zero q t₀)))
  refine ⟨u 0, ?_⟩
  have hu0 : u = ![u 0] := funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl
  rwa [hu0] at hu

end Realization

/-- **Target: both types of a one-point pair occur, at `ω₁`.**  In a receiving model `R` at `ω₁`,
above every countable block stage `λ_ξ`, some two legal top-free stage types on one point with the
same scheme, distinct, with the same reduction to `λ_ξ`, are the types of points `a₁` and `a₂` of
`R`.  Given-model statement. -/
def OnePointPairOccursTarget : Prop :=
  ∀ ⦃M : Type w⦄ (R : Realization.{0, w} ω₁ M), R.IsReceivingModel → ∀ ⦃ξ : Ordinal.{0}⦄,
    ξ < ω₁ → ∃ d₁ d₂ : StageType.{0} ω₁ 1, d₁.IsLegal ∧ d₂.IsLegal ∧ d₁.IsTopFree ∧
      d₂.IsTopFree ∧ d₁.toScheme = d₂.toScheme ∧ d₁ ≠ d₂ ∧
      d₁.reduce (isSuccPrelimit_blockStage ξ) = d₂.reduce (isSuccPrelimit_blockStage ξ) ∧
      ∃ a₁ a₂ : M, R.Covers d₁ ![a₁] ∧ R.Covers d₂ ![a₂]

/-- Both types of a one-point pair occur in a receiving model at `ω₁`. -/
theorem onePointPairOccursTarget : OnePointPairOccursTarget.{w} := by
  intro M R hR ξ hξ
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  obtain ⟨d₁, d₂, hl₁, hl₂, ht₁, ht₂, hs, hne, hr⟩ := existsOnePointPairTarget hω.isSuccPrelimit
    (isSuccPrelimit_blockStage ξ) (blockStage_lt_omega_one hξ)
  obtain ⟨a₁, h₁⟩ := hR.exists_covers_onePoint hω hl₁ ht₁
  obtain ⟨a₂, h₂⟩ := hR.exists_covers_onePoint hω hl₂ ht₂
  exact ⟨d₁, d₂, hl₁, hl₂, ht₁, ht₂, hs, hne, hr, a₁, a₂, h₁, h₂⟩

end VaughtConjecture
