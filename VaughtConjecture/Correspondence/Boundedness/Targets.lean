/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Boundedness.Rank
import VaughtConjecture.Realization.Families

/-!
# Targets of Boundedness

Numbering as in the current draft of [AFK26].  Write `λ_ξ = blockStage ξ = ω + ω · ξ`.  `τ_β` is
`projectStructure β`, `K_β[L]` is `templateStageClass M β`, `N↾L_c[L]` is `baseReduct N`, and
the rank `rank_τ(N)` of [AFK26, Definitions 2.6 and 2.7] is the least fixing stage:
"`ρ` is the rank of `N`" is `IsLeast (fixingStages N) ρ` (`Boundedness/Rank.lean`).  It is the
projection-fixing rank, not a Scott rank.

This file states the targets of Boundedness [AFK26, Proposition 4.34] as propositions, every
premise visible.

* **Least fixing rank** (`LeastFixingRankTarget β M`, proved: `leastFixingRankTarget`): for
  `β < ω₁`, every `G ∈ K_β[L]` has a rank.
* **Rank at most stage** (`RankLeStageTarget β M`, proved: `rankLeStageTarget`): the rank of
  `G ∈ K_β[L]` is at most `β`.
* **Strongly coded uniformity donors** (`HasStronglyCodedUniformityDonors`, proved in
  `Boundedness/StageBound.lean`: `hasStronglyCodedUniformityDonors`): for `ξ < η`, a strongly
  coded legal one-point stage type at `λ_η` with a label in the block `[λ_ξ, λ_ξ + ω)`.  It is
  the premise of the conditional stage bound.
* **Stage bound** (`StageBoundTarget M`, proved in `Boundedness/StageBound.lean`:
  `stageBoundTarget`): on a countable carrier, the lift stages `liftStages M B` of every base
  structure `B` are bounded below `ω₁`.  Its form conditional on the donors is
  `StageBoundOfDonorsTarget M`, proved there as `stageBoundOfDonorsTarget`.
* **B.T15, Boundedness** (`BoundednessTarget M`, proved in `Boundedness/StageBound.lean`:
  `boundednessTarget`): on a countable carrier, the lift ranks `liftRanks M B` of every base
  structure `B` form a countable set bounded below `ω₁`.  The derivation from the stage bound is
  proved here (`boundednessTarget_of_stageBoundTarget`), through the rank-at-most-stage bound and
  the countability of the ordinals below a countable ordinal.

**What is not used.**  None of these targets says that the rank of `G ∈ K_β[L]` is `β`, and the
derivation of Boundedness from the stage bound does not use it.  The stage bound is a bound on
the stages `β ∈ liftStages M B` themselves; no downward closure of `liftStages M B` is used.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The rank -/

/-- **Target: least fixing rank**: for `β < ω₁`, every structure `G ∈ K_β[L]` on `M` has a rank,
a least fixing stage.  Correspondence with the printed definitions. -/
def LeastFixingRankTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → ∀ G ∈ templateStageClass M β, ∃ ρ, IsLeast (fixingStages G) ρ

/-- **The least fixing rank exists** (`leastFixingRank_of_mem_templateStageClass`).
Correspondence with the printed definitions. -/
theorem leastFixingRankTarget (β : Ordinal.{u}) (M : Type v) : LeastFixingRankTarget β M :=
  fun hβ _ hG ↦ leastFixingRank_of_mem_templateStageClass hG hβ

/-- **Target: the rank is at most the stage**: if `G ∈ K_β[L]` and `ρ` is the least fixing stage
of `G`, then `ρ ≤ β`.  No hypothesis on `β`.  Correspondence with the printed definitions. -/
def RankLeStageTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  ∀ ⦃G : templateLanguage.{u}.Structure M⦄ ⦃ρ : Ordinal.{u}⦄, G ∈ templateStageClass M β →
    IsLeast (fixingStages G) ρ → ρ ≤ β

/-- **The rank is at most the stage** (`rank_le_stage_of_mem_templateStageClass`).
Correspondence with the printed definitions. -/
theorem rankLeStageTarget (β : Ordinal.{u}) (M : Type v) : RankLeStageTarget β M :=
  fun _ _ hG hρ ↦ rank_le_stage_of_mem_templateStageClass hG hρ

/-! ### Strongly coded uniformity donors -/

/-- **Strongly coded uniformity donors** (native construction): for `ξ < η`, some strongly coded
legal stage type `d` on one point at the stage `λ_η` has a label in the block `[λ_ξ, λ_ξ + ω)`
(`d ∈ StageType.uniformityFamily (blockStage ξ)`).  Compare the uniformity field of
`StageType.HasNonemptyCofaceInstances`, which asks for a coface of any legal stage type with a
label in a block, with no strong coding; here only the coface of the stage type on no points is
asked for, and it must be strongly coded.  Proved: `hasStronglyCodedUniformityDonors`
(`Boundedness/StageBound.lean`). -/
def HasStronglyCodedUniformityDonors : Prop :=
  ∀ ⦃ξ η : Ordinal.{u}⦄, ξ < η → ∃ d : StageType.{u} (blockStage η) 1,
    d.IsStronglyCodedLegal ∧ d ∈ StageType.uniformityFamily (blockStage ξ)

/-! ### The stage bound -/

/-- **Target: the stage bound**: on a countable carrier `M`, for every base structure `B` of
`L_c[L]` on `M`, the stages `β < ω₁` at which `B` has a lift in `K_β[L]` are all below one
`A < ω₁`.

Route (a pigeonhole on disjoint label blocks):

* a lift `G ∈ K_γ[L]` of `B` at `γ > ξ` has a point whose one-point type carries a cell label in
  the block `[λ_ξ, λ_ξ + ω)`: density `D[α]` of `G` at a cutoff `α < λ_γ` above that label, with
  a strongly coded uniformity donor (`HasStronglyCodedUniformityDonors`) amalgamated with the type
  of a point; the exact label `λ_ξ` is not used;
* lifts of `B` at different stages cohere: the projection of a lift at `γ` to `γ' ≤ γ` lies in
  `K_γ'[L]` (B.T9) and has base reduct `B` (`baseReduct_projectStructure`), so it is the lift at
  `γ'` (B.T10, Reconstruction), and labels below `λ_γ'` survive the projection;
* if the lift stages were unbounded below `ω₁`, each of uncountably many blocks would be
  witnessed at some point of the countable carrier `M`, so one point would carry labels in
  infinitely many pairwise disjoint blocks; finitely many of them more than the number of cells
  are read in one lift, at the largest of their witnessing stages, but a one-point type has
  finitely many cells, a contradiction.

Correspondence with the printed definitions. -/
def StageBoundTarget (M : Type v) : Prop :=
  Countable M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    ∃ A < ω₁, ∀ β ∈ liftStages M B, β < A

/-- **Target: the stage bound from strongly coded uniformity donors**: the stage bound
(`StageBoundTarget`) under the premise `HasStronglyCodedUniformityDonors`.  Correspondence with
the printed definitions. -/
def StageBoundOfDonorsTarget (M : Type v) : Prop :=
  HasStronglyCodedUniformityDonors.{u} → StageBoundTarget.{u} M

/-! ### Boundedness -/

/-- **Target B.T15, Boundedness** [AFK26, Proposition 4.34]: on a countable carrier `M`, for every
base structure `B` of `L_c[L]` on `M`, the ranks of the lifts of `B` (to `K_β[L]` for `β < ω₁`)
form a countable set, bounded below `ω₁`.  The premise `M ⊨ σ[L]` of the printed statement is not
needed here: a base structure without lifts has no lift ranks.  Correspondence with the printed
definitions. -/
def BoundednessTarget (M : Type v) : Prop :=
  Countable M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    (liftRanks M B).Countable ∧ ∃ A < ω₁, ∀ ρ ∈ liftRanks M B, ρ < A

/-- **Boundedness from the stage bound**: a bound `A < ω₁` on the lift stages bounds the lift
ranks, since the rank of a lift at `β` is at most `β` (`rankLeStageTarget`), and the ordinals
below a countable ordinal form a countable set.  Correspondence with the printed definitions. -/
theorem boundednessTarget_of_stageBoundTarget {M : Type v} (h : StageBoundTarget.{u} M) :
    BoundednessTarget.{u} M := fun hM B ↦ by
  obtain ⟨A, hA, hS⟩ := h hM B
  obtain ⟨hc, hR⟩ := liftRanks_countable_and_bounded_of_liftStages_bounded hA hS
  exact ⟨hc, A, hA, hR⟩

/-- **Boundedness from strongly coded uniformity donors and the conditional stage bound**.
Correspondence with the printed definitions. -/
theorem boundednessTarget_of_hasStronglyCodedUniformityDonors {M : Type v}
    (h : StageBoundOfDonorsTarget.{u} M) (hd : HasStronglyCodedUniformityDonors.{u}) :
    BoundednessTarget.{u} M :=
  boundednessTarget_of_stageBoundTarget (h hd)

end VaughtConjecture
