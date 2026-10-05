/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Continuation

/-!
# Examples: output 3 from stable capped receiving, and the continuation criterion

Special cases of `VaughtConjecture.Continuation.Continuation`, each conditional only where stated:

* **The first block** `ξ = 0`: the candidate lives at `λ_1 = ω + ω`, and output 3 there is the
  assembly under (R4) and the coface instances at `ω + ω`.
* **Stable lawfulness of models**: every model at a block stage is stably lawful, with no
  hypothesis; at a cell labelled the formal top, every threshold forced over a realized rooted
  cover is forced at a twin (two cells labelled the formal top at one graded index) over a
  realized rooted cover.  The trivial case of availability for a pair of cells of one graded index
  needs no hypothesis on the realization.
* **Cover-hollow models**: the candidate is not a model, so under the coface instances it lacks
  finite-cut receiving; so (R4) extended to cover-hollow models would, with the coface instances,
  exclude cover-hollow models with unbounded growth.
* **Bounded stable labels**: likewise the candidate lacks finite-cut receiving; unbounded growth
  excludes such a bound.
* **Top-free models**: cover-hollow vacuously, with top-grade supremum `0`, stably lawful, and with
  a candidate that is not a model; they satisfy neither hypothesis of the criterion.
* **The cover of the terminal models** under (R4) and the coface instances.
-/

namespace VaughtConjecture.Continuation.ContinuationExamples

open Ordinal Realization

variable {ξ : Ordinal.{0}} {M : Type} {R : Realization.{0, 0} (blockStage ξ) M}

/-! ### The first block -/

/-- The candidate of a model at `λ_0 = ω` lives at `λ_1 = ω + ω`. -/
example : blockStage (0 + 1 : Ordinal.{0}) = ω + ω := by
  rw [blockStage_add_one, blockStage_zero]

/-- Output 3 at the first block, under (R4) and the coface instances at `λ_1`. -/
example (hR4 : StableCappedReceiving.{0})
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (0 + 1)))
    {R : Realization.{0, 0} (blockStage 0) M} (hR : R.IsModel) (hnh : ¬ R.IsCoverHollow)
    (hgrow : R.topGradeSup = ⊤) :
    (R.stableCandidate hR.isStablyLawful).IsModel ∧
      (R.stableCandidate hR.isStablyLawful).reduce (isSuccPrelimit_blockStage 0) = R :=
  ⟨isModel_stableCandidate (omega0_pos.trans omega0_lt_omega_one) hR hnh hgrow hR4 hinst,
    stableCandidate_reduce⟩

/-! ### Stable lawfulness of models -/

/-- Every model at a block stage is stably lawful, and its stable candidate reduces to it. -/
example (hR : R.IsModel) :
    (R.stableCandidate hR.isStablyLawful).reduce (isSuccPrelimit_blockStage ξ) = R :=
  stableCandidate_reduce

/-- **Forcing transfers to a twin**: in a model, at a cell `s₀` labelled the formal top and a cell
`t₀` with the scope of `s₀` in that of `t₀` and equal grades, every threshold forced at `s₀` over a
realized rooted cover is forced at a cell labelled the formal top at the graded index of `t₀`; only
the legality of the types is used. -/
example (hR : R.IsModel) {k : ℕ} {u : Fin k ↪ M} {t : StageType.{0} (blockStage ξ) k}
    (ht : R.eval u = some t) {s₀ t₀ : Fin t.card}
    (hst : t.toCellScheme.scope s₀ ⊆ t.toCellScheme.scope t₀)
    (hg : t.toCellScheme.grade s₀ = t.toCellScheme.grade t₀) (hs₀ : t.label s₀ = ⊤) (n : ℕ)
    (hn : R.ForcesOverCover u t s₀ n) :
    ∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex t₀ ∧ t.label w = ⊤ ∧
      R.ForcesOverCover u t w n :=
  (availability_stableSection_iff ht hs₀).mp
    (availability_stableSection_of_hasLegalTypes hR.hasLegalTypes ht hst hg) n hn

/-- Availability at a pair of cells of one graded index holds trivially, so the criterion of
`availability_stableSection_iff` holds there: each forced threshold is forced at a cell labelled
the formal top of that graded index. -/
example {k : ℕ} {u : Fin k ↪ M} {t : StageType.{0} (blockStage ξ) k} (ht : R.eval u = some t)
    {s₀ : Fin t.card} (hs₀ : t.label s₀ = ⊤) (n : ℕ) (hn : R.ForcesOverCover u t s₀ n) :
    ∃ w, t.toCellScheme.gradedIndex w = t.toCellScheme.gradedIndex s₀ ∧ t.label w = ⊤ ∧
      R.ForcesOverCover u t w n :=
  (availability_stableSection_iff ht hs₀).mp ⟨s₀, rfl, le_rfl⟩ n hn

/-! ### Cover-hollow models -/

/-- A cover-hollow model is stably lawful, and, under the coface instances at `λ_{ξ+1}`, its
candidate lacks finite-cut receiving: receiving would make it a model. -/
example (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    (hR : R.IsModel) (hh : R.IsCoverHollow) :
    ¬ (R.stableCandidate (isStablyLawful_of_isCoverHollow hh)).HasFiniteCutReceiving :=
  fun hr ↦ not_isModel_stableCandidate_of_isCoverHollow hh _
    (isModel_stableCandidate_of_hasFiniteCutReceiving hR hinst hr)

/-- Non-hollowness gives the candidate a label in `[λ_ξ, λ_ξ + ω)`, which a cover-hollow
realization does not have. -/
example (hnh : ¬ R.IsCoverHollow) (hlaw : R.IsStablyLawful) :
    ∃ (x : (R.stableCandidate hlaw).Occurrence) (a : Fin x.type.card),
      ((blockStage ξ : Ordinal.{0}) : Label.{0}) ≤ x.type.label a ∧
        x.type.label a < ((blockStage ξ + ω : Ordinal.{0}) : Label.{0}) := by
  obtain ⟨x, a, i, h⟩ := exists_stableCandidate_label_eq_coe_add hnh hlaw
  refine ⟨x, a, ?_, ?_⟩ <;> rw [h]
  · exact_mod_cast le_self_add
  · exact_mod_cast add_lt_add_right (natCast_lt_omega0 i) _

/-! ### Bounded stable labels -/

/-- If every stable label is at most `λ_ξ + K`, then under the coface instances at `λ_{ξ+1}` the
candidate of a model lacks finite-cut receiving. -/
example (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    (hR : R.IsModel) (hlaw : R.IsStablyLawful) {K : ℕ}
    (hK : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{0} (blockStage ξ) n), R.eval u = some t →
      ∀ d, t.label d = ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d ≤
        ((blockStage ξ + K : Ordinal.{0}) : Label.{0})) :
    ¬ (R.stableCandidate hlaw).HasFiniteCutReceiving :=
  fun hr ↦ not_isModel_stableCandidate_of_stableLabel_le hK hlaw
    (isModel_stableCandidate_of_hasFiniteCutReceiving hR hinst hr)

/-- Unbounded growth excludes a bound `λ_ξ + K` on the stable labels. -/
example (hgrow : R.topGradeSup = ⊤) (hlaw : R.IsStablyLawful) (K : ℕ)
    (hK : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{0} (blockStage ξ) n), R.eval u = some t →
      ∀ d, t.label d = ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d ≤
        ((blockStage ξ + K : Ordinal.{0}) : Label.{0})) : False := by
  obtain ⟨⟨n, u, P, hP⟩, a, h⟩ := exists_lt_stableCandidate_label hgrow hlaw K
  obtain ⟨t, ht, rfl⟩ := exists_eq_stableType_of_stableCandidate_eval hP
  refine h.not_ge ?_
  -- the label of the stable type at `a` is the stable section there
  change R.stableSection u t a ≤ _
  by_cases ha : t.label a = ⊤
  · rw [stableSection_of_eq_top ha]
    exact hK u t ht a ha
  · rw [stableSection_of_ne_top ha]
    exact ((t.atStage a).resolve_right ha).le.trans (by exact_mod_cast le_self_add)

/-! ### Top-free models -/

/-- A top-free realization is cover-hollow and has top-grade supremum `0`, so it satisfies neither
hypothesis of the criterion; it is stably lawful, and no candidate of it is a model.  No model is
assumed. -/
example (h : ∀ x : R.Occurrence, x.type.IsTopFree) :
    R.IsCoverHollow ∧ R.topGradeSup = 0 ∧ R.IsStablyLawful ∧
      ∀ hlaw : R.IsStablyLawful, ¬ (R.stableCandidate hlaw).IsModel :=
  ⟨isCoverHollow_of_isTopFree h, topGradeSup_eq_zero_iff.mpr h,
    isStablyLawful_of_isCoverHollow (isCoverHollow_of_isTopFree h),
    not_isModel_stableCandidate_of_isCoverHollow (isCoverHollow_of_isTopFree h)⟩

/-! ### The cover of the terminal models -/

/-- Under (R4) and the coface instances, every terminal model at the first block has a terminal
property. -/
example (hR4 : StableCappedReceiving.{0})
    (hinst : ∀ ξ < ω₁, StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    {R : Realization.{0, 0} (blockStage 0) M} (hR : R.IsModel) (ht : R.IsTerminalAt 0) :
    ∃ P, R.HasTerminalProperty P :=
  exists_hasTerminalProperty (.of_stableCappedReceiving hR4 hinst)
    (omega0_pos.trans omega0_lt_omega_one) hR ht

end VaughtConjecture.Continuation.ContinuationExamples
