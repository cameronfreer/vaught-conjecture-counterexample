/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.ScottAnalysis
import VaughtConjecture.Stage.Cap

/-!
# A tuple covering a chart with a top cell has orbit rank at least `ω₁`

Companion programme over the density sentence, process rank `ω₁`.  Conventions as in
`VaughtConjecture.ProcessRank.RankConventions`: `r(a) = orbitRank a`.  Every statement here is a
**given-model statement** about one receiving model expansion `R` at stage `ω₁`
(`ModelExpansion M ω₁` with `R.1.IsReceivingModel`); none asserts the existence of a model.

**The obstruction.**  Let `a` cover a stage type `p` at `ω₁` that is not top-free.  For every
countable `η`, capping `p` above the block stage `λ_η` gives a legal top-free stage type `q` with
the same reduction to `λ_η` (`ExistsTopFreeReduceEqTarget`, finite).  A cover `b` of `q` occurs
in the same model, by exact receiving of the legal top-free types over the empty root
(`Realization.exactReceivingWithin_isTopFree`).  Then `a` and `b` are back-and-forth equivalent
at `η` (the comparison from a common chart at `λ_η`,
`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`), and not at the countable rank
of the chart selection formula of `q` (`chartSelectionFormula`): that formula holds of `b`, and
would make `a` a cover of the top-free `q ≠ p`.  The approximating tuple `b` depends on `η`
(`ExistsCappedApproximationTarget`).  Hence `r(a) ≥ ω₁` (`OrbitRankGeOmegaOneOfCoversTarget`),
the implication being `orbitRankGeOmegaOneOfCoversTarget_of_approximation`.

**Results.**

* `ExistsTopFreeReduceEqTarget` (stated).
* `ExistsCappedApproximationTarget` (stated).
* `OrbitRankGeOmegaOneOfCoversTarget` (stated).
* `orbitRankGeOmegaOneOfCoversTarget_of_approximation` (proved): the approximation gives the
  bound.
-/

universe w

namespace VaughtConjecture.ProcessRank

open Ordinal _root_.Order FirstOrder Language

/-- **Target: a legal stage type at `ω₁` has a legal top-free stage type with the same reduction
to any countable block stage.**  For a legal stage type `p` at `ω₁` and a countable index `η`,
some legal top-free stage type `q` at `ω₁` on the same points has the same reduction to `λ_η` as
`p`.  Route: `q = p.cap c` for an ordinal `c < ω₁` self-visible at the arity with `λ_η ≤ c`
(`Label.exists_lt_lt_isSelfVisible`); labels below `λ_η` are unchanged by the cap, and labels at
or above `λ_η`, `⊤` included, stay at or above `λ_η`, so both reduce to `⊤`.  Finite statement.
Stated. -/
def ExistsTopFreeReduceEqTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω₁ n), p.IsLegal → ∀ ⦃η : Ordinal.{0}⦄, η < ω₁ →
    ∃ q : StageType.{0} ω₁ n, q.IsLegal ∧ q.IsTopFree ∧
      q.reduce (isSuccPrelimit_blockStage η) = p.reduce (isSuccPrelimit_blockStage η)

/-- **Target: capped approximations of a tuple covering a chart with a top cell.**  In a
receiving model expansion `R` to `ω₁`, if `a` covers a stage type `p` that is not top-free, then
for every countable `η` some tuple `b` of the same model is back-and-forth equivalent to `a` at
`η` in the base language and not at some countable level.  The tuple `b` depends on `η`.
Given-model statement.  Stated. -/
def ExistsCappedApproximationTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω₁ n) (a : Fin n → M), R.1.Covers p a → ¬ p.IsTopFree →
      ∀ ⦃η : Ordinal.{0}⦄, η < ω₁ → ∃ b : Fin n → M,
        BFEquiv (L := baseLanguage.{0}) η n a b ∧
          ∃ γ < (ω₁ : Ordinal.{0}), ¬ BFEquiv (L := baseLanguage.{0}) γ n a b

/-- **Target: a tuple covering a chart with a top cell has orbit rank at least `ω₁`.**  In a
receiving model expansion `R` to `ω₁`, a tuple `a` covering a stage type `p` that is not
top-free has `r(a) = orbitRank a` at least the lift of `ω₁` to the carrier universe.
Given-model statement.  Stated. -/
def OrbitRankGeOmegaOneOfCoversTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω₁ n) (a : Fin n → M), R.1.Covers p a → ¬ p.IsTopFree →
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤ orbitRank (L := baseLanguage.{0}) a

/-- **The approximations give the bound**: if `r(a)` were below the lift of `ω₁`, it would be the
lift of a countable `η`; the approximation `b` at `η` would be equivalent to `a` at `r(a)`, hence
at every level (`bfEquiv_all_of_bfEquiv_orbitRank`), against the separating countable level. -/
theorem orbitRankGeOmegaOneOfCoversTarget_of_approximation
    (h : ExistsCappedApproximationTarget.{w}) : OrbitRankGeOmegaOneOfCoversTarget.{w} := by
  intro M _ R hR n p a hp htop
  refine le_of_not_gt fun hlt ↦ ?_
  obtain ⟨η, hη, hηa⟩ := Ordinal.lt_lift_iff.1 hlt
  obtain ⟨b, hab, γ, -, hγ⟩ := h R hR p a hp htop hη
  exact hγ (BFEquiv.toOrdinalLift
    (bfEquiv_all_of_bfEquiv_orbitRank (hηa ▸ hab.ofOrdinalLift) (Ordinal.lift.{w} γ)))

end VaughtConjecture.ProcessRank
