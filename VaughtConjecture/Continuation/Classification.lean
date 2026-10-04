/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Continuation.Terminal
import VaughtConjecture.Realization.BlockStages
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Realization.Model

/-!
# Terminal properties, their countability, and the cover of the terminal models

Roadmap, Layer 4 (the terminal classification: rigid finite core, eventual top grade, hollow
unbounded growth; condition 2, the countable successor losses; output 3 of higher-stage
reconstruction, the continuation criterion); semantic contract, item 8.

Throughout, `ξ : Ordinal.{0}`, `λ_ξ = blockStage ξ` is the block stage, and `λ_{ξ+1}` is the next
one.  Realizations at `λ_ξ` are on a carrier `M : Type w`.

**Terminal properties.**  The index `TerminalProperty ξ` is the sum of three families:

* a stage type `p` at `λ_ξ` on `n` points (`inl ⟨n, p⟩`): the type of a globally rigid core;
* a natural number `K` (`inr (inl K)`): the eventual top grade of a model with no rigid core;
* a single point (`inr (inr ())`): hollow unbounded growth.

For `ξ < ω₁` it is countable (`countable_terminalProperty`): then `λ_ξ < ω₁`
(`blockStage_lt_omega_one`), and at a countable stage there are countably many stage types on
each number of points (`StageType.countable_of_lt_omega_one`).  No ordinal parameter enters, and
`K` is a natural number since grades are.

**Having a property** (`Realization.HasTerminalProperty`).  A realization `R` at `λ_ξ` has

* `inl ⟨n, p⟩` when some cover of `p` in `R` is a globally rigid core
  (`Realization.IsGloballyRigidCore`);
* `inr (inl K)` when no cover is a globally rigid core and the top-grade supremum
  (`Realization.topGradeSup`) is `K`;
* `inr (inr ())` when `R` is cover-hollow (`Realization.IsCoverHollow`) and its top-grade
  supremum is `⊤`.

A realization may have several properties: the definitions do not exclude a cover-hollow model
with unbounded growth that also has a globally rigid core, and the top-free witness of
`Continuation.ClassificationExamples` has the rigid-core property both on no points and on one
point.  There is no canonical property of a model, and no disjointness is claimed.

**The continuation criterion** (`ContinuationCriterion`) is output 3 of higher-stage
reconstruction in its sufficiency direction, and is **still to be proved**; here it is a
hypothesis.  It states that a model at `λ_ξ`, for `ξ < ω₁`, that is not cover-hollow and has
top-grade supremum `⊤` is the stage reduction of a model at `λ_{ξ+1}` on the same carrier.  Its
intended derivation rests on:

* output 1b (lawfulness of the stable candidate at `λ_{ξ+1}`);
* (R4) of the table of Layer 3, with its empty-root base case;
* the apex coatom extension property at `λ_{ξ+1}`.

None of these is proved.  The converse of the criterion (H1) is neither stated nor used.

**The cover of the terminal models** (`exists_hasTerminalProperty`).  Under the continuation
criterion, every model at `λ_ξ` that is terminal at `ξ` (`Realization.IsTerminalAt`) has some
terminal property.  The top-grade supremum lies in `ℕ∞`, so it is `⊤` or a natural number `K`,
and no attainment lemma is needed:

* if it is `⊤`, the model is cover-hollow: otherwise the criterion makes it the reduction of a
  model at `λ_{ξ+1}`, against terminality;
* if it is `K`, either some cover is a globally rigid core, or none is.

The criterion is used once, contrapositively.  Positivity of `K` in the residual property is
derived (`Realization.topGradeSup_ne_zero_of_residual`): for a model with top-grade supremum `0`,
the empty tuple covers a stage type on no points (`Realization.IsModel.exists_covers_zero`) and
is a globally rigid core (`Realization.IsModel.isGloballyRigidCore_empty_iff`).

**Top-free models.**  A model whose actual types are top-free has the property `inl ⟨0, p⟩`,
for the stage type `p` on no points, unique by `StageType.eq_of_zero`
(`Realization.hasTerminalProperty_inl_zero_of_isTopFree`), and does not have the hollow property
`inr (inr ())`, since its top-grade supremum is `0`, not `⊤`
(`Realization.not_hasTerminalProperty_hollow_of_isTopFree`), although it is cover-hollow
vacuously (`Realization.isCoverHollow_of_isTopFree`).

Nothing here uses uniqueness or normalization of expansions, global termination, a canonical
choice of property, or characteristic arity.  Cover-hollowness enters only through the
continuation criterion and the hollow property; its equivalence with the original anchor
definition of hollowness (roadmap, Layer 4; semantic contract, item 8) is still to be proved.
The countability of the successor losses needs, besides this cover, terminality of the
expansions of a class in a loss (`Realization.IsExpansionOf.isTerminalAt`) and the comparison of
two expansions sharing a property (`VaughtConjecture.Continuation.Comparison`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal Cardinal

/-- The **terminal properties** at the block `ξ`: the type of a globally rigid core (a stage type
at `λ_ξ` on finitely many points), the eventual top grade `K` of a model with no rigid core, and
hollow unbounded growth. -/
abbrev TerminalProperty (ξ : Ordinal.{0}) :=
  (Σ n, StageType.{0} (blockStage ξ) n) ⊕ ℕ ⊕ Unit

/-- **The terminal properties are countable** at every countable block. -/
theorem countable_terminalProperty {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    Countable (TerminalProperty ξ) :=
  have := StageType.countable_of_lt_omega_one (blockStage_lt_omega_one hξ)
  inferInstance

namespace Realization

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

variable (R) in
/-- A realization at `λ_ξ` **has the terminal property** `P`:

* `inl ⟨n, p⟩`: some cover of `p` is a globally rigid core;
* `inr (inl K)`: no cover is a globally rigid core, and the top-grade supremum is `K`;
* `inr (inr ())`: the realization is cover-hollow, and the top-grade supremum is `⊤`. -/
def HasTerminalProperty : TerminalProperty ξ → Prop
  | .inl ⟨_, p⟩ => ∃ c, R.Covers p c ∧ R.IsGloballyRigidCore c
  | .inr (.inl K) => (¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M),
      R.Covers p c ∧ R.IsGloballyRigidCore c) ∧ R.topGradeSup = K
  | .inr (.inr ()) => R.IsCoverHollow ∧ R.topGradeSup = ⊤

end Realization

/-- **The continuation criterion**, output 3 of higher-stage reconstruction in its sufficiency
direction, still to be proved: a model at `λ_ξ`, for `ξ < ω₁`, that is not cover-hollow and has
top-grade supremum `⊤` is the stage reduction of a model at `λ_{ξ+1}` on the same carrier.  Its
intended derivation rests on output 1b (lawfulness of the stable candidate), (R4) of the table of
Layer 3 with its empty-root base case, and the apex coatom extension property at `λ_{ξ+1}`; none
of these is proved.  The converse is not part of the criterion. -/
structure ContinuationCriterion : Prop where
  /-- A model that is not cover-hollow and has unbounded top-grade growth is the reduction of a
  model at the next block stage. -/
  exists_model ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) :
    ξ < ω₁ → R.IsModel → ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∃ R' : Realization.{0, w} (blockStage (ξ + 1)) M, R'.IsModel ∧
        R'.reduce (isSuccPrelimit_blockStage ξ) = R

namespace Realization

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **The cover of the terminal models**: under the continuation criterion, every model at `λ_ξ`,
for `ξ < ω₁`, that is terminal at `ξ` has some terminal property.  With unbounded growth it is
cover-hollow, since otherwise the criterion contradicts terminality; with top-grade supremum `K`
it has a globally rigid core or is residual. -/
theorem exists_hasTerminalProperty (hcont : ContinuationCriterion.{w}) (hξ : ξ < ω₁)
    (hR : R.IsModel) (ht : R.IsTerminalAt ξ) : ∃ P, R.HasTerminalProperty P := by
  by_cases htop : R.topGradeSup = ⊤
  · refine ⟨.inr (.inr ()), not_not.mp fun hhol ↦ ?_, htop⟩
    obtain ⟨R', hR', hred⟩ := hcont.exists_model R hξ hR hhol htop
    exact ht R' hR' hred
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp htop
  by_cases hcore : ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M),
      R.Covers p c ∧ R.IsGloballyRigidCore c
  · obtain ⟨k, p, hp⟩ := hcore
    exact ⟨.inl ⟨k, p⟩, hp⟩
  · exact ⟨.inr (.inl K), hcore, hK.symm⟩

/-- **Positivity of the residual top grade**: in a model with the residual property `K`, `K ≠ 0`.
For top-grade supremum `0`, the empty tuple covers a stage type on no points and is a globally
rigid core. -/
theorem topGradeSup_ne_zero_of_residual (hR : R.IsModel) {K : ℕ}
    (h : R.HasTerminalProperty (.inr (.inl K))) : K ≠ 0 := by
  rintro rfl
  obtain ⟨p, hp⟩ := hR.exists_covers_zero
  exact h.1 ⟨0, p, ![], hp,
    (hR.isGloballyRigidCore_empty_iff (isSuccLimit_blockStage ξ)).mpr (by exact_mod_cast h.2)⟩

/-- **Top-free models have the rigid-core property on no points**: a model whose actual types are
top-free has the property `inl ⟨0, p⟩` for the stage type `p` on no points. -/
theorem hasTerminalProperty_inl_zero_of_isTopFree (hR : R.IsModel)
    (h : ∀ x : R.Occurrence, x.type.IsTopFree) (p : StageType.{0} (blockStage ξ) 0) :
    R.HasTerminalProperty (.inl ⟨0, p⟩) := by
  obtain ⟨q, hq⟩ := hR.exists_covers_zero
  exact ⟨![], StageType.eq_of_zero q p ▸ hq, isGloballyRigidCore_of_forall_isTopFree h _⟩

/-- **Top-free realizations do not have the hollow property**: their top-grade supremum is `0`,
not `⊤`, although they are cover-hollow vacuously. -/
theorem not_hasTerminalProperty_hollow_of_isTopFree (h : ∀ x : R.Occurrence, x.type.IsTopFree) :
    ¬ R.HasTerminalProperty (.inr (.inr ())) := fun hP ↦ by
  simp [HasTerminalProperty, topGradeSup_eq_zero_iff.mpr h] at hP

end Realization

end VaughtConjecture
