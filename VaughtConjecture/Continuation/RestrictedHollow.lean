/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Classification
import VaughtConjecture.Continuation.Comparison

/-!
# Cover-hollowness without a globally rigid core, and the restricted terminal properties

Roadmap, Layer 3 ((R3) of the table of 3.4, exact hollow-growth receiving) and Layer 4 (the
terminal classification and the hollow comparison); semantic contract, item 8.

**The predicate.**  A realization `R` at a block stage `λ_ξ` is **cover-hollow without a globally
rigid core** (`Realization.IsCoverHollowWithoutRigidCore`) when it is cover-hollow
(`Realization.IsCoverHollow`) and no cover in it is a globally rigid core
(`Realization.IsGloballyRigidCore`).  As (R3) takes a predicate on realizations at every stage, a
realization at `α` is **cover-hollow without a globally rigid core at a block stage**
(`Realization.IsCoverHollowWithoutRigidCoreAtBlock`) when it is cover-hollow at a block stage
(`Realization.IsCoverHollowAtBlock`) and no cover in it is a globally rigid core; at `λ_ξ` this is
the predicate above (`Realization.isCoverHollowWithoutRigidCoreAtBlock_iff`).  Cover-hollowness
itself, and the hollow property of `Realization.HasTerminalProperty`, are unchanged.  The two
predicates differ: a model whose actual types are top-free is cover-hollow, and the empty tuple is
a globally rigid core of it (`VaughtConjecture.Continuation.RestrictedHollowExamples`).

**The restricted terminal properties** (`Realization.HasRestrictedTerminalProperty`).  The index
is that of the terminal properties (`TerminalProperty ξ`), and the rigid-core and residual clauses
are those of `Realization.HasTerminalProperty`.  The hollow clause asks, besides unbounded
top-grade growth, for cover-hollowness without a globally rigid core.  So:

* a restricted property is a property
  (`Realization.HasRestrictedTerminalProperty.hasTerminalProperty`);
* the restricted hollow property is the hollow property together with the absence of a globally
  rigid core (`Realization.hasRestrictedTerminalProperty_hollow_iff`), and a realization with a
  globally rigid core does not have it
  (`Realization.not_hasRestrictedTerminalProperty_hollow_of_isGloballyRigidCore`).

**The cover survives.**  A realization with some terminal property has some restricted one
(`Realization.exists_hasRestrictedTerminalProperty_of_hasTerminalProperty`, with no hypothesis):
the rigid-core and residual properties are restricted properties; a realization with the hollow
property and a globally rigid core covering `p` on `k` points has the rigid-core property
`inl ⟨k, p⟩`; and one with the hollow property and no globally rigid core has the restricted
hollow property.  Composed with the cover of the terminal models
(`Realization.exists_hasTerminalProperty`), every model at `λ_ξ`, `ξ < ω₁`, that is terminal at
`ξ` has some restricted terminal property, under the continuation criterion
(`Realization.exists_hasRestrictedTerminalProperty`).  The models moved from the hollow property
to a rigid-core property are compared by the rigid-core comparison
(`Realization.nonempty_equiv_of_isGloballyRigidCore`), which uses finite-extension receiving only,
that is, (R1).

**(R3) for the restricted predicate.**  With the restricted properties, the hollow comparison is
needed only for cover-hollow models without a globally rigid core, that is, (R3) for the
predicate `Realization.IsCoverHollowWithoutRigidCoreAtBlock`:
`Realization.HollowReceiving IsCoverHollowWithoutRigidCoreAtBlock`.  (R3) for cover-hollowness at a
block stage implies it (`Realization.HollowReceiving.withoutRigidCore`): the restricted hypothesis
is weaker than or equal to the unrestricted one.  That it is strictly weaker is not shown.  The
countable losses and the main theorem under the restricted hypothesis are in
`VaughtConjecture.Expansion.Losses` and `VaughtConjecture.MainTheorem.ModelExpansionDomains`.

**A risk for the unrestricted form (informal, not compiled).**  Under (R3) for cover-hollowness at
a block stage, in a cover-hollow model with unbounded growth, a globally rigid core covering a
stage type `t` receives every one-point coface `D` of `t` exactly, and its rigidity then makes the
root rigid in `D`.  So if every legal stage type at a block stage had a legal one-point coface in
which the root is not rigid, (R3) for cover-hollowness would force every cover-hollow model with
unbounded growth to have no globally rigid core.  Neither that property of the legal stage types
nor its consequence is proved; (R3) for cover-hollowness is not claimed to be false.  The
restricted form does not depend on this argument.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Ordinal

namespace Realization

/-! ### The predicate -/

section Predicate

variable {ξ : Ordinal.{u}} {M : Type w}

variable (R : Realization.{u, w} (blockStage ξ) M) in
/-- A realization at `λ_ξ` is **cover-hollow without a globally rigid core** when it is
cover-hollow and no cover in it is a globally rigid core. -/
def IsCoverHollowWithoutRigidCore : Prop :=
  R.IsCoverHollow ∧ ¬ ∃ (k : ℕ) (p : StageType.{u} (blockStage ξ) k) (c : Fin k → M),
    R.Covers p c ∧ R.IsGloballyRigidCore c

/-- A realization at `α` is **cover-hollow without a globally rigid core at a block stage** when
it is cover-hollow at a block stage and no cover in it is a globally rigid core. -/
def IsCoverHollowWithoutRigidCoreAtBlock {α : Ordinal.{u}} {M : Type w}
    (R : Realization.{u, w} α M) : Prop :=
  R.IsCoverHollowAtBlock ∧ ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M),
    R.Covers p c ∧ R.IsGloballyRigidCore c

/-- At a block stage, cover-hollowness without a globally rigid core at a block stage is
cover-hollowness without a globally rigid core. -/
theorem isCoverHollowWithoutRigidCoreAtBlock_iff {R : Realization.{u, w} (blockStage ξ) M} :
    R.IsCoverHollowWithoutRigidCoreAtBlock ↔ R.IsCoverHollowWithoutRigidCore :=
  and_congr_left' isCoverHollowAtBlock_iff

/-- Cover-hollowness without a globally rigid core at a block stage gives cover-hollowness at a
block stage. -/
theorem IsCoverHollowWithoutRigidCoreAtBlock.isCoverHollowAtBlock {α : Ordinal.{u}}
    {R : Realization.{u, w} α M} (h : R.IsCoverHollowWithoutRigidCoreAtBlock) :
    R.IsCoverHollowAtBlock :=
  h.1

end Predicate

/-! ### (R3) for the restricted predicate -/

/-- **(R3) for cover-hollowness at a block stage gives (R3) for cover-hollowness without a
globally rigid core at a block stage**: the predicate is stronger, so the receiving statement for
it is weaker than or equal to the one for cover-hollowness. -/
theorem HollowReceiving.withoutRigidCore (hhol : HollowReceiving.{u, w} IsCoverHollowAtBlock) :
    HollowReceiving.{u, w} IsCoverHollowWithoutRigidCoreAtBlock where
  exists_covers _ _ _ hα hR hH htop := hhol.exists_covers hα hR hH.1 htop

/-! ### The restricted terminal properties -/

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

variable (R) in
/-- A realization at `λ_ξ` **has the restricted terminal property** `P`:

* `inl ⟨n, p⟩`: some cover of `p` is a globally rigid core;
* `inr (inl K)`: no cover is a globally rigid core, and the top-grade supremum is `K`;
* `inr (inr ())`: the realization is cover-hollow without a globally rigid core, and the
  top-grade supremum is `⊤`.

The first two clauses are those of `HasTerminalProperty`; the third also excludes a globally
rigid core. -/
def HasRestrictedTerminalProperty : TerminalProperty ξ → Prop
  | .inl ⟨_, p⟩ => ∃ c, R.Covers p c ∧ R.IsGloballyRigidCore c
  | .inr (.inl K) => (¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M),
      R.Covers p c ∧ R.IsGloballyRigidCore c) ∧ R.topGradeSup = K
  | .inr (.inr ()) => R.IsCoverHollowWithoutRigidCore ∧ R.topGradeSup = ⊤

/-- **A restricted terminal property is a terminal property.** -/
theorem HasRestrictedTerminalProperty.hasTerminalProperty {P : TerminalProperty ξ}
    (h : R.HasRestrictedTerminalProperty P) : R.HasTerminalProperty P := by
  rcases P with ⟨_, p⟩ | K | ⟨⟩
  · exact h
  · exact h
  · exact ⟨h.1.1, h.2⟩

/-- **The restricted hollow property** is the hollow property together with the absence of a
globally rigid core. -/
theorem hasRestrictedTerminalProperty_hollow_iff :
    R.HasRestrictedTerminalProperty (.inr (.inr ())) ↔
      R.HasTerminalProperty (.inr (.inr ())) ∧
        ¬ ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M),
          R.Covers p c ∧ R.IsGloballyRigidCore c :=
  ⟨fun h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩

/-- **A realization with a globally rigid core does not have the restricted hollow property.** -/
theorem not_hasRestrictedTerminalProperty_hollow_of_isGloballyRigidCore {k : ℕ}
    {p : StageType.{0} (blockStage ξ) k} {c : Fin k → M} (hc : R.Covers p c)
    (hcore : R.IsGloballyRigidCore c) : ¬ R.HasRestrictedTerminalProperty (.inr (.inr ())) :=
  fun h ↦ h.1.2 ⟨k, p, c, hc, hcore⟩

/-- **A realization with a terminal property has a restricted one**, with no hypothesis: the
rigid-core and residual properties are restricted ones; with the hollow property, a globally
rigid core covering `p` on `k` points gives the rigid-core property `inl ⟨k, p⟩`, and otherwise
the restricted hollow property holds. -/
theorem exists_hasRestrictedTerminalProperty_of_hasTerminalProperty {P : TerminalProperty ξ}
    (h : R.HasTerminalProperty P) : ∃ P', R.HasRestrictedTerminalProperty P' := by
  rcases P with ⟨k, p⟩ | K | ⟨⟩
  · exact ⟨.inl ⟨k, p⟩, h⟩
  · exact ⟨.inr (.inl K), h⟩
  · by_cases hcore : ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M),
        R.Covers p c ∧ R.IsGloballyRigidCore c
    · obtain ⟨k, p, hp⟩ := hcore
      exact ⟨.inl ⟨k, p⟩, hp⟩
    · exact ⟨.inr (.inr ()), hasRestrictedTerminalProperty_hollow_iff.mpr ⟨h, hcore⟩⟩

/-- **The cover of the terminal models by the restricted properties**: under the continuation
criterion, every model at `λ_ξ`, for `ξ < ω₁`, that is terminal at `ξ` has some restricted
terminal property.  A model with the hollow property and a globally rigid core has a rigid-core
property. -/
theorem exists_hasRestrictedTerminalProperty (hcont : ContinuationCriterion.{w}) (hξ : ξ < ω₁)
    (hR : R.IsModel) (ht : R.IsTerminalAt ξ) : ∃ P, R.HasRestrictedTerminalProperty P :=
  let ⟨_, hP⟩ := exists_hasTerminalProperty hcont hξ hR ht
  exists_hasRestrictedTerminalProperty_of_hasTerminalProperty hP

end Realization

end VaughtConjecture
