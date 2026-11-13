/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Hull

/-!
# Exhaustive chains of occurrences and of charts

Two statements about realizations built from an increasing sequence of finite pieces.

**An exhaustive chain of occurrences.**  In a covering realization on a countable carrier, every
occurrence begins a monotone sequence of occurrences whose supports exhaust the carrier
(`Realization.ExistsExhaustiveOccurrenceChainTarget`): the sets of occurrences whose support
contains a given point are dense, by covering (`Realization.IsCovering.exists_subset_support`),
and countably many dense sets are met by a chain
(`VaughtConjecture.Construction.exists_monotone_forall_exists_mem`).

**The realization of an exhaustive chain of charts.**  Let `w k` be injective tuples of a type `X`
with stage types `T k`, each `w k` a face of `w (k + 1)` along a literal face map `g` whose
restriction of `T (k + 1)` is `T k`, and let every point of `X` occur in some `w k`.  Then some
exactly consistent covering realization on `X` gives each `w k` the type `T k`, and every type it
assigns is the restriction of some `T k` along the face map of the tuple in `w k`
(`Realization.ChartChainRealizationTarget`).  The intended evaluation of a tuple is the restriction
of `T k` for the first `k` whose chart contains the tuple; it does not depend on `k`, by
`StageType.restrictFace_trans` along the face maps.  Neither the carrier nor the stage is assumed
countable.

Both statements are stated and open.

## Placement

This file belongs to Layer 0 of `roadmap/README.md` ("Countable construction and comparison"); it
is used by the exact countable attachment of the `ℵ₁` companion construction
(`VaughtConjecture.AlephOne.OptionAttachment`).
-/

universe u v

namespace VaughtConjecture.Realization

/-- **Target: an exhaustive chain of occurrences through a given occurrence.**  In a covering
realization on a countable carrier, every occurrence `x` begins a monotone sequence of occurrences
whose supports exhaust the carrier.  Stated; open. -/
def ExistsExhaustiveOccurrenceChainTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M] (R : Realization.{u, v} α M), R.IsCovering →
    ∀ x : R.Occurrence, ∃ c : ℕ → R.Occurrence, c 0 = x ∧ Monotone c ∧
      ∀ a : M, ∃ k, a ∈ (c k).support

/-- **Target: the realization of an exhaustive chain of charts.**  Let `w k` be injective tuples
of a type `X` with stage types `T k`, each the face of the next along a literal face map `g`
(`g.trans (w (k + 1)) = w k`, and the restriction of `T (k + 1)` along `g` is `T k`), and let every
point of `X` occur in some `w k`.  Then some exactly consistent covering realization `S` on `X`
gives each `w k` the type `T k`, and every type `p` that `S` assigns to a tuple `t` is the
restriction of some `T k` along a face map `f` with `f.trans (w k) = t`.  No countability of `X`
or of the stage.  Stated; open. -/
def ChartChainRealizationTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ (N : ℕ → ℕ) (w : ∀ k, Fin (N k) ↪ X)
    (T : ∀ k, StageType.{u} α (N k)),
    (∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
      StageType.restrictFace g (T (k + 1)) = some (T k)) →
    (∀ x : X, ∃ k, x ∈ Set.range (w k)) →
      ∃ S : Realization.{u, v} α X, S.IsConsistent ∧ S.IsCovering ∧
        (∀ k, S.eval (w k) = some (T k)) ∧
        ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X) (p : StageType.{u} α n), S.eval t = some p →
          ∃ (k : ℕ) (f : Fin n ↪ Fin (N k)), f.trans (w k) = t ∧
            StageType.restrictFace f (T k) = some p

end VaughtConjecture.Realization
