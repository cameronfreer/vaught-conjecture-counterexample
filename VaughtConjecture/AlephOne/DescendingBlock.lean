/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.ClosureCardinality
import VaughtConjecture.Realization.SuffixCharts

/-!
# The descending block

A block of new points of order type `ω*` above a realization `R` on `M`.  The carrier is `M ⊕ ℕ`,
with the old points `Sum.inl a` and the block points `y_j = Sum.inr j`.  The block is descending in
the exterior order: `y_0 > y_1 > y_2 > ⋯`.

**Suffix cuts.**  The suffix cut at `k` (`Realization.suffixCut`) is the set of old points with
the block points `y_j`, `k ≤ j`.  Every suffix cut is closed in the block; the prefix sets (old
points with `y_j`, `j < k`) need not be.

**The statements** (all stated, none proved):

* `Realization.DescendingBlockOfChainTarget`: over an exhaustive monotone sequence of occurrences
  of `R` (no countability), an exactly consistent covering realization `S` on `M ⊕ ℕ` with legal
  top-free types keeps every old evaluation, `none` included, and has every suffix cut closed.
  Intended proof: the suffix charts of `Realization.ExistsSuffixChartsTarget` along the sequence,
  realized by `Realization.ChartChainRealizationTarget`; a finite subset of a suffix cut lies in a
  suffix face of some chart, a closed face, whose points form a support of `S`, so its hull stays
  in the cut (`finiteHull_subset_of_isSupport`).
* `Realization.DescendingBlockTarget`: the same over a countable carrier `M`, through an exhaustive
  chain of occurrences (`Realization.ExistsExhaustiveOccurrenceChainTarget`).
* `Realization.DescendingBlockOrderTarget` (given-realization): if `S` keeps the typed tuples of
  `R` typed and has every suffix cut closed, then for every infinite `B ⊆ M`,
  `y_i ∈ cl(B ∪ {y_j}) ↔ j ≤ i`, every old point lies strictly before every block point, and a
  closed set of `R` is closed in `S`.  The order is `Closure.closedCutOrderTarget` with index
  `ℕᵒᵈ` (a lower cut of `ℕᵒᵈ` is an upper cut of `ℕ`) at the root of all old points, which is
  closed; the root `B` enters by root change (`Closure.exteriorRootChangeTarget`).

Countability is of the old carrier only, and only where an exhaustive chain is built; the stage is
any limit ordinal.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (block types of
the construction); that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v

namespace VaughtConjecture.Realization

variable {M : Type v}

/-- The **suffix cut** at `k` of `M ⊕ ℕ`: the old points and the block points `Sum.inr j` with
`k ≤ j`. -/
def suffixCut (k : ℕ) : Set (M ⊕ ℕ) :=
  Set.range Sum.inl ∪ Sum.inr '' Set.Ici k

/-- **Target: the descending block over an exhaustive chain.**  At a limit stage `α`, let `R` be
an exactly consistent realization with legal top-free types on `M`, and `c` a monotone sequence of
occurrences of `R` whose supports exhaust `M`.  Some exactly consistent covering realization `S`
with legal top-free types on `M ⊕ ℕ` gives every tuple of old points its evaluation in `R`, `none`
included, and has every suffix cut closed for its canonical closure.  No countability.
Construction over a given realization.  Stated. -/
def DescendingBlockOfChainTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (R : Realization.{u, v} α M),
    R.IsConsistent → R.HasLegalTypes → R.HasTopFreeTypes →
    ∀ (c : ℕ → R.Occurrence), Monotone c → (∀ a : M, ∃ k, a ∈ (c k).support) →
      ∃ (S : Realization.{u, v} α (M ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        ∀ k, (S.closure hS hSc).IsClosed (suffixCut k)

/-- **Target: the descending block over a countable realization.**  At a limit stage `α`, let `R`
be an exactly consistent covering realization with legal top-free types on a countable carrier
`M`.  Some exactly consistent covering realization `S` with legal top-free types on `M ⊕ ℕ` gives
every tuple of old points its evaluation in `R`, `none` included, and has every suffix cut closed
for its canonical closure.  Countability is of the old carrier only.  Construction over a given
realization.  Stated. -/
def DescendingBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (S : Realization.{u, v} α (M ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        ∀ k, (S.closure hS hSc).IsClosed (suffixCut k)

/-- **Target: the order of a descending block** (given-realization).  Let `R` on `M` and `S` on
`M ⊕ ℕ` be exactly consistent and covering, let `S` give every typed tuple of `R`, read in
`M ⊕ ℕ`, the same type, and let every suffix cut be closed in `S`.  For every infinite `B ⊆ M`:

* the block is descending above `B`: `Sum.inr i` lies in the closure of `B` with `Sum.inr j`
  added exactly when `j ≤ i`;
* every old point lies strictly before every block point in the exterior relation of `B`;
* if `B` is closed for the canonical closure of `R`, it is closed in `S`.

About every pair of realizations satisfying the hypotheses; asserts no existence.  Stated. -/
def DescendingBlockOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} α M)
    (S : Realization.{u, v} α (M ⊕ ℕ)) (hR : R.IsConsistent) (hc : R.IsCovering)
    (hS : S.IsConsistent) (hSc : S.IsCovering),
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      S.eval (t.trans Function.Embedding.inl) = some p) →
    (∀ k, (S.closure hS hSc).IsClosed (suffixCut k)) →
    ∀ ⦃B : Set M⦄, B.Infinite →
      (∀ i j : ℕ, Sum.inr i ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ↔ j ≤ i) ∧
      (∀ (a : M) (j : ℕ), Sum.inl a ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ∧
        Sum.inr j ∉ S.closure hS hSc (insert (Sum.inl a) (Sum.inl '' B))) ∧
      ((R.closure hR hc).IsClosed B → (S.closure hS hSc).IsClosed (Sum.inl '' B))

end VaughtConjecture.Realization
