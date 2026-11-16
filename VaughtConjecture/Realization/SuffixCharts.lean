/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.OptionAttachment
import VaughtConjecture.Extension.TowerTransfer

/-!
# Finite suffix charts over a chain of occurrences

The finite charts of a descending block over a realization `R` on `M`.  The carrier of the block is
`M ⊕ ℕ`: the old points `Sum.inl a` and the block points `y_j = Sum.inr j`.

**Suffix charts.**  A *suffix chart* over an occurrence `x` of `R` with `k` block points
(`Realization.IsSuffixChart`) is a tuple `w` of `M ⊕ ℕ` with a legal top-free stage type `T`:

* `w` lists the old points of `x`, in the order of the tuple of `x`, followed by the block points
  `y_{k-1}, …, y_0`, newest first;
* `T` is a tower over the type of `x` along the old positions (`StageType.IsTowerOver`), so the
  old points carry the type that `R` gives them, literally;
* every *suffix face* — the old points of `x` with the block points `y_j` for `i ≤ j < k` — is a
  closed face of `T`.  These are the initial segments of `w` of length at least the arity of `x`,
  the stages of the tower, so this clause follows from the tower and the order of the block points
  (`StageType.IsTowerOver.exists_restrictFace_castLEEmb`); it is listed for use.

**The statement** (`Realization.ExistsSuffixChartsTarget`): along any monotone sequence `c` of
occurrences of an exactly consistent realization with legal top-free types, at a limit stage, there
are suffix charts over `c k` with `k` block points, each the face of the next along a literal face
map, as in `Realization.ChartChainRealizationTarget`.  No countability: exhaustion of the carrier
by the occurrences is used only for the union (`VaughtConjecture.AlephOne.DescendingBlock`).  The
intended proof is a recursion on `k`: chart `k + 1` is the tower transfer
(`StageType.exists_isTopFree_tower_transfer`) of chart `k` onto a top-free one-point coface of the
type of `c (k + 1)`, whose new point is `y_k`.  Stated, not proved.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.ChartChain`; it is used by the descending block of the `ℵ₁`
companion construction.
-/

universe u v

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {M : Type v}

/-- The **suffix points** from `i` to `k` over a finite set `F` of old points: the old points of
`F`, read in `M ⊕ ℕ`, and the block points `Sum.inr j` with `i ≤ j < k`. -/
def suffixPoints (F : Finset M) (i k : ℕ) : Set (M ⊕ ℕ) :=
  Sum.inl '' (F : Set M) ∪ Sum.inr '' Set.Ico i k

/-- A **suffix chart** over the occurrence `x` with `k` block points: the tuple `w` of `M ⊕ ℕ`
lists the old points of `x` in the order of its tuple, followed by the block points
`Sum.inr (k - 1), …, Sum.inr 0`, newest first; the stage type `T` is legal, top-free, a tower over
the type of `x` along the old positions, and every suffix face (the old points of `x` with the block
points `Sum.inr j`, `i ≤ j < k`) is a closed face of `T`. -/
structure IsSuffixChart (R : Realization.{u, v} α M) (x : R.Occurrence) (k : ℕ) {N : ℕ}
    (w : Fin N ↪ M ⊕ ℕ) (T : StageType.{u} α N) : Prop where
  /-- The chart is legal. -/
  isLegal : T.IsLegal
  /-- The chart is top-free. -/
  isTopFree : T.IsTopFree
  /-- The chart has the old points of `x` and `k` block points. -/
  arity_eq : N = x.arity + k
  /-- The chart is a tower over the type of `x` along the old positions, which list the tuple of
  `x`. -/
  exists_isTowerOver : ∃ o : Fin x.arity ↪ Fin N,
    o.trans w = x.tuple.trans Function.Embedding.inl ∧ StageType.IsTowerOver x.type o T
  /-- After the old positions, the block points come newest first. -/
  apply_block : ∀ (s : ℕ) (hs : x.arity + s < N), w ⟨x.arity + s, hs⟩ = Sum.inr (k - 1 - s)
  /-- Every suffix face is a closed face. -/
  exists_suffix_face : ∀ i ≤ k, ∃ (r : ℕ) (f : Fin r ↪ Fin N),
    Set.range (f.trans w) = suffixPoints x.support i k ∧ (StageType.restrictFace f T).isSome

/-- **Target: coherent suffix charts along a chain of occurrences.**  At a limit stage `α`, let
`R` be an exactly consistent realization with legal top-free types on `M`, and `c` a monotone
sequence of occurrences of `R`.  There are tuples `w k` of `M ⊕ ℕ` with stage types `T k`, each a
suffix chart over `c k` with `k` block points (`Realization.IsSuffixChart`), and each chart the
face of the next along a literal face map (`g.trans (w (k + 1)) = w k`, restriction `T k`).  No
countability, and the occurrences need not exhaust `M`.  Construction over a given realization.
Stated. -/
def ExistsSuffixChartsTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (R : Realization.{u, v} α M),
    R.IsConsistent → R.HasLegalTypes → R.HasTopFreeTypes →
    ∀ (c : ℕ → R.Occurrence), Monotone c →
      ∃ (N : ℕ → ℕ) (w : ∀ k, Fin (N k) ↪ M ⊕ ℕ) (T : ∀ k, StageType.{u} α (N k)),
        (∀ k, R.IsSuffixChart (c k) k (w k) (T k)) ∧
        ∀ k, ∃ g : Fin (N k) ↪ Fin (N (k + 1)), g.trans (w (k + 1)) = w k ∧
          StageType.restrictFace g (T (k + 1)) = some (T k)

end VaughtConjecture.Realization
