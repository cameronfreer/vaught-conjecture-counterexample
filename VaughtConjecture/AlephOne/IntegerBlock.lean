/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.DescendingBlock

/-!
# The ascending block and the block of order type `ℤ`

**The ascending block.**  A block of new points `a_0, a_1, …` of order type `ω` above a
realization on `X`, on the carrier `X ⊕ ℕ` with `a_j = Sum.inr j`.  The prefix cut at `n`
(`Realization.prefixCut`) is the set of old points with the block points `a_j`, `j < n`; every
prefix cut is closed (`Realization.AscendingBlockTarget`, over a countable carrier), and then
`a_i ∈ cl(B ∪ {a_j}) ↔ i ≤ j` for every infinite `B ⊆ X` (`Realization.AscendingBlockOrderTarget`,
given-realization; `Closure.closedCutOrderTarget` with index `ℕ`).  The intended proof of the
existence statement attaches `a_0, a_1, …` one at a time, each over the whole structure built so
far and keeping all of it: an evaluation-keeping extension has the old carrier closed
(`Realization.imageClosureOfEvalEmbeddingTarget`).  In finite charts this is the chart chain of
towers over the occurrences of an exhaustive chain with the block points oldest first, each chart
the tower transfer of the previous one followed by one top-free pinned extension.

**The block of order type `ℤ`.**  An ascending block after a descending block, on
`(M ⊕ ℕ) ⊕ ℕ`: the descending points `y_j = Sum.inl (Sum.inr j)` and the ascending points
`a_j = Sum.inr j`, enumerated by `ℤ` through `Realization.integerBlockPoint` (`a_n` at `n ≥ 0`,
`y_n` at `-(n + 1)`).  The integer cut at `z` (`Realization.integerCut`) is the set of old points
of `M` with the block points enumerated at most `z`: for `z = -(j + 1)` it is the image of the
suffix cut at `j` of the descending block, and for `z = n ≥ 0` the prefix cut at `n + 1` of the
ascending block.  Every integer cut is closed (`Realization.IntegerBlockTarget`), and then the
exterior relation above any infinite `B ⊆ M` is the order of `ℤ`
(`Realization.IntegerBlockOrderTarget`, given-realization; `Closure.closedCutOrderTarget` with
index `ℤ`, and root change).  The exterior order of the block is `ω* + ω`.

With a prescribed request: the ascending block whose first point realizes a given top-free donor
over a given occurrence (`Realization.AscendingBlockServiceTarget`), and the block of order type
`ℤ` whose first ascending point does so over an occurrence of the descending part
(`Realization.IntegerBlockServiceTarget`); one serving point per block.

All statements are stated, none proved.  Countability is of the old carrier only; the stage is
any limit ordinal.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (block types of
the construction); that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v

namespace VaughtConjecture.Realization

/-! ### The ascending block -/

section Ascending

variable {X : Type v}

/-- The **prefix cut** at `n` of `X ⊕ ℕ`: the old points and the block points `Sum.inr j` with
`j < n`. -/
def prefixCut (n : ℕ) : Set (X ⊕ ℕ) :=
  Set.range Sum.inl ∪ Sum.inr '' Set.Iio n

/-- **Target: the ascending block over a countable realization.**  At a limit stage `α`, let `R`
be an exactly consistent covering realization with legal top-free types on a countable carrier
`X`.  Some exactly consistent covering realization `S` with legal top-free types on `X ⊕ ℕ` gives
every tuple of old points its evaluation in `R`, `none` included, and has every prefix cut closed
for its canonical closure.  Countability is of the old carrier only.  Construction over a given
realization.  Stated. -/
def AscendingBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ [Countable X], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α X), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (S : Realization.{u, v} α (X ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        ∀ n, (S.closure hS hSc).IsClosed (prefixCut n)

/-- **Target: the order of an ascending block** (given-realization).  Let `S` on `X ⊕ ℕ` be
exactly consistent and covering with every prefix cut closed.  For every infinite `B ⊆ X`, the
block is ascending above `B` (`Sum.inr i` lies in the closure of `B` with `Sum.inr j` added
exactly when `i ≤ j`), and every old point lies strictly before every block point in the exterior
relation of `B`.  About every realization satisfying the hypotheses; asserts no existence.
Stated. -/
def AscendingBlockOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ (S : Realization.{u, v} α (X ⊕ ℕ)) (hS : S.IsConsistent)
    (hSc : S.IsCovering), (∀ n, (S.closure hS hSc).IsClosed (prefixCut n)) →
    ∀ ⦃B : Set X⦄, B.Infinite →
      (∀ i j : ℕ, Sum.inr i ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ↔ i ≤ j) ∧
      ∀ (a : X) (j : ℕ), Sum.inl a ∈ S.closure hS hSc (insert (Sum.inr j) (Sum.inl '' B)) ∧
        Sum.inr j ∉ S.closure hS hSc (insert (Sum.inl a) (Sum.inl '' B))

/-- A tuple `t` of old points, read in `X ⊕ ℕ`, followed by the block point `Sum.inr j`. -/
def appendBlockPoint {n : ℕ} (t : Fin n ↪ X) (j : ℕ) : Fin (n + 1) ↪ X ⊕ ℕ :=
  Fin.Embedding.snoc (t.trans Function.Embedding.inl) (a := Sum.inr j) (by simp)

/-- **Target: the ascending block with a prescribed request served.**  At a limit stage `α`, let
`R` be an exactly consistent covering realization with legal top-free types on a countable carrier
`X`, `x` an occurrence of `R` and `d` a top-free coface of its type.  Some exactly consistent
covering realization `S` with legal top-free types on `X ⊕ ℕ` gives every tuple of old points its
evaluation in `R`, `none` included, has every prefix cut closed, and gives the tuple of `x`
followed by the first block point `Sum.inr 0` the type `d`.  Intended proof: attach the first
block point by `Realization.optionAttachmentTarget`, attach the remaining block points by
`Realization.AscendingBlockTarget` over the result, and relabel `Option X ⊕ ℕ` as `X ⊕ ℕ` fixing
the old points.  Construction over a given realization.  Stated. -/
def AscendingBlockServiceTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ [Countable X], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α X), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes → ∀ (x : R.Occurrence), ∀ d ∈ x.type.cofaces, d.IsTopFree →
      ∃ (S : Realization.{u, v} α (X ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        (∀ n, (S.closure hS hSc).IsClosed (prefixCut n)) ∧
        S.eval (appendBlockPoint x.tuple 0) = some d

end Ascending

/-! ### The block of order type `ℤ` -/

section Integer

variable {M : Type v}

/-- The **point enumerated by an integer** in the block of order type `ℤ` on `(M ⊕ ℕ) ⊕ ℕ`: the
ascending point `Sum.inr n` at `n ≥ 0`, and the descending point `Sum.inl (Sum.inr n)` at
`-(n + 1)`. -/
def integerBlockPoint : ℤ → (M ⊕ ℕ) ⊕ ℕ
  | Int.ofNat n => Sum.inr n
  | Int.negSucc n => Sum.inl (Sum.inr n)

/-- The **integer cut** at `z`: the old points of `M` and the block points enumerated by integers
at most `z`. -/
def integerCut (z : ℤ) : Set ((M ⊕ ℕ) ⊕ ℕ) :=
  Set.range (fun a : M ↦ Sum.inl (Sum.inl a)) ∪ integerBlockPoint '' Set.Iic z

/-- **Target: the block of order type `ℤ` over a countable realization.**  At a limit stage `α`,
let `R` be an exactly consistent covering realization with legal top-free types on a countable
carrier `M`.  Some exactly consistent covering realization `U` with legal top-free types on
`(M ⊕ ℕ) ⊕ ℕ` gives every tuple of old points of `M` its evaluation in `R`, `none` included, and
has every integer cut closed for its canonical closure.  Intended proof: the ascending block
(`Realization.AscendingBlockTarget`) over the descending block
(`Realization.DescendingBlockTarget`), whose suffix cuts stay closed by
`Realization.imageClosureOfEvalEmbeddingTarget`.  Countability is of the old carrier only.
Construction over a given realization.  Stated. -/
def IntegerBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ)) (hU : U.IsConsistent) (hUc : U.IsCovering),
        U.HasLegalTypes ∧ U.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
          U.eval ((t.trans Function.Embedding.inl).trans Function.Embedding.inl) = R.eval t) ∧
        ∀ z, (U.closure hU hUc).IsClosed (integerCut z)

/-- **Target: the block of order type `ℤ` with a request served after the descending part.**  At a
limit stage `α`, let `R` be an exactly consistent covering realization with legal top-free types on
a countable carrier `M`.  Some exactly consistent covering realization `S` with legal top-free
types on `M ⊕ ℕ` (the descending part) gives every tuple of old points its evaluation in `R`,
`none` included, and has every suffix cut closed; and for every occurrence `x` of `S` and every
top-free coface `d` of its type, some exactly consistent covering realization `U` with legal
top-free types on `(M ⊕ ℕ) ⊕ ℕ` gives every tuple of `M ⊕ ℕ` its evaluation in `S`, `none`
included, has every integer cut closed, and gives the tuple of `x` followed by the first ascending
point `Sum.inr 0` the type `d`.  The request may involve descending points.  Intended proof:
`Realization.descendingBlockTarget`, then `Realization.AscendingBlockServiceTarget` over `S`; the
suffix cuts of `S` stay closed by `Realization.imageClosureOfEvalEmbeddingTarget`.  Construction
over a given realization.  Stated. -/
def IntegerBlockServiceTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes →
      ∃ (S : Realization.{u, v} α (M ⊕ ℕ)) (hS : S.IsConsistent) (hSc : S.IsCovering),
        S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.inl) = R.eval t) ∧
        (∀ k, (S.closure hS hSc).IsClosed (suffixCut k)) ∧
        ∀ (x : S.Occurrence), ∀ d ∈ x.type.cofaces, d.IsTopFree →
          ∃ (U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ)) (hU : U.IsConsistent)
            (hUc : U.IsCovering), U.HasLegalTypes ∧ U.HasTopFreeTypes ∧
            (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M ⊕ ℕ),
              U.eval (t.trans Function.Embedding.inl) = S.eval t) ∧
            (∀ z, (U.closure hU hUc).IsClosed (integerCut z)) ∧
            U.eval (appendBlockPoint x.tuple 0) = some d

/-- **Target: the order of a block of order type `ℤ`** (given-realization).  Let `U` on
`(M ⊕ ℕ) ⊕ ℕ` be exactly consistent and covering with every integer cut closed.  For every
infinite `B ⊆ M`, the block point enumerated by `i` lies in the closure of `B` with the block
point enumerated by `j` added exactly when `i ≤ j`, and every old point of `M` lies strictly before
every block point in the exterior relation of `B`.  About every realization satisfying the
hypotheses; asserts no existence.  Stated. -/
def IntegerBlockOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ (U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ))
    (hU : U.IsConsistent) (hUc : U.IsCovering),
    (∀ z, (U.closure hU hUc).IsClosed (integerCut z)) →
    ∀ ⦃B : Set M⦄, B.Infinite →
      (∀ i j : ℤ, integerBlockPoint i ∈ U.closure hU hUc
        (insert (integerBlockPoint j) ((fun a : M ↦ Sum.inl (Sum.inl a)) '' B)) ↔ i ≤ j) ∧
      ∀ (a : M) (j : ℤ), Sum.inl (Sum.inl a) ∈ U.closure hU hUc
          (insert (integerBlockPoint j) ((fun a : M ↦ Sum.inl (Sum.inl a)) '' B)) ∧
        integerBlockPoint j ∉ U.closure hU hUc
          (insert (Sum.inl (Sum.inl a)) ((fun a : M ↦ Sum.inl (Sum.inl a)) '' B))

end Integer

end VaughtConjecture.Realization
