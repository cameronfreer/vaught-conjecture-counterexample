/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.IntegerBlock
import VaughtConjecture.Continuation.ExactAge

/-!
# Conditions built by completed blocks

A second construction of a realization of cardinality `ℵ₁`, beside the one-point construction:
the realization is built in **phases**, each phase appending one **completed block** (a block of
new points of order type `ω*`, `ω` or `ℤ`, with all its cuts closed) above everything built
before, and each phase serving **one request** at **one designated serving point** of its block.
Everything in this file is self-contained: it uses neither the carrier nor the conditions of the
one-point construction, and its names live in the namespace `VaughtConjecture.AlephOne.Phase`.

**Shapes.**  A block has a shape (`Phase.BlockShape`): descending, ascending or integer, with index
order `ℕᵒᵈ`, `ℕ` or `ℤ` (`Phase.BlockShape.Index`), and a designated serving index
(`Phase.BlockShape.servingIndex`): the first block point `y_0` of a descending block, and the
first ascending point `a_0` of an ascending or integer block.

**Closedness without the closure operator.**  A set `C` is *support-closed* in a realization
(`Phase.IsSupportClosed`) when every finite subset of `C` lies in the points of a typed tuple whose
points lie in `C`.  For an exactly consistent covering realization this is closedness for the
canonical closure (`Phase.IsSupportClosedIffTarget`); it makes sense for the realization of a
condition, which is covering only on its domain, and it is kept by every extension that keeps the
evaluations.

**Requests and service.**  A request (`Phase.PhaseRequest`) is a tuple with a one-point donor.  A
realization serves it at a point `a` over a set `D` (`Phase.ServesAt`) when, if the tuple lies in
`D` and has a type of which the donor is a top-free coface, the tuple followed by `a` has the donor
as its type.

**Completed phases** (`Phase.IsCompletedPhase`).  A realization `S` on `N` with an embedding
`ι : M ↪ N` and an enumeration `z` of the new points by the index of a shape is a completed phase
over `R` on `M` when `S` is exactly consistent, covering, with legal top-free types, keeps every
evaluation of `R` along `ι` (`none` included), and the range of `ι` and every cut
`range ι ∪ z '' Iic j` are support-closed.

**Phase conditions** (`Phase.PhaseCondition`).  For a linear order `Φ` of phases, a shape and a
request for every phase, a phase condition on a carrier `X` is a lower set of completed phases, a
block enumeration of each phase, injective with pairwise disjoint ranges, and one realization on
`X` that types no tuple leaving the union of the blocks, is exactly consistent, covers every tuple
inside it, has legal top-free types, has the union of the earlier blocks and every cut of each
block over it support-closed, and serves the request of each phase at its designated serving
point over the union of the earlier blocks.  Phase conditions are preordered by extension
(`Phase.PhaseCondition.Extends`).

**The statements.**  All are stated; none is proved in this file.

* `Phase.IsSupportClosedIffTarget` (given-realization): support-closed is closed.
* `Phase.ExistsCompletedPhaseTarget` (construction over a given countable realization): a
  completed phase of any shape serving any one request over the old carrier.  For the ascending
  and integer shapes this is the content of `Realization.AscendingBlockServiceTarget` and
  `Realization.IntegerBlockServiceTarget` (under review); for the descending shape it needs a
  prescribed donor for `y_0` in the suffix charts.
* `Phase.CompletedPhaseOrderTarget` (given-realization): the exterior order of the block points of a
  completed phase above an infinite part of the old carrier is the order of the index.
* `Phase.PhaseConditionExtensionTarget`: a phase condition whose completed phases are those below
  `ξ`, with countable domain, extends to one whose completed phases are those at most `ξ`, with
  the new block on any prescribed countably infinite set of free points of the carrier.
* `Phase.PhaseChainUpperBoundTarget`: a nonempty chain of phase conditions has an upper bound whose
  completed phases are the union.
* `Phase.ExistsFullPhaseConditionTarget`: at stage `ω₁`, on the carrier `ω₁.ToType` with phases
  indexed by `ω₁.ToType`, every choice of shapes and requests has a phase condition in which every
  phase is completed and every point is a block point.
* `Phase.FullPhaseExactReceivingTarget`: for a request schedule that schedules every request at
  arbitrarily late phases, the realization of such a full phase condition has exact receiving
  within the legal top-free stage types.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (Stage 3, by
completed blocks); that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v w

namespace VaughtConjecture.AlephOne.Phase

open Ordinal Realization

/-! ### Shapes of blocks -/

/-- The **shape** of a completed block: descending (order type `ω*`), ascending (`ω`) or integer
(`ℤ`). -/
inductive BlockShape
  /-- A descending block, of order type `ω*`. -/
  | descending
  /-- An ascending block, of order type `ω`. -/
  | ascending
  /-- An integer block, of order type `ℤ`. -/
  | integer
  deriving DecidableEq

/-- The **index order** of a block of each shape: `ℕᵒᵈ`, `ℕ` or `ℤ`. -/
def BlockShape.Index : BlockShape → Type
  | .descending => ℕᵒᵈ
  | .ascending => ℕ
  | .integer => ℤ

/-- The index orders are linear orders. -/
instance BlockShape.instLinearOrderIndex : ∀ b : BlockShape, LinearOrder b.Index
  | .descending => inferInstanceAs (LinearOrder ℕᵒᵈ)
  | .ascending => inferInstanceAs (LinearOrder ℕ)
  | .integer => inferInstanceAs (LinearOrder ℤ)

/-- The **designated serving index** of a block: the first block point `y_0` of a descending block,
and the first ascending point `a_0` of an ascending or integer block. -/
def BlockShape.servingIndex : ∀ b : BlockShape, b.Index
  | .descending => OrderDual.toDual (0 : ℕ)
  | .ascending => (0 : ℕ)
  | .integer => (0 : ℤ)

/-! ### Support-closed sets, requests and service -/

section Service

variable {α : Ordinal.{u}} {X : Type v}

/-- A set `C` is **support-closed** in `R` when every finite subset of `C` lies in the points of a
typed tuple whose points lie in `C`. -/
def IsSupportClosed (R : Realization.{u, v} α X) (C : Set X) : Prop :=
  ∀ F : Finset X, ↑F ⊆ C → ∃ (n : ℕ) (t : Fin n ↪ X),
    (R.eval t).isSome ∧ ↑F ⊆ Set.range t ∧ Set.range t ⊆ C

/-- A **request**: a tuple with a one-point donor. -/
structure PhaseRequest (α : Ordinal.{u}) (X : Type v) where
  /-- The number of points of the tuple. -/
  arity : ℕ
  /-- The tuple. -/
  tuple : Fin arity ↪ X
  /-- The donor: a stage type on one more point. -/
  donor : StageType.{u} α (arity + 1)

/-- A request read along an embedding of carriers. -/
def PhaseRequest.map {Y : Type w} (ι : X ↪ Y) (r : PhaseRequest α X) : PhaseRequest α Y :=
  ⟨r.arity, r.tuple.trans ι, r.donor⟩

/-- `R` **serves the request `r` at the point `a` over `D`**: if the tuple of `r` lies in `D`,
does not contain `a`, and has a type `p` of which the donor is a top-free coface, then the tuple
followed by `a` has the donor as its type. -/
def ServesAt (R : Realization.{u, v} α X) (r : PhaseRequest α X) (D : Set X) (a : X) : Prop :=
  ∀ (ha : a ∉ Set.range r.tuple) (p : StageType.{u} α r.arity), Set.range r.tuple ⊆ D →
    R.eval r.tuple = some p → r.donor ∈ p.cofaces → r.donor.IsTopFree →
      R.eval (Fin.Embedding.snoc r.tuple ha) = some r.donor

/-- **Target: support-closed is closed** (given-realization).  In an exactly consistent covering
realization, a set is support-closed exactly when it is closed for the canonical closure.  Stated.
-/
def IsSupportClosedIffTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ (R : Realization.{u, v} α X) (hR : R.IsConsistent)
    (hc : R.IsCovering) (C : Set X), IsSupportClosed R C ↔ (R.closure hR hc).IsClosed C

end Service

/-! ### Completed phases -/

section CompletedPhase

variable {α : Ordinal.{u}} {M : Type v} {N : Type v}

/-- **A completed phase** over `R` on `M`: a realization `S` on `N`, an embedding `ι : M ↪ N`,
and an enumeration `z` of the new points by the index of the shape `b`, such that `S` is exactly
consistent, covering, with legal top-free types, keeps every evaluation of `R` along `ι` (`none`
included), `z` is injective with values exactly the points outside the range of `ι`, and the range
of `ι` and every cut `range ι ∪ z '' Iic j` are support-closed. -/
structure IsCompletedPhase (R : Realization.{u, v} α M) (S : Realization.{u, v} α N) (ι : M ↪ N)
    (b : BlockShape) (z : b.Index → N) : Prop where
  /-- Exact consistency. -/
  isConsistent : S.IsConsistent
  /-- Covering. -/
  isCovering : S.IsCovering
  /-- Legal types. -/
  hasLegalTypes : S.HasLegalTypes
  /-- Top-free types. -/
  hasTopFreeTypes : S.HasTopFreeTypes
  /-- Every old evaluation is kept, `none` included. -/
  eval_trans : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans ι) = R.eval t
  /-- The enumeration of the block is injective. -/
  injective : Function.Injective z
  /-- The block points are new. -/
  notMem_range : ∀ i, z i ∉ Set.range ι
  /-- Every point is old or a block point. -/
  mem_range_or : ∀ y, y ∈ Set.range ι ∨ y ∈ Set.range z
  /-- The old points form a support-closed set. -/
  isSupportClosed_range : IsSupportClosed S (Set.range ι)
  /-- Every cut of the block over the old points is support-closed. -/
  isSupportClosed_cut : ∀ j, IsSupportClosed S (Set.range ι ∪ z '' Set.Iic j)

/-- **Target: a completed phase serving one request.**  At a limit stage `α`, let `R` be an exactly
consistent covering realization with legal top-free types on a countable carrier `M`.  For every
shape `b` and every request `r` over `M`, some completed phase `(S, ι, z)` over `R` of shape `b`, on
a countable carrier, serves `r`, read along `ι`, at the designated serving point over the old
points.  Construction over a given realization.  Stated. -/
def ExistsCompletedPhaseTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes → ∀ (b : BlockShape) (r : PhaseRequest α M),
        ∃ (N : Type v) (_ : Countable N) (S : Realization.{u, v} α N) (ι : M ↪ N)
          (z : b.Index → N), IsCompletedPhase R S ι b z ∧
          ServesAt S (r.map ι) (Set.range ι) (z b.servingIndex)

/-- **Target: the order of a completed phase** (given-realization).  For a completed phase
`(S, ι, z)` over `R` and an infinite set `B` of old points, the block point `z i` lies in the
canonical closure of `ι '' B` with `z j` added exactly when `i ≤ j`.  Stated. -/
def CompletedPhaseOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type v⦄ (R : Realization.{u, v} α M)
    (S : Realization.{u, v} α N) (ι : M ↪ N) (b : BlockShape) (z : b.Index → N)
    (h : IsCompletedPhase R S ι b z) ⦃B : Set M⦄, B.Infinite →
      ∀ i j, z i ∈ S.closure h.isConsistent h.isCovering (insert (z j) (ι '' B)) ↔ i ≤ j

end CompletedPhase

/-! ### Phase conditions -/

section Conditions

variable {α : Ordinal.{u}} {X : Type v} {Φ : Type w} [LinearOrder Φ] {shape : Φ → BlockShape}

/-- The **points of a set of phases**: the union of the ranges of their block enumerations. -/
def phasePoints (P : Set Φ) (block : ∀ ξ, (shape ξ).Index → X) : Set X :=
  ⋃ ξ ∈ P, Set.range (block ξ)

/-- A **phase condition** on the carrier `X` for the shapes `shape` and the requests `req` of the
phases `Φ`: a lower set `phases` of completed phases, a block enumeration of each phase (injective
on completed phases, with pairwise disjoint ranges), and one realization `real` on `X` that types
no tuple leaving the points of the completed phases, is exactly consistent, covers every tuple
inside them, has legal top-free types, has the points of the earlier phases and every cut of each
block over them support-closed, and serves the request of each completed phase at its designated
serving point over the points of the earlier phases. -/
structure PhaseCondition (α : Ordinal.{u}) (X : Type v) (Φ : Type w) [LinearOrder Φ]
    (shape : Φ → BlockShape) (req : Φ → PhaseRequest α X) where
  /-- The completed phases. -/
  phases : Set Φ
  /-- The completed phases form a lower set. -/
  isLowerSet_phases : IsLowerSet phases
  /-- The block enumeration of each phase. -/
  block : ∀ ξ, (shape ξ).Index → X
  /-- The block enumerations of completed phases are injective. -/
  injective_block : ∀ ξ ∈ phases, Function.Injective (block ξ)
  /-- Distinct completed phases have disjoint blocks. -/
  disjoint_block : ∀ ξ ∈ phases, ∀ η ∈ phases, ξ ≠ η →
    Disjoint (Set.range (block ξ)) (Set.range (block η))
  /-- The realization. -/
  real : Realization.{u, v} α X
  /-- No tuple leaving the points of the completed phases is typed. -/
  eval_eq_none : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), ¬ Set.range t ⊆ phasePoints phases block →
    real.eval t = none
  /-- Exact consistency. -/
  isConsistent : real.IsConsistent
  /-- Covering of the tuples inside the points of the completed phases. -/
  isCovering : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ phasePoints phases block →
    ∃ (m : ℕ) (u : Fin m ↪ X) (f : Fin n ↪ Fin m), f.trans u = t ∧ (real.eval u).isSome
  /-- Legal types. -/
  hasLegalTypes : real.HasLegalTypes
  /-- Top-free types. -/
  hasTopFreeTypes : real.HasTopFreeTypes
  /-- The points of the phases before a completed phase form a support-closed set. -/
  isSupportClosed_before : ∀ ξ ∈ phases,
    IsSupportClosed real (phasePoints (phases ∩ Set.Iio ξ) block)
  /-- Every cut of a completed block over the earlier phases is support-closed. -/
  isSupportClosed_cut : ∀ ξ ∈ phases, ∀ j,
    IsSupportClosed real (phasePoints (phases ∩ Set.Iio ξ) block ∪ block ξ '' Set.Iic j)
  /-- Each completed phase serves its request at its designated serving point. -/
  serves : ∀ ξ ∈ phases, ServesAt real (req ξ) (phasePoints (phases ∩ Set.Iio ξ) block)
    (block ξ (shape ξ).servingIndex)

namespace PhaseCondition

variable {req : Φ → PhaseRequest α X}

/-- The **domain** of a phase condition: the points of its completed phases. -/
def dom (c : PhaseCondition α X Φ shape req) : Set X :=
  phasePoints c.phases c.block

/-- **Extension of phase conditions**: the completed phases grow, the blocks of the old completed
phases are kept, and so are the evaluations of the tuples inside the old domain, `none`
included. -/
def Extends (c c' : PhaseCondition α X Φ shape req) : Prop :=
  c.phases ⊆ c'.phases ∧ (∀ ξ ∈ c.phases, c'.block ξ = c.block ξ) ∧
    ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ c.dom → c'.real.eval t = c.real.eval t

end PhaseCondition

/-- **Target: extension of a phase condition by one completed phase.**  At a limit stage, let `c`
be a phase condition whose completed phases are those below `ξ` and whose domain is countable.
For every countably infinite set `Y` of points outside the domain, `c` extends to a phase condition
whose completed phases are those at most `ξ` and whose domain is the old domain together with `Y`
(the block of phase `ξ` is `Y`).  Stated. -/
def PhaseConditionExtensionTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X), Order.IsSuccLimit α →
    ∀ (c : PhaseCondition α X Φ shape req) (ξ : Φ), c.phases = Set.Iio ξ → c.dom.Countable →
      ∀ ⦃Y : Set X⦄, Y ⊆ c.domᶜ → Y.Countable → Y.Infinite →
        ∃ c' : PhaseCondition α X Φ shape req, c.Extends c' ∧ c'.phases = Set.Iic ξ ∧
          c'.dom = c.dom ∪ Y

/-- **Target: upper bounds of chains of phase conditions.**  A nonempty chain of phase conditions
for the extension preorder has an upper bound whose completed phases are the union of theirs.
Stated. -/
def PhaseChainUpperBoundTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (C : Set (PhaseCondition α X Φ shape req)), C.Nonempty →
      IsChain PhaseCondition.Extends C →
        ∃ c' : PhaseCondition α X Φ shape req, (∀ c ∈ C, c.Extends c') ∧
          c'.phases = ⋃ c ∈ C, c.phases

/-- **Target: a full phase condition.**  At stage `ω₁`, on the carrier `ω₁.ToType` with phases
indexed by `ω₁.ToType`, for every choice of shapes and requests some phase condition has every
phase completed and every point of the carrier as a block point.  Stated. -/
def ExistsFullPhaseConditionTarget : Prop :=
  ∀ (shape : (ω₁ : Ordinal.{0}).ToType → BlockShape)
    (req : (ω₁ : Ordinal.{0}).ToType →
      PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType),
    ∃ c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType shape req, c.phases = Set.univ ∧ c.dom = Set.univ

/-- **Target: exact top-free receiving for a full phase condition.**  At stage `ω₁`, on the
carrier `ω₁.ToType` with phases indexed by `ω₁.ToType`, if every request is scheduled at
arbitrarily late phases, the realization of a phase condition with every phase completed and every
point a block point has exact receiving within the legal top-free stage types.  Stated. -/
def FullPhaseExactReceivingTarget : Prop :=
  ∀ (shape : (ω₁ : Ordinal.{0}).ToType → BlockShape)
    (req : (ω₁ : Ordinal.{0}).ToType →
      PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType),
    (∀ (r : PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
      (ξ : (ω₁ : Ordinal.{0}).ToType), ∃ η, ξ ≤ η ∧ req η = r) →
    ∀ c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType shape req, c.phases = Set.univ → c.dom = Set.univ →
      c.real.ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.IsTopFree}

end Conditions

end VaughtConjecture.AlephOne.Phase
