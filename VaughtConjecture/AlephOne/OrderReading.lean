/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.PhaseModel
import VaughtConjecture.Order.CodedOrder
import VaughtConjecture.Realization.ClosureCardinality

/-!
# Reading the coded order from a full phase condition

For a phase condition built by completed blocks (`VaughtConjecture.AlephOne.PhaseConditions`) in
which every phase is completed and every point is a block point, the exterior order above the
first block is the coded order of the shapes (`VaughtConjecture.Order.CodedOrder`) with its first
block removed, read with the original phase indices.

**Shapes and bits.**  The bit of a shape (`Phase.BlockShape.bit`) follows the convention of
`CodedOrder`, whose block at a bit `false` is `ℕ` and at a bit `true` is `ℤ`: an ascending block
(index order `ℕ`) has bit `false` and an integer block (index order `ℤ`) has bit `true`.  The
position in `ℤ` of an index (`Phase.BlockShape.posOfIndex`) and the index at a position
(`Phase.BlockShape.indexOfPos`, total: a negative position of an ascending block is read as
index `0`) identify the index order of a shape with the positions that `CodedOrder` allows at its
bit.  `Phase.shapeBits shape` is the bit sequence of the shapes of the phases; for the shapes
`BlockShape.ofBit ∘ A ∘ r` of a parameter `A` along a repetition scheme `r` it is `A ∘ r`, the bit
sequence of `CodedOrder.tailEquivalentInjectiveTarget`.

**The tail.**  For a phase `ξ₀`, `Phase.codedTail b ξ₀` is the set of points of `CodedOrder b` of
rank strictly above `ξ₀`, a subset of the coded order itself (not a coded order over a smaller
index set), so the original phase indices are kept.  It is an upper set because the rank is
monotone, and nonempty as soon as some phase lies above `ξ₀`: a tail in the sense of
`Order.TailEquivalent`.

**The block enumeration as a map from the coded order.**  `Phase.PhaseCondition.codedPoint c x` is
the block point of the phase `rank x` at the index of the position `pos x`.  Above the first phase
`ξ₀` (a least phase), the root is the first block `Set.range (c.block ξ₀)`, and the exterior
relation is the one of `Realization.ExteriorOrderIsLinearTarget`, written inline exactly as there:
`x.1 ∈ R.closure hR hc (insert y.1 B)` on the points outside `B`.  No second exterior relation and
no `LinearOrder` instance on the exterior are introduced; an order isomorphism onto the exterior is
a relation isomorphism (`RelIso`) from `≤` on the tail to the exterior relation
(`Phase.PhaseCondition.HasOrderReading`).

**The statements** (all stated, none proved).

* `Phase.ShapeBitTarget`: the shape ↔ bit ↔ index correspondence.
* `Phase.CodedTailIsTailTarget` (pure order): the tail above a phase is an upper set, nonempty
  exactly when some phase lies above it.
* `Phase.RootBlockTarget` (given-condition): the first block of a full phase condition is
  countable, infinite and closed for the canonical closure.
* `Phase.CodedPointInjectiveTarget` (given-condition): the block enumeration read on the coded
  order is injective.
* `Phase.CodedPointNotMemRootTarget` (given-condition): the tail is carried outside the root.
* `Phase.CodedPointCutClosedTarget` (given-condition): the root together with the image of the part
  of the tail at or below a point is closed: the hypothesis of `Closure.closedCutOrderTarget` for
  the enumeration of the exterior by the tail.
* `Phase.CodedPointOrderTarget` (given-condition, the comparison clause): a tail point is below
  another in the exterior relation exactly when it is below it in the coded order, within and
  between blocks.
* `Phase.CodedPointSurjectiveTarget` (given-condition): every point outside the root is the block
  point of a tail point.
* `Phase.TailOrderIsoExteriorTarget` (given-condition, any stage, carrier and phases): a full phase
  condition has the order reading above a least phase.
* `Phase.OmegaOneOrderReadingTarget` (given-condition, at `ω₁`): above the first phase
  `Phase.firstPhase` the root is countably infinite and closed, the tail is a nonempty upper set,
  and the order reading holds.
* `Phase.ExistsOmegaOneOrderReadingTarget` (existence, at `ω₁`): for every choice of shapes, a full
  phase condition whose realization is a receiving model with top-free types and has the order
  reading above the first phase.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (Stage 3, by
completed blocks); that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v w

namespace VaughtConjecture.AlephOne.Phase

open Ordinal Realization

/-! ### Shapes and bits -/

/-- The **bit** of a shape, in the convention of `CodedOrder`: an ascending block (index order
`ℕ`) has bit `false`, an integer block (index order `ℤ`) has bit `true`. -/
def BlockShape.bit : BlockShape → Bool
  | .ascending => false
  | .integer => true

/-- The **shape of a bit**: `false` gives an ascending block, `true` an integer block. -/
def BlockShape.ofBit : Bool → BlockShape
  | false => .ascending
  | true => .integer

/-- The **position** in `ℤ` of an index of a block: the index itself, read in `ℤ`. -/
def BlockShape.posOfIndex : ∀ s : BlockShape, s.Index → ℤ
  | .ascending, i => ((show ℕ from i) : ℤ)
  | .integer, i => show ℤ from i

/-- The **index at a position** of a block: the position itself for an integer block, and its
natural truncation for an ascending block (only nonnegative positions occur in an `ℕ`-block of
`CodedOrder`). -/
def BlockShape.indexOfPos : ∀ s : BlockShape, ℤ → s.Index
  | .ascending, n => n.toNat
  | .integer, n => n

/-- The **bit sequence of the shapes** of the phases. -/
def shapeBits {Φ : Type w} (shape : Φ → BlockShape) : Φ → Bool := fun ξ ↦ (shape ξ).bit

/-- **Target: shapes, bits and indices correspond** (stated).  The bit of an ascending shape is
`false` and of an integer shape `true`; `BlockShape.bit` and `BlockShape.ofBit` are inverse; the
bits of the shapes `ofBit ∘ b` are `b`; the position of an index is strictly monotone, its values
are exactly the positions allowed by `CodedOrder` at the bit of the shape (nonnegative at bit
`false`), and the index at a position inverts it on those positions. -/
def ShapeBitTarget : Prop :=
  BlockShape.ascending.bit = false ∧ BlockShape.integer.bit = true ∧
    (∀ s : BlockShape, BlockShape.ofBit s.bit = s) ∧
    (∀ β : Bool, (BlockShape.ofBit β).bit = β) ∧
    (∀ ⦃Φ : Type w⦄ (b : Φ → Bool), shapeBits (fun ξ ↦ BlockShape.ofBit (b ξ)) = b) ∧
    (∀ s : BlockShape, StrictMono s.posOfIndex) ∧
    (∀ (s : BlockShape) (n : ℤ), n ∈ Set.range s.posOfIndex ↔ (s.bit = false → 0 ≤ n)) ∧
    (∀ (s : BlockShape) (i : s.Index), s.indexOfPos (s.posOfIndex i) = i) ∧
    (∀ (s : BlockShape) (n : ℤ), (s.bit = false → 0 ≤ n) → s.posOfIndex (s.indexOfPos n) = n)

/-! ### The tail above a phase -/

/-- The **tail above a phase** `ξ₀` of a coded order: the points of rank strictly above `ξ₀`, as a
subset of the coded order itself, keeping the original indices. -/
def codedTail {I : Type w} [LinearOrder I] (b : I → Bool) (ξ₀ : I) : Set (CodedOrder b) :=
  CodedOrder.rank ⁻¹' Set.Ioi ξ₀

/-- **Target: the tail above a phase is a tail** (stated; pure order).  It is an upper set of the
coded order (the rank is monotone), and it is nonempty exactly when some index lies above
`ξ₀`. -/
def CodedTailIsTailTarget : Prop :=
  ∀ ⦃I : Type w⦄ [LinearOrder I] (b : I → Bool) (ξ₀ : I),
    IsUpperSet (codedTail b ξ₀) ∧ ((codedTail b ξ₀).Nonempty ↔ ∃ ξ, ξ₀ < ξ)

/-! ### The block enumeration on the coded order -/

section Reading

variable {α : Ordinal.{u}} {X : Type v} {Φ : Type w} [LinearOrder Φ] {shape : Φ → BlockShape}
  {req : Φ → PhaseRequest α X}

/-- The **block point of a point of the coded order**: the point of the block of phase `rank x`
at the index of the position `pos x`. -/
def PhaseCondition.codedPoint (c : PhaseCondition α X Φ shape req)
    (x : CodedOrder (shapeBits shape)) : X :=
  c.block (CodedOrder.rank x) ((shape (CodedOrder.rank x)).indexOfPos (CodedOrder.pos x))

/-- **The order reading** of a phase condition above the phase `ξ₀`: an order isomorphism from the
tail of the coded order of the shapes above `ξ₀` onto the whole exterior of the first block
`Set.range (c.block ξ₀)`, with the exterior relation of `Realization.ExteriorOrderIsLinearTarget`
(a relation isomorphism from `≤` on the tail), given on every tail point by its block point. -/
def PhaseCondition.HasOrderReading (c : PhaseCondition α X Φ shape req)
    (hc : c.real.IsCovering) (ξ₀ : Φ) : Prop :=
  ∃ e : (· ≤ · : codedTail (shapeBits shape) ξ₀ → codedTail (shapeBits shape) ξ₀ → Prop) ≃r
      (fun x y : {x : X // x ∉ Set.range (c.block ξ₀)} ↦
        x.1 ∈ c.real.closure c.isConsistent hc (insert y.1 (Set.range (c.block ξ₀)))),
    ∀ x, (e x).1 = c.codedPoint x.1

end Reading

/-! ### The given-condition targets -/

/-- **Target: the first block is a countably infinite closed root** (stated; given-condition).  In
a phase condition with every phase completed and a covering realization, the block of a least
phase `ξ₀` is countable, infinite (its enumeration is injective), and closed for the canonical
closure (the union of its closed cuts, directed by the index). -/
def RootBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ), IsBot ξ₀ →
    c.phases = Set.univ → ∀ hc : c.real.IsCovering,
      (Set.range (c.block ξ₀)).Countable ∧ (Set.range (c.block ξ₀)).Infinite ∧
        (c.real.closure c.isConsistent hc).IsClosed (Set.range (c.block ξ₀))

/-- **Target: the block enumeration is injective on the coded order** (stated; given-condition).
With every phase completed, distinct points of the coded order of the shapes have distinct block
points: blocks of distinct phases are disjoint, each block enumeration is injective, and the index
at a position is injective on the positions allowed at the bit. -/
def CodedPointInjectiveTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req),
    c.phases = Set.univ → Function.Injective c.codedPoint

/-- **Target: the tail is carried outside the root** (stated; given-condition).  With every phase
completed, the block point of a point of rank above `ξ₀` is not in the block of `ξ₀`. -/
def CodedPointNotMemRootTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ),
    c.phases = Set.univ → ∀ x ∈ codedTail (shapeBits shape) ξ₀,
      c.codedPoint x ∉ Set.range (c.block ξ₀)

/-- **Target: the cuts of the tail enumeration are closed** (stated; given-condition).  With every
phase completed, a covering realization and a least phase `ξ₀`, for every tail point `j` the root
together with the block points of the tail points at or below `j` is closed for the canonical
closure: it is the set of points of the phases below `rank j` together with the cut at the index
of `pos j` of the block of `rank j`, closed by `PhaseCondition.isSupportClosed_cut` and
`Phase.isSupportClosedIffTarget`.  This is the hypothesis of `Closure.closedCutOrderTarget` for
the enumeration of the exterior by the tail. -/
def CodedPointCutClosedTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ), IsBot ξ₀ →
    c.phases = Set.univ → ∀ (hc : c.real.IsCovering) (j : codedTail (shapeBits shape) ξ₀),
      (c.real.closure c.isConsistent hc).IsClosed (Set.range (c.block ξ₀) ∪
        (fun x : codedTail (shapeBits shape) ξ₀ ↦ c.codedPoint x.1) '' Set.Iic j)

/-- **Target: the comparison clause** (stated; given-condition).  With every phase completed, a
covering realization and a least phase `ξ₀`, for tail points `x` and `y` the block point of `x`
lies in the canonical closure of the first block with the block point of `y` added exactly when
`x ≤ y` in the coded order, within one block and between blocks
(`Closure.closedCutOrderTarget` with `Phase.CodedPointCutClosedTarget`). -/
def CodedPointOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ), IsBot ξ₀ →
    c.phases = Set.univ → ∀ (hc : c.real.IsCovering) (x y : CodedOrder (shapeBits shape)),
      x ∈ codedTail (shapeBits shape) ξ₀ → y ∈ codedTail (shapeBits shape) ξ₀ →
        (c.codedPoint x ∈ c.real.closure c.isConsistent hc
          (insert (c.codedPoint y) (Set.range (c.block ξ₀))) ↔ x ≤ y)

/-- **Target: the tail covers the exterior** (stated; given-condition).  With every phase completed,
every point a block point and a least phase `ξ₀`, every point outside the block of `ξ₀` is the
block point of a tail point. -/
def CodedPointSurjectiveTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ), IsBot ξ₀ →
    c.phases = Set.univ → c.dom = Set.univ → ∀ z ∉ Set.range (c.block ξ₀),
      ∃ x ∈ codedTail (shapeBits shape) ξ₀, c.codedPoint x = z

/-- **Target: the order reading of a full phase condition** (stated; given-condition).  At any
stage, on any carrier, with any linear order of phases, a phase condition with every phase
completed, every point a block point and a covering realization has the order reading above a
least phase `ξ₀` (`PhaseCondition.HasOrderReading`): the block enumeration is an order isomorphism
from the tail of the coded order of the shapes above `ξ₀` onto the whole exterior of the first
block. -/
def TailOrderIsoExteriorTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ), IsBot ξ₀ →
    c.phases = Set.univ → c.dom = Set.univ → ∀ hc : c.real.IsCovering,
      c.HasOrderReading hc ξ₀

/-! ### At `ω₁` -/

/-- The **first phase** of `ω₁.ToType`: the point of the ordinal `0`. -/
noncomputable def firstPhase : (ω₁ : Ordinal.{0}).ToType :=
  Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩

/-- **Target: the order reading at `ω₁`** (stated; given-condition).  At stage `ω₁`, on the carrier
`ω₁.ToType` with phases indexed by `ω₁.ToType`, for a phase condition with every phase completed
and every point a block point, and a covering realization: the first phase is least; its block is
countable, infinite and closed for the canonical closure; the tail of the coded order of the
shapes above the first phase is a nonempty upper set; and the condition has the order reading
above the first phase.  The tail is a tail of `CodedOrder (shapeBits shape)` in the sense of
`Order.TailEquivalent`, with the original phase indices. -/
def OmegaOneOrderReadingTarget : Prop :=
  ∀ (shape : (ω₁ : Ordinal.{0}).ToType → BlockShape)
    (req : (ω₁ : Ordinal.{0}).ToType →
      PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
    (c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType shape req), c.phases = Set.univ → c.dom = Set.univ →
    ∀ hc : c.real.IsCovering,
      IsBot firstPhase ∧ (Set.range (c.block firstPhase)).Countable ∧
        (Set.range (c.block firstPhase)).Infinite ∧
        (c.real.closure c.isConsistent hc).IsClosed (Set.range (c.block firstPhase)) ∧
        IsUpperSet (codedTail (shapeBits shape) firstPhase) ∧
        (codedTail (shapeBits shape) firstPhase).Nonempty ∧
        c.HasOrderReading hc firstPhase

/-- **Target: a receiving model with the order reading, for every choice of shapes** (stated;
existence).  At stage `ω₁`, on the carrier `ω₁.ToType` with phases indexed by `ω₁.ToType`, for
every choice of shapes there are a schedule of requests scheduling every request at arbitrarily
late phases and a phase condition for these shapes and requests with every phase completed and
every point a block point, whose realization is a receiving model with top-free types, is covering,
and has the order reading above the first phase.  The condition is part of the conclusion. -/
def ExistsOmegaOneOrderReadingTarget : Prop :=
  ∀ shape : (ω₁ : Ordinal.{0}).ToType → BlockShape,
    ∃ req : (ω₁ : Ordinal.{0}).ToType →
        PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType,
      (∀ (r : PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
        (ξ : (ω₁ : Ordinal.{0}).ToType), ∃ η, ξ ≤ η ∧ req η = r) ∧
      ∃ c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
          (ω₁ : Ordinal.{0}).ToType shape req,
        c.phases = Set.univ ∧ c.dom = Set.univ ∧ c.real.IsReceivingModel ∧
          c.real.HasTopFreeTypes ∧ ∃ hc : c.real.IsCovering, c.HasOrderReading hc firstPhase

end VaughtConjecture.AlephOne.Phase
