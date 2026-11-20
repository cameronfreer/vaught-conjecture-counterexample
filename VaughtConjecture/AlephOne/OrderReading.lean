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

**The statements** (all proved, each by the theorem of the same name in lower camel case; the
recorded cut is identified by `Phase.PhaseCondition.range_block_union_image_Iic_eq`).

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

This file belongs to the `ℵ₁` companion construction over the density sentence, recorded in
`roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction"), where the construction by completed
blocks is recorded as "Every assignment of block shapes".  It is a step towards the item recorded
there as not yet proved, `2^ℵ₁` pairwise nonisomorphic models: it reads the coded order of the
shapes from the exterior order of a full phase condition.
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

/-- **Target: shapes, bits and indices correspond** (proved).  The bit of an ascending shape is
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

namespace BlockShape

/-- The position of an index is strictly monotone. -/
theorem posOfIndex_strictMono : ∀ s : BlockShape, StrictMono s.posOfIndex
  | .ascending => fun _ _ h ↦ Int.ofNat_lt.mpr h
  | .integer => fun _ _ h ↦ h

/-- The position of an index is allowed at the bit of its shape. -/
theorem posOfIndex_nonneg :
    ∀ (s : BlockShape) (i : s.Index), s.bit = false → 0 ≤ s.posOfIndex i
  | .ascending, i, _ => Int.natCast_nonneg (show ℕ from i)
  | .integer, _, h => absurd h (by decide)

/-- The index at the position of an index is that index. -/
theorem indexOfPos_posOfIndex :
    ∀ (s : BlockShape) (i : s.Index), s.indexOfPos (s.posOfIndex i) = i
  | .ascending, i => Int.toNat_natCast (show ℕ from i)
  | .integer, _ => rfl

/-- The position of the index at an allowed position is that position. -/
theorem posOfIndex_indexOfPos :
    ∀ (s : BlockShape) (n : ℤ), (s.bit = false → 0 ≤ n) → s.posOfIndex (s.indexOfPos n) = n
  | .ascending, _, h => Int.toNat_of_nonneg (h rfl)
  | .integer, _, _ => rfl

/-- The index at a position is monotone. -/
theorem indexOfPos_mono : ∀ s : BlockShape, Monotone s.indexOfPos
  | .ascending => fun _ _ h ↦ Int.toNat_le_toNat h
  | .integer => fun _ _ h ↦ h

end BlockShape

/-- **Shapes, bits and indices correspond**, the target form: case analysis on the shape. -/
theorem shapeBitTarget : ShapeBitTarget.{w} := by
  refine ⟨rfl, rfl, fun s ↦ by cases s <;> rfl, fun β ↦ by cases β <;> rfl,
    fun Φ b ↦ funext fun ξ ↦ ?_, BlockShape.posOfIndex_strictMono, fun s n ↦ ⟨?_, ?_⟩,
    BlockShape.indexOfPos_posOfIndex, BlockShape.posOfIndex_indexOfPos⟩
  · change (BlockShape.ofBit (b ξ)).bit = b ξ
    cases b ξ <;> rfl
  · rintro ⟨i, rfl⟩
    exact s.posOfIndex_nonneg i
  · exact fun h ↦ ⟨s.indexOfPos n, s.posOfIndex_indexOfPos n h⟩

/-! ### The tail above a phase -/

/-- The **tail above a phase** `ξ₀` of a coded order: the points of rank strictly above `ξ₀`, as a
subset of the coded order itself, keeping the original indices. -/
def codedTail {I : Type w} [LinearOrder I] (b : I → Bool) (ξ₀ : I) : Set (CodedOrder b) :=
  CodedOrder.rank ⁻¹' Set.Ioi ξ₀

/-- **Target: the tail above a phase is a tail** (proved; pure order).  It is an upper set of the
coded order (the rank is monotone), and it is nonempty exactly when some index lies above
`ξ₀`. -/
def CodedTailIsTailTarget : Prop :=
  ∀ ⦃I : Type w⦄ [LinearOrder I] (b : I → Bool) (ξ₀ : I),
    IsUpperSet (codedTail b ξ₀) ∧ ((codedTail b ξ₀).Nonempty ↔ ∃ ξ, ξ₀ < ξ)

/-- **The tail above a phase is a tail**, the target form: the rank is monotone, and the point at
position `0` of a block above `ξ₀` lies in the tail. -/
theorem codedTailIsTailTarget : CodedTailIsTailTarget.{w} := by
  intro I _ b ξ₀
  refine ⟨fun x y hxy hx ↦ lt_of_lt_of_le (show ξ₀ < CodedOrder.rank x from hx)
    (CodedOrder.rank_mono hxy), fun ⟨x, hx⟩ ↦ ⟨_, hx⟩, fun ⟨ξ, hξ⟩ ↦ ?_⟩
  exact ⟨CodedOrder.mk ξ 0 fun _ ↦ le_rfl, hξ⟩

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

omit [LinearOrder Φ] in
/-- Membership in the points of a set of phases. -/
theorem mem_phasePoints {P : Set Φ} {block : ∀ ξ, (shape ξ).Index → X} {y : X} :
    y ∈ phasePoints P block ↔ ∃ ξ ∈ P, ∃ i, block ξ i = y := by
  simp only [phasePoints, Set.mem_iUnion, Set.mem_range, exists_prop]

/-- The position of a point of the coded order of the shapes is allowed at the bit of the shape of
its rank. -/
theorem pos_allowed (x : CodedOrder (shapeBits shape)) :
    (shape (CodedOrder.rank x)).bit = false → 0 ≤ CodedOrder.pos x :=
  x.2

/-- The point of the coded order of the shapes at the phase `ξ` and the position of the index
`i`. -/
def codedOfIndex (shape : Φ → BlockShape) (ξ : Φ) (i : (shape ξ).Index) :
    CodedOrder (shapeBits shape) :=
  CodedOrder.mk ξ ((shape ξ).posOfIndex i) ((shape ξ).posOfIndex_nonneg i)

@[simp] theorem rank_codedOfIndex (ξ : Φ) (i : (shape ξ).Index) :
    CodedOrder.rank (codedOfIndex shape ξ i) = ξ := rfl

@[simp] theorem pos_codedOfIndex (ξ : Φ) (i : (shape ξ).Index) :
    CodedOrder.pos (codedOfIndex shape ξ i) = (shape ξ).posOfIndex i := rfl

/-- The block point of the point at a phase and an index is the block point of that index. -/
theorem PhaseCondition.codedPoint_codedOfIndex (c : PhaseCondition α X Φ shape req) (ξ : Φ)
    (i : (shape ξ).Index) : c.codedPoint (codedOfIndex shape ξ i) = c.block ξ i := by
  change c.block ξ ((shape ξ).indexOfPos ((shape ξ).posOfIndex i)) = c.block ξ i
  rw [BlockShape.indexOfPos_posOfIndex]

/-- The block point of a point of rank `ξ`, read in the block of `ξ`. -/
theorem PhaseCondition.codedPoint_of_rank_eq (c : PhaseCondition α X Φ shape req)
    {x : CodedOrder (shapeBits shape)} {ξ : Φ} (h : CodedOrder.rank x = ξ) :
    c.codedPoint x = c.block ξ ((shape ξ).indexOfPos (CodedOrder.pos x)) := by
  subst h
  rfl

/-- **The root with an initial part of the tail is a recorded cut.**  With every phase completed
and a least phase `ξ₀`, for a tail point `j` the first block together with the block points of
the tail points at or below `j` is the set of points of the phases below `rank j` together with
the cut at the index of `pos j` of the block of `rank j`, the set recorded closed by
`PhaseCondition.isSupportClosed_cut`. -/
theorem PhaseCondition.range_block_union_image_Iic_eq (c : PhaseCondition α X Φ shape req)
    (hph : c.phases = Set.univ) {ξ₀ : Φ} (hbot : IsBot ξ₀)
    (j : codedTail (shapeBits shape) ξ₀) :
    Set.range (c.block ξ₀) ∪
        (fun x : codedTail (shapeBits shape) ξ₀ ↦ c.codedPoint x.1) '' Set.Iic j =
      phasePoints (c.phases ∩ Set.Iio (CodedOrder.rank j.1)) c.block ∪
        c.block (CodedOrder.rank j.1) ''
          Set.Iic ((shape (CodedOrder.rank j.1)).indexOfPos (CodedOrder.pos j.1)) := by
  have hmem : ∀ ξ, ξ ∈ c.phases := fun ξ ↦ hph ▸ Set.mem_univ ξ
  have hj : ξ₀ < CodedOrder.rank j.1 := j.2
  apply Set.Subset.antisymm
  · rintro y (⟨i, rfl⟩ | ⟨x, hxj, rfl⟩)
    · exact Or.inl (mem_phasePoints.mpr ⟨ξ₀, ⟨hmem _, hj⟩, i, rfl⟩)
    · rcases CodedOrder.le_iff.mp (show x.1 ≤ j.1 from hxj) with h | ⟨h, h'⟩
      · exact Or.inl (mem_phasePoints.mpr ⟨_, ⟨hmem _, h⟩, _, rfl⟩)
      · exact Or.inr ⟨(shape (CodedOrder.rank j.1)).indexOfPos (CodedOrder.pos x.1),
          BlockShape.indexOfPos_mono _ h', (c.codedPoint_of_rank_eq h).symm⟩
  · rintro y (hy | ⟨i, hi, rfl⟩)
    · obtain ⟨η, ⟨-, hη⟩, i, rfl⟩ := mem_phasePoints.mp hy
      rcases eq_or_ne η ξ₀ with rfl | hne
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨⟨codedOfIndex shape η i, lt_of_le_of_ne (hbot η) hne.symm⟩,
          (CodedOrder.lt_of_rank_lt hη).le, c.codedPoint_codedOfIndex η i⟩
    · refine Or.inr ⟨⟨codedOfIndex shape _ i, hj⟩, ?_, c.codedPoint_codedOfIndex _ i⟩
      refine CodedOrder.le_iff.mpr (Or.inr ⟨rfl, ?_⟩)
      calc (shape (CodedOrder.rank j.1)).posOfIndex i
          ≤ (shape (CodedOrder.rank j.1)).posOfIndex
              ((shape (CodedOrder.rank j.1)).indexOfPos (CodedOrder.pos j.1)) :=
            (BlockShape.posOfIndex_strictMono _).monotone hi
        _ = CodedOrder.pos j.1 := BlockShape.posOfIndex_indexOfPos _ _ (pos_allowed j.1)

end Reading

/-! ### The given-condition targets -/

/-- **Target: the first block is a countably infinite closed root** (proved; given-condition).  In
a phase condition with every phase completed and a covering realization, the block of a least
phase `ξ₀` is countable, infinite (its enumeration is injective), and closed for the canonical
closure (the union of its closed cuts, directed by the index). -/
def RootBlockTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ), IsBot ξ₀ →
    c.phases = Set.univ → ∀ hc : c.real.IsCovering,
      (Set.range (c.block ξ₀)).Countable ∧ (Set.range (c.block ξ₀)).Infinite ∧
        (c.real.closure c.isConsistent hc).IsClosed (Set.range (c.block ξ₀))

/-- **The first block is a countably infinite closed root**, the target form.  Every finite subset
of the block has its indices bounded by some `j`, so it lies in the cut at `j` over the (empty) set
of earlier points; that cut is support-closed, so the block is support-closed, hence closed
(`Phase.isSupportClosedIffTarget`). -/
theorem rootBlockTarget : RootBlockTarget.{u, v, w} := by
  intro α X Φ _ shape req c ξ₀ hbot hph hc
  have hmem : ξ₀ ∈ c.phases := hph ▸ Set.mem_univ ξ₀
  have hinj := c.injective_block ξ₀ hmem
  refine ⟨Set.countable_range _, Set.infinite_range_of_injective hinj, ?_⟩
  refine (isSupportClosedIffTarget c.real c.isConsistent hc _).mp fun F hF ↦ ?_
  obtain ⟨j, hj⟩ := (F.finite_toSet.preimage hinj.injOn).bddAbove
  have hbefore : phasePoints (c.phases ∩ Set.Iio ξ₀) c.block = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy ↦ ?_
    obtain ⟨η, ⟨-, hη⟩, -⟩ := mem_phasePoints.mp hy
    exact absurd hη (not_lt.mpr (hbot η))
  have hFcut : ↑F ⊆ phasePoints (c.phases ∩ Set.Iio ξ₀) c.block ∪ c.block ξ₀ '' Set.Iic j := by
    intro y hy
    obtain ⟨i, rfl⟩ := hF hy
    exact Or.inr ⟨i, hj (show i ∈ c.block ξ₀ ⁻¹' ↑F from hy), rfl⟩
  obtain ⟨n, t, ht, hFt, htcut⟩ := c.isSupportClosed_cut ξ₀ hmem j F hFcut
  refine ⟨n, t, ht, hFt, htcut.trans ?_⟩
  rw [hbefore, Set.empty_union]
  exact Set.image_subset_range _ _

/-- **Target: the block enumeration is injective on the coded order** (proved; given-condition).
With every phase completed, distinct points of the coded order of the shapes have distinct block
points: blocks of distinct phases are disjoint, each block enumeration is injective, and the index
at a position is injective on the positions allowed at the bit. -/
def CodedPointInjectiveTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req),
    c.phases = Set.univ → Function.Injective c.codedPoint

/-- **The block enumeration is injective on the coded order**, the target form. -/
theorem codedPointInjectiveTarget : CodedPointInjectiveTarget.{u, v, w} := by
  intro α X Φ _ shape req c hph x y hxy
  have hmem : ∀ ξ, ξ ∈ c.phases := fun ξ ↦ hph ▸ Set.mem_univ ξ
  have hr : CodedOrder.rank y = CodedOrder.rank x := by
    by_contra hne
    have h₁ : c.codedPoint y ∈ Set.range (c.block (CodedOrder.rank y)) := ⟨_, rfl⟩
    have h₂ : c.codedPoint y ∈ Set.range (c.block (CodedOrder.rank x)) := by
      rw [← hxy]
      exact ⟨_, rfl⟩
    exact Set.disjoint_left.mp (c.disjoint_block _ (hmem _) _ (hmem _) hne) h₁ h₂
  have h₃ : c.block (CodedOrder.rank x) ((shape (CodedOrder.rank x)).indexOfPos (CodedOrder.pos x))
      = c.block (CodedOrder.rank x)
        ((shape (CodedOrder.rank x)).indexOfPos (CodedOrder.pos y)) :=
    hxy.trans (c.codedPoint_of_rank_eq hr)
  have hidx := c.injective_block _ (hmem _) h₃
  have hay : (shape (CodedOrder.rank x)).bit = false → 0 ≤ CodedOrder.pos y := by
    rw [← hr]
    exact pos_allowed y
  refine CodedOrder.ext_rank_pos hr.symm ?_
  calc CodedOrder.pos x
      = (shape (CodedOrder.rank x)).posOfIndex
          ((shape (CodedOrder.rank x)).indexOfPos (CodedOrder.pos x)) :=
        (BlockShape.posOfIndex_indexOfPos _ _ (pos_allowed x)).symm
    _ = (shape (CodedOrder.rank x)).posOfIndex
          ((shape (CodedOrder.rank x)).indexOfPos (CodedOrder.pos y)) := congrArg _ hidx
    _ = CodedOrder.pos y := BlockShape.posOfIndex_indexOfPos _ _ hay

/-- **Target: the tail is carried outside the root** (proved; given-condition).  With every phase
completed, the block point of a point of rank above `ξ₀` is not in the block of `ξ₀`. -/
def CodedPointNotMemRootTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ),
    c.phases = Set.univ → ∀ x ∈ codedTail (shapeBits shape) ξ₀,
      c.codedPoint x ∉ Set.range (c.block ξ₀)

/-- **The tail is carried outside the root**, the target form: blocks of distinct phases are
disjoint. -/
theorem codedPointNotMemRootTarget : CodedPointNotMemRootTarget.{u, v, w} := by
  intro α X Φ _ shape req c ξ₀ hph x hx hB
  have hmem : ∀ ξ, ξ ∈ c.phases := fun ξ ↦ hph ▸ Set.mem_univ ξ
  exact Set.disjoint_left.mp (c.disjoint_block _ (hmem _) _ (hmem ξ₀)
    (show ξ₀ < CodedOrder.rank x from hx).ne')
    (⟨_, rfl⟩ : c.codedPoint x ∈ Set.range (c.block (CodedOrder.rank x))) hB

/-- **Target: the cuts of the tail enumeration are closed** (proved; given-condition).  With every
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

/-- **The cuts of the tail enumeration are closed**, the target form: the set is a recorded cut
(`PhaseCondition.range_block_union_image_Iic_eq`), support-closed by
`PhaseCondition.isSupportClosed_cut`, hence closed (`Phase.isSupportClosedIffTarget`). -/
theorem codedPointCutClosedTarget : CodedPointCutClosedTarget.{u, v, w} := by
  intro α X Φ _ shape req c ξ₀ hbot hph hc j
  rw [c.range_block_union_image_Iic_eq hph hbot j]
  exact (isSupportClosedIffTarget c.real c.isConsistent hc _).mp
    (c.isSupportClosed_cut _ (hph ▸ Set.mem_univ _) _)

/-- **Target: the comparison clause** (proved; given-condition).  With every phase completed, a
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

/-- **The comparison clause**, the target form: one application of `Closure.closedCutOrderTarget`
to the enumeration of the exterior by the tail, at the canonical hull, with the infinite root
(`Phase.rootBlockTarget`), injectivity (`Phase.codedPointInjectiveTarget`), values outside the
root (`Phase.codedPointNotMemRootTarget`) and closed cuts (`Phase.codedPointCutClosedTarget`). -/
theorem codedPointOrderTarget : CodedPointOrderTarget.{u, v, w} := by
  intro α X Φ _ shape req c ξ₀ hbot hph hc x y hx hy
  have hz : Function.Injective fun x : codedTail (shapeBits shape) ξ₀ ↦ c.codedPoint x.1 :=
    fun a b h ↦ Subtype.ext (codedPointInjectiveTarget shape req c hph h)
  exact Closure.closedCutOrderTarget (c.real.hullClosure c.isConsistent hc)
    (exists_subset_card_le_two_hullClosure_eq c.isConsistent hc)
    (fun x : codedTail (shapeBits shape) ξ₀ ↦ c.codedPoint x.1)
    (rootBlockTarget shape req c ξ₀ hbot hph hc).2.1 hz
    (fun i ↦ codedPointNotMemRootTarget shape req c ξ₀ hph i.1 i.2)
    (fun j ↦ codedPointCutClosedTarget shape req c ξ₀ hbot hph hc j) ⟨x, hx⟩ ⟨y, hy⟩

/-- **Target: the tail covers the exterior** (proved; given-condition).  With every phase completed,
every point a block point and a least phase `ξ₀`, every point outside the block of `ξ₀` is the
block point of a tail point. -/
def CodedPointSurjectiveTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (c : PhaseCondition α X Φ shape req) (ξ₀ : Φ), IsBot ξ₀ →
    c.phases = Set.univ → c.dom = Set.univ → ∀ z ∉ Set.range (c.block ξ₀),
      ∃ x ∈ codedTail (shapeBits shape) ξ₀, c.codedPoint x = z

/-- **The tail covers the exterior**, the target form: a point is a block point of some phase,
which is not `ξ₀`, hence above it. -/
theorem codedPointSurjectiveTarget : CodedPointSurjectiveTarget.{u, v, w} := by
  intro α X Φ _ shape req c ξ₀ hbot hph hdom z hz
  have hzdom : z ∈ phasePoints c.phases c.block := by
    change z ∈ c.dom
    rw [hdom]
    exact Set.mem_univ z
  obtain ⟨η, -, i, rfl⟩ := mem_phasePoints.mp hzdom
  have hne : η ≠ ξ₀ := by
    rintro rfl
    exact hz ⟨i, rfl⟩
  exact ⟨codedOfIndex shape η i, lt_of_le_of_ne (hbot η) hne.symm, c.codedPoint_codedOfIndex η i⟩

/-- **Target: the order reading of a full phase condition** (proved; given-condition).  At any
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

/-- **The order reading of a full phase condition**, the target form: the block enumeration on
the tail is a bijection onto the exterior (`Phase.codedPointNotMemRootTarget`,
`Phase.codedPointInjectiveTarget`, `Phase.codedPointSurjectiveTarget`) carrying `≤` to the
exterior relation (`Phase.codedPointOrderTarget`). -/
theorem tailOrderIsoExteriorTarget : TailOrderIsoExteriorTarget.{u, v, w} := by
  intro α X Φ _ shape req c ξ₀ hbot hph hdom hc
  let f : codedTail (shapeBits shape) ξ₀ → {x : X // x ∉ Set.range (c.block ξ₀)} :=
    fun x ↦ ⟨c.codedPoint x.1, codedPointNotMemRootTarget shape req c ξ₀ hph x.1 x.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h ↦ Subtype.ext (codedPointInjectiveTarget shape req c hph
      (congrArg Subtype.val h)), fun z ↦ ?_⟩
    obtain ⟨x, hx, hxz⟩ := codedPointSurjectiveTarget shape req c ξ₀ hbot hph hdom z.1 z.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  exact ⟨⟨Equiv.ofBijective f hf,
    fun {a b} ↦ codedPointOrderTarget shape req c ξ₀ hbot hph hc a.1 b.1 a.2 b.2⟩, fun _ ↦ rfl⟩

/-! ### At `ω₁` -/

/-- The **first phase** of `ω₁.ToType`: the point of the ordinal `0`. -/
noncomputable def firstPhase : (ω₁ : Ordinal.{0}).ToType :=
  Ordinal.ToType.mk ⟨0, Ordinal.omega_pos 1⟩

/-- The first phase is least. -/
theorem isBot_firstPhase : IsBot firstPhase := fun η ↦ by
  rw [← Ordinal.ToType.mk.apply_symm_apply η]
  exact Ordinal.ToType.mk.monotone (show (0 : Ordinal) ≤ (Ordinal.ToType.mk.symm η).1 from zero_le)

/-- **Target: the order reading at `ω₁`** (proved; given-condition).  At stage `ω₁`, on the carrier
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

/-- **The order reading at `ω₁`**, the target form: `Phase.rootBlockTarget`,
`Phase.codedTailIsTailTarget` (some phase lies above the first, as `ω₁` has no largest point) and
`Phase.tailOrderIsoExteriorTarget` at the least phase `Phase.firstPhase`. -/
theorem omegaOneOrderReadingTarget : OmegaOneOrderReadingTarget := by
  intro shape req c hph hdom hc
  have := noMaxOrder_omegaOne
  obtain ⟨hcount, hinf, hclosed⟩ := rootBlockTarget shape req c firstPhase isBot_firstPhase hph hc
  obtain ⟨hup, hne⟩ := codedTailIsTailTarget (shapeBits shape) firstPhase
  exact ⟨isBot_firstPhase, hcount, hinf, hclosed, hup, hne.mpr (exists_gt firstPhase),
    tailOrderIsoExteriorTarget shape req c firstPhase isBot_firstPhase hph hdom hc⟩

/-- **Target: a receiving model with the order reading, for every choice of shapes** (proved;
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

/-- **A receiving model with the order reading, for every choice of shapes**, the target form:
the condition of `Phase.existsFullPhaseReceivingModelTarget`, whose realization is covering since
its domain is the whole carrier, with the order reading of `Phase.tailOrderIsoExteriorTarget`. -/
theorem existsOmegaOneOrderReadingTarget : ExistsOmegaOneOrderReadingTarget := by
  intro shape
  obtain ⟨req, hreq, c, hph, hdom, hrm, htf⟩ := existsFullPhaseReceivingModelTarget shape
  have hc : c.real.IsCovering := fun n t ↦ c.isCovering t (by
    have h := Set.subset_univ (Set.range t)
    rwa [← hdom] at h)
  exact ⟨req, hreq, c, hph, hdom, hrm, htf, hc,
    tailOrderIsoExteriorTarget shape req c firstPhase isBot_firstPhase hph hdom hc⟩

end VaughtConjecture.AlephOne.Phase
