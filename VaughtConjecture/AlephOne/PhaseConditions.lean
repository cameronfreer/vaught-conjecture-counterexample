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
new points of order type `ω` or `ℤ`, with all its cuts closed) above everything built before, and
each phase serving **one request** at **one designated serving point** of its block.  Pure
descending blocks (order type `ω*`, `VaughtConjecture.AlephOne.DescendingBlock`) are construction
helpers inside integer blocks, not phases: no descending point serves.
Everything in this file is self-contained: it uses neither the carrier nor the conditions of the
one-point construction, and its names live in the namespace `VaughtConjecture.AlephOne.Phase`.

**Shapes.**  A phase has a shape (`Phase.BlockShape`): ascending or integer, with index order `ℕ`
or `ℤ` (`Phase.BlockShape.Index`), and a designated serving index
(`Phase.BlockShape.servingIndex`): the first ascending point `a_0`.

**Where the infinite root comes from.**  Phase conditions have no separate initial root.  The first
completed block is a countably infinite closed set, the root; the exterior order is read from the
remaining phases, each above the infinite domain of the phases before it
(`Phase.CompletedPhaseOrderTarget` needs an infinite set of old points).  The order theorem does
not apply to phase `0` over its empty predecessor domain; discarding the first phase is harmless
for reading the coded order.

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

**The statements.**

* `Phase.IsSupportClosedIffTarget` (given-realization): support-closed is closed.  Proved.
* `Phase.ExistsCompletedPhaseTarget` (construction over a given countable realization): a
  completed phase of either shape serving any one request over the old carrier.  Proved, from
  `Realization.ascendingBlockServiceTarget` and `Realization.integerBlockServiceTarget`.
* `Phase.CompletedPhaseOrderTarget` (given-realization): the exterior order of the block points of a
  completed phase above an infinite part of the old carrier is the order of the index.  Proved.
* `Phase.PhaseConditionExtensionTarget`: a phase condition whose completed phases are those below
  `ξ`, with countable domain, extends to one whose completed phases are those at most `ξ`, with
  the new block on any prescribed countably infinite set of free points of the carrier.
* `Phase.PhaseChainUpperBoundTarget`: a nonempty chain of phase conditions has an upper bound whose
  completed phases are the union.
* `Phase.ExistsFullPhaseConditionTarget`: at stage `ω₁`, on the carrier `ω₁.ToType` with phases
  indexed by `ω₁.ToType`, every choice of shapes and requests has a phase condition in which every
  phase is completed and every point is a block point.  Intended route: maximality among the
  phase conditions with the coverage invariant (`Phase.PhaseCondition.CoversPhases`: every
  completed phase, read as a point of the carrier, is in the domain), which survives chain unions
  and extensions whose prescribed new block contains `ξ` when `ξ` is still unused.
* `Phase.FullPhaseExactReceivingTarget`: for a request schedule that schedules every request at
  arbitrarily late phases, the realization of such a full phase condition has exact receiving
  within the legal top-free stage types.

The last four are stated, not proved.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (Stage 3, by
completed blocks); that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v w

namespace VaughtConjecture.AlephOne.Phase

open Ordinal Realization

/-! ### Shapes of blocks -/

/-- The **shape** of a phase: an ascending block (order type `ω`) or an integer block (`ℤ`).
Descending blocks are not phases. -/
inductive BlockShape
  /-- An ascending block, of order type `ω`. -/
  | ascending
  /-- An integer block, of order type `ℤ`. -/
  | integer
  deriving DecidableEq

/-- The **index order** of a block of each shape: `ℕ` or `ℤ`. -/
def BlockShape.Index : BlockShape → Type
  | .ascending => ℕ
  | .integer => ℤ

/-- The index orders are linear orders. -/
instance BlockShape.instLinearOrderIndex : ∀ b : BlockShape, LinearOrder b.Index
  | .ascending => inferInstanceAs (LinearOrder ℕ)
  | .integer => inferInstanceAs (LinearOrder ℤ)

/-- The **designated serving index** of a block: the first ascending point `a_0`. -/
def BlockShape.servingIndex : ∀ b : BlockShape, b.Index
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
realization, a set is support-closed exactly when it is closed for the canonical closure.  Proved
(`Phase.isSupportClosedIffTarget`). -/
def IsSupportClosedIffTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ (R : Realization.{u, v} α X) (hR : R.IsConsistent)
    (hc : R.IsCovering) (C : Set X), IsSupportClosed R C ↔ (R.closure hR hc).IsClosed C

/-- **Support-closed is closed**, the target form.  A finite subset of a support-closed set lies
in a support inside the set, which contains its canonical hull (`finiteHull_subset_of_isSupport`);
conversely the canonical hull of a finite subset of a closed set is a support inside the set
(`isSupport_finiteHull`). -/
theorem isSupportClosedIffTarget : IsSupportClosedIffTarget.{u, v} := by
  intro α X R hR hc C
  classical
  constructor
  · intro h
    rw [ClosureOperator.isClosed_iff_closure_le]
    intro y hy
    obtain ⟨F, hF, hyF⟩ := (mem_closure_iff hR hc).mp hy
    obtain ⟨n, t, ht, hFt, htC⟩ := h F hF
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ht
    have hsup : R.IsSupport (Finset.univ.map t) := ⟨⟨n, t, p, hp⟩, rfl⟩
    have hcoe : (↑(Finset.univ.map t) : Set X) = Set.range t := by
      ext z
      simp
    have hFs : F ⊆ Finset.univ.map t := by
      rw [← Finset.coe_subset, hcoe]
      exact hFt
    have hy' := finiteHull_subset_of_isSupport hR hc hsup hFs hyF
    rw [← Finset.mem_coe, hcoe] at hy'
    exact htC hy'
  · intro h F hF
    obtain ⟨x, hx⟩ := isSupport_finiteHull hR hc F
    refine ⟨x.arity, x.tuple, by simp, fun a ha ↦ ?_, ?_⟩
    · have ha' : a ∈ x.support := hx ▸ subset_finiteHull F ha
      obtain ⟨i, rfl⟩ := (Occurrence.mem_support _).mp ha'
      exact ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      have hi : x.tuple i ∈ R.finiteHull F := hx ▸ (Occurrence.mem_support _).mpr ⟨i, rfl⟩
      have hmem := (mem_closure_iff hR hc (A := C)).mpr ⟨F, hF, hi⟩
      rwa [h.closure_eq] at hmem

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
points.  Construction over a given realization.  Proved (`Phase.existsCompletedPhaseTarget`). -/
def ExistsCompletedPhaseTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes → ∀ (b : BlockShape) (r : PhaseRequest α M),
        ∃ (N : Type v) (_ : Countable N) (S : Realization.{u, v} α N) (ι : M ↪ N)
          (z : b.Index → N), IsCompletedPhase R S ι b z ∧
          ServesAt S (r.map ι) (Set.range ι) (z b.servingIndex)

/-- An ascending block is a completed phase of ascending shape: the old points form the prefix cut
at `0`, and the cuts of `ℕ` are the prefix cuts. -/
theorem isCompletedPhase_ascending {R : Realization.{u, v} α M}
    {S : Realization.{u, v} α (M ⊕ ℕ)} (hS : S.IsConsistent) (hSc : S.IsCovering)
    (hSL : S.HasLegalTypes) (hST : S.HasTopFreeTypes)
    (hSev : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.inl) = R.eval t)
    (hScut : ∀ n, (S.closure hS hSc).IsClosed (prefixCut n)) :
    IsCompletedPhase R S Function.Embedding.inl .ascending (Sum.inr : ℕ → M ⊕ ℕ) where
  isConsistent := hS
  isCovering := hSc
  hasLegalTypes := hSL
  hasTopFreeTypes := hST
  eval_trans := hSev
  injective := Sum.inr_injective
  notMem_range i := by
    rintro ⟨a, ha⟩
    exact Sum.inl_ne_inr ha
  mem_range_or y := by
    rcases y with a | j
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  isSupportClosed_range := by
    refine (isSupportClosedIffTarget S hS hSc _).mpr ?_
    have h := hScut 0
    rwa [prefixCut, show Set.Iio (0 : ℕ) = ∅ from Set.ext fun i ↦ by simp, Set.image_empty,
      Set.union_empty] at h
  isSupportClosed_cut := fun (j : ℕ) ↦ by
    refine (isSupportClosedIffTarget S hS hSc _).mpr ?_
    have h := hScut (j + 1)
    rwa [prefixCut, show Set.Iio (j + 1) = Set.Iic j from Set.ext fun i ↦ by simp] at h

/-- An integer block is a completed phase of integer shape: the old points of `M` form a closed set
below the integer cuts (`Closure.isClosed_of_isClosed_cuts`), and the cuts of `ℤ` are the integer
cuts. -/
theorem isCompletedPhase_integer {R : Realization.{u, v} α M}
    {U : Realization.{u, v} α ((M ⊕ ℕ) ⊕ ℕ)} (hU : U.IsConsistent) (hUc : U.IsCovering)
    (hUL : U.HasLegalTypes) (hUT : U.HasTopFreeTypes)
    (hUev : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M),
      U.eval ((t.trans Function.Embedding.inl).trans Function.Embedding.inl) = R.eval t)
    (hUcut : ∀ z, (U.closure hU hUc).IsClosed (integerCut z)) :
    IsCompletedPhase R U (Function.Embedding.inl.trans Function.Embedding.inl) .integer
      (integerBlockPoint : ℤ → (M ⊕ ℕ) ⊕ ℕ) where
  isConsistent := hU
  isCovering := hUc
  hasLegalTypes := hUL
  hasTopFreeTypes := hUT
  eval_trans := hUev
  injective := integerBlockPoint_injective
  notMem_range := integerBlockPoint_notMem
  mem_range_or y := by
    rcases y with (a | m) | m
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨Int.negSucc m, rfl⟩
    · exact Or.inr ⟨Int.ofNat m, rfl⟩
  isSupportClosed_range :=
    (isSupportClosedIffTarget U hU hUc _).mpr
      (Closure.isClosed_of_isClosed_cuts (I := ℤ) integerBlockPoint_injective hUcut)
  isSupportClosed_cut j := (isSupportClosedIffTarget U hU hUc _).mpr (hUcut j)

/-- **A completed phase serving one request**, the target form.  If the request is effective (its
tuple has a type of which the donor is a top-free coface), an ascending block
(`Realization.ascendingBlockServiceTarget`) or an integer block
(`Realization.integerBlockServiceTarget`) serving it; otherwise any ascending or integer block
(`Realization.ascendingBlockTarget`, `Realization.integerBlockTarget`), where service holds
vacuously. -/
theorem existsCompletedPhaseTarget : ExistsCompletedPhaseTarget.{u, v} := by
  intro α M _ hα R hR hc hL hT b r
  by_cases hr : ∃ p, R.eval r.tuple = some p ∧ r.donor ∈ p.cofaces ∧ r.donor.IsTopFree
  · obtain ⟨p, hp, hdc, hdt⟩ := hr
    let x : R.Occurrence := ⟨r.arity, r.tuple, p, hp⟩
    cases b with
    | ascending =>
      obtain ⟨S, hS, hSc, hSL, hST, hSev, hScut, hSd⟩ :=
        ascendingBlockServiceTarget hα R hR hc hL hT x r.donor hdc hdt
      exact ⟨M ⊕ ℕ, inferInstance, S, _, _,
        isCompletedPhase_ascending hS hSc hSL hST hSev hScut, fun _ _ _ _ _ _ ↦ hSd⟩
    | integer =>
      obtain ⟨S, hS, hSc, hSL, hST, hSev, hScut, hU⟩ :=
        integerBlockServiceTarget hα R hR hc hL hT
      let xS : S.Occurrence := ⟨r.arity, r.tuple.trans Function.Embedding.inl, p, by rw [hSev, hp]⟩
      obtain ⟨U, hU, hUc, hUL, hUT, hUev, hUcut, hUd⟩ := hU xS r.donor hdc hdt
      exact ⟨(M ⊕ ℕ) ⊕ ℕ, inferInstance, U, _, _,
        isCompletedPhase_integer hU hUc hUL hUT (fun n t ↦ by rw [hUev, hSev]) hUcut,
        fun _ _ _ _ _ _ ↦ hUd⟩
  · have hvac : ∀ {N : Type v} (S : Realization.{u, v} α N) (ι : M ↪ N) (a : N),
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans ι) = R.eval t) →
          ServesAt S (r.map ι) (Set.range ι) a := by
      intro N S ι a hev ha p _ hp hdc hdt
      exact absurd ⟨p, (hev r.tuple).symm.trans hp, hdc, hdt⟩ hr
    cases b with
    | ascending =>
      obtain ⟨S, hS, hSc, hSL, hST, hSev, hScut⟩ := ascendingBlockTarget hα R hR hc hL hT
      exact ⟨M ⊕ ℕ, inferInstance, S, _, _,
        isCompletedPhase_ascending hS hSc hSL hST hSev hScut, hvac S _ _ hSev⟩
    | integer =>
      obtain ⟨U, hU, hUc, hUL, hUT, hUev, hUcut⟩ := integerBlockTarget hα R hR hc hL hT
      exact ⟨(M ⊕ ℕ) ⊕ ℕ, inferInstance, U, _, _,
        isCompletedPhase_integer hU hUc hUL hUT hUev hUcut, hvac U _ _ hUev⟩

/-- **Target: the order of a completed phase** (given-realization).  For a completed phase
`(S, ι, z)` over `R` and an infinite set `B` of old points, the block point `z i` lies in the
canonical closure of `ι '' B` with `z j` added exactly when `i ≤ j`.  The old carrier must be
infinite: over the empty domain of the first phase there is no root, and the first completed block
serves as the root of the later ones.  Proved (`Phase.completedPhaseOrderTarget`). -/
def CompletedPhaseOrderTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ ⦃N : Type v⦄ (R : Realization.{u, v} α M)
    (S : Realization.{u, v} α N) (ι : M ↪ N) (b : BlockShape) (z : b.Index → N)
    (h : IsCompletedPhase R S ι b z) ⦃B : Set M⦄, B.Infinite →
      ∀ i j, z i ∈ S.closure h.isConsistent h.isCovering (insert (z j) (ι '' B)) ↔ i ≤ j

/-- **The order of a completed phase**, the target form: the range of `ι` and the cuts are closed
(`Phase.isSupportClosedIffTarget`), and the order is
`Closure.mem_setClosure_insert_iff_of_isClosed_cuts` at the root `range ι`, over its infinite
part `ι '' B`. -/
theorem completedPhaseOrderTarget : CompletedPhaseOrderTarget.{u, v} := by
  intro α M N R S ι b z h B hB i j
  have hgen := exists_subset_card_le_two_hullClosure_eq h.isConsistent h.isCovering
  exact Closure.mem_setClosure_insert_iff_of_isClosed_cuts
    (c := S.hullClosure h.isConsistent h.isCovering) hgen z (hB.image ι.injective.injOn)
    (Set.image_subset_range _ _)
    ((isSupportClosedIffTarget S _ _ _).mp h.isSupportClosed_range) h.injective h.notMem_range
    (fun j ↦ (isSupportClosedIffTarget S _ _ _).mp (h.isSupportClosed_cut j)) i j

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

/-- The **coverage invariant**, on a carrier that is also the order of the phases: every completed
phase, read as a point of the carrier, lies in the domain.  It survives unions of chains and
extensions through phase `ξ` whose new block contains `ξ` when `ξ` is still unused; with every
phase completed it gives a full domain. -/
def CoversPhases {req : Φ → PhaseRequest α Φ} (c : PhaseCondition α Φ Φ shape req) : Prop :=
  ∀ ξ ∈ c.phases, ξ ∈ c.dom

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
