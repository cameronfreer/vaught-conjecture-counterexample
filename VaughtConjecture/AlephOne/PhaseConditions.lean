/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.IntegerBlock
import VaughtConjecture.Realization.Pushforward
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

/-- The index orders are countable. -/
instance BlockShape.instCountableIndex : ∀ b : BlockShape, Countable b.Index
  | .ascending => inferInstanceAs (Countable ℕ)
  | .integer => inferInstanceAs (Countable ℤ)

/-- The index orders are infinite. -/
instance BlockShape.instInfiniteIndex : ∀ b : BlockShape, Infinite b.Index
  | .ascending => inferInstanceAs (Infinite ℕ)
  | .integer => inferInstanceAs (Infinite ℤ)

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

/-- The points of a tuple followed by a point. -/
theorem mem_range_snoc {n : ℕ} {t : Fin n ↪ X} {a : X} (ha : a ∉ Set.range t) {y : X} :
    y ∈ Set.range (Fin.Embedding.snoc t ha) ↔ y = a ∨ y ∈ Set.range t := by
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inl Fin.Embedding.snoc_last
    | cast i => exact Or.inr ⟨i, Fin.Embedding.snoc_castSucc.symm⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last n, Fin.Embedding.snoc_last⟩
    · exact ⟨i.castSucc, Fin.Embedding.snoc_castSucc⟩

/-- Support-closedness of a set inside `D` passes to a realization with the same evaluations on
the tuples inside `D`. -/
theorem IsSupportClosed.of_agree {R R' : Realization.{u, v} α X} {C D : Set X} (hCD : C ⊆ D)
    (hag : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ D → R'.eval t = R.eval t)
    (h : IsSupportClosed R C) : IsSupportClosed R' C := fun F hF ↦ by
  obtain ⟨n, t, ht, hFt, htC⟩ := h F hF
  exact ⟨n, t, by rw [hag t (htC.trans hCD)]; exact ht, hFt, htC⟩

/-- Service over `D` at a point of `E ⊇ D` passes to a realization with the same evaluations on
the tuples inside `E`. -/
theorem ServesAt.of_agree {R R' : Realization.{u, v} α X} {r : PhaseRequest α X} {D E : Set X}
    {a : X} (hDE : D ⊆ E) (haE : a ∈ E)
    (hag : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ E → R'.eval t = R.eval t)
    (h : ServesAt R r D a) : ServesAt R' r D a := fun ha p hsub hp hdc hdt ↦ by
  rw [hag _ fun y hy ↦ ?_]
  · exact h ha p hsub (by rw [← hag _ (hsub.trans hDE)]; exact hp) hdc hdt
  · rcases (mem_range_snoc ha).mp hy with rfl | hy
    · exact haE
    · exact hDE (hsub hy)

/-- Support-closedness passes to the pushforward along an embedding, onto the image. -/
theorem IsSupportClosed.pushforward {N : Type w} {S : Realization.{u, w} α N} (π : N ↪ X)
    {C : Set N} (h : IsSupportClosed S C) : IsSupportClosed (S.pushforward π) (π '' C) :=
  fun F hF ↦ by
    classical
    obtain ⟨n, t, ht, hGt, htC⟩ := h (F.preimage π π.injective.injOn) fun y hy ↦ by
      obtain ⟨y', hy'C, hy'⟩ := hF (Finset.mem_preimage.mp hy)
      exact π.injective hy' ▸ hy'C
    refine ⟨n, t.trans π, by rw [pushforward_eval_trans]; exact ht, fun x hx ↦ ?_, ?_⟩
    · obtain ⟨y, -, rfl⟩ := hF hx
      obtain ⟨i, hi⟩ := hGt (Finset.mem_preimage.mpr hx)
      exact ⟨i, by simp [hi]⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨t i, htC ⟨i, rfl⟩, rfl⟩

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

/-- Extension is reflexive. -/
theorem Extends.refl {req : Φ → PhaseRequest α X} (c : PhaseCondition α X Φ shape req) :
    c.Extends c :=
  ⟨subset_rfl, fun _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩

/-- The domain grows along an extension. -/
theorem Extends.dom_subset {req : Φ → PhaseRequest α X} {c c' : PhaseCondition α X Φ shape req}
    (h : c.Extends c') : c.dom ⊆ c'.dom := fun x hx ↦ by
  simp only [dom, phasePoints, Set.mem_iUnion, Set.mem_range, exists_prop] at hx ⊢
  obtain ⟨ξ, hξ, i, rfl⟩ := hx
  exact ⟨ξ, h.1 hξ, i, by rw [h.2.1 ξ hξ]⟩

/-- Extension is transitive. -/
theorem Extends.trans {req : Φ → PhaseRequest α X} {c₁ c₂ c₃ : PhaseCondition α X Φ shape req}
    (h₁ : c₁.Extends c₂) (h₂ : c₂.Extends c₃) : c₁.Extends c₃ :=
  ⟨h₁.1.trans h₂.1, fun ξ hξ ↦ (h₂.2.1 ξ (h₁.1 hξ)).trans (h₁.2.1 ξ hξ),
    fun _ t ht ↦ (h₂.2.2 t (ht.trans h₁.dom_subset)).trans (h₁.2.2 t ht)⟩

/-- Phase conditions are preordered by extension. -/
instance {req : Φ → PhaseRequest α X} : Preorder (PhaseCondition α X Φ shape req) where
  le := Extends
  le_refl := Extends.refl
  le_trans _ _ _ := Extends.trans

/-- The block of a completed phase lies in the domain. -/
theorem range_block_subset_dom {req : Φ → PhaseRequest α X} (c : PhaseCondition α X Φ shape req)
    {ξ : Φ} (hξ : ξ ∈ c.phases) : Set.range (c.block ξ) ⊆ c.dom :=
  fun _ hx ↦ Set.mem_biUnion hξ hx

end PhaseCondition

omit [LinearOrder Φ] in
/-- The points of fewer phases are fewer. -/
theorem phasePoints_mono {P P' : Set Φ} (h : P ⊆ P') (block : ∀ ξ, (shape ξ).Index → X) :
    phasePoints P block ⊆ phasePoints P' block :=
  Set.biUnion_subset_biUnion_left h

/-- **Target: extension of a phase condition by one completed phase.**  At a limit stage, let `c`
be a phase condition whose completed phases are those below `ξ` and whose domain is countable.
For every countably infinite set `Y` of points outside the domain, `c` extends to a phase condition
whose completed phases are those at most `ξ` and whose domain is the old domain together with `Y`
(the block of phase `ξ` is `Y`).  Proved (`Phase.phaseConditionExtensionTarget`). -/
def PhaseConditionExtensionTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X), Order.IsSuccLimit α →
    ∀ (c : PhaseCondition α X Φ shape req) (ξ : Φ), c.phases = Set.Iio ξ → c.dom.Countable →
      ∀ ⦃Y : Set X⦄, Y ⊆ c.domᶜ → Y.Countable → Y.Infinite →
        ∃ c' : PhaseCondition α X Φ shape req, c.Extends c' ∧ c'.phases = Set.Iic ξ ∧
          c'.dom = c.dom ∪ Y

/-- **Extension of a phase condition by one completed phase**, the target form.  The old
realization on the domain (`Realization.comap`) is exactly consistent and covering with legal
top-free types; a completed phase of shape `shape ξ` over it serving the request of `ξ`
(`Phase.existsCompletedPhaseTarget`, with the request read on the domain when its tuple lies
there) is carried onto the old domain together with `Y` (`Realization.pushforward`), its old points
going to themselves and its block onto `Y` along an enumeration of `Y` by the index.  The new
realization agrees with the old one on the old domain, so the earlier phases keep their
closedness and service (`Phase.IsSupportClosed.of_agree`, `Phase.ServesAt.of_agree`); the new
phase is closed and served by transport (`Phase.IsSupportClosed.pushforward`). -/
theorem phaseConditionExtensionTarget : PhaseConditionExtensionTarget.{u, v, w} := by
  classical
  intro α X Φ _ shape req hα c ξ hph hcount Y hY hYc hYi
  have : Countable c.dom := hcount.to_subtype
  -- the old realization on the domain
  let π₀ : c.dom ↪ X := Function.Embedding.subtype _
  have hrange₀ : Set.range π₀ = c.dom := Subtype.range_coe
  let R₀ := c.real.comap π₀
  have hR₀ : R₀.IsConsistent := c.isConsistent.comap π₀
  have hc₀ : R₀.IsCovering := comap_isCovering π₀
    (fun n t ht ↦ c.eval_eq_none t (by rwa [hrange₀] at ht))
    (fun n t ht ↦ c.isCovering t (by rwa [hrange₀] at ht))
  -- a completed phase over it, serving the request of `ξ` when its tuple lies in the domain
  obtain ⟨N, _, S, ι, z, hS, hserve⟩ : ∃ (N : Type v) (_ : Countable N)
      (S : Realization.{u, v} α N) (ι : c.dom ↪ N) (z : (shape ξ).Index → N),
      IsCompletedPhase R₀ S ι (shape ξ) z ∧ ∀ ht : ∀ i, (req ξ).tuple i ∈ c.dom,
        ServesAt S (PhaseRequest.map ι ⟨_, (req ξ).tuple.codRestrict c.dom ht, (req ξ).donor⟩)
          (Set.range ι) (z (shape ξ).servingIndex) := by
    by_cases ht : ∀ i, (req ξ).tuple i ∈ c.dom
    · obtain ⟨N, hN, S, ι, z, h, hs⟩ := existsCompletedPhaseTarget hα R₀ hR₀ hc₀
        (c.hasLegalTypes.comap π₀) (c.hasTopFreeTypes.comap π₀) (shape ξ)
        ⟨_, (req ξ).tuple.codRestrict c.dom ht, (req ξ).donor⟩
      exact ⟨N, hN, S, ι, z, h, fun _ ↦ hs⟩
    · obtain ⟨N, hN, S, ι, z, h, -⟩ := existsCompletedPhaseTarget hα R₀ hR₀ hc₀
        (c.hasLegalTypes.comap π₀) (c.hasTopFreeTypes.comap π₀) (shape ξ)
        ⟨0, Function.Embedding.ofIsEmpty, StageType.onePointApex⟩
      exact ⟨N, hN, S, ι, z, h, fun h' ↦ absurd h' ht⟩
  -- an enumeration of `Y` by the index of the shape
  have : Countable Y := hYc.to_subtype
  have : Infinite Y := hYi.to_subtype
  obtain ⟨hdY⟩ := nonempty_denumerable Y
  obtain ⟨hdI⟩ := nonempty_denumerable (shape ξ).Index
  let e : (shape ξ).Index ≃ Y := (Denumerable.eqv _).trans (Denumerable.eqv Y).symm
  -- the map of the new carrier into `X`
  have hbij : Function.Bijective (Sum.elim ι z) := by
    refine ⟨ι.injective.sumElim hS.injective fun a i h ↦ hS.notMem_range i ⟨a, h⟩, fun y ↦ ?_⟩
    rcases hS.mem_range_or y with ⟨a, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩
  let σ : c.dom ⊕ (shape ξ).Index ↪ X :=
    ⟨Sum.elim Subtype.val fun i ↦ (e i : X), Subtype.val_injective.sumElim
      (Subtype.val_injective.comp e.injective) fun a i h ↦ hY (e i).2 (h ▸ a.2)⟩
  let π : N ↪ X := (Equiv.ofBijective _ hbij).symm.toEmbedding.trans σ
  have hπι : ∀ a, π (ι a) = a := fun a ↦ by
    change σ ((Equiv.ofBijective _ hbij).symm (Sum.elim ι z (Sum.inl a))) = a
    rw [Equiv.ofBijective_symm_apply_apply]
    rfl
  have hπz : ∀ i, π (z i) = e i := fun i ↦ by
    change σ ((Equiv.ofBijective _ hbij).symm (Sum.elim ι z (Sum.inr i))) = e i
    rw [Equiv.ofBijective_symm_apply_apply]
    rfl
  have hrangeπ : Set.range π = c.dom ∪ Y := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rcases hS.mem_range_or y with ⟨a, rfl⟩ | ⟨i, rfl⟩
      · exact Or.inl (by rw [hπι]; exact a.2)
      · exact Or.inr (by rw [hπz]; exact (e i).2)
    · rintro (hx | hx)
      · exact ⟨ι ⟨x, hx⟩, hπι _⟩
      · exact ⟨z (e.symm ⟨x, hx⟩), by rw [hπz]; simp⟩
  have hιπ : π '' Set.range ι = c.dom := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      rw [hπι]
      exact a.2
    · intro hx
      exact ⟨ι ⟨x, hx⟩, ⟨_, rfl⟩, hπι _⟩
  -- the new block
  let block' : ∀ η, (shape η).Index → X := Function.update c.block ξ fun i ↦ (e i : X)
  have hblock_ne : ∀ η, η ≠ ξ → block' η = c.block η := fun η h ↦ Function.update_of_ne h _ _
  have hblock_ξ : block' ξ = fun i ↦ (e i : X) := Function.update_self _ _ _
  have hdom' : phasePoints (Set.Iic ξ) block' = c.dom ∪ Y := by
    ext x
    simp only [phasePoints, PhaseCondition.dom, Set.mem_iUnion, Set.mem_union, Set.mem_Iic,
      Set.mem_range, exists_prop, hph, Set.mem_Iio]
    constructor
    · rintro ⟨η, hη, i, rfl⟩
      rcases lt_or_eq_of_le hη with h | rfl
      · exact Or.inl ⟨η, h, i, by rw [hblock_ne η h.ne]⟩
      · exact Or.inr (by rw [hblock_ξ]; exact (e i).2)
    · rintro (⟨η, h, i, rfl⟩ | hx)
      · exact ⟨η, h.le, i, by rw [hblock_ne η h.ne]⟩
      · exact ⟨ξ, le_rfl, e.symm ⟨x, hx⟩, by rw [hblock_ξ]; simp⟩
  have hpts : ∀ η ≤ ξ, phasePoints (Set.Iic ξ ∩ Set.Iio η) block' =
      phasePoints (c.phases ∩ Set.Iio η) c.block := by
    intro η hη
    ext x
    simp only [phasePoints, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Iio,
      Set.mem_range, exists_prop, hph]
    constructor
    · rintro ⟨ζ, ⟨-, hζ⟩, i, rfl⟩
      exact ⟨ζ, ⟨hζ.trans_le hη, hζ⟩, i, by rw [hblock_ne ζ (hζ.trans_le hη).ne]⟩
    · rintro ⟨ζ, ⟨h1, hζ⟩, i, rfl⟩
      exact ⟨ζ, ⟨h1.le, hζ⟩, i, by rw [hblock_ne ζ h1.ne]⟩
  have hD_eq : phasePoints (c.phases ∩ Set.Iio ξ) c.block = c.dom := by
    rw [PhaseCondition.dom, hph, Set.inter_self]
  have hbefore : ∀ η, phasePoints (c.phases ∩ Set.Iio η) c.block ⊆ c.dom := fun η ↦
    phasePoints_mono Set.inter_subset_left _
  -- the new realization agrees with the old one on the old domain
  let real' := S.pushforward π
  have hag : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ c.dom → real'.eval t = c.real.eval t := by
    intro n t ht
    have hu : ((t.codRestrict c.dom fun i ↦ ht ⟨i, rfl⟩).trans ι).trans π = t :=
      Function.Embedding.ext fun i ↦ hπι _
    conv_lhs => rw [← hu]
    rw [pushforward_eval_trans, hS.eval_trans]
    exact congrArg c.real.eval (Function.Embedding.ext fun i ↦ rfl)
  have hlt : ∀ η ∈ Set.Iic ξ, η ≠ ξ → η ∈ c.phases := fun η hη h ↦ by
    rw [hph]
    exact lt_of_le_of_ne hη h
  refine ⟨{
      phases := Set.Iic ξ
      isLowerSet_phases := isLowerSet_Iic ξ
      block := block'
      injective_block := fun η hη ↦ ?_
      disjoint_block := fun η hη ζ hζ hne ↦ ?_
      real := real'
      eval_eq_none := fun n t ht ↦ ?_
      isConsistent := hS.isConsistent.pushforward π
      isCovering := fun n t ht ↦ ?_
      hasLegalTypes := hS.hasLegalTypes.pushforward π
      hasTopFreeTypes := hS.hasTopFreeTypes.pushforward π
      isSupportClosed_before := fun η hη ↦ ?_
      isSupportClosed_cut := fun η hη j ↦ ?_
      serves := fun η hη ↦ ?_ }, ⟨?_, fun η hη ↦ ?_, hag⟩, rfl, hdom'⟩
  · by_cases h : η = ξ
    · subst h
      rw [hblock_ξ]
      exact Subtype.val_injective.comp e.injective
    · rw [hblock_ne η h]
      exact c.injective_block η (hlt η hη h)
  · have hnew : ∀ η, η ≠ ξ → η ∈ Set.Iic ξ → Disjoint (Set.range (block' η))
        (Set.range (block' ξ)) := fun η h hη ↦ by
      rw [hblock_ne η h, hblock_ξ, Set.disjoint_iff]
      rintro x ⟨hx, ⟨i, rfl⟩⟩
      exact hY (e i).2 (c.range_block_subset_dom (hlt η hη h) hx)
    by_cases h1 : η = ξ
    · subst h1
      exact (hnew ζ (Ne.symm hne) hζ).symm
    · by_cases h2 : ζ = ξ
      · subst h2
        exact hnew η h1 hη
      · rw [hblock_ne η h1, hblock_ne ζ h2]
        exact c.disjoint_block η (hlt η hη h1) ζ (hlt ζ hζ h2) hne
  · rw [hdom', ← hrangeπ] at ht
    exact pushforward_eval_of_not π S ht
  · rw [hdom', ← hrangeπ] at ht
    exact pushforward_isCovering_of_range_subset π hS.isCovering ht
  · rw [hpts η hη]
    by_cases h : η = ξ
    · subst h
      rw [hD_eq, ← hιπ]
      exact hS.isSupportClosed_range.pushforward π
    · exact (c.isSupportClosed_before η (hlt η hη h)).of_agree (hbefore η) hag
  · rw [hpts η hη]
    by_cases h : η = ξ
    · subst h
      rw [hD_eq, hblock_ξ, ← hιπ]
      have himg : (fun i ↦ (e i : X)) '' Set.Iic j = π '' (z '' Set.Iic j) := by
        rw [Set.image_image]
        simp only [hπz]
      rw [himg, ← Set.image_union]
      exact (hS.isSupportClosed_cut j).pushforward π
    · rw [hblock_ne η h]
      refine (c.isSupportClosed_cut η (hlt η hη h) j).of_agree
        (Set.union_subset (hbefore η) ?_) hag
      rintro _ ⟨i, -, rfl⟩
      exact c.range_block_subset_dom (hlt η hη h) ⟨i, rfl⟩
  · rw [hpts η hη]
    by_cases h : η = ξ
    · subst h
      rw [hD_eq, hblock_ξ]
      intro ha p hsub hp hdc hdt
      have ht : ∀ i, (req η).tuple i ∈ c.dom := fun i ↦ hsub ⟨i, rfl⟩
      let u := (req η).tuple.codRestrict c.dom ht
      have hu : (u.trans ι).trans π = (req η).tuple := Function.Embedding.ext fun i ↦ hπι _
      have ha' : z (shape η).servingIndex ∉ Set.range (u.trans ι) := by
        rintro ⟨i, hi⟩
        exact hS.notMem_range _ ⟨u i, hi⟩
      have hS' := hserve ht ha' p (by rintro _ ⟨i, rfl⟩; exact ⟨u i, rfl⟩)
        (by
          change S.eval (u.trans ι) = some p
          rw [← pushforward_eval_trans π S, hu]
          exact hp) hdc hdt
      have hsnoc : Fin.Embedding.snoc (req η).tuple ha =
          (Fin.Embedding.snoc (u.trans ι) ha').trans π := by
        refine Function.Embedding.ext fun i ↦ ?_
        induction i using Fin.lastCases with
        | last => simp [hπz]
        | cast i => simp [hπι, u]
      rw [hsnoc, pushforward_eval_trans]
      exact hS'
    · rw [hblock_ne η h]
      exact (c.serves η (hlt η hη h)).of_agree (hbefore η)
        (c.range_block_subset_dom (hlt η hη h) ⟨_, rfl⟩) hag
  · intro η hη
    have h : η < ξ := by rw [hph] at hη; exact hη
    exact Set.mem_Iic.mpr h.le
  · have h : η < ξ := by rw [hph] at hη; exact hη
    exact hblock_ne η h.ne

/-- The stage type on no points at a stage (there is only one, `StageType.eq_of_zero`): the empty
face of the one-point apex type. -/
noncomputable def emptyType (α : Ordinal.{u}) : StageType.{u} α 0 :=
  (StageType.restrictFace Function.Embedding.ofIsEmpty (StageType.onePointApex (α := α))).get
    (StageType.isSome_restrictFace_of_zero _ _)

theorem isLegal_emptyType : (emptyType α).IsLegal :=
  StageType.isLegal_onePointApex.restrictFace _ (Option.some_get _).symm

/-- The realization typing only the empty tuple. -/
noncomputable def emptyRealization (α : Ordinal.{u}) (X : Type v) : Realization.{u, v} α X where
  eval {n} _ := match n with
    | 0 => some (emptyType α)
    | _ + 1 => none

/-- **Target: the initial phase condition.**  On a nonempty carrier, for every choice of shapes and
requests, some phase condition has no completed phase.  Proved
(`Phase.phaseInitialConditionTarget`). -/
def PhaseInitialConditionTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ [Nonempty X] ⦃Φ : Type w⦄ [LinearOrder Φ]
    (shape : Φ → BlockShape) (req : Φ → PhaseRequest α X),
      ∃ c : PhaseCondition α X Φ shape req, c.phases = ∅

/-- **The initial phase condition**, the target form: no completed phase, arbitrary blocks, and the
realization typing only the empty tuple (`Phase.emptyRealization`). -/
theorem phaseInitialConditionTarget : PhaseInitialConditionTarget.{u, v, w} := by
  intro α X _ Φ _ shape req
  have hempty : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ phasePoints (∅ : Set Φ)
      (fun _ _ ↦ Classical.arbitrary X : ∀ ξ, (shape ξ).Index → X) → n = 0 := by
    intro n t ht
    by_contra hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have := ht ⟨0, rfl⟩
    simp [phasePoints] at this
  refine ⟨{
      phases := ∅
      isLowerSet_phases := isLowerSet_empty
      block := fun _ _ ↦ Classical.arbitrary X
      injective_block := fun _ h ↦ h.elim
      disjoint_block := fun _ h ↦ h.elim
      real := emptyRealization α X
      eval_eq_none := fun n t ht ↦ ?_
      isConsistent := fun m n t p f hp ↦ ?_
      isCovering := fun n t ht ↦ ?_
      hasLegalTypes := fun n t p hp ↦ ?_
      hasTopFreeTypes := fun n t p hp ↦ ?_
      isSupportClosed_before := fun _ h ↦ h.elim
      isSupportClosed_cut := fun _ h ↦ h.elim
      serves := fun _ h ↦ h.elim }, rfl⟩
  · cases n with
    | zero => exact absurd (fun x hx ↦ by obtain ⟨i, -⟩ := hx; exact i.elim0) ht
    | succ k => rfl
  · cases n with
    | succ k => exact absurd hp (by simp [emptyRealization])
    | zero =>
      have hm : m = 0 := by simpa using Fintype.card_le_of_embedding f
      subst hm
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (p.isSome_restrictFace_of_zero f)
      rw [hq, StageType.eq_of_zero q (emptyType α)]
      rfl
  · obtain rfl := hempty t ht
    exact ⟨0, t, Function.Embedding.refl _, rfl, rfl⟩
  · cases n with
    | succ k => exact absurd hp (by simp [emptyRealization])
    | zero =>
      obtain rfl : emptyType α = p := Option.some_injective _ hp
      exact isLegal_emptyType
  · cases n with
    | succ k => exact absurd hp (by simp [emptyRealization])
    | zero => exact StageType.isTopFree_of_zero p

/-- **Target: upper bounds of chains of phase conditions.**  A nonempty chain of phase conditions
for the extension preorder has an upper bound whose completed phases are the union of theirs.
Proved (`Phase.phaseChainUpperBoundTarget`). -/
def PhaseChainUpperBoundTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃X : Type v⦄ ⦃Φ : Type w⦄ [LinearOrder Φ] (shape : Φ → BlockShape)
    (req : Φ → PhaseRequest α X) (C : Set (PhaseCondition α X Φ shape req)), C.Nonempty →
      IsChain PhaseCondition.Extends C →
        ∃ c' : PhaseCondition α X Φ shape req, (∀ c ∈ C, c.Extends c') ∧
          c'.phases = ⋃ c ∈ C, c.phases

/-- **Upper bounds of chains of phase conditions**, the target form.  The union: its completed
phases are the union, the block of a phase is its block in any member completing it, and a tuple
inside the domain of some member has the evaluation in that member.  These do not depend on the
member, the chain being a chain for extension; a finite set inside the union of the domains lies in
one domain.  The earlier phases of a completed phase are completed in the same member, so the
closedness and service of each phase come from one member (`Phase.IsSupportClosed.of_agree`,
`Phase.ServesAt.of_agree`). -/
theorem phaseChainUpperBoundTarget : PhaseChainUpperBoundTarget.{u, v, w} := by
  classical
  intro α X Φ _ shape req C hne hch
  have hcomp : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁.Extends c₂ ∨ c₂.Extends c₁ := fun c₁ h₁ c₂ h₂ ↦ by
    by_cases h : c₁ = c₂
    · subst h
      exact Or.inl (PhaseCondition.Extends.refl c₁)
    · exact hch h₁ h₂ h
  -- finite sets inside the union of the domains lie in one domain
  have hfin : ∀ F : Finset X, ↑F ⊆ ⋃ c ∈ C, c.dom → ∃ c ∈ C, ↑F ⊆ c.dom := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      obtain ⟨c, hc⟩ := hne
      exact fun _ ↦ ⟨c, hc, by simp⟩
    | insert a F _ ih =>
      intro hF
      obtain ⟨c₁, h₁, hF₁⟩ := ih (fun x hx ↦ hF (Finset.mem_insert_of_mem hx))
      obtain ⟨c₂, h₂, ha₂⟩ := Set.mem_iUnion₂.mp (hF (Finset.mem_insert_self a F))
      rcases hcomp c₁ h₁ c₂ h₂ with h | h
      · refine ⟨c₂, h₂, ?_⟩
        rw [Finset.coe_insert]
        exact Set.insert_subset ha₂ (hF₁.trans h.dom_subset)
      · refine ⟨c₁, h₁, ?_⟩
        rw [Finset.coe_insert]
        exact Set.insert_subset (h.dom_subset ha₂) hF₁
  have htuple : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ ⋃ c ∈ C, c.dom →
      ∃ c ∈ C, Set.range t ⊆ c.dom := fun n t ht ↦ by
    obtain ⟨c, hc, h⟩ := hfin (Finset.univ.image t) (by simpa using ht)
    exact ⟨c, hc, by simpa using h⟩
  -- the blocks
  let block' : ∀ ξ, (shape ξ).Index → X := fun ξ ↦
    if h : ∃ c ∈ C, ξ ∈ c.phases then h.choose.block ξ else hne.some.block ξ
  have hblock : ∀ c ∈ C, ∀ ξ ∈ c.phases, block' ξ = c.block ξ := fun c hc ξ hξ ↦ by
    have h : ∃ c ∈ C, ξ ∈ c.phases := ⟨c, hc, hξ⟩
    simp only [block', dite_eq_left h]
    rcases hcomp _ h.choose_spec.1 c hc with h' | h'
    · exact (h'.2.1 ξ h.choose_spec.2).symm
    · exact h'.2.1 ξ hξ
  -- the realization
  let real' : Realization.{u, v} α X := ⟨fun {n} t ↦
    if h : ∃ c ∈ C, Set.range t ⊆ c.dom then h.choose.real.eval t else none⟩
  have hreal : ∀ c ∈ C, ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ c.dom →
      real'.eval t = c.real.eval t := fun c hc n t ht ↦ by
    have h : ∃ c ∈ C, Set.range t ⊆ c.dom := ⟨c, hc, ht⟩
    change (if h : ∃ c ∈ C, Set.range t ⊆ c.dom then h.choose.real.eval t else none) = _
    rw [dite_eq_left h]
    rcases hcomp _ h.choose_spec.1 c hc with h' | h'
    · exact (h'.2.2 t h.choose_spec.2).symm
    · exact h'.2.2 t ht
  have hreal_none : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), ¬ (∃ c ∈ C, Set.range t ⊆ c.dom) →
      real'.eval t = none := fun n t h ↦ by
    change (if h : ∃ c ∈ C, Set.range t ⊆ c.dom then h.choose.real.eval t else none) = _
    rw [dite_eq_right h]
  have htyped : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X) (p : StageType.{u} α n), real'.eval t = some p →
      ∃ c ∈ C, Set.range t ⊆ c.dom ∧ c.real.eval t = some p := fun n t p hp ↦ by
    by_cases h : ∃ c ∈ C, Set.range t ⊆ c.dom
    · obtain ⟨c, hc, ht⟩ := h
      exact ⟨c, hc, ht, (hreal c hc t ht).symm.trans hp⟩
    · rw [hreal_none t h] at hp
      exact absurd hp (by simp)
  have hdom : phasePoints (⋃ c ∈ C, c.phases) block' = ⋃ c ∈ C, c.dom := by
    ext x
    simp only [phasePoints, PhaseCondition.dom, Set.mem_iUnion, Set.mem_range, exists_prop]
    constructor
    · rintro ⟨ξ, ⟨c, hc, hξ⟩, i, rfl⟩
      exact ⟨c, hc, ξ, hξ, i, by rw [hblock c hc ξ hξ]⟩
    · rintro ⟨c, hc, ξ, hξ, i, rfl⟩
      exact ⟨ξ, ⟨c, hc, hξ⟩, i, by rw [hblock c hc ξ hξ]⟩
  -- the earlier phases of a completed phase are completed in one member
  have hbefore : ∀ c ∈ C, ∀ ξ ∈ c.phases,
      phasePoints ((⋃ c ∈ C, c.phases) ∩ Set.Iio ξ) block' =
        phasePoints (c.phases ∩ Set.Iio ξ) c.block := fun c hc ξ hξ ↦ by
    ext x
    simp only [phasePoints, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iio, Set.mem_range,
      exists_prop]
    constructor
    · rintro ⟨η, ⟨-, hη⟩, i, rfl⟩
      have hηc : η ∈ c.phases := c.isLowerSet_phases hη.le hξ
      exact ⟨η, ⟨hηc, hη⟩, i, by rw [hblock c hc η hηc]⟩
    · rintro ⟨η, ⟨hηc, hη⟩, i, rfl⟩
      exact ⟨η, ⟨⟨c, hc, hηc⟩, hη⟩, i, by rw [hblock c hc η hηc]⟩
  have hbsub : ∀ c ∈ C, ∀ ξ, phasePoints (c.phases ∩ Set.Iio ξ) c.block ⊆ c.dom :=
    fun c _ ξ ↦ phasePoints_mono Set.inter_subset_left _
  refine ⟨{
      phases := ⋃ c ∈ C, c.phases
      isLowerSet_phases := isLowerSet_iUnion₂ fun c _ ↦ c.isLowerSet_phases
      block := block'
      injective_block := fun ξ hξ ↦ ?_
      disjoint_block := fun ξ hξ η hη hne ↦ ?_
      real := real'
      eval_eq_none := fun n t ht ↦ ?_
      isConsistent := fun m n t p f hp ↦ ?_
      isCovering := fun n t ht ↦ ?_
      hasLegalTypes := fun n t p hp ↦ ?_
      hasTopFreeTypes := fun n t p hp ↦ ?_
      isSupportClosed_before := fun ξ hξ ↦ ?_
      isSupportClosed_cut := fun ξ hξ j ↦ ?_
      serves := fun ξ hξ ↦ ?_ }, fun c hc ↦ ⟨?_, fun ξ hξ ↦ hblock c hc ξ hξ, ?_⟩, rfl⟩
  · obtain ⟨c, hc, hξc⟩ := Set.mem_iUnion₂.mp hξ
    rw [hblock c hc ξ hξc]
    exact c.injective_block ξ hξc
  · obtain ⟨c₁, h₁, hξ₁⟩ := Set.mem_iUnion₂.mp hξ
    obtain ⟨c₂, h₂, hη₂⟩ := Set.mem_iUnion₂.mp hη
    have key : ∀ c ∈ C, ξ ∈ c.phases → η ∈ c.phases →
        Disjoint (Set.range (block' ξ)) (Set.range (block' η)) := fun c hc h1 h2 ↦ by
      rw [hblock c hc ξ h1, hblock c hc η h2]
      exact c.disjoint_block ξ h1 η h2 hne
    rcases hcomp c₁ h₁ c₂ h₂ with h | h
    · exact key c₂ h₂ (h.1 hξ₁) hη₂
    · exact key c₁ h₁ hξ₁ (h.1 hη₂)
  · rw [hdom] at ht
    exact hreal_none t fun ⟨c, hc, h⟩ ↦ ht (h.trans (Set.subset_biUnion_of_mem hc))
  · obtain ⟨c, hc, ht, hp'⟩ := htyped t p hp
    rw [hreal c hc _ ((Set.range_comp_subset_range f t).trans ht)]
    exact c.isConsistent t p f hp'
  · rw [hdom] at ht
    obtain ⟨c, hc, htc⟩ := htuple t ht
    obtain ⟨m, u, f, hfu, hu⟩ := c.isCovering t htc
    have hrange : Set.range u ⊆ c.dom := by
      by_contra h
      rw [c.eval_eq_none u h] at hu
      exact Bool.false_ne_true hu
    exact ⟨m, u, f, hfu, by rw [hreal c hc u hrange]; exact hu⟩
  · obtain ⟨c, hc, -, hp'⟩ := htyped t p hp
    exact c.hasLegalTypes t p hp'
  · obtain ⟨c, hc, -, hp'⟩ := htyped t p hp
    exact c.hasTopFreeTypes t p hp'
  · obtain ⟨c, hc, hξc⟩ := Set.mem_iUnion₂.mp hξ
    rw [hbefore c hc ξ hξc]
    exact (c.isSupportClosed_before ξ hξc).of_agree (hbsub c hc ξ) (hreal c hc)
  · obtain ⟨c, hc, hξc⟩ := Set.mem_iUnion₂.mp hξ
    rw [hbefore c hc ξ hξc, hblock c hc ξ hξc]
    refine (c.isSupportClosed_cut ξ hξc j).of_agree
      (Set.union_subset (hbsub c hc ξ) ?_) (hreal c hc)
    rintro _ ⟨i, -, rfl⟩
    exact c.range_block_subset_dom hξc ⟨i, rfl⟩
  · obtain ⟨c, hc, hξc⟩ := Set.mem_iUnion₂.mp hξ
    rw [hbefore c hc ξ hξc, hblock c hc ξ hξc]
    exact (c.serves ξ hξc).of_agree (hbsub c hc ξ) (c.range_block_subset_dom hξc ⟨_, rfl⟩)
      (hreal c hc)
  · exact Set.subset_biUnion_of_mem hc
  · exact fun n t ht ↦ hreal c hc t ht

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
