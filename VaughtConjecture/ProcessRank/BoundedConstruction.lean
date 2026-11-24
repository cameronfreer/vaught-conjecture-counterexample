/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Schedule
import VaughtConjecture.Continuation.ExactAge
import VaughtConjecture.ProcessRank.BoundedAge
import VaughtConjecture.Realization.ReceivingLimit

/-!
# One receiving model per bounded age, on the carrier of size `ℵ₁`: the statements

The `ℵ₁` companion construction (`VaughtConjecture.AlephOne.Conditions` to
`VaughtConjecture.AlephOne.ReceivingModel`) builds, on the carrier `AlephOne.Carrier = ω₁.ToType`,
a receiving model at stage `ω₁` with exact receiving within the legal top-free types.  This file
states its variant for the bounded age `A_K` of `VaughtConjecture.ProcessRank.BoundedAge` (the
legal types of top grade at most `K`), beside the existing files, which are not changed.  At
`K = 0` the bounded age is the top-free age (`ProcessRank.Bounded.boundedAge_zero`).

**Top grades of a realization.**  A realization has top grades at most `K`
(`ProcessRank.Bounded.HasTopGradeLe`) when every type it assigns has top grade at most `K`; at
`K = 0` this is `Realization.HasTopFreeTypes` (`ProcessRank.Bounded.hasTopGradeLe_zero_iff`,
proved).  The **realized age** of a realization (`ProcessRank.Bounded.realizedAge`) is the family
of the stage types it covers.

**The construction** (proved in `VaughtConjecture.ProcessRank.BoundedExistence`).  Requests and
the unbounded schedule are those of the `ℵ₁` companion construction (`AlephOne.Request`,
`AlephOne.existsUnboundedScheduleTarget`); only the service and the invariant change.

* `ProcessRank.Bounded.BoundedServesAt`: the service of a request whose donor has top grade at
  most `K` (in place of top-free).
* `ProcessRank.Bounded.BoundedCondition`: a condition whose types have top grades at most `K` (in
  place of top-free types); extension of conditions as before (proved to be a preorder).
* `ProcessRank.Bounded.BoundedOptionAttachmentTarget`: exact one-point attachment over a countable
  realization with top grades at most `K`, for a donor of top grade at most `K`.  The intended
  proof is that of `Realization.optionAttachmentTarget`, with the bounded pinned extension
  (`ProcessRank.Bounded.exists_pinned_extension_mem`) in place of the top-free one; the type of
  each occurrence of the chain has top grade at most `K` by the invariant.
* `ProcessRank.Bounded.BoundedChainUnionTarget`, `BoundedOnePointExtensionTarget`,
  `BoundedExistsFullHeightConditionTarget`, `BoundedFullHeightExactReceivingTarget`: Zorn's lemma
  on bounded conditions, as in `VaughtConjecture.AlephOne.Construction`.
* `ProcessRank.Bounded.BoundedFiniteCutReceivingTarget` (given-model): finite-cut receiving from
  exact receiving within `A_K`.  Over an occurrence of type `p` (top grade at most `K`), a legal
  coface `d` (of any top grade) and a permitted cutoff `δ`, the donor is `d` capped above the grade
  `K` (`StageType.capAbove`) at an ordinal `c < α`, self-visible at the arity of `d`, above `δ` and
  above every label of `d` other than `⊤`.  It has the scheme of `d`, so it is legal; it has top
  grade at most `K` (`StageType.topGrade_capAbove_le`); it restricts to `p` literally, since every
  cell of `p` labelled `⊤` has grade at most `K` (`StageType.restrictFace_capAbove`, which needs
  the cap above every label of `d` other than `⊤`, not only above those of `p`); and its labels
  agree with those of `d` below `δ`: the labels other than `⊤` are kept, and a cell labelled `⊤`
  of grade above `K` is labelled `c > δ`.  The cap is above the grade `K`, not a cap of the whole
  chart, which would erase the cells labelled `⊤` of the root.
* `ProcessRank.Bounded.BoundedIsReceivingModelOfExactReceivingTarget` (given-model): exact
  receiving within `A_K` makes a receiving model (finite-cut receiving, then
  `Realization.isModel_of_hasFiniteCutReceiving`, as in
  `AlephOne.isReceivingModelOfExactReceivingTarget`).
* `ProcessRank.Bounded.ExistsBoundedReceivingModelTarget`: for every `K`, a receiving model at
  `ω₁` on the carrier with top grades at most `K` and exact receiving within `A_K`.

**The realized age is exactly `A_K`** (`ProcessRank.Bounded.realizedAge_eq_boundedAge`, proved,
given-model): a model with legal types of top grades at most `K` and exact receiving within `A_K`
covers exactly the members of `A_K`; every member is received over the empty root.

## Placement

The bounded top-grade part of the process-rank companion programme (the files
`VaughtConjecture/ProcessRank/Bounded*.lean`).
-/

universe u v

namespace VaughtConjecture.ProcessRank.Bounded

open Ordinal Set Realization AlephOne

variable {α : Ordinal.{u}} {M : Type v}

/-! ### Top grades and the realized age of a realization -/

/-- A realization **has top grades at most `K`** when every type it assigns has top grade at most
`K`. -/
def HasTopGradeLe (R : Realization.{u, v} α M) (K : ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p → p.topGrade ≤ K

/-- **Top grades at most `0` are top-free types.** -/
theorem hasTopGradeLe_zero_iff {R : Realization.{u, v} α M} :
    HasTopGradeLe R 0 ↔ R.HasTopFreeTypes := by
  simp only [HasTopGradeLe, HasTopFreeTypes, Nat.le_zero, StageType.topGrade_eq_zero_iff]

/-- The **realized age** of a realization: the stage types it covers. -/
def realizedAge (R : Realization.{u, v} α M) (m : ℕ) : Set (StageType.{u} α m) :=
  {D | ∃ u : Fin m → M, R.Covers D u}

/-- **The realized age is exactly the bounded age** (given-model): a model with top grades at most
`K` and exact receiving within `A_K` covers a stage type exactly when it lies in `A_K`.  A covered
type is legal and of top grade at most `K`; a member of `A_K` is received over the empty cover,
which covers the only stage type on no points. -/
theorem realizedAge_eq_boundedAge {R : Realization.{u, v} α M} (hR : R.IsModel) {K : ℕ}
    (hK : HasTopGradeLe R K) (hrec : R.ExactReceivingWithin (boundedAge K)) (m : ℕ) :
    realizedAge R m = boundedAge K m := by
  ext D
  constructor
  · rintro ⟨u, hinj, hu⟩
    exact ⟨hR.isLegal _ D hu, hK _ D hu⟩
  · intro hD
    obtain ⟨t, ht⟩ := hR.exists_covers_zero
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
      (D.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
    rw [StageType.eq_of_zero q t] at hq
    obtain ⟨u, hu, -⟩ := hrec t ![] ht D Function.Embedding.ofIsEmpty hD hq
    exact ⟨u, hu⟩

/-! ### Exact one-point attachment within the bounded age -/

/-- **Target: exact one-point attachment within `A_K` over a countable realization.**  At a limit
stage `α`, let `R` be an exactly consistent covering realization with legal types of top grades at
most `K` on a countable carrier `M`, `x` an occurrence of `R`, and `d` a coface of the type of `x`
of top grade at most `K`.  Some exactly consistent covering realization `S` with legal types of
top grades at most `K` on `Option M` gives every tuple of old points its evaluation in `R`
(`none` included) and gives the tuple of `x` followed by the new point the type `d`.
Construction over a given realization.  Proved (`boundedOptionAttachmentTarget`, in
`VaughtConjecture.ProcessRank.BoundedExistence`). -/
def BoundedOptionAttachmentTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α → ∀ (K : ℕ)
    (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      HasTopGradeLe R K → ∀ (x : R.Occurrence), ∀ d ∈ x.type.cofaces, d.topGrade ≤ K →
        ∃ S : Realization.{u, v} α (Option M), S.IsConsistent ∧ S.IsCovering ∧
          S.HasLegalTypes ∧ HasTopGradeLe S K ∧
          (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.some) = R.eval t) ∧
          S.eval (appendNone x.tuple) = some d

/-! ### Bounded conditions on the carrier -/

/-- A realization **serves the request `r` at `γ` within `A_K`**: if the tuple of `r` lies below
`γ` and has a type `p` of which the donor is a coface of top grade at most `K`, the tuple
followed by `γ` has the donor as its type. -/
def BoundedServesAt (K : ℕ) (R : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier) (r : Request)
    (γ : Carrier) : Prop :=
  ∀ (h : ∀ i, r.tuple i < γ) (p : StageType.{0} (ω₁ : Ordinal.{0}) r.arity),
    R.eval r.tuple = some p → r.donor ∈ p.cofaces → r.donor.topGrade ≤ K →
      R.eval (r.extendAt h) = some r.donor

/-- A **bounded condition** for the bound `K` and the schedule `s`: a lower set `dom` of the
carrier and a realization on the carrier that types no tuple leaving `dom`, is exactly
consistent, covers every tuple inside `dom`, has legal types of top grades at most `K`, and serves
within `A_K` the request scheduled at every point of `dom`. -/
structure BoundedCondition (K : ℕ) (s : Carrier → Request) where
  /-- The domain: an initial segment of the carrier. -/
  dom : Set Carrier
  /-- The domain is a lower set. -/
  isLowerSet_dom : IsLowerSet dom
  /-- The realization. -/
  real : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier
  /-- No tuple leaving the domain is typed. -/
  eval_eq_none ⦃n : ℕ⦄ (t : Fin n ↪ Carrier) : ¬ range t ⊆ dom → real.eval t = none
  /-- Exact consistency. -/
  isConsistent : real.IsConsistent
  /-- Covering of the tuples inside the domain. -/
  isCovering ⦃n : ℕ⦄ (t : Fin n ↪ Carrier) : range t ⊆ dom →
    ∃ (m : ℕ) (u : Fin m ↪ Carrier) (f : Fin n ↪ Fin m), f.trans u = t ∧ (real.eval u).isSome
  /-- Legal types. -/
  hasLegalTypes : real.HasLegalTypes
  /-- Top grades at most `K`. -/
  hasTopGradeLe : HasTopGradeLe real K
  /-- Service within `A_K` of the request scheduled at every point of the domain. -/
  serves : ∀ γ ∈ dom, BoundedServesAt K real (s γ) γ

namespace BoundedCondition

variable {K : ℕ} {s : Carrier → Request}

/-- **Extension of bounded conditions**: the domain grows and the evaluations of the tuples inside
the old domain are kept, `none` included. -/
instance : Preorder (BoundedCondition K s) where
  le c c' := c.dom ⊆ c'.dom ∧
    ∀ ⦃n : ℕ⦄ (t : Fin n ↪ Carrier), range t ⊆ c.dom → c'.real.eval t = c.real.eval t
  le_refl _ := ⟨subset_rfl, fun _ _ _ ↦ rfl⟩
  le_trans _ _ _ hab hbc :=
    ⟨hab.1.trans hbc.1, fun _ t ht ↦ (hbc.2 t (ht.trans hab.1)).trans (hab.2 t ht)⟩

end BoundedCondition

/-! ### Zorn's lemma on bounded conditions -/

/-- **Target: upper bounds of chains of bounded conditions.**  Every chain of bounded conditions,
of any length, has an upper bound; a nonempty chain has one whose domain is the union of the
domains.  Proved (`boundedChainUnionTarget`, in
`VaughtConjecture.ProcessRank.BoundedExistence`). -/
def BoundedChainUnionTarget (K : ℕ) : Prop :=
  ∀ (s : Carrier → Request) (C : Set (BoundedCondition K s)), IsChain (· ≤ ·) C →
    (∃ ub : BoundedCondition K s, ∀ c ∈ C, c ≤ ub) ∧
      (C.Nonempty → ∃ ub : BoundedCondition K s, (∀ c ∈ C, c ≤ ub) ∧ ub.dom = ⋃ c ∈ C, c.dom)

/-- **Target: the one-point extension of a bounded condition.**  A bounded condition of countable
domain extends to one whose domain is the old domain with one more point: the least point `x`
outside the domain, attached by `ProcessRank.Bounded.BoundedOptionAttachmentTarget` over the
tuple of the request scheduled at `x` when it is eligible, and over the empty tuple with the
bottom one-point type otherwise.  Proved (`boundedOnePointExtensionTarget`, in
`VaughtConjecture.ProcessRank.BoundedExistence`). -/
def BoundedOnePointExtensionTarget (K : ℕ) : Prop :=
  ∀ (s : Carrier → Request) (c : BoundedCondition K s), c.dom.Countable →
    ∃ c' : BoundedCondition K s, c ≤ c' ∧ ∃ x ∉ c.dom, c'.dom = insert x c.dom

/-- **Target: a bounded condition of full domain exists**, for every schedule (Zorn's lemma, with
the one-point extension).  Proved (`boundedExistsFullHeightConditionTarget`, in
`VaughtConjecture.ProcessRank.BoundedExistence`). -/
def BoundedExistsFullHeightConditionTarget (K : ℕ) : Prop :=
  ∀ s : Carrier → Request, ∃ c : BoundedCondition K s, c.dom = Set.univ

/-- **Target: exact receiving within `A_K` from the served requests.**  For an unbounded
schedule, the realization of a bounded condition of full domain has exact receiving within `A_K`:
over a cover, a one-point coface in `A_K` is a request scheduled above the cover, where it is
served; the one-point form gives every arity (`Realization.ExactReceivingWithin.of_one_point`,
`A_K` being face closed, `ProcessRank.Bounded.mem_boundedAge_of_restrictFace`).  Proved
(`boundedFullHeightExactReceivingTarget`, in `VaughtConjecture.ProcessRank.BoundedExistence`). -/
def BoundedFullHeightExactReceivingTarget (K : ℕ) : Prop :=
  ∀ s : Carrier → Request, IsUnboundedSchedule s → ∀ c : BoundedCondition K s, c.dom = Set.univ →
    c.real.ExactReceivingWithin (boundedAge K)

/-! ### From exact receiving within the bounded age to receiving models -/

/-- **Target: finite-cut receiving from exact receiving within `A_K`** (given-model statement).
At a limit stage, a realization with top grades at most `K` and exact receiving within `A_K` has
finite-cut receiving: each coface is capped above the grade `K` (`StageType.capAbove`) at an
ordinal above the cutoff and above every label of the coface other than `⊤`.  Proved
(`boundedFiniteCutReceivingTarget`, in `VaughtConjecture.ProcessRank.BoundedExistence`). -/
def BoundedFiniteCutReceivingTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (K : ℕ)
    (R : Realization.{u, v} α M), HasTopGradeLe R K → R.ExactReceivingWithin (boundedAge K) →
      R.HasFiniteCutReceiving

/-- **Target: exact receiving within `A_K` makes a receiving model** (given-model statement).  At
a limit stage, an exactly consistent covering realization on a nonempty carrier with legal types
of top grades at most `K` and exact receiving within `A_K` is a receiving model.  Proved
(`boundedIsReceivingModelOfExactReceivingTarget`, in
`VaughtConjecture.ProcessRank.BoundedExistence`). -/
def BoundedIsReceivingModelOfExactReceivingTarget : Prop :=
  ∀ ⦃α : Ordinal.{0}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (K : ℕ) (R : Realization.{0, v} α M),
    Nonempty M → R.IsConsistent → R.IsCovering → R.HasLegalTypes → HasTopGradeLe R K →
      R.ExactReceivingWithin (boundedAge K) → R.IsReceivingModel

/-- **Target: a receiving model for every bounded age, on the carrier.**  For every `K`, some
realization at stage `ω₁` on the carrier `ω₁.ToType` (of cardinality `ℵ₁`) is a receiving model
with top grades at most `K` and exact receiving within `A_K`; its realized age is then exactly
`A_K` (`ProcessRank.Bounded.realizedAge_eq_boundedAge`).  Existence statement.  Proved
(`existsBoundedReceivingModelTarget`, in `VaughtConjecture.ProcessRank.BoundedExistence`). -/
def ExistsBoundedReceivingModelTarget (K : ℕ) : Prop :=
  ∃ R : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier, R.IsReceivingModel ∧ HasTopGradeLe R K ∧
    R.ExactReceivingWithin (boundedAge K)

end VaughtConjecture.ProcessRank.Bounded
