/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Zorn
import VaughtConjecture.AlephOne.OptionAttachment

/-!
# Conditions on a fixed carrier of size `ℵ₁`, and upper bounds of their chains

Stage 3 of the `ℵ₁` companion construction builds one realization at stage `ω₁` on a carrier
fixed in advance, by Zorn's lemma on partial realizations.  This file holds the carrier, the
requests, the schedules, the conditions and their order, and proves that **every chain of
conditions has an upper bound** (`AlephOne.Condition.exists_upperBound`), with the service of the
scheduled requests kept.

**The carrier** (`AlephOne.Carrier`) is `ω₁.ToType`: a type in `Type`, well ordered of order type
`ω₁`, of cardinality exactly `ℵ₁` (`AlephOne.mk_carrier`).  A partial realization lives on an
initial segment of it, and the point `x` is the point added when the initial segment `Set.Iio x`
is extended.

**Requests** (`AlephOne.Request`): a tuple of the carrier with a one-point donor.  A **schedule**
assigns a request to each point; it is **unbounded** (`AlephOne.IsUnboundedSchedule`) when every
request is scheduled at points above every point.  The request scheduled at `γ` is **served**
(`AlephOne.ServesAt`) when, if its tuple lies below `γ`, is typed with type `p`, and its donor is
a top-free coface of `p`, then the tuple followed by `γ` has the donor as its type.  Requests do
not depend on the construction.

**Conditions** (`AlephOne.Condition`).  A condition is a domain `dom`, a lower set of the
carrier, and a realization `real` on the whole carrier that types no tuple leaving `dom`, is
exactly consistent, covers every tuple inside `dom`, has legal top-free types, and serves the
request scheduled at every point of `dom`.  The domain may be the whole carrier (height `ω₁`).
The realization on the subtype `dom` itself is `AlephOne.Condition.restrict`; it is exactly
consistent and covering with legal top-free types (`AlephOne.Condition.isConsistent_restrict` and
the following theorems), so a condition is a realization on an initial segment, extended by
`none`.  Conditions are preordered by extension of the domain with the same evaluations on the old
domain.  No receiving or modelhood is required of a condition.

**Upper bounds of chains.**  The empty chain is bounded by the initial condition
(`AlephOne.Condition.initial`: empty domain, only the empty tuple typed).  A nonempty chain is
bounded by its union (`AlephOne.Condition.union`): its domain is the union of the domains, and a
tuple inside the domain of some member has the evaluation in that member, which does not depend
on the member since the chain is a chain (`AlephOne.Condition.eval_unionRealization`).  A finite
tuple inside the union lies in one domain, since the domains are lower sets of a linear order and
the tuple has a largest point.  Nothing is assumed about the length of the chain or the sizes of
the domains; a chain whose domains exhaust the carrier has the whole carrier as the domain of its
union (`AlephOne.Condition.union_dom_eq_univ`).

## Placement

This file is Stage 3 (one model of cardinality `ℵ₁`) of the `ℵ₁` companion construction over the
density sentence; that construction is not yet recorded in `roadmap/COMPANIONS.md`.  The
statements that use these conditions are in `VaughtConjecture.AlephOne.Construction`.
-/

namespace VaughtConjecture.AlephOne

open Ordinal Set Realization

/-- The **carrier** of the construction: `ω₁` as a type in `Type`, well ordered of order type
`ω₁`. -/
abbrev Carrier : Type :=
  (ω₁ : Ordinal.{0}).ToType

/-- The carrier is nonempty. -/
instance : Nonempty Carrier :=
  nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'

/-- The carrier has cardinality exactly `ℵ₁`. -/
theorem mk_carrier : Cardinal.mk Carrier = Cardinal.aleph 1 := by
  rw [Cardinal.mk_toType, Ordinal.card_omega]

/-- A **request**: a tuple of the carrier with a one-point donor at stage `ω₁`. -/
structure Request where
  /-- The number of points of the tuple. -/
  arity : ℕ
  /-- The tuple. -/
  tuple : Fin arity ↪ Carrier
  /-- The donor: a stage type on one more point. -/
  donor : StageType.{0} (ω₁ : Ordinal.{0}) (arity + 1)

/-- A schedule of requests is **unbounded** when every request is scheduled at points above every
point. -/
def IsUnboundedSchedule (s : Carrier → Request) : Prop :=
  ∀ (r : Request) (x : Carrier), ∃ y, x ≤ y ∧ s y = r

/-- The tuple of a request lying below `γ`, followed by `γ`. -/
def Request.extendAt (r : Request) {γ : Carrier} (h : ∀ i, r.tuple i < γ) :
    Fin (r.arity + 1) ↪ Carrier :=
  Fin.Embedding.snoc r.tuple (a := γ) (by rintro ⟨i, hi⟩; exact (h i).ne hi)

/-- The points of `r.extendAt h` are the points of the tuple and `γ`. -/
theorem Request.extendAt_le (r : Request) {γ : Carrier} (h : ∀ i, r.tuple i < γ)
    (i : Fin (r.arity + 1)) : r.extendAt h i ≤ γ := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [Request.extendAt]
  · simpa [Request.extendAt] using (h j).le

/-- A realization **serves the request `r` at `γ`**: if the tuple of `r` lies below `γ` and has a
type `p` of which the donor is a top-free coface, the tuple followed by `γ` has the donor as its
type. -/
def ServesAt (R : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier) (r : Request) (γ : Carrier) :
    Prop :=
  ∀ (h : ∀ i, r.tuple i < γ) (p : StageType.{0} (ω₁ : Ordinal.{0}) r.arity),
    R.eval r.tuple = some p → r.donor ∈ p.cofaces → r.donor.IsTopFree →
      R.eval (r.extendAt h) = some r.donor

/-- A **condition** for the schedule `s`: a lower set `dom` of the carrier and a realization on the
carrier that types no tuple leaving `dom`, is exactly consistent, covers every tuple inside `dom`,
has legal top-free types, and serves the request scheduled at every point of `dom`.  The domain
may be the whole carrier. -/
structure Condition (s : Carrier → Request) where
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
  /-- Top-free types. -/
  hasTopFreeTypes : real.HasTopFreeTypes
  /-- Service of the request scheduled at every point of the domain. -/
  serves : ∀ γ ∈ dom, ServesAt real (s γ) γ

namespace Condition

variable {s : Carrier → Request}

/-- **Extension of conditions**: the domain grows and the evaluations of the tuples inside the old
domain are kept, `none` included. -/
instance : Preorder (Condition s) where
  le c c' := c.dom ⊆ c'.dom ∧
    ∀ ⦃n : ℕ⦄ (t : Fin n ↪ Carrier), range t ⊆ c.dom → c'.real.eval t = c.real.eval t
  le_refl _ := ⟨subset_rfl, fun _ _ _ ↦ rfl⟩
  le_trans _ _ _ hab hbc :=
    ⟨hab.1.trans hbc.1, fun _ t ht ↦ (hbc.2 t (ht.trans hab.1)).trans (hab.2 t ht)⟩

theorem le_def {c c' : Condition s} : c ≤ c' ↔ c.dom ⊆ c'.dom ∧
    ∀ ⦃n : ℕ⦄ (t : Fin n ↪ Carrier), range t ⊆ c.dom → c'.real.eval t = c.real.eval t :=
  Iff.rfl

/-- A typed tuple lies inside the domain. -/
theorem range_subset_of_isSome (c : Condition s) {n : ℕ} {t : Fin n ↪ Carrier}
    (ht : (c.real.eval t).isSome) : range t ⊆ c.dom := by
  by_contra h
  simp [c.eval_eq_none t h] at ht

/-- A tuple below a point of the domain followed by that point lies inside the domain. -/
theorem range_extendAt_subset (c : Condition s) (r : Request) {γ : Carrier} (hγ : γ ∈ c.dom)
    (h : ∀ i, r.tuple i < γ) : range (r.extendAt h) ⊆ c.dom := by
  rintro _ ⟨i, rfl⟩
  exact c.isLowerSet_dom (r.extendAt_le h i) hγ

/-- A tuple below a point of the domain lies inside the domain. -/
theorem range_tuple_subset (c : Condition s) (r : Request) {γ : Carrier} (hγ : γ ∈ c.dom)
    (h : ∀ i, r.tuple i < γ) : range r.tuple ⊆ c.dom := by
  rintro _ ⟨i, rfl⟩
  exact c.isLowerSet_dom (h i).le hγ

/-! ### The initial condition -/

/-- The stage type on no points at stage `ω₁` (there is only one, `StageType.eq_of_zero`): the
empty face of the bottom labelling of the one-point scheme. -/
noncomputable def emptyType : StageType.{0} (ω₁ : Ordinal.{0}) 0 :=
  (StageType.restrictFace Function.Embedding.ofIsEmpty
    (Scheme.isLegal_onePoint.toStageType (ω₁ : Ordinal.{0}))).get
    (StageType.isSome_restrictFace_of_zero _ _)

theorem isLegal_emptyType : emptyType.IsLegal :=
  (Scheme.isLegal_onePoint.isLegal_toStageType _).restrictFace _ (Option.some_get _).symm

/-- The realization typing only the empty tuple. -/
noncomputable def initialRealization : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier where
  eval {n} _ := match n with
    | 0 => some emptyType
    | _ + 1 => none

theorem eq_zero_of_isSome_initialRealization {n : ℕ} {t : Fin n ↪ Carrier}
    (ht : (initialRealization.eval t).isSome) : n = 0 := by
  cases n with
  | zero => rfl
  | succ k => simp [initialRealization] at ht

/-- The **initial condition**: empty domain, only the empty tuple typed. -/
noncomputable def initial (s : Carrier → Request) : Condition s where
  dom := ∅
  isLowerSet_dom := isLowerSet_empty
  real := initialRealization
  eval_eq_none n t ht := by
    cases n with
    | zero => exact absurd (by simp [range_eq_empty]) ht
    | succ k => rfl
  isConsistent m n t p f ht := by
    obtain rfl := eq_zero_of_isSome_initialRealization (t := t) (by simp [ht])
    obtain rfl : m = 0 := by simpa using Fintype.card_le_of_embedding f
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (p.isSome_restrictFace_of_zero f)
    rw [hq, StageType.eq_of_zero q emptyType]
    rfl
  isCovering n t ht := by
    refine ⟨n, t, Function.Embedding.refl _, rfl, ?_⟩
    cases n with
    | zero => rfl
    | succ k => exact absurd ht (by simp)
  hasLegalTypes n t p ht := by
    obtain rfl := eq_zero_of_isSome_initialRealization (t := t) (by simp [ht])
    rw [StageType.eq_of_zero p emptyType]
    exact isLegal_emptyType
  hasTopFreeTypes n t p ht := by
    obtain rfl := eq_zero_of_isSome_initialRealization (t := t) (by simp [ht])
    exact StageType.isTopFree_of_zero p
  serves _ h := h.elim

@[simp] theorem initial_dom : (initial s).dom = ∅ := rfl

/-! ### The union of a nonempty chain -/

open Classical in
/-- The **union realization** of a set of conditions: a tuple inside the domain of some member has
the evaluation of a chosen such member, and every other tuple is untyped. -/
noncomputable def unionRealization (C : Set (Condition s)) :
    Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier where
  eval t := if h : ∃ c ∈ C, range t ⊆ c.dom then h.choose.real.eval t else none

/-- **The union realization agrees with every member of a chain** on the tuples inside the domain
of the member: the chosen member and the given one are comparable. -/
theorem eval_unionRealization {C : Set (Condition s)} (hC : IsChain (· ≤ ·) C) {c : Condition s}
    (hc : c ∈ C) {n : ℕ} {t : Fin n ↪ Carrier} (ht : range t ⊆ c.dom) :
    (unionRealization C).eval t = c.real.eval t := by
  simp only [unionRealization]
  split_ifs with h
  swap
  · exact absurd ⟨c, hc, ht⟩ h
  obtain ⟨hc', ht'⟩ := h.choose_spec
  rcases eq_or_ne h.choose c with heq | hne
  · rw [heq]
  rcases hC hc' hc hne with hle | hle
  · exact (hle.2 t ht').symm
  · exact hle.2 t ht

/-- A tuple of the union realization that is typed lies inside the domain of some member, where it
has the same type. -/
theorem exists_of_eval_unionRealization {C : Set (Condition s)} (hC : IsChain (· ≤ ·) C)
    {n : ℕ} {t : Fin n ↪ Carrier} {p : StageType.{0} (ω₁ : Ordinal.{0}) n}
    (ht : (unionRealization C).eval t = some p) :
    ∃ c ∈ C, range t ⊆ c.dom ∧ c.real.eval t = some p := by
  by_cases h : ∃ c ∈ C, range t ⊆ c.dom
  · obtain ⟨c, hc, htc⟩ := h
    exact ⟨c, hc, htc, (eval_unionRealization hC hc htc).symm.trans ht⟩
  · simp [unionRealization, h] at ht

/-- **A finite tuple inside the union of the domains of a nonempty chain lies inside one domain**:
the domains are lower sets of a linear order and the tuple has a largest point. -/
theorem exists_range_subset_dom {C : Set (Condition s)} (hne : C.Nonempty) {n : ℕ}
    {t : Fin n ↪ Carrier} (ht : range t ⊆ ⋃ c ∈ C, c.dom) : ∃ c ∈ C, range t ⊆ c.dom := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · obtain ⟨c, hc⟩ := hne
    exact ⟨c, hc, by simp [range_eq_empty]⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i ↦ t i) Finset.univ_nonempty
  obtain ⟨c, hc, hci⟩ := mem_iUnion₂.mp (ht ⟨i₀, rfl⟩)
  refine ⟨c, hc, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact c.isLowerSet_dom (hi₀ i (Finset.mem_univ _)) hci

/-- The **union** of a nonempty chain of conditions: the union of the domains, with the union
realization. -/
noncomputable def union (C : Set (Condition s)) (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    Condition s where
  dom := ⋃ c ∈ C, c.dom
  isLowerSet_dom := isLowerSet_iUnion₂ fun c _ ↦ c.isLowerSet_dom
  real := unionRealization C
  eval_eq_none n t ht := by
    by_cases h : ∃ c ∈ C, range t ⊆ c.dom
    · obtain ⟨c, hc, htc⟩ := h
      exact absurd (htc.trans (subset_biUnion_of_mem hc)) ht
    · simp [unionRealization, h]
  isConsistent m n t p f ht := by
    obtain ⟨c, hc, htc, htp⟩ := exists_of_eval_unionRealization hC ht
    have hft : range (f.trans t) ⊆ c.dom := by
      rintro _ ⟨i, rfl⟩
      exact htc ⟨f i, rfl⟩
    rw [eval_unionRealization hC hc hft]
    exact c.isConsistent t p f htp
  isCovering n t ht := by
    obtain ⟨c, hc, htc⟩ := exists_range_subset_dom hne ht
    obtain ⟨m, u, f, hfu, hu⟩ := c.isCovering t htc
    exact ⟨m, u, f, hfu, by rwa [eval_unionRealization hC hc (c.range_subset_of_isSome hu)]⟩
  hasLegalTypes n t p ht := by
    obtain ⟨c, -, -, htp⟩ := exists_of_eval_unionRealization hC ht
    exact c.hasLegalTypes t p htp
  hasTopFreeTypes n t p ht := by
    obtain ⟨c, -, -, htp⟩ := exists_of_eval_unionRealization hC ht
    exact c.hasTopFreeTypes t p htp
  serves γ hγ h p ht hd hdt := by
    obtain ⟨c, hc, hγc⟩ := mem_iUnion₂.mp hγ
    rw [eval_unionRealization hC hc (c.range_tuple_subset _ hγc h)] at ht
    rw [eval_unionRealization hC hc (c.range_extendAt_subset _ hγc h)]
    exact c.serves γ hγc h p ht hd hdt

@[simp] theorem union_dom (C : Set (Condition s)) (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    (union C hC hne).dom = ⋃ c ∈ C, c.dom :=
  rfl

/-- **The union is an upper bound** of the chain. -/
theorem le_union {C : Set (Condition s)} (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty)
    {c : Condition s} (hc : c ∈ C) : c ≤ union C hC hne :=
  ⟨subset_biUnion_of_mem hc, fun _ _ ht ↦ eval_unionRealization hC hc ht⟩

/-- **A chain whose domains exhaust the carrier** (for instance a chain whose domains are cofinal
in `ω₁`) has the whole carrier as the domain of its union. -/
theorem union_dom_eq_univ {C : Set (Condition s)} (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty)
    (hcof : ∀ x : Carrier, ∃ c ∈ C, x ∈ c.dom) : (union C hC hne).dom = Set.univ :=
  eq_univ_of_forall fun x ↦ by
    obtain ⟨c, hc, hx⟩ := hcof x
    exact mem_iUnion₂.mpr ⟨c, hc, hx⟩

/-- **Every chain of conditions has an upper bound**: the initial condition for the empty chain,
the union for a nonempty chain.  The service of the scheduled requests is a field of a condition,
so the upper bound serves the request scheduled at every point of its domain. -/
theorem exists_upperBound (C : Set (Condition s)) (hC : IsChain (· ≤ ·) C) :
    ∃ ub : Condition s, ∀ c ∈ C, c ≤ ub := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨initial s, fun _ h ↦ h.elim⟩
  · exact ⟨union C hC hne, fun _ hc ↦ le_union hC hne hc⟩

/-- **Zorn's lemma for conditions**: there is a maximal condition. -/
theorem exists_isMax (s : Carrier → Request) : ∃ c : Condition s, IsMax c :=
  zorn_le fun C hC ↦ exists_upperBound C hC

/-! ### The realization on the domain -/

/-- The **realization on the domain** of a condition: a tuple of the domain has the evaluation of
the same tuple of the carrier. -/
def restrict (c : Condition s) : Realization.{0, 0} (ω₁ : Ordinal.{0}) c.dom where
  eval t := c.real.eval (t.trans (Function.Embedding.subtype _))

theorem restrict_eval (c : Condition s) {n : ℕ} (t : Fin n ↪ c.dom) :
    c.restrict.eval t = c.real.eval (t.trans (Function.Embedding.subtype _)) :=
  rfl

theorem isConsistent_restrict (c : Condition s) : c.restrict.IsConsistent :=
  fun _ _ _ p f ht ↦ c.isConsistent _ p f ht

theorem hasLegalTypes_restrict (c : Condition s) : c.restrict.HasLegalTypes :=
  fun _ _ p ht ↦ c.hasLegalTypes _ p ht

theorem hasTopFreeTypes_restrict (c : Condition s) : c.restrict.HasTopFreeTypes :=
  fun _ _ p ht ↦ c.hasTopFreeTypes _ p ht

theorem isCovering_restrict (c : Condition s) : c.restrict.IsCovering := by
  intro n t
  have ht : range (t.trans (Function.Embedding.subtype _)) ⊆ c.dom := by
    rintro _ ⟨i, rfl⟩
    exact (t i).2
  obtain ⟨m, u, f, hfu, hu⟩ := c.isCovering _ ht
  have hud := c.range_subset_of_isSome hu
  refine ⟨m, u.codRestrict c.dom fun i ↦ hud ⟨i, rfl⟩, f, ?_, hu⟩
  exact Function.Embedding.ext fun i ↦ Subtype.ext (congrArg (fun v : Fin n ↪ Carrier ↦ v i) hfu)

/-- A condition of full domain is exactly consistent and covering on the whole carrier. -/
theorem isCovering_of_dom_eq_univ (c : Condition s) (h : c.dom = Set.univ) : c.real.IsCovering :=
  fun _ t ↦ c.isCovering t (h ▸ subset_univ _)

end Condition

end VaughtConjecture.AlephOne
