/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.OrdinalCountability

/-!
# Filtrations of a class space by countable-loss domains

Roadmap, Layer 0, "Counting and observation", and the counting theorem of Layer 6 via Scott
separation.
A `Filtration X` on a type `X` of isomorphism classes is a family of domains `D ξ ⊆ X` indexed by
the ordinals, of which only the stages `ξ < ω₁` carry information, with

* `D 0 = univ`, `D` antitone, and continuity at limit stages below `ω₁`;
* countable successor losses `D ξ \ D (ξ + 1)` for `ξ < ω₁`;
* cofinally many nonempty successor losses below `ω₁`;
* `D ξ = ∅` for `ω₁ ≤ ξ`, so no data is carried at or above `ω₁` and two filtrations agreeing
  below `ω₁` are equal (`Filtration.ext`).

The **persistent core** `Filtration.core` is `⋂ ξ < ω₁, D ξ`.  Countable complements
(`Filtration.compl_countable`) are InfinitaryLogic's `InfinitaryLogic.compl_countable_of_loss`,
not restated.  The counting theorems are in `VaughtConjecture.Counting.Separation`.

Cf. the proof of [Mon, Lemma XII.8]: for a scattered, minimally unbounded sentence
[Mon, Definition XII.4], the unique unbounded `≡_β`-classes of its models, `β < ω₁`, decrease
and are continuous at limits.  No back-and-forth relation is used here.

## The filtration by a rank

A **rank** on `X` is a map `r : X → Ordinal.{0}` into the countable ordinals (`r x < ω₁`) whose
fibres `{x | r x = α}` over the countable ordinals `α < ω₁` are countable (the form of
InfinitaryLogic's `InfinitaryLogic.countable_iff_rank_bounded`).  Its **tails** `{x | η ≤ r x}`
form a filtration (`Filtration.ofRank`) exactly when `X` is uncountable:

* the tail at `0` is everything, the tails decrease, and they are continuous at limits because
  the condition `η ≤ r x` is closed under suprema of `η`; the loss at `η` is the fibre over `η`
  (`Filtration.sdiff_domain_ofRank`), hence countable;
* every tail at a stage `≥ ω₁` is empty, and so is the persistent core
  (`Filtration.core_ofRank`): every class leaves the tail just above its rank;
* nonempty losses occur cofinally below `ω₁` exactly when the ranks are unbounded below `ω₁`,
  that is, exactly when `X` is uncountable (`forall_exists_le_rank_iff`, from InfinitaryLogic's
  `InfinitaryLogic.countable_iff_rank_bounded`).  Uncountability is the only hypothesis of
  `Filtration.ofRank` beyond the rank itself.

The complement of the tail at a countable stage, the classes of smaller rank, is countable with
no hypothesis on `X` (`countable_setOf_rank_lt`).

A **countable cover** `Q α` (`α < ω₁`) of `X` by countable sets gives a rank, the **least level**
`leastLevel Q x`, the least `α < ω₁` with `x ∈ Q α`; its fibres lie in the sets `Q α`, and the
tail at `η` is the set of classes in no `Q α` with `α < η`
(`Filtration.domain_ofCountableCover`).  The resulting filtration is
`Filtration.ofCountableCover`.  The bound `#X ≤ ℵ₁` for a rank, and for a countable cover, is in
`VaughtConjecture.Counting.Separation`.

## Indexing

The index is `Ordinal.{0}` with the bound `ξ < ω₁`, and the successor stage is `ξ + 1`.  This
is the form of the hypotheses of `compl_countable_of_loss`, and for ordinals `Order.succ ξ` is
definitionally `ξ + 1`, so `exists_injective_mem_sdiff_succ` of `Counting.Domains` applies
unchanged.  The roadmap sketch `SentenceAgreementDomains` indexes its domains by
`Set.Iio (aleph 1).ord` and assumes countable complements outright; here the complements are
derived from countable losses and limit continuity, and the stages at or above `ω₁` carry no
data: every such domain is empty (`(aleph 1).ord = ω₁` by `Cardinal.ord_aleph`).  Restricting
`domain` to `Set.Iio ω₁` is therefore injective and gives the sketch's `domain` and
`complement_countable` fields; its `homogeneous` and `separates` fields are the hypotheses of
`Filtration.mk_eq_aleph_one_of_separation`.

## References

Scattered sentences are those of [Mon, §XII.1] (countably many `≡_α`-classes for every
`α < ω₁`); minimally unbounded sentences are [Mon, Definition XII.4], and the decreasing unbounded
`≡_β`-classes are in the proof of [Mon, Lemma XII.8], for A. Montalbán, *Computable Structure
Theory: Beyond the arithmetic* (draft, 22 April 2025).
-/

namespace VaughtConjecture.Counting

open Set
open scoped Ordinal

universe u

/-- A **filtration** of a type `X` of classes by domains indexed by the countable ordinals:
`D 0 = univ`, antitone, continuous at limits below `ω₁`, with countable successor losses below
`ω₁` and cofinally many nonempty successor losses below `ω₁`.  The domains at stages `ξ ≥ ω₁`
are empty, so a filtration is determined by its stages below `ω₁`. -/
structure Filtration (X : Type u) where
  /-- The domain at stage `ξ`. -/
  domain : Ordinal.{0} → Set X
  /-- The first domain is everything. -/
  zero : domain 0 = univ
  /-- The domains decrease. -/
  antitone : Antitone domain
  /-- At a limit stage below `ω₁` the domain contains the intersection of the earlier ones. -/
  limit : ∀ l, Order.IsSuccLimit l → l < ω₁ → (⋂ ξ < l, domain ξ) ⊆ domain l
  /-- Each successor loss below `ω₁` is countable. -/
  loss_countable : ∀ ξ, ξ < ω₁ → (domain ξ \ domain (ξ + 1)).Countable
  /-- Nonempty successor losses occur cofinally below `ω₁`. -/
  cofinal_losses : ∀ β, β < ω₁ → ∃ ξ, β ≤ ξ ∧ ξ < ω₁ ∧ (domain ξ \ domain (ξ + 1)).Nonempty
  /-- No data is carried at or above `ω₁`: the domains there are empty. -/
  domain_eq_empty_of_omega_one_le : ∀ ξ, ω₁ ≤ ξ → domain ξ = ∅

namespace Filtration

variable {X : Type u} (F : Filtration X)

/-- Two filtrations agreeing below `ω₁` are equal: at and above `ω₁` both domains are empty. -/
@[ext]
theorem ext {F G : Filtration X} (h : ∀ ξ, ξ < ω₁ → F.domain ξ = G.domain ξ) : F = G := by
  obtain ⟨D, _, _, _, _, _, hD⟩ := F
  obtain ⟨E, _, _, _, _, _, hE⟩ := G
  congr
  funext ξ
  rcases lt_or_ge ξ ω₁ with hξ | hξ
  · exact h ξ hξ
  · rw [hD ξ hξ, hE ξ hξ]

/-- The **persistent core**: the classes lying in every domain below `ω₁`. -/
def core : Set X := ⋂ ξ < ω₁, F.domain ξ

@[simp]
theorem mem_core_iff {x : X} : x ∈ F.core ↔ ∀ ξ, ξ < ω₁ → x ∈ F.domain ξ :=
  mem_iInter₂

/-- Countable losses and limit continuity give countable complements below `ω₁`
(InfinitaryLogic's `compl_countable_of_loss`). -/
theorem compl_countable {β : Ordinal.{0}} (hβ : β < ω₁) : (F.domain β)ᶜ.Countable :=
  InfinitaryLogic.compl_countable_of_loss F.domain F.zero F.loss_countable F.limit β hβ

end Filtration

/-! ### The filtration by a rank -/

section Rank

variable {X : Type u} (r : X → Ordinal.{0})

/-- **Small ranks are countable**: for a rank with countable fibres, the classes of rank below a
countable ordinal form a countable set. -/
theorem countable_setOf_rank_lt (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable)
    {η : Ordinal.{0}} (hη : η < ω₁) : {x | r x < η}.Countable :=
  ((InfinitaryLogic.setCountable_Iio_of_lt_omega1 η hη).biUnion fun α hα ↦
    hfib α (lt_trans hα hη)).mono
    fun x hx ↦ mem_iUnion₂.2 ⟨r x, hx, rfl⟩

/-- **Cofinal ranks exactly for uncountable classes**: for a rank into the countable ordinals
with countable fibres, the ranks are unbounded below `ω₁` exactly when `X` is uncountable
(InfinitaryLogic's `countable_iff_rank_bounded`). -/
theorem forall_exists_le_rank_iff (hr : ∀ x, r x < ω₁)
    (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable) :
    (∀ β, β < ω₁ → ∃ x, β ≤ r x) ↔ ¬ Countable X := by
  rw [← countable_univ_iff,
    InfinitaryLogic.countable_iff_rank_bounded r hr fun α hα ↦ (hfib α hα).to_subtype]
  simp only [mem_univ, forall_const, not_exists, not_and, not_forall, not_lt]

/-- No class lies in every tail of a rank into the countable ordinals: each leaves the tail just
above its rank. -/
theorem iInter_setOf_le_rank_eq_empty (hr : ∀ x, r x < ω₁) :
    (⋂ ξ < ω₁, {x | ξ ≤ r x}) = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ (Order.lt_succ (r x)).not_ge
    (mem_iInter₂.1 hx _ ((Cardinal.isSuccLimit_omega 1).succ_lt (hr x)))

namespace Filtration

/-- **The filtration by a rank**: for a rank `r` into the countable ordinals with countable
fibres on an uncountable type, the tails `{x | η ≤ r x}`.  The loss at `η` is the fibre over `η`,
continuity at limits holds because the tails are defined by a lower bound on the rank, and
uncountability gives the cofinal nonempty losses (`forall_exists_le_rank_iff`). -/
def ofRank (hr : ∀ x, r x < ω₁) (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable)
    (hX : ¬ Countable X) : Filtration X where
  domain η := {x | η ≤ r x}
  zero := eq_univ_of_forall fun x ↦ (zero_le : (0 : Ordinal) ≤ r x)
  antitone _ _ h _ hx := h.trans hx
  limit l hl _ x hx := by
    by_contra h
    exact (Order.lt_succ (r x)).not_ge (mem_iInter₂.1 hx _ (hl.succ_lt (not_le.1 h)))
  loss_countable ξ hξ := (hfib ξ hξ).mono fun x hx ↦
    (Order.lt_add_one_iff.1 (not_le.1 hx.2)).antisymm hx.1
  cofinal_losses β hβ :=
    have ⟨x, hx⟩ := (forall_exists_le_rank_iff r hr hfib).2 hX β hβ
    ⟨r x, hx, hr x, x, le_refl (r x), (Order.lt_add_one_iff.2 (le_refl (r x))).not_ge⟩
  domain_eq_empty_of_omega_one_le _ h :=
    eq_empty_of_forall_notMem fun x hx ↦ (h.trans hx).not_gt (hr x)

variable {r} {hr : ∀ x, r x < ω₁} {hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable}
  {hX : ¬ Countable X}

/-- The domain of the filtration by a rank at `η` is the tail `{x | η ≤ r x}`. -/
theorem domain_ofRank (η : Ordinal.{0}) : (ofRank r hr hfib hX).domain η = {x | η ≤ r x} :=
  rfl

@[simp]
theorem mem_domain_ofRank {η : Ordinal.{0}} {x : X} :
    x ∈ (ofRank r hr hfib hX).domain η ↔ η ≤ r x :=
  Iff.rfl

/-- The loss of the filtration by a rank at `η` is the fibre over `η`. -/
theorem sdiff_domain_ofRank (η : Ordinal.{0}) :
    (ofRank r hr hfib hX).domain η \ (ofRank r hr hfib hX).domain (η + 1) = {x | r x = η} :=
  Set.ext fun _ ↦ ⟨fun hx ↦ (Order.lt_add_one_iff.1 (not_le.1 hx.2)).antisymm hx.1,
    fun hx ↦ ⟨hx.ge, fun h ↦ (Order.lt_add_one_iff.2 hx.le).not_ge h⟩⟩

/-- **The persistent core of the filtration by a rank is empty.** -/
@[simp]
theorem core_ofRank : (ofRank r hr hfib hX).core = ∅ :=
  iInter_setOf_le_rank_eq_empty r hr

end Filtration

/-! ### The least level of a countable cover -/

variable {r}

/-- The **least level** of `x` in a family `Q α` of sets indexed by the ordinals: the least
`α < ω₁` with `x ∈ Q α` (`0` if there is none). -/
noncomputable def leastLevel (Q : Ordinal.{0} → Set X) (x : X) : Ordinal.{0} :=
  sInf {α | α < ω₁ ∧ x ∈ Q α}

variable {Q : Ordinal.{0} → Set X}

/-- For a cover by the sets `Q α` with `α < ω₁`, the least level of `x` is a countable ordinal
`α` with `x ∈ Q α`. -/
theorem leastLevel_lt_and_mem (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) (x : X) :
    leastLevel Q x < ω₁ ∧ x ∈ Q (leastLevel Q x) :=
  csInf_mem (hcover x)

/-- The least level of `x` is at most every countable level of a set `Q α` containing `x`. -/
theorem leastLevel_le {α : Ordinal.{0}} {x : X} (hα : α < ω₁) (hx : x ∈ Q α) :
    leastLevel Q x ≤ α :=
  csInf_le' ⟨hα, hx⟩

/-- For a cover by the sets `Q α` with `α < ω₁`, the least level of `x` is at least `η` exactly
when `x` lies in no `Q α` with `α < η`. -/
theorem le_leastLevel_iff (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) {η : Ordinal.{0}} {x : X} :
    η ≤ leastLevel Q x ↔ x ∉ ⋃ α < η, Q α := by
  have hx := leastLevel_lt_and_mem hcover x
  simp only [mem_iUnion₂, not_exists]
  refine ⟨fun hη α hαη hxα ↦ ?_, fun h ↦ not_lt.1 fun hlt ↦ h _ hlt hx.2⟩
  rcases lt_or_ge α ω₁ with hα | hα
  · exact (leastLevel_le hα hxα).not_gt (hαη.trans_le hη)
  · exact (hx.1.trans_le hα).not_ge (hη.trans' hαη.le)

/-- For a cover by countable sets `Q α` with `α < ω₁`, the fibres of the least level over the
countable ordinals are countable: the fibre over `α` lies in `Q α`. -/
theorem countable_setOf_leastLevel_eq (hQ : ∀ α, α < ω₁ → (Q α).Countable)
    (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) (α : Ordinal.{0}) (hα : α < ω₁) :
    {x | leastLevel Q x = α}.Countable :=
  (hQ α hα).mono fun x hx ↦ hx ▸ (leastLevel_lt_and_mem hcover x).2

namespace Filtration

/-- **The filtration by a countable cover**: for a cover of an uncountable type by countable sets
`Q α` with `α < ω₁`, the filtration by the least level, whose domain at `η` is the set of classes
in no `Q α` with `α < η` (`domain_ofCountableCover`). -/
noncomputable def ofCountableCover (Q : Ordinal.{0} → Set X)
    (hQ : ∀ α, α < ω₁ → (Q α).Countable) (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α)
    (hX : ¬ Countable X) : Filtration X :=
  ofRank (leastLevel Q) (fun x ↦ (leastLevel_lt_and_mem hcover x).1)
    (countable_setOf_leastLevel_eq hQ hcover) hX

/-- The domain of the filtration by a countable cover at `η` is the set of classes in no `Q α`
with `α < η`. -/
theorem domain_ofCountableCover {hQ : ∀ α, α < ω₁ → (Q α).Countable}
    {hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α} {hX : ¬ Countable X} (η : Ordinal.{0}) :
    (ofCountableCover Q hQ hcover hX).domain η = (⋃ α < η, Q α)ᶜ :=
  Set.ext fun _ ↦ le_leastLevel_iff hcover

end Filtration

end Rank

end VaughtConjecture.Counting
