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
InfinitaryLogic's `InfinitaryLogic.countable_iff_rank_bounded`).  Its **tails**
`InfinitaryLogic.rankTail r η = {x | η ≤ r x}` form a filtration (`Filtration.ofRank`) exactly
when `X` is uncountable:

* the tail at `0` is everything, the tails decrease, and they are continuous at limits because
  the condition `η ≤ r x` is closed under suprema of `η`; the loss at `η` is the fibre over `η`
  (`Filtration.sdiff_domain_ofRank`), hence countable;
* every tail at a stage `≥ ω₁` is empty, and so is the persistent core
  (`Filtration.core_ofRank`): every class leaves the tail just above its rank;
* nonempty losses occur cofinally below `ω₁` exactly when the ranks are unbounded below `ω₁`,
  that is, exactly when `X` is uncountable (`forall_exists_le_rank_iff`, and InfinitaryLogic's
  `InfinitaryLogic.rankTail_cofinal_losses_iff` in the form of the losses).  Uncountability is
  the only hypothesis of `Filtration.ofRank` beyond the rank itself.

The complement of the tail at a countable stage, the classes of smaller rank, is countable with
no hypothesis on `X` (`countable_setOf_rank_lt`).

A **countable cover** `Q α` (`α < ω₁`) of `X` by countable sets gives a rank, the **least level**
`leastLevel Q x`, the least `α < ω₁` with `x ∈ Q α`; its fibres lie in the sets `Q α`, and the
tail at `η` is the set of classes in no `Q α` with `α < η`
(`Filtration.domain_ofCountableCover`).  The resulting filtration is
`Filtration.ofCountableCover`.  The bound `#X ≤ ℵ₁` for a rank, and for a countable cover, is in
`VaughtConjecture.Counting.Separation`.

## InfinitaryLogic's rank tails and least levels

The results about ranks and least levels are proved as quotations of InfinitaryLogic's
`OrdinalCountability` (at the pin), with the statements kept in the form used here.

* `Filtration.ofRank` has domain `InfinitaryLogic.rankTail r`, each field one lemma of
  InfinitaryLogic, so `Filtration.domain_ofRank` holds by definition.
* The fibres are sets here, `{x | r x = α}.Countable`, and subtypes there,
  `Countable {x // r x = α}`; `Set.Countable.to_subtype` converts.
* `leastLevel Q` is by definition InfinitaryLogic's `InfinitaryLogic.leastLevel` of the family
  restricted to levels below `ω₁` (`leastLevel_eq_leastLevel_inter`), and under the cover it is
  InfinitaryLogic's least level of `Q` itself (`leastLevel_eq_leastLevel_of_cover`).
  InfinitaryLogic's is `sInf {α | x ∈ Q α}` with the global cover `(⋃ α < ω₁, Q α) = univ`;
  `leastLevel` is `sInf {α | α < ω₁ ∧ x ∈ Q α}` with the pointwise cover
  `∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α` (`biUnion_lt_omega_one_eq_univ`).  They differ only at a point with
  a level at or above `ω₁` and none below, where `leastLevel` is `0`; `leastLevel` is always below
  `ω₁`.  The examples at the end of this file record the levels at or above `ω₁`, the degenerate
  cases, and the equality of `Filtration.ofCountableCover` with the filtration by
  InfinitaryLogic's least level (by `Filtration.ext`, not by definition).

Kept here, with no counterpart in InfinitaryLogic: the structure `Filtration` and
`Filtration.ext`, `Filtration.core` and `Filtration.mem_core_iff`.  The structure is the
hypothesis of the counting theorem with a countable persistent core
(`Filtration.mk_eq_aleph_one_of_separation` of `VaughtConjecture.Counting.Separation`), which
allows a nonempty core; InfinitaryLogic's `InfinitaryLogic.mk_eq_aleph_one_of_domains` requires
every point to leave some domain.  The restriction `α < ω₁` inside `leastLevel` is kept so that
the least level is below `ω₁` with no hypothesis.

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
countable ordinal form a countable set.  A quotation of InfinitaryLogic's
`InfinitaryLogic.countable_of_forall_rank_lt` (at the pin), with the fibres as sets. -/
theorem countable_setOf_rank_lt (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable)
    {η : Ordinal.{0}} (hη : η < ω₁) : {x | r x < η}.Countable :=
  InfinitaryLogic.countable_of_forall_rank_lt r (fun α hα ↦ (hfib α hα).to_subtype) hη
    fun _ h ↦ h

/-- **Cofinal ranks exactly for uncountable classes**: for a rank into the countable ordinals
with countable fibres, the ranks are unbounded below `ω₁` exactly when `X` is uncountable.  A
quotation of InfinitaryLogic's `InfinitaryLogic.countable_iff_rank_bounded` (at the pin) on
`univ`; the same equivalence with cofinally many nonempty losses of the tails in place of
unbounded ranks is `InfinitaryLogic.rankTail_cofinal_losses_iff`. -/
theorem forall_exists_le_rank_iff (hr : ∀ x, r x < ω₁)
    (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable) :
    (∀ β, β < ω₁ → ∃ x, β ≤ r x) ↔ ¬ Countable X := by
  rw [← countable_univ_iff,
    InfinitaryLogic.countable_iff_rank_bounded r hr fun α hα ↦ (hfib α hα).to_subtype]
  simp only [mem_univ, forall_const, not_exists, not_and, not_forall, not_lt]

/-- No class lies in every tail of a rank into the countable ordinals: each leaves the tail just
above its rank.  A quotation of InfinitaryLogic's `InfinitaryLogic.biInter_rankTail_eq_empty`
(at the pin). -/
theorem iInter_setOf_le_rank_eq_empty (hr : ∀ x, r x < ω₁) :
    (⋂ ξ < ω₁, {x | ξ ≤ r x}) = ∅ :=
  InfinitaryLogic.biInter_rankTail_eq_empty r hr

namespace Filtration

/-- **The filtration by a rank**: for a rank `r` into the countable ordinals with countable
fibres on an uncountable type, the tails `InfinitaryLogic.rankTail r η = {x | η ≤ r x}`.  Each
field is one lemma of InfinitaryLogic's `OrdinalCountability` (at the pin): the loss at `η` is the
fibre over `η` (`rankTail_loss_countable`), continuity at limits is
`rankTail_eq_iInter_of_isSuccLimit`, and uncountability gives the cofinal nonempty losses
(`rankTail_cofinal_losses_iff`). -/
def ofRank (hr : ∀ x, r x < ω₁) (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable)
    (hX : ¬ Countable X) : Filtration X where
  domain := InfinitaryLogic.rankTail r
  zero := InfinitaryLogic.rankTail_zero r
  antitone := InfinitaryLogic.rankTail_antitone r
  limit _ hl _ := (InfinitaryLogic.rankTail_eq_iInter_of_isSuccLimit r hl).ge
  loss_countable ξ _ :=
    InfinitaryLogic.rankTail_loss_countable r hr (fun α hα ↦ (hfib α hα).to_subtype) ξ
  cofinal_losses :=
    (InfinitaryLogic.rankTail_cofinal_losses_iff r hr fun α hα ↦ (hfib α hα).to_subtype).2 hX
  domain_eq_empty_of_omega_one_le _ h := InfinitaryLogic.rankTail_eq_empty_of_omega1_le r hr h

variable {r} {hr : ∀ x, r x < ω₁} {hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable}
  {hX : ¬ Countable X}

/-- The domain of the filtration by a rank at `η` is the tail `{x | η ≤ r x}`, which is
InfinitaryLogic's `InfinitaryLogic.rankTail r η` by definition. -/
theorem domain_ofRank (η : Ordinal.{0}) : (ofRank r hr hfib hX).domain η = {x | η ≤ r x} :=
  rfl

/-- A class lies in the domain of the filtration by a rank at `η` exactly when its rank is at
least `η`.  A quotation of InfinitaryLogic's `InfinitaryLogic.mem_rankTail` (at the pin). -/
@[simp]
theorem mem_domain_ofRank {η : Ordinal.{0}} {x : X} :
    x ∈ (ofRank r hr hfib hX).domain η ↔ η ≤ r x :=
  InfinitaryLogic.mem_rankTail

/-- The loss of the filtration by a rank at `η` is the fibre over `η`.  A quotation of
InfinitaryLogic's `InfinitaryLogic.rankTail_diff_succ` (at the pin); `Order.succ η` is
definitionally `η + 1`. -/
theorem sdiff_domain_ofRank (η : Ordinal.{0}) :
    (ofRank r hr hfib hX).domain η \ (ofRank r hr hfib hX).domain (η + 1) = {x | r x = η} :=
  InfinitaryLogic.rankTail_diff_succ r η

/-- **The persistent core of the filtration by a rank is empty.**  A quotation of
InfinitaryLogic's `InfinitaryLogic.biInter_rankTail_eq_empty` (at the pin), which needs only the
bound `r x < ω₁`. -/
@[simp]
theorem core_ofRank : (ofRank r hr hfib hX).core = ∅ :=
  InfinitaryLogic.biInter_rankTail_eq_empty r hr

end Filtration

/-! ### The least level of a countable cover -/

variable {r}

/-- The **least level** of `x` in a family `Q α` of sets indexed by the ordinals: the least
`α < ω₁` with `x ∈ Q α` (`0` if there is none).

This is by definition InfinitaryLogic's `InfinitaryLogic.leastLevel` of the family restricted to
levels below `ω₁`, `fun α ↦ {x | α < ω₁ ∧ x ∈ Q α}` (`leastLevel_eq_leastLevel_inter`).  The two
conventions differ as follows.

* InfinitaryLogic's least level is `sInf {α | x ∈ Q α}`, over all ordinals.  Its lemmas assume
  the global cover `(⋃ α < ω₁, Q α) = univ`, except `InfinitaryLogic.leastLevel_le_of_mem` and
  `InfinitaryLogic.leastLevel_mem_of_exists`, which assume none.
* `leastLevel` is `sInf {α | α < ω₁ ∧ x ∈ Q α}`, so it is below `ω₁` with no hypothesis (an
  example at the end of this file), and the lemmas below assume the pointwise cover
  `∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α`, which gives the global one (`biUnion_lt_omega_one_eq_univ`).
* They differ exactly at a point with a level at or above `ω₁` and none below: if
  `Q α = univ` for `ω₁ ≤ α` and `Q α = ∅` below, `leastLevel` is `0` and InfinitaryLogic's is
  `ω₁`.  Under the cover they are equal (`leastLevel_eq_leastLevel_of_cover`), so every lemma below
  with a covering hypothesis is a quotation of InfinitaryLogic's. -/
noncomputable def leastLevel (Q : Ordinal.{0} → Set X) (x : X) : Ordinal.{0} :=
  sInf {α | α < ω₁ ∧ x ∈ Q α}

variable {Q : Ordinal.{0} → Set X}

/-- The least level `leastLevel Q` is InfinitaryLogic's `InfinitaryLogic.leastLevel` of the
family restricted to levels below `ω₁`, by definition. -/
theorem leastLevel_eq_leastLevel_inter (Q : Ordinal.{0} → Set X) :
    leastLevel Q = InfinitaryLogic.leastLevel fun α ↦ {x | α < ω₁ ∧ x ∈ Q α} :=
  rfl

/-- The pointwise cover by the sets `Q α`, `α < ω₁`, is InfinitaryLogic's covering hypothesis
`(⋃ α < ω₁, Q α) = univ`. -/
theorem biUnion_lt_omega_one_eq_univ (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) :
    (⋃ α < ω₁, Q α) = univ :=
  eq_univ_of_forall fun x ↦ (hcover x).elim fun α h ↦ mem_iUnion₂.2 ⟨α, h.1, h.2⟩

/-- For a cover by the sets `Q α` with `α < ω₁`, the least level of `x` is a countable ordinal
`α` with `x ∈ Q α`.  A quotation of InfinitaryLogic's `InfinitaryLogic.leastLevel_mem_of_exists`
(at the pin) for the family restricted to levels below `ω₁`, through the definitional equality
`leastLevel_eq_leastLevel_inter`. -/
theorem leastLevel_lt_and_mem (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) (x : X) :
    leastLevel Q x < ω₁ ∧ x ∈ Q (leastLevel Q x) :=
  InfinitaryLogic.leastLevel_mem_of_exists (Q := fun α ↦ {x | α < ω₁ ∧ x ∈ Q α}) (hcover x)

/-- The least level of `x` is at most every countable level of a set `Q α` containing `x`.  A
quotation of InfinitaryLogic's `InfinitaryLogic.leastLevel_le_of_mem` (at the pin) for the family
restricted to levels below `ω₁`, through the definitional equality
`leastLevel_eq_leastLevel_inter`. -/
theorem leastLevel_le {α : Ordinal.{0}} {x : X} (hα : α < ω₁) (hx : x ∈ Q α) :
    leastLevel Q x ≤ α :=
  InfinitaryLogic.leastLevel_le_of_mem (Q := fun α ↦ {x | α < ω₁ ∧ x ∈ Q α}) ⟨hα, hx⟩

/-- **The least level is InfinitaryLogic's under the cover.**  For a cover by the sets `Q α` with
`α < ω₁`, `leastLevel Q` is InfinitaryLogic's `InfinitaryLogic.leastLevel Q`: each is at most the
other, by `InfinitaryLogic.leastLevel_le_of_mem` and `leastLevel_le`. -/
theorem leastLevel_eq_leastLevel_of_cover (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) :
    leastLevel Q = InfinitaryLogic.leastLevel Q :=
  have hU := biUnion_lt_omega_one_eq_univ hcover
  funext fun x ↦ le_antisymm
    (leastLevel_le (InfinitaryLogic.leastLevel_lt_omega1 Q hU x)
      (InfinitaryLogic.leastLevel_mem Q hU x))
    (InfinitaryLogic.leastLevel_le_of_mem (leastLevel_lt_and_mem hcover x).2)

/-- For a cover by the sets `Q α` with `α < ω₁`, the least level of `x` is at least `η` exactly
when `x` lies in no `Q α` with `α < η`.  A quotation of InfinitaryLogic's
`InfinitaryLogic.rankTail_leastLevel` (at the pin), through
`leastLevel_eq_leastLevel_of_cover`. -/
theorem le_leastLevel_iff (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) {η : Ordinal.{0}} {x : X} :
    η ≤ leastLevel Q x ↔ x ∉ ⋃ α < η, Q α := by
  rw [leastLevel_eq_leastLevel_of_cover hcover]
  exact Set.ext_iff.1 (InfinitaryLogic.rankTail_leastLevel Q
    (biUnion_lt_omega_one_eq_univ hcover) η) x

/-- For a cover by countable sets `Q α` with `α < ω₁`, the fibres of the least level over the
countable ordinals are countable: the fibre over `α` lies in `Q α`.  A quotation of
InfinitaryLogic's `InfinitaryLogic.setOf_leastLevel_eq_subset` (at the pin), through
`leastLevel_eq_leastLevel_of_cover`. -/
theorem countable_setOf_leastLevel_eq (hQ : ∀ α, α < ω₁ → (Q α).Countable)
    (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) (α : Ordinal.{0}) (hα : α < ω₁) :
    {x | leastLevel Q x = α}.Countable := by
  rw [leastLevel_eq_leastLevel_of_cover hcover]
  exact (hQ α hα).mono
    (InfinitaryLogic.setOf_leastLevel_eq_subset Q (biUnion_lt_omega_one_eq_univ hcover) α)

namespace Filtration

/-- **The filtration by a countable cover**: for a cover of an uncountable type by countable sets
`Q α` with `α < ω₁`, the filtration by the least level, whose domain at `η` is the set of classes
in no `Q α` with `α < η` (`domain_ofCountableCover`).  It is the filtration by InfinitaryLogic's
`InfinitaryLogic.leastLevel Q`, equal to it by `Filtration.ext` (not by definition, since the two
least levels are only equal under the cover). -/
noncomputable def ofCountableCover (Q : Ordinal.{0} → Set X)
    (hQ : ∀ α, α < ω₁ → (Q α).Countable) (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α)
    (hX : ¬ Countable X) : Filtration X :=
  ofRank (leastLevel Q) (fun x ↦ (leastLevel_lt_and_mem hcover x).1)
    (countable_setOf_leastLevel_eq hQ hcover) hX

/-- The domain of the filtration by a countable cover at `η` is the set of classes in no `Q α`
with `α < η`.  A quotation of InfinitaryLogic's `InfinitaryLogic.rankTail_leastLevel` (at the
pin), through `leastLevel_eq_leastLevel_of_cover`. -/
theorem domain_ofCountableCover {hQ : ∀ α, α < ω₁ → (Q α).Countable}
    {hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α} {hX : ¬ Countable X} (η : Ordinal.{0}) :
    (ofCountableCover Q hQ hcover hX).domain η = (⋃ α < η, Q α)ᶜ :=
  (congrArg (InfinitaryLogic.rankTail · η) (leastLevel_eq_leastLevel_of_cover hcover)).trans
    (InfinitaryLogic.rankTail_leastLevel Q (biUnion_lt_omega_one_eq_univ hcover) η)

end Filtration

end Rank

/-! ### Examples: levels at or above `ω₁` and the degenerate cases -/

section Examples

open InfinitaryLogic in
/-- The filtration by a rank has InfinitaryLogic's tails as its domains, by definition. -/
example {X : Type u} (r : X → Ordinal.{0}) (hr : ∀ x, r x < ω₁)
    (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable) (hX : ¬ Countable X) :
    (Filtration.ofRank r hr hfib hX).domain = rankTail r :=
  rfl

open InfinitaryLogic in
/-- The filtration by a countable cover is the filtration by InfinitaryLogic's least level, by
`Filtration.ext`. -/
example {X : Type u} (Q : Ordinal.{0} → Set X) (hQ : ∀ α, α < ω₁ → (Q α).Countable)
    (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) (hX : ¬ Countable X) :
    Filtration.ofCountableCover Q hQ hcover hX = Filtration.ofRank (InfinitaryLogic.leastLevel Q)
      (leastLevel_lt_omega1 Q (biUnion_lt_omega_one_eq_univ hcover))
      (fun α hα ↦ (hQ α hα).mono
        (setOf_leastLevel_eq_subset Q (biUnion_lt_omega_one_eq_univ hcover) α)) hX :=
  Filtration.ext fun η _ ↦ (Filtration.domain_ofCountableCover η).trans
    (rankTail_leastLevel Q (biUnion_lt_omega_one_eq_univ hcover) η).symm

/-- The least level `leastLevel Q` is below `ω₁` with no covering hypothesis. -/
example {X : Type u} (Q : Ordinal.{0} → Set X) (x : X) : leastLevel Q x < ω₁ := by
  rcases {α | α < ω₁ ∧ x ∈ Q α}.eq_empty_or_nonempty with h | h
  · rw [leastLevel, h, Ordinal.sInf_empty]
    exact Ordinal.omega_pos 1
  · exact (csInf_mem h).1

/-- **Levels at or above `ω₁`.**  For a family whose levels are all at or above `ω₁`,
`leastLevel` is `0` and InfinitaryLogic's least level is `ω₁`: there is no cover below `ω₁`. -/
example : leastLevel (fun α ↦ {_u : Unit | ω₁ ≤ α}) () = 0 ∧
    InfinitaryLogic.leastLevel (fun α ↦ {_u : Unit | ω₁ ≤ α}) () = ω₁ := by
  refine ⟨?_, csInf_Ici⟩
  rw [leastLevel, ← Ordinal.sInf_empty]
  exact congrArg sInf (eq_empty_of_forall_notMem fun α hα ↦ hα.1.not_ge hα.2)

/-- With no cover, the two least levels still agree when the family is empty from `ω₁` on, as for
the levels `MainTheorem.FullPresentations.presentedAt` of full presentations. -/
example {X : Type u} {Q : Ordinal.{0} → Set X} (hQ : ∀ α, ω₁ ≤ α → Q α = ∅) :
    leastLevel Q = InfinitaryLogic.leastLevel Q :=
  funext fun x ↦ congrArg sInf <| Set.ext fun α ↦
    ⟨fun h ↦ h.2, fun h ↦ ⟨not_le.1 fun hα ↦ by simp [hQ α hα] at h, h⟩⟩

/-- **Overlapping levels**: when every `Q α` is everything, both least levels are `0`. -/
example {X : Type u} (x : X) : leastLevel (fun _ ↦ (univ : Set X)) x = 0 ∧
    InfinitaryLogic.leastLevel (fun _ ↦ (univ : Set X)) x = 0 :=
  ⟨nonpos_iff_eq_zero.1 (leastLevel_le (Ordinal.omega_pos 1) (mem_univ x)),
    nonpos_iff_eq_zero.1 (InfinitaryLogic.leastLevel_le_of_mem (mem_univ x))⟩

/-- **An empty type** is covered by every family, and the two least levels agree. -/
example (Q : Ordinal.{0} → Set Empty) : leastLevel Q = InfinitaryLogic.leastLevel Q :=
  leastLevel_eq_leastLevel_of_cover (·.elim)

open InfinitaryLogic in
/-- **A countable type has no cofinal losses**: for the rank `n ↦ n` on `ℕ`, nonempty losses of
the tails do not occur cofinally below `ω₁`, so `ℕ` carries no filtration by a rank. -/
example : ¬ ∀ β < ω₁, ∃ ξ, β ≤ ξ ∧ ξ < ω₁ ∧
    (rankTail (fun n : ℕ ↦ (n : Ordinal.{0})) ξ \
      rankTail (fun n : ℕ ↦ (n : Ordinal.{0})) (Order.succ ξ)).Nonempty := fun h ↦
  (rankTail_cofinal_losses_iff _ (fun n ↦ (Ordinal.natCast_lt_omega0 n).trans
    Ordinal.omega0_lt_omega_one) fun _ _ ↦ inferInstance).1 h inferInstance

/-- From `ω₁` on, the domains of the filtration by a countable cover are empty: every class lies
in some `Q α` with `α < ω₁`. -/
example {X : Type u} {Q : Ordinal.{0} → Set X} (hQ : ∀ α, α < ω₁ → (Q α).Countable)
    (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) (hX : ¬ Countable X) {η : Ordinal.{0}}
    (hη : ω₁ ≤ η) : (⋃ α < η, Q α)ᶜ = ∅ :=
  (Filtration.domain_ofCountableCover (hQ := hQ) (hcover := hcover) (hX := hX) η).symm.trans
    ((Filtration.ofCountableCover Q hQ hcover hX).domain_eq_empty_of_omega_one_le η hη)

end Examples

end VaughtConjecture.Counting
