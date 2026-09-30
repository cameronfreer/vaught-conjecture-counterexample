/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.Assembly

/-!
# Examples of the conditional composition

The hypotheses of `VaughtConjecture.MainTheorem.Assembly` on abstract types of classes (the
countable ordinals, with or without `2 ^ ℵ₁` further classes, and a single class), with the
observations "is the class `s`", which separate distinct classes.

* The **tail domains** of the countable ordinals (stage `ξ` keeps the ordinals `≥ ξ`) satisfy
  every hypothesis, and the composition gives exactly `ℵ₁` classes; the persistent core is empty.
* **Logical agreement is needed**: adjoining `2 ^ ℵ₁` further classes lying in every domain
  keeps the domain laws, countable losses, and nonempty losses, but gives more than `ℵ₁` classes;
  so no family of observations separating the classes is constant on the domains.
* **Countable losses are needed**: adjoining `2 ^ ℵ₁` further classes all lost at the first
  successor keeps the domain laws, nonempty losses, and logical agreement, but gives more than
  `ℵ₁` classes.
* **Nonempty losses are needed**: a single class in every domain satisfies the domain laws,
  countable losses, and logical agreement, and there are fewer than `ℵ₁` classes.

The tail domains repeat the private tail filtration of `VaughtConjecture.Counting.Separation`,
as expansion domains; that example is private to its file.
-/

namespace VaughtConjecture.MainTheorem

open Cardinal Set
open scoped Ordinal

section Examples

/-- The countable ordinals. -/
private abbrev CountableOrdinal : Type 1 := Iio (ω₁ : Ordinal.{0})

/-- The `2 ^ ℵ₁` further classes: the sets of countable ordinals. -/
private abbrev Block : Type 1 := Set CountableOrdinal

/-- There are exactly `ℵ₁` countable ordinals. -/
private theorem mk_countableOrdinal : #CountableOrdinal = ℵ₁ := by
  simp [mk_Iio_ordinal]

/-- Adjoining the further classes gives more than `ℵ₁` classes. -/
private theorem aleph_one_lt_mk_sum : ℵ₁ < #(CountableOrdinal ⊕ Block) :=
  calc ℵ₁ < 2 ^ ℵ₁ := cantor _
    _ = #Block := by rw [mk_set, mk_countableOrdinal]
    _ ≤ _ := mk_le_of_injective Sum.inr_injective

/-- The observations "is the class `s`" separate distinct classes. -/
private theorem separates_eq {X : Type*} (p q : X) (h : p ≠ q) :
    ∃ s : X, ¬ ((p = s) ↔ (q = s)) :=
  ⟨p, by simp [Ne.symm h]⟩

/-- The class `s` is not in a domain that excludes it, so "is the class `s`" is constant there. -/
private theorem uniform_eq {X : Type*} {D : Set X} {s : X} (hs : s ∉ D) :
    ∀ p ∈ D, ∀ q ∈ D, ((p = s) ↔ (q = s)) := by
  intro p hp q hq
  have hp' : p ≠ s := by rintro rfl; exact hs hp
  have hq' : q ≠ s := by rintro rfl; exact hs hq
  simp only [hp', hq']

/-- The successor of a countable ordinal is countable. -/
private theorem add_one_lt_omega_one {ξ : Ordinal.{0}} (hξ : ξ < ω₁) : ξ + 1 < ω₁ :=
  (isSuccLimit_omega 1).succ_lt hξ

/-- One is a countable ordinal. -/
private theorem one_lt_omega_one : (1 : Ordinal.{0}) < ω₁ :=
  Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one

/-- A countable ordinal is not at least its successor. -/
private theorem not_add_one_le (ξ : Ordinal.{0}) : ¬ ξ + 1 ≤ ξ :=
  (Order.lt_add_one_iff.2 le_rfl).not_ge

/-! ### The tail domains -/

/-- The tail domains of the countable ordinals: stage `ξ` keeps the ordinals `≥ ξ`. -/
private def tail : ExpansionDomains CountableOrdinal where
  domain ξ := {x | ξ ≤ x.1}
  zero := eq_univ_of_forall fun x ↦ (zero_le : (0 : Ordinal) ≤ x.1)
  antitone _ _ h _ hx := h.trans hx
  limit l hl _ x hx := by
    by_contra h
    exact not_add_one_le x.1 (mem_iInter₂.1 hx _ (hl.succ_lt (not_le.1 h)))

/-- A class in the loss of the tail domains at `ξ` is the ordinal `ξ`. -/
private theorem eq_of_mem_tail_loss {ξ : Ordinal.{0}} {x : CountableOrdinal}
    (hx : x ∈ tail.domain ξ \ tail.domain (ξ + 1)) : x.1 = ξ :=
  (Order.lt_add_one_iff.1 (not_le.1 hx.2)).antisymm hx.1

/-- The tail domains have countable losses: each loss is at most one ordinal. -/
private theorem tail_hasCountableLosses : tail.HasCountableLosses :=
  ⟨fun _ _ ↦ Subsingleton.countable fun _ ha _ hb ↦
    Subtype.ext ((eq_of_mem_tail_loss ha).trans (eq_of_mem_tail_loss hb).symm)⟩

/-- The tail domains have nonempty losses: the loss at `ξ` contains `ξ`. -/
private theorem tail_hasNonemptyLosses : tail.HasNonemptyLosses :=
  ⟨fun ξ hξ ↦ ⟨⟨ξ, hξ⟩, le_refl ξ, not_add_one_le ξ⟩⟩

/-- The class `s` is not in the tail domain just above it. -/
private theorem notMem_tail_domain_add_one (s : CountableOrdinal) : s ∉ tail.domain (s.1 + 1) :=
  not_add_one_le s.1

/-- The tail domains have logical agreement for the observations "is the class `s`": each is false
on the domain just above `s`. -/
private theorem tail_hasLogicalAgreement :
    tail.HasLogicalAgreement fun (s x : CountableOrdinal) ↦ x = s :=
  ⟨fun s ↦ ⟨s.1 + 1, add_one_lt_omega_one s.2, uniform_eq (notMem_tail_domain_add_one s)⟩⟩

/-- **The composition applies to the tail domains**: exactly `ℵ₁` classes, from the four
hypotheses and separation. -/
example : #CountableOrdinal = ℵ₁ :=
  tail.mk_eq_aleph_one tail_hasCountableLosses tail_hasNonemptyLosses tail_hasLogicalAgreement
    separates_eq

/-- The persistent core of the tail domains is empty. -/
example : (⋂ ξ < ω₁, tail.domain ξ) = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦
    notMem_tail_domain_add_one x (mem_iInter₂.1 hx _ (add_one_lt_omega_one x.2))

/-! ### Logical agreement is needed -/

/-- The tail domains with the further classes adjoined to every domain. -/
private def adjoinPersistent : ExpansionDomains (CountableOrdinal ⊕ Block) where
  domain ξ := {z | Sum.elim (· ∈ tail.domain ξ) (fun _ ↦ True) z}
  zero := eq_univ_of_forall fun
    | .inl x => by simp [tail.zero]
    | .inr _ => trivial
  antitone _ _ h
    | .inl _, hx => tail.antitone h hx
    | .inr _, _ => trivial
  limit l hl hlt
    | .inl x, hx => tail.limit l hl hlt (mem_iInter₂.2 fun ξ hξ ↦ mem_iInter₂.1 hx ξ hξ)
    | .inr _, _ => trivial

/-- **Logical agreement cannot be dropped**: the domains with the further classes adjoined have
countable and nonempty losses and more than `ℵ₁` classes, so no family of observations
separating the classes is constant on the domains. -/
example : adjoinPersistent.HasCountableLosses ∧ adjoinPersistent.HasNonemptyLosses ∧
    ℵ₁ < #(CountableOrdinal ⊕ Block) ∧
    ∀ (truth : CountableOrdinal ⊕ Block → CountableOrdinal ⊕ Block → Prop),
      (∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q)) →
        ¬ adjoinPersistent.HasLogicalAgreement truth := by
  have hc : adjoinPersistent.HasCountableLosses := by
    refine ⟨fun ξ hξ ↦ ((tail_hasCountableLosses.countable_loss ξ hξ).image Sum.inl).mono ?_⟩
    rintro (x | y) ⟨h₁, h₂⟩
    · exact mem_image_of_mem _ ⟨h₁, h₂⟩
    · exact (h₂ trivial).elim
  have hn : adjoinPersistent.HasNonemptyLosses := ⟨fun ξ hξ ↦
    have ⟨x, hx⟩ := tail_hasNonemptyLosses.nonempty_loss ξ hξ
    ⟨.inl x, hx⟩⟩
  exact ⟨hc, hn, aleph_one_lt_mk_sum, fun truth hsep ha ↦
    aleph_one_lt_mk_sum.ne' (adjoinPersistent.mk_eq_aleph_one hc hn ha hsep)⟩

/-! ### Countable losses are needed -/

/-- The tail domains with the further classes adjoined to the first domain only. -/
private def adjoinLost : ExpansionDomains (CountableOrdinal ⊕ Block) where
  domain ξ := {z | Sum.elim (· ∈ tail.domain ξ) (fun _ ↦ ξ = 0) z}
  zero := eq_univ_of_forall fun
    | .inl x => by simp [tail.zero]
    | .inr _ => rfl
  antitone ξ _ h
    | .inl _, hx => tail.antitone h hx
    | .inr _, hx => le_antisymm (h.trans_eq hx) zero_le
  limit l hl hlt
    | .inl x, hx => tail.limit l hl hlt (mem_iInter₂.2 fun ξ hξ ↦ mem_iInter₂.1 hx ξ hξ)
    | .inr _, hx => by
      have h1 : (1 : Ordinal.{0}) < l := by
        simpa using hl.succ_lt (pos_iff_ne_zero.2 hl.ne_bot)
      exact absurd (mem_iInter₂.1 hx 1 h1) one_ne_zero

/-- **Countable losses cannot be dropped**: the domains with the further classes lost at the first
successor have nonempty losses and logical agreement for the observations "is the class `s`",
which separate the classes, and more than `ℵ₁` classes. -/
example : adjoinLost.HasNonemptyLosses ∧
    adjoinLost.HasLogicalAgreement (fun s z : CountableOrdinal ⊕ Block ↦ z = s) ∧
    ℵ₁ < #(CountableOrdinal ⊕ Block) ∧ ¬ adjoinLost.HasCountableLosses := by
  have hn : adjoinLost.HasNonemptyLosses := ⟨fun ξ hξ ↦
    have ⟨x, hx⟩ := tail_hasNonemptyLosses.nonempty_loss ξ hξ
    ⟨.inl x, hx⟩⟩
  have ha : adjoinLost.HasLogicalAgreement (fun s z : CountableOrdinal ⊕ Block ↦ z = s) := by
    refine ⟨fun
      | .inl s => ⟨s.1 + 1, add_one_lt_omega_one s.2, uniform_eq ?_⟩
      | .inr _ => ⟨1, one_lt_omega_one, uniform_eq one_ne_zero⟩⟩
    exact notMem_tail_domain_add_one s
  exact ⟨hn, ha, aleph_one_lt_mk_sum, fun hc ↦
    aleph_one_lt_mk_sum.ne' (adjoinLost.mk_eq_aleph_one hc hn ha separates_eq)⟩

/-! ### Nonempty losses are needed -/

/-- A single class in every domain. -/
private def constant : ExpansionDomains Unit where
  domain _ := univ
  zero := rfl
  antitone _ _ _ := le_rfl
  limit _ _ _ := subset_univ _

/-- **Nonempty losses cannot be dropped**: a single class in every domain has countable losses
and logical agreement for the observations `z = s`, which separate its one class, and fewer than
`ℵ₁` classes. -/
example : constant.HasCountableLosses ∧
    constant.HasLogicalAgreement (fun s z : Unit ↦ z = s) ∧ #Unit < ℵ₁ ∧
    ¬ constant.HasNonemptyLosses :=
  ⟨⟨fun _ _ ↦ countable_univ.mono sdiff_subset⟩,
    ⟨fun _ ↦ ⟨0, Ordinal.omega_pos 1, fun _ _ _ _ ↦ by simp⟩⟩,
    by simp [one_lt_aleph0.trans aleph0_lt_aleph_one],
    fun ⟨h⟩ ↦ by simpa [constant] using h 0 (Ordinal.omega_pos 1)⟩

/-! ### The density sentence -/

/-- The sharp comparison (agreement on the sentences of quantifier rank at most the stage) gives
logical agreement for the classes of the density sentence. -/
example (D : ExpansionDomains DensityClass)
    (h : ∀ η, η < ω₁ → ∀ p ∈ D.domain η, ∀ q ∈ D.domain η, ∀ θ : baseLanguage.Sentenceω,
      θ.qrank ≤ η → (densityTruth θ p ↔ densityTruth θ q)) :
    D.HasLogicalAgreement densityTruth :=
  .of_qrank_le h

end Examples

end VaughtConjecture.MainTheorem
