/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Counting.Domains
import VaughtConjecture.Counting.Filtration

/-!
# Counting classes: cofinal losses, a countable persistent core, and Scott separation

Roadmap, Layer 0, "Counting and observation", and the counting theorem of Layer 6 via Scott
separation.
For decreasing domains `D ξ` on a type `X` of classes, indexed by the countable
ordinals as in `VaughtConjecture.Counting.Filtration`:

* `aleph_one_le_mk_of_cofinal`: cofinally many nonempty successor losses below `ω₁` give
  `ℵ₁ ≤ #X`.  One point is chosen from each nonempty loss (`exists_injective_mem_sdiff_succ`);
  a cofinal set of countable ordinals is uncountable (Mathlib's `Ordinal.iSup_lt_omega_one`).
  Neither countability of losses nor continuity is used.
* `mk_eq_aleph_one_of_countable_core`: with countable complements below `ω₁` and a countable
  persistent core `⋂ ξ < ω₁, D ξ`, in fact `#X = ℵ₁`.  Outside the core every point leaves some
  domain below `ω₁`, so InfinitaryLogic's `InfinitaryLogic.mk_eq_aleph_one_of_domains` (a union
  of `ℵ₁` countable complements) applies to the complement of the core; the core adds only
  countably many points.  Eventual departure of every point is **not** assumed, and no
  perfect-set argument is used.
* `persistent_subsingleton_of_separation`: if observations separate distinct classes and each
  observation is constant on some domain below `ω₁`, then the persistent core has at most one
  point.  It need not be empty.

The `Filtration` versions combine these with InfinitaryLogic's `compl_countable_of_loss`:
`Filtration.mk_eq_aleph_one_of_separation` is the counting theorem, and
`Filtration.countable_truth_side` is the sentence split of `countable_split_of_uniform_domain`.

*Scott separation* is the hypothesis that the observations separate distinct classes; for the
classes of countable models of a sentence, observed by the sentences of `L_{ω₁,ω}`, it holds
because each class is defined by a Scott sentence ([Mon, Theorem II.9];
`MainTheorem.classTruth_separates`).  A countable truth side or false side for every sentence is
sentence minimality, the hypothesis of `MainTheorem.isThinOnNatModels_of_countable_truth_sides`
(cf. [Mon, Definition XII.4]).

For the filtration by a rank (`Filtration.ofRank`) the persistent core is empty, so the count
needs no Scott separation on the core: `mk_eq_aleph_one_of_rank` gives `#X = ℵ₁` for an
uncountable type with a rank into the countable ordinals with countable fibres, and
`mk_le_aleph_one_of_rank` and `mk_le_aleph_one_of_countable_cover` give `#X ≤ ℵ₁` with no
uncountability hypothesis.

Two private examples close the file: the tail filtration of the countable
ordinals satisfies every hypothesis, and adjoining a persistent summand of size `2 ^ ℵ₁` keeps every
filtration axiom but not the cardinality, so the countable-core hypothesis cannot be dropped.

## References

Scott sentences are [Mon, Theorem II.9] and minimally unbounded sentences
[Mon, Definition XII.4], for A. Montalbán, *Computable Structure Theory: Beyond the arithmetic*
(draft, 22 April 2025).
-/

namespace VaughtConjecture.Counting

open Cardinal Set
open scoped Ordinal

universe u v

/-- A set of countable ordinals that is cofinal in `ω₁` is uncountable: the supremum of a
countable set of countable ordinals is countable (Mathlib's `Ordinal.iSup_lt_omega_one`), and
its successor is still below `ω₁`. -/
private theorem not_countable_of_cofinal {T : Set Ordinal.{0}} (hT : ∀ ξ ∈ T, ξ < ω₁)
    (hcof : ∀ β, β < ω₁ → ∃ ξ ∈ T, β ≤ ξ) : ¬ T.Countable := fun hc ↦ by
  have := hc.to_subtype
  have hs := Ordinal.iSup_lt_omega_one fun x : T ↦ hT x x.2
  obtain ⟨ξ, hξ, hle⟩ := hcof _ ((isSuccLimit_omega 1).succ_lt hs)
  exact (Order.lt_succ _).not_ge (hle.trans (Ordinal.le_iSup (fun x : T ↦ x.1) ⟨ξ, hξ⟩))

/-- **Lower bound from cofinal losses.**  If nonempty successor losses of an antitone family of
domains occur cofinally below `ω₁`, then there are at least `ℵ₁` classes. -/
theorem aleph_one_le_mk_of_cofinal {X : Type u} {D : Ordinal.{0} → Set X} (hD : Antitone D)
    (hloss : ∀ β, β < ω₁ → ∃ ξ, β ≤ ξ ∧ ξ < ω₁ ∧ (D ξ \ D (ξ + 1)).Nonempty) :
    ℵ₁ ≤ #X := by
  obtain ⟨f, hf, -⟩ := exists_injective_mem_sdiff_succ hD
    (S := {ξ | ξ < ω₁ ∧ (D ξ \ D (ξ + 1)).Nonempty}) fun ξ hξ ↦ hξ.2
  rw [aleph_one_le_iff, ← not_le, mk_le_aleph0_iff]
  intro hX
  refine not_countable_of_cofinal (fun ξ hξ ↦ hξ.1) (fun β hβ ↦ ?_) hf.countable
  obtain ⟨ξ, hβξ, hξ, hne⟩ := hloss β hβ
  exact ⟨ξ, ⟨hξ, hne⟩, hβξ⟩

/-- **Exact cardinality with a countable persistent core.**  Antitone domains with countable
complements below `ω₁`, cofinally many nonempty successor losses below `ω₁`, and a countable
persistent core give exactly `ℵ₁` classes.  No point is required to leave. -/
theorem mk_eq_aleph_one_of_countable_core {X : Type u} {D : Ordinal.{0} → Set X}
    (hD : Antitone D) (hcompl : ∀ β, β < ω₁ → (D β)ᶜ.Countable)
    (hloss : ∀ β, β < ω₁ → ∃ ξ, β ≤ ξ ∧ ξ < ω₁ ∧ (D ξ \ D (ξ + 1)).Nonempty)
    (hcore : (⋂ ξ < ω₁, D ξ).Countable) : #X = ℵ₁ := by
  set C := ⋂ ξ < ω₁, D ξ with hC
  have hout : #(Cᶜ : Set X) = ℵ₁ := by
    refine InfinitaryLogic.mk_eq_aleph_one_of_domains (fun β ↦ Subtype.val ⁻¹' D β)
      (fun β γ h ↦ preimage_mono (hD h)) (fun β hβ ↦ (hcompl β hβ).preimage Subtype.val_injective)
      (fun β hβ ↦ ?_) fun x ↦ ?_
    · obtain ⟨ξ, hβξ, hξ, x, hx, hx'⟩ := hloss β hβ
      exact ⟨⟨x, fun hxC ↦ hx' (mem_iInter₂.1 hxC _ ((isSuccLimit_omega 1).succ_lt hξ))⟩,
        hD hβξ hx⟩
    · have hx : x.1 ∉ C := x.2
      simp only [hC, mem_iInter₂, not_forall] at hx
      obtain ⟨β, hβ, hxβ⟩ := hx
      exact ⟨β, hβ, hxβ⟩
  rw [← mk_sum_compl C, hout]
  exact add_eq_right (aleph0_le_aleph 1)
    ((mk_le_aleph0_iff.2 hcore.to_subtype).trans (aleph0_le_aleph 1))

/-- **Scott separation bounds the persistent core.**  If the observations `truth s` separate
distinct classes and each observation is constant on some domain below `ω₁`, then at most one
class lies in every domain below `ω₁`.  The core need not be empty. -/
theorem persistent_subsingleton_of_separation {X : Type u} {S : Type v}
    (D : Ordinal.{0} → Set X) (truth : S → X → Prop)
    (separates : ∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q))
    (homogeneous : ∀ s, ∃ ξ, ξ < ω₁ ∧ ∀ p ∈ D ξ, ∀ q ∈ D ξ, (truth s p ↔ truth s q)) :
    (⋂ ξ < ω₁, D ξ).Subsingleton := by
  intro p hp q hq
  by_contra hne
  obtain ⟨s, hs⟩ := separates p q hne
  obtain ⟨ξ, hξ, hh⟩ := homogeneous s
  exact hs (hh p (mem_iInter₂.1 hp ξ hξ) q (mem_iInter₂.1 hq ξ hξ))

namespace Filtration

variable {X : Type u} (F : Filtration X)

include F in
/-- A filtration has at least `ℵ₁` classes. -/
theorem aleph_one_le_mk : ℵ₁ ≤ #X :=
  aleph_one_le_mk_of_cofinal F.antitone F.cofinal_losses

/-- A filtration with countable persistent core has exactly `ℵ₁` classes. -/
theorem mk_eq_aleph_one (hcore : F.core.Countable) : #X = ℵ₁ :=
  mk_eq_aleph_one_of_countable_core F.antitone (fun _ ↦ F.compl_countable) F.cofinal_losses hcore

/-- Under Scott separation by observations constant on domains below `ω₁`, the persistent core
of a filtration has at most one class. -/
theorem core_subsingleton {S : Type v} (truth : S → X → Prop)
    (separates : ∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q))
    (homogeneous : ∀ s, ∃ ξ, ξ < ω₁ ∧ ∀ p ∈ F.domain ξ, ∀ q ∈ F.domain ξ,
      (truth s p ↔ truth s q)) :
    F.core.Subsingleton :=
  persistent_subsingleton_of_separation F.domain truth separates homogeneous

/-- **Counting theorem.**  A filtration whose classes are separated by observations, each
constant on some domain below `ω₁`, has exactly `ℵ₁` classes. -/
theorem mk_eq_aleph_one_of_separation {S : Type v} (truth : S → X → Prop)
    (separates : ∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q))
    (homogeneous : ∀ s, ∃ ξ, ξ < ω₁ ∧ ∀ p ∈ F.domain ξ, ∀ q ∈ F.domain ξ,
      (truth s p ↔ truth s q)) :
    #X = ℵ₁ :=
  F.mk_eq_aleph_one (F.core_subsingleton truth separates homogeneous).countable

/-- **Countable truth side.**  A predicate constant on some domain below `ω₁` holds at only
countably many classes or fails at only countably many classes. -/
theorem countable_truth_side (P : X → Prop) {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    (huniform : ∀ p ∈ F.domain ξ, ∀ q ∈ F.domain ξ, P p ↔ P q) :
    {q | P q}.Countable ∨ {q | ¬ P q}.Countable :=
  countable_split_of_uniform_domain P (F.compl_countable hξ) huniform

end Filtration

/-! ### Counting by a rank -/

section Rank

variable {X : Type u} {r : X → Ordinal.{0}}

/-- **Exactly `ℵ₁` classes from a rank on an uncountable type**: the filtration by a rank into the
countable ordinals with countable fibres has an empty persistent core (`Filtration.core_ofRank`),
so `Filtration.mk_eq_aleph_one` applies with no hypothesis of Scott separation on the core. -/
theorem mk_eq_aleph_one_of_rank (hr : ∀ x, r x < ω₁)
    (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable) (hX : ¬ Countable X) : #X = ℵ₁ :=
  (Filtration.ofRank r hr hfib hX).mk_eq_aleph_one (by simp)

/-- **At most `ℵ₁` classes from a rank** into the countable ordinals with countable fibres. -/
theorem mk_le_aleph_one_of_rank (hr : ∀ x, r x < ω₁)
    (hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable) : #X ≤ ℵ₁ := by
  by_cases hX : Countable X
  · exact (mk_le_aleph0_iff.2 hX).trans (aleph0_le_aleph 1)
  · exact (mk_eq_aleph_one_of_rank hr hfib hX).le

/-- **At most `ℵ₁` classes from a countable cover**: a type covered by countable sets `Q α` with
`α < ω₁` has at most `ℵ₁` elements (through the least level, `leastLevel`). -/
theorem mk_le_aleph_one_of_countable_cover {Q : Ordinal.{0} → Set X}
    (hQ : ∀ α, α < ω₁ → (Q α).Countable) (hcover : ∀ x, ∃ α, α < ω₁ ∧ x ∈ Q α) : #X ≤ ℵ₁ :=
  mk_le_aleph_one_of_rank (fun x ↦ (leastLevel_lt_and_mem hcover x).1)
    (countable_setOf_leastLevel_eq hQ hcover)

end Rank

/-! ### Examples -/

section Examples

/-- The tail filtration of the countable ordinals: stage `ξ` keeps the ordinals `≥ ξ`, so each
successor loss is the single ordinal `ξ`. -/
private def tail : Filtration (Iio (ω₁ : Ordinal.{0})) where
  domain ξ := {x | ξ ≤ x.1}
  zero := eq_univ_of_forall fun x ↦ (zero_le : (0 : Ordinal) ≤ x.1)
  antitone _ _ h _ hx := h.trans hx
  limit l hl _ x hx := by
    by_contra h
    exact (Order.lt_succ x.1).not_ge (mem_iInter₂.1 hx _ (hl.succ_lt (not_le.1 h)))
  loss_countable ξ _ := by
    have key : ∀ x ∈ {x : Iio ω₁ | ξ ≤ x.1} \ {x | ξ + 1 ≤ x.1}, x.1 = ξ := fun x hx ↦
      (Order.lt_add_one_iff.1 (not_le.1 hx.2)).antisymm hx.1
    exact Subsingleton.countable fun a ha b hb ↦ Subtype.ext ((key a ha).trans (key b hb).symm)
  cofinal_losses β hβ := ⟨β, le_rfl, hβ, ⟨⟨β, hβ⟩, le_refl β,
    (Order.lt_add_one_iff.2 (le_refl β)).not_ge⟩⟩
  domain_eq_empty_of_omega_one_le _ h :=
    eq_empty_of_forall_notMem fun x hx ↦ (h.trans hx).not_gt x.2

/-- Membership in a tail domain. -/
private theorem mem_tail_domain {ξ : Ordinal.{0}} {x : Iio (ω₁ : Ordinal.{0})} :
    x ∈ tail.domain ξ ↔ ξ ≤ x.1 :=
  Iff.rfl

/-- No countable ordinal lies in the tail domain just above it. -/
private theorem notMem_tail_domain_add_one (x : Iio (ω₁ : Ordinal.{0})) :
    x ∉ tail.domain (x.1 + 1) :=
  fun h ↦ (Order.lt_add_one_iff.2 (le_refl x.1)).not_ge (mem_tail_domain.1 h)

/-- The tail filtration is separated by the observations "is the ordinal `s`", each constant
(false) on the domain at stage `s + 1`. -/
private theorem mk_tail : #(Iio (ω₁ : Ordinal.{0})) = ℵ₁ :=
  tail.mk_eq_aleph_one_of_separation (fun s x ↦ x = s)
    (fun p q h ↦ ⟨p, by simp [Ne.symm h]⟩)
    fun s ↦ ⟨s.1 + 1, (isSuccLimit_omega 1).succ_lt s.2, fun p hp q hq ↦ by
      have hp' : p ≠ s := by rintro rfl; exact notMem_tail_domain_add_one p hp
      have hq' : q ≠ s := by rintro rfl; exact notMem_tail_domain_add_one q hq
      simp only [hp', hq']⟩

/-- Adjoining a persistent summand `Y` to a filtration: the classes of `Y` lie in every domain
below `ω₁`.  All filtration axioms survive, and the persistent core contains `Y`. -/
private def adjoin {X : Type u} (F : Filtration X) (Y : Type u) : Filtration (X ⊕ Y) where
  domain ξ := {z | Sum.elim (· ∈ F.domain ξ) (fun _ ↦ ξ < ω₁) z}
  zero := eq_univ_of_forall fun
    | .inl x => by simp [F.zero]
    | .inr _ => Ordinal.omega_pos 1
  antitone _ _ h
    | .inl _, hx => F.antitone h hx
    | .inr _, hx => h.trans_lt hx
  limit l hl hlt
    | .inl x, hx => F.limit l hl hlt (mem_iInter₂.2 fun ξ hξ ↦ mem_iInter₂.1 hx ξ hξ)
    | .inr _, _ => hlt
  loss_countable ξ hξ := by
    refine ((F.loss_countable ξ hξ).image Sum.inl).mono ?_
    rintro (x | y) ⟨h₁, h₂⟩
    · exact mem_image_of_mem _ ⟨h₁, h₂⟩
    · exact (h₂ ((isSuccLimit_omega 1).succ_lt h₁)).elim
  cofinal_losses β hβ := by
    obtain ⟨ξ, hβξ, hξ, x, hx⟩ := F.cofinal_losses β hβ
    exact ⟨ξ, hβξ, hξ, .inl x, hx⟩
  domain_eq_empty_of_omega_one_le ξ h := eq_empty_of_forall_notMem fun
    | .inl x, hx => by simp [F.domain_eq_empty_of_omega_one_le ξ h] at hx
    | .inr _, hx => h.not_gt hx

/-- The tail filtration satisfies every hypothesis, and its classes number exactly `ℵ₁`. -/
example : #(Iio (ω₁ : Ordinal.{0})) = ℵ₁ ∧ tail.core = ∅ := by
  refine ⟨mk_tail, eq_empty_of_forall_notMem fun x hx ↦ ?_⟩
  exact notMem_tail_domain_add_one x (tail.mem_core_iff.1 hx _ ((isSuccLimit_omega 1).succ_lt x.2))

/-- **The countable-core hypothesis is needed.**  Adjoining `2 ^ ℵ₁` persistent classes to the
tail filtration gives a filtration (every axiom holds) with an uncountable core and more than
`ℵ₁` classes. -/
example : ¬ (adjoin tail (Set (Iio (ω₁ : Ordinal.{0})))).core.Countable ∧
    ℵ₁ < #(Iio (ω₁ : Ordinal.{0}) ⊕ Set (Iio (ω₁ : Ordinal.{0}))) := by
  have hlt : ℵ₁ < #(Iio (ω₁ : Ordinal.{0}) ⊕ Set (Iio (ω₁ : Ordinal.{0}))) := by
    calc ℵ₁ < 2 ^ ℵ₁ := cantor _
      _ = #(Set (Iio (ω₁ : Ordinal.{0}))) := by rw [mk_set, mk_tail]
      _ ≤ _ := mk_le_of_injective Sum.inr_injective
  exact ⟨fun h ↦ hlt.ne' ((adjoin tail _).mk_eq_aleph_one h), hlt⟩

end Examples

end VaughtConjecture.Counting
