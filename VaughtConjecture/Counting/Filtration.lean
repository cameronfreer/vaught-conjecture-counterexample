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

end VaughtConjecture.Counting
