/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Countable
import Mathlib.Order.SuccPred.Basic

/-!
# Domains with countable complements and disjoint successor losses

Roadmap, the reduction of the main theorem to expansion domains, and Layers 5–6; semantic
contract item 9.  Two general facts about domains `D ⊆ Q` in a type `Q` of isomorphism classes,
with no topology, measurability, or rank function.

* `countable_split_of_uniform_domain`: a predicate constant on a domain with countable complement
  has a countable truth side or a countable false side.  With the countable complements given by
  InfinitaryLogic's `InfinitaryLogic.compl_countable_of_loss` and the uniformity by logical
  agreement on a domain, this yields countable sentence splits for InfinitaryLogic's
  `Descriptive/CountableSplits` and `Descriptive/SentenceSplits` interfaces.  A countable truth
  side or false side for every sentence is the sentence minimality of
  `MainTheorem.isThinOnNatModels_of_countable_truth_sides` (cf. [Mon, Definition XII.4]).
* `exists_injective_mem_sdiff_succ`: the successor losses `D ξ \ D (succ ξ)` of an antitone family
  are pairwise disjoint, so a choice of one point from each nonempty loss is injective.  This is
  the lower-bound choice; it uses neither countability of losses nor logical comparison.  For
  ordinals `Order.succ ξ` is definitionally `ξ + 1`, the form used by `compl_countable_of_loss`.

Countable complements from countable successor losses is InfinitaryLogic's
`InfinitaryLogic.compl_countable_of_loss`, not restated here.  (InfinitaryLogic's
`mk_eq_aleph_one_of_domains` assumes that every point leaves some domain below `ω₁`, a global
eventual-departure hypothesis that the main theorem does not assume; it is not the route to the
cardinality bound here.)

## References

Minimally unbounded sentences are [Mon, Definition XII.4], for A. Montalbán, *Computable
Structure Theory: Beyond the Arithmetic* (draft, 22 April 2025).
-/

namespace VaughtConjecture.Counting

/-- **Countable split from a uniform domain.**  If `D` has countable complement and `P` takes the
same truth value at all points of `D`, then `P` is true at only countably many points or false at
only countably many points. -/
theorem countable_split_of_uniform_domain {Q : Type*} {D : Set Q} (P : Q → Prop)
    (hsmall : Dᶜ.Countable) (huniform : ∀ q ∈ D, ∀ s ∈ D, P q ↔ P s) :
    {q | P q}.Countable ∨ {q | ¬ P q}.Countable := by
  by_cases hex : ∃ q ∈ D, P q
  · obtain ⟨q, hq, hp⟩ := hex
    exact .inr (hsmall.mono fun s hs hsD ↦ hs ((huniform q hq s hsD).1 hp))
  · exact .inl (hsmall.mono fun q hq hqD ↦ hex ⟨q, hqD, hq⟩)

/-- **Injective choice from nonempty successor losses.**  For an antitone family `D` indexed by a
linear successor order and a set `S` of indices whose successor losses `D ξ \ D (succ ξ)` are
nonempty, some injective map sends each `ξ ∈ S` into its own loss. -/
theorem exists_injective_mem_sdiff_succ {α Q : Type*} [LinearOrder α] [SuccOrder α]
    {D : α → Set Q} (hD : Antitone D) {S : Set α}
    (hne : ∀ ξ ∈ S, (D ξ \ D (Order.succ ξ)).Nonempty) :
    ∃ f : S → Q, Function.Injective f ∧ ∀ ξ : S, f ξ ∈ D ξ \ D (Order.succ ξ) := by
  choose f hf using fun ξ : S ↦ hne ξ ξ.2
  refine ⟨f, fun ξ η hξη ↦ ?_, hf⟩
  have key : ∀ ξ η : S, ξ.1 < η.1 → f ξ ≠ f η := fun ξ η hlt heq ↦
    (hf ξ).2 (heq ▸ hD (Order.succ_le_of_lt hlt) (hf η).1)
  rcases lt_trichotomy ξ.1 η.1 with h | h | h
  · exact (key ξ η h hξη).elim
  · exact Subtype.ext h
  · exact (key η ξ h hξη.symm).elim

end VaughtConjecture.Counting
