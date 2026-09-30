/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Countable

/-!
# Countability from a countable cover by at-most-one conditions

Roadmap, Layer 0, "Counting and observation"; semantic contract item 8.  A type `I` is countable
as soon as countably many conditions `P c` cover it and each condition holds of at most one
element.  The conditions may overlap: no disjointness, canonical descriptor, or classifying
invariant is required.  The intended client counts terminal isomorphism classes through the
countable index `(Σ n, S n) ⊕ ℕ ⊕ Unit`, where each condition is satisfied by at most one class.
-/

namespace VaughtConjecture.Counting

/-- **Countable subsingleton cover.**  If every element of `I` satisfies one of countably many
conditions `P c`, each satisfied by at most one element, then `I` is countable. -/
theorem countable_of_subsingleton_cover {I C : Type*} [Countable C] (P : C → I → Prop)
    (hsub : ∀ c, {i | P c i}.Subsingleton) (hcover : ∀ i, ∃ c, P c i) : Countable I := by
  rw [← Set.countable_univ_iff]
  refine (Set.countable_iUnion fun c ↦ (hsub c).countable).mono fun i _ ↦ ?_
  exact Set.mem_iUnion.2 (hcover i)

end VaughtConjecture.Counting
