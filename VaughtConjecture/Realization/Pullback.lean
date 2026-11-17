/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.OptionAttachment
import VaughtConjecture.Realization.Pushforward

/-!
# Pullbacks of realizations, and top-free types along embeddings

For an embedding `π : M ↪ X` of carriers, the **pullback** `R.comap π` of a realization `R` on `X`
gives a tuple of `M` the type of its image (`Realization.comap`).  Exact consistency, legal types
and top-free types pass to it (`Realization.IsConsistent.comap`, `Realization.HasLegalTypes.comap`,
`Realization.HasTopFreeTypes.comap`), and it is covering when `R` covers the tuples inside the
range of `π` and types no tuple leaving it (`Realization.comap_isCovering`).

Top-free types also pass to the pushforward `Realization.pushforward`
(`Realization.HasTopFreeTypes.pushforward`), beside the consistency, legality and covering
lemmas of `VaughtConjecture.Realization.Pushforward`.

All statements are proved.

## Placement

This file belongs to Layer 2 of `roadmap/README.md` (realizations), beside
`VaughtConjecture.Realization.Pushforward`; it is used by the conditions built by completed blocks
(`VaughtConjecture.AlephOne.PhaseConditions`).
-/

universe u v w

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {M : Type v} {X : Type w} {n : ℕ}

section Comap

variable (R : Realization.{u, w} α X) (π : M ↪ X)

/-- The **pullback** of a realization along an embedding of carriers: a tuple has the type of its
image. -/
def comap : Realization.{u, v} α M where
  eval t := R.eval (t.trans π)

theorem comap_eval (t : Fin n ↪ M) : (R.comap π).eval t = R.eval (t.trans π) :=
  rfl

variable {R}

/-- The pullback of an exactly consistent realization is exactly consistent. -/
theorem IsConsistent.comap (hR : R.IsConsistent) : (R.comap π).IsConsistent :=
  fun _ _ t p f h ↦ by
    rw [comap_eval, Function.Embedding.trans_assoc]
    exact hR _ _ f h

/-- The pullback of a realization with legal types has legal types. -/
theorem HasLegalTypes.comap (hL : R.HasLegalTypes) : (R.comap π).HasLegalTypes :=
  fun _ t p h ↦ hL (t.trans π) p h

/-- The pullback of a realization with top-free types has top-free types. -/
theorem HasTopFreeTypes.comap (hT : R.HasTopFreeTypes) : (R.comap π).HasTopFreeTypes :=
  fun _ t p h ↦ hT (t.trans π) p h

/-- The pullback is covering when `R` covers every tuple inside the range of `π` and types no tuple
leaving it. -/
theorem comap_isCovering
    (hnone : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), ¬ Set.range t ⊆ Set.range π → R.eval t = none)
    (hcov : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ X), Set.range t ⊆ Set.range π →
      ∃ (m : ℕ) (u : Fin m ↪ X) (f : Fin n ↪ Fin m), f.trans u = t ∧ (R.eval u).isSome) :
    (R.comap π).IsCovering := fun n t ↦ by
  obtain ⟨m, u, f, hfu, hu⟩ := hcov (t.trans π) (by rintro _ ⟨i, rfl⟩; exact ⟨t i, rfl⟩)
  have hrange : Set.range u ⊆ Set.range π := by
    by_contra h
    rw [hnone u h] at hu
    exact Bool.false_ne_true hu
  obtain ⟨u', hu'⟩ := exists_pullback_trans_eq (ι := π) fun i ↦ hrange ⟨i, rfl⟩
  refine ⟨m, u', f, Function.Embedding.ext fun i ↦ π.injective ?_, ?_⟩
  · have := DFunLike.congr_fun hfu i
    simp only [Function.Embedding.trans_apply] at this ⊢
    rw [← this, ← hu']
    rfl
  · rw [comap_eval, hu']
    exact hu

end Comap

/-- **Top-free types pass to the pushforward.** -/
theorem HasTopFreeTypes.pushforward {R : Realization.{u, v} α M} {π : M ↪ X}
    (hT : R.HasTopFreeTypes) : (R.pushforward π).HasTopFreeTypes := fun _ _ p h ↦ by
  obtain ⟨u, -, hu⟩ := exists_of_pushforward_eval_eq_some h
  exact hT u p hu

end VaughtConjecture.Realization
