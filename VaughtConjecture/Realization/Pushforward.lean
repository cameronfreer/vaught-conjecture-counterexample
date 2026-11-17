/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.OptionAttachment

/-!
# Realizations along embeddings of carriers

For an embedding `π : M ↪ X` of carriers:

* the **pullback** `R.comap π` of a realization `R` on `X`: a tuple of `M` has the type of its
  image (`Realization.comap`);
* the **pushforward** `R.pushforward π` of a realization `R` on `M`: a tuple of `X` inside the range
  of `π` has the type of its preimage, and every other tuple is untyped
  (`Realization.pushforward`, with `Realization.pushforward_eval_trans`).

Exact consistency, legal types and top-free types pass to both
(`Realization.IsConsistent.comap`, `Realization.IsConsistent.pushforward` and the following
theorems); the pushforward covers every tuple inside the range of `π` when `R` is covering
(`Realization.pushforward_isCovering_of_range_subset`), and the pullback is covering when `R`
covers the tuples inside the range and types no tuple leaving it
(`Realization.comap_isCovering`).  For a bijection these are `Realization.map` up to the inverse.

All statements are proved.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.Transport`; it is used by the conditions built by completed blocks
(`VaughtConjecture.AlephOne.PhaseConditions`).
-/

universe u v w

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {M : Type v} {X : Type w} {n : ℕ}

/-! ### Pullback -/

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
  choose v hv using fun i ↦ hrange ⟨i, rfl⟩
  let u' : Fin m ↪ M := ⟨v, fun i j hij ↦ u.injective (by rw [← hv i, ← hv j, hij])⟩
  have hu' : u'.trans π = u := Function.Embedding.ext fun i ↦ hv i
  refine ⟨m, u', f, Function.Embedding.ext fun i ↦ π.injective ?_, ?_⟩
  · have := DFunLike.congr_fun hfu i
    simp only [Function.Embedding.trans_apply] at this ⊢
    rw [← this, ← hv]
    rfl
  · rw [comap_eval, hu']
    exact hu

end Comap

/-! ### Pushforward -/

section Pushforward

variable (π : M ↪ X)

/-- The preimage of a tuple inside the range of an embedding. -/
noncomputable def pullTuple (t : Fin n ↪ X) (h : ∀ i, t i ∈ Set.range π) : Fin n ↪ M :=
  ⟨fun i ↦ (h i).choose, fun i j hij ↦
    t.injective (by rw [← (h i).choose_spec, ← (h j).choose_spec]; exact congrArg π hij)⟩

theorem pullTuple_trans (t : Fin n ↪ X) (h : ∀ i, t i ∈ Set.range π) :
    (pullTuple π t h).trans π = t :=
  Function.Embedding.ext fun i ↦ (h i).choose_spec

theorem pullTuple_trans_self (u : Fin n ↪ M) (h : ∀ i, (u.trans π) i ∈ Set.range π) :
    pullTuple π (u.trans π) h = u :=
  Function.Embedding.ext fun i ↦ π.injective (h i).choose_spec

variable (R : Realization.{u, v} α M)

open Classical in
/-- The **pushforward** of a realization along an embedding of carriers: a tuple inside the range
has the type of its preimage, and every other tuple is untyped. -/
noncomputable def pushforward : Realization.{u, w} α X where
  eval t := if h : ∀ i, t i ∈ Set.range π then R.eval (pullTuple π t h) else none

/-- The pushforward gives the image of a tuple the type of the tuple. -/
theorem pushforward_eval_trans (u : Fin n ↪ M) :
    (R.pushforward π).eval (u.trans π) = R.eval u := by
  have h : ∀ i, (u.trans π) i ∈ Set.range π := fun i ↦ ⟨u i, rfl⟩
  simp only [pushforward, h, implies_true, dite_true, pullTuple_trans_self]

/-- The pushforward types no tuple leaving the range. -/
theorem pushforward_eval_of_not {t : Fin n ↪ X} (h : ¬ Set.range t ⊆ Set.range π) :
    (R.pushforward π).eval t = none := by
  have h' : ¬ ∀ i, t i ∈ Set.range π := fun h' ↦ h (Set.range_subset_iff.mpr h')
  simp only [pushforward, h', dite_false]

/-- A typed tuple of the pushforward is the image of a tuple with the same type. -/
theorem exists_trans_eq_of_pushforward_eval {t : Fin n ↪ X} {p : StageType.{u} α n}
    (h : (R.pushforward π).eval t = some p) :
    ∃ u : Fin n ↪ M, u.trans π = t ∧ R.eval u = some p := by
  by_cases ht : Set.range t ⊆ Set.range π
  · have ht' : ∀ i, t i ∈ Set.range π := fun i ↦ ht ⟨i, rfl⟩
    refine ⟨pullTuple π t ht', pullTuple_trans π t ht', ?_⟩
    rw [← pushforward_eval_trans π R, pullTuple_trans]
    exact h
  · rw [pushforward_eval_of_not π R ht] at h
    exact absurd h (by simp)

variable {R}

/-- The pushforward of an exactly consistent realization is exactly consistent. -/
theorem IsConsistent.pushforward (hR : R.IsConsistent) : (R.pushforward π).IsConsistent :=
  fun _ _ t p f h ↦ by
    obtain ⟨u, rfl, hu⟩ := exists_trans_eq_of_pushforward_eval π R h
    rw [← Function.Embedding.trans_assoc, pushforward_eval_trans]
    exact hR _ _ f hu

/-- The pushforward of a realization with legal types has legal types. -/
theorem HasLegalTypes.pushforward (hL : R.HasLegalTypes) : (R.pushforward π).HasLegalTypes :=
  fun _ _ p h ↦ by
    obtain ⟨u, -, hu⟩ := exists_trans_eq_of_pushforward_eval π R h
    exact hL u p hu

/-- The pushforward of a realization with top-free types has top-free types. -/
theorem HasTopFreeTypes.pushforward (hT : R.HasTopFreeTypes) :
    (R.pushforward π).HasTopFreeTypes :=
  fun _ _ p h ↦ by
    obtain ⟨u, -, hu⟩ := exists_trans_eq_of_pushforward_eval π R h
    exact hT u p hu

/-- The pushforward of a covering realization covers every tuple inside the range. -/
theorem pushforward_isCovering_of_range_subset (hc : R.IsCovering) {t : Fin n ↪ X}
    (ht : Set.range t ⊆ Set.range π) :
    ∃ (m : ℕ) (v : Fin m ↪ X) (f : Fin n ↪ Fin m), f.trans v = t ∧
      ((R.pushforward π).eval v).isSome := by
  have ht' : ∀ i, t i ∈ Set.range π := fun i ↦ ht ⟨i, rfl⟩
  obtain ⟨m, v, f, hfv, hv⟩ := hc (pullTuple π t ht')
  refine ⟨m, v.trans π, f, ?_, by rw [pushforward_eval_trans]; exact hv⟩
  rw [← Function.Embedding.trans_assoc, hfv, pullTuple_trans]

end Pushforward

end VaughtConjecture.Realization
