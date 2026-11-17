/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Model

/-!
# Extension of a realization along an embedding of carriers

For an embedding `ι : Y ↪ X` and a realization `S` on `Y`, the **pushforward** `S.pushforward ι`
is the realization on `X` that gives the image `u.trans ι` of a tuple `u` of `Y` the evaluation of
`u` (`Realization.pushforward_eval_trans`) and leaves every tuple with a point outside the range
of `ι` untyped (`Realization.pushforward_eval_of_not_forall`).  Along a bijection it is the
transport `Realization.map` read through the inverse; along an inclusion of a subset it extends a
realization of the subset by `none`.

Exact consistency, legal types and the covering of the tuples inside the range pass to the
pushforward (`Realization.IsConsistent.pushforward`, `Realization.HasLegalTypes.pushforward`,
`Realization.IsCovering.pushforward`).

## Placement

This file belongs to Layer 2 of `roadmap/README.md` (realizations); it is used by the one-point
extension of the `ℵ₁` companion construction (`VaughtConjecture.AlephOne.OnePointExtension`).
-/

universe u v w

namespace VaughtConjecture.Realization

open Set

variable {α : Ordinal.{u}} {X : Type v} {Y : Type w} (ι : Y ↪ X) {n m : ℕ}

/-- The tuple of `Y` whose image under `ι` is a given tuple of `X` inside the range of `ι`. -/
noncomputable def pullbackTuple (t : Fin n ↪ X) (h : ∀ i, t i ∈ range ι) : Fin n ↪ Y :=
  ⟨fun i ↦ (h i).choose, fun i j hij ↦ t.injective <| by
    simp only at hij
    rw [← (h i).choose_spec, ← (h j).choose_spec, hij]⟩

@[simp] theorem pullbackTuple_trans (t : Fin n ↪ X) (h : ∀ i, t i ∈ range ι) :
    (pullbackTuple ι t h).trans ι = t :=
  Function.Embedding.ext fun i ↦ (h i).choose_spec

@[simp] theorem pullbackTuple_trans_self (s : Fin n ↪ Y) (h : ∀ i, (s.trans ι) i ∈ range ι) :
    pullbackTuple ι (s.trans ι) h = s :=
  Function.Embedding.ext fun i ↦ ι.injective (h i).choose_spec

open Classical in
/-- The **pushforward** of a realization on `Y` along `ι : Y ↪ X`: the image of a tuple of `Y`
has the evaluation of the tuple, and a tuple with a point outside the range of `ι` is untyped. -/
noncomputable def pushforward (S : Realization.{u, w} α Y) : Realization.{u, v} α X where
  eval t := if h : ∀ i, t i ∈ range ι then S.eval (pullbackTuple ι t h) else none

variable {ι}

@[simp] theorem pushforward_eval_trans (S : Realization.{u, w} α Y) (s : Fin n ↪ Y) :
    (S.pushforward ι).eval (s.trans ι) = S.eval s := by
  simp [pushforward]

theorem pushforward_eval_of_not_forall (S : Realization.{u, w} α Y) {t : Fin n ↪ X}
    (h : ¬ ∀ i, t i ∈ range ι) : (S.pushforward ι).eval t = none := by
  simp only [pushforward]
  exact dite_eq_right_of_eq_false (eq_false h)

/-- A tuple inside the range of `ι` is the image of a tuple of `Y`. -/
theorem exists_pullback_trans_eq {t : Fin n ↪ X} (h : ∀ i, t i ∈ range ι) :
    ∃ s : Fin n ↪ Y, s.trans ι = t :=
  ⟨_, pullbackTuple_trans ι t h⟩

/-- A typed tuple of the pushforward is the image of a tuple of `Y` with the same evaluation. -/
theorem exists_of_pushforward_eval_eq_some {S : Realization.{u, w} α Y} {t : Fin n ↪ X}
    {p : StageType.{u} α n} (ht : (S.pushforward ι).eval t = some p) :
    ∃ s : Fin n ↪ Y, s.trans ι = t ∧ S.eval s = some p := by
  by_cases h : ∀ i, t i ∈ range ι
  · obtain ⟨s, rfl⟩ := exists_pullback_trans_eq h
    exact ⟨s, rfl, by rwa [pushforward_eval_trans] at ht⟩
  · rw [pushforward_eval_of_not_forall S h] at ht
    exact absurd ht (Option.some_ne_none _).symm

/-- **Exact consistency passes to the pushforward.** -/
theorem IsConsistent.pushforward {S : Realization.{u, w} α Y} (hS : S.IsConsistent) :
    (S.pushforward ι).IsConsistent := by
  intro m n t p f ht
  obtain ⟨s, rfl, hs⟩ := exists_of_pushforward_eval_eq_some ht
  rw [← Function.Embedding.trans_assoc, pushforward_eval_trans]
  exact hS s p f hs

/-- **Legal types pass to the pushforward.** -/
theorem HasLegalTypes.pushforward {S : Realization.{u, w} α Y} (hS : S.HasLegalTypes) :
    (S.pushforward ι).HasLegalTypes := by
  intro n t p ht
  obtain ⟨s, -, hs⟩ := exists_of_pushforward_eval_eq_some ht
  exact hS s p hs

/-- **Covering of the tuples inside the range passes to the pushforward.** -/
theorem IsCovering.pushforward {S : Realization.{u, w} α Y} (hS : S.IsCovering)
    {t : Fin n ↪ X} (h : ∀ i, t i ∈ range ι) :
    ∃ (m : ℕ) (u : Fin m ↪ X) (f : Fin n ↪ Fin m), f.trans u = t ∧
      ((S.pushforward ι).eval u).isSome := by
  obtain ⟨s, rfl⟩ := exists_pullback_trans_eq h
  obtain ⟨m, w, f, hfw, hw⟩ := hS s
  refine ⟨m, w.trans ι, f, ?_, by rwa [pushforward_eval_trans]⟩
  rw [← Function.Embedding.trans_assoc, hfw]

end VaughtConjecture.Realization
