/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Amalgamation
import VaughtConjecture.Continuation.ExactAge

/-!
# Examples: exact receiving within an age and the exact-age comparison

* **Transport.**  A realization and its transport along a bijection of carriers have the same
  actual types and exact receiving together (`Realization.exactReceivingWithin_map_iff`), so the
  comparison applies to `R` and `R.map e`.
* **The matching relation.**  The empty tuples are matched by the cores, the empty tuples of two
  model expansions by their covers of the stage type on no points
  (`ModelExpansion.exists_covers_zero`, `StageType.eq_of_zero`), and a repeated coordinate is
  matched by a non-injective selector.
* **Age inclusion is needed.**  Exact receiving within the empty family holds for every
  realization, while no realization with an occurrence has its actual types in the empty family:
  exact receiving within a family missing the actual types carries no information.
* **Cutoff receiving is not exact.**  Capping a stage type with a top cell at an ordinal `c` below
  the stage (`StageType.cap`) gives a member of its receiving family at every cutoff `δ ≤ c` that
  differs from it: a received type agrees with the donor below the cutoff, not exactly.  Exact
  receiving of donors with top cells needs a further argument (rigidity of a core).
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Realization

variable {α : Ordinal.{u}} {k₀ : ℕ}

/-! ### Transport -/

/-- The exact-age comparison of a realization with its transport along a bijection of carriers:
the transport has the same actual types and exact receiving. -/
example {M N : Type w} [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]
    [Countable M] [Countable N] {R : Realization.{u, w} α M} (e : M ≃ N)
    {A : ∀ m, Set (StageType.{u} α m)} (he : R.IsExpansionOf) (he' : (R.map e).IsExpansionOf)
    (hage : ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D → D ∈ A m)
    (hr : R.ExactReceivingWithin A) {t : StageType.{u} α k₀} {x₀ : Fin k₀ → M}
    (h₀ : R.Covers t x₀) : Nonempty (M ≃[baseLanguage.{u}] N) :=
  nonempty_equiv_of_exactReceivingWithin he he' hage (fun _ s D hD ↦ hage _ D hD) hr
    ((exactReceivingWithin_map_iff e).mpr hr) h₀ (y₀ := ⇑e ∘ x₀)
    ((covers_map_iff e).mpr (by rwa [← Function.comp_assoc, e.symm_comp_self, Function.id_comp]))

/-! ### The matching relation -/

section Match

variable {M : Type v} {N : Type w} {R : Realization.{u, v} α M} {R' : Realization.{u, w} α N}

/-- The empty tuples are matched by two covers of one stage type. -/
example {p : StageType.{u} α k₀} {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N} (h₀ : R.Covers p x₀)
    (h₀' : R'.Covers p y₀) : CoverMatch R R' x₀ y₀ 0 ![] ![] :=
  CoverMatch.zero h₀ h₀'

/-- The empty tuples of two model expansions are matched through their covers of the stage type
on no points. -/
example [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N] (e : ModelExpansion M α)
    (f : ModelExpansion N α) : CoverMatch e.1 f.1 ![] ![] 0 ![] ![] := by
  obtain ⟨t, ht⟩ := e.exists_covers_zero
  obtain ⟨t', ht'⟩ := f.exists_covers_zero
  rw [StageType.eq_of_zero t' t] at ht'
  exact CoverMatch.zero ht ht'

/-- **A repeated coordinate** is matched by a non-injective selector. -/
example {x₀ : Fin k₀ → M} {y₀ : Fin k₀ → N} {a : M} {b : N}
    (h : CoverMatch R R' x₀ y₀ 1 ![a] ![b]) : CoverMatch R R' x₀ y₀ 2 ![a, a] ![b, b] := by
  obtain ⟨k, t, x, y, ι, s, hx, hy, hxι, hyι, ha, hb⟩ := h
  have ha0 : a = x (s 0) := congrFun ha 0
  have hb0 : b = y (s 0) := congrFun hb 0
  exact ⟨k, t, x, y, ι, ![s 0, s 0], hx, hy, hxι, hyι,
    funext (Fin.forall_fin_two.mpr ⟨ha0, ha0⟩), funext (Fin.forall_fin_two.mpr ⟨hb0, hb0⟩)⟩

end Match

/-! ### Age inclusion is needed -/

section Age

variable {M : Type v} (R : Realization.{u, v} α M)

/-- Exact receiving within the empty family holds for every realization. -/
example : R.ExactReceivingWithin fun _ ↦ ∅ :=
  fun _ _ _ _ _ _ _ hD _ ↦ absurd hD (Set.notMem_empty _)

/-- …while the actual types of a realization with an occurrence do not lie in the empty family:
age inclusion fails, and the comparison does not apply. -/
example (hR : Nonempty R.Occurrence) :
    ¬ ∀ ⦃m : ℕ⦄ (s : Fin m ↪ M) (D : StageType.{u} α m), R.eval s = some D →
      D ∈ (∅ : Set (StageType.{u} α m)) := fun h ↦
  let ⟨x⟩ := hR
  h x.tuple x.type x.eval_tuple

end Age

/-! ### Cutoff receiving is not exact -/

section Cap

variable {n : ℕ} {d : StageType.{u} α n} {c : Ordinal.{u}}
  {hc : Label.IsSelfVisible n (c : Label.{u})} {hcα : c < α}

/-- A capped stage type lies in the receiving family of the stage type at every cutoff `δ` at
most the cap. -/
example {δ : Label.{u}} (hδ : δ ≤ c) : d.cap c hc hcα ∈ StageType.receivingFamily d δ := by
  refine ⟨rfl, fun i j hij ↦ ?_⟩
  obtain rfl : i = j := Fin.ext hij
  exact (min_assoc _ _ _).trans (congrArg (min (d.label i)) (min_eq_right hδ))

/-- …and it differs from the stage type when the stage type has a top cell: received at a cutoff,
a donor with a top cell need not be received exactly. -/
example (h : ¬ d.IsTopFree) : d.cap c hc hcα ≠ d := fun he ↦
  h (he ▸ StageType.isTopFree_cap)

end Cap

end VaughtConjecture
