/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.OnePointExtension
import VaughtConjecture.Stage.CountOmegaOne

/-!
# At most `ℵ₁` requests, and an unbounded schedule

There are at most `ℵ₁` requests (`AlephOne.requestCardinalityTarget`): at most `ℵ₁` tuples of the
carrier of each length (`AlephOne.mk_embedding_le_aleph_one`) and at most `ℵ₁` stage types at
stage `ω₁` of each arity (`StageType.mk_le_aleph_one_of_omega_one`), over countably many arities.

**An unbounded schedule** (`AlephOne.existsUnboundedScheduleTarget`).  The requests are nonempty
and at most `ℵ₁` many, so the carrier is in bijection with the pairs of a request and a point of
the carrier; the schedule is the request coordinate.  The fibre over a request contains a copy of
the carrier, which is uncountable, while the points below a given point are countably many
(`AlephOne.countable_of_isLowerSet_ne_univ`); so every fibre has points above every point.  No
order-compatible pairing is used.

## Placement

This file is Stage 3 (one model of cardinality `ℵ₁`) of the `ℵ₁` companion construction over the
density sentence, recorded in `roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction").
-/

namespace VaughtConjecture.AlephOne

open Cardinal Ordinal Set

/-- The carrier is uncountable. -/
theorem not_countable_carrier : ¬ Countable Carrier := fun h ↦ by
  have h₁ := mk_le_aleph0_iff.mpr h
  rw [mk_carrier] at h₁
  exact absurd h₁ (not_le.mpr aleph0_lt_aleph_one)

/-- At most `ℵ₁` tuples of the carrier of each length. -/
theorem mk_embedding_le_aleph_one (n : ℕ) : Cardinal.mk (Fin n ↪ Carrier) ≤ Cardinal.aleph 1 :=
  calc Cardinal.mk (Fin n ↪ Carrier) ≤ Cardinal.mk (Fin n → Carrier) :=
        mk_le_of_injective DFunLike.coe_injective
    _ = Cardinal.aleph 1 ^ (n : Cardinal) := by rw [← power_def, mk_carrier, mk_fin]
    _ ≤ Cardinal.aleph 1 := power_nat_le (aleph0_le_aleph 1)

/-- **At most `ℵ₁` requests**, the target form. -/
theorem requestCardinalityTarget : RequestCardinalityTarget := by
  let F : Request → Σ n : ℕ, (Fin n ↪ Carrier) × StageType.{0} (ω₁ : Ordinal.{0}) (n + 1) :=
    fun r ↦ ⟨r.arity, r.tuple, r.donor⟩
  have hF : Function.Injective F := by
    rintro ⟨a, t, d⟩ ⟨a', t', d'⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq h)
    rfl
  calc Cardinal.mk Request
      ≤ Cardinal.mk (Σ n : ℕ, (Fin n ↪ Carrier) × StageType.{0} (ω₁ : Ordinal.{0}) (n + 1)) :=
        mk_le_of_injective hF
    _ = sum fun n : ℕ ↦
          Cardinal.mk ((Fin n ↪ Carrier) × StageType.{0} (ω₁ : Ordinal.{0}) (n + 1)) :=
        mk_sigma _
    _ ≤ sum fun _ : ℕ ↦ Cardinal.aleph 1 := sum_le_sum _ _ fun n ↦ by
        rw [mk_prod]
        refine mul_le_of_le (aleph0_le_aleph 1) ?_ ?_
        · simpa using mk_embedding_le_aleph_one n
        · simpa using StageType.mk_le_aleph_one_of_omega_one (n + 1)
    _ ≤ Cardinal.aleph 1 := by
        rw [sum_const]
        simp

instance : Nonempty Request :=
  ⟨⟨0, Function.Embedding.ofIsEmpty, Condition.pointType⟩⟩

/-- **An unbounded schedule exists**, the target form: the request coordinate of a bijection of
the carrier with the pairs of a request and a point. -/
theorem existsUnboundedScheduleTarget : ExistsUnboundedScheduleTarget := by
  have hmk : Cardinal.mk (Request × Carrier) = Cardinal.aleph 1 := by
    rw [mk_prod, mk_carrier]
    simp only [Cardinal.lift_uzero, lift_aleph, Ordinal.lift_one]
    refine le_antisymm (mul_le_of_le (aleph0_le_aleph 1) ?_ le_rfl)
      (Cardinal.le_mul_left (mk_ne_zero Request))
    exact requestCardinalityTarget
  obtain ⟨e⟩ : Nonempty (Carrier ≃ Request × Carrier) :=
    lift_mk_eq'.mp (by rw [hmk, mk_carrier]; simp)
  refine ⟨fun x ↦ (e x).1, fun r x₀ ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  have hlt : ∀ z, e.symm (r, z) < x₀ := fun z ↦ lt_of_not_ge fun h ↦ hcon _ h (by simp)
  have : Countable (Set.Iio x₀) :=
    (countable_of_isLowerSet_ne_univ (isLowerSet_Iio x₀)
      (ne_univ_iff_exists_notMem _ |>.mpr ⟨x₀, lt_irrefl x₀⟩)).to_subtype
  exact not_countable_carrier <| Function.Injective.countable
    (f := fun z ↦ (⟨e.symm (r, z), hlt z⟩ : Set.Iio x₀)) fun z z' h ↦ by
      simpa using congrArg Subtype.val h

end VaughtConjecture.AlephOne
