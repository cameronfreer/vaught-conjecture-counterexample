/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Visibility replacement of ordinals

Every ordinal `o` is uniquely `ω * (o / ω) + o % ω` with `o % ω < ω` (`Ordinal.div_add_mod`); the
summand `o % ω` is its *finite part*, and the ordinals sharing `o / ω` form the *band*
`[ω * (o / ω), ω * (o / ω) + ω)` of `o` (the upper end is `Ordinal.lt_mul_div_add`).

`Ordinal.visibilityReplace k i o` is the thresholded replacement of the finite part: at
threshold `k` with value `i`, the finite part of `o` is replaced by `i` when it is below `k`, and
`o` is left unchanged otherwise.

* Visibility replacement stays in the band of its argument
  (`Ordinal.omega0_mul_div_le_visibilityReplace`, `Ordinal.visibilityReplace_lt`), so at a stage
  that is zero or a limit it keeps an ordinal below the stage exactly when it was below
  (`Ordinal.visibilityReplace_lt_iff`, from `Ordinal.lt_iff_of_mem_band`).
* For `i ≤ k` it is monotone (`Ordinal.monotone_visibilityReplace`); for `k ≤ i + 1` it is
  inflationary (`Ordinal.le_visibilityReplace`).
* Replacing again at the full threshold forgets the first value
  (`Ordinal.visibilityReplace_self_visibilityReplace`).

The extension to labels, fixing the bottom label and the formal top, is
`VaughtConjecture.Label.visibilityReplace`.

## References

Visibility replacement is Definition 2.2.3 of R. W. Knight, *A counterexample to Vaught's
Conjecture using generalised Stone spaces* (draft, 20 February 2026) [Kni26].
-/

universe u

namespace Ordinal

variable {α o : Ordinal.{u}} {k i : ℕ}

/-! ### Bands -/

/-- The quotient of `b * a + r` by `b`, for `r < b`. -/
private theorem mul_add_div_of_lt {b r : Ordinal.{u}} (a : Ordinal.{u}) (hr : r < b) :
    (b * a + r) / b = a := by
  rw [Ordinal.mul_add_div _ hr.ne_bot, Ordinal.div_eq_zero_of_lt hr, add_zero]

/-- The remainder of `b * a + r` modulo `b`, for `r < b`. -/
private theorem mul_add_mod_of_lt {b r : Ordinal.{u}} (a : Ordinal.{u}) (hr : r < b) :
    (b * a + r) % b = r := by
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-- At a stage that is zero or a limit (a multiple of `ω`), a band lies entirely below the stage
or entirely at or above it. -/
theorem lt_iff_of_mem_band {a y : Ordinal.{u}} (hα : Order.IsSuccPrelimit α) (hy₀ : ω * a ≤ y)
    (hy : y < ω * a + ω) : y < α ↔ ω * a < α := by
  obtain ⟨b, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hα
  refine ⟨hy₀.trans_lt, fun h ↦ hy.trans_le ?_⟩
  rw [← Ordinal.mul_succ]
  exact mul_le_mul_right (Order.succ_le_of_lt ((mul_lt_mul_iff_right₀ omega0_pos).mp h)) _

/-! ### Visibility replacement -/

open Classical in
/-- Visibility replacement of an ordinal at threshold `k` with value `i` [Kni26, Definition
2.2.3]: the finite part `o % ω` is replaced by `i` if it is below `k`, and kept otherwise. -/
noncomputable def visibilityReplace (k i : ℕ) (o : Ordinal.{u}) : Ordinal.{u} :=
  ω * (o / ω) + if o % ω < k then (i : Ordinal.{u}) else o % ω

/-- Below the threshold, the finite part is replaced. -/
theorem visibilityReplace_of_lt (h : o % ω < k) (i : ℕ) :
    visibilityReplace k i o = ω * (o / ω) + i := by
  simp [visibilityReplace, h]

/-- At or above the threshold, the ordinal is unchanged. -/
theorem visibilityReplace_of_le (h : (k : Ordinal.{u}) ≤ o % ω) (i : ℕ) :
    visibilityReplace k i o = o := by
  simp [visibilityReplace, h.not_gt, Ordinal.div_add_mod]

/-- The replaced value of the finite part is finite. -/
private theorem ite_lt_omega0 (k i : ℕ) (o : Ordinal.{u}) :
    (if o % ω < k then (i : Ordinal.{u}) else o % ω) < ω := by
  split_ifs
  · exact natCast_lt_omega0 i
  · exact Ordinal.mod_lt _ omega0_ne_zero

/-- Visibility replacement does not leave the band: lower end. -/
theorem omega0_mul_div_le_visibilityReplace (k i : ℕ) (o : Ordinal.{u}) :
    ω * (o / ω) ≤ visibilityReplace k i o :=
  le_self_add

/-- Visibility replacement does not leave the band: upper end. -/
theorem visibilityReplace_lt (k i : ℕ) (o : Ordinal.{u}) :
    visibilityReplace k i o < ω * (o / ω) + ω :=
  add_lt_add_right (ite_lt_omega0 k i o) _

/-- Visibility replacement keeps the quotient by `ω`. -/
theorem visibilityReplace_div (k i : ℕ) (o : Ordinal.{u}) :
    visibilityReplace k i o / ω = o / ω :=
  mul_add_div_of_lt _ (ite_lt_omega0 k i o)

/-- The finite part after visibility replacement. -/
theorem visibilityReplace_mod (k i : ℕ) (o : Ordinal.{u}) :
    visibilityReplace k i o % ω = if o % ω < k then (i : Ordinal.{u}) else o % ω :=
  mul_add_mod_of_lt _ (ite_lt_omega0 k i o)

/-- At a stage that is zero or a limit, visibility replacement keeps an ordinal below the stage
exactly when it was below. -/
theorem visibilityReplace_lt_iff (hα : Order.IsSuccPrelimit α) (k i : ℕ) :
    visibilityReplace k i o < α ↔ o < α := by
  rw [lt_iff_of_mem_band hα (omega0_mul_div_le_visibilityReplace k i o)
      (visibilityReplace_lt k i o),
    lt_iff_of_mem_band hα (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o omega0_ne_zero)]

/-- On the finite ordinals visibility replacement replaces the ordinal itself. -/
theorem visibilityReplace_of_lt_omega0 (ho : o < ω) (k i : ℕ) :
    visibilityReplace k i o = if o < k then (i : Ordinal.{u}) else o := by
  simp [visibilityReplace, Ordinal.div_eq_zero_of_lt ho, Ordinal.mod_eq_of_lt ho]

/-- Visibility replacement is monotone when the new value does not exceed the threshold. -/
theorem monotone_visibilityReplace (hi : i ≤ k) :
    Monotone (visibilityReplace k i : Ordinal.{u} → Ordinal.{u}) := by
  intro o o' h
  rcases (Ordinal.div_le_left h ω).lt_or_eq with hlt | heq
  · refine (visibilityReplace_lt k i o).le.trans ?_
    rw [← Ordinal.mul_succ]
    exact (mul_le_mul_right (Order.succ_le_of_lt hlt) _).trans
      (omega0_mul_div_le_visibilityReplace k i o')
  · have hmod : o % ω ≤ o' % ω := by
      have := Ordinal.div_add_mod o ω ▸ Ordinal.div_add_mod o' ω ▸ h
      rwa [heq, add_le_add_iff_left] at this
    have hik : (i : Ordinal.{u}) ≤ k := by exact_mod_cast hi
    unfold visibilityReplace
    rw [heq]
    refine add_le_add_right ?_ _
    split_ifs with h₁ h₂ h₂
    · exact le_rfl
    · exact hik.trans (not_lt.mp h₂)
    · exact absurd (hmod.trans_lt h₂) h₁
    · exact hmod

/-- Replacing again at the full threshold forgets an earlier value `i ≤ k`. -/
theorem visibilityReplace_self_visibilityReplace (hi : i ≤ k) (o : Ordinal.{u}) :
    visibilityReplace k k (visibilityReplace k i o) = visibilityReplace k k o := by
  have hik : (i : Ordinal.{u}) ≤ k := by exact_mod_cast hi
  conv_lhs => rw [visibilityReplace, visibilityReplace_div, visibilityReplace_mod]
  rw [visibilityReplace]
  by_cases hm : o % ω < k
  · by_cases hk : (i : Ordinal.{u}) < k
    · simp [hm, hk]
    · simp [hm, le_antisymm hik (not_lt.mp hk)]
  · simp [hm]

/-- An ordinal lies below its visibility replacement when the new value is at least one below
the threshold. -/
theorem le_visibilityReplace (h : k ≤ i + 1) (o : Ordinal.{u}) : o ≤ visibilityReplace k i o := by
  by_cases hk : o % ω < k
  · rw [visibilityReplace_of_lt hk]
    conv_lhs => rw [← Ordinal.div_add_mod o ω]
    refine (add_le_add_iff_left _).mpr ?_
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt o omega0_ne_zero)
    rw [hn] at hk ⊢
    exact_mod_cast Nat.lt_succ_iff.mp ((Nat.cast_lt.mp hk).trans_le h)
  · exact (visibilityReplace_of_le (not_lt.mp hk) i).ge

end Ordinal
