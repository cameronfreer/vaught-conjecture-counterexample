/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import VaughtConjecture.Label.Basic

/-!
# Labels: the coded labels lie at stage `ω₁`

The printed labels of [Kni26] are `{-∞} ∪ ω₁ ∪ {∞}`: in the vocabulary of
`VaughtConjecture.Label.Basic`, the labels at stage `ω₁`.  The coded labels, bottom and the
ordinals below `ω ^ 2`, are among them, since `ω ^ 2 < ω₁` (`Label.omega0_sq_lt_omega_one`).
-/

universe u

namespace VaughtConjecture

namespace Label

open Ordinal

/-- `ω ^ 2 < ω₁`: the coded labels, bottom and the ordinals below `ω ^ 2`, lie at stage `ω₁`. -/
theorem omega0_sq_lt_omega_one : (ω ^ 2 : Ordinal.{u}) < Ordinal.omega.{u} 1 := by
  rw [Cardinal.lt_omega_iff_card_lt, pow_two]
  simp [Cardinal.aleph0_mul_aleph0]

end Label

end VaughtConjecture
