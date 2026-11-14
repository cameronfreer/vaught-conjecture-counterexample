/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Construction
import VaughtConjecture.Realization.Expansion

/-!
# A receiving model of cardinality `ℵ₁` at stage `ω₁`

**Given-model statements** (about every realization in the stated class; no existence asserted).

* `AlephOne.alephOneLeMkOfIsModelTarget`: a model at stage `ω₁` has at least `ℵ₁` points, since a
  model on a countable carrier has a countable stage (`Realization.IsModel.lt_omega_one`).
* `AlephOne.mkEqAlephOneTarget`: every receiving model at stage `ω₁` with top-free types has
  exactly `ℵ₁` points (the upper bound is `AlephOne.mk_le_aleph_one_of_isCovering`).
* The base interpretation of every receiving model at stage `ω₁` satisfies the density sentence
  (`AlephOne.realizeDensitySentenceTarget`, in `VaughtConjecture.AlephOne.Construction`).

**Existence** (`AlephOne.existsReceivingModelTarget`): some realization at stage `ω₁` on the
carrier `ω₁.ToType` (a type in `Type`) is a receiving model with top-free types.  It is the Zorn
construction of `VaughtConjecture.AlephOne.Conditions` with the unbounded schedule
(`AlephOne.existsUnboundedScheduleTarget`), the one-point extension
(`AlephOne.onePointExtensionTarget`) and the passage from exact top-free receiving to receiving
models (`AlephOne.isReceivingModelOfExactReceivingTarget`).  With the given-model statements:
some base-language structure on a carrier in `Type` satisfies the density sentence and has
cardinality exactly `ℵ₁` (`AlephOne.existsAlephOneModelTarget`).

Nothing here concerns Scott ranks.

## Placement

This file is Stage 3 (one model of cardinality `ℵ₁`) of the `ℵ₁` companion construction over the
density sentence; that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe v

namespace VaughtConjecture.AlephOne

open Ordinal Realization FirstOrder Language

/-! ### Given-model statements -/

/-- **At least `ℵ₁` points**, the target form: a model at stage `ω₁` on a countable carrier would
have a countable stage (`Realization.IsModel.lt_omega_one`). -/
theorem alephOneLeMkOfIsModelTarget : AlephOneLeMkOfIsModelTarget.{v} := by
  intro M R hR
  by_contra h
  rw [not_le, ← Cardinal.succ_aleph0, Order.lt_succ_iff] at h
  have : Countable M := Cardinal.mk_le_aleph0_iff.mp h
  exact lt_irrefl _ hR.lt_omega_one

/-- **Exactly `ℵ₁` points** for every receiving model at stage `ω₁` with top-free types, the target
form. -/
theorem mkEqAlephOneTarget : MkEqAlephOneTarget.{v} :=
  mkEqAlephOneTarget_of alephOneLeMkOfIsModelTarget

end VaughtConjecture.AlephOne
