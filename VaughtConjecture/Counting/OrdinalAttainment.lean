/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# An attained greatest index

A predicate `P` on ordinals that holds at `β`, is closed downward, is closed at the nonzero
countable limits (it holds at a limit `l < ω₁` when it holds below `l`), and holds only below a
countable ordinal `δ`, has a greatest element `ρ`, with `β ≤ ρ < δ`
(`exists_isGreatest_of_closed`).  The greatest element is the supremum `ρ` of the ordinals at
which `P` holds; if `P` failed at `ρ`, it would hold at every ordinal below `ρ` by downward
closure, so `ρ` would be neither zero (`P β` with `β ≤ ρ`), nor a successor (the supremum of
ordinals below `a + 1` is at most `a`), nor a limit (closure at limits).

The statement uses Mathlib only.  It is not stated in InfinitaryLogic at the pin `e460cb6`.  It
follows from the greatest-stage statements of InfinitaryLogic (`OrdinalUtil`), available
upstream, not at the pin, but it is not the same statement as any of them:
* the general forms `exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed` and
  `exists_forall_iff_le_of_bounded_of_isSuccLimit_closed` assume closure at every nonzero limit,
  not only below `ω₁`; here closure at a limit above `δ` holds vacuously, since `P` fails at `δ`;
* the countable form `exists_greatest_stage_lt_omega1`, on `Ordinal.{0}`, assumes `P 0` (here
  from `P β` by downward closure) and a bound `ξ ≤ A` on the countable `ξ` at which `P` holds
  (here `A = δ`), and concludes that `P ξ` holds exactly when `ξ ≤ ρ`.

## Placement

This file belongs to Layer 0 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Order Ordinal

/-- **An attained greatest index**: a predicate on ordinals that holds at `β`, is closed
downward, is closed at the nonzero countable limits, and holds only below a countable ordinal `δ`
has a greatest element `ρ`, with `β ≤ ρ < δ`.  Mathlib only; it follows from the greatest-stage
statements of InfinitaryLogic, available upstream, not at the pin `e460cb6`, whose hypotheses and
conclusions differ (see the module docstring). -/
theorem exists_isGreatest_of_closed {P : Ordinal.{u} → Prop} {β δ : Ordinal.{u}} (hβ : P β)
    (hdown : ∀ ⦃a b⦄, a ≤ b → P b → P a)
    (hlim : ∀ l, IsSuccLimit l → l < ω₁ → (∀ a < l, P a) → P l)
    (hbound : ∀ a, P a → a < δ) (hδ : δ < ω₁) :
    ∃ ρ, IsGreatest {a | P a} ρ ∧ β ≤ ρ ∧ ρ < δ := by
  have hbdd : BddAbove {a | P a} := ⟨δ, fun a ha ↦ (hbound a ha).le⟩
  set ρ := sSup {a | P a}
  have hle : ∀ a, P a → a ≤ ρ := fun a ha ↦ le_csSup hbdd ha
  suffices hρ : P ρ from ⟨ρ, ⟨hρ, hle⟩, hle β hβ, hbound ρ hρ⟩
  by_contra hρ
  -- below the supremum, `P` holds everywhere
  have hbelow : ∀ a < ρ, P a := fun a ha ↦
    let ⟨b, hb, hab⟩ := exists_lt_of_lt_csSup ⟨β, hβ⟩ ha
    hdown hab.le hb
  rcases zero_or_succ_or_isSuccLimit ρ with h0 | ⟨a, ha⟩ | hl
  · exact hρ (hdown (h0.le.trans (zero_le (a := β))) hβ)
  · -- every element is below `a + 1`, so the supremum is at most `a`
    have hsup : ρ ≤ a := csSup_le ⟨β, hβ⟩ fun b hb ↦
      lt_succ_iff.mp (ha ▸ (hle b hb).lt_of_ne fun h ↦ hρ (h ▸ hb))
    exact (lt_succ a).not_ge (ha ▸ hsup)
  · exact hρ (hlim ρ hl ((csSup_le ⟨β, hβ⟩ fun b hb ↦ (hbound b hb).le).trans_lt hδ) hbelow)

end VaughtConjecture
