/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.UniquenessOfForcing

/-!
# Examples for next-block uniqueness from finite-cut receiving and forcing donors

Special cases of `VaughtConjecture.Expansion.UniquenessOfForcing`:

* **the block index `η = 0`**: two models at `λ_1 = ω + ω` with equal reductions to `λ_0 = ω`
  are equal, given (R1) and forcing donors at `0` alone;
* **uniqueness of model expansions**: next-block uniqueness from (R1) and forcing donors, composed
  with `ModelExpansion.subsingleton`, gives at most one model expansion to each countable block
  stage, and hence coherence of model expansions to countable block stages.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

namespace VaughtConjecture.Expansion

open Ordinal

/-- The block index `η = 0`: two models at `λ_1 = ω + ω` with equal reductions to `λ_0 = ω` are
equal, given (R1) and forcing donors at `0` only. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ForcingDonors.{0} 0) {M : Type}
    {R R' : Realization.{0, 0} (blockStage (0 + 1)) M} (hR : R.IsModel) (hR' : R'.IsModel)
    (h : R.reduce (isSuccPrelimit_blockStage 0) = R'.reduce (isSuccPrelimit_blockStage 0)) :
    R = R' :=
  hrec.finiteExtensionReceiving.eq_of_reduce_eq_of_forcingDonors hF (Ordinal.omega_pos 1) hR hR' h

section ModelExpansion

variable {M : Type} [baseLanguage.{0}.Structure M]

/-- Uniqueness of model expansions: `NextBlockUniqueness.of_forcingDonors` composed with
`ModelExpansion.subsingleton`. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ) {ξ : Ordinal.{0}}
    (hξ : ξ < ω₁) : Subsingleton (ModelExpansion M (blockStage ξ)) :=
  ModelExpansion.subsingleton (NextBlockUniqueness.of_forcingDonors hrec hF) hξ

/-- Coherence from (R1) and forcing donors: the reduction of a model expansion to `λ_ξ` to an
earlier countable block stage is the given model expansion there. -/
example (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    {ζ ξ : Ordinal.{0}} (hξ : ξ < ω₁) (h : ζ ≤ ξ) (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion M (blockStage ζ)) : e.reduceBlock h = e' :=
  ModelExpansion.reduceBlock_eq (NextBlockUniqueness.of_forcingDonors hrec hF) hξ h e e'

end ModelExpansion

end VaughtConjecture.Expansion
