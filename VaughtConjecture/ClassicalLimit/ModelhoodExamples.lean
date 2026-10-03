/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Modelhood

/-!
# Examples: modelhood of the reconstructed realization

Roadmap, the section on the top-free witnesses, step 7; regression examples for
`VaughtConjecture.ClassicalLimit.Modelhood`.

* At the block stages `ω` and `λ₁ = ω · 2`, the reconstructed realization of a structure whose age
  is the age of top-free charts and which is ultrahomogeneous is a model, given the nonemptiness
  of the uniformity and dominance instances over legal top-free stage types.
* That stage `0` is excluded is the example `not_isModel_of_hasFiniteCutReceiving_stage_zero` of
  `VaughtConjecture.Realization.ModelExamples`.
-/

namespace VaughtConjecture

open FirstOrder Language StageType
open scoped Ordinal

/-- `λ₁ = ω · 2` is a nonzero limit. -/
private theorem isSuccLimit_omega0_mul_two : Order.IsSuccLimit (ω * 2 : Ordinal.{0}) :=
  Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 two_pos

/-- At `ω`: the cap-to-model theorem for the reconstructed realization of a Fraïssé limit. -/
example {M : Type} [(hullLanguage.{0} ω).Structure M] [Countable M]
    (hM : IsFraisseLimit (topFreeAge.{0} ω) M)
    (hunif : ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{0}, Order.IsSuccPrelimit γ → γ < ω →
        (p.cofaces ∩ uniformityFamily γ).Nonempty)
    (hdom : ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{0}, γ < ω → (p.cofaces ∩ dominanceFamily γ).Nonempty) :
    (reconstruct ω M).IsModel :=
  isModel_reconstruct_of_isFraisseLimit hM Ordinal.isSuccLimit_omega0 hunif hdom

/-- At `λ₁ = ω · 2`, where the uniformity clause at `γ = ω` is among those asked. -/
example {M : Type} [(hullLanguage.{0} (ω * 2)).Structure M]
    (hage : (hullLanguage.{0} (ω * 2)).age M = topFreeAge (ω * 2))
    (hu : (hullLanguage.{0} (ω * 2)).IsUltrahomogeneous M)
    (hunif : ∀ ⦃n : ℕ⦄ (p : StageType.{0} (ω * 2) n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{0}, Order.IsSuccPrelimit γ → γ < ω * 2 →
        (p.cofaces ∩ uniformityFamily γ).Nonempty)
    (hdom : ∀ ⦃n : ℕ⦄ (p : StageType.{0} (ω * 2) n), p.IsLegal → p.IsTopFree →
      ∀ γ : Ordinal.{0}, γ < ω * 2 → (p.cofaces ∩ dominanceFamily γ).Nonempty) :
    (reconstruct (ω * 2) M).IsModel :=
  isModel_reconstruct hage hu isSuccLimit_omega0_mul_two hunif hdom

end VaughtConjecture
