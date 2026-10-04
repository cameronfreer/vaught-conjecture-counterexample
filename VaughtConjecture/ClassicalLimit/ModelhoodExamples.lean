/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Modelhood

/-!
# Examples: modelhood of the reconstructed realization

Roadmap, the section on the top-free witnesses, step 7; examples for
`VaughtConjecture.ClassicalLimit.Modelhood`.

* At `ω`, the reconstructed realization of a Fraïssé limit of the age of top-free charts is a
  model, given the nonemptiness of the uniformity and dominance instances over legal top-free
  stage types.
* The `ω`-stage witness: under the coatom extension property with apex at `ω`, a Fraïssé limit of
  the age of top-free charts exists, its reconstructed realization is a model, its carrier is
  infinite, and no model at a stage `β > ω` reduces to it; at `λ₁` the same property at `λ₁`
  gives modelhood, and no model at `ω · 3` reduces to the reconstructed realization.
* Infinitude from the plain coatom extension property alone, through receiving.
* The reconstructed realization with its labels kept, at a higher stage, fails the uniformity
  clause at `γ = α`: no label in `[α, α + ω)` is realized over any occurrence.
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

/-- **The `ω`-stage witness** under the coatom extension property with apex at `ω`: a model on an
infinite carrier, which is not the reduction of any model at a higher stage. -/
example (hext : HasApexCoatomExtensions.{0} ω) :
    ∃ M : CategoryTheory.Bundled.{0} (hullLanguage.{0} ω).Structure,
      (reconstruct ω M).IsModel ∧ Infinite M ∧ ∀ (β : Ordinal.{0}) (_ : ω < β)
        (S : Realization.{0, 0} β M), S.IsModel →
          S.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit ≠ reconstruct ω M := by
  obtain ⟨M, _, hM⟩ := exists_isFraisseLimit_topFreeAge_omega hext.hasCoatomExtensions
  have hmod := isModel_reconstruct_of_hasApexCoatomExtensions hext hM.age hM.ultrahomogeneous
    Ordinal.isSuccLimit_omega0
  exact ⟨M, hmod, hmod.infinite Ordinal.omega0_pos,
    fun _ hωβ _ hS ↦ reduce_ne_reconstruct hM.age.subset _ hωβ hS⟩

/-- Infinitude from the plain coatom extension property, without modelhood. -/
example (hext : HasCoatomExtensions.{0} ω) {M : Type} [(hullLanguage.{0} ω).Structure M]
    (hage : (hullLanguage.{0} ω).age M = topFreeAge ω)
    (hu : (hullLanguage.{0} ω).IsUltrahomogeneous M) : Infinite M :=
  infinite_of_age_eq_of_hasCoatomExtensions hext hage hu
    Ordinal.isSuccLimit_omega0.isSuccPrelimit Ordinal.omega0_pos

/-- At `λ₁ = ω · 2`, from the coatom extension property with apex at `λ₁`. -/
example (hext : HasApexCoatomExtensions.{0} (ω * 2)) {M : Type}
    [(hullLanguage.{0} (ω * 2)).Structure M]
    (hage : (hullLanguage.{0} (ω * 2)).age M = topFreeAge (ω * 2))
    (hu : (hullLanguage.{0} (ω * 2)).IsUltrahomogeneous M) : (reconstruct (ω * 2) M).IsModel :=
  isModel_reconstruct_of_hasApexCoatomExtensions hext hage hu isSuccLimit_omega0_mul_two

/-- Terminality at `λ₁ = ω · 2` against `ω · 3`. -/
example {M : Type} [(hullLanguage.{0} (ω * 2)).Structure M]
    (hage : (hullLanguage.{0} (ω * 2)).age M ⊆ topFreeAge (ω * 2))
    {S : Realization.{0, 0} (ω * 3) M} (hS : S.IsModel) :
    S.reduce isSuccLimit_omega0_mul_two.isSuccPrelimit ≠ reconstruct (ω * 2) M :=
  reduce_ne_reconstruct hage _ ((mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mpr
    (by exact_mod_cast (show (2 : ℕ) < 3 by omega))) hS

/-- **The witness with its labels kept at a higher stage fails the uniformity clause at
`γ = α`**: a realization at `β` whose reduction to `α` is the reconstructed realization realizes no
label in `[α, α + ω)` over any occurrence.  This is a clause of a model at `β` only when `α < β`;
for `β ≤ α` the statement holds but that clause is not asked, and it is vacuous when the
realization has no occurrence. -/
example {α β : Ordinal.{0}} {M : Type} [(hullLanguage.{0} α).Structure M]
    (hage : (hullLanguage.{0} α).age M ⊆ topFreeAge α) (hα : Order.IsSuccPrelimit α)
    {S : Realization.{0, 0} β M} (hS : S.reduce hα = reconstruct α M) (x : S.Occurrence) :
    ¬ S.RealizesOver x.tuple (uniformityFamily α) := by
  rintro ⟨u, -, q, ⟨d, hd, -⟩, hq⟩
  have ht : (reconstruct α M).eval u = some (q.reduce hα) := by
    rw [← hS, Realization.reduce_eval, hq, Option.map_some]
  exact isTopFree_of_reconstruct_eval hage ht d (Label.reduce_of_le hd)

end VaughtConjecture
