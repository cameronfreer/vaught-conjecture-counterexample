/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Domains
import VaughtConjecture.MainTheorem.Assembly

/-!
# Examples for the expansion domains

Special cases of `VaughtConjecture.Expansion.Domains`:

* the domain at `0`: membership is modelhood of the realization of a code, unconditionally; the
  domain is every class given the cap-to-model theorem; and there is at most one model expansion
  at the base stage, unconditionally;
* transport of model expansions along the identity, along an isomorphism and back, and between
  carriers in different universes; codes of one class have the same membership;
* a successor step: the domain at `ξ + 1` is contained in the domain at `ξ`, and the loss
  `D ξ \ D (ξ + 1)` consists of the classes with an expansion to `λ_ξ` and none to `λ_ξ + ω`;
* the domain at `ω₁` is empty, and no structure on `ℕ` has a model expansion to the stage `ω₁`;
* the existential representative of the definition is exactly the representative hypothesis of
  `ExpansionDomains.hasLogicalAgreement_of_modelExpansions`.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

namespace VaughtConjecture.Expansion

open Ordinal FirstOrder Language Structure baseLanguage MainTheorem

/-! ### The domain at `0` -/

/-- Membership in the domain at `0` is modelhood of the realization of a code, unconditionally. -/
example (c : ModelsOf densitySentence.{0}) :
    Quotient.mk _ c ∈ expansionDomain 0 ↔ (@toRealization ℕ c.1.toStructure).IsModel :=
  mem_expansionDomain_zero_iff c

/-- The domain at `0` is every class, given the cap-to-model theorem on `ℕ`. -/
example (hcap : CapToModel.{0}) : expansionDomain 0 = Set.univ :=
  expansionDomain_zero fun R ↦ hcap.isModel R

/-- At most one model expansion at the base stage, unconditionally. -/
example {M : Type} [baseLanguage.{0}.Structure M] : Subsingleton (ModelExpansion M ω) :=
  inferInstance

/-- At most one model expansion at the block stage `λ_0`. -/
example {M : Type} [baseLanguage.{0}.Structure M] :
    Subsingleton (ModelExpansion M (blockStage 0)) := by
  rw [blockStage_zero]
  infer_instance

/-! ### Transport -/

section Transport

variable {M N : Type} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
  {α : Ordinal.{0}}

/-- Transport along the identity isomorphism is the identity. -/
example (f : ModelExpansion M α) : f.map (Language.Equiv.refl baseLanguage.{0} M) = f :=
  ModelExpansion.map_refl f

/-- Transport along an isomorphism and then along its inverse is the identity. -/
example (f : ModelExpansion M α) (e : M ≃[baseLanguage.{0}] N) : (f.map e).map e.symm = f :=
  ModelExpansion.map_symm_map f e

/-- Transport between carriers in different universes. -/
example {P : Type 1} [baseLanguage.{0}.Structure P] (f : ModelExpansion M α)
    (e : M ≃[baseLanguage.{0}] P) : ModelExpansion P α :=
  f.map e

/-- Two codes of one class have the same membership. -/
example {η : Ordinal.{0}} (c c' : ModelsOf densitySentence.{0})
    (h : (isoSetoid densitySentence.{0}).r c c') :
    Nonempty (@ModelExpansion ℕ c.1.toStructure (blockStage η)) ↔
      Nonempty (@ModelExpansion ℕ c'.1.toStructure (blockStage η)) := by
  rw [← mem_expansionDomain_iff, ← mem_expansionDomain_iff, Quotient.sound h]

end Transport

/-! ### A successor step -/

/-- The domain at `ξ + 1` is contained in the domain at `ξ`. -/
example (ξ : Ordinal.{0}) : expansionDomain (ξ + 1) ⊆ expansionDomain ξ :=
  expansionDomain_antitone (Order.lt_add_one_iff.mpr le_rfl).le

/-- The same inclusion by reduction from `λ_{ξ+1} = λ_ξ + ω` to `λ_ξ`, with the same
representative. -/
example (ξ : Ordinal.{0}) : expansionDomain (ξ + 1) ⊆ expansionDomain ξ :=
  fun _ ⟨c, hc, ⟨e⟩⟩ ↦ ⟨c, hc, ⟨@ModelExpansion.reduce ℕ c.1.toStructure _ _ e
    (blockStage_add_one ξ ▸ isSuccPrelimit_blockStage (ξ + 1)) (isSuccLimit_blockStage ξ)
    (omega0_le_blockStage ξ) (blockStage_add_one ξ ▸ le_self_add)⟩⟩

/-- The loss at `ξ`: a code whose structure has a model expansion to `λ_ξ` and none to
`λ_ξ + ω`. -/
example (ξ : Ordinal.{0}) (c : ModelsOf densitySentence.{0}) :
    Quotient.mk _ c ∈ expansionDomain ξ \ expansionDomain (ξ + 1) ↔
      Nonempty (@ModelExpansion ℕ c.1.toStructure (blockStage ξ)) ∧
        IsEmpty (@ModelExpansion ℕ c.1.toStructure (blockStage ξ + ω)) := by
  rw [Set.mem_sdiff, mem_expansionDomain_iff, mem_expansionDomain_iff, blockStage_add_one,
    not_nonempty_iff]

/-! ### Emptiness at `ω₁` -/

/-- The domain at `ω₁` is empty. -/
example : expansionDomain ω₁ = ∅ :=
  expansionDomain_eq_empty le_rfl

/-- No structure on `ℕ` has a model expansion to the stage `ω₁`. -/
example (s : baseLanguage.{0}.Structure ℕ) : IsEmpty (@ModelExpansion ℕ s ω₁) :=
  @ModelExpansion.isEmpty_of_omega_one_le ℕ s _ _ le_rfl

/-- A model on `ℕ` has a countable stage. -/
example {α : Ordinal.{0}} {R : Realization.{0, 0} α ℕ} (hR : R.IsModel) : α < ω₁ :=
  hR.lt_omega_one

/-! ### The representative hypothesis of logical agreement -/

/-- The existential representative of the definition is the representative hypothesis of
`ExpansionDomains.hasLogicalAgreement_of_modelExpansions`, by definition. -/
example : ∀ η, η < ω₁ → ∀ q ∈ expansionDomain η, ∃ c : ModelsOf densitySentence.{0},
    Quotient.mk _ c = q ∧ Nonempty (@ModelExpansion ℕ c.1.toStructure (blockStage η)) :=
  fun _ _ _ hq ↦ hq

/-- Expansion domains whose domain is `expansionDomain` have logical agreement, conditional on
finite-extension receiving of models: the representative hypothesis is `fun _ _ _ hq ↦ hq`. -/
example (hrec : FiniteExtensionReceiving.{0}) (D : ExpansionDomains DensityClass)
    (hdom : D.domain = expansionDomain) : D.HasLogicalAgreement densityTruth := by
  obtain ⟨domain, _, _, _, _⟩ := D
  subst hdom
  exact ExpansionDomains.hasLogicalAgreement_of_modelExpansions hrec fun _ _ _ hq ↦ hq

end VaughtConjecture.Expansion
