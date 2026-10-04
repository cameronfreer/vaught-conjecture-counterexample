/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LowerBound

/-!
# Examples for the lower bound

Special cases of `VaughtConjecture.MainTheorem.LowerBound`:

* the class of a witness at `η` lies in every expansion domain up to `η` with no uniqueness
  hypothesis, and, given uniqueness at `λ_η`, in none above `η`;
* the `ω`-stage witness: the loss at `0` is nonempty under the coatom extension property with
  apex at `ω` alone, with no uniqueness hypothesis, both at the level of a given witness and from
  the Fraïssé limit; in particular the density sentence has a model on `ℕ`;
* at `λ₁ = ω · 2`: the loss at `1` is nonempty under the coatom extension property with apex at
  `λ₁` and uniqueness of model expansions at `λ₁`;
* the composition with the thin `ℵ₁` spectrum of the density sentence, through the conditional
  theorem for the expansion domains, with the nonempty losses supplied.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion Realization StageType Ordinal

/-! ### The class of a witness -/

section Witness

variable {η : Ordinal.{0}} {M : Type} [(hullLanguage.{0} (blockStage η)).Structure M]
  [Countable M] (hage : (hullLanguage.{0} (blockStage η)).age M = topFreeAge (blockStage η))
  (hu : (hullLanguage.{0} (blockStage η)).IsUltrahomogeneous M)
  (hmod : (reconstruct (blockStage η) M).IsModel)
include hage hu hmod

/-- Without any uniqueness hypothesis, the class of the witness lies in every expansion domain
up to its block. -/
example : ∃ q, ∀ ξ ≤ η, q ∈ expansionDomain ξ :=
  let ⟨c, ⟨e⟩⟩ := exists_code_of_witness hage hu hmod
  ⟨_, fun _ hξ ↦ expansionDomain_antitone hξ (mem_expansionDomain_of_witness hmod c e)⟩

/-- Given uniqueness at `λ_η`, the class of the witness lies in no expansion domain above its
block. -/
example (huniq : ∀ e : @ModelExpansion M
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage η), e.1 = reconstruct (blockStage η) M) :
    ∃ q ∈ expansionDomain η, ∀ ξ > η, q ∉ expansionDomain ξ :=
  let ⟨c, ⟨e⟩⟩ := exists_code_of_witness hage hu hmod
  ⟨_, mem_expansionDomain_of_witness hmod c e, fun _ hξ hq ↦
    notMem_expansionDomain_succ_of_witness hage.subset huniq c e
      (expansionDomain_antitone (Order.add_one_le_of_lt hξ) hq)⟩

/-- Given next-block uniqueness of models, the class of the witness at a countable block lies in
the loss there. -/
example (hnext : NextBlockUniqueness.{0}) (hη : η < ω₁) :
    (expansionDomain η \ expansionDomain (η + 1)).Nonempty :=
  nonempty_loss_of_witness hage hu hmod (eq_reconstruct_of_nextBlockUniqueness hnext hη hmod)

end Witness

/-! ### The `ω`-stage witness -/

/-- A witness at `λ_0 = ω` places its class in the loss at `0` with no uniqueness hypothesis. -/
example {M : Type} [(hullLanguage.{0} (blockStage 0)).Structure M] [Countable M]
    (hage : (hullLanguage.{0} (blockStage 0)).age M = topFreeAge (blockStage 0))
    (hu : (hullLanguage.{0} (blockStage 0)).IsUltrahomogeneous M)
    (hmod : (reconstruct (blockStage 0) M).IsModel) :
    (expansionDomain 0 \ expansionDomain (0 + 1)).Nonempty :=
  nonempty_loss_of_witness hage hu hmod (eq_reconstruct_of_blockStage_zero hmod)

/-- The loss at `0` from the coatom extension property with apex at `ω` alone. -/
example (hext : HasApexCoatomExtensions.{0} ω) :
    (expansionDomain 0 \ expansionDomain 1).Nonempty :=
  nonempty_loss_zero_of_hasApexCoatomExtensions hext

/-- The coatom extension property with apex at `ω` alone gives a model of the density sentence
on `ℕ`: the loss at `0` contains a class. -/
example (hext : HasApexCoatomExtensions.{0} ω) : HasModelOnNat :=
  hasModelOnNat_iff.mpr ⟨(nonempty_loss_zero_of_hasApexCoatomExtensions hext).some⟩

/-! ### The block stage `λ₁ = ω · 2` -/

/-- `λ₁ = ω · 2`. -/
example : blockStage (1 : Ordinal.{0}) = ω * 2 := by
  rw [blockStage_eq_mul, one_add_one_eq_two]

/-- The loss at `1` under the coatom extension property with apex at `λ₁` and uniqueness of model
expansions at `λ₁`. -/
example (hext : HasApexCoatomExtensions.{0} (blockStage 1))
    (hsub : ∀ (N : Type) [baseLanguage.{0}.Structure N],
      Subsingleton (ModelExpansion N (blockStage 1))) :
    (expansionDomain 1 \ expansionDomain (1 + 1)).Nonempty :=
  nonempty_loss_of_hasApexCoatomExtensions (one_lt_omega0.trans omega0_lt_omega_one) hext hsub

/-! ### The composition -/

/-- The composition through the conditional spectrum theorem for the expansion domains, with the
nonempty losses supplied by the lower bound and the cap-to-model theorem by the coatom extension
property with apex at `ω`. -/
example (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η))
    (hnext : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable)
    (hω : HasApexCoatomExtensions.{0} ω) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_modelExpansions
    (CapToModel.of_hasApexCoatomExtensions hω) hnext hrec hc
    (hasNonemptyLosses_of_hasApexCoatomExtensions (CapToModel.of_hasApexCoatomExtensions hω)
      hnext hext).nonempty_loss

/-- The same composition, stated with its remaining hypotheses only. -/
example (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η))
    (hnext : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_hasApexCoatomExtensions hext hnext hrec hc

end VaughtConjecture.MainTheorem
