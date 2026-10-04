/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Losses
import VaughtConjecture.MainTheorem.ModelExpansionDomains

/-!
# Examples: countable successor losses

* **The base block.**  At `ξ = 0`, with `λ_0 = ω`, a code of a class in the loss has exactly one
  model expansion to `λ_0`, and it is terminal; the loss at `0` is countable under the named
  hypotheses.
* **Covers by subsingletons.**  A finite set covered by its singletons, and a cover whose members
  all coincide: the cover need not be disjoint.
* **Cover-hollowness at a block stage.**  The hollow property gives it; no realization at the
  successor stage `ω + 1` has it; and (R3) for it is exactly (R3) at the block stages for
  cover-hollow models, so naming it does not strengthen (R3).
* **One class per property**, and the hypotheses of the spectrum theorem.
-/

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage Realization Expansion MainTheorem

/-! ### The base block -/

/-- A code of a class in the loss at `0` has exactly one model expansion to `λ_0 = ω`, and it is
terminal at `0`.  Unconditional. -/
example {c : ModelsOf densitySentence.{0}}
    (hq : Quotient.mk _ c ∈ expansionDomain 0 \ expansionDomain (0 + 1)) :
    ∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage 0),
      e.1.IsTerminalAt 0 ∧ ∀ e' : @ModelExpansion ℕ c.1.toStructure (blockStage 0), e' = e := by
  let := c.1.toStructure
  have : Subsingleton (ModelExpansion ℕ (blockStage (0 : Ordinal.{0}))) := by
    rw [blockStage_zero]
    exact ModelExpansion.instSubsingletonOmega
  obtain ⟨e⟩ := (mem_expansionDomain_iff c).mp hq.1
  exact ⟨e, e.isTerminalAt_of_mem_loss hq, fun _ ↦ Subsingleton.elim _ _⟩

/-- The loss at `0` is countable, under (R1), the continuation criterion, (R2) and (R3). -/
example (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : ResidualReceiving.{0, 0}) (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) :
    (expansionDomain 0 \ expansionDomain (0 + 1)).Countable :=
  expansionDomain_loss_countable hrec hcont hres hhol 0 (omega0_pos.trans omega0_lt_omega_one)

/-! ### Covers by subsingletons -/

/-- A finite set covered by its singletons. -/
example : (Set.univ : Set (Fin 3)).Countable :=
  countable_of_subsingleton_cover (fun i : Fin 3 ↦ {i}) (fun _ ↦ Set.subsingleton_singleton)
    fun x _ ↦ Set.mem_iUnion.mpr ⟨x, rfl⟩

/-- The members of the cover may coincide. -/
example : ({0} : Set ℕ).Countable :=
  countable_of_subsingleton_cover (fun _ : ℕ ↦ {0}) (fun _ ↦ Set.subsingleton_singleton)
    fun _ hx ↦ Set.mem_iUnion.mpr ⟨0, hx⟩

/-! ### Cover-hollowness at a block stage -/

/-- The hollow property gives cover-hollowness at a block stage and unbounded growth. -/
example {ξ : Ordinal.{0}} {M : Type} {R : Realization.{0, 0} (blockStage ξ) M}
    (h : R.HasTerminalProperty (.inr (.inr ()))) :
    R.IsCoverHollowAtBlock ∧ R.topGradeSup = ⊤ :=
  ⟨isCoverHollowAtBlock_iff.mpr h.1, h.2⟩

/-- No realization at the successor stage `ω + 1` is cover-hollow at a block stage. -/
example {M : Type} (R : Realization.{0, 0} (ω + 1) M) : ¬ R.IsCoverHollowAtBlock := by
  rintro ⟨ξ, h, -⟩
  have := isSuccLimit_blockStage ξ
  rw [← h, ← Order.succ_eq_add_one] at this
  exact Order.not_isSuccLimit_succ _ this

/-- (R3) for cover-hollowness at a block stage is exactly (R3) at the block stages for
cover-hollow models: the predicate does not strengthen (R3). -/
example : HollowReceiving.{0, 0} IsCoverHollowAtBlock ↔
    ∀ ⦃ξ : Ordinal.{0}⦄ ⦃M : Type⦄ ⦃R : Realization.{0, 0} (blockStage ξ) M⦄, R.IsModel →
      R.IsCoverHollow → R.topGradeSup = ⊤ → ∀ ⦃n : ℕ⦄ (t : StageType.{0} (blockStage ξ) n)
        (c : Fin n → M), R.Covers t c → ∀ D ∈ t.cofaces, ∃ y : M, R.Covers D (Fin.snoc c y) := by
  refine ⟨fun h ξ _ _ hR hH ↦ h.exists_covers (isSuccLimit_blockStage ξ) hR
    (isCoverHollowAtBlock_iff.mpr hH), fun h ↦ ⟨fun α M R _ hR ⟨ξ, hα, hH⟩ ↦ ?_⟩⟩
  subst hα
  exact h hR hH

/-! ### One class per property, and the spectrum theorem -/

/-- Two codes with model expansions to `λ_ξ` sharing a terminal property have the same class,
under (R1), (R2) and (R3); terminality is not used. -/
example (hrec : FiniteCutReceiving.{0}) (hres : ResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    {c c' : ModelsOf densitySentence.{0}} (P : TerminalProperty ξ)
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage ξ))
    (e' : @ModelExpansion ℕ c'.1.toStructure (blockStage ξ))
    (h : e.1.HasTerminalProperty P) (h' : e'.1.HasTerminalProperty P) :
    (Quotient.mk _ c : Quotient (isoSetoid densitySentence.{0})) = Quotient.mk _ c' :=
  subsingleton_classes_of_property hrec hres hhol hξ P ⟨c, e, rfl, h⟩ ⟨c', e', rfl, h'⟩

/-- **The hypotheses of the spectrum theorem from the terminal classification**, as printed by
`#check @densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`:
```
CapToModel →
  FiniteCutReceiving →
    (∀ ξ < Ordinal.omega 1, ForcingDonors ξ) →
      ContinuationCriterion →
        Realization.ResidualReceiving →
          (Realization.HollowReceiving fun {α} {M} => Realization.IsCoverHollowAtBlock) →
            (∀ ξ < Ordinal.omega 1, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) →
              HasThinAlephOneSpectrum baseLanguage.densitySentence
```
No hypothesis on the countability of the losses, and no next-block uniqueness. -/
example : CapToModel.{0} → FiniteCutReceiving.{0} → (∀ ξ < ω₁, ForcingDonors.{0} ξ) →
    ContinuationCriterion.{0} → ResidualReceiving.{0, 0} →
    HollowReceiving.{0, 0} IsCoverHollowAtBlock →
    (∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Nonempty) →
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_terminalClassification

end VaughtConjecture
