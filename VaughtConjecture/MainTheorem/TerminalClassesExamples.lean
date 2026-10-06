/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.TerminalClasses

/-!
# Examples: countably many terminal classes at each level

* **The losses from the count.**  The successor losses are countable because they lie among the
  terminal classes, under the hypotheses of the count.
* **The base block.**  At `β = 0`, with `λ_0 = ω`, a code has at most one model expansion to
  `λ_0`, and the classes terminal at `0` are exactly the loss at `0`.
* **The empty core.**  The pointed comparison at the core on no points: two model expansions with
  top-grade supremum `0` covering one stage type on no points have isomorphic base structures,
  under (R1) only.
* **A chosen injection.**  Choosing a terminal property for each terminal class gives an
  injection into the countable index; the choice is not canonical.
* **Transport.**  Terminality and the terminal properties are read at any code of a class, and
  a model expansion transported along an isomorphism of base structures is terminal when the
  original is, and has its terminal properties.
-/

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage Realization Expansion MainTheorem

/-! ### The losses from the count -/

/-- The successor losses are countable, from the count of the terminal classes, under (R1), the
continuation criterion, (R2) and (R3). -/
example (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : ResidualReceiving.{0, 0}) (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) :
    ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable := fun _ hξ ↦
  (countable_isoClasses_terminalAt hrec hcont hres hhol hξ).mono (loss_subset_terminalClasses _)

/-! ### The base block -/

/-- At `β = 0` the classes terminal at `0` are exactly the loss at `0`: a code has at most one
model expansion to `λ_0 = ω`, so a terminal one is not the reduction of an expansion to `λ_1`.
Unconditional. -/
example : terminalClasses 0 = expansionDomain 0 \ expansionDomain (0 + 1) := by
  refine Set.Subset.antisymm ?_ (loss_subset_terminalClasses 0)
  intro q hq
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e, ht⟩ := (mem_terminalClasses_iff c).mp hq
  have : Subsingleton (ModelExpansion ℕ (blockStage (0 : Ordinal.{0}))) := by
    rw [blockStage_zero]
    exact ModelExpansion.instSubsingletonOmega
  refine ⟨(mem_expansionDomain_iff c).mpr ⟨e⟩, fun h ↦ ?_⟩
  obtain ⟨e'⟩ := (mem_expansionDomain_iff c).mp h
  exact ht e'.1 e'.2.isModel
    (congrArg Subtype.val (Subsingleton.elim (e'.reduceBlock zero_le) e))

/-- The classes terminal at `0` are countable, under (R1), the continuation criterion, (R2) and
(R3). -/
example (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : ResidualReceiving.{0, 0}) (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) :
    (terminalClasses 0).Countable :=
  countable_isoClasses_terminalAt hrec hcont hres hhol (omega0_pos.trans omega0_lt_omega_one)

/-! ### The empty core -/

/-- **The pointed comparison at the empty core**: two model expansions to `λ_ξ`, `ξ < ω₁`, of
countable base structures, with top-grade supremum `0` (every actual type top-free) and covering
one stage type on no points, have isomorphic base structures, under (R1) only. -/
example {M N : Type} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N] [Countable M]
    [Countable N] (hrec : FiniteCutReceiving.{0}) {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    {p : StageType.{0} (blockStage ξ) 0} (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion N (blockStage ξ)) (hx : e.1.Covers p ![]) (hy : e'.1.Covers p ![])
    (h0 : e.1.topGradeSup = 0) (h0' : e'.1.topGradeSup = 0) :
    Nonempty (M ≃[baseLanguage.{0}] N) :=
  have hα := isSuccLimit_blockStage ξ
  let ⟨i, _⟩ := ModelExpansion.exists_equiv_comp_eq_of_isGloballyRigidCore hrec hξ e e' hx hy
    ((e.2.isModel.isGloballyRigidCore_empty_iff hα).mpr h0)
    ((e'.2.isModel.isGloballyRigidCore_empty_iff hα).mpr h0')
  ⟨i⟩

/-! ### A chosen injection -/

/-- Choosing, for each class terminal at `β`, a terminal property of one of its terminal
expansions gives an injection into the terminal properties, under (R1), the continuation
criterion, (R2) and (R3).  The choice is not canonical: a model may have several properties. -/
example (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : ResidualReceiving.{0, 0}) (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock)
    {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ f : terminalClasses β → TerminalProperty β,
      Function.Injective f ∧ ∀ q, (q : DensityClass) ∈ propertyClasses β (f q) := by
  have h (q : terminalClasses β) : ∃ P, (q : DensityClass) ∈ propertyClasses β P :=
    Set.mem_iUnion.mp (terminalClasses_subset_iUnion hcont hβ q.2)
  choose f hf using h
  refine ⟨f, fun q q' hqq' ↦ Subtype.ext ?_, hf⟩
  exact subsingleton_classes_of_property hrec hres hhol hβ (f q') (hqq' ▸ hf q) (hf q')

/-! ### Transport -/

/-- **Terminality is read at any code**: two codes of one class have structures with a model
expansion to `λ_β` terminal at `β` together (`mem_terminalClasses_iff`). -/
example {β : Ordinal.{0}} (c c' : ModelsOf densitySentence.{0})
    (h : (Quotient.mk _ c : DensityClass) = Quotient.mk _ c') :
    (∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage β), e.1.IsTerminalAt β) ↔
      ∃ e : @ModelExpansion ℕ c'.1.toStructure (blockStage β), e.1.IsTerminalAt β := by
  rw [← mem_terminalClasses_iff, ← mem_terminalClasses_iff, h]

/-- **A terminal property is read at any code**: two codes of one class have structures with a
model expansion to `λ_β` with the terminal property `P` together (`mem_propertyClasses_iff`). -/
example {β : Ordinal.{0}} (P : TerminalProperty β) (c c' : ModelsOf densitySentence.{0})
    (h : (Quotient.mk _ c : DensityClass) = Quotient.mk _ c') :
    (∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage β), e.1.HasTerminalProperty P) ↔
      ∃ e : @ModelExpansion ℕ c'.1.toStructure (blockStage β), e.1.HasTerminalProperty P := by
  rw [← mem_propertyClasses_iff, ← mem_propertyClasses_iff, h]

/-- A model expansion transported along an isomorphism of base structures has the terminal
properties of the original (`Realization.hasTerminalProperty_map_iff`). -/
example {M : Type} {N : Type 1} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    {ξ : Ordinal.{0}} (f : ModelExpansion M (blockStage ξ)) (i : M ≃[baseLanguage.{0}] N)
    (P : TerminalProperty ξ) : (f.map i).1.HasTerminalProperty P ↔ f.1.HasTerminalProperty P := by
  rw [ModelExpansion.map_val, hasTerminalProperty_map_iff]

/-- A model expansion transported along an isomorphism of base structures is terminal when the
original is (`Realization.IsTerminalAt.map`); the carriers may lie in different universes. -/
example {M : Type} {N : Type 1} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    {ξ : Ordinal.{0}} (f : ModelExpansion M (blockStage ξ)) (i : M ≃[baseLanguage.{0}] N)
    (h : f.1.IsTerminalAt ξ) : (f.map i).1.IsTerminalAt ξ :=
  h.map _

end VaughtConjecture
