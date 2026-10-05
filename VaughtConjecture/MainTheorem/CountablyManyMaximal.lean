/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Losses
import VaughtConjecture.MainTheorem.Assembly

/-!
# Countably many terminal classes at each level

Roadmap, "Reduction to full presentations" (the count at one level, for the terminal models of
the construction: the second of the four statements special to the construction), Layer 4 (the
countable cover of the terminal classes) and Layer 5; `IMPLEMENTATION.md`, checkpoint 5
(checkpoint F of condition 2); semantic contract, item 8.

Throughout, `β : Ordinal.{0}` is a block index, `λ_β = blockStage β` its block stage, and the
classes are those of the density sentence coded on `ℕ` (`DensityClass`, the encoding of
`VaughtConjecture.MainTheorem.Assembly` and `VaughtConjecture.MainTheorem.Spectrum`).

**Terminal classes.**  A class is **terminal at `β`** (`terminalClasses β`) when some code of it
has a model expansion to `λ_β` that is terminal at `β` (`Realization.IsTerminalAt`): no model at
`λ_{β+1}` on the same carrier reduces to it, equivalently no model at any higher stage that is
zero or a limit does (`Realization.isTerminalAt_iff_forall_lt`).  So a terminal expansion is
maximal among the model expansions on its carrier under stage reduction; this is the sense of
"maximal" in the name of the module.  Only some expansion of some code is required to be
terminal: no uniqueness of expansions is used, and no canonical expansion is chosen.

**The count** (`countable_isoClasses_terminalAt`).  For `β < ω₁` the classes terminal at `β`
form a countable set.  The proof has three steps, each a theorem here:

* *the cover* (`terminalClasses_subset_iUnion`): every class terminal at `β` lies in the set of
  classes with some terminal property `P` (`propertyClasses β P`), by the cover of the terminal
  models (`Realization.exists_hasTerminalProperty`, conditional on the continuation criterion);
* *one class per property* (`subsingleton_propertyClasses`): two codes with model expansions to
  `λ_β` sharing a terminal property have isomorphic structures
  (`Expansion.subsingleton_classes_of_property`), by the rigid-core comparison under (R1), the
  residual comparison under (R2), and the hollow comparison under (R3);
* *the countable index* (`countable_terminalProperty`, unconditional): rigid cores are typed by
  stage types at the countable stage `λ_β`, residual models by a natural number (their top grade),
  and hollow models by a single point.

Choosing, for each class terminal at `β`, a property of one of its terminal expansions gives an
injection into the terminal properties (`exists_injective_terminalProperty`); the choice is not
canonical, a model may have several properties, and no property is claimed to be realized.

**The rigid case keeps the core** (`ModelExpansion.exists_equiv_comp_eq_of_isGloballyRigidCore`).
Two model expansions on countable carriers with globally rigid cores covering one stage type have
an isomorphism of their base structures carrying the one core to the other, conditional on (R1)
only.  The count itself uses only the unpointed comparison.

**Losses** (`loss_subset_terminalClasses`, unconditional).  The successor loss of the expansion
domains at `ξ` is contained in the classes terminal at `ξ`, since every expansion of a class in
the loss is terminal (`ModelExpansion.isTerminalAt_of_mem_loss`); so the count recovers the
countability of the losses (`Expansion.expansionDomain_loss_countable`).

The hypotheses, **each still to be proved**, and where they are used:

* (R1) of the table of Layer 3 (`Expansion.FiniteCutReceiving`): the rigid-core comparison;
* output 3 of higher-stage reconstruction, Layer 4 (`ContinuationCriterion`, sufficiency only):
  the cover;
* (R2) of the table of Layer 3 (`Realization.ResidualReceiving`): the residual comparison;
* (R3) of the table of Layer 3 (`Realization.HollowReceiving`, for cover-hollowness at a block
  stage, `Realization.IsCoverHollowAtBlock`): the hollow comparison.

Nothing here uses uniqueness or normalization of expansions, global termination, a canonical
property or representative of a class, disjointness of the properties, or the realizability of
every property.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

/-- **The rigid-core comparison of model expansions keeps the core**: two model expansions to
`λ_ξ`, `ξ < ω₁`, of countable base structures, with globally rigid cores `x₀` and `y₀` covering
one stage type `p`, have an isomorphism of their base structures carrying `x₀` to `y₀`,
conditional on (R1) of the table of Layer 3 (`hrec`), still to be proved. -/
theorem ModelExpansion.exists_equiv_comp_eq_of_isGloballyRigidCore {M N : Type w}
    [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N] [Countable M] [Countable N]
    (hrec : Expansion.FiniteCutReceiving.{w}) {ξ : Ordinal.{0}} (hξ : ξ < ω₁) {k : ℕ}
    {p : StageType.{0} (blockStage ξ) k} (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion N (blockStage ξ)) {x₀ : Fin k → M} {y₀ : Fin k → N}
    (hx : e.1.Covers p x₀) (hy : e'.1.Covers p y₀) (hcx : e.1.IsGloballyRigidCore x₀)
    (hcy : e'.1.IsGloballyRigidCore y₀) : ∃ i : M ≃[baseLanguage.{0}] N, ⇑i ∘ x₀ = y₀ := by
  have hα := isSuccLimit_blockStage ξ
  have hr {K : Type w} (R : Realization.{0, w} (blockStage ξ) K) :=
    hrec.finiteExtensionReceiving.receive hα (blockStage_lt_omega_one hξ) R
  exact Realization.exists_equiv_comp_eq_of_isGloballyRigidCore hα e.2 e'.2 (hr _ e.2.isModel)
    (hr _ e'.2.isModel) hx hy hcx hcy

namespace MainTheorem

/-- The **classes terminal at `β`**: the classes of models of the density sentence coded on `ℕ`
with a code whose structure has a model expansion to the block stage `λ_β` that is terminal at
`β`. -/
def terminalClasses (β : Ordinal.{0}) : Set DensityClass :=
  {q | ∃ (c : ModelsOf densitySentence.{0})
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage β)),
      Quotient.mk _ c = q ∧ e.1.IsTerminalAt β}

/-- The **classes with the terminal property `P`** at `β`: the classes with a code whose structure
has a model expansion to `λ_β` with the terminal property `P`. -/
def propertyClasses (β : Ordinal.{0}) (P : TerminalProperty β) : Set DensityClass :=
  {q | ∃ (c : ModelsOf densitySentence.{0})
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage β)),
      Quotient.mk _ c = q ∧ e.1.HasTerminalProperty P}

/-- **Losses are terminal classes**: the successor loss of the expansion domains at `ξ` is
contained in the classes terminal at `ξ`.  Unconditional. -/
theorem loss_subset_terminalClasses (ξ : Ordinal.{0}) :
    Expansion.expansionDomain ξ \ Expansion.expansionDomain (ξ + 1) ⊆ terminalClasses ξ := by
  intro q hq
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e⟩ := (Expansion.mem_expansionDomain_iff c).mp hq.1
  exact ⟨c, e, rfl, e.isTerminalAt_of_mem_loss hq⟩

/-- **The cover of the terminal classes**: for `β < ω₁`, every class terminal at `β` has a
terminal property, conditional on the continuation criterion (`hcont`), still to be proved. -/
theorem terminalClasses_subset_iUnion (hcont : ContinuationCriterion.{0}) {β : Ordinal.{0}}
    (hβ : β < ω₁) : terminalClasses β ⊆ ⋃ P, propertyClasses β P := by
  rintro _ ⟨c, e, rfl, ht⟩
  let := c.1.toStructure
  obtain ⟨P, hP⟩ := e.1.exists_hasTerminalProperty hcont hβ e.2.isModel ht
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, hP⟩

/-- **At most one class per terminal property**: for `β < ω₁`, the classes with the terminal
property `P` form a subsingleton, conditional on (R1) (`hrec`), (R2) (`hres`) and (R3) (`hhol`)
of the table of Layer 3, each still to be proved. -/
theorem subsingleton_propertyClasses (hrec : Expansion.FiniteCutReceiving.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    {β : Ordinal.{0}} (hβ : β < ω₁) (P : TerminalProperty β) :
    (propertyClasses β P).Subsingleton :=
  Expansion.subsingleton_classes_of_property hrec hres hhol hβ P

/-- **An injection of the terminal classes into the terminal properties**: for `β < ω₁`, there
is an injective map assigning to each class terminal at `β` a terminal property of a model
expansion of one of its codes, conditional on (R1) (`hrec`), the continuation criterion
(`hcont`), (R2) (`hres`) and (R3) (`hhol`), each still to be proved.  The map is chosen, not
canonical. -/
theorem exists_injective_terminalProperty (hrec : Expansion.FiniteCutReceiving.{0})
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ f : terminalClasses β → TerminalProperty β,
      Function.Injective f ∧ ∀ q, (q : DensityClass) ∈ propertyClasses β (f q) := by
  have h (q : terminalClasses β) : ∃ P, (q : DensityClass) ∈ propertyClasses β P :=
    Set.mem_iUnion.mp (terminalClasses_subset_iUnion hcont hβ q.2)
  choose f hf using h
  refine ⟨f, fun q q' hqq' ↦ Subtype.ext ?_, hf⟩
  exact subsingleton_propertyClasses hrec hres hhol hβ (f q') (hqq' ▸ hf q) (hf q')

/-- **Countably many terminal classes at each level**: for `β < ω₁`, only countably many classes
of models of the density sentence coded on `ℕ` have a code with a model expansion to `λ_β` that
is terminal at `β`.  Conditional on the following hypotheses, each still to be proved: (R1) of
the table of Layer 3 (`hrec`), output 3 of higher-stage reconstruction (`hcont`, the
continuation criterion; Layer 4), (R2) (`hres`) and (R3) (`hhol`) of the table of Layer 3. -/
theorem countable_isoClasses_terminalAt (hrec : Expansion.FiniteCutReceiving.{0})
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    {β : Ordinal.{0}} (hβ : β < ω₁) : (terminalClasses β).Countable := by
  have := countable_terminalProperty hβ
  obtain ⟨f, hf, -⟩ := exists_injective_terminalProperty hrec hcont hres hhol hβ
  exact Set.countable_coe_iff.mp hf.countable

end MainTheorem

end VaughtConjecture
