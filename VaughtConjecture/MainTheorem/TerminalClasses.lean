/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Losses
import VaughtConjecture.MainTheorem.Assembly

/-!
# Countably many terminal classes at each level

Roadmap, "Reduction to full presentations" ("Three separate arguments": terminal classification
gives the count at one level; here for the terminal models of the construction, whose countable
index is the countable family of Layer 4, the second of the four statements special to the
construction read in the application), Layer 4 (the countable cover of the terminal classes) and
Layer 5; `IMPLEMENTATION.md`, checkpoint 5 (checkpoint F, the count at one level); semantic
contract, item 8.

Throughout, `β : Ordinal.{0}` is a block index, `λ_β = blockStage β` its block stage, and the
classes are those of the density sentence coded on `ℕ` (`DensityClass`, the encoding of
`VaughtConjecture.MainTheorem.Assembly` and `VaughtConjecture.MainTheorem.Spectrum`).

**Terminal classes.**  A class is **terminal at `β`** (`terminalClasses β`) when some code of it
has a model expansion to `λ_β` that is terminal at `β` (`Realization.IsTerminalAt`): no model at
`λ_{β+1}` on the same carrier reduces to it, equivalently no model at any higher stage that is
zero or a limit does (`Realization.isTerminalAt_iff_forall_lt`).  Only some expansion of some
code is required to be terminal: no uniqueness of expansions is used, and no canonical expansion
is chosen.  A maximal presentation (`roadmap/README.md`, "Manuscript correspondence (required)",
item 5) is terminal, so the classes of codes with a maximal presentation at `β`, namely the loss
at `β`, are among the classes terminal at `β` (`loss_subset_terminalClasses`).

**Membership up to isomorphism** (`mem_terminalClasses_iff`, `mem_propertyClasses_iff`).  The
membership of a class is read at any code of it: a class is terminal at `β`, or has the terminal
property `P`, exactly when the structure of a given code has a model expansion to `λ_β` that is
terminal at `β`, or has the property `P`.  Model expansions transport along isomorphisms of base
structures (`ModelExpansion.map`), and terminality (`Realization.IsTerminalAt.map`) and the
terminal properties (`Realization.HasTerminalProperty.map`) along bijections of carriers.

**The count** (`countable_isoClasses_terminalAt`).  For `β < ω₁` the classes terminal at `β`
form a countable set.  The proof has three steps:

* *the cover* (`terminalClasses_subset_iUnion`): every class terminal at `β` lies in the set of
  classes with some terminal property `P` (`propertyClasses β P`), by the cover of the terminal
  models (`Realization.exists_hasTerminalProperty`, conditional on the continuation criterion);
* *one class per property* (`Expansion.subsingleton_classes_of_property`, whose set is
  `propertyClasses β P`): two codes with model expansions to `λ_β` sharing a terminal property
  have isomorphic structures, by the rigid-core comparison under (R1), the residual comparison
  under (R2), and the hollow comparison under (R3);
* *the countable index* (`countable_terminalProperty`, unconditional): rigid cores are typed by
  stage types at the countable stage `λ_β`, residual models by a natural number (their top grade),
  and hollow models by a single point.

A countable union of subsingletons is countable (`Counting.countable_of_subsingleton_cover`), so
no property of a class is chosen; a model may have several properties, and no property is claimed
to be realized.  In the rigid-core case the comparison keeps the core
(`ModelExpansion.exists_equiv_comp_eq_of_isGloballyRigidCore`, in
`VaughtConjecture.Expansion.Losses`); the count uses only the unpointed comparison.

**Losses** (`loss_subset_terminalClasses`, unconditional).  The successor loss of the expansion
domains at `ξ` is contained in the classes terminal at `ξ`, since every expansion of a class in
the loss is terminal (`ModelExpansion.isTerminalAt_of_mem_loss`); with `Set.Countable.mono`, the
count gives the countability of the losses (`Expansion.expansionDomain_loss_countable`).

**Carriers.**  The count is stated for classes coded on `ℕ`.  Terminality transports along a
bijection of carriers (`Realization.IsTerminalAt.map`); the form for countable models on all
carriers, through `MainTheorem.classOfCode`, is not derived here.

The hypotheses, **each still to be proved**, and where they are used:

* (R1) of the table of Layer 3 (`Expansion.FiniteCutReceiving`): the rigid-core comparison;
* output 3 of higher-stage reconstruction, Layer 4 (`ContinuationCriterion`, sufficiency only):
  the cover;
* (R2) of the table of Layer 3 (`Realization.ResidualReceiving`): the residual comparison;
* (R3) of the table of Layer 3 (`Realization.HollowReceiving`, for cover-hollowness at a block
  stage, `Realization.IsCoverHollowAtBlock`): the hollow comparison.

Nothing here uses uniqueness or normalization of expansions, global termination, a canonical
property or representative of a class, disjointness of the properties, or the realizability of
every property.  The equivalence of cover-hollowness with the original anchor definition of
hollowness (semantic contract, item 8) is still to be proved.

**The restricted hollow property.**  With the hollow property restricted to cover-hollow models
without a globally rigid core (`Realization.HasRestrictedTerminalProperty`, in
`VaughtConjecture.Continuation.RestrictedHollow`), the count holds with (R3) for the restricted
predicate `Realization.IsCoverHollowWithoutRigidCoreAtBlock` in place of (R3) for
cover-hollowness at a block stage
(`countable_isoClasses_terminalAt_of_restrictedTerminalClassification`): the cover is
`Realization.exists_hasRestrictedTerminalProperty`, and one class per restricted property is
`Expansion.subsingleton_classes_of_restrictedProperty`.  (R3) for cover-hollowness at a block
stage implies (R3) for the restricted predicate (`Realization.HollowReceiving.withoutRigidCore`);
that the restricted hypothesis is strictly weaker is not shown.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open Ordinal FirstOrder Language Structure baseLanguage

/-- The **classes terminal at `β`**: the classes of models of the density sentence coded on `ℕ`
with a code whose structure has a model expansion to the block stage `λ_β` that is terminal at
`β`. -/
def terminalClasses (β : Ordinal.{0}) : Set DensityClass :=
  {q | ∃ (c : ModelsOf densitySentence.{0})
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage β)),
      Quotient.mk _ c = q ∧ e.1.IsTerminalAt β}

/-- The **classes with the terminal property `P`** at `β`: the classes with a code whose structure
has a model expansion to `λ_β` with the terminal property `P`.  It is the set of
`Expansion.subsingleton_classes_of_property`. -/
def propertyClasses (β : Ordinal.{0}) (P : TerminalProperty β) : Set DensityClass :=
  {q | ∃ (c : ModelsOf densitySentence.{0})
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage β)),
      Quotient.mk _ c = q ∧ e.1.HasTerminalProperty P}

/-- **Terminal classes, membership up to isomorphism**: a class is terminal at `β` exactly when the
structure of a given code of it has a model expansion to `λ_β` that is terminal at `β`.  A
terminal model expansion of another code of the class transports along an isomorphism of the two
structures (`ModelExpansion.map`, `Realization.IsTerminalAt.map`). -/
theorem mem_terminalClasses_iff {β : Ordinal.{0}} (c : ModelsOf densitySentence.{0}) :
    Quotient.mk _ c ∈ terminalClasses β ↔
      ∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage β), e.1.IsTerminalAt β := by
  refine ⟨fun ⟨c', e, hc', ht⟩ ↦ ?_, fun ⟨e, ht⟩ ↦ ⟨c, e, rfl, ht⟩⟩
  obtain ⟨i⟩ := (isoSetoid_r_iff (c₁ := c') (c₂ := c)).mp (Quotient.exact hc')
  exact ⟨@ModelExpansion.map ℕ c'.1.toStructure _ ℕ c.1.toStructure e i, ht.map _⟩

/-- **Classes with a terminal property, membership up to isomorphism**: a class has the terminal
property `P` at `β` exactly when the structure of a given code of it has a model expansion to
`λ_β` with the property `P`.  A model expansion of another code of the class with the property `P`
transports along an isomorphism of the two structures (`ModelExpansion.map`,
`Realization.HasTerminalProperty.map`). -/
theorem mem_propertyClasses_iff {β : Ordinal.{0}} {P : TerminalProperty β}
    (c : ModelsOf densitySentence.{0}) :
    Quotient.mk _ c ∈ propertyClasses β P ↔
      ∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage β), e.1.HasTerminalProperty P := by
  refine ⟨fun ⟨c', e, hc', hP⟩ ↦ ?_, fun ⟨e, hP⟩ ↦ ⟨c, e, rfl, hP⟩⟩
  obtain ⟨i⟩ := (isoSetoid_r_iff (c₁ := c') (c₂ := c)).mp (Quotient.exact hc')
  exact ⟨@ModelExpansion.map ℕ c'.1.toStructure _ ℕ c.1.toStructure e i, hP.map _⟩

/-- **Losses are terminal classes**: the successor loss of the expansion domains at `ξ` is
contained in the classes terminal at `ξ`.  Unconditional. -/
theorem loss_subset_terminalClasses (ξ : Ordinal.{0}) :
    Expansion.expansionDomain ξ \ Expansion.expansionDomain (ξ + 1) ⊆ terminalClasses ξ := by
  intro q hq
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e⟩ := (Expansion.mem_expansionDomain_iff c).mp hq.1
  exact (mem_terminalClasses_iff c).mpr ⟨e, e.isTerminalAt_of_mem_loss hq⟩

/-- **The cover of the terminal classes**: for `β < ω₁`, every class terminal at `β` has a
terminal property, conditional on the continuation criterion (`hcont`), still to be proved. -/
theorem terminalClasses_subset_iUnion (hcont : ContinuationCriterion.{0}) {β : Ordinal.{0}}
    (hβ : β < ω₁) : terminalClasses β ⊆ ⋃ P, propertyClasses β P := by
  rintro _ ⟨c, e, rfl, ht⟩
  let := c.1.toStructure
  obtain ⟨P, hP⟩ := e.1.exists_hasTerminalProperty hcont hβ e.2.isModel ht
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, hP⟩

/-- **Countably many terminal classes at each level**: for `β < ω₁`, only countably many classes
of models of the density sentence coded on `ℕ` have a code with a model expansion to `λ_β` that
is terminal at `β`.  Conditional on the following hypotheses, each still to be proved: (R1) of
the table of Layer 3 (`hrec`), output 3 of higher-stage reconstruction (`hcont`, the
continuation criterion; Layer 4), (R2) (`hres`) and (R3) (`hhol`) of the table of Layer 3. -/
theorem countable_isoClasses_terminalAt (hrec : Expansion.FiniteCutReceiving.{0})
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    {β : Ordinal.{0}} (hβ : β < ω₁) : (terminalClasses β).Countable :=
  have := countable_terminalProperty hβ
  Counting.countable_of_subsingleton_cover (propertyClasses β)
    (Expansion.subsingleton_classes_of_property hrec hres hhol hβ)
    (terminalClasses_subset_iUnion hcont hβ)

/-- **Countably many terminal classes at each level, with the restricted hollow property**: for
`β < ω₁`, only countably many classes of models of the density sentence coded on `ℕ` have a code
with a model expansion to `λ_β` that is terminal at `β`.  Conditional on the following hypotheses,
each still to be proved: (R1) of the table of Layer 3 (`hrec`), output 3 of higher-stage
reconstruction (`hcont`, the continuation criterion; Layer 4), (R2) (`hres`), and (R3) for
cover-hollowness without a globally rigid core at a block stage (`hhol`).  The cover is by the
classes with a given restricted terminal property
(`Realization.exists_hasRestrictedTerminalProperty`).  (R3) for cover-hollowness at a block stage
gives `hhol` (`Realization.HollowReceiving.withoutRigidCore`). -/
theorem countable_isoClasses_terminalAt_of_restrictedTerminalClassification
    (hrec : Expansion.FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowWithoutRigidCoreAtBlock)
    {β : Ordinal.{0}} (hβ : β < ω₁) : (terminalClasses β).Countable := by
  have := countable_terminalProperty hβ
  refine Counting.countable_of_subsingleton_cover _
    (Expansion.subsingleton_classes_of_restrictedProperty hrec hres hhol hβ) ?_
  rintro _ ⟨c, e, rfl, ht⟩
  let := c.1.toStructure
  obtain ⟨P, hP⟩ := e.1.exists_hasRestrictedTerminalProperty hcont hβ e.2.isModel ht
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, hP⟩

end VaughtConjecture.MainTheorem
