/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Classification
import VaughtConjecture.Continuation.Comparison
import VaughtConjecture.Counting.Domains
import VaughtConjecture.Expansion.Agreement
import VaughtConjecture.Expansion.Domains

/-!
# The successor losses of the expansion domains are countable

Roadmap, the reduction of the main theorem to expansion domains (condition 2, the countable
successor losses), Layer 4 (the countable cover of the terminal classes) and Layer 5 (map
successor losses into fixed-stage terminal classes and obtain countability); semantic contract,
item 8.

Throughout, `ξ : Ordinal.{0}`, `λ_ξ = blockStage ξ`, and the **loss** at `ξ` is
`expansionDomain ξ \ expansionDomain (ξ + 1)`: by `Expansion.mem_expansionDomain_iff`, the classes
whose codes have a model expansion to `λ_ξ` and none to `λ_{ξ+1}`.

**Losses are terminal** (`ModelExpansion.isTerminalAt_of_mem_loss`, unconditional).  Every model
expansion to `λ_ξ` of a code of a class in the loss is terminal at `ξ`: a model at `λ_{ξ+1}`
reducing to it would be a model expansion of the same code (`IsExpansionOf.isTerminalAt`, by
`Realization.reduce_reduce`).  No uniqueness of expansions is used; uniqueness is needed only for
the converse, that a terminal expansion places its class in the loss.

**Cover-hollowness at a block stage.**  The hollow comparison takes (R3) of the table of Layer 3
(`Realization.HollowReceiving`) for cover-hollowness at a block stage
(`Realization.IsCoverHollowAtBlock`, in `VaughtConjecture.Continuation.Hollow`).  At a block stage
it is cover-hollowness (`Realization.isCoverHollowAtBlock_iff`), and every successor-limit stage,
the only stages at which (R3) applies, is a block stage (`exists_blockStage_eq_of_isSuccLimit`).
So (R3) for this predicate is (R3) for cover-hollowness at the block stages, not a strengthening.

**At most one class per property** (`subsingleton_classes_of_property`).  Two model expansions to
`λ_ξ`, on countable carriers, sharing a terminal property have isomorphic base structures
(`ModelExpansion.nonempty_equiv_of_hasTerminalProperty`), by the comparisons of
`VaughtConjecture.Continuation.Comparison`: the rigid-core comparison (the top-free case is the
core on no points), the residual comparison under (R2), and the hollow comparison under (R3).  The
finite-extension receiving that the rigid-core comparison takes for each expansion is supplied by
(R1) (`FiniteCutReceiving.finiteExtensionReceiving`); no exact receiving for donors with top cells
is assumed, since rigidity of the core is what makes cutoff receiving exact.  Terminality is not
used here.  In the rigid-core case the comparison keeps the core
(`ModelExpansion.exists_equiv_comp_eq_of_isGloballyRigidCore`, on (R1) only): the isomorphism
carries the one core to the other.  The count uses only the unpointed comparison.

**Countability** (`expansionDomain_loss_countable`).  The loss at `ξ < ω₁` is covered by the
countably many sets of classes with a given terminal property (`countable_terminalProperty`): each
class in the loss has an expansion to `λ_ξ`, which is terminal, hence has some property under the
continuation criterion (`Realization.exists_hasTerminalProperty`).  Each set is a subsingleton,
so the loss is countable (`Counting.countable_of_subsingleton_cover`).  The properties need not be
disjoint, and no canonical property of a class is chosen.

The hypotheses, **each still to be proved**, and where they are used:

* (R1) of the table of Layer 3 (`FiniteCutReceiving`, open): the rigid-core comparison;
* output 3 of higher-stage reconstruction, Layer 4 (`ContinuationCriterion`, sufficiency only):
  the cover;
* (R2) of the table of Layer 3 (`Realization.ResidualReceiving`): the residual comparison;
* (R3) of the table of Layer 3 (`Realization.HollowReceiving`, for cover-hollowness at a block
  stage): the hollow comparison.

Nothing here uses the converse of output 3, next-block uniqueness, normalization, forcing donors,
global termination, disjointness of the properties, or characteristic arity.  The equivalence of
cover-hollowness with the original anchor definition of hollowness (semantic contract, item 8) is
still to be proved.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

/-- **Expansions of a class in a loss are terminal**: every model expansion to `λ_ξ` of a code
whose class lies in the loss at `ξ` is terminal at `ξ`.  Unconditional. -/
theorem ModelExpansion.isTerminalAt_of_mem_loss {ξ : Ordinal.{0}}
    {c : ModelsOf densitySentence.{0}}
    (hq : Quotient.mk _ c ∈ Expansion.expansionDomain ξ \ Expansion.expansionDomain (ξ + 1))
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage ξ)) : e.1.IsTerminalAt ξ :=
  let := c.1.toStructure
  e.2.isTerminalAt (not_nonempty_iff.mp ((Expansion.mem_expansionDomain_iff c).not.mp hq.2))

/-- **Two model expansions sharing a terminal property have isomorphic base structures**, for
countable carriers at `λ_ξ` with `ξ < ω₁`, conditional on (R1) (`hrec`), (R2) (`hres`) and (R3)
(`hhol`) of the table of Layer 3, each still to be proved.  (R1) is used for the rigid-core
property, (R2) for the residual property, and (R3) for the hollow property. -/
theorem ModelExpansion.nonempty_equiv_of_hasTerminalProperty {M N : Type w}
    [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N] [Countable M] [Countable N]
    (hrec : Expansion.FiniteCutReceiving.{w}) (hres : Realization.ResidualReceiving.{0, w})
    (hhol : Realization.HollowReceiving.{0, w} Realization.IsCoverHollowAtBlock)
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    {P : TerminalProperty ξ} (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion N (blockStage ξ)) (h : e.1.HasTerminalProperty P)
    (h' : e'.1.HasTerminalProperty P) : Nonempty (M ≃[baseLanguage.{0}] N) := by
  have hα := isSuccLimit_blockStage ξ
  have hr {K : Type w} (R : Realization.{0, w} (blockStage ξ) K) :=
    hrec.finiteExtensionReceiving.receive hα (blockStage_lt_omega_one hξ) R
  rcases P with ⟨_, p⟩ | K | ⟨⟩
  · obtain ⟨x, hx, hcx⟩ := h
    obtain ⟨y, hy, hcy⟩ := h'
    exact Realization.nonempty_equiv_of_isGloballyRigidCore hα e.2 e'.2 (hr _ e.2.isModel)
      (hr _ e'.2.isModel) hx hy hcx hcy
  · exact Realization.nonempty_equiv_of_residual hres hα e.2 e'.2 h.1 h'.1 h.2 h'.2
  · exact Realization.nonempty_equiv_of_hollow hhol hα e.2 e'.2 ⟨ξ, rfl, h.1⟩ ⟨ξ, rfl, h'.1⟩ h.2
      h'.2

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

namespace Expansion

open Realization

/-- **At most one class per terminal property**: for `ξ < ω₁`, the classes with a code having a
model expansion to `λ_ξ` with the terminal property `P` form a subsingleton, conditional on (R1)
(`hrec`), (R2) (`hres`) and (R3) (`hhol`) of the table of Layer 3, each still to be proved. -/
theorem subsingleton_classes_of_property (hrec : FiniteCutReceiving.{0})
    (hres : ResidualReceiving.{0, 0}) (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock)
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁) (P : TerminalProperty ξ) :
    {q : Quotient (isoSetoid densitySentence.{0}) | ∃ (c : ModelsOf densitySentence.{0})
      (e : @ModelExpansion ℕ c.1.toStructure (blockStage ξ)),
        Quotient.mk _ c = q ∧ e.1.HasTerminalProperty P}.Subsingleton := by
  rintro _ ⟨c, e, rfl, h⟩ _ ⟨c', e', rfl, h'⟩
  obtain ⟨i⟩ := @ModelExpansion.nonempty_equiv_of_hasTerminalProperty ℕ ℕ c.1.toStructure
    c'.1.toStructure _ _ hrec hres hhol ξ hξ P e e' h h'
  exact Quotient.sound (isoSetoid_r_iff.mpr ⟨i⟩)

/-- **The successor losses of the expansion domains are countable**, conditional on the following
hypotheses, each still to be proved: (R1) of the table of Layer 3 (`hrec`), output 3 of
higher-stage reconstruction (`hcont`, the continuation criterion; Layer 4), (R2) (`hres`) and (R3)
(`hhol`) of the table of Layer 3.  The
loss at `ξ` is covered by the countably many subsingletons of classes with a given terminal
property, since every expansion of a class in the loss is terminal. -/
theorem expansionDomain_loss_countable (hrec : FiniteCutReceiving.{0})
    (hcont : ContinuationCriterion.{0}) (hres : ResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsCoverHollowAtBlock) :
    ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable := by
  intro ξ hξ
  have := countable_terminalProperty hξ
  refine Counting.countable_of_subsingleton_cover _
    (subsingleton_classes_of_property hrec hres hhol hξ) fun q hq ↦ ?_
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e⟩ := (mem_expansionDomain_iff c).mp hq.1
  obtain ⟨P, hP⟩ :=
    e.1.exists_hasTerminalProperty hcont hξ e.2.isModel (e.isTerminalAt_of_mem_loss hq)
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, hP⟩

end Expansion

end VaughtConjecture
