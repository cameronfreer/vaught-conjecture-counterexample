/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Descriptive.StructureIsoSetoid
import VaughtConjecture.Language.Density
import VaughtConjecture.Realization.Expansion

/-!
# The expansion domains

Roadmap, the reduction of the main theorem to expansion domains (condition 1) and Layer 5
(construct the expansion domain on actual isomorphism classes; downward closure and literal
same-carrier normalization); semantic contract, items 5, 9 and 12.

The classes are the models of the density sentence coded on `ℕ`, up to isomorphism:
`Quotient (isoSetoid densitySentence)`, from the infinitary-logic library.  The **expansion
domain** at `η` (`expansionDomain η`) is the set of classes with a coded representative on `ℕ`
whose structure has a model expansion to the block stage `λ_η = ω + ω · η`, on the same carrier
`ℕ` and with the structure of the code as its literal base reduct (`ModelExpansion`, in
`VaughtConjecture.Realization.Expansion`).  The definition is literal and unguarded: it is made at
every ordinal `η`, and no canonical expansion, no uniqueness of expansions, and no coherence of
expansions at different stages enter it.

**Up to isomorphism.**  A model expansion transports along an isomorphism of base structures
(`ModelExpansion.map`), so membership does not depend on the representative: a class is in the
domain at `η` exactly when the structure of *any* of its codes has a model expansion to `λ_η`
(`mem_expansionDomain_iff`).

**Downward closure.**  The domains decrease (`expansionDomain_antitone`): an expansion to `λ_η`
reduces to an expansion to `λ_ξ` for `ξ ≤ η` (`ModelExpansion.reduceBlock`), with the same
representative.

**Emptiness above `ω₁`.**  A model on a countable carrier has a countable stage
(`Realization.IsModel.lt_omega_one`, by the uniformity clause), and `η ≤ λ_η`, so the domains at
`η ≥ ω₁` are empty (`expansionDomain_eq_empty`), with no guard in the definition.

**The domain at `0`.**  A model expansion to `λ_0 = ω` is the realization of its base structure
(`ModelExpansion.val_eq_toRealization`), so a class is in the domain at `0` exactly when the
realization of the structure of a code of it is a model (`mem_expansionDomain_zero_iff`,
unconditional).  That the domain at `0` is every class (`expansionDomain_zero`) is therefore
equivalent to the modelhood of these realizations, and it is proved **conditional on the
cap-to-model theorem** at `ω` on `ℕ` (Layer 3, 3.4; checkpoint 4; compiled in this repository
(theorem named), `MainTheorem.capToModel`), stated as an explicit hypothesis in the unbundled form
of `VaughtConjecture.Language.Density`.  The finite-cut receiving it uses is the one the density
sentence provides, not (R1).

The other statements here are unconditional.  Continuity at limits is not part of the definition
and is not assumed: that the domain at a nonzero countable limit contains the intersection of the
earlier ones needs an actual model expansion at the limit.  A coherent family of model expansions
below a limit glues to one (`ModelExpansion.nonempty_of_coherent`, in
`VaughtConjecture.Realization.Limit`, which proves every clause of a model for the glued
expansion); the coherence of the expansions below the limit is to be derived from uniqueness of
expansions (semantic contract, item 9), not assumed.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

namespace Expansion

/-! ### The expansion domains -/

/-- The **expansion domain** at `η`: the classes of models of the density sentence coded on `ℕ`
with a coded representative whose structure has a model expansion to the block stage `λ_η`. -/
def expansionDomain (η : Ordinal.{0}) : Set (Quotient (isoSetoid densitySentence.{0})) :=
  {q | ∃ c : ModelsOf densitySentence.{0}, Quotient.mk _ c = q ∧
    Nonempty (@ModelExpansion ℕ c.1.toStructure (blockStage η))}

/-- **Membership up to isomorphism**: a class is in the expansion domain at `η` exactly when the
structure of a given code of it has a model expansion to `λ_η`.  A model expansion of another code
of the class transports along an isomorphism of the two structures (`ModelExpansion.map`). -/
theorem mem_expansionDomain_iff {η : Ordinal.{0}} (c : ModelsOf densitySentence.{0}) :
    Quotient.mk _ c ∈ expansionDomain η ↔
      Nonempty (@ModelExpansion ℕ c.1.toStructure (blockStage η)) := by
  refine ⟨fun ⟨c', hc', ⟨e⟩⟩ ↦ ?_, fun h ↦ ⟨c, rfl, h⟩⟩
  obtain ⟨i⟩ := (isoSetoid_r_iff (c₁ := c') (c₂ := c)).mp (Quotient.exact hc')
  exact ⟨@ModelExpansion.map ℕ c'.1.toStructure _ ℕ c.1.toStructure e i⟩

/-- **The expansion domains decrease**: an expansion to `λ_η` reduces to an expansion to `λ_ξ`
for `ξ ≤ η`. -/
theorem expansionDomain_antitone : Antitone expansionDomain :=
  fun _ _ h _ ⟨c, hc, ⟨e⟩⟩ ↦ ⟨c, hc, ⟨@ModelExpansion.reduceBlock ℕ c.1.toStructure _ _ e h⟩⟩

/-- **The expansion domains are empty at and above `ω₁`**: a model on `ℕ` has a countable stage,
and `η ≤ λ_η`. -/
theorem expansionDomain_eq_empty {η : Ordinal.{0}} (h : ω₁ ≤ η) : expansionDomain η = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨c, _, ⟨e⟩⟩ ↦
    (@ModelExpansion.isEmpty_of_omega_one_le ℕ c.1.toStructure _ _
      (h.trans (le_blockStage η))).false e

/-! ### The domain at `0`, conditional on the cap-to-model theorem -/

/-- **Membership in the domain at `0`**: a class is in the expansion domain at `0` exactly when
the realization of the structure of a code of it is a model.  The structure of a code is a type
assignment (`realize_densitySentence_iff`), and a model expansion to `λ_0 = ω` is the realization
of its base structure (`ModelExpansion.nonempty_omega_iff`). -/
theorem mem_expansionDomain_zero_iff (c : ModelsOf densitySentence.{0}) :
    Quotient.mk _ c ∈ expansionDomain 0 ↔ (@toRealization ℕ c.1.toStructure).IsModel := by
  let := c.1.toStructure
  rw [mem_expansionDomain_iff, blockStage_zero]
  exact ModelExpansion.nonempty_omega_iff ((realize_densitySentence_iff ℕ).mp c.2).1

/-- **The domain at `0` is every class, conditional on the cap-to-model theorem** at `ω` on `ℕ`
(`hcap`, in the unbundled form of `VaughtConjecture.Language.Density`; Layer 3, 3.4, and checkpoint
4 of the roadmap, compiled in this repository (theorem named) as `MainTheorem.capToModel`; the
bundled `MainTheorem.CapToModel.{0}` supplies it as `fun R ↦ hcap.isModel R`, and follows from the
coatom extension property with apex at `ω`, `MainTheorem.CapToModel.of_hasApexCoatomExtensions`, in
`VaughtConjecture.MainTheorem.CapToModel`).  The structure of every code satisfies the density
sentence, so its realization has legal types, a nonempty carrier, exact consistency, covering, and
the finite-cut receiving property (`realize_densitySentence_iff`); the receiving used is the one the
density sentence itself provides, not (R1).  Nothing weaker than `hcap` on these realizations
suffices: by `mem_expansionDomain_zero_iff`, the conclusion is equivalent to the modelhood of the
realization of every code of a model of the density sentence. -/
theorem expansionDomain_zero
    (hcap : ∀ R : Realization.{0, 0} ω ℕ, Nonempty ℕ → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel) :
    expansionDomain 0 = Set.univ :=
  Set.eq_univ_of_forall fun q ↦ Quotient.inductionOn q fun c ↦ by
    let := c.1.toStructure
    obtain ⟨-, hne, hcons, hcov, hr⟩ := (realize_densitySentence_iff ℕ).mp c.2
    exact (mem_expansionDomain_zero_iff c).mpr
      (hcap _ hne hasLegalTypes_toRealization hcons hcov hr)

end Expansion

end VaughtConjecture
