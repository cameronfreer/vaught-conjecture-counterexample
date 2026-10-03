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

These are unconditional.  Continuity at limits is not part of the definition and is not assumed:
that the domain at a nonzero countable limit contains the intersection of the earlier ones needs
an actual model expansion at the limit, built from expansions below it whose coherence is to be
derived from uniqueness of expansions (semantic contract, item 9).

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

end Expansion

end VaughtConjecture
