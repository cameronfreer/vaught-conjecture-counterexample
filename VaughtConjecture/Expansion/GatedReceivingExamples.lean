/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.GatedReceiving

/-!
# Examples for receiving from the gated pinned extension property

Special cases of `VaughtConjecture.Expansion.GatedReceiving`:

* under the gated pinned extension property at every countable limit stage, two base structures
  with model expansions to `λ_η`, for `η < ω₁`, have back-and-forth equivalent empty tuples at
  `η`, and two codes on `ℕ` with such expansions agree on the sentences of quantifier rank at
  most `η`: the theorems of `VaughtConjecture.Expansion.Agreement` with finite-extension
  receiving supplied by `finiteExtensionReceiving_of_hasGatedPinnedExtensions`;
* the height `η = 0`, where the same conclusion also holds with no hypothesis.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.Expansion

open Ordinal FirstOrder Language Comparison

variable {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
  (hg : ∀ ⦃α : Ordinal.{0}⦄, Order.IsSuccLimit α → α < ω₁ →
    StageType.HasGatedPinnedExtensions α)
include hg

/-- **Back-and-forth equivalence under the gated pinned extension property**: two base structures
with model expansions to `λ_η`, for `η < ω₁`, have back-and-forth equivalent empty tuples at
`η`. -/
example {η : Ordinal.{0}} (hη : η < ω₁) (hM : Nonempty (ModelExpansion M (blockStage η)))
    (hN : Nonempty (ModelExpansion N (blockStage η))) :
    BFEquiv (L := baseLanguage.{0}) (M := M) (N := N) η 0 ![] ![] :=
  bfEquiv_of_modelExpansions (finiteExtensionReceiving_of_hasGatedPinnedExtensions hg) hη hM hN

/-- **Sentence agreement for codes under the gated pinned extension property**: two codes on `ℕ`
with model expansions to `λ_η`, for `η < ω₁`, lie in the same sets `ModelsOf θ` for the sentences
of quantifier rank at most `η`. -/
example {η : Ordinal.{0}} (hη : η < ω₁) (c₁ c₂ : StructureSpace baseLanguage.{0})
    (h₁ : Nonempty (@ModelExpansion ℕ c₁.toStructure (blockStage η)))
    (h₂ : Nonempty (@ModelExpansion ℕ c₂.toStructure (blockStage η)))
    (θ : baseLanguage.{0}.Sentenceω) (hθ : θ.qrank ≤ η) :
    c₁ ∈ ModelsOf θ ↔ c₂ ∈ ModelsOf θ :=
  mem_modelsOf_iff_of_modelExpansions (finiteExtensionReceiving_of_hasGatedPinnedExtensions hg)
    hη c₁ c₂ h₁ h₂ θ hθ

/-- **The height `0`**: the instance `η = 0` of the first example.  It also holds without the
gated pinned extension property, since the forth and back laws are vacuous at height `0`
(`VaughtConjecture.Expansion.AgreementExamples`). -/
example (hM : Nonempty (ModelExpansion M (blockStage 0)))
    (hN : Nonempty (ModelExpansion N (blockStage 0))) :
    BFEquiv (L := baseLanguage.{0}) (M := M) (N := N) (0 : Ordinal.{0}) 0 ![] ![] :=
  bfEquiv_of_modelExpansions (finiteExtensionReceiving_of_hasGatedPinnedExtensions hg)
    (omega0_pos.trans omega0_lt_omega_one) hM hN

end VaughtConjecture.Expansion
