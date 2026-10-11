/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SolutionDefinitions

/-!
# The solution module for the Comparator check

A proof of the reference statement `PalomarChallenge.independent_challenge` of
`comparator/Challenge.lean`, for the relation symbols of `baseLanguage` and the sentence
`baseLanguage.densitySentence`, from the public statement of this repository,
`MainTheorem.vaughtCounterexample_allCarriers_densitySentence` (through the three clauses of
`comparator/SolutionDefinitions.lean`).  Neither this module nor anything it imports imports
`comparator/Challenge.lean`.
-/

namespace PalomarChallenge

open VaughtConjecture

/-- **The reference statement**, for the relation symbols of `baseLanguage` and the sentence
`baseLanguage.densitySentence`. -/
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧
      NoFiniteModels R φ ∧ NoPerfectAntichain R φ :=
  ⟨baseLanguage.{0}.Relations, inferInstance, baseLanguage.densitySentence.{0},
    card_isoClasses_densitySentence, noFiniteModels_densitySentence,
    noPerfectAntichain_densitySentence⟩

end PalomarChallenge
