/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SolutionDefinitions

/-!
# Expected failure: a weakened statement

A valid proof, with the standard axioms only, of a weaker statement under the name of the
reference statement: the clause `NoPerfectAntichain` is dropped.  Every definition is the one of
the reference statement.  Comparator must reject it because the statement differs
(`comparator/check.sh` asserts the diagnostic "Challenge and solution theorem statement do not
match").
-/

namespace PalomarChallenge

open VaughtConjecture

/-- The reference statement without its last clause. -/
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧ NoFiniteModels R φ :=
  ⟨baseLanguage.{0}.Relations, inferInstance, baseLanguage.densitySentence.{0},
    card_isoClasses_densitySentence, noFiniteModels_densitySentence⟩

end PalomarChallenge
