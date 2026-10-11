/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import SolutionDefinitions

/-!
# Expected failure: a solution with `sorry`

The statement and every definition are those of the reference statement, but the proof is `sorry`,
that is, the axiom `sorryAx`.  Comparator must reject it because `sorryAx` is not a permitted
axiom (`comparator/check.sh` asserts the diagnostic "Illegal axiom detected: 'sorryAx'").
-/

namespace PalomarChallenge

/-- The reference statement, with its proof left open. -/
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧
      NoFiniteModels R φ ∧ NoPerfectAntichain R φ := by
  sorry

end PalomarChallenge
