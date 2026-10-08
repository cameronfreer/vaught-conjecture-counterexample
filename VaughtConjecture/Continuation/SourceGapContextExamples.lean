/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceivingExamples
import VaughtConjecture.Continuation.SourceGapContext

/-!
# Examples: source-gap contexts

Checks for `VaughtConjecture.Continuation.SourceGapContext`.

* **The context of the determination counterexample for the predicate that is always true is not
  a source-gap context**: the root of the apex point `ExactReceivingExamples.apexPoint` (the stage
  type on no points) along the identity, at every grade, since the identity is surjective.
* **The apex point itself is not a source-gap context**, along any root and at any grade: it is
  built with `StageType.addApex` (`StageType.not_isSourceGapContext_addApex`).
-/

namespace VaughtConjecture

open StageType

namespace ExactReceivingExamples

/-- The root of the apex point along the identity is not a source-gap context. -/
example (t : StageType.{0} Ordinal.omega0 0)
    (_ : restrictFace Fin.castSuccEmb apexPoint = some t) (K : ℕ) :
    ¬ t.IsSourceGapContext K (Function.Embedding.refl _) :=
  not_isSourceGapContext_of_surjective fun i ↦ ⟨i, rfl⟩

/-- The apex point is not a source-gap context. -/
example {n : ℕ} (K : ℕ) (h : Fin n ↪ Fin 1) : ¬ apexPoint.IsSourceGapContext K h :=
  not_isSourceGapContext_addApex _ one_pos K h

end ExactReceivingExamples

end VaughtConjecture
