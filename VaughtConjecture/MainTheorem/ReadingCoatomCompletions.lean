/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCoatom
import VaughtConjecture.MainTheorem.CapToModel

/-!
# The continuation criterion from hypothesis 8 and reading coatom completions

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion); the main
theorem's hypothesis `ContinuationCriterion`; semantic contract, items 4 and 8.

(R4) follows from the coatom extension property at every `λ_{ξ+1}` and reading coatom completions
at every `ξ < ω₁` (`StableCappedReceiving.of_hasReadingCoatomCompletions`, in
`VaughtConjecture.Continuation.StableRecoveryCoatom`).  With the coface instances at the next block
(`ContinuationCriterion.of_hasApexCoatomExtensions`, in `VaughtConjecture.MainTheorem.CapToModel`),
the continuation criterion follows from hypothesis 8 at every `λ_{ξ+1}` and reading coatom
completions at every `ξ < ω₁` (`ContinuationCriterion.of_hasReadingCoatomCompletions`, compiled in
this repository (theorem named)).  Hypothesis 8 is compiled
(`StageType.hasApexCoatomExtensions_blockStage`); reading coatom completions
(`StageType.HasReadingCoatomCompletions`) are open, and none of the constructions of this
repository establishes whether they follow from hypothesis 8.

## Placement

This file belongs to the main theorem of `roadmap/README.md`; it is downstream of
`VaughtConjecture.Continuation.StableRecoveryCoatom` so that the latter does not import
`VaughtConjecture.MainTheorem.CapToModel`.
-/

universe w

namespace VaughtConjecture

open Ordinal

/-- **The continuation criterion from hypothesis 8 and reading coatom completions**: if the coatom
extension property with apex holds at every `λ_{ξ+1}` (hypothesis 8) and reading coatom
completions exist at every `ξ < ω₁`, the continuation criterion holds.  Hypothesis 8 enters twice:
for the intermediate coatom steps of (R4)
(`StableCappedReceiving.of_hasReadingCoatomCompletions`) and for the coface instances at the next
block (`ContinuationCriterion.of_hasApexCoatomExtensions`).  So (R4), and with it the continuation
criterion, is reduced to hypothesis 8 and `StageType.HasReadingCoatomCompletions`; the latter is
proved at no general input.  Both hypotheses are explicit; hypothesis 8 is compiled
(`StageType.hasApexCoatomExtensions_blockStage`), reading coatom completions are not proved. -/
theorem ContinuationCriterion.of_hasReadingCoatomCompletions
    (hext : ∀ ξ < ω₁, StageType.HasApexCoatomExtensions.{0} (blockStage (ξ + 1)))
    (h : ∀ ξ < ω₁, StageType.HasReadingCoatomCompletions.{0} ξ) : ContinuationCriterion.{w} :=
  .of_hasApexCoatomExtensions
    (.of_hasReadingCoatomCompletions (fun ξ hξ ↦ (hext ξ hξ).hasCoatomExtensions) h) hext

end VaughtConjecture
