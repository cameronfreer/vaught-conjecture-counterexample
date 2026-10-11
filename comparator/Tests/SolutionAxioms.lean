/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Solution

/-!
# The axioms of the solution module

The solution module's theorem and the lemmas of `comparator/SolutionDefinitions.lean` use only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.  This is checked in the
elaborated environment, separately from Comparator's own check on the exported declarations.
-/

open Lean in
run_cmd do
  let roots := #[``PalomarChallenge.independent_challenge,
    ``PalomarChallenge.isomorphic_iff_structureIsoSetoid,
    ``PalomarChallenge.modelSetoid_baseLanguage_eq,
    ``PalomarChallenge.card_isoClasses_densitySentence,
    ``PalomarChallenge.noFiniteModels_densitySentence,
    ``PalomarChallenge.noPerfectAntichain_densitySentence]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in roots do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"axioms of {root}: {axioms}"
