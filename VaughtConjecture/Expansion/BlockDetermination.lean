/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Definability.BlockDetermination
import VaughtConjecture.Expansion.Agreement

/-!
# Block determination from finite-extension receiving of models

Roadmap, Layer 5 (comparison of model expansions), with Layer 4, outputs 1–2.

Finite-extension receiving of models at countable limit stages
(`Expansion.FiniteExtensionReceiving`, which follows from (R1) of the table of Layer 3 by
`Expansion.FiniteCutReceiving.finiteExtensionReceiving`; still to be proved) gives finite-extension
receiving of every model expansion to a block stage `λ_{η+1}`, `η < ω₁`, since `λ_{η+1}` is a
countable limit (`FiniteExtensionReceiving.hasFiniteExtensionReceiving_of_modelExpansion`).  With
forcing donors at `η` (`ForcingDonors`, still to be proved) it gives block determination for the
forcing thresholds (`FiniteExtensionReceiving.forcingThresholds_determines`).

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.Expansion

open Ordinal

/-- **Finite-extension receiving of model expansions to a block stage**: from finite-extension
receiving of models, every model expansion to `λ_{η+1}`, `η < ω₁`, has finite-extension
receiving. -/
theorem FiniteExtensionReceiving.hasFiniteExtensionReceiving_of_modelExpansion
    (hrec : FiniteExtensionReceiving.{w}) {η : Ordinal.{0}} (hη : η < ω₁) ⦃M : Type w⦄
    [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage (η + 1))) :
    R.1.HasFiniteExtensionReceiving :=
  hrec.receive (isSuccLimit_blockStage (η + 1))
    (blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hη)) R.1 R.2.isModel

/-- **Block determination by the forcing thresholds**, conditional on finite-extension receiving
of models (from (R1), still to be proved) and on forcing donors at `η` (still to be proved). -/
theorem FiniteExtensionReceiving.forcingThresholds_determines
    (hrec : FiniteExtensionReceiving.{w}) {η : Ordinal.{0}} (hF : ForcingDonors.{0} η)
    (hη : η < ω₁) : (forcingThresholds η).Determines.{w} :=
  VaughtConjecture.forcingThresholds_determines
    (hrec.hasFiniteExtensionReceiving_of_modelExpansion hη) hF

end VaughtConjecture.Expansion
