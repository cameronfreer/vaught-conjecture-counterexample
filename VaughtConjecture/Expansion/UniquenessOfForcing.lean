/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Expansion.Agreement
import VaughtConjecture.Expansion.Uniqueness

/-!
# Next-block uniqueness from finite-cut receiving and forcing donors

Roadmap, Layer 5 (coherent countable-limit expansions, through condition 1 of the reduction of
the main theorem to expansion domains), with Layer 4, output 2 of higher-stage reconstruction
(normalization); semantic contract, items 5, 9 and 12.

Next-block uniqueness of models (`Expansion.NextBlockUniqueness`) is the hypothesis of the
successor step of uniqueness of model expansions (`ModelExpansion.subsingleton`).  Here it is
derived from two statements, both still to be proved:
* (R1) of the table of Layer 3, finite-cut receiving of models at countable limit stages
  (`Expansion.FiniteCutReceiving`), which gives finite-extension receiving of models
  (`Expansion.FiniteCutReceiving.finiteExtensionReceiving`);
* forcing donors (`ForcingDonors ξ`, in `VaughtConjecture.Continuation.Normalization`) at every
  countable block index `ξ`, a finite statement about legal stage types with no realization.

**The argument.**  Two models at `λ_{ξ+1}`, `ξ < ω₁`, with equal reductions to `λ_ξ` are exactly
consistent and have legal types; since `λ_{ξ+1}` is a countable limit stage
(`isSuccLimit_blockStage`, `blockStage_lt_omega_one`), finite-extension receiving of models
applies to both.  Determination by the reduction (`Realization.eq_of_reduce_eq_of_forcingDonors`,
which carries no hypothesis on the stage beyond `λ_{ξ+1} = λ_ξ + ω` and asks for forcing donors at
`ξ` only) then gives equality.  The countability `ξ < ω₁` is the binder of
`NextBlockUniqueness`; it is used only to apply receiving at `λ_{ξ+1}` and to select the forcing
donors at `ξ`.

**Not assumed and not claimed.**  No uniqueness or coherence of expansions is assumed: both are
derived (`ModelExpansion.subsingleton`, `ModelExpansion.reduceBlock_eq`).  Neither (R1) nor
forcing donors is proved here, so next-block uniqueness remains conditional on both.  Block
determination (`CoverThresholds.Determines`, of the quantitative reconstruction pathway) is not
used.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal

namespace Expansion

/-- **Determination of models at a block stage by their reduction**, conditional on
finite-extension receiving of models (from (R1), still to be proved) and on forcing donors at `ξ`
(still to be proved): two models at `λ_{ξ+1}`, `ξ < ω₁`, with equal reductions to `λ_ξ` are
equal.  Receiving applies at `λ_{ξ+1}`, a countable limit stage. -/
theorem FiniteExtensionReceiving.eq_of_reduce_eq_of_forcingDonors
    (hrec : FiniteExtensionReceiving.{w}) {ξ : Ordinal.{0}} (hF : ForcingDonors.{0} ξ)
    (hξ : ξ < ω₁) {M : Type w} {R R' : Realization.{0, w} (blockStage (ξ + 1)) M}
    (hR : R.IsModel) (hR' : R'.IsModel)
    (h : R.reduce (isSuccPrelimit_blockStage ξ) = R'.reduce (isSuccPrelimit_blockStage ξ)) :
    R = R' :=
  have hα := isSuccLimit_blockStage (ξ + 1)
  have hαω := blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hξ)
  Realization.eq_of_reduce_eq_of_forcingDonors hF hR.isConsistent hR'.isConsistent
    hR.hasLegalTypes hR'.hasLegalTypes (hrec.receive hα hαω R hR) (hrec.receive hα hαω R' hR') h

/-- **Next-block uniqueness from finite-cut receiving and forcing donors**: (R1) of the table of
Layer 3 (`hrec`, still to be proved) and forcing donors at every countable block index (`hF`;
compiled, `forcingDonors_of_blockStage`) give next-block uniqueness of models on the carriers in the
universe `w`. -/
theorem NextBlockUniqueness.of_forcingDonors (hrec : FiniteCutReceiving.{w})
    (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ) : NextBlockUniqueness.{w} :=
  ⟨fun hξ _ _ hR hR' h ↦
    hrec.finiteExtensionReceiving.eq_of_reduce_eq_of_forcingDonors (hF _ hξ) hξ hR hR' h⟩

end Expansion

end VaughtConjecture
