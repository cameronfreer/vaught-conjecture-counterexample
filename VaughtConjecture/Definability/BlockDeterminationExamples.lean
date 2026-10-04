/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Definability.BlockDetermination

/-!
# Examples for block determination from forcing thresholds

Special cases of `VaughtConjecture.Definability.BlockDetermination` at the block index `η = 0`
(`λ_0 = ω`, `λ_1 = ω + ω`):

* block determination at `0` for the forcing thresholds, from finite-extension receiving and
  forcing donors at `0`;
* the chart formulas at `λ_1` (written `0 + 1`, the form of the successor equation) built from the
  forcing thresholds hold of exactly the covers, under the same hypotheses;
* membership in the forcing thresholds is forcing, and a pair restricting to the root forces the
  grade of a cell reducing to the formal top (the order law).

## Placement

`roadmap/COMPANIONS.md`, Further companion results, Quantitative reconstruction, row 1.
-/

universe w

namespace VaughtConjecture.Definability.BlockDeterminationExamples

open Ordinal

/-- The countable ordinal `0`. -/
private theorem zero_lt_omega_one : (0 : Ordinal.{0}) < ω₁ :=
  omega0_pos.trans omega0_lt_omega_one

/-- Block determination at `0` for the forcing thresholds, conditional on finite-extension
receiving and on forcing donors at `0`. -/
example (hrec : Expansion.FiniteExtensionReceiving.{w}) (hF : ForcingDonors.{0} 0) :
    (forcingThresholds 0).Determines.{w} :=
  forcingThresholds_determines hrec hF zero_lt_omega_one

/-- The chart formulas at `λ_1` built from the forcing thresholds hold of exactly the covers, in
every model expansion to `λ_1`, conditional on finite-extension receiving and on forcing donors at
`0`. -/
example (hrec : Expansion.FiniteExtensionReceiving.{w}) (hF : ForcingDonors.{0} 0)
    (hη : (0 + 1 : Ordinal.{0}) < ω₁) {M : Type w} [baseLanguage.{0}.Structure M]
    (R : ModelExpansion M (blockStage (0 + 1))) {k : ℕ}
    (t : StageType.{0} (blockStage (0 + 1)) k) (c : Fin k → M) :
    (blockFormula forcingThresholds (0 + 1) hη t).Realize c ↔ R.1.Covers t c :=
  realize_blockFormula_forcingThresholds_iff hrec
    (fun _ hξ ↦ (Order.lt_add_one_iff.mp hξ).antisymm zero_le ▸ hF) hη R t c

/-- Membership in the forcing thresholds at `0` is forcing; by the order law, a pair restricting
to the root forces the grade of a cell labelled the formal top. -/
example {k m : ℕ} {q : StageType.{0} (blockStage 0) m} {f : Fin k ↪ Fin m}
    {p : StageType.{0} (blockStage 0) k} {d : Fin p.card}
    (hfp : StageType.restrictFace f q = some p) (hd : p.label d = ⊤) :
    ⟨m, q, f⟩ ∈ forcingThresholds 0 p d (p.toCellScheme.grade d) :=
  StageType.forcesThreshold_of_le_grade hfp hd le_rfl

end VaughtConjecture.Definability.BlockDeterminationExamples
