/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Definability.BlockFormulas
import VaughtConjecture.Expansion.Agreement

/-!
# Block determination from forcing thresholds

Roadmap, the quantitative reconstruction pathway of `roadmap/COMPANIONS.md` ("Further companion
results"), row 1: the threshold data of the chart formulas at the block stages, from Layer 4,
outputs 1–2 (`VaughtConjecture.Continuation.Normalization`).

The **forcing thresholds** at the block index `η` (`forcingThresholds η : CoverThresholds η`)
assign to a stage type `p` at `λ_η`, a cell `d` of `p` and `n : ℕ` the triples `(m, q, f)` such
that `(q, f)` forces `n` at `d` (`StageType.ForcesThreshold`): every stage type at `λ_{η+1}`
reducing to `q` has, on its face along `f`, a label at least `λ_η + n` at `d`.  These data depend
only on the finite data `(q, f, p, d)`.

**Results.**

* `forcingThresholds_determines`: block determination at `η < ω₁` (`CoverThresholds.Determines`)
  for the forcing thresholds, conditional on finite-extension receiving of models
  (`Expansion.FiniteExtensionReceiving`, which follows from (R1) of the table of Layer 3 by
  `Expansion.FiniteCutReceiving.finiteExtensionReceiving`; still to be proved) and on forcing donors
  at `η` (`ForcingDonors`, still to be proved).  It is the threshold lemma
  (`Realization.le_label_iff_exists_forcesThreshold`) applied to a model expansion at the limit
  stage `λ_{η+1} < ω₁`, whose reduction to `λ_η` is the reduction of the expansion.
* `realize_blockFormula_forcingThresholds_iff`: the chart formulas built from the forcing thresholds
  hold of exactly the covers in every model expansion to `λ_η`, under the same hypotheses at every
  block index below `η`.

**The shape of the threshold data.**  The stable value of a cell is the supremum over rooted
covers of the provisional offset (`StageType.provisionalOffset`), an offset determined by the
cover's type at `λ_η`, the coordinate embedding and the transported cell, and the threshold
`λ_η + n ≤ label` is witnessed by a single rooted cover forcing `n`: the existential finite-data
form of `CoverThresholds.Determines`.  An eventual-value construction that allows decreases does
not arise.  What remains is completeness: finite-extension receiving and forcing donors.

Neither uniqueness nor coherence of expansions is assumed, and nothing here gives the existence of
an expansion.

## Placement

`roadmap/COMPANIONS.md`, Further companion results, Quantitative reconstruction, row 1.
-/

universe w

namespace VaughtConjecture

open Ordinal

/-- The **forcing thresholds** at the block index `η`: for a stage type `p` at `λ_η`, a cell `d`
of `p` and `n : ℕ`, the triples `(m, q, f)` such that `(q, f)` forces `n` at `d`. -/
def forcingThresholds (η : Ordinal.{0}) : CoverThresholds η := fun _ p d n ↦
  {x | StageType.ForcesThreshold (blockStage (η + 1)) (isSuccPrelimit_blockStage η) x.2.1 x.2.2 p
    d n}

/-- **Block determination by the forcing thresholds**, conditional on finite-extension receiving
of models (from (R1), still to be proved) and on forcing donors at `η` (still to be proved). -/
theorem forcingThresholds_determines (hrec : Expansion.FiniteExtensionReceiving.{w})
    {η : Ordinal.{0}} (hF : ForcingDonors.{0} η) (hη : η < ω₁) :
    (forcingThresholds η).Determines.{w} :=
  fun _ _ R _ _ _ hc d hd n ↦ Realization.le_label_iff_exists_forcesThreshold
    R.2.isModel.isConsistent R.2.isModel.hasLegalTypes
    (hrec.receive (isSuccLimit_blockStage (η + 1))
      (blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hη)) R.1 R.2.isModel)
    hF hc d hd n

/-- **Correctness of the chart formulas built from the forcing thresholds**, conditional on
finite-extension receiving of models (from (R1), still to be proved) and on forcing donors at every
block index below `η` (still to be proved): in every model expansion `R` to `λ_η`, the formula of
`t` holds of a tuple exactly when the tuple covers `t` in `R`. -/
theorem realize_blockFormula_forcingThresholds_iff (hrec : Expansion.FiniteExtensionReceiving.{w})
    {η : Ordinal.{0}} (hF : ∀ ξ < η, ForcingDonors.{0} ξ) (hη : η < ω₁) {M : Type w}
    [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage η)) {k : ℕ}
    (t : StageType.{0} (blockStage η) k) (c : Fin k → M) :
    (blockFormula forcingThresholds η hη t).Realize c ↔ R.1.Covers t c :=
  realize_blockFormula_iff forcingThresholds
    (fun ξ hξ ↦ forcingThresholds_determines hrec (hF ξ hξ) (hξ.trans hη)) hη R t c

end VaughtConjecture
