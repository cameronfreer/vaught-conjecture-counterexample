/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Definability.BlockFormulas

/-!
# Block determination from forcing thresholds

Roadmap, the quantitative reconstruction pathway of `roadmap/COMPANIONS.md` ("Further companion
results"), row 1: the threshold data of the chart formulas at the block stages, from Layer 4,
outputs 1–2 (`VaughtConjecture.Continuation.Normalization`).

A **rooted cover** of a tuple `c` in a realization `S` at `λ_η` is a triple `(m, q, f)` — a stage
type `q` at `λ_η` on `m` points and an embedding `f : Fin k ↪ Fin m` — such that `c` extends to a
cover of it in `S` (`Realization.ExtendsToCover`): some tuple covering `q` in `S` restricts along
`f` to `c`.  The **forcing thresholds** at the block index `η` (`forcingThresholds η :
CoverThresholds η`) assign to a stage type `p` at `λ_η`, a cell `d` of `p` and `n : ℕ` the triples
`(m, q, f)` such that `(q, f)` forces `n` at `d` (`StageType.ForcesThreshold`): every stage type at
`λ_{η+1}` reducing to `q` has, on its face along `f`, a label at least `λ_η + n` at `d`.  These data
depend only on the finite data `(q, f, p, d)`.

**Results.**

* `forcingThresholds_determines`: block determination at `η` (`CoverThresholds.Determines`) for
  the forcing thresholds, conditional on finite-extension receiving of every model expansion to
  `λ_{η+1}` (a consequence of (R1) of the table of Layer 3, still to be proved; the form for models
  at countable limit stages is `Expansion.FiniteExtensionReceiving.forcingThresholds_determines`,
  Layer 5) and on forcing donors at `η` (`ForcingDonors`, still to be proved).  It is the threshold
  lemma (`Realization.le_label_iff_exists_forcesThreshold`) applied to a model expansion to
  `λ_{η+1}`, whose reduction to `λ_η` is the reduction of the expansion.
* `realize_blockFormula_forcingThresholds_iff`: the chart formulas built from the forcing thresholds
  hold of exactly the covers in every model expansion to `λ_η`, under the same hypotheses at every
  block index below `η`.

**The shape of the threshold data, and what is conditional.**  For the stable label the
single-cover form holds unconditionally: the stable value of a cell is the supremum over rooted
covers of the provisional offset (`StageType.provisionalOffset`), determined by the cover's type at
`λ_η`, the coordinate embedding and the transported cell, and the stable label is at least
`λ_η + n` exactly when a single rooted cover forces `n` (`Realization.coe_add_le_stableLabel_iff`).
An eventual-value construction that allows decreases does not arise.  The conditional part is
normalization: that the label of the cell equals its stable label
(`Realization.label_eq_stableLabel`), which uses finite-extension receiving and forcing donors.

Neither uniqueness nor coherence of expansions is assumed, and nothing here gives the existence of
an expansion.  The import closure of this module meets none of the forbidden prefixes of the
row-1 guard: finite-extension receiving enters as a hypothesis on the model expansions.

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
of every model expansion to `λ_{η+1}` (from (R1), still to be proved) and on forcing donors at `η`
(still to be proved). -/
theorem forcingThresholds_determines {η : Ordinal.{0}}
    (hrec : ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M]
      (R : ModelExpansion M (blockStage (η + 1))), R.1.HasFiniteExtensionReceiving)
    (hF : ForcingDonors.{0} η) : (forcingThresholds η).Determines.{w} :=
  -- Both sides agree by definition: the realization of `R.reduceBlock le_self_add` is
  -- `R.1.reduce (isSuccPrelimit_blockStage η)` (`ModelExpansion.reduceBlock_val`), and membership
  -- in `forcingThresholds η p d n` is `StageType.ForcesThreshold`.
  fun _ _ R _ _ _ hc d hd n ↦ Realization.le_label_iff_exists_forcesThreshold
    R.2.isModel.isConsistent R.2.isModel.hasLegalTypes (hrec R) hF hc d hd n

/-- **Correctness of the chart formulas built from the forcing thresholds**, conditional on
finite-extension receiving of the model expansions to `λ_{ξ+1}` (from (R1), still to be proved) and
on forcing donors (still to be proved) at every block index `ξ < η`: in every model expansion `R`
to `λ_η`, the formula of `t` holds of a tuple exactly when the tuple covers `t` in `R`. -/
theorem realize_blockFormula_forcingThresholds_iff {η : Ordinal.{0}}
    (hrec : ∀ ξ < η, ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M]
      (R : ModelExpansion M (blockStage (ξ + 1))), R.1.HasFiniteExtensionReceiving)
    (hF : ∀ ξ < η, ForcingDonors.{0} ξ) (hη : η < ω₁) {M : Type w}
    [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage η)) {k : ℕ}
    (t : StageType.{0} (blockStage η) k) (c : Fin k → M) :
    (blockFormula forcingThresholds η hη t).Realize c ↔ R.1.Covers t c :=
  realize_blockFormula_iff forcingThresholds
    (fun ξ hξ ↦ forcingThresholds_determines (hrec ξ hξ) (hF ξ hξ)) hη R t c

end VaughtConjecture
