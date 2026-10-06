/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.AllCarriers
import VaughtConjecture.MainTheorem.LowerBound

/-!
# The main theorem with the coatom extension property with apex at every countable block

Roadmap, Layer 6 ("Status: the hypotheses of the main theorem"), the reduction of the main theorem
to expansion domains (conditions 1–4), and the section on the top-free witnesses (step 7);
`IMPLEMENTATION.md`, checkpoints 5 and 6; semantic contract, items 5 and 9.

`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`
(`VaughtConjecture.MainTheorem.ModelExpansionDomains`) proves the thin `ℵ₁` spectrum of the
density sentence conditional on seven named hypotheses: the cap-to-model theorem at `ω`
(`CapToModel`), (R1), forcing donors at every countable block, the continuation criterion, (R2),
(R3) for cover-hollowness at a block stage, and nonempty losses of the expansion domains
(condition 4).  The theorems here replace the first and the last by one hypothesis, the coatom
extension property with apex at every countable block stage `λ_η = ω + ω · η`, `η < ω₁`
(`StageType.HasApexCoatomExtensions`; Layer 3, 3.1, the open part of (R6)), leaving six:

* the coatom extension property with apex at every countable block stage (`hext`);
* (R1), finite-cut receiving of models (`hrec`);
* forcing donors at every countable block index (`hF`);
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction);
* (R2), exact residual receiving (`hres`);
* (R3), exact hollow-growth receiving for cover-hollowness at a block stage (`hhol`).

Each is still to be proved.  The statements formerly taken as hypotheses are derived as follows,
each by a theorem compiled in this repository:

* the cap-to-model theorem at `ω`, from `hext` at `η = 0`
  (`CapToModel.of_hasApexCoatomExtensions`; for the carriers of every universe);
* next-block uniqueness of models, from `hrec` and `hF`
  (`Expansion.NextBlockUniqueness.of_forcingDonors`);
* countable losses (condition 2), from `hrec`, `hcont`, `hres` and `hhol`
  (`Expansion.expansionDomain_loss_countable`);
* nonempty losses (condition 4), from `hext` and next-block uniqueness
  (`hasNonemptyLosses_of_hasApexCoatomExtensions`; the class of the top-free witness at each
  block lies in the loss at that block).

The thin `ℵ₁` spectrum
(`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions`)
is the composition of `densitySentence_hasThinAlephOneSpectrum_of_hasApexCoatomExtensions` with
the last three derivations.  The counterexample form on all countable carriers
(`vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions`) applies
`vaughtCounterexample_allCarriers_of_expansionDomains` to the expansion domains of the density
sentence, with the cap-to-model theorem on the carriers of the universe `w` also derived from
`hext` at `η = 0`.

The continuation criterion remains a hypothesis.  It follows from (R4) and `hext` at the successor
blocks (`ContinuationCriterion.of_hasApexCoatomExtensions`), but (R4) is itself still to be proved
and the criterion is a consequence of it, so replacing the criterion by (R4) would give a weaker
theorem with as many hypotheses.

These theorems are conditional; the main theorem of the roadmap has none of these hypotheses.  The
theorem with seven hypotheses is kept beside them: the theorems here follow from it, and, given
(R1) and forcing donors, its hypotheses `CapToModel` and nonempty losses follow from the coatom
extension property with apex at every countable block stage, not conversely.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion StageType
open scoped Ordinal

/-- The coatom extension property with apex at every countable block stage gives it at `ω`, the
block stage `λ_0`. -/
private theorem hasApexCoatomExtensions_omega
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    HasApexCoatomExtensions.{0} ω :=
  blockStage_zero.{0} ▸ hext 0 (Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one)

/-- **The thin `ℵ₁` spectrum of the density sentence from the terminal classification and the
coatom extension property with apex at every countable block stage**: the density sentence has
exactly `ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise nonisomorphic ones,
conditional on the following six hypotheses, each still to be proved:
* finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3): next-block uniqueness,
  logical agreement, and the rigid-core comparison;
* forcing donors at every countable block index (`hF`; a finite construction of Layer 3):
  next-block uniqueness;
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction, Layer 4): the
  cover of the terminal models;
* exact residual receiving (`hres`; (R2) of the table of Layer 3): the residual comparison;
* exact hollow-growth receiving for cover-hollowness at a block stage (`hhol`; (R3) of the table
  of Layer 3): the hollow comparison;
* the coatom extension property with apex at every countable block stage (`hext`; Layer 3, 3.1,
  the open part of (R6)): the cap-to-model theorem at `ω` and the top-free witnesses.
Derived, not assumed: the cap-to-model theorem at `ω` (`CapToModel.of_hasApexCoatomExtensions`,
from `hext` at `η = 0`), next-block uniqueness (`Expansion.NextBlockUniqueness.of_forcingDonors`),
countable losses (`Expansion.expansionDomain_loss_countable`), and nonempty losses
(`hasNonemptyLosses_of_hasApexCoatomExtensions`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions
    (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_hasApexCoatomExtensions hext
    (NextBlockUniqueness.of_forcingDonors hrec hF) hrec
    (expansionDomain_loss_countable hrec hcont hres hhol)

/-- **A thin uncountable infinitary class on all countable carriers, from the terminal
classification and the coatom extension property with apex at every countable block stage**: the
conclusion of `vaughtCounterexample_allCarriers_of_expansionDomains` for the expansion domains of
the density sentence, conditional on the six hypotheses of
`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions`,
each still to be proved.  The cap-to-model theorem, at `ω` on `ℕ` for the first domain and on the
carriers of the universe `w` for the reduction to `ℕ`, is derived from `hext` at `η = 0`
(`CapToModel.of_hasApexCoatomExtensions`); next-block uniqueness, countable losses and nonempty
losses are derived as for the spectrum. -/
theorem vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions
    (hrec : FiniteCutReceiving.{0}) (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ)
    (hcont : ContinuationCriterion.{0}) (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧ ¬ φ.PerfectSetDichotomyAllCountable ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) :=
  have hcap : CapToModel.{0} :=
    CapToModel.of_hasApexCoatomExtensions (hasApexCoatomExtensions_omega hext)
  have hnext : NextBlockUniqueness.{0} := NextBlockUniqueness.of_forcingDonors hrec hF
  vaughtCounterexample_allCarriers_of_expansionDomains (modelExpansionDomains hcap hnext)
    (modelExpansionDomains_hasLogicalAgreement hcap hnext hrec)
    ⟨expansionDomain_loss_countable hrec hcont hres hhol⟩
    (hasNonemptyLosses_of_hasApexCoatomExtensions hcap hnext hext)
    (CapToModel.of_hasApexCoatomExtensions (hasApexCoatomExtensions_omega hext))

end VaughtConjecture.MainTheorem
