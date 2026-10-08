/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ForcingDonorsCoatom
import VaughtConjecture.MainTheorem.AllCarriers
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem
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
(condition 4).  The theorems of the six-hypothesis form replace the first and the last by one
hypothesis, the coatom extension property with apex at every countable block stage
`λ_η = ω + ω · η`, `η < ω₁` (`StageType.HasApexCoatomExtensions`; Layer 3, 3.1, (R6), compiled as
`StageType.hasApexCoatomExtensions_blockStage`), leaving six:

* the coatom extension property with apex at every countable block stage (`hext`);
* (R1), finite-cut receiving of models (`hrec`);
* forcing donors at every countable block index (`hF`);
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction);
* (R2), exact residual receiving (`hres`);
* (R3), exact hollow-growth receiving for cover-hollowness at a block stage (`hhol`).

Each is still to be proved except the first, now compiled (the four-hypothesis form, below).  The
statements formerly taken as hypotheses are derived as follows, each by a theorem compiled in this
repository:

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
and the criterion is a consequence of it together with `hext` at the successor blocks, so
replacing the criterion by (R4) would give a weaker theorem with as many hypotheses.

These theorems are conditional; the main theorem of the roadmap has none of these hypotheses.  The
theorem with seven hypotheses is kept beside them.  The six-hypothesis form comes from it by the
two derivations above (`CapToModel.of_hasApexCoatomExtensions` and
`hasNonemptyLosses_of_hasApexCoatomExtensions`), which give its hypotheses `CapToModel` and
nonempty losses from the coatom extension property with apex at every countable block stage,
given (R1) and forcing donors; the five-hypothesis form (below) adds the derivation of forcing
donors.  No converse is known; the seven-hypothesis form is not derived from the six-hypothesis
form.

## The five-hypothesis form

Forcing donors at every countable block index follow from `hext` at the next block stage
`λ_{ξ+1}` (`forcingDonors_of_forall_hasApexCoatomExtensions`), so `hF` is dropped in
`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'`
and `vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'`,
which take five hypotheses: (R1), the continuation criterion, (R2), (R3), and `hext`.  In them
the cap-to-model theorem is derived from `hext` (at `η = 0`); forcing donors from `hext` at the
next block stage; next-block uniqueness from (R1) and forcing donors; countable losses from (R1),
the continuation criterion, (R2) and (R3); and nonempty losses from `hext` and next-block
uniqueness.  No compiled theorem derives next-block uniqueness or countable losses from the
coatom extension property with apex alone; both derivations use (R1).  The six-hypothesis form is
kept, and the five-hypothesis form is obtained from it by the derivation of forcing donors.

## The four-hypothesis form

The coatom extension property with apex holds at every stage that is zero or a limit
(`StageType.hasApexCoatomExtensions`; compiled in this repository (theorem named)), in particular
at every block stage (`StageType.hasApexCoatomExtensions_blockStage`).  So `hext` is discharged in
`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification''` and
`vaughtCounterexample_allCarriers_of_terminalClassification''`, which take four hypotheses, each
still to be proved: (R1), the continuation criterion, (R2) and (R3).  They are the five-hypothesis
forms with `hext` given by that theorem.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion StageType
open scoped Ordinal

/-- **The thin `ℵ₁` spectrum of the density sentence from the terminal classification and the
coatom extension property with apex at every countable block stage**: the density sentence has
exactly `ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise nonisomorphic ones,
conditional on the following six hypotheses, each still to be proved except the last, now compiled
(`StageType.hasApexCoatomExtensions_blockStage`):
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
  (R6), compiled as `StageType.hasApexCoatomExtensions_blockStage`): the cap-to-model theorem at `ω`
  and the top-free witnesses.
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
each still to be proved except `hext`, now compiled.  The cap-to-model theorem, at `ω` on `ℕ` for
the first domain and on the
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
  have hω := hasApexCoatomExtensions_omega_of_forall_blockStage hext
  have hcap : CapToModel.{0} := CapToModel.of_hasApexCoatomExtensions hω
  have hnext : NextBlockUniqueness.{0} := NextBlockUniqueness.of_forcingDonors hrec hF
  vaughtCounterexample_allCarriers_of_expansionDomains (modelExpansionDomains hcap hnext)
    (modelExpansionDomains_hasLogicalAgreement hcap hnext hrec)
    ⟨expansionDomain_loss_countable hrec hcont hres hhol⟩
    (hasNonemptyLosses_of_hasApexCoatomExtensions hcap hnext hext)
    (CapToModel.of_hasApexCoatomExtensions hω)

/-- **The thin `ℵ₁` spectrum of the density sentence from the terminal classification and the
coatom extension property with apex at every countable block stage, with forcing donors
derived**: the conclusion of
`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions`,
conditional on the following five hypotheses, each still to be proved except the last, now compiled
(`StageType.hasApexCoatomExtensions_blockStage`):
* finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3);
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction, Layer 4);
* exact residual receiving (`hres`; (R2) of the table of Layer 3);
* exact hollow-growth receiving for cover-hollowness at a block stage (`hhol`; (R3) of the table
  of Layer 3);
* the coatom extension property with apex at every countable block stage (`hext`; Layer 3, 3.1,
  (R6), compiled as `StageType.hasApexCoatomExtensions_blockStage`).
Derived, not assumed: the cap-to-model theorem at `ω`, from `hext` at `η = 0`
(`CapToModel.of_hasApexCoatomExtensions`); forcing donors at every countable block index, from
`hext` at the next block stage (`forcingDonors_of_forall_hasApexCoatomExtensions`); next-block
uniqueness, from `hrec` and forcing donors (`Expansion.NextBlockUniqueness.of_forcingDonors`);
countable losses, from `hrec`, `hcont`, `hres` and `hhol`
(`Expansion.expansionDomain_loss_countable`); and nonempty losses, from `hext` and next-block
uniqueness (`hasNonemptyLosses_of_hasApexCoatomExtensions`). -/
theorem
    densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions hrec
    (forcingDonors_of_forall_hasApexCoatomExtensions hext) hcont hres hhol hext

/-- **A thin uncountable infinitary class on all countable carriers, from the terminal
classification and the coatom extension property with apex at every countable block stage, with
forcing donors derived**: the conclusion of
`vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions`,
conditional on the five hypotheses of
`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'`,
each still to be proved except `hext`, now compiled.  Forcing donors at every countable block
index are derived from `hext`
at the next block stage (`forcingDonors_of_forall_hasApexCoatomExtensions`); the other
statements are derived as for the six-hypothesis form. -/
theorem vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock)
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧ ¬ φ.PerfectSetDichotomyAllCountable ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) :=
  vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions hrec
    (forcingDonors_of_forall_hasApexCoatomExtensions hext) hcont hres hhol hext

/-- **The thin `ℵ₁` spectrum of the density sentence from the terminal classification**: the
conclusion of
`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'`,
conditional on exactly the following four hypotheses, each still to be proved:
* finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3);
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction, Layer 4);
* exact residual receiving (`hres`; (R2) of the table of Layer 3);
* exact hollow-growth receiving for cover-hollowness at a block stage (`hhol`; (R3) of the table
  of Layer 3).
The coatom extension property with apex at every countable block stage is not assumed: it is
`StageType.hasApexCoatomExtensions_blockStage`, compiled in this repository (theorem named).  The
other statements are derived as in the five-hypothesis form. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_terminalClassification''
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'
    hrec hcont hres hhol fun η _ ↦ StageType.hasApexCoatomExtensions_blockStage η

/-- **A thin uncountable infinitary class on all countable carriers, from the terminal
classification**: the conclusion of
`vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'`,
conditional on exactly the four hypotheses of
`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification''` ((R1), the continuation
criterion, (R2), (R3)), each still to be proved.  The coatom extension property with apex at every
countable block stage is `StageType.hasApexCoatomExtensions_blockStage`, compiled in this
repository (theorem named). -/
theorem vaughtCounterexample_allCarriers_of_terminalClassification''
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsCoverHollowAtBlock) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧ ¬ φ.PerfectSetDichotomyAllCountable ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) :=
  vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'
    hrec hcont hres hhol fun η _ ↦ StageType.hasApexCoatomExtensions_blockStage η

end VaughtConjecture.MainTheorem
