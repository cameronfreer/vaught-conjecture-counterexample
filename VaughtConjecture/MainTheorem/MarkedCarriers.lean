/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCarrierAcquisition
import VaughtConjecture.Expansion.ReceivingHollowLosses
import VaughtConjecture.MainTheorem.Composition

/-!
# The main theorem with marked carriers in place of (R3)

Roadmap, Layer 6 ("Status: the hypotheses of the main theorem"); the five-hypothesis form of
`VaughtConjecture.MainTheorem.Composition` with (R3) replaced by marked carriers.

`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'`
takes five hypotheses: (R1), the continuation criterion, (R2), (R3) for cover-hollowness at a block
stage, and the coatom extension property with apex at every countable block stage.  (R3) follows
from marked carriers at every block stage (`StageType.HasMarkedCarriers`, a named hypothesis on
stage types, open; `Realization.hollowReceiving_of_hasMarkedCarriers`, compiled in this
repository (theorem named)), so the conclusion holds conditional on:

* finite-cut receiving of models (`hrec`; (R1));
* the continuation criterion (`hcont`; output 3 of higher-stage reconstruction);
* exact residual receiving (`hres`; (R2));
* marked carriers at every block stage (`hcar`; in place of (R3));
* the coatom extension property with apex at every countable block stage (`hext`).

Each is still to be proved.  No implication between marked carriers and the coatom extension
property is compiled.

`densitySentence_hasThinAlephOneSpectrum_of_hasTopMarkedCarriers` has the same hypotheses with
top-marked carriers (`StageType.HasTopMarkedCarriers`, open; the cutoff form, which prescribes only
the readings of the new tops) in place of marked carriers.  There (R3) is used for cover-hollow
models with finite-cut receiving (`Realization.IsCoverHollowWithReceivingAtBlock`), which (R1)
provides at the countable block stages of the count
(`Expansion.expansionDomain_loss_countable_of_receivingHollow`).

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion StageType
open scoped Ordinal

/-- **The thin `ℵ₁` spectrum of the density sentence with marked carriers in place of (R3)**:
the density sentence has exactly `ℵ₁` classes of models coded on `ℕ` and no perfect set of
pairwise nonisomorphic ones, conditional on (R1) (`hrec`), the continuation criterion (`hcont`),
(R2) (`hres`), marked carriers at every block stage (`hcar`), and the coatom extension property
with apex at every countable block stage (`hext`), each still to be proved.  (R3) for
cover-hollowness at a block stage is derived (`Realization.hollowReceiving_of_hasMarkedCarriers`).
-/
theorem densitySentence_hasThinAlephOneSpectrum_of_hasMarkedCarriers
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hcar : ∀ ξ : Ordinal.{0}, HasMarkedCarriers.{0} (blockStage ξ))
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'
    hrec hcont hres (Realization.hollowReceiving_of_hasMarkedCarriers hcar) hext

/-- **A thin uncountable infinitary class on all countable carriers, with marked carriers in place
of (R3)**: the conclusion of
`vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'`,
conditional on the five hypotheses of
`densitySentence_hasThinAlephOneSpectrum_of_hasMarkedCarriers`, each still to be proved. -/
theorem vaughtCounterexample_allCarriers_of_hasMarkedCarriers
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hcar : ∀ ξ : Ordinal.{0}, HasMarkedCarriers.{0} (blockStage ξ))
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧ ¬ φ.PerfectSetDichotomyAllCountable ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) :=
  vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'
    hrec hcont hres (Realization.hollowReceiving_of_hasMarkedCarriers hcar) hext

/-- **The thin `ℵ₁` spectrum of the density sentence with top-marked carriers in place of (R3)**:
the conclusion of `densitySentence_hasThinAlephOneSpectrum_of_hasMarkedCarriers`, conditional on
(R1) (`hrec`), the continuation criterion (`hcont`), (R2) (`hres`), top-marked carriers at every
block stage (`hcar`), and the coatom extension property with apex at every countable block stage
(`hext`), each still to be proved.  The hollow comparison uses (R3) for cover-hollow models with
finite-cut receiving, derived from `hcar`
(`Realization.hollowReceiving_withReceiving_of_hasTopMarkedCarriers`); `hrec` gives the hollow
models of the count finite-cut receiving
(`Expansion.expansionDomain_loss_countable_of_receivingHollow`).  Forcing donors are derived from
`hext` (`forcingDonors_of_forall_hasApexCoatomExtensions`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_hasTopMarkedCarriers
    (hrec : FiniteCutReceiving.{0}) (hcont : ContinuationCriterion.{0})
    (hres : Realization.ResidualReceiving.{0, 0})
    (hcar : ∀ ξ : Ordinal.{0}, HasTopMarkedCarriers.{0} (blockStage ξ))
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_hasApexCoatomExtensions hext
    (NextBlockUniqueness.of_forcingDonors hrec
      (forcingDonors_of_forall_hasApexCoatomExtensions hext)) hrec
    (expansionDomain_loss_countable_of_receivingHollow hrec hcont hres
      (Realization.hollowReceiving_withReceiving_of_hasTopMarkedCarriers hcar))

end VaughtConjecture.MainTheorem
