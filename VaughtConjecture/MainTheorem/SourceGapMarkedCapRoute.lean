/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCarrierAcquisition
import VaughtConjecture.Continuation.SourceGapContextRelabel
import VaughtConjecture.MainTheorem.DeterminationRoute

/-!
# The receiving route from three finite coatom statements

Roadmap, Layer 6 ("Status: the hypotheses of the main theorem"), for the receiving route
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_receivingModels'`); semantic contract,
items 5, 8 and 12.

**The main theorem from three finite statements**
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`).
The thin `ℵ₁` spectrum of the density sentence follows from exactly three finite statements about
stage types, each open.  The coatom forms are stronger than the full forms
(`Realization.CutoffDetermination`, `Realization.HollowCutoffDetermination`,
`StageType.HasCutoffStableRecoverySchemes`): they imply them, and no converse is claimed.  The
(R2) coatom form quantifies over every coface `tb` of the coatom face, also of top grade above
`K`; the form restricted to `tb` of top grade at most `K`
(`Realization.BoundedCoatomCutoffDetermination`) gives cutoff determination for every predicate
whose contexts of grade `K` have top grade at most `K`, whose roots are never onto, and which is
invariant under relabelling the points of the context with the root relabelled along, through the
truncation of the pinned extension above `K`
(`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination`, in
`VaughtConjecture.MainTheorem.BoundedCoatomDetermination`); the three premises are compiled for the
source-gap context (`Realization.BoundedCoatomCutoffDetermination.cutoffDetermination_sourceGap`).
* (R4): cutoff completions at the first coatom for the graded cap calibration at every `ξ < ω₁`
  (`StageType.HasCutoffFirstCoatomCompletions`);
* (R2): coatom cutoff determination for the source-gap context
  (`Realization.CoatomCutoffDetermination`, `StageType.IsSourceGapContext`);
* (R3): hollow coatom cutoff determination for the marked-cap context
  (`Realization.HollowCoatomCutoffDetermination`, `StageType.IsMarkedCapContext`).
Everything else is compiled in this repository (theorem named):
* the acquisitions: `Realization.residualAcquisition_isSourceGapContext` and
  `Realization.hollowAcquisition_isMarkedCapContext`, and for (R4)
  `Realization.IsModel.acquiresCalibratedContexts_gradedCap`;
* the roots of the contexts are not onto: `StageType.not_isSourceGapContext_of_surjective` and
  `StageType.IsMarkedCapContext.not_surjective`;
* the contexts are invariant under relabelling: `StageType.IsSourceGapContext.reindex` and
  `StageType.IsMarkedCapContext.reindex`;
* the coatom extension property at every stage that is zero or a limit:
  `StageType.hasCoatomExtensions`.

**Not claimed.**  None of the three finite statements is proved, so the spectrum is not proved
here.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open FirstOrder Language baseLanguage Realization StageType
open Ordinal hiding univ

/-- **The thin `ℵ₁` spectrum from three finite coatom statements**: the density sentence has exactly
`ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise nonisomorphic ones, conditional
on exactly three finite statements about stage types, none proved:
* (R4): cutoff completions at the first coatom for the graded cap calibration at every `ξ < ω₁`
  (`h4`);
* (R2): coatom cutoff determination for the source-gap context (`h2`);
* (R3): hollow coatom cutoff determination for the marked-cap context (`h3`).
The acquisitions, the side conditions on the contexts and the coatom extension property are
compiled. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletions.{0} ξ (GradedCapCalibration.{0} ξ))
    (h2 : CoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContext K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_markedCap h4
    residualAcquisition_isSourceGapContext h2
    (fun _ _ _ _ _ _ hs hh ↦ not_isSourceGapContext_of_surjective hh hs)
    (fun _ _ _ _ _ _ σ hs ↦ hs.reindex σ) hollowAcquisition_isMarkedCapContext h3

/-- **The thin `ℵ₁` spectrum from three finite coatom statements, with the calibration margin**:
`densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap` with (R4)
asked only at the inputs of the margin calibration (`StageType.GradedCapMarginCalibration`: an
offset `R < N` above `γ` and a marker in the block of `λ_ξ`).  This (R4) hypothesis is implied
by the one of the graded cap form
(`StageType.HasCutoffFirstCoatomCompletions.gradedCapMargin`), and no converse is claimed, so this
theorem implies the graded cap form.  The acquisition of the margin calibration is
compiled (`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap_margin
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletions.{0} ξ (GradedCapMarginCalibration.{0} ξ))
    (h2 : CoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContext K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_markedCap_margin h4
    residualAcquisition_isSourceGapContext h2
    (fun _ _ _ _ _ _ hs hh ↦ not_isSourceGapContext_of_surjective hh hs)
    (fun _ _ _ _ _ _ σ hs ↦ hs.reindex σ) hollowAcquisition_isMarkedCapContext h3

end VaughtConjecture.MainTheorem
