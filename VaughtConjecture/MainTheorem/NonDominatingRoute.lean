/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.NonDominatingAcquisition
import VaughtConjecture.MainTheorem.SourceGapMarkedCapRoute

/-!
# The receiving route through the calibration with a non-dominating cap

Roadmap, Layer 6, for the receiving route; the (R4) hypothesis at the calibration with a
non-dominating cap (`StageType.GradedCapMarginCalibrationND`), with a chosen intermediate coface.

Compiled in this repository (theorem named):

* **(R4) for receiving models** (`ReceivingStableCappedReceiving.of_firstCoatomEx_nd`): from
  first-coatom completions with a chosen coface for the calibration with a non-dominating cap at
  every `ξ < ω₁`, conditional on `CompletionNonDominating` (some completion of every seed whose
  caps dominate no live cell), through the acquisition
  `Realization.IsModel.acquiresCalibratedContexts_gradedCapMarginND`.  The completion of the
  profile tower does not give it: its same-layer part is proved (`towerLayerSeparating`), but
  cross-layer non-domination fails there (`not_towerCrossLayer`, at a seed on six points whose
  cells below the grade `4` are dead), and so does the cross separation that would give it
  (`not_towerCrossSeparating`).
* **The hypothesis of the endpoint gives this one**
  (`StageType.HasCutoffFirstCoatomCompletions.ex_nd`): first-coatom completions for the graded cap
  calibration (the `h4` of
  `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`)
  give first-coatom completions with a chosen coface for the calibration with a non-dominating cap,
  whose inputs are among those of the graded cap calibration.
* **The thin `ℵ₁` spectrum through this calibration**
  (`densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap_nd`,
  in `MainTheorem`): from the (R4) hypothesis in this form, (R2) and (R3) as in the endpoint,
  conditional on `CompletionNonDominating`.  The endpoint's own `h4` implies
  the (R4) hypothesis here (`StageType.HasCutoffFirstCoatomCompletions.ex_nd`); no converse is
  claimed.

The calibration with the clause restricted to the grade of the cap, whose acquisition needs no
hypothesis, and its route are in `VaughtConjecture.MainTheorem.SameLayerRoute`.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Ordinal hiding univ

namespace StageType

variable {ξ : Ordinal.{u}}

/-- **The calibration with a non-dominating cap is a graded cap calibration.** -/
theorem GradedCapMarginCalibrationND.gradedCapCalibration ⦃m k : ℕ⦄
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibrationND ξ Tp f D γ) : GradedCapCalibration ξ Tp f D γ :=
  h.1.gradedCapMarginCalibration.gradedCapCalibration

/-- **First-coatom completions for the graded cap calibration give first-coatom completions with a
chosen coface for the calibration with a non-dominating cap.** -/
theorem HasCutoffFirstCoatomCompletions.ex_nd
    (h : HasCutoffFirstCoatomCompletions ξ (GradedCapCalibration ξ)) :
    HasCutoffFirstCoatomCompletionsEx ξ (GradedCapMarginCalibrationND ξ) :=
  HasCutoffFirstCoatomCompletions.ex fun _ _ Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC ↦
    h Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC.gradedCapCalibration

end StageType

namespace Expansion

open Realization

/-- **(R4) for receiving models from first-coatom completions with a chosen coface for the
calibration with a non-dominating cap**, conditional on `CompletionNonDominating`. -/
theorem ReceivingStableCappedReceiving.of_firstCoatomEx_nd (hND : CompletionNonDominating.{0})
    (h : ∀ ξ < ω₁, StageType.HasCutoffFirstCoatomCompletionsEx.{0} ξ
      (StageType.GradedCapMarginCalibrationND.{0} ξ)) :
    ReceivingStableCappedReceiving.{w} :=
  .of_hasCutoffStableRecoverySchemes (fun ξ ↦ StageType.GradedCapMarginCalibrationND ξ)
    (fun ξ hξ ↦ (h ξ hξ).hasCutoffStableRecoverySchemes_nd)
    fun _ _ _ _ hR _ hnh hgrow ↦
      hR.acquiresCalibratedContexts_gradedCapMarginND hnh hgrow hND

end Expansion

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType

/-- **The thin `ℵ₁` spectrum through the calibration with a non-dominating cap**: from first-coatom
completions with a chosen coface for that calibration at every `ξ < ω₁` (`h4`, implied by the
`h4` of the endpoint through `StageType.HasCutoffFirstCoatomCompletions.ex_nd`), (R2) and (R3) as
in `densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`,
conditional on completions dominating no live cell (`CompletionNonDominating`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap_nd
    (hND : CompletionNonDominating.{0})
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletionsEx.{0} ξ (GradedCapMarginCalibrationND.{0} ξ))
    (h2 : CoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContext K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels'
    (.of_firstCoatomEx_nd hND h4)
    (receivingResidualReceiving_of_cutoffDetermination residualAcquisition_isSourceGapContext
      (h2.cutoffDetermination (fun _ _ _ _ _ _ hs hh ↦ not_isSourceGapContext_of_surjective hh hs)
        fun _ _ _ _ _ _ σ hs ↦ hs.reindex σ))
    (receivingHollowReceiving_of_cutoffDetermination hollowAcquisition_isMarkedCapContext
      (h3.hollowCutoffDetermination (fun _ _ _ _ _ ht ↦ ht.not_surjective)
        fun _ _ _ _ _ σ ht ↦ ht.reindex σ))

end MainTheorem

end VaughtConjecture
