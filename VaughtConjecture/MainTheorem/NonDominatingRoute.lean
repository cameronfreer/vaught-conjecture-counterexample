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

* **The acquisition from the profile tower**
  (`Realization.IsModel.acquiresCalibratedContexts_gradedCapMarginND_of_tower`): conditional on
  layer separation (`TowerLayerSeparating`) and cross-layer non-domination (`TowerCrossLayer`),
  through `completionNonDominating_of_tower`.
* **(R4) for receiving models** (`ReceivingStableCappedReceiving.of_firstCoatomEx_nd`): from
  first-coatom completions with a chosen coface for the calibration with a non-dominating cap at
  every `ξ < ω₁`, conditional on the same two named hypotheses.
* **The hypothesis of the endpoint gives this one**
  (`StageType.HasCutoffFirstCoatomCompletions.ex_nd`): first-coatom completions for the graded cap
  calibration (the `h4` of
  `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`)
  give first-coatom completions with a chosen coface for the calibration with a non-dominating cap,
  whose inputs are among those of the graded cap calibration.
* **The thin `ℵ₁` spectrum through this calibration**
  (`densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap_nd`,
  in `MainTheorem`): from the (R4) hypothesis in this form, (R2) and (R3) as in the endpoint,
  conditional on `TowerLayerSeparating` and `TowerCrossLayer`.  The endpoint's own `h4` implies
  the (R4) hypothesis here (`StageType.HasCutoffFirstCoatomCompletions.ex_nd`); no converse is
  claimed.

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

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Acquisition of the calibration with a non-dominating cap from the profile tower**,
conditional on layer separation and cross-layer non-domination. -/
theorem IsModel.acquiresCalibratedContexts_gradedCapMarginND_of_tower (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) (hsep : TowerLayerSeparating.{u})
    (hcross : TowerCrossLayer.{u}) :
    AcquiresCalibratedContexts ξ (StageType.GradedCapMarginCalibrationND ξ) R
      hR.isStablyLawful :=
  hR.acquiresCalibratedContexts_gradedCapMarginND hnh hgrow
    (completionNonDominating_of_tower hsep hcross)

end Realization

namespace Expansion

open Realization

/-- **(R4) for receiving models from first-coatom completions with a chosen coface for the
calibration with a non-dominating cap**, conditional on layer separation and cross-layer
non-domination. -/
theorem ReceivingStableCappedReceiving.of_firstCoatomEx_nd (hsep : TowerLayerSeparating.{0})
    (hcross : TowerCrossLayer.{0})
    (h : ∀ ξ < ω₁, StageType.HasCutoffFirstCoatomCompletionsEx.{0} ξ
      (StageType.GradedCapMarginCalibrationND.{0} ξ)) :
    ReceivingStableCappedReceiving.{w} :=
  .of_hasCutoffStableRecoverySchemes (fun ξ ↦ StageType.GradedCapMarginCalibrationND ξ)
    (fun ξ hξ ↦ (h ξ hξ).hasCutoffStableRecoverySchemes_nd)
    fun _ _ _ _ hR _ hnh hgrow ↦
      hR.acquiresCalibratedContexts_gradedCapMarginND_of_tower hnh hgrow hsep hcross

end Expansion

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType

/-- **The thin `ℵ₁` spectrum through the calibration with a non-dominating cap**: from first-coatom
completions with a chosen coface for that calibration at every `ξ < ω₁` (`h4`, implied by the
`h4` of the endpoint through `StageType.HasCutoffFirstCoatomCompletions.ex_nd`), (R2) and (R3) as
in `densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`,
conditional on layer separation (`TowerLayerSeparating`) and cross-layer non-domination
(`TowerCrossLayer`). -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap_nd
    (hsep : TowerLayerSeparating.{0}) (hcross : TowerCrossLayer.{0})
    (h4 : ∀ ξ < ω₁, HasCutoffFirstCoatomCompletionsEx.{0} ξ (GradedCapMarginCalibrationND.{0} ξ))
    (h2 : CoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContext K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels'
    (.of_firstCoatomEx_nd hsep hcross h4)
    (receivingResidualReceiving_of_cutoffDetermination residualAcquisition_isSourceGapContext
      (h2.cutoffDetermination (fun _ _ _ _ _ _ hs hh ↦ not_isSourceGapContext_of_surjective hh hs)
        fun _ _ _ _ _ _ σ hs ↦ hs.reindex σ))
    (receivingHollowReceiving_of_cutoffDetermination hollowAcquisition_isMarkedCapContext
      (h3.hollowCutoffDetermination (fun _ _ _ _ _ ht ↦ ht.not_surjective)
        fun _ _ _ _ _ σ ht ↦ ht.reindex σ))

end MainTheorem

end VaughtConjecture
