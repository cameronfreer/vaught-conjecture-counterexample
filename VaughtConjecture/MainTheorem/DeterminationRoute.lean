/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CutoffStableRecovery
import VaughtConjecture.MainTheorem.CoatomDetermination
import VaughtConjecture.MainTheorem.ReceivingRoute
import VaughtConjecture.Stage.MarkedCap

/-!
# The receiving route from three finite statements about stage types

Roadmap, Layer 6 ("Status: the hypotheses of the main theorem"), for the receiving route
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_receivingModels'`); semantic contract,
items 5, 8 and 12.

The receiving route has three hypotheses: (R4), (R2) and (R3) for receiving models.  Each is
reduced here, by compiled implications, to an acquisition statement about models and a finite
statement about stage types of the shape "for every input, one carrier, and then every labelling in
a class".  Each item below is compiled in this repository (theorem named), unless marked
otherwise.

**The determination form**
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_determinations`).
The thin `ℵ₁` spectrum of the density sentence follows from:
* (R4): cutoff stable recovery for the graded cap calibration at every `ξ < ω₁`
  (`StageType.HasCutoffStableRecoverySchemes`, open; its acquisition is compiled,
  `Realization.IsModel.acquiresCalibratedContexts_gradedCap`);
* (R2): for a predicate `P₂` on contexts, residual acquisition (`Realization.ResidualAcquisition`)
  and cutoff determination (`Realization.CutoffDetermination`, open);
* (R3): for a predicate `P₃` on contexts, hollow acquisition at cover-hollowness at a block stage
  (`Realization.HollowAcquisition`) and hollow cutoff determination
  (`Realization.HollowCutoffDetermination`, open).
The predicates are parameters.  For (R2) the intended predicate is the source-gap context and for
(R3) the marked-cap context (`StageType.IsMarkedCapContext`, defined in this repository); their
acquisitions are not on this branch.

**The coatom form**
(`MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations`).
The same with the three finite statements in their coatom forms
(`StageType.HasCutoffCoatomCompletions`, `Realization.CoatomCutoffDetermination`,
`Realization.HollowCoatomCutoffDetermination`, all open), in which the donor arrives through an
arbitrary coface of a closed coatom of the context and the carrier completes the coatom pair.
For (R2) and (R3) the reduction asks that the roots of the contexts are never onto and that the
predicate is invariant under relabelling the points of the context; for the marked-cap context the
first is compiled (`StageType.IsMarkedCapContext.not_surjective`), and the second is not.

**Not claimed.**  None of the finite statements is proved for the intended inputs, so the spectrum
is not proved here.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Ordinal hiding univ

/-- **The root of a marked-cap context is not onto**: its top cap has grade above `n + 1`, at most
the number `k` of points of the context, so `n < k`. -/
theorem StageType.IsMarkedCapContext.not_surjective {α : Ordinal.{u}} {n k : ℕ}
    {t' : StageType.{u} α k} {h : Fin n ↪ Fin k} (ht : t'.IsMarkedCapContext h) :
    ¬ Function.Surjective h := by
  obtain ⟨c, -, -, -, hn, -⟩ := ht
  intro hs
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_surjective h hs
  have := t'.grade_le c
  omega

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType

/-- **The thin `ℵ₁` spectrum from the determination statements**: the density sentence has exactly
`ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise nonisomorphic ones, conditional
on the following hypotheses, for predicates `P₂` and `P₃` on contexts:
* (R4): cutoff stable recovery for the graded cap calibration at every `ξ < ω₁` (`h4`);
* (R2): residual acquisition for `P₂` (`hacq₂`) and cutoff determination for `P₂` (`h2`);
* (R3): hollow acquisition at cover-hollowness at a block stage for `P₃` (`hacq₃`) and hollow
  cutoff determination for `P₃` (`h3`).
No hypothesis is proved here.  Through
`Expansion.ReceivingStableCappedReceiving.of_hasCutoffStableRecoverySchemes_gradedCap`,
`Realization.receivingResidualReceiving_of_cutoffDetermination` and
`Realization.receivingHollowReceiving_of_cutoffDetermination`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_determinations
    {P₂ : ∀ {α : Ordinal.{0}} {n k : ℕ}, ℕ → StageType.{0} α k → (Fin n ↪ Fin k) → Prop}
    {P₃ : ∀ {α : Ordinal.{0}} {n k : ℕ}, StageType.{0} α k → (Fin n ↪ Fin k) → Prop}
    (h4 : ∀ ξ < ω₁, HasCutoffStableRecoverySchemes.{0} ξ (GradedCapCalibration.{0} ξ))
    (hacq₂ : ResidualAcquisition.{0, 0} P₂) (h2 : CutoffDetermination.{0} P₂)
    (hacq₃ : HollowAcquisition.{0, 0} IsCoverHollowAtBlock P₃)
    (h3 : HollowCutoffDetermination.{0} P₃) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels'
    (.of_hasCutoffStableRecoverySchemes_gradedCap h4)
    (receivingResidualReceiving_of_cutoffDetermination hacq₂ h2)
    (receivingHollowReceiving_of_cutoffDetermination hacq₃ h3)

/-- **The thin `ℵ₁` spectrum from the determination statements, with the marked-cap context**:
`densitySentence_hasThinAlephOneSpectrum_of_determinations` with `P₃` the marked-cap context
(`StageType.IsMarkedCapContext`).  Its hollow acquisition (`hacq₃`) is a hypothesis here. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_determinations_markedCap
    {P₂ : ∀ {α : Ordinal.{0}} {n k : ℕ}, ℕ → StageType.{0} α k → (Fin n ↪ Fin k) → Prop}
    (h4 : ∀ ξ < ω₁, HasCutoffStableRecoverySchemes.{0} ξ (GradedCapCalibration.{0} ξ))
    (hacq₂ : ResidualAcquisition.{0, 0} P₂) (h2 : CutoffDetermination.{0} P₂)
    (hacq₃ : HollowAcquisition.{0, 0} IsCoverHollowAtBlock fun t' h ↦ t'.IsMarkedCapContext h)
    (h3 : HollowCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_determinations h4 hacq₂ h2 hacq₃ h3

/-- **The thin `ℵ₁` spectrum from the coatom forms**: the conclusion of
`densitySentence_hasThinAlephOneSpectrum_of_determinations` with the three finite statements in
their coatom forms, conditional on:
* (R4): cutoff coatom completions for the graded cap calibration at every `ξ < ω₁` (`h4`);
* (R2): residual acquisition for `P₂` (`hacq₂`), coatom cutoff determination for `P₂` (`h2`), roots
  of `P₂`-contexts never onto (`hns₂`) and `P₂` invariant under relabelling (`hinv₂`);
* (R3): hollow acquisition for `P₃` (`hacq₃`), hollow coatom cutoff determination for `P₃` (`h3`),
  roots never onto (`hns₃`) and invariance under relabelling (`hinv₃`).
The coatom extension property used by the reductions is compiled. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations
    {P₂ : ∀ {α : Ordinal.{0}} {n k : ℕ}, ℕ → StageType.{0} α k → (Fin n ↪ Fin k) → Prop}
    {P₃ : ∀ {α : Ordinal.{0}} {n k : ℕ}, StageType.{0} α k → (Fin n ↪ Fin k) → Prop}
    (h4 : ∀ ξ < ω₁, HasCutoffCoatomCompletions.{0} ξ (GradedCapCalibration.{0} ξ))
    (hacq₂ : ResidualAcquisition.{0, 0} P₂) (h2 : CoatomCutoffDetermination.{0} P₂)
    (hns₂ : ∀ ⦃α : Ordinal.{0}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{0} α k) (h : Fin n ↪ Fin k),
      P₂ K t' h → ¬ Function.Surjective h)
    (hinv₂ : ∀ ⦃α : Ordinal.{0}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{0} α k) (h : Fin n ↪ Fin k)
      (σ : Equiv.Perm (Fin k)), P₂ K t' h → P₂ K (t'.reindex σ) (h.trans σ.symm.toEmbedding))
    (hacq₃ : HollowAcquisition.{0, 0} IsCoverHollowAtBlock P₃)
    (h3 : HollowCoatomCutoffDetermination.{0} P₃)
    (hns₃ : ∀ ⦃α : Ordinal.{0}⦄ ⦃n k : ℕ⦄ (t' : StageType.{0} α k) (h : Fin n ↪ Fin k),
      P₃ t' h → ¬ Function.Surjective h)
    (hinv₃ : ∀ ⦃α : Ordinal.{0}⦄ ⦃n k : ℕ⦄ (t' : StageType.{0} α k) (h : Fin n ↪ Fin k)
      (σ : Equiv.Perm (Fin k)), P₃ t' h → P₃ (t'.reindex σ) (h.trans σ.symm.toEmbedding)) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_determinations
    (fun ξ hξ ↦ (h4 ξ hξ).hasCutoffStableRecoverySchemes fun _ _ _ _ _ _ hC ↦ hC.lt)
    hacq₂ (h2.cutoffDetermination hns₂ hinv₂) hacq₃ (h3.hollowCutoffDetermination hns₃ hinv₃)

end MainTheorem

end VaughtConjecture
