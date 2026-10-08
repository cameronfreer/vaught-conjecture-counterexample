/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.NonDominatingRoute

/-!
# The receiving route through the calibration with a cap non-dominating at its grade

Roadmap, Layer 6, for the receiving route; the (R4) hypothesis at the calibration with a cap that
dominates no live cell of its own grade (`StageType.GradedCapMarginCalibrationNDSame`), with a
chosen intermediate coface.

The clause at the grade of the cap (`Scheme.CapNonDominatingSameAt`) is the clause
`Scheme.CapNonDominatingAt` restricted to the live cells `a` of the grade of the cap; the
calibration with a non-dominating cap (`StageType.GradedCapMarginCalibrationND`) is the stronger
form, conditional on `CompletionNonDominating`.  Compiled in this repository (theorem named):

* **The acquisition at the grade of the cap**
  (`Realization.IsModel.acquiresCalibratedContexts_gradedCapMarginNDSame`): for a model at `λ_ξ`
  that is not cover-hollow and has top-grade supremum `⊤`, with no further hypothesis: the
  completion of the seed of the extended type with itself is the bot-keeping completion of the
  profile tower, which satisfies the clause at the grade of the cap
  (`exists_botKeeping_capNonDominating_sameLayer`).
* **(R4) for receiving models** (`ReceivingStableCappedReceiving.of_firstCoatomEx_ndSame`): from
  first-coatom completions with a chosen coface for this calibration at every `ξ < ω₁`.
* **The hypothesis of the endpoint gives this one**
  (`StageType.HasCutoffFirstCoatomCompletions.ex_ndSame`): first-coatom completions for the graded
  cap calibration give first-coatom completions with a chosen coface for this calibration.
* **The thin `ℵ₁` spectrum through this calibration**
  (`densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap_ndSame`,
  in `MainTheorem`): from the (R4) hypothesis in this form, (R2) and (R3) as in the endpoint.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset
open Ordinal hiding univ

namespace Scheme

variable {n : ℕ}

/-- **The cell `c` dominates no live cell of its grade off the point `x`**: for every cell `a`
whose scope avoids `x`, of the grade of `c`, reading itself other than `⊥`, and every cell `G` of
full scope and the grade of `a`, some cell of the graded index of `G` reads `c` in a block strictly
below its reading of `a`. -/
def CapNonDominatingSameAt (S : Scheme.{u} n) (x : Fin n) (c : Fin S.card) : Prop :=
  ∀ a G : Fin S.card, x ∉ S.toCellScheme.scope a → S.toCellScheme.scope G = univ →
    S.toCellScheme.grade a = S.toCellScheme.grade G →
    S.toCellScheme.grade a = S.toCellScheme.grade c → S.rowAt a a ≠ ⊥ →
      ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex G ∧
        Label.LowerBlock (S.rowAt u c) (S.rowAt u a)

/-- The clause at every grade from the cap gives the clause at the grade of the cap. -/
theorem CapNonDominatingAt.sameAt {S : Scheme.{u} n} {x : Fin n} {c : Fin S.card}
    (h : S.CapNonDominatingAt x c) : S.CapNonDominatingSameAt x c :=
  fun a G ha hG hag hac hlive ↦ h a G ha hG hag hac.ge hlive

end Scheme

namespace StageType

variable {ξ : Ordinal.{u}}

variable (ξ) in
/-- **The margin calibration with a cap non-dominating at its grade** at `(Tp, f, D, γ)`: the
margin calibration with a floor, a last point `x` off the root with `univ.erase x` a face, and the
clause at the grade of the cap (`Scheme.CapNonDominatingSameAt`) at `x` for every cell of full
scope and grade `3 ≤ g` with `g + 2 ≤ m`. -/
def GradedCapMarginCalibrationNDSame ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (f : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  GradedCapMarginCalibration' ξ Tp f D γ ∧
    ∃ x : Fin m, (x : ℕ) + 1 = m ∧ (∀ i, f i ≠ x) ∧ univ.erase x ∈ Tp.toCellScheme.faces ∧
      ∀ c : Fin Tp.card, Tp.toCellScheme.scope c = univ → 3 ≤ Tp.toCellScheme.grade c →
        Tp.toCellScheme.grade c + 2 ≤ m → Tp.toScheme.CapNonDominatingSameAt x c

/-- The calibration with a non-dominating cap gives the calibration at the grade of the cap. -/
theorem GradedCapMarginCalibrationND.ndSame ⦃m k : ℕ⦄
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibrationND ξ Tp f D γ) :
    GradedCapMarginCalibrationNDSame ξ Tp f D γ := by
  obtain ⟨hC, x, hx, hfx, hxf, hnd⟩ := h
  exact ⟨hC, x, hx, hfx, hxf, fun c hc h3 hcm ↦ (hnd c hc h3 hcm).sameAt⟩

/-- **The calibration at the grade of the cap is a graded cap calibration.** -/
theorem GradedCapMarginCalibrationNDSame.gradedCapCalibration ⦃m k : ℕ⦄
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibrationNDSame ξ Tp f D γ) : GradedCapCalibration ξ Tp f D γ :=
  h.1.gradedCapMarginCalibration.gradedCapCalibration

/-- **First-coatom completions for the graded cap calibration give first-coatom completions with a
chosen coface for the calibration at the grade of the cap.** -/
theorem HasCutoffFirstCoatomCompletions.ex_ndSame
    (h : HasCutoffFirstCoatomCompletions ξ (GradedCapCalibration ξ)) :
    HasCutoffFirstCoatomCompletionsEx ξ (GradedCapMarginCalibrationNDSame ξ) :=
  HasCutoffFirstCoatomCompletions.ex fun _ _ Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC ↦
    h Tp p tb f P hT hp htb hk hP D hD htbD γ hγ hC.gradedCapCalibration

/-- **Cutoff stable recovery for the calibration at the grade of the cap from first-coatom
completions with a chosen coface**: the root avoids the last point, whose complement is a face, so
the input is an input at the first coatom. -/
theorem HasCutoffFirstCoatomCompletionsEx.hasCutoffStableRecoverySchemes_ndSame
    (h : HasCutoffFirstCoatomCompletionsEx ξ (GradedCapMarginCalibrationNDSame ξ)) :
    HasCutoffStableRecoverySchemes ξ (GradedCapMarginCalibrationNDSame ξ) := by
  intro m k Tp f P hT hk hP D hD γ hγ hC
  obtain ⟨-, x, hx, hfx, hxf, -⟩ := id hC
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain rfl : x = Fin.last m' := Fin.ext (by simp; omega)
  obtain ⟨f', rfl⟩ := exists_trans_castSuccEmb f hfx
  have hmem : univ.map (Fin.castSuccEmb : Fin m' ↪ Fin (m' + 1)) ∈ Tp.toCellScheme.faces := by
    convert hxf using 1
    ext y
    induction y using Fin.lastCases with
    | last => simp
    | cast y => simp [Fin.castSucc_ne_last]
  have hTp : restrictFace Fin.castSuccEmb Tp = some (Tp.comap Fin.castSuccEmb hmem) :=
    restrictFace_of_mem Tp _ hmem
  have hpP : restrictFace f' (Tp.comap Fin.castSuccEmb hmem) = some P :=
    (restrictFace_trans Tp Fin.castSuccEmb f' hTp).trans hP
  obtain ⟨-, -, -, q, δ, -, hq⟩ := h Tp _ f' P hT hTp hk hpP D hD γ hγ hC
  exact ⟨q, δ, hq⟩

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Acquisition of the margin calibration with a cap non-dominating at its grade**, for a model
`R` at `λ_ξ` that is not cover-hollow and has top-grade supremum `⊤`: as
`Realization.IsModel.acquiresCalibratedContexts_gradedCapMarginND`, with the bot-keeping
completion of the profile tower (`exists_botKeeping_capNonDominating_sameLayer`) for the seed of
the extended type with itself. -/
theorem IsModel.acquiresCalibratedContexts_gradedCapMarginNDSame (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (StageType.GradedCapMarginCalibrationNDSame ξ) R
      hR.isStablyLawful := by
  intro x hx D hD γ hγ
  have hβ := isSuccLimit_blockStage ξ
  obtain ⟨w, f, hf, hC⟩ := hR.acquiresCalibratedContexts_gradedCapMargin' hnh hgrow x hx D hD γ hγ
  -- one point more, by high-arity dominance at `0`
  obtain ⟨u, hu, q₀, ⟨⟨hq₀l, hq₀f⟩, -⟩, he₀⟩ :=
    (hR.dominance w 0 hβ.bot_lt).inter_cofaces hR.isConsistent hR.isLegal
  set Z₁ : R.Occurrence := ⟨w.arity + 1, u, q₀, he₀⟩
  -- the bot-keeping completion of the profile tower of the seed of `q₀` with itself
  obtain ⟨F, -, hF⟩ :=
    exists_botKeeping_capNonDominating_sameLayer (Seed.ofCoatoms hq₀l hq₀l hq₀f hq₀f)
  set qs := F.completion hβ.isSuccPrelimit
  have hqs : qs ∈ q₀.cofaces :=
    ⟨F.isLegal_completion _, F.restrictFace_left_completion hβ.isSuccPrelimit⟩
  have hne : (Z₁.type.cofaces ∩ StageType.saturationFamily qs.toScheme).Nonempty := ⟨qs, hqs, rfl⟩
  obtain ⟨v, hv, q, ⟨⟨-, hqf⟩, hqS⟩, hev⟩ :=
    (hR.saturation Z₁ qs.toScheme hne).inter_cofaces hR.isConsistent hR.isLegal
  set V : R.Occurrence := ⟨w.arity + 2, v, q, hev⟩
  set g : Fin w.arity ↪ Fin (w.arity + 2) := Fin.castSuccEmb.trans Fin.castSuccEmb
  have hgv : g.trans v = w.tuple := by
    rw [Function.Embedding.trans_assoc, hv]
    exact hu
  -- the stable type of `V` has face the stable type of `w` along the first points
  have hface : StageType.restrictFace g
      (R.stableType hR.isStablyLawful v q hev) =
        some (R.stableType hR.isStablyLawful w.tuple w.type w.eval_tuple) := by
    rw [← isConsistent_stableCandidate hR.isConsistent hR.isCovering v _ g
      (stableCandidate_eval_of_eval hev), hgv]
    exact stableCandidate_eval_of_eval w.eval_tuple
  refine ⟨V, f.trans g, ?_, hC.of_restrictFace hface, Fin.last _, rfl, fun i ↦ ?_, ?_, ?_⟩
  · rw [Function.Embedding.trans_assoc, hgv, hf]
  · simp only [g, Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
    exact Fin.castSucc_ne_last _
  · -- the first points span a face: the face of `q` along the first points is the type of `Z₁`
    have h := ((StageType.restrictFace_eq_some_iff q Fin.castSuccEmb).mp hqf).1
    change univ.erase (Fin.last (w.arity + 1)) ∈ q.toCellScheme.faces
    convert h using 1
    exact (Coatom.univ_map_left (m := w.arity)).symm
  · -- the clause holds on the scheme of the completion
    have key : ∀ S : Scheme.{u} (w.arity + 2), S = qs.toScheme → ∀ c : Fin S.card,
        S.toCellScheme.scope c = univ → 3 ≤ S.toCellScheme.grade c →
        S.toCellScheme.grade c + 2 ≤ w.arity + 2 → S.CapNonDominatingSameAt (Fin.last _) c := by
      rintro S rfl c hc h3 hcm
      exact hF hβ.isSuccPrelimit c hc h3 (by change qs.toCellScheme.grade c ≤ w.arity; omega)
    exact key _ hqS

end Realization

namespace Expansion

open Realization

/-- **(R4) for receiving models from first-coatom completions with a chosen coface for the
calibration with a cap non-dominating at its grade.** -/
theorem ReceivingStableCappedReceiving.of_firstCoatomEx_ndSame
    (h : ∀ ξ < ω₁, StageType.HasCutoffFirstCoatomCompletionsEx.{0} ξ
      (StageType.GradedCapMarginCalibrationNDSame.{0} ξ)) :
    ReceivingStableCappedReceiving.{w} :=
  .of_hasCutoffStableRecoverySchemes (fun ξ ↦ StageType.GradedCapMarginCalibrationNDSame ξ)
    (fun ξ hξ ↦ (h ξ hξ).hasCutoffStableRecoverySchemes_ndSame)
    fun _ _ _ _ hR _ hnh hgrow ↦ hR.acquiresCalibratedContexts_gradedCapMarginNDSame hnh hgrow

end Expansion

namespace MainTheorem

open FirstOrder Language baseLanguage Realization StageType

/-- **The thin `ℵ₁` spectrum through the calibration with a cap non-dominating at its grade**:
from first-coatom completions with a chosen coface for that calibration at every `ξ < ω₁` (`h4`,
implied by the `h4` of the endpoint through `StageType.HasCutoffFirstCoatomCompletions.ex_ndSame`),
(R2) and (R3) as in
`densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap`. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_coatomDeterminations_sourceGap_markedCap_ndSame
    (h4 : ∀ ξ < ω₁,
      HasCutoffFirstCoatomCompletionsEx.{0} ξ (GradedCapMarginCalibrationNDSame.{0} ξ))
    (h2 : CoatomCutoffDetermination.{0} fun K t' h ↦ t'.IsSourceGapContext K h)
    (h3 : HollowCoatomCutoffDetermination.{0} fun t' h ↦ t'.IsMarkedCapContext h) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  densitySentence_hasThinAlephOneSpectrum_of_receivingModels'
    (.of_firstCoatomEx_ndSame h4)
    (receivingResidualReceiving_of_cutoffDetermination residualAcquisition_isSourceGapContext
      (h2.cutoffDetermination (fun _ _ _ _ _ _ hs hh ↦ not_isSourceGapContext_of_surjective hh hs)
        fun _ _ _ _ _ _ σ hs ↦ hs.reindex σ))
    (receivingHollowReceiving_of_cutoffDetermination hollowAcquisition_isMarkedCapContext
      (h3.hollowCutoffDetermination (fun _ _ _ _ _ ht ↦ ht.not_surjective)
        fun _ _ _ _ _ σ ht ↦ ht.reindex σ))

end MainTheorem

end VaughtConjecture
