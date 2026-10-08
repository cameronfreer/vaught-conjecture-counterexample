/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecovery
import VaughtConjecture.Realization.GrowthCarrier

/-!
# (R4) as the stable evaluation of a growth carrier

Roadmap, Layer 3 ((R4), the evaluation by stable labels).  The growth engine
(`GrowthCarrier.exists_recovered`, in `VaughtConjecture.Realization.GrowthCarrier`) is evaluated by
the **stable labels** of a model `R` at `λ_ξ`.  The carrier is a legal scheme realized in `R`
itself, at `λ_ξ`; its recovery quantifies over every lawful section of its rows, and the stable
section of the realized tuple is one of them.  The recovered relation is the **capped relation**
of a donor `D` at `γ` (`StageType.CappedRelation`): `Q d = D d` where `D d` is not the formal top,
and `γ < Q d` where it is.  This is the conclusion of (R4) at `(x, D, γ)`; modelhood of the stable
candidate is not used, and it is only afterwards that the cap-to-model theorem gives it (the main
theorem of `VaughtConjecture.MainTheorem.ReceivingRoute`).

The encoded template, the admitted state, and the realized carrier are three objects here: the
carrier and its display (`GrowthCarrier`, `GrowthCarrier.displayType`) are a scheme and a lawful
section at `λ_ξ` used only for legality and realization; the admitted state is the stable section
of the context (`Realization.stableSection`), which differs from the display at the cells
labelled the formal top; the realized carrier is the occurrence given by generalized saturation.

## Main definitions

* `Realization.stableLabelling`: the stable sections of a stably lawful realization, exactly
  consistent and covering, as an evaluator of actual occurrences.  No modelhood of the stable
  candidate is used.
* `StageType.CappedRelation D γ`: the relation of (R4) at a donor `D` and an ordinal `γ`.
* `StageType.HasStableGrowthCarriers ξ C`, a **finite** statement about stage types (open): every
  legal stage type `T⁺` at `λ_{ξ+1}` satisfying the calibration `C` for `f`, `D` and `γ` has a
  growth carrier, with a coface of `T⁺↓λ_ξ` on it, recovering the capped relation from the labels
  of `T⁺`.

## Main statements

* `Realization.stablyReceivesAt_of_growthCarrier`, **the stable evaluation**: (R4) at `(x, D, γ)`
  from a growth carrier over an occurrence of `R` containing `x`, recovering the capped relation
  from the stable section of that occurrence.
* `GrowthCarrier.isStableRecoveryScheme`: a growth carrier recovering the capped relation is a
  stable recovery scheme (`StageType.IsStableRecoveryScheme`), since every stage type at
  `λ_{ξ+1}` on the carrier is a lawful section of its rows; so
  `StageType.HasStableGrowthCarriers.hasStableRecoverySchemes`.
* `StableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin`: (R4) from stable growth
  carriers for the margin calibration (`StageType.GradedCapMarginCalibration`: a cap of grade `N`
  above the root arity, a marker offset `R < N` with `γ < λ_ξ + R`, and reference cells for the
  blocks of the proper labels of `D`), whose acquisition is compiled
  (`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`).  Its receiving form, the
  first hypothesis of the three-hypothesis main theorem, is in
  `VaughtConjecture.MainTheorem.GrowthRoute`.

## References

The stable labels are those of the continuation of a model at a limit stage, [Kni26, §4.3];
generalized saturation is [Kni26, Definition 3.2.1, clause 4(a)i].
-/

universe u v w

namespace VaughtConjecture

open Finset Ordinal Label StageType

/-! ### The capped relation -/

namespace StageType

variable {α : Ordinal.{u}} {k : ℕ}

/-- The **capped relation** of a donor `D` at `γ`: at a cell where `D` is not the formal top, the
label is that of `D`; at a cell where `D` is the formal top, the label exceeds `γ`. -/
def CappedRelation (D : StageType.{u} α (k + 1)) (γ : Ordinal.{u}) :
    Fin D.card → Label.{u} → Prop :=
  fun j ℓ ↦ (D.label j ≠ ⊤ → ℓ = D.label j) ∧ (D.label j = ⊤ → (γ : Label.{u}) < ℓ)

end StageType

/-! ### The stable labels as an evaluator -/

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **The stable labels as an evaluator**: for a stably lawful realization that is exactly
consistent and covering, the stable sections are lawful (stable lawfulness) and compatible with
restriction (`stableOffset_comap`).  Modelhood of the stable candidate is not used. -/
noncomputable def stableLabelling (hR : R.IsConsistent) (hc : R.IsCovering)
    (hlaw : R.IsStablyLawful) : R.OccurrenceLabelling where
  label u t := R.stableSection u t
  isLawful _ u t h := hlaw u t h
  label_comap _ _ w q f hf i h := by
    by_cases ht : q.label (q.cellMap f i) = ⊤
    · rw [stableSection_of_eq_top (t := q.comap f hf) (d := i) ht, stableSection_of_eq_top ht]
      exact congrArg (Label.ofOffset _) (stableOffset_comap hR hc h f hf i)
    · rw [stableSection_of_ne_top (t := q.comap f hf) (d := i) ht, stableSection_of_ne_top ht]
      rfl

@[simp] theorem stableLabelling_label (hR : R.IsConsistent) (hc : R.IsCovering)
    (hlaw : R.IsStablyLawful) {n : ℕ} (u : Fin n ↪ M) (t : StageType.{u} (blockStage ξ) n) :
    (stableLabelling hR hc hlaw).label u t = R.stableSection u t :=
  rfl

/-- **The stable evaluation of a growth carrier**: in a model `R` at `λ_ξ`, let `w` be an
occurrence of `R` containing the tuple of `x` along `f`, and let a growth carrier over the type of
`w`, with donor scheme that of `D` along `f`, have a nonempty saturation instance over `w` and
recover the capped relation of `D` at `γ` from the stable section of `w`.  Then (R4) holds at
`(x, D, γ)`.  The carrier is realized in `R`; the stable labels are read on the realized tuple. -/
theorem stablyReceivesAt_of_growthCarrier (hR : R.IsModel)
    {x : (R.stableCandidate hR.isStablyLawful).Occurrence}
    {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)} {γ : Ordinal.{u}} (w : R.Occurrence)
    {f : Fin x.arity ↪ Fin w.arity} (hf : f.trans w.tuple = x.tuple)
    (G : GrowthCarrier w.type.toScheme D.toScheme f)
    (hsat : (w.type.cofaces ∩ saturationFamily G.scheme).Nonempty)
    (hrec : G.Recovers (R.stableSection w.tuple w.type) (CappedRelation D γ)) :
    R.StablyReceivesAt hR.isStablyLawful x D γ := by
  obtain ⟨u, hu, -, s, hs, hsD, hl⟩ := G.exists_recovered hR
    (stableLabelling hR.isConsistent hR.isCovering hR.isStablyLawful) w hsat hrec
  exact ⟨u, hu.trans hf, R.stableType hR.isStablyLawful u s hs, stableCandidate_eval_of_eval hs,
    hsD, hl⟩

end Realization

/-! ### Stable growth carriers are stable recovery schemes -/

namespace GrowthCarrier

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- **A growth carrier recovering the capped relation is a stable recovery scheme**: every stage
type at `λ_{ξ+1}` on the carrier with face `T⁺` along the first points is a lawful section of the
carrier's rows agreeing with `T⁺` on the context face, so its face along `f` followed by the new
point satisfies the capped relation. -/
theorem isStableRecoveryScheme {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (G : GrowthCarrier Tp.toScheme D.toScheme f)
    (hsat : ((Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces ∩
      saturationFamily G.scheme).Nonempty)
    (hrec : G.Recovers Tp.label (CappedRelation D γ)) :
    Tp.IsStableRecoveryScheme f D γ G.scheme := by
  obtain ⟨q, hq, hqE⟩ := hsat
  refine ⟨⟨q, hq, hqE⟩, fun Q' hQ' hface ↦ ?_⟩
  obtain ⟨S, lab, hwf, hcod, hlaw, hst⟩ := Q'
  change S = G.scheme at hQ'
  subst hQ'
  set Q' : StageType.{u} (blockStage (ξ + 1)) (m + 1) := ⟨G.scheme, lab, hwf, hcod, hlaw, hst⟩
  have hc : univ.map Fin.castSuccEmb ∈ Q'.toCellScheme.faces := G.context_mem
  have hctx : Q'.comap Fin.castSuccEmb hc = Tp := by
    rw [restrictFace_of_mem Q' _ hc] at hface
    exact Option.some_injective _ hface
  refine ⟨Q'.comap (extendByLast f) G.donor_mem, restrictFace_of_mem Q' _ G.donor_mem,
    G.comap_donor, fun i j hij ↦ hrec lab hlaw (fun i' j' hij' ↦ ?_) i j hij⟩
  exact StageType.label_congr hctx hij'

end GrowthCarrier

namespace StageType

variable {ξ : Ordinal.{u}}

variable (ξ) in
/-- **Stable growth carriers** for a calibration `C`, a finite statement about stage types (no
realization), open: every legal stage type `T⁺` at `λ_{ξ+1}` with `C T⁺ f D γ`, for a coface `D`
of its face along `f` (`0 < k`) and `γ < λ_{ξ+1}`, has a growth carrier over its scheme with donor
scheme that of `D` along `f`, a coface of `T⁺↓λ_ξ` on it, and recovery of the capped relation of
`D` at `γ` from the labels of `T⁺`.  The recovery quantifies over every lawful section of the
carrier's rows, with no stage bound. -/
def HasStableGrowthCarriers
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      C Tp f D γ → ∃ G : GrowthCarrier Tp.toScheme D.toScheme f,
        ((Tp.reduce (isSuccPrelimit_blockStage ξ)).cofaces ∩
          saturationFamily G.scheme).Nonempty ∧ G.Recovers Tp.label (CappedRelation D γ)

/-- **Stable growth carriers give stable recovery schemes** (`GrowthCarrier.isStableRecoveryScheme`)
for the same calibration. -/
theorem HasStableGrowthCarriers.hasStableRecoverySchemes
    {C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}
    (h : HasStableGrowthCarriers ξ C) : HasStableRecoverySchemes ξ C :=
  fun _ _ Tp f P hT hk hP D hD γ hγ hC ↦
    let ⟨G, hsat, hrec⟩ := h Tp f P hT hk hP D hD γ hγ hC
    ⟨G.scheme, G.isStableRecoveryScheme hsat hrec⟩

end StageType

/-- **(R4) from stable growth carriers for the margin calibration**: stable growth carriers for
`StageType.GradedCapMarginCalibration` at every `ξ < ω₁`, a finite statement about stage types
(open), give (R4); the acquisition of the calibration is compiled
(`Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin`). -/
theorem StableCappedReceiving.of_hasStableGrowthCarriers_gradedCapMargin
    (h : ∀ ξ < ω₁,
      StageType.HasStableGrowthCarriers.{0} ξ (StageType.GradedCapMarginCalibration.{0} ξ)) :
    StableCappedReceiving.{w} :=
  StableCappedReceiving.of_stableRecoveryContexts ⟨fun ξ hξ ↦ ⟨_,
    (h ξ hξ).hasStableRecoverySchemes, fun _ _ hR hnh hgrow ↦
      Realization.IsModel.acquiresCalibratedContexts_gradedCapMargin hR hnh hgrow⟩⟩

end VaughtConjecture
