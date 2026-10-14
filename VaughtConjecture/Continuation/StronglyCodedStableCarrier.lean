/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthStableCarrier
import VaughtConjecture.Continuation.StronglyCodedRecoveryTarget

/-!
# Strongly coded stable growth carriers

Roadmap, Layer 3 ((R4), the evaluation step) and Correspondence, item 1 (the strongly coded legal
stage types).  All results here are native constructions of this repository.

`StageType.HasStableGrowthCarriers ξ C` asks for a growth carrier recovering the capped relation,
and says nothing about the rows of the carrier.  The strongly coded form keeps the strong coding of
the carrier's rows next to its recovery.

* `StageType.StronglyCodedMarginCalibration ξ`: the margin calibration
  (`StageType.GradedCapMarginCalibration`) at a strongly coded context and a strongly coded donor,
  the calibration of
  `StageType.HasCodedLadderGrowthCarriersStable.hasStableGrowthCarriers_stronglyCoded`.
* `StageType.HasStronglyCodedStableGrowthCarriers ξ C`: `StageType.HasStableGrowthCarriers ξ C`
  with a carrier whose rows are strongly coded.
* `StageType.StronglyCodedStableGrowthCarriersTarget`: strongly coded stable growth carriers for
  the strongly coded margin calibration at every stage.
* `StageType.IsStableRecoveryScheme.exists_isCutoffStableRecovery_of_isStronglyCoded`: a stable
  recovery scheme with strongly coded rows gives a strongly coded carrier of cutoff stable
  recovery, the coface on the scheme.
* `StageType.HasStronglyCodedStableGrowthCarriers.hasStronglyCodedCutoffStableRecovery`: strongly
  coded stable growth carriers for the strongly coded margin calibration give the finite target
  `StageType.HasStronglyCodedCutoffStableRecovery ξ`, through the argument of
  `StageType.HasStableGrowthCarriers.hasStableRecoverySchemes` and
  `StageType.HasStableRecoverySchemes.hasCutoffStableRecoverySchemes`.  The recovery contract
  (`StageType.IsCutoffStableRecovery`) is unchanged.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Ordinal Label StageType

namespace StageType

variable (ξ : Ordinal.{u})

/-- The **strongly coded margin calibration**: the margin calibration
(`StageType.GradedCapMarginCalibration`) at a context `T⁺` and a donor `D` whose rows are strongly
coded. -/
def StronglyCodedMarginCalibration ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (f : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  Tp.rows.IsStronglyCoded ∧ D.rows.IsStronglyCoded ∧ GradedCapMarginCalibration ξ Tp f D γ

/-- **Strongly coded stable growth carriers** for a calibration `C`, a finite statement about stage
types (no realization): `StageType.HasStableGrowthCarriers ξ C` with a growth carrier whose rows are
strongly coded.  The recovery is that of `StageType.HasStableGrowthCarriers`: it quantifies over
every lawful section of the carrier's rows, with no stage bound. -/
def HasStronglyCodedStableGrowthCarriers
    (C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop) : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) →
      C Tp f D γ → ∃ G : GrowthCarrier Tp.toScheme D.toScheme f,
        G.scheme.rows.IsStronglyCoded ∧ G.Recovers Tp.label (CappedRelation D γ)

/-- **Strongly coded stable growth carriers for the strongly coded margin calibration at every
stage** (a named statement). -/
def StronglyCodedStableGrowthCarriersTarget : Prop :=
  ∀ ξ : Ordinal.{u}, HasStronglyCodedStableGrowthCarriers ξ (StronglyCodedMarginCalibration ξ)

variable {ξ}

/-- **Strongly coded stable growth carriers are stable growth carriers**, forgetting the strong
coding of the carrier's rows. -/
theorem HasStronglyCodedStableGrowthCarriers.hasStableGrowthCarriers
    {C : ∀ ⦃m k : ℕ⦄, StageType.{u} (blockStage (ξ + 1)) m → (Fin k ↪ Fin m) →
      StageType.{u} (blockStage (ξ + 1)) (k + 1) → Ordinal.{u} → Prop}
    (h : HasStronglyCodedStableGrowthCarriers ξ C) : HasStableGrowthCarriers ξ C :=
  fun _ _ Tp f P hT hk hP D hD γ hγ hC ↦
    let ⟨G, _, hrec⟩ := h Tp f P hT hk hP D hD γ hγ hC
    ⟨G, hrec⟩

/-- **A strongly coded stable recovery scheme gives a strongly coded carrier of cutoff stable
recovery**: as `StageType.IsStableRecoveryScheme.exists_isCutoffStableRecovery`, the coface `q` of
`T⁺↓λ_ξ` on the scheme `E` carries cutoff stable recovery, and its rows are those of `E`.  The
recovery contract is that of `StageType.IsCutoffStableRecovery`: every stage type whose reduction
lies in the receiving family of `q`. -/
theorem IsStableRecoveryScheme.exists_isCutoffStableRecovery_of_isStronglyCoded {m k : ℕ}
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} {E : Scheme.{u} (m + 1)}
    (hE : Tp.IsStableRecoveryScheme f D γ E) (hEs : E.rows.IsStronglyCoded) :
    ∃ (q : StageType.{u} (blockStage ξ) (m + 1)) (δ : Label.{u}),
      q.rows.IsStronglyCoded ∧ Tp.IsCutoffStableRecovery f D γ q δ := by
  obtain ⟨q, hq, hqE⟩ := hE.1
  have hqs : q.rows.IsStronglyCoded := by
    rw [hqE]
    exact hEs
  exact ⟨q, _, hqs, hE.isCutoffStableRecovery hq hqE
    (isPermittedCutoff_coe.mpr (isSuccLimit_blockStage ξ).bot_lt)⟩

/-- **Strongly coded cutoff stable recovery from strongly coded stable growth carriers** for the
strongly coded margin calibration: the existing argument (`GrowthCarrier.isStableRecoveryScheme`,
then `StageType.IsStableRecoveryScheme.exists_isCutoffStableRecovery`), with the strong coding of
the carrier's rows carried to the carrier `q` of cutoff stable recovery.  The recovery contract is
unchanged: every stage type whose reduction lies in the receiving family of `q` at `δ`. -/
theorem HasStronglyCodedStableGrowthCarriers.hasStronglyCodedCutoffStableRecovery
    (h : HasStronglyCodedStableGrowthCarriers ξ (StronglyCodedMarginCalibration ξ)) :
    HasStronglyCodedCutoffStableRecovery ξ :=
  fun _ _ Tp f P hT hk hP D hD hDs γ hγ hC ↦
    let ⟨G, hGs, hrec⟩ := h Tp f P hT.1 hk hP D hD γ hγ ⟨hT.2, hDs, hC⟩
    (G.isStableRecoveryScheme hrec).exists_isCutoffStableRecovery_of_isStronglyCoded hGs

end StageType

end VaughtConjecture
