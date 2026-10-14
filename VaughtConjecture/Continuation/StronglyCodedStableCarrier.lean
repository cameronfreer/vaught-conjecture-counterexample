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

end StageType

end VaughtConjecture
