/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.PhaseConditions
import VaughtConjecture.AlephOne.ReceivingModel
import VaughtConjecture.AlephOne.Schedule

/-!
# Receiving models built by completed blocks

The assembly of the construction by completed blocks (`VaughtConjecture.AlephOne.PhaseConditions`)
at stage `ω₁`, on the carrier `ω₁.ToType` with phases indexed by `ω₁.ToType`.

* `Phase.FullPhaseIsReceivingModelTarget` (given-condition): for a schedule of requests that
  schedules every request at arbitrarily late phases, the realization of a phase condition with
  every phase completed and every point a block point is a receiving model with top-free types:
  exact top-free receiving (`Phase.fullPhaseExactReceivingTarget`) and the passage from exact
  receiving to receiving models (`AlephOne.isReceivingModelOfExactReceivingTarget`).
* `Phase.ExistsFullPhaseReceivingModelTarget` (existence): for every choice of shapes of the
  phases, some unbounded schedule of requests (read from the unbounded schedule of
  `AlephOne.existsUnboundedScheduleTarget`) and some full phase condition for these shapes and
  requests exist, and its realization is a receiving model with top-free types.  The condition,
  with its block enumeration, is kept in the conclusion.

Both are proved.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence (Stage 3, by
completed blocks), recorded in `roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction").
-/

namespace VaughtConjecture.AlephOne.Phase

open Ordinal Realization

/-- **Target: a full phase condition gives a member of the exported class** (given-condition).  At
stage `ω₁`, on the carrier `ω₁.ToType` with phases indexed by `ω₁.ToType`, if every request is
scheduled at arbitrarily late phases, the realization of a phase condition with every phase
completed and every point a block point is a receiving model with top-free types.  Proved
(`Phase.fullPhaseIsReceivingModelTarget`). -/
def FullPhaseIsReceivingModelTarget : Prop :=
  ∀ (shape : (ω₁ : Ordinal.{0}).ToType → BlockShape)
    (req : (ω₁ : Ordinal.{0}).ToType →
      PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType),
    (∀ (r : PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
      (ξ : (ω₁ : Ordinal.{0}).ToType), ∃ η, ξ ≤ η ∧ req η = r) →
    ∀ c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType shape req, c.phases = Set.univ → c.dom = Set.univ →
      c.real.IsReceivingModel ∧ c.real.HasTopFreeTypes

/-- **A full phase condition gives a member of the exported class**, the target form: the
realization is exactly consistent, covering (its domain is the whole carrier), with legal top-free
types and exact top-free receiving (`Phase.fullPhaseExactReceivingTarget`), hence a receiving model
(`AlephOne.isReceivingModelOfExactReceivingTarget`). -/
theorem fullPhaseIsReceivingModelTarget : FullPhaseIsReceivingModelTarget := by
  intro shape req hsched c hph hdom
  have : Nonempty (ω₁ : Ordinal.{0}).ToType := nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'
  refine ⟨isReceivingModelOfExactReceivingTarget (Cardinal.isSuccLimit_omega 1) c.real
    inferInstance c.isConsistent (fun n t ↦ c.isCovering t (by
      have h := Set.subset_univ (Set.range t)
      rwa [← hdom] at h))
    c.hasLegalTypes c.hasTopFreeTypes (fullPhaseExactReceivingTarget shape req hsched c hph hdom),
    c.hasTopFreeTypes⟩

/-- **Target: a receiving model built by completed blocks, for every choice of shapes.**  At stage
`ω₁`, on the carrier `ω₁.ToType` with phases indexed by `ω₁.ToType`, for every choice of shapes of
the phases there are a schedule of requests scheduling every request at arbitrarily late phases and
a phase condition for these shapes and requests with every phase completed and every point a block
point, whose realization is a receiving model with top-free types.  The condition, with its block
enumeration, is part of the conclusion.  Proved (`Phase.existsFullPhaseReceivingModelTarget`). -/
def ExistsFullPhaseReceivingModelTarget : Prop :=
  ∀ shape : (ω₁ : Ordinal.{0}).ToType → BlockShape,
    ∃ req : (ω₁ : Ordinal.{0}).ToType →
        PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType,
      (∀ (r : PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
        (ξ : (ω₁ : Ordinal.{0}).ToType), ∃ η, ξ ≤ η ∧ req η = r) ∧
      ∃ c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
          (ω₁ : Ordinal.{0}).ToType shape req,
        c.phases = Set.univ ∧ c.dom = Set.univ ∧ c.real.IsReceivingModel ∧
          c.real.HasTopFreeTypes

/-- **A receiving model built by completed blocks, for every choice of shapes**, the target form:
the requests of an unbounded schedule of the one-point construction
(`AlephOne.existsUnboundedScheduleTarget`), read as phase requests, are scheduled at arbitrarily
late phases; a full phase condition exists for them (`Phase.existsFullPhaseConditionTarget`), and
its realization is a receiving model with top-free types
(`Phase.fullPhaseIsReceivingModelTarget`). -/
theorem existsFullPhaseReceivingModelTarget : ExistsFullPhaseReceivingModelTarget := by
  intro shape
  obtain ⟨sched, hsched⟩ := existsUnboundedScheduleTarget
  let req : (ω₁ : Ordinal.{0}).ToType →
      PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType :=
    fun ξ ↦ ⟨(sched ξ).arity, (sched ξ).tuple, (sched ξ).donor⟩
  have hreq : ∀ (r : PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
      (ξ : (ω₁ : Ordinal.{0}).ToType), ∃ η, ξ ≤ η ∧ req η = r := fun r ξ ↦ by
    obtain ⟨η, hη, hs⟩ := hsched ⟨r.arity, r.tuple, r.donor⟩ ξ
    refine ⟨η, hη, ?_⟩
    change (⟨(sched η).arity, (sched η).tuple, (sched η).donor⟩ : PhaseRequest _ _) = r
    rw [hs]
  obtain ⟨c, hph, hdom⟩ := existsFullPhaseConditionTarget shape req
  exact ⟨req, hreq, c, hph, hdom, fullPhaseIsReceivingModelTarget shape req hreq c hph hdom⟩

end VaughtConjecture.AlephOne.Phase
