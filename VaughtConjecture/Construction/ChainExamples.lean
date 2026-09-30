/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Construction.ChainModel

/-!
# Partial realizations and chains: examples

Roadmap, Layer 2 (the countable chain construction; a supported invisible face is distinguished
from an unsupported tuple); semantic contract, item 4 (absence of a face is mathematical
information).

**Supported invisible and unsupported tuples.**  `bare` is a stage type on three points with no
cells whose faces form the interval plan on `Fin 3` (the stage type of the same name in
`VaughtConjecture.Stage.Examples`).  In the partial realization of `bare` on `{0, 1, 2}`, the pair
`(0, 2)` is supported and invisible: its points are points of the chart, but `{0, 2}` is not an
interval, so it spans no closed face (`chartRealization_bare_eval_pairZeroTwo`).  The pair
`(0, 5)` is unsupported (`not_isSupported_pairZeroFive`), and has no type for that reason alone
(`chartRealization_bare_eval_pairZeroFive`).  The point `0` spans a closed face and is typed
(`isSome_chartRealization_bare_eval_pointZero`).

**Chains.**  The union of the constant chain at the one-point condition (the one-point chart) is
the partial realization of that condition (`chainUnion_const_onePoint`); it types the point `0`
(`chainUnion_const_onePoint_eval_pointZero`).  A chain that never absorbs a new point need not be
covering: in the union of the constant chain at the one-point condition, the pair `(0, 1)` is
unsupported and untyped (`chainUnion_const_onePoint_eval_pairZeroOne`), and the union is not
covering (`not_isCovering_chainUnion_const_onePoint`).  Absorption requirements are what make
the union of the construction covering.
-/

namespace VaughtConjecture.Construction

open Finset StageType

/-- A stage type on three points with no cells, whose faces are the intervals of `Fin 3`. -/
private def bare : StageType.{0} 0 3 where
  card := 0
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, Fin.elim0, Fin.elim0⟩
  rows := ⟨fun s ↦ s.elim0⟩
  label := Fin.elim0
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ d.elim0⟩⟩
  isCoded s := s.elim0
  isLawful := CellScheme.Rows.isLawful_of_isEmpty _
  atStage d := d.elim0

/-- The tuple `(0, 2)` of natural numbers. -/
private def pairZeroTwo : Fin 2 ↪ ℕ :=
  ⟨fun i ↦ 2 * i, fun a b h ↦ Fin.ext (by simpa using h)⟩

/-- The tuple `(0, 5)` of natural numbers. -/
private def pairZeroFive : Fin 2 ↪ ℕ :=
  ⟨fun i ↦ 5 * i, fun a b h ↦ Fin.ext (by simpa using h)⟩

/-- The tuple `(0, 1)` of natural numbers. -/
private def pairZeroOne : Fin 2 ↪ ℕ :=
  Fin.valEmbedding

/-- The tuple `(0)` of natural numbers. -/
private def pointZero : Fin 1 ↪ ℕ :=
  Fin.valEmbedding

/-- The pair `(0, 2)` is supported by a chart on three points. -/
private theorem isSupported_pairZeroTwo : IsSupported 3 pairZeroTwo := by
  decide

/-- **A supported invisible tuple**: the pair `(0, 2)` is supported by `bare` but spans no closed
face, so it has no type. -/
private theorem chartRealization_bare_eval_pairZeroTwo :
    bare.chartRealization.eval pairZeroTwo = none := by
  rw [chartRealization_eval_eq_none_iff isSupported_pairZeroTwo]
  decide

/-- The pair `(0, 5)` is not supported by a chart on three points. -/
private theorem not_isSupported_pairZeroFive : ¬ IsSupported 3 pairZeroFive :=
  fun h ↦ absurd (h 1) (by decide)

/-- **An unsupported tuple**: the pair `(0, 5)` has no type, because the point `5` is not a point
of the chart. -/
private theorem chartRealization_bare_eval_pairZeroFive :
    bare.chartRealization.eval pairZeroFive = none :=
  chartRealization_eval_of_not_isSupported not_isSupported_pairZeroFive

/-- The point `0` spans a closed face of `bare`, so it is typed. -/
private theorem isSome_chartRealization_bare_eval_pointZero :
    (bare.chartRealization.eval pointZero).isSome := by
  rw [chartRealization_eval_of_isSupported (k := 3) fun i ↦ i.isLt.trans_le (by decide),
    isSome_restrictFace_iff]
  decide

/-- The union of the constant chain at the one-point condition is the partial realization of
that condition. -/
private theorem chainUnion_const_onePoint :
    chainUnion (fun _ ↦ Condition.onePoint.{0} 0) = (Condition.onePoint 0).realization :=
  chainUnion_const _

/-- The union of the constant chain at the one-point condition types the point `0` by the
one-point stage type. -/
private theorem chainUnion_const_onePoint_eval_pointZero :
    (chainUnion fun _ ↦ Condition.onePoint.{0} 0).eval pointZero = some (onePoint 0) := by
  rw [chainUnion_const_onePoint]
  exact (Condition.onePoint 0).realization_eval_valEmbedding

/-- In the union of the constant chain at the one-point condition, the pair `(0, 1)` is
unsupported and has no type. -/
private theorem chainUnion_const_onePoint_eval_pairZeroOne :
    (chainUnion fun _ ↦ Condition.onePoint.{0} 0).eval pairZeroOne = none :=
  chainUnion_eval_of_forall_not_isSupported fun _ h ↦ absurd (h 1) (by decide)

/-- **A chain that never absorbs a point is not covering**: the union of the constant chain at
the one-point condition does not cover the point `1`. -/
private theorem not_isCovering_chainUnion_const_onePoint :
    ¬ (chainUnion fun _ ↦ Condition.onePoint.{0} 0).IsCovering := by
  rw [isCovering_chainUnion_iff monotone_const]
  intro h
  obtain ⟨_, hi⟩ := h 1
  exact absurd hi (by decide)

end VaughtConjecture.Construction
