/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Construction
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.Realization.CapToModel
import VaughtConjecture.Stage.Cap

/-!
# Exact top-free receiving makes a receiving model

A given-model statement at every limit stage `α`
(`AlephOne.isReceivingModelOfExactReceivingTarget`): an exactly consistent covering realization
on a nonempty carrier with legal top-free types and exact receiving within the legal top-free stage
types is a receiving model.

**Finite-cut receiving by capping** (`AlephOne.hasFiniteCutReceiving_of_exactReceivingWithin`).
Over an occurrence `x` with a coface `d` and a cutoff `δ < α`, cap `d` at an ordinal `c' < α`,
self-visible at the arity of `d`, above `δ` and above every label of the type of `x` (which is
top-free, so its labels are bounded below `α`, `StageType.IsTopFree.exists_label_le`).  The capped
coface is legal and top-free, restricts to the type of `x` (`StageType.restrictFace_cap`), and has
the observation of `d` at `δ`; exact receiving realizes it over `x`.

**Modelhood** is then `Realization.isModel_of_hasFiniteCutReceiving`, with the uniformity and
dominance instances nonempty by the coatom extension property with apex
(`StageType.hasApexCoatomExtensions`, `StageType.nonempty_cofaces_inter_uniformityFamily`,
`StageType.nonempty_cofaces_inter_dominanceFamily`).

## Placement

This file is Stage 3 (one model of cardinality `ℵ₁`) of the `ℵ₁` companion construction over the
density sentence; that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v

namespace VaughtConjecture.AlephOne

open Ordinal Realization

/-- **Finite-cut receiving from exact top-free receiving**, at a stage that is zero or a limit,
for a realization with top-free types: the coface is capped above the cutoff and the labels of the
occurrence, and the capped coface is received exactly. -/
theorem hasFiniteCutReceiving_of_exactReceivingWithin {α : Ordinal.{u}} {M : Type v}
    {R : Realization.{u, v} α M} (hα : Order.IsSuccPrelimit α) (htf : R.HasTopFreeTypes)
    (hrec : R.ExactReceivingWithin fun _ ↦ {D | D.IsLegal ∧ D.IsTopFree}) :
    R.HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨δ, hδ, rfl⟩ := Label.isPermittedCutoff_iff.mp hc
  have h0 : 0 < α := pos_of_gt hδ
  obtain ⟨o, ho, hpo⟩ := (htf _ _ x.eval_tuple).exists_label_le h0
  obtain ⟨c', hoc', hc'α, hc'⟩ := Label.exists_lt_lt_isSelfVisible hα (max_lt ho hδ) (x.arity + 1)
  have hle {y : Ordinal.{u}} (hy : y ≤ max o δ) : (y : Label.{u}) ≤ c' :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (hy.trans hoc'.le))
  have hQ : StageType.restrictFace Fin.castSuccEmb (d.cap c' hc' hc'α) = some x.type :=
    StageType.restrictFace_cap hd.2 fun i ↦ (hpo i).trans (hle (le_max_left _ _))
  obtain ⟨u, ⟨hinj, hu⟩, huc⟩ := hrec x.type x.tuple (covers_of_eval _ x.eval_tuple)
    (d.cap c' hc' hc'α) Fin.castSuccEmb
    ⟨StageType.isLegal_cap.mpr hd.1, StageType.isTopFree_cap⟩ hQ
  refine ⟨⟨u, hinj⟩, Function.Embedding.ext fun i ↦ congrFun huc i, d.cap c' hc' hc'α,
    ⟨rfl, fun i j hij ↦ ?_⟩, hu⟩
  obtain rfl : i = j := Fin.ext hij
  -- the labels of the capped coface are `min (d.label i) c'` (`StageType.cap_label`)
  change min (min (d.label i) (c' : Label.{u})) _ = _
  rw [min_assoc, min_eq_right (hle (le_max_right _ _))]

/-- **Exact top-free receiving makes a receiving model**, the target form: finite-cut receiving by
capping (`AlephOne.hasFiniteCutReceiving_of_exactReceivingWithin`), then modelhood by
`Realization.isModel_of_hasFiniteCutReceiving`. -/
theorem isReceivingModelOfExactReceivingTarget : IsReceivingModelOfExactReceivingTarget.{v} := by
  intro α M hα R hne hc hcov hl htf hrec
  have hr := hasFiniteCutReceiving_of_exactReceivingWithin hα.isSuccPrelimit htf hrec
  have hext := StageType.hasApexCoatomExtensions hα.isSuccPrelimit
  exact ⟨isModel_of_hasFiniteCutReceiving hα hne hl hc hcov hr
    (fun x _ _ hγα ↦ StageType.nonempty_cofaces_inter_uniformityFamily hext.hasCoatomExtensions
      hα.isSuccPrelimit (hl _ _ x.eval_tuple) hγα)
    (fun x _ hγα ↦ StageType.nonempty_cofaces_inter_dominanceFamily hext hα.isSuccPrelimit
      (hl _ _ x.eval_tuple) hγα), hr⟩

end VaughtConjecture.AlephOne
