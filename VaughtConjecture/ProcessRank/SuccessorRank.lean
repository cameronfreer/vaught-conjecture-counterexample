/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SuccessorDetection
import VaughtConjecture.ProcessRank.SuccessorExistence
import VaughtConjecture.ProcessRank.SuccessorPair

/-!
# A receiving successor at `ω₁` gives process rank above `ω₁`

Proofs of steps 5 and 6 of `VaughtConjecture.ProcessRank.SuccessorSeparation`, and of
`UnboundedNotHollowOrbitRankGtTarget`.

* `successorSeparatedPairTarget` (proved): the points `a₁`, `a₂` of the one-point pair labelled
  `λ_{ω₁} + 1` and `λ_{ω₁} + 2` in a receiving model expansion at `λ_{ω₁ + 1}` are equivalent at
  `ω₁` (`successorPairAgreementTarget`).  A rooted cover forcing `2` extends `![a₂]` in the
  reduction to `λ_{ω₁}`, and none extends `![a₁]` (`successorThresholdSeparationTarget`).  If the
  two were equivalent at `ω₁ + m`, `m` the size of that rooted cover, the rooted cover would extend
  `![a₁]` (`stageOmegaOneExtendsToCoverBFEquivTarget`, in the receiving reduction to `λ_{ω₁}`).
  So the pair is separated at `ω₁ + m` in the base language.
* `successorOrbitRankGtTarget`, `receivingNotTerminalOrbitRankGtTarget`,
  `successorProcessRankGtTarget`, `unboundedNotHollowOrbitRankGtTarget` (proved).
-/

universe w

namespace VaughtConjecture.ProcessRank

open Ordinal Order FirstOrder Language Label InfinitaryLogic.ScottProcess.Semantic

/-- A receiving successor at `ω₁` separates two points after `ω₁`, in the base language. -/
theorem successorSeparatedPairTarget : SuccessorSeparatedPairTarget.{w} := by
  intro M _ e he
  have hR : e.1.IsReceivingModel := ⟨e.2.isModel, he⟩
  have hβ := isSuccPrelimit_blockStage (ω₁ : Ordinal.{0})
  have hc₁ : IsSelfVisible 1 ((blockStage ω₁ + (1 : ℕ) : Ordinal.{0}) : Label.{0}) :=
    isSelfVisible_coe_add hβ le_rfl
  have hc₂ : IsSelfVisible 1 ((blockStage ω₁ + (2 : ℕ) : Ordinal.{0}) : Label.{0}) :=
    isSelfVisible_coe_add hβ one_le_two
  have hne : blockStage (ω₁ : Ordinal.{0}) + ((1 : ℕ) : Ordinal.{0}) ≠ blockStage ω₁ + (2 : ℕ) :=
    fun h ↦ absurd (Nat.cast_injective (add_left_cancel h)) (by decide)
  obtain ⟨hl₁, hl₂, ht₁, ht₂, -, -, hr⟩ := onePointPairTarget hβ hc₁ hc₂
    (coe_add_lt_blockStage_add_one 1) (coe_add_lt_blockStage_add_one 2) le_self_add le_self_add
    hne
  obtain ⟨a₁, h₁⟩ := hR.exists_covers_onePoint (isSuccLimit_blockStage _) hl₁ ht₁
  obtain ⟨a₂, h₂⟩ := hR.exists_covers_onePoint (isSuccLimit_blockStage _) hl₂ ht₂
  refine ⟨a₁, a₂, successorPairAgreementTarget e he hr h₁ h₂, ?_⟩
  have htop : (((StageType.onePointApex (α := blockStage (ω₁ + 1))).cap _ hc₁
      (coe_add_lt_blockStage_add_one 1)).reduce hβ).label ⟨0, Nat.one_pos⟩ = ⊤ :=
    (congrArg (Label.reduce _) (StageType.onePointApex_cap_label hc₁
      (coe_add_lt_blockStage_add_one 1) ⟨0, Nat.one_pos⟩)).trans
      (Label.reduce_of_le (by exact_mod_cast (le_self_add : blockStage ω₁ ≤ _)))
  have hlt : ((StageType.onePointApex (α := blockStage (ω₁ + 1))).cap _ hc₁
      (coe_add_lt_blockStage_add_one 1)).label ⟨0, Nat.one_pos⟩ <
      ((blockStage ω₁ + (2 : ℕ) : Ordinal.{0}) : Label.{0}) := by
    rw [StageType.onePointApex_cap_label]
    exact_mod_cast (add_lt_add_iff_left _).2 (Nat.cast_lt.2 one_lt_two)
  have hle : ((blockStage ω₁ + (2 : ℕ) : Ordinal.{0}) : Label.{0}) ≤
      ((StageType.onePointApex (α := blockStage (ω₁ + 1))).cap _ hc₂
        (coe_add_lt_blockStage_add_one 2)).label ⟨0, Nat.one_pos⟩ := by
    rw [StageType.onePointApex_cap_label]
  obtain ⟨⟨x, hx, hcov⟩, hnot⟩ := successorThresholdSeparationTarget e.1 hR h₁ h₂ hr
    ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩ rfl htop 2 hlt hle
  refine ⟨x.1, fun hbf ↦ hnot ⟨x, hx, ?_⟩⟩
  have hΩ : (ω₁ : Ordinal.{0}) ≤ ω₁ + 1 := le_self_add
  exact stageOmegaOneExtendsToCoverBFEquivTarget (e.reduceBlock hΩ)
    (hR.reduce (isSuccPrelimit_blockStage _) (isSuccLimit_blockStage _) (blockStage_mono hΩ))
    x _ _ hbf.symm hcov

/-- A receiving successor at `ω₁` gives an orbit rank above `ω₁`: an orbit rank of `![a₁]` at most
`ω₁` would make the separated pair equivalent at every level
(`bfEquiv_all_of_bfEquiv_orbitRank`). -/
theorem successorOrbitRankGtTarget : SuccessorOrbitRankGtTarget.{w} := by
  intro M _ e he
  obtain ⟨a₁, a₂, hbf, m, hm⟩ := successorSeparatedPairTarget e he
  refine ⟨1, ![a₁], lt_of_not_ge fun hle ↦ hm ?_⟩
  exact BFEquiv.toOrdinalLift
    (bfEquiv_all_of_bfEquiv_orbitRank (BFEquiv.monotone hle hbf.ofOrdinalLift) _)

/-- A model expansion at `λ_{ω₁}` that is not receiving-terminal gives an orbit rank above `ω₁`:
the receiving model at `λ_{ω₁ + 1}` reducing to it is an expansion of the same base structure
(its reduction to `ω` is that of the given expansion, `Realization.reduce_reduce`). -/
theorem receivingNotTerminalOrbitRankGtTarget : ReceivingNotTerminalOrbitRankGtTarget.{w} := by
  intro M _ R hnt
  obtain ⟨R', hR', hred⟩ : ∃ R' : Realization.{0, w} (blockStage (ω₁ + 1)) M,
      R'.IsReceivingModel ∧ R'.reduce (isSuccPrelimit_blockStage ω₁) = R.1 := by
    by_contra h
    exact hnt fun R' hR' hr ↦ h ⟨R', hR', hr⟩
  refine successorOrbitRankGtTarget ⟨R', hR'.1, ?_⟩ hR'.2
  rw [← Realization.reduce_reduce R' (isSuccPrelimit_blockStage ω₁) _
    (omega0_le_blockStage _), hred]
  exact R.2.toStructure_reduce

/-- A receiving successor at `ω₁` gives process rank above `ω₁`: a rank `β ≤ ω₁` would bound the
lifted supremum of the orbit ranks (`isRank_iff_lift_eq_iSup_orbitRank`) by `ω₁`. -/
theorem successorProcessRankGtTarget : SuccessorProcessRankGtTarget.{w} := by
  intro M _ _ e he δ hδ β hβ hrank
  obtain ⟨n, a, ha⟩ := successorOrbitRankGtTarget e he
  have h := (isRank_iff_lift_eq_iSup_orbitRank.1 hrank).2
  exact (ha.trans_le (((orbitRank_le_iSup_orbitRank a).trans_eq h.symm).trans
    (Ordinal.lift_le.2 hβ))).false

/-- Unbounded growth without cover-hollowness at `λ_{ω₁}` gives an orbit rank above `ω₁`: the
model is not receiving-terminal (`omegaOneNotReceivingTerminalTarget`). -/
theorem unboundedNotHollowOrbitRankGtTarget : UnboundedNotHollowOrbitRankGtTarget.{w} :=
  fun _ _ R hR hnh hgrow ↦
    receivingNotTerminalOrbitRankGtTarget R (omegaOneNotReceivingTerminalTarget R.1 hR hnh hgrow)

end VaughtConjecture.ProcessRank
