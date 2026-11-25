/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SuccessorSeparation

/-!
# The pair of a receiving successor: occurrence, agreement through `ω₁`, and the threshold

Proofs of steps 1–3 of `VaughtConjecture.ProcessRank.SuccessorSeparation`.

* `successorOnePointPairTarget` (proved): the capped one-point pair at `λ_ξ + i` and `λ_ξ + j`
  (`onePointPairTarget`) occurs in a receiving model at `λ_{ξ+1}`
  (`Realization.IsReceivingModel.exists_covers_onePoint`).
* `successorPairAgreementTarget` (proved): covers in a receiving model expansion at `λ_{ω₁ + 1}`
  of two types with equal reductions to `λ_{ω₁}` cover one type in every countable reduction, so
  they are equivalent at every `η < ω₁`
  (`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`), hence at the limit `ω₁`.
* `successorThresholdSeparationTarget` (proved): the threshold lemma
  (`Realization.le_label_iff_exists_forcesThreshold`) in both directions, with forcing donors from
  the coatom extension property with apex at `λ_{ξ+1}`.
-/

universe u v w

namespace VaughtConjecture.ProcessRank

open Ordinal Order FirstOrder Language Label

/-- The one-point pair occurs in a receiving model at `λ_{ξ+1}`: the one-point apex type capped
at `λ_ξ + i` and at `λ_ξ + j`, both self-visible at `1` since `0 < i < j`
(`Label.isSelfVisible_coe_add`), is a legal top-free pair with one scheme and equal reductions to
`λ_ξ` (`onePointPairTarget`); exact receiving of the legal top-free types realizes both
(`Realization.IsReceivingModel.exists_covers_onePoint`). -/
theorem successorOnePointPairTarget : SuccessorOnePointPairTarget.{u, v} := by
  intro ξ M R hR i j hi hij
  have hβ := isSuccPrelimit_blockStage ξ
  have hc (n : ℕ) (hn : 0 < n) : IsSelfVisible 1 ((blockStage ξ + n : Ordinal.{u}) : Label.{u}) :=
    isSelfVisible_coe_add hβ hn
  have hne : blockStage ξ + (i : Ordinal.{u}) ≠ blockStage ξ + j := fun h ↦
    hij.ne (Nat.cast_injective (add_left_cancel h))
  obtain ⟨hl₁, hl₂, ht₁, ht₂, hs, -, hr⟩ := onePointPairTarget hβ (hc i hi) (hc j (hi.trans hij))
    (coe_add_lt_blockStage_add_one i) (coe_add_lt_blockStage_add_one j) le_self_add le_self_add hne
  obtain ⟨a₁, h₁⟩ := hR.exists_covers_onePoint (isSuccLimit_blockStage (ξ + 1)) hl₁ ht₁
  obtain ⟨a₂, h₂⟩ := hR.exists_covers_onePoint (isSuccLimit_blockStage (ξ + 1)) hl₂ ht₂
  exact ⟨_, _, hl₁, hl₂, ht₁, ht₂, hs, StageType.onePointApex_cap_label _ _,
    StageType.onePointApex_cap_label _ _, hr, a₁, a₂, h₁, h₂⟩

/-- Agreement through `ω₁`: at each `η < ω₁` the two covers cover one stage type in the reduction
of `e` to `λ_η`, a receiving model expansion, so they are equivalent at `η`
(`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`); `ω₁` is a limit
(`BFEquiv.limit`). -/
theorem successorPairAgreementTarget : SuccessorPairAgreementTarget.{w} := by
  intro M _ e he k t₁ t₂ c₁ c₂ ht h₁ h₂
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have hR : e.1.IsReceivingModel := ⟨e.2.isModel, he⟩
  refine (BFEquiv.limit _ hω _ _).2 fun η hη ↦ ?_
  have hηΩ : blockStage η ≤ blockStage ω₁ := blockStage_mono hη.le
  let f := e.reduceBlock (le_of_lt (hη.trans (Order.lt_add_one_iff.mpr le_rfl)))
  have hf : f.1.HasFiniteCutReceiving := (hR.reduce (isSuccPrelimit_blockStage _)
    (isSuccLimit_blockStage η) (blockStage_mono (hη.trans (Order.lt_add_one_iff.mpr le_rfl)).le)).2
  have key : t₁.reduce (isSuccPrelimit_blockStage η) = t₂.reduce (isSuccPrelimit_blockStage η) := by
    rw [← StageType.reduce_reduce t₁ (isSuccPrelimit_blockStage ω₁) _ hηΩ, ht,
      StageType.reduce_reduce _ _ _ hηΩ]
  have h₂' : f.1.Covers (t₁.reduce (isSuccPrelimit_blockStage η)) c₂ := by
    rw [key]
    exact h₂.reduce _
  exact ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving hη f f hf hf
    (h₁.reduce _) h₂' id

/-- The threshold separates the two covers at the reduction: the threshold lemma at `c₂` gives a
rooted cover forcing `n` (transported to the common root and the cell `d₁`), and at `c₁` it turns
any such rooted cover into the bound `λ_ξ + n ≤ t₁.label d₁`, against the hypothesis. -/
theorem successorThresholdSeparationTarget : SuccessorThresholdSeparationTarget.{u, v} := by
  intro ξ M R hR k t₁ t₂ c₁ c₂ h₁ h₂ hred d₁ d₂ hd hdtop n hlt hle
  have hrec := hR.2.hasFiniteExtensionReceiving hR.1.isConsistent
    (isSuccPrelimit_blockStage (ξ + 1))
  have hF : ForcingDonors.{u} ξ := forcingDonors_of_hasApexCoatomExtensions
    (StageType.hasApexCoatomExtensions (isSuccPrelimit_blockStage (ξ + 1)))
  have hd₂ : (t₂.reduce (isSuccPrelimit_blockStage ξ)).label d₂ = ⊤ :=
    (StageType.label_congr hred hd).symm.trans hdtop
  have transport : ∀ (p p' : StageType.{u} (blockStage ξ) k), p = p' → ∀ (e : Fin p.card)
      (e' : Fin p'.card), (e : ℕ) = e' → ∀ {m : ℕ} (q : StageType.{u} (blockStage ξ) m)
      (f : Fin k ↪ Fin m),
      StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) q f p' e' n →
        StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) q f p e n := by
    rintro p _ rfl e e' hee m q f h
    rwa [Fin.ext hee]
  refine ⟨?_, fun hx ↦ ?_⟩
  · obtain ⟨x, hx, hcov⟩ := (Realization.le_label_iff_exists_forcesThreshold hR.1.isConsistent
      hR.1.hasLegalTypes hrec hF h₂ d₂ hd₂ n).mp hle
    exact ⟨x, transport _ _ hred d₁ d₂ hd x.2.1 x.2.2 hx, hcov⟩
  · exact (Realization.le_label_iff_exists_forcesThreshold hR.1.isConsistent hR.1.hasLegalTypes
      hrec hF h₁ d₁ hdtop n).mpr hx |>.not_gt hlt

end VaughtConjecture.ProcessRank
