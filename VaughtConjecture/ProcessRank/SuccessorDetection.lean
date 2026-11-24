/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.CoverTransfer
import VaughtConjecture.ProcessRank.Reconstruction
import VaughtConjecture.ProcessRank.SuccessorSeparation

/-!
# Stage-`ω₁` charts in the base language

Proofs of step 4 of `VaughtConjecture.ProcessRank.SuccessorSeparation`, at the block stage
`λ_{ω₁}`.  The statements about a receiving model expansion at `λ_{ω₁}` are converted to the stage
`ω₁` by `blockStage_omegaOne` and read off the countable block formulas there
(`realizeBlockFormulaOfIsReceivingModelTarget`, `ProcessRank.covers_of_forall_bfEquiv`).

* `realize_blockFormula_iff_of_blockStage_omegaOne` (proved): the block formula of the forcing
  thresholds of a type at `λ_η`, `η < ω₁`, holds of exactly the covers of that type in the
  reduction to `λ_η` of a receiving model expansion at `λ_{ω₁}`.
* `stageOmegaOneCoversDefinableTarget` (proved): covers at `λ_{ω₁}` are the tuples satisfying
  the block formulas of all countable reductions; the full type is recovered from its countable
  reductions by `StageType.option_eq_of_forall_map_reduce_eq`.
* `stageOmegaOneCoversBFEquivTarget` (proved): covers at `λ_{ω₁}` transfer along back-and-forth
  equivalence at `ω₁` (`ProcessRank.covers_of_forall_bfEquiv`).
* `exists_bfEquiv_append` (proved): from equivalence at `β + j`, `j` forth moves extend the pair
  by any `j` points, keeping equivalence at `β`.
* `stageOmegaOneExtendsToCoverBFEquivTarget` (proved): rooted covers on `m` points at `λ_{ω₁}`
  transfer along equivalence at `ω₁ + m`.
-/

universe u v w w' u'

namespace VaughtConjecture.ProcessRank

open Ordinal Order FirstOrder Language

/-- **Block formulas at a receiving model expansion at `λ_{ω₁}`**: at `η < ω₁`, the block
formula of the forcing thresholds of `t` holds of exactly the covers of `t` in the reduction to
`λ_η`.  `realizeBlockFormulaOfIsReceivingModelTarget` at `ω₁ = λ_{ω₁}` (`blockStage_omegaOne`). -/
theorem realize_blockFormula_iff_of_blockStage_omegaOne {M : Type w}
    [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage ω₁))
    (hR : R.1.IsReceivingModel) {η : Ordinal.{0}} (hη : η < ω₁) {k : ℕ}
    (t : StageType.{0} (blockStage η) k) (c : Fin k → M) :
    (blockFormula forcingThresholds η hη t).Realize c ↔
      (R.1.reduce (isSuccPrelimit_blockStage η)).Covers t c := by
  revert R
  rw [blockStage_omegaOne]
  intro R hR
  exact realizeBlockFormulaOfIsReceivingModelTarget R hR hη t c

/-- Covers at `λ_{ω₁}` are defined by the countable block formulas: a cover satisfies the block
formula of every reduction; conversely, the block formulas give covers of every countable
reduction, hence an injective tuple whose type has the reductions of `t`, hence type `t`
(`StageType.option_eq_of_forall_map_reduce_eq` at the limit index `ω₁`). -/
theorem stageOmegaOneCoversDefinableTarget : StageOmegaOneCoversDefinableTarget.{w} := by
  intro M _ R hR k t c
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  refine ⟨fun hc η hη ↦
    (realize_blockFormula_iff_of_blockStage_omegaOne R hR hη _ c).2 (hc.reduce _), fun h ↦ ?_⟩
  have hred (η : Ordinal.{0}) (hη : η < ω₁) : (R.1.reduce (isSuccPrelimit_blockStage η)).Covers
      (t.reduce (isSuccPrelimit_blockStage η)) c :=
    (realize_blockFormula_iff_of_blockStage_omegaOne R hR hη _ c).1 (h η hη)
  obtain ⟨hinj, -⟩ := hred 0 hω.pos
  refine ⟨hinj, StageType.option_eq_of_forall_map_reduce_eq hω fun ξ hξ ↦ ?_⟩
  obtain ⟨_, hξ'⟩ := hred ξ hξ
  rw [Realization.reduce_eval] at hξ'
  rw [Option.map_some]
  exact hξ'

/-- Covers at `λ_{ω₁}` transfer along equivalence at `ω₁`: equivalence at `ω₁` gives equivalence
at every countable level, and `ProcessRank.covers_of_forall_bfEquiv` applies at `ω₁ = λ_{ω₁}`
(`blockStage_omegaOne`), with both expansions the given one. -/
theorem stageOmegaOneCoversBFEquivTarget : StageOmegaOneCoversBFEquivTarget.{w} := by
  intro M _ R hR k t c c' hbf
  revert R t
  rw [blockStage_omegaOne]
  intro R hR t hc
  exact covers_of_forall_bfEquiv hR hR (fun ξ hξ ↦ (BFEquiv.monotone hξ.le hbf).symm) hc

/-- **Extension by `j` points**: if `a` and `b` are back-and-forth equivalent at `β + j`, every
extension of `a` by `j` points is matched by an extension of `b` by `j` points, the two
extensions being equivalent at `β`.  By `j` forth moves (`BFEquiv.forth`). -/
theorem exists_bfEquiv_append {L : Language.{u, v}} {M : Type w} [L.Structure M] {N : Type w'}
    [L.Structure N] : ∀ (j : ℕ) (β : Ordinal.{u'}) {n : ℕ} {a : Fin n → M} {b : Fin n → N},
      BFEquiv (L := L) (β + j) n a b → ∀ u : Fin j → M,
        ∃ u' : Fin j → N, BFEquiv (L := L) β (n + j) (Fin.append a u) (Fin.append b u')
  | 0, β, n, a, b, h, u => by
    refine ⟨Fin.elim0, ?_⟩
    obtain rfl : u = Fin.elim0 := funext fun i ↦ i.elim0
    rw [Fin.append_elim0, Fin.append_elim0]
    rw [Nat.cast_zero, add_zero] at h
    exact BFEquiv.relabel β h _
  | j + 1, β, n, a, b, h, u => by
    have hlev : β + ((j + 1 : ℕ) : Ordinal.{u'}) = (β + 1) + (j : Ordinal.{u'}) := by
      rw [add_assoc, ← Nat.cast_one (R := Ordinal.{u'}), ← Nat.cast_add, Nat.add_comm 1 j]
    rw [hlev] at h
    obtain ⟨v, hv⟩ := exists_bfEquiv_append j (β + 1) h (Fin.init u)
    rw [← Order.succ_eq_add_one] at hv
    obtain ⟨y, hy⟩ := hv.forth (u (Fin.last j))
    refine ⟨Fin.snoc v y, ?_⟩
    rw [← Fin.snoc_init_self u, Fin.append_snoc, Fin.append_snoc]
    exact hy

/-- Rooted covers at `λ_{ω₁}` transfer along equivalence at `ω₁ + m`: `m` forth moves
(`exists_bfEquiv_append`) match the witness `s` of the rooted cover by `s'` with `c ⌢ s` and
`c' ⌢ s'` equivalent at `ω₁`; then `s'` covers the same type (`stageOmegaOneCoversBFEquivTarget`)
and restricts to `c'` along the root, by the equality atoms (`BFEquiv.eq_iff_eq`). -/
theorem stageOmegaOneExtendsToCoverBFEquivTarget :
    StageOmegaOneExtendsToCoverBFEquivTarget.{w} := by
  rintro M _ R hR k ⟨m, q, f⟩ c c' hbf ⟨s, hsc, hs⟩
  obtain ⟨s', hs'⟩ := exists_bfEquiv_append m (ω₁ : Ordinal.{0}) hbf s
  have hss' : BFEquiv (L := baseLanguage.{0}) (ω₁ : Ordinal.{0}) m s s' := by
    have h := BFEquiv.relabel _ hs' (Fin.natAdd k)
    have e₁ : Fin.append c s ∘ Fin.natAdd k = s := funext fun i ↦ Fin.append_right c s i
    have e₂ : Fin.append c' s' ∘ Fin.natAdd k = s' := funext fun i ↦ Fin.append_right c' s' i
    rwa [e₁, e₂] at h
  refine ⟨s', funext fun i ↦ ?_, stageOmegaOneCoversBFEquivTarget R hR q s s' hss' hs⟩
  have h := (hs'.eq_iff_eq (Fin.natAdd k (f i)) (Fin.castAdd m i)).1 (by
    rw [Fin.append_right, Fin.append_left]
    exact congrFun hsc i)
  rw [Fin.append_right, Fin.append_left] at h
  exact h

end VaughtConjecture.ProcessRank
