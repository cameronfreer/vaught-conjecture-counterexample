/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Expansion
import VaughtConjecture.Stage.Countable

/-!
# Stage types at block stages: determination by reductions and by thresholds

Roadmap, Layers 1–2 (stage reduction between block stages): the finite facts used at limit block
stages by the gluing of model expansions (`VaughtConjecture.Realization.Limit`) and at the limit,
successor and base steps of the quantitative reconstruction pathway of `roadmap/COMPANIONS.md`,
row 1.

The block stages are `λ_ξ = ω + ω · ξ` (`blockStage`).  Three finite facts about stage types at
block stages, each a statement about one type, with no realization involved:

* **Limit blocks** (`StageType.eq_of_forall_reduce_eq_of_isSuccLimit`): at a limit index `η`, a
  stage type at `λ_η` is determined by its reductions to the lower block stages `λ_ξ`, `ξ < η`.
  Every ordinal below `λ_η` lies below some `λ_ξ` (`exists_lt_blockStage_of_isSuccLimit`), so a
  label below `λ_η` is kept by the reduction to that `λ_ξ`, and the formal top is the only label
  sent to the top by every such reduction.
* **One block** (`StageType.eq_of_reduce_eq_of_threshold_iff`): a stage type at `λ_{η+1}` is
  determined by its reduction to `λ_η` together with its **thresholds**: for each cell whose
  reduction to `λ_η` is the formal top and each `n : ℕ`, whether its label is at least `λ_η + n`.
  The labels of such cells lie in the block `[λ_η, λ_η + ω)` or are the formal top, and two such
  labels with the same thresholds are equal (`Label.eq_of_forall_threshold_iff`); the other labels
  are kept by the reduction (`StageType.eq_of_reduce_eq_of_label_eq`).
* **Reduction to a larger stage is injective** (`StageType.reduce_injective_of_le`), since it only
  relabels the stage (`StageType.reduce_eq_castLE`).

Conversely to `isSuccLimit_blockStage`, **every successor-limit ordinal is a block stage**
(`exists_blockStage_eq_of_isSuccLimit`): a successor limit is `ω · β` with `β ≥ 1`, which is
`λ_{β-1}`.  So the successor-limit ordinals are exactly the block stages.

## Placement

This file belongs to Layer 2 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Ordinal Order

/-! ### Ordinals below a limit block stage -/

/-- **Every ordinal below a limit block stage lies below a lower block stage**: for a limit index
`η`, every `v < λ_η` is below `λ_ξ` for some `ξ < η`. -/
theorem exists_lt_blockStage_of_isSuccLimit {η v : Ordinal.{u}} (hη : IsSuccLimit η)
    (hv : v < blockStage η) : ∃ ξ < η, v < blockStage ξ := by
  rw [blockStage_eq_mul, one_add_of_omega0_le (omega0_le_of_isSuccLimit hη),
    lt_mul_iff_of_isSuccLimit hη] at hv
  obtain ⟨ξ, hξ, hv⟩ := hv
  exact ⟨ξ, hξ, hv.trans_le (CanonicallyOrderedAdd.le_add_self _ _)⟩

/-! ### Successor limits are block stages -/

/-- **Every successor-limit ordinal is a block stage**: the converse of `isSuccLimit_blockStage`.
-/
theorem exists_blockStage_eq_of_isSuccLimit {α : Ordinal.{u}} (hα : IsSuccLimit α) :
    ∃ ξ, blockStage ξ = α := by
  obtain ⟨β, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hα.isSuccPrelimit
  have hβ : 1 ≤ β := one_le_iff_ne_zero.mpr fun h ↦ hα.ne_bot (by simp [h])
  exact ⟨β - 1, by rw [blockStage_eq_mul, Ordinal.add_sub_cancel_of_le hβ]⟩

namespace Label

variable {x y : Label.{u}}

/-- Every label below a limit block stage, bottom included, is below a lower block stage. -/
theorem exists_lt_blockStage_of_lt {η : Ordinal.{u}} (hη : IsSuccLimit η)
    (hx : x < (blockStage η : Label.{u})) : ∃ ξ < η, x < (blockStage ξ : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact ⟨0, hη.pos, WithBot.bot_lt_coe _⟩
  | coe o =>
    obtain ⟨ξ, hξ, ho⟩ := exists_lt_blockStage_of_isSuccLimit hη
      (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hx))
    exact ⟨ξ, hξ, WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ho)⟩
  | top => exact absurd hx not_top_lt

/-- **A label at a limit block stage is determined by its reductions to the lower block stages.**
-/
theorem eq_of_forall_reduce_blockStage_eq {η : Ordinal.{u}} (hη : IsSuccLimit η)
    (hx : AtStage (blockStage η) x) (hy : AtStage (blockStage η) y)
    (h : ∀ ξ < η, reduce (blockStage ξ) x = reduce (blockStage ξ) y) : x = y := by
  have key : ∀ x y : Label.{u}, x < (blockStage η : Label.{u}) →
      (∀ ξ < η, reduce (blockStage ξ) x = reduce (blockStage ξ) y) → x = y := by
    intro x y hx h
    obtain ⟨ξ, hξ, hxξ⟩ := exists_lt_blockStage_of_lt hη hx
    have h1 := h ξ hξ
    rw [reduce_of_lt hxξ] at h1
    rwa [reduce_of_lt (reduce_lt_iff.mp (h1 ▸ hxξ))] at h1
  rcases hx with hx | rfl
  · exact key x y hx h
  rcases hy with hy | rfl
  · exact (key y ⊤ hy fun ξ hξ ↦ (h ξ hξ).symm).symm
  · rfl

/-- A label in `[β, β + ω)` is `β + j` for some `j : ℕ`. -/
private theorem exists_eq_add_natCast {β : Ordinal.{u}} (hx : (β : Label.{u}) ≤ x)
    (hx' : AtStage (β + ω) x) (hne : x ≠ ⊤) : ∃ j : ℕ, x = ((β + j : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd hx (not_le.mpr (WithBot.bot_lt_coe _))
  | coe o =>
    have hβo : β ≤ o := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hx)
    have hlt : o < β + ω := atStage_coe.mp hx'
    have hsub : o - β < ω := by
      by_contra hc
      refine hlt.not_ge ?_
      rw [← Ordinal.add_sub_cancel_of_le hβo]
      exact add_le_add_right (not_lt.mp hc) β
    obtain ⟨j, hj⟩ := Ordinal.lt_omega0.mp hsub
    exact ⟨j, by rw [← hj, Ordinal.add_sub_cancel_of_le hβo]⟩
  | top => exact absurd rfl hne

/-- **Two labels of `[β, β + ω) ∪ {⊤}` with the same thresholds are equal**: if `x` and `y` lie in
`[β, β + ω) ∪ {⊤}` and, for every `n : ℕ`, `β + n ≤ x` exactly when `β + n ≤ y`, then `x = y`.
-/
theorem eq_of_forall_threshold_iff {β : Ordinal.{u}} (hx : (β : Label.{u}) ≤ x)
    (hx' : AtStage (β + ω) x) (hy : (β : Label.{u}) ≤ y) (hy' : AtStage (β + ω) y)
    (h : ∀ n : ℕ,
      ((β + n : Ordinal.{u}) : Label.{u}) ≤ x ↔ ((β + n : Ordinal.{u}) : Label.{u}) ≤ y) :
    x = y := by
  have key : ∀ x y : Label.{u}, (β : Label.{u}) ≤ x → AtStage (β + ω) x →
      (∀ n : ℕ, ((β + n : Ordinal.{u}) : Label.{u}) ≤ y →
        ((β + n : Ordinal.{u}) : Label.{u}) ≤ x) → ¬ x < y := by
    intro x y hx hx' h hlt
    obtain ⟨j, rfl⟩ := exists_eq_add_natCast hx hx' (ne_top_of_lt hlt)
    have hle : ((β + (j + 1 : ℕ) : Ordinal.{u}) : Label.{u}) ≤ y := by
      rw [Nat.cast_add_one, ← add_assoc]
      exact not_lt.mp fun h' ↦ (lt_coe_add_one_iff.mp h').not_gt hlt
    have := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp (h (j + 1) hle))
    rw [Nat.cast_add_one, ← add_assoc] at this
    exact this.not_gt (Order.lt_add_one_iff.mpr le_rfl)
  rcases lt_trichotomy x y with hlt | heq | hlt
  · exact absurd hlt (key x y hx hx' fun n ↦ (h n).mpr)
  · exact heq
  · exact absurd hlt (key y x hy hy' fun n ↦ (h n).mp)

end Label

namespace StageType

variable {α β : Ordinal.{u}} {k : ℕ}

/-! ### Limit blocks -/

/-- **A stage type at a limit block stage is determined by its reductions to the lower block
stages**: if `t` and `t'` at `λ_η`, for a limit `η`, have the same reduction to `λ_ξ` for every
`ξ < η`, then `t = t'`. -/
theorem eq_of_forall_reduce_eq_of_isSuccLimit {η : Ordinal.{u}} (hη : IsSuccLimit η)
    {t t' : StageType.{u} (blockStage η) k}
    (h : ∀ ξ < η,
      t.reduce (isSuccPrelimit_blockStage ξ) = t'.reduce (isSuccPrelimit_blockStage ξ)) :
    t = t' := by
  have hs := congrArg StageType.toScheme (h 0 hη.pos)
  exact ext hs fun i j hij ↦ Label.eq_of_forall_reduce_blockStage_eq hη (t.atStage i)
    (t'.atStage j) fun ξ hξ ↦ label_congr (h ξ hξ) hij

/-! ### One block -/

/-- **A stage type is determined by its reduction and its labels at the cells reducing to the
top**: if `t` and `t'` have the same reduction to `β` and the same labels at the cells whose
reduction to `β` is the formal top (cells matched by position), then `t = t'`.  The other labels
are below `β`, where reduction keeps them. -/
theorem eq_of_reduce_eq_of_label_eq {t t' : StageType.{u} α k} (hβ : IsSuccPrelimit β)
    (h : t.reduce hβ = t'.reduce hβ)
    (hl : ∀ (i : Fin t.card) (j : Fin t'.card), (i : ℕ) = j → (t.reduce hβ).label i = ⊤ →
      t.label i = t'.label j) : t = t' := by
  have hs := congrArg StageType.toScheme h
  refine ext hs fun i j hij ↦ ?_
  by_cases hi : (t.reduce hβ).label i = ⊤
  · exact hl i j hij hi
  · have hr : Label.reduce β (t.label i) = Label.reduce β (t'.label j) := label_congr h hij
    have hxi : t.label i < β := not_le.mp (mt Label.reduce_eq_top_iff.mpr hi)
    rw [Label.reduce_of_lt hxi] at hr
    rwa [Label.reduce_of_lt (Label.reduce_lt_iff.mp (hr ▸ hxi))] at hr

/-- The label of a cell of a type at `λ_{η+1}` that reduces to the top at `λ_η` lies in the block
`[λ_η, λ_η + ω)` or is the formal top. -/
theorem label_mem_block {η : Ordinal.{u}} (t : StageType.{u} (blockStage (η + 1)) k)
    {d : Fin t.card} (hd : (t.reduce (isSuccPrelimit_blockStage η)).label d = ⊤) :
    (blockStage η : Label.{u}) ≤ t.label d ∧ Label.AtStage (blockStage η + ω) (t.label d) :=
  ⟨Label.reduce_eq_top_iff.mp hd, blockStage_add_one η ▸ t.atStage d⟩

/-- **A stage type at `λ_{η+1}` is determined by its reduction to `λ_η` and its thresholds**: if
`t` and `t'` have the same reduction to `λ_η` and, at every cell reducing to the top there (cells
matched by position), the same thresholds `λ_η + n ≤ label` for all `n : ℕ`, then `t = t'`. -/
theorem eq_of_reduce_eq_of_threshold_iff {η : Ordinal.{u}}
    {t t' : StageType.{u} (blockStage (η + 1)) k}
    (h : t.reduce (isSuccPrelimit_blockStage η) = t'.reduce (isSuccPrelimit_blockStage η))
    (hl : ∀ (i : Fin t.card) (j : Fin t'.card), (i : ℕ) = j →
      (t.reduce (isSuccPrelimit_blockStage η)).label i = ⊤ → ∀ n : ℕ,
        (((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t.label i ↔
          ((blockStage η + n : Ordinal.{u}) : Label.{u}) ≤ t'.label j)) : t = t' := by
  refine eq_of_reduce_eq_of_label_eq _ h fun i j hij hi ↦ ?_
  have hj : (t'.reduce (isSuccPrelimit_blockStage η)).label j = ⊤ :=
    (label_congr h hij).symm.trans hi
  exact Label.eq_of_forall_threshold_iff (t.label_mem_block hi).1 (t.label_mem_block hi).2
    (t'.label_mem_block hj).1 (t'.label_mem_block hj).2 (hl i j hij hi)

/-! ### Reduction to a larger stage -/

/-- **Reduction to a larger stage is injective**: for `α ≤ β`, it only relabels the stage. -/
theorem reduce_injective_of_le {n : ℕ} (hβ : IsSuccPrelimit β) (h : α ≤ β) :
    Function.Injective fun t : StageType.{u} α n ↦ t.reduce hβ := by
  intro t t' htt
  simp only [reduce_eq_castLE _ hβ h] at htt
  have hs := congrArg StageType.toScheme htt
  exact ext hs fun i j hij ↦ label_congr htt hij

end StageType

end VaughtConjecture
