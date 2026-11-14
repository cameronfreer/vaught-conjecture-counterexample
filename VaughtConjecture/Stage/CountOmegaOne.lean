/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Countable

/-!
# At most `ℵ₁` stage types at stage `ω₁`

A stage type at stage `ω₁` has finitely many labels, each `⊥`, `⊤` or an ordinal below `ω₁`; so
all its labels occur at some stage `β < ω₁` (`StageType.exists_lt_omega_one_forall_atStage`), and
the same scheme and labels form a stage type at stage `β` (`StageType.restage`).  There are
countably many stage types at each `β < ω₁` (`StageType.countable_of_lt_omega_one`), hence at
most `ℵ₁ · ℵ₀ = ℵ₁` stage types at stage `ω₁` on `n` points
(`StageType.mk_le_aleph_one_of_omega_one`).

## Placement

This file belongs to Layer 1 of `roadmap/README.md` (countable stage types), beside
`VaughtConjecture.Stage.Countable`; it counts the requests of the `ℵ₁` companion construction
(`VaughtConjecture.AlephOne.Schedule`).
-/

universe u

namespace VaughtConjecture.StageType

open Cardinal Ordinal

variable {α β : Ordinal.{u}} {n : ℕ}

/-- The same scheme and labels at a stage `β` at which every label occurs. -/
def restage (t : StageType.{u} α n) (h : ∀ d, Label.AtStage β (t.label d)) :
    StageType.{u} β n where
  toScheme := t.toScheme
  label := t.label
  isWellFormed := t.isWellFormed
  isCoded := t.isCoded
  isLawful := t.isLawful
  atStage := h

/-- Every label of a stage type at stage `ω₁` occurs at a common stage below `ω₁`. -/
theorem exists_lt_omega_one_forall_atStage (t : StageType.{u} ω₁ n) :
    ∃ β < (ω₁ : Ordinal.{u}), ∀ d, Label.AtStage β (t.label d) := by
  have hd : ∀ d, ∃ β < (ω₁ : Ordinal.{u}), Label.AtStage β (t.label d) := fun d ↦ by
    rcases Label.atStage_iff.mp (t.atStage d) with h | ⟨o, ho, h⟩ | h
    · exact ⟨0, omega_pos 1, by rw [h]; exact Label.atStage_bot⟩
    · refine ⟨Order.succ o, (Cardinal.isSuccLimit_omega 1).succ_lt ho, ?_⟩
      rw [← h]
      exact Label.atStage_iff.mpr (Or.inr (Or.inl ⟨o, Order.lt_succ o, rfl⟩))
    · exact ⟨0, omega_pos 1, by rw [h]; exact Label.atStage_top⟩
  choose β hβ hβt using hd
  exact ⟨Finset.univ.sup β, (Finset.sup_lt_iff (omega_pos 1)).mpr fun d _ ↦ hβ d,
    fun d ↦ (hβt d).mono (Finset.le_sup (Finset.mem_univ d))⟩

/-- **At most `ℵ₁` stage types at stage `ω₁`** on `n` points. -/
theorem mk_le_aleph_one_of_omega_one (n : ℕ) :
    Cardinal.mk (StageType.{u} ω₁ n) ≤ Cardinal.aleph 1 := by
  have key : ∀ t : StageType.{u} ω₁ n, ∃ b : Set.Iio (ω₁ : Ordinal.{u}),
      ∀ d, Label.AtStage b (t.label d) := fun t ↦
    let ⟨b, hb, h⟩ := exists_lt_omega_one_forall_atStage t
    ⟨⟨b, hb⟩, h⟩
  choose b hb using key
  let F : StageType.{u} ω₁ n → Σ c : Set.Iio (ω₁ : Ordinal.{u}), StageType.{u} c n :=
    fun t ↦ ⟨b t, t.restage (hb t)⟩
  have hF : Function.Injective F := by
    intro t t' h
    have hs : t.toScheme = t'.toScheme := congrArg (fun p ↦ p.2.toScheme) h
    have hl := congrArg (fun p : Σ c : Set.Iio (ω₁ : Ordinal.{u}), StageType.{u} c n ↦
      fun i : ℕ ↦ if hi : i < p.2.card then p.2.label ⟨i, hi⟩ else ⊥) h
    refine StageType.ext hs fun i j hij ↦ ?_
    have hi := congrFun hl i
    have hj : (i : ℕ) < t'.card := hij ▸ j.2
    simp only [F, restage, i.2, hj, ↓reduceDIte] at hi
    rw [hi]
    exact congrArg t'.label (Fin.ext hij)
  calc Cardinal.mk (StageType.{u} ω₁ n)
      ≤ Cardinal.mk (Σ c : Set.Iio (ω₁ : Ordinal.{u}), StageType.{u} c n) :=
        mk_le_of_injective hF
    _ = sum fun c : Set.Iio (ω₁ : Ordinal.{u}) ↦ Cardinal.mk (StageType.{u} c n) := mk_sigma _
    _ ≤ sum fun _ : Set.Iio (ω₁ : Ordinal.{u}) ↦ ℵ₀ := sum_le_sum _ _ fun c ↦
        mk_le_aleph0_iff.mpr (countable_of_lt_omega_one c.2 n)
    _ ≤ Cardinal.aleph 1 := by
        rw [sum_const, mk_Iio_ordinal, card_omega]
        simp

end VaughtConjecture.StageType
