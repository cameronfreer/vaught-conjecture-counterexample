/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Dominate

/-!
# A witness at the root (work file for `h3`)

Work file (placement later), for the named condition `H3.RootWitness` of
`VaughtConjecture.MainTheorem.H3RaiseCoface`.  Compiled in this repository (theorem named):

* **Bounded readings** (`Label.IsBoundedReading`): maps fixing `⊥`, monotone, commuting with
  visibility replacement at the thresholds `≤ K`.  Finite maxima are bounded readings
  (`Label.IsBoundedReading.finsetSup`); a bounded reading sending no label other than `⊥` to `⊥`
  is a witness bounded by `K` (`Label.IsBoundedReading.isWitness`).
* **The pieces** (`Label.isBoundedReading_minCap`, `Label.isBoundedReading_nonBot`,
  `Label.isBoundedReading_atTop`, `Label.isBoundedReading_band`): the shifter of a witness capped
  at a label below its suppressor; a constant off `⊥`; a constant at `⊤`; and a band map from a
  block start `λ` to a block start `κ`, `⊥` below `λ`, followed by a bounded reading.
-/

universe u

namespace VaughtConjecture

open Finset

namespace Label

variable {K : ℕ}

/-- The constant `⊥` is a bounded reading. -/
theorem isBoundedReading_bot : IsBoundedReading K fun _ : Label.{u} ↦ (⊥ : Label.{u}) :=
  ⟨rfl, fun _ _ _ ↦ le_rfl, fun _ _ _ _ _ ↦ by simp⟩

/-- The maximum of two bounded readings is a bounded reading. -/
theorem IsBoundedReading.max {φ ψ : Label.{u} → Label.{u}} (hφ : IsBoundedReading K φ)
    (hψ : IsBoundedReading K ψ) : IsBoundedReading K fun y ↦ max (φ y) (ψ y) :=
  ⟨by simp [hφ.map_bot, hψ.map_bot], fun _ _ h ↦ max_le_max (hφ.monotone h) (hψ.monotone h),
    fun x k i hk hi ↦ by rw [hφ.comm x k i hk hi, hψ.comm x k i hk hi, visibilityReplace_max hi]⟩

/-- **A finite maximum of bounded readings is a bounded reading.** -/
theorem IsBoundedReading.finsetSup {ι : Type*} (s : Finset ι) {φ : ι → Label.{u} → Label.{u}}
    (h : ∀ i ∈ s, IsBoundedReading K (φ i)) :
    IsBoundedReading K fun y ↦ s.sup fun i ↦ φ i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isBoundedReading_bot (K := K))
  | insert a s ha ih =>
    simp only [Finset.sup_insert]
    exact (h a (mem_insert_self a s)).max (ih fun i hi ↦ h i (mem_insert_of_mem hi))

/-- **A bounded reading sending no label other than `⊥` to `⊥` is a witness bounded by `K`.** -/
theorem IsBoundedReading.isWitness {φ : Label.{u} → Label.{u}} (hφ : IsBoundedReading K φ)
    (hrefl : ∀ y, φ y = ⊥ → y = ⊥) : IsWitness (stepSuppressor.{u} K) φ where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := hφ.map_bot
  monotone := hφ.monotone
  visibilityReplace_comm x k hx i hi := by
    rcases le_or_gt k K with hk | hk
    · exact hφ.comm x k i hk hi
    · rw [stepSuppressor_of_lt hk, le_bot_iff] at hx
      rw [hrefl x hx, visibilityReplace_bot, hφ.map_bot, visibilityReplace_bot]

/-- **The shifter of a witness capped below its suppressor** is a bounded reading. -/
theorem isBoundedReading_minCap {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness g σ) {θ : Label.{u}} (hθ : IsSelfVisible K θ) (hθg : θ ≤ g K) :
    IsBoundedReading K fun z ↦ min (σ z) θ := by
  refine ⟨by simp [hw.map_bot], fun _ _ h ↦ min_le_min_right _ (hw.monotone h),
    fun x k i hk hi ↦ ?_⟩
  have hck : IsSelfVisible k θ := hθ.mono hk
  have hcg : θ ≤ g k := hθg.trans (hw.antitone hk)
  rcases le_or_gt (σ x) θ with hle | hlt
  · rw [min_eq_left hle, hw.visibilityReplace_comm x k (hle.trans hcg) i hi,
      min_eq_left (visibilityReplace_le_of_le hi hck hle)]
  · rw [min_eq_right hlt.le, hck.visibilityReplace_eq,
      min_eq_right (hw.le_apply_visibilityReplace hck hcg hlt hi)]

/-- **A constant off `⊥`**, self-visible at `K`, is a bounded reading. -/
theorem isBoundedReading_nonBot {c : Label.{u}} (hc : IsSelfVisible K c) :
    IsBoundedReading K fun y ↦ if y = ⊥ then ⊥ else c := by
  classical
  refine ⟨by simp, fun x y hxy ↦ ?_, fun x k i hk hi ↦ ?_⟩
  · by_cases hx : x = ⊥
    · simp [hx]
    · have hy : y ≠ ⊥ := fun h ↦ hx (le_bot_iff.mp (h ▸ hxy))
      simp [hx, hy]
  · by_cases hx : x = ⊥
    · simp [hx]
    · have hx' : visibilityReplace k i x ≠ ⊥ := by simpa using hx
      simp only [hx, hx', ite_false, (hc.mono hk).visibilityReplace_eq]

/-- **A constant at `⊤`**, self-visible at `K`, is a bounded reading. -/
theorem isBoundedReading_atTop {c : Label.{u}} (hc : IsSelfVisible K c) :
    IsBoundedReading K fun y ↦ if y = ⊤ then c else ⊥ := by
  classical
  refine ⟨by simp, fun x y hxy ↦ ?_, fun x k i hk hi ↦ ?_⟩
  · by_cases hx : x = ⊤
    · have hy : y = ⊤ := top_le_iff.mp (hx ▸ hxy)
      simp [hx, hy]
    · simp [hx]
  · by_cases hx : x = ⊤
    · simp only [hx, visibilityReplace_top, ite_true, (hc.mono hk).visibilityReplace_eq]
    · have hx' : visibilityReplace k i x ≠ ⊤ := by simpa using hx
      simp [hx, hx']

/-- **A band map followed by a bounded reading**: `⊥` below the block start `λ`, and the band map
from `λ` to the block start `κ` at a grade `N ≥ K` followed by the bounded reading `ν` above. -/
theorem isBoundedReading_band {ν : Label.{u} → Label.{u}} (hν : IsBoundedReading K ν)
    {κ lam : Ordinal.{u}} (hκ : Order.IsSuccPrelimit κ) (hlam : Order.IsSuccPrelimit lam)
    {N : ℕ} (hKN : K ≤ N) :
    IsBoundedReading K fun y ↦ if y < (lam : Label.{u}) then ⊥ else ν (bandMap κ lam N y) := by
  classical
  refine ⟨by simp [WithBot.bot_lt_coe], fun x y hxy ↦ ?_, fun x k i hk hi ↦ ?_⟩
  · by_cases hx : x < (lam : Label.{u})
    · simp only [hx, ite_true]
      exact bot_le
    · have hy : ¬ y < (lam : Label.{u}) := fun h ↦ hx (hxy.trans_lt h)
      simp only [hx, hy, ite_false]
      exact hν.monotone (monotone_bandMap κ lam N hxy)
  · have hlt : visibilityReplace k i x < (lam : Label.{u}) ↔ x < (lam : Label.{u}) :=
      visibilityReplace_lt_iff hlam
    by_cases hx : x < (lam : Label.{u})
    · simp [hx, hlt.mpr hx]
    · simp only [hx, mt hlt.mp hx, ite_false]
      rw [bandMap_visibilityReplace hκ hlam (hk.trans hKN) hi (not_lt.mp hx), hν.comm _ k i hk hi]

end Label

end VaughtConjecture
