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

/-- **A witness inverting a bounded reading on finitely many labels.**  Let `σ₀` be a bounded
reading at `N > 0` reading finitely many row values `ρ x` (none `⊤`) as labels `ℓ x = σ₀ (ρ x)`
whose finite parts lie below `N`, `ν` a bounded reading at `K ≤ N`, and `θ` self-visible at
`K`.  For a label `c₀ ≠ ⊥`, self-visible at `K` and at most `ν (ρ x)` at every ordinal `ℓ x`,
some witness `Φ` bounded by `K` sends no label other than `⊥` to `⊥`, sends `⊤` to at least
`θ`, and sends every ordinal `ℓ x` to `ν (ρ x)`: the maximum of the
constant `c₀` off `⊥`, the constant `θ` at `⊤`, and, for each `x`, the band map from the block of
`ℓ x` to the block of `ρ x` followed by `ν` (no-separation: `Label.IsBoundedReading.strip`,
`Label.IsBoundedReading.eq_of_eq`). -/
theorem exists_witness_of_reading {ι : Type*} [Finite ι] {ℓ ρ : ι → Label.{u}} {N : ℕ}
    (hN : 0 < N) {σ₀ : Label.{u} → Label.{u}} (hσ₀ : IsBoundedReading N σ₀)
    (hread : ∀ x, ℓ x = σ₀ (ρ x)) (hρ : ∀ x, ρ x ≠ ⊤)
    (hoff : ∀ x (μ : Ordinal.{u}) (j : ℕ), Order.IsSuccPrelimit μ →
      ℓ x = ((μ + j : Ordinal.{u}) : Label.{u}) → j < N)
    (hKN : K ≤ N) {ν : Label.{u} → Label.{u}} (hν : IsBoundedReading K ν) {θ : Label.{u}}
    (hθ : IsSelfVisible K θ) {c₀ : Label.{u}} (hc₀ : IsSelfVisible K c₀) (hc₀b : c₀ ≠ ⊥)
    (hc₀ν : ∀ x (o : Ordinal.{u}), ℓ x = o → c₀ ≤ ν (ρ x)) :
    ∃ Φ : Label.{u} → Label.{u}, IsWitness (stepSuppressor.{u} K) Φ ∧
      (∀ y, Φ y = ⊥ → y = ⊥) ∧ θ ≤ Φ ⊤ ∧ ∀ x (o : Ordinal.{u}), ℓ x = o → Φ (ℓ x) = ν (ρ x) := by
  classical
  have := Fintype.ofFinite ι
  -- the blocks of the ordinal labels and of their row values
  have hdec (x : ι) : ∃ (lam κ : Ordinal.{u}) (j : ℕ), Order.IsSuccPrelimit lam ∧
      Order.IsSuccPrelimit κ ∧ ((∃ o : Ordinal.{u}, ℓ x = o) →
        ℓ x = ((lam + j : Ordinal.{u}) : Label.{u}) ∧ ρ x = ((κ + j : Ordinal.{u}) : Label.{u}) ∧
          ∀ i ≤ N, σ₀ ((κ + i : Ordinal.{u}) : Label.{u}) = ((lam + i : Ordinal.{u}) : Label.{u}))
      := by
    by_cases hx : ∃ o : Ordinal.{u}, ℓ x = o
    · obtain ⟨o, ho⟩ := hx
      obtain ⟨lam, hlam, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
      have hjN := hoff x lam j hlam ho
      induction hρx : ρ x using recBotCoeTop with
      | bot =>
        rw [hread, hρx, hσ₀.map_bot] at ho
        exact absurd ho.symm WithBot.coe_ne_bot
      | top => exact absurd hρx (hρ x)
      | coe o' =>
        obtain ⟨κ, hκ, j', rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o'
        rw [hread, hρx] at ho
        obtain ⟨rfl, hstrip⟩ := hσ₀.strip hN hκ hlam hjN ho
        exact ⟨lam, κ, j', hlam, hκ, fun _ ↦ ⟨(hread x).trans (hρx ▸ ho), rfl, hstrip⟩⟩
    · exact ⟨0, 0, 0, Ordinal.isSuccPrelimit_zero, Ordinal.isSuccPrelimit_zero, fun h ↦ absurd h hx⟩
  choose lam κ j hlam hκ hblk using hdec
  set piece : ι → Label.{u} → Label.{u} := fun x y ↦
    if ∃ o : Ordinal.{u}, ℓ x = o then
      (if y < ((lam x : Ordinal.{u}) : Label.{u}) then ⊥ else ν (bandMap (κ x) (lam x) N y))
    else ⊥ with hpiece
  have hpiece_br (x : ι) : IsBoundedReading K (piece x) := by
    by_cases hx : ∃ o : Ordinal.{u}, ℓ x = o
    · simpa only [hpiece, hx, ite_true] using isBoundedReading_band hν (hκ x) (hlam x) hKN
    · simpa only [hpiece, hx, ite_false] using (isBoundedReading_bot (K := K))
  set Φ : Label.{u} → Label.{u} := fun y ↦
    max (max (if y = ⊥ then ⊥ else c₀) (if y = ⊤ then θ else ⊥))
      (univ.sup fun x ↦ piece x y) with hΦ
  have hΦbr : IsBoundedReading K Φ :=
    ((isBoundedReading_nonBot hc₀).max (isBoundedReading_atTop hθ)).max
      (IsBoundedReading.finsetSup univ fun x _ ↦ hpiece_br x)
  have hrefl (y : Label.{u}) (hy : Φ y = ⊥) : y = ⊥ := by
    by_contra hne
    have h : c₀ ≤ Φ y := by
      simp only [hΦ, hne, ite_false]
      exact (le_max_left _ _).trans (le_max_left _ _)
    exact hc₀b (le_bot_iff.mp (hy ▸ h))
  refine ⟨Φ, hΦbr.isWitness hrefl, hrefl, ?_, fun x' o ho ↦ ?_⟩
  · simp only [hΦ, top_ne_bot, ite_false, ite_true]
    exact (le_max_right _ _).trans (le_max_left _ _)
  -- the value at an ordinal label
  obtain ⟨hℓ', hρ', hst'⟩ := hblk x' ⟨o, ho⟩
  have hne : ℓ x' ≠ ⊥ := by rw [ho]; exact WithBot.coe_ne_bot
  have hnt : ℓ x' ≠ ⊤ := fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective (ho.symm.trans h))
  have hjN : j x' < N := hoff x' (lam x') (j x') (hlam x') hℓ'
  -- the piece at `x'` reads `ℓ x'` as `ν (ρ x')`
  have hband (x : ι) (hx : ∃ o : Ordinal.{u}, ℓ x = o) (hlx : lam x = lam x') :
      piece x (ℓ x') = ν (ρ x') := by
    obtain ⟨-, -, hst⟩ := hblk x hx
    have hnl : ¬ ℓ x' < ((lam x : Ordinal.{u}) : Label.{u}) := by
      rw [hℓ', hlx]
      exact not_lt.mpr (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add))
    simp only [hpiece, hx, hnl, ite_true, ite_false]
    rw [hℓ', ← hlx, bandMap_coe_add_natCast, min_eq_left hjN.le]
    congr 1
    refine hσ₀.eq_of_eq hN (fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)) (hρ x')
      (hlam x') hjN ?_ ?_
    · rw [hst (j x') hjN.le, hlx]
    · rw [← hread, hℓ']
  refine le_antisymm ?_ ?_
  · simp only [hΦ, hne, hnt, ite_false]
    refine max_le (max_le (hc₀ν x' o ho) bot_le) (Finset.sup_le fun x _ ↦ ?_)
    by_cases hx : ∃ o : Ordinal.{u}, ℓ x = o
    swap
    · simp only [hpiece, hx, ite_false]
      exact bot_le
    obtain ⟨-, -, hst⟩ := hblk x hx
    by_cases hlt : ℓ x' < ((lam x : Ordinal.{u}) : Label.{u})
    · simp only [hpiece, hx, hlt, ite_true]
      exact bot_le
    have hle : lam x ≤ lam x' := by
      by_contra hgt
      push Not at hgt
      apply hlt
      rw [hℓ']
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ((hlam x).add_natCast_lt hgt _))
    rcases hle.lt_or_eq with hlt' | heq
    · simp only [hpiece, hx, hlt, ite_true, ite_false]
      have hbm : bandMap (κ x) (lam x) N (ℓ x') = ((κ x + N : Ordinal.{u}) : Label.{u}) := by
        refine bandMap_of_le ?_
        rw [hℓ']
        exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
          (((hlam x').add_natCast_lt hlt' N).le.trans le_self_add))
      rw [hbm]
      refine hν.monotone (le_of_not_gt fun hρlt ↦ ?_)
      have h1 := hσ₀.monotone hρlt.le
      rw [← hread x', hst N le_rfl, hℓ'] at h1
      have h2 : lam x' + j x' ≤ lam x + N := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h1)
      exact absurd (h2.trans_lt ((hlam x').add_natCast_lt hlt' N)) (not_lt.mpr le_self_add)
    · exact (hband x hx heq).le
  · simp only [hΦ]
    exact (hband x' ⟨o, ho⟩ rfl).symm.le.trans
      ((Finset.le_sup (f := fun x ↦ piece x (ℓ x')) (mem_univ x')).trans (le_max_right _ _))

end Label

end VaughtConjecture
