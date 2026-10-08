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
* **A witness inverting a bounded reading** (`Label.exists_witness_of_reading`).
* **A witness at the root from the locality at the cap** (`H3.rootWitness_of_locality`), given a
  lower bound at the root (`H3.RootLowBound`, a named condition: some root cell has a finite
  ordinal label, or the prescription is at least `n + 1` at the root cells with ordinal labels).
* **The donor raise over a gluing coface at an acquired context**
  (`H3.exists_raiseCoface_of_rootLowBound`), from the lower bound at the root (assumed).
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

/-- **A replacement at the value `i` is self-visible at `i`**, for `i ≤ k`. -/
theorem isSelfVisible_visibilityReplace_of_le {k i : ℕ} (hi : i ≤ k) (x : Label.{u}) :
    IsSelfVisible i (visibilityReplace k i x) := by
  by_cases hb : x = ⊥
  · rw [hb, visibilityReplace_bot]; exact isSelfVisible_bot _
  by_cases ht : x = ⊤
  · rw [ht, visibilityReplace_top]; exact isSelfVisible_top _
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  rw [visibilityReplace_block, isSelfVisible_block]
  split_ifs <;> omega

/-- **A witness inverting a bounded reading on finitely many labels.**  Let `σ₀` be a bounded
reading at `N > 0` reading finitely many row values `ρ x` (none `⊤`) as labels `ℓ x = σ₀ (ρ x)`
whose finite parts lie below `N`, `ν` a bounded reading at `K ≤ N`, and `θ` self-visible at
`K`, with `ν` not `⊥` at the row values of the ordinal labels and its zero set closed under the
replacements.  If some label `c₀ ≠ ⊥`, self-visible at `K`, is at most `ν (ρ x)` at every ordinal
`ℓ x`, or some ordinal `ℓ x` is finite (its band piece is then `⊥` only at `⊥`), some witness
`Φ` bounded by `K` sends no label other than `⊥` to `⊥`, sends `⊤` to at least `θ`, and sends
every ordinal `ℓ x` to `ν (ρ x)`: the maximum of the
constant `c₀` off `⊥`, the constant `θ` at `⊤`, and, for each `x`, the band map from the block of
`ℓ x` to the block of `ρ x` followed by `ν` (no-separation: `Label.IsBoundedReading.strip`,
`Label.IsBoundedReading.eq_of_eq`). -/
theorem exists_witness_of_reading {ι : Type*} [Finite ι] {ℓ ρ : ι → Label.{u}} {N : ℕ}
    (hN : 0 < N) {σ₀ : Label.{u} → Label.{u}} (hσ₀ : IsBoundedReading N σ₀)
    (hread : ∀ x, ℓ x = σ₀ (ρ x)) (hρ : ∀ x, ρ x ≠ ⊤)
    (hoff : ∀ x (μ : Ordinal.{u}) (j : ℕ), Order.IsSuccPrelimit μ →
      ℓ x = ((μ + j : Ordinal.{u}) : Label.{u}) → j < N)
    (hKN : K ≤ N) {ν : Label.{u} → Label.{u}} (hν : IsBoundedReading K ν) {θ : Label.{u}}
    (hθ : IsSelfVisible K θ)
    (hνz : ∀ z, ν z = ⊥ → ∀ k i, i ≤ k → ν (visibilityReplace k i z) = ⊥)
    (hν0 : ∀ x (o : Ordinal.{u}), ℓ x = o → ν (ρ x) ≠ ⊥)
    (hlow : (∃ c₀ : Label.{u}, IsSelfVisible K c₀ ∧ c₀ ≠ ⊥ ∧
        ∀ x (o : Ordinal.{u}), ℓ x = o → c₀ ≤ ν (ρ x)) ∨
      ∃ (x : ι) (o : Ordinal.{u}), ℓ x = o ∧ o < Ordinal.omega0) :
    ∃ Φ : Label.{u} → Label.{u}, IsWitness (stepSuppressor.{u} K) Φ ∧
      (∀ y, Φ y = ⊥ → y = ⊥) ∧ θ ≤ Φ ⊤ ∧ ∀ x (o : Ordinal.{u}), ℓ x = o → Φ (ℓ x) = ν (ρ x) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨c₀, hc₀, hc₀ν, hcase⟩ : ∃ c₀ : Label.{u}, IsSelfVisible K c₀ ∧
      (∀ x (o : Ordinal.{u}), ℓ x = o → c₀ ≤ ν (ρ x)) ∧
      (c₀ ≠ ⊥ ∨ ∃ (x : ι) (o : Ordinal.{u}), ℓ x = o ∧ o < Ordinal.omega0) := by
    rcases hlow with ⟨c₀, h1, h2, h3⟩ | h
    · exact ⟨c₀, h1, h3, .inl h2⟩
    · exact ⟨⊥, isSelfVisible_bot _, fun _ _ _ ↦ bot_le, .inr h⟩
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
    rcases hcase with hc₀b | ⟨x₀, o₀, ho₀, hω⟩
    · have h : c₀ ≤ Φ y := by
        simp only [hΦ, hne, ite_false]
        exact (le_max_left _ _).trans (le_max_left _ _)
      exact hc₀b (le_bot_iff.mp (hy ▸ h))
    -- a root label in the finite block: its piece is not `⊥` off `⊥`
    obtain ⟨hℓ₀, hρ₀, -⟩ := hblk x₀ ⟨o₀, ho₀⟩
    have hlam0 : lam x₀ = 0 := by
      have h1 : (lam x₀ : Ordinal.{u}) + j x₀ = o₀ :=
        (WithTop.coe_injective (WithBot.coe_injective (ho₀.symm.trans hℓ₀))).symm
      have hlt : lam x₀ < Ordinal.omega0 := lt_of_le_of_lt le_self_add (h1 ▸ hω)
      obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hlt
      cases m with
      | zero => simpa using hm
      | succ m =>
        exfalso
        apply hlam x₀ (m : Ordinal.{u})
        rw [hm, Nat.cast_succ, ← Order.succ_eq_add_one]
        exact Order.covBy_succ _
    have hκ0 : ν ((κ x₀ : Ordinal.{u}) : Label.{u}) ≠ ⊥ := fun h ↦ by
      have h' := hνz _ h (j x₀ + 1) (j x₀) (Nat.le_succ _)
      have e : visibilityReplace (j x₀ + 1) (j x₀) ((κ x₀ : Ordinal.{u}) : Label.{u}) =
          ρ x₀ := by
        rw [hρ₀, show ((κ x₀ : Ordinal.{u}) : Label.{u}) =
          ((κ x₀ + ((0 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) by simp]
        exact visibilityReplace_coe_add_natCast (hκ x₀) (Nat.succ_pos _) _
      rw [e] at h'
      exact hν0 x₀ o₀ ho₀ h'
    have hpx : ν ((κ x₀ : Ordinal.{u}) : Label.{u}) ≤ piece x₀ y := by
      have hnl : ¬ y < ((lam x₀ : Ordinal.{u}) : Label.{u}) := by
        rw [hlam0]
        intro hlt
        induction y using recBotCoeTop with
        | bot => exact hne rfl
        | coe o => exact absurd hlt (not_lt.mpr (WithBot.coe_le_coe.mpr
            (WithTop.coe_le_coe.mpr (zero_le (a := o)))))
        | top => exact absurd hlt (not_lt.mpr le_top)
      simp only [hpiece, show ∃ o : Ordinal.{u}, ℓ x₀ = o from ⟨o₀, ho₀⟩, hnl, ite_true,
        ite_false]
      exact hν.monotone (coe_le_bandMap hne)
    have hle : piece x₀ y ≤ Φ y := by
      simp only [hΦ]
      exact (Finset.le_sup (f := fun x ↦ piece x y) (mem_univ x₀)).trans (le_max_right _ _)
    exact hκ0 (le_bot_iff.mp (hy ▸ hpx.trans hle))
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

namespace H3

open Label StageType CellScheme ProfileTower

variable {α : Ordinal.{u}} {n k : ℕ}

section Witness

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {t : StageType.{u} α n} (hpt : restrictFace g p = some t)
  {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces)

variable (n) in
/-- **The cap of the witness at the root** of a prescription `f`: the replacement at the value
`n + 1` of its value at the marker, capped at its value at the cap. -/
noncomputable def rootCap (c r : Fin t'.card) (f : Prof (seed ht' hp htb)) : Label.{u} :=
  min (visibilityReplace (t'.toCellScheme.grade c) (n + 1)
      (f (faceCell (restrictFace_left_seed ht' hp htb) r)))
    (f (faceCell (restrictFace_left_seed ht' hp htb) c))

variable (n) in
/-- **A lower bound at the root** for a prescription `f` (a named condition): some root cell has a
finite ordinal label, or `f` is at least `n + 1` at every root cell with an ordinal label.  It is
used only to keep the witness at the root away from `⊥` below the lowest block of the root
labels. -/
def RootLowBound (f : Prof (seed ht' hp htb)) : Prop :=
  (∃ (x : Fin t.card) (o : Ordinal.{u}), t.label x = o ∧ o < Ordinal.omega0) ∨
    ∀ x (o : Ordinal.{u}), t.label x = o →
      (((n + 1 : ℕ) : Ordinal.{u}) : Label.{u}) ≤ f (rootCell ht' hp htb hpt x)

/-- **A witness at the root from the locality at the cap.**  At an acquired context, a
prescription `f` lawful below the private coatom at a grade from the grade of the cap, not `⊥` at
the cap and at the marker, and not `⊥` at the root cells not labelled `⊥`, has a witness at the
root at its root cap (`H3.rootCap`), provided the lower bound at the root (`H3.RootLowBound`, a
named condition: a finite ordinal root label, or `f ≥ n + 1` at the ordinal root cells): the witness of `Label.exists_witness_of_reading` for the bounded
reading of the label of `t'` at the cap and the shifter of the locality of `f` at the cap, capped
at the root cap; the root cells labelled `⊤` read at least the root cap by the marker inequality,
those labelled `⊥` are `⊥` by the root bottoms. -/
theorem rootWitness_of_locality {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c) {k' : ℕ}
    (f : Prof (seed ht' hp htb))
    (hf : (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), k')
      (fun e ↦ f e))
    (hck : t'.toCellScheme.grade c ≤ k')
    (hcap : f (faceCell (restrictFace_left_seed ht' hp htb) c) ≠ ⊥)
    (hmark : f (faceCell (restrictFace_left_seed ht' hp htb) r) ≠ ⊥)
    (hcl : ∀ x, t.label x ≠ ⊥ → f (rootCell ht' hp htb hpt x) ≠ ⊥)
    (hlow : RootLowBound n ht' hp htb hpt f) :
    RootWitness hd.2 (fun x ↦ f (rootCell ht' hp htb hpt x)) (rootCap n ht' hp htb c r f) := by
  classical
  set N := t'.toCellScheme.grade c with hNdef
  set θ := rootCap n ht' hp htb c r f with hθdef
  have hL := restrictFace_left_seed ht' hp htb
  have ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t :=
    (restrictFace_trans t' Fin.castSuccEmb g hp).symm.trans hpt
  have hrc (x : Fin t.card) : rootCell ht' hp htb hpt x = faceCell hL (faceCell ht x) := by
    change faceCell hL (faceCell hp (faceCell hpt x)) = _
    rw [faceCell_trans rfl hp hpt ht x]
  have hn := hctx.2.2.1
  have hvis (x : Fin t.card) : faceCell ht x ∈ t'.visibleCells (g.trans Fin.castSuccEmb) :=
    t'.toScheme.faceCell_mem_visibleCells _ x
  have hbelow (x : Fin t.card) :
      faceCell ht x ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) :=
    mem_below_of_mem_visibleCells hctx.1.1 (by omega) (hvis x)
  have hbelowA (y : Fin t'.card) (hy : y ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c)) :
      faceCell hL y ∈ (seed ht' hp htb).amalgam.toCellScheme.below
        ((seed ht' hp htb).amalgam.toCellScheme.gradedIndex (faceCell hL c)) := by
    rw [CellScheme.mem_below] at hy ⊢
    simp only [CellScheme.gradedIndex, Prod.mk_le_mk, scope_faceCell, grade_faceCell,
      map_subset_map] at hy ⊢
    exact hy
  have hcb : faceCell hL c ∈ (seed ht' hp htb).amalgam.toCellScheme.below
      (univ.erase (Fin.last (k + 1)), k') := by
    refine ⟨?_, ?_⟩
    · change (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_left]
      exact map_subset_map.mpr (subset_univ _)
    · change (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) ≤ k'
      rw [grade_faceCell]
      exact hck
  obtain ⟨hord, hloc, -⟩ := Rows.isLawfulBelow_iff_forall.mp hf
  obtain ⟨gf, σf, hw, heq⟩ := hloc _ hcb
  have hloc' (y : Fin t'.card) (hy : y ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c)) :
      min (f (faceCell hL y)) (f (faceCell hL c)) =
        min (σf (t'.rowAt c y)) (gf (t'.toCellScheme.grade y)) := by
    have h := heq ⟨faceCell hL y, hbelowA y hy⟩
    change min (f (faceCell hL y)) (f (faceCell hL c)) =
      min (σf ((seed ht' hp htb).amalgam.rows.row (faceCell hL c) ⟨faceCell hL y, hbelowA y hy⟩))
        (gf ((seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL y))) at h
    rw [← Scheme.rowAt_of_mem (hbelowA y hy), rowAt_faceCell hL, grade_faceCell] at h
    exact h
  have hcc : c ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) :=
    t'.toCellScheme.mem_below_gradedIndex c
  have hgN : f (faceCell hL c) ≤ gf N := by
    have h := hloc' c hcc
    rw [min_self] at h
    exact h.le.trans (min_le_right _ _)
  have hcsv : IsSelfVisible N (f (faceCell hL c)) := by
    have h := hord _ hcb
    change IsSelfVisible ((seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c)) _ at h
    rwa [grade_faceCell] at h
  have hθcap : θ ≤ f (faceCell hL c) := min_le_right _ _
  have hθg {j : ℕ} (hj : j ≤ N) : θ ≤ gf j := hθcap.trans (hgN.trans (hw.antitone hj))
  have hθsv : IsSelfVisible (n + 1) θ :=
    (Label.isSelfVisible_visibilityReplace_of_le (by omega) _).min (hcsv.mono (by omega))
  set ν : Label.{u} → Label.{u} := fun z ↦ min (σf z) θ
  have hν : Label.IsBoundedReading (n + 1) ν :=
    Label.isBoundedReading_minCap hw hθsv (hθg (by omega))
  obtain ⟨σ₀, hσ₀, hread₀⟩ := exists_isBoundedReading t'.isLawful hctx.1.2.1
  have hgrade (x : Fin t.card) : t'.toCellScheme.grade (faceCell ht x) ≤ N := by
    have h := hbelow x
    rw [CellScheme.mem_below] at h
    exact h.2
  have hid (x : Fin t.card) : min (f (rootCell ht' hp htb hpt x)) θ =
      min (σf (t'.rowAt c (faceCell ht x))) θ := by
    rw [hrc]
    calc min (f (faceCell hL (faceCell ht x))) θ
        = min (min (f (faceCell hL (faceCell ht x))) (f (faceCell hL c))) θ := by
          rw [min_assoc, min_eq_right hθcap]
      _ = min (min (σf (t'.rowAt c (faceCell ht x))) (gf (t'.toCellScheme.grade (faceCell ht x))))
            θ := by rw [hloc' _ (hbelow x)]
      _ = min (σf (t'.rowAt c (faceCell ht x))) θ := by
          rw [min_assoc, min_eq_right (hθg (hgrade x))]
  have hθ0 : θ ≠ ⊥ := by
    intro h
    rcases min_eq_bot.mp h with h' | h'
    · exact hmark (visibilityReplace_eq_bot_iff.mp h')
    · exact hcap h'
  have hνz : ∀ z, ν z = ⊥ → ∀ k i, i ≤ k → ν (visibilityReplace k i z) = ⊥ := by
    intro z hz k i hi
    have hσ : σf z = ⊥ := (min_eq_bot.mp hz).resolve_right hθ0
    change min (σf (visibilityReplace k i z)) θ = ⊥
    rw [hw.apply_visibilityReplace_eq_bot hσ k hi, min_bot_left]
  have hν0 : ∀ x (o : Ordinal.{u}), t.label x = o → ν (t'.rowAt c (faceCell ht x)) ≠ ⊥ := by
    intro x o ho h
    have h' : min (f (rootCell ht' hp htb hpt x)) θ = ⊥ := (hid x).trans h
    rcases min_eq_bot.mp h' with h'' | h''
    · exact hcl x (by rw [ho]; exact WithBot.coe_ne_bot) h''
    · exact hθ0 h''
  have hlow' : (∃ c₀ : Label.{u}, IsSelfVisible (n + 1) c₀ ∧ c₀ ≠ ⊥ ∧
      ∀ x (o : Ordinal.{u}), t.label x = o → c₀ ≤ ν (t'.rowAt c (faceCell ht x))) ∨
      ∃ (x : Fin t.card) (o : Ordinal.{u}), t.label x = o ∧ o < Ordinal.omega0 := by
    rcases hlow with h | h
    · exact .inr h
    · refine .inl ⟨(((n + 1 : ℕ) : Ordinal.{u}) : Label.{u}), ?_, WithBot.coe_ne_bot,
        fun x o ho ↦ ?_⟩
      · rw [isSelfVisible_coe, Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 _)]
      · change _ ≤ min (σf _) θ
        rw [← hid x]
        exact le_min (h x o ho) (natCast_le_of_isSelfVisible hθsv hθ0)
  obtain ⟨Φ, hΦ, hrefl, hΦtop, hΦval⟩ := Label.exists_witness_of_reading (ι := Fin t.card)
    (ℓ := t.label) (ρ := fun x ↦ t'.rowAt c (faceCell ht x)) (by omega) hσ₀
    (fun x ↦ (label_faceCell ht x).symm.trans (hread₀ _ (hbelow x)))
    (fun x ↦ ((t'.isCoded.rowAt_lt c _).trans_le le_top).ne)
    (fun x μ j hμ h ↦ hoff _ (hvis x) μ j hμ ((label_faceCell ht x).trans h))
    (by omega) hν hθsv hνz hν0 hlow'
  refine ⟨n + 1, le_rfl, Φ, hΦ, fun z h ↦ hrefl _ h, hΦtop, fun x ↦ ?_⟩
  induction hx : t.label x using Label.recBotCoeTop with
  | bot =>
    rw [hΦ.map_bot, min_bot_left]
    have hl : t'.label (faceCell ht x) = ⊥ := (label_faceCell ht x).trans hx
    have hrow := hbot _ (hvis x) hl
    have h := hloc' _ (hbelow x)
    rw [hrow, hw.map_bot, min_bot_left] at h
    have hf0 : f (faceCell hL (faceCell ht x)) = ⊥ := (min_eq_bot.mp h).resolve_right hcap
    change ⊥ = min (f (rootCell ht' hp htb hpt x)) θ
    rw [hrc, hf0, min_bot_left]
  | coe o =>
    rw [← hx, hΦval x o hx, hid x]
    simp only [ν, min_assoc, min_self]
  | top =>
    rw [min_eq_right hΦtop]
    have hl : t'.label (faceCell ht x) = ⊤ := (label_faceCell ht x).trans hx
    have hmark := hctx.2.2.2 _ (hvis x) hl
    have hrb : r ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex c) := hctx.2.1.2.1
    have hθA : θ ≤ σf (visibilityReplace N (n + 1) (t'.rowAt c r)) := by
      by_cases hA : σf (t'.rowAt c r) ≤ gf N
      · rw [hw.visibilityReplace_comm _ N hA (n + 1) (by omega)]
        calc θ = visibilityReplace N (n + 1) (min (f (faceCell hL r)) (f (faceCell hL c))) :=
              (visibilityReplace_min_of_isSelfVisible (by omega) hcsv _).symm
          _ = visibilityReplace N (n + 1) (min (σf (t'.rowAt c r))
                (gf (t'.toCellScheme.grade r))) := by rw [hloc' r hrb]
          _ ≤ visibilityReplace N (n + 1) (σf (t'.rowAt c r)) :=
              monotone_visibilityReplace (by omega) (min_le_left _ _)
      · exact hθcap.trans (hw.le_apply_visibilityReplace hcsv hgN
          (hgN.trans_lt (not_le.mp hA)) (by omega))
    have h1 : θ ≤ σf (t'.rowAt c (faceCell ht x)) := hθA.trans (hw.monotone hmark)
    have h2 : θ ≤ min (f (rootCell ht' hp htb hpt x)) (f (faceCell hL c)) := by
      rw [hrc, hloc' _ (hbelow x)]
      exact le_min h1 (hθg (hgrade x))
    exact (min_eq_right (h2.trans (min_le_left _ _))).symm

end Witness

/-- **The donor raise over a gluing coface at an acquired context**, from the lower bound at the
root (assumed, `H3.RootLowBound`): some coface `tb` of `p` with face `d` has the donor raise in
the class form at every grade `N ≤ k' ≤ k + 1` at which every prescription in the class, not `⊥`
at the cap and at the marker, has a lower bound at the root.  At a prescription `⊥` at the marker
the marker value is `⊥` and the identity is a witness at the cap `⊥`; otherwise the witness is that
of `H3.rootWitness_of_locality` at the root cap, which is at least the marker value. -/
theorem exists_raiseCoface_of_rootLowBound (hα : Order.IsSuccLimit α)
    {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} (ht' : t'.IsLegal)
    (hp : restrictFace Fin.castSuccEmb t' = some p) {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c) :
    ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      ∃ hpt : restrictFace g p = some t,
      ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        (∀ f : Prof (seed ht' hp htb),
          (seed ht' hp htb).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last (k + 1)), k')
            (fun e ↦ f e) →
          f (faceCell (restrictFace_left_seed ht' hp htb) c) ≠ ⊥ →
          f (faceCell (restrictFace_left_seed ht' hp htb) r) ≠ ⊥ →
          (∀ e ∈ classCells ht' hp htb htbd, e ∈ (seed ht' hp htb).amalgam.toCellScheme.below
            (univ.erase (Fin.last (k + 1)), k') → f e ≠ ⊥) →
          RootLowBound n ht' hp htb hpt f) →
        CapRequests.DonorRaiseBotAtIn
          (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' := by
  obtain ⟨tb, htb, htbd, hpt, hraise⟩ := exists_raiseCoface_gluing hα ht' hp ht hd hctx
  refine ⟨tb, htb, htbd, hpt, fun k' hk' hkm hlow ↦ hraise k' hk' hkm fun f hf hcap hcl ↦ ?_⟩
  have hn := hctx.2.2.1
  by_cases hm : f (faceCell (restrictFace_left_seed ht' hp htb) r) = ⊥
  · -- the marker value is `⊥`: the identity at the cap `⊥`
    refine ⟨⊥, isSelfVisible_bot _, ?_, n + 1, le_rfl, id, IsWitness.id_step _,
      fun _ h ↦ h, bot_le, fun _ ↦ by simp⟩
    change min (visibilityReplace _ _ (f (faceCell (restrictFace_left_seed ht' hp htb) r))) _ ≤ ⊥
    rw [hm, visibilityReplace_bot, min_bot_left]
  have hroot : ∀ x, t.label x ≠ ⊥ → f (rootCell ht' hp htb hpt x) ≠ ⊥ := by
    intro x hx
    have he : rootCell ht' hp htb hpt x =
        faceCell (restrictFace_left_seed ht' hp htb) (faceCell ht x) := by
      change faceCell _ (faceCell hp (faceCell hpt x)) = _
      rw [faceCell_trans rfl hp hpt ht x]
    rw [he]
    refine hcl _ (.inl ⟨faceCell ht x, t'.toScheme.faceCell_mem_visibleCells _ x,
      (label_faceCell ht x).trans_ne hx, rfl⟩) ⟨?_, ?_⟩
    · change (seed ht' hp htb).amalgam.toCellScheme.scope
        (faceCell (restrictFace_left_seed ht' hp htb) (faceCell ht x)) ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_left]
      exact map_subset_map.mpr (subset_univ _)
    · change (seed ht' hp htb).amalgam.toCellScheme.grade
        (faceCell (restrictFace_left_seed ht' hp htb) (faceCell ht x)) ≤ k'
      rw [grade_faceCell, grade_faceCell]
      have := t.grade_le x
      omega
  refine ⟨rootCap n ht' hp htb c r f, ?_, ?_,
    rootWitness_of_locality ht' hp htb hpt hd hctx hoff hbot f hf hk' hcap hm hroot
      (hlow f hf hcap hm hcl)⟩
  · have hcsv : IsSelfVisible (t'.toCellScheme.grade c)
        (f (faceCell (restrictFace_left_seed ht' hp htb) c)) := by
      have hcb : faceCell (restrictFace_left_seed ht' hp htb) c ∈
          (seed ht' hp htb).amalgam.toCellScheme.below (univ.erase (Fin.last (k + 1)), k') := by
        refine ⟨?_, ?_⟩
        · change (seed ht' hp htb).amalgam.toCellScheme.scope
            (faceCell (restrictFace_left_seed ht' hp htb) c) ⊆ _
          rw [scope_faceCell, ← Coatom.univ_map_left]
          exact map_subset_map.mpr (subset_univ _)
        · change (seed ht' hp htb).amalgam.toCellScheme.grade
            (faceCell (restrictFace_left_seed ht' hp htb) c) ≤ k'
          rw [grade_faceCell]
          exact hk'
      have h := (Rows.isLawfulBelow_iff_forall.mp hf).1 _ hcb
      change IsSelfVisible ((seed ht' hp htb).amalgam.toCellScheme.grade
        (faceCell (restrictFace_left_seed ht' hp htb) c)) _ at h
      rwa [grade_faceCell] at h
    exact (Label.isSelfVisible_visibilityReplace_of_le (by omega) _).min (hcsv.mono (by omega))
  · exact min_le_min_right _ (visibilityReplace_le_visibilityReplace (Nat.zero_le _) _)

end H3

end VaughtConjecture
