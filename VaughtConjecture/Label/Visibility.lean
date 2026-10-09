/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Basic
import VaughtConjecture.Label.OrdinalVisibility

/-!
# Visibility replacement

Roadmap, Layer 1 (visibility replacement); semantic contract, item 3 (the visibility
replacement maps and the special bottom/top values).

Visibility replacement of an ordinal at threshold `k` with value `i` replaces its finite part
`o % ω` by `i` when that finite part is below `k` (`Ordinal.visibilityReplace`).  On labels
(`visibilityReplace k i`) it fixes the bottom label and the formal top.  A label is
*self-visible* at `k` (`IsSelfVisible k x`) if visibility replacement at threshold `k` with value
`k` fixes it; for an ordinal this says that its finite part is at least `k`
(`isSelfVisible_coe`), and for a natural number `n` that `k ≤ n` (`isSelfVisible_natCast`).

* Visibility replacement stays in the block of its argument, so it commutes with stage reduction
  at every stage `α` that is zero or a limit (`reduce_visibilityReplace`).
* For `i ≤ k` it is monotone (`monotone_visibilityReplace`), hence commutes with `min` and `max`,
  and it cannot push a label above a self-visible bound (`visibilityReplace_le_of_le`).
* Replacing again at the full threshold forgets the first value
  (`visibilityReplace_self_visibilityReplace`); a replacement below the threshold is undone by a
  second one (`exists_visibilityReplace_visibilityReplace`).  A replacement at threshold `K` with
  value `j` followed by one at threshold `k ≤ K` with value `i` is the replacement at `K` with
  value `i` if `j < k` and `j` otherwise (`visibilityReplace_visibilityReplace_of_le`).
* Replacement with a larger value gives a larger label
  (`visibilityReplace_le_visibilityReplace`), and replacement keeps a label at or above `ω` at or
  above `ω` (`not_lt_omega_visibilityReplace`).
* At a stage `α` that is zero or a limit, `α + K` is self-visible at every `k ≤ K`
  (`isSelfVisible_coe_add`); a label at least `α` and self-visible at `n` is at least `α + n`
  (`coe_add_le_of_isSelfVisible`), since `α` is a multiple of `ω`, and conversely a label at the
  stage `α + ω` that is at least `α + n` is self-visible at `n`
  (`isSelfVisible_of_coe_add_le`); replacement with a value
  `i ≤ K` keeps a label at most `α + K` at most `α + K` (`visibilityReplace_le_coe_add`); finitely
  many labels below `α` have a common bound below `α` that is self-visible at a given threshold
  (`exists_isSelfVisible_bound`), and between an ordinal `o` and a stage `β > o` that is zero or
  a limit there is an ordinal self-visible at any given threshold (`exists_lt_lt_isSelfVisible`).
* In the block `[μ, μ + ω)` of an ordinal `μ` that is zero or a limit, an ordinal `μ + k` whose
  finite part `k` is below the threshold `n` is not self-visible at `n`
  (`not_isSelfVisible_coe_add_natCast`), and replacement at `n` with value `i` gives `μ + i`
  (`visibilityReplace_coe_add_natCast`); it is self-visible at `n` exactly when `n ≤ k`
  (`isSelfVisible_coe_add_natCast_iff`), and `μ` and `k` are determined by `μ + k`
  (`add_natCast_eq_add_natCast_iff`).  Every ordinal is `μ + j` with `μ` zero or a limit and
  `j` finite (`exists_eq_add_natCast_isSuccPrelimit`), and replacement at `K` with value `m` sends
  `μ + j` to `μ + m` if `j < K` and fixes it otherwise (`visibilityReplace_coe_add`).
* On a natural number `n` it gives `i` if `n < k` and `n` otherwise (`visibilityReplace_natCast`,
  with `visibilityReplace_zero`, `visibilityReplace_one`, `visibilityReplace_ofNat` for numerals).
* At the threshold `3`: replacement with value `1` gives a label self-visible at `1`
  (`isSelfVisible_visibilityReplace_three_one`) and does not raise a label self-visible at `1`
  (`visibilityReplace_three_one_le`); a cap `c` self-visible at `3` does not separate finite parts
  below `3`: it lies below `visibilityReplace 3 1 y` when `c ≤ y`
  (`le_visibilityReplace_three_one`) and above `visibilityReplace 3 2 y` when `y < c`
  (`visibilityReplace_three_two_lt`).

## References

Visibility replacement is [Kni26, Definition 2.2.3], and the characterization of self-visible
ordinals (`isSelfVisible_coe`) is [Kni26, Lemma 2.2.4].
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {α o : Ordinal.{u}} {K k k' i : ℕ} {x y c : Label.{u}}

/-! ### Visibility replacement of labels -/

/-- Visibility replacement of labels at threshold `k` with value `i` [Kni26, Definition 2.2.3]:
bottom and the formal top are fixed, and an ordinal label is replaced by
`Ordinal.visibilityReplace k i`. -/
noncomputable def visibilityReplace (k i : ℕ) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map (Ordinal.visibilityReplace k i))

/-- Visibility replacement fixes the bottom label. -/
@[simp] theorem visibilityReplace_bot (k i : ℕ) : visibilityReplace k i (⊥ : Label.{u}) = ⊥ := rfl

/-- Visibility replacement fixes the formal top. -/
@[simp] theorem visibilityReplace_top (k i : ℕ) : visibilityReplace k i (⊤ : Label.{u}) = ⊤ := rfl

/-- Visibility replacement of an ordinal label is visibility replacement of the ordinal. -/
@[simp] theorem visibilityReplace_coe (k i : ℕ) (o : Ordinal.{u}) :
    visibilityReplace k i (o : Label.{u}) = (Ordinal.visibilityReplace k i o : Label.{u}) := rfl

/-- Visibility replacement of a natural number `n` gives `i` if `n < k`, and `n` otherwise. -/
@[simp] theorem visibilityReplace_natCast (k i n : ℕ) :
    visibilityReplace k i (n : Label.{u}) = if n < k then (i : Label.{u}) else n := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast, visibilityReplace_coe,
    Ordinal.visibilityReplace_natCast]
  split_ifs <;> rfl

/-- Visibility replacement of ordinal zero gives `i` if `0 < k`, and `0` otherwise. -/
@[simp] theorem visibilityReplace_zero (k i : ℕ) :
    visibilityReplace k i (0 : Label.{u}) = if 0 < k then (i : Label.{u}) else 0 := by
  simpa using visibilityReplace_natCast.{u} k i 0

/-- Visibility replacement of the ordinal `1` gives `i` if `1 < k`, and `1` otherwise. -/
@[simp] theorem visibilityReplace_one (k i : ℕ) :
    visibilityReplace k i (1 : Label.{u}) = if 1 < k then (i : Label.{u}) else 1 := by
  simpa using visibilityReplace_natCast.{u} k i 1

/-- Visibility replacement of a numeral `n` gives `i` if `n < k`, and `n` otherwise. -/
@[simp] theorem visibilityReplace_ofNat (k i n : ℕ) [n.AtLeastTwo] :
    visibilityReplace k i (ofNat(n) : Label.{u}) =
      if ofNat(n) < k then (i : Label.{u}) else ofNat(n) :=
  visibilityReplace_natCast k i n

/-- Visibility replacement preserves and reflects the bottom label. -/
@[simp] theorem visibilityReplace_eq_bot_iff : visibilityReplace k i x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop <;> simp

/-- Visibility replacement preserves and reflects the formal top. -/
@[simp] theorem visibilityReplace_eq_top_iff : visibilityReplace k i x = ⊤ ↔ x = ⊤ := by
  induction x using recBotCoeTop <;> simp

/-- Visibility replacement of labels is monotone when the new value does not exceed the
threshold. -/
theorem monotone_visibilityReplace (hi : i ≤ k) :
    Monotone (visibilityReplace k i : Label.{u} → Label.{u}) :=
  (Ordinal.monotone_visibilityReplace hi).withTop_map.withBot_map

/-- Visibility replacement commutes with `min` (in particular with a cap). -/
theorem visibilityReplace_min (hi : i ≤ k) (x y : Label.{u}) :
    visibilityReplace k i (min x y) = min (visibilityReplace k i x) (visibilityReplace k i y) :=
  (monotone_visibilityReplace hi).map_min

/-- Visibility replacement commutes with `max`. -/
theorem visibilityReplace_max (hi : i ≤ k) (x y : Label.{u}) :
    visibilityReplace k i (max x y) = max (visibilityReplace k i x) (visibilityReplace k i y) :=
  (monotone_visibilityReplace hi).map_max

/-- At a stage that is zero or a limit, visibility replacement keeps a label below the stage
exactly when it was below. -/
theorem visibilityReplace_lt_iff (hα : Order.IsSuccPrelimit α) :
    visibilityReplace k i x < α ↔ x < α := by
  induction x using recBotCoeTop with
  | bot => simp
  | coe o => simpa using Ordinal.visibilityReplace_lt_iff hα k i
  | top => simp

/-- Stage reduction to a stage that is zero or a limit commutes with visibility replacement. -/
theorem reduce_visibilityReplace (hα : Order.IsSuccPrelimit α) (k i : ℕ) (x : Label.{u}) :
    reduce α (visibilityReplace k i x) = visibilityReplace k i (reduce α x) := by
  by_cases hx : x < α
  · rw [reduce_of_lt hx, reduce_of_lt ((visibilityReplace_lt_iff hα).mpr hx)]
  · rw [reduce_of_le (not_lt.mp hx), visibilityReplace_top,
      reduce_of_le (not_lt.mp (mt (visibilityReplace_lt_iff hα).mp hx))]

/-- Replacing again at the full threshold forgets an earlier value `i ≤ k`. -/
theorem visibilityReplace_self_visibilityReplace (hi : i ≤ k) (x : Label.{u}) :
    visibilityReplace k k (visibilityReplace k i x) = visibilityReplace k k x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o => simp [Ordinal.visibilityReplace_self_visibilityReplace hi]
  | top => rfl

/-- A label lies below its visibility replacement when the new value is at least one below the
threshold (in particular for `i = k`). -/
theorem le_visibilityReplace (h : k ≤ i + 1) (x : Label.{u}) : x ≤ visibilityReplace k i x := by
  induction x using recBotCoeTop with
  | bot => exact le_rfl
  | coe o => simpa using Ordinal.le_visibilityReplace h o
  | top => exact le_rfl

/-- At a stage `α` that is zero or a limit, visibility replacement with a value `i ≤ K` keeps a
label at most `α + K` at most `α + K`. -/
theorem visibilityReplace_le_coe_add (hα : Order.IsSuccPrelimit α)
    (h : x ≤ ((α + K : Ordinal.{u}) : Label.{u})) (hi : i ≤ K) (k : ℕ) :
    visibilityReplace k i x ≤ ((α + K : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact bot_le
  | coe o => exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      (Ordinal.visibilityReplace_le_add hα (WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h)) hi k))
  | top => exact absurd h (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)))

/-- A label is recovered from its visibility replacement below the threshold by a second
visibility replacement below the threshold. -/
theorem exists_visibilityReplace_visibilityReplace (hi : i < k) (x : Label.{u}) :
    ∃ j < k, visibilityReplace k j (visibilityReplace k i x) = x := by
  induction x using recBotCoeTop with
  | bot => exact ⟨i, hi, rfl⟩
  | coe o =>
    obtain ⟨j, hj, h⟩ := Ordinal.exists_visibilityReplace_visibilityReplace hi o
    exact ⟨j, hj, by simp only [visibilityReplace_coe, h]⟩
  | top => exact ⟨i, hi, rfl⟩

/-- **Two replacements, the second at a threshold `k ≤ K`.**  A replacement at threshold `K` with
value `j` followed by one at threshold `k ≤ K` with value `i` is the replacement at threshold `K`
with value `i` if `j < k`, and with value `j` otherwise. -/
theorem visibilityReplace_visibilityReplace_of_le (hk : k ≤ K) (i j : ℕ) (x : Label.{u}) :
    visibilityReplace k i (visibilityReplace K j x) =
      visibilityReplace K (if j < k then i else j) x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o =>
    simp only [visibilityReplace_coe]
    rw [Ordinal.visibilityReplace, Ordinal.visibilityReplace_div, Ordinal.visibilityReplace_mod,
      Ordinal.visibilityReplace]
    obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
    rw [hn]
    split_ifs <;> simp_all
    omega
  | top => rfl

/-- Visibility replacement with a larger value gives a larger label. -/
theorem visibilityReplace_le_visibilityReplace {k i j : ℕ} (hij : i ≤ j)
    (A : Label.{u}) : visibilityReplace k i A ≤ visibilityReplace k j A := by
  induction A using recBotCoeTop with
  | bot => exact le_rfl
  | coe o =>
    simp only [visibilityReplace_coe, WithBot.coe_le_coe, WithTop.coe_le_coe,
      Ordinal.visibilityReplace]
    gcongr
    split_ifs
    · exact_mod_cast hij
    · exact le_rfl
  | top => exact le_rfl

/-- Visibility replacement keeps a label at or above `ω` at or above `ω`. -/
theorem not_lt_omega_visibilityReplace {x : Label.{u}} (hx : x ≠ ⊥)
    (hxω : ¬ x < ((ω : Ordinal.{u}) : Label.{u})) (k i : ℕ) :
    ¬ visibilityReplace k i x < ((ω : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | coe o => rwa [visibilityReplace_lt_iff isSuccLimit_omega0.isSuccPrelimit]
  | top => rwa [visibilityReplace_top]

/-! ### Self-visible labels -/

/-- A label is *self-visible* at threshold `k` if visibility replacement at threshold `k` with
value `k` fixes it: bottom, the formal top, or an ordinal whose finite part is at least `k`. -/
def IsSelfVisible (k : ℕ) (x : Label.{u}) : Prop := visibilityReplace k k x = x

/-- The bottom label is self-visible at every threshold. -/
@[simp, grind .] theorem isSelfVisible_bot (k : ℕ) : IsSelfVisible k (⊥ : Label.{u}) :=
  visibilityReplace_bot k k

/-- The formal top is self-visible at every threshold. -/
@[simp, grind .] theorem isSelfVisible_top (k : ℕ) : IsSelfVisible k (⊤ : Label.{u}) :=
  visibilityReplace_top k k

/-- An ordinal label is self-visible at `k` exactly when its finite part is at least `k`
[Kni26, Lemma 2.2.4]. -/
@[simp, grind =] theorem isSelfVisible_coe :
    IsSelfVisible k (o : Label.{u}) ↔ (k : Ordinal.{u}) ≤ o % ω := by
  refine ⟨fun h ↦ not_lt.mp fun hk ↦ ?_,
    fun h ↦ by simp [IsSelfVisible, Ordinal.visibilityReplace_of_le h]⟩
  have h' : Ordinal.visibilityReplace k k o = o := by simpa [IsSelfVisible] using h
  have := congrArg (· % ω) h'
  simp only [Ordinal.visibilityReplace_mod, hk, ite_true] at this
  exact hk.ne' this

/-- Ordinal zero is self-visible only at threshold zero. -/
@[simp] theorem isSelfVisible_zero : IsSelfVisible k (0 : Label.{u}) ↔ k = 0 := by
  simpa using isSelfVisible_coe (k := k) (o := 0)

/-- The ordinal `1` is self-visible exactly at the thresholds `≤ 1`. -/
@[simp] theorem isSelfVisible_one : IsSelfVisible k (1 : Label.{u}) ↔ k ≤ 1 :=
  isSelfVisible_coe.trans <| by rw [Ordinal.mod_eq_of_lt one_lt_omega0]; exact_mod_cast Iff.rfl

/-- A natural number `n` is self-visible exactly at the thresholds `≤ n`. -/
@[simp] theorem isSelfVisible_natCast (n : ℕ) : IsSelfVisible k (n : Label.{u}) ↔ k ≤ n :=
  isSelfVisible_coe.trans <| by rw [Ordinal.natCast_mod_omega0, Nat.cast_le]

/-- A numeral `n` is self-visible exactly at the thresholds `≤ n`. -/
@[simp] theorem isSelfVisible_ofNat (n : ℕ) [n.AtLeastTwo] :
    IsSelfVisible k (ofNat(n) : Label.{u}) ↔ k ≤ ofNat(n) :=
  isSelfVisible_natCast n

/-- The finite part of `α + K` is `K` when `α` is zero or a limit. -/
private theorem add_natCast_mod_omega0 (hα : Order.IsSuccPrelimit α) (K : ℕ) :
    (α + K) % ω = K := by
  obtain ⟨b, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hα
  rw [Ordinal.mul_add_mod_self, natCast_mod_omega0]

/-- At a stage `α` that is zero or a limit, the ordinal `α + K` is self-visible at every
threshold `k ≤ K`. -/
theorem isSelfVisible_coe_add (hα : Order.IsSuccPrelimit α) (hk : k ≤ K) :
    IsSelfVisible k ((α + K : Ordinal.{u}) : Label.{u}) :=
  isSelfVisible_coe.mpr (by rw [add_natCast_mod_omega0 hα]; exact_mod_cast hk)

/-- **The order law at a stage that is zero or a limit**: a label at least `β` and self-visible
at `n` is at least `β + n`. -/
theorem coe_add_le_of_isSelfVisible {β : Ordinal.{u}} {x : Label.{u}} {n : ℕ}
    (hβ : Order.IsSuccPrelimit β) (hx : (β : Label.{u}) ≤ x)
    (hv : IsSelfVisible n x) : ((β + n : Ordinal.{u}) : Label.{u}) ≤ x := by
  induction x using recBotCoeTop with
  | bot => exact absurd hx (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact le_top
  | coe v =>
    have hβv : β ≤ v := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hx)
    obtain ⟨b, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hβ
    have hb : ω * b ≤ ω * (v / ω) :=
      mul_le_mul_right ((mul_le_iff_le_div omega0_ne_zero).mp hβv) ω
    refine WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
    rw [← div_add_mod v ω]
    exact add_le_add hb (isSelfVisible_coe.mp hv)

/-- **A converse of the order law**: at a stage `β` that is zero or a limit, a label at the stage
`β + ω` that is at least `β + N` is self-visible at `N`: it is `β + j` with `N ≤ j`, or the formal
top. -/
theorem isSelfVisible_of_coe_add_le {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) {N : ℕ}
    (hx : AtStage (β + ω) x) (hN : ((β + N : Ordinal.{u}) : Label.{u}) ≤ x) :
    IsSelfVisible N x := by
  induction x using recBotCoeTop with
  | bot => exact absurd hN (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact isSelfVisible_top N
  | coe v =>
    have hNv : β + N ≤ v := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hN)
    have hβv : β ≤ v := le_self_add.trans hNv
    have hj : v - β < ω := by
      rw [← add_lt_add_iff_left β, Ordinal.add_sub_cancel_of_le hβv]
      exact atStage_coe.mp hx
    obtain ⟨j, hj'⟩ := lt_omega0.mp hj
    obtain rfl : v = β + j := by rw [← hj', Ordinal.add_sub_cancel_of_le hβv]
    exact isSelfVisible_coe_add hβ (by exact_mod_cast (add_le_add_iff_left β).mp hNv)

section Block

variable {μ : Ordinal.{u}} {n : ℕ}

/-- **Visibility replacement in a block**: at threshold `n`, the finite part `k < n` of an ordinal
`μ + k` in the block of `μ` is replaced by any value `i`. -/
theorem visibilityReplace_coe_add_natCast (hμ : Order.IsSuccPrelimit μ) (hk : k < n) (i : ℕ) :
    visibilityReplace n i ((μ + k : Ordinal.{u}) : Label.{u}) =
      ((μ + i : Ordinal.{u}) : Label.{u}) := by
  simp only [visibilityReplace_coe, Ordinal.visibilityReplace_add hμ,
    Ordinal.visibilityReplace_natCast, hk, ↓reduceIte]

/-- An ordinal `μ + k` of the block of `μ` whose finite part `k` is below `n` is not self-visible
at `n`. -/
theorem not_isSelfVisible_coe_add_natCast (hμ : Order.IsSuccPrelimit μ) (hk : k < n) :
    ¬ IsSelfVisible n ((μ + k : Ordinal.{u}) : Label.{u}) := by
  rw [isSelfVisible_coe, add_natCast_mod_omega0 hμ, not_le]
  exact_mod_cast hk

/-- An ordinal `μ + k` of the block of `μ` is self-visible at `n` exactly when its finite part `k`
is at least `n`. -/
theorem isSelfVisible_coe_add_natCast_iff (hμ : Order.IsSuccPrelimit μ) :
    IsSelfVisible n ((μ + k : Ordinal.{u}) : Label.{u}) ↔ n ≤ k := by
  rw [isSelfVisible_coe, add_natCast_mod_omega0 hμ, Nat.cast_le]

/-- **The block and the finite part of an ordinal are unique**: for `μ` and `μ'` zero or limits,
`μ + k = μ' + k'` exactly when `μ = μ'` and `k = k'`. -/
theorem add_natCast_eq_add_natCast_iff {μ' : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    (hμ' : Order.IsSuccPrelimit μ') : μ + k = μ' + k' ↔ μ = μ' ∧ k = k' := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by rw [h₁, h₂]⟩
  have hk : k = k' := by
    have := congrArg (· % ω) h
    simp only [add_natCast_mod_omega0 hμ, add_natCast_mod_omega0 hμ'] at this
    exact_mod_cast this
  subst hk
  obtain ⟨b, rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hμ
  obtain ⟨b', rfl⟩ := isSuccPrelimit_iff_omega0_dvd.mp hμ'
  have := congrArg (· / ω) h
  simp only [mul_add_div _ omega0_ne_zero, div_eq_zero_of_lt (natCast_lt_omega0 _),
    add_zero] at this
  exact ⟨by rw [this], rfl⟩

end Block

/-- A self-visible label is fixed by visibility replacement at its threshold, with any value. -/
theorem IsSelfVisible.visibilityReplace_eq (h : IsSelfVisible k x) (i : ℕ) :
    visibilityReplace k i x = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o => simpa using Ordinal.visibilityReplace_of_le (isSelfVisible_coe.mp h) i
  | top => rfl

/-- Every ordinal is `μ + j` with `μ` zero or a limit and `j` finite: `μ = ω * (o / ω)` and
`j = o % ω`. -/
theorem exists_eq_add_natCast_isSuccPrelimit (o : Ordinal.{u}) :
    ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ j : ℕ, o = μ + j := by
  obtain ⟨j, hj⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
  exact ⟨ω * (o / ω), isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _), j, by
    rw [← hj, div_add_mod]⟩

/-- **Visibility replacement in the normal form of [Kni26, Definition 2.2.3]**: for `μ` zero or a
limit and `j` finite, replacement at threshold `K` with value `m` sends `μ + j` to `μ + m` if
`j < K`, and fixes it otherwise. -/
theorem visibilityReplace_coe_add {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) (K m j : ℕ) :
    visibilityReplace K m ((μ + j : Ordinal.{u}) : Label.{u}) =
      if j < K then ((μ + m : Ordinal.{u}) : Label.{u})
      else ((μ + j : Ordinal.{u}) : Label.{u}) := by
  split_ifs with hj
  · exact visibilityReplace_coe_add_natCast hμ hj m
  · exact (isSelfVisible_coe_add hμ (not_lt.mp hj)).visibilityReplace_eq m

/-- Self-visibility at a threshold implies self-visibility at every lower threshold. -/
theorem IsSelfVisible.mono (h : IsSelfVisible k x) (hk : k' ≤ k) : IsSelfVisible k' x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o => exact isSelfVisible_coe.mpr ((Nat.cast_le.mpr hk).trans (isSelfVisible_coe.mp h))
  | top => rfl

/-- The minimum of two self-visible labels is self-visible. -/
theorem IsSelfVisible.min (hx : IsSelfVisible k x) (hy : IsSelfVisible k y) :
    IsSelfVisible k (min x y) := by
  rcases min_choice x y with h | h <;> rwa [h]

/-- The maximum of two self-visible labels is self-visible. -/
theorem IsSelfVisible.max (hx : IsSelfVisible k x) (hy : IsSelfVisible k y) :
    IsSelfVisible k (max x y) := by
  rcases max_choice x y with h | h <;> rwa [h]

/-- Stage reduction preserves self-visibility. -/
theorem IsSelfVisible.reduce (h : IsSelfVisible k x) (α : Ordinal.{u}) :
    IsSelfVisible k (reduce α x) := by
  by_cases hx : x < α
  · rwa [reduce_of_lt hx]
  · rw [reduce_of_le (not_lt.mp hx)]; rfl

/-- Visibility replacement with value `i ≤ k` cannot push a label above a bound that is
self-visible at `k`. -/
theorem visibilityReplace_le_of_le (hi : i ≤ k) (hy : IsSelfVisible k y) (h : x ≤ y) :
    visibilityReplace k i x ≤ y :=
  (monotone_visibilityReplace hi h).trans_eq (hy.visibilityReplace_eq i)

/-- A label above a bound self-visible at `k` stays above it after visibility replacement at `k`
with any value `i ≤ k`. -/
theorem lt_visibilityReplace_of_lt {k i : ℕ} {δ y : Label.{u}} (hi : i ≤ k)
    (hδ : IsSelfVisible k δ) (hy : δ < y) : δ < visibilityReplace k i y := by
  by_contra hle
  rw [not_lt] at hle
  have h := visibilityReplace_le_of_le le_rfl hδ hle
  rw [visibilityReplace_self_visibilityReplace hi] at h
  exact hy.not_ge ((le_visibilityReplace (by omega) y).trans h)

/-- Capping by a label self-visible at `k` commutes with visibility replacement at `k`. -/
theorem visibilityReplace_min_of_isSelfVisible (hi : i ≤ k) (hc : IsSelfVisible k c)
    (x : Label.{u}) :
    visibilityReplace k i (min x c) = min (visibilityReplace k i x) c := by
  rw [visibilityReplace_min hi, hc.visibilityReplace_eq]

/-- Finitely many labels, together with a label `b` below a stage `α` that is zero or a limit,
have a common upper bound below `α` that is self-visible at a given threshold `n`: every one of
the labels that lies below `α` lies below it. -/
theorem exists_isSelfVisible_bound {ι : Type*} [Finite ι] (hα : Order.IsSuccPrelimit α) (n : ℕ)
    {b : Label.{u}} (hb : b < α) (f : ι → Label.{u}) :
    ∃ c, b ≤ c ∧ c < α ∧ IsSelfVisible n c ∧ ∀ t, f t < α → f t ≤ c := by
  have := Fintype.ofFinite ι
  set s := max b (Finset.univ.sup fun t ↦ if f t < α then f t else ⊥)
  have hs : s < α := max_lt hb ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun t _ ↦ by
    split_ifs with h
    exacts [h, WithBot.bot_lt_coe _])
  have hsc : s ≤ visibilityReplace n n s := le_visibilityReplace (by omega) s
  refine ⟨_, (le_max_left _ _).trans hsc, (visibilityReplace_lt_iff hα).mpr hs,
    visibilityReplace_self_visibilityReplace le_rfl s, fun t ht ↦ ?_⟩
  refine le_trans ?_ ((le_max_right _ _).trans hsc)
  simpa [ht] using Finset.le_sup (f := fun t ↦ if f t < α then f t else ⊥) (Finset.mem_univ t)

section

variable {β : Ordinal.{u}}

/-- **Self-visible caps.**  Between an ordinal `o` and a stage `β > o` that is zero or a limit
there is an ordinal self-visible at any given threshold `k`: `o + (k + 1)`. -/
theorem exists_lt_lt_isSelfVisible (hβ : Order.IsSuccPrelimit β) (ho : o < β) (k : ℕ) :
    ∃ c : Ordinal.{u}, o < c ∧ c < β ∧ IsSelfVisible k (c : Label.{u}) := by
  refine ⟨o + (k + 1 : ℕ), ?_, hβ.add_natCast_lt ho _, isSelfVisible_coe.mpr ?_⟩
  · exact lt_add_of_pos_right o (by exact_mod_cast k.succ_pos)
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt o Ordinal.omega0_ne_zero)
  have hdecomp : o + (k + 1 : ℕ) = Ordinal.omega0 * (o / Ordinal.omega0) + (m + (k + 1) : ℕ) := by
    conv_lhs => rw [← Ordinal.div_add_mod o Ordinal.omega0]
    rw [hm, add_assoc]
    norm_cast
  rw [hdecomp, Ordinal.mul_add_mod_self, Ordinal.natCast_mod_omega0]
  exact_mod_cast (by omega : k ≤ m + (k + 1))

end

/-! ### Labels of the form `ω * q + n` -/

/-- Visibility replacement on a label `ω * q + n` replaces the finite part `n` when `n < k`. -/
theorem visibilityReplace_block (q : Ordinal.{u}) (n k i : ℕ) :
    visibilityReplace k i ((ω * q + n : Ordinal.{u}) : Label.{u}) =
      ((ω * q + ((if n < k then i else n : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  rw [visibilityReplace_coe, Ordinal.visibilityReplace, mul_add_div _ omega0_ne_zero,
    div_eq_zero_of_lt (natCast_lt_omega0 n), add_zero, mul_add_mod_self,
    mod_eq_of_lt (natCast_lt_omega0 n)]
  split_ifs <;> simp_all

/-- A label `ω * q + n` is self-visible at `k` exactly when `k ≤ n`. -/
theorem isSelfVisible_block {q : Ordinal.{u}} {n k : ℕ} :
    IsSelfVisible k ((ω * q + n : Ordinal.{u}) : Label.{u}) ↔ k ≤ n := by
  rw [isSelfVisible_coe, mul_add_mod_self, mod_eq_of_lt (natCast_lt_omega0 n), Nat.cast_le]

/-- A label self-visible at `1` is fixed by visibility replacement at `2` with value `1`. -/
theorem visibilityReplace_two_one_of_isSelfVisible {a : Label.{u}} (ha : IsSelfVisible 1 a) :
    visibilityReplace 2 1 a = a := by
  by_cases hb : a = ⊥
  · rw [hb]; simp
  by_cases ht : a = ⊤
  · rw [ht]; simp
  obtain ⟨b, n, rfl⟩ := exists_block hb ht
  have hn : 1 ≤ n := isSelfVisible_block.mp ha
  have hif : (if n < 2 then 1 else n) = n := by split_ifs <;> omega
  rw [visibilityReplace_block, hif]

/-- **One step above a label of finite part `1`**: if `a` is self-visible at `1` and `a < b`,
then `visibilityReplace 2 2 a ≤ b`. -/
theorem visibilityReplace_two_two_le_of_lt {a b : Label.{u}} (ha : IsSelfVisible 1 a)
    (hab : a < b) :
    visibilityReplace 2 2 a ≤ b := by
  by_cases ha2 : IsSelfVisible 2 a
  · rw [ha2]; exact hab.le
  have hb : a ≠ ⊥ := fun h ↦ ha2 (h ▸ isSelfVisible_bot 2)
  have ht : a ≠ ⊤ := fun h ↦ ha2 (h ▸ isSelfVisible_top 2)
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  have hn1 : 1 ≤ n := isSelfVisible_block.mp ha
  have hn2 : ¬ 2 ≤ n := fun h ↦ ha2 (isSelfVisible_block.mpr h)
  obtain rfl : n = 1 := by omega
  rw [visibilityReplace_block, ite_eq_left (by omega)]
  induction b using recBotCoeTop with
  | bot => exact absurd hab (not_lt.mpr bot_le)
  | top => exact le_top
  | coe o =>
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe] at hab
    rw [WithBot.coe_le_coe, WithTop.coe_le_coe]
    have := Order.add_one_le_of_lt hab
    rw [add_assoc] at this
    simpa [one_add_one_eq_two] using this

/-! ### Labels below a cap self-visible at `3` -/

/-- Visibility replacement at `3` with value `1` gives a label self-visible at `1`. -/
theorem isSelfVisible_visibilityReplace_three_one (x : Label.{u}) :
    IsSelfVisible 1 (visibilityReplace 3 1 x) := by
  by_cases hb : x = ⊥
  · rw [hb, visibilityReplace_bot]; exact isSelfVisible_bot _
  by_cases ht : x = ⊤
  · rw [ht, visibilityReplace_top]; exact isSelfVisible_top _
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  rw [visibilityReplace_block, isSelfVisible_block]
  split_ifs <;> omega

/-- Visibility replacement at `3` with value `1` does not raise a label self-visible at `1`. -/
theorem visibilityReplace_three_one_le (hx : IsSelfVisible 1 x) :
    visibilityReplace 3 1 x ≤ x := by
  by_cases hb : x = ⊥
  · rw [hb, visibilityReplace_bot]
  by_cases ht : x = ⊤
  · rw [ht, visibilityReplace_top]
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  have hn : 1 ≤ n := isSelfVisible_block.mp hx
  rw [visibilityReplace_block, WithBot.coe_le_coe, WithTop.coe_le_coe]
  have hle : (if n < 3 then 1 else n) ≤ n := by split_ifs <;> omega
  exact add_le_add_right (Nat.cast_le (α := Ordinal.{u}).mpr hle) _

/-- **A cap self-visible at `3` does not separate finite parts below `3`**: a label `c`
self-visible at `3` below `y` lies below `visibilityReplace 3 1 y`. -/
theorem le_visibilityReplace_three_one (hc : IsSelfVisible 3 c) (h : c ≤ y) :
    c ≤ visibilityReplace 3 1 y :=
  (hc.visibilityReplace_eq 1).symm.le.trans (monotone_visibilityReplace (by omega) h)

/-- **A cap self-visible at `3` above a label stays above its replacement at `2`**: for `c`
self-visible at `3` and `y < c`, `visibilityReplace 3 2 y < c`.  The replacement is at most `c`
(`visibilityReplace_le_of_le`); it is `y` if `y` is self-visible at `3`, and otherwise has finite
part `2`, so it is not the label `c`, which is self-visible at `3`. -/
theorem visibilityReplace_three_two_lt (hc : IsSelfVisible 3 c) (h : y < c) :
    visibilityReplace 3 2 y < c := by
  refine (visibilityReplace_le_of_le (by omega) hc h.le).lt_of_ne fun he ↦ ?_
  by_cases hy : IsSelfVisible 3 y
  · exact h.ne ((hy.visibilityReplace_eq 2).symm.trans he)
  have hb : y ≠ ⊥ := fun h' ↦ hy (h' ▸ isSelfVisible_bot 3)
  have ht : y ≠ ⊤ := fun h' ↦ hy (h' ▸ isSelfVisible_top 3)
  obtain ⟨q, n, rfl⟩ := exists_block hb ht
  have hn : n < 3 := by
    by_contra hn
    exact hy (isSelfVisible_block.mpr (by omega))
  rw [← he, visibilityReplace_block, ite_eq_left hn, isSelfVisible_block] at hc
  omega

end VaughtConjecture.Label
