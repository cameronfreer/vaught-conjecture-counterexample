/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import VaughtConjecture.Label.Basic

/-!
# Visibility replacement

Roadmap, Layer 1 (visibility replacement); semantic contract, item 3 (the visibility
replacement maps and the special bottom/top values).

Every ordinal `o` is uniquely `ω * (o / ω) + o % ω` with `o % ω < ω`; the summand `o % ω` is its
*finite part*, and the ordinals sharing `o / ω` form the *band* `[ω * (o / ω), ω * (o / ω) + ω)`
of `o`.  Visibility replacement at threshold `k` with value `i` replaces the finite part of `o` by
`i` when that finite part is below `k`, and leaves `o` unchanged otherwise
(`replaceFinitePart`).  On labels (`visibilityReplace k i`) it fixes the bottom label and the
formal top.  A label is *self-visible* at `k` (`IsSelfVisible k x`) if visibility replacement at
threshold `k` with value `k` fixes it; for an ordinal this says that its finite part is at least
`k` (`isSelfVisible_coe`), and for a natural number `n` that `k ≤ n` (`isSelfVisible_natCast`).

* Visibility replacement stays in the band of its argument (`omega0_mul_div_le_replaceFinitePart`,
  `replaceFinitePart_lt`), so it commutes with stage reduction at every stage `α` that is zero or a
  limit (`reduce_visibilityReplace`).
* For `i ≤ k` it is monotone (`monotone_visibilityReplace`), hence commutes with `min` and `max`,
  and it cannot push a label above a self-visible bound (`visibilityReplace_le_of_le`).
* Replacing again at the full threshold forgets the first value
  (`visibilityReplace_self_visibilityReplace`).
-/

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {α o o' : Ordinal.{u}} {k k' i : ℕ} {x y c : Label.{u}}

/-! ### Bands of ordinals -/

/-- The quotient of `b * a + r` by `b`, for `r < b`. -/
private theorem mul_add_div_of_lt {b r : Ordinal.{u}} (a : Ordinal.{u}) (hr : r < b) :
    (b * a + r) / b = a := by
  rw [Ordinal.mul_add_div _ hr.ne_bot, Ordinal.div_eq_zero_of_lt hr, add_zero]

/-- The remainder of `b * a + r` modulo `b`, for `r < b`. -/
private theorem mul_add_mod_of_lt {b r : Ordinal.{u}} (a : Ordinal.{u}) (hr : r < b) :
    (b * a + r) % b = r := by
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-- At a stage that is zero or a limit (a multiple of `ω`), a band lies entirely below the stage
or entirely at or above it. -/
theorem lt_iff_of_mem_band {a y : Ordinal.{u}} (hα : Order.IsSuccPrelimit α) (hy₀ : ω * a ≤ y)
    (hy : y < ω * a + ω) : y < α ↔ ω * a < α := by
  obtain ⟨b, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hα
  refine ⟨hy₀.trans_lt, fun h ↦ hy.trans_le ?_⟩
  rw [← Ordinal.mul_succ]
  exact mul_le_mul_right (Order.succ_le_of_lt ((mul_lt_mul_iff_right₀ omega0_pos).mp h)) _

/-! ### Visibility replacement of ordinals -/

open Classical in
/-- Visibility replacement of an ordinal at threshold `k` with value `i`: the finite part
`o % ω` is replaced by `i` if it is below `k`, and kept otherwise. -/
noncomputable def replaceFinitePart (k i : ℕ) (o : Ordinal.{u}) : Ordinal.{u} :=
  ω * (o / ω) + if o % ω < k then (i : Ordinal.{u}) else o % ω

/-- Below the threshold, the finite part is replaced. -/
theorem replaceFinitePart_of_lt (h : o % ω < k) (i : ℕ) :
    replaceFinitePart k i o = ω * (o / ω) + i := by
  simp [replaceFinitePart, h]

/-- At or above the threshold, the ordinal is unchanged. -/
theorem replaceFinitePart_of_le (h : (k : Ordinal.{u}) ≤ o % ω) (i : ℕ) :
    replaceFinitePart k i o = o := by
  simp [replaceFinitePart, h.not_gt, Ordinal.div_add_mod]

/-- The replaced value of the finite part is finite. -/
private theorem ite_lt_omega0 (k i : ℕ) (o : Ordinal.{u}) :
    (if o % ω < k then (i : Ordinal.{u}) else o % ω) < ω := by
  split_ifs
  · exact natCast_lt_omega0 i
  · exact Ordinal.mod_lt _ omega0_ne_zero

/-- Visibility replacement does not leave the band: lower end. -/
theorem omega0_mul_div_le_replaceFinitePart (k i : ℕ) (o : Ordinal.{u}) :
    ω * (o / ω) ≤ replaceFinitePart k i o :=
  le_self_add

/-- Visibility replacement does not leave the band: upper end. -/
theorem replaceFinitePart_lt (k i : ℕ) (o : Ordinal.{u}) :
    replaceFinitePart k i o < ω * (o / ω) + ω :=
  add_lt_add_right (ite_lt_omega0 k i o) _

/-- Visibility replacement keeps the quotient by `ω`. -/
theorem replaceFinitePart_div (k i : ℕ) (o : Ordinal.{u}) :
    replaceFinitePart k i o / ω = o / ω :=
  mul_add_div_of_lt _ (ite_lt_omega0 k i o)

/-- The finite part after visibility replacement. -/
theorem replaceFinitePart_mod (k i : ℕ) (o : Ordinal.{u}) :
    replaceFinitePart k i o % ω = if o % ω < k then (i : Ordinal.{u}) else o % ω :=
  mul_add_mod_of_lt _ (ite_lt_omega0 k i o)

/-- At a stage that is zero or a limit, visibility replacement keeps an ordinal below the stage
exactly when it was below. -/
theorem replaceFinitePart_lt_iff (hα : Order.IsSuccPrelimit α) (k i : ℕ) :
    replaceFinitePart k i o < α ↔ o < α := by
  rw [lt_iff_of_mem_band hα (omega0_mul_div_le_replaceFinitePart k i o)
      (replaceFinitePart_lt k i o),
    lt_iff_of_mem_band hα (Ordinal.mul_div_le o ω) (Ordinal.lt_mul_div_add o omega0_ne_zero)]

/-- On the finite ordinals visibility replacement replaces the ordinal itself. -/
theorem replaceFinitePart_of_lt_omega0 (ho : o < ω) (k i : ℕ) :
    replaceFinitePart k i o = if o < k then (i : Ordinal.{u}) else o := by
  simp [replaceFinitePart, Ordinal.div_eq_zero_of_lt ho, Ordinal.mod_eq_of_lt ho]

/-- Visibility replacement is monotone when the new value does not exceed the threshold. -/
theorem monotone_replaceFinitePart (hi : i ≤ k) :
    Monotone (replaceFinitePart k i : Ordinal.{u} → Ordinal.{u}) := by
  intro o o' h
  rcases (Ordinal.div_le_left h ω).lt_or_eq with hlt | heq
  · refine (replaceFinitePart_lt k i o).le.trans ?_
    rw [← Ordinal.mul_succ]
    exact (mul_le_mul_right (Order.succ_le_of_lt hlt) _).trans
      (omega0_mul_div_le_replaceFinitePart k i o')
  · have hmod : o % ω ≤ o' % ω := by
      have := Ordinal.div_add_mod o ω ▸ Ordinal.div_add_mod o' ω ▸ h
      rwa [heq, add_le_add_iff_left] at this
    have hik : (i : Ordinal.{u}) ≤ k := by exact_mod_cast hi
    unfold replaceFinitePart
    rw [heq]
    refine add_le_add_right ?_ _
    split_ifs with h₁ h₂ h₂
    · exact le_rfl
    · exact hik.trans (not_lt.mp h₂)
    · exact absurd (hmod.trans_lt h₂) h₁
    · exact hmod

/-- Replacing again at the full threshold forgets an earlier value `i ≤ k`. -/
theorem replaceFinitePart_self_replaceFinitePart (hi : i ≤ k) (o : Ordinal.{u}) :
    replaceFinitePart k k (replaceFinitePart k i o) = replaceFinitePart k k o := by
  have hik : (i : Ordinal.{u}) ≤ k := by exact_mod_cast hi
  conv_lhs => rw [replaceFinitePart, replaceFinitePart_div, replaceFinitePart_mod]
  rw [replaceFinitePart]
  by_cases hm : o % ω < k
  · by_cases hk : (i : Ordinal.{u}) < k
    · simp [hm, hk]
    · simp [hm, le_antisymm hik (not_lt.mp hk)]
  · simp [hm]

/-- An ordinal lies below its visibility replacement when the new value is at least one below
the threshold. -/
theorem le_replaceFinitePart (h : k ≤ i + 1) (o : Ordinal.{u}) : o ≤ replaceFinitePart k i o := by
  by_cases hk : o % ω < k
  · rw [replaceFinitePart_of_lt hk]
    conv_lhs => rw [← Ordinal.div_add_mod o ω]
    refine (add_le_add_iff_left _).mpr ?_
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt o omega0_ne_zero)
    rw [hn] at hk ⊢
    exact_mod_cast Nat.lt_succ_iff.mp ((Nat.cast_lt.mp hk).trans_le h)
  · exact (replaceFinitePart_of_le (not_lt.mp hk) i).ge

/-! ### Visibility replacement of labels -/

/-- Visibility replacement of labels at threshold `k` with value `i`: bottom and the formal top
are fixed, and an ordinal label is replaced by `replaceFinitePart k i`. -/
noncomputable def visibilityReplace (k i : ℕ) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map (replaceFinitePart k i))

/-- Visibility replacement fixes the bottom label. -/
@[simp] theorem visibilityReplace_bot (k i : ℕ) : visibilityReplace k i (⊥ : Label.{u}) = ⊥ := rfl

/-- Visibility replacement fixes the formal top. -/
@[simp] theorem visibilityReplace_top (k i : ℕ) : visibilityReplace k i (⊤ : Label.{u}) = ⊤ := rfl

/-- Visibility replacement of an ordinal label is visibility replacement of the ordinal. -/
@[simp] theorem visibilityReplace_coe (k i : ℕ) (o : Ordinal.{u}) :
    visibilityReplace k i (o : Label.{u}) = (replaceFinitePart k i o : Label.{u}) := rfl

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
  (monotone_replaceFinitePart hi).withTop_map.withBot_map

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
  | coe o => simpa using replaceFinitePart_lt_iff hα k i
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
  | coe o => simp [replaceFinitePart_self_replaceFinitePart hi]
  | top => rfl

/-- A label lies below its visibility replacement when the new value is at least one below the
threshold (in particular for `i = k`). -/
theorem le_visibilityReplace (h : k ≤ i + 1) (x : Label.{u}) : x ≤ visibilityReplace k i x := by
  induction x using recBotCoeTop with
  | bot => exact le_rfl
  | coe o => simpa using le_replaceFinitePart h o
  | top => exact le_rfl

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

/-- An ordinal label is self-visible at `k` exactly when its finite part is at least `k`. -/
@[simp, grind =] theorem isSelfVisible_coe :
    IsSelfVisible k (o : Label.{u}) ↔ (k : Ordinal.{u}) ≤ o % ω := by
  refine ⟨fun h ↦ not_lt.mp fun hk ↦ ?_, fun h ↦ by simp [IsSelfVisible, replaceFinitePart_of_le h]⟩
  have h' : replaceFinitePart k k o = o := by simpa [IsSelfVisible] using h
  have := congrArg (· % ω) h'
  simp only [replaceFinitePart_mod, hk, ite_true] at this
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

/-- A self-visible label is fixed by visibility replacement at its threshold, with any value. -/
theorem IsSelfVisible.visibilityReplace_eq (h : IsSelfVisible k x) (i : ℕ) :
    visibilityReplace k i x = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o => simpa using replaceFinitePart_of_le (isSelfVisible_coe.mp h) i
  | top => rfl

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

/-- Capping by a label self-visible at `k` commutes with visibility replacement at `k`. -/
theorem visibilityReplace_min_of_isSelfVisible (hi : i ≤ k) (hc : IsSelfVisible k c)
    (x : Label.{u}) :
    visibilityReplace k i (min x c) = min (visibilityReplace k i x) c := by
  rw [visibilityReplace_min hi, hc.visibilityReplace_eq]

end VaughtConjecture.Label
