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
  second one (`exists_visibilityReplace_visibilityReplace`).
* At a stage `α` that is zero or a limit, `α + K` is self-visible at every `k ≤ K`
  (`isSelfVisible_coe_add`); a label at least `α` and self-visible at `n` is at least `α + n`
  (`coe_add_le_of_isSelfVisible`), since `α` is a multiple of `ω`; replacement with a value
  `i ≤ K` keeps a label at most `α + K` at most `α + K` (`visibilityReplace_le_coe_add`); finitely
  many labels below `α` have a common bound below `α` that is self-visible at a given threshold
  (`exists_isSelfVisible_bound`), and between an ordinal `o` and a stage `β > o` that is zero or
  a limit there is an ordinal self-visible at any given threshold (`exists_lt_lt_isSelfVisible`).
* In the block `[μ, μ + ω)` of an ordinal `μ` that is zero or a limit, an ordinal `μ + k` whose
  finite part `k` is below the threshold `n` is not self-visible at `n`
  (`not_isSelfVisible_coe_add_natCast`), and replacement at `n` with value `i` gives `μ + i`
  (`visibilityReplace_coe_add_natCast`).
* On a natural number `n` it gives `i` if `n < k` and `n` otherwise (`visibilityReplace_natCast`,
  with `visibilityReplace_zero`, `visibilityReplace_one`, `visibilityReplace_ofNat` for numerals).

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

end Block

/-- A self-visible label is fixed by visibility replacement at its threshold, with any value. -/
theorem IsSelfVisible.visibilityReplace_eq (h : IsSelfVisible k x) (i : ℕ) :
    visibilityReplace k i x = x := by
  induction x using recBotCoeTop with
  | bot => rfl
  | coe o => simpa using Ordinal.visibilityReplace_of_le (isSelfVisible_coe.mp h) i
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

end VaughtConjecture.Label
