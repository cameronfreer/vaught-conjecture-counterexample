/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform

/-!
# The top shifter and the step suppressors with a constant value

Roadmap, Layer 1 (the bounded transformations used by the construction); semantic contract,
item 3.

Two elementary witness components (`IsWitness`, module `VaughtConjecture.Label.Transform`), used
to show that explicit labellings are lawful:

* the *top shifter* `topShifter`, sending `⊥` to `⊥` and every other label to `⊤`; with every
  antitone suppressor whose values are self-visible at their grades it is a witness
  (`isWitness_topShifter`);
* the *step suppressor with value `a`* `constStepSuppressor K a`, equal to `a` at the grades
  `≤ K` and `⊥` above; it is antitone (`antitone_constStepSuppressor`), and its value at each
  grade `n` is self-visible at `n` when `a` is self-visible at `K`
  (`isSelfVisible_constStepSuppressor`), so that with the top shifter it is a witness
  (`isWitness_constStepSuppressor_topShifter`).  The step suppressor `stepSuppressor K` is the
  case `a = ⊤`.  When every grade is at most `K`, the two transform a row to the labelling that
  is `a` where the row is not `⊥` and `⊥` where it is (`transformsTo_of_eq_bot_iff`);
* *raising above a cap* `h`, `raise h`, sending every label `≥ h` to `⊤` and fixing the labels
  below `h`; we say that `raise h x` is `x` *raised to `⊤` above `h`*.  It keeps `x` capped at `h`
  (`min_raise`), and when `⊥ < h` and `h` is self-visible at `K + 1` it is a witness bounded by
  the grade `K` (`isWitness_raise`): visibility replacement at a threshold `k ≤ K` with a value
  `i ≤ k` moves no label across `h` (`IsSelfVisible.le_visibilityReplace_iff`).
-/

universe u

namespace VaughtConjecture.Label

/-- The shifter sending `⊥` to `⊥` and every other label to `⊤`. -/
noncomputable def topShifter (x : Label.{u}) : Label.{u} := if x = ⊥ then ⊥ else ⊤

/-- The top shifter sends every natural number to the formal top. -/
theorem topShifter_natCast (n : ℕ) : topShifter (n : Label.{u}) = ⊤ := by
  simp [topShifter]

/-- The top shifter is a witness for every antitone suppressor whose values are self-visible at
their grades. -/
theorem isWitness_topShifter {g : ℕ → Label.{u}} (hg : Antitone g)
    (hgv : ∀ n, IsSelfVisible n (g n)) : IsWitness g topShifter where
  antitone := hg
  isSelfVisible := hgv
  map_bot := by simp [topShifter]
  monotone := by
    intro x y hxy
    unfold topShifter
    by_cases hx : x = ⊥
    · simp [hx]
    · have hy : y ≠ ⊥ := fun hy ↦ hx (le_bot_iff.mp (hy ▸ hxy))
      simp [hx, hy]
  visibilityReplace_comm x k _ i _ := by
    unfold topShifter
    by_cases hx : x = ⊥
    · simp [hx]
    · simp [hx]

/-- The suppressor equal to `a` up to the grade `K` and `⊥` above. -/
noncomputable def constStepSuppressor (K : ℕ) (a : Label.{u}) (n : ℕ) : Label.{u} :=
  if n ≤ K then a else ⊥

/-- The suppressor equal to `a` up to the grade `K` is `a` at the grades up to `K`. -/
theorem constStepSuppressor_of_le {K n : ℕ} (a : Label.{u}) (h : n ≤ K) :
    constStepSuppressor K a n = a := by
  unfold constStepSuppressor; rw [ite_eq_left h]

/-- The step suppressor with value `a` is antitone. -/
theorem antitone_constStepSuppressor (K : ℕ) (a : Label.{u}) :
    Antitone (constStepSuppressor K a) := by
  intro n m hnm
  unfold constStepSuppressor
  split_ifs with hm hn <;> first | exact le_rfl | exact bot_le | omega

/-- The step suppressor with value `a` is self-visible at each grade when `a` is self-visible
at `K`. -/
theorem isSelfVisible_constStepSuppressor {K : ℕ} {a : Label.{u}} (ha : IsSelfVisible K a)
    (n : ℕ) : IsSelfVisible n (constStepSuppressor K a n) := by
  unfold constStepSuppressor
  split_ifs with hn
  · exact ha.mono hn
  · exact isSelfVisible_bot n

/-- **The top shifter with a step suppressor**: for `a` self-visible at `K`, the step suppressor
with value `a` and the top shifter form a witness. -/
theorem isWitness_constStepSuppressor_topShifter {K : ℕ} {a : Label.{u}}
    (ha : IsSelfVisible K a) : IsWitness (constStepSuppressor K a) topShifter :=
  isWitness_topShifter (antitone_constStepSuppressor _ _) (isSelfVisible_constStepSuppressor ha)

/-- **The top shifter on a row with one nonzero kind.**  If the suppressor `Ω` is self-visible at
`K` and every grade is at most `K`, a row transforms to the labelling that is `Ω` where the row is
not `⊥` and `⊥` where it is. -/
theorem transformsTo_of_eq_bot_iff {D : Type*} (grade : D → ℕ) {K : ℕ} (hgr : ∀ d, grade d ≤ K)
    {Ω : Label.{u}} (hΩ : IsSelfVisible K Ω) (r q : D → Label.{u})
    (hq : ∀ d, q d = if r d = ⊥ then ⊥ else Ω) : TransformsTo grade r q := by
  refine ⟨constStepSuppressor K Ω, topShifter,
    isWitness_topShifter (antitone_constStepSuppressor _ _)
      (isSelfVisible_constStepSuppressor hΩ), fun d ↦ ?_⟩
  have hg : constStepSuppressor K Ω (grade d) = Ω := by
    unfold constStepSuppressor; rw [ite_eq_left (hgr d)]
  rw [hg, hq, topShifter]
  split_ifs <;> simp

open Ordinal in
/-- **Visibility replacement does not cross a label self-visible above its threshold**: for `h`
self-visible at `K + 1`, a threshold `k ≤ K` and a value `i ≤ k`, `h ≤ visibilityReplace k i x`
exactly when `h ≤ x`. -/
theorem IsSelfVisible.le_visibilityReplace_iff {K k i : ℕ} {h : Label.{u}}
    (hh : IsSelfVisible (K + 1) h) (hk : k ≤ K) (hi : i ≤ k) (x : Label.{u}) :
    h ≤ visibilityReplace k i x ↔ h ≤ x := by
  refine ⟨fun hle ↦ ?_, fun hle ↦ ?_⟩
  · induction x using recBotCoeTop with
    | bot => rwa [visibilityReplace_bot] at hle
    | top => exact le_top
    | coe o =>
      induction h using recBotCoeTop with
      | bot => exact bot_le
      | top => simp at hle
      | coe o' =>
        rw [isSelfVisible_coe] at hh
        rw [visibilityReplace_coe, WithBot.coe_le_coe, WithTop.coe_le_coe] at hle
        rw [WithBot.coe_le_coe, WithTop.coe_le_coe]
        by_cases ho : o % ω < k
        · -- The finite part of `o` is replaced by `i`, below the finite part of `o'`: so `o'`
          -- lies in an earlier block than `o`.
          rw [Ordinal.visibilityReplace_of_lt ho] at hle
          have hdiv : o' / ω < o / ω := by
            by_contra hge
            rcases (not_lt.mp hge).lt_or_eq with hlt | heq
            · refine absurd hle (not_le.mpr ?_)
              calc ω * (o / ω) + (i : Ordinal.{u}) < ω * (o / ω) + ω :=
                    (add_lt_add_iff_left _).mpr (natCast_lt_omega0 i)
                _ = ω * (o / ω + 1) := by rw [mul_add_one]
                _ ≤ ω * (o' / ω) := by gcongr; exact Order.add_one_le_of_lt hlt
                _ ≤ o' := Ordinal.mul_div_le _ _
            · have h1 : ω * (o' / ω) + o' % ω ≤ ω * (o' / ω) + i := by
                rw [Ordinal.div_add_mod, ← heq]; exact hle
              have h2 := hh.trans ((add_le_add_iff_left _).mp h1)
              exact absurd (Nat.cast_le.mp h2) (by omega)
          refine le_of_lt ?_
          calc o' < ω * (o' / ω) + ω := Ordinal.lt_mul_div_add o' omega0_ne_zero
            _ = ω * (o' / ω + 1) := by rw [mul_add_one]
            _ ≤ ω * (o / ω) := by gcongr; exact Order.add_one_le_of_lt hdiv
            _ ≤ o := Ordinal.mul_div_le _ _
        · rwa [Ordinal.visibilityReplace_of_le (not_lt.mp ho)] at hle
  · calc h = visibilityReplace k i h := ((hh.mono (by omega)).visibilityReplace_eq i).symm
      _ ≤ visibilityReplace k i x := monotone_visibilityReplace hi hle

/-- **Raising above the cap `h`**: `⊤` at the labels `≥ h`, the identity below. -/
noncomputable def raise (h x : Label.{u}) : Label.{u} := if h ≤ x then ⊤ else x

/-- Raising above a positive cap fixes `⊥`. -/
theorem raise_bot {h : Label.{u}} (hbot : ⊥ < h) : raise h ⊥ = ⊥ := by
  unfold raise; rw [ite_eq_right (not_le.mpr hbot)]

/-- Raising reflects `⊥`. -/
theorem eq_bot_of_raise_eq_bot {h x : Label.{u}} (hx : raise h x = ⊥) : x = ⊥ := by
  unfold raise at hx
  split_ifs at hx
  · exact absurd hx top_ne_bot
  · exact hx

/-- Raising above `h` does not change a label capped at `h`. -/
theorem min_raise (h x : Label.{u}) : min (raise h x) h = min x h := by
  unfold raise
  split_ifs with hx
  · rw [min_top_left, min_eq_right hx]
  · rfl

/-- Raising keeps self-visibility. -/
theorem isSelfVisible_raise {k : ℕ} (h : Label.{u}) {x : Label.{u}} (hx : IsSelfVisible k x) :
    IsSelfVisible k (raise h x) := by
  unfold raise
  split_ifs
  exacts [isSelfVisible_top _, hx]

/-- **Raising above a cap self-visible at `K + 1` is a witness bounded by the grade `K`.** -/
theorem isWitness_raise {K : ℕ} {h : Label.{u}} (hh : IsSelfVisible (K + 1) h) (hbot : ⊥ < h) :
    IsWitness (stepSuppressor K) (raise h) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := raise_bot hbot
  monotone := by
    intro x y hxy
    unfold raise
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans hxy) h2
    · exact le_top
    · exact hxy
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · unfold raise
      by_cases h1 : h ≤ x
      · rw [ite_eq_left ((hh.le_visibilityReplace_iff hk hi x).mpr h1), ite_eq_left h1,
          visibilityReplace_top]
      · rw [ite_eq_right fun h2 ↦ h1 ((hh.le_visibilityReplace_iff hk hi x).mp h2),
          ite_eq_right h1]
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      rw [eq_bot_of_raise_eq_bot hx, visibilityReplace_bot, raise_bot hbot, visibilityReplace_bot]

end VaughtConjecture.Label
