/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Labels: ordinals with a bottom and a formal top

Roadmap, Layer 1 (extended-ordinal labels); semantic contract, item 3 ("Labels and rows"); the
expositions, §1.  A **label** is a point of `{-∞} ∪ Ordinal ∪ {∞}`.  It is represented by
Mathlib's `WithBot (WithTop Ordinal)`, whose order, lattice operations, and bounded-order
structure are used unchanged: `⊥` is the bottom label `-∞`, `⊤` is the formal top `∞`, and an
ordinal `o` is the label `((o : WithTop Ordinal) : Label)`, written `(o : Label)`.

Four kinds of label are distinguished.  The bottom label lies strictly below ordinal zero
(Mathlib's `WithBot.bot_lt_coe`); ordinal zero is the least label that is not bottom
(`WithBot.coe_bot_le`), so the only label below it is bottom (`WithBot.lt_coe_bot`); a *proper*
label is an ordinal (`IsProper`); the formal top is not an ordinal and lies above all of them.

* `AtStage α x`: the label `x` occurs at stage `α`, that is, `x` is `⊥`, an ordinal `< α`, or `⊤`
  (expositions, §1: labels at stage `α` lie in `{-∞} ∪ α ∪ {∞}`).  The labels at a stage are
  closed under `min` (`AtStage.min`), and finitely many labels lie at a common stage that is zero
  or a limit (`exists_isSuccPrelimit_forall_atStage`).
* `reduce α x`: stage reduction of a single label to stage `α`.  Labels `< α` are kept and every
  other label becomes the formal top; this is the label-level content of the reduction of a
  stage type to a lower stage.  Its image is exactly the labels at stage `α`
  (`reduce_eq_self_iff`), and reductions compose (`reduce_reduce_of_le`).  At a successor stage
  `o + 1` it keeps exactly the labels `≤ o` (`reduce_add_one_of_le`, `reduce_add_one_of_lt`).

Stage reduction is not capped observation (`VaughtConjecture.Label.Cap`): reduction keeps the
formal top, while a cap at a proper cutoff forgets it.

The cast of a natural number `n` to a label is the label of the ordinal `n` (`natCast_label`);
these casts are injective and order-preserving, lie below `ω` (so below `ω ^ 2`,
`natCast_label_lt_omega0_sq`) and above `⊥`, and are the only labels other than `⊥` below `ω`
(`exists_natCast_of_lt_omega`).  Every ordinal is `ω * b + n` with `n` a natural number
(`exists_eq_omega0_mul_add_natCast`).

If there are countably many ordinals below `α`, there are countably many labels at stage `α`
(`countable_setOf_atStage`); in particular the labels below `ω ^ 2` form a countable set
(`countable_setOf_lt_omega0_sq`).

## Implementation notes

The numerals `0`, `1`, `2`, … and the casts `(n : Label)` of natural numbers have their own
`simp` lemmas (`isProper_natCast`, `atStage_ofNat`, and so on), so `simp` reduces the predicates
of this file and of `VaughtConjecture.Label.Cap` and `VaughtConjecture.Label.Visibility` on
them to a comparison of ordinals (of natural numbers for `IsSelfVisible` and
`visibilityReplace`, which `simp` then decides; a comparison such as `3 < 5` between ordinal
numerals needs `exact_mod_cast`).  The spelling `((n : Ordinal) : Label)` is normalized by
`simp [WithBot.coe_natCast]`; `WithBot.coe_natCast` is not a `simp` lemma in the pinned Mathlib.
-/

universe u

namespace VaughtConjecture

/-- The labels: the bottom label `⊥`, the ordinals, and the formal top `⊤`, ordered with `⊥`
least and `⊤` greatest.  The formal top is not an ordinal. -/
abbrev Label : Type (u + 1) := WithBot (WithTop Ordinal.{u})

namespace Label

variable {α β o : Ordinal.{u}} {x y : Label.{u}}

/-- Recursion on labels by the three kinds: bottom, an ordinal, and the formal top. -/
@[elab_as_elim]
def recBotCoeTop {motive : Label.{u} → Sort*} (bot : motive ⊥)
    (coe : ∀ o : Ordinal.{u}, motive o) (top : motive ⊤) : ∀ x, motive x
  | ⊥ => bot
  | some ⊤ => top
  | some (some o) => coe o

/-! ### Proper labels -/

/-- A label is *proper* if it is an ordinal, that is, neither bottom nor the formal top. -/
def IsProper (x : Label.{u}) : Prop := ∃ o : Ordinal.{u}, (o : Label.{u}) = x

/-- Every ordinal label is proper. -/
@[simp, grind .] theorem isProper_coe (o : Ordinal.{u}) : IsProper (o : Label.{u}) := ⟨o, rfl⟩

/-- The bottom label is not proper. -/
@[simp] theorem not_isProper_bot : ¬ IsProper (⊥ : Label.{u}) := fun ⟨_, h⟩ ↦ by simp at h

/-- The formal top is not proper. -/
@[simp] theorem not_isProper_top : ¬ IsProper (⊤ : Label.{u}) := fun ⟨_, h⟩ ↦ by simp at h

/-- Ordinal zero is proper. -/
@[simp] theorem isProper_zero : IsProper (0 : Label.{u}) := isProper_coe 0

/-- The ordinal `1` is proper. -/
@[simp] theorem isProper_one : IsProper (1 : Label.{u}) := isProper_coe 1

/-- Every natural number is proper. -/
@[simp] theorem isProper_natCast (n : ℕ) : IsProper (n : Label.{u}) := isProper_coe n

/-- Every numeral is proper. -/
@[simp] theorem isProper_ofNat (n : ℕ) [n.AtLeastTwo] : IsProper (ofNat(n) : Label.{u}) :=
  isProper_natCast n

/-- A label is proper exactly when it is neither bottom nor the formal top. -/
theorem isProper_iff_ne : IsProper x ↔ x ≠ ⊥ ∧ x ≠ ⊤ := by
  induction x using recBotCoeTop <;> simp

/-! ### Labels at a stage -/

/-- The label `x` *occurs at stage* `α`: it is below the ordinal `α` (bottom included) or it is
the formal top.  These are the labels `{-∞} ∪ α ∪ {∞}` of a stage type at stage `α`. -/
def AtStage (α : Ordinal.{u}) (x : Label.{u}) : Prop := x < α ∨ x = ⊤

/-- The bottom label occurs at every stage, including stage zero. -/
@[simp, grind .] theorem atStage_bot : AtStage α ⊥ := .inl (WithBot.bot_lt_coe _)

/-- The formal top occurs at every stage. -/
@[simp, grind .] theorem atStage_top : AtStage α ⊤ := .inr rfl

/-- An ordinal label occurs at stage `α` exactly when it is below `α`. -/
@[simp, grind =] theorem atStage_coe : AtStage α (o : Label.{u}) ↔ o < α := by
  simp [AtStage]

/-- Ordinal zero occurs at stage `α` exactly when `α` is positive. -/
@[simp] theorem atStage_zero : AtStage α (0 : Label.{u}) ↔ 0 < α := atStage_coe

/-- The ordinal `1` occurs at stage `α` exactly when `1 < α`. -/
@[simp] theorem atStage_one : AtStage α (1 : Label.{u}) ↔ 1 < α := atStage_coe

/-- A natural number `n` occurs at stage `α` exactly when `n < α`. -/
@[simp] theorem atStage_natCast (n : ℕ) : AtStage α (n : Label.{u}) ↔ (n : Ordinal.{u}) < α :=
  atStage_coe

/-- A numeral `n` occurs at stage `α` exactly when `n < α`. -/
@[simp] theorem atStage_ofNat (n : ℕ) [n.AtLeastTwo] :
    AtStage α (ofNat(n) : Label.{u}) ↔ (ofNat(n) : Ordinal.{u}) < α :=
  atStage_natCast n

/-- The labels at stage `α`: bottom, an ordinal below `α`, or the formal top. -/
theorem atStage_iff : AtStage α x ↔ x = ⊥ ∨ (∃ o < α, (o : Label.{u}) = x) ∨ x = ⊤ := by
  induction x using recBotCoeTop <;> simp

/-- At stage zero the only labels are bottom and the formal top. -/
theorem atStage_zero_iff : AtStage 0 x ↔ x = ⊥ ∨ x = ⊤ := by
  induction x using recBotCoeTop <;> simp

/-- A label at a stage also occurs at every higher stage. -/
theorem AtStage.mono (h : AtStage α x) (hαβ : α ≤ β) : AtStage β x :=
  h.imp_left (·.trans_le (by simpa using hαβ))

/-- The minimum of two labels at a stage is at that stage. -/
theorem AtStage.min {x y : Label.{u}} (hx : AtStage α x) (hy : AtStage α y) :
    AtStage α (min x y) := by
  rcases min_choice x y with h | h <;> rwa [h]

/-- Finitely many labels lie at a common stage that is zero or a limit. -/
theorem exists_isSuccPrelimit_forall_atStage {S : Set Label.{u}} (hS : S.Finite) :
    ∃ θ : Ordinal.{u}, Order.IsSuccPrelimit θ ∧ ∀ x ∈ S, AtStage θ x := by
  let f : Label.{u} → Ordinal.{u} := fun x ↦ WithTop.untopD 0 (WithBot.unbotD ⊤ x)
  obtain ⟨s, hs⟩ := (hS.image f).bddAbove
  refine ⟨Ordinal.omega0 * (s + 1),
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _), fun x hx ↦ ?_⟩
  induction x using recBotCoeTop with
  | bot => exact atStage_bot
  | top => exact atStage_top
  | coe o =>
    have ho : o ≤ s := by simpa [f] using hs ⟨_, hx, rfl⟩
    exact atStage_coe.mpr ((Order.lt_add_one_iff.mpr ho).trans_le
      (Ordinal.le_mul_right _ Ordinal.omega0_pos))

/-! ### Stage reduction -/

open Classical in
/-- Stage reduction of a label to stage `α`: labels below the ordinal `α` are kept, and every
other label (the ordinals `≥ α` and the formal top) becomes the formal top. -/
noncomputable def reduce (α : Ordinal.{u}) (x : Label.{u}) : Label.{u} :=
  if x < α then x else ⊤

/-- Stage reduction keeps a label below the stage. -/
@[simp] theorem reduce_of_lt (h : x < α) : reduce α x = x := ite_eq_left h

/-- Stage reduction sends a label at or above the stage to the formal top. -/
@[simp] theorem reduce_of_le (h : (α : Label.{u}) ≤ x) : reduce α x = ⊤ := ite_eq_right h.not_gt

/-- Stage reduction fixes the bottom label. -/
theorem reduce_bot : reduce α (⊥ : Label.{u}) = ⊥ := reduce_of_lt (WithBot.bot_lt_coe _)

/-- Stage reduction fixes the formal top. -/
theorem reduce_top : reduce α (⊤ : Label.{u}) = ⊤ := reduce_of_le le_top

/-- Stage reduction of an ordinal label: the ordinal is kept when it is below the stage, and
becomes the formal top otherwise. -/
theorem reduce_coe_eq_ite (β o : Ordinal.{u}) :
    reduce β (o : Label.{u}) = if o < β then (o : Label.{u}) else ⊤ := by
  split_ifs with h
  · exact reduce_of_lt (by exact_mod_cast h)
  · exact reduce_of_le (by exact_mod_cast not_lt.mp h)

/-- Stage reduction never lowers a label. -/
theorem le_reduce (α : Ordinal.{u}) (x : Label.{u}) : x ≤ reduce α x := by
  unfold reduce; split_ifs <;> simp

/-- Stage reduction is monotone. -/
theorem monotone_reduce (α : Ordinal.{u}) : Monotone (reduce α) := by
  intro x y hxy
  by_cases hy : y < α
  · rw [reduce_of_lt (hxy.trans_lt hy), reduce_of_lt hy]; exact hxy
  · rw [reduce_of_le (not_lt.mp hy)]; exact le_top

/-- A reduced label lies at the stage of the reduction. -/
@[simp] theorem atStage_reduce (α : Ordinal.{u}) (x : Label.{u}) : AtStage α (reduce α x) := by
  unfold reduce; split_ifs with h
  · exact .inl h
  · exact atStage_top

/-- Stage reduction fixes exactly the labels at its stage. -/
theorem reduce_eq_self_iff : reduce α x = x ↔ AtStage α x := by
  refine ⟨fun h ↦ h ▸ atStage_reduce α x, ?_⟩
  rintro (h | rfl)
  · exact reduce_of_lt h
  · exact reduce_top

/-- Stage reduction fixes a label at its stage. -/
theorem AtStage.reduce_eq (h : AtStage α x) : reduce α x = x := reduce_eq_self_iff.mpr h

/-- A label reduces to the formal top exactly when it is at least the stage. -/
theorem reduce_eq_top_iff : reduce α x = ⊤ ↔ (α : Label.{u}) ≤ x := by
  refine ⟨fun h ↦ ?_, reduce_of_le⟩
  by_contra hlt
  rw [reduce_of_lt (not_le.mp hlt)] at h
  exact hlt (h ▸ le_top)

/-- Stage reduction preserves and reflects the bottom label. -/
@[simp] theorem reduce_eq_bot_iff : reduce α x = ⊥ ↔ x = ⊥ := by
  refine ⟨fun h ↦ le_bot_iff.mp (h ▸ le_reduce α x), ?_⟩
  rintro rfl
  exact reduce_bot

/-- A reduced label is below the stage exactly when the original label is. -/
@[simp] theorem reduce_lt_iff : reduce α x < α ↔ x < α := by
  by_cases h : x < α
  · simp [h]
  · simp [reduce_of_le (not_lt.mp h), h]

/-- Reductions compose: reducing to `α` and then to a lower stage `β` is reducing to `β`. -/
theorem reduce_reduce_of_le (h : β ≤ α) (x : Label.{u}) :
    reduce β (reduce α x) = reduce β x := by
  by_cases hx : x < α
  · rw [reduce_of_lt hx]
  · have hβ : (β : Label.{u}) ≤ x := (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)).trans
      (not_lt.mp hx)
    rw [reduce_of_le (not_lt.mp hx), reduce_top, reduce_of_le hβ]

/-- Reducing to a stage `α` a label already reduced to a lower stage `β` does not change it. -/
theorem reduce_reduce_of_ge (h : β ≤ α) (x : Label.{u}) :
    reduce α (reduce β x) = reduce β x :=
  ((atStage_reduce β x).mono h).reduce_eq

/-- Stage reduction is idempotent. -/
@[simp] theorem reduce_reduce (α : Ordinal.{u}) (x : Label.{u}) :
    reduce α (reduce α x) = reduce α x :=
  reduce_reduce_of_le le_rfl x

/-- `β ≤ β + n` as labels. -/
theorem coe_le_coe_add (β : Ordinal.{u}) (n : ℕ) :
    (β : Label.{u}) ≤ ((β + n : Ordinal.{u}) : Label.{u}) :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr le_self_add)

/-- A label lies below the successor stage `o + 1` exactly when it is at most `o`. -/
theorem lt_coe_add_one_iff : x < ((o + 1 : Ordinal.{u}) : Label.{u}) ↔ x ≤ o := by
  induction x using recBotCoeTop with
  | bot => exact iff_of_true (WithBot.bot_lt_coe _) bot_le
  | coe a => rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe, WithBot.coe_le_coe, WithTop.coe_le_coe,
      Order.lt_add_one_iff]
  | top =>
    exact iff_of_false not_top_lt (not_le.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top o)))

/-- Stage reduction to a successor stage `o + 1` keeps a label at most `o`. -/
@[simp] theorem reduce_add_one_of_le (h : x ≤ o) : reduce (o + 1) x = x :=
  reduce_of_lt (lt_coe_add_one_iff.mpr h)

/-- Stage reduction to a successor stage `o + 1` sends a label above `o` to the formal top. -/
@[simp] theorem reduce_add_one_of_lt (h : (o : Label.{u}) < x) : reduce (o + 1) x = ⊤ :=
  reduce_of_le (not_lt.mp (mt lt_coe_add_one_iff.mp (not_le.mpr h)))

/-- A label at most `o` that is below the stage reduction of `z` to `o + 1` is below `z`. -/
theorem le_of_le_reduce_add_one {y z : Label.{u}} (hy : y ≤ o) (h : y ≤ reduce (o + 1) z) :
    y ≤ z := by
  rcases le_or_gt z o with hz | hz
  · rwa [reduce_add_one_of_le hz] at h
  · exact hy.trans hz.le

/-! ### Natural numbers -/

section NatCast

open Ordinal

/-- The cast of a natural number to a label is the label of its cast to an ordinal. -/
theorem natCast_label (n : ℕ) : (n : Label.{u}) = ((n : Ordinal.{u}) : Label.{u}) := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast]

theorem natCast_label_inj {n m : ℕ} : (n : Label.{u}) = m ↔ n = m := by
  rw [natCast_label, natCast_label, WithBot.coe_inj, WithTop.coe_inj, Nat.cast_inj]

theorem natCast_label_le {n m : ℕ} : (n : Label.{u}) ≤ m ↔ n ≤ m := by
  rw [natCast_label, natCast_label, WithBot.coe_le_coe, WithTop.coe_le_coe, Nat.cast_le]

/-- The casts of natural numbers to labels are strictly ordered as the natural numbers. -/
theorem natCast_label_lt {n m : ℕ} : (n : Label.{u}) < m ↔ n < m := by
  rw [natCast_label, natCast_label, WithBot.coe_lt_coe, WithTop.coe_lt_coe, Nat.cast_lt]

theorem natCast_label_lt_omega (n : ℕ) :
    (n : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
  rw [natCast_label, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  exact natCast_lt_omega0 n

/-- Every natural number lies below `ω ^ 2`. -/
theorem natCast_label_lt_omega0_sq (n : ℕ) :
    (n : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rw [natCast_label, WithBot.coe_lt_coe, WithTop.coe_lt_coe, pow_two]
  exact (natCast_lt_omega0 n).trans_le (le_mul_left _ omega0_pos)

theorem natCast_label_ne_bot (n : ℕ) : (n : Label.{u}) ≠ ⊥ := by
  rw [natCast_label]; exact WithBot.coe_ne_bot

/-- A label other than `⊥` below `ω` is a natural number. -/
theorem exists_natCast_of_lt_omega {x : Label.{u}} (hx : x ≠ ⊥)
    (hxω : x < ((ω : Ordinal.{u}) : Label.{u})) : ∃ n : ℕ, x = n := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | top => exact absurd hxω (not_lt.mpr le_top)
  | coe o =>
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe] at hxω
    obtain ⟨n, rfl⟩ := lt_omega0.mp hxω
    exact ⟨n, (natCast_label n).symm⟩

/-- Every ordinal is `ω * b + n` for an ordinal `b` and a natural number `n`. -/
theorem exists_eq_omega0_mul_add_natCast (o : Ordinal.{u}) :
    ∃ (b : Ordinal.{u}) (n : ℕ), o = ω * b + n := by
  obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
  exact ⟨o / ω, n, by rw [← hn, div_add_mod]⟩

end NatCast

/-! ### Labels of the form `ω * q + n` -/

section Block

open Ordinal

/-- A label `ω * q + n` lies below `ω * m` exactly when `q < m`. -/
theorem coe_block_lt_iff {q m : Ordinal.{u}} {n : ℕ} :
    ((ω * q + n : Ordinal.{u}) : Label.{u}) < ((ω * m : Ordinal.{u}) : Label.{u}) ↔ q < m := by
  rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  constructor
  · intro h
    by_contra hmq
    rw [not_lt] at hmq
    exact absurd h (not_lt.mpr ((show ω * m ≤ ω * q by gcongr).trans le_self_add))
  · intro h
    calc ω * q + n < ω * q + ω := add_lt_add_right (natCast_lt_omega0 n) _
      _ = ω * Order.succ q := (mul_succ _ _).symm
      _ ≤ ω * m := by gcongr; exact Order.succ_le_of_lt h

/-- Every label other than `⊥` and `⊤` has the form `ω * q + n`. -/
theorem exists_block {x : Label.{u}} (hb : x ≠ ⊥) (ht : x ≠ ⊤) :
    ∃ (q : Ordinal.{u}) (n : ℕ), x = ((ω * q + n : Ordinal.{u}) : Label.{u}) := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hb
  | top => exact absurd rfl ht
  | coe o =>
    obtain ⟨n, hn⟩ := lt_omega0.mp (mod_lt o omega0_ne_zero)
    exact ⟨o / ω, n, by rw [← hn, div_add_mod]⟩

end Block

/-! ### Countability -/

section Countability

open Cardinal Ordinal

/-- If there are countably many ordinals below `α`, then there are countably many labels at stage
`α`. -/
theorem countable_setOf_atStage {α : Ordinal.{u}} (hα : (Set.Iio α).Countable) :
    {x : Label.{u} | AtStage α x}.Countable := by
  refine (((hα.image fun o : Ordinal.{u} ↦ (o : Label.{u})).insert ⊥).insert ⊤).mono ?_
  intro x hx
  rcases atStage_iff.mp hx with rfl | ⟨o, ho, rfl⟩ | rfl
  · simp
  · simp [ho]
  · simp

/-- The labels below `ω ^ 2`, that is, bottom and the ordinals `ω · i + j`, form a countable
set. -/
theorem countable_setOf_lt_omega0_sq :
    {x : Label.{u} | x < ((ω ^ 2 : Ordinal.{u}) : Label.{u})}.Countable := by
  have h : (Set.Iio (ω ^ 2 : Ordinal.{u})).Countable := by
    rw [← le_aleph0_iff_set_countable, Cardinal.mk_Iio_ordinal, pow_two, card_mul, card_omega0]
    simp [aleph0_mul_aleph0]
  exact (countable_setOf_atStage h).mono fun _ hx ↦ .inl hx

end Countability

end Label

end VaughtConjecture
