/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Basic

/-!
# Permitted cutoffs and capped observation

Roadmap, "Library conventions" (observations `obs_c(q)`, the permitted-cap test, and the
distinction between stage reduction and capped observation); semantic contract, item 3; the
expositions, §2.

The capped observation of a label `x` at a cutoff `c` is `min x c`; no separate operation is
introduced, and capping twice, monotonicity, and so on are Mathlib's lemmas about `min`.  At
stage `α` a cutoff is *permitted* (`IsPermittedCutoff α c`) if `⊥ < c < α`: it is an ordinal
below the stage, possibly ordinal zero (`isPermittedCutoff_iff`).

* Capping at an ordinal `α` and stage reduction to `α` have the same equality kernel
  (`min_eq_min_iff_reduce_eq`): both record a label below `α` exactly and identify all others.
* Stage reduction to `α` does not change a capped observation at a cutoff `≤ α`
  (`min_reduce_of_le`), so stage reduction preserves and reflects capped agreement at every
  permitted cutoff (`min_reduce_eq_min_reduce_iff`).
* **Capping is not stage reduction.**  A cap at a permitted cutoff identifies the formal top with
  a proper label at the same stage, which stage reduction never does
  (`IsPermittedCutoff.exists_min_eq_min_reduce_ne`).  Agreement below a proper cutoff therefore
  never establishes agreement at the formal top.  Nor is a capped observation of lawful data
  claimed to be lawful: nothing here concerns lawfulness.
-/

universe u

namespace VaughtConjecture.Label

variable {α β δ : Ordinal.{u}} {x y c : Label.{u}}

/-- A cutoff `c` is *permitted* at stage `α` if `⊥ < c < α`.  Ordinal zero is permitted at
every positive stage. -/
def IsPermittedCutoff (α : Ordinal.{u}) (c : Label.{u}) : Prop := ⊥ < c ∧ c < α

/-- An ordinal cutoff is permitted at stage `α` exactly when it is below `α`. -/
@[simp, grind =] theorem isPermittedCutoff_coe :
    IsPermittedCutoff α (δ : Label.{u}) ↔ δ < α := by
  simp [IsPermittedCutoff]

/-- Ordinal zero is a permitted cutoff exactly at the positive stages. -/
@[simp] theorem isPermittedCutoff_zero : IsPermittedCutoff α (0 : Label.{u}) ↔ 0 < α :=
  isPermittedCutoff_coe

/-- The ordinal `1` is a permitted cutoff exactly at the stages `α > 1`. -/
@[simp] theorem isPermittedCutoff_one : IsPermittedCutoff α (1 : Label.{u}) ↔ 1 < α :=
  isPermittedCutoff_coe

/-- A natural number `n` is a permitted cutoff exactly at the stages `α > n`. -/
@[simp] theorem isPermittedCutoff_natCast (n : ℕ) :
    IsPermittedCutoff α (n : Label.{u}) ↔ (n : Ordinal.{u}) < α :=
  isPermittedCutoff_coe

/-- A numeral `n` is a permitted cutoff exactly at the stages `α > n`. -/
@[simp] theorem isPermittedCutoff_ofNat (n : ℕ) [n.AtLeastTwo] :
    IsPermittedCutoff α (ofNat(n) : Label.{u}) ↔ (ofNat(n) : Ordinal.{u}) < α :=
  isPermittedCutoff_natCast n

/-- The bottom label is never a permitted cutoff. -/
@[simp] theorem not_isPermittedCutoff_bot : ¬ IsPermittedCutoff α (⊥ : Label.{u}) :=
  fun h ↦ h.1.false

/-- The formal top is never a permitted cutoff. -/
@[simp] theorem not_isPermittedCutoff_top : ¬ IsPermittedCutoff α (⊤ : Label.{u}) :=
  fun h ↦ not_top_lt h.2

/-- The permitted cutoffs at stage `α` are exactly the ordinals below `α`. -/
theorem isPermittedCutoff_iff : IsPermittedCutoff α c ↔ ∃ δ < α, (δ : Label.{u}) = c := by
  induction c using recBotCoeTop <;> simp

/-- A cutoff permitted at a stage is permitted at every higher stage. -/
theorem IsPermittedCutoff.mono (h : IsPermittedCutoff α c) (hαβ : α ≤ β) :
    IsPermittedCutoff β c :=
  ⟨h.1, h.2.trans_le (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hαβ))⟩

/-- A permitted cutoff is a proper label. -/
theorem IsPermittedCutoff.isProper (h : IsPermittedCutoff α c) : IsProper c := by
  obtain ⟨δ, -, rfl⟩ := isPermittedCutoff_iff.mp h
  exact isProper_coe δ

/-- A label capped at a permitted cutoff occurs at the stage. -/
theorem IsPermittedCutoff.atStage_min (h : IsPermittedCutoff α c) (x : Label.{u}) :
    AtStage α (min x c) :=
  .inl ((min_le_right x c).trans_lt h.2)

/-- Stage reduction to `α` does not change a capped observation at a cutoff `c ≤ α`. -/
theorem min_reduce_of_le (hc : c ≤ α) (x : Label.{u}) : min (reduce α x) c = min x c := by
  by_cases hx : x < α
  · rw [reduce_of_lt hx]
  · rw [reduce_of_le (not_lt.mp hx), min_eq_right le_top, min_eq_right (hc.trans (not_lt.mp hx))]

/-- Stage reduction to `α` preserves and reflects capped agreement at every cutoff `c ≤ α`. -/
theorem min_reduce_eq_min_reduce_iff (hc : c ≤ α) :
    min (reduce α x) c = min (reduce α y) c ↔ min x c = min y c := by
  rw [min_reduce_of_le hc, min_reduce_of_le hc]

/-- Capping at `α` and stage reduction to `α` have the same equality kernel. -/
theorem min_eq_min_iff_reduce_eq :
    min x (α : Label.{u}) = min y α ↔ reduce α x = reduce α y := by
  constructor
  · intro h
    have h' := congrArg (reduce α) h
    simpa [(monotone_reduce α).map_min] using h'
  · intro h
    simpa only [min_reduce_of_le le_rfl] using congrArg (min · (α : Label.{u})) h

/-- Agreement after stage reduction descends to every lower stage. -/
theorem reduce_eq_reduce_of_le (hβα : β ≤ α) (h : reduce α x = reduce α y) :
    reduce β x = reduce β y := by
  simpa only [reduce_reduce_of_le hβα] using congrArg (reduce β) h

/-- Stage reduction fixes a label capped at a permitted cutoff. -/
theorem IsPermittedCutoff.reduce_min (h : IsPermittedCutoff α c) (x : Label.{u}) :
    reduce α (min x c) = min x c :=
  (h.atStage_min x).reduce_eq

/-- **Capping is not stage reduction.**  At every permitted cutoff `c` of stage `α`, the labels
`c` and `⊤` both occur at stage `α` and have the same capped observation at `c`, but stage
reduction to `α` keeps them apart. -/
theorem IsPermittedCutoff.exists_min_eq_min_reduce_ne (h : IsPermittedCutoff α c) :
    ∃ x y : Label.{u}, AtStage α x ∧ AtStage α y ∧ min x c = min y c ∧
      reduce α x ≠ reduce α y :=
  ⟨c, ⊤, .inl h.2, atStage_top, by simp, by
    rw [reduce_of_lt h.2, reduce_top]; exact h.2.ne_top⟩

/-- The permitted cutoffs at stage `ω` are countably many: they are the natural numbers. -/
instance countable_permittedCutoff :
    Countable {c : Label.{u} // IsPermittedCutoff Ordinal.omega0.{u} c} :=
  Set.Countable.to_subtype <|
    (Set.countable_range fun k : ℕ ↦ ((k : Ordinal.{u}) : Label.{u})).mono fun _ hc ↦ by
      obtain ⟨δ, hδ, rfl⟩ := isPermittedCutoff_iff.mp hc
      obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hδ
      exact ⟨k, rfl⟩

end VaughtConjecture.Label
