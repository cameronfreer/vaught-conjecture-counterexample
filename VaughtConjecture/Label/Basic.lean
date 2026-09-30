/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Labels: ordinals with a bottom and a formal top

Roadmap, Layer 1 (extended-ordinal labels); semantic contract, item 3 ("Labels and rows"); the
expositions, §1.  A **label** is a point of `{-∞} ∪ Ordinal ∪ {∞}`.  It is represented by
Mathlib's `WithBot (WithTop Ordinal)`, whose order, lattice operations, and bounded-order
structure are used unchanged: `⊥` is the bottom label `-∞`, `⊤` is the formal top `∞`, and an
ordinal `o` is the label `((o : WithTop Ordinal) : Label)`, written `(o : Label)`.

Four kinds of label are distinguished.  The bottom label lies strictly below ordinal zero
(`bot_lt_coe_zero`); ordinal zero is the least label that is not bottom (`coe_zero_le_iff`); a
*proper* label is an ordinal (`IsProper`); the formal top is not an ordinal and lies above all
of them.

* `AtStage α x`: the label `x` occurs at stage `α`, that is, `x` is `⊥`, an ordinal `< α`, or `⊤`
  (expositions, §1: labels at stage `α` lie in `{-∞} ∪ α ∪ {∞}`).
* `reduce α x`: stage reduction of a single label to stage `α`.  Labels `< α` are kept and every
  other label becomes the formal top; this is the label-level content of the reduction of a
  stage type to a lower stage.  Its image is exactly the labels at stage `α`
  (`reduce_eq_self_iff`), and reductions compose (`reduce_reduce_of_le`).

Stage reduction is not capped observation (`VaughtConjecture.Label.Cap`): reduction keeps the
formal top, while a cap at a proper cutoff forgets it.
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

/-! ### Bottom, ordinal zero, proper labels, and top -/

/-- The bottom label lies strictly below ordinal zero. -/
theorem bot_lt_coe_zero : (⊥ : Label.{u}) < ((0 : Ordinal.{u}) : Label.{u}) :=
  WithBot.bot_lt_coe _

/-- Ordinal zero is the least label other than bottom. -/
theorem coe_zero_le_iff : ((0 : Ordinal.{u}) : Label.{u}) ≤ x ↔ x ≠ ⊥ := by
  induction x using recBotCoeTop <;> simp

/-- The only label below ordinal zero is bottom. -/
theorem lt_coe_zero_iff : x < ((0 : Ordinal.{u}) : Label.{u}) ↔ x = ⊥ := by
  rw [← not_le, coe_zero_le_iff, not_not]

/-- A label is *proper* if it is an ordinal, that is, neither bottom nor the formal top. -/
def IsProper (x : Label.{u}) : Prop := ∃ o : Ordinal.{u}, (o : Label.{u}) = x

/-- Every ordinal label is proper. -/
@[simp, grind .] theorem isProper_coe (o : Ordinal.{u}) : IsProper (o : Label.{u}) := ⟨o, rfl⟩

/-- The bottom label is not proper. -/
@[simp] theorem not_isProper_bot : ¬ IsProper (⊥ : Label.{u}) := fun ⟨_, h⟩ ↦ by simp at h

/-- The formal top is not proper. -/
@[simp] theorem not_isProper_top : ¬ IsProper (⊤ : Label.{u}) := fun ⟨_, h⟩ ↦ by simp at h

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

/-- The labels at stage `α`: bottom, an ordinal below `α`, or the formal top. -/
theorem atStage_iff : AtStage α x ↔ x = ⊥ ∨ (∃ o < α, (o : Label.{u}) = x) ∨ x = ⊤ := by
  induction x using recBotCoeTop <;> simp

/-- At stage zero the only labels are bottom and the formal top. -/
theorem atStage_zero_iff : AtStage 0 x ↔ x = ⊥ ∨ x = ⊤ := by
  induction x using recBotCoeTop <;> simp

/-- A label at a stage also occurs at every higher stage. -/
theorem AtStage.mono (h : AtStage α x) (hαβ : α ≤ β) : AtStage β x :=
  h.imp_left (·.trans_le (by simpa using hαβ))

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
@[simp] theorem reduce_bot : reduce α (⊥ : Label.{u}) = ⊥ := reduce_of_lt (WithBot.bot_lt_coe _)

/-- Stage reduction fixes the formal top. -/
@[simp] theorem reduce_top : reduce α (⊤ : Label.{u}) = ⊤ := reduce_of_le le_top

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

/-- Stage reduction is idempotent. -/
@[simp] theorem reduce_reduce (α : Ordinal.{u}) (x : Label.{u}) :
    reduce α (reduce α x) = reduce α x :=
  reduce_reduce_of_le le_rfl x

end Label

end VaughtConjecture
