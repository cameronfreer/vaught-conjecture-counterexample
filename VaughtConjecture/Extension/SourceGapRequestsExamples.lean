/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SourceGapRequests

/-!
# Source-gap requests at the separation input

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3).

The lemmas of `VaughtConjecture.Extension.SourceGapRequests` at the labellings of the separation
input `SeparationObstruction.T α` on two points: five cells `y` (`0`, scope `{0}`), `e` (`1`, dead),
`z` (`2`), `o` (`3`, the owner) and `r` (`4`, the lost top), of grades `1, 1, 1, 2, 2`, labelled
`lab v w s = (v, ⊥, v, w, s)`; the input is `lab ⊤ ⊤ ⊤`, the twisted donor
`TwistedDonor.U α w s` is labelled `lab ⊤ w s`.  A state on the amalgam is read here as a state
`Sum.elim p q` on `Fin 5 ⊕ Fin 5` (the context `p` on the left copy, the donor `q` on the right).

* The requests `reqU` for the twisted donor: owner `o` and lost top `r` of the context, `K = 2`,
  the new top `z` of the donor designated top, its cells `e`, `o`, `r` designated below.  The actual
  state satisfies the low clause at every field.
* The frontier of the lawful labelling `lab 2 2 ⊤` of the input (the root top `y` at `2`, the lost
  top at `⊤`) is `2`.
* The low clause says something at a field above the low maximum: the donor state `lab 2 2 2`
  fails it at the field `⊤`.  The existential form with `⊥` in the grid holds for every state.
* **The grade bound of the code is needed**: with the input as its own donor (designated tops `z`,
  `o`, `r`; designated below, `e`), the actual state satisfies the clause at the field `⊤`, but its
  splice at the grade `1`, which sends `o` and `r` to `⊥`, does not.
-/

universe u

namespace VaughtConjecture.SourceGapRequestsExamples

open Label SourceGapRequests

/-- The labelling `(v, ⊥, v, w, s)` of the five cells of the separation input. -/
noncomputable def lab (v w s : Label.{u}) : Fin 5 → Label.{u} := ![v, ⊥, v, w, s]

/-- The label `2`. -/
noncomputable abbrev two : Label.{u} := ((2 : ℕ) : Label.{u})

theorem two_ne_bot : two.{u} ≠ ⊥ := natCast_label_ne_bot 2

theorem two_lt_top : two.{u} < ⊤ := WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

/-- The requests for the twisted donor: owner `o` and lost top `r` on the context copy, `K = 2`,
designated below the donor cells `e`, `o`, `r`, designated top the donor cell `z`. -/
def reqU : SourceGapRequests (Fin 5 ⊕ Fin 5) where
  owner := .inl 3
  lost := .inl 4
  K := 2
  Lo := {.inr 1, .inr 3, .inr 4}
  Tops := {.inr 2}

/-- **The actual state is admitted at every field**: the new top `z` of the twisted donor is `⊤`. -/
example (w s b : Label.{u}) :
    reqU.AdmitsLowAt (Sum.elim (lab ⊤ ⊤ ⊤) (lab ⊤ w s)) b :=
  admitsLowAt_of_eq_top fun y hy ↦ by
    obtain rfl := Finset.mem_singleton.mp hy
    rfl

/-- **The frontier of `lab 2 2 ⊤`** is `2`: the owner at `2`, the lost top at `⊤`. -/
example (q : Fin 5 → Label.{u}) : reqU.frontier (Sum.elim (lab two two ⊤) q) = two := by
  simp only [frontier, reqU, Sum.elim_inl, lab]
  change min two (visibilityReplace 2 2 ⊤) = two
  rw [visibilityReplace_top, min_top_right]

/-- **The low clause says something above the low maximum**: the donor state `lab 2 2 2` fails it
at the field `⊤`. -/
example : ¬ reqU.AdmitsLowAt (Sum.elim (lab.{u} ⊤ ⊤ ⊤) (lab two two two)) ⊤ := by
  intro h
  have hlow : reqU.lowMax (Sum.elim (lab ⊤ ⊤ ⊤) (lab two.{u} two two)) = two := by
    simp [lowMax, reqU, lab]
  have := h (lt_of_eq_of_lt hlow two_lt_top) (.inr 2) (Finset.mem_singleton_self _)
  exact absurd ((le_max_left _ _).trans this) (not_le.mpr two_lt_top)

/-- **The existential form with `⊥` in the grid holds for every state.** -/
example (p q : Fin 5 → Label.{u}) : reqU.AdmitsLow {⊥} (Sum.elim p q) :=
  admitsLow_of_bot_mem rfl

/-- The requests with the input as its own donor: designated tops `z`, `o`, `r`, designated below
`e`. -/
def reqT : SourceGapRequests (Fin 5 ⊕ Fin 5) where
  owner := .inl 3
  lost := .inl 4
  K := 2
  Lo := {.inr 1}
  Tops := {.inr 2, .inr 3, .inr 4}

/-- The grades of the cells of the separation input, on both copies. -/
def grade : Fin 5 ⊕ Fin 5 → ℕ := Sum.elim ![1, 1, 1, 2, 2] ![1, 1, 1, 2, 2]

/-- **The grade bound of the code is needed**: the actual state of the input over itself satisfies
the low clause at the field `⊤`, and its splice at the grade `1` does not. -/
example : reqT.AdmitsLowAt (Sum.elim (lab ⊤ ⊤ ⊤) (lab ⊤ ⊤ ⊤)) ⊤ ∧
    ¬ reqT.AdmitsLowAt
      (fun d ↦ if grade d ≤ 1 then Sum.elim (lab.{u} ⊤ ⊤ ⊤) (lab ⊤ ⊤ ⊤) d else ⊥) ⊤ := by
  refine ⟨admitsLowAt_of_eq_top fun y hy ↦ ?_, fun h ↦ ?_⟩
  · simp only [reqT, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> rfl
  · have hlow : reqT.lowMax
        (fun d ↦ if grade d ≤ 1 then Sum.elim (lab.{u} ⊤ ⊤ ⊤) (lab ⊤ ⊤ ⊤) d else ⊥) = ⊥ := by
      simp [lowMax, reqT, grade, lab]
    have := h (lt_of_eq_of_lt hlow bot_lt_top) (.inr 3) (by simp [reqT])
    have h3 : (if grade (.inr 3) ≤ 1 then Sum.elim (lab.{u} ⊤ ⊤ ⊤) (lab ⊤ ⊤ ⊤) (.inr 3) else ⊥) =
        ⊥ := by simp [grade]
    exact absurd (le_bot_iff.mp ((le_max_left _ _).trans (this.trans_eq h3))) top_ne_bot

end VaughtConjecture.SourceGapRequestsExamples
