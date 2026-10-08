/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapFieldUniversal

/-!
# A field cell beside the doubling copies is not free down to `⊥`

Roadmap, Layer 3 ((R2) of the table of 3.4); the field cell of the LOW clause with a separate field
(`VaughtConjecture.Continuation.SourceGapFieldUniversal`), in the completion at the seed of the
input `SeparationObstruction.T` with itself (`VaughtConjecture.Continuation.SourceGapAdmittedSeed`).

**The placement.**  The field cell `φ` must be invisible in both coatom faces, so its scope contains
both new points; the faces of the amalgam are the ground set and the faces of the two coatoms, so
its scope is the ground set.  At grade `2` it would be an old cell of graded index `(univ, 2)`,
which the admitted field layer excludes; so it has graded index `(univ, 1)`, the graded index of
the doubling copies of `z`, and the row of each copy reads it.  A copy reads the root-type cells at
`2`; reading `φ` at `⊥` forces `φ` to `⊥`, and at `2` or above forces `φ` at least the root
(refuted as a field: `FieldAdmission.not_fieldAboveRoot`); so it reads `φ` at a nonzero label below
`2`.

**Such a reading forces `φ` above `⊥`** (`FieldAdmission.eq_bot_of_transformsTo_one_two`): a
witness sending a row value `1` to `⊥` sends `2` to `⊥` (`visibilityReplace 2 2 1 = 2`, and the
guard at the grade `2` holds at `⊥`), so a section `⊥` at the cell read at `1` is `⊥` at every cell
of no lower grade read at `2`.  At the copies (equal to the root) this says: `φ` is `⊥` only when
the root is.

**A field above `⊥` at a root above `⊥` is not served** (`FieldAdmission.not_lowAt_field_ne_bot`):
at the donor face `(1, ⊥, 1, ⊥, ⊥)` (cap `⊥`), every field other than `⊥` makes the clause ask
`o' ≠ ⊥`, for every designation with `o'` a top and the designated cells below the top among
`e'`, `r'`.  So the provision from the donor coatom at the cap `⊥` fails for a field cell placed
beside the copies (whatever its own row), and the engine build with the field cell stops here:
the field cell needs a placement outside `(univ, 1)` — a scope that is not a face of the amalgam,
or an old cell at `(univ, 2)` in a generalized admitted field layer — neither of which the current
completion framework (`CompletionBelowFullGrade`, faces equal to those of the amalgam) allows.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.FieldAdmission

open Finset Label SeparationObstruction

/-- Replacement at `2` with value `2` sends `1` to `2`. -/
theorem visibilityReplace_two_two_one :
    visibilityReplace 2 2 ((1 : ℕ) : Label.{u}) = ((2 : ℕ) : Label.{u}) := by
  simp

/-- **A reading at `1` beside readings at `2`**: if a row reads `d` at `1` and `d'` at `2`, with
`d` of grade at most that of `d'`, and the transformed section is `⊥` at `d`, then it is `⊥` at
`d'`. -/
theorem eq_bot_of_transformsTo_one_two {E : Type*} {grade : E → ℕ} {p q : E → Label.{u}}
    (h : TransformsTo grade p q) {d d' : E} (hd : p d = ((1 : ℕ) : Label.{u}))
    (hd' : p d' = ((2 : ℕ) : Label.{u})) (hg : grade d ≤ grade d') (hq : q d = ⊥) :
    q d' = ⊥ := by
  obtain ⟨g, σ, hw, he⟩ := h
  rw [he d, hd, min_eq_bot] at hq
  rw [he d', hd']
  rcases hq with hσ | hg0
  · have hc := hw.visibilityReplace_comm ((1 : ℕ) : Label.{u}) 2 (by rw [hσ]; exact bot_le) 2
      le_rfl
    rw [visibilityReplace_two_two_one, hσ, visibilityReplace_bot] at hc
    rw [hc, min_eq_bot]
    exact .inl rfl
  · rw [min_eq_bot]
    exact .inr (le_bot_iff.mp (hg0 ▸ hw.antitone hg))

/-- **A field other than `⊥` is not served at the donor face `(1, ⊥, 1, ⊥, ⊥)`**: the clause at a
field above `⊥` asks `o' ≠ ⊥` there, for every designation with `o'` a top and the designated
cells below the top among `e'`, `r'`; the face is lawful, and at the cap `⊥` it agrees with every
donor face. -/
theorem not_lowAt_field_ne_bot {Lo Tops : Finset (Fin 5)} (hLo : ∀ d ∈ Lo, d = 1 ∨ d = 4)
    (h3 : (3 : Fin 5) ∈ Tops) :
    S.{u}.rows.IsLawful (lab ((1 : ℕ) : Label.{u}) ⊥ ⊥) ∧
      ∀ (W : Fin 5 → Label.{u}) (b : Label.{u}), b ≠ ⊥ →
        ¬ LowAt Lo Tops W (lab ((1 : ℕ) : Label.{u}) ⊥ ⊥) b := by
  refine ⟨isLawful_lab (by rw [Nat.cast_one]; exact isSelfVisible_one.mpr le_rfl)
    (isSelfVisible_bot 2) (isSelfVisible_bot 2) bot_le (by simp), fun W b hb hlow ↦ ?_⟩
  have hsup : Lo.sup (lab ((1 : ℕ) : Label.{u}) ⊥ ⊥) = ⊥ := by
    refine le_bot_iff.mp (Finset.sup_le fun d hd ↦ ?_)
    rcases hLo d hd with rfl | rfl <;> exact le_rfl
  have := hlow (by rw [hsup]; exact bot_lt_iff_ne_bot.mpr hb) 3 h3
  exact hb (le_bot_iff.mp ((le_max_left _ _).trans this))

end VaughtConjecture.FieldAdmission
