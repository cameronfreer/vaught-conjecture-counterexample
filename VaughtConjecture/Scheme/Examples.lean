/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Bountiful

/-!
# Mute rows and a two-cell example

Roadmap, Layer 1 (zero/bottom cases); semantic contract, item 3.

The **mute** rows of a scheme (`Rows.mute D`) are constantly bottom.  Every cell's row is bottom at
the cell itself, so the only lawful section is the bottom labelling (`isLawful_mute_iff`), below
every pair as well (`isLawfulBelow_mute_iff`).  Hence mute rows are consistent
(`isConsistent_mute`) and bountiful (`isBountiful_mute`): every cap ball is the singleton of the
bottom labelling.  Mute rows pull back to mute rows (`comap_mute`).

`twoCells` is a concrete well-formed scheme on the one-point ground set `{0}` with two cells of the
same graded index `({0}, 1)`, illustrating physical multiplicities; with mute rows it is consistent
and bountiful (`twoCells_isWellFormed`, `isConsistent_mute`, `isBountiful_mute`).

## References

Mute rows are the mute semantics of the last clause of Lemma 4.2.2 of R. W. Knight, *A
counterexample to Vaught's Conjecture using generalised Stone spaces* (draft, 20 February 2026)
[Kni26].
-/

universe u

namespace VaughtConjecture.CellScheme

open Label

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β}

namespace Rows

variable (D) in
/-- The **mute** rows: every row is constantly bottom [Kni26, Lemma 4.2.2]. -/
def mute : D.Rows.{u} := ⟨fun _ _ ↦ ⊥⟩

/-- A value of a mute row. -/
@[simp] theorem mute_row (s : ι) (t : D.below (D.gradedIndex s)) : (mute D).row s t = ⊥ := rfl

/-- Mute rows pull back to mute rows. -/
@[simp] theorem comap_mute {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ) :
    (mute D).comap hφ = mute E := rfl

/-- The lawful sections of mute rows: only the bottom labelling. -/
theorem isLawful_mute_iff {p : ι → Label.{u}} : (mute D).IsLawful p ↔ p = fun _ ↦ ⊥ := by
  refine ⟨fun h ↦ funext fun s ↦ h.eq_bot_of_row_self_eq_bot s rfl, ?_⟩
  rintro rfl
  exact isLawful_bot

/-- Below every pair, the only labelling lawful for mute rows is the bottom labelling. -/
theorem isLawfulBelow_mute_iff {X : Finset α × ℕ} {r : D.below X → Label.{u}} :
    (mute D).IsLawfulBelow X r ↔ r = fun _ ↦ ⊥ := by
  rw [isLawfulBelow_iff, comap_mute, isLawful_mute_iff]

/-- Mute rows are consistent. -/
theorem isConsistent_mute : (mute D : D.Rows.{u}).IsConsistent := fun _ ↦ isLawfulBelow_bot _

/-- Mute rows are bountiful. -/
theorem isBountiful_mute : (mute D : D.Rows.{u}).IsBountiful := by
  intro X Y _ _ h c _ q hq p ⟨hp, _⟩
  rw [isLawfulBelow_mute_iff] at hq hp
  subst hq hp
  exact ⟨fun _ ↦ ⊥, self_mem_capBall _ (isLawfulBelow_bot Y) c, rfl⟩

end Rows

/-- A scheme on the ground set `{0}` with two cells, both of scope `{0}` and grade `1`. -/
private def twoCells : CellScheme (Fin 2) ℕ where
  ground := {0}
  faces := {∅, {0}}
  scope _ := {0}
  grade _ := 1

/-- The two cells of `twoCells` share their graded index. -/
private theorem twoCells_gradedIndex (d : Fin 2) : twoCells.gradedIndex d = ({0}, 1) := rfl

/-- `twoCells` is a well-formed scheme; its plan law is decided. -/
private theorem twoCells_isWellFormed : twoCells.IsWellFormed :=
  ⟨inferInstance, by decide, fun _ ↦ by simp [twoCells]⟩

end VaughtConjecture.CellScheme
