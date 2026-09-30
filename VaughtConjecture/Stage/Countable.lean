/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import VaughtConjecture.Stage.Basic

/-!
# Countably many stage types

Roadmap, Layer 1 (countable stage types; the countability results needed for the language and the
requests); the expositions, §1 ("for countable `α`, there are only countably many stage types of
each finite arity").

A stage type at stage `α` on `n` points is determined by finite data: the number `k` of its cells,
its cell scheme on `Fin k` and `Fin n` (a ground set, a finite family of faces, and a scope and a
grade for each cell), finitely many row values, and finitely many labels.  The cell schemes with
finitely many cells over a countable ground type form a countable type (`CellScheme.countable`);
the row values are coded, hence lie in the countable set of labels below `ω ^ 2`
(`Label.countable_setOf_lt_omega0_sq`); and the labels occur at stage `α`, hence lie in a
countable set as soon as there are countably many ordinals below `α`
(`Label.countable_setOf_atStage`).  Therefore:

* `StageType.countable`: for `α` with `(Set.Iio α).Countable` (equivalently `α < ω₁`,
  `StageType.countable_of_lt_omega_one`), there are countably many stage types on `n` points;
* `StageType.countable_sigma`: the same holds for the stage types of all finite arities together,
  the relation symbols of the language at stage `α`.

No bound on the rows other than the coding is used.

The label-level statements `Label.countable_setOf_atStage` and
`Label.countable_setOf_lt_omega0_sq` belong in `VaughtConjecture.Label.Basic`, and
`CellScheme.countable` in `VaughtConjecture.Scheme.Cell`; they are stated here so that those files
are unchanged.

## References

This is [Kni26, Proposition 3.1.4] (numbering to be verified against the manuscript), for
R. W. Knight, *A counterexample to Vaught's Conjecture using generalised Stone spaces* (draft,
20 February 2026).
-/

universe u

namespace VaughtConjecture

open Cardinal Ordinal

namespace Label

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
    simp
  exact (countable_setOf_atStage h).mono fun _ hx ↦ .inl hx

end Label

/-- Cell schemes with finitely many cells over a countable ground type form a countable type. -/
instance CellScheme.countable {ι α : Type*} [Finite ι] [Countable α] :
    Countable (CellScheme ι α) :=
  Function.Injective.countable (f := fun D : CellScheme ι α ↦ (D.ground, D.faces, D.scope, D.grade))
    fun D E h ↦ by
      simp only [Prod.mk.injEq] at h
      exact CellScheme.ext h.1 h.2.1 h.2.2.1 h.2.2.2

namespace StageType

variable {α : Ordinal.{u}}

/-- **Countably many stage types** [Kni26, §3.1]: if there are countably many ordinals below the
stage `α`, then there are countably many stage types at stage `α` on `n` points. -/
theorem countable (hα : (Set.Iio α).Countable) (n : ℕ) : Countable (StageType.{u} α n) := by
  let V := {x : Label.{u} | x < ((ω ^ 2 : Ordinal.{u}) : Label.{u})}
  let W := {x : Label.{u} | Label.AtStage α x}
  have : Countable V := Label.countable_setOf_lt_omega0_sq.to_subtype
  have : Countable W := (Label.countable_setOf_atStage hα).to_subtype
  let F : StageType.{u} α n → Σ k : ℕ, Σ D : CellScheme (Fin k) (Fin n),
      ((s : Fin k) → D.below (D.gradedIndex s) → V) × (Fin k → W) :=
    fun t ↦ ⟨t.card, t.toCellScheme, fun s d ↦ ⟨t.rows.row s d, t.isCoded s d⟩,
      fun d ↦ ⟨t.label d, t.atStage d⟩⟩
  refine Function.Injective.countable (f := F) ?_
  rintro ⟨⟨k, D, R⟩, p, _, _, _, _⟩ ⟨⟨k', D', R'⟩, p', _, _, _, _⟩ h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h)
  obtain ⟨hR, hp⟩ := Prod.mk.inj (eq_of_heq h)
  obtain rfl : R = R' := CellScheme.Rows.ext
    (funext fun s ↦ funext fun d ↦ congrArg Subtype.val (congrFun (congrFun hR s) d))
  obtain rfl : p = p' := funext fun d ↦ congrArg Subtype.val (congrFun hp d)
  rfl

/-- There are countably many stage types on `n` points at a countable stage `α < ω₁`. -/
theorem countable_of_lt_omega_one (hα : α < ω₁) (n : ℕ) : Countable (StageType.{u} α n) :=
  countable (countable_Iio_of_lt_omega_one hα) n

/-- If there are countably many ordinals below the stage `α`, then there are countably many
stage types at stage `α` of all finite arities together. -/
theorem countable_sigma (hα : (Set.Iio α).Countable) : Countable (Σ n, StageType.{u} α n) :=
  have := countable hα
  inferInstance

end StageType

end VaughtConjecture
