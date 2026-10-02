/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.InheritedLocality
import VaughtConjecture.Extension.Restoration

/-!
# Examples: grade cuts, source prefixes, and restoration in the special cases

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (lifting and alignment), and the special cases of the
checkpoints of `roadmap/IMPLEMENTATION.md` (empty, zero, one coordinate, repeated coordinates, and
the bottom section).

* **The grade `0`.**  The grade cut at `0` of a well-formed scheme has no cells, so its rows are
  bountiful whatever the rows of the scheme; and in the one-grade lift to the grade `1`, the lift
  at the lower grade `0` holds for all rows of a well-formed scheme, since no cell lies below a
  pair of grade `0`.
* **No cells.**  On a scheme with no cells every lift holds, and the grade cuts and source
  prefixes have no cells either.
* **One coordinate.**  On the one-point scheme `Scheme.onePoint` (one cell of grade `1`, the bottom
  rows), the one-grade lift at the grade `1` holds with no owner-capped lift: every owner label is
  bottom, at most every cap.
* **Repeated coordinates.**  On two cells of scope `{0}` and grade `1` (one graded index, two
  cells), with rows `(1, 1)` and `(1, 2)`, the section `(1, 2)` is lawful; the grade cut at `1`
  keeps both cells, and the owner of the prescription below their common graded index has the
  larger label `2`.
* **A lower prescribed label above the cap.**  On one point with a cell `x` of grade `1` labelled
  with the formal top and a cell `y` of grade `2` labelled `2`, restoration at the cap `2` (above
  the grade `1`) returns a lawful labelling that reads the formal top at `x`, although the lift it
  restores is capped at `2`.
* **The bottom section.**  The grade cut of the bottom rows is the bottom rows, whose only lawful
  section is the bottom one, and the splice of two bottom labellings is bottom.
-/

namespace VaughtConjecture

open Finset Label CellScheme

universe u

/-! ### The grade `0` and schemes without cells -/

/-- **The grade `0`**: the grade cut at `0` of a well-formed scheme is bountiful, whatever its
rows, since it has no cells. -/
example {ι α : Type*} [DecidableEq α] {D : CellScheme ι α} (hD : D.IsWellFormed)
    (R : D.Rows.{u}) : (R.gradeCut 0).IsBountiful := by
  have := hD.isEmpty_gradeCut_zero
  intro X Y _ _ h
  exact Rows.cappedLift_of_below_eq_empty (Set.eq_empty_of_isEmpty _) h

/-- **The lift at the lower grade `0`**, in the one-grade lift to the grade `1`, holds for all
rows of a well-formed scheme. -/
example {ι α : Type*} [DecidableEq α] {D : CellScheme ι α} (hD : D.IsWellFormed)
    (R : D.Rows.{u}) {C B : Finset α} (hCB : C ⊆ B) :
    R.CappedLift (X := (C, 0)) (Y := (B, 0)) ⟨hCB, le_rfl⟩ :=
  hD.cappedLift R (.inl rfl) _

/-- **No cells**: on a scheme with no cells, every grade cut lifts capped between any pairs. -/
example {ι α : Type*} [IsEmpty ι] {D : CellScheme ι α} (R : D.Rows.{u}) (g : ℕ)
    {X Y : Finset α × ℕ} (h : X ≤ Y) : (R.gradeCut g).CappedLift h :=
  Rows.cappedLift_of_below_eq_empty (Set.eq_empty_of_isEmpty _) h

/-- **No cells**: the empty source is a source prefix of a scheme at every pair below which it has
no cells. -/
example {ι κ α : Type*} [IsEmpty κ] {D : CellScheme ι α} {E : CellScheme κ α} {φ : κ → ι}
    (hφ : E.IsLowerEmbedding D φ) {Z : Finset α × ℕ} (hZ : D.below Z = ∅) :
    E.IsSourcePrefix D φ Z :=
  ⟨hφ, isEmptyElim, fun d hd ↦ absurd (show d ∈ D.below Z from hd) (hZ ▸ Set.notMem_empty d)⟩

/-! ### One coordinate -/

/-- **One coordinate**: on the one-point scheme, the one-grade lift at the grade `1` holds with no
owner-capped lift, since the only lawful labelling of the bottom rows is bottom. -/
example : Scheme.onePoint.{u}.rows.CappedLift (X := ((univ : Finset (Fin 1)), 1)) (Y := (univ, 1))
    ⟨subset_rfl, le_rfl⟩ := by
  refine Rows.cappedLift_of_ownerCappedLift (j := 0) subset_rfl ⟨⟨0, Nat.one_pos⟩, rfl⟩
    (Scheme.isLegal_onePoint.isWellFormed.isWellFormed.cappedLift _ (.inl rfl) _) ?_
  intro c _ p _ hp _ _ o _ _ hco
  have hp' : p = fun _ ↦ ⊥ := Rows.isLawfulBelow_bot_iff.mp hp
  rw [hp'] at hco
  exact absurd hco (not_lt_bot)

/-! ### Repeated coordinates -/

/-- Two cells of scope `{0}` and grade `1`, `false` and `true`: one graded index, two cells. -/
private def twinScheme : CellScheme Bool (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩

/-- The rows of `twinScheme`: `(1, 1)` at `false` and `(1, 2)` at `true`. -/
private def twinRows : twinScheme.Rows.{u} := ⟨fun s t ↦ if s && t.1 then 2 else 1⟩

/-- The section `(1, 2)` of `twinScheme`. -/
private def twinSection : Bool → Label.{u} := fun b ↦ if b then 2 else 1

/-- `1 ≤ 2`, as labels. -/
private theorem one_le_two_label : (1 : Label.{u}) ≤ 2 :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by simp))

/-- The labels of `twinSection` are at most `2`. -/
private theorem twinSection_le (b : Bool) : twinSection.{u} b ≤ 2 := by
  cases b
  · exact one_le_two_label
  · exact le_rfl

/-- **The section `(1, 2)` is lawful** for the rows `(1, 1)` and `(1, 2)`: both localities are the
identity transformation. -/
private theorem isLawful_twinSection : twinRows.{u}.IsLawful twinSection where
  orderly d := by cases d <;> simp [twinSection, twinScheme]
  locality s := by
    convert TransformsTo.refl _ (twinRows.row s) using 1
    funext d
    obtain ⟨b, hb⟩ := d
    cases s <;> cases b <;> simp [twinSection, twinRows]
  availability s _ _ _ := ⟨true, rfl, twinSection_le s⟩

/-- **Repeated coordinates**: the grade cut at `1` keeps both cells of the one graded index. -/
example : Nat.card {d // twinScheme.grade d ≤ 1} = 2 :=
  (Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ le_rfl)).trans (by simp)

/-- **Repeated coordinates**: below the common graded index `({0}, 1)` of the two cells, the owner
of the prescription `(1, 2)` is a cell of that graded index with the larger label `2`. -/
example : ∃ o : twinScheme.below (univ, 1), twinScheme.gradedIndex o = (univ, 1) ∧
    twinSection.{u} o = 2 := by
  obtain ⟨o, ho, hmax⟩ := (isLawful_twinSection.{u}.isLawfulBelow (univ, 1)).exists_owner
    ⟨true, rfl⟩
  exact ⟨o, ho, le_antisymm (twinSection_le o) (hmax ⟨true, subset_rfl, le_rfl⟩ rfl)⟩

/-- **Repeated coordinates**: the grade cut at `1` is a source prefix of the scheme at `({0}, 1)`,
and its lifts there are those of the scheme. -/
example {X : Finset (Fin 1) × ℕ} (h : X ≤ (univ, 1)) :
    (twinRows.{u}.gradeCut 1).CappedLift h ↔ twinRows.{u}.CappedLift h :=
  Rows.cappedLift_gradeCut_iff h le_rfl

/-! ### A lower prescribed label above the cap -/

/-- One point, with a cell `false` of grade `1` and a cell `true` of grade `2`, both of full
scope. -/
private def stepScheme : CellScheme Bool (Fin 1) :=
  ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun b ↦ if b then 2 else 1⟩

/-- The rows of `stepScheme`: `(⊤)` at `false` and `(2, 2)` at `true`. -/
private def stepRows : stepScheme.Rows.{u} := ⟨fun s _ ↦ if s then 2 else ⊤⟩

/-- The section `(⊤, 2)` of `stepScheme`. -/
private def stepSection : Bool → Label.{u} := fun b ↦ if b then 2 else ⊤

/-- Two cells of `stepScheme` of the same grade are equal. -/
private theorem eq_of_grade_eq {s t : Bool} (h : stepScheme.grade s = stepScheme.grade t) :
    s = t := by
  cases s <;> cases t <;> simp_all [stepScheme]

/-- **The section `(⊤, 2)` is lawful**: both localities are the identity transformation. -/
private theorem isLawful_stepSection : stepRows.{u}.IsLawful stepSection where
  orderly d := by cases d <;> simp [stepSection, stepScheme]
  locality s := by
    convert TransformsTo.refl _ (stepRows.row s) using 1
    funext d
    obtain ⟨b, hb⟩ := d
    cases s <;> cases b
    · simp [stepSection, stepRows]
    · exact absurd hb.2 (by simp [stepScheme])
    · simp [stepSection, stepRows]
    · simp [stepSection, stepRows]
  availability s t _ hg := ⟨t, rfl, (eq_of_grade_eq hg) ▸ le_rfl⟩

/-- **A lower prescribed label above the cap**: restoring, at the cap `2`, the lift of the
prescription `(⊤, 2)` capped at `2` reads the formal top at the cell of grade `1`.  Here `X = Y`,
and the scheme is not well formed (a cell of grade `2` on one point); both are admissible, since
restoration assumes neither `X < Y` nor well-formedness. -/
example : ∃ r : stepScheme.below (univ, 2) → Label.{u}, stepRows.IsLawfulBelow (univ, 2) r ∧
    r ⟨false, subset_rfl, by simp [stepScheme]⟩ = ⊤ := by
  have hp := isLawful_stepSection.{u}.isLawfulBelow (univ, 2)
  obtain ⟨r, hr, hrp, -, -⟩ := Rows.exists_restoration (X := (univ, 2)) (Y := (univ, 2)) le_rfl
    (j := 1) (by simp) (Rows.cappedLift_refl ((univ : Finset (Fin 1)), 1)) hp
    (hp.min_const_of_isSelfVisible (c := 2) (by simp)) (by simp) (fun _ ↦ rfl)
    fun e he ↦ by
      obtain ⟨b, hb⟩ := e
      cases b
      · exact absurd he (by simp [stepScheme])
      · exact le_rfl
  exact ⟨r, hr, hrp ⟨false, subset_rfl, by simp [stepScheme]⟩⟩

/-! ### The bottom section -/

/-- **The bottom section**: the only lawful section of the grade cut of the bottom rows is the
bottom labelling. -/
example {ι α : Type*} {D : CellScheme ι α} (g : ℕ) (p : {d // D.grade d ≤ g} → Label.{u}) :
    ((Rows.bot D).gradeCut g).IsLawful p ↔ p = fun _ ↦ ⊥ := by
  rw [Rows.gradeCut_bot]
  exact Rows.isLawful_bot_iff

/-- **The bottom section**: the splice of two bottom labellings is bottom. -/
example {ι α : Type*} {D : CellScheme ι α} (j : ℕ) :
    D.splice j (fun _ ↦ (⊥ : Label.{u})) (fun _ ↦ ⊥) = fun _ ↦ ⊥ := by
  funext d
  by_cases h : D.grade d ≤ j
  · exact splice_of_le h
  · exact splice_of_lt (not_le.mp h)

end VaughtConjecture
