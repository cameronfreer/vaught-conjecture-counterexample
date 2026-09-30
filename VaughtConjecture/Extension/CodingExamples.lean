/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Extension.CoatomAmalgam
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Geometry.IntervalPlan

/-!
# Examples: a legal scheme violating the offset bound, and coding transport over it

Roadmap, Library conventions (legality imposes coding as the range normalization only) and
Layer 3 (the coatom extension construction: coding of the completion); semantic contract, item 3.

**A legal scheme violating the offset bound.**  For a label `x` below `ω ^ 2` that is self-visible
at grade `1`, `pointRow x` is the scheme on one point with a single cell of scope `{0}` and grade
`1` whose row takes the value `x`.  It is legal (`isLegal_pointRow`): the constant row is lawful
below its cell, the only graded face is that of the cell, and a pair lifts capped to itself.  For
`x = 3` and for `x = ω + 5` the row value has finite part `3`, respectively `5`, above the grade
plus one, so the scheme is not strongly coded (`not_isStronglyCoded_pointRow_three`,
`not_isStronglyCoded_pointRow_omega0_add_five`): the offset bound of [Kni26, Lemma 2.5.13] fails
for these legal inputs.  Each carries a legal stage type at every stage, its bottom labelling.

**Coding transport over it.**  A proof of a coding statement that used the offset bound of its
inputs would not apply here; the transport lemmas of `VaughtConjecture.Extension.Coding` do.

* The amalgam of `pointRow 3` with itself over the empty face is coded
  (`isCoded_amalgam_pointRow_three`) and not strongly coded
  (`not_isStronglyCoded_amalgam_pointRow_three`: strong coding would pull back to the input).
* `pairRow x` is the scheme on two points with the cells `({0}, 1)` and `({1}, 1)`, both with row
  value `x`, and no cell of full scope, as in the amalgam; `apexRow x` appends the apex, a cell of
  scope `{0, 1}` and grade `2` with row bottom.  The cells of `pairRow x` are a lower set of those
  of `apexRow x`, with the same rows (`isLowerEmbedding_castSucc`, `comap_apexRow`).  So
  `apexRow 3` is coded (`isCoded_apexRow_three`), by the transport lemma with the new cell
  strongly coded, although it is not strongly coded (`not_isStronglyCoded_apexRow_three`); and it
  is consistent (`isConsistent_apexRow_three`), by the consistency transport with the apex row
  lawful below its cell.

## References

The offset bound is that of [Kni26, Lemma 2.5.13], the amalgam is [Kni26, Definition 4.3.1], and
its completion by cells of full scope is [Kni26, Definition 4.3.14].
-/

universe u

namespace VaughtConjecture

open Finset CellScheme
open scoped Ordinal

namespace CodingExamples

/-! ### Constant rows -/

/-- Rows that take the value `x` everywhere are consistent when `x` is self-visible at the grade of
every cell. -/
private theorem isConsistent_const {ι α : Type*} {D : CellScheme ι α} (x : Label.{u})
    (hx : ∀ d, Label.IsSelfVisible (D.grade d) x) :
    (⟨fun _ _ ↦ x⟩ : D.Rows.{u}).IsConsistent := fun _ ↦
  Rows.isLawfulBelow_iff.mpr
    { orderly := fun d ↦ hx d.1
      locality := fun _ ↦ by
        simp only [min_self]
        exact Label.TransformsTo.refl _ fun _ ↦ x
      availability := fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩ }

/-! ### A legal scheme on one point violating the offset bound -/

/-- The scheme on one point with a single cell of scope `{0}` and grade `1` whose row takes the
value `x`. -/
private def pointRow (x : Label.{u}) : Scheme.{u} 1 where
  card := 1
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩
  rows := ⟨fun _ _ ↦ x⟩

/-- The only graded face of `pointRow x` is `({0}, 1)`. -/
private theorem eq_of_mem_gradedFaces_pointRow {x : Label.{u}} {X : Finset (Fin 1) × ℕ}
    (hX : X ∈ (pointRow x).toCellScheme.gradedFaces) : X = (univ, 1) := by
  obtain ⟨C, j⟩ := X
  obtain ⟨_, hpos, hle⟩ := hX
  have hC : #C ≤ 1 := card_le_univ C
  simp only at hpos hle
  have hC' : C = univ := (card_eq_iff_eq_univ C).mp (by simp; omega)
  subst hC'
  simp only [card_univ, Fintype.card_fin] at hle
  ext <;> simp; omega

/-- **`pointRow x` is legal** when `x` lies below `ω ^ 2` and is self-visible at grade `1`, with no
bound on the finite part of `x` in terms of the grade. -/
private theorem isLegal_pointRow {x : Label.{u}} (hx : x < ((ω ^ 2 : Ordinal.{u}) : Label.{u}))
    (hv : Label.IsSelfVisible 1 x) : (pointRow x).IsLegal where
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun _ ↦ by
    simp [pointRow, CellScheme.gradedIndex]⟩⟩
  isCoded _ _ := hx
  isConsistent := isConsistent_const x fun _ ↦ hv
  isBountiful X Y hX hY h := by
    obtain rfl := eq_of_mem_gradedFaces_pointRow hX
    obtain rfl := eq_of_mem_gradedFaces_pointRow hY
    exact Rows.cappedLift_refl _
  isComplete X hX := ⟨(0 : Fin 1), by
    rw [eq_of_mem_gradedFaces_pointRow hX]
    rfl⟩

/-- The label `3` lies below `ω ^ 2` and is self-visible at grade `1`. -/
private theorem three_lt_omega0_sq : (3 : Label.{u}) < ((ω ^ 2 : Ordinal.{u}) : Label.{u}) :=
  Label.lt_omega0_sq_iff.mpr (.inr ⟨0, 3, by simp⟩)

/-- The label `ω + 5`, written `ω · 1 + 5`. -/
private noncomputable abbrev omega0AddFive : Label.{u} :=
  ((ω * (1 : ℕ) + (5 : ℕ) : Ordinal.{u}) : Label.{u})

/-- **`pointRow 3` is legal**: its row value `3` at a cell of grade `1` exceeds the grade plus
one. -/
private theorem isLegal_pointRow_three : (pointRow (3 : Label.{u})).IsLegal :=
  isLegal_pointRow three_lt_omega0_sq (by simp)

/-- **`pointRow (ω + 5)` is legal**: its row value has finite part `5`. -/
private theorem isLegal_pointRow_omega0_add_five : (pointRow omega0AddFive.{u}).IsLegal :=
  isLegal_pointRow (Label.lt_omega0_sq_iff.mpr (.inr ⟨1, 5, rfl⟩))
    (Label.isSelfVisible_coe.mpr (by
      rw [Ordinal.omega0_mul_add_natCast_mod_omega0]
      exact_mod_cast (by decide : 1 ≤ 5)))

/-- `pointRow 3` is not strongly coded: `3` is not strongly coded at grade `1`. -/
private theorem not_isStronglyCoded_pointRow_three :
    ¬ (pointRow (3 : Label.{u})).IsStronglyCoded := fun h ↦ by
  simpa [pointRow] using h (0 : Fin 1) ⟨(0 : Fin 1), CellScheme.mem_below_gradedIndex _ _⟩

/-- `pointRow (ω + 5)` is not strongly coded: `ω + 5` is not strongly coded at grade `1`. -/
private theorem not_isStronglyCoded_pointRow_omega0_add_five :
    ¬ (pointRow omega0AddFive.{u}).IsStronglyCoded := fun h ↦
  absurd ((Label.isStronglyCoded_coe_omega0_mul_add 1 1 5).mp
    (h (0 : Fin 1) ⟨(0 : Fin 1), CellScheme.mem_below_gradedIndex _ _⟩)) (by decide)

/-- `pointRow 3` carries a legal stage type at every stage, its bottom labelling. -/
private theorem isLegal_toStageType_pointRow_three (α : Ordinal.{u}) :
    (isLegal_pointRow_three.toStageType α).IsLegal :=
  isLegal_pointRow_three.isLegal_toStageType α

/-! ### The amalgam of the violating scheme with itself -/

/-- **The amalgam of `pointRow 3` with itself is coded**, by the coding of the amalgam of two
coded schemes; no offset bound is used. -/
private theorem isCoded_amalgam_pointRow_three :
    (Coatom.amalgam (Sa := pointRow (3 : Label.{u})) (Sb := pointRow 3) rfl).IsCoded :=
  Coatom.isCoded_amalgam rfl isLegal_pointRow_three.isCoded isLegal_pointRow_three.isCoded

/-- The amalgam of `pointRow 3` with itself is not strongly coded: its rows pull back to those
of `pointRow 3` along the inclusion of the first coatom. -/
private theorem not_isStronglyCoded_amalgam_pointRow_three :
    ¬ (Coatom.amalgamRows (Sa := pointRow (3 : Label.{u})) (Sb := pointRow 3)
      rfl).IsStronglyCoded :=
  fun h ↦ not_isStronglyCoded_pointRow_three <| by
    have h' := h.comap (Coatom.isLowerEmbedding_left rfl)
    rwa [Coatom.comap_amalgamRows_left] at h'

/-! ### Appending an apex -/

/-- The scheme on two points with the cells `({0}, 1)` and `({1}, 1)`, all faces, and row value
`x`: no cell has full scope. -/
private def pairRow (x : Label.{u}) : Scheme.{u} 2 where
  card := 2
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, ![({0} : Finset (Fin 2)), {1}], fun _ ↦ 1⟩
  rows := ⟨fun _ _ ↦ x⟩

/-- `pairRow x` with the apex appended: a third cell of scope `{0, 1}` and grade `2` whose row is
bottom. -/
private def apexRow (x : Label.{u}) : Scheme.{u} 2 where
  card := 3
  toCellScheme :=
    ⟨univ, Geometry.intervalPlan univ, ![({0} : Finset (Fin 2)), {1}, univ], ![1, 1, 2]⟩
  rows := ⟨fun s _ ↦ if s = 2 then ⊥ else x⟩

/-- The cells of `pairRow x` are a lower set of the cells of `apexRow x`, with the same scopes and
grades. -/
private theorem isLowerEmbedding_castSucc (x : Label.{u}) :
    (pairRow x).toCellScheme.IsLowerEmbedding (apexRow x).toCellScheme Fin.castSucc where
  injective := Fin.castSucc_injective 2
  grade_eq t := by fin_cases t <;> rfl
  le_iff s t := by
    fin_cases s <;> fin_cases t <;> simp [pairRow, apexRow, CellScheme.gradedIndex]
  mem_range t d hd := by
    by_cases h : d = Fin.last 2
    · subst h
      have h1 : (1 : Fin 2) ∈ (apexRow x).toCellScheme.scope (Fin.castSucc t) := hd.1 (mem_univ 1)
      have h0 : (0 : Fin 2) ∈ (apexRow x).toCellScheme.scope (Fin.castSucc t) := hd.1 (mem_univ 0)
      fin_cases t
      · exact absurd h1 (by decide : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)))
      · exact absurd h0 (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)))
    · exact Fin.exists_castSucc_eq.mpr h

/-- The rows of `apexRow x` pull back to those of `pairRow x`. -/
private theorem comap_apexRow (x : Label.{u}) :
    (apexRow x).rows.comap (isLowerEmbedding_castSucc x) = (pairRow x).rows := by
  ext s t
  fin_cases s <;> rfl

/-- The only new cell of `apexRow x` is the apex, whose row is bottom. -/
private theorem row_eq_bot_of_notMem_range (x : Label.{u}) {s : Fin 3}
    (hs : s ∉ Set.range (Fin.castSucc : Fin 2 → Fin 3)) (t) : (apexRow x).rows.row s t = ⊥ := by
  fin_cases s
  · exact absurd ⟨0, rfl⟩ hs
  · exact absurd ⟨1, rfl⟩ hs
  · rfl

/-- **`apexRow 3` is coded**: its inherited rows are coded (with the value `3` at grade `1`) and
its new row, the apex row, is strongly coded. -/
private theorem isCoded_apexRow_three : (apexRow (3 : Label.{u})).IsCoded :=
  Scheme.isCoded_of_isLowerEmbedding (isLowerEmbedding_castSucc 3) (comap_apexRow 3)
    (S := pairRow 3) (fun _ _ ↦ three_lt_omega0_sq) fun _ hs ↦
      Rows.isStronglyCodedAt_of_forall_eq_bot (row_eq_bot_of_notMem_range 3 hs)

/-- `apexRow 3` is not strongly coded: its first cell has row value `3` at grade `1`. -/
private theorem not_isStronglyCoded_apexRow_three :
    ¬ (apexRow (3 : Label.{u})).IsStronglyCoded := fun h ↦ by
  simpa [apexRow] using h (0 : Fin 3) ⟨(0 : Fin 3), CellScheme.mem_below_gradedIndex _ _⟩

/-- **`apexRow 3` is consistent**: the rows of `pairRow 3` are, and the apex row, bottom, is
lawful below the apex. -/
private theorem isConsistent_apexRow_three : (apexRow (3 : Label.{u})).rows.IsConsistent :=
  Rows.isConsistent_of_isLowerEmbedding (isLowerEmbedding_castSucc 3) (comap_apexRow 3)
    (isConsistent_const 3 fun _ ↦ by simp [pairRow]) fun s hs ↦ by
      convert Rows.isLawfulBelow_bot (R := (apexRow (3 : Label.{u})).rows) _ using 1
      funext t
      exact row_eq_bot_of_notMem_range 3 hs t

end CodingExamples

end VaughtConjecture
