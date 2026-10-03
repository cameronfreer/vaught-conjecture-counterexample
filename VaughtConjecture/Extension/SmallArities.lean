/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FieldLayer
import VaughtConjecture.Extension.SourcePrefix

/-!
# The completion at arity zero

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities; here `m = 0`); semantic
contract, items 2–4.

A seed on two points (`Seed α 0`) is the amalgam over the empty face of two coatom types on one
point, `{0}` and `{1}`.  Every cell of the amalgam has grade `1` (`Seed.grade_eq_one`); several
cells may lie on one point.  Its completion below the full grade is one layer of cells of full
scope and grade `1`: the canonical field layer of the amalgam at grade `1`
(`Seed.fieldLayerZero`, `VaughtConjecture.Extension.FieldLayer`).

**Bountifulness** (`Seed.isBountiful_fieldLayerZero`) is checked coatom by coatom
(`CellScheme.Rows.isBountiful_of_coatoms`):

* off the full face, the lifts are those of the amalgam: the amalgam is a source prefix of the
  field layer at every pair whose face is not the ground set
  (`Seed.isSourcePrefix_fieldLayerZero`), and its rows are bountiful
  (`Seed.cappedLift_fieldLayerZero_of_ne_univ`);
* from a coatom to the full face at grade `0` there are no cells;
* from a coatom to the full face at grade `1` (`Seed.cappedLift_fieldLayerZero`), the one-grade
  lift `CellScheme.Rows.cappedLift_of_boundary` at `j = 0` applies, with `U` the coatom, `V` the
  other coatom, and `O = (∅, 1)`: the lower lift and the lift from `O` are lifts from pairs with no
  cells, the lift from the coatom to itself is trivial, the boundary is every old cell, the field
  layer extends from the boundary at the cap `⊥` and at every positive cap along every new row,
  and every new row is lawful, short at `1` and never the formal top.  The lift keeps the cap at
  every cell below `(univ, 1)`, the new cells of full scope and the cells of the other coatom
  included (`Seed.exists_lift_fieldLayerZero`).

No completion is assumed in proving these lifts: the lifts off the full face come from the
bountifulness of the amalgam through the source prefix, not from a completion.

**The completion** (`Seed.completionBelowFullGradeZero`): the field layer, with the old cells
along `Fin.castAdd`, legal below the full grade (`Seed.isLegalBelowFullGrade_fieldLayerZero`;
completeness at `(univ, 1)` by the cell of the canonical code of the bottom labelling), and the
labelling extending the glued one at the cap `⊥` (`Scheme.exists_isLawful_fieldLayer`).  Every
lawful labelling of the amalgam extends, not only the glued one
(`Seed.exists_completionBelowFullGrade_zero`, `Seed.nonempty_completionBelowFullGrade_zero`).  No
hypothesis on the stage enters; the literal coatom faces of the completion follow from
`CompletionBelowFullGrade.restrictFace_left_completion` and
`CompletionBelowFullGrade.restrictFace_right_completion`.

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The amalgam is [Kni26, Definition 4.3.1], with its bountifulness [Kni26, Lemma 4.3.2]; the
completion has the shape of [Kni26, Definition 4.3.14], not its rows, and its bountifulness is the
statement of [Kni26, Lemma 4.3.20] for this completion, at arity zero; the printed proof is not
used.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 0)

/-- Every cell of the amalgam of a seed on two points has grade `1`. -/
theorem grade_eq_one (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d = 1 := by
  have h1 := I.grade_lt d
  have h0 : 0 < I.amalgam.toCellScheme.grade d :=
    (I.amalgam.isWellFormed.isWellFormed.gradedIndex_mem d).2.1
  omega

/-- The **field layer of a seed on two points**: the canonical field layer at grade `1` of its
amalgam.  It is the completion below the full grade (`Seed.completionBelowFullGradeZero`). -/
noncomputable abbrev fieldLayerZero : Scheme.{u} 2 :=
  I.amalgam.toScheme.fieldLayer 1 (I.not_univ_le 1)

/-- The first coatom is a face of the amalgam. -/
theorem erase_last_mem_faces :
    univ.erase (Fin.last 1) ∈ I.amalgam.toCellScheme.faces := by
  by_contra h
  rw [← Coatom.univ_map_left] at h
  have := StageType.restrictFace_of_notMem _ _ h
  rw [I.restrictFace_left] at this
  exact Option.some_ne_none _ this

/-- The second coatom is a face of the amalgam. -/
theorem erase_castSucc_mem_faces :
    univ.erase (Fin.castSucc (Fin.last 0)) ∈ I.amalgam.toCellScheme.faces := by
  by_contra h
  rw [← Coatom.univ_map_right] at h
  have := StageType.restrictFace_of_notMem _ _ h
  rw [I.restrictFace_right] at this
  exact Option.some_ne_none _ this

/-- The field layer of a seed on two points is well formed. -/
theorem isWellFormed_fieldLayerZero : I.fieldLayerZero.IsWellFormed :=
  Scheme.isWellFormed_fieldLayer I.amalgam.isWellFormed one_pos (by omega)

/-- Every cell of the field layer of a seed on two points has grade `1`. -/
theorem fieldLayerZero_grade (d : Fin I.fieldLayerZero.card) :
    I.fieldLayerZero.toCellScheme.grade d = 1 :=
  Scheme.fieldLayer_grade I.grade_eq_one d

/-- The field layer of a seed on two points has a cell of graded index `(univ, 1)`: the cell of
the canonical code of the bottom labelling. -/
theorem exists_gradedIndex_eq_univ :
    ∃ t, I.fieldLayerZero.toCellScheme.gradedIndex t = (univ, 1) := by
  obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq
    (Scheme.canonicalCode_mem_catalogue I.grade_eq_one
      (Rows.isLawful_const_bot (R := I.amalgam.rows)))
  exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩

/-- A pair whose face is not the ground set lies below no new cell. -/
private theorem not_univ_le_of_ne {Y : Finset (Fin 2) × ℕ} (hY : Y.1 ≠ univ) :
    ¬ ((univ : Finset (Fin 2)), 1) ≤ Y :=
  fun h ↦ hY (univ_subset_iff.mp h.1)

/-- **The amalgam is a source prefix of the field layer** at every pair whose face is not the
ground set. -/
theorem isSourcePrefix_fieldLayerZero {Y : Finset (Fin 2) × ℕ} (hY : Y.1 ≠ univ) :
    I.amalgam.toCellScheme.IsSourcePrefix I.fieldLayerZero.toCellScheme (Fin.castAdd _) Y :=
  ⟨Scheme.isLowerEmbedding_fieldLayer _ _ _, Scheme.appendFullCellsScheme_scope_castAdd _ _ _,
    fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below (not_univ_le_of_ne hY) hd⟩, rfl⟩⟩

/-- **Lifts off the full face**: between graded faces `X ≤ Y` with `Y` not on the ground set, the
field layer lifts capped, since the amalgam is bountiful. -/
theorem cappedLift_fieldLayerZero_of_ne_univ {X Y : Finset (Fin 2) × ℕ}
    (hX : X ∈ I.fieldLayerZero.toCellScheme.gradedFaces)
    (hY : Y ∈ I.fieldLayerZero.toCellScheme.gradedFaces) (hXY : X ≤ Y) (hYne : Y.1 ≠ univ) :
    I.fieldLayerZero.rows.CappedLift hXY :=
  (I.isSourcePrefix_fieldLayerZero hYne).cappedLift_of_isBountiful
    (by rw [Scheme.comap_rows_fieldLayer]; exact I.isBountiful) hX hY hXY le_rfl

/-- **The lift from a coatom to the full face at grade `1`.**  For the coatom `univ.erase x` and
the other coatom `univ.erase y`, the one-grade lift (`CellScheme.Rows.cappedLift_of_boundary` at
`j = 0`) applies to the field layer: the lower lift and the lift from the empty face are lifts
from pairs with no cells, the boundary is every old cell, the extension from the boundary at the
cap `⊥` and at every positive cap along every new row is that of the canonical field layer, and
every new row is lawful, short at `1` and never the formal top. -/
theorem cappedLift_fieldLayerZero {x y : Fin 2} (hxy : x ≠ y)
    (hx : univ.erase x ∈ I.amalgam.toCellScheme.faces)
    (hcover : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y) :
    I.fieldLayerZero.rows.CappedLift (X := (univ.erase x, 1)) (Y := (univ, 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  have hwf := I.isWellFormed_fieldLayerZero.isWellFormed
  have hne (z : Fin 2) : univ.erase z ≠ univ := by
    intro he
    have hz := mem_univ z
    rw [← he] at hz
    exact notMem_erase z univ hz
  have hcover' (d : Fin I.amalgam.card) :
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase x, 1) ∨
        I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase y, 1) :=
    (hcover d).imp (fun h ↦ ⟨h, (I.grade_eq_one d).le⟩) fun h ↦ ⟨h, (I.grade_eq_one d).le⟩
  refine Rows.cappedLift_of_boundary (C := univ.erase x) (B := univ) (j := 0)
    (U := (univ.erase x, 1)) (V := (univ.erase y, 1)) (O := (∅, 1)) (erase_subset _ _) ?_
    (hwf.cappedLift _ (Or.inl rfl) _) le_rfl ⟨empty_subset _, le_rfl⟩ ⟨empty_subset _, le_rfl⟩
    ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩ ?_ (Rows.cappedLift_refl _)
    (hwf.cappedLift _ (Or.inr rfl) _)
    (Scheme.extendsFromBoundary_bot_fieldLayer I.grade_eq_one (not_univ_le_of_ne (hne x))
      (not_univ_le_of_ne (hne y)) hcover')
    I.exists_gradedIndex_eq_univ fun u hu ↦ ⟨?_, ?_, ?_, fun h hh hbot ↦
      Scheme.extendsFromBoundary_fieldLayer I.grade_eq_one (not_univ_le_of_ne (hne x))
        (not_univ_le_of_ne (hne y)) hcover' hu hh hbot⟩
  · -- A cell of graded index `(univ.erase x, 1)`.
    have hXf : (univ.erase x, 1) ∈ I.amalgam.toCellScheme.gradedFaces :=
      ⟨hx, one_pos, by rw [card_erase_of_mem (mem_univ x)]; simp⟩
    obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hXf (hne x)
    exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩
  · -- The two coatoms meet in the empty face.
    intro d hdU hdV
    refine ⟨fun z hz ↦ ?_, hdU.2⟩
    have h1 := mem_erase.mp (hdU.1 hz)
    have h2 := mem_erase.mp (hdV.1 hz)
    exact absurd (show ∀ a b c : Fin 2, a ≠ b → a ≠ c → b ≠ c → False by decide) fun h ↦
      h z x y h1.1 h2.1 hxy
  · exact Scheme.isConsistent_fieldLayer I.isConsistent u
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).1
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).2

/-- **The lift from a coatom to the full face, coordinate by coordinate.**  At every cap `c`
self-visible at `1`, a prescription lawful below the coatom `(univ.erase x, 1)` and an ambient
lawful below `(univ, 1)` with the same observation at `c` below the coatom have a lift lawful below
`(univ, 1)` that reads the prescription literally and keeps the observation of the ambient at `c`
at every cell below `(univ, 1)`: the new cells of full scope and the cells of the other coatom
included. -/
theorem exists_lift_fieldLayerZero {x y : Fin 2} (hxy : x ≠ y)
    (hx : univ.erase x ∈ I.amalgam.toCellScheme.faces)
    (hcover : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y)
    {c : Label.{u}} (hc : IsSelfVisible 1 c)
    (p : I.fieldLayerZero.toCellScheme.below (univ.erase x, 1) → Label.{u})
    (q : I.fieldLayerZero.toCellScheme.below (univ, 1) → Label.{u})
    (hp : I.fieldLayerZero.rows.IsLawfulBelow _ p) (hq : I.fieldLayerZero.rows.IsLawfulBelow _ q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _
      (show ((univ.erase x, 1) : Finset (Fin 2) × ℕ) ≤ (univ, 1) from
        ⟨erase_subset _ _, le_rfl⟩)) d)) c = min (p d) c) :
    ∃ q' : I.fieldLayerZero.toCellScheme.below (univ, 1) → Label.{u},
      I.fieldLayerZero.rows.IsLawfulBelow _ q' ∧ (∀ d, min (q' d) c = min (q d) c) ∧
        ∀ d, q' (Set.inclusion (CellScheme.below_mono _
          (show ((univ.erase x, 1) : Finset (Fin 2) × ℕ) ≤ (univ, 1) from
            ⟨erase_subset _ _, le_rfl⟩)) d) = p d :=
  (Rows.cappedLift_iff_forall_exists _).mp (I.cappedLift_fieldLayerZero hxy hx hcover) c hc p q
    hp hq hpq

/-- **The field layer of a seed on two points is bountiful**, by the coatoms
(`CellScheme.Rows.isBountiful_of_coatoms`): off the full face the lifts are those of the amalgam
(through the source prefix, from the bountifulness of the amalgam), and from each coatom to the
full face they are the lifts at grade `0` (no cells) and at grade `1`
(`Seed.cappedLift_fieldLayerZero`). -/
theorem isBountiful_fieldLayerZero : I.fieldLayerZero.rows.IsBountiful := by
  have h10 : (Fin.last 1 : Fin 2) ≠ Fin.castSucc (Fin.last 0) := by decide
  have hwf := I.isWellFormed_fieldLayerZero.isWellFormed
  have hcover (d : Fin I.amalgam.card) :
      I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.last 1) ∨
        I.amalgam.toCellScheme.scope d ⊆ univ.erase (Fin.castSucc (Fin.last 0)) :=
    I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d) (I.scope_ne_univ d)
  have hle (z : Fin 2) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j = 0 ∨ j = 1 := by
    rw [card_erase_of_mem (mem_univ z)] at hj
    simp at hj
    omega
  refine Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 1)
    (b := Fin.castSucc (Fin.last 0)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces
    (fun X Y hX hY hXY hYne ↦ I.cappedLift_fieldLayerZero_of_ne_univ hX hY hXY hYne)
    (fun j hj ↦ ?_) fun j hj ↦ ?_
  · rcases hle _ j hj with rfl | rfl
    · exact hwf.cappedLift _ (Or.inl rfl) _
    · exact I.cappedLift_fieldLayerZero h10 I.erase_last_mem_faces hcover
  · rcases hle _ j hj with rfl | rfl
    · exact hwf.cappedLift _ (Or.inl rfl) _
    · exact I.cappedLift_fieldLayerZero h10.symm I.erase_castSucc_mem_faces fun d ↦ (hcover d).symm

/-- **The field layer of a seed on two points is legal below the full grade.** -/
theorem isLegalBelowFullGrade_fieldLayerZero : I.fieldLayerZero.IsLegalBelowFullGrade where
  isWellFormed := I.isWellFormed_fieldLayerZero
  isCoded := Scheme.isCoded_fieldLayer I.amalgam.isCoded
  isConsistent := Scheme.isConsistent_fieldLayer I.isConsistent
  isBountiful := I.isBountiful_fieldLayerZero
  grade_lt d := (I.fieldLayerZero_grade d).trans_lt (by omega)
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    obtain rfl : j = 1 := by have := hX.2.1; simp only at hX2 this; omega
    by_cases hC : C = univ
    · subst hC
      exact I.exists_gradedIndex_eq_univ
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩

/-- **The completion below the full grade of a seed on two points**: the field layer at grade `1`
of the amalgam, with the old cells along `Fin.castAdd`, and the extension of the glued labelling
(`Scheme.exists_isLawful_fieldLayer`). -/
noncomputable def completionBelowFullGradeZero : CompletionBelowFullGrade I where
  scheme := I.fieldLayerZero
  embed := Fin.castAddOrderEmb _
  isLowerEmbedding := Scheme.isLowerEmbedding_fieldLayer _ _ _
  scope_embed := Scheme.appendFullCellsScheme_scope_castAdd _ _ _
  comap_rows := Scheme.comap_rows_fieldLayer
  mem_range_embed z hz := by
    by_cases hlt : (z : ℕ) < I.amalgam.card
    · exact ⟨⟨z, hlt⟩, rfl⟩
    · have hz' : (z : ℕ) < I.amalgam.card + _ := z.2
      have hz2 : z = Fin.natAdd _ ⟨z - I.amalgam.card, by omega⟩ := Fin.ext (by simp; omega)
      rw [hz2] at hz
      exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ _) hz
  faces_eq := rfl
  isLegalBelowFullGrade := I.isLegalBelowFullGrade_fieldLayerZero
  label := (Scheme.exists_isLawful_fieldLayer (hS := I.not_univ_le 1) I.grade_eq_one
    I.amalgam.isLawful).choose
  isLawful := (Scheme.exists_isLawful_fieldLayer (hS := I.not_univ_le 1) I.grade_eq_one
    I.amalgam.isLawful).choose_spec.1
  label_embed := (Scheme.exists_isLawful_fieldLayer (hS := I.not_univ_le 1) I.grade_eq_one
    I.amalgam.isLawful).choose_spec.2

/-- **The completion at arity zero.**  Every seed on two points (two coatom types on one point
over the empty face) has a completion below the full grade, whose completed scheme extends every
lawful labelling of the amalgam, not only the glued one.  No hypothesis on the stage is used. -/
theorem exists_completionBelowFullGrade_zero :
    ∃ F : CompletionBelowFullGrade I, ∀ p : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawful p → ∃ r, F.scheme.rows.IsLawful r ∧ ∀ d, r (F.embed d) = p d :=
  ⟨I.completionBelowFullGradeZero, fun _ hp ↦ by
    obtain ⟨r, hr, hre⟩ :=
      Scheme.exists_isLawful_fieldLayer (hS := I.not_univ_le 1) I.grade_eq_one hp
    exact ⟨r, hr, hre⟩⟩

/-- **A seed on two points has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_zero : Nonempty (CompletionBelowFullGrade I) :=
  ⟨I.completionBelowFullGradeZero⟩

end Seed

end VaughtConjecture
