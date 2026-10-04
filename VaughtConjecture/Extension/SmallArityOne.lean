/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SmallArities

/-!
# The completion at arity one

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities; here `m = 1`); semantic
contract, items 2–4.

A seed on three points (`Seed α 1`) is the amalgam of two coatom types on `{0, 1}` and `{0, 2}`
over the common face `{0}`.  Its cells have grades `1` and `2` (`Seed.grade_le_two`), and the
common face `{0}` is a face of the amalgam (`Seed.face_mem_faces`).  The candidate completion has
two layers of cells of full scope (`VaughtConjecture.Extension.FieldLayer`):

* **the lower layer** (`Seed.lowerFieldLayer`): the canonical field layer at grade `1` of the
  amalgam; its catalogue entries are bottom at the old cells of grade `2`, which its rows do not
  read;
* **the layer at grade two** (`Seed.fieldLayerOne`): the canonical field layer at grade `2` of the
  lower layer; its rows read every cell of the lower layer, the old cells of grade `1` through the
  orbit code.

The lower layer is a source prefix of the layer at grade two below `(univ, 1)`, and the amalgam is
one of both off the full face (`Scheme.isSourcePrefix_fieldLayer`).

**The lifts at grade one** (`Seed.cappedLift_lowerFieldLayer`, `Seed.cappedLift_fieldLayerOne_one`):
from a coatom `C` at grade `1` to `(univ, 1)`, by the one-grade lift
`CellScheme.Rows.cappedLift_of_boundary` at `j = 0` on the lower layer, with `U = (C, 1)`, `V` the
other coatom at grade `1`, and `O = ({0}, 1)`: the lift from `O` to `V` is a lift of the amalgam,
and the extension from the boundary is that of the field layer, whose old cells of grade at most
`1` all have grade `1`.  It is carried to the layer at grade two through the source prefix.

**The lifts at grade two** (`Seed.cappedLift_fieldLayerOne_two`): from a coatom `C` at grade `2` to
`(univ, 2)`, by the short-cap one-grade lift `CellScheme.Rows.cappedLift_of_boundary_short` at
`j = 1`, with `U = (C, 2)`, **`V = (univ, 1)` and `O = (C, 1)`**: the lift from `O` to `V` and the
lift at the lower grade are the lift at grade one, the lift from `C` to `U` is trivial.  The
boundary is every cell below `(C, 2)` or below `(univ, 1)`: all of the lower layer except the old
cells of grade `2` on the other coatom `D`.  The extension from the boundary
(`Seed.extendsFromBoundary_fieldLayerOne`, `Seed.extendsFromBoundary_bot_fieldLayerOne`) lifts the
boundary labelling within the face `D`, from `(D, 1)` to `(D, 2)`
(`CellScheme.Rows.cappedLift_of_fst_eq`), glues the three pieces
(`CellScheme.Rows.IsLawfulBelow.glue₃`: the cells below both `(D, 2)` and `(C, 2)` lie on `{0}`,
of grade `1`), and extends through the new cells of grade two (`Scheme.exists_extension_fieldLayer`
at a cap short at `2`, `Scheme.exists_isLawfulBelow_fieldLayer` at `⊥`).  So the cap on the cells
of the lower layer during a lift at grade two is kept by the lift at grade one, used as the
boundary lift into `(univ, 1)`; the catalogue at grade one does not read the cells of grade two.

**Bountifulness** (`Seed.isBountiful_fieldLayerOne`) is checked coatom by coatom
(`CellScheme.Rows.isBountiful_of_coatoms`): off the full face the lifts are those of the amalgam,
through the source prefix and the bountifulness of the amalgam
(`Seed.cappedLift_fieldLayerOne_of_ne_univ`), never through a completion; from each coatom to the
full face they are the lifts at grade `0` (no cells), `1` and `2`.

**The completion** (`Seed.completionBelowFullGradeOne`): the layer at grade two, with the old
cells along `Fin.castAdd` twice, legal below the full grade
(`Seed.isLegalBelowFullGrade_fieldLayerOne`: completeness at `(univ, 1)` and `(univ, 2)` by the
cells of the orbit code of the bottom labelling), and the glued labelling extended through both
layers (`Seed.exists_isLawful_fieldLayerOne`).  Every lawful labelling of the amalgam extends
(`Seed.exists_completionBelowFullGrade_one`), and with the arity zero every seed on at most three
points has a completion below the full grade (`Seed.nonempty_completionBelowFullGrade_of_le_one`).
No hypothesis on the stage enters.  So checkpoint 2.5 is proved at both small arities; the
recursion on the grade for `m ≥ 2` (checkpoint 2.6) is still to be proved.  There the step from
grade `j` to `j + 1` cannot use `V = (univ, j)` and a lift within the other coatom's face as here:
the other coatom `D` meets the first in cells of grade `j + 1`, so its cells of grade `j + 1` need
a lift from the union of `(C ∩ D, j + 1)` and `(D, j)`.  At `m = 1` the common face `{0}` carries
no cell of grade `2`, which is what makes the lift within the face exact.

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The amalgam is [Kni26, Definition 4.3.1], with its bountifulness [Kni26, Lemma 4.3.2]; the
completion has the shape of [Kni26, Definition 4.3.14], not its rows.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} (I : Seed.{u} α 1)

/-! ### The two layers -/

/-- Every cell of the amalgam of a seed on three points has grade at most `2`. -/
theorem grade_le_two (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d ≤ 2 := by
  have := I.grade_lt d
  omega

/-- **The common face `{0}` is a face of the amalgam**: it is the face of the first coatom along
`Fin.castSuccEmb`, and that coatom is the face of the amalgam along `Fin.castSuccEmb`. -/
theorem face_mem_faces : ({0} : Finset (Fin 3)) ∈ I.amalgam.toCellScheme.faces := by
  have h := (StageType.restrictFace_trans _ _ _ I.restrictFace_left).symm.trans
    I.restrictFace_face_left
  have hmem := (StageType.isSome_restrictFace_iff _ _).mp (by rw [h]; rfl)
  convert hmem using 1
  decide

/-- The **lower layer** of a seed on three points: the canonical field layer at grade `1` of its
amalgam. -/
noncomputable abbrev lowerFieldLayer : Scheme.{u} 3 :=
  I.amalgam.toScheme.fieldLayer 1 (I.not_univ_le 1)

/-- No cell of the lower layer lies above `(univ, 2)`. -/
theorem not_univ_two_le_lowerFieldLayer (d : Fin I.lowerFieldLayer.card) :
    ¬ ((univ : Finset (Fin 3)), 2) ≤ I.lowerFieldLayer.toCellScheme.gradedIndex d := by
  induction d using Fin.addCases with
  | left d =>
    rw [show I.lowerFieldLayer.toCellScheme.gradedIndex (Fin.castAdd _ d) =
      I.amalgam.toCellScheme.gradedIndex d from Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _
        _ d]
    exact I.not_univ_le 2 d
  | right i =>
    rw [show I.lowerFieldLayer.toCellScheme.gradedIndex (Fin.natAdd _ i) = (univ, 1) from
      Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i]
    exact fun h ↦ absurd h.2 (by decide)

/-- The **layer at grade two** of a seed on three points: the canonical field layer at grade `2`
of the lower layer. -/
noncomputable abbrev fieldLayerOne : Scheme.{u} 3 :=
  I.lowerFieldLayer.fieldLayer 2 I.not_univ_two_le_lowerFieldLayer

/-- Every cell of the lower layer has grade at most `2`. -/
theorem lowerFieldLayer_grade_le (d : Fin I.lowerFieldLayer.card) :
    I.lowerFieldLayer.toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left d => exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ d).trans_le (I.grade_le_two d)
  | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).trans_le (by decide)

/-- The lower layer is well formed. -/
theorem isWellFormed_lowerFieldLayer : I.lowerFieldLayer.IsWellFormed :=
  Scheme.isWellFormed_fieldLayer I.amalgam.isWellFormed one_pos (by omega)

/-- The layer at grade two is well formed. -/
theorem isWellFormed_fieldLayerOne : I.fieldLayerOne.IsWellFormed :=
  Scheme.isWellFormed_fieldLayer I.isWellFormed_lowerFieldLayer two_pos (by omega)

/-- The lower layer is consistent. -/
theorem isConsistent_lowerFieldLayer : I.lowerFieldLayer.rows.IsConsistent :=
  Scheme.isConsistent_fieldLayer I.isConsistent

/-- **The amalgam is a source prefix of the layer at grade two** at every pair whose face is not
the ground set. -/
theorem isSourcePrefix_fieldLayerOne {Y : Finset (Fin 3) × ℕ} (hY : Y.1 ≠ univ) :
    I.amalgam.toCellScheme.IsSourcePrefix I.fieldLayerOne.toCellScheme
      (Fin.castAdd _ ∘ Fin.castAdd _) Y :=
  (Scheme.isSourcePrefix_fieldLayer _ _ _ fun h ↦ hY (univ_subset_iff.mp h.1)).comp
    (Scheme.isSourcePrefix_fieldLayer _ _ _ fun h ↦ hY (univ_subset_iff.mp h.1))

/-! ### The two coatoms -/

/-- The two coatoms of a seed on three points are `univ.erase 2` and `univ.erase 1`. -/
private theorem coatom_cases {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x = Fin.last 2 ∧ y = Fin.castSucc (Fin.last 1)) ∨
      (x = Fin.castSucc (Fin.last 1) ∧ y = Fin.last 2) := by
  revert x y
  decide

/-- A coatom of a seed on three points is a face of the amalgam. -/
private theorem erase_mem_faces {x : Fin 3} (hx : x ≠ 0) :
    univ.erase x ∈ I.amalgam.toCellScheme.faces := by
  rcases (show x = Fin.last 2 ∨ x = Fin.castSucc (Fin.last 1) by revert x; decide) with rfl | rfl
  exacts [I.erase_last_mem_faces, I.erase_castSucc_mem_faces]

/-- Every cell of the amalgam lies on one of the two coatoms. -/
private theorem scope_subset_or {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    (d : Fin I.amalgam.card) :
    I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨ I.amalgam.toCellScheme.scope d ⊆ univ.erase y :=
  by
  have h := I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d)
  rcases coatom_cases hxy hx hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

/-- The two coatoms meet in the common face `{0}`. -/
private theorem erase_inter_erase {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    univ.erase x ∩ univ.erase y = {0} := by
  revert x y
  decide

/-- A coatom of `Fin 3` is not the ground set. -/
private theorem erase_ne_univ (x : Fin 3) : univ.erase x ≠ univ := fun h ↦
  notMem_erase x univ (by rw [h]; exact mem_univ x)

/-- A coatom of `Fin 3` has two points. -/
private theorem card_erase (x : Fin 3) : #(univ.erase x) = 2 := by
  rw [card_erase_of_mem (mem_univ x)]
  rfl

/-! ### The lifts at grade one -/

/-- The cells of the amalgam other than bottom have positive grade. -/
private theorem one_le_grade (d : Fin I.amalgam.card) : 1 ≤ I.amalgam.toCellScheme.grade d :=
  (I.amalgam.isWellFormed.isWellFormed.gradedIndex_mem d).2.1

/-- **The lift at grade one on the lower layer.**  For the coatoms `univ.erase x` and
`univ.erase y`, the one-grade lift `CellScheme.Rows.cappedLift_of_boundary` at `j = 0` applies to
the lower layer, with `U = (univ.erase x, 1)`, `V = (univ.erase y, 1)` and `O = ({0}, 1)`: the
lower lift is from a pair with no cells, the lift from `O` to `V` is a lift of the amalgam, the
boundary is every old cell of grade `1`, and the field layer extends from it at `⊥` and at every
positive cap, its old cells of grade at most `1` all having grade `1`. -/
theorem cappedLift_lowerFieldLayer {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    I.lowerFieldLayer.rows.CappedLift (X := (univ.erase x, 1)) (Y := (univ, 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  have hwf := I.isWellFormed_lowerFieldLayer.isWellFormed
  have hnot (z : Fin 3) (j : ℕ) : ¬ ((univ : Finset (Fin 3)), 1) ≤ (univ.erase z, j) :=
    fun h ↦ erase_ne_univ z (univ_subset_iff.mp h.1)
  have hcover (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 1) :
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase x, 1) ∨
        I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase y, 1) :=
    (I.scope_subset_or hxy hx hy d).imp (fun h ↦ ⟨h, hd⟩) fun h ↦ ⟨h, hd⟩
  have h0 (z : Fin 3) (hz : z ≠ 0) : ({0} : Finset (Fin 3)) ⊆ univ.erase z :=
    singleton_subset_iff.mpr (mem_erase.mpr ⟨Ne.symm hz, mem_univ _⟩)
  refine Rows.cappedLift_of_boundary (C := univ.erase x) (B := univ) (j := 0)
    (U := (univ.erase x, 1)) (V := (univ.erase y, 1)) (O := ({0}, 1)) (erase_subset _ _) ?_
    (hwf.cappedLift _ (Or.inl rfl) _) le_rfl ⟨h0 x hx, le_rfl⟩ ⟨h0 y hy, le_rfl⟩
    ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩ ?_ (Rows.cappedLift_refl _) ?_
    (Scheme.extendsFromBoundary_bot_fieldLayer (hnot x 1) (hnot y 1) hcover) ?_
    fun u hu ↦ ⟨Scheme.isConsistent_fieldLayer I.isConsistent u, ?_, ?_, fun h hh hbot ↦
      Scheme.extendsFromBoundary_fieldLayer
        (fun d hd ↦ le_antisymm hd (I.one_le_grade d)) (hnot x 1) (hnot y 1) hcover hu hh hbot⟩
  · -- A cell of graded index `(univ.erase x, 1)`.
    obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase x, 1)
      ⟨I.erase_mem_faces hx, one_pos, by rw [card_erase]; omega⟩ (erase_ne_univ x)
    exact ⟨Fin.castAdd _ d, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd⟩
  · -- The two coatoms meet in `{0}`.
    intro d hdU hdV
    exact ⟨(subset_inter hdU.1 hdV.1).trans (erase_inter_erase hxy hx hy).le, hdU.2⟩
  · -- The lift from `({0}, 1)` to the other coatom, a lift of the amalgam.
    refine ((Scheme.isSourcePrefix_fieldLayer _ _ _ (hnot y 1)).cappedLift_of_isBountiful
      (by rw [Scheme.comap_rows_fieldLayer]; exact I.isBountiful)
      ⟨I.face_mem_faces, one_pos, by simp⟩
      (X := ({0}, 1)) (Y := (univ.erase y, 1))
      ⟨I.erase_mem_faces hy, one_pos, by rw [card_erase]; omega⟩ _ le_rfl)
  · -- The cell of the orbit code of the bottom labelling.
    obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
      (S := I.amalgam.toScheme) (k := 1) (p := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _))
    exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).1
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).2

/-- **The lift at grade one on the layer at grade two**: the lower layer is a source prefix of the
layer at grade two below `(univ, 1)`, so the lift of the lower layer from a coatom at grade `1` to
`(univ, 1)` is a lift of the layer at grade two. -/
theorem cappedLift_fieldLayerOne_one {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    I.fieldLayerOne.rows.CappedLift (X := (univ.erase x, 1)) (Y := (univ, 1))
      ⟨erase_subset _ _, le_rfl⟩ := by
  have h := Scheme.isSourcePrefix_fieldLayer I.lowerFieldLayer 2
    I.not_univ_two_le_lowerFieldLayer (Y := (univ, 1)) fun h ↦ absurd h.2 (by decide)
  refine (h.cappedLift_iff _ le_rfl).mp ?_
  have hc : I.fieldLayerOne.rows.comap h.isLowerEmbedding = I.lowerFieldLayer.rows :=
    Scheme.comap_rows_fieldLayer
  rw [hc]
  exact I.cappedLift_lowerFieldLayer hxy hx hy

/-! ### The extension from the boundary at grade two -/

/-- **The boundary labelling, completed on the lower layer.**  Let `w` be a labelling of the layer
at grade two lawful below `(univ.erase x, 2)` and `(univ, 1)`, and `a` a lawful section of the
lower layer that agrees with `w` capped at `h` on the boundary.  Then some labelling of the lower
layer, lawful below `(univ, 2)`, is `w` on the boundary and agrees with `a` capped at `h`
everywhere: on the other coatom `D = univ.erase y` the boundary labelling below `(D, 1)` is lifted
within the face to `(D, 2)` along `a` (`CellScheme.Rows.cappedLift_of_fst_eq`), and the three
pieces are glued (`CellScheme.Rows.IsLawfulBelow.glue₃`). -/
theorem exists_isLawfulBelow_lowerFieldLayer {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0)
    (hy : y ≠ 0) {w : Fin I.fieldLayerOne.card → Label.{u}}
    (hwU : I.fieldLayerOne.rows.IsLawfulBelow (univ.erase x, 2) fun d ↦ w d)
    (hwV : I.fieldLayerOne.rows.IsLawfulBelow (univ, 1) fun d ↦ w d)
    {a : Fin I.lowerFieldLayer.card → Label.{u}} (ha : I.lowerFieldLayer.rows.IsLawful a)
    {h : Label.{u}} (hh : IsSelfVisible 2 h)
    (hag : ∀ e, I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ.erase x, 2) ∨
      I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ, 1) →
        min (w (Fin.castAdd _ e)) h = min (a e) h) :
    ∃ g : Fin I.lowerFieldLayer.card → Label.{u},
      I.lowerFieldLayer.rows.IsLawfulBelow (univ, 2) (fun d ↦ g d) ∧
      (∀ e, I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ.erase x, 2) ∨
        I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ, 1) → g e = w (Fin.castAdd _ e)) ∧
      ∀ e, min (g e) h = min (a e) h := by
  classical
  have hwf := I.isWellFormed_lowerFieldLayer.isWellFormed
  have hnot2 (X : Finset (Fin 3) × ℕ) (hX : X.1 ≠ univ ∨ X.2 < 2) :
      ¬ ((univ : Finset (Fin 3)), 2) ≤ X := fun h ↦
    hX.elim (fun hX ↦ hX (univ_subset_iff.mp h.1)) fun hX ↦ absurd h.2 (by omega)
  -- The boundary labelling on the lower layer.
  have hw₁U : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase x, 2)
      fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := I.lowerFieldLayer) (k := 2)
      (r := fun i ↦ I.lowerFieldLayer.fieldRow 2 (I.lowerFieldLayer.catalogueEntry 2 i))
      (h := I.not_univ_two_le_lowerFieldLayer) (v := w)
      (hnot2 _ (.inl (erase_ne_univ x)))).mp hwU
  have hw₁V : I.lowerFieldLayer.rows.IsLawfulBelow (univ, 1) fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := I.lowerFieldLayer) (k := 2)
      (r := fun i ↦ I.lowerFieldLayer.fieldRow 2 (I.lowerFieldLayer.catalogueEntry 2 i))
      (h := I.not_univ_two_le_lowerFieldLayer) (v := w)
      (hnot2 _ (.inr one_lt_two))).mp hwV
  -- The lift within the other coatom, from grade `1` to grade `2`, along `a`.
  have hDD : ((univ.erase y, 1) : Finset (Fin 3) × ℕ) ≤ (univ.erase y, 2) :=
    ⟨subset_rfl, one_le_two⟩
  have hw₁D : I.lowerFieldLayer.rows.IsLawfulBelow (univ.erase y, 1)
      fun e ↦ w (Fin.castAdd _ e.1) :=
    hw₁V.mono (X := (univ.erase y, 1)) ⟨subset_univ _, le_rfl⟩
  obtain ⟨v, hv, hvcap, hvw⟩ := (Rows.cappedLift_iff_forall_exists hDD).mp
    (Rows.cappedLift_of_fst_eq hDD rfl) h hh (fun e ↦ w (Fin.castAdd _ e.1)) (fun e ↦ a e)
    hw₁D (ha.isLawfulBelow _) fun e ↦ (hag e (.inr ⟨subset_univ _, e.2.2⟩)).symm
  -- Every cell of the lower layer lies below one of the three pairs.
  have hcover (e : Fin I.lowerFieldLayer.card) :
      e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) ∨
          e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2) := by
    induction e using Fin.addCases with
    | right i =>
      exact .inr (.inl (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i).le)
    | left d =>
      have hsc : I.lowerFieldLayer.toCellScheme.scope (Fin.castAdd _ d) =
          I.amalgam.toCellScheme.scope d :=
        Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d
      have hg := I.lowerFieldLayer_grade_le (Fin.castAdd _ d)
      rcases I.scope_subset_or hxy hx hy d with hd | hd
      · exact .inl ⟨(hsc ▸ hd : I.lowerFieldLayer.toCellScheme.scope (Fin.castAdd _ d) ⊆ _), hg⟩
      · exact .inr (.inr ⟨(hsc ▸ hd :
          I.lowerFieldLayer.toCellScheme.scope (Fin.castAdd _ d) ⊆ _), hg⟩)
  -- A cell below `(univ.erase y, 2)` and on the boundary lies below `(univ.erase y, 1)`.
  have hlow (e : Fin I.lowerFieldLayer.card)
      (he : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2))
      (hb : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)) :
      e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 1) := by
    refine ⟨he.1, ?_⟩
    rcases hb with hb | hb
    · have hsub : I.lowerFieldLayer.toCellScheme.scope e ⊆ {0} :=
        (subset_inter hb.1 he.1).trans (erase_inter_erase hxy hx hy).le
      exact (hwf.grade_le_card e).trans ((card_le_card hsub).trans (by simp))
    · exact hb.2
  -- The glued labelling: `w` on the boundary, the lift within the other coatom elsewhere.
  obtain ⟨g, hgb, hgo⟩ : ∃ g : Fin I.lowerFieldLayer.card → Label.{u},
      (∀ e, e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) → g e = w (Fin.castAdd _ e)) ∧
      ∀ e (he : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2)),
        ¬ (e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
          e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)) → g e = v ⟨e, he⟩ :=
    ⟨fun e ↦ if e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1) then w (Fin.castAdd _ e)
      else Rows.extendBot (univ.erase y, 2) v e,
      fun e hb ↦ ite_eq_left hb, fun e he hb ↦ (ite_eq_right hb).trans (Rows.extendBot_of_mem v he)⟩
  have hgD (e : Fin I.lowerFieldLayer.card)
      (he : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase y, 2)) : g e = v ⟨e, he⟩ := by
    by_cases hb : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)
    · rw [hgb e hb]
      exact (hvw ⟨e, hlow e he hb⟩).symm
    · exact hgo e he hb
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, 2)) (V := (univ, 1))
    (W := (univ.erase y, 2)) ?_ ?_ ?_ fun e _ ↦ hcover e, hgb, fun e ↦ ?_⟩
  · convert hw₁U using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hw₁V using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · convert hv using 1
    exact funext fun e ↦ hgD e e.2
  · by_cases hb : e ∈ I.lowerFieldLayer.toCellScheme.below (univ.erase x, 2) ∨
        e ∈ I.lowerFieldLayer.toCellScheme.below (univ, 1)
    · rw [hgb e hb]
      exact hag e hb
    · have he := ((hcover e).resolve_left fun h ↦ hb (.inl h)).resolve_left fun h ↦ hb (.inr h)
      rw [hgD e he]
      exact hvcap ⟨e, he⟩

/-- A boundary cell below `(univ, 2)` of the layer at grade two is a cell of the lower layer below
`(univ.erase x, 2)` or below `(univ, 1)`. -/
private theorem exists_castAdd_eq_of_boundary_two {x : Fin 3}
    {d : I.fieldLayerOne.toCellScheme.below (univ, 2)}
    (hd : (d : Fin I.fieldLayerOne.card) ∈ I.fieldLayerOne.toCellScheme.below (univ.erase x, 2) ∨
      (d : Fin I.fieldLayerOne.card) ∈ I.fieldLayerOne.toCellScheme.below (univ, 1)) :
    ∃ e, ∃ he : I.lowerFieldLayer.toCellScheme.grade e ≤ 2,
      d = ⟨Fin.castAdd _ e, Scheme.castAdd_mem_below he⟩ ∧
        (I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ.erase x, 2) ∨
          I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ, 1)) := by
  obtain ⟨e, he, rfl⟩ := Scheme.exists_castAdd_eq_of_boundary
    (fun h ↦ erase_ne_univ x (univ_subset_iff.mp h.1)) (fun h ↦ absurd h.2 (by decide)) hd
  refine ⟨e, he, rfl, ?_⟩
  have hgi : I.fieldLayerOne.toCellScheme.gradedIndex (Fin.castAdd _ e) =
      I.lowerFieldLayer.toCellScheme.gradedIndex e :=
    Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e
  rcases hd with hd | hd
  · exact .inl (hgi ▸ (hd : I.fieldLayerOne.toCellScheme.gradedIndex (Fin.castAdd _ e) ≤ _))
  · exact .inr (hgi ▸ (hd : I.fieldLayerOne.toCellScheme.gradedIndex (Fin.castAdd _ e) ≤ _))

/-- **Extension from the boundary at grade two, at a short positive cap.**  Along the row of a new
cell `u` of graded index `(univ, 2)`, at a cap `h` self-visible and short at `2` with `⊥ < h`,
every labelling lawful below `(univ.erase x, 2)` and below `(univ, 1)` that agrees with the row of
`u` capped at `h` on the boundary extends, unchanged there, to a labelling lawful below `(univ, 2)`
that agrees with the row of `u` capped at `h` everywhere: the boundary labelling is completed on
the lower layer along the catalogue entry `a` of `u`
(`Seed.exists_isLawfulBelow_lowerFieldLayer`), then extended through the new cells of grade two
(`Scheme.exists_extension_fieldLayer`, at a short cap). -/
theorem extendsFromBoundary_fieldLayerOne {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    {u : Fin I.fieldLayerOne.card}
    (hu : I.fieldLayerOne.toCellScheme.gradedIndex u = (univ, 2)) {h : Label.{u}}
    (hh : IsSelfVisible 2 h) (hs : IsShort 2 h) (hbot : ⊥ < h) :
    I.fieldLayerOne.rows.ExtendsFromBoundary (univ.erase x, 2) (univ, 1) (univ, 2) h
      (I.fieldLayerOne.rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
  set a := I.lowerFieldLayer.catalogueEntry 2 i
  have ha := Scheme.catalogueEntry_mem (S := I.lowerFieldLayer) (k := 2) i
  have hrowBelow (d : I.fieldLayerOne.toCellScheme.below (univ, 2)) :
      I.fieldLayerOne.rows.rowBelow (Fin.natAdd _ i) hu d = I.lowerFieldLayer.fieldRow 2 a d :=
    Scheme.fieldLayer_row_natAdd i _
  have hag (e : Fin I.lowerFieldLayer.card)
      (he : I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ.erase x, 2) ∨
        I.lowerFieldLayer.toCellScheme.gradedIndex e ≤ (univ, 1)) :
      min (w (Fin.castAdd _ e)) h = min (a e) h := by
    have hgi : I.fieldLayerOne.toCellScheme.gradedIndex (Fin.castAdd _ e) =
        I.lowerFieldLayer.toCellScheme.gradedIndex e :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e
    have := hwS ⟨_, Scheme.castAdd_mem_below (I.lowerFieldLayer_grade_le e)⟩
      (by
        rcases he with he | he
        · exact .inl (show I.fieldLayerOne.toCellScheme.gradedIndex (Fin.castAdd _ e) ≤ _ from
            hgi ▸ he)
        · exact .inr (show I.fieldLayerOne.toCellScheme.gradedIndex (Fin.castAdd _ e) ≤ _ from
            hgi ▸ he))
    rwa [hrowBelow, Scheme.fieldRow_castAdd] at this
  obtain ⟨g, hg, hgw, hga⟩ := I.exists_isLawfulBelow_lowerFieldLayer hxy hx hy hwU hwV
    (Scheme.mem_catalogue.mp ha).1 hh hag
  obtain ⟨r, hr, hrg, hrS⟩ := Scheme.exists_extension_fieldLayer
    (hS := I.not_univ_two_le_lowerFieldLayer) (p := g) hg ha hh hbot (.inl hs)
    fun d _ ↦ hga d
  refine ⟨r, hr, fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hrS d⟩
  obtain ⟨e, he, rfl, hb⟩ := I.exists_castAdd_eq_of_boundary_two hd
  rw [hrg e he]
  exact hgw e hb

/-- **Extension from the boundary at grade two, at the cap `⊥`**: the boundary labelling is
completed on the lower layer along the bottom labelling, then extended through the new cells of
grade two (`Scheme.exists_isLawfulBelow_fieldLayer`). -/
theorem extendsFromBoundary_bot_fieldLayerOne {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    I.fieldLayerOne.rows.ExtendsFromBoundary (univ.erase x, 2) (univ, 1) (univ, 2) ⊥
      fun _ ↦ ⊥ := by
  intro w hwU hwV _
  obtain ⟨g, hg, hgw, -⟩ := I.exists_isLawfulBelow_lowerFieldLayer hxy hx hy hwU hwV
    (Rows.isLawful_const_bot (R := I.lowerFieldLayer.rows)) (isSelfVisible_bot 2)
    fun _ _ ↦ by simp
  obtain ⟨r, hr, hrg⟩ := Scheme.exists_isLawfulBelow_fieldLayer
    (hS := I.not_univ_two_le_lowerFieldLayer) (p := g) hg
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he, rfl, hb⟩ := I.exists_castAdd_eq_of_boundary_two hd
  rw [hrg e he]
  exact hgw e hb

/-! ### The lifts at grade two -/

/-- **The lift from a coatom to the full face at grade two.**  For the coatoms `C = univ.erase x`
and `univ.erase y`, the short-cap one-grade lift `CellScheme.Rows.cappedLift_of_boundary_short` at
`j = 1` applies to the layer at grade two, with `U = (C, 2)`, `V = (univ, 1)` and `O = (C, 1)`:
the lift at the lower grade and the lift from `O` to `V` are the lift at grade one
(`Seed.cappedLift_fieldLayerOne_one`), the cells below both `U` and `V` lie below `O`, the field
layer at grade two extends from the boundary at `⊥` and at every positive cap short at `2`, and its
new rows are lawful, short at `2` and never the formal top.  The lift keeps the cap at every cell
below `(univ, 2)`: the cells of the lower layer, by the lift at grade one used as the boundary lift
into `(univ, 1)`, and the other coatom's cells of grade two, by the lift within its face. -/
theorem cappedLift_fieldLayerOne_two {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0) :
    I.fieldLayerOne.rows.CappedLift (X := (univ.erase x, 2)) (Y := (univ, 2))
      ⟨erase_subset _ _, le_rfl⟩ := by
  have hL1 := I.cappedLift_fieldLayerOne_one hxy hx hy
  refine Rows.cappedLift_of_boundary_short (C := univ.erase x) (B := univ) (j := 1)
    (U := (univ.erase x, 2)) (V := (univ, 1)) (O := (univ.erase x, 1)) (erase_subset _ _) ?_ hL1
    le_rfl ⟨subset_rfl, one_le_two⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, one_le_two⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (Rows.cappedLift_refl _) hL1
    (I.extendsFromBoundary_bot_fieldLayerOne hxy hx hy) ?_ fun u hu ↦
      ⟨Scheme.isConsistent_fieldLayer I.isConsistent_lowerFieldLayer u, ?_, ?_,
        fun h hh hs hbot ↦ I.extendsFromBoundary_fieldLayerOne hxy hx hy hu hh hs hbot⟩
  · -- A cell of graded index `(univ.erase x, 2)`: an old cell of the amalgam.
    obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (univ.erase x, 2)
      ⟨I.erase_mem_faces hx, two_pos, (card_erase x).ge⟩ (erase_ne_univ x)
    refine ⟨Fin.castAdd _ (Fin.castAdd _ d), ?_⟩
    exact (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
      ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd)
  · -- The cell of the orbit code of the bottom labelling.
    obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
      (S := I.lowerFieldLayer) (k := 2) (p := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _))
    exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).1
  · intro d
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq hu
    exact (Scheme.isShort_ne_top_row_fieldLayer i _).2

/-- **The lift from a coatom to the full face at grade two, coordinate by coordinate.**  At every
cap `c` self-visible at `2`, a prescription lawful below the coatom `(univ.erase x, 2)` and an
ambient lawful below `(univ, 2)` with the same observation at `c` below the coatom have a lift
lawful below `(univ, 2)` that reads the prescription literally and keeps the observation of the
ambient at `c` at every cell below `(univ, 2)`: the cells of both layers and the other coatom's
cells included. -/
theorem exists_lift_fieldLayerOne_two {x y : Fin 3} (hxy : x ≠ y) (hx : x ≠ 0) (hy : y ≠ 0)
    {c : Label.{u}} (hc : IsSelfVisible 2 c)
    (p : I.fieldLayerOne.toCellScheme.below (univ.erase x, 2) → Label.{u})
    (q : I.fieldLayerOne.toCellScheme.below (univ, 2) → Label.{u})
    (hp : I.fieldLayerOne.rows.IsLawfulBelow _ p) (hq : I.fieldLayerOne.rows.IsLawfulBelow _ q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _
      (show ((univ.erase x, 2) : Finset (Fin 3) × ℕ) ≤ (univ, 2) from
        ⟨erase_subset _ _, le_rfl⟩)) d)) c = min (p d) c) :
    ∃ q' : I.fieldLayerOne.toCellScheme.below (univ, 2) → Label.{u},
      I.fieldLayerOne.rows.IsLawfulBelow _ q' ∧ (∀ d, min (q' d) c = min (q d) c) ∧
        ∀ d, q' (Set.inclusion (CellScheme.below_mono _
          (show ((univ.erase x, 2) : Finset (Fin 3) × ℕ) ≤ (univ, 2) from
            ⟨erase_subset _ _, le_rfl⟩)) d) = p d :=
  (Rows.cappedLift_iff_forall_exists _).mp (I.cappedLift_fieldLayerOne_two hxy hx hy) c hc p q
    hp hq hpq


/-! ### Bountifulness and the completion -/

/-- **Lifts off the full face**: between graded faces `X ≤ Y` with `Y` not on the ground set, the
layer at grade two lifts capped, since the amalgam is bountiful and a source prefix there. -/
theorem cappedLift_fieldLayerOne_of_ne_univ {X Y : Finset (Fin 3) × ℕ}
    (hX : X ∈ I.fieldLayerOne.toCellScheme.gradedFaces)
    (hY : Y ∈ I.fieldLayerOne.toCellScheme.gradedFaces) (hXY : X ≤ Y) (hYne : Y.1 ≠ univ) :
    I.fieldLayerOne.rows.CappedLift hXY := by
  have h := I.isSourcePrefix_fieldLayerOne hYne
  refine h.cappedLift_of_isBountiful ?_ hX hY hXY le_rfl
  have hc : I.fieldLayerOne.rows.comap h.isLowerEmbedding = I.amalgam.rows := by
    change (I.fieldLayerOne.rows.comap (Scheme.isLowerEmbedding_fieldLayer _ _ _)).comap
      (Scheme.isLowerEmbedding_fieldLayer _ _ _) = _
    rw [Scheme.comap_rows_fieldLayer, Scheme.comap_rows_fieldLayer]
  rw [hc]
  exact I.isBountiful

/-- **The layer at grade two is bountiful**, by the coatoms
(`CellScheme.Rows.isBountiful_of_coatoms`): off the full face the lifts are those of the amalgam,
through the source prefix; from each coatom to the full face they are the lifts at grade `0` (no
cells), at grade `1` (`Seed.cappedLift_fieldLayerOne_one`) and at grade `2`
(`Seed.cappedLift_fieldLayerOne_two`). -/
theorem isBountiful_fieldLayerOne : I.fieldLayerOne.rows.IsBountiful := by
  have hwf := I.isWellFormed_fieldLayerOne.isWellFormed
  have hle (z : Fin 3) (j : ℕ) (hj : j ≤ #(univ.erase z)) : j = 0 ∨ j = 1 ∨ j = 2 := by
    rw [card_erase] at hj
    omega
  have h21 : (Fin.last 2 : Fin 3) ≠ Fin.castSucc (Fin.last 1) := by decide
  have h20 : (Fin.last 2 : Fin 3) ≠ 0 := by decide
  have h10 : (Fin.castSucc (Fin.last 1) : Fin 3) ≠ 0 := by decide
  refine Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 2)
    (b := Fin.castSucc (Fin.last 1)) (mem_univ _) (mem_univ _) I.subset_or_subset
    I.erase_last_mem_faces I.erase_castSucc_mem_faces
    (fun X Y hX hY hXY hYne ↦ I.cappedLift_fieldLayerOne_of_ne_univ hX hY hXY hYne)
    (fun j hj ↦ ?_) fun j hj ↦ ?_
  · rcases hle _ j hj with rfl | rfl | rfl
    · exact hwf.cappedLift _ (Or.inl rfl) _
    · exact I.cappedLift_fieldLayerOne_one h21 h20 h10
    · exact I.cappedLift_fieldLayerOne_two h21 h20 h10
  · rcases hle _ j hj with rfl | rfl | rfl
    · exact hwf.cappedLift _ (Or.inl rfl) _
    · exact I.cappedLift_fieldLayerOne_one h21.symm h10 h20
    · exact I.cappedLift_fieldLayerOne_two h21.symm h10 h20

/-- Every cell of the layer at grade two has grade at most `2`. -/
theorem fieldLayerOne_grade_le (d : Fin I.fieldLayerOne.card) :
    I.fieldLayerOne.toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left d =>
    exact (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ d).trans_le
      (I.lowerFieldLayer_grade_le d)
  | right i => exact (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i).le

/-- **The layer at grade two is legal below the full grade**: well formed, coded, consistent,
bountiful, of grades below `3`, and complete below the full grade (the old cells off the full
face, the cells of the orbit code of the bottom labelling at `(univ, 1)` and `(univ, 2)`). -/
theorem isLegalBelowFullGrade_fieldLayerOne : I.fieldLayerOne.IsLegalBelowFullGrade where
  isWellFormed := I.isWellFormed_fieldLayerOne
  isCoded := Scheme.isCoded_fieldLayer (Scheme.isCoded_fieldLayer I.amalgam.isCoded)
  isConsistent := Scheme.isConsistent_fieldLayer I.isConsistent_lowerFieldLayer
  isBountiful := I.isBountiful_fieldLayerOne
  grade_lt d := (I.fieldLayerOne_grade_le d).trans_lt (by omega)
  exists_gradedIndex_eq X hX hX2 := by
    obtain ⟨C, j⟩ := X
    have hj0 : 0 < j := hX.2.1
    by_cases hC : C = univ
    · subst hC
      rcases (show j = 1 ∨ j = 2 by simp only at hX2; omega) with rfl | rfl
      · obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
          (S := I.amalgam.toScheme) (k := 1) (p := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _))
        exact ⟨Fin.castAdd _ (Fin.natAdd _ i),
          (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
            (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)⟩
      · obtain ⟨i, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
          (S := I.lowerFieldLayer) (k := 2) (p := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _))
        exact ⟨Fin.natAdd _ i, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i⟩
    · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq _ hX hC
      exact ⟨Fin.castAdd _ (Fin.castAdd _ d),
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
          ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d).trans hd)⟩

/-- **Extension through both layers**: every lawful labelling of the amalgam extends, unchanged at
the old cells, to a lawful labelling of the layer at grade two (`Scheme.exists_isLawful_fieldLayer`
twice). -/
theorem exists_isLawful_fieldLayerOne {p : Fin I.amalgam.card → Label.{u}}
    (hp : I.amalgam.rows.IsLawful p) :
    ∃ r, I.fieldLayerOne.rows.IsLawful r ∧ ∀ d, r (Fin.castAdd _ (Fin.castAdd _ d)) = p d := by
  obtain ⟨r₁, hr₁, hr₁p⟩ := Scheme.exists_isLawful_fieldLayer (S := I.amalgam.toScheme) (k := 1)
    (hS := I.not_univ_le 1) hp
  obtain ⟨r₂, hr₂, hr₂p⟩ := Scheme.exists_isLawful_fieldLayer (S := I.lowerFieldLayer) (k := 2)
    (hS := I.not_univ_two_le_lowerFieldLayer) hr₁
  exact ⟨r₂, hr₂, fun d ↦ (hr₂p _).trans (hr₁p d)⟩

/-- **The completion below the full grade of a seed on three points**: the layer at grade two over
the lower layer, with the old cells along `Fin.castAdd` twice, and the extension of the glued
labelling through both layers. -/
noncomputable def completionBelowFullGradeOne : CompletionBelowFullGrade I where
  scheme := I.fieldLayerOne
  embed := (Fin.castAddOrderEmb _).trans (Fin.castAddOrderEmb _)
  isLowerEmbedding :=
    (Scheme.isLowerEmbedding_fieldLayer _ _ _).comp (Scheme.isLowerEmbedding_fieldLayer _ _ _)
  scope_embed d := (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
    (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ d)
  comap_rows := by
    change (I.fieldLayerOne.rows.comap (Scheme.isLowerEmbedding_fieldLayer _ _ _)).comap
      (Scheme.isLowerEmbedding_fieldLayer _ _ _) = _
    rw [Scheme.comap_rows_fieldLayer, Scheme.comap_rows_fieldLayer]
  mem_range_embed z hz := by
    induction z using Fin.addCases with
    | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
    | left z =>
      induction z using Fin.addCases with
      | right i =>
        exact absurd ((Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans
          (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i)) hz
      | left d => exact ⟨d, rfl⟩
  faces_eq := rfl
  isLegalBelowFullGrade := I.isLegalBelowFullGrade_fieldLayerOne
  label := (I.exists_isLawful_fieldLayerOne I.amalgam.isLawful).choose
  isLawful := (I.exists_isLawful_fieldLayerOne I.amalgam.isLawful).choose_spec.1
  label_embed := (I.exists_isLawful_fieldLayerOne I.amalgam.isLawful).choose_spec.2

/-- **The completion at arity one.**  Every seed on three points (two coatom types on two points
over a common face on one point) has a completion below the full grade, whose completed scheme
extends every lawful labelling of the amalgam, not only the glued one.  No hypothesis on the stage
is used. -/
theorem exists_completionBelowFullGrade_one :
    ∃ F : CompletionBelowFullGrade I, ∀ p : Fin I.amalgam.card → Label.{u},
      I.amalgam.rows.IsLawful p → ∃ r, F.scheme.rows.IsLawful r ∧ ∀ d, r (F.embed d) = p d :=
  ⟨I.completionBelowFullGradeOne, fun _ hp ↦ I.exists_isLawful_fieldLayerOne hp⟩

/-- **A seed on three points has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_one : Nonempty (CompletionBelowFullGrade I) :=
  ⟨I.completionBelowFullGradeOne⟩

end Seed

/-- **The completion at the small arities**: every seed on at most three points (`m ≤ 1`) has a
completion below the full grade (`Seed.nonempty_completionBelowFullGrade_zero`,
`Seed.nonempty_completionBelowFullGrade_one`). -/
theorem Seed.nonempty_completionBelowFullGrade_of_le_one {α : Ordinal.{u}} {m : ℕ} (hm : m ≤ 1)
    (I : Seed.{u} α m) : Nonempty (CompletionBelowFullGrade I) :=
  match m, hm, I with
  | 0, _, I => I.nonempty_completionBelowFullGrade_zero
  | 1, _, I => I.nonempty_completionBelowFullGrade_one

end VaughtConjecture
