/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Apex
import VaughtConjecture.Extension.Gluing

/-!
# The part of a legal scheme below the full grade

Roadmap, Layer 3 (finite extension constructions), for Layer 4, output 2 (forcing donors,
`ForcingDonors`); semantic contract, items 3–4.

**The part below the full grade** (`Scheme.partBelowFullGrade`).  For a scheme `S` on `n` points,
keep the cells of grade below `n`, in their order (`Scheme.embBelowFullGrade`), with their scopes,
grades, and rows, and the same faces.  In a well-formed scheme the cells removed are exactly those
of graded index `(univ, n)`, and the cells kept are the cells below `(univ, n - 1)`: a lower set,
so the inclusion is a lower embedding (`Scheme.isLowerEmbedding_embBelowFullGrade`) and the rows
pull back along it.

**A legal scheme has a part below the full grade that is legal below the full grade**
(`Scheme.IsLegal.isLegalBelowFullGrade_partBelowFullGrade`):

* well-formedness, coding, and consistency pass to the cells of a lower set;
* completeness below the full grade: a graded face of grade below `n` is the graded index of a
  cell of `S`, and that cell has grade below `n`;
* bountifulness, at a fixed grade (`CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst`): a
  lift from `X` to `(Y.1, X.2)` with `X.1 = Y.1` is within a face, and any rows have it
  (`CellScheme.Rows.cappedLift_of_fst_eq`); otherwise `X.1` is a proper subset of `Y.1`, so the
  grade `X.2` is below `n`, every cell below `X` or `(Y.1, X.2)` is kept, and the lift of `S`
  pulls back (`CellScheme.Rows.CappedLift.comap`).

For a stage type the labels are kept (`StageType.partBelowFullGrade`), and the faces along
embeddings onto proper subsets are unchanged (`StageType.restrictFace_partBelowFullGrade`): a cell
visible through such an embedding has scope of fewer than `n` points, hence grade below `n`.

So every legal stage type on `n` points with a face `t` along a proper embedding gives a stage type
legal below the full grade with the same face, to which the apex (`StageType.addApex`) or a tied
apex (`StageType.addTiedApex`) can be added.  This replaces the completion below the full grade
wherever only some legal type with a prescribed proper face is needed: there the coatom extension
property (`StageType.HasCoatomExtensions`) suffices.

## Placement

Layer 3 of `roadmap/README.md` (3.1, (R6): forcing donors from the plain form).
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n)

/-! ### The cells below the full grade -/

/-- The cells of `S` of grade below `n`. -/
def cellsBelowFullGrade : Finset (Fin S.card) := {d | S.toCellScheme.grade d < n}

/-- A cell is below the full grade exactly when its grade is below `n`. -/
@[simp] theorem mem_cellsBelowFullGrade {d : Fin S.card} :
    d ∈ S.cellsBelowFullGrade ↔ S.toCellScheme.grade d < n := by
  simp [cellsBelowFullGrade]

/-- The enumeration in increasing order of the cells of grade below `n`. -/
noncomputable def embBelowFullGrade : Fin #S.cellsBelowFullGrade ↪o Fin S.card :=
  S.cellsBelowFullGrade.orderEmbOfFin rfl

/-- The enumerated cells have grade below `n`. -/
theorem grade_embBelowFullGrade_lt (i : Fin #S.cellsBelowFullGrade) :
    S.toCellScheme.grade (S.embBelowFullGrade i) < n :=
  S.mem_cellsBelowFullGrade.mp (S.cellsBelowFullGrade.orderEmbOfFin_mem rfl i)

/-- Every cell of grade below `n` is enumerated. -/
theorem mem_range_embBelowFullGrade {d : Fin S.card} (hd : S.toCellScheme.grade d < n) :
    d ∈ Set.range S.embBelowFullGrade := by
  rw [embBelowFullGrade, range_orderEmbOfFin]
  exact mem_coe.mpr (S.mem_cellsBelowFullGrade.mpr hd)

/-- **The cells below the full grade form a lower embedding**: every cell below a cell of grade
below `n` has grade below `n`. -/
theorem isLowerEmbedding_embBelowFullGrade :
    (S.toCellScheme.reindex S.embBelowFullGrade).IsLowerEmbedding S.toCellScheme
      S.embBelowFullGrade where
  injective := S.embBelowFullGrade.injective
  grade_eq _ := rfl
  le_iff _ _ := Iff.rfl
  mem_range t _ hd := S.mem_range_embBelowFullGrade (lt_of_le_of_lt hd.2
    (S.grade_embBelowFullGrade_lt t))

/-- The **part below the full grade** of `S`: the cells of grade below `n`, in their order, with
their scopes, grades, and rows, and the faces of `S`. -/
noncomputable def partBelowFullGrade : Scheme.{u} n where
  card := #S.cellsBelowFullGrade
  toCellScheme := S.toCellScheme.reindex S.embBelowFullGrade
  rows := S.rows.comap S.isLowerEmbedding_embBelowFullGrade

/-- Below a pair of grade below `n`, the cells of the part below the full grade are the cells
of `S`. -/
theorem image_embBelowFullGrade_below {X : Finset (Fin n) × ℕ} (hX : X.2 < n) :
    S.embBelowFullGrade '' (S.toCellScheme.reindex S.embBelowFullGrade).below X =
      S.toCellScheme.below X := by
  ext d
  refine ⟨fun ⟨i, hi, hid⟩ ↦ hid ▸ hi, fun hd ↦ ?_⟩
  obtain ⟨i, rfl⟩ := S.mem_range_embBelowFullGrade (lt_of_le_of_lt hd.2 hX)
  exact ⟨i, hd, rfl⟩

/-- **The part below the full grade of a legal scheme is legal below the full grade.** -/
theorem IsLegal.isLegalBelowFullGrade_partBelowFullGrade (hS : S.IsLegal) :
    S.partBelowFullGrade.IsLegalBelowFullGrade where
  isWellFormed := ⟨hS.isWellFormed.ground_eq, hS.isWellFormed.isWellFormed.reindex _⟩
  isCoded _ _ := hS.isCoded _ _
  isConsistent := hS.isConsistent.comap S.isLowerEmbedding_embBelowFullGrade
  isBountiful := by
    refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
    by_cases hXY : X.1 = Y.1
    · exact CellScheme.Rows.cappedLift_of_fst_eq _ hXY
    -- `X.1` is a proper subset of `Y.1`, so its grade is below `n`.
    have hlt : X.2 < n := by
      have hss : X.1 ⊂ Y.1 := ssubset_of_subset_of_ne h.1 hXY
      have h1 := card_lt_card hss
      have h2 : #Y.1 ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
      exact lt_of_le_of_lt hX.2.2 (lt_of_lt_of_le h1 h2)
    have hY' : (Y.1, X.2) ∈ S.toCellScheme.gradedFaces :=
      ⟨hY.1, hX.2.1, hX.2.2.trans (card_le_card h.1)⟩
    exact (hS.isBountiful hX hY' ⟨h.1, le_rfl⟩).comap S.isLowerEmbedding_embBelowFullGrade
      (S.image_embBelowFullGrade_below hlt) (S.image_embBelowFullGrade_below hlt) le_rfl
  grade_lt := S.grade_embBelowFullGrade_lt
  exists_gradedIndex_eq X hX hXn := by
    obtain ⟨d, hd⟩ := hS.isComplete X hX
    have hdn : S.toCellScheme.grade d < n := by rw [← hd] at hXn; exact hXn
    obtain ⟨i, rfl⟩ := S.mem_range_embBelowFullGrade hdn
    exact ⟨i, hd⟩

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} (t : StageType.{u} α n)

/-- The **part below the full grade** of a stage type: the part below the full grade of its scheme
(`Scheme.partBelowFullGrade`), with the labels of the cells kept. -/
noncomputable def partBelowFullGrade : StageType.{u} α n where
  toScheme := t.toScheme.partBelowFullGrade
  label := t.label ∘ t.toScheme.embBelowFullGrade
  isWellFormed := ⟨t.isWellFormed.ground_eq, t.isWellFormed.isWellFormed.reindex _⟩
  isCoded _ _ := t.isCoded _ _
  isLawful := t.isLawful.comap t.toScheme.isLowerEmbedding_embBelowFullGrade
  atStage _ := t.atStage _

/-- The label of a cell of the part below the full grade is its label in `t`. -/
@[simp] theorem partBelowFullGrade_label (i : Fin t.partBelowFullGrade.card) :
    t.partBelowFullGrade.label i = t.label (t.toScheme.embBelowFullGrade i) := rfl

variable {t}

/-- **The part below the full grade of a legal stage type is legal below the full grade.** -/
theorem IsLegal.isLegalBelowFullGrade_partBelowFullGrade (ht : t.IsLegal) :
    t.partBelowFullGrade.IsLegalBelowFullGrade :=
  Scheme.IsLegal.isLegalBelowFullGrade_partBelowFullGrade t.toScheme ht

variable (t) in
/-- **The proper faces of the part below the full grade are those of `t`**: along an embedding
whose image is not the whole ground set, the face maps agree, including definedness. -/
theorem restrictFace_partBelowFullGrade (f : Fin m ↪ Fin n) (hf : univ.map f ≠ univ) :
    restrictFace f t.partBelowFullGrade = restrictFace f t := by
  refine (restrictFace_eq_of_strictMono (t := t) (s := t.partBelowFullGrade) f
    (φ := t.toScheme.embBelowFullGrade) t.toScheme.embBelowFullGrade.strictMono
    t.toScheme.isLowerEmbedding_embBelowFullGrade (fun _ ↦ rfl) rfl rfl rfl (fun _ ↦ rfl)
    fun z hz ↦ ?_).symm
  refine t.toScheme.mem_range_embBelowFullGrade ?_
  -- a cell visible through `f` has scope inside the proper subset `univ.map f`
  have hsub : t.toCellScheme.scope z ⊆ univ.map f := fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hz (mem_coe.mpr hx)
    exact mem_map_of_mem _ (mem_univ y)
  have hlt : #(univ.map f) < n := by
    have h := card_lt_card (ssubset_univ_iff.mpr hf)
    rwa [card_univ, Fintype.card_fin] at h
  exact lt_of_le_of_lt (t.isWellFormed.isWellFormed.grade_le_card z)
    (lt_of_le_of_lt (card_le_card hsub) hlt)

end StageType

end VaughtConjecture
