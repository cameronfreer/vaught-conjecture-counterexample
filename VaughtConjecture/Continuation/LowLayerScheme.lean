/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowProfile
import VaughtConjecture.Extension.FieldLayer

/-!
# The LOW layer scheme

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3); semantic contract,
items 3, 4 and 8.

The layer of controllers of the LOW construction [Kni26, §3.3], built with the appending of cells
of full scope of `VaughtConjecture.Extension.FieldLayer`.  Let `S` be a scheme on `n` points with
no cell above `(univ, K)`, `G` a finite set of labels, and `C` a finite catalogue of **profiles**,
labellings of the **fields** `Fin S.card ⊕ Unit` (the cells of `S` and one more field, the
cutoff).  The **LOW layer** (`Scheme.lowLayer S K G C hS`) appends to `S` one cell of scope `univ`
and grade `K` for each profile `a` of `C` (`Scheme.lowEntry`), whose row is the **LOW row** of `a`
(`Scheme.lowRow`): `a` on the old cells, and on the new cell of a profile `b` the agreement height
of `a` and `b` in `G` (`Label.agreementHeight`), which compares the cutoffs as well as the
cells.  This is the field row of `VaughtConjecture.Extension.FieldLayer` with the cutoff as an
extra field.

**Rows** (`Scheme.lowRow_castAdd`, `Scheme.lowRow_natAdd`, `Scheme.rowAt_lowLayer_castAdd`,
`Scheme.rowAt_lowLayer_natAdd`): the row of the new cell of `a` reads the old cells of grade at most
`K` at `a` and the new cells at agreement heights; these are the clauses of
`StageType.IsLowLayer`.

**Consistency** (`Scheme.isConsistent_lowLayer`, compiled in this repository).  If `S` is
consistent and every profile of `C` is lawful on the old cells, with values at most a largest
member of `G`, whose members are self-visible at `K` and include `⊥`, then the LOW layer is
consistent: the LOW row of every profile is a lawful section of the layer
(`Scheme.isLawful_lowRow`).  On the old cells it is the profile; at a new cell its locality is the
identity capped at the agreement height, by the ultrametric inequality
(`Scheme.min_lowRow_agreementHeight`); availability at the full face holds at the cell of the
profile itself, read at the largest member of `G`.  The layer is well formed and, when the
profiles and `G` lie below `ω²`, coded (`Scheme.isWellFormed_lowLayer`, `Scheme.isCoded_lowLayer`).
No strong coding of the rows of `S` is used.

**Completeness at the layer** (`Scheme.exists_gradedIndex_eq_lowLayer`): when `C` is nonempty,
`(univ, K)` is the graded index of a cell; below it, the graded faces are those of `S`.

**Bountifulness** of the displays built from LOW layers is not proved here: it is the open part
of the construction (`StageType.HasLowLayers`, in `VaughtConjecture.MainTheorem.LowDisplayRoute`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (K : ℕ) (G : Finset Label.{u})
  (C : Finset (Fin S.card ⊕ Unit → Label.{u}))

/-- The profile of the `i`-th new cell. -/
noncomputable def lowEntry (i : Fin C.card) : Fin S.card ⊕ Unit → Label.{u} :=
  (C.equivFin.symm i).1

theorem lowEntry_mem (i : Fin C.card) : lowEntry S C i ∈ C := (C.equivFin.symm i).2

theorem exists_lowEntry_eq {a : Fin S.card ⊕ Unit → Label.{u}} (ha : a ∈ C) :
    ∃ i, lowEntry S C i = a :=
  ⟨C.equivFin ⟨a, ha⟩, by simp [lowEntry]⟩

/-- The **LOW row** of a profile `a`: `a` on the old cells, and on the new cell of a profile `b`
the agreement height of `a` and `b` in `G`. -/
noncomputable def lowRow (a : Fin S.card ⊕ Unit → Label.{u}) : Fin (S.card + C.card) → Label.{u} :=
  Fin.append (fun d ↦ a (Sum.inl d)) fun j ↦ agreementHeight G a (lowEntry S C j)

variable {S G C} in
@[simp] theorem lowRow_castAdd (a : Fin S.card ⊕ Unit → Label.{u}) (d : Fin S.card) :
    lowRow S G C a (Fin.castAdd _ d) = a (Sum.inl d) :=
  Fin.append_left _ _ d

variable {S G C} in
@[simp] theorem lowRow_natAdd (a : Fin S.card ⊕ Unit → Label.{u}) (j : Fin C.card) :
    lowRow S G C a (Fin.natAdd _ j) = agreementHeight G a (lowEntry S C j) :=
  Fin.append_right _ _ j

/-- **The LOW layer**: `S` with one cell of scope `univ` and grade `K` for each profile of `C`,
whose row is the LOW row of the profile. -/
noncomputable abbrev lowLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.appendFullCells K C.card (fun i ↦ lowRow S G C (lowEntry S C i)) hS

variable {S K G C} {hS : ∀ d, ¬ ((univ : Finset (Fin n)), K) ≤ S.toCellScheme.gradedIndex d}

/-- **Two LOW rows agree capped at the agreement height of their profiles.** -/
theorem min_lowRow_agreementHeight (hG : ⊥ ∈ G) (a b : Fin S.card ⊕ Unit → Label.{u})
    (x : Fin (S.card + C.card)) :
    min (lowRow S G C a x) (agreementHeight G a b) =
      min (lowRow S G C b x) (agreementHeight G a b) := by
  induction x using Fin.addCases with
  | left d =>
    rw [lowRow_castAdd, lowRow_castAdd]
    exact (agreementHeight_spec hG a b).2 _
  | right j =>
    rw [lowRow_natAdd, lowRow_natAdd]
    exact agreementHeight_tri hG a b _

/-- **The LOW row of a profile is a lawful section of the LOW layer**, for a profile `a` of `C`
lawful on the old cells, when `⊥ ∈ G`, the members of `G` are self-visible at `K`, and some member
`y` of `G` lies above every member of `G` and every value of `a`. -/
theorem isLawful_lowRow (hG : ⊥ ∈ G) (hvis : ∀ x ∈ G, IsSelfVisible K x) {y : Label.{u}}
    (hy : y ∈ G) (hmax : ∀ x ∈ G, x ≤ y) {a : Fin S.card ⊕ Unit → Label.{u}} (ha : a ∈ C)
    (hlaw : S.rows.IsLawful fun d ↦ a (Sum.inl d)) (hay : ∀ f, a f ≤ y) :
    (S.lowLayer K G C hS).rows.IsLawful (lowRow S G C a) := by
  refine isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s _ ↦ ?_
  · convert hlaw using 1
    exact funext fun d ↦ lowRow_castAdd a d
  · rw [lowRow_natAdd]
    exact hvis _ (agreementHeight_spec hG _ _).1
  · have hc := hvis _ (agreementHeight_spec hG a (lowEntry S C i)).1
    convert (TransformsTo.refl (fun t : (S.appendFullCellsScheme K C.card).below
      ((S.appendFullCellsScheme K C.card).gradedIndex (Fin.natAdd S.card i)) ↦
        (S.appendFullCellsScheme K C.card).grade t)
          fun t ↦ lowRow S G C (lowEntry S C i) t.1)
      |>.min_const (K := K) (fun t ↦ t.2.2.trans (appendFullCellsScheme_grade_natAdd S K _ i).le)
        hc using 1
    funext t
    rw [lowRow_natAdd]
    exact min_lowRow_agreementHeight hG a _ t.1
  · obtain ⟨i, hi⟩ := exists_lowEntry_eq S C ha
    refine ⟨i, ?_⟩
    rw [lowRow_natAdd, hi, agreementHeight_self hy hmax]
    induction s using Fin.addCases with
    | left d => rw [lowRow_castAdd]; exact hay _
    | right j => rw [lowRow_natAdd]; exact hmax _ (agreementHeight_spec hG _ _).1

/-- **The LOW layer is consistent**, under the hypotheses of `Scheme.isLawful_lowRow` for every
profile of `C`. -/
theorem isConsistent_lowLayer (hcons : S.rows.IsConsistent) (hG : ⊥ ∈ G)
    (hvis : ∀ x ∈ G, IsSelfVisible K x) {y : Label.{u}} (hy : y ∈ G) (hmax : ∀ x ∈ G, x ≤ y)
    (hC : ∀ a ∈ C, S.rows.IsLawful (fun d ↦ a (Sum.inl d)) ∧ ∀ f, a f ≤ y) :
    (S.lowLayer K G C hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦ isLawful_lowRow hG hvis hy hmax (lowEntry_mem S C i)
    (hC _ (lowEntry_mem S C i)).1 (hC _ (lowEntry_mem S C i)).2

/-- **The LOW layer is well formed** when `(univ, K)` is a graded face. -/
theorem isWellFormed_lowLayer (hwf : S.IsWellFormed) (hK0 : 0 < K) (hKn : K ≤ n) :
    (S.lowLayer K G C hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf hK0 hKn

/-- **The LOW layer is coded** when the profiles and `G` lie below `ω ^ 2`. -/
theorem isCoded_lowLayer (hc : S.IsCoded) (hG : ⊥ ∈ G)
    (hGω : ∀ x ∈ G, x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}))
    (hCω : ∀ a ∈ C, ∀ f, a f < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (S.lowLayer K G C hS).IsCoded :=
  isCoded_appendFullCells hc fun i x ↦ by
    induction x using Fin.addCases with
    | left d => rw [lowRow_castAdd]; exact hCω _ (lowEntry_mem S C i) _
    | right j => rw [lowRow_natAdd]; exact hGω _ (agreementHeight_spec hG _ _).1

/-- **Completeness at the layer**: when `C` is nonempty, `(univ, K)` is the graded index of a
new cell. -/
theorem exists_gradedIndex_eq_lowLayer (hC : C.Nonempty) :
    ∃ s, (S.lowLayer K G C hS).toCellScheme.gradedIndex s = (univ, K) := by
  obtain ⟨a, ha⟩ := hC
  obtain ⟨i, -⟩ := exists_lowEntry_eq S C ha
  exact ⟨Fin.natAdd S.card i, appendFullCellsScheme_gradedIndex_natAdd S K _ i⟩

/-- **The LOW layer reads an old cell at the profile**: the new cell of a profile reads every old
cell of grade at most `K` at the profile. -/
theorem rowAt_lowLayer_castAdd (i : Fin C.card) {d : Fin S.card}
    (hd : S.toCellScheme.grade d ≤ K) :
    (S.lowLayer K G C hS).rowAt (Fin.natAdd S.card i) (Fin.castAdd C.card d) =
      lowEntry S C i (Sum.inl d) := by
  have hmem : Fin.castAdd C.card d ∈ (S.lowLayer K G C hS).toCellScheme.below
      ((S.lowLayer K G C hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [CellScheme.mem_below]
    change (S.appendFullCellsScheme K C.card).gradedIndex (Fin.castAdd C.card d) ≤
      (S.appendFullCellsScheme K C.card).gradedIndex (Fin.natAdd S.card i)
    rw [appendFullCellsScheme_gradedIndex_castAdd, appendFullCellsScheme_gradedIndex_natAdd]
    exact ⟨subset_univ _, hd⟩
  rw [rowAt_of_mem hmem, appendFullCells_row_natAdd, lowRow_castAdd]

/-- **The LOW layer reads a new cell at the agreement height** of the two profiles. -/
theorem rowAt_lowLayer_natAdd (i j : Fin C.card) :
    (S.lowLayer K G C hS).rowAt (Fin.natAdd S.card i) (Fin.natAdd S.card j) =
      agreementHeight G (lowEntry S C i) (lowEntry S C j) := by
  have hmem : Fin.natAdd S.card j ∈ (S.lowLayer K G C hS).toCellScheme.below
      ((S.lowLayer K G C hS).toCellScheme.gradedIndex (Fin.natAdd S.card i)) := by
    rw [CellScheme.mem_below]
    change (S.appendFullCellsScheme K C.card).gradedIndex (Fin.natAdd S.card j) ≤
      (S.appendFullCellsScheme K C.card).gradedIndex (Fin.natAdd S.card i)
    rw [appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]
  rw [rowAt_of_mem hmem, appendFullCells_row_natAdd, lowRow_natAdd]

end VaughtConjecture.Scheme
