/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerStep
import VaughtConjecture.Extension.FieldLayer

/-!
# The multi-layer step on five points

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: several
new cells at each graded face of full scope, as a named hypothesis on an arbitrary seed, and the
completion from it); semantic contract, items 2–4.

Let `I` be a seed on five points (`m = 3`), with coatoms `C = {0, 1, 2, 3}` (`coatomC`) and
`D = {0, 1, 2, 4}` (`coatomD`).

**The multi-layer scheme** (`OrderedLayer.multiLayerScheme I M r`).  Given *multiplicities*
`M : Fin 4 → ℕ` and *multi-layer rows* `r k i`, labellings of all cells
(`OrderedLayer.MultiRows`), the multi-layer scheme is the amalgam of `I` (its cells are the *old
cells*, `OrderedLayer.multiOldCell`) followed by `M k` *new cells* of full scope and grade `k + 1`
(`OrderedLayer.multiNewCell k i`) for `k = 0, 1, 2, 3`, appended in that order by
`Scheme.appendFullCells`; the row of the `i`-th new cell of grade `k + 1` reads every cell below it
by `r k i` (`OrderedLayer.row_multiNewCell`).  Unlike the layer scheme of
`VaughtConjecture.Extension.OrderedLayerStep`, whose rows are read off graded indices, these rows
are read off cells, so two new cells with one graded index may read each other, and themselves,
at different values.

**The multi-layer step** (`Seed.MultiLayerStep I M r`, a named hypothesis on the seed, the
multiplicities and the rows).  Its fields are exactly what is not automatic in the multi-layer
scheme: positive multiplicities (completeness at the graded faces of full scope); coded rows; each
new row lawful below its graded index (consistency); the capped lifts from `(C, k)` and `(D, k)`
into `(univ, k)`, `1 ≤ k ≤ 4`, the only lifts that need capping, since every other lift is one of
the amalgam or a composite with one of them (`OrderedLayer.isBountiful_multiLayerScheme`); and a
lawful labelling extending the glued one.  It gives a completion below the full grade
(`Seed.MultiLayerStep.completion`), and it is exactly legality below the full grade of the
multi-layer scheme with a lawful extension of the glued labelling (`Seed.multiLayerStep_iff`).
Since its rows are arbitrary labellings of the cells, a completion below the full grade whose new
cells are listed by grade is a multi-layer scheme (argued, not formalized); so the step at `m = 3`
reformulates the completion rather than restricting it, and its content lies in the choice of
multiplicities and rows.

**Lawful labellings** (`OrderedLayer.isLawful_multiLayerScheme_of`): a labelling is lawful when
it is lawful on the old cells, self-visible at the new cells, the row of each new cell transforms
to it capped at that cell, and each cell of grade `k + 1` is at most some new cell of grade
`k + 1`.

**Instance.**  The legal seed `CrossedCouplingCounterexample.seedHG`, which has no ordered-layer
step, has a multi-layer step with two new cells at `(univ, 1)`, one for each forced orientation,
and one at each other graded face of full scope
(`CrossedCouplingCounterexample.multiLayerStep_HG`,
`VaughtConjecture.Extension.CrossedCouplingCompletion`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion has the shape of [Kni26, Definition 4.3.14] (the old cells kept, the new cells of
full scope, several at one graded face); its rows are not those of that definition, and neither
printed proof of [Kni26, Lemma 4.3.16] or [Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture.OrderedLayer

open Finset Label CellScheme

/-- After appending cells at `(univ, j)`, no cell lies above `(univ, k)` for `j < k`. -/
theorem noneAbove_appendFullCells {S : Scheme.{u} 5} {j M : ℕ}
    {r : Fin M → Fin (S.card + M) → Label.{u}} (h : NoneAbove S j) :
    NoneAbove (S.appendFullCells j M r (h j le_rfl)) (j + 1) := by
  intro k hk d
  induction d using Fin.addCases with
  | left d =>
    -- The cell scheme of the appended scheme is `appendFullCellsScheme`.
    change ¬ _ ≤ (S.appendFullCellsScheme j M).gradedIndex _
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact h k (by omega) d
  | right i =>
    -- The cell scheme of the appended scheme is `appendFullCellsScheme`.
    change ¬ _ ≤ (S.appendFullCellsScheme j M).gradedIndex _
    rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact fun h' ↦ by have := h'.2; simp only at this; omega

/-- The row of an old cell after appending cells is its row before. -/
theorem appendFullCells_row_castAdd {n k M' : ℕ} {S : Scheme.{u} n}
    {r' : Fin M' → Fin (S.card + M') → Label.{u}}
    {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d} (s : Fin S.card)
    (t : (S.appendFullCells k M' r' h).toCellScheme.below
      ((S.appendFullCells k M' r' h).toCellScheme.gradedIndex (Fin.castAdd M' s))) :
    (S.appendFullCells k M' r' h).rows.row (Fin.castAdd M' s) t =
      S.rows.row s ⟨⟨t.1, Scheme.lt_card_of_mem_below
        (Scheme.not_le_gradedIndex_of_lt h s.isLt) t.2⟩, Scheme.mem_below_of_lt h s.isLt t⟩ :=
  dite_eq_left s.isLt


variable {α : Ordinal.{u}} (I : Seed.{u} α 3) (M : Fin 4 → ℕ)

/-- The number of cells of the multi-layer scheme: the cells of the amalgam and `M k` new cells of
grade `k + 1` for each `k : Fin 4`. -/
abbrev multiCard : ℕ := I.amalgam.card + M 0 + M 1 + M 2 + M 3

/-- **Multi-layer rows**: `r k i` is the row of the `i`-th new cell of grade `k + 1`, given as a
labelling of all cells of the multi-layer scheme (read on the cells below the new cell). -/
abbrev MultiRows : Type (u + 1) := Fin 4 → ℕ → Fin (multiCard I M) → Label.{u}

variable (r : MultiRows I M)

/-- The amalgam with the new cells of grade `1`. -/
noncomputable abbrev multiStage₁ : Scheme.{u} 5 :=
  I.amalgam.toScheme.appendFullCells 1 (M 0)
    (fun i z ↦ r 0 i (Fin.castLE (by simp only [multiCard]; omega) z))
    (noneAbove_amalgam I 1 le_rfl)

/-- The amalgam with the new cells of grades `1` and `2`. -/
noncomputable abbrev multiStage₂ : Scheme.{u} 5 :=
  (multiStage₁ I M r).appendFullCells 2 (M 1)
    (fun i z ↦ r 1 i (Fin.castLE (by simp only [multiCard]; omega) z))
    (noneAbove_appendFullCells (noneAbove_amalgam I) 2 le_rfl)

/-- The amalgam with the new cells of grades `1`, `2` and `3`. -/
noncomputable abbrev multiStage₃ : Scheme.{u} 5 :=
  (multiStage₂ I M r).appendFullCells 3 (M 2)
    (fun i z ↦ r 2 i (Fin.castLE (by simp only [multiCard]; omega) z))
    (noneAbove_appendFullCells (noneAbove_appendFullCells (noneAbove_amalgam I)) 3 le_rfl)

/-- **The multi-layer scheme** of a seed `I` on five points with multiplicities `M` and rows `r`:
the amalgam of `I`, followed by `M k` new cells at `(univ, k + 1)` for `k = 0, 1, 2, 3`, in that
order; the row of the `i`-th new cell of grade `k + 1` is `r k i`. -/
noncomputable abbrev multiLayerScheme : Scheme.{u} 5 :=
  (multiStage₃ I M r).appendFullCells 4 (M 3) (fun i z ↦ r 3 i z)
    (noneAbove_appendFullCells (noneAbove_appendFullCells (noneAbove_appendFullCells
      (noneAbove_amalgam I))) 4 le_rfl)

/-- The old cells: the cells of the amalgam. -/
def multiOldCell (d : Fin I.amalgam.card) : Fin (multiCard I M) :=
  Fin.castAdd (M 3) (Fin.castAdd (M 2) (Fin.castAdd (M 1) (Fin.castAdd (M 0) d)))

/-- The `i`-th new cell of grade `k + 1`. -/
def multiNewCell : (k : Fin 4) → Fin (M k) → Fin (multiCard I M)
  | ⟨0, _⟩, i => Fin.castAdd (M 3) (Fin.castAdd (M 2) (Fin.castAdd (M 1)
      (Fin.natAdd I.amalgam.card i)))
  | ⟨1, _⟩, i => Fin.castAdd (M 3) (Fin.castAdd (M 2) (Fin.natAdd (I.amalgam.card + M 0) i))
  | ⟨2, _⟩, i => Fin.castAdd (M 3) (Fin.natAdd (I.amalgam.card + M 0 + M 1) i)
  | ⟨3, _⟩, i => Fin.natAdd (I.amalgam.card + M 0 + M 1 + M 2) i

variable {I M r}

/-- The old cells keep their graded indices. -/
@[simp] theorem gradedIndex_multiOldCell (d : Fin I.amalgam.card) :
    (multiLayerScheme I M r).toCellScheme.gradedIndex (multiOldCell I M d) =
      I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₃ I M r) 4 (M 3) _).trans <|
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₂ I M r) 3 (M 2) _).trans <|
      (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₁ I M r) 2 (M 1) _).trans <|
        Scheme.appendFullCellsScheme_gradedIndex_castAdd I.amalgam.toScheme 1 (M 0) d

/-- The new cells of grade `k + 1` have graded index `(univ, k + 1)`. -/
@[simp] theorem gradedIndex_multiNewCell (k : Fin 4) (i : Fin (M k)) :
    (multiLayerScheme I M r).toCellScheme.gradedIndex (multiNewCell I M k i) =
      (univ, (k : ℕ) + 1) := by
  match k, i with
  | ⟨0, _⟩, i =>
    exact (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₃ I M r) 4 (M 3) _).trans <|
      (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₂ I M r) 3 (M 2) _).trans <|
        (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₁ I M r) 2 (M 1) _).trans <|
          Scheme.appendFullCellsScheme_gradedIndex_natAdd I.amalgam.toScheme 1 (M 0) i
  | ⟨1, _⟩, i =>
    exact (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₃ I M r) 4 (M 3) _).trans <|
      (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₂ I M r) 3 (M 2) _).trans <|
        Scheme.appendFullCellsScheme_gradedIndex_natAdd (multiStage₁ I M r) 2 (M 1) i
  | ⟨2, _⟩, i =>
    exact (Scheme.appendFullCellsScheme_gradedIndex_castAdd (multiStage₃ I M r) 4 (M 3) _).trans <|
      Scheme.appendFullCellsScheme_gradedIndex_natAdd (multiStage₂ I M r) 3 (M 2) i
  | ⟨3, _⟩, i =>
    exact Scheme.appendFullCellsScheme_gradedIndex_natAdd (multiStage₃ I M r) 4 (M 3) i

/-- **The row of the `i`-th new cell of grade `k + 1` is `r k i`.** -/
theorem row_multiNewCell (k : Fin 4) (i : Fin (M k))
    (t : (multiLayerScheme I M r).toCellScheme.below
      ((multiLayerScheme I M r).toCellScheme.gradedIndex (multiNewCell I M k i))) :
    (multiLayerScheme I M r).rows.row (multiNewCell I M k i) t = r k i t.1 := by
  match k, i with
  | ⟨0, _⟩, i =>
    exact (appendFullCells_row_castAdd (S := multiStage₃ I M r) _ t).trans <|
      (appendFullCells_row_castAdd (S := multiStage₂ I M r) _ _).trans <|
        (appendFullCells_row_castAdd (S := multiStage₁ I M r) _ _).trans <|
          Scheme.appendFullCells_row_natAdd (S := I.amalgam.toScheme) i _
  | ⟨1, _⟩, i =>
    exact (appendFullCells_row_castAdd (S := multiStage₃ I M r) _ t).trans <|
      (appendFullCells_row_castAdd (S := multiStage₂ I M r) _ _).trans <|
        Scheme.appendFullCells_row_natAdd (S := multiStage₁ I M r) i _
  | ⟨2, _⟩, i =>
    exact (appendFullCells_row_castAdd (S := multiStage₃ I M r) _ t).trans <|
      Scheme.appendFullCells_row_natAdd (S := multiStage₂ I M r) i _
  | ⟨3, _⟩, i =>
    exact Scheme.appendFullCells_row_natAdd (S := multiStage₃ I M r) i t

/-! ### The old cells -/

variable (I M r) in
/-- **The old cells form a lower embedding** of the amalgam into the multi-layer scheme. -/
theorem isLowerEmbedding_multiOldCell :
    I.amalgam.toCellScheme.IsLowerEmbedding (multiLayerScheme I M r).toCellScheme
      (multiOldCell I M) :=
  (Scheme.isLowerEmbedding_castAdd 4 (M 3) _ _).comp
    ((Scheme.isLowerEmbedding_castAdd 3 (M 2) _ _).comp
      ((Scheme.isLowerEmbedding_castAdd 2 (M 1) _ _).comp
        (Scheme.isLowerEmbedding_castAdd 1 (M 0) _ _)))

/-- **The rows of the multi-layer scheme pull back to those of the amalgam** along the old
cells. -/
theorem comap_rows_multiOldCell :
    (multiLayerScheme I M r).rows.comap (isLowerEmbedding_multiOldCell I M r) =
      I.amalgam.rows := by
  -- Unfold the embedding of the old cells into the composite of the four embeddings.
  change (multiLayerScheme I M r).rows.comap
    ((Scheme.isLowerEmbedding_castAdd 4 (M 3) _ _).comp
      ((Scheme.isLowerEmbedding_castAdd 3 (M 2) _ _).comp
        ((Scheme.isLowerEmbedding_castAdd 2 (M 1) _ _).comp
          (Scheme.isLowerEmbedding_castAdd 1 (M 0) _ _)))) = _
  rw [← CellScheme.Rows.comap_comap, Scheme.comap_rows_castAdd, ← CellScheme.Rows.comap_comap,
    Scheme.comap_rows_castAdd, ← CellScheme.Rows.comap_comap, Scheme.comap_rows_castAdd,
    Scheme.comap_rows_castAdd]
  all_goals first
    | exact Scheme.isLowerEmbedding_castAdd _ _ _ _
    | exact (Scheme.isLowerEmbedding_castAdd _ _ _ _).comp (Scheme.isLowerEmbedding_castAdd _ _ _ _)
    | exact (Scheme.isLowerEmbedding_castAdd _ _ _ _).comp
        ((Scheme.isLowerEmbedding_castAdd _ _ _ _).comp (Scheme.isLowerEmbedding_castAdd _ _ _ _))

/-- The old cells keep their scopes. -/
@[simp] theorem scope_multiOldCell (d : Fin I.amalgam.card) :
    (multiLayerScheme I M r).toCellScheme.scope (multiOldCell I M d) =
      I.amalgam.toCellScheme.scope d :=
  congrArg Prod.fst (gradedIndex_multiOldCell d)

/-- The old cells keep their grades. -/
@[simp] theorem grade_multiOldCell (d : Fin I.amalgam.card) :
    (multiLayerScheme I M r).toCellScheme.grade (multiOldCell I M d) =
      I.amalgam.toCellScheme.grade d :=
  congrArg Prod.snd (gradedIndex_multiOldCell d)

/-- The new cells have full scope. -/
@[simp] theorem scope_multiNewCell (k : Fin 4) (i : Fin (M k)) :
    (multiLayerScheme I M r).toCellScheme.scope (multiNewCell I M k i) = univ :=
  congrArg Prod.fst (gradedIndex_multiNewCell k i)

/-- The new cells of grade `k + 1` have grade `k + 1`. -/
@[simp] theorem grade_multiNewCell (k : Fin 4) (i : Fin (M k)) :
    (multiLayerScheme I M r).toCellScheme.grade (multiNewCell I M k i) = (k : ℕ) + 1 :=
  congrArg Prod.snd (gradedIndex_multiNewCell k i)

/-- **Every cell of the multi-layer scheme is old or new.** -/
theorem multiCell_cases (z : Fin (multiLayerScheme I M r).card) :
    (∃ d, z = multiOldCell I M d) ∨ ∃ k i, z = multiNewCell I M k i := by
  -- The cells are those of the amalgam followed by the four blocks of new cells.
  change Fin (I.amalgam.card + M 0 + M 1 + M 2 + M 3) at z
  induction z using Fin.addCases with
  | right i => exact .inr ⟨3, i, rfl⟩
  | left z =>
    induction z using Fin.addCases with
    | right i => exact .inr ⟨2, i, rfl⟩
    | left z =>
      induction z using Fin.addCases with
      | right i => exact .inr ⟨1, i, rfl⟩
      | left z =>
        induction z using Fin.addCases with
        | right i => exact .inr ⟨0, i, rfl⟩
        | left d => exact .inl ⟨d, rfl⟩

/-- The scope of an old cell is not the ground set. -/
theorem scope_multiOldCell_ne (d : Fin I.amalgam.card) :
    (multiLayerScheme I M r).toCellScheme.scope (multiOldCell I M d) ≠ univ := by
  rw [scope_multiOldCell]; exact I.scope_ne_univ d

/-- A cell of scope other than the ground set is old. -/
theorem exists_eq_multiOldCell {z : Fin (multiLayerScheme I M r).card}
    (hz : (multiLayerScheme I M r).toCellScheme.scope z ≠ univ) : ∃ d, z = multiOldCell I M d := by
  rcases multiCell_cases z with h | ⟨k, i, rfl⟩
  · exact h
  · exact absurd (scope_multiNewCell k i) hz

/-- **The cells at `(univ, j)` are the new cells of grade `j`.** -/
theorem exists_eq_multiNewCell {z : Fin (multiLayerScheme I M r).card} {j : ℕ}
    (hz : (multiLayerScheme I M r).toCellScheme.gradedIndex z = (univ, j)) :
    ∃ (k : Fin 4) (i : Fin (M k)), (k : ℕ) + 1 = j ∧ z = multiNewCell I M k i := by
  rcases multiCell_cases z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
  · rw [gradedIndex_multiOldCell] at hz
    exact absurd (congrArg Prod.fst hz) (I.scope_ne_univ d)
  · rw [gradedIndex_multiNewCell] at hz
    exact ⟨k, i, (Prod.mk.inj hz).2, rfl⟩

/-- Every cell has grade at most `4`. -/
theorem grade_le_four_multi (z : Fin (multiLayerScheme I M r).card) :
    (multiLayerScheme I M r).toCellScheme.grade z ≤ 4 := by
  rcases multiCell_cases z with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
  · rw [grade_multiOldCell]; exact Nat.lt_succ_iff.mp (I.grade_lt d)
  · rw [grade_multiNewCell]; omega

/-- Every cell is below `(univ, 4)`. -/
theorem mem_below_univ_four_multi (z : Fin (multiLayerScheme I M r).card) :
    z ∈ (multiLayerScheme I M r).toCellScheme.below ((univ : Finset (Fin 5)), 4) :=
  ⟨subset_univ _, grade_le_four_multi z⟩

/-- Below a pair of scope other than the ground set, the cells are the old cells. -/
theorem image_multiOldCell_below {X : Finset (Fin 5) × ℕ} (hX : X.1 ≠ univ) :
    multiOldCell I M '' I.amalgam.toCellScheme.below X =
      (multiLayerScheme I M r).toCellScheme.below X := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [CellScheme.mem_below, gradedIndex_multiOldCell]
    exact hd
  · intro hz
    obtain ⟨d, rfl⟩ := exists_eq_multiOldCell (r := r) (z := z) fun h ↦
      hX (univ_subset_iff.mp (h ▸ hz.1))
    refine ⟨d, ?_, rfl⟩
    rw [CellScheme.mem_below, ← gradedIndex_multiOldCell (r := r)]
    exact hz

/-- **Below a pair of scope other than the ground set, lawfulness in the multi-layer scheme is
lawfulness in the amalgam**, along the old cells. -/
theorem isLawfulBelow_multiOldCell_iff {X : Finset (Fin 5) × ℕ} (hX : X.1 ≠ univ)
    {w : Fin (multiLayerScheme I M r).card → Label.{u}} :
    (multiLayerScheme I M r).rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (multiOldCell I M d)) := by
  have h := Rows.isLawfulBelow_comap_iff (R := (multiLayerScheme I M r).rows)
    (isLowerEmbedding_multiOldCell I M r) (image_multiOldCell_below hX) (r := fun z ↦ w z)
  rw [comap_rows_multiOldCell] at h
  exact h.symm

/-- The rows of the old cells are those of the amalgam. -/
theorem row_multiOldCell (s d : Fin I.amalgam.card)
    (h : multiOldCell I M d ∈ (multiLayerScheme I M r).toCellScheme.below
      ((multiLayerScheme I M r).toCellScheme.gradedIndex (multiOldCell I M s)))
    (h' : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    (multiLayerScheme I M r).rows.row (multiOldCell I M s) ⟨multiOldCell I M d, h⟩ =
      I.amalgam.rows.row s ⟨d, h'⟩ :=
  congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row s ⟨d, h'⟩)
    (comap_rows_multiOldCell (I := I) (M := M) (r := r))

/-- A cell below an old cell is old. -/
theorem exists_multiOldCell_of_mem_below {s : Fin I.amalgam.card}
    {z : Fin (multiLayerScheme I M r).card}
    (hz : z ∈ (multiLayerScheme I M r).toCellScheme.below
      ((multiLayerScheme I M r).toCellScheme.gradedIndex (multiOldCell I M s))) :
    ∃ d, z = multiOldCell I M d ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s) := by
  obtain ⟨d, rfl⟩ := (isLowerEmbedding_multiOldCell I M r).mem_range s z hz
  exact ⟨d, rfl, ((isLowerEmbedding_multiOldCell I M r).le_iff d s).mp hz⟩

/-- An old cell is below a pair when its graded index is. -/
theorem multiOldCell_mem_below {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ}
    (h : I.amalgam.toCellScheme.gradedIndex d ≤ X) :
    multiOldCell I M d ∈ (multiLayerScheme I M r).toCellScheme.below X := by
  rw [CellScheme.mem_below, gradedIndex_multiOldCell]; exact h

/-- A new cell of grade `k + 1` is below `(univ, j)` for `k + 1 ≤ j`. -/
theorem multiNewCell_mem_below {k : Fin 4} (i : Fin (M k)) {j : ℕ} (hkj : (k : ℕ) + 1 ≤ j) :
    multiNewCell I M k i ∈
      (multiLayerScheme I M r).toCellScheme.below ((univ : Finset (Fin 5)), j) := by
  rw [CellScheme.mem_below, gradedIndex_multiNewCell]; exact ⟨subset_rfl, hkj⟩

/-- An old cell below `(univ, k)` lies below one of the two coatoms at the grade `k`. -/
theorem mem_below_coatom_of_ne_multi {z : Fin (multiLayerScheme I M r).card} {k : ℕ}
    (hz : z ∈ (multiLayerScheme I M r).toCellScheme.below ((univ : Finset (Fin 5)), k))
    (hne : (multiLayerScheme I M r).toCellScheme.scope z ≠ univ) :
    z ∈ (multiLayerScheme I M r).toCellScheme.below (coatomC, k) ∨
      z ∈ (multiLayerScheme I M r).toCellScheme.below (coatomD, k) := by
  obtain ⟨d, rfl⟩ := exists_eq_multiOldCell hne
  rw [CellScheme.mem_below, gradedIndex_multiOldCell] at hz
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d) with h | h
  · exact .inl (multiOldCell_mem_below ⟨h, hz.2⟩)
  · exact .inr (multiOldCell_mem_below ⟨h, hz.2⟩)

variable (I M r) in
/-- The old cells, in their order. -/
noncomputable def embedMultiOld : Fin I.amalgam.card ↪o Fin (multiLayerScheme I M r).card :=
  OrderEmbedding.ofStrictMono (multiOldCell I M) fun _ _ h ↦ h

/-! ### Legality below the full grade -/

/-- The faces of the multi-layer scheme are those of the amalgam. -/
theorem faces_multiLayerScheme :
    (multiLayerScheme I M r).toCellScheme.faces = I.amalgam.toCellScheme.faces := rfl

/-- **Pairs below a coatom**: the capped lifts of the amalgam, transported along the old
cells. -/
theorem cappedLift_multiOld {X Y : Finset (Fin 5) × ℕ}
    (hX : X ∈ (multiLayerScheme I M r).toCellScheme.gradedFaces)
    (hY : Y ∈ (multiLayerScheme I M r).toCellScheme.gradedFaces) (hY1 : Y.1 ≠ univ) (h : X ≤ Y) :
    (multiLayerScheme I M r).rows.CappedLift h := by
  have hX1 : X.1 ≠ univ := fun hX ↦ hY1 (univ_subset_iff.mp (hX ▸ h.1))
  refine Rows.CappedLift.of_comap (isLowerEmbedding_multiOldCell I M r)
    (image_multiOldCell_below hX1) (image_multiOldCell_below hY1) le_rfl (h' := h) ?_
  rw [comap_rows_multiOldCell]
  exact I.isBountiful hX hY h

/-- **The multi-layer scheme is bountiful** once the rows lift capped from each coatom into the
full scope at each grade `1 ≤ k ≤ 4`: below a coatom the lifts are those of the amalgam, and a
lift from `(B, k)` to the full scope goes first within the amalgam to the coatom containing `B`,
and then by the given lift. -/
theorem isBountiful_multiLayerScheme
    (hC : ∀ k, 1 ≤ k → k ≤ 4 → (multiLayerScheme I M r).rows.CappedLift (X := (coatomC, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩)
    (hD : ∀ k, 1 ≤ k → k ≤ 4 → (multiLayerScheme I M r).rows.CappedLift (X := (coatomD, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩) :
    (multiLayerScheme I M r).rows.IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  by_cases hY1 : Y.1 = univ
  · obtain ⟨Y1, k⟩ := Y
    simp only at hY1
    subst hY1
    obtain ⟨X1, j⟩ := X
    by_cases hX1 : X1 = univ
    · subst hX1; exact Rows.cappedLift_refl _
    have hj1 : 1 ≤ j := hX.2.1
    have hside : X1 ⊆ coatomC ∨ X1 ⊆ coatomD := I.subset_or_subset X1 hX.1 hX1
    have hj4 : j ≤ 4 := hX.2.2.trans (by
      rcases hside with hs | hs
      · exact (card_le_card hs).trans (by decide)
      · exact (card_le_card hs).trans (by decide))
    rcases hside with hs | hs
    · have hB : (coatomC, j) ∈ (multiLayerScheme I M r).toCellScheme.gradedFaces :=
        ⟨coatomC_mem_faces I, hj1, hj4.trans (show (4 : ℕ) ≤ #coatomC by decide)⟩
      exact (cappedLift_multiOld hX hB (show coatomC ≠ univ by decide) (X := (X1, j))
        ⟨hs, le_rfl⟩).trans (hC j hj1 hj4)
    · have hB : (coatomD, j) ∈ (multiLayerScheme I M r).toCellScheme.gradedFaces :=
        ⟨coatomD_mem_faces I, hj1, hj4.trans (show (4 : ℕ) ≤ #coatomD by decide)⟩
      exact (cappedLift_multiOld hX hB (show coatomD ≠ univ by decide) (X := (X1, j))
        ⟨hs, le_rfl⟩).trans (hD j hj1 hj4)
  · exact cappedLift_multiOld (Y := (Y.1, X.2)) hX
      ⟨hY.1, hX.2.1, hX.2.2.trans (card_le_card h.1)⟩ hY1 _

variable (I M r) in
/-- **The multi-layer scheme is well formed.** -/
theorem isWellFormed_multiLayerScheme : (multiLayerScheme I M r).IsWellFormed :=
  Scheme.isWellFormed_appendFullCells (Scheme.isWellFormed_appendFullCells
    (Scheme.isWellFormed_appendFullCells (Scheme.isWellFormed_appendFullCells
      I.amalgam.isWellFormed (by omega) (by omega)) (by omega) (by omega)) (by omega)
        (by omega)) (by omega) (by omega)

/-- **The multi-layer scheme is coded** when each new row is coded at the cells below its new
cell: the old rows are those of the amalgam. -/
theorem isCoded_multiLayerScheme
    (hr : ∀ k (i : Fin (M k)), ∀ z ∈ (multiLayerScheme I M r).toCellScheme.below
      ((univ : Finset (Fin 5)), (k : ℕ) + 1),
        r k i z < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (multiLayerScheme I M r).IsCoded := by
  intro s t
  rcases multiCell_cases s with ⟨a, rfl⟩ | ⟨k, i, rfl⟩
  · obtain ⟨d, hd, hda⟩ := exists_multiOldCell_of_mem_below t.2
    rw [(multiLayerScheme I M r).rows.row_congr rfl
      (t' := ⟨multiOldCell I M d, hd ▸ t.2⟩) hd, row_multiOldCell a d _ hda]
    exact I.amalgam.isCoded _ _
  · rw [row_multiNewCell]
    refine hr k i _ ?_
    rw [← gradedIndex_multiNewCell (r := r) k i]
    exact t.2

/-- **The rows of the multi-layer scheme are consistent** when each new row `r k i` is lawful below
`(univ, k + 1)`. -/
theorem isConsistent_multiLayerScheme
    (hr : ∀ k (i : Fin (M k)), (multiLayerScheme I M r).rows.IsLawfulBelow
      ((univ : Finset (Fin 5)), (k : ℕ) + 1) fun z ↦ r k i z) :
    (multiLayerScheme I M r).rows.IsConsistent := by
  intro s
  rcases multiCell_cases s with ⟨a, rfl⟩ | ⟨k, i, rfl⟩
  · have hφ := isLowerEmbedding_multiOldCell I M r
    refine (Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex a)).mp ?_
    rw [comap_rows_multiOldCell]
    convert I.isConsistent a using 1
    funext t
    exact congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row a t) comap_rows_multiOldCell
  · have h := hr k i
    rw [← gradedIndex_multiNewCell (r := r) k i] at h
    convert h using 1
    funext t
    exact row_multiNewCell k i t

/-- **The multi-layer scheme is complete below the full grade** when every multiplicity is
positive. -/
theorem exists_gradedIndex_eq_multiLayerScheme (hM : ∀ k, 0 < M k) {X : Finset (Fin 5) × ℕ}
    (hX : X ∈ (multiLayerScheme I M r).toCellScheme.gradedFaces) (hX5 : X.2 < 5) :
    ∃ z, (multiLayerScheme I M r).toCellScheme.gradedIndex z = X := by
  by_cases hX1 : X.1 = univ
  · obtain ⟨X1, j⟩ := X
    simp only at hX1 hX5
    subst hX1
    have hj1 : 1 ≤ j := hX.2.1
    refine ⟨multiNewCell I M ⟨j - 1, by omega⟩ ⟨0, hM _⟩, ?_⟩
    rw [gradedIndex_multiNewCell]
    exact Prod.ext rfl (by simp only; omega)
  · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq X hX hX1
    exact ⟨multiOldCell I M d, (gradedIndex_multiOldCell d).trans hd⟩

/-- **Lawful labellings of the multi-layer scheme.**  A labelling `v` is lawful when it is lawful
on the old cells, its values at the new cells are self-visible at their grades, the row of every
new cell transforms to `v` capped at its value, and every cell of grade `k + 1` has a value at
most that of some new cell of grade `k + 1`. -/
theorem isLawful_multiLayerScheme_of {v : Fin (multiLayerScheme I M r).card → Label.{u}}
    (hv : I.amalgam.rows.IsLawful fun d ↦ v (multiOldCell I M d))
    (hvis : ∀ k (i : Fin (M k)), IsSelfVisible ((k : ℕ) + 1) (v (multiNewCell I M k i)))
    (hloc : ∀ k (i : Fin (M k)), TransformsTo (fun t : (multiLayerScheme I M r).toCellScheme.below
        ((multiLayerScheme I M r).toCellScheme.gradedIndex (multiNewCell I M k i)) ↦
          (multiLayerScheme I M r).toCellScheme.grade t) (fun t ↦ r k i t.1)
        fun t ↦ min (v t) (v (multiNewCell I M k i)))
    (havail : ∀ s (k : Fin 4), (multiLayerScheme I M r).toCellScheme.grade s = (k : ℕ) + 1 →
      ∃ i : Fin (M k), v s ≤ v (multiNewCell I M k i)) :
    (multiLayerScheme I M r).rows.IsLawful v where
  orderly d := by
    rcases multiCell_cases d with ⟨d, rfl⟩ | ⟨k, i, rfl⟩
    · rw [grade_multiOldCell]; exact hv.orderly d
    · rw [grade_multiNewCell]; exact hvis k i
  locality s := by
    rcases multiCell_cases s with ⟨a, rfl⟩ | ⟨k, i, rfl⟩
    · have hb : (multiLayerScheme I M r).rows.IsLawfulBelow
          ((multiLayerScheme I M r).toCellScheme.gradedIndex (multiOldCell I M a))
          (fun z ↦ v z) := by
        refine (isLawfulBelow_multiOldCell_iff ?_).mpr ?_
        · rw [gradedIndex_multiOldCell]; exact I.scope_ne_univ a
        · exact hv.isLawfulBelow _
      exact (Rows.isLawfulBelow_iff_forall.mp hb).2.1 _ (CellScheme.mem_below_gradedIndex _ _)
    · have hrow : (multiLayerScheme I M r).rows.row (multiNewCell I M k i) =
          fun t ↦ r k i t.1 := funext (row_multiNewCell k i)
      rw [hrow]
      exact hloc k i
  availability s t hst hg := by
    rcases multiCell_cases t with ⟨b, rfl⟩ | ⟨k, i, rfl⟩
    · obtain ⟨a, rfl⟩ := exists_eq_multiOldCell (r := r) (z := s) fun h ↦
        scope_multiOldCell_ne (r := r) b (univ_subset_iff.mp (h ▸ hst))
      rw [scope_multiOldCell, scope_multiOldCell] at hst
      rw [grade_multiOldCell, grade_multiOldCell] at hg
      obtain ⟨u, hu, hle⟩ := hv.availability a b hst hg
      exact ⟨multiOldCell I M u, by rw [gradedIndex_multiOldCell, gradedIndex_multiOldCell, hu],
        hle⟩
    · obtain ⟨i', hi'⟩ := havail s k (hg.trans (grade_multiNewCell k i))
      exact ⟨multiNewCell I M k i', by rw [gradedIndex_multiNewCell, gradedIndex_multiNewCell],
        hi'⟩

end VaughtConjecture.OrderedLayer

namespace VaughtConjecture.Seed

open Finset Label CellScheme OrderedLayer

variable {α : Ordinal.{u}} (I : Seed.{u} α 3) (M : Fin 4 → ℕ) (r : MultiRows I M)

/-- **The multi-layer step** of a seed on five points with multiplicities `M` and rows `r`: the
conditions under which the multi-layer scheme (`OrderedLayer.multiLayerScheme`: the amalgam with
`M k` new cells at `(univ, k + 1)`, the `i`-th with row `r k i`) is legal below the full grade and
carries a lawful extension of the glued labelling.

* `pos`: every multiplicity is positive (completeness at the graded faces of full scope);
* `row_lt`: the new rows are coded at the cells below their new cells;
* `isLawfulBelow_row`: each new row `r k i` is lawful below `(univ, k + 1)` (consistency);
* `cappedLift_left`, `cappedLift_right`: the capped lifts from `(C, k)` and `(D, k)` into
  `(univ, k)`, `1 ≤ k ≤ 4`, the only lifts that need capping;
* `exists_isLawful`: a lawful labelling equal to the glued labelling on the old cells. -/
structure MultiLayerStep : Prop where
  /-- Every multiplicity is positive. -/
  pos : ∀ k, 0 < M k
  /-- The new rows are coded: every value at a cell below the new cell lies below `ω ^ 2`. -/
  row_lt : ∀ k (i : Fin (M k)), ∀ z ∈ (multiLayerScheme I M r).toCellScheme.below
    ((univ : Finset (Fin 5)), (k : ℕ) + 1),
      r k i z < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})
  /-- The row of each new cell is lawful below its graded index. -/
  isLawfulBelow_row : ∀ k (i : Fin (M k)), (multiLayerScheme I M r).rows.IsLawfulBelow
    ((univ : Finset (Fin 5)), (k : ℕ) + 1) fun z ↦ r k i z
  /-- The capped lift from `(C, k)` to `(univ, k)`. -/
  cappedLift_left : ∀ k, 1 ≤ k → k ≤ 4 → (multiLayerScheme I M r).rows.CappedLift
    (X := (coatomC, k)) (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩
  /-- The capped lift from `(D, k)` to `(univ, k)`. -/
  cappedLift_right : ∀ k, 1 ≤ k → k ≤ 4 → (multiLayerScheme I M r).rows.CappedLift
    (X := (coatomD, k)) (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩
  /-- A lawful labelling of the multi-layer scheme extends the glued labelling of the amalgam. -/
  exists_isLawful : ∃ w : Fin (multiLayerScheme I M r).card → Label.{u},
    (multiLayerScheme I M r).rows.IsLawful w ∧ ∀ d, w (multiOldCell I M d) = I.amalgam.label d

variable {I M r}

/-- **The multi-layer scheme is legal below the full grade** under the multi-layer step. -/
theorem MultiLayerStep.isLegalBelowFullGrade (h : I.MultiLayerStep M r) :
    (multiLayerScheme I M r).IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_multiLayerScheme I M r
  isCoded := isCoded_multiLayerScheme h.row_lt
  isConsistent := isConsistent_multiLayerScheme h.isLawfulBelow_row
  isBountiful := isBountiful_multiLayerScheme h.cappedLift_left h.cappedLift_right
  grade_lt z := Nat.lt_succ_of_le (grade_le_four_multi z)
  exists_gradedIndex_eq _ hX hX5 := exists_gradedIndex_eq_multiLayerScheme h.pos hX hX5

/-- **The completion from the multi-layer step**: the multi-layer scheme, with a lawful labelling
extending the glued one. -/
noncomputable def MultiLayerStep.completion (h : I.MultiLayerStep M r) :
    CompletionBelowFullGrade I where
  scheme := multiLayerScheme I M r
  embed := embedMultiOld I M r
  isLowerEmbedding := isLowerEmbedding_multiOldCell I M r
  scope_embed := scope_multiOldCell
  comap_rows := comap_rows_multiOldCell
  mem_range_embed z hz := by
    obtain ⟨d, rfl⟩ := exists_eq_multiOldCell hz
    exact ⟨d, rfl⟩
  faces_eq := faces_multiLayerScheme
  isLegalBelowFullGrade := h.isLegalBelowFullGrade
  label := h.exists_isLawful.choose
  isLawful := h.exists_isLawful.choose_spec.1
  label_embed := h.exists_isLawful.choose_spec.2

/-- The scheme of the completion from the multi-layer step is the multi-layer scheme. -/
theorem MultiLayerStep.completion_scheme (h : I.MultiLayerStep M r) :
    h.completion.scheme = multiLayerScheme I M r := rfl

/-- **The multi-layer step gives a completion below the full grade.** -/
theorem MultiLayerStep.nonempty_completionBelowFullGrade (h : I.MultiLayerStep M r) :
    Nonempty (CompletionBelowFullGrade I) :=
  ⟨h.completion⟩

/-- **The multi-layer step is exactly legality of the multi-layer scheme with a lawful
extension**: the hypothesis is the exact content of a completion with `M k` new cells at each
graded face `(univ, k + 1)` of full scope. -/
theorem multiLayerStep_iff : I.MultiLayerStep M r ↔
    (multiLayerScheme I M r).IsLegalBelowFullGrade ∧
      ∃ w : Fin (multiLayerScheme I M r).card → Label.{u},
        (multiLayerScheme I M r).rows.IsLawful w ∧
          ∀ d, w (multiOldCell I M d) = I.amalgam.label d := by
  refine ⟨fun h ↦ ⟨h.isLegalBelowFullGrade, h.exists_isLawful⟩,
    fun ⟨hL, hw⟩ ↦ ⟨fun k ↦ ?_, fun k i z hz ↦ ?_, fun k i ↦ ?_, fun k hk1 hk4 ↦ ?_,
      fun k hk1 hk4 ↦ ?_, hw⟩⟩
  · obtain ⟨z, hz⟩ := hL.exists_gradedIndex_eq (((univ : Finset (Fin 5)), (k : ℕ) + 1))
      ⟨(isWellFormed_multiLayerScheme I M r).univ_mem_faces, by omega, by simp; omega⟩
      (by simp only; omega)
    obtain ⟨k', i, hk', -⟩ := exists_eq_multiNewCell hz
    obtain rfl : k' = k := Fin.ext (by omega)
    exact Nat.zero_lt_of_lt i.isLt
  · rw [← gradedIndex_multiNewCell (r := r) k i] at hz
    have := hL.isCoded (multiNewCell I M k i) ⟨z, hz⟩
    rwa [row_multiNewCell] at this
  · have := hL.isConsistent (multiNewCell I M k i)
    have hrow : (multiLayerScheme I M r).rows.row (multiNewCell I M k i) =
        fun t ↦ r k i t.1 := funext (row_multiNewCell k i)
    rw [hrow, gradedIndex_multiNewCell] at this
    exact this
  · have hX : ((coatomC, k) : Finset (Fin 5) × ℕ) ∈
        (multiLayerScheme I M r).toCellScheme.gradedFaces :=
      ⟨coatomC_mem_faces I, hk1, hk4.trans (show (4 : ℕ) ≤ #coatomC by decide)⟩
    have hY : ((univ : Finset (Fin 5)), k) ∈ (multiLayerScheme I M r).toCellScheme.gradedFaces :=
      ⟨(isWellFormed_multiLayerScheme I M r).univ_mem_faces, hk1, by simp; omega⟩
    exact hL.isBountiful hX hY _
  · have hX : ((coatomD, k) : Finset (Fin 5) × ℕ) ∈
        (multiLayerScheme I M r).toCellScheme.gradedFaces :=
      ⟨coatomD_mem_faces I, hk1, hk4.trans (show (4 : ℕ) ≤ #coatomD by decide)⟩
    have hY : ((univ : Finset (Fin 5)), k) ∈ (multiLayerScheme I M r).toCellScheme.gradedFaces :=
      ⟨(isWellFormed_multiLayerScheme I M r).univ_mem_faces, hk1, by simp; omega⟩
    exact hL.isBountiful hX hY _

end VaughtConjecture.Seed
