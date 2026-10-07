/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CompletionBelowFullGrade
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Extension.CanonicalCode

/-!
# The ordered-layer step on five points

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: the
ordered-layer step as a named hypothesis on an arbitrary seed, and the completion from it);
semantic contract, items 2–4.

Let `I` be a seed on five points (`m = 3`), with coatoms `C = {0, 1, 2, 3}` (`coatomC`) and
`D = {0, 1, 2, 4}` (`coatomD`).

**The layer scheme** (`layerScheme I ρ`).  Given *layer rows* `ρ k : Finset (Fin 5) × ℕ → Label`
for `k = 1, 2, 3, 4`, the layer scheme is the amalgam of `I` (its cells are the *old cells*,
`oldCell`) followed by one *new cell* at each graded face `(univ, k)` of full scope, `k = 1, …, 4`
(`newCell`), appended in that order; the row of the new cell at `(univ, k)` reads each cell below
it through its graded index, by `ρ k` (`row_newCell`).  The rows are read off graded indices: the
cells of one graded index are read at one value.  For the three seeds with compiled results
(`seed4`, `seed5`, `seedL`) the amalgam has one cell at each graded index, so this is no
restriction there.  The thin scheme of `VaughtConjecture.Extension.ThinScheme` is the layer scheme
of the rows `thinRow k ∘ thinKind`, by definition.

**The ordered-layer step** (`Seed.OrderedLayerStep I ρ`, a named hypothesis on the seed and the
rows).  Its fields are exactly what is not automatic in the layer scheme:

* the coding of the rows (`row_lt`): every value at a cell below the new cell is below `ω ^ 2`;
* the consistency of the new rows (`isLawfulBelow_row`): the labelling read off the graded indices
  by `ρ k` is lawful below `(univ, k)`;
* the capped lifts from the two coatoms into the full scope (`cappedLift_left`,
  `cappedLift_right`): from `(C, k)` and from `(D, k)` to `(univ, k)`, for `k = 1, …, 4`; these
  are the only lifts that need capping: every other lift of the layer scheme is a lift of the
  amalgam or a composite with one of them (`isBountiful_layerScheme`);
* a lawful labelling of the layer scheme extending the glued labelling of the amalgam
  (`exists_isLawful`).

**The completion** (`Seed.OrderedLayerStep.completion`): the ordered-layer step gives a completion
below the full grade of `I`; well-formedness, coding of the old rows, consistency of the old rows,
completeness below the full grade, and bountifulness from the capped lifts are proved here for
every seed.  Conversely, the ordered-layer step is exactly legality below the full grade of the
layer scheme together with a lawful extension of the glued labelling
(`Seed.orderedLayerStep_iff`), so the hypothesis is the exact content of a completion of this
shape: one new cell per graded face of full scope, rows read off graded indices.  The step is a
restriction of the completion of the seed; whether the converse fails for some seed is open (it
fails at `CrossedCouplingCounterexample.seedHG` if and only if `seedHG` has a completion below the
full grade).

**At `m = 3`** (`Seed.HasOrderedLayerStep`): a seed on five points with an ordered-layer step for
some rows has a completion below the full grade
(`Seed.HasOrderedLayerStep.nonempty_completionBelowFullGrade`).  The universal form
`∀ I, I.HasOrderedLayerStep` is refuted: the legal seed `CrossedCouplingCounterexample.seedHG` has
no ordered-layer step (`CrossedCouplingCounterexample.not_forall_hasOrderedLayerStep`, module
`VaughtConjecture.Extension.CrossedCouplingCounterexample`); no theorem is stated under the
universal form.  The ordered-layer step holds for the
seeds `seed4`, `seed5`, `seedL`, its mirror `seedLM`, and `seedLL`
(`VaughtConjecture.Extension.OrderedLayerExamples`, `ThinCompletionMirrorExamples`,
`ThinCompletionTLTL`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion has the shape of [Kni26, Definition 4.3.14] (the old cells kept, the new cells of
full scope), with one new cell per graded face of full scope; its rows are not those of that
definition, and neither printed proof of [Kni26, Lemma 4.3.16] or [Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture.OrderedLayer

open Finset Label CellScheme

/-- **The top row**: the row of the new cell at `(univ, 4)` that reads only the cells of grade `4`,
at `ω + 4`. -/
noncomputable def topRow (X : Finset (Fin 5) × ℕ) : Label.{u} :=
  if X.2 = 4 then gridPoint 4 1 else ⊥

/-- **Layer rows** on five points: for each grade `k`, the row of the new cell at `(univ, k)`,
read off the graded indices of the cells below it. -/
abbrev LayerRows := ℕ → Finset (Fin 5) × ℕ → Label.{u}

/-- No cell of `S` lies above a pair `(univ, k)` with `j ≤ k`. -/
def NoneAbove (S : Scheme.{u} 5) (j : ℕ) : Prop :=
  ∀ k, j ≤ k → ∀ d, ¬ ((univ : Finset (Fin 5)), k) ≤ S.toCellScheme.gradedIndex d

/-- **Adding the new cell at `(univ, j)`**, whose row reads the graded indices by `r`. -/
noncomputable abbrev addLayerCell (S : Scheme.{u} 5) (j : ℕ)
    (r : Finset (Fin 5) × ℕ → Label.{u}) (h : NoneAbove S j) : Scheme.{u} 5 :=
  S.appendFullCell j (fun d ↦ r ((S.appendFullCellScheme j).gradedIndex d)) (h j le_rfl)

/-- After adding the new cell at `(univ, j)`, no cell lies above `(univ, k)` for `j < k`. -/
theorem noneAbove_addLayerCell {S : Scheme.{u} 5} {j : ℕ} {r : Finset (Fin 5) × ℕ → Label.{u}}
    (h : NoneAbove S j) : NoneAbove (addLayerCell S j r h) (j + 1) := by
  intro k hk d
  induction d using Fin.lastCases with
  | last =>
    rw [Scheme.appendFullCell_toCellScheme, Scheme.appendFullCellScheme_gradedIndex_last]
    exact fun h' ↦ by have := h'.2; simp only at this; omega
  | cast d =>
    rw [Scheme.appendFullCell_toCellScheme, Scheme.appendFullCellScheme_gradedIndex_castSucc]
    exact h k (by omega) d

variable {α : Ordinal.{u}} (I : Seed.{u} α 3) (ρ : LayerRows.{u})

/-- No cell of the amalgam has full scope. -/
theorem noneAbove_amalgam : NoneAbove I.amalgam.toScheme 1 :=
  fun k _ d ↦ I.not_univ_le k d

/-- The layer scheme with the new cells at `(univ, 1)` and `(univ, 2)`. -/
private noncomputable abbrev layerScheme₂ : Scheme.{u} 5 :=
  addLayerCell (addLayerCell I.amalgam.toScheme 1 (ρ 1) (noneAbove_amalgam I)) 2 (ρ 2)
    (noneAbove_addLayerCell _)

/-- **The layer scheme** of a seed `I` on five points with layer rows `ρ`: its amalgam, followed by
one new cell at each `(univ, k)`, `k = 1, 2, 3, 4`, whose row reads the graded indices by
`ρ k`. -/
noncomputable abbrev layerScheme : Scheme.{u} 5 :=
  addLayerCell (addLayerCell (layerScheme₂ I ρ) 3 (ρ 3) (noneAbove_addLayerCell _)) 4 (ρ 4)
    (noneAbove_addLayerCell _)

/-- The old cells: the cells of the amalgam. -/
noncomputable def oldCell (d : Fin I.amalgam.card) : Fin (layerScheme I ρ).card :=
  d.castSucc.castSucc.castSucc.castSucc

/-- The new cell at `(univ, k)`, for `k = 1, 2, 3, 4`. -/
noncomputable def newCell : ℕ → Fin (layerScheme I ρ).card
  | 1 => (Fin.last _).castSucc.castSucc.castSucc
  | 2 => (Fin.last _).castSucc.castSucc
  | 3 => (Fin.last _).castSucc
  | _ => Fin.last _

variable {I ρ}

/-- The old cells keep their graded indices. -/
@[simp] theorem gradedIndex_oldCell (d : Fin I.amalgam.card) :
    (layerScheme I ρ).toCellScheme.gradedIndex (oldCell I ρ d) =
      I.amalgam.toCellScheme.gradedIndex d := by
  simp [oldCell]

/-- The new cell at `(univ, k)` has graded index `(univ, k)`. -/
theorem gradedIndex_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ k) = (univ, k) := by
  rcases k with _ | _ | _ | _ | _ | k
  all_goals first | omega | skip
  all_goals simp only [newCell, Scheme.appendFullCellScheme_gradedIndex_castSucc]
  all_goals exact Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- The row of the cell appended by `addLayerCell` reads the graded indices by `r`. -/
theorem row_last_addLayerCell {S : Scheme.{u} 5} {j : ℕ} {r : Finset (Fin 5) × ℕ → Label.{u}}
    {h : NoneAbove S j}
    (t : (addLayerCell S j r h).toCellScheme.below
      ((addLayerCell S j r h).toCellScheme.gradedIndex (Fin.last _))) :
    (addLayerCell S j r h).rows.row (Fin.last _) t =
      r ((addLayerCell S j r h).toCellScheme.gradedIndex t.1) :=
  Scheme.appendFullCell_row_last t

/-- A row read off the graded indices stays so after adding a new cell. -/
theorem row_castSucc_addLayerCell {S : Scheme.{u} 5} {j : ℕ}
    {r : Finset (Fin 5) × ℕ → Label.{u}} {hS : NoneAbove S j}
    {s : Fin S.card} {σ : Finset (Fin 5) × ℕ → Label.{u}}
    (hs : ∀ t, S.rows.row s t = σ (S.toCellScheme.gradedIndex t.1))
    (t : (addLayerCell S j r hS).toCellScheme.below
      ((addLayerCell S j r hS).toCellScheme.gradedIndex s.castSucc)) :
    (addLayerCell S j r hS).rows.row s.castSucc t =
      σ ((addLayerCell S j r hS).toCellScheme.gradedIndex t.1) :=
  Scheme.row_castSucc_eq hs t

/-- **The row of the new cell at `(univ, k)` reads the graded indices by `ρ k`.** -/
theorem row_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ k))) :
    (layerScheme I ρ).rows.row (newCell I ρ k) t =
      ρ k ((layerScheme I ρ).toCellScheme.gradedIndex t.1) := by
  obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  · exact row_castSucc_addLayerCell (σ := ρ 1) (row_castSucc_addLayerCell (σ := ρ 1)
      (row_castSucc_addLayerCell (σ := ρ 1) row_last_addLayerCell)) t
  · exact row_castSucc_addLayerCell (σ := ρ 2)
      (row_castSucc_addLayerCell (σ := ρ 2) row_last_addLayerCell) t
  · exact row_castSucc_addLayerCell (σ := ρ 3) row_last_addLayerCell t
  · exact row_last_addLayerCell t

/-- The row of the new cell at `(univ, k)`, as a function. -/
theorem row_newCell_eq {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (layerScheme I ρ).rows.row (newCell I ρ k) =
      fun t ↦ ρ k ((layerScheme I ρ).toCellScheme.gradedIndex t.1) :=
  funext (row_newCell hk1 hk4)

/-! ### The old cells -/

/-- The old cells of a scheme form a lower embedding into the scheme with a new cell. -/
theorem isLowerEmbedding_addLayerCell (S : Scheme.{u} 5) (j : ℕ)
    (r : Finset (Fin 5) × ℕ → Label.{u}) (h : NoneAbove S j) :
    S.toCellScheme.IsLowerEmbedding (addLayerCell S j r h).toCellScheme Fin.castSucc :=
  Scheme.isLowerEmbedding_castSucc _ _ _

/-- The rows pull back along the old cells. -/
theorem comap_rows_addLayerCell (S : Scheme.{u} 5) (j : ℕ) (r : Finset (Fin 5) × ℕ → Label.{u})
    (h : NoneAbove S j) :
    (addLayerCell S j r h).rows.comap (isLowerEmbedding_addLayerCell S j r h) = S.rows :=
  Scheme.comap_rows_castSucc

variable (I ρ) in
/-- **The old cells form a lower embedding** of the amalgam into the layer scheme. -/
theorem isLowerEmbedding_oldCell :
    I.amalgam.toCellScheme.IsLowerEmbedding (layerScheme I ρ).toCellScheme (oldCell I ρ) :=
  (isLowerEmbedding_addLayerCell _ 4 _ (noneAbove_addLayerCell _)).comp
    ((isLowerEmbedding_addLayerCell _ 3 _ (noneAbove_addLayerCell _)).comp
      ((isLowerEmbedding_addLayerCell _ 2 _ (noneAbove_addLayerCell _)).comp
        (isLowerEmbedding_addLayerCell _ 1 _ (noneAbove_amalgam I))))

/-- **The rows of the layer scheme pull back to those of the amalgam** along the old cells. -/
theorem comap_rows_oldCell :
    (layerScheme I ρ).rows.comap (isLowerEmbedding_oldCell I ρ) = I.amalgam.rows := by
  -- Unfold the embedding of the old cells into the composite of the four one-cell embeddings.
  change (layerScheme I ρ).rows.comap
    ((isLowerEmbedding_addLayerCell _ 4 _ (noneAbove_addLayerCell _)).comp
      ((isLowerEmbedding_addLayerCell _ 3 _ (noneAbove_addLayerCell _)).comp
        ((isLowerEmbedding_addLayerCell _ 2 _ (noneAbove_addLayerCell _)).comp
          (isLowerEmbedding_addLayerCell _ 1 _ (noneAbove_amalgam I))))) = _
  rw [← CellScheme.Rows.comap_comap, comap_rows_addLayerCell, ← CellScheme.Rows.comap_comap,
    comap_rows_addLayerCell, ← CellScheme.Rows.comap_comap, comap_rows_addLayerCell,
    comap_rows_addLayerCell]
  all_goals first
    | exact isLowerEmbedding_addLayerCell _ _ _ _
    | exact (isLowerEmbedding_addLayerCell _ _ _ _).comp (isLowerEmbedding_addLayerCell _ _ _ _)
    | exact (isLowerEmbedding_addLayerCell _ _ _ _).comp
        ((isLowerEmbedding_addLayerCell _ _ _ _).comp (isLowerEmbedding_addLayerCell _ _ _ _))

/-- The old cells keep their scopes. -/
@[simp] theorem scope_oldCell (d : Fin I.amalgam.card) :
    (layerScheme I ρ).toCellScheme.scope (oldCell I ρ d) = I.amalgam.toCellScheme.scope d :=
  congrArg Prod.fst (gradedIndex_oldCell d)

/-- The old cells keep their grades. -/
@[simp] theorem grade_oldCell (d : Fin I.amalgam.card) :
    (layerScheme I ρ).toCellScheme.grade (oldCell I ρ d) = I.amalgam.toCellScheme.grade d :=
  congrArg Prod.snd (gradedIndex_oldCell d)

/-- The new cells have full scope. -/
theorem scope_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (layerScheme I ρ).toCellScheme.scope (newCell I ρ k) = univ :=
  congrArg Prod.fst (gradedIndex_newCell hk1 hk4)

/-- The new cell at `(univ, k)` has grade `k`. -/
theorem grade_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (layerScheme I ρ).toCellScheme.grade (newCell I ρ k) = k :=
  congrArg Prod.snd (gradedIndex_newCell hk1 hk4)

/-- **Every cell of the layer scheme is old or one of the four new cells.** -/
theorem cell_cases (z : Fin (layerScheme I ρ).card) :
    (∃ d, z = oldCell I ρ d) ∨ z = newCell I ρ 1 ∨ z = newCell I ρ 2 ∨ z = newCell I ρ 3 ∨
      z = newCell I ρ 4 := by
  -- The layer scheme has the cells of the amalgam and four more, so `Fin.lastCases` applies.
  change Fin (I.amalgam.card + 1 + 1 + 1 + 1) at z
  induction z using Fin.lastCases with
  | last => exact .inr (.inr (.inr (.inr rfl)))
  | cast z =>
    induction z using Fin.lastCases with
    | last => exact .inr (.inr (.inr (.inl rfl)))
    | cast z =>
      induction z using Fin.lastCases with
      | last => exact .inr (.inr (.inl rfl))
      | cast z =>
        induction z using Fin.lastCases with
        | last => exact .inr (.inl rfl)
        | cast d => exact .inl ⟨d, rfl⟩

/-- The scope of an old cell is not the ground set. -/
theorem scope_oldCell_ne (d : Fin I.amalgam.card) :
    (layerScheme I ρ).toCellScheme.scope (oldCell I ρ d) ≠ univ := by
  rw [scope_oldCell]; exact I.scope_ne_univ d

/-- A cell of scope other than the ground set is old. -/
theorem exists_eq_oldCell {z : Fin (layerScheme I ρ).card}
    (hz : (layerScheme I ρ).toCellScheme.scope z ≠ univ) : ∃ d, z = oldCell I ρ d := by
  rcases cell_cases z with h | rfl | rfl | rfl | rfl
  · exact h
  all_goals exact absurd (scope_newCell (by omega) (by omega)) hz

/-- A cell of full scope is one of the new cells. -/
theorem eq_newCell_of_scope {z : Fin (layerScheme I ρ).card}
    (hz : (layerScheme I ρ).toCellScheme.scope z = univ) :
    ∃ j, 1 ≤ j ∧ j ≤ 4 ∧ z = newCell I ρ j := by
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · exact absurd hz (scope_oldCell_ne d)
  · exact ⟨1, le_rfl, by omega, rfl⟩
  · exact ⟨2, by omega, by omega, rfl⟩
  · exact ⟨3, by omega, by omega, rfl⟩
  · exact ⟨4, by omega, le_rfl, rfl⟩

/-- The only cell at `(univ, k)` is the new cell. -/
theorem eq_newCell {z : Fin (layerScheme I ρ).card} {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hz : (layerScheme I ρ).toCellScheme.gradedIndex z = (univ, k)) : z = newCell I ρ k := by
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [gradedIndex_oldCell] at hz
    exact absurd (congrArg Prod.fst hz) (I.scope_ne_univ d)
  all_goals
    rw [gradedIndex_newCell (by omega) (by omega)] at hz
    obtain ⟨-, hk⟩ := Prod.mk.inj hz
    subst hk
    rfl

/-- Every cell has grade at most `4`. -/
theorem grade_le_four (z : Fin (layerScheme I ρ).card) :
    (layerScheme I ρ).toCellScheme.grade z ≤ 4 := by
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [grade_oldCell]; exact Nat.lt_succ_iff.mp (I.grade_lt d)
  all_goals rw [grade_newCell (by omega) (by omega)]
  all_goals omega

/-- Every cell is below `(univ, 4)`. -/
theorem mem_below_univ_four (z : Fin (layerScheme I ρ).card) :
    z ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), 4) :=
  ⟨subset_univ _, grade_le_four z⟩

/-- Below a pair of scope other than the ground set, the cells are the old cells. -/
theorem image_oldCell_below {X : Finset (Fin 5) × ℕ} (hX : X.1 ≠ univ) :
    oldCell I ρ '' I.amalgam.toCellScheme.below X = (layerScheme I ρ).toCellScheme.below X := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [CellScheme.mem_below, gradedIndex_oldCell]
    exact hd
  · intro hz
    obtain ⟨d, rfl⟩ := exists_eq_oldCell (I := I) (ρ := ρ) (z := z) fun h ↦
      hX (univ_subset_iff.mp (h ▸ hz.1))
    refine ⟨d, ?_, rfl⟩
    rw [CellScheme.mem_below, ← gradedIndex_oldCell]
    exact hz

/-- **Below a pair of scope other than the ground set, lawfulness in the layer scheme is
lawfulness in the amalgam**, along the old cells. -/
theorem isLawfulBelow_oldCell_iff {X : Finset (Fin 5) × ℕ} (hX : X.1 ≠ univ)
    {w : Fin (layerScheme I ρ).card → Label.{u}} :
    (layerScheme I ρ).rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (oldCell I ρ d)) := by
  have h := Rows.isLawfulBelow_comap_iff (R := (layerScheme I ρ).rows)
    (isLowerEmbedding_oldCell I ρ) (image_oldCell_below hX) (r := fun z ↦ w z)
  rw [comap_rows_oldCell] at h
  exact h.symm

/-- The rows of the old cells are those of the amalgam. -/
theorem row_oldCell (s d : Fin I.amalgam.card)
    (h : oldCell I ρ d ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (oldCell I ρ s)))
    (h' : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    (layerScheme I ρ).rows.row (oldCell I ρ s) ⟨oldCell I ρ d, h⟩ =
      I.amalgam.rows.row s ⟨d, h'⟩ :=
  congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row s ⟨d, h'⟩)
    (comap_rows_oldCell (I := I) (ρ := ρ))

/-- A cell below an old cell is old. -/
theorem exists_oldCell_of_mem_below {s : Fin I.amalgam.card} {z : Fin (layerScheme I ρ).card}
    (hz : z ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (oldCell I ρ s))) :
    ∃ d, z = oldCell I ρ d ∧
      d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s) := by
  obtain ⟨d, rfl⟩ := (isLowerEmbedding_oldCell I ρ).mem_range s z hz
  exact ⟨d, rfl, ((isLowerEmbedding_oldCell I ρ).le_iff d s).mp hz⟩

/-- An old cell is below a pair when its graded index is. -/
theorem oldCell_mem_below {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ}
    (h : I.amalgam.toCellScheme.gradedIndex d ≤ X) :
    oldCell I ρ d ∈ (layerScheme I ρ).toCellScheme.below X := by
  rw [CellScheme.mem_below, gradedIndex_oldCell]; exact h

/-- A new cell is below `(univ, k)` for `j ≤ k`. -/
theorem newCell_mem_below {j k : ℕ} (hj1 : 1 ≤ j) (hj4 : j ≤ 4) (hjk : j ≤ k) :
    newCell I ρ j ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), k) := by
  rw [CellScheme.mem_below, gradedIndex_newCell hj1 hj4]; exact ⟨subset_rfl, hjk⟩

/-- A cell below the new cell at `(univ, k)` has grade at most `k`. -/
theorem grade_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ k))) :
    (layerScheme I ρ).toCellScheme.grade t.1 ≤ k := by
  have h : (layerScheme I ρ).toCellScheme.gradedIndex t.1 ≤ ((univ : Finset (Fin 5)), k) :=
    gradedIndex_newCell hk1 hk4 ▸ t.2
  exact h.2

/-- The new cell at `(univ, k)` is below itself. -/
theorem newCell_mem_below_self {k : ℕ} :
    newCell I ρ k ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ k)) :=
  (layerScheme I ρ).toCellScheme.mem_below_gradedIndex _

/-- An old cell below the new cell at `(univ, k)`, of grade at most `k`. -/
theorem oldCell_mem_below_newCell {d : Fin I.amalgam.card} {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hd : I.amalgam.toCellScheme.grade d ≤ k) :
    oldCell I ρ d ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ k)) := by
  rw [gradedIndex_newCell hk1 hk4]
  exact oldCell_mem_below ⟨subset_univ _, hd⟩

/-! ### The two coatoms -/

/-- The first coatom `C = {0, 1, 2, 3}`. -/
abbrev coatomC : Finset (Fin 5) := univ.erase (Fin.last 4)

/-- The second coatom `D = {0, 1, 2, 4}`. -/
abbrev coatomD : Finset (Fin 5) := univ.erase (Fin.castSucc (Fin.last 3))

/-- The first coatom is the image of the first coatom embedding. -/
theorem coatomC_eq : coatomC = univ.map (Coatom.left 3) := Coatom.univ_map_left.symm

/-- The second coatom is the image of the second coatom embedding. -/
theorem coatomD_eq : coatomD = univ.map (Coatom.right 3) := Coatom.univ_map_right.symm

variable (I) in
/-- The first coatom is a face of the amalgam. -/
theorem coatomC_mem_faces : coatomC ∈ I.amalgam.toCellScheme.faces :=
  coatomC_eq ▸ ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1

variable (I) in
/-- The second coatom is a face of the amalgam. -/
theorem coatomD_mem_faces : coatomD ∈ I.amalgam.toCellScheme.faces :=
  coatomD_eq ▸ ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1

/-- An old cell below `(univ, k)` lies below one of the two coatoms at the grade `k`. -/
theorem mem_below_coatom_of_ne {z : Fin (layerScheme I ρ).card} {k : ℕ}
    (hz : z ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), k))
    (hne : (layerScheme I ρ).toCellScheme.scope z ≠ univ) :
    z ∈ (layerScheme I ρ).toCellScheme.below (coatomC, k) ∨
      z ∈ (layerScheme I ρ).toCellScheme.below (coatomD, k) := by
  obtain ⟨d, rfl⟩ := exists_eq_oldCell hne
  rw [CellScheme.mem_below, gradedIndex_oldCell] at hz
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d) with h | h
  · exact .inl (oldCell_mem_below ⟨h, hz.2⟩)
  · exact .inr (oldCell_mem_below ⟨h, hz.2⟩)

/-- A cell below `(C, k)` misses the point `4`. -/
theorem four_notMem_of_mem_below {z : Fin (layerScheme I ρ).card} {k : ℕ}
    (hz : z ∈ (layerScheme I ρ).toCellScheme.below (coatomC, k)) :
    (4 : Fin 5) ∉ ((layerScheme I ρ).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.last 4) univ) (hz.1 h)

/-- A cell below `(D, k)` misses the point `3`. -/
theorem three_notMem_of_mem_below {z : Fin (layerScheme I ρ).card} {k : ℕ}
    (hz : z ∈ (layerScheme I ρ).toCellScheme.below (coatomD, k)) :
    (3 : Fin 5) ∉ ((layerScheme I ρ).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.castSucc (Fin.last 3)) univ) (hz.1 h)

/-! ### Legality below the full grade -/

/-- The faces of the layer scheme are those of the amalgam. -/
theorem faces_layerScheme :
    (layerScheme I ρ).toCellScheme.faces = I.amalgam.toCellScheme.faces := rfl

/-- **Pairs below a coatom**: the capped lifts of the amalgam, transported along the old
cells. -/
theorem cappedLift_old {X Y : Finset (Fin 5) × ℕ}
    (hX : X ∈ (layerScheme I ρ).toCellScheme.gradedFaces)
    (hY : Y ∈ (layerScheme I ρ).toCellScheme.gradedFaces) (hY1 : Y.1 ≠ univ) (h : X ≤ Y) :
    (layerScheme I ρ).rows.CappedLift h := by
  have hX1 : X.1 ≠ univ := fun hX ↦ hY1 (univ_subset_iff.mp (hX ▸ h.1))
  refine Rows.CappedLift.of_comap (isLowerEmbedding_oldCell I ρ) (image_oldCell_below hX1)
    (image_oldCell_below hY1) le_rfl (h' := h) ?_
  rw [comap_rows_oldCell]
  exact I.isBountiful hX hY h

/-- **The layer scheme is bountiful** once the rows lift capped from each coatom into the full
scope at each grade `1 ≤ k ≤ 4`.  By `Rows.isBountiful_iff_forall_cappedLift_fst` it is enough to
lift from `X` to the pair on the face of `Y` at the grade of `X`.  Below a coatom the lifts are
those of the amalgam; to the full scope, a lift from `(B, k)` goes first within the amalgam to the
coatom containing `B`, and then by the given lift. -/
theorem isBountiful_layerScheme
    (hC : ∀ k, 1 ≤ k → k ≤ 4 → (layerScheme I ρ).rows.CappedLift (X := (coatomC, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩)
    (hD : ∀ k, 1 ≤ k → k ≤ 4 → (layerScheme I ρ).rows.CappedLift (X := (coatomD, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩) :
    (layerScheme I ρ).rows.IsBountiful := by
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
    · have hB : (coatomC, j) ∈ (layerScheme I ρ).toCellScheme.gradedFaces :=
        ⟨coatomC_mem_faces I, hj1, hj4.trans (show (4 : ℕ) ≤ #coatomC by decide)⟩
      exact (cappedLift_old hX hB (show coatomC ≠ univ by decide) (X := (X1, j))
        ⟨hs, le_rfl⟩).trans (hC j hj1 hj4)
    · have hB : (coatomD, j) ∈ (layerScheme I ρ).toCellScheme.gradedFaces :=
        ⟨coatomD_mem_faces I, hj1, hj4.trans (show (4 : ℕ) ≤ #coatomD by decide)⟩
      exact (cappedLift_old hX hB (show coatomD ≠ univ by decide) (X := (X1, j))
        ⟨hs, le_rfl⟩).trans (hD j hj1 hj4)
  · exact cappedLift_old (Y := (Y.1, X.2)) hX
      ⟨hY.1, hX.2.1, hX.2.2.trans (card_le_card h.1)⟩ hY1 _

/-- Adding a new cell keeps well-formedness. -/
theorem isWellFormed_addLayerCell {S : Scheme.{u} 5} {j : ℕ}
    {r : Finset (Fin 5) × ℕ → Label.{u}} {h : NoneAbove S j}
    (hS : S.IsWellFormed) (hj : 0 < j) (hj5 : j ≤ 5) : (addLayerCell S j r h).IsWellFormed :=
  Scheme.isWellFormed_appendFullCell hS hj hj5

variable (I ρ) in
/-- **The layer scheme is well formed.** -/
theorem isWellFormed_layerScheme : (layerScheme I ρ).IsWellFormed :=
  isWellFormed_addLayerCell (isWellFormed_addLayerCell (isWellFormed_addLayerCell
    (isWellFormed_addLayerCell I.amalgam.isWellFormed (by omega) (by omega)) (by omega)
      (by omega)) (by omega) (by omega)) (by omega) (by omega)

/-- **The layer scheme is coded** when each layer row is coded at the cells below its new cell:
the old rows are those of the amalgam. -/
theorem isCoded_layerScheme
    (hρ : ∀ k, 1 ≤ k → k ≤ 4 → ∀ z ∈ (layerScheme I ρ).toCellScheme.below
      ((univ : Finset (Fin 5)), k), ρ k ((layerScheme I ρ).toCellScheme.gradedIndex z) <
        ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (layerScheme I ρ).IsCoded := by
  intro s t
  rcases cell_cases s with ⟨a, rfl⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨d, hd, hda⟩ := exists_oldCell_of_mem_below t.2
    rw [(layerScheme I ρ).rows.row_congr rfl (t' := ⟨oldCell I ρ d, hd ▸ t.2⟩) hd,
      row_oldCell a d _ hda]
    exact I.amalgam.isCoded _ _
  all_goals
    rw [row_newCell (by omega) (by omega)]
    refine hρ _ (by omega) (by omega) _ ?_
    rw [← gradedIndex_newCell (I := I) (ρ := ρ) (by omega) (by omega)]
    exact t.2

/-- **The rows of the layer scheme are consistent** when the labelling read off the graded indices
by `ρ k` is lawful below `(univ, k)`, for each `k = 1, …, 4`. -/
theorem isConsistent_layerScheme
    (hρ : ∀ k, 1 ≤ k → k ≤ 4 → (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ ρ k ((layerScheme I ρ).toCellScheme.gradedIndex z)) :
    (layerScheme I ρ).rows.IsConsistent := by
  intro s
  rcases cell_cases s with ⟨a, rfl⟩ | rfl | rfl | rfl | rfl
  · have hφ := isLowerEmbedding_oldCell I ρ
    refine (Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex a)).mp ?_
    rw [comap_rows_oldCell]
    convert I.isConsistent a using 1
    funext t
    exact congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row a t) comap_rows_oldCell
  all_goals
    rw [row_newCell_eq (by omega) (by omega), gradedIndex_newCell (by omega) (by omega)]
    exact hρ _ (by omega) (by omega)

/-- **The layer scheme is complete below the full grade.** -/
theorem exists_gradedIndex_eq_layerScheme {X : Finset (Fin 5) × ℕ}
    (hX : X ∈ (layerScheme I ρ).toCellScheme.gradedFaces) (hX5 : X.2 < 5) :
    ∃ z, (layerScheme I ρ).toCellScheme.gradedIndex z = X := by
  by_cases hX1 : X.1 = univ
  · obtain ⟨X1, k⟩ := X
    simp only at hX1 hX5
    subst hX1
    exact ⟨newCell I ρ k, gradedIndex_newCell hX.2.1 (by omega)⟩
  · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq X hX hX1
    exact ⟨oldCell I ρ d, (gradedIndex_oldCell d).trans hd⟩

/-! ### Lifts at the grades below `3` from lifts at the grade `3` -/

/-- **From lifts at the grade `3` to capped lifts at a grade `k ≤ 3`.**  A prescription below
`(B, k)` and an ambient below `(univ, k)` are extended by `⊥` above the grade `k`; a lift at the
grade `3` of the extensions, restricted below `(univ, k)`, is the capped lift.  So the lifts at
the grades `k ≤ 3` need only be given for labellings that vanish above the grade `k`, at caps
self-visible at `k`. -/
theorem cappedLift_of_lift_three {B : Finset (Fin 5)} {k : ℕ} (hk3 : k ≤ 3)
    (H : ∀ c : Label.{u}, IsSelfVisible k c → ∀ p q : Fin (layerScheme I ρ).card → Label.{u},
      (layerScheme I ρ).rows.IsLawfulBelow (B, 3) (fun z ↦ p z) →
      (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ q z) →
      (∀ z, k < (layerScheme I ρ).toCellScheme.grade z → p z = ⊥) →
      (∀ z, k < (layerScheme I ρ).toCellScheme.grade z → q z = ⊥) →
      (∀ z ∈ (layerScheme I ρ).toCellScheme.below (B, 3), min (q z) c = min (p z) c) →
      ∃ x : Fin (layerScheme I ρ).card → Label.{u},
        (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
        (∀ z ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), 3),
          min (x z) c = min (q z) c) ∧
        ∀ z ∈ (layerScheme I ρ).toCellScheme.below (B, 3), x z = p z) :
    (layerScheme I ρ).rows.CappedLift (X := (B, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ := by
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  let p' : Fin (layerScheme I ρ).card → Label.{u} := fun z ↦
    if (layerScheme I ρ).toCellScheme.grade z ≤ k then Rows.extendBot (B, k) p z else ⊥
  let q' : Fin (layerScheme I ρ).card → Label.{u} := fun z ↦
    if (layerScheme I ρ).toCellScheme.grade z ≤ k then
      Rows.extendBot ((univ : Finset (Fin 5)), k) q z else ⊥
  have hp' (z) : p' z = if (layerScheme I ρ).toCellScheme.grade z ≤ k then
      Rows.extendBot (B, k) p z else ⊥ := rfl
  have hq' (z) : q' z = if (layerScheme I ρ).toCellScheme.grade z ≤ k then
      Rows.extendBot ((univ : Finset (Fin 5)), k) q z else ⊥ := rfl
  have hpl : (layerScheme I ρ).rows.IsLawfulBelow (B, 3) (fun z ↦ p' z) :=
    Rows.isLawfulBelow_extendAbove (Rows.isLawfulBelow_extendBot.mpr hp)
  have hql : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ q' z) :=
    Rows.isLawfulBelow_extendAbove (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpq' : ∀ z ∈ (layerScheme I ρ).toCellScheme.below (B, 3), min (q' z) c = min (p' z) c := by
    intro z hz
    rw [hp', hq']
    split_ifs with h
    · rw [Rows.extendBot_of_mem p (⟨hz.1, h⟩ : z ∈ (layerScheme I ρ).toCellScheme.below (B, k)),
        Rows.extendBot_of_mem q (⟨subset_univ _, h⟩ :
          z ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), k))]
      exact hpq ⟨z, ⟨hz.1, h⟩⟩
    · rfl
  obtain ⟨x, hx, hxq, hxp⟩ := H c hc p' q' hpl hql
    (fun z hz ↦ by rw [hp', ite_eq_right (by omega)])
    (fun z hz ↦ by rw [hq', ite_eq_right (by omega)]) hpq'
  refine ⟨fun z ↦ x z, hx.mono (X := ((univ : Finset (Fin 5)), k)) ⟨subset_rfl, hk3⟩,
    fun z ↦ ?_, fun z ↦ ?_⟩
  · have hz : (layerScheme I ρ).toCellScheme.grade z.1 ≤ k := z.2.2
    rw [hxq z.1 ⟨subset_univ _, hz.trans hk3⟩, hq', ite_eq_left hz,
      Rows.extendBot_of_mem q z.2]
  · have hz : (layerScheme I ρ).toCellScheme.grade z.1 ≤ k := z.2.2
    -- The restriction of `x` below `(univ, k)`, at `z`.
    change x z.1 = p z
    rw [hxp z.1 ⟨z.2.1, hz.trans hk3⟩, hp', ite_eq_left hz, Rows.extendBot_of_mem p z.2]

/-- The old cells, in their order. -/
noncomputable def embedOld : Fin I.amalgam.card ↪o Fin (layerScheme I ρ).card :=
  OrderEmbedding.ofStrictMono (oldCell I ρ) fun _ _ h ↦ by
    unfold oldCell; simpa [Fin.castSucc_lt_castSucc_iff] using h

end VaughtConjecture.OrderedLayer

namespace VaughtConjecture.Seed

open Finset Label CellScheme OrderedLayer

variable {α : Ordinal.{u}} (I : Seed.{u} α 3) (ρ : LayerRows.{u})

/-- **The ordered-layer step** of a seed on five points with layer rows `ρ`: the conditions under
which the layer scheme (`OrderedLayer.layerScheme`: the amalgam with one new cell at each graded
face `(univ, k)` of full scope, whose row reads the graded indices by `ρ k`) is legal below the
full grade and carries a lawful extension of the glued labelling.

* `row_lt`: the layer rows are coded at the cells below their new cells;
* `isLawfulBelow_row`: the labelling read off the graded indices by `ρ k` is lawful below
  `(univ, k)` (the consistency of the new rows);
* `cappedLift_left`, `cappedLift_right`: the capped lifts from `(C, k)` and `(D, k)` into
  `(univ, k)`, `1 ≤ k ≤ 4`, the only lifts that need capping;
* `exists_isLawful`: a lawful labelling of the layer scheme equal to the glued labelling on the
  old cells. -/
structure OrderedLayerStep : Prop where
  /-- The layer rows are coded: every value at a cell below the new cell lies below `ω ^ 2`. -/
  row_lt : ∀ k, 1 ≤ k → k ≤ 4 → ∀ z ∈ (layerScheme I ρ).toCellScheme.below
    ((univ : Finset (Fin 5)), k), ρ k ((layerScheme I ρ).toCellScheme.gradedIndex z) <
      ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})
  /-- The row of the new cell at `(univ, k)` is lawful below `(univ, k)`. -/
  isLawfulBelow_row : ∀ k, 1 ≤ k → k ≤ 4 →
    (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ ρ k ((layerScheme I ρ).toCellScheme.gradedIndex z)
  /-- The capped lift from `(C, k)` to `(univ, k)`. -/
  cappedLift_left : ∀ k, 1 ≤ k → k ≤ 4 → (layerScheme I ρ).rows.CappedLift (X := (coatomC, k))
    (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩
  /-- The capped lift from `(D, k)` to `(univ, k)`. -/
  cappedLift_right : ∀ k, 1 ≤ k → k ≤ 4 → (layerScheme I ρ).rows.CappedLift (X := (coatomD, k))
    (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩
  /-- A lawful labelling of the layer scheme extends the glued labelling of the amalgam. -/
  exists_isLawful : ∃ w : Fin (layerScheme I ρ).card → Label.{u},
    (layerScheme I ρ).rows.IsLawful w ∧ ∀ d, w (oldCell I ρ d) = I.amalgam.label d

variable {I ρ}

/-- **The layer scheme is legal below the full grade** under the ordered-layer step. -/
theorem OrderedLayerStep.isLegalBelowFullGrade (h : I.OrderedLayerStep ρ) :
    (layerScheme I ρ).IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_layerScheme I ρ
  isCoded := isCoded_layerScheme h.row_lt
  isConsistent := isConsistent_layerScheme h.isLawfulBelow_row
  isBountiful := isBountiful_layerScheme h.cappedLift_left h.cappedLift_right
  grade_lt z := Nat.lt_succ_of_le (grade_le_four z)
  exists_gradedIndex_eq _ hX hX5 := exists_gradedIndex_eq_layerScheme hX hX5

/-- **The completion from the ordered-layer step**: the layer scheme, with a lawful labelling
extending the glued one. -/
noncomputable def OrderedLayerStep.completion (h : I.OrderedLayerStep ρ) :
    CompletionBelowFullGrade I where
  scheme := layerScheme I ρ
  embed := embedOld
  isLowerEmbedding := isLowerEmbedding_oldCell I ρ
  scope_embed := scope_oldCell
  comap_rows := comap_rows_oldCell
  mem_range_embed z hz := by
    obtain ⟨d, rfl⟩ := exists_eq_oldCell hz
    exact ⟨d, rfl⟩
  faces_eq := faces_layerScheme
  isLegalBelowFullGrade := h.isLegalBelowFullGrade
  label := h.exists_isLawful.choose
  isLawful := h.exists_isLawful.choose_spec.1
  label_embed := h.exists_isLawful.choose_spec.2

/-- The scheme of the completion from the ordered-layer step is the layer scheme. -/
theorem OrderedLayerStep.completion_scheme (h : I.OrderedLayerStep ρ) :
    h.completion.scheme = layerScheme I ρ := rfl

/-- The old cells of the completion from the ordered-layer step are the old cells of the layer
scheme. -/
theorem OrderedLayerStep.completion_embed (h : I.OrderedLayerStep ρ) (d : Fin I.amalgam.card) :
    h.completion.embed d = oldCell I ρ d := rfl

/-- **The ordered-layer step gives a completion below the full grade.** -/
theorem OrderedLayerStep.nonempty_completionBelowFullGrade (h : I.OrderedLayerStep ρ) :
    Nonempty (CompletionBelowFullGrade I) :=
  ⟨h.completion⟩

/-- **The ordered-layer step is exactly legality of the layer scheme with a lawful extension**:
the hypothesis is the exact content of a completion with one new cell per graded face of full
scope, whose rows are read off graded indices. -/
theorem orderedLayerStep_iff : I.OrderedLayerStep ρ ↔
    (layerScheme I ρ).IsLegalBelowFullGrade ∧ ∃ w : Fin (layerScheme I ρ).card → Label.{u},
      (layerScheme I ρ).rows.IsLawful w ∧ ∀ d, w (oldCell I ρ d) = I.amalgam.label d := by
  refine ⟨fun h ↦ ⟨h.isLegalBelowFullGrade, h.exists_isLawful⟩, fun ⟨hL, hw⟩ ↦ ⟨?_, ?_, ?_, ?_, hw⟩⟩
  · intro k hk1 hk4 z hz
    rw [← gradedIndex_newCell (I := I) (ρ := ρ) hk1 hk4] at hz
    have := hL.isCoded (newCell I ρ k) ⟨z, hz⟩
    rwa [row_newCell hk1 hk4] at this
  · intro k hk1 hk4
    have := hL.isConsistent (newCell I ρ k)
    rw [row_newCell_eq hk1 hk4, gradedIndex_newCell hk1 hk4] at this
    exact this
  · intro k hk1 hk4
    have hX : ((coatomC, k) : Finset (Fin 5) × ℕ) ∈ (layerScheme I ρ).toCellScheme.gradedFaces :=
      ⟨coatomC_mem_faces I, hk1, hk4.trans (show (4 : ℕ) ≤ #coatomC by decide)⟩
    have hY : ((univ : Finset (Fin 5)), k) ∈ (layerScheme I ρ).toCellScheme.gradedFaces :=
      ⟨(isWellFormed_layerScheme I ρ).univ_mem_faces, hk1, by simp; omega⟩
    exact hL.isBountiful hX hY _
  · intro k hk1 hk4
    have hX : ((coatomD, k) : Finset (Fin 5) × ℕ) ∈ (layerScheme I ρ).toCellScheme.gradedFaces :=
      ⟨coatomD_mem_faces I, hk1, hk4.trans (show (4 : ℕ) ≤ #coatomD by decide)⟩
    have hY : ((univ : Finset (Fin 5)), k) ∈ (layerScheme I ρ).toCellScheme.gradedFaces :=
      ⟨(isWellFormed_layerScheme I ρ).univ_mem_faces, hk1, by simp; omega⟩
    exact hL.isBountiful hX hY _

variable (I ρ) in
/-- **The ordered-layer step below the top grade**: the fields of `OrderedLayerStep` at the grades
`k ≤ 3`.  For a seed whose two coatom types are the apex added to `⊥` labels
(`Seed.HasBottomApexes`), with the top row at the grade `4` (`OrderedLayer.topRow`), it gives the
ordered-layer step (`Seed.OrderedLayerStepBelowTop.orderedLayerStep`,
`VaughtConjecture.Extension.OrderedLayerTop`). -/
structure OrderedLayerStepBelowTop : Prop where
  /-- The layer rows at the grades `k ≤ 3` are coded at the cells below their new cells. -/
  row_lt : ∀ k, 1 ≤ k → k ≤ 3 → ∀ z ∈ (layerScheme I ρ).toCellScheme.below
    ((univ : Finset (Fin 5)), k), ρ k ((layerScheme I ρ).toCellScheme.gradedIndex z) <
      ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})
  /-- The row of the new cell at `(univ, k)`, `k ≤ 3`, is lawful below `(univ, k)`. -/
  isLawfulBelow_row : ∀ k, 1 ≤ k → k ≤ 3 →
    (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ ρ k ((layerScheme I ρ).toCellScheme.gradedIndex z)
  /-- The capped lift from `(C, k)` to `(univ, k)`, `k ≤ 3`. -/
  cappedLift_left : ∀ k, 1 ≤ k → k ≤ 3 → (layerScheme I ρ).rows.CappedLift (X := (coatomC, k))
    (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩
  /-- The capped lift from `(D, k)` to `(univ, k)`, `k ≤ 3`. -/
  cappedLift_right : ∀ k, 1 ≤ k → k ≤ 3 → (layerScheme I ρ).rows.CappedLift (X := (coatomD, k))
    (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩

variable (I) in
/-- A seed on five points **has an ordered-layer step** when it has one for some layer rows. -/
def HasOrderedLayerStep : Prop := ∃ ρ : LayerRows.{u}, I.OrderedLayerStep ρ

/-- **The completion at `m = 3` from the ordered-layer step**: a seed with an ordered-layer step
has a completion below the full grade. -/
theorem HasOrderedLayerStep.nonempty_completionBelowFullGrade (h : I.HasOrderedLayerStep) :
    Nonempty (CompletionBelowFullGrade I) :=
  h.choose_spec.nonempty_completionBelowFullGrade

end VaughtConjecture.Seed
