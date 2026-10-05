/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedRow

/-!
# The thin scheme of the asymmetric seed and its lawful labellings below `(univ, 3)`

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the recursion on the grade; here the scheme of the
thin completion of a seed whose coatom types are `TL` and `T5`, and its lawful labellings below
the grade `3`); semantic contract, items 2–4.

Let `I` be a seed on five points, with coatoms `C = {0, 1, 2, 3}` (`coatomC`) and
`D = {0, 1, 2, 4}` (`coatomD`).

**The thin scheme** (`thinScheme I`): the cells of the amalgam of `I`, in their order (the *old
cells*, `oldCell`), followed by one new cell at each graded face `(univ, k)` of full scope,
`k = 1, 2, 3, 4` (`newCell`), appended in that order (`addThinCell`, by `Scheme.appendFullCell`; no
cell lies above `(univ, k)` when the new cell of grade `k` is added).  The row of the new cell at
`(univ, k)` reads the *kind* of each cell below it by the ordered row `thinRow k`
(`VaughtConjecture.Extension.OrderedRow`; `row_newCell`).  The kinds are read off graded indices
(`thinKind`): at the full scope, the kind of the new cell of that grade; at another scope, `Ω` at
the grade `4` (the two apexes) and otherwise the live kind of `tripleKind`, with `F_C` and `F_D`
merged into `F`.  The *thin labelling* of parameters `A_C`, `A_D`, `F`, `G`, `Ω`
(`thinLabelling`) gives each cell the parameter of its kind.

**The old cells** form a lower embedding of the amalgam (`isLowerEmbedding_oldCell`) along which
the rows pull back to those of the amalgam (`comap_rows_oldCell`), so below a pair of scope other
than the ground set lawfulness is lawfulness in the amalgam (`isLawfulBelow_oldCell_iff`).  Every
cell is old or one of the four new cells (`cell_cases`), and a cell of scope other than the ground
set is old (`exists_eq_oldCell`).

**The lawful labellings below `(univ, 3)`**, for a seed whose coatom types are `TL` and `T5`, are
exactly the thin labellings of parameters satisfying `IsThinLawfulBelow`:

* *sufficiency* (`isLawfulBelow_thinLabel`): on the old cells the thin labelling is
  `tripleLabelling A_C F A_D F G`, lawful below both coatoms at the grade `3`
  (`isLawfulBelow_tripleLabelling`); at the new cells the witnesses of `OrderedRow` give locality;
  and availability into a new cell holds since every cell of its grade carries at most its label;
* *necessity* (`exists_of_isLawfulBelow_three`): below `C` a lawful labelling is a labelling of `TL`
  (`exists_of_isLawfulBelow_left`, with `G ≤ F` and `VisibilityReplaceFixedOfLT A_C G`), below `D`
  one of `T5` (`exists_of_isLawfulBelow_right`, with `G ≤ A_D` and `G ≤ F`); locality and
  availability at the new cells identify the label of the new cell at `(univ, 1)` with `A_D`, of
  `(univ, 2)` with both `F_C` and `F_D`, and of `(univ, 3)` with `G`, and give `A_C ≤ A_D`
  (availability into the new cell at `(univ, 1)`); the collision lemma
  (`eq_of_transformsTo_collision`) at the new cell at `(univ, 2)` excludes collisions.

Below `(univ, k)` for `k < 3` the same holds with `F` or `G` set to `⊥`, through the extension of a
lawful labelling by `⊥` above a grade (`isLawfulBelow_extendAbove`, for any rows).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ThinCompletion

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftExistsCounterexample
open TwoFaceLiftCounterexample (liveC liveD)
open CaseSplitCounterexample (tripleLabelling tripleKind liveG)

/-! ### Kinds of graded indices -/

/-- The **kind** of a graded index on five points (see `kindLabel`): at the full scope, the kind
of the new cell of that grade; at a scope other than the ground set, `Ω` at the grade `4` (the two
apexes) and otherwise the live kind of `tripleKind`, with `F_C` and `F_D` merged into `F`. -/
def thinKind (X : Finset (Fin 5) × ℕ) : Fin 6 :=
  if X.1 = univ then
    (if X.2 = 1 then 2 else if X.2 = 2 then 3 else if X.2 = 3 then 4 else if X.2 = 4 then 5
      else 0)
  else if X.2 = 4 then 5 else ![0, 1, 3, 2, 3, 4] (tripleKind X)

/-- The **thin labelling** of graded indices with the parameters `A_C`, `A_D`, `F`, `G`, `Ω`. -/
def thinLabel (AC AD F G Ω : Label.{u}) (X : Finset (Fin 5) × ℕ) : Label.{u} :=
  kindLabel AC AD F G Ω (thinKind X)

/-- The grade of the cells of each kind. -/
def kindGrade : Fin 6 → ℕ := ![0, 1, 1, 2, 3, 4]

private theorem liveC_snd : ∀ Y ∈ liveC, Y.2 = 1 ∨ Y.2 = 2 := by decide
private theorem liveD_snd : ∀ Y ∈ liveD, Y.2 = 1 ∨ Y.2 = 2 := by decide
private theorem liveC_three : ∀ Y ∈ liveC, (3 : Fin 5) ∈ Y.1 := by decide
private theorem liveD_four : ∀ Y ∈ liveD, (4 : Fin 5) ∈ Y.1 := by decide

/-- A graded index of a live kind has the grade of its kind. -/
theorem snd_eq_kindGrade {X : Finset (Fin 5) × ℕ} (hX : thinKind X ≠ 0) :
    X.2 = kindGrade (thinKind X) := by
  unfold thinKind at hX ⊢
  split_ifs at hX ⊢ with h1 h2 h3 h4 h5 h6 <;> try first | rfl | exact (hX rfl).elim
  all_goals first | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | skip
  unfold tripleKind at hX ⊢
  split_ifs at hX ⊢ with hC hC1 hD hD1 hG
  · exact hC1
  · exact (liveC_snd X hC).resolve_left hC1
  · exact hD1
  · exact (liveD_snd X hD).resolve_left hD1
  · exact CaseSplitCounterexample.liveG_three X hG
  · exact (hX rfl).elim

/-- A graded index whose scope misses the point `4` (on the coatom `C`) is not of the kind
`A_D`. -/
theorem thinKind_ne_two {X : Finset (Fin 5) × ℕ} (hX : (4 : Fin 5) ∉ X.1) : thinKind X ≠ 2 := by
  unfold thinKind
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact absurd (h1 ▸ mem_univ _) hX
  all_goals try decide
  unfold tripleKind
  split_ifs with hC hC1 hD hD1 hG <;> try decide
  · exact absurd (liveD_four X hD) hX

/-- A graded index whose scope misses the point `3` (on the coatom `D`) is not of the kind
`A_C`. -/
theorem thinKind_ne_one {X : Finset (Fin 5) × ℕ} (hX : (3 : Fin 5) ∉ X.1) : thinKind X ≠ 1 := by
  unfold thinKind
  split_ifs with h1 h2 h3 h4 h5 h6 <;> try decide
  unfold tripleKind
  split_ifs with hC hC1 hD hD1 hG <;> try decide
  · exact absurd (liveC_three X hC) hX

/-- Below the full scope and below the grade `4`, the thin labelling is the labelling
`tripleLabelling` with `F_C = F_D = F`. -/
theorem thinLabel_eq_tripleLabelling {X : Finset (Fin 5) × ℕ} (h1 : X.1 ≠ univ) (h4 : X.2 ≠ 4)
    (AC AD F G Ω : Label.{u}) :
    thinLabel AC AD F G Ω X = tripleLabelling AC F AD F G X := by
  unfold thinLabel thinKind tripleLabelling
  rw [ite_eq_right h1, ite_eq_right h4]
  generalize tripleKind X = c
  fin_cases c <;> rfl

/-- At a scope other than the ground set, the grade `4` is the kind `Ω`. -/
theorem thinKind_four {B : Finset (Fin 5)} (hB : B ≠ univ) : thinKind (B, 4) = 5 := by
  simp [thinKind, hB]

/-- The new cell at `(univ, 1)` is of the kind `A_D`. -/
@[simp] theorem thinKind_univ_one : thinKind ((univ : Finset (Fin 5)), 1) = 2 := by
  simp [thinKind]
/-- The new cell at `(univ, 2)` is of the kind `F`. -/
@[simp] theorem thinKind_univ_two : thinKind ((univ : Finset (Fin 5)), 2) = 3 := by
  simp [thinKind]
/-- The new cell at `(univ, 3)` is of the kind `G`. -/
@[simp] theorem thinKind_univ_three : thinKind ((univ : Finset (Fin 5)), 3) = 4 := by
  simp [thinKind]
/-- The new cell at `(univ, 4)` is of the kind `Ω`. -/
@[simp] theorem thinKind_univ_four : thinKind ((univ : Finset (Fin 5)), 4) = 5 := by
  simp [thinKind]

/-! ### The thin scheme -/

/-- No cell of `S` lies above a pair `(univ, k)` with `j ≤ k`. -/
def NoneAbove (S : Scheme.{u} 5) (j : ℕ) : Prop :=
  ∀ k, j ≤ k → ∀ d, ¬ ((univ : Finset (Fin 5)), k) ≤ S.toCellScheme.gradedIndex d

/-- **Adding the new cell at `(univ, j)`**, whose row reads the kinds of the cells by
`thinRow j`. -/
noncomputable abbrev addThinCell (S : Scheme.{u} 5) (j : ℕ) (h : NoneAbove S j) :
    Scheme.{u} 5 :=
  S.appendFullCell j (fun d ↦ thinRow j (thinKind ((S.appendFullCellScheme j).gradedIndex d)))
    (h j le_rfl)

/-- After adding the new cell at `(univ, j)`, no cell lies above `(univ, k)` for `j < k`. -/
theorem noneAbove_addThinCell {S : Scheme.{u} 5} {j : ℕ} (h : NoneAbove S j) :
    NoneAbove (addThinCell S j h) (j + 1) := by
  intro k hk d
  induction d using Fin.lastCases with
  | last =>
    rw [Scheme.appendFullCell_toCellScheme, Scheme.appendFullCellScheme_gradedIndex_last]
    exact fun h' ↦ by have := h'.2; simp only at this; omega
  | cast d =>
    rw [Scheme.appendFullCell_toCellScheme, Scheme.appendFullCellScheme_gradedIndex_castSucc]
    exact h k (by omega) d

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- No cell of the amalgam has full scope. -/
theorem noneAbove_amalgam : NoneAbove I.amalgam.toScheme 1 :=
  fun k _ d ↦ I.not_univ_le k d

/-- The scheme with the new cells at `(univ, 1)` and `(univ, 2)`. -/
noncomputable abbrev thinScheme₂ : Scheme.{u} 5 :=
  addThinCell (addThinCell I.amalgam.toScheme 1 (noneAbove_amalgam I)) 2
    (noneAbove_addThinCell _)

/-- **The thin scheme** of a seed `I` on five points: its amalgam, followed by one new cell at each
`(univ, k)`, `k = 1, 2, 3, 4`, whose row is `thinRow k` read off the kinds. -/
noncomputable abbrev thinScheme : Scheme.{u} 5 :=
  addThinCell (addThinCell (thinScheme₂ I) 3 (noneAbove_addThinCell _)) 4
    (noneAbove_addThinCell _)

/-- The old cells: the cells of the amalgam. -/
noncomputable def oldCell (d : Fin I.amalgam.card) : Fin (thinScheme I).card :=
  d.castSucc.castSucc.castSucc.castSucc

/-- The new cell at `(univ, k)`, for `k = 1, 2, 3, 4`. -/
noncomputable def newCell : ℕ → Fin (thinScheme I).card
  | 1 => (Fin.last _).castSucc.castSucc.castSucc
  | 2 => (Fin.last _).castSucc.castSucc
  | 3 => (Fin.last _).castSucc
  | _ => Fin.last _

variable {I}

/-- The old cells keep their graded indices. -/
@[simp] theorem gradedIndex_oldCell (d : Fin I.amalgam.card) :
    (thinScheme I).toCellScheme.gradedIndex (oldCell I d) =
      I.amalgam.toCellScheme.gradedIndex d := by
  simp [oldCell]

/-- The new cell at `(univ, k)` has graded index `(univ, k)`. -/
theorem gradedIndex_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (thinScheme I).toCellScheme.gradedIndex (newCell I k) = (univ, k) := by
  rcases k with _ | _ | _ | _ | _ | k
  all_goals first | omega | skip
  all_goals simp only [newCell, Scheme.appendFullCellScheme_gradedIndex_castSucc]
  all_goals exact Scheme.appendFullCellScheme_gradedIndex_last _ _

/-! ### The rows of the new cells -/

section Rows

variable {S : Scheme.{u} 5} {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin 5)), j) ≤ S.toCellScheme.gradedIndex d}

/-- A row read off the graded indices stays so after appending a cell. -/
theorem row_castSucc_eq {s : Fin S.card} {ρ : Finset (Fin 5) × ℕ → Label.{u}}
    (hs : ∀ t, S.rows.row s t = ρ (S.toCellScheme.gradedIndex t.1))
    (t : (S.appendFullCell j r h).toCellScheme.below
      ((S.appendFullCell j r h).toCellScheme.gradedIndex s.castSucc)) :
    (S.appendFullCell j r h).rows.row s.castSucc t =
      ρ ((S.appendFullCell j r h).toCellScheme.gradedIndex t.1) := by
  have ht : t.1 ≠ Fin.last _ := Scheme.ne_last_of_mem_below (by
    rw [Scheme.appendFullCell_toCellScheme, Scheme.appendFullCellScheme_gradedIndex_castSucc]
    exact h s) t.2
  refine (dite_eq_right (Fin.castSucc_ne_last s)).trans ?_
  have hmem : t.1.castPred ht ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex s) := by
    rw [CellScheme.mem_below, Scheme.gradedIndex_castPred t.1 ht,
      ← Scheme.appendFullCellScheme_gradedIndex_castSucc S j s]
    exact t.2
  refine (S.rows.row_congr (Fin.castPred_castSucc _) (t' := ⟨t.1.castPred ht, hmem⟩) rfl).trans ?_
  rw [hs, Scheme.gradedIndex_castPred t.1 ht]

end Rows

/-- The row of the cell appended by `addThinCell` reads the kinds by `thinRow j`. -/
theorem row_last_addThinCell {S : Scheme.{u} 5} {j : ℕ} {h : NoneAbove S j}
    (t : (addThinCell S j h).toCellScheme.below
      ((addThinCell S j h).toCellScheme.gradedIndex (Fin.last _))) :
    (addThinCell S j h).rows.row (Fin.last _) t =
      thinRow j (thinKind ((addThinCell S j h).toCellScheme.gradedIndex t.1)) :=
  Scheme.appendFullCell_row_last t

/-- A row read off the graded indices stays so after adding a new cell. -/
theorem row_castSucc_addThinCell {S : Scheme.{u} 5} {j : ℕ} {hS : NoneAbove S j}
    {s : Fin S.card} {ρ : Finset (Fin 5) × ℕ → Label.{u}}
    (hs : ∀ t, S.rows.row s t = ρ (S.toCellScheme.gradedIndex t.1))
    (t : (addThinCell S j hS).toCellScheme.below
      ((addThinCell S j hS).toCellScheme.gradedIndex s.castSucc)) :
    (addThinCell S j hS).rows.row s.castSucc t =
      ρ ((addThinCell S j hS).toCellScheme.gradedIndex t.1) :=
  row_castSucc_eq hs t

/-- **The row of the new cell at `(univ, k)` reads the kinds by `thinRow k`.** -/
theorem row_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I k))) :
    (thinScheme I).rows.row (newCell I k) t =
      thinRow k (thinKind ((thinScheme I).toCellScheme.gradedIndex t.1)) := by
  obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  · exact row_castSucc_addThinCell (ρ := fun X ↦ thinRow 1 (thinKind X))
      (row_castSucc_addThinCell (ρ := fun X ↦ thinRow 1 (thinKind X))
        (row_castSucc_addThinCell (ρ := fun X ↦ thinRow 1 (thinKind X))
          row_last_addThinCell)) t
  · exact row_castSucc_addThinCell (ρ := fun X ↦ thinRow 2 (thinKind X))
      (row_castSucc_addThinCell (ρ := fun X ↦ thinRow 2 (thinKind X)) row_last_addThinCell) t
  · exact row_castSucc_addThinCell (ρ := fun X ↦ thinRow 3 (thinKind X)) row_last_addThinCell t
  · exact row_last_addThinCell t

/-! ### The old cells -/

/-- The old cells of a scheme form a lower embedding into the scheme with a new cell. -/
theorem isLowerEmbedding_addThinCell (S : Scheme.{u} 5) (j : ℕ) (h : NoneAbove S j) :
    S.toCellScheme.IsLowerEmbedding (addThinCell S j h).toCellScheme Fin.castSucc :=
  Scheme.isLowerEmbedding_castSucc _ _ _

/-- The rows pull back along the old cells. -/
theorem comap_rows_addThinCell (S : Scheme.{u} 5) (j : ℕ) (h : NoneAbove S j) :
    (addThinCell S j h).rows.comap (isLowerEmbedding_addThinCell S j h) = S.rows :=
  Scheme.comap_rows_castSucc

variable (I) in
/-- **The old cells form a lower embedding** of the amalgam into the thin scheme. -/
theorem isLowerEmbedding_oldCell :
    I.amalgam.toCellScheme.IsLowerEmbedding (thinScheme I).toCellScheme (oldCell I) :=
  (isLowerEmbedding_addThinCell _ 4 (noneAbove_addThinCell _)).comp
    ((isLowerEmbedding_addThinCell _ 3 (noneAbove_addThinCell _)).comp
      ((isLowerEmbedding_addThinCell _ 2 (noneAbove_addThinCell _)).comp
        (isLowerEmbedding_addThinCell _ 1 (noneAbove_amalgam I))))

/-- **The rows of the thin scheme pull back to those of the amalgam** along the old cells. -/
theorem comap_rows_oldCell :
    (thinScheme I).rows.comap (isLowerEmbedding_oldCell I) = I.amalgam.rows := by
  -- Unfold the embedding of the old cells into the composite of the four one-cell embeddings.
  change (thinScheme I).rows.comap
    ((isLowerEmbedding_addThinCell _ 4 (noneAbove_addThinCell _)).comp
      ((isLowerEmbedding_addThinCell _ 3 (noneAbove_addThinCell _)).comp
        ((isLowerEmbedding_addThinCell _ 2 (noneAbove_addThinCell _)).comp
          (isLowerEmbedding_addThinCell _ 1 (noneAbove_amalgam I))))) = _
  rw [← CellScheme.Rows.comap_comap, comap_rows_addThinCell, ← CellScheme.Rows.comap_comap,
    comap_rows_addThinCell, ← CellScheme.Rows.comap_comap, comap_rows_addThinCell,
    comap_rows_addThinCell]
  all_goals first
    | exact isLowerEmbedding_addThinCell _ _ _
    | exact (isLowerEmbedding_addThinCell _ _ _).comp (isLowerEmbedding_addThinCell _ _ _)
    | exact (isLowerEmbedding_addThinCell _ _ _).comp
        ((isLowerEmbedding_addThinCell _ _ _).comp (isLowerEmbedding_addThinCell _ _ _))

/-- The old cells keep their scopes. -/
@[simp] theorem scope_oldCell (d : Fin I.amalgam.card) :
    (thinScheme I).toCellScheme.scope (oldCell I d) = I.amalgam.toCellScheme.scope d :=
  congrArg Prod.fst (gradedIndex_oldCell d)

/-- The old cells keep their grades. -/
@[simp] theorem grade_oldCell (d : Fin I.amalgam.card) :
    (thinScheme I).toCellScheme.grade (oldCell I d) = I.amalgam.toCellScheme.grade d :=
  congrArg Prod.snd (gradedIndex_oldCell d)

/-- The new cells have full scope. -/
theorem scope_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (thinScheme I).toCellScheme.scope (newCell I k) = univ :=
  congrArg Prod.fst (gradedIndex_newCell hk1 hk4)

/-- The new cell at `(univ, k)` has grade `k`. -/
theorem grade_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (thinScheme I).toCellScheme.grade (newCell I k) = k :=
  congrArg Prod.snd (gradedIndex_newCell hk1 hk4)

/-- **Every cell of the thin scheme is old or one of the four new cells.** -/
theorem cell_cases (z : Fin (thinScheme I).card) :
    (∃ d, z = oldCell I d) ∨ z = newCell I 1 ∨ z = newCell I 2 ∨ z = newCell I 3 ∨
      z = newCell I 4 := by
  -- The thin scheme has the cells of the amalgam and four more, so `Fin.lastCases` applies.
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

/-- A cell of scope other than the ground set is old. -/
theorem exists_eq_oldCell {z : Fin (thinScheme I).card}
    (hz : (thinScheme I).toCellScheme.scope z ≠ univ) : ∃ d, z = oldCell I d := by
  rcases cell_cases z with h | rfl | rfl | rfl | rfl
  · exact h
  all_goals exact absurd (scope_newCell (by omega) (by omega)) hz

/-- The only cell at `(univ, k)` is the new cell. -/
theorem eq_newCell {z : Fin (thinScheme I).card} {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hz : (thinScheme I).toCellScheme.gradedIndex z = (univ, k)) : z = newCell I k := by
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [gradedIndex_oldCell] at hz
    exact absurd (congrArg Prod.fst hz) (I.scope_ne_univ d)
  all_goals
    rw [gradedIndex_newCell (by omega) (by omega)] at hz
    obtain ⟨-, hk⟩ := Prod.mk.inj hz
    subst hk
    rfl

/-- Below a pair of scope other than the ground set, the cells are the old cells. -/
theorem image_oldCell_below {X : Finset (Fin 5) × ℕ} (hX : X.1 ≠ univ) :
    oldCell I '' I.amalgam.toCellScheme.below X = (thinScheme I).toCellScheme.below X := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [CellScheme.mem_below, gradedIndex_oldCell]
    exact hd
  · intro hz
    obtain ⟨d, rfl⟩ := exists_eq_oldCell (I := I) (z := z) fun h ↦
      hX (univ_subset_iff.mp (h ▸ hz.1))
    refine ⟨d, ?_, rfl⟩
    rw [CellScheme.mem_below, ← gradedIndex_oldCell]
    exact hz

/-- **Below a pair of scope other than the ground set, lawfulness in the thin scheme is
lawfulness in the amalgam**, along the old cells. -/
theorem isLawfulBelow_oldCell_iff {X : Finset (Fin 5) × ℕ} (hX : X.1 ≠ univ)
    {w : Fin (thinScheme I).card → Label.{u}} :
    (thinScheme I).rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (oldCell I d)) := by
  have h := Rows.isLawfulBelow_comap_iff (R := (thinScheme I).rows) (isLowerEmbedding_oldCell I)
    (image_oldCell_below hX) (r := fun z ↦ w z)
  rw [comap_rows_oldCell] at h
  exact h.symm

/-- A labelling equal to another below a pair is lawful there exactly when the other is. -/
theorem isLawfulBelow_congr {ι β : Type*} {D : CellScheme ι β} {R : D.Rows.{u}}
    {X : Finset β × ℕ} {w w' : ι → Label.{u}} (h : ∀ d ∈ D.below X, w d = w' d) :
    R.IsLawfulBelow X (fun d : D.below X ↦ w d) ↔
      R.IsLawfulBelow X (fun d : D.below X ↦ w' d) := by
  have : (fun d : D.below X ↦ w d) = fun d : D.below X ↦ w' d := funext fun d ↦ h d d.2
  rw [this]

/-! ### The two coatoms -/

/-- The first coatom `C = {0, 1, 2, 3}`. -/
abbrev coatomC : Finset (Fin 5) := univ.erase (Fin.last 4)

/-- The second coatom `D = {0, 1, 2, 4}`. -/
abbrev coatomD : Finset (Fin 5) := univ.erase (Fin.castSucc (Fin.last 3))

/-- The first coatom is the image of the first coatom embedding. -/
theorem coatomC_eq : coatomC = univ.map (Coatom.left 3) := Coatom.univ_map_left.symm

/-- The second coatom is the image of the second coatom embedding. -/
theorem coatomD_eq : coatomD = univ.map (Coatom.right 3) := Coatom.univ_map_right.symm

/-- **Every old cell below `(univ, k)` lies below one of the two coatoms at the grade `k`.** -/
theorem mem_below_coatom {d : Fin I.amalgam.card} {k : ℕ}
    (hd : I.amalgam.toCellScheme.grade d ≤ k) :
    d ∈ I.amalgam.toCellScheme.below (coatomC, k) ∨
      d ∈ I.amalgam.toCellScheme.below (coatomD, k) := by
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d) with h | h
  · exact .inl ⟨h, hd⟩
  · exact .inr ⟨h, hd⟩

/-- The scope of an old cell is not the ground set. -/
theorem scope_oldCell_ne (d : Fin I.amalgam.card) :
    (thinScheme I).toCellScheme.scope (oldCell I d) ≠ univ := by
  rw [scope_oldCell]; exact I.scope_ne_univ d

/-! ### Lawful labellings below the two coatoms -/

/-- The cells of `TL`: the nineteen cells of `SL` and the apex. -/
theorem cases_TL {α : Ordinal.{u}} (i : Fin (TL α).card) :
    i = Fin.last 19 ∨ ∃ d : Fin 19, i = Fin.castSucc d := by
  -- `TL` has the nineteen cells of `SL` and the apex, so `Fin.lastCases` applies.
  change Fin (19 + 1) at i
  induction i using Fin.lastCases with
  | last => exact .inl rfl
  | cast d => exact .inr ⟨d, rfl⟩

/-- The apex of `TL` has graded index `(univ, 4)`. -/
theorem gradedIndex_TL_last {α : Ordinal.{u}} :
    (TL α).toCellScheme.gradedIndex (Fin.last 19) = ((univ : Finset (Fin 4)), 4) :=
  Scheme.appendFullCellScheme_gradedIndex_last SL 4

/-- **Lawful labellings below a coatom whose type is `TL`**, read on `TL`: the labellings
`labelling A F G` with `G ≤ F` and `VisibilityReplaceFixedOfLT A G`. -/
theorem exists_labelling_of_comap_TL {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (TL α)) {k : ℕ} (hk : k ≤ 3)
    (p : Fin Am.card → Label.{u}) (hp : Am.rows.IsLawfulBelow (univ.map f, k) fun d ↦ p d) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ F ∧
      VisibilityReplaceFixedOfLT A G ∧ ∀ d ∈ Am.toCellScheme.below (univ.map f, k), ∃ c : Fin 19,
        Am.toCellScheme.gradedIndex d =
          Prod.map (Finset.map f) id (TwoFaceLiftCounterexample.cells.gradedIndex c) ∧
        p d = CaseSplitCounterexample.labelling A F G c := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (TL α).toScheme := congrArg StageType.toScheme he
  have hgen : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), k) (fun i ↦ x i) →
      ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ F ∧
        VisibilityReplaceFixedOfLT A G ∧
        ∀ i ∈ (Am.toScheme.comap f).toCellScheme.below ((univ : Finset (Fin 4)), k),
          ∃ c : Fin 19, (Am.toScheme.comap f).toCellScheme.gradedIndex i =
            TwoFaceLiftCounterexample.cells.gradedIndex c ∧
            x i = CaseSplitCounterexample.labelling A F G c := by
    rw [heq]
    intro x hx
    have hx' := (isLawfulBelow_TL_iff (α := α) (w := x) (fun h ↦ by
      have := h.2; simp only at this; omega)).mp hx
    obtain ⟨A, F, G, hA, hF, hG, hGF, hc, hAF⟩ :=
      (TwoFaceLiftExistsCounterexample.isLawfulBelow_iff (x := fun e ↦ x (Fin.castSucc e))).mp hx'
    refine ⟨A, F, G, hA, hF, hG, hGF, hc, fun i hi ↦ ?_⟩
    rcases cases_TL (α := α) i with rfl | ⟨c, rfl⟩
    · exfalso
      have h2 := hi.2
      rw [gradedIndex_TL_last] at h2
      simp only at h2
      omega
    · refine ⟨c, gradedIndex_TL_castSucc c, hAF c ?_⟩
      rw [CellScheme.mem_below, ← gradedIndex_TL_castSucc (α := α) c]
      exact hi
  obtain ⟨A, F, G, hA, hF, hG, hGF, hc, hall⟩ := hgen (fun i ↦ p (Am.toScheme.cellMap f i))
    ((Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f _ p).mpr hp)
  refine ⟨A, F, G, hA, hF, hG, hGF, hc, fun d hd ↦ ?_⟩
  have hd' : d ∈ Am.toScheme.cellMap f '' (Am.toScheme.comap f).toCellScheme.below
      ((univ : Finset (Fin 4)), k) := by
    rw [Am.toScheme.image_cellMap_below f]; exact hd
  obtain ⟨i, hi, rfl⟩ := hd'
  obtain ⟨c, hgi, hpc⟩ := hall i hi
  exact ⟨c, by rw [← Am.toScheme.map_comap_gradedIndex f i, hgi], hpc⟩

variable (hIL : I.left = TL α) (hIR : I.right = CaseSplitCounterexample.T5 α)
include hIL in
/-- **Lawful labellings below `(C, 3)` in the thin scheme**: `thinLabel A ⊥ F G ⊥` with the
constraints of `TL`. -/
theorem exists_of_isLawfulBelow_left {w : Fin (thinScheme I).card → Label.{u}}
    (hw : (thinScheme I).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ F ∧
      VisibilityReplaceFixedOfLT A G ∧ ∀ z ∈ (thinScheme I).toCellScheme.below (coatomC, 3),
        w z = thinLabel A ⊥ F G ⊥ ((thinScheme I).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomC_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGF, hc, hall⟩ :=
    exists_labelling_of_comap_TL (hIL ▸ I.restrictFace_left) le_rfl
      (fun d ↦ w (oldCell I d)) hw'
  refine ⟨A, F, G, hA, hF, hG, hGF, hc, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ := (image_oldCell_below (I := I) (X := (coatomC, 3)) (by decide)).symm ▸ hz
  rw [coatomC_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, thinLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_left]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

include hIR in
/-- **Lawful labellings below `(D, 3)` in the thin scheme**: `thinLabel ⊥ A F G ⊥` with the
constraints of `T5`. -/
theorem exists_of_isLawfulBelow_right {w : Fin (thinScheme I).card → Label.{u}}
    (hw : (thinScheme I).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧
      G ≤ F ∧ ∀ z ∈ (thinScheme I).toCellScheme.below (coatomD, 3),
        w z = thinLabel ⊥ A F G ⊥ ((thinScheme I).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomD_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hall⟩ :=
    CaseSplitCounterexample.exists_labelling_of_comap (hIR ▸ I.restrictFace_right) le_rfl
      (fun d ↦ w (oldCell I d)) hw'
  refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ := (image_oldCell_below (I := I) (X := (coatomD, 3)) (by decide)).symm ▸ hz
  rw [coatomD_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, thinLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_right]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

/-! ### Extension by bottom above a grade -/

/-- **Extension by bottom above a grade.**  A labelling lawful below `(B, k)`, replaced by `⊥` at
every cell of grade above `k`, is lawful below `(B, K)` for every `K`: the new cells of the lower
set carry `⊥`, their targets are `⊥`, and they are available to every cell. -/
theorem isLawfulBelow_extendAbove {ι β : Type*} {D : CellScheme ι β} {R : D.Rows.{u}}
    {B : Finset β} {k K : ℕ} {w : ι → Label.{u}} (hw : R.IsLawfulBelow (B, k) fun d ↦ w d) :
    R.IsLawfulBelow (B, K) fun d ↦ if D.grade d ≤ k then w d else ⊥ := by
  obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  refine (Rows.isLawfulBelow_iff_forall (w := fun e ↦ if D.grade e ≤ k then w e else ⊥)).mpr
    ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · split_ifs with h
    · exact ho d ⟨hd.1, h⟩
    · exact isSelfVisible_bot _
  · by_cases h : D.grade s ≤ k
    · have he : (fun d : D.below (D.gradedIndex s) ↦
          min (if D.grade d ≤ k then w d else ⊥) (if D.grade s ≤ k then w s else ⊥)) =
          fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s) := by
        funext d
        have hd : D.grade d.1 ≤ k := d.2.2.trans h
        rw [ite_eq_left hd, ite_eq_left h]
      rw [he]
      exact hl s ⟨hs.1, h⟩
    · have he : (fun d : D.below (D.gradedIndex s) ↦
          min (if D.grade d ≤ k then w d else ⊥) (if D.grade s ≤ k then w s else ⊥)) =
          fun _ ↦ ⊥ := by
        funext d
        rw [ite_eq_right h, min_bot_right]
      rw [he]
      exact TransformsTo.bot _ _
  · by_cases h : D.grade t ≤ k
    · obtain ⟨u, hu, hle⟩ := ha s t ⟨ht.1, h⟩ hst hg
      have hu' : D.grade u ≤ k := (congrArg Prod.snd hu).trans_le h
      refine ⟨u, hu, ?_⟩
      rw [ite_eq_left (hg ▸ h), ite_eq_left hu']
      exact hle
    · refine ⟨t, rfl, ?_⟩
      rw [ite_eq_right (hg ▸ h)]
      exact bot_le

/-! ### Kinds and grades -/

/-- The kind of a graded index is at most one more than its grade. -/
theorem thinKind_le (X : Finset (Fin 5) × ℕ) : (thinKind X : ℕ) ≤ X.2 + 1 := by
  by_cases h : thinKind X = 0
  · rw [h]; exact Nat.zero_le _
  · rw [snd_eq_kindGrade h]
    generalize thinKind X = c
    fin_cases c <;> decide

/-- At a graded index of grade `k`, the thin labelling is at most the parameter of the grade `k`,
when `A_C ≤ A_D`. -/
theorem thinLabel_le {AC AD F G Ω : Label.{u}} (hle : AC ≤ AD) {X : Finset (Fin 5) × ℕ}
    {k : ℕ} (hX : X.2 = k) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    thinLabel AC AD F G Ω X ≤ kindLabel AC AD F G Ω (thinKind ((univ : Finset (Fin 5)), k)) := by
  unfold thinLabel
  by_cases h : thinKind X = 0
  · rw [h]; exact bot_le
  have hg := snd_eq_kindGrade h
  rw [hX] at hg
  obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  all_goals
    simp only [thinKind_univ_one, thinKind_univ_two, thinKind_univ_three, thinKind_univ_four]
    generalize thinKind X = c at h hg
    fin_cases c <;> first | exact absurd hg (by decide) | exact (h rfl).elim | exact le_rfl | skip
  exact hle

/-- A cell below the new cell at `(univ, k)` has grade at most `k`. -/
theorem grade_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I k))) :
    (thinScheme I).toCellScheme.grade t.1 ≤ k := by
  have h : (thinScheme I).toCellScheme.gradedIndex t.1 ≤ ((univ : Finset (Fin 5)), k) :=
    gradedIndex_newCell hk1 hk4 ▸ t.2
  exact h.2

/-- The kind of a cell below the new cell at `(univ, k)` is at most `k + 1`. -/
theorem thinKind_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I k))) :
    (thinKind ((thinScheme I).toCellScheme.gradedIndex t.1) : ℕ) ≤ k + 1 :=
  (thinKind_le _).trans (Nat.succ_le_succ (grade_le_of_mem_below_newCell hk1 hk4 t))

/-- An old cell below `(univ, k)` lies below one of the two coatoms at the grade `k`. -/
theorem mem_below_coatom_of_ne {z : Fin (thinScheme I).card} {k : ℕ}
    (hz : z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), k))
    (hne : (thinScheme I).toCellScheme.scope z ≠ univ) :
    z ∈ (thinScheme I).toCellScheme.below (coatomC, k) ∨
      z ∈ (thinScheme I).toCellScheme.below (coatomD, k) := by
  obtain ⟨d, rfl⟩ := exists_eq_oldCell hne
  have hg : I.amalgam.toCellScheme.grade d ≤ k := by rw [← grade_oldCell]; exact hz.2
  rcases mem_below_coatom hg with h | h
  · left
    rw [CellScheme.mem_below, gradedIndex_oldCell]; exact h
  · right
    rw [CellScheme.mem_below, gradedIndex_oldCell]; exact h

/-- A cell of full scope below `(univ, k)` is one of the new cells, of grade at most `k`. -/
theorem eq_newCell_of_scope {z : Fin (thinScheme I).card}
    (hz : (thinScheme I).toCellScheme.scope z = univ) :
    ∃ j, 1 ≤ j ∧ j ≤ 4 ∧ z = newCell I j := by
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · exact absurd hz (scope_oldCell_ne d)
  · exact ⟨1, le_rfl, by omega, rfl⟩
  · exact ⟨2, by omega, by omega, rfl⟩
  · exact ⟨3, by omega, by omega, rfl⟩
  · exact ⟨4, by omega, le_rfl, rfl⟩

/-! ### Sufficiency: the thin labellings are lawful below `(univ, 3)` -/

variable (I) in
/-- The **thin labelling** of the cells of the thin scheme, read off their graded indices. -/
noncomputable def thinLabelling (AC AD F G Ω : Label.{u}) (z : Fin (thinScheme I).card) :
    Label.{u} :=
  thinLabel AC AD F G Ω ((thinScheme I).toCellScheme.gradedIndex z)

/-- The row of the new cell at `(univ, k)`, as a function. -/
theorem row_newCell_eq {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (thinScheme I).rows.row (newCell I k) =
      fun t ↦ thinRow k (thinKind ((thinScheme I).toCellScheme.gradedIndex t.1)) :=
  funext (row_newCell hk1 hk4)

/-- The thin labelling at the new cell at `(univ, k)`. -/
theorem thinLabel_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (AC AD F G Ω : Label.{u}) :
    thinLabelling I AC AD F G Ω (newCell I k) =
      kindLabel AC AD F G Ω (thinKind ((univ : Finset (Fin 5)), k)) := by
  rw [thinLabelling, gradedIndex_newCell hk1 hk4]; rfl

include hIL hIR in
/-- **The thin labellings are lawful below the coatoms** at the grade `3`: on the old cells they
are the labellings `tripleLabelling A_C F A_D F G`. -/
theorem isLawfulBelow_coatom_thinLabel {AC AD F G Ω : Label.{u}} (h : IsThinLawfulBelow AC AD F G) :
    (thinScheme I).rows.IsLawfulBelow (coatomC, 3)
        (fun z ↦ thinLabelling I AC AD F G Ω z) ∧
      (thinScheme I).rows.IsLawfulBelow (coatomD, 3)
        (fun z ↦ thinLabelling I AC AD F G Ω z) := by
  have hCD := isLawfulBelow_tripleLabelling (I := I) hIL hIR h.svAC h.svF h.svAD h.svF h.svG
    h.G_le_F h.visibilityReplaceFixed h.G_le_AD h.G_le_F
  have key (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      thinLabelling I AC AD F G Ω (oldCell I d) =
        tripleLabelling AC F AD F G (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [thinLabelling, gradedIndex_oldCell]
    exact thinLabel_eq_tripleLabelling (I.scope_ne_univ d)
      (show I.amalgam.toCellScheme.grade d ≠ 4 by omega) _ _ _ _ _
  constructor
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomC, 3))
      fun d hd ↦ (key d hd.2).symm).mp hCD.1
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomD, 3))
      fun d hd ↦ (key d hd.2).symm).mp hCD.2

include hIL hIR in
/-- **Sufficiency**: the thin labelling of parameters satisfying `IsThinLawfulBelow` is lawful below
`(univ, 3)`. -/
theorem isLawfulBelow_thinLabel {AC AD F G Ω : Label.{u}} (h : IsThinLawfulBelow AC AD F G) :
    (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      (fun z ↦ thinLabelling I AC AD F G Ω z) := by
  obtain ⟨hC, hD⟩ := isLawfulBelow_coatom_thinLabel hIL hIR (Ω := Ω) h
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hD
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hne : (thinScheme I).toCellScheme.scope d = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hd.2
      rw [grade_newCell hj1 hj4, thinLabel_newCell hj1 hj4]
      obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact h.svAD
      · exact h.svF
      · exact h.svG
    · exact (mem_below_coatom_of_ne hd hne).elim (hoC d) (hoD d)
  · rcases cell_cases s with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
    · exact (mem_below_coatom_of_ne hs (scope_oldCell_ne d)).elim (hlC _) (hlD _)
    · rw [row_newCell_eq le_rfl (by omega), thinLabel_newCell le_rfl (by omega)]
      exact transformsTo_rowOne _ (fun t ↦ thinKind ((thinScheme I).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell le_rfl (by omega))
        (thinKind_le_of_mem_below_newCell le_rfl (by omega)) h.svAC h.svAD h.le_AD
    · rw [row_newCell_eq (by omega) (by omega), thinLabel_newCell (by omega) (by omega)]
      exact transformsTo_rowTwo _ (fun t ↦ thinKind ((thinScheme I).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (thinKind_le_of_mem_below_newCell (by omega) (by omega)) h.svAC h.svAD h.svF h.le_AD
        h.noCollision
    · rw [row_newCell_eq (by omega) (by omega), thinLabel_newCell (by omega) (by omega)]
      exact transformsTo_rowThree _
        (fun t ↦ thinKind ((thinScheme I).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (thinKind_le_of_mem_below_newCell (by omega) (by omega)) h.svG h.visibilityReplaceFixed
        h.G_le_AD h.G_le_F
    · have h4 : (thinScheme I).toCellScheme.gradedIndex (newCell I 4) ≤
          ((univ : Finset (Fin 5)), 3) := hs
      rw [gradedIndex_newCell (by omega) le_rfl] at h4
      exact absurd h4.2 (by decide)
  · by_cases hne : (thinScheme I).toCellScheme.scope t = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      refine ⟨newCell I j, rfl, ?_⟩
      rw [thinLabel_newCell hj1 hj4]
      exact thinLabel_le h.le_AD (hg.trans (grade_newCell hj1 hj4)) hj1 hj4
    · exact (mem_below_coatom_of_ne ht hne).elim (haC s t · hst hg) (haD s t · hst hg)

/-! ### Necessity: the lawful labellings below `(univ, 3)` are thin -/

/-- The thin labelling does not read `A_D` at a graded index of another kind. -/
theorem thinLabel_congr_two {X : Finset (Fin 5) × ℕ} (hX : thinKind X ≠ 2)
    (AC AD AD' F G Ω : Label.{u}) : thinLabel AC AD F G Ω X = thinLabel AC AD' F G Ω X := by
  unfold thinLabel
  generalize thinKind X = c at hX
  fin_cases c <;> first | rfl | exact (hX rfl).elim

/-- The thin labelling does not read `A_C` at a graded index of another kind. -/
theorem thinLabel_congr_one {X : Finset (Fin 5) × ℕ} (hX : thinKind X ≠ 1)
    (AC AC' AD F G Ω : Label.{u}) : thinLabel AC AD F G Ω X = thinLabel AC' AD F G Ω X := by
  unfold thinLabel
  generalize thinKind X = c at hX
  fin_cases c <;> first | rfl | exact (hX rfl).elim

/-- A cell below `(C, k)` misses the point `4`. -/
theorem four_notMem_of_mem_below {z : Fin (thinScheme I).card} {k : ℕ}
    (hz : z ∈ (thinScheme I).toCellScheme.below (coatomC, k)) :
    (4 : Fin 5) ∉ ((thinScheme I).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.last 4) univ) (hz.1 h)

/-- A cell below `(D, k)` misses the point `3`. -/
theorem three_notMem_of_mem_below {z : Fin (thinScheme I).card} {k : ℕ}
    (hz : z ∈ (thinScheme I).toCellScheme.below (coatomD, k)) :
    (3 : Fin 5) ∉ ((thinScheme I).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.castSucc (Fin.last 3)) univ) (hz.1 h)

/-- The old cell at a graded index of the first coatom. -/
theorem exists_oldCell_left (hIL : I.left = TL α) (c : Fin 19) :
    ∃ d : Fin I.amalgam.card, I.amalgam.toCellScheme.gradedIndex d =
      Prod.map (Finset.map (Coatom.left 3)) id (TwoFaceLiftCounterexample.cells.gradedIndex c) :=
  exists_cell_TL (hIL ▸ I.restrictFace_left) c

/-- The old cell at a graded index of the second coatom. -/
theorem exists_oldCell_right (hIR : I.right = CaseSplitCounterexample.T5 α) (c : Fin 19) :
    ∃ d : Fin I.amalgam.card, I.amalgam.toCellScheme.gradedIndex d =
      Prod.map (Finset.map (Coatom.right 3)) id (TwoFaceLiftCounterexample.cells.gradedIndex c) :=
  CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) c

/-- An old cell is below a pair when its graded index is. -/
theorem oldCell_mem_below {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ}
    (h : I.amalgam.toCellScheme.gradedIndex d ≤ X) :
    oldCell I d ∈ (thinScheme I).toCellScheme.below X := by
  rw [CellScheme.mem_below, gradedIndex_oldCell]; exact h

/-- A new cell is below `(univ, k)` for `j ≤ k`. -/
theorem newCell_mem_below {j k : ℕ} (hj1 : 1 ≤ j) (hj4 : j ≤ 4) (hjk : j ≤ k) :
    newCell I j ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), k) := by
  rw [CellScheme.mem_below, gradedIndex_newCell hj1 hj4]; exact ⟨subset_rfl, hjk⟩

/-- The new cell at `(univ, k)` is below itself. -/
theorem newCell_mem_below_self {k : ℕ} :
    newCell I k ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I k)) :=
  (thinScheme I).toCellScheme.mem_below_gradedIndex _

/-- An old cell below the new cell at `(univ, k)`, of grade at most `k`. -/
theorem oldCell_mem_below_newCell {d : Fin I.amalgam.card} {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hd : I.amalgam.toCellScheme.grade d ≤ k) :
    oldCell I d ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I k)) := by
  rw [gradedIndex_newCell hk1 hk4]
  exact oldCell_mem_below ⟨subset_univ _, hd⟩

include hIL hIR in
/-- **Necessity**: every labelling lawful below `(univ, 3)` is a thin labelling, of parameters
satisfying `IsThinLawfulBelow`.  On each coatom it is a labelling of `TL` or of `T5`; locality and
availability at the new cells identify `A_D`, `F` (on both coatoms) and `G` with their labels, and
give `A_C ≤ A_D`; and the collision lemma at the new cell at `(univ, 2)` gives the exclusion of
collisions. -/
theorem exists_of_isLawfulBelow_three {w : Fin (thinScheme I).card → Label.{u}}
    (hw : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ w z) :
    ∃ AC AD F G : Label.{u}, IsThinLawfulBelow AC AD F G ∧
      ∀ z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        w z = thinLabelling I AC AD F G ⊥ z := by
  -- Step 1: below each coatom, `w` is a labelling of `TL` (parameters `A_C`, `F_C`, `G_C`) or of
  -- `T5` (parameters `A_D`, `F_D`, `G_D`).
  have hC : (thinScheme I).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z :=
    hw.mono (X := (coatomC, 3)) ⟨subset_univ _, le_rfl⟩
  have hD : (thinScheme I).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z :=
    hw.mono (X := (coatomD, 3)) ⟨subset_univ _, le_rfl⟩
  obtain ⟨AC, FC, GC, hAC, hFC, hGC, hGFC, hcC, hC'⟩ := exists_of_isLawfulBelow_left hIL hC
  obtain ⟨AD, FD, GD, hAD, hFD, hGD, hGAD, hGFD, hD'⟩ := exists_of_isLawfulBelow_right hIR hD
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  -- Step 2: the old cells used, one of each live kind, and their labels.
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hw₁ : w (oldCell I d₁) = AC := by
    rw [hC' _ (oldCell_mem_below (by rw [hd₁]; decide)), gradedIndex_oldCell, hd₁]; rfl
  have hwsC : w (oldCell I sC) = FC := by
    rw [hC' _ (oldCell_mem_below (by rw [hsC]; decide)), gradedIndex_oldCell, hsC]; rfl
  have hwgC : w (oldCell I gE) = GC := by
    rw [hC' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hwgD : w (oldCell I gE) = GD := by
    rw [hD' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hw₂ : w (oldCell I d₂) = AD := by
    rw [hD' _ (oldCell_mem_below (by rw [hd₂]; decide)), gradedIndex_oldCell, hd₂]; rfl
  have hwsD : w (oldCell I sD) = FD := by
    rw [hD' _ (oldCell_mem_below (by rw [hsD]; decide)), gradedIndex_oldCell, hsD]; rfl
  have hGCD : GC = GD := hwgC.symm.trans hwgD
  -- Step 3: locality (`hle`) and availability (`hge`) at the new cell at `(univ, k)` compare its
  -- label with that of an old cell of grade `k`; they identify the labels of the new cells with
  -- `A_D`, `F_C = F_D` and `G`, and give `A_C ≤ A_D`.
  have hrow {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      (thinScheme I).rows.row (newCell I k) ⟨oldCell I d, oldCell_mem_below_newCell hk1 hk4 hd⟩ =
        thinRow k (thinKind (I.amalgam.toCellScheme.gradedIndex d)) := by
    rw [row_newCell hk1 hk4, gradedIndex_oldCell]
  have hrowself {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
      (thinScheme I).rows.row (newCell I k) ⟨newCell I k, newCell_mem_below_self⟩ =
        thinRow k (thinKind ((univ : Finset (Fin 5)), k)) := by
    rw [row_newCell hk1 hk4, gradedIndex_newCell hk1 hk4]
  have hle {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k)
      (hr : thinRow k (thinKind ((univ : Finset (Fin 5)), k)) ≤
        thinRow k (thinKind (I.amalgam.toCellScheme.gradedIndex d))) :
      w (newCell I k) ≤ w (oldCell I d) := by
    have := (hl _ (newCell_mem_below hk1 (by omega) hk3)).le_of_le
      (d := ⟨newCell I k, newCell_mem_below_self⟩)
      (d' := ⟨oldCell I d, oldCell_mem_below_newCell hk1 (by omega) hd.le⟩)
      (by rw [hrowself hk1 (by omega), hrow hk1 (by omega) hd.le]; exact hr)
      (show (thinScheme I).toCellScheme.grade (oldCell I d) ≤
          (thinScheme I).toCellScheme.grade (newCell I k) by
        rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have hge {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k) : w (oldCell I d) ≤ w (newCell I k) := by
    obtain ⟨u, hu, hle⟩ := ha (oldCell I d) (newCell I k) (newCell_mem_below hk1 (by omega) hk3)
      (by rw [scope_newCell hk1 (by omega)]; exact subset_univ _)
      (by rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    rwa [eq_newCell hk1 (by omega) (hu.trans (gradedIndex_newCell hk1 (by omega)))] at hle
  have hn₁ : w (newCell I 1) = AD := by
    rw [← hw₂]
    exact le_antisymm (hle le_rfl (by omega) (congrArg Prod.snd hd₂) (by rw [hd₂]; rfl))
      (hge le_rfl (by omega) (congrArg Prod.snd hd₂))
  have hn₂C : w (newCell I 2) = FC := by
    rw [← hwsC]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsC) (by rw [hsC]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsC))
  have hn₂D : w (newCell I 2) = FD := by
    rw [← hwsD]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsD) (by rw [hsD]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsD))
  have hn₃ : w (newCell I 3) = GC := by
    rw [← hwgC]
    exact le_antisymm (hle (by omega) le_rfl (congrArg Prod.snd hgE) (by rw [hgE]; rfl))
      (hge (by omega) le_rfl (congrArg Prod.snd hgE))
  have hACAD : AC ≤ AD := hw₁ ▸ hn₁ ▸ hge le_rfl (by omega) (congrArg Prod.snd hd₁)
  have hFCD : FC = FD := hn₂C.symm.trans hn₂D
  -- Step 4: no collision, by the collision lemma at the new cell at `(univ, 2)`.
  have hnc : AC = AD → AC < FC → IsSelfVisible 2 AC := by
    intro heq hlt
    by_contra hev
    have hg₁' : I.amalgam.toCellScheme.grade d₁ = 1 := congrArg Prod.snd hd₁
    have hg₂' : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
    have hg₁ : I.amalgam.toCellScheme.grade d₁ ≤ 2 := by omega
    have hg₂ : I.amalgam.toCellScheme.grade d₂ ≤ 2 := by omega
    have := eq_of_transformsTo_collision (hl _ (newCell_mem_below (by omega) (by omega) (by omega)))
      (d₁ := ⟨oldCell I d₁, oldCell_mem_below_newCell (by omega) (by omega) hg₁⟩)
      (d₂ := ⟨oldCell I d₂, oldCell_mem_below_newCell (by omega) (by omega) hg₂⟩)
      (z := ⟨newCell I 2, newCell_mem_below_self⟩)
      ((grade_oldCell d₁).trans hg₁') ((grade_oldCell d₂).trans hg₂')
      (grade_newCell (by omega) (by omega))
      (by rw [hrow (by omega) (by omega) hg₁, hd₁]; exact isSelfVisible_gridPoint 1 0)
      (by rw [hrow (by omega) (by omega) hg₂, hd₂]; exact isSelfVisible_gridPoint 1 1)
      (e := AC) (by simp only; rw [hw₁, hn₂C, min_eq_left hlt.le])
      (by simp only; rw [hw₂, hn₂C, ← heq, min_eq_left hlt.le]) hev
      (by simp only; rw [hn₂C, min_self]; exact hlt)
    rw [hrow (by omega) (by omega) hg₁, hrow (by omega) (by omega) hg₂, hd₁, hd₂] at this
    exact absurd this (gridPoint_lt_gridPoint.mpr (by omega)).ne
  -- Step 5: `w` is the thin labelling of these parameters: at the new cells by step 3, and at
  -- the old cells by step 1 (the kinds merge `F_C`, `F_D` into `F` and `G_C`, `G_D` into `G`).
  refine ⟨AC, AD, FC, GC, ⟨hAC, hAD, hFC, hGC, hACAD, hGFC, hGCD ▸ hGAD, hcC, hnc⟩,
    fun z hz ↦ ?_⟩
  by_cases hne : (thinScheme I).toCellScheme.scope z = univ
  · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
    have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hz.2
    rw [thinLabel_newCell hj1 hj4]
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · exact hn₁
    · exact hn₂C
    · exact hn₃
  · rcases mem_below_coatom_of_ne hz hne with h | h
    · rw [hC' z h, thinLabelling]
      exact thinLabel_congr_two (thinKind_ne_two (four_notMem_of_mem_below h)) _ _ _ _ _ _
    · rw [hD' z h, thinLabelling, ← hFCD, ← hGCD]
      exact thinLabel_congr_one (thinKind_ne_one (three_notMem_of_mem_below h)) _ _ _ _ _ _

end VaughtConjecture.ThinCompletion
