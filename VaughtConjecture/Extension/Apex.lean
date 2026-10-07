/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CodedSection
import VaughtConjecture.Extension.CoatomScheme
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Stage.Legal

/-!
# Adding the apex: a full cell of full grade above a scheme complete below it

Roadmap, Layer 3 (the coatom extension construction: the apex of [Kni26, Corollary 4.3.22], a
cell of full scope and full grade carrying the largest label); semantic contract, items 3–4.

**Appending a cell of full scope.**  For a scheme `S` on `n` points, a grade `j`, and a labelling
`r` of the cells of `S` and one more cell, `S.appendFullCell j r h` is the scheme with the cells
of `S`, in their order, followed by one cell of scope `univ` and grade `j` whose row is `r`; the
hypothesis `h` says that no cell of `S` lies above `(univ, j)`, so the new cell lies below no old
cell and the old rows are kept.  The old cells form a lower embedding along `Fin.castSucc`
(`Scheme.isLowerEmbedding_castSucc`), along which the rows pull back to those of `S`
(`Scheme.comap_rows_castSucc`); below a pair not above `(univ, j)` lawfulness is lawfulness in `S`
(`Scheme.isLawfulBelow_appendFullCell_iff`), and a labelling is lawful when it is lawful on the old
cells and its locality at the new cell holds (`Scheme.isLawful_appendFullCell`).

**Restrictions along proper faces** (`StageType.restrictFace_eq_of_strictMono`): a strictly
monotone lower embedding of the cells of `s` into those of `t`, keeping scopes, rows, and labels,
whose image contains every cell of `t` visible through `f`, identifies the faces of `s` and `t`
along `f`, including definedness.  This is the uniqueness of the enumeration of the cells visible
through `f` (`Scheme.cellMap_eq_of_strictMono`), in the form
`Scheme.cellMap_eq_of_strictMono_of_mem_range`.

**Legality below the full grade** (`Scheme.IsLegalBelowFullGrade`).  A scheme on `n` points is
legal below the full grade when it is well formed, its rows are coded, consistent, and bountiful,
every cell has grade below `n`, and every graded face of grade below `n` is the graded index of a
cell: every law of a legal scheme, with completeness only below the full grade.  This one predicate
is the hypothesis for adding the apex and the legality field of a completion below the full grade
(`VaughtConjecture.Extension.CompletionBelowFullGrade`).

**Adding the apex** (`StageType.addApex`).  Let `t` be a stage type on `n` points, `0 < n`, whose
scheme is legal below the full grade.  Append one cell of full scope and full grade `n`, labelled
with the formal top.  The hypothesis `0 < n` makes `(univ, n)` a graded face (grades are positive),
so that the new cell has a graded face as its graded index.  Its row is the coded copy of the
labels of `t`, their image under a block coding (`CellScheme.Rows.IsLawful.exists_blockEncode`),
with the code of the formal top at the new cell: it is coded and lawful, and the block decoding
transforms it back to the labels.  The result is legal (`StageType.isLegal_addApex`):

* consistency: the old rows are those of `t`, and the new row is lawful;
* bountifulness: below the full grade the lifts are those of `t`, and a lift to a pair of full
  grade `n` starts at the full face itself, where it is trivial
  (`CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst`);
* completeness: the only graded face of grade `n` is `(univ, n)`, the graded index of the new
  cell.

The new cell is the apex: its graded index is `(univ, n)` and its label `⊤` is the largest
(`StageType.exists_apex_addApex`); it is the only cell of full grade
(`StageType.eq_of_grade_addApex`), and the faces along embeddings onto proper subsets are those of
`t` (`StageType.restrictFace_addApex`).  Adding the apex uses no hypothesis on the stage: the apex
label `⊤` occurs at every stage.  (The stage enters before it: the completion
(`CompletionBelowFullGrade.completion`) truncates a completion below the full grade of a seed to a
stage that is zero or a limit, reducing its labels to the stage, and then adds the apex; see
`VaughtConjecture.Extension.CompletionBelowFullGrade`.)

A bottom row at the apex would not do: a cell whose row is bottom at itself has bottom label in
every lawful section (`CellScheme.Rows.IsLawful.eq_bot_of_row_self_eq_bot`), which is why the row
of the apex is the coded copy of the labels.

## Placement

`Scheme.appendFullCell` and its laws belong in `VaughtConjecture.Stage.Scheme`, and
`Scheme.mem_range_comp_cellMap_iff`, `Scheme.cellMap_eq_of_strictMono_of_mem_range`, and
`Scheme.comap_eq_of_strictMono` there too, beside `Scheme.cellMap_eq_of_strictMono`;
`StageType.restrictFace_eq_of_strictMono` belongs in `VaughtConjecture.Stage.Basic`, beside
`StageType.restrictFace_trans`; `Scheme.IsLegalBelowFullGrade` belongs in
`VaughtConjecture.Stage.Legal`, beside `Scheme.IsLegal`.  They are stated here so that those files
are unchanged.

## References

The apex is the cell `Ξ` of full scope and full grade with `q(Ξ) = max ran q` of
[Kni26, Corollary 4.3.22]; completeness is [Kni26, Definition 2.5.15] and bountifulness
[Kni26, Definition 2.5.14]; the row of the apex is coded, as in the range normalization of
[Kni26, Lemma 2.5.13].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Unique enumerations of visible cells -/

namespace Scheme

variable {n m : ℕ} {S T : Scheme.{u} n} {φ : Fin S.card → Fin T.card} (f : Fin m ↪ Fin n)

/-- The cells of `T` visible through `f` are the images under `φ` of the cells of `S` visible
through `f`, when `φ` keeps scopes and its image contains every cell of `T` visible through `f`. -/
theorem mem_range_comp_cellMap_iff
    (hscope : ∀ d, T.toCellScheme.scope (φ d) = S.toCellScheme.scope d)
    (hvis : ∀ z, (T.toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f → z ∈ Set.range φ)
    (z : Fin T.card) : z ∈ Set.range (φ ∘ S.cellMap f) ↔ z ∈ T.visibleCells f := by
  rw [mem_visibleCells]
  constructor
  · rintro ⟨i, rfl⟩
    rw [Function.comp_apply, hscope]
    exact mem_visibleCells.mp (S.cellMap_mem f i)
  · intro hz
    obtain ⟨d, rfl⟩ := hvis z hz
    rw [hscope] at hz
    obtain ⟨i, rfl⟩ : d ∈ Set.range (S.cellMap f) := by
      rw [range_cellMap]
      exact mem_visibleCells.mpr hz
    exact ⟨i, rfl⟩

/-- **Enumerations of visible cells along an embedding of cells.**  If `φ` is strictly monotone,
keeps scopes, and its image contains every cell of `T` visible through `f`, then the cell map of
`T` along `f` is `φ` after the cell map of `S` along `f`. -/
theorem cellMap_eq_of_strictMono_of_mem_range (hmono : StrictMono φ)
    (hscope : ∀ d, T.toCellScheme.scope (φ d) = S.toCellScheme.scope d)
    (hvis : ∀ z, (T.toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f → z ∈ Set.range φ)
    {i : Fin (S.comap f).card} {k : Fin (T.comap f).card} (hik : (i : ℕ) = k) :
    T.cellMap f k = φ (S.cellMap f i) :=
  (T.cellMap_eq_of_strictMono f (hmono.comp (S.cellMap f).strictMono)
    (mem_range_comp_cellMap_iff f hscope hvis) hik).symm

/-- **Faces along an embedding of cells.**  If `φ` is a strictly monotone lower embedding of the
cells of `S` into those of `T` keeping scopes and rows, the two schemes have the same ground set
and faces, and the image of `φ` contains every cell of `T` visible through `f`, then the
restrictions of `S` and `T` along `f` are equal. -/
theorem comap_eq_of_strictMono (hmono : StrictMono φ)
    (hφ : S.toCellScheme.IsLowerEmbedding T.toCellScheme φ)
    (hscope : ∀ d, T.toCellScheme.scope (φ d) = S.toCellScheme.scope d)
    (hrows : T.rows.comap hφ = S.rows) (hground : T.toCellScheme.ground = S.toCellScheme.ground)
    (hfaces : T.toCellScheme.faces = S.toCellScheme.faces)
    (hvis : ∀ z, (T.toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f → z ∈ Set.range φ) :
    T.comap f = S.comap f := by
  have key {k : Fin (T.comap f).card} {i : Fin (S.comap f).card} (h : (k : ℕ) = i) :
      T.cellMap f k = φ (S.cellMap f i) :=
    cellMap_eq_of_strictMono_of_mem_range f hmono hscope hvis h.symm
  have hcard : (T.comap f).card = (S.comap f).card :=
    T.card_visibleCells_eq_of_strictMono f (hmono.comp (S.cellMap f).strictMono)
      (mem_range_comp_cellMap_iff f hscope hvis)
  refine Scheme.ext hcard ?_ ?_ (fun k i h ↦ ?_) (fun k i h ↦ ?_) (fun s s' t t' hs ht ↦ ?_)
  · rw [comap_ground, comap_ground, hground]
  · ext C
    rw [mem_comap_faces, mem_comap_faces, hfaces]
  · rw [comap_scope, comap_scope, key h, hscope]
  · rw [comap_grade, comap_grade, key h, hφ.grade_eq]
  · rw [comap_row, comap_row]
    have hrow := congrArg (fun R : S.toCellScheme.Rows ↦
      R.row (S.cellMap f s') ⟨S.cellMap f t'.1,
        ((S.isLowerEmbedding_comap f).le_iff t'.1 s').mpr t'.2⟩) hrows
    simp only [CellScheme.Rows.comap_row] at hrow
    rw [← hrow]
    exact T.rows.row_congr (key hs) (key ht)

end Scheme

/-! ### Faces of stage types along an embedding of cells -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} {s t : StageType.{u} α n} {φ : Fin s.card → Fin t.card}

/-- **Faces of stage types along an embedding of cells.**  If `φ` is a strictly monotone lower
embedding of the cells of `s` into those of `t` keeping scopes, rows, and labels, the two types
have the same ground set and faces, and the image of `φ` contains every cell of `t` visible
through `f`, then the faces of `s` and `t` along `f` agree, including definedness. -/
theorem restrictFace_eq_of_strictMono (f : Fin m ↪ Fin n) (hmono : StrictMono φ)
    (hφ : s.toCellScheme.IsLowerEmbedding t.toCellScheme φ)
    (hscope : ∀ d, t.toCellScheme.scope (φ d) = s.toCellScheme.scope d)
    (hrows : t.rows.comap hφ = s.rows) (hground : t.toCellScheme.ground = s.toCellScheme.ground)
    (hfaces : t.toCellScheme.faces = s.toCellScheme.faces)
    (hlabel : ∀ d, t.label (φ d) = s.label d)
    (hvis : ∀ z, (t.toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f → z ∈ Set.range φ) :
    restrictFace f t = restrictFace f s := by
  by_cases hf : univ.map f ∈ s.toCellScheme.faces
  · have hf' : univ.map f ∈ t.toCellScheme.faces := hfaces ▸ hf
    rw [restrictFace_of_mem t f hf', restrictFace_of_mem s f hf]
    refine congrArg some (ext (Scheme.comap_eq_of_strictMono f hmono hφ hscope hrows hground
      hfaces hvis) fun k i h ↦ ?_)
    rw [comap_label, comap_label,
      Scheme.cellMap_eq_of_strictMono_of_mem_range f hmono hscope hvis h.symm, hlabel]
  · rw [restrictFace_of_notMem s f hf, restrictFace_of_notMem t f (hfaces ▸ hf)]

end StageType


/-! ### Appending a cell of full scope -/

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n) (j : ℕ)

/-- The cell scheme of `S` with one more cell, last, of scope `univ` and grade `j`. -/
def appendFullCellScheme : CellScheme (Fin (S.card + 1)) (Fin n) where
  ground := S.toCellScheme.ground
  faces := S.toCellScheme.faces
  scope := Fin.snoc (α := fun _ ↦ Finset (Fin n)) S.toCellScheme.scope univ
  grade := Fin.snoc (α := fun _ ↦ ℕ) S.toCellScheme.grade j

/-- An old cell keeps its scope. -/
@[simp] theorem appendFullCellScheme_scope_castSucc (d : Fin S.card) :
    (S.appendFullCellScheme j).scope d.castSucc = S.toCellScheme.scope d :=
  Fin.snoc_castSucc (α := fun _ ↦ Finset (Fin n)) ..

/-- The new cell has full scope. -/
@[simp] theorem appendFullCellScheme_scope_last :
    (S.appendFullCellScheme j).scope (Fin.last _) = univ :=
  Fin.snoc_last (α := fun _ ↦ Finset (Fin n)) ..

/-- An old cell keeps its grade. -/
@[simp] theorem appendFullCellScheme_grade_castSucc (d : Fin S.card) :
    (S.appendFullCellScheme j).grade d.castSucc = S.toCellScheme.grade d :=
  Fin.snoc_castSucc (α := fun _ ↦ ℕ) ..

/-- The new cell has grade `j`. -/
@[simp] theorem appendFullCellScheme_grade_last :
    (S.appendFullCellScheme j).grade (Fin.last _) = j :=
  Fin.snoc_last (α := fun _ ↦ ℕ) ..

/-- An old cell keeps its graded index. -/
@[simp] theorem appendFullCellScheme_gradedIndex_castSucc (d : Fin S.card) :
    (S.appendFullCellScheme j).gradedIndex d.castSucc = S.toCellScheme.gradedIndex d := by
  simp [CellScheme.gradedIndex]

/-- The new cell has graded index `(univ, j)`. -/
@[simp] theorem appendFullCellScheme_gradedIndex_last :
    (S.appendFullCellScheme j).gradedIndex (Fin.last _) = (univ, j) := by
  simp [CellScheme.gradedIndex]

variable {S j}

/-- The graded index of a cell other than the new one, read in `S`. -/
theorem gradedIndex_castPred (d : Fin (S.card + 1)) (hd : d ≠ Fin.last _) :
    S.toCellScheme.gradedIndex (d.castPred hd) = (S.appendFullCellScheme j).gradedIndex d := by
  rw [← appendFullCellScheme_gradedIndex_castSucc, Fin.castSucc_castPred]

/-- If no old cell lies above `(univ, j)`, the new cell lies below no pair that is not above
`(univ, j)`. -/
theorem ne_last_of_mem_below {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), j) ≤ X)
    {d : Fin (S.card + 1)} (hd : d ∈ (S.appendFullCellScheme j).below X) : d ≠ Fin.last _ := by
  rintro rfl
  rw [CellScheme.mem_below, appendFullCellScheme_gradedIndex_last] at hd
  exact hX hd

variable (S j) in
/-- **Appending a cell of full scope**: the scheme with the cells of `S`, in their order, followed
by one cell of scope `univ` and grade `j` whose row is `r`.  The hypothesis says that no cell of
`S` lies above `(univ, j)`, so that the old rows, which are those of `S`, see only old cells.

It is an `abbrev`, not a `def`: its number of cells must unfold reducibly to `S.card + 1`, so that
`Fin.castSucc`, `Fin.last`, and `Fin.lastCases` apply to its cells in rewriting and in `simp`
(with a `def`, `Fin (S.appendFullCell j r h).card` and `Fin (S.card + 1)` do not match at reducible
transparency, and the laws below fail to rewrite). -/
abbrev appendFullCell (r : Fin (S.card + 1) → Label.{u})
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n where
  card := S.card + 1
  toCellScheme := S.appendFullCellScheme j
  rows := ⟨fun s t ↦ if hs : s = Fin.last _ then r t.1 else
    S.rows.row (s.castPred hs) ⟨t.1.castPred (ne_last_of_mem_below
      (by rw [← gradedIndex_castPred s hs]; exact h _) t.2),
      by rw [CellScheme.mem_below, gradedIndex_castPred, gradedIndex_castPred]; exact t.2⟩⟩

variable {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

/-- The cell scheme after appending a cell. -/
theorem appendFullCell_toCellScheme :
    (S.appendFullCell j r h).toCellScheme = S.appendFullCellScheme j := rfl

/-- The row of the new cell is `r`. -/
theorem appendFullCell_row_last
    (t : (S.appendFullCellScheme j).below ((S.appendFullCellScheme j).gradedIndex (Fin.last _))) :
    (S.appendFullCell j r h).rows.row (Fin.last _) t = r t.1 :=
  dite_eq_left rfl

/-- The row of the new cell is `r`, as a function. -/
theorem appendFullCell_row_last_eq :
    (S.appendFullCell j r h).rows.row (Fin.last _) = fun t ↦ r t.1 :=
  funext appendFullCell_row_last

variable (j r h) in
/-- **The old cells form a lower embedding** along `Fin.castSucc`. -/
theorem isLowerEmbedding_castSucc :
    S.toCellScheme.IsLowerEmbedding (S.appendFullCell j r h).toCellScheme Fin.castSucc where
  injective := Fin.castSucc_injective _
  grade_eq d := appendFullCellScheme_grade_castSucc S j d
  le_iff s t := by
    simp only [appendFullCellScheme_gradedIndex_castSucc]
  mem_range t d hd := by
    have hd' : d ≠ Fin.last _ := ne_last_of_mem_below
      (by rw [appendFullCell_toCellScheme, appendFullCellScheme_gradedIndex_castSucc]; exact h t)
      hd
    exact ⟨d.castPred hd', Fin.castSucc_castPred _ _⟩

/-- **The rows pull back to those of `S`** along the old cells. -/
theorem comap_rows_castSucc :
    (S.appendFullCell j r h).rows.comap (isLowerEmbedding_castSucc j r h) = S.rows := by
  ext s t
  rw [CellScheme.Rows.comap_row]
  refine (dite_eq_right (Fin.castSucc_ne_last s)).trans ?_
  exact S.rows.row_congr (Fin.castPred_castSucc (Fin.castSucc_ne_last _)) (t' := t)
    (Fin.castPred_castSucc (Fin.castSucc_ne_last _))

/-- The old cells below a pair that is not above `(univ, j)` are all its cells. -/
theorem image_castSucc_below {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), j) ≤ X) :
    Fin.castSucc '' S.toCellScheme.below X = (S.appendFullCell j r h).toCellScheme.below X := by
  ext d
  constructor
  · rintro ⟨d, hd, rfl⟩
    rwa [appendFullCell_toCellScheme, CellScheme.mem_below,
      appendFullCellScheme_gradedIndex_castSucc]
  · intro hd
    have hd' := ne_last_of_mem_below hX hd
    refine ⟨d.castPred hd', ?_, Fin.castSucc_castPred _ _⟩
    rw [CellScheme.mem_below, gradedIndex_castPred]
    exact hd

/-- **Lawfulness below a pair that is not above `(univ, j)`** is lawfulness in `S`. -/
theorem isLawfulBelow_appendFullCell_iff {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), j) ≤ X) {v : Fin (S.card + 1) → Label.{u}} :
    (S.appendFullCell j r h).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castSucc d)) := by
  have := CellScheme.Rows.isLawfulBelow_comap_iff (R := (S.appendFullCell j r h).rows)
    (isLowerEmbedding_castSucc j r h) (image_castSucc_below hX) (r := fun d ↦ v d)
  rw [comap_rows_castSucc] at this
  exact this.symm

/-- **Lawful labellings after appending a cell.**  A labelling `v` is lawful when it is lawful on
the old cells, its value at the new cell is self-visible at `j`, the row `r` of the new cell
transforms to `v` capped at that value, and every old cell of grade `j` has a value at most it. -/
theorem isLawful_appendFullCell {v : Fin (S.card + 1) → Label.{u}}
    (hv : S.rows.IsLawful (v ∘ Fin.castSucc)) (hlast : IsSelfVisible j (v (Fin.last _)))
    (hloc : TransformsTo (S.appendFullCellScheme j).grade r fun d ↦ min (v d) (v (Fin.last _)))
    (havail : ∀ d, S.toCellScheme.grade d = j → v d.castSucc ≤ v (Fin.last _)) :
    (S.appendFullCell j r h).rows.IsLawful v where
  orderly d := by
    induction d using Fin.lastCases with
    | last =>
      rw [appendFullCell_toCellScheme, appendFullCellScheme_grade_last]
      exact hlast
    | cast d =>
      rw [appendFullCell_toCellScheme, appendFullCellScheme_grade_castSucc]
      exact hv.orderly d
  locality s := by
    induction s using Fin.lastCases with
    | last =>
      rw [appendFullCell_row_last_eq]
      exact hloc.reindex Subtype.val
    | cast s =>
      have hX : ¬ ((univ : Finset (Fin n)), j) ≤
          (S.appendFullCell j r h).toCellScheme.gradedIndex s.castSucc := by
        rw [appendFullCell_toCellScheme, appendFullCellScheme_gradedIndex_castSucc]
        exact h s
      have hb := (isLawfulBelow_appendFullCell_iff (r := r) (h := h) hX).mpr
        (hv.isLawfulBelow _)
      exact (CellScheme.Rows.isLawfulBelow_iff_forall.mp hb).2.1 _
        (CellScheme.mem_below_gradedIndex _ _)
  availability s t hst hg := by
    induction t using Fin.lastCases with
    | last =>
      refine ⟨Fin.last _, rfl, ?_⟩
      induction s using Fin.lastCases with
      | last => exact le_rfl
      | cast s =>
        refine havail s ?_
        simpa using hg
    | cast t =>
      induction s using Fin.lastCases with
      | last =>
        refine absurd ?_ (h t)
        simp only [appendFullCellScheme_scope_last,
          appendFullCellScheme_scope_castSucc, appendFullCellScheme_grade_last,
          appendFullCellScheme_grade_castSucc] at hst hg
        exact ⟨hst, hg.le⟩
      | cast s =>
        simp only [appendFullCellScheme_scope_castSucc,
          appendFullCellScheme_grade_castSucc] at hst hg
        obtain ⟨u, hu, hle⟩ := hv.availability s t hst hg
        refine ⟨u.castSucc, ?_, hle⟩
        simpa using hu

/-- **Consistency after appending a cell**: the old rows are those of `S`, and the new row is
lawful. -/
theorem isConsistent_appendFullCell (hS : S.rows.IsConsistent)
    (hr : (S.appendFullCell j r h).rows.IsLawful r) :
    (S.appendFullCell j r h).rows.IsConsistent := by
  intro s
  induction s using Fin.lastCases with
  | last =>
    rw [appendFullCell_row_last_eq]
    exact hr.isLawfulBelow _
  | cast s =>
    have hφ := isLowerEmbedding_castSucc j r h
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [comap_rows_castSucc]
    convert hS s using 1
    funext t
    exact congrArg (fun R : S.toCellScheme.Rows ↦ R.row s t) comap_rows_castSucc

/-- **Appending a cell keeps well-formedness** when `(univ, j)` is a graded face. -/
theorem isWellFormed_appendFullCell (hS : S.IsWellFormed) (hj : 0 < j) (hjn : j ≤ n) :
    (S.appendFullCell j r h).IsWellFormed where
  ground_eq := hS.ground_eq
  isWellFormed := by
    refine ⟨inferInstance, hS.isWellFormed.isPlan, fun d ↦ ?_⟩
    induction d using Fin.lastCases with
    | last =>
      rw [appendFullCellScheme_gradedIndex_last]
      exact ⟨hS.univ_mem_faces, hj, by simpa using hjn⟩
    | cast d =>
      rw [appendFullCellScheme_gradedIndex_castSucc]
      exact hS.isWellFormed.gradedIndex_mem d

/-- **Appending a cell keeps coding** when the new row is coded. -/
theorem isCoded_appendFullCell (hS : S.IsCoded)
    (hr : ∀ d, r d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (S.appendFullCell j r h).IsCoded := by
  intro s t
  induction s using Fin.lastCases with
  | last => exact (appendFullCell_row_last t).trans_lt (hr _)
  | cast s => exact (dite_eq_right (Fin.castSucc_ne_last s)).trans_lt (hS _ _)

end Scheme


/-! ### A cell of full grade -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), n) ≤ S.toCellScheme.gradedIndex d}

/-- The grade of a graded face is at most the number of points. -/
private theorem snd_le_of_mem_gradedFaces {X : Finset (Fin n) × ℕ}
    (hX : X ∈ S.toCellScheme.gradedFaces) : X.2 ≤ n :=
  hX.2.2.trans ((card_le_univ _).trans_eq (Fintype.card_fin n))

/-- A graded face of full grade `n` is `(univ, n)`. -/
private theorem eq_of_mem_gradedFaces_of_snd_eq {X : Finset (Fin n) × ℕ}
    (hX : X ∈ S.toCellScheme.gradedFaces) (hXn : X.2 = n) : X = (univ, n) := by
  refine Prod.ext (eq_univ_of_card _ ?_) hXn
  exact le_antisymm ((card_le_univ _).trans_eq rfl) (hXn ▸ hX.2.2 |>.trans_eq' (by simp))

/-- A scheme on `n` points is **legal below the full grade**: every law of a legal scheme
(`Scheme.IsLegal`), with completeness only below the full grade `n`, and every cell of grade below
`n`.  Appending a cell of full scope and full grade makes it legal (`StageType.isLegal_addApex`).
-/
structure IsLegalBelowFullGrade (S : Scheme.{u} n) : Prop where
  /-- The scheme is well formed. -/
  isWellFormed : S.IsWellFormed
  /-- The rows are coded: every row value lies below `ω ^ 2`. -/
  isCoded : S.IsCoded
  /-- The rows are consistent [Kni26, Definition 2.5.12]. -/
  isConsistent : S.rows.IsConsistent
  /-- The rows are bountiful [Kni26, Definition 2.5.14], between any two graded faces. -/
  isBountiful : S.rows.IsBountiful
  /-- Every cell has grade below `n`. -/
  grade_lt (d : Fin S.card) : S.toCellScheme.grade d < n
  /-- Every graded face of grade below `n` is the graded index of a cell: completeness
  [Kni26, Definition 2.5.15] below the full grade. -/
  exists_gradedIndex_eq :
    ∀ X ∈ S.toCellScheme.gradedFaces, X.2 < n → ∃ d, S.toCellScheme.gradedIndex d = X

/-- No cell of a scheme legal below the full grade lies above `(univ, n)`. -/
theorem IsLegalBelowFullGrade.not_le (hS : S.IsLegalBelowFullGrade) (d : Fin S.card) :
    ¬ ((univ : Finset (Fin n)), n) ≤ S.toCellScheme.gradedIndex d :=
  fun hle ↦ (hS.grade_lt d).not_ge hle.2

/-- After appending a cell of grade `n` to a scheme legal below the full grade, every cell has
grade at most `n`. -/
theorem IsLegalBelowFullGrade.grade_appendFullCellScheme_le (hS : S.IsLegalBelowFullGrade)
    (d : Fin (S.card + 1)) : (S.appendFullCellScheme n).grade d ≤ n := by
  induction d using Fin.lastCases with
  | last => rw [appendFullCellScheme_grade_last]
  | cast d => rw [appendFullCellScheme_grade_castSucc]; exact (hS.grade_lt d).le

/-- **A cell of full grade keeps bountifulness.**  Below the full grade the lifts are those of
`S`; a lift to a pair of full grade starts at the full face itself, where it is trivial. -/
theorem isBountiful_appendFullCell (hB : S.rows.IsBountiful) :
    (S.appendFullCell n r h).rows.IsBountiful := by
  refine CellScheme.Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY hXY ↦ ?_
  have hXS : X ∈ S.toCellScheme.gradedFaces := hX
  rcases (snd_le_of_mem_gradedFaces hXS).lt_or_eq with hXn | hXn
  · -- Below the full grade: the lift of `S`, transported along the old cells.
    have hY' : (Y.1, X.2) ∈ S.toCellScheme.gradedFaces :=
      ⟨hY.1, hX.2.1, hX.2.2.trans (card_le_card hXY.1)⟩
    have hnot : ∀ Z : Finset (Fin n) × ℕ, Z.2 < n → ¬ ((univ : Finset (Fin n)), n) ≤ Z :=
      fun Z hZ hle ↦ hZ.not_ge hle.2
    refine CellScheme.Rows.CappedLift.of_comap (isLowerEmbedding_castSucc n r h)
      (image_castSucc_below (hnot X hXn)) (image_castSucc_below (X := (Y.1, X.2)) (hnot _ hXn))
      le_rfl (X' := X) (Y' := (Y.1, X.2)) (h' := ⟨hXY.1, le_rfl⟩) ?_
    rw [comap_rows_castSucc]
    exact hB hXS hY' _
  · -- At the full grade: `X` is the full face, and so is the face of `Y`.
    obtain rfl := eq_of_mem_gradedFaces_of_snd_eq hXS hXn
    obtain ⟨Y1, Y2⟩ := Y
    obtain rfl : Y1 = univ := eq_univ_of_forall fun x ↦ hXY.1 (mem_univ x)
    exact CellScheme.Rows.cappedLift_refl _

/-- **A cell of full grade completes a scheme complete below the full grade.** -/
theorem isComplete_appendFullCell
    (hc : ∀ X ∈ S.toCellScheme.gradedFaces, X.2 < n → ∃ d, S.toCellScheme.gradedIndex d = X) :
    (S.appendFullCell n r h).toCellScheme.IsComplete := by
  intro X hX
  have hXS : X ∈ S.toCellScheme.gradedFaces := hX
  rcases (snd_le_of_mem_gradedFaces hXS).lt_or_eq with hXn | hXn
  · obtain ⟨d, hd⟩ := hc X hXS hXn
    exact ⟨d.castSucc, (appendFullCellScheme_gradedIndex_castSucc S n d).trans hd⟩
  · exact ⟨Fin.last _, (appendFullCellScheme_gradedIndex_last S n).trans
      (eq_of_mem_gradedFaces_of_snd_eq hXS hXn).symm⟩

end Scheme

/-! ### Rows read off the graded indices -/

namespace Scheme

section Rows

variable {n : ℕ} {S : Scheme.{u} n} {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

/-- A row read off the graded indices stays so after appending a cell. -/
theorem row_castSucc_eq {s : Fin S.card} {ρ : Finset (Fin n) × ℕ → Label.{u}}
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

end Scheme

/-! ### Adding the apex -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} {t : StageType.{u} α n}

/-- The codes of the apex row: a finite set of labels containing every label of `t`, for which the
coded copy of the labels of `t` is lawful. -/
noncomputable def apexCodes (ht : t.IsLegalBelowFullGrade) : Finset Label.{u} :=
  (t.isLawful.exists_blockEncode (K := n) fun d ↦ (ht.grade_lt d).le).choose

variable (ht : t.IsLegalBelowFullGrade)

/-- Every label of `t` is among the codes of the apex row. -/
theorem label_mem_apexCodes (d : Fin t.card) : t.label d ∈ apexCodes ht :=
  (t.isLawful.exists_blockEncode (K := n) fun d ↦ (ht.grade_lt d).le).choose_spec.1 d

/-- The coded copy of the labels of `t` is lawful. -/
theorem isLawful_blockEncode_apexCodes :
    t.rows.IsLawful (blockEncode (apexCodes ht) n ∘ t.label) :=
  (t.isLawful.exists_blockEncode (K := n) fun d ↦ (ht.grade_lt d).le).choose_spec.2

/-- The **row of the apex**: the coded copy of the labels of `t`, and the code of the formal top at
the apex itself. -/
noncomputable def apexRow : Fin (t.card + 1) → Label.{u} :=
  Fin.snoc (α := fun _ ↦ Label.{u}) (blockEncode (apexCodes ht) n ∘ t.label)
    (blockEncode (apexCodes ht) n ⊤)

/-- The labels after adding the apex: the labels of `t`, and the formal top at the apex. -/
def apexLabel : Fin (t.card + 1) → Label.{u} := Fin.snoc (α := fun _ ↦ Label.{u}) t.label ⊤

/-- The apex row at an old cell. -/
@[simp] theorem apexRow_castSucc (d : Fin t.card) :
    apexRow ht d.castSucc = blockEncode (apexCodes ht) n (t.label d) :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

/-- The apex row at the apex. -/
@[simp] theorem apexRow_last : apexRow ht (Fin.last _) = blockEncode (apexCodes ht) n ⊤ :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

/-- The label of an old cell after adding the apex. -/
@[simp] theorem apexLabel_castSucc (d : Fin t.card) : apexLabel (t := t) d.castSucc = t.label d :=
  Fin.snoc_castSucc (α := fun _ ↦ Label.{u}) ..

/-- The label of the apex. -/
@[simp] theorem apexLabel_last : apexLabel (t := t) (Fin.last _) = ⊤ :=
  Fin.snoc_last (α := fun _ ↦ Label.{u}) ..

/-- **The apex row is lawful**: it is the coded copy of the labels of `t`, and the code of the
formal top lies above every code. -/
theorem isLawful_apexRow :
    (t.toScheme.appendFullCell n (apexRow ht) ht.not_le).rows.IsLawful (apexRow ht) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert isLawful_blockEncode_apexCodes ht using 1
    funext d
    exact apexRow_castSucc ht d
  · rw [apexRow_last]
    exact isSelfVisible_blockEncode_top le_rfl
  · convert TransformsTo.refl _ (apexRow ht) using 1
    funext d
    refine min_eq_left ?_
    rw [apexRow_last]
    induction d using Fin.lastCases with
    | last => rw [apexRow_last]
    | cast d => rw [apexRow_castSucc]; exact blockEncode_le_blockEncode_top _

/-- **The labels after adding the apex are lawful**: the decoding transforms the apex row back to
the labels, with the formal top at the apex. -/
theorem isLawful_apexLabel :
    (t.toScheme.appendFullCell n (apexRow ht) ht.not_le).rows.IsLawful (apexLabel (t := t)) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful using 1
    funext d
    exact apexLabel_castSucc d
  · rw [apexLabel_last]
    exact isSelfVisible_top n
  · refine ⟨fun _ ↦ ⊤, blockDecode (apexCodes ht), isWitness_blockDecode, fun d ↦ ?_⟩
    beta_reduce
    rw [apexLabel_last, min_top_right, min_top_right]
    induction d using Fin.lastCases with
    | last => rw [apexLabel_last, apexRow_last, blockDecode_blockEncode_top]
    | cast d =>
      rw [apexLabel_castSucc, apexRow_castSucc, blockDecode_blockEncode (label_mem_apexCodes ht d)]

variable (hn : 0 < n)

/-- **Adding the apex** to a stage type legal below the full grade: one cell of full scope and full
grade `n` appended last, labelled with the formal top, whose row is the coded copy of the labels
(`StageType.apexRow`).  The hypothesis `0 < n` makes `(univ, n)` a graded face (grades are
positive), so the new cell has a graded face as its graded index. -/
noncomputable def addApex : StageType.{u} α n where
  toScheme := t.toScheme.appendFullCell n (apexRow ht) ht.not_le
  label := apexLabel
  isWellFormed := Scheme.isWellFormed_appendFullCell t.isWellFormed hn le_rfl
  isCoded := Scheme.isCoded_appendFullCell t.isCoded fun d ↦ by
    induction d using Fin.lastCases with
    | last => rw [apexRow_last]; exact blockEncode_lt _
    | cast d => rw [apexRow_castSucc]; exact blockEncode_lt _
  isLawful := isLawful_apexLabel ht
  atStage d := by
    induction d using Fin.lastCases with
    | last => rw [apexLabel_last]; exact atStage_top
    | cast d => rw [apexLabel_castSucc]; exact t.atStage d

/-- The label of an old cell after adding the apex is its label in `t`. -/
@[simp] theorem addApex_label_castSucc (d : Fin t.card) :
    (t.addApex ht hn).label d.castSucc = t.label d :=
  apexLabel_castSucc d

/-- The label of the apex is the formal top. -/
@[simp] theorem addApex_label_last : (t.addApex ht hn).label (Fin.last _) = ⊤ :=
  apexLabel_last

/-- The apex has full scope. -/
theorem addApex_scope_last : (t.addApex ht hn).toCellScheme.scope (Fin.last _) = univ :=
  Scheme.appendFullCellScheme_scope_last _ _

/-- **Adding the apex gives a legal stage type**: consistency, bountifulness, and completeness at
the full grade.  It uses no hypothesis on the stage. -/
theorem isLegal_addApex : (t.addApex ht hn).IsLegal :=
  isLegal_iff.mpr ⟨Scheme.isConsistent_appendFullCell ht.isConsistent (isLawful_apexRow ht),
    Scheme.isBountiful_appendFullCell (h := ht.not_le) ht.isBountiful,
    Scheme.isComplete_appendFullCell (h := ht.not_le) ht.exists_gradedIndex_eq⟩

/-- **The apex**: the new cell has full scope and full grade `n`, and carries the largest label,
the formal top. -/
theorem exists_apex_addApex : ∃ d, (t.addApex ht hn).toCellScheme.gradedIndex d = (univ, n) ∧
    ∀ e, (t.addApex ht hn).label e ≤ (t.addApex ht hn).label d :=
  ⟨Fin.last _, Scheme.appendFullCellScheme_gradedIndex_last _ _,
    fun _ ↦ by rw [addApex_label_last]; exact le_top⟩

/-- The cells of the type with the apex added that are visible through a proper face are old. -/
theorem mem_range_castSucc_of_addApex {k : ℕ} (f : Fin k ↪ Fin n) (hf : univ.map f ≠ univ)
    (z : Fin (t.addApex ht hn).card)
    (hz : ((t.addApex ht hn).toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f) :
    z ∈ Set.range (Fin.castSucc : Fin t.card → Fin (t.card + 1)) := by
  induction z using Fin.lastCases with
  | last =>
    refine absurd (eq_univ_of_forall fun x ↦ ?_) hf
    obtain ⟨y, rfl⟩ : x ∈ Set.range f :=
      hz (mem_coe.mpr ((addApex_scope_last ht hn).symm ▸ mem_univ x))
    exact mem_map_of_mem _ (mem_univ y)
  | cast z => exact ⟨z, rfl⟩

/-- **The proper faces after adding the apex are those of `t`**: along an embedding whose image is
not the whole ground set, the face maps of `t.addApex ht hn` and of `t` agree, including
definedness. -/
theorem restrictFace_addApex (f : Fin m ↪ Fin n) (hf : univ.map f ≠ univ) :
    restrictFace f (t.addApex ht hn) = restrictFace f t := by
  refine restrictFace_eq_of_strictMono (t := t.addApex ht hn) (s := t) f
    (φ := (Fin.castSucc : Fin t.card → Fin (t.card + 1))) Fin.strictMono_castSucc
    (Scheme.isLowerEmbedding_castSucc n (apexRow ht) ht.not_le)
    (Scheme.appendFullCellScheme_scope_castSucc _ _) (Scheme.comap_rows_castSucc (h := ht.not_le))
    rfl rfl
    (addApex_label_castSucc ht hn) (mem_range_castSucc_of_addApex ht hn f hf)

/-- **After adding the apex, the apex is the only cell of full grade.** -/
theorem eq_of_grade_addApex {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
    (hn : 0 < n) {i : Fin (t.addApex ht hn).card}
    (hi : (t.addApex ht hn).toCellScheme.grade i = n) :
    i = Fin.last _ := by
  -- `t.addApex` has the cells of `t` and the apex, so `Fin.lastCases` applies.
  change Fin (t.card + 1) at i
  induction i using Fin.lastCases with
  | last => rfl
  | cast d =>
    exfalso
    -- The cell scheme of `t.addApex` is `appendFullCellScheme`.
    change (Scheme.appendFullCellScheme t.toScheme n).grade d.castSucc = n at hi
    rw [Scheme.appendFullCellScheme_grade_castSucc] at hi
    exact (ht.grade_lt d).ne hi

/-! ### Adding the apex to `⊥` labels -/

/-- **The labels of a type with the apex added to `⊥` labels**: `⊤` at the apex and `⊥`
elsewhere. -/
theorem label_addApex {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
    (hn : 0 < n) (hbot : ∀ d, t.label d = ⊥) (i : Fin (t.addApex ht hn).card) :
    (t.addApex ht hn).label i = if (t.addApex ht hn).toCellScheme.grade i = n then ⊤ else ⊥ := by
  -- `t.addApex` has the cells of `t` and the apex, so `Fin.lastCases` applies.
  change Fin (t.card + 1) at i
  induction i using Fin.lastCases with
  | last =>
    have h : (t.addApex ht hn).toCellScheme.grade (Fin.last _) = n :=
      Scheme.appendFullCellScheme_grade_last _ _
    rw [StageType.addApex_label_last, ite_eq_left h]
  | cast d =>
    have h : (t.addApex ht hn).toCellScheme.grade d.castSucc ≠ n := by
      -- The cell scheme of `t.addApex` is `appendFullCellScheme`.
      change (Scheme.appendFullCellScheme t.toScheme n).grade d.castSucc ≠ n
      rw [Scheme.appendFullCellScheme_grade_castSucc]
      exact (ht.grade_lt d).ne
    rw [StageType.addApex_label_castSucc, hbot, ite_eq_right h]

/-- **The row of the apex of a type with `⊥` labels**: `⊥` exactly at the cells other than the
apex, which are the cells of grade below `n`. -/
theorem row_addApex {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
    (hn : 0 < n) (hbot : ∀ d, t.label d = ⊥) (s : Fin (t.addApex ht hn).card)
    (hs : (t.addApex ht hn).toCellScheme.grade s = n)
    (i : (t.addApex ht hn).toCellScheme.below ((t.addApex ht hn).toCellScheme.gradedIndex s)) :
    ((t.addApex ht hn).rows.row s i = ⊥ ↔ (t.addApex ht hn).toCellScheme.grade i ≠ n) := by
  -- `t.addApex` has the cells of `t` and the apex, so `Fin.lastCases` applies.
  change Fin (t.card + 1) at s
  induction s using Fin.lastCases with
  | cast d =>
    exfalso
    -- The cell scheme of `t.addApex` is `appendFullCellScheme`.
    change (Scheme.appendFullCellScheme t.toScheme n).grade d.castSucc = n at hs
    rw [Scheme.appendFullCellScheme_grade_castSucc] at hs
    exact (ht.grade_lt d).ne hs
  | last =>
    rw [show (t.addApex ht hn).rows.row (Fin.last _) i = StageType.apexRow ht i.1 from
      Scheme.appendFullCell_row_last (h := ht.not_le) i]
    obtain ⟨i, hi⟩ := i
    -- As for `s`: the cells of `t` and the apex.
    change Fin (t.card + 1) at i
    induction i using Fin.lastCases with
    | last =>
      rw [StageType.apexRow_last, blockEncode_top]
      exact ⟨fun h ↦ absurd h WithBot.coe_ne_bot,
        fun h ↦ absurd (Scheme.appendFullCellScheme_grade_last _ _) h⟩
    | cast d =>
      rw [StageType.apexRow_castSucc, hbot, blockEncode_bot]
      simp only [true_iff]
      -- The cell scheme of `t.addApex` is `appendFullCellScheme`.
      change (Scheme.appendFullCellScheme t.toScheme n).grade d.castSucc ≠ n
      rw [Scheme.appendFullCellScheme_grade_castSucc]
      exact (ht.grade_lt d).ne

end StageType

end VaughtConjecture
