/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ActualCoverConverse

/-!
# Global row anchors

Roadmap, Layer 4 (cover-hollowness and the anchor definition of hollowness); semantic contract,
item 8.  A research file: a native global-cell rendering of the printed inequality of the anchor
at infinity of [Kni26, Definition 5.4.2, p. 56], its cells quantified over the whole realization
as in the printed definition, compared at the same bound with the row anchor
`Realization.IsRowAnchor` (`VaughtConjecture.Continuation.ActualCoverTransport`), whose cells are
those of the actual rooted covers of one occurrence.

**The same cell** (`Realization.IsSameCell x a z e`).  The printed definition quantifies over
elements `Θ`, `Σ` of the domains of all the types of the model, with the value `𝔐(Θ)` allotted by
the model as a whole ([Kni26, Definition 3.2.5 and Lemma 3.2.6, p. 31]), and asks that the anchor
`⚓∞` lie in the domain of the semantics `ℰ(Θ)`.  The cells of the types here are positions
`Fin card`, with the codes of the cells forgotten (roadmap, `IMPLEMENTATION.md`, "Manuscript
concordance", note 7), so the identity of a cell across types is a relation: `a` and `e` are the
same cell when some occurrence `w` is a face of both `x` and `z` and `a` and `e` are the cells at
the position of one cell of `w` on the two faces (`StageType.IsFaceCell`).  Its laws:

* an equivalence: `IsSameCell.refl` and `IsSameCell.symm` with no hypothesis, and
  `IsSameCell.trans` under exact consistency, through the face of the middle occurrence on the
  intersection of two faces (a face, since the faces of a stage type form a plan);
  `Realization.isSameCell_equivalence` states the three together;
* distinct cells stay distinct: two cells of one type are the same cell only if they are equal
  (`IsSameCell.eq`, `isSameCell_self_iff`); cells with equal scope and grade are not identified;
  under exact consistency a cell is the same cell as at most one cell of a given occurrence
  (`IsSameCell.unique`);
* under exact consistency the same cell has the same scope as a set of points of the carrier,
  the same label and the same grade (`IsSameCell.scope_map_eq`, `IsSameCell.label_eq`,
  `IsSameCell.grade_eq`);
* refinement: the cell at the position of `a` on a face of `u` is the same cell as `a`
  (`isSameCell_of_trans_eq`), and under exact consistency every cell has one
  (`exists_isSameCell_of_trans_eq`);
* below-domains and rows transport: if `θ, θ'` and `a, e` are pairs of the same cell, then `e`
  is below `θ'` exactly when `a` is below `θ`, and the rows agree
  (`IsSameCell.mem_below_iff`, `IsSameCell.rowAt_eq`, under exact consistency).

**Minimality at infinity and the label.**  `Realization.IsMinimalAtInfinity x a K` is a native
global-cell rendering of the printed inequality at the cell `a` with the bound `K` (the printed
`K'`), no label being required of `a`.  `Realization.IsGlobalRowAnchor x a K` adds that `a` is
labelled `⊤`.  The label conjunct makes explicit the requirement that the anchor be labelled `⊤`,
which the printed definition does not state: without it the inequality degenerates.  Under
exact consistency every cell not labelled `⊤` is minimal at infinity at every bound, strictly
(`Realization.isMinimalAtInfinity_of_label_ne_top`, from the locality law through
`StageType.rowAt_lt_rowAt_of_label_ne_top`), and every model at a positive stage has such a cell,
by uniformity at `γ = 0` (`Realization.IsModel.exists_isMinimalAtInfinity`); so the inequality
without the label never yields hollowness.  The proof of [Kni26, Lemma 5.5.1, p. 57] uses the
label (`𝔐⁺(⚓∞) ∈ [α, α + ω)` is derived from the alternative `𝔐⁺(⚓∞) = ∞`).  The compiled
degeneracy supports making the top-label requirement explicit; the conjunct is a formalization
adjustment, not an erratum confirmed by the author, and not a correspondence between the models
of [Kni26] and the models of this repository.

**Clauses of [Kni26, Definition 5.4.2, p. 56] and of `IsMinimalAtInfinity`**, the native
global-cell rendering of the printed inequality.

| Printed | Here |
| --- | --- |
| `Θ`, `Σ` in the domains of the types of `𝔐` | cells `θ`, `σ` of the type of any occurrence `z` |
| `⚓∞ ∈ dom p`, read in the domain of `Θ` | a cell `e` of `z` with `IsSameCell x a z e` |
| `𝔐(Θ) = ∞`, `𝔐(Σ) = ∞` | `z.type.label θ = ⊤`, `z.type.label σ = ⊤` |
| `Θ` has arity `≥ K'` | `K ≤ z.type.toCellScheme.grade θ` |
| `ℰ(Θ)(Σ)`, `ℰ(Θ)(⚓∞)` defined (the domain `𝒟⪯⟨B,j⟩` of `ℰ(Θ)`) | `σ` and `e` below `θ` |
| `ℰ(Θ)(Σ) ⌊+⌋^{K'} K' ≥ ℰ(Θ)(⚓∞)` | `z.type.rowAt θ e ≤ visibilityReplace K K (z.type.rowAt θ σ)` |
| strict if the arity of `Θ` exceeds `K'` | strict if `K < z.type.toCellScheme.grade θ` |

The semantics `ℰ(Θ)` is read as the row of `θ` ([Kni26, Definition 2.5.3, p. 20]; rows of the
types, concordance rows 4, 7 and 8), and `⌊+⌋^{K'} K'` is visibility replacement at threshold `K'`
with value `K'` ([Kni26, Definition 2.2.3, p. 9]; concordance row 2).

**The comparison at the same bound.**

* `Realization.IsGlobalRowAnchor.isRowAnchor`, with no hypothesis on `R`: an actual rooted cover
  of `x` is an occurrence, and the cell transported from `a` is the same cell as `a`.
* `Realization.IsRowAnchor.isGlobalRowAnchor`, under exact consistency and covering: an
  occurrence `z` and an occurrence containing `x` and `z` (covering) carry the cells of `z` into
  an actual rooted cover of `x`, with labels, grades, below-domains and rows unchanged.
* At a model: `Realization.IsModel.isGlobalRowAnchor_iff_isRowAnchor`,
  `Realization.IsModel.hasGlobalRowAnchor_iff_hasRowAnchor`, and, at a block stage,
  `Realization.IsModel.isCoverHollow_iff_not_hasGlobalRowAnchor`.

The comparison here is between the global and the rooted readings of one row condition, at one
bound.  It does not remove the distinction of bounds between the row anchor and the anchor at
the top (`Realization.IsTopAnchor`): under legal types a row anchor at `K` gives an anchor at the
top at `K + 1` (`Realization.IsRowAnchor.isTopAnchor`), and at a model an anchor at the top at `N`
is a row anchor at `N` (`Realization.IsTopAnchor.isRowAnchor`).

**Open.**  Characteristic arity ([Kni26, Definition 5.4.1, p. 54]) has no counterpart here, and
the hypothesis `0 < K ≤ ∞` under which the printed definition is made is not represented: the
statements here hold for every model.  The reconstruction of the printed coded domains and the
correspondence between the models of `S^α` of [Kni26, Definition 3.2.1] and the models of this
repository, under which the cells, labels and rows of the two would correspond, are not
addressed: every statement here concerns realizations of this repository.

## Placement

This file belongs to Layer 4 of `roadmap/README.md` (research).

## References

The anchor at infinity and hollowness are [Kni26, Definition 5.4.2, p. 56]; the value of an
element allotted by the model is [Kni26, Definition 3.2.5 and Lemma 3.2.6, p. 31].
-/

universe u v

namespace VaughtConjecture

open Finset Order Label
open scoped Ordinal

/-! ### Positions along a face -/

namespace Scheme

variable {n m k : ℕ}

/-- Equal schemes have equal scopes at cells with equal positions. -/
theorem scope_congr {S S' : Scheme.{u} n} (h : S = S') {i : Fin S.card} {j : Fin S'.card}
    (hij : (i : ℕ) = j) : S.toCellScheme.scope i = S'.toCellScheme.scope j := by
  subst h
  rw [Fin.ext hij]

/-- Equal schemes have equal graded indices at cells with equal positions. -/
theorem gradedIndex_congr {S S' : Scheme.{u} n} (h : S = S') {i : Fin S.card} {j : Fin S'.card}
    (hij : (i : ℕ) = j) : S.toCellScheme.gradedIndex i = S'.toCellScheme.gradedIndex j :=
  Prod.ext (scope_congr h hij) (grade_congr h hij)

/-- Equal schemes have equal rows at cells with equal positions. -/
theorem rowAt_congr {S S' : Scheme.{u} n} (h : S = S') {s x : Fin S.card} {s' x' : Fin S'.card}
    (hs : (s : ℕ) = s') (hx : (x : ℕ) = x') : S.rowAt s x = S'.rowAt s' x' := by
  subst h
  rw [Fin.ext hs, Fin.ext hx]

/-- Equal schemes have cell maps along `f` with equal positions at equal positions. -/
theorem cellMap_val_congr {S S' : Scheme.{u} n} (h : S = S') (f : Fin m ↪ Fin n)
    {i : Fin (S.comap f).card} {i' : Fin (S'.comap f).card} (hi : (i : ℕ) = i') :
    (S.cellMap f i : ℕ) = S'.cellMap f i' := by
  subst h
  rw [Fin.ext hi]

variable (S : Scheme.{u} n)

/-- The cell map along the identity keeps positions. -/
theorem cellMap_refl_val (i : Fin (S.comap (Function.Embedding.refl (Fin n))).card) :
    (S.cellMap (Function.Embedding.refl (Fin n)) i : ℕ) = i := by
  have hr : ∀ d, d ∈ Set.range (id : Fin S.card → Fin S.card) ↔
      d ∈ S.visibleCells (Function.Embedding.refl (Fin n)) := fun d ↦ by
    simp [Function.Embedding.coe_refl]
  have hc : #(S.visibleCells (Function.Embedding.refl (Fin n))) = S.card :=
    S.card_visibleCells_eq_of_strictMono _ strictMono_id hr
  have key := S.cellMap_eq_of_strictMono _ strictMono_id hr
    (i := ⟨i, lt_of_lt_of_eq i.2 hc⟩) (j := i) rfl
  rw [← key]
  rfl

/-- Rows along a restriction: the row of a cell of the restriction at a cell is the row of the
corresponding cells.  (The same statement as `Scheme.rowAt_comap` of
`VaughtConjecture.MainTheorem.GrowthRelabelLadder`, which is not imported here.) -/
theorem rowAt_cellMap (f : Fin m ↪ Fin n) (i j : Fin (S.comap f).card) :
    S.rowAt (S.cellMap f i) (S.cellMap f j) = (S.comap f).rowAt i j := by
  have hle := S.isLowerEmbedding_comap f
  unfold Scheme.rowAt
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((hle.le_iff j i).mp h1) h2
  · exact absurd ((hle.le_iff j i).mpr h2) h1
  · rfl

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- The cell `a` of `t` is the cell at the position `c` of the face along `f`: the image under
the cell map along `f` of the cell of the restriction at position `c`. -/
def IsFaceCell (t : StageType.{u} α n) (f : Fin m ↪ Fin n) (c : ℕ) (a : Fin t.card) : Prop :=
  ∃ i : Fin (t.toScheme.comap f).card, (i : ℕ) = c ∧ t.cellMap f i = a

variable {t : StageType.{u} α n} {f : Fin m ↪ Fin n} {c c' : ℕ} {a a' : Fin t.card}

/-- A position of the face is the position of at most one cell. -/
theorem IsFaceCell.eq (h : t.IsFaceCell f c a) (h' : t.IsFaceCell f c a') : a = a' := by
  obtain ⟨i, hi, rfl⟩ := h
  obtain ⟨i', hi', rfl⟩ := h'
  rw [Fin.ext (hi.trans hi'.symm)]

/-- A cell is the cell of at most one position of the face. -/
theorem IsFaceCell.val_eq (h : t.IsFaceCell f c a) (h' : t.IsFaceCell f c' a) : c = c' := by
  obtain ⟨i, rfl, hi⟩ := h
  obtain ⟨i', rfl, hi'⟩ := h'
  rw [(t.cellMap f).injective (hi.trans hi'.symm)]

/-- The cell map of `f` sends each cell of the restriction to the cell at its position. -/
theorem isFaceCell_cellMap (i : Fin (t.toScheme.comap f).card) : t.IsFaceCell f i (t.cellMap f i) :=
  ⟨i, rfl, rfl⟩

/-- Along the identity, every cell is the cell at its own position. -/
theorem isFaceCell_refl (a : Fin t.card) :
    t.IsFaceCell (Function.Embedding.refl (Fin n)) a a := by
  have hc : (t.toScheme.comap (Function.Embedding.refl (Fin n))).card = t.card := by
    rw [Scheme.comap_refl]
  refine ⟨⟨a, lt_of_lt_of_eq a.2 hc.symm⟩, rfl, Fin.ext ?_⟩
  exact t.toScheme.cellMap_refl_val _

/-- A cell whose scope lies in the range of `f` is the cell at some position of the face. -/
theorem exists_isFaceCell_of_scope_subset (hs : t.toCellScheme.scope a ⊆ univ.map f) :
    ∃ c : ℕ, t.IsFaceCell f c a := by
  have ha : a ∈ Set.range (t.cellMap f) := by
    rw [Scheme.range_cellMap]
    simpa [Scheme.visibleCells] using hs
  obtain ⟨i, rfl⟩ := ha
  exact ⟨i, isFaceCell_cellMap i⟩

end StageType

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **A cell not labelled `⊤` is read strictly below every cell labelled `⊤`** by the row of a
cell labelled `⊤`.  Let `θ` and `σ` be labelled `⊤` and `e` not, with `σ` and `e` below `θ`.
By locality, the row of `θ` transforms to the labels below `θ` capped at the label `⊤` of `θ`,
that is, to the labels themselves; the suppressor is `⊤` at the grade of `θ`, hence at every
smaller grade, so the label of a cell below `θ` is the shifter applied to its row entry.  The
shifter is monotone, so the row entry of `e` is below that of `σ`. -/
theorem rowAt_lt_rowAt_of_label_ne_top (t : StageType.{u} α n) {θ σ e : Fin t.card}
    (hθ : t.label θ = ⊤) (hσ : t.label σ = ⊤) (he : t.label e ≠ ⊤)
    (hσθ : σ ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex θ))
    (heθ : e ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex θ)) :
    t.rowAt θ e < t.rowAt θ σ := by
  obtain ⟨g, f, hw, hq⟩ := t.isLawful.locality θ
  have hθθ := t.toCellScheme.mem_below_gradedIndex θ
  have hgθ : g (t.toCellScheme.grade θ) = ⊤ := by
    have h := hq ⟨θ, hθθ⟩
    simp only [hθ, min_self] at h
    exact (min_eq_top.mp h.symm).2
  have hlabel (d : Fin t.card) (hd : d ∈ t.toCellScheme.below (t.toCellScheme.gradedIndex θ)) :
      t.label d = f (t.rowAt θ d) := by
    have hg : g (t.toCellScheme.grade d) = ⊤ :=
      top_le_iff.mp (hgθ ▸ hw.antitone ((CellScheme.mem_below _).mp hd).2)
    have h := hq ⟨d, hd⟩
    simp only [hθ, le_top, min_eq_left, hg] at h
    rw [h, Scheme.rowAt_of_mem hd]
  by_contra hlt
  refine he (top_le_iff.mp ?_)
  rw [← hσ, hlabel σ hσθ, hlabel e heθ]
  exact hw.monotone (not_lt.mp hlt)

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

section Face

variable (hR : R.IsConsistent) {w x : R.Occurrence} {h : Fin w.arity ↪ Fin x.arity}
  (hh : h.trans x.tuple = w.tuple)
include hR hh

/-- **The scheme of a face.**  Under exact consistency, if the tuple of `w` is the face of the
tuple of `x` along `h`, the restriction of the scheme of `x` along `h` is the scheme of `w`. -/
theorem comap_toScheme_eq_of_trans_eq : x.type.toScheme.comap h = w.type.toScheme := by
  obtain ⟨hf, hw⟩ := (StageType.restrictFace_eq_some_iff _ _).mp
    (Occurrence.restrictFace_eq_some_of_trans_eq hR hh)
  exact congrArg StageType.toScheme hw

/-- Every cell of the type of a face `w` of `x` is the cell at its position of the face. -/
theorem exists_isFaceCell (c : Fin w.type.card) : ∃ a, x.type.IsFaceCell h c a := by
  have hc := congrArg Scheme.card (comap_toScheme_eq_of_trans_eq hR hh)
  exact ⟨_, StageType.isFaceCell_cellMap ⟨c, lt_of_lt_of_eq c.2 hc.symm⟩⟩

variable {c c' : Fin w.type.card} {a a' : Fin x.type.card}

/-- A cell at a position of a face has the label of the cell of the face there. -/
theorem label_eq_of_isFaceCell (ha : x.type.IsFaceCell h c a) :
    x.type.label a = w.type.label c := by
  obtain ⟨hf, hw⟩ := (StageType.restrictFace_eq_some_iff _ _).mp
    (Occurrence.restrictFace_eq_some_of_trans_eq hR hh)
  obtain ⟨i, hi, rfl⟩ := ha
  exact StageType.label_congr hw (i := i) hi

/-- A cell at a position of a face has the grade of the cell of the face there. -/
theorem grade_eq_of_isFaceCell (ha : x.type.IsFaceCell h c a) :
    x.type.toCellScheme.grade a = w.type.toCellScheme.grade c := by
  obtain ⟨i, hi, rfl⟩ := ha
  exact (Scheme.grade_congr (comap_toScheme_eq_of_trans_eq hR hh) hi :)

/-- A cell at a position of a face has the image of the scope of the cell of the face there. -/
theorem scope_eq_of_isFaceCell (ha : x.type.IsFaceCell h c a) :
    x.type.toCellScheme.scope a = (w.type.toCellScheme.scope c).map h := by
  obtain ⟨i, hi, rfl⟩ := ha
  rw [← Scheme.map_comap_scope, Scheme.scope_congr (comap_toScheme_eq_of_trans_eq hR hh) hi]

/-- Cells at positions of a face lie one below the other exactly when the cells of the face
there do. -/
theorem mem_below_iff_of_isFaceCell (ha : x.type.IsFaceCell h c a)
    (ha' : x.type.IsFaceCell h c' a') :
    a' ∈ x.type.toCellScheme.below (x.type.toCellScheme.gradedIndex a) ↔
      c' ∈ w.type.toCellScheme.below (w.type.toCellScheme.gradedIndex c) := by
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨i', hi', rfl⟩ := ha'
  have hS := comap_toScheme_eq_of_trans_eq hR hh
  rw [CellScheme.mem_below, CellScheme.mem_below, (x.type.isLowerEmbedding_comap h).le_iff,
    Scheme.gradedIndex_congr hS hi, Scheme.gradedIndex_congr hS hi']

/-- Cells at positions of a face have the row of the cells of the face there. -/
theorem rowAt_eq_of_isFaceCell (ha : x.type.IsFaceCell h c a) (ha' : x.type.IsFaceCell h c' a') :
    x.type.rowAt a a' = w.type.rowAt c c' := by
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨i', hi', rfl⟩ := ha'
  rw [Scheme.rowAt_cellMap]
  exact Scheme.rowAt_congr (comap_toScheme_eq_of_trans_eq hR hh) hi hi'

/-- A position of a face at which some cell of `x` lies is a position of a cell of `w`. -/
theorem lt_card_of_isFaceCell {c : ℕ} {a : Fin x.type.card} (ha : x.type.IsFaceCell h c a) :
    c < w.type.card := by
  obtain ⟨i, rfl, -⟩ := ha
  exact lt_of_lt_of_eq i.2 (congrArg Scheme.card (comap_toScheme_eq_of_trans_eq hR hh))

end Face

/-! ### The same cell in two occurrences -/

section SameCell

variable (R) in
/-- The cell `a` of the type of `x` and the cell `e` of the type of `z` are **the same cell** of
`R`: some occurrence `w` is a face of both, along `h` into `x` and `g` into `z`, and `a` and `e`
are the cells at the position of one cell `c` of the type of `w` on the two faces.  This is the
reading, on the positional cells of this repository, of the identity of the elements of the
domains of the types of a model in [Kni26, Definition 3.2.5, p. 31] (the value `𝔐(Σ)` of an
element `Σ`, allotted by the model as a whole). -/
def IsSameCell (x : R.Occurrence) (a : Fin x.type.card) (z : R.Occurrence)
    (e : Fin z.type.card) : Prop :=
  ∃ (w : R.Occurrence) (h : Fin w.arity ↪ Fin x.arity) (g : Fin w.arity ↪ Fin z.arity)
    (c : Fin w.type.card), h.trans x.tuple = w.tuple ∧ g.trans z.tuple = w.tuple ∧
    x.type.IsFaceCell h c a ∧ z.type.IsFaceCell g c e

variable {x y z u : R.Occurrence} {a θ : Fin x.type.card} {b : Fin y.type.card}
  {e e' θ' : Fin z.type.card}

/-- **Reflexivity** of the same-cell relation. -/
theorem IsSameCell.refl (x : R.Occurrence) (a : Fin x.type.card) : R.IsSameCell x a x a :=
  ⟨x, Function.Embedding.refl _, Function.Embedding.refl _, a, rfl, rfl,
    StageType.isFaceCell_refl a, StageType.isFaceCell_refl a⟩

/-- **Symmetry** of the same-cell relation. -/
theorem IsSameCell.symm (h : R.IsSameCell x a z e) : R.IsSameCell z e x a :=
  let ⟨w, h, g, c, hh, hg, ha, he⟩ := h
  ⟨w, g, h, c, hg, hh, he, ha⟩

/-- **Distinct cells stay distinct**: two cells of the type of one occurrence are the same cell
only if they are equal.  Cells with equal scope and grade are not identified. -/
theorem IsSameCell.eq (h : R.IsSameCell z e z e') : e = e' := by
  obtain ⟨w, h, g, c, hh, hg, he, he'⟩ := h
  obtain rfl : h = g := Function.Embedding.ext fun i ↦ z.tuple.injective
    ((DFunLike.congr_fun hh i).trans (DFunLike.congr_fun hg i).symm)
  exact he.eq he'

/-- Two cells of the type of one occurrence are the same cell exactly when they are equal. -/
theorem isSameCell_self_iff : R.IsSameCell z e z e' ↔ e = e' :=
  ⟨IsSameCell.eq, fun h ↦ h ▸ IsSameCell.refl z e⟩

/-- **Refinement**: if the tuple of `x` is the face of the tuple of `u` along `f`, the cell of
the type of `u` at the position of `a` on that face is the same cell as `a`. -/
theorem isSameCell_of_trans_eq {f : Fin x.arity ↪ Fin u.arity} (hf : f.trans u.tuple = x.tuple)
    {a' : Fin u.type.card} (ha : u.type.IsFaceCell f a a') : R.IsSameCell x a u a' :=
  ⟨x, Function.Embedding.refl _, f, a, rfl, hf, StageType.isFaceCell_refl a, ha⟩

/-- Under exact consistency every cell of `x` is the same cell as some cell of a refinement
`u` of `x`, the cell at its position on the face. -/
theorem exists_isSameCell_of_trans_eq (hR : R.IsConsistent) {f : Fin x.arity ↪ Fin u.arity}
    (hf : f.trans u.tuple = x.tuple) (a : Fin x.type.card) :
    ∃ a', u.type.IsFaceCell f a a' ∧ R.IsSameCell x a u a' :=
  let ⟨a', ha'⟩ := exists_isFaceCell hR hf a
  ⟨a', ha', isSameCell_of_trans_eq hf ha'⟩

/-- **The same cell has the same label** [Kni26, Lemma 3.2.6, p. 31], under exact consistency. -/
theorem IsSameCell.label_eq (hR : R.IsConsistent) (h : R.IsSameCell x a z e) :
    z.type.label e = x.type.label a := by
  obtain ⟨w, h, g, c, hh, hg, ha, he⟩ := h
  rw [label_eq_of_isFaceCell hR hg he, label_eq_of_isFaceCell hR hh ha]

/-- The same cell has the same grade, under exact consistency. -/
theorem IsSameCell.grade_eq (hR : R.IsConsistent) (h : R.IsSameCell x a z e) :
    z.type.toCellScheme.grade e = x.type.toCellScheme.grade a := by
  obtain ⟨w, h, g, c, hh, hg, ha, he⟩ := h
  rw [grade_eq_of_isFaceCell hR hg he, grade_eq_of_isFaceCell hR hh ha]

/-- The same cell has the same scope, as a set of points of the carrier, under exact
consistency. -/
theorem IsSameCell.scope_map_eq (hR : R.IsConsistent) (h : R.IsSameCell x a z e) :
    (z.type.toCellScheme.scope e).map z.tuple = (x.type.toCellScheme.scope a).map x.tuple := by
  obtain ⟨w, h, g, c, hh, hg, ha, he⟩ := h
  rw [scope_eq_of_isFaceCell hR hg he, scope_eq_of_isFaceCell hR hh ha, Finset.map_map,
    Finset.map_map, hh, hg]

/-- **Composition of faces at a cell.**  Let `w` be a face of `x` along `h` and of `z` along
`g`, with `a` and `e` the cells at the position `c` of the two faces, and let `v = p.trans g`.
If `e` is the cell at the position `d` of the face of `z` along `v`, then `a` is the cell at
the position `d` of the face of `x` along `p.trans h`. -/
theorem isFaceCell_trans_of_isFaceCell (hR : R.IsConsistent) {w : R.Occurrence}
    {h : Fin w.arity ↪ Fin x.arity} {g : Fin w.arity ↪ Fin z.arity} {c : ℕ}
    (hh : h.trans x.tuple = w.tuple) (hg : g.trans z.tuple = w.tuple)
    (ha : x.type.IsFaceCell h c a) (he : z.type.IsFaceCell g c e) {k : ℕ}
    {p : Fin k ↪ Fin w.arity} {v : Fin k ↪ Fin z.arity} (hp : p.trans g = v) {d : ℕ}
    (hd : z.type.IsFaceCell v d e) : x.type.IsFaceCell (p.trans h) d a := by
  obtain ⟨jd, rfl, hjd⟩ := hd
  obtain ⟨j, rfl, hj⟩ := he
  obtain ⟨i, hi, rfl⟩ := ha
  have hSx := comap_toScheme_eq_of_trans_eq hR hh
  have hSz := comap_toScheme_eq_of_trans_eq hR hg
  have hxz : x.type.toScheme.comap h = z.type.toScheme.comap g := hSx.trans hSz.symm
  have hcz : ((z.type.toScheme.comap g).comap p).card = (z.type.toScheme.comap v).card := by
    rw [Scheme.comap_comap, hp]
  have hcx : ((x.type.toScheme.comap h).comap p).card = (z.type.toScheme.comap v).card := by
    rw [hxz, hcz]
  set kz : Fin ((z.type.toScheme.comap g).comap p).card := ⟨jd, lt_of_lt_of_eq jd.2 hcz.symm⟩
  set kx : Fin ((x.type.toScheme.comap h).comap p).card := ⟨jd, lt_of_lt_of_eq jd.2 hcx.symm⟩
  have hzv : z.type.cellMap g ((z.type.toScheme.comap g).cellMap p kz) = z.type.cellMap v jd :=
    (z.type.toScheme.cellMap_cellMap g p (j := ⟨jd, lt_of_lt_of_eq jd.2
      (by rw [hp])⟩) rfl).trans (z.type.toScheme.cellMap_congr hp rfl)
  have hkz : (z.type.toScheme.comap g).cellMap p kz = j :=
    (z.type.cellMap g).injective (hzv.trans (hjd.trans hj.symm))
  have hkx : (x.type.toScheme.comap h).cellMap p kx = i := Fin.ext
    ((Scheme.cellMap_val_congr hxz p rfl).trans ((congrArg Fin.val hkz).trans hi.symm))
  refine ⟨⟨jd, lt_of_lt_of_eq jd.2 (by rw [← Scheme.comap_comap, ← hcx])⟩, rfl, ?_⟩
  rw [← hkx]
  exact (x.type.toScheme.cellMap_cellMap h p rfl).symm

/-- **Transitivity** of the same-cell relation, under exact consistency.  The common face of `x`
and `y` is the face of `z` on the intersection of the two faces through which `e` is seen, a
face since the faces of a stage type form a plan. -/
theorem IsSameCell.trans (hR : R.IsConsistent) (h₁ : R.IsSameCell x a z e)
    (h₂ : R.IsSameCell z e y b) : R.IsSameCell x a y b := by
  obtain ⟨w, h, g, c, hh, hg, ha, he⟩ := h₁
  obtain ⟨w', h', g', c', hh', hg', he', hb⟩ := h₂
  have hF {m : ℕ} {w₀ : R.Occurrence} {f : Fin w₀.arity ↪ Fin z.arity}
      (hf : f.trans z.tuple = w₀.tuple) : univ.map f ∈ z.type.toCellScheme.faces :=
    (StageType.isSome_restrictFace_iff _ _).mp
      (by rw [Occurrence.restrictFace_eq_some_of_trans_eq hR hf]; rfl)
  set V : Finset (Fin z.arity) := univ.map g ∩ univ.map h'
  have hV : V ∈ z.type.toCellScheme.faces :=
    z.type.isPlan.infClosed (hF (m := 0) hg) (hF (m := 0) hh')
  set v : Fin #V ↪ Fin z.arity := (V.orderEmbOfFin rfl).toEmbedding
  have hvV : univ.map v = V := map_orderEmbOfFin_univ V rfl
  have hvmem (i : Fin #V) : v i ∈ V := orderEmbOfFin_mem V rfl i
  obtain ⟨p, hp⟩ : ∃ p : Fin #V ↪ Fin w.arity, p.trans g = v :=
    Function.Embedding.exists_trans_eq fun i ↦ by
      obtain ⟨j, -, hj⟩ := mem_map.mp (mem_inter.mp (hvmem i)).1
      exact ⟨j, hj⟩
  obtain ⟨p', hp'⟩ : ∃ p' : Fin #V ↪ Fin w'.arity, p'.trans h' = v :=
    Function.Embedding.exists_trans_eq fun i ↦ by
      obtain ⟨j, -, hj⟩ := mem_map.mp (mem_inter.mp (hvmem i)).2
      exact ⟨j, hj⟩
  have hs : z.type.toCellScheme.scope e ⊆ univ.map v := by
    rw [hvV]
    refine subset_inter ?_ ?_
    · rw [scope_eq_of_isFaceCell hR hg he]; exact map_subset_map.mpr (subset_univ _)
    · rw [scope_eq_of_isFaceCell hR hh' he']; exact map_subset_map.mpr (subset_univ _)
  obtain ⟨d, hd⟩ := StageType.exists_isFaceCell_of_scope_subset hs
  have hax := isFaceCell_trans_of_isFaceCell hR hh hg ha he hp hd
  have hby := isFaceCell_trans_of_isFaceCell hR hg' hh' hb he' hp' hd
  let u₀ : R.Occurrence := z.face hR v (by rwa [hvV])
  have hu₀ : v.trans z.tuple = u₀.tuple := rfl
  have hpx : (p.trans h).trans x.tuple = u₀.tuple := by
    rw [← hu₀, ← hp]
    ext i
    simp only [Function.Embedding.trans_apply]
    exact (DFunLike.congr_fun hh (p i)).trans (DFunLike.congr_fun hg (p i)).symm
  have hpy : (p'.trans g').trans y.tuple = u₀.tuple := by
    rw [← hu₀, ← hp']
    ext i
    simp only [Function.Embedding.trans_apply]
    exact (DFunLike.congr_fun hg' (p' i)).trans (DFunLike.congr_fun hh' (p' i)).symm
  exact ⟨u₀, p.trans h, p'.trans g', ⟨d, lt_card_of_isFaceCell hR hpx hax⟩, hpx, hpy, hax, hby⟩

/-- **The same-cell relation is an equivalence** on the cells of the occurrences of `R`, under
exact consistency. -/
theorem isSameCell_equivalence (hR : R.IsConsistent) :
    Equivalence fun p q : Σ x : R.Occurrence, Fin x.type.card ↦ R.IsSameCell p.1 p.2 q.1 q.2 :=
  ⟨fun p ↦ IsSameCell.refl p.1 p.2, IsSameCell.symm, IsSameCell.trans hR⟩

/-- Under exact consistency a cell of `x` is the same cell as at most one cell of `z`. -/
theorem IsSameCell.unique (hR : R.IsConsistent) (h : R.IsSameCell x a z e)
    (h' : R.IsSameCell x a z e') : e = e' :=
  (h.symm.trans hR h').eq

/-- Below a cell, inside a common face: if `θ` and `θ'` are the same cell, `a` and `e` are the
same cell and `a` lies below `θ`, then `e` lies below `θ'` and the rows agree there. -/
theorem IsSameCell.mem_below_and_rowAt_eq (hR : R.IsConsistent) (hθ : R.IsSameCell x θ z θ')
    (ha : R.IsSameCell x a z e)
    (hb : a ∈ x.type.toCellScheme.below (x.type.toCellScheme.gradedIndex θ)) :
    e ∈ z.type.toCellScheme.below (z.type.toCellScheme.gradedIndex θ') ∧
      z.type.rowAt θ' e = x.type.rowAt θ a := by
  obtain ⟨w, h, g, c, hh, hg, hθx, hθz⟩ := hθ
  have hs : x.type.toCellScheme.scope a ⊆ univ.map h :=
    (CellScheme.mem_below _ |>.mp hb).1.trans
      (by rw [CellScheme.gradedIndex_fst, scope_eq_of_isFaceCell hR hh hθx]
          exact map_subset_map.mpr (subset_univ _))
  obtain ⟨c₁, hc₁⟩ := StageType.exists_isFaceCell_of_scope_subset hs
  set c₁' : Fin w.type.card := ⟨c₁, lt_card_of_isFaceCell hR hh hc₁⟩
  obtain ⟨e₁, he₁⟩ := exists_isFaceCell hR hg c₁'
  obtain rfl : e₁ = e := IsSameCell.unique hR ⟨w, h, g, c₁', hh, hg, hc₁, he₁⟩ ha
  refine ⟨(mem_below_iff_of_isFaceCell hR hg hθz he₁).mpr
    ((mem_below_iff_of_isFaceCell hR hh hθx (c' := c₁') hc₁).mp hb), ?_⟩
  rw [rowAt_eq_of_isFaceCell hR hg hθz he₁, rowAt_eq_of_isFaceCell hR hh hθx (c' := c₁') hc₁]

/-- **Below-domains transport along the same cell**, under exact consistency. -/
theorem IsSameCell.mem_below_iff (hR : R.IsConsistent) (hθ : R.IsSameCell x θ z θ')
    (ha : R.IsSameCell x a z e) :
    e ∈ z.type.toCellScheme.below (z.type.toCellScheme.gradedIndex θ') ↔
      a ∈ x.type.toCellScheme.below (x.type.toCellScheme.gradedIndex θ) :=
  ⟨fun hb ↦ (hθ.symm.mem_below_and_rowAt_eq hR ha.symm hb).1,
    fun hb ↦ (hθ.mem_below_and_rowAt_eq hR ha hb).1⟩

/-- **Rows transport along the same cell**, under exact consistency: the row of `θ'` at `e` is
the row of `θ` at `a` (both `⊥` off the cells below). -/
theorem IsSameCell.rowAt_eq (hR : R.IsConsistent) (hθ : R.IsSameCell x θ z θ')
    (ha : R.IsSameCell x a z e) : z.type.rowAt θ' e = x.type.rowAt θ a := by
  by_cases hb : a ∈ x.type.toCellScheme.below (x.type.toCellScheme.gradedIndex θ)
  · exact (hθ.mem_below_and_rowAt_eq hR ha hb).2
  · rw [Scheme.rowAt_of_notMem hb,
      Scheme.rowAt_of_notMem fun he ↦ hb ((hθ.mem_below_iff hR ha).mp he)]

end SameCell

/-! ### Minimality at infinity and global row anchors -/

section Anchor

variable (R) in
/-- **Minimal at infinity**: a native global-cell rendering of the printed inequality of
[Kni26, Definition 5.4.2, p. 56], at the cell `a` of the type of `x` with the bound `K` (the
printed `K'`), quantified over the cells of the whole realization: for every occurrence `z`,
every cell `e` of its type that is the same cell as `a`, every cell `θ` labelled `⊤` of grade at
least `K` and every cell `σ` labelled `⊤`, with `σ` and `e` below `θ` (the domain of the row of
`θ`),
`z.type.rowAt θ e ≤ visibilityReplace K K (z.type.rowAt θ σ)`, strictly when the grade of `θ`
exceeds `K`.  No label is required of `a`; see `Realization.IsGlobalRowAnchor`. -/
def IsMinimalAtInfinity (x : R.Occurrence) (a : Fin x.type.card) (K : ℕ) : Prop :=
  ∀ (z : R.Occurrence) (e : Fin z.type.card), R.IsSameCell x a z e →
    ∀ θ : Fin z.type.card, z.type.label θ = ⊤ → K ≤ z.type.toCellScheme.grade θ →
    ∀ σ : Fin z.type.card, z.type.label σ = ⊤ →
      σ ∈ z.type.toCellScheme.below (z.type.toCellScheme.gradedIndex θ) →
      e ∈ z.type.toCellScheme.below (z.type.toCellScheme.gradedIndex θ) →
      z.type.rowAt θ e ≤ visibilityReplace K K (z.type.rowAt θ σ) ∧
        (K < z.type.toCellScheme.grade θ →
          z.type.rowAt θ e < visibilityReplace K K (z.type.rowAt θ σ))

variable (R) in
/-- A **global row anchor**: the native global-cell rendering of the printed inequality of the
anchor at infinity of [Kni26, Definition 5.4.2, p. 56], with the requirement that the anchor be
labelled `⊤` made explicit.  The cell `a` is labelled `⊤` and is minimal at infinity at the bound
`K`.  Without the label the inequality degenerates: every cell not labelled `⊤` is minimal at
infinity at every bound (`Realization.isMinimalAtInfinity_of_label_ne_top`), and every model at a
positive stage has such a cell (`Realization.IsModel.exists_isMinimalAtInfinity`).  The compiled
degeneracy supports making the label explicit; this is a formalization adjustment, not an erratum
confirmed by the author, and not a correspondence of model classes. -/
def IsGlobalRowAnchor (x : R.Occurrence) (a : Fin x.type.card) (K : ℕ) : Prop :=
  x.type.label a = ⊤ ∧ R.IsMinimalAtInfinity x a K

variable (R) in
/-- The realization **has a global row anchor**: some occurrence, cell and bound form one. -/
def HasGlobalRowAnchor : Prop :=
  ∃ (x : R.Occurrence) (a : Fin x.type.card) (K : ℕ), R.IsGlobalRowAnchor x a K

variable {x : R.Occurrence} {a : Fin x.type.card} {K : ℕ}

/-- **The inequality without the label degenerates**: under exact consistency, a cell not
labelled `⊤` is minimal at infinity at every bound, with the strict inequality at every `θ`.
The cell read by the row of `θ` is the same cell, so it is not labelled `⊤`
(`Realization.IsSameCell.label_eq`), and the row of `θ` reads it strictly below every cell
labelled `⊤` (`StageType.rowAt_lt_rowAt_of_label_ne_top`), hence below the visibility
replacement (`Label.le_visibilityReplace`). -/
theorem isMinimalAtInfinity_of_label_ne_top (hR : R.IsConsistent) (ha : x.type.label a ≠ ⊤)
    (K : ℕ) : R.IsMinimalAtInfinity x a K := by
  intro z e hxe θ hθ _ σ hσ hσθ heθ
  have hlt := (z.type.rowAt_lt_rowAt_of_label_ne_top hθ hσ (by rwa [hxe.label_eq hR]) hσθ
    heθ).trans_le (le_visibilityReplace (Nat.le_succ K) _)
  exact ⟨hlt.le, fun _ ↦ hlt⟩

/-- **Every model at a positive stage has a cell minimal at infinity at every bound** that is
not labelled `⊤`: uniformity at `γ = 0` gives a cell labelled in `[0, ω)`.  So the inequality
"minimal at infinity" without the label holds in every such model, and its absence never
holds. -/
theorem IsModel.exists_isMinimalAtInfinity (hR : R.IsModel) (hα : 0 < α) :
    ∃ (x : R.Occurrence) (a : Fin x.type.card), x.type.label a ≠ ⊤ ∧
      ∀ K, R.IsMinimalAtInfinity x a K := by
  obtain ⟨x₀⟩ := hR.nonempty_occurrence
  obtain ⟨u, -, q, ⟨d, -, hd⟩, hq⟩ := hR.uniformity x₀ 0 Ordinal.isSuccPrelimit_zero hα
  have hd' : q.label d ≠ ⊤ := ne_top_of_lt hd
  exact ⟨⟨_, u, q, hq⟩, d, hd', isMinimalAtInfinity_of_label_ne_top hR.isConsistent hd'⟩

/-- **A global row anchor is a row anchor at the same bound**, with no hypothesis on `R`.  An
actual rooted cover `(m, q, f)` of `x` with tuple `s` is an occurrence, and the cell `e` of `q`
transported from `a` is the same cell as `a` (`Realization.isSameCell_of_trans_eq`). -/
theorem IsGlobalRowAnchor.isRowAnchor (h : R.IsGlobalRowAnchor x a K) :
    R.IsRowAnchor x a K := by
  refine ⟨h.1, fun ⟨m, q, f⟩ ⟨s, hsf, hs⟩ hfp e he θ hθ hK σ hσ hσθ heθ ↦ ?_⟩
  let z : R.Occurrence := ⟨m, ⟨s, hs.injective⟩, q, hs.eval_eq⟩
  have hfz : f.trans z.tuple = x.tuple :=
    Function.Embedding.ext fun i ↦ congrFun hsf i
  obtain ⟨hf, hqp⟩ := (StageType.restrictFace_eq_some_iff q f).mp hfp
  have hcard : (q.toScheme.comap f).card = x.type.card :=
    congrArg (fun t : StageType.{u} α x.arity ↦ t.card) hqp
  have hae : q.IsFaceCell f a e :=
    ⟨⟨a, lt_of_lt_of_eq a.2 hcard.symm⟩, rfl, he _ rfl⟩
  exact h.2 z e (isSameCell_of_trans_eq (u := z) hfz hae) θ hθ hK σ hσ hσθ heθ

/-- **A row anchor is a global row anchor at the same bound**, under exact consistency and
covering.  A cell `e` of an occurrence `z` that is the same cell as `a`, and cells `θ` and `σ` of
`z`, are carried into an occurrence `u` containing `x` and `z` (covering); there `e` becomes the
cell transported from `a` (`Realization.IsSameCell.unique`), with the same labels, grades,
below-domains and rows (`Realization.IsSameCell.label_eq`, `IsSameCell.grade_eq`,
`IsSameCell.mem_below_iff`, `IsSameCell.rowAt_eq`), and `u` is an actual rooted cover of `x`. -/
theorem IsRowAnchor.isGlobalRowAnchor (hR : R.IsConsistent) (hc : R.IsCovering)
    (h : R.IsRowAnchor x a K) : R.IsGlobalRowAnchor x a K := by
  refine ⟨h.1, fun z e hxe θ hθ hK σ hσ hσθ heθ ↦ ?_⟩
  have := hc.isDirected
  obtain ⟨u, hxu, hzu⟩ := directed_of (· ≤ ·) x z
  obtain ⟨f, hf, hfp⟩ := (Occurrence.le_iff_exists_restrictFace hR).mp hxu
  obtain ⟨g, hg, -⟩ := (Occurrence.le_iff_exists_restrictFace hR).mp hzu
  obtain ⟨a', ha'f, ha'⟩ := exists_isSameCell_of_trans_eq hR hf a
  obtain ⟨θ', -, hθ'⟩ := exists_isSameCell_of_trans_eq hR hg θ
  obtain ⟨σ', -, hσ'⟩ := exists_isSameCell_of_trans_eq hR hg σ
  obtain ⟨e', -, he'⟩ := exists_isSameCell_of_trans_eq hR hg e
  obtain rfl : a' = e' := (ha'.symm.trans hR (hxe.trans hR he')).eq
  have hcov : R.ExtendsToCover x.tuple ⟨u.arity, u.type, f⟩ :=
    ⟨u.tuple, funext fun i ↦ DFunLike.congr_fun hf i, covers_of_eval _ u.eval_tuple⟩
  have htr : ∀ i : Fin (u.type.toScheme.comap f).card, (i : ℕ) = a → u.type.cellMap f i = a' :=
    fun i hi ↦ by
      obtain ⟨j, hj, rfl⟩ := ha'f
      rw [Fin.ext (hi.trans hj.symm)]
  have hrow := h.2 ⟨u.arity, u.type, f⟩ hcov hfp a' htr θ' (by rw [hθ'.label_eq hR, hθ])
    (by rwa [hθ'.grade_eq hR]) σ' (by rw [hσ'.label_eq hR, hσ])
    ((hθ'.mem_below_iff hR hσ').mpr hσθ) ((hθ'.mem_below_iff hR he').mpr heθ)
  rw [hθ'.rowAt_eq hR he', hθ'.rowAt_eq hR hσ', hθ'.grade_eq hR] at hrow
  exact hrow

/-- **At a model, global row anchors are row anchors at the same bound.** -/
theorem IsModel.isGlobalRowAnchor_iff_isRowAnchor (hR : R.IsModel) :
    R.IsGlobalRowAnchor x a K ↔ R.IsRowAnchor x a K :=
  ⟨fun h ↦ h.isRowAnchor,
    fun h ↦ h.isGlobalRowAnchor hR.isConsistent hR.isCovering⟩

/-- **At a model, a global row anchor exists exactly when a row anchor does.** -/
theorem IsModel.hasGlobalRowAnchor_iff_hasRowAnchor (hR : R.IsModel) :
    R.HasGlobalRowAnchor ↔ R.HasRowAnchor :=
  exists_congr fun _ ↦ exists_congr fun _ ↦ exists_congr fun _ ↦
    hR.isGlobalRowAnchor_iff_isRowAnchor

end Anchor

/-- **At a model at a block stage, cover-hollowness is the absence of a global row anchor**
(`Realization.IsModel.isCoverHollow_iff_not_hasRowAnchor` and
`Realization.IsModel.hasGlobalRowAnchor_iff_hasRowAnchor`).  [Kni26, Definition 5.4.2, p. 56]
defines hollowness only for models of characteristic arity `0 < K ≤ ∞`; this statement has no
such hypothesis, and characteristic arity has no counterpart here.  The existential form absorbs
the distinction of bounds between row anchors and anchors at the top (`K` to `K + 1` forward,
`N` to `N` conversely); no equivalence with anchors at the top at one bound is stated. -/
theorem IsModel.isCoverHollow_iff_not_hasGlobalRowAnchor {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsModel) :
    R.IsCoverHollow ↔ ¬ R.HasGlobalRowAnchor := by
  rw [hR.isCoverHollow_iff_not_hasRowAnchor, hR.hasGlobalRowAnchor_iff_hasRowAnchor]

end Realization

end VaughtConjecture
