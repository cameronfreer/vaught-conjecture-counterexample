/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Transform
import VaughtConjecture.Scheme.Cell

/-!
# Semantic rows and lawful sections

Roadmap, Layer 1 (semantic rows and lawful sections; the order, availability, and locality laws;
restriction, transport, pullback, and the bottom cases); semantic contract, item 3; the
expositions, §1 (semantic rows constrain which labellings are lawful).

The **semantic rows** of a cell scheme `D` (`CellScheme.Rows D`) are raw data: for every cell `s`
a labelling `R.row s` of the cells below `s`, that is, of `D.below (D.gradedIndex s)`.  A labelling
`p : ι → Label` of all cells is a **lawful section** of the rows (`Rows.IsLawful R p`) when it
satisfies three laws:

* **order**: every label `p d` is self-visible at the grade of its cell;
* **locality**: for every cell `s`, the row `R.row s` transforms (`Label.TransformsTo`, over the
  grades of the cells below `s`) to the section below `s` capped at the label of `s`,
  `d ↦ min (p d) (p s)`;
* **availability**: if the scope of `s` lies in the scope of `t` and the grades agree, then some
  cell `u` with the graded index of `t` has `p s ≤ p u`.  Availability quantifies over all cells
  with a given graded index, so it depends on the multiplicities of cells.

Rows pull back along a lower embedding of schemes (`Rows.comap`), and lawful sections pull back
with them (`IsLawful.comap`).  Instances are the restriction to a face (`Rows.restrict`,
`IsLawful.restrict`), the pullback along an embedding of ground sets, reindexing along an
equivalence of cells (in both directions, `isLawful_comap_reindex_iff`), and the lower sets:
a labelling `r` of the cells below a pair `X` is *lawful below `X`* (`Rows.IsLawfulBelow R X r`)
when it is a lawful section of the rows restricted to the scheme `D⟨X⟩` of cells below `X`.  Lawful
sections restrict to every lower set (`IsLawful.isLawfulBelow`) and from a lower set to a smaller
one (`IsLawfulBelow.mono`).

The constant bottom labelling is lawful for all rows (`isLawful_bot`), and a cell whose row is
bottom at the cell itself has bottom label in every lawful section
(`IsLawful.eq_bot_of_row_self_eq_bot`).  The rows are **consistent** (`Rows.IsConsistent`) when
each row `R.row s` is lawful below the graded index of `s`; consistent rows are orderly
(`IsConsistent.isOrderly`) and consistency pulls back along lower embeddings
(`IsConsistent.comap`).  Since the bottom labelling is always lawful, the mere existence of lawful
sections carries no information; consistency is the statement about the rows themselves.
-/

universe u

namespace VaughtConjecture.CellScheme

open Label

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β}

/-- The **semantic rows** of a cell scheme: for every cell `s`, a labelling `row s` of the cells
below `s`. -/
@[ext]
structure Rows (D : CellScheme ι α) where
  /-- The semantic row of a cell: a labelling of the cells below it. -/
  row (s : ι) : D.below (D.gradedIndex s) → Label.{u}

namespace Rows

variable (R : D.Rows) {φ : κ → ι}

/-- Values of a row at equal cells and equal arguments are equal. -/
theorem row_congr {s s' : ι} (hs : s = s') {t : D.below (D.gradedIndex s)}
    {t' : D.below (D.gradedIndex s')} (ht : t.1 = t'.1) : R.row s t = R.row s' t' := by
  subst hs
  rw [Subtype.ext ht]

/-- The rows are *orderly*: every value of the row of `s` at a cell `t` is self-visible at the
grade of `t`. -/
def IsOrderly : Prop :=
  ∀ s (t : D.below (D.gradedIndex s)), IsSelfVisible (D.grade t) (R.row s t)

/-- The pullback of rows along a lower embedding `φ` of `E` into `D`: the row of `s` at `t` is
the row of `φ s` at `φ t`. -/
def comap (hφ : E.IsLowerEmbedding D φ) : E.Rows where
  row s t := R.row (φ s) ⟨φ t, (hφ.le_iff t s).mpr t.2⟩

/-- The row of a pulled-back cell. -/
@[simp] theorem comap_row (hφ : E.IsLowerEmbedding D φ) (s : κ) (t : E.below (E.gradedIndex s)) :
    (R.comap hφ).row s t = R.row (φ s) ⟨φ t, (hφ.le_iff t s).mpr t.2⟩ := rfl

/-- Pulling back along the identity does not change the rows. -/
@[simp] theorem comap_id : R.comap (IsLowerEmbedding.id D) = R := rfl

/-- The rows of the restriction of a scheme to a face: the rows of the visible cells. -/
def restrict [DecidableEq α] (B : Finset α) : (D.restrict B).Rows :=
  R.comap (IsLowerEmbedding.restrict D B)

/-! ### Lawful sections -/

/-- A labelling `p` of the cells is a **lawful section** of the rows `R`: it satisfies the order,
locality, and availability laws. -/
structure IsLawful (p : ι → Label.{u}) : Prop where
  /-- Order: the label of every cell is self-visible at the grade of the cell. -/
  orderly (d : ι) : IsSelfVisible (D.grade d) (p d)
  /-- Locality: the row of every cell `s` transforms, over the grades of the cells below `s`, to
  the labelling `d ↦ min (p d) (p s)` of the cells below `s`. -/
  locality (s : ι) : TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
    (fun d ↦ min (p d) (p s))
  /-- Availability: if the scope of `s` lies in the scope of `t` and their grades agree, then
  some cell with the graded index of `t` has a label at least that of `s`. -/
  availability (s t : ι) : D.scope s ⊆ D.scope t → D.grade s = D.grade t →
    ∃ u, D.gradedIndex u = D.gradedIndex t ∧ p s ≤ p u

/-- A labelling `r` of the cells below `X` is *lawful below `X`*: it is a lawful section of the
rows restricted to the scheme `D⟨X⟩` of cells below `X`. -/
def IsLawfulBelow (X : Finset α × ℕ) (r : D.below X → Label.{u}) : Prop :=
  (R.comap (IsLowerEmbedding.subtypeVal_below D X)).IsLawful r

/-- The rows are **consistent**: the row of every cell `s` is lawful below the graded index of
`s`. -/
def IsConsistent : Prop := ∀ s, R.IsLawfulBelow (D.gradedIndex s) (R.row s)

variable {R}

/-- The constant bottom labelling is a lawful section of all rows. -/
theorem isLawful_bot : R.IsLawful fun _ ↦ ⊥ where
  orderly _ := isSelfVisible_bot _
  locality s := by simpa only [min_self] using TransformsTo.bot _ (R.row s)
  availability _ t _ _ := ⟨t, rfl, le_rfl⟩

/-- The constant bottom labelling is lawful below every pair. -/
theorem isLawfulBelow_bot (X : Finset α × ℕ) : R.IsLawfulBelow X fun _ ↦ ⊥ := isLawful_bot

/-- Every labelling of a scheme without cells is lawful. -/
theorem isLawful_of_isEmpty [IsEmpty ι] (p : ι → Label.{u}) : R.IsLawful p where
  orderly d := isEmptyElim d
  locality s := isEmptyElim s
  availability s := isEmptyElim s

namespace IsLawful

variable {p : ι → Label.{u}}

/-- A cell whose row is bottom at the cell itself has bottom label in every lawful section. -/
theorem eq_bot_of_row_self_eq_bot (h : R.IsLawful p) (s : ι)
    (hs : R.row s ⟨s, D.mem_below_gradedIndex s⟩ = ⊥) : p s = ⊥ := by
  simpa using (h.locality s).eq_bot (d := ⟨s, D.mem_below_gradedIndex s⟩) hs

/-- **Pullback of lawful sections**: along a lower embedding `φ`, a lawful section `p` of `R`
pulls back to the lawful section `p ∘ φ` of the pulled-back rows. -/
theorem comap (h : R.IsLawful p) (hφ : E.IsLowerEmbedding D φ) :
    (R.comap hφ).IsLawful (p ∘ φ) where
  orderly t := hφ.grade_eq t ▸ h.orderly (φ t)
  locality s := by
    have hg : (fun t : E.below (E.gradedIndex s) ↦ E.grade t) =
        (fun d : D.below (D.gradedIndex (φ s)) ↦ D.grade d) ∘
          fun t : E.below (E.gradedIndex s) ↦
            (⟨φ t, (hφ.le_iff t s).mpr t.2⟩ : D.below (D.gradedIndex (φ s))) :=
      funext fun t ↦ (hφ.grade_eq t).symm
    rw [hg]
    exact (h.locality (φ s)).reindex _
  availability s t hst hg := by
    have hle : D.gradedIndex (φ s) ≤ D.gradedIndex (φ t) :=
      (hφ.le_iff s t).mpr ((gradedIndex_le_iff E).mpr ⟨hst, hg.le⟩)
    obtain ⟨u, hu, hpu⟩ := h.availability (φ s) (φ t) hle.1
      (by rw [hφ.grade_eq, hφ.grade_eq, hg])
    obtain ⟨u', rfl⟩ := hφ.mem_range t u hu.le
    exact ⟨u', (hφ.gradedIndex_eq_iff u' t).mp hu, hpu⟩

/-- **Restriction to a face**: a lawful section restricts to a lawful section of the restricted
rows on the cells visible in the face. -/
theorem restrict [DecidableEq α] (h : R.IsLawful p) (B : Finset α) :
    (R.restrict B).IsLawful fun d ↦ p d :=
  h.comap (IsLowerEmbedding.restrict D B)

/-- A lawful section is lawful below every pair. -/
theorem isLawfulBelow (h : R.IsLawful p) (X : Finset α × ℕ) :
    R.IsLawfulBelow X fun d ↦ p d :=
  h.comap (IsLowerEmbedding.subtypeVal_below D X)

end IsLawful

/-- Rows pulled back along an equivalence of cells and then back along its inverse are the
original rows. -/
theorem comap_reindex_comap_symm (R : D.Rows) (e : κ ≃ ι)
    (he : D.IsLowerEmbedding (D.reindex e) e.symm) :
    (R.comap (IsLowerEmbedding.reindex D e)).comap he = R := by
  ext s t
  exact R.row_congr (e.apply_symm_apply s) (e.apply_symm_apply t)

/-- **Transport along an equivalence of cells**: `p ∘ e` is lawful for the reindexed rows exactly
when `p` is lawful. -/
theorem isLawful_comap_reindex_iff (e : κ ≃ ι) {p : ι → Label.{u}} :
    (R.comap (IsLowerEmbedding.reindex D e)).IsLawful (p ∘ e) ↔ R.IsLawful p := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comap _⟩
  have he : D.IsLowerEmbedding (D.reindex e) e.symm :=
    ⟨e.symm.injective, fun _ ↦ by simp, fun _ _ ↦ by simp, fun _ d _ ↦ e.symm.surjective d⟩
  have h' := h.comap he
  rwa [comap_reindex_comap_symm, Function.comp_assoc, e.self_comp_symm,
    Function.comp_id] at h'

namespace IsLawfulBelow

variable {X Y : Finset α × ℕ}

/-- **Restriction between lower sets**: a labelling lawful below `Y` restricts to one lawful
below every `X ≤ Y`. -/
theorem mono {q : D.below Y → Label.{u}} (h : R.IsLawfulBelow Y q) (hXY : X ≤ Y) :
    R.IsLawfulBelow X (q ∘ Set.inclusion (D.below_mono hXY)) :=
  IsLawful.comap h (IsLowerEmbedding.inclusion_below D hXY)

/-- A labelling lawful below a pair lying above every cell is a lawful section. -/
theorem isLawful {r : D.below X → Label.{u}} (h : R.IsLawfulBelow X r)
    (hX : ∀ d, d ∈ D.below X) : R.IsLawful fun d ↦ r ⟨d, hX d⟩ := by
  have hψ : D.IsLowerEmbedding (D.reindex ((↑) : D.below X → ι)) fun d ↦ ⟨d, hX d⟩ :=
    ⟨fun _ _ h ↦ congrArg Subtype.val h, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl,
      fun _ d _ ↦ ⟨d.1, rfl⟩⟩
  exact IsLawful.comap h hψ

end IsLawfulBelow

/-! ### Consistent rows -/

/-- For a lower embedding `φ` and a cell `s`, the induced map from the cells below `s` to the
cells below `φ s` is a lower embedding of the schemes of cells below them. -/
theorem _root_.VaughtConjecture.CellScheme.IsLowerEmbedding.below
    (hφ : E.IsLowerEmbedding D φ) (s : κ) :
    (E.reindex ((↑) : E.below (E.gradedIndex s) → κ)).IsLowerEmbedding
      (D.reindex ((↑) : D.below (D.gradedIndex (φ s)) → ι))
      (fun t ↦ ⟨φ t, (hφ.le_iff t s).mpr t.2⟩) := by
  refine ⟨fun a b h ↦ Subtype.ext (hφ.injective (congrArg Subtype.val h)),
    fun t ↦ hφ.grade_eq t, fun a b ↦ hφ.le_iff a b, fun t d hd ↦ ?_⟩
  obtain ⟨d', hd'⟩ := hφ.mem_range t d hd
  have hd's : E.gradedIndex d' ≤ E.gradedIndex s :=
    le_trans ((hφ.le_iff d' t).mp (hd' ▸ hd)) t.2
  exact ⟨⟨d', hd's⟩, Subtype.ext hd'⟩

namespace IsConsistent

/-- Consistent rows are orderly. -/
theorem isOrderly (hR : R.IsConsistent) : R.IsOrderly := fun s t ↦ (hR s).orderly t

/-- Consistency pulls back along lower embeddings. -/
theorem comap (hR : R.IsConsistent) (hφ : E.IsLowerEmbedding D φ) : (R.comap hφ).IsConsistent :=
  fun s ↦ IsLawful.comap (hR (φ s)) (hφ.below s)

/-- The restriction of consistent rows to a face is consistent. -/
theorem restrict [DecidableEq α] (hR : R.IsConsistent) (B : Finset α) :
    (R.restrict B).IsConsistent :=
  hR.comap (IsLowerEmbedding.restrict D B)

end IsConsistent

end Rows

end VaughtConjecture.CellScheme
