/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OwnerwiseDecoding
import VaughtConjecture.Extension.SourcePrefix

/-!
# Locality of inherited long rows

Roadmap, Layer 3, 3.1 (the section theorem: inherited owners carry the rows of the original
schemes literally, and their long-row locality is the mapped locality, transported along the exact
base table) and 3.1, (R6), checkpoint 2.4 (the locality of inherited long rows explicit); semantic
contract, item 3.

A construction keeps the cells of its input schemes, with their rows, along a lower embedding `φ`
of an input scheme `E` into the constructed scheme `D` along which the rows `R` of `D` pull back to
the rows `Q` of `E` (`R.comap hφ = Q`); the cells outside the range of `φ` are the new cells.  The
rows of the inherited cells may be long (not short at their grades): legality bounds their entries
only below `ω ^ 2`.

* **Which rows are inherited**: the row of an inherited cell `φ s` at the image `φ t` of a cell
  below `s` is the row of `s` at `t` (`CellScheme.Rows.row_of_comap_eq`), and every cell below
  `φ s` is such an image (`CellScheme.IsLowerEmbedding.image_below_gradedIndex`).
* **Locality is local**: the locality of a labelling `w` at a cell `s` depends only on the values
  of `w` at the cells below `s` (`CellScheme.Rows.locality_congr`); at an inherited cell `φ s` it
  is the locality of `w ∘ φ` at `s` for the inherited rows (`CellScheme.Rows.locality_comap_iff`).
  Transformations transport along equivalences of the cells in both directions
  (`Label.transformsTo_comp_equiv_iff`).
* **Long-row locality from the exact base table**
  (`CellScheme.Rows.locality_of_eq_on_below`): if `w` agrees, at the images of the cells below
  `s`, with a lawful section `S` of the inherited rows (the exact base table), the locality of `w`
  holds at `φ s`, whatever the row: no shortness of the row and no bottom reflection is used.
* **The section theorem along a lower embedding**
  (`CellScheme.Rows.IsLawful.map_of_isLowerEmbedding`): for a lawful section `q` of `D` on cells
  of grade at most `K` and a witness `ν` bounded by grade `K`, the decoded section `ν ∘ q` is lawful
  when every new cell has a short row and `ν ∘ q ∘ φ` is a lawful section `S` of the inherited
  rows.  The strongly coded decoder is the instance
  `CellScheme.Rows.IsLawful.strongDecode_of_isLowerEmbedding`, and a completion below the full
  grade of a seed, with the amalgam as the inherited scheme and the cells of full scope as the new
  cells, the instance `CompletionBelowFullGrade.isLawful_map`.

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Lawful sections are [Kni26, Definition 2.5.4], and transformations and witnesses
[Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-- **Transformations along an equivalence of cells**: a labelling transforms to another exactly
when their compositions with an equivalence of cells do. -/
theorem Label.transformsTo_comp_equiv_iff {D D' : Type*} {grade : D → ℕ} {p q : D → Label.{u}}
    (e : D' ≃ D) : TransformsTo (grade ∘ e) (p ∘ e) (q ∘ e) ↔ TransformsTo grade p q := by
  refine ⟨fun ⟨g, σ, hw, h⟩ ↦ ⟨g, σ, hw, fun d ↦ ?_⟩, fun h ↦ h.reindex e⟩
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h (e.symm d)

namespace CellScheme.Rows

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β} {R : D.Rows.{u}}
  {Q : E.Rows.{u}} {φ : κ → ι}

/-- **Locality is local**: the locality of a labelling at a cell depends only on its values at the
cells below that cell.  It is used in the recursion on the grade, where a lawful labelling is
changed only away from the cells below an inherited owner. -/
theorem locality_congr {w w' : ι → Label.{u}} {s : ι}
    (hw : ∀ d ∈ D.below (D.gradedIndex s), w d = w' d) :
    TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
        (fun d ↦ min (w d) (w s)) ↔
      TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
        (fun d ↦ min (w' d) (w' s)) := by
  have he : (fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s)) =
      fun d : D.below (D.gradedIndex s) ↦ min (w' d) (w' s) :=
    funext fun d ↦ by rw [hw d d.2, hw s (D.mem_below_gradedIndex s)]
  rw [he]

/-- **The rows inherited along a lower embedding**: if the rows pull back to `Q`, the row of an
inherited cell `φ s` at the image `φ t` of a cell below `s` is the row of `s` at `t`. -/
theorem row_of_comap_eq (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q) (s : κ)
    (t : E.below (E.gradedIndex s)) : R.row (φ s) ⟨φ t, (hφ.le_iff t s).mpr t.2⟩ = Q.row s t := by
  subst hRQ
  rfl

/-- **Locality at an inherited cell**: along a lower embedding, the locality of a labelling `w` at
the inherited cell `φ s` is the locality of `w ∘ φ` at `s` for the pulled-back rows, since the
cells below `φ s` are the images of the cells below `s`. -/
theorem locality_comap_iff (hφ : E.IsLowerEmbedding D φ) (w : ι → Label.{u}) (s : κ) :
    TransformsTo (fun d : D.below (D.gradedIndex (φ s)) ↦ D.grade d) (R.row (φ s))
        (fun d ↦ min (w d) (w (φ s))) ↔
      TransformsTo (fun t : E.below (E.gradedIndex s) ↦ E.grade t) ((R.comap hφ).row s)
        (fun t ↦ min (w (φ t)) (w (φ s))) := by
  set e := hφ.belowEquiv (hφ.image_below_gradedIndex s)
  have hg : (fun t : E.below (E.gradedIndex s) ↦ E.grade t) =
      (fun d : D.below (D.gradedIndex (φ s)) ↦ D.grade d) ∘ e :=
    funext fun t ↦ (hφ.grade_eq t).symm
  rw [hg]
  exact (Label.transformsTo_comp_equiv_iff e).symm

/-- **Long-row locality from the exact base table.**  Let the rows pull back to `Q` along the
lower embedding `φ`, and let `S` be a lawful section of `Q`.  If a labelling `w` of the cells of
`D` agrees with `S` at the images of the cells below `s`, its locality holds at the inherited cell
`φ s`, whatever the row of `φ s`: neither shortness of the row nor bottom reflection of a decoder
is used.  It is the branch of the mapped locality of an inherited owner in the section theorem of
the completion of the coatom amalgam, at its small arities and in its recursion on the grade. -/
theorem locality_of_eq_on_below (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q)
    {S : κ → Label.{u}} (hS : Q.IsLawful S) (s : κ) {w : ι → Label.{u}}
    (hw : ∀ t : E.below (E.gradedIndex s), w (φ t) = S t) :
    TransformsTo (fun d : D.below (D.gradedIndex (φ s)) ↦ D.grade d) (R.row (φ s))
      (fun d ↦ min (w d) (w (φ s))) := by
  rw [locality_comap_iff hφ w s, hRQ]
  have hs : w (φ s) = S s := hw ⟨s, E.mem_below_gradedIndex s⟩
  simp only [hw, hs]
  exact hS.locality s

/-- **The section theorem along a lower embedding.**  Let `q` be a lawful section of `D`, on cells
of grade at most `K`, `ν` a witness bounded by grade `K`, and `φ` a lower embedding along which the
rows pull back to `Q`.  If every new cell (outside the range of `φ`) has a row short at its grade
and the decoded labels `ν ∘ q` at the inherited cells form a lawful section `S` of `Q` (the exact
base table), then `ν ∘ q` is lawful.  It is the section theorem of the completion of the coatom
amalgam, at its small arities and in its recursion on the grade: new owners take the shortness
branch, inherited owners the branch of the mapped locality, by
`CellScheme.Rows.locality_of_eq_on_below`. -/
theorem IsLawful.map_of_isLowerEmbedding {q : ι → Label.{u}} (hq : R.IsLawful q) {K : ℕ}
    (hK : ∀ d, D.grade d ≤ K) {ν : Label.{u} → Label.{u}} (hν : IsWitness (stepSuppressor K) ν)
    (hφ : E.IsLowerEmbedding D φ) (hRQ : R.comap hφ = Q) {S : κ → Label.{u}} (hS : Q.IsLawful S)
    (hnew : ∀ c ∉ Set.range φ, ∀ t, IsShort (D.grade c) (R.row c t))
    (hbase : ∀ t, ν (q (φ t)) = S t) : R.IsLawful (ν ∘ q) :=
  hq.map_of_isShort_or hK hν fun s ↦ by
    by_cases hs : s ∈ Set.range φ
    · obtain ⟨s, rfl⟩ := hs
      exact .inr (locality_of_eq_on_below hφ hRQ hS s (w := ν ∘ q) fun t ↦ hbase t)
    · exact .inl (hnew s hs)

/-- **Ownerwise decoding along a lower embedding**: the section theorem along a lower embedding for
the strongly coded decoder `strongDecode V K`, which does not reflect bottom.  It proves the
lawfulness of the decoded source section in the completion of the coatom amalgam. -/
theorem IsLawful.strongDecode_of_isLowerEmbedding {q : ι → Label.{u}} (hq : R.IsLawful q)
    {K : ℕ} (hK : ∀ d, D.grade d ≤ K) {V : Finset Label.{u}} (hφ : E.IsLowerEmbedding D φ)
    (hRQ : R.comap hφ = Q) {S : κ → Label.{u}} (hS : Q.IsLawful S)
    (hnew : ∀ c ∉ Set.range φ, ∀ t, IsShort (D.grade c) (R.row c t))
    (hbase : ∀ t, strongDecode V K (q (φ t)) = S t) : R.IsLawful (strongDecode V K ∘ q) :=
  hq.map_of_isLowerEmbedding hK isWitness_strongDecode hφ hRQ hS hnew hbase

end CellScheme.Rows

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)

/-- **The section theorem of a completion below the full grade.**  For a lawful section `q` of the
completed scheme, on cells of grade at most `K`, and a witness `ν` bounded by grade `K`: if every
cell of full scope has a row short at its grade and `ν ∘ q` reads, on the old cells, a lawful
section `S` of the amalgam (the exact base table), then `ν ∘ q` is lawful.  The old cells keep the
rows of the amalgam, which may be long; their locality is the locality of `S`. -/
theorem isLawful_map {q : Fin F.scheme.card → Label.{u}} (hq : F.scheme.rows.IsLawful q) {K : ℕ}
    (hK : ∀ d, F.scheme.toCellScheme.grade d ≤ K) {ν : Label.{u} → Label.{u}}
    (hν : IsWitness (stepSuppressor K) ν) {S : Fin I.amalgam.card → Label.{u}}
    (hS : I.amalgam.rows.IsLawful S)
    (hnew : ∀ c, F.scheme.toCellScheme.scope c = univ →
      ∀ t, IsShort (F.scheme.toCellScheme.grade c) (F.scheme.rows.row c t))
    (hbase : ∀ d, ν (q (F.embed d)) = S d) : F.scheme.rows.IsLawful (ν ∘ q) :=
  hq.map_of_isLowerEmbedding hK hν F.isLowerEmbedding F.comap_rows hS
    (fun c hc ↦ hnew c (by_contra fun h ↦ hc (F.mem_range_embed c h))) hbase

end CompletionBelowFullGrade

end VaughtConjecture
