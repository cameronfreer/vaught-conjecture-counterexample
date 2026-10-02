/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CompletionBelowFullGrade
import VaughtConjecture.Extension.GradeCut

/-!
# Source prefixes

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (carrying lawful sections across source prefixes);
Layer 3, 3.1 (the section theorem: a source section of the constructed scheme below a grade);
semantic contract, item 3.

The completion of the coatom amalgam reads the sections it needs in smaller schemes: the amalgam
itself, at every pair whose face is not the ground set, and the scheme reached after the previous
grade, at every pair below that grade.  A **source prefix** at a pair `Z`
(`CellScheme.IsSourcePrefix E D φ Z`) is a lower embedding `φ` of a cell scheme `E` (the source)
into a cell scheme `D` over the same points that keeps scopes and whose image contains every cell
of `D` below `Z`.  Below every pair `X ≤ Z` the cells of `D` are then exactly the images of the
cells of `E` (`IsSourcePrefix.image_below`), identified by `IsSourcePrefix.belowEquiv`, and the rows
of `D` pulled back along `φ` are the rows of `E` there.

* **Carrying lawful sections**: below `X ≤ Z` a labelling is lawful for `D` exactly when its
  transport is lawful for the pulled-back rows (`IsSourcePrefix.isLawfulBelow_iff`), so a
  labelling lawful below `X` in the source is carried to one lawful below `X` in `D` that reads it
  literally at every image cell (`IsSourcePrefix.exists_isLawfulBelow`).  In the other direction,
  along any lower embedding that keeps scopes, a labelling lawful below any pair restricts to one
  lawful below the same pair in the source (`CellScheme.Rows.IsLawfulBelow.comap_of_scope_eq`).
* **Carrying lifts**: between pairs below `Z` the rows of `D` lift capped exactly when the
  pulled-back rows do (`IsSourcePrefix.cappedLift_iff`), with the cap kept at every cell below the
  target, not only at the prescribed cells (`IsSourcePrefix.exists_lift`); bountiful pulled-back
  rows give every lift of `D` between graded faces of the source below `Z`
  (`IsSourcePrefix.cappedLift_of_isBountiful`).
* **Instances**: the identity (`IsSourcePrefix.id`), composites (`IsSourcePrefix.comp`), smaller
  pairs (`IsSourcePrefix.mono`), a lower embedding whose image contains the cells of grade at most
  `g`, at every pair of grade `g` (`IsSourcePrefix.of_grade_le`); the grade cut at `g`, at every
  pair of grade `g` (`isSourcePrefix_gradeCut`), and the inclusion of one grade cut in a higher
  one (`isSourcePrefix_gradeCut_mono`); and the old cells of a completion below the full grade of
  a seed, at every pair whose face is not the ground set
  (`CompletionBelowFullGrade.isSourcePrefix`).  For the last, the completion lifts capped at every
  pair of graded faces off the full face, because the amalgam does
  (`CompletionBelowFullGrade.cappedLift_iff`, `CompletionBelowFullGrade.cappedLift_of_ne_univ`):
  bountifulness of a completion is a statement about lifts to pairs on the full face only.

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Semantic rows and lawful sections are [Kni26, Definitions 2.5.3 and 2.5.4], and bountifulness is
[Kni26, Definition 2.5.14]; the amalgam is [Kni26, Definition 4.3.1], with its bountifulness
[Kni26, Lemma 4.3.2].
-/

universe u

namespace VaughtConjecture.CellScheme

open Finset Label

variable {ι κ μ α : Type*} {D : CellScheme ι α} {E : CellScheme κ α} {F : CellScheme μ α}
  {φ : κ → ι} {ψ : μ → κ} {X Y Z Z' : Finset α × ℕ} {g : ℕ}

/-- A **source prefix** at the pair `Z`: a lower embedding `φ` of the source `E` into `D`, over
the same points, that keeps scopes and whose image contains every cell of `D` below `Z`.  Below
every pair `X ≤ Z` the cells of `D` are then the images of the cells of `E`. -/
structure IsSourcePrefix (E : CellScheme κ α) (D : CellScheme ι α) (φ : κ → ι)
    (Z : Finset α × ℕ) : Prop where
  /-- The cell map is a lower embedding. -/
  isLowerEmbedding : E.IsLowerEmbedding D φ
  /-- The cell map keeps scopes. -/
  scope_eq (t : κ) : D.scope (φ t) = E.scope t
  /-- Every cell of `D` below `Z` is the image of a cell of the source. -/
  mem_range (d : ι) : D.gradedIndex d ≤ Z → d ∈ Set.range φ

namespace IsSourcePrefix

variable (h : E.IsSourcePrefix D φ Z)
include h

/-- A source prefix keeps graded indices. -/
theorem gradedIndex_eq (t : κ) : D.gradedIndex (φ t) = E.gradedIndex t :=
  Prod.ext (h.scope_eq t) (h.isLowerEmbedding.grade_eq t)

/-- The image of a cell lies below a pair exactly when the cell does. -/
theorem mem_below_iff (t : κ) : φ t ∈ D.below X ↔ t ∈ E.below X := by
  rw [mem_below, mem_below, h.gradedIndex_eq]

/-- The images of the cells of the source below any pair lie below that pair. -/
theorem image_below_subset (X : Finset α × ℕ) : φ '' E.below X ⊆ D.below X := by
  rintro _ ⟨t, ht, rfl⟩
  exact (h.mem_below_iff t).mpr ht

/-- **Below a pair `X ≤ Z`, the cells are those of the source**: the cells of `D` below `X` are
exactly the images of the cells of the source below `X`. -/
theorem image_below (hX : X ≤ Z) : φ '' E.below X = D.below X := by
  refine (h.image_below_subset X).antisymm fun d hd ↦ ?_
  obtain ⟨t, rfl⟩ := h.mem_range d (le_trans hd hX)
  exact ⟨t, (h.mem_below_iff t).mp hd, rfl⟩

/-- A source prefix at `Z` is a source prefix at every smaller pair. -/
protected theorem mono (hZ : Z' ≤ Z) : E.IsSourcePrefix D φ Z' :=
  ⟨h.isLowerEmbedding, h.scope_eq, fun d hd ↦ h.mem_range d (le_trans hd hZ)⟩

omit h in
/-- The identity is a source prefix at every pair. -/
protected theorem id (D : CellScheme ι α) (Z : Finset α × ℕ) : D.IsSourcePrefix D id Z :=
  ⟨IsLowerEmbedding.id D, fun _ ↦ rfl, fun d _ ↦ ⟨d, rfl⟩⟩

/-- **Composition**: a source prefix of a source prefix at `Z` is a source prefix at `Z`.  It is
used in the recursion on the grade to read the amalgam inside every scheme reached. -/
theorem comp (hψ : F.IsSourcePrefix E ψ Z) : F.IsSourcePrefix D (φ ∘ ψ) Z where
  isLowerEmbedding := h.isLowerEmbedding.comp hψ.isLowerEmbedding
  scope_eq t := (h.scope_eq (ψ t)).trans (hψ.scope_eq t)
  mem_range d hd := by
    obtain ⟨t, rfl⟩ := h.mem_range d hd
    obtain ⟨s, rfl⟩ := hψ.mem_range t (h.gradedIndex_eq t ▸ hd)
    exact ⟨s, rfl⟩

omit h in
/-- **A prefix at a grade.**  A lower embedding that keeps scopes and whose image contains every
cell of grade at most `g` is a source prefix at every pair of grade `g`.  It is used for the
scheme reached after the grade `g` inside every later scheme of the recursion on the grade. -/
theorem of_grade_le (hφ : E.IsLowerEmbedding D φ) (hscope : ∀ t, D.scope (φ t) = E.scope t)
    (hrange : ∀ d, D.grade d ≤ g → d ∈ Set.range φ) (C : Finset α) :
    E.IsSourcePrefix D φ (C, g) :=
  ⟨hφ, hscope, fun d hd ↦ hrange d hd.2⟩

/-! ### Carrying lawful sections and lifts -/

/-- Below a pair `X ≤ Z`, the cells of the source and those of `D`, identified by the cell map. -/
noncomputable def belowEquiv (hX : X ≤ Z) : E.below X ≃ D.below X :=
  h.isLowerEmbedding.belowEquiv (h.image_below hX)

/-- The identification of the cells below a pair `X ≤ Z` is the cell map. -/
@[simp] theorem coe_belowEquiv (hX : X ≤ Z) (t : E.below X) : (h.belowEquiv hX t : ι) = φ t :=
  rfl

variable {R : D.Rows.{u}}

/-- **Lawfulness below a pair `X ≤ Z`** is the same for `D` and for the source with the
pulled-back rows, along the identification of the cells below `X`.  It is used to carry a lawful
section between the scheme reached after a grade and the next one. -/
theorem isLawfulBelow_iff (hX : X ≤ Z) {r : D.below X → Label.{u}} :
    (R.comap h.isLowerEmbedding).IsLawfulBelow X (r ∘ h.belowEquiv hX) ↔ R.IsLawfulBelow X r :=
  Rows.isLawfulBelow_comap_iff _ _

/-- **Carrying a lawful section across a source prefix.**  A labelling lawful below `X ≤ Z` for
the pulled-back rows is carried to a labelling lawful below `X` for `D` that reads it literally at
the image of every cell.  It is used in the one-grade step to place a prescription of the scheme
reached after the previous grade in the next one. -/
theorem exists_isLawfulBelow (hX : X ≤ Z) {s : E.below X → Label.{u}}
    (hs : (R.comap h.isLowerEmbedding).IsLawfulBelow X s) :
    ∃ r : D.below X → Label.{u}, R.IsLawfulBelow X r ∧ ∀ t, r (h.belowEquiv hX t) = s t := by
  refine ⟨s ∘ (h.belowEquiv hX).symm, (h.isLawfulBelow_iff hX).mp ?_, fun t ↦ ?_⟩
  · simpa [Function.comp_assoc] using hs
  · simp

/-- **Lifts across a source prefix**: between pairs `X ≤ Y ≤ Z`, the rows of `D` lift capped
exactly when the pulled-back rows do.  It is used in the recursion on the grade to obtain the
lifts of each scheme below the grade being built from those of the scheme reached before. -/
theorem cappedLift_iff (hXY : X ≤ Y) (hY : Y ≤ Z) :
    (R.comap h.isLowerEmbedding).CappedLift hXY ↔ R.CappedLift hXY :=
  Rows.cappedLift_comap_iff _ (h.image_below (hXY.trans hY)) (h.image_below hY) rfl

/-- **A lift across a source prefix, coordinate by coordinate.**  If the pulled-back rows lift
capped from `X` to `Y ≤ Z`, then for a cap `c` self-visible at the grade of `Y`, a prescription `p`
lawful below `X`, and an ambient `q` lawful below `Y` with the same observation at `c` below `X`,
some `r` lawful below `Y` for `D` reads `p` literally below `X` and keeps the observation of `q` at
`c` at every cell below `Y`, not only at the cells of `X`.  It is the form in which the recursion on
the grade uses the lifts of the scheme reached before. -/
theorem exists_lift (hXY : X ≤ Y) (hYZ : Y ≤ Z) (hl : (R.comap h.isLowerEmbedding).CappedLift hXY)
    {c : Label.{u}} (hc : IsSelfVisible Y.2 c) {p : D.below X → Label.{u}}
    {q : D.below Y → Label.{u}} (hp : R.IsLawfulBelow X p) (hq : R.IsLawfulBelow Y q)
    (hpq : ∀ d, min (q (Set.inclusion (D.below_mono hXY) d)) c = min (p d) c) :
    ∃ r : D.below Y → Label.{u}, R.IsLawfulBelow Y r ∧ (∀ d, min (r d) c = min (q d) c) ∧
      ∀ d, r (Set.inclusion (D.below_mono hXY) d) = p d :=
  (Rows.cappedLift_iff_forall_exists hXY).mp ((h.cappedLift_iff hXY hYZ).mp hl) c hc p q hp hq hpq

/-- **Lifts from a bountiful source**: if the pulled-back rows are bountiful, the rows of `D` lift
capped between any two graded faces `X ≤ Y` of the source with `Y ≤ Z`. -/
theorem cappedLift_of_isBountiful (hE : (R.comap h.isLowerEmbedding).IsBountiful)
    (hX : X ∈ E.gradedFaces) (hY : Y ∈ E.gradedFaces) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    R.CappedLift hXY :=
  (h.cappedLift_iff hXY hYZ).mp (hE hX hY hXY)

end IsSourcePrefix

/-! ### Restricting lawful sections to the source -/

/-- A lower embedding that keeps scopes keeps graded indices. -/
theorem IsLowerEmbedding.gradedIndex_eq_of_scope_eq (hφ : E.IsLowerEmbedding D φ)
    (hscope : ∀ t, D.scope (φ t) = E.scope t) (t : κ) : D.gradedIndex (φ t) = E.gradedIndex t :=
  Prod.ext (hscope t) (hφ.grade_eq t)

/-- Along a lower embedding that keeps scopes, the image of a cell below a pair lies below it. -/
theorem IsLowerEmbedding.mem_below_of_scope_eq (hφ : E.IsLowerEmbedding D φ)
    (hscope : ∀ t, D.scope (φ t) = E.scope t) {t : κ} (ht : t ∈ E.below X) : φ t ∈ D.below X :=
  (show D.gradedIndex (φ t) ≤ X from hφ.gradedIndex_eq_of_scope_eq hscope t ▸ ht)

/-- Along a lower embedding that keeps scopes, the induced map of the cells below a pair is a lower
embedding of the schemes of cells below it. -/
theorem IsLowerEmbedding.below_of_scope_eq (hφ : E.IsLowerEmbedding D φ)
    (hscope : ∀ t, D.scope (φ t) = E.scope t) (X : Finset α × ℕ) :
    (E.reindex ((↑) : E.below X → κ)).IsLowerEmbedding (D.reindex ((↑) : D.below X → ι))
      (fun t ↦ ⟨φ t, hφ.mem_below_of_scope_eq hscope t.2⟩) := by
  refine ⟨fun a b hab ↦ Subtype.ext (hφ.injective (Subtype.mk.inj hab)), fun t ↦ hφ.grade_eq t,
    fun a b ↦ hφ.le_iff a b, fun t d hd ↦ ?_⟩
  obtain ⟨s, hs⟩ := hφ.mem_range t d hd
  have hsX : E.gradedIndex s ≤ X := by
    rw [← hφ.gradedIndex_eq_of_scope_eq hscope s, hs]
    exact d.2
  exact ⟨⟨s, hsX⟩, Subtype.ext hs⟩

/-- **Restricting a lawful labelling to the source**: along a lower embedding that keeps scopes, a
labelling lawful below any pair restricts to one lawful below the same pair for the pulled-back
rows.  It is used in the one-grade step to read an ambient section of the scheme being built in
the scheme reached before. -/
theorem Rows.IsLawfulBelow.comap_of_scope_eq {R : D.Rows.{u}} (hφ : E.IsLowerEmbedding D φ)
    (hscope : ∀ t, D.scope (φ t) = E.scope t) {r : D.below X → Label.{u}}
    (hr : R.IsLawfulBelow X r) :
    (R.comap hφ).IsLawfulBelow X fun t ↦ r ⟨φ t, hφ.mem_below_of_scope_eq hscope t.2⟩ :=
  (Rows.isLawfulBelow_iff.mp hr).comap (hφ.below_of_scope_eq hscope X)

/-! ### Instances -/

variable (D) in
/-- **The grade cut is a source prefix** at every pair of its grade. -/
theorem isSourcePrefix_gradeCut (C : Finset α) (g : ℕ) :
    (D.gradeCut g).IsSourcePrefix D Subtype.val (C, g) :=
  ⟨IsLowerEmbedding.gradeCut D g, fun _ ↦ rfl, fun d hd ↦ ⟨⟨d, hd.2⟩, rfl⟩⟩

variable (D) in
/-- **Nested grade cuts**: for `g ≤ g'`, the grade cut at `g` is a source prefix of the grade cut
at `g'` at every pair of grade `g`. -/
theorem isSourcePrefix_gradeCut_mono {g g' : ℕ} (hgg : g ≤ g') (C : Finset α) :
    (D.gradeCut g).IsSourcePrefix (D.gradeCut g')
      (fun d : {d // D.grade d ≤ g} ↦ (⟨d.1, d.2.trans hgg⟩ : {d // D.grade d ≤ g'})) (C, g) :=
  ⟨IsLowerEmbedding.gradeCut_mono D hgg, fun _ ↦ rfl, fun d hd ↦ ⟨⟨d.1, hd.2⟩, rfl⟩⟩

end VaughtConjecture.CellScheme

namespace VaughtConjecture.CompletionBelowFullGrade

open Finset CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  {X Y : Finset (Fin (m + 2)) × ℕ}

/-- **The amalgam is a source prefix of a completion** at every pair whose face is not the ground
set: the cells below such a pair have proper scope, so they are old. -/
theorem isSourcePrefix (hX : X.1 ≠ univ) :
    I.amalgam.toCellScheme.IsSourcePrefix F.scheme.toCellScheme F.embed X :=
  ⟨F.isLowerEmbedding, F.scope_embed, fun d hd ↦ F.mem_range_embed d fun he ↦
    hX (univ_subset_iff.mp (he ▸ (hd.1 : F.scheme.toCellScheme.scope d ⊆ X.1)))⟩

/-- **Lifts off the full face**: between pairs `X ≤ Y` whose larger face is not the ground set, the
rows of a completion lift capped exactly when those of the amalgam do. -/
theorem cappedLift_iff (hXY : X ≤ Y) (hY : Y.1 ≠ univ) :
    F.scheme.rows.CappedLift hXY ↔ I.amalgam.rows.CappedLift hXY := by
  rw [← F.comap_rows]
  exact ((F.isSourcePrefix hY).cappedLift_iff hXY le_rfl).symm

/-- **A completion lifts off the full face**: between graded faces `X ≤ Y` with `Y` not on the
ground set, the rows of a completion below the full grade lift capped, since those of the amalgam
are bountiful.  So bountifulness of a completion is a statement about the lifts to pairs on the
full face; it is used in the recursion on the grade to reduce the bountifulness of each scheme
reached to those lifts. -/
theorem cappedLift_of_ne_univ (hX : X ∈ F.scheme.toCellScheme.gradedFaces)
    (hY : Y ∈ F.scheme.toCellScheme.gradedFaces) (hXY : X ≤ Y) (hYne : Y.1 ≠ univ) :
    F.scheme.rows.CappedLift hXY :=
  (F.cappedLift_iff hXY hYne).mpr (I.isBountiful ⟨F.faces_eq ▸ hX.1, hX.2⟩
    ⟨F.faces_eq ▸ hY.1, hY.2⟩ hXY)

end VaughtConjecture.CompletionBelowFullGrade
