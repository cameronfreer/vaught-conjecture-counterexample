/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Extension.NormalForm
import VaughtConjecture.Scheme.Transport

/-!
# Grade cuts

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (carrying lawful sections across grade cuts, the
restrictions to the cells of grade at most a given grade); semantic contract, item 3.

The completion of the coatom amalgam is built grade by grade: the scheme reached after the grade
`g` has, below every pair of grade at most `g`, the cells it will have at the end.  The **grade
cut** of a cell scheme `D` at `g` (`CellScheme.gradeCut D g`) is the scheme of the cells of `D` of
grade at most `g`, with their scopes and grades, on the same ground set with the same faces.  Its
cells are the cells `d` with `D.grade d ≤ g`, so physical multiplicities are kept.  For semantic
rows `R` of `D`, the rows of the grade cut (`CellScheme.Rows.gradeCut R g`) are the rows of those
cells, read literally.

* **Literal restriction**: a cell of the grade cut has its scope, grade, graded index, and row
  (`gradeCut_scope`, `gradeCut_grade`, `gradedIndex_gradeCut`, `Rows.gradeCut_row`); the faces,
  ground set, and graded faces are those of `D` (`gradeCut_faces`, `gradeCut_ground`,
  `gradedFaces_gradeCut`).  The inclusion is a lower embedding
  (`IsLowerEmbedding.gradeCut`), and so is the inclusion of a grade cut in a higher one
  (`IsLowerEmbedding.gradeCut_mono`).  Below a pair of grade at most `g` the cells of the grade
  cut are those of `D` (`image_val_below_gradeCut`); below any pair `X` they are those of `D`
  below `(X.1, min X.2 g)` (`image_val_below_gradeCut_eq`).
* **Boundedness**: every cell of the grade cut has grade at most `g` (`gradeCut_grade_le`), the
  grade bound of the section theorem and of the normal forms, so the lawful sections of the grade
  cut have strongly coded normal forms at `g`
  (`CellScheme.Rows.IsLawful.exists_stronglyCoded_gradeCut`).  A well-formed scheme has a
  well-formed grade cut (`IsWellFormed.gradeCut`), with no cells at the grade `0`
  (`IsWellFormed.isEmpty_gradeCut_zero`); a complete scheme has a cell of the grade cut at every
  graded face of grade at most `g` (`IsComplete.exists_gradedIndex_gradeCut`).
* **Lawfulness**: lawful sections restrict to lawful sections of the grade cut
  (`CellScheme.Rows.IsLawful.gradeCut`), and below a pair of grade at most `g` a labelling is
  lawful for `D` exactly when it is lawful for the grade cut
  (`CellScheme.Rows.isLawfulBelow_gradeCut_iff`, along `gradeCutBelowEquiv`).
* **Consistency and coding**: consistent rows have consistent grade cuts
  (`CellScheme.Rows.IsConsistent.gradeCut`); coded and strongly coded rows have coded and strongly
  coded grade cuts, and the grade cut is coded exactly when the rows of the cells of grade at most
  `g` are (`CellScheme.Rows.isCoded_gradeCut_iff`).
* **Lifts**: between pairs of grade at most `g` the rows of `D` lift capped exactly when those of
  the grade cut do (`CellScheme.Rows.cappedLift_gradeCut_iff`), and a lift of `D` between the pairs
  lowered to the grade `g` is a lift of the grade cut (`CellScheme.Rows.CappedLift.gradeCut`).
  Bountiful rows have bountiful grade cuts at every positive grade
  (`CellScheme.Rows.IsBountiful.gradeCut`).

The bottom rows cut to the bottom rows (`CellScheme.Rows.gradeCut_bot`).

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Semantic rows and lawful sections are [Kni26, Definitions 2.5.3 and 2.5.4]; bountifulness is
[Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture.CellScheme

open Label

variable {ι α : Type*} (D : CellScheme ι α) {g g' : ℕ} {X Y : Finset α × ℕ}

/-! ### The grade cut of a scheme -/

/-- The **grade cut** of a scheme at grade `g`: its cells of grade at most `g`, with their scopes
and grades, on the same ground set with the same faces. -/
def gradeCut (g : ℕ) : CellScheme {d // D.grade d ≤ g} α := D.reindex Subtype.val

/-- The ground set of a grade cut is that of the scheme. -/
@[simp] theorem gradeCut_ground : (D.gradeCut g).ground = D.ground := rfl

/-- The faces of a grade cut are those of the scheme. -/
@[simp] theorem gradeCut_faces : (D.gradeCut g).faces = D.faces := rfl

/-- A cell of a grade cut has its scope in the scheme. -/
@[simp] theorem gradeCut_scope (d : {d // D.grade d ≤ g}) : (D.gradeCut g).scope d = D.scope d :=
  rfl

/-- A cell of a grade cut has its grade in the scheme. -/
@[simp] theorem gradeCut_grade (d : {d // D.grade d ≤ g}) : (D.gradeCut g).grade d = D.grade d :=
  rfl

/-- A cell of a grade cut has its graded index in the scheme. -/
@[simp] theorem gradedIndex_gradeCut (d : {d // D.grade d ≤ g}) :
    (D.gradeCut g).gradedIndex d = D.gradedIndex d :=
  rfl

/-- The graded faces of a grade cut are those of the scheme. -/
theorem gradedFaces_gradeCut : (D.gradeCut g).gradedFaces = D.gradedFaces := rfl

/-- **Boundedness**: every cell of the grade cut at `g` has grade at most `g`.  This is the grade
bound of the section theorem (`CellScheme.Rows.IsLawful.map_of_isShort_or`) and of the normal
forms, used in the one-grade step to decode and encode sections of the scheme reached after the
grade `g`. -/
theorem gradeCut_grade_le (d : {d // D.grade d ≤ g}) : (D.gradeCut g).grade d ≤ g := d.2

/-- **The grade cut is a lower set**: its inclusion is a lower embedding, since a cell below a cell
of grade at most `g` has grade at most `g`. -/
theorem IsLowerEmbedding.gradeCut (g : ℕ) :
    (D.gradeCut g).IsLowerEmbedding D Subtype.val :=
  ⟨Subtype.val_injective, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl, fun t d hd ↦ ⟨⟨d, hd.2.trans t.2⟩, rfl⟩⟩

/-- **Grade cuts are nested**: for `g ≤ g'`, the inclusion of the grade cut at `g` in the grade cut
at `g'` is a lower embedding.  It is used in the recursion on the grade to compare the scheme
reached after one grade with the scheme reached after the next. -/
theorem IsLowerEmbedding.gradeCut_mono (h : g ≤ g') :
    (D.gradeCut g).IsLowerEmbedding (D.gradeCut g')
      (fun d : {d // D.grade d ≤ g} ↦ (⟨d.1, d.2.trans h⟩ : {d // D.grade d ≤ g'})) :=
  ⟨fun _ _ he ↦ Subtype.ext (Subtype.mk.inj he), fun _ ↦ rfl, fun _ _ ↦ Iff.rfl,
    fun t d hd ↦ ⟨⟨d.1, (hd.2 : D.grade d.1 ≤ D.grade t.1).trans t.2⟩, rfl⟩⟩

/-- Below a pair of grade at most `g`, the cells of the grade cut at `g` are the cells of the
scheme. -/
theorem image_val_below_gradeCut (hX : X.2 ≤ g) :
    Subtype.val '' (D.gradeCut g).below X = D.below X := by
  ext d
  refine ⟨?_, fun hd ↦ ⟨⟨d, hd.2.trans hX⟩, hd, rfl⟩⟩
  rintro ⟨d, hd, rfl⟩
  exact hd

/-- Below any pair `X`, the cells of the grade cut at `g` are the cells of the scheme below the
pair `(X.1, min X.2 g)`, lowered to the grade `g`. -/
theorem image_val_below_gradeCut_eq (X : Finset α × ℕ) :
    Subtype.val '' (D.gradeCut g).below X = D.below (X.1, min X.2 g) := by
  ext d
  refine ⟨?_, fun hd ↦ ⟨⟨d, hd.2.trans (min_le_right _ _)⟩,
    ⟨hd.1, hd.2.trans (min_le_left _ _)⟩, rfl⟩⟩
  rintro ⟨d, hd, rfl⟩
  exact ⟨hd.1, le_min hd.2 d.2⟩

/-- Below a pair of grade at most `g`, the cells of the grade cut at `g` and those of the scheme,
identified by the inclusion. -/
noncomputable def gradeCutBelowEquiv (hX : X.2 ≤ g) : (D.gradeCut g).below X ≃ D.below X :=
  (IsLowerEmbedding.gradeCut D g).belowEquiv (D.image_val_below_gradeCut hX)

/-- The identification of the cells below a pair, in the grade cut and in the scheme, is the
inclusion. -/
@[simp] theorem coe_gradeCutBelowEquiv (hX : X.2 ≤ g) (d : (D.gradeCut g).below X) :
    (D.gradeCutBelowEquiv hX d : ι) = d.1.1 :=
  rfl

/-- A well-formed scheme has a well-formed grade cut. -/
theorem IsWellFormed.gradeCut [DecidableEq α] {D : CellScheme ι α} (hD : D.IsWellFormed)
    (g : ℕ) : (D.gradeCut g).IsWellFormed :=
  have := hD.finite
  hD.reindex _

/-- **The grade `0`**: the grade cut at `0` of a well-formed scheme has no cells, since every cell
has a positive grade. -/
theorem IsWellFormed.isEmpty_gradeCut_zero [DecidableEq α] {D : CellScheme ι α}
    (hD : D.IsWellFormed) : IsEmpty {d // D.grade d ≤ 0} :=
  ⟨fun d ↦ (hD.grade_pos d.1).ne' (Nat.le_zero.mp d.2)⟩

/-- **Completeness below the grade of the cut**: in a complete scheme, every graded face of grade
at most `g` is the graded index of a cell of the grade cut at `g`.  It is used in the one-grade
step to find, at a prescribed graded face, the cells among which its owner is chosen. -/
theorem IsComplete.exists_gradedIndex_gradeCut {D : CellScheme ι α} (hD : D.IsComplete)
    (hX : X ∈ D.gradedFaces) (hXg : X.2 ≤ g) :
    ∃ d : {d // D.grade d ≤ g}, (D.gradeCut g).gradedIndex d = X := by
  obtain ⟨d, hd⟩ := hD X hX
  exact ⟨⟨d, (congrArg Prod.snd hd).le.trans hXg⟩, hd⟩

/-! ### The rows of a grade cut -/

namespace Rows

variable {D} (R : D.Rows.{u})

/-- The rows of the grade cut at `g`: the rows of the cells of grade at most `g`, read literally. -/
def gradeCut (g : ℕ) : (D.gradeCut g).Rows := R.comap (IsLowerEmbedding.gradeCut D g)

/-- **Literal restriction of rows**: the row of a cell of the grade cut is its row in the scheme. -/
@[simp] theorem gradeCut_row (s : {d // D.grade d ≤ g})
    (t : (D.gradeCut g).below ((D.gradeCut g).gradedIndex s)) :
    (R.gradeCut g).row s t = R.row s ⟨t.1, t.2⟩ :=
  rfl

/-- The bottom rows cut to the bottom rows. -/
@[simp] theorem gradeCut_bot : (bot D : D.Rows.{u}).gradeCut g = bot (D.gradeCut g) := rfl

variable {R} {p : ι → Label.{u}}

/-- **Lawful sections restrict to the grade cut**: a lawful section of `R` is, on the cells of
grade at most `g`, a lawful section of the rows of the grade cut.  It is used in the one-grade
step to read the scheme reached after the grade `g` inside the next one. -/
theorem IsLawful.gradeCut (hp : R.IsLawful p) (g : ℕ) :
    (R.gradeCut g).IsLawful fun d ↦ p d :=
  hp.comap (IsLowerEmbedding.gradeCut D g)

/-- **Lawfulness below a pair of grade at most `g`** is the same for the scheme and for its grade
cut at `g`, along the identification of the cells below the pair.  It is used to carry lawful
sections of the scheme reached after the grade `g` into the next one, and back. -/
theorem isLawfulBelow_gradeCut_iff (hX : X.2 ≤ g) {r : D.below X → Label.{u}} :
    (R.gradeCut g).IsLawfulBelow X (r ∘ D.gradeCutBelowEquiv hX) ↔ R.IsLawfulBelow X r :=
  isLawfulBelow_comap_iff _ (D.image_val_below_gradeCut hX)

/-- **Consistent rows have consistent grade cuts.** -/
theorem IsConsistent.gradeCut (hR : R.IsConsistent) (g : ℕ) : (R.gradeCut g).IsConsistent :=
  hR.comap (IsLowerEmbedding.gradeCut D g)

/-- **Coded rows have coded grade cuts.** -/
theorem IsCoded.gradeCut (hR : R.IsCoded) (g : ℕ) : (R.gradeCut g).IsCoded :=
  hR.comap (IsLowerEmbedding.gradeCut D g)

/-- **Strongly coded rows have strongly coded grade cuts**, since the grades are kept. -/
theorem IsStronglyCoded.gradeCut (hR : R.IsStronglyCoded) (g : ℕ) :
    (R.gradeCut g).IsStronglyCoded :=
  hR.comap (IsLowerEmbedding.gradeCut D g)

/-- **Coding across the cut**: the grade cut at `g` is coded exactly when the rows of the cells of
grade at most `g` are.  It is used in the recursion on the grade to obtain the coding of the
scheme reached after each grade from the coding of its rows grade by grade. -/
theorem isCoded_gradeCut_iff :
    (R.gradeCut g).IsCoded ↔
      ∀ s, D.grade s ≤ g → ∀ t, R.row s t < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
  ⟨fun h s hs t ↦ h (s := ⟨s, hs⟩) (t := ⟨⟨t.1, t.2.2.trans hs⟩, t.2⟩), fun h s _ ↦ h s s.2 _⟩

/-- **Strongly coded normal forms on a grade cut.**  On finitely many cells, a lawful section of
the grade cut at `g` has a lawful normal form strongly coded at `g`, with values in the coded
alphabet with block bound `2 · #cells + 1` and offset bound `g + 1`, from which a witness bounded
by grade `g` recovers it (`CellScheme.Rows.IsLawful.exists_stronglyCoded`, with the grade bound
`gradeCut_grade_le`).  It is used in the one-grade step to give a new cell of grade `g` a strongly
coded row.  `CellScheme.Rows.IsLawfulBelow.exists_stronglyCoded` gives the same normal form below a
pair; this form is for a whole lawful section of the grade cut, the input of the section theorem on
the scheme reached after the grade `g`, whose cells need not all lie below one pair.  The normal
form is strongly coded at `g`, not short at `g`; whether a row taken from it is short at its grade,
as the section theorem needs for a new owner, is a property of the construction of that row. -/
theorem IsLawful.exists_stronglyCoded_gradeCut [Finite {d // D.grade d ≤ g}]
    {w : {d // D.grade d ≤ g} → Label.{u}} (hw : (R.gradeCut g).IsLawful w) :
    ∃ w' : {d // D.grade d ≤ g} → Label.{u}, (R.gradeCut g).IsLawful w' ∧
      (∀ d, Label.IsStronglyCoded g (w' d)) ∧
      (∀ d, w' d ∈ codedAlphabet (2 * Nat.card {d // D.grade d ≤ g} + 1) (g + 1)) ∧
      TransformsTo (D.gradeCut g).grade w w' ∧ TransformsTo (D.gradeCut g).grade w' w ∧
      ∃ ν, IsWitness (stepSuppressor g) ν ∧ ∀ d, ν (w' d) = w d :=
  hw.exists_stronglyCoded (D.gradeCut_grade_le)

/-! ### Lifts across a grade cut -/

/-- **Lifts below the grade of the cut**: between pairs of grade at most `g`, the rows lift capped
exactly when the rows of the grade cut at `g` do.  It is used in the recursion on the grade to
obtain the lifts below the grade being built from those of the scheme reached after the previous
grade. -/
theorem cappedLift_gradeCut_iff (h : X ≤ Y) (hY : Y.2 ≤ g) :
    (R.gradeCut g).CappedLift h ↔ R.CappedLift h :=
  cappedLift_comap_iff (IsLowerEmbedding.gradeCut D g) (D.image_val_below_gradeCut (h.2.trans hY))
    (D.image_val_below_gradeCut hY) rfl

/-- **Lifts of the grade cut from lifts lowered to the grade of the cut.**  A capped lift of the
rows between the pairs `X` and `Y` lowered to the grade `g`, `(X.1, min X.2 g)` and
`(Y.1, min Y.2 g)`, is a capped lift of the grade cut at `g` from `X` to `Y`: the cells of the
grade cut below `X` and `Y` are the cells of the scheme below the lowered pairs, and a cap
self-visible at the grade of `Y` is self-visible at the lower grade. -/
theorem CappedLift.gradeCut (h : X ≤ Y)
    (hl : R.CappedLift (X := (X.1, min X.2 g)) (Y := (Y.1, min Y.2 g))
      ⟨h.1, min_le_min_right g h.2⟩) :
    (R.gradeCut g).CappedLift h :=
  hl.comap (IsLowerEmbedding.gradeCut D g) (D.image_val_below_gradeCut_eq X)
    (D.image_val_below_gradeCut_eq Y) (min_le_left _ _)

/-- **Bountiful rows have bountiful grade cuts** at every positive grade `g`: a capped lift of the
grade cut between graded faces is a capped lift of the scheme between the graded faces lowered to
the grade `g`.  The grade `g` is positive so that the lowered pairs are graded faces; at the grade
`0` a well-formed scheme has an empty grade cut (`IsWellFormed.isEmpty_gradeCut_zero`). -/
theorem IsBountiful.gradeCut (hR : R.IsBountiful) (hg : 0 < g) : (R.gradeCut g).IsBountiful := by
  intro X Y hX hY h
  refine CappedLift.gradeCut h (hR ?_ ?_ _)
  · exact ⟨hX.1, lt_min hX.2.1 hg, (min_le_left _ _).trans hX.2.2⟩
  · exact ⟨hY.1, lt_min hY.2.1 hg, (min_le_left _ _).trans hY.2.2⟩

end Rows

end VaughtConjecture.CellScheme
