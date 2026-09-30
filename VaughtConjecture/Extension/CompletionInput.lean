/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CoatomAmalgam

/-!
# The completion input of the coatom extension, and its seeds

Roadmap, Layer 3 (the coatom extension construction: the finite data of the completion of the
amalgam, and the obligations a completion must meet); semantic contract, items 2–4.

**The completion input** (`CompletionInput α m`) is the finite data from which the completion of
[Kni26, Definition 4.3.14] starts: the amalgam of two legal coatom stage types on `m + 1` points
(`Coatom.amalgamType`), a stage type on `m + 2` points with the glued lawful labelling, together
with the two coatom types, its literal faces along the two coatoms, and the laws already proved
for it: consistent and bountiful rows ([Kni26, Lemma 4.3.2]), no cell of full scope, and every
graded face of scope other than the ground set the graded index of a cell.  The two coatom types
embed into the amalgam as lower embeddings along the cell maps of the coatoms
(`CompletionInput.isLowerEmbedding_left`, `CompletionInput.isLowerEmbedding_right`), and every
cell of the amalgam has grade at most `m + 1` (`CompletionInput.grade_le`).
`CompletionInput.ofCoatoms` builds it from two legal stage types with the same face along
`Fin.castSuccEmb`.

**A seed** (`CompletionInput.Seed I`) of a completion input `I` is the completion of the amalgam
below the full grade: a scheme on `m + 2` points that extends the amalgam by cells of full scope
only, with its rows and a lawful labelling at stage `α`, subject to every law of a legal stage
type except completeness at the full grade `m + 2`, which the apex layer adds
(`VaughtConjecture.Extension.ApexLayer`).  Every obligation is a separate field:

* the old cells: an order embedding of the cells of the amalgam, a lower embedding that keeps
  scopes, rows, and labels literally, whose image contains every cell of scope other than the
  ground set (so the new cells have full scope), and the same faces;
* the grades: every cell has grade at most `m + 1`;
* the laws: well formed, coded, consistent ([Kni26, Definition 2.5.12]), bountiful between every
  two graded faces ([Kni26, Definition 2.5.14]; for the completion this is the statement of
  [Kni26, Lemma 4.3.20]), and complete ([Kni26, Definition 2.5.15]) at every graded face of grade
  at most `m + 1`;
* the labelling: lawful, at stage `α`, and equal to the glued labelling on the old cells.

The seed carries no apex: the cell of full scope and full grade, with the largest label, is added
by the apex layer, and the coatom extension with apex follows
(`VaughtConjecture.Extension.CoatomExtensionOfSeed`).

## References

The amalgam is [Kni26, Definition 4.3.1] with its consistency and bountifulness
[Kni26, Lemma 4.3.2]; its completion by cells of full scope is [Kni26, Definition 4.3.14], and the
bountifulness of the completion is [Kni26, Lemma 4.3.20]; the coatom extension with apex is
[Kni26, Corollary 4.3.22].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The completion input -/

/-- The **completion input** of the coatom extension at stage `α` on `m + 2` points: the amalgam of
two legal coatom stage types, with its glued labelling, its literal coatom faces, and the laws
proved for it [Kni26, Definition 4.3.1 and Lemma 4.3.2]. -/
structure CompletionInput (α : Ordinal.{u}) (m : ℕ) where
  /-- The amalgam, with the glued lawful labelling: a stage type on `m + 2` points. -/
  amalgam : StageType.{u} α (m + 2)
  /-- The stage type on the coatom omitting the last point. -/
  left : StageType.{u} α (m + 1)
  /-- The stage type on the coatom omitting the point `m`. -/
  right : StageType.{u} α (m + 1)
  /-- The stage type on the first coatom is legal. -/
  isLegal_left : left.IsLegal
  /-- The stage type on the second coatom is legal. -/
  isLegal_right : right.IsLegal
  /-- The face of the amalgam along `Fin.castSuccEmb` is literally `left`, labels included. -/
  restrictFace_left : StageType.restrictFace (Coatom.left m) amalgam = some left
  /-- The face of the amalgam along `extendByLast Fin.castSuccEmb` is literally `right`, labels
  included. -/
  restrictFace_right : StageType.restrictFace (Coatom.right m) amalgam = some right
  /-- The rows of the amalgam are consistent [Kni26, Lemma 4.3.2]. -/
  isConsistent : amalgam.rows.IsConsistent
  /-- The rows of the amalgam are bountiful [Kni26, Lemma 4.3.2]. -/
  isBountiful : amalgam.rows.IsBountiful
  /-- No cell of the amalgam has the full scope. -/
  scope_ne_univ (d : Fin amalgam.card) : amalgam.toCellScheme.scope d ≠ univ
  /-- Every graded face of scope other than the ground set is the graded index of a cell. -/
  exists_gradedIndex_eq : ∀ X ∈ amalgam.toCellScheme.gradedFaces, X.1 ≠ univ →
    ∃ d, amalgam.toCellScheme.gradedIndex d = X

namespace CompletionInput

variable {α : Ordinal.{u}} {m : ℕ} (I : CompletionInput.{u} α m)

/-- The first coatom is a closed face of the amalgam. -/
theorem univ_map_left_mem : univ.map (Coatom.left m) ∈ I.amalgam.toCellScheme.faces :=
  ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1

/-- The second coatom is a closed face of the amalgam. -/
theorem univ_map_right_mem : univ.map (Coatom.right m) ∈ I.amalgam.toCellScheme.faces :=
  ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1

/-- The first coatom type is the restriction of the amalgam to the first coatom. -/
theorem comap_left : I.amalgam.comap (Coatom.left m) I.univ_map_left_mem = I.left :=
  ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).2

/-- The second coatom type is the restriction of the amalgam to the second coatom. -/
theorem comap_right : I.amalgam.comap (Coatom.right m) I.univ_map_right_mem = I.right :=
  ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).2

/-- **The first coatom embeds as a lower embedding**, along the enumeration of the cells of the
amalgam visible in it. -/
theorem isLowerEmbedding_left :
    (I.amalgam.comap (Coatom.left m) I.univ_map_left_mem).toCellScheme.IsLowerEmbedding
      I.amalgam.toCellScheme (I.amalgam.cellMap (Coatom.left m)) :=
  I.amalgam.isLowerEmbedding_comap _

/-- **The second coatom embeds as a lower embedding**, along the enumeration of the cells of the
amalgam visible in it. -/
theorem isLowerEmbedding_right :
    (I.amalgam.comap (Coatom.right m) I.univ_map_right_mem).toCellScheme.IsLowerEmbedding
      I.amalgam.toCellScheme (I.amalgam.cellMap (Coatom.right m)) :=
  I.amalgam.isLowerEmbedding_comap _

/-- Every cell of the amalgam has grade at most `m + 1`: its scope is a proper subset of the
`m + 2` points. -/
theorem grade_le (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d ≤ m + 1 := by
  have hlt : #(I.amalgam.toCellScheme.scope d) < m + 2 := by
    simpa using card_lt_card (ssubset_univ_iff.mpr (I.scope_ne_univ d))
  exact (I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans (Nat.le_of_lt_succ hlt)

/-- No cell of the amalgam lies above a pair on the full face. -/
theorem not_univ_le (j : ℕ) (d : Fin I.amalgam.card) :
    ¬ ((univ : Finset (Fin (m + 2))), j) ≤ I.amalgam.toCellScheme.gradedIndex d :=
  fun h ↦ I.scope_ne_univ d (eq_univ_of_forall fun x ↦ h.1 (mem_univ x))

variable {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m}

/-- **The completion input of two legal coatom types** with the same face along
`Fin.castSuccEmb`: their amalgam with the glued labelling, and the laws proved for it
[Kni26, Definition 4.3.1 and Lemma 4.3.2]. -/
noncomputable def ofCoatoms (hla : ta.IsLegal) (hlb : tb.IsLegal)
    (hpa : StageType.restrictFace (Coatom.face m) ta = some p)
    (hpb : StageType.restrictFace (Coatom.face m) tb = some p) : CompletionInput.{u} α m where
  amalgam := Coatom.amalgamType hpa hpb
  left := ta
  right := tb
  isLegal_left := hla
  isLegal_right := hlb
  restrictFace_left := Coatom.restrictFace_left_amalgamType hpa hpb
  restrictFace_right := Coatom.restrictFace_right_amalgamType hpa hpb
  isConsistent := Coatom.isConsistent_amalgamType hpa hpb hla hlb
  isBountiful := Coatom.isBountiful_amalgamType hpa hpb hla hlb
  scope_ne_univ := Coatom.amalgamType_scope_ne_univ hpa hpb
  exists_gradedIndex_eq _ hX hne := Coatom.exists_gradedIndex_eq_amalgamType hpa hpb hla hlb hX hne

/-! ### Seeds -/

/-- A **seed** of a completion input `I`: the completion of the amalgam below the full grade.  It
is a scheme on `m + 2` points extending the amalgam of `I` by cells of full scope only, with its
rows and a lawful labelling at stage `α`, subject to every law of a legal stage type except
completeness at the full grade `m + 2` ([Kni26, Definition 4.3.14], below the full grade). -/
structure Seed (I : CompletionInput.{u} α m) where
  /-- The completed scheme: cells, scopes, grades, faces, and rows, on `m + 2` points. -/
  scheme : Scheme.{u} (m + 2)
  /-- The old cells: the cells of the amalgam, in their order. -/
  embed : Fin I.amalgam.card ↪o Fin scheme.card
  /-- The old cells form a lower embedding of the amalgam: grades and the graded order are kept,
  and every cell below an old cell is old. -/
  isLowerEmbedding : I.amalgam.toCellScheme.IsLowerEmbedding scheme.toCellScheme embed
  /-- The old cells keep their scopes. -/
  scope_embed (d : Fin I.amalgam.card) : scheme.toCellScheme.scope (embed d) =
    I.amalgam.toCellScheme.scope d
  /-- The old cells keep their rows: the rows pull back to those of the amalgam. -/
  comap_rows : scheme.rows.comap isLowerEmbedding = I.amalgam.rows
  /-- Every cell of scope other than the ground set is old; the new cells have full scope. -/
  mem_range_embed (z : Fin scheme.card) :
    scheme.toCellScheme.scope z ≠ univ → z ∈ Set.range embed
  /-- The faces are those of the amalgam. -/
  faces_eq : scheme.toCellScheme.faces = I.amalgam.toCellScheme.faces
  /-- Every cell has grade at most `m + 1`; the full grade `m + 2` is left to the apex. -/
  grade_le (d : Fin scheme.card) : scheme.toCellScheme.grade d ≤ m + 1
  /-- The scheme is well formed: its ground set is all of `Fin (m + 2)`, its faces form a plan,
  and every cell has a graded face as graded index. -/
  isWellFormed : scheme.IsWellFormed
  /-- The rows are coded: every row value lies below `ω ^ 2` [Kni26, Lemma 2.5.13]. -/
  isCoded : scheme.IsCoded
  /-- The rows are consistent [Kni26, Definition 2.5.12]. -/
  isConsistent : scheme.rows.IsConsistent
  /-- The rows are bountiful between every two graded faces [Kni26, Definition 2.5.14]; for the
  completion this is the statement of [Kni26, Lemma 4.3.20]. -/
  isBountiful : scheme.rows.IsBountiful
  /-- Completeness below the full grade: every graded face of grade at most `m + 1` is the graded
  index of a cell [Kni26, Definition 2.5.15]. -/
  isComplete : ∀ X ∈ scheme.toCellScheme.gradedFaces, X.2 ≤ m + 1 →
    ∃ d, scheme.toCellScheme.gradedIndex d = X
  /-- The labelling of the cells. -/
  label : Fin scheme.card → Label.{u}
  /-- The labelling is a lawful section of the rows. -/
  isLawful : scheme.rows.IsLawful label
  /-- Every label occurs at stage `α`. -/
  atStage (d : Fin scheme.card) : AtStage α (label d)
  /-- The old cells keep the glued labels of the amalgam. -/
  label_embed (d : Fin I.amalgam.card) : label (embed d) = I.amalgam.label d

end CompletionInput

end VaughtConjecture
