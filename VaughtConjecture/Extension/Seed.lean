/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CoatomAmalgam

/-!
# The seed of the completion of the coatom extension

Roadmap, Layer 3 (the coatom extension construction: the finite input of the completion of the
amalgam, with the conditions it satisfies), checkpoint 2.1; semantic contract, items 2–4.

**A seed** (`Seed α m`) is the finite input of the completion of the coatom extension on `m + 2`
points, together with the conditions it must satisfy, each stated as a separate field:

* the data: two stage types `left` and `right` on the coatoms of `m + 1` points, their common face
  `face` on `m` points, and the amalgam, a stage type on `m + 2` points with the glued lawful
  labelling;
* legality of the two coatom types, and the common face literally the face of both along
  `Fin.castSuccEmb`;
* the literal restrictions: the faces of the amalgam along the two coatoms are the two coatom types,
  labels included;
* the laws of the amalgam: consistent rows, and bountiful rows (the lifting condition)
  [Kni26, Lemma 4.3.2];
* its cells and faces: no cell of full scope, every graded face of scope other than the ground set
  the graded index of a cell, and every face other than the ground set inside one of the two
  coatoms (the face structure under which bountifulness is checked coatom by coatom,
  `CellScheme.Rows.isBountiful_of_coatoms`).

Every cell of the amalgam has grade below `m + 2` (`Seed.grade_lt`), and no cell lies above a pair
on the full face (`Seed.not_univ_le`).

**The amalgam of two legal coatom types is a seed** (`Seed.ofCoatoms`), from
`Coatom.isConsistent_amalgamType`, `Coatom.isBountiful_amalgamType`, and the restriction theorems
`Coatom.restrictFace_left_amalgamType` and `Coatom.restrictFace_right_amalgamType`; its face
structure is `Coatom.subset_or_subset_of_mem_amalgamFaces`, read off the faces of the amalgam
(`Coatom.mem_amalgamFaces`).

The completion of a seed by cells of full scope, below the full grade, is
`VaughtConjecture.Extension.CompletionBelowFullGrade`.

## References

The amalgam is [Kni26, Definition 4.3.1] with its consistency and bountifulness
[Kni26, Lemma 4.3.2]; its completion is the subject of [Kni26, Corollary 4.3.22].
-/

universe u

namespace VaughtConjecture

open Finset Label

/-- A **seed** of the coatom extension at stage `α` on `m + 2` points: two legal coatom stage types
with a common face, their amalgam with its glued labelling and literal coatom faces, and the laws
and face structure of the amalgam [Kni26, Definition 4.3.1 and Lemma 4.3.2]. -/
structure Seed (α : Ordinal.{u}) (m : ℕ) where
  /-- The amalgam, with the glued lawful labelling: a stage type on `m + 2` points. -/
  amalgam : StageType.{u} α (m + 2)
  /-- The stage type on the coatom omitting the last point. -/
  left : StageType.{u} α (m + 1)
  /-- The stage type on the coatom omitting the point `m`. -/
  right : StageType.{u} α (m + 1)
  /-- The common face of the two coatom types, on `m` points. -/
  face : StageType.{u} α m
  /-- The stage type on the first coatom is legal. -/
  isLegal_left : left.IsLegal
  /-- The stage type on the second coatom is legal. -/
  isLegal_right : right.IsLegal
  /-- The face of `left` along `Fin.castSuccEmb` is literally `face`. -/
  restrictFace_face_left : StageType.restrictFace (Coatom.face m) left = some face
  /-- The face of `right` along `Fin.castSuccEmb` is literally `face`. -/
  restrictFace_face_right : StageType.restrictFace (Coatom.face m) right = some face
  /-- The face of the amalgam along `Fin.castSuccEmb` is literally `left`, labels included. -/
  restrictFace_left : StageType.restrictFace (Coatom.left m) amalgam = some left
  /-- The face of the amalgam along `extendByLast Fin.castSuccEmb` is literally `right`, labels
  included. -/
  restrictFace_right : StageType.restrictFace (Coatom.right m) amalgam = some right
  /-- The rows of the amalgam are consistent [Kni26, Lemma 4.3.2]. -/
  isConsistent : amalgam.rows.IsConsistent
  /-- The rows of the amalgam are bountiful [Kni26, Lemma 4.3.2]. -/
  isBountiful : amalgam.rows.IsBountiful
  /-- Every face of the amalgam other than the ground set lies in one of the two coatoms, the
  ground set without the last point or without the point `m`. -/
  subset_or_subset : ∀ B ∈ amalgam.toCellScheme.faces, B ≠ univ →
    B ⊆ univ.erase (Fin.last (m + 1)) ∨ B ⊆ univ.erase (Fin.castSucc (Fin.last m))
  /-- No cell of the amalgam has the full scope. -/
  scope_ne_univ (d : Fin amalgam.card) : amalgam.toCellScheme.scope d ≠ univ
  /-- Every graded face of scope other than the ground set is the graded index of a cell. -/
  exists_gradedIndex_eq : ∀ X ∈ amalgam.toCellScheme.gradedFaces, X.1 ≠ univ →
    ∃ d, amalgam.toCellScheme.gradedIndex d = X

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- Every cell of the amalgam has grade below `m + 2`: its scope is a proper subset of the `m + 2`
points. -/
theorem grade_lt (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d < m + 2 := by
  have hlt : #(I.amalgam.toCellScheme.scope d) < m + 2 := by
    simpa using card_lt_card (ssubset_univ_iff.mpr (I.scope_ne_univ d))
  exact (I.amalgam.isWellFormed.isWellFormed.grade_le_card d).trans_lt hlt

/-- No cell of the amalgam lies above a pair on the full face. -/
theorem not_univ_le (j : ℕ) (d : Fin I.amalgam.card) :
    ¬ ((univ : Finset (Fin (m + 2))), j) ≤ I.amalgam.toCellScheme.gradedIndex d :=
  fun h ↦ I.scope_ne_univ d (eq_univ_of_forall fun x ↦ h.1 (mem_univ x))

variable {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m}

/-- **The amalgam of two legal coatom types is a seed**: two legal stage types with the same face
along `Fin.castSuccEmb`, their amalgam with the glued labelling, and the laws proved for it
[Kni26, Definition 4.3.1 and Lemma 4.3.2]. -/
noncomputable def ofCoatoms (hla : ta.IsLegal) (hlb : tb.IsLegal)
    (hpa : StageType.restrictFace (Coatom.face m) ta = some p)
    (hpb : StageType.restrictFace (Coatom.face m) tb = some p) : Seed.{u} α m where
  amalgam := Coatom.amalgamType hpa hpb
  left := ta
  right := tb
  face := p
  isLegal_left := hla
  isLegal_right := hlb
  restrictFace_face_left := hpa
  restrictFace_face_right := hpb
  restrictFace_left := Coatom.restrictFace_left_amalgamType hpa hpb
  restrictFace_right := Coatom.restrictFace_right_amalgamType hpa hpb
  isConsistent := Coatom.isConsistent_amalgamType hpa hpb hla hlb
  isBountiful := Coatom.isBountiful_amalgamType hpa hpb hla hlb
  subset_or_subset B hB hne := by
    rw [← Coatom.univ_map_left, ← Coatom.univ_map_right]
    exact Coatom.subset_or_subset_of_mem_amalgamFaces (Sa := ta.toScheme) (Sb := tb.toScheme)
      hB hne
  scope_ne_univ := Coatom.amalgamType_scope_ne_univ hpa hpb
  exists_gradedIndex_eq _ hX hne := Coatom.exists_gradedIndex_eq_amalgamType hpa hpb hla hlb hX hne

end Seed

end VaughtConjecture
