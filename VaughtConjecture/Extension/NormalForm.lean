/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Finite
import VaughtConjecture.Extension.Encoders

/-!
# Strongly coded normal forms of lawful sections

Roadmap, Layer 3, 3.1, row 6, checkpoint 2.3 (normal forms) and 3.1 (catalogues of canonical
vectors); semantic contract, item 3.

The rows of a legal scheme are coded only in the sense of the range normalization of
[Kni26, Lemma 2.5.13]: their values lie below `ω ^ 2` (`Scheme.IsCoded`).  A construction that
adds a cell needs a row for it, and wants that row strongly coded (`Label.IsStronglyCoded`,
finite part at most the grade plus one) and drawn from a finite catalogue.  This file proves that
every lawful section on finitely many cells of grade at most `K` has such a representative; the
strong coding is a property of the representative that the encoder constructs, proved here, and
no bound on the finite parts of the given section or of the given rows is assumed or derived.

**Normal forms.**  Let `w` be a labelling of cells of grade at most `K`, and `V` a finite set of
labels containing its values.  The **normal form** of `w` is `Label.strongEncode V K ∘ w`.

* `w` and its normal form transform into each other (`Label.transformsTo_strongEncode_comp`,
  `Label.strongEncode_comp_transformsTo`), and the decoder, a witness bounded by `K`, reads `w`
  back from it (`Label.strongDecode_comp_strongEncode_comp`).  Transformation is not transitive,
  so this two-sided relation is recorded as two statements, not as an equivalence relation.
* If `w` is lawful, so is its normal form (`CellScheme.Rows.IsLawful.strongEncode`).
* **Strongly coded representatives** (`CellScheme.Rows.IsLawful.exists_stronglyCoded`): over
  finitely many cells, every lawful section `w` has a lawful representative `w'`, strongly coded
  at `K`, with values in the coded alphabet with block bound `2 · #cells + 1` and offset bound
  `K + 1`, such that `w ⇒ w'`, `w' ⇒ w`, and a witness bounded by `K` sends `w'` to `w`.  Below
  a pair `X` (`CellScheme.Rows.IsLawfulBelow.exists_stronglyCoded`) the grade bound is the grade
  of `X`, so the representative is admissible as the row of a new cell of that grade that is
  strongly coded (`CellScheme.Rows.IsStronglyCodedAt`).

**Strongly coded, not short.**  The representatives produced here have finite parts up to
`K + 1`: they are strongly coded at `K` but in general not short at `K` (`Label.IsShort`; the code
of `3` at `K = 1` has finite part `2`, `VaughtConjecture.Extension.TransformationExamples`).  So a
row built from a representative need not satisfy the shortness branch of the section theorem
(`CellScheme.Rows.IsLawful.map_of_isShort_or`) at its grade.  Where 2.5 and 2.6 need the
full-scope rows to be short, the shortness comes from how the field layer builds their profiles
(checkpoints 2.5 and 2.6), not from this normal form: it is the hypothesis on the rows of the new
owners in ownerwise decoding (`CellScheme.Rows.IsLawful.strongDecode_of_ownerwise`), whose
inherited owners are discharged by literal readback (`Label.strongDecode_comp_strongEncode_comp`).

The lawfulness of the representative, its strong coding, and the decoding identity are separate
statements, as are the cap statements of `VaughtConjecture.Extension.Encoders`.

## References

The coding of rows below `ω ^ 2` is the range normalization of [Kni26, Lemma 2.5.13]; the strong
coding of the representative is a theorem of this library about the representative it constructs.
Lawful sections are [Kni26, Definition 2.5.4] and transformations [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

variable {D : Type*} {grade : D → ℕ} {V : Finset Label.{u}} {K : ℕ}

/-- **A labelling transforms to its normal form.**  Used by 2.5 and 2.6: the boundary labels
transform to their strongly coded representative. -/
theorem transformsTo_strongEncode_comp (hK : ∀ d, grade d ≤ K) (w : D → Label.{u}) :
    TransformsTo grade w (strongEncode V K ∘ w) :=
  isWitness_strongEncode.transformsTo_comp hK w

/-- **The decoder reads a labelling back from its normal form**, when `V` contains its values.
Used by 2.5 and 2.6: the literal readback by which the inherited owners are discharged in
ownerwise decoding (`CellScheme.Rows.IsLawful.strongDecode_of_ownerwise`). -/
theorem strongDecode_comp_strongEncode_comp {w : D → Label.{u}} (hV : ∀ d, w d ∈ V) :
    strongDecode V K ∘ (strongEncode V K ∘ w) = w :=
  funext fun d ↦ strongDecode_strongEncode (hV d)

/-- **The normal form transforms back to the labelling**, when `V` contains its values.  Used by
2.5 and 2.6: the strongly coded representative of the boundary labels transforms back to them,
through the decoder. -/
theorem strongEncode_comp_transformsTo (hK : ∀ d, grade d ≤ K) {w : D → Label.{u}}
    (hV : ∀ d, w d ∈ V) : TransformsTo grade (strongEncode V K ∘ w) w := by
  have h := (isWitness_strongDecode (V := V)).transformsTo_comp hK (strongEncode V K ∘ w)
  rwa [strongDecode_comp_strongEncode_comp hV] at h

end Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {w : ι → Label.{u}} {K : ℕ}

/-- **Strongly coded representatives of lawful sections.**  Let `w` be a lawful section on
finitely many cells of grade at most `K`.  Some lawful section `w'` is strongly coded at `K`, takes
its values in the coded alphabet with block bound `2 · #cells + 1` and offset bound `K + 1`,
transforms to `w` and is transformed to by `w`, and is sent to `w` by a witness bounded by `K`.
No coding of `w` or of the rows is assumed.  The finite parts of `w'` reach `K + 1`, so `w'` is
strongly coded at `K` but need not be short at `K`.  Used by 2.5 and 2.6: the boundary labels of
a seed are replaced by a strongly coded catalogue vector, whose decoding restores them
literally. -/
theorem IsLawful.exists_stronglyCoded [Finite ι] (hw : R.IsLawful w) (hK : ∀ d, D.grade d ≤ K) :
    ∃ w' : ι → Label.{u}, R.IsLawful w' ∧ (∀ d, Label.IsStronglyCoded K (w' d)) ∧
      (∀ d, w' d ∈ codedAlphabet (2 * Nat.card ι + 1) (K + 1)) ∧
      TransformsTo D.grade w w' ∧ TransformsTo D.grade w' w ∧
      ∃ ν, IsWitness (stepSuppressor K) ν ∧ ∀ d, ν (w' d) = w d := by
  classical
  have := Fintype.ofFinite ι
  set V : Finset Label.{u} := univ.image w
  have hV (d : ι) : w d ∈ V := mem_image_of_mem _ (mem_univ d)
  have hcard : 2 * #V + 1 ≤ 2 * Nat.card ι + 1 := by
    have : #V ≤ Nat.card ι := card_image_le.trans (by rw [card_univ, Nat.card_eq_fintype_card])
    omega
  refine ⟨Label.strongEncode V K ∘ w, hw.strongEncode hK, fun d ↦ isStronglyCoded_strongEncode _,
    fun d ↦ ?_, transformsTo_strongEncode_comp hK w, strongEncode_comp_transformsTo hK hV,
    Label.strongDecode V K, isWitness_strongDecode, fun d ↦ strongDecode_strongEncode (hV d)⟩
  rcases mem_codedAlphabet.mp (strongEncode_mem_codedAlphabet (V := V) (K := K) (w d)) with
    h | ⟨a, ha, b, hb, h⟩
  · exact mem_codedAlphabet.mpr (.inl h)
  · exact mem_codedAlphabet.mpr (.inr ⟨a, ha.trans hcard, b, hb, h⟩)

/-- **Strongly coded representatives below a pair.**  Let `r` be lawful below `X`, on finitely
many cells.  Some `r'` lawful below `X` is strongly coded at the grade of `X`, takes its values in
the coded alphabet with block bound `2 · #cells + 1` and offset bound the grade of `X` plus one,
transforms to `r` and is transformed to by `r`, and is sent to `r` by a witness bounded by the
grade of `X`.  The finite parts of `r'` reach the grade of `X` plus one, so `r'` need not be
short at the grade of `X`.  Used by 2.5 and 2.6: `r'` is the row of a new cell of scope and grade
those of `X`, and that cell is strongly coded (`CellScheme.Rows.IsStronglyCodedAt`); shortness
of a full-scope row, where the section theorem needs it, comes from how the field layer builds
its profile. -/
theorem IsLawfulBelow.exists_stronglyCoded {X : Finset α × ℕ} [Finite (D.below X)]
    {r : D.below X → Label.{u}} (hr : R.IsLawfulBelow X r) :
    ∃ r' : D.below X → Label.{u}, R.IsLawfulBelow X r' ∧
      (∀ d, Label.IsStronglyCoded X.2 (r' d)) ∧
      (∀ d, r' d ∈ codedAlphabet (2 * Nat.card (D.below X) + 1) (X.2 + 1)) ∧
      TransformsTo (fun d : D.below X ↦ D.grade d) r r' ∧
      TransformsTo (fun d : D.below X ↦ D.grade d) r' r ∧
      ∃ ν, IsWitness (stepSuppressor X.2) ν ∧ ∀ d, ν (r' d) = r d :=
  (isLawfulBelow_iff.mp hr).exists_stronglyCoded fun d ↦ d.2.2

end CellScheme.Rows

end VaughtConjecture
