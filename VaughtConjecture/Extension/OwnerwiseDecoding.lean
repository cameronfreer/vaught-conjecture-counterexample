/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Encoders

/-!
# Ownerwise decoding

Roadmap, Layer 3, 3.1 (the section theorem, ownerwise decoding, and the exact base table) and
3.1, row 6, checkpoint 2.3 (coded decoders; lawfulness kept apart from the numerical decoding
identities and from cap preservation); semantic contract, item 3.

**The decoder does not reflect bottom.**  The band coding of
`VaughtConjecture.Extension.CodedSection` reserves the code rank `0`: the band decoding sends
every code below `ω` to bottom, so the strongly coded decoder `Label.strongDecode V K` sends
labels other than bottom to bottom as well (relative to the empty set at grade `1`, the label `1`;
`VaughtConjecture.Extension.TransformationExamples`).  The unconditional statement "the decoded
section of a lawful section is lawful" is false for it: on two cells of grade `1` whose rows are
`(1, 1)` and `(1, 2)`, the lawful section `(1, ω * 5 + 1)` decodes, relative to the empty set of
labels, to `(⊥, ⊤)`, which is not lawful (the regression in
`VaughtConjecture.Extension.TransformationExamples`).

**Decoding is lawful ownerwise.**  In its place, the lawfulness of a decoded section is proved
owner by owner, from the section theorem `CellScheme.Rows.IsLawful.map_of_isShort_or`, each owner
taking one of its two branches.  Let `q` be a lawful section (the coded source section of a
construction), on cells of grade at most `K`, and let `N` be a set of cells (the new cells of
the construction).

* **New owners are short by their rows**
  (`CellScheme.Rows.IsLawful.strongDecode_locality_of_isShort_row`).  At a cell of `N` whose row
  is short at its grade, the row transforms to the decoded labels capped at the decoded owner
  label: the shortness branch.  The hypothesis is on the row itself (`Label.IsShort` of every
  entry of `R.row c`), so a concrete construction discharges it from how it builds the row: the
  full-scope rows that the field layer builds in 2.5 and 2.6.  It is not a property of the codes,
  which are strongly coded but need not be short.
* **Inherited owners by literal readback**
  (`CellScheme.Rows.IsLawful.strongDecode_locality_of_readback`).  At a cell `c` outside `N`, if
  the decoded labels of all cells below `c` (including `c`) are literally those of a lawful
  section `p` (the original section, read back along the exact base table), the mapped locality
  of `c` is the locality of `p` at `c`: the branch of the mapped locality, with no condition on
  the row and no bottom reflection.
* **The combination** (`CellScheme.Rows.IsLawful.strongDecode_of_ownerwise`): if every cell of
  `N` has a short row and every cell outside `N` reads back `p` on its lower domain, the decoded
  section `Label.strongDecode V K ∘ q` is lawful.  Orderliness and availability pass through the
  decoder, a witness bounded by `K` (`Label.isWitness_strongDecode`).

This replaces the unconditional decoding of a bottom-reflecting decoder.  The failure of bottom
reflection alone does not make lawful decoding fail: in the regression, the same rows and the
section `(1, ω * 5 + 1)` decode lawfully through its own normal form, by literal readback.  The
roadmap's phrase "using the decoder's bottom reflection" (for the long-row locality of the
inherited owners) is to be reworded accordingly in a later roadmap revision: the inherited owners
are discharged by literal readback along the exact base table.

Cap preservation is numerical and separate from lawfulness (`Label.strongDecode_min_strongEncode`
and `Label.min_strongDecode_eq_min_strongDecode` in `VaughtConjecture.Extension.Encoders`).

## Placement

These statements belong in `VaughtConjecture.Scheme.Row`, beside the section theorem, once the
strongly coded decoder is placed.  They are stated here so that that folder is unchanged.

## References

Lawful sections are [Kni26, Definition 2.5.4] and witnesses [Kni26, Definition 2.3.9]; the
coding of rows below `ω ^ 2` is the range normalization of [Kni26, Lemma 2.5.13].
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {p q : ι → Label.{u}} {K : ℕ}
  {V : Finset Label.{u}}

/-- **Locality of an inherited owner, by literal readback.**  If the decoded labels of all cells
below `s`, including `s`, are those of a lawful section `p`, then the row of `s` transforms to the
decoded labels capped at the decoded label of `s`: this is the locality of `p` at `s`.  Neither
shortness of the row nor bottom reflection of the decoder is needed.  Used by 2.5 and 2.6: the
inherited owners of a seed construction, whose rows are the original rows (possibly long) and
whose lower cells read back the original lawful section along the exact base table. -/
theorem IsLawful.strongDecode_locality_of_readback (hp : R.IsLawful p) {s : ι}
    (hread : ∀ d : D.below (D.gradedIndex s), strongDecode V K (q d) = p d) :
    TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
      (fun d ↦ min (strongDecode V K (q d)) (strongDecode V K (q s))) := by
  have hs : strongDecode V K (q s) = p s := hread ⟨s, D.mem_below_gradedIndex s⟩
  simp only [hread, hs]
  exact hp.locality s

/-- **Locality of a new owner, by the shortness of its row.**  Let `q` be lawful and `s` a cell
of grade at most `K` whose row is short at the grade of `s`.  Then the row of `s` transforms to
the decoded labels capped at the decoded label of `s`, with no condition on the decoded values:
the shortness branch of the section theorem (`Label.TransformsTo.map_of_isShort`).  Used by 2.5
and 2.6: the new full-scope owners of a seed construction, whose rows the field layer builds
short at their grade. -/
theorem IsLawful.strongDecode_locality_of_isShort_row (hq : R.IsLawful q) {s : ι}
    (hsK : D.grade s ≤ K) (hshort : ∀ t, IsShort (D.grade s) (R.row s t)) :
    TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
      (fun d ↦ min (strongDecode V K (q d)) (strongDecode V K (q s))) :=
  TransformsTo.map_of_isShort (grade := fun d : D.below (D.gradedIndex s) ↦ D.grade d)
    (E := R.row s) (p := fun d ↦ q d) (c := ⟨s, D.mem_below_gradedIndex s⟩) (fun d ↦ d.2.2)
    hsK hshort (hq.orderly s) (hq.locality s) isWitness_strongDecode

/-- **Ownerwise decoding.**  Let `q` and `p` be lawful sections on cells of grade at most `K`,
and `N` a set of cells.  Suppose every cell of `N` (a new owner) has a row short at its grade,
and every cell outside `N` (an inherited owner) reads back `p` literally: the decoded labels of
all cells below it are those of `p`.  Then the decoded section `strongDecode V K ∘ q` is lawful.
This is the section theorem (`CellScheme.Rows.IsLawful.map_of_isShort_or`) with each new owner on
the shortness branch and each inherited owner on the branch of the mapped locality
(`CellScheme.Rows.IsLawful.strongDecode_locality_of_readback`).  No bottom reflection of the
decoder is assumed.  Used by 2.5 and 2.6: the decoded source section of a seed construction is
lawful, its new rows being short by how the field layer builds them and its inherited cells
reading back the original section along the exact base table. -/
theorem IsLawful.strongDecode_of_ownerwise (hq : R.IsLawful q) (hp : R.IsLawful p)
    (hK : ∀ d, D.grade d ≤ K) (N : Set ι) (hnew : ∀ c ∈ N, ∀ d, IsShort (D.grade c) (R.row c d))
    (hread : ∀ c ∉ N, ∀ d : D.below (D.gradedIndex c), strongDecode V K (q d) = p d) :
    R.IsLawful (strongDecode V K ∘ q) :=
  hq.map_of_isShort_or hK isWitness_strongDecode fun s ↦ (em (s ∈ N)).elim
    (fun hs ↦ .inl (hnew s hs)) fun hs ↦ .inr (hp.strongDecode_locality_of_readback (hread s hs))

end VaughtConjecture.CellScheme.Rows
