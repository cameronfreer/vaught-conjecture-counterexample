/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.WitnessAlgebra
import VaughtConjecture.Scheme.Row

/-!
# Lawful transformations of sections, and the section theorem

Roadmap, Layer 3, 3.1 (the section theorem and the shared decoding lemma) and 3.1, row 6,
checkpoint 2.3 (lawful transformations); Layer 1 (capping a lawful section at a self-visible cap);
semantic contract, item 3.

Let `R` be semantic rows of a cell scheme `D` whose cells have grades at most `K`, and let `p` be
a lawful section.  Three operations on `p` keep it lawful, with the rows unchanged.

* **Capping** at a label `c` (`CellScheme.Rows.IsLawful.min_const`, [Kni26, Lemma 2.5.8], in
  `VaughtConjecture.Scheme.Row`): the capped section is lawful when `c` is self-visible at the
  grade of every cell whose label is at least `c`.  Below a pair:
  `CellScheme.Rows.IsLawfulBelow.min_const`.  The special case of a cap self-visible at a bound
  `K` of all grades is `CellScheme.Rows.IsLawful.min_const_of_isSelfVisible` and, at the grade of
  a pair, `CellScheme.Rows.IsLawfulBelow.min_const_of_isSelfVisible`.  Capping at a cutoff that is
  not self-visible need not keep lawfulness.
* **The section theorem** (`CellScheme.Rows.IsLawful.map_of_isShort_or`, roadmap, 3.1): for a
  witness `ν` bounded by grade `K` (a witness whose suppressor is the formal top at the grades `≤ K`
  and bottom above; the bound is on the grades, not on the values of `ν`), `ν ∘ p` is lawful
  provided every owner (a cell with its row) is **short** (every entry of its row is short at its
  grade, `Label.IsShort`) or satisfies the **mapped locality**
  `E(s) ⇒ (d ↦ min (ν (p d)) (ν (p s)))`.  Orderliness and availability pass through `ν` once;
  locality is proved owner by owner, at a short owner by `Label.TransformsTo.map_of_isShort` and at
  any other owner by the hypothesis.  Neither lawfulness of `ν ∘ p`, nor bottom reflection of `ν`,
  nor shortness of every row is assumed.  For the strongly coded decoder, which does not reflect
  bottom, the owners are treated one by one (`CellScheme.Rows.IsLawful.strongDecode_of_ownerwise`):
  new owners by the shortness of their rows, inherited owners because the decoded labels below them
  are those of a lawful section.
* **A bottom-reflecting witness** `ν` bounded by grade `K`
  (`CellScheme.Rows.IsLawful.map_of_bot_reflecting`): `ν ∘ p` is lawful when `ν` sends a label to
  bottom only if it is bottom.  This is the section theorem with every owner on the branch of
  the mapped locality, which `Label.TransformsTo.map_of_bot_reflecting` proves.

Lawfulness below a pair is lawfulness for the pulled-back rows (`Rows.isLawfulBelow_iff`), so
the last two statements apply below a pair as they stand.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

Lawful sections are [Kni26, Definition 2.5.4]; capping is [Kni26, Lemma 2.5.8]; witnesses are
[Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {p : ι → Label.{u}} {K : ℕ}
  {ν : Label.{u} → Label.{u}}

/-- The cells below a cell have grade at most the grade of that cell. -/
private theorem grade_le_of_mem_below (s : ι) (d : D.below (D.gradedIndex s)) :
    D.grade d ≤ D.grade s :=
  d.2.2

namespace IsLawful

/-- **The section theorem** (roadmap, Layer 3, 3.1).  Let `p` be lawful, the grades at most `K`,
and `ν` a witness bounded by grade `K`.  If every owner `s` is short (every entry of its row is
short at the grade of `s`) or satisfies the mapped locality
`E(s) ⇒ (d ↦ min (ν (p d)) (ν (p s)))`, then `ν ∘ p` is lawful.  No bottom reflection of `ν` and
no shortness of the other rows is assumed.  It proves ownerwise decoding
(`CellScheme.Rows.IsLawful.strongDecode_of_ownerwise`): the decoded section is lawful when the new
owners have short rows (a property of the construction of those rows, not of the normal form,
whose finite parts reach `K + 1`) and the decoded labels below each inherited owner are those of
a lawful section, which gives its mapped locality. -/
theorem map_of_isShort_or (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν)
    (howner : ∀ s, (∀ t, IsShort (D.grade s) (R.row s t)) ∨
      TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
        (fun d ↦ min (ν (p d)) (ν (p s)))) :
    R.IsLawful (ν ∘ p) where
  orderly d := hν.isSelfVisible_apply (hp.orderly d) (by simp [hK d])
  locality s := (howner s).elim
    (fun hs ↦ TransformsTo.map_of_isShort (grade := fun d : D.below (D.gradedIndex s) ↦
      D.grade d) (E := R.row s) (p := fun d ↦ p d) (c := ⟨s, D.mem_below_gradedIndex s⟩)
      (grade_le_of_mem_below s) (hK s) hs (hp.orderly s) (hp.locality s) hν) id
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hp.availability s t hst hg
    exact ⟨u, hu, hν.monotone hle⟩

/-- **Lawfulness through a bottom-reflecting witness.**  If the grades are at most `K` and `ν` is
a witness bounded by grade `K` that sends a label to bottom only if it is bottom, then `ν ∘ p` is
lawful: the section theorem with every owner on the branch of the mapped locality
(`Label.TransformsTo.map_of_bot_reflecting`).  It proves that the normal form of a lawful section
is lawful (`CellScheme.Rows.IsLawful.strongEncode`). -/
theorem map_of_bot_reflecting (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) : R.IsLawful (ν ∘ p) :=
  hp.map_of_isShort_or hK hν fun s ↦ .inr (TransformsTo.map_of_bot_reflecting
    (grade := fun d : D.below (D.gradedIndex s) ↦ D.grade d) (E := R.row s) (p := fun d ↦ p d)
    (c := ⟨s, D.mem_below_gradedIndex s⟩) (grade_le_of_mem_below s) (hK s) (hp.orderly s)
    (hp.locality s) hν hbot)

end IsLawful

end VaughtConjecture.CellScheme.Rows
