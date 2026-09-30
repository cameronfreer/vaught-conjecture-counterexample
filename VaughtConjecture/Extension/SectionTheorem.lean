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

* **Capping** at a label `c` (`CellScheme.Rows.IsLawful.min_const`, [Kni26, Lemma 2.5.8]): the
  capped section is lawful when `c` is self-visible at the grade of every cell whose label is at
  least `c`.  Below a pair: `CellScheme.Rows.IsLawfulBelow.min_const`.  The special case of a cap
  self-visible at a bound `K` of all grades is `CellScheme.Rows.IsLawful.min_const_of_isSelfVisible`
  and, at the grade of a pair, `CellScheme.Rows.IsLawfulBelow.min_const_of_isSelfVisible`.
  Capping at a cutoff that is not self-visible need not keep lawfulness.
* **The section theorem** (`CellScheme.Rows.IsLawful.map_of_isShort_or`, roadmap, 3.1): for a
  witness `ν` bounded by `K`, `ν ∘ p` is lawful provided every owner (a cell with its row) is
  **short** (every entry of its row is short at its grade, `Label.IsShort`) or satisfies the
  **mapped locality** `E(s) ⇒ (d ↦ min (ν (p d)) (ν (p s)))`.  Orderliness and availability pass
  through `ν` once; locality is proved owner by owner, at a short owner by
  `Label.TransformsTo.map_of_isShort` and at any other owner by the hypothesis.  Neither
  lawfulness of `ν ∘ p`, nor bottom reflection of `ν`, nor shortness of every row is assumed.
* **A bottom-reflecting witness** `ν` bounded by `K`
  (`CellScheme.Rows.IsLawful.map_of_bot_reflecting`): `ν ∘ p` is lawful when `ν` sends a label to
  bottom only if it is bottom.  This is the section theorem with every owner on the branch of
  the mapped locality, which `Label.TransformsTo.map_of_bot_reflecting` supplies.

Lawfulness below a pair is lawfulness for the pulled-back rows (`Rows.isLawfulBelow_iff`), so
the last two statements apply below a pair as they stand.

## Placement

These statements belong in `VaughtConjecture.Scheme.Row`, after the lawful sections.  They are
stated here so that that file is unchanged.

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

/-- **Capping a lawful section** [Kni26, Lemma 2.5.8].  If the cap `c` is self-visible at the
grade of every cell whose label is at least `c`, the section capped at `c` is lawful.  At a cell
whose label is below `c` the capped section agrees with `p`; at the others its label is `c`, and
the locality of such an owner is capped at `c` (`Label.TransformsTo.min_const`).  Used by 2.5
through `CellScheme.Rows.IsLawfulBelow.min_const`. -/
theorem min_const (hp : R.IsLawful p) {c : Label.{u}}
    (hc : ∀ d, c ≤ p d → IsSelfVisible (D.grade d) c) : R.IsLawful fun d ↦ min (p d) c where
  orderly d := by
    rcases le_total (p d) c with h | h
    · rw [min_eq_left h]; exact hp.orderly d
    · rw [min_eq_right h]; exact hc d h
  locality s := by
    rcases le_total c (p s) with h | h
    · have := (hp.locality s).min_const (grade_le_of_mem_below s) (hc s h)
      -- The target `d ↦ min (min (p d) c) (min (p s) c)` is `d ↦ min (min (p d) (p s)) c`.
      convert this using 2 with d
      rw [min_min_min_comm, min_self]
    · -- Here `p s ≤ c`, so the capped target reduces to `d ↦ min (p d) (p s)`, that of `p`.
      convert hp.locality s using 2 with d
      rw [min_min_min_comm, min_self]
      exact min_eq_left ((min_le_right _ _).trans h)
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hp.availability s t hst hg
    exact ⟨u, hu, min_le_min_right c hle⟩

/-- **Capping a lawful section at a cap self-visible at a grade bound**, the special case of
[Kni26, Lemma 2.5.8] in which the grades are at most `K` and `c` is self-visible at `K`. -/
theorem min_const_of_isSelfVisible (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K) {c : Label.{u}}
    (hc : IsSelfVisible K c) : R.IsLawful fun d ↦ min (p d) c :=
  hp.min_const fun d _ ↦ hc.mono (hK d)

/-- **The section theorem** (roadmap, Layer 3, 3.1).  Let `p` be lawful, the grades at most `K`,
and `ν` a witness bounded by `K`.  If every owner `s` is short (every entry of its row is short at
the grade of `s`) or satisfies the mapped locality `E(s) ⇒ (d ↦ min (ν (p d)) (ν (p s)))`, then
`ν ∘ p` is lawful.  No bottom reflection of `ν` and no shortness of the other rows is assumed.
Used by 2.5 and 2.6: the decoded section of a seed construction is lawful, its full-scope owners
being short by how the field layer builds their profiles (not by the normal form, whose
representatives have finite parts up to `K + 1`) and each inherited owner satisfying its mapped
locality. -/
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
a witness bounded by `K` that sends a label to bottom only if it is bottom, then `ν ∘ p` is
lawful: the section theorem with every owner on the branch of the mapped locality
(`Label.TransformsTo.map_of_bot_reflecting`).  Used by 2.5 and 2.6: the strongly coded
representative of the boundary labels (`Label.strongEncode`) is lawful. -/
theorem map_of_bot_reflecting (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) : R.IsLawful (ν ∘ p) :=
  hp.map_of_isShort_or hK hν fun s ↦ .inr (TransformsTo.map_of_bot_reflecting
    (grade := fun d : D.below (D.gradedIndex s) ↦ D.grade d) (E := R.row s) (p := fun d ↦ p d)
    (c := ⟨s, D.mem_below_gradedIndex s⟩) (grade_le_of_mem_below s) (hK s) (hp.orderly s)
    (hp.locality s) hν hbot)

end IsLawful

/-- **Capping a labelling lawful below a pair** [Kni26, Lemma 2.5.8]: if the cap `c` is
self-visible at the grade of every cell below `X` whose label is at least `c`, the capped
labelling is lawful below `X`. -/
theorem IsLawfulBelow.min_const {X : Finset α × ℕ} {r : D.below X → Label.{u}}
    (hr : R.IsLawfulBelow X r) {c : Label.{u}}
    (hc : ∀ d : D.below X, c ≤ r d → IsSelfVisible (D.grade d) c) :
    R.IsLawfulBelow X fun d ↦ min (r d) c :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hr).min_const hc)

/-- **Capping a labelling lawful below a pair at a cap self-visible at its grade**, the special
case of [Kni26, Lemma 2.5.8] at the grade of `X`.  Used by 2.5: each lift of a prescription caps
the ambient labelling at the lift's cap, a label self-visible at the target grade. -/
theorem IsLawfulBelow.min_const_of_isSelfVisible {X : Finset α × ℕ} {r : D.below X → Label.{u}}
    (hr : R.IsLawfulBelow X r) {c : Label.{u}} (hc : IsSelfVisible X.2 c) :
    R.IsLawfulBelow X fun d ↦ min (r d) c :=
  hr.min_const fun d _ ↦ hc.mono d.2.2

end VaughtConjecture.CellScheme.Rows
