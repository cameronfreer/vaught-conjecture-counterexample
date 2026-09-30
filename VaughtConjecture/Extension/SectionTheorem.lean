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

* **Capping** at a label `c` self-visible at `K` (`CellScheme.Rows.IsLawful.min_const`, and
  `CellScheme.Rows.IsLawfulBelow.min_const` below a pair, at a cap self-visible at its grade):
  [Kni26, Lemma 2.5.8].  Capping at a cutoff that is not self-visible need not keep lawfulness.
* **A bottom-reflecting witness** `ν` bounded by `K`
  (`CellScheme.Rows.IsLawful.map_of_bot_reflecting`): `ν ∘ p` is lawful when `ν` sends a label to
  bottom only if it is bottom.  At each owner the capped witness of its locality is followed by
  `ν`, by the library's guarded composition.
* **The section theorem** (`CellScheme.Rows.IsLawful.map_of_isShort_or`, roadmap, 3.1): for a
  witness `ν` bounded by `K`, `ν ∘ p` is lawful provided every owner (a cell with its row) is
  **short** (every entry of its row is short at its grade, `Label.IsShort`) or satisfies the
  **mapped locality** `E(s) ⇒ (d ↦ min (ν (p d)) (ν (p s)))`.  Orderliness and availability pass
  through `ν` once; locality is proved owner by owner, at a short owner by
  `Label.TransformsTo.map_of_isShort` and at any other owner by the hypothesis.  Neither
  lawfulness of `ν ∘ p`, nor bottom reflection of `ν`, nor shortness of every row is assumed.

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

/-- **Capping a lawful section** [Kni26, Lemma 2.5.8].  If the grades are at most `K` and `c` is
self-visible at `K`, the section capped at `c` is lawful.  Used by 2.5 through
`CellScheme.Rows.IsLawfulBelow.min_const`. -/
theorem min_const (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K) {c : Label.{u}}
    (hc : IsSelfVisible K c) : R.IsLawful fun d ↦ min (p d) c where
  orderly d := (hp.orderly d).min (hc.mono (hK d))
  locality s := by
    have h := (hp.locality s).min_const (fun d ↦ (grade_le_of_mem_below s d).trans (hK s)) hc
    convert h using 2 with d
    rw [min_min_min_comm, min_self]
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hp.availability s t hst hg
    exact ⟨u, hu, min_le_min_right c hle⟩

/-- **Lawfulness through a bottom-reflecting witness.**  If the grades are at most `K` and `ν` is
a witness bounded by `K` that sends a label to bottom only if it is bottom, then `ν ∘ p` is
lawful.  Used by 2.5 and 2.6: the strongly coded representative of the boundary labels
(`Label.strongEncode`) is lawful. -/
theorem map_of_bot_reflecting (hp : R.IsLawful p) (hK : ∀ d, D.grade d ≤ K)
    (hν : IsWitness (stepSuppressor K) ν) (hbot : ∀ x, ν x = ⊥ → x = ⊥) : R.IsLawful (ν ∘ p) where
  orderly d := hν.isSelfVisible_apply (hp.orderly d) (by simp [hK d])
  locality s := TransformsTo.map_of_bot_reflecting (grade := fun d : D.below (D.gradedIndex s) ↦
    D.grade d) (E := R.row s) (p := fun d ↦ p d) (c := ⟨s, D.mem_below_gradedIndex s⟩)
    (grade_le_of_mem_below s) (hK s) (hp.orderly s) (hp.locality s) hν hbot
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hp.availability s t hst hg
    exact ⟨u, hu, hν.monotone hle⟩

/-- **The section theorem** (roadmap, Layer 3, 3.1).  Let `p` be lawful, the grades at most `K`,
and `ν` a witness bounded by `K`.  If every owner `s` is short (every entry of its row is short at
the grade of `s`) or satisfies the mapped locality `E(s) ⇒ (d ↦ min (ν (p d)) (ν (p s)))`, then
`ν ∘ p` is lawful.  No bottom reflection of `ν` and no shortness of the other rows is assumed.
Used by 2.5 and 2.6: the decoded section of a seed construction is lawful, its new owners being
short by their support and each inherited owner satisfying its long-row locality. -/
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

end IsLawful

/-- **Capping a labelling lawful below a pair** [Kni26, Lemma 2.5.8]: at a cap self-visible at
the grade of `X`, the capped labelling is lawful below `X`.  Used by 2.5: each lift of a
prescription caps the ambient labelling at the lift's cap, a label self-visible at the target
grade. -/
theorem IsLawfulBelow.min_const {X : Finset α × ℕ} {r : D.below X → Label.{u}}
    (hr : R.IsLawfulBelow X r) {c : Label.{u}} (hc : IsSelfVisible X.2 c) :
    R.IsLawfulBelow X fun d ↦ min (r d) c :=
  isLawfulBelow_iff.mpr ((isLawfulBelow_iff.mp hr).min_const (fun d ↦ d.2.2) hc)

end VaughtConjecture.CellScheme.Rows
