/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Stage.Legal

/-!
# Cap lowering for legal private types

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate); the coupled
gated pinned extension property of `VaughtConjecture.Extension.GatedExtension`.

**The theorems.**
* `StageType.IsLegal.capLowering`: cap lowering (CL), as stated in the docstring of
  `StageType.HasCoupledGatedPinnedExtensions`, holds for every legal private type on `n ≥ 2`
  points.  Let `P` be a legal stage type on `n` points, `(F, n - 1)` a graded face of `P`, `c` a
  cap self-visible at `n`, and `p` a labelling lawful below `(F, n - 1)` in the cap ball of the
  labelling of `P` at `c`.  For every cell `C` of grade `n` and every label `v ≥ c`, some lawful
  labelling of `P` extends `p`, lies in that cap ball, and is at most `v` at `C`.  At `n = 1` the
  statement is vacuous, since a graded face `(F, n - 1)` needs `0 < n - 1`; the property uses only
  `n ≥ 2` (its arities satisfy `m + 1 < n`).
* `StageType.IsLegal.capLowering_of_isLawful`: the same with an arbitrary lawful labelling `q` of
  `P` as the ambient, in place of the labelling of `P`.
* `StageType.IsLegal.capLowering_eq_of_isLawful`: when `c ≤ q C`, the lowered value at `C` is
  exactly `c`.

**The proof** (`StageType.IsLegal.exists_capLowering_of_isLawful`).
1. Bountifulness of `P` from `(F, n - 1)` to `(univ, n)` at the cap `c` lifts `p` to a lawful
   labelling `r₁` of `P` in the cap ball of `q` at `c`.
2. Capping `r₁` at `c` at the cells of grade `n` only keeps it lawful
   (`CellScheme.Rows.IsLawful.capTopGrade`).
3. The cells below `(F, n - 1)` have grade below `n`, so the result extends `p`.  Capping at `c`
   does not change the observation capped at `c`, so the result lies in the cap ball.  At every
   cell of grade `n` it is at most `c`.

**What the statement says.**  `capLowering` is the private-face half of what the display needs at
a lift from a coatom containing the new point, in the only range where that half can hold.  The
bound `≤ v` is trivial: the lowered labelling is at most `c` at every cell of grade `n`, so (CL)
for every `v ≥ c` is its case `v = c` followed by `c ≤ v` (the proof of `capLowering`).  When
`c ≤ P.label C`, no labelling in the cap ball is below `c` at `C`, and the lowered value at `C` is
exactly `c` (`capLowering_eq_of_isLawful`); the case `v < c`, which the hypothesis `c ≤ v`
excludes, has no solution there.  So proving (CL) as stated does not establish that the open
requirement of the construction is satisfied.

**The requirement at a forcing lift.**  `StageType.HasCoupledGatedPinnedExtensions` asks for a
legal display.  At a forcing lift this is the bountifulness of the display: `CappedLift` from a
coatom `(F ∪ {y}, n)`, `y` the new point, to `(univ, n)`, for every cap `c` self-visible at `n` and
every lawful ambient labelling of the display, not only its own labelling.  It has four parts.
1. **The private half at an arbitrary ambient.**  The private face of a lawful labelling of the
   display is an arbitrary lawful labelling of `P`.  This half is compiled here
   (`capLowering_of_isLawful`).
2. **Whether the readings of the donor cells or of the anchors can force the gate below some
   `v < c` while the ambient cap is at least `c`.**  The gate dominates the cap
   (`StageType.CoupledGatedExtension.cap_le_gate`), so then no lift exists.  This is open; it
   cannot happen at the instance of `VaughtConjecture.Extension.CoupledGateInstance`.
3. **Joint lawfulness.**  The lowered private labelling must extend to one labelling of the
   display lawful below `(univ, n)`, jointly with the gate, the twins, the donor cells, and the
   cells of grade `n` that contain the new point.  `capLowering` caps every private cell of grade
   `n` at `c`, a top-grade anchor `z` included, which changes the anchored readings
   `vr_n(label z, i)`.  This is open.
4. **The rows of the display.**  For every anchored legal donor, rows satisfying
   `CellScheme.Rows.IsGate` and `CellScheme.Rows.TwinsReadGate` must exist.  This is open.

The open point is therefore the bountifulness of the display at lifts from coatoms containing the
new point, jointly over all its cells and at every lawful ambient labelling.  Nothing is proved
here about the property itself, which is open, or about (R1).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **Cap lowering for a legal private type, at a lawful ambient.**  Let `P` be a legal stage type
on `n ≥ 2` points, `(F, n - 1)` a graded face of `P`, `c` a cap self-visible at `n`, `q` a lawful
labelling of `P`, and `p` a labelling lawful below `(F, n - 1)` in the cap ball of `q` at `c`.
Some lawful labelling `r` of `P` extends `p`, lies in the cap ball of `q` at `c`, and is at most
`c` at every cell of grade `n`: lift `p` by bountifulness from `(F, n - 1)` to `(univ, n)`, then
cap the cells of grade `n` at `c` (`CellScheme.Rows.IsLawful.capTopGrade`). -/
theorem IsLegal.exists_capLowering_of_isLawful {P : StageType.{u} α n} (hP : P.IsLegal)
    {F : Finset (Fin n)} (hF : (F, n - 1) ∈ P.toCellScheme.gradedFaces) (hn : 0 < n)
    {c : Label.{u}} (hc : IsSelfVisible n c) {q : Fin P.card → Label.{u}}
    (hq : P.rows.IsLawful q) {p : P.toCellScheme.below (F, n - 1) → Label.{u}}
    (hp : p ∈ P.rows.capBall (F, n - 1) c (fun d ↦ q d)) :
    ∃ r : Fin P.card → Label.{u}, P.rows.IsLawful r ∧
      (∀ d : P.toCellScheme.below (F, n - 1), r d = p d) ∧
      (∀ d, min (r d) c = min (q d) c) ∧
      ∀ d, P.toCellScheme.grade d = n → r d ≤ c := by
  have hY : ((univ : Finset (Fin n)), n) ∈ P.toCellScheme.gradedFaces :=
    ⟨P.univ_mem_faces, hn, by simp⟩
  have hXY : (F, n - 1) ≤ ((univ : Finset (Fin n)), n) := ⟨subset_univ _, Nat.sub_le n 1⟩
  have hall : ∀ d, d ∈ P.toCellScheme.below ((univ : Finset (Fin n)), n) :=
    fun d ↦ ⟨subset_univ _, P.grade_le d⟩
  obtain ⟨q', hq', hcap, hres⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (hP.isBountiful hF hY hXY) c hc p (fun d ↦ q d) hp.1 (hq.isLawfulBelow _)
    fun d ↦ (hp.2 d).symm
  set r₁ : Fin P.card → Label.{u} := fun d ↦ q' ⟨d, hall d⟩
  have hlaw : P.rows.IsLawful r₁ := hq'.isLawful hall
  refine ⟨_, hlaw.capTopGrade P.grade_le hc, fun d ↦ ?_, fun d ↦ ?_, fun d hd ↦ ?_⟩
  · have hd : P.toCellScheme.grade d.1 ≠ n := fun h ↦ by
      have : P.toCellScheme.grade d.1 ≤ n - 1 := d.2.2
      omega
    simp only [hd, ite_false]
    exact hres d
  · have h := hcap ⟨d, hall d⟩
    split_ifs
    · rw [min_assoc, min_self]; exact h
    · exact h
  · simp only [hd, ite_true]
    exact min_le_right _ _

/-- **Cap lowering for a legal private type**: `IsLegal.exists_capLowering_of_isLawful` at the
labelling of `P` as the ambient. -/
theorem IsLegal.exists_capLowering {P : StageType.{u} α n} (hP : P.IsLegal)
    {F : Finset (Fin n)} (hF : (F, n - 1) ∈ P.toCellScheme.gradedFaces) (hn : 0 < n)
    {c : Label.{u}} (hc : IsSelfVisible n c) {p : P.toCellScheme.below (F, n - 1) → Label.{u}}
    (hp : p ∈ P.rows.capBall (F, n - 1) c (fun d ↦ P.label d)) :
    ∃ r : Fin P.card → Label.{u}, P.rows.IsLawful r ∧
      (∀ d : P.toCellScheme.below (F, n - 1), r d = p d) ∧
      (∀ d, min (r d) c = min (P.label d) c) ∧
      ∀ d, P.toCellScheme.grade d = n → r d ≤ c :=
  hP.exists_capLowering_of_isLawful hF hn hc P.isLawful hp

/-- **Cap lowering (CL) at a cell of grade `n`, at a lawful ambient**: for a legal private type `P`
on `n ≥ 2` points, a graded face `(F, n - 1)` (so `F` has at least `n - 1` points), a cap `c`
self-visible at `n`, a lawful labelling `q` of `P`, a labelling `p` lawful below `(F, n - 1)` in
the cap ball of `q` at `c`, a cell `C` of grade `n`, and a label `v ≥ c`, some lawful labelling of
`P` extends `p`, lies in that cap ball, and is at most `v` at `C`.  This is the private-face half
of what the display needs at a lift from a coatom containing the new point, at the ambient whose
private face is `q`. -/
theorem IsLegal.capLowering_of_isLawful {P : StageType.{u} α n} (hP : P.IsLegal)
    {F : Finset (Fin n)} (hF : (F, n - 1) ∈ P.toCellScheme.gradedFaces) (hn : 0 < n)
    {c : Label.{u}} (hc : IsSelfVisible n c) {q : Fin P.card → Label.{u}}
    (hq : P.rows.IsLawful q) {p : P.toCellScheme.below (F, n - 1) → Label.{u}}
    (hp : p ∈ P.rows.capBall (F, n - 1) c (fun d ↦ q d)) {C : Fin P.card}
    (hC : P.toCellScheme.grade C = n) {v : Label.{u}} (hcv : c ≤ v) :
    ∃ r : Fin P.card → Label.{u}, P.rows.IsLawful r ∧
      (∀ d : P.toCellScheme.below (F, n - 1), r d = p d) ∧
      (∀ d, min (r d) c = min (q d) c) ∧ r C ≤ v := by
  obtain ⟨r, hr, hres, hcap, htop⟩ := hP.exists_capLowering_of_isLawful hF hn hc hq hp
  exact ⟨r, hr, hres, hcap, (htop C hC).trans hcv⟩

/-- **The lowered value is the cap**: under the hypotheses of `IsLegal.capLowering_of_isLawful`,
when `c ≤ q C` the lowered labelling is exactly `c` at `C`.  Its value at `C` is at most `c`, and
its observation capped at `c` is that of `q`, which is `c`. -/
theorem IsLegal.capLowering_eq_of_isLawful {P : StageType.{u} α n} (hP : P.IsLegal)
    {F : Finset (Fin n)} (hF : (F, n - 1) ∈ P.toCellScheme.gradedFaces) (hn : 0 < n)
    {c : Label.{u}} (hc : IsSelfVisible n c) {q : Fin P.card → Label.{u}}
    (hq : P.rows.IsLawful q) {p : P.toCellScheme.below (F, n - 1) → Label.{u}}
    (hp : p ∈ P.rows.capBall (F, n - 1) c (fun d ↦ q d)) {C : Fin P.card}
    (hC : P.toCellScheme.grade C = n) (hcC : c ≤ q C) :
    ∃ r : Fin P.card → Label.{u}, P.rows.IsLawful r ∧
      (∀ d : P.toCellScheme.below (F, n - 1), r d = p d) ∧
      (∀ d, min (r d) c = min (q d) c) ∧ r C = c := by
  obtain ⟨r, hr, hres, hcap, htop⟩ := hP.exists_capLowering_of_isLawful hF hn hc hq hp
  refine ⟨r, hr, hres, hcap, le_antisymm (htop C hC) ?_⟩
  have h := hcap C
  rw [min_eq_right hcC, min_eq_left (htop C hC)] at h
  exact h.ge

/-- **Cap lowering (CL) at a cell of grade `n`**, in the form of the docstring of
`StageType.HasCoupledGatedPinnedExtensions`: for a legal private type `P` on `n ≥ 2` points, a
graded face `(F, n - 1)` (so `F` has at least `n - 1` points), a cap `c` self-visible at `n`, a
labelling `p` lawful below `(F, n - 1)` in the cap ball of the labelling of `P` at `c`, a cell `C`
of grade `n`, and a label `v ≥ c`, some lawful labelling of `P` extends `p`, lies in that cap
ball, and is at most `v` at `C`.

This is the private-face half of what the display needs at a lift from a coatom containing the new
point, with the labelling of `P` as the ambient, in the only range `v ≥ c` where that half can
hold; it is its case `v = c` followed by `c ≤ v`.  It does not establish that the construction's
open requirement is satisfied.  It does not address whether the readings of the donor cells or of
the anchors can force the gate below some `v < c`, the joint lawfulness of the whole display at
every lawful ambient, or the existence of its rows (see the module docstring). -/
theorem IsLegal.capLowering {P : StageType.{u} α n} (hP : P.IsLegal)
    {F : Finset (Fin n)} (hF : (F, n - 1) ∈ P.toCellScheme.gradedFaces) (hn : 0 < n)
    {c : Label.{u}} (hc : IsSelfVisible n c) {p : P.toCellScheme.below (F, n - 1) → Label.{u}}
    (hp : p ∈ P.rows.capBall (F, n - 1) c (fun d ↦ P.label d)) {C : Fin P.card}
    (hC : P.toCellScheme.grade C = n) {v : Label.{u}} (hcv : c ≤ v) :
    ∃ r : Fin P.card → Label.{u}, P.rows.IsLawful r ∧
      (∀ d : P.toCellScheme.below (F, n - 1), r d = p d) ∧
      (∀ d, min (r d) c = min (P.label d) c) ∧ r C ≤ v :=
  hP.capLowering_of_isLawful hF hn hc P.isLawful hp hC hcv

end StageType

end VaughtConjecture
