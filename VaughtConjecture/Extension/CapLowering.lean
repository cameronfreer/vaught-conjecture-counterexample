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

**The theorem** (`StageType.IsLegal.capLowering`).  Cap lowering (CL), stated in the docstring of
`StageType.HasCoupledGatedPinnedExtensions`, holds for every legal private type.  Let `P` be a
legal stage type on `n > 0` points, `(F, n - 1)` a graded face of `P`, `c` a cap self-visible at
`n`, and `p` a labelling lawful below `(F, n - 1)` in the cap ball of the labelling of `P` at `c`.
For every cell `C` of grade `n` and every label `v ≥ c`, some lawful labelling of `P` extends `p`,
lies in that cap ball, and is at most `v` at `C`.

**The proof** (`StageType.IsLegal.exists_capLowering`).
1. Bountifulness of `P` from `(F, n - 1)` to `(univ, n)` at the cap `c` lifts `p` to a lawful
   labelling `r₁` of `P` in the cap ball of the labelling of `P` at `c`.
2. Capping `r₁` at `c` at the cells of grade `n` only keeps it lawful
   (`CellScheme.Rows.IsLawful.capTopGrade`).  No grade exceeds `n`, so the locality at a cell of
   grade `n` is that of `r₁` capped at `c` (`Label.TransformsTo.min_const`); the cells below a
   cell of lower grade have lower grade, so its locality does not change; and availability
   compares cells of equal grade.
3. The cells below `(F, n - 1)` have grade below `n`, so the result extends `p`.  Capping at `c`
   does not change the observation capped at `c`, so the result lies in the cap ball.  At every
   cell of grade `n` it is at most `c ≤ v`.

The value `v` plays no role beyond `c ≤ v`: the cap is lowered to `c` itself.

**What this does not show.**  (CL) is a statement about the private type alone.  It was recorded
as the open point of the coupled gated pinned extension property: a strengthening of what the
construction of the display needs at a lift from a coatom containing the new point, not shown
necessary and not shown sufficient.  Since (CL) holds for every legal private type, no failure of
that property comes from (CL).  Nothing is proved here about the property itself, which is open,
or about (R1).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {r : ι → Label.{u}}

/-- **Capping the top grade.**  If every grade is at most `N` and `c` is self-visible at `N`, then
capping a lawful section at `c` at the cells of grade `N` only, and keeping it at the others, gives
a lawful section.  At a cell of grade `N` the locality is that of `r` capped at `c`
(`Label.TransformsTo.min_const`); below a cell of lower grade nothing changes. -/
theorem IsLawful.capTopGrade (hr : R.IsLawful r) {N : ℕ} (hN : ∀ d, D.grade d ≤ N)
    {c : Label.{u}} (hc : IsSelfVisible N c) :
    R.IsLawful fun d ↦ if D.grade d = N then min (r d) c else r d where
  orderly d := by
    split_ifs with h
    · exact (hr.orderly d).min (h ▸ hc)
    · exact hr.orderly d
  locality s := by
    by_cases hs : D.grade s = N
    · have := (hr.locality s).min_const (fun d ↦ hN d.1) hc
      convert this using 2 with d
      simp only [hs, ite_true]
      split_ifs with hd
      · rw [min_min_min_comm, min_self]
      · rw [min_assoc]
    · convert hr.locality s using 2 with d
      have hd : D.grade d.1 ≠ N := fun h ↦ hs (le_antisymm (hN s) (h ▸ d.2.2))
      simp only [hs, hd, ite_false]
  availability s t hst hg := by
    obtain ⟨u, hu, hle⟩ := hr.availability s t hst hg
    refine ⟨u, hu, ?_⟩
    have hgu : D.grade u = D.grade s := (congrArg Prod.snd hu).trans hg.symm
    by_cases h : D.grade s = N
    · simp only [h, hgu, ite_true]
      exact min_le_min_right c hle
    · simp only [h, hgu, ite_false]
      exact hle

/-- A labelling of all cells lawful below a pair above every cell is lawful. -/
theorem isLawful_of_isLawfulBelow {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hall : ∀ d, d ∈ D.below X) (h : R.IsLawfulBelow X (fun d ↦ w d)) : R.IsLawful w := by
  obtain ⟨ho, hl, ha⟩ := isLawfulBelow_iff_forall.mp h
  exact ⟨fun d ↦ ho d (hall d), fun s ↦ hl s (hall s), fun s t hst hg ↦ ha s t (hall t) hst hg⟩

end CellScheme.Rows

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- **Cap lowering for a legal private type.**  Let `P` be a legal stage type on `n > 0` points,
`(F, n - 1)` a graded face of `P`, `c` a cap self-visible at `n`, and `p` a labelling lawful below
`(F, n - 1)` in the cap ball of the labelling of `P` at `c`.  Some lawful labelling `r` of `P`
extends `p`, lies in the cap ball of the labelling of `P` at `c`, and is at most `c` at every cell
of grade `n`: lift `p` by bountifulness from `(F, n - 1)` to `(univ, n)`, then cap the cells of
grade `n` at `c` (`CellScheme.Rows.IsLawful.capTopGrade`). -/
theorem IsLegal.exists_capLowering {P : StageType.{u} α n} (hP : P.IsLegal)
    {F : Finset (Fin n)} (hF : (F, n - 1) ∈ P.toCellScheme.gradedFaces) (hn : 0 < n)
    {c : Label.{u}} (hc : IsSelfVisible n c) {p : P.toCellScheme.below (F, n - 1) → Label.{u}}
    (hp : p ∈ P.rows.capBall (F, n - 1) c (fun d ↦ P.label d)) :
    ∃ r : Fin P.card → Label.{u}, P.rows.IsLawful r ∧
      (∀ d : P.toCellScheme.below (F, n - 1), r d = p d) ∧
      (∀ d, min (r d) c = min (P.label d) c) ∧
      ∀ d, P.toCellScheme.grade d = n → r d ≤ c := by
  have hY : ((univ : Finset (Fin n)), n) ∈ P.toCellScheme.gradedFaces :=
    ⟨P.univ_mem_faces, hn, by simp⟩
  have hXY : (F, n - 1) ≤ ((univ : Finset (Fin n)), n) := ⟨subset_univ _, Nat.sub_le n 1⟩
  have hall : ∀ d, d ∈ P.toCellScheme.below ((univ : Finset (Fin n)), n) :=
    fun d ↦ ⟨subset_univ _, P.grade_le d⟩
  obtain ⟨q', hq', hcap, hres⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (hP.isBountiful hF hY hXY) c hc p (fun d ↦ P.label d) hp.1 (P.isLawful.isLawfulBelow _)
    fun d ↦ (hp.2 d).symm
  set r₁ : Fin P.card → Label.{u} := fun d ↦ q' ⟨d, hall d⟩ with hr₁
  have hlaw : P.rows.IsLawful r₁ :=
    CellScheme.Rows.isLawful_of_isLawfulBelow hall (by convert hq' using 1)
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

/-- **Cap lowering (CL) at a cell of grade `n`**, in the form of the docstring of
`StageType.HasCoupledGatedPinnedExtensions`: for a legal private type `P`, a face `F` of `n - 1`
points (a graded face at grade `n - 1`), a cap `c` self-visible at `n`, a labelling `p` lawful
below `(F, n - 1)` in the cap ball of the labelling of `P` at `c`, a cell `C` of grade `n`, and a
label `v ≥ c`, some lawful labelling of `P` extends `p`, lies in that cap ball, and is at most `v`
at `C`. -/
theorem IsLegal.capLowering {P : StageType.{u} α n} (hP : P.IsLegal)
    {F : Finset (Fin n)} (hF : (F, n - 1) ∈ P.toCellScheme.gradedFaces) (hn : 0 < n)
    {c : Label.{u}} (hc : IsSelfVisible n c) {p : P.toCellScheme.below (F, n - 1) → Label.{u}}
    (hp : p ∈ P.rows.capBall (F, n - 1) c (fun d ↦ P.label d)) {C : Fin P.card}
    (hC : P.toCellScheme.grade C = n) {v : Label.{u}} (hcv : c ≤ v) :
    ∃ r : Fin P.card → Label.{u}, P.rows.IsLawful r ∧
      (∀ d : P.toCellScheme.below (F, n - 1), r d = p d) ∧
      (∀ d, min (r d) c = min (P.label d) c) ∧ r C ≤ v := by
  obtain ⟨r, hr, hres, hcap, htop⟩ := hP.exists_capLowering hF hn hc hp
  exact ⟨r, hr, hres, hcap, (htop C hC).trans hcv⟩

end StageType

end VaughtConjecture
