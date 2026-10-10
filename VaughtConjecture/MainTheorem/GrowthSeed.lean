/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CoatomExtensionTheorem

/-!
# The growth seed

Roadmap, Layer 3 ((R3) and (R4), the amalgam under the controllers of the growth construction).

The controllers of the growth construction are appended over the levels of the profile tower of
a seed (`Seed`, two legal coatom types with a common face).  For a context `t'` on `m + 1` points
whose last point is off the root and spans with the others a closed coatom (`t'` restricts to `p'`
along `Fin.castSuccEmb`), and a legal coface `d` of the root face, the **growth seed**
(`StageType.exists_growthSeed`) is `Seed.ofCoatoms` of `t'` and an **enlarged donor**: a legal
one-point extension of `p'` with face `d` along the root followed by the new point, of top grade
at most that of `t'` (`StageType.exists_pinned_extension_topGrade_le`).  Its amalgam has `t'`
literally as its face along the first coatom and `d` literally as its face along the root followed
by the new point: the context and donor faces of the growth carrier.

**The position is reached by relabelling** (`StageType.exists_extreme_notMem_range`): the root
spans a closed face of `t'`, other than the ground set when the root misses a point, and in the
convex geometry of the plan of `t'` it lies in a coatom `univ.erase x` with `x` extreme
(`Geometry.IsConvexGeometry.exists_coatom`); relabelling `x` last puts the context in the position
above.

**Scope.**  Not used by the main theorem through the levels
(`VaughtConjecture.MainTheorem.GrowthLevelRoute`); kept as reusable mathematics.

## References

Coatom amalgams and pinned extensions are [Kni26, Lemma 4.3.2 and Corollary 4.3.22].
-/

universe u

namespace VaughtConjecture

open Finset StageType

namespace StageType

variable {α : Ordinal.{u}} {m n : ℕ}

/-- **An extreme point off the root**: if the root `e` of a stage type `t'` spans a closed face and
misses a point, some point `x` outside the range of `e` is extreme: `univ.erase x` is a closed
face of `t'`. -/
theorem exists_extreme_notMem_range {t' : StageType.{u} α m} {e : Fin n ↪ Fin m}
    {p : StageType.{u} α n} (hte : restrictFace e t' = some p) (he : ¬ Function.Surjective e) :
    ∃ x, x ∉ Set.range e ∧ univ.erase x ∈ t'.toCellScheme.faces := by
  obtain ⟨hf, -⟩ := (restrictFace_eq_some_iff t' e).mp hte
  have hne : univ.map e ≠ univ := by
    intro h
    apply he
    intro y
    have hy : y ∈ univ.map e := h ▸ mem_univ y
    obtain ⟨a, -, ha⟩ := mem_map.mp hy
    exact ⟨a, ha⟩
  obtain ⟨x, hx, hsub⟩ := t'.isPlan.isConvexGeometry.exists_coatom hf hne
  refine ⟨x, fun ⟨a, ha⟩ ↦ ?_, (Geometry.mem_extremes.mp hx).2⟩
  have := hsub (mem_map_of_mem e (mem_univ a))
  rw [ha] at this
  simp at this

/-- **The growth seed.**  Let `t'` be a legal stage type on `m + 1` points at a limit stage with
face `p'` along the first `m` points, `e₀` a root in those points with face `p`, and `d` a legal
coface of `p` of top grade at most that of `t'`.  Some seed has `t'` as its first coatom type, a
second coatom type of top grade at most that of `t'`, and `d` as the face of its amalgam along the
root followed by the new point. -/
theorem exists_growthSeed (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (m + 1)}
    (ht' : t'.IsLegal) {p' : StageType.{u} α m}
    (hp' : restrictFace Fin.castSuccEmb t' = some p') {e₀ : Fin n ↪ Fin m}
    {p : StageType.{u} α n} (hp : restrictFace e₀ p' = some p) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ p.cofaces) (hdK : d.topGrade ≤ t'.topGrade) :
    ∃ I : Seed.{u} α m, I.left = t' ∧ I.right.topGrade ≤ t'.topGrade ∧
      restrictFace (extendByLast (e₀.trans Fin.castSuccEmb)) I.amalgam = some d := by
  obtain ⟨Q, hQ, hQp', hQd, hQK⟩ := exists_pinned_extension_topGrade_le hα (ht'.restrictFace _ hp')
    hp hd.1 hd.2 ((topGrade_le_of_restrictFace hp').trans le_rfl) hdK
  let I : Seed.{u} α m := Seed.ofCoatoms ht' hQ hp' hQp'
  refine ⟨I, rfl, hQK, ?_⟩
  have hright : restrictFace (Coatom.right m) I.amalgam = some Q := I.restrictFace_right
  rw [← extendByLast_trans, ← restrictFace_trans I.amalgam _ _ hright]
  exact hQd

end StageType

end VaughtConjecture
