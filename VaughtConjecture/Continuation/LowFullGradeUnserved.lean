/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStepTie

/-!
# The unserved case of the private frontier at every grade, the full grade included

Roadmap, Layer 3 ((R2), the LOW layer at the grade `K = k + 1`).

The owner lowering at a cap (`H2.exists_lowered_at`) and the unserved case of the private frontier
(`StageType.lowStepUnserved_of_le`) were stated below the full grade, `K ≤ k`, at a source-gap
context `t'` on `k + 1` points with the lost point last.  The construction does not use the bound:
its only use is the capped lift from the root into the grade-`K` faces
(`H2.hasCappedLifts_lawfulAt'`), which holds for `K ≤ k + 1`, and `K ≤ k + 1` holds at every context
since the owner is a cell of `t'`.  At `K = k + 1` the owner is the cell of full scope and full
grade (the apex of `t'`); the min-cap construction runs unchanged: the next label `c'` self-visible
at `K` above the cap, `W₂ = min W₁ c'` (largest label at the owner), the capping below the threshold
(`H2.lawfulAt_capBelowAt_of_max`, which uses the owner's own row and availability inside its graded
index `(univ, K)`), and the capped lift back from the root.

* `H2.exists_lowered_at_succ`: the lowered face at a cap `c > ⊥`, at every grade.
* `StageType.lowStepUnserved`: `StageType.LowStepUnserved` holds at every legal source-gap context
  with the lost point last, the full grade `K = k + 1` included.

## References

The LOW layer is the step of [AFK26] at the owner's grade; bountifulness is [Kni26, Definition
2.5.14].
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission CellScheme

variable {α : Ordinal.{u}}

/-- **The lowered face at a cap `c > ⊥`, at every grade** (`H2.exists_lowered_at` without the bound
`K ≤ k`): at a legal source-gap context of grade `K` on `k + 1` points with the lost point last, for
a legal donor with the same root face, every cap `h ≤ c` self-visible at `K`, every context face `L`
and donor face `g` agreeing on the root capped at `h`, with the root cells not labelled `⊤` at most
`c` in `g`, there is a grade-`K` face with the root of `g`, agreeing with `L` capped at `h`, with
frontier at most `c`.  At `K = k + 1` the owner is the apex of `t'`. -/
theorem exists_lowered_at_succ {k K n : ℕ} {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal)
    {g₀ : Fin n ↪ Fin k} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g₀.trans Fin.castSuccEmb) (Fin.last k) o r)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α (k + 1)} (htbleg : tb.IsLegal)
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {h : Label.{u}} (hh : IsSelfVisible K h)
    {L : Fin t'.card → Label.{u}} {g : Fin tb.card → Label.{u}} (hL : LawfulAt t' K L)
    (hg : LawfulAt tb K g)
    (hagr : ∀ x, min (g (StageType.faceCell htbp x)) h = min (L (StageType.faceCell hp x)) h)
    {c : Label.{u}} (hc : IsSelfVisible K c) (hc0 : ⊥ < c) (hhc : h ≤ c)
    (hlow : ∀ x : Fin p.card, p.label x ≠ ⊤ → g (StageType.faceCell htbp x) ≤ c) :
    ∃ W : Fin t'.card → Label.{u}, LawfulAt t' K W ∧
      (∀ x, W (StageType.faceCell hp x) = g (StageType.faceCell htbp x)) ∧
      (∀ d, min (W d) h = min (L d) h) ∧ frontierAt o r K W ≤ c := by
  classical
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hKk : K ≤ k + 1 := hs.grade_owner ▸ t'.grade_le o
  have hCL : HasCappedLifts (StageType.faceCell htbp) (StageType.faceCell hp) K (LawfulAt tb K)
      (LawfulAt t' K) := hasCappedLifts_lawfulAt' hK0 hKk htbleg htbp hleg hp
  obtain ⟨W1, hW1, hW1r, hW1L⟩ := hCL hh hL hg hagr
  by_cases hF : frontierAt o r K W1 ≤ c
  · exact ⟨W1, hW1, hW1r, hW1L, hF⟩
  have hFc : c < frontierAt o r K W1 := not_le.mp hF
  have hct : c ≠ ⊤ := fun e ↦ by rw [e] at hFc; exact not_top_lt hFc
  obtain ⟨c', hc', hcc', hnext⟩ := exists_next_isSelfVisible hc hc0 hct
  have hW1o : c' ≤ W1 o := hnext _ (hFc.trans_le (min_le_left _ _))
  set W2 : Fin t'.card → Label.{u} := fun d ↦ min (W1 d) c' with hW2def
  have hW2 : LawfulAt t' K W2 := lawfulAt_min hW1 hc'
  have hW2o : W2 o = c' := min_eq_right hW1o
  have hmax (d : Fin t'.card) : W2 d ≤ W2 o := hW2o ▸ min_le_right _ _
  set L1 := capBelowAt t' K o r W2 c with hL1def
  have hL1 : LawfulAt t' K L1 := lawfulAt_capBelowAt_of_max hleg hs hW2 hmax hc hc0
  have hroot1 (x : Fin p.card) : min (g (StageType.faceCell htbp x)) c' =
      min (L1 (StageType.faceCell hp x)) c' := by
    by_cases hZ : t'.rowAt o (StageType.faceCell hp x) ≤ thresholdAt t' K o r
    · rw [hL1def, capBelowAt_of_le hZ]
      change _ = min (min (min (W1 _) c') c) c'
      rw [hW1r x]
      have hgx : g (StageType.faceCell htbp x) ≤ c := by
        by_cases hx : p.label x = ⊤
        · exact absurd hZ (not_le.mpr (hs.gap_retained _
            ((StageType.label_faceCell hp x).trans hx)
            (StageType.last_notMem_scope_faceCell hp x)))
        · exact hlow x hx
      rw [min_eq_left (hgx.trans hcc'.le), min_eq_left hgx, min_eq_left (hgx.trans hcc'.le)]
    · rw [hL1def, capBelowAt_of_not_le hZ]
      change _ = min (min (W1 _) c') c'
      rw [hW1r x, min_assoc, min_self]
  obtain ⟨W, hW, hWr, hWL1⟩ := hCL hc' hL1 hg hroot1
  have hhc' : h ≤ c' := hhc.trans hcc'.le
  have hL1h (d : Fin t'.card) : min (L1 d) h = min (W1 d) h := by
    by_cases hZ : t'.rowAt o d ≤ thresholdAt t' K o r
    · rw [hL1def, capBelowAt_of_le hZ]
      change min (min (min (W1 d) c') c) h = _
      rw [min_assoc, min_eq_right hhc, min_assoc, min_eq_right hhc']
    · rw [hL1def, capBelowAt_of_not_le hZ]
      change min (min (W1 d) c') h = _
      rw [min_assoc, min_eq_right hhc']
  have hFL1 : frontierAt o r K L1 ≤ c := by
    have hZr : t'.rowAt o r ≤ thresholdAt t' K o r := le_visibilityReplace (by omega) _
    refine (min_le_right _ _).trans ?_
    rw [hL1def, capBelowAt_of_le hZr, visibilityReplace_min le_rfl, hc.visibilityReplace_eq]
    exact min_le_right _ _
  have hFW : frontierAt o r K W = frontierAt o r K L1 :=
    Label.eq_of_min_eq_of_lt (frontierAt_cap (o := o) (r := r) hc' hWL1).symm
      (hFL1.trans_lt hcc')
  refine ⟨W, hW, hWr, fun d ↦ ?_, hFW ▸ hFL1⟩
  calc min (W d) h = min (min (W d) c') h := by rw [min_assoc, min_eq_right hhc']
    _ = min (min (L1 d) c') h := by rw [hWL1 d]
    _ = min (L1 d) h := by rw [min_assoc, min_eq_right hhc']
    _ = min (W1 d) h := hL1h d
    _ = min (L d) h := hW1L d

end VaughtConjecture.H2

namespace VaughtConjecture.StageType

open Finset Label H2 FieldAdmission

variable {α : Ordinal.{u}} {k K : ℕ}

/-- **The unserved case holds at every grade**: at a legal source-gap context `t'` of grade `K` on
`k + 1` points with the lost point last, with face `p` along the first points, the unserved case of
the private frontier (`StageType.LowStepUnserved`) holds, `K = k + 1` included: the lowered face at
the cap (`H2.exists_lowered_at_succ`, with the context as its own donor). -/
theorem lowStepUnserved {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal)
    {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K Fin.castSuccEmb (Fin.last k) o r)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p) :
    LowStepUnserved K t' (Fin.last k) o r := by
  intro u hu c hc hc0 hroot _ _ _
  have hs' : t'.IsSourceGapContextAt K ((Function.Embedding.refl (Fin k)).trans Fin.castSuccEmb)
      (Fin.last k) o r := by
    convert hs
    exact Function.Embedding.ext fun _ ↦ rfl
  set L : Fin t'.card → Label.{u} := t'.toCellScheme.splice K (fun _ ↦ ⊥) u with hL_def
  have hLle (d : Fin t'.card) (hd : t'.toCellScheme.grade d ≤ K) : L d = u d :=
    CellScheme.splice_of_le hd
  have hL : LawfulAt t' K L :=
    ⟨(CellScheme.Rows.isLawfulBelow_congr (R := t'.rows) (X := ((univ : Finset (Fin (k + 1))), K))
      (w := u) (w' := L) fun d hd ↦
        (hLle d (show t'.toCellScheme.grade d ≤ K from hd.2)).symm).mp hu,
      fun d hd ↦ CellScheme.splice_of_lt (not_le.mp hd)⟩
  have hlow : ∀ x : Fin p.card, p.label x ≠ ⊤ → L (faceCell hp x) ≤ c := fun x hx ↦ by
    by_cases hd : t'.toCellScheme.grade (faceCell hp x) ≤ K
    · rw [hLle _ hd]
      exact hroot _ hd (last_notMem_scope_faceCell hp x) (by rwa [label_faceCell])
    · rw [hL_def, CellScheme.splice_of_lt (not_le.mp hd)]; exact bot_le
  obtain ⟨W, hW, hWr, hWL, hWf⟩ := exists_lowered_at_succ hleg hs' hp hleg hp hc hL hL
    (fun _ ↦ rfl) hc hc0 le_rfl hlow
  refine ⟨W, hW.1, fun d hd ↦ by rw [hWL d, hLle d hd], fun d hd hl ↦ ?_, hWf⟩
  obtain ⟨x, rfl⟩ := exists_faceCell_eq_of_last_notMem hp hl
  rw [hWr x, hLle _ hd]

end VaughtConjecture.StageType
