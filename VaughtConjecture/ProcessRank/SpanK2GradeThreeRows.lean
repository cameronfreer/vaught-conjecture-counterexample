/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeThreeLabels

/-!
# The row conditions of the mirror theorem on the grade-three scheme of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the one-member reading, the common shadow
and the twin hypotheses of the lift theorem over a mirrored attachment
(`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed`: `hreadMember`, `hshadow`, `htwinAbove`),
stated literally for the grade-three scheme `ProcessRank.k2Grade3`.  The parameters are
instantiated as at the grade two: the scheme `T` is `k2Grade3`, the attachment `Att` is the
attachment of the test with `K = 2`, the profiles `Pf` are the rank members at the height `8` with
their rank profiles `prof`, the attachment cells `att e` are the old cells
`ProcessRank.k2Att3 e` and the ladder points `lad v` are the old cells `ProcessRank.k2Lad3 v`.

The cells of full scope of `k2Grade3` at a grade at least two are the grade-two controllers, old
cells read as in `k2Grade2`, and the grade-three controllers, at the grade three, reading the old
cells through the sections `ProcessRank.k2Sec3` (`ProcessRank.k2Grade3_full_cases`).  The
attachment has no cell of grade three, so the shadows and twins are at the grade two.  Compiled
here (theorem named):
* **one-member reading** (`ProcessRank.k2Grade3_hreadMember`), from
  `ProcessRank.k2Grade2_hreadMember` and `ProcessRank.k2Sec3_readMember`;
* **common shadow** (`ProcessRank.k2Grade3_hshadow`), from `ProcessRank.k2Grade2_hshadow` and the
  cross-grade shadow `ProcessRank.k2Sec3_shadow`;
* **twin** (`ProcessRank.k2Grade3_htwinAbove`), from `ProcessRank.k2Grade2_htwinAbove` and the
  controller domination `ProcessRank.k2Sec3_twinAbove`.

Open: the remaining premises of the mirror theorem at the grade three and the mixed-face lifts at
the grade three, the grade four, legality of the completed scheme, the four-point span of mutual
rigidity of the test pair, and the countable upper bound on the Scott classes.  None of these is
claimed here.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex 8 (Scheme.rankProf k2AttachmentBase.S 8) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))

/-- The attachment cells of the grade-three scheme. -/
noncomputable abbrev k2Att3 (e : Fin k2AttachmentBase.{u}.S.card) : Fin k2Grade3.{u}.card :=
  Fin.castAdd _ (k2Att e)

/-- The ladder points of the grade-three scheme. -/
noncomputable abbrev k2Lad3
    (v : Scheme.LadderPt k2AttachmentBase.{u}.S (Scheme.RankMember k2AttachmentBase.{u}.S 8) 8) :
    Fin k2Grade3.{u}.card :=
  Fin.castAdd _ (k2Lad v)

/-- Old cells of the grade-three scheme read old cells as in the grade-two scheme. -/
theorem k2Grade3_rowAt_castAdd_castAdd (a d : Fin k2Grade2.{u}.card) :
    k2Grade3.{u}.rowAt (Fin.castAdd _ a) (Fin.castAdd _ d) = k2Grade2.{u}.rowAt a d :=
  Scheme.rowAt_appendFullCells_castAdd _ _

/-- Old cells of the grade-three scheme keep their graded indices. -/
theorem k2Grade3_gradedIndex_castAdd (z : Fin k2Grade2.{u}.card) :
    k2Grade3.{u}.toCellScheme.gradedIndex (Fin.castAdd _ z) =
      k2Grade2.{u}.toCellScheme.gradedIndex z :=
  Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ z

/-- The grade-three controllers lie at `(univ, 3)`. -/
theorem k2Grade3_gradedIndex_natAdd (i : Fin k2Cat3.{u}.card) :
    k2Grade3.{u}.toCellScheme.gradedIndex (Fin.natAdd _ i) = ((univ : Finset (Fin 4)), 3) :=
  Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i

/-- **The cells of full scope of the grade-three scheme**: old cells, at the same graded index in
the grade-two scheme, or grade-three controllers, at the grade three. -/
theorem k2Grade3_full_cases {f : Fin k2Grade3.{u}.card} {K : ℕ}
    (hf : k2Grade3.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K)) :
    (∃ g, f = Fin.castAdd _ g ∧
        k2Grade2.{u}.toCellScheme.gradedIndex g = ((univ : Finset (Fin 4)), K)) ∨
      K = 3 ∧ ∃ i, f = Fin.natAdd _ i := by
  induction f using Fin.addCases with
  | left g => exact .inl ⟨g, rfl, (k2Grade3_gradedIndex_castAdd g).symm.trans hf⟩
  | right i =>
    exact .inr ⟨(congrArg Prod.snd ((k2Grade3_gradedIndex_natAdd i).symm.trans hf)).symm, i, rfl⟩

/-- Every attachment cell has grade at most two. -/
theorem k2Att_grade_le (e : Fin k2AttachmentBase.{u}.S.card) :
    k2AttachmentBase.{u}.S.toCellScheme.grade e ≤ 2 :=
  (by decide : ∀ d : Fin 8, attGrade d ≤ 2) e

/-- **The one-member reading**, in the form of the hypothesis `hreadMember` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for the grade-three scheme. -/
theorem k2Grade3_hreadMember : ∀ (f : Fin k2Grade3.{u}.card) K,
    k2Grade3.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember k2AttachmentBase.{u}.S 8) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, k2Grade3.{u}.rowAt f (k2Lad3 v) = Φ (idx b v)) ∧
        ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e ≤ K →
          k2Grade3.{u}.rowAt f (k2Att3 e) = Φ (Scheme.rankProf k2AttachmentBase.S 8 b e) := by
  intro f K hf hK
  rcases k2Grade3_full_cases hf with ⟨g, rfl, hg⟩ | ⟨rfl, i, rfl⟩
  · obtain ⟨b, Φ, hΦ, hΦ0, hl, ha⟩ := k2Grade2_hreadMember g K hg hK
    exact ⟨b, Φ, hΦ, hΦ0, fun v ↦ (k2Grade3_rowAt_castAdd_castAdd _ _).trans (hl v),
      fun e he ↦ (k2Grade3_rowAt_castAdd_castAdd _ _).trans (ha e he)⟩
  · obtain ⟨b, Φ, hΦ, hΦ0, hl, ha⟩ := k2Sec3_readMember (k2Cat3.equivFin.symm i).2
    exact ⟨b, Φ, hΦ, hΦ0, fun v ↦ (k2Grade3_rowAt_natAdd_castAdd i _).trans (hl v),
      fun e _ ↦ (k2Grade3_rowAt_natAdd_castAdd i _).trans (ha e)⟩

/-- **The common shadow**, in the form of the hypothesis `hshadow` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for the grade-three scheme. -/
theorem k2Grade3_hshadow : ∀ (f u : Fin k2Grade3.{u}.card) K k,
    k2Grade3.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) →
    k2Grade3.{u}.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), k) → 2 ≤ k → k ≤ K →
    ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e = k → ∃ v,
      k2Grade3.{u}.rowAt u (k2Lad3 v) = k2Grade3.{u}.rowAt u (k2Att3 e) ∧
        min (k2Grade3.{u}.rowAt f (k2Lad3 v)) (k2Grade3.{u}.rowAt f u) =
          min (k2Grade3.{u}.rowAt f (k2Att3 e)) (k2Grade3.{u}.rowAt f u) := by
  intro f u K k hf hu hk2 hkK e he
  obtain rfl : k = 2 := le_antisymm (he ▸ k2Att_grade_le e) hk2
  obtain ⟨u', rfl, hu'⟩ : ∃ u', u = Fin.castAdd _ u' ∧
      k2Grade2.{u}.toCellScheme.gradedIndex u' = ((univ : Finset (Fin 4)), 2) := by
    rcases k2Grade3_full_cases hu with h | ⟨h, -⟩
    · exact h
    · omega
  rcases k2Grade3_full_cases hf with ⟨f', rfl, hf'⟩ | ⟨-, i, rfl⟩
  · obtain ⟨v, h1, h2⟩ := k2Grade2_hshadow f' u' K 2 hf' hu' hk2 hkK e he
    refine ⟨v, ?_, ?_⟩
    · rw [k2Grade3_rowAt_castAdd_castAdd, k2Grade3_rowAt_castAdd_castAdd]
      exact h1
    · rw [k2Grade3_rowAt_castAdd_castAdd, k2Grade3_rowAt_castAdd_castAdd,
        k2Grade3_rowAt_castAdd_castAdd]
      exact h2
  · obtain ⟨v, h1, h2⟩ := k2Sec3_shadow (k2Cat3.equivFin.symm i).2 u' 2 hu' le_rfl (by omega) e he
    refine ⟨v, ?_, ?_⟩
    · rw [k2Grade3_rowAt_castAdd_castAdd, k2Grade3_rowAt_castAdd_castAdd]
      exact h1
    · rw [k2Grade3_rowAt_natAdd_castAdd, k2Grade3_rowAt_natAdd_castAdd,
        k2Grade3_rowAt_natAdd_castAdd]
      exact h2

/-- **The twin**, in the form of the hypothesis `htwinAbove` of
`ProcessRank.MirrorAttachment.cappedLift_mirror_mixed` for the grade-three scheme. -/
theorem k2Grade3_htwinAbove : ∀ (f : Fin k2Grade3.{u}.card) K k,
    k2Grade3.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), K) →
    2 ≤ k → k ≤ K → ∀ e, k2AttachmentBase.{u}.S.toCellScheme.grade e = k →
      ∃ et, k2Grade3.{u}.toCellScheme.gradedIndex et = ((univ : Finset (Fin 4)), k) ∧
        k2Grade3.{u}.rowAt f (k2Att3 e) ≤ k2Grade3.{u}.rowAt f et := by
  intro f K k hf hk2 hkK e he
  obtain rfl : k = 2 := le_antisymm (he ▸ k2Att_grade_le e) hk2
  rcases k2Grade3_full_cases hf with ⟨f', rfl, hf'⟩ | ⟨-, i, rfl⟩
  · obtain ⟨et, het, hle⟩ := k2Grade2_htwinAbove f' K 2 hf' hk2 hkK e he
    refine ⟨Fin.castAdd _ et, (k2Grade3_gradedIndex_castAdd et).trans het, ?_⟩
    rw [k2Grade3_rowAt_castAdd_castAdd, k2Grade3_rowAt_castAdd_castAdd]
    exact hle
  · obtain ⟨et, het, hle⟩ := k2Sec3_twinAbove (k2Cat3.equivFin.symm i).2 2 hk2 (by omega) e he
    refine ⟨Fin.castAdd _ et, (k2Grade3_gradedIndex_castAdd et).trans het, ?_⟩
    rw [k2Grade3_rowAt_natAdd_castAdd, k2Grade3_rowAt_natAdd_castAdd]
    exact hle

end VaughtConjecture.ProcessRank
