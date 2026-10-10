/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.MirrorMixedCopies

/-!
# The copied ladder at a mixed face of a mirrored scheme

Roadmap, Layer 3 ((R3) and (R4), the lifts into the mixed faces, for any scheme over the attachment
mirrored at the mixed faces of the seed).

Let `T` carry ladder points `lad p` of graded index `(univ, 1)` reading one another with the rows
of the ladder (`ladderSource` of the ceiling of the reader at the index of the read point for the
reader's member).  Their copies at a mixed face `U` (`Seed.mCopyLadder`) read one another in the
same way (`Seed.rowAt_mCopyLadder`), so a section lawful below a pair above `(U, 1)` is lawful on
the ladder table there (`Seed.ladderLawful_mCopyLadder`) and has the shape of the table of one
member, or is `⊥` throughout (`Seed.mCopyLadder_exists_shape`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {T : Scheme.{u} (m + 2)}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ I.mixedFaces g, ¬ U ⊆ T.toCellScheme.scope c}
  {U : Finset (Fin (m + 2))}
  {lad : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H →
    Fin T.card}

variable (hmix) in
/-- **The copied ladder** at the mixed face `U`: the copies at `U` of the ladder points. -/
noncomputable def mCopyLadder (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) =
      ((univ : Finset (Fin (m + 2))), 1)) (hU : U ∈ I.mixedFaces g)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    Fin (Scheme.mirror hmix).card :=
  mCopyFull hmix hU (lad p) (hlad p) (one_le_card_of_mem_mixedFaces hU)

theorem gradedIndex_mCopyLadder
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hU : U ∈ I.mixedFaces g)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyLadder hmix hlad hU p) = (U, 1) :=
  gradedIndex_mCopyFull hU _ _ _

/-- **The copied ladder reads itself as the ladder does.** -/
theorem rowAt_mCopyLadder
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hU : U ∈ I.mixedFaces g)
    (p q : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (Scheme.mirror hmix).rowAt (mCopyLadder hmix hlad hU p) (mCopyLadder hmix hlad hU q) =
      T.rowAt (lad p) (lad q) := by
  have hmem : mCopyLadder hmix hlad hU q ∈ (Scheme.mirror hmix).toCellScheme.below
      ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyLadder hmix hlad hU p)) := by
    rw [CellScheme.mem_below, gradedIndex_mCopyLadder, gradedIndex_mCopyLadder]
  rw [Scheme.rowAt_mirror_of_mem hmem]
  exact congrArg₂ T.rowAt (mirrorOrig_mCopyFull hU _ _ _) (mirrorOrig_mCopyFull hU _ _ _)

/-- **The copied ladder is lawful on the ladder table.** -/
theorem ladderLawful_mCopyLadder
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
          (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) p.1 v))
    (hU : U ∈ I.mixedFaces g) {Y : Finset (Fin (m + 2)) × ℕ}
    {w : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hw : (Scheme.mirror hmix).rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    LadderLawful H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
      (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))
      fun p ↦ w (mCopyLadder hmix hlad hU p) := by
  obtain ⟨hord, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have hg1 (p : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) :
      (Scheme.mirror hmix).toCellScheme.grade (mCopyLadder hmix hlad hU p) = 1 :=
    congrArg Prod.snd (gradedIndex_mCopyLadder hlad hU p)
  have hmY (p : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) :
      mCopyLadder hmix hlad hU p ∈ (Scheme.mirror hmix).toCellScheme.below Y := by
    rw [CellScheme.mem_below, gradedIndex_mCopyLadder]
    exact hUY
  refine ⟨fun p ↦ ?_, fun c ↦ ?_⟩
  · have h := hord _ (hmY p)
    rwa [hg1] at h
  · have hb (p : Scheme.LadderPt (I.attachmentBase g).S
        (Scheme.RankMember (I.attachmentBase g).S H) H) :
        mCopyLadder hmix hlad hU p ∈ (Scheme.mirror hmix).toCellScheme.below
          ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyLadder hmix hlad hU c)) := by
      rw [CellScheme.mem_below, gradedIndex_mCopyLadder, gradedIndex_mCopyLadder]
    have h := (hloc _ (hmY c)).reindex fun p ↦ (⟨_, hb p⟩ :
      (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyLadder hmix hlad hU c)))
    convert h using 1
    · funext p
      exact (hg1 p).symm
    · funext p
      simp only [Function.comp_apply]
      rw [← Scheme.rowAt_of_mem (hb p), rowAt_mCopyLadder, hrowLL]
      rfl
    · rfl

/-- **The shape of the copied ladder** at a mixed face: a section lawful below a pair above
`(U, 1)` is `⊥` at every copied ladder point, or the chart image of the table of one member `a`,
`⊥` exactly at its index `0`. -/
theorem mCopyLadder_exists_shape (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
          (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) p.1 v))
    (hU : U ∈ I.mixedFaces g) {Y : Finset (Fin (m + 2)) × ℕ}
    {w : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hw : (Scheme.mirror hmix).rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    (∀ p, w (mCopyLadder hmix hlad hU p) = ⊥) ∨
      ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (gg : ℕ → Label.{u})
        (σ : Label.{u} → Label.{u}), IsWitness gg σ ∧
        (∀ p, w (mCopyLadder hmix hlad hU p) = min (σ (ladderSource H
          (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
            (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a p))) (gg 1)) ∧
        ∀ p, w (mCopyLadder hmix hlad hU p) = ⊥ ↔
          ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
            (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a p = 0 :=
  (ladderLawful_mCopyLadder hlad hrowLL hU hw hUY).exists_shape hH
    (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
    (fun a i ↦ (a, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ _ ↦ rfl)
    fun _ i hi ↦ by simp only [Scheme.ladderCeil, Sum.elim_inl]; omega

end Seed

end VaughtConjecture
