/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanMirrorCopies

/-!
# The copied ladder at a mixed face, over a pure attachment and a family of rank profiles

Process rank `ω₁`, the finite span of mutual rigidity: the copied ladder of
`VaughtConjecture.MainTheorem.MirrorMixedLadder`, for an attachment scheme `Att` on `N` points, a
finite nonempty family `Pf` of rank profiles `prof : Pf → Fin Att.card → ℕ` bounded by `H` (the
instance premise `Fact (∀ q d, prof q d ≤ H)`), and a family `MF` of mixed faces.  The seed's rank
members and their rank vectors are replaced by `Pf` and `prof`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace ProcessRank.MirrorAttachment

variable {N H : ℕ} {Att : Scheme.{u} N} {MF : Finset (Finset (Fin N))}
  {Pf : Type} [Finite Pf] [Nonempty Pf] {prof : Pf → Fin Att.card → ℕ}
  [hMF : Fact (∀ U ∈ MF, 1 ≤ #U ∧ U ≠ univ)] [hprof : Fact (∀ q d, prof q d ≤ H)]
  {T : Scheme.{u} N}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ MF, ¬ U ⊆ T.toCellScheme.scope c}
  {U : Finset (Fin N)}
  {lad : Scheme.LadderPt Att (Pf) H →
    Fin T.card}

variable (hmix) in
/-- **The copied ladder** at the mixed face `U`: the copies at `U` of the ladder points. -/
noncomputable def mCopyLadder (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) =
      ((univ : Finset (Fin N)), 1)) (hU : U ∈ MF)
    (p : Scheme.LadderPt Att (Pf) H) :
    Fin (Scheme.mirror hmix).card :=
  mCopyFull hmix hU (lad p) (hlad p) ((hMF.out _ hU).1)

omit [Finite Pf] [Nonempty Pf] in
theorem gradedIndex_mCopyLadder
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hU : U ∈ MF)
    (p : Scheme.LadderPt Att (Pf) H) :
    (Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyLadder hmix hlad hU p) = (U, 1) :=
  gradedIndex_mCopyFull hU _ _ _

omit [Finite Pf] [Nonempty Pf] in
/-- **The copied ladder reads itself as the ladder does.** -/
theorem rowAt_mCopyLadder
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hU : U ∈ MF)
    (p q : Scheme.LadderPt Att (Pf) H) :
    (Scheme.mirror hmix).rowAt (mCopyLadder hmix hlad hU p) (mCopyLadder hmix hlad hU q) =
      T.rowAt (lad p) (lad q) := by
  have hmem : mCopyLadder hmix hlad hU q ∈ (Scheme.mirror hmix).toCellScheme.below
      ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyLadder hmix hlad hU p)) := by
    rw [CellScheme.mem_below, gradedIndex_mCopyLadder, gradedIndex_mCopyLadder]
  rw [Scheme.rowAt_mirror_of_mem hmem]
  exact congrArg₂ T.rowAt (mirrorOrig_mCopyFull hU _ _ _) (mirrorOrig_mCopyFull hU _ _ _)

omit hprof in
omit [Finite Pf] [Nonempty Pf] in
/-- **The copied ladder is lawful on the ladder table.** -/
theorem ladderLawful_mCopyLadder
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (prof) p)
        (ladderIndex H (prof) Prod.fst
          (Scheme.ladderCeil (prof)) p.1 v))
    (hU : U ∈ MF) {Y : Finset (Fin N) × ℕ}
    {w : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hw : (Scheme.mirror hmix).rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    LadderLawful H (prof) Prod.fst
      (Scheme.ladderCeil (prof))
      fun p ↦ w (mCopyLadder hmix hlad hU p) := by
  obtain ⟨hord, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have hg1 (p : Scheme.LadderPt Att
      (Pf) H) :
      (Scheme.mirror hmix).toCellScheme.grade (mCopyLadder hmix hlad hU p) = 1 :=
    congrArg Prod.snd (gradedIndex_mCopyLadder hlad hU p)
  have hmY (p : Scheme.LadderPt Att
      (Pf) H) :
      mCopyLadder hmix hlad hU p ∈ (Scheme.mirror hmix).toCellScheme.below Y := by
    rw [CellScheme.mem_below, gradedIndex_mCopyLadder]
    exact hUY
  refine ⟨fun p ↦ ?_, fun c ↦ ?_⟩
  · have h := hord _ (hmY p)
    rwa [hg1] at h
  · have hb (p : Scheme.LadderPt Att
        (Pf) H) :
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
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (prof) p)
        (ladderIndex H (prof) Prod.fst
          (Scheme.ladderCeil (prof)) p.1 v))
    (hU : U ∈ MF) {Y : Finset (Fin N) × ℕ}
    {w : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hw : (Scheme.mirror hmix).rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    (∀ p, w (mCopyLadder hmix hlad hU p) = ⊥) ∨
      ∃ (a : Pf) (gg : ℕ → Label.{u})
        (σ : Label.{u} → Label.{u}), IsWitness gg σ ∧
        (∀ p, w (mCopyLadder hmix hlad hU p) = min (σ (ladderSource H
          (ladderIndex H (prof) Prod.fst
            (Scheme.ladderCeil (prof)) a p))) (gg 1)) ∧
        ∀ p, w (mCopyLadder hmix hlad hU p) = ⊥ ↔
          ladderIndex H (prof) Prod.fst
            (Scheme.ladderCeil (prof)) a p = 0 :=
  (ladderLawful_mCopyLadder hlad hrowLL hU hw hUY).exists_shape hH
    (Scheme.ladderCeil_le hprof.out)
    (fun a i ↦ (a, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ _ ↦ rfl)
    fun _ i hi ↦ by simp only [Scheme.ladderCeil, Sum.elim_inl]; omega

end ProcessRank.MirrorAttachment

end VaughtConjecture
