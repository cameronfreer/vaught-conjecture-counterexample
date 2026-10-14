/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CodedLadderSource
import VaughtConjecture.MainTheorem.MirrorMixedDecode

/-!
# The coded ladder copied at a mixed face of a mirrored scheme

Roadmap, Layer 3 ((R3) and (R4), the lifts into the mixed faces, for any scheme over the attachment
mirrored at the mixed faces of the seed) and Correspondence, item 1 (the strongly coded legal stage
types).  All results here are native constructions of this repository.

The statements of `VaughtConjecture.MainTheorem.MirrorMixedLadder` and
`VaughtConjecture.MainTheorem.MirrorMixedDecode` that assume the ladder points of `T` read one
another through `Label.ladderSource` (`hrowLL`), with that assumption made with the coded ladder
source (`Label.codedLadderSource`) instead.  Their proofs use of the ladder only the monotonicity
of the codes, the zero characterization, and recognition on the ladder table
(`Label.LadderLawful.exists_shape`), which hold for the coded ladder
(`Label.monotone_codedLadderSource`, `Label.codedLadderSource_eq_bot_iff`,
`Label.CodedLadderLawful.exists_shape`); the other statements of those files do not mention the
codes and are used unchanged.

* `Seed.codedLadderLawful_mCopyLadder`, `Seed.mCopyLadder_exists_shape_coded`: the copied ladder at
  a mixed face is lawful on the coded ladder table and has the shape of the table of one member.
* `Seed.exists_mladder_reading_coded`, `Seed.min_decode_eq_decode_one_m_coded`,
  `Seed.decode_controller_dichotomy_m_coded`, `Seed.decode_one_dichotomy_m_coded`: the decoded
  readings through the copies.

## References

Bountifulness is [Kni26, Definition 2.5.14]; witnesses are [Kni26, Definition 2.3.9].

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {T : Scheme.{u} (m + 2)}
  {hmix : ∀ c, T.toCellScheme.scope c ≠ univ → ∀ U ∈ I.mixedFaces g, ¬ U ⊆ T.toCellScheme.scope c}
  {U : Finset (Fin (m + 2))}
  {att : Fin (I.attachment g).card → Fin T.card}
  {lad : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H →
    Fin T.card}

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))

/-- **The copied ladder is lawful on the ladder table.** -/
theorem codedLadderLawful_mCopyLadder
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      codedLadderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
          (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) p.1 v))
    (hU : U ∈ I.mixedFaces g) {Y : Finset (Fin (m + 2)) × ℕ}
    {w : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hw : (Scheme.mirror hmix).rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    CodedLadderLawful H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
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
theorem mCopyLadder_exists_shape_coded (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      codedLadderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
          (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) p.1 v))
    (hU : U ∈ I.mixedFaces g) {Y : Finset (Fin (m + 2)) × ℕ}
    {w : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hw : (Scheme.mirror hmix).rows.IsLawfulBelow Y fun d ↦ w d) (hUY : (U, 1) ≤ Y) :
    (∀ p, w (mCopyLadder hmix hlad hU p) = ⊥) ∨
      ∃ (a : Scheme.RankMember (I.attachmentBase g).S H) (gg : ℕ → Label.{u})
        (σ : Label.{u} → Label.{u}), IsWitness gg σ ∧
        (∀ p, w (mCopyLadder hmix hlad hU p) = min (σ (codedLadderSource H
          (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
            (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a p))) (gg 1)) ∧
        ∀ p, w (mCopyLadder hmix hlad hU p) = ⊥ ↔
          ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
            (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a p = 0 :=
  (codedLadderLawful_mCopyLadder hlad hrowLL hU hw hUY).exists_shape hH
    (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
    (fun a i ↦ (a, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ _ ↦ rfl)
    fun _ i hi ↦ by simp only [Scheme.ladderCeil, Sum.elim_inl]; omega

/-- **Every cell of full scope reads the ladder through one member**, at every grade `K ≥ 1`: a
ladder point reads the ladder through its own member and the table of its ceiling. -/
theorem exists_mladder_reading_coded
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      codedLadderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (idx p.1 v))
    (hrowLA : ∀ p e, (I.attachment g).toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 2))), 1) →
      ∃ p, x = lad p)
    (hread : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (Scheme.rankProf (I.attachmentBase g).S H b e))
    {K : ℕ} (hK1 : 1 ≤ K) {f : Fin T.card}
    (hf : T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K)) :
    ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
      (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
      ∀ e, (I.attachment g).toCellScheme.grade e = 1 →
        T.rowAt f (att e) = Φ (Scheme.rankProf (I.attachmentBase g).S H b e) := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · obtain rfl : K = 1 := by omega
    obtain ⟨p, rfl⟩ := hone f hf
    refine ⟨p.1, codedLadderSource (Scheme.ladderCeil (Scheme.rankProf _ H) p),
      monotone_codedLadderSource _, fun v ↦ hrowLL p v, fun e he ↦ ?_⟩
    rw [hrowLA p e he, hrowLL]
    congr 1
    exact ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H)) (p.1, Sum.inr e)
  · obtain ⟨b, Φ, hΦ, -, hl, ha⟩ := hread f K hf hK
    exact ⟨b, Φ, hΦ, hl, fun e he ↦ ha e (by omega)⟩

/-- **The grade-one reading of a cell of the attachment, capped at a cell of full scope, is that
cell's reading**, through capped decoders at the copies at `U`, when the grade-one reading is
through the top rung of a member whose copy dominates the copied ladder. -/
theorem min_decode_eq_decode_one_m_coded (hU : U ∈ I.mixedFaces g) (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      codedLadderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (idx p.1 v))
    (hrowLA : ∀ p e, (I.attachment g).toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 2))), 1) →
      ∃ p, x = lad p)
    (hread : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (Scheme.rankProf (I.attachmentBase g).S H b e))
    {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    {K : ℕ} (hK1 : 1 ≤ K) (hKU : K ≤ #U) {f : Fin T.card}
    (hf : T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K))
    (a : Scheme.RankMember (I.attachmentBase g).S H)
    (hmax : ∀ v, P (mCopyLadder hmix hlad hU v) ≤
      P (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩)))
    {θf θ1 : Label.{u} → Label.{u}} (hθf_mono : Monotone θf)
    (hθf_le : ∀ x, θf x ≤ P (mCopyFull hmix hU f hf hKU))
    (hθf : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU f hf hKU)),
      θf ((Scheme.mirror hmix).rowAt (mCopyFull hmix hU f hf hKU) d) =
        min (P d) (P (mCopyFull hmix hU f hf hKU)))
    (hθ1 : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex
          (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩))),
      θ1 ((Scheme.mirror hmix).rowAt (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩))
          d) = min (P d) (P (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩))))
    {e : Fin (I.attachment g).card} (he : (I.attachment g).toCellScheme.grade e = 1) :
    min (θ1 (T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e)))
        (P (mCopyFull hmix hU f hf hKU)) = θf (T.rowAt f (att e)) := by
  set top : Scheme.LadderPt (I.attachmentBase g).S
    (Scheme.RankMember (I.attachmentBase g).S H) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  have hU1 : 1 ≤ #U := hK1.trans hKU
  have r1 : θ1 (T.rowAt (lad top) (att e)) = P (mCopyLadder hmix hlad hU (a, Sum.inr e)) := by
    rw [hrowLA top e he]
    rw [decode_mCopyFull hU (hlad top) (one_le_card_of_mem_mixedFaces hU) hθ1 (hlad _) le_rfl]
    exact min_eq_left (hmax _)
  rw [r1]
  obtain ⟨b, Φ, hΦ, hrl, hre⟩ := exists_mladder_reading_coded hrowLL hrowLA hone hread hK1 hf
  set κ := rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
    (Scheme.rankProf (I.attachmentBase g).S H a) with hκ
  have hagr := rankAgree_rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
    (Scheme.rankProf (I.attachmentBase g).S H a) e
  have hidx_sh : idx b ((a, Sum.inr e) : Scheme.LadderPt (I.attachmentBase g).S
      (Scheme.RankMember (I.attachmentBase g).S H) H) =
      min (Scheme.rankProf (I.attachmentBase g).S H b e) κ := by
    change min κ (Scheme.rankProf (I.attachmentBase g).S H a e) = _
    rw [min_comm]
    exact hagr.symm
  have hidx_top : idx b top = κ := by
    unfold ladderIndex
    simp only [top, Scheme.ladderCeil, Sum.elim_inl]
    have hκH := rankCut_le H (Scheme.rankProf (I.attachmentBase g).S H b)
      (Scheme.rankProf (I.attachmentBase g).S H a)
    exact min_eq_left (by omega)
  have hrow_sh : T.rowAt f (lad (a, Sum.inr e)) =
      min (T.rowAt f (att e)) (T.rowAt f (lad top)) := by
    rw [hrl, hrl, hre e he, hidx_sh, hidx_top, hΦ.map_min]
  have hdec_sh := decode_mCopyFull hU hf hKU hθf (hlad (a, Sum.inr e)) hK1
  have hdec_top := decode_mCopyFull hU hf hKU hθf (hlad top) hK1
  have hle_top : θf (T.rowAt f (att e)) ≤
      P (mCopyFull hmix hU (lad top) (hlad top) (hK1.trans hKU)) := by
    have hsh : T.rowAt f (att e) = T.rowAt f (lad (b, Sum.inr e)) := by
      rw [hre e he, hrl]
      congr 1
      exact (ladderIndex_parent (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
        (b, Sum.inr e)).symm
    rw [hsh, decode_mCopyFull hU hf hKU hθf (hlad (b, Sum.inr e)) hK1]
    exact (min_le_left _ _).trans (hmax _)
  have h1 := congrArg θf hrow_sh
  rw [hθf_mono.map_min, hdec_sh, hdec_top, min_eq_left (le_min hle_top (hθf_le _))] at h1
  exact h1

/-- **The bottom pattern of a decoded dominating row**: a capped decoder at the copy of a cell of
full scope of grade `K ≥ 2` sends all its readings of the cells of the attachment of grade at most
`K` to `⊥`, or exactly the readings `⊥`. -/
theorem decode_controller_dichotomy_m_coded (hU : U ∈ I.mixedFaces g) (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      codedLadderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (idx p.1 v))
    (hread : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin (m + 2))), K) → 2 ≤ K →
      ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, (I.attachment g).toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (Scheme.rankProf (I.attachmentBase g).S H b e))
    {j : ℕ} {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hP : (Scheme.mirror hmix).rows.IsLawfulBelow (U, j) fun d ↦ P d) (hj1 : 1 ≤ j) {K : ℕ}
    (hK2 : 2 ≤ K) (hKU : K ≤ #U) {u : Fin T.card}
    (hu : T.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), K))
    {θ : Label.{u} → Label.{u}} (hθ_bot : θ ⊥ = ⊥)
    (hθ : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU u hu hKU)),
      θ ((Scheme.mirror hmix).rowAt (mCopyFull hmix hU u hu hKU) d) =
        min (P d) (P (mCopyFull hmix hU u hu hKU))) :
    (∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e ≤ K →
        θ (T.rowAt u (att e)) = ⊥) ∨
      ∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e ≤ K →
        (θ (T.rowAt u (att e)) = ⊥ ↔ T.rowAt u (att e) = ⊥) := by
  obtain ⟨b, Φ, -, hΦ0, hl, ha⟩ := hread u K hu hK2
  -- the reading of a cell is the reading of a rung of `b`
  have hrung (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e ≤ K)
      (h0 : Scheme.rankProf (I.attachmentBase g).S H b e ≠ 0) :
      ∃ (i : ℕ) (hi : i < H), θ (T.rowAt u (att e)) =
        min (P (mCopyLadder hmix hlad hU (b, Sum.inl ⟨i, hi⟩)))
          (P (mCopyFull hmix hU u hu hKU)) := by
    have hrH : Scheme.rankProf (I.attachmentBase g).S H b e ≤ H := Scheme.rankProf_le _ H b e
    have hi : Scheme.rankProf (I.attachmentBase g).S H b e - 1 < H := by omega
    refine ⟨_, hi, ?_⟩
    have hpt := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
      (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
      ((b, Sum.inl ⟨_, hi⟩) :
        Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H)
    have hre : T.rowAt u (att e) = T.rowAt u (lad (b, Sum.inl ⟨_, hi⟩)) := by
      rw [ha e he, hl, hpt]
      simp only [Scheme.ladderCeil, Sum.elim_inl]
      congr 1
      omega
    rw [hre, decode_mCopyFull hU hu hKU hθ (hlad _) (by omega)]
    rfl
  have hzero (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e ≤ K)
      (h0 : Scheme.rankProf (I.attachmentBase g).S H b e = 0) : T.rowAt u (att e) = ⊥ := by
    rw [ha e he, h0, hΦ0]
  rcases mCopyLadder_exists_shape_coded hH hlad hrowLL hU hP
      (show ((U, 1) : Finset (Fin (m + 2)) × ℕ) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
    hall | ⟨a, gg, σ, hwit, hch, hbot⟩
  · left
    intro e he
    by_cases h0 : Scheme.rankProf (I.attachmentBase g).S H b e = 0
    · rw [hzero e he h0, hθ_bot]
    · obtain ⟨i, hi, hθe⟩ := hrung e he h0
      rw [hθe, hall, min_eq_left bot_le]
  · by_cases hκ : rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
        (Scheme.rankProf (I.attachmentBase g).S H b) = 0 ∨
        P (mCopyFull hmix hU u hu hKU) = ⊥
    · left
      intro e he
      by_cases h0 : Scheme.rankProf (I.attachmentBase g).S H b e = 0
      · rw [hzero e he h0, hθ_bot]
      · obtain ⟨i, hi, hθe⟩ := hrung e he h0
        rw [hθe]
        rcases hκ with h0 | h0
        · have hz : idx a ((b, Sum.inl ⟨i, hi⟩) : Scheme.LadderPt (I.attachmentBase g).S
              (Scheme.RankMember (I.attachmentBase g).S H) H) = 0 := by
            change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
              (Scheme.rankProf (I.attachmentBase g).S H b)) (i + 1) = 0
            rw [h0]
            exact Nat.zero_min _
          rw [(hbot _).mpr hz, min_eq_left bot_le]
        · rw [h0, min_eq_right bot_le]
    · right
      push Not at hκ
      intro e he
      refine ⟨fun h0 ↦ ?_, fun h0 ↦ by rw [h0, hθ_bot]⟩
      by_contra hrow
      have hb0 : Scheme.rankProf (I.attachmentBase g).S H b e ≠ 0 := fun h ↦ hrow (hzero e he h)
      obtain ⟨i, hi, hθe⟩ := hrung e he hb0
      rw [hθe] at h0
      rcases min_eq_bot.mp h0 with h | h
      · have hpos : idx a ((b, Sum.inl ⟨i, hi⟩) : Scheme.LadderPt (I.attachmentBase g).S
            (Scheme.RankMember (I.attachmentBase g).S H) H) ≠ 0 := by
          change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
            (Scheme.rankProf (I.attachmentBase g).S H b)) (i + 1) ≠ 0
          have := hκ.1
          omega
        exact hpos ((hbot _).mp h)
      · exact hκ.2 h

/-- **The bottom pattern of the decoded top rung**: a capped decoder at the copy of the top rung of
a member `a` whose copy dominates the copied ladder sends all readings of the cells of the
attachment of grade one by the top rung to `⊥`, or exactly the readings `⊥`. -/
theorem decode_one_dichotomy_m_coded (hU : U ∈ I.mixedFaces g) (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin (m + 2))), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      codedLadderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (idx p.1 v))
    (hrowLA : ∀ p e, (I.attachment g).toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    {j : ℕ} {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hP : (Scheme.mirror hmix).rows.IsLawfulBelow (U, j) fun d ↦ P d) (hj1 : 1 ≤ j)
    (a : Scheme.RankMember (I.attachmentBase g).S H)
    (hmax : ∀ v, P (mCopyLadder hmix hlad hU v) ≤
      P (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩)))
    {θ : Label.{u} → Label.{u}}
    (hθ : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex
          (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩))),
      θ ((Scheme.mirror hmix).rowAt (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩))
          d) = min (P d) (P (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩)))) :
    (∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e = 1 →
        θ (T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e)) = ⊥) ∨
      ∀ e : Fin (I.attachment g).card, (I.attachment g).toCellScheme.grade e = 1 →
        (θ (T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e)) = ⊥ ↔
          T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e) = ⊥) := by
  set top : Scheme.LadderPt (I.attachmentBase g).S
    (Scheme.RankMember (I.attachmentBase g).S H) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  have hread (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e = 1) :
      θ (T.rowAt (lad top) (att e)) = P (mCopyLadder hmix hlad hU (a, Sum.inr e)) ∧
      T.rowAt (lad top) (att e) =
        codedLadderSource H (Scheme.rankProf (I.attachmentBase g).S H a e) := by
    rw [hrowLA top e he]
    refine ⟨?_, ?_⟩
    · rw [decode_mCopyFull hU (hlad top) (one_le_card_of_mem_mixedFaces hU) hθ (hlad _) le_rfl]
      exact min_eq_left (hmax _)
    · rw [hrowLL]
      have h := ladderIndex_parent (H := H) (prof := Scheme.rankProf (I.attachmentBase g).S H)
        (parent := Prod.fst) (Scheme.ladderCeil_le (Scheme.rankProf_le _ H))
        ((a, Sum.inr e) : Scheme.LadderPt (I.attachmentBase g).S
          (Scheme.RankMember (I.attachmentBase g).S H) H)
      rw [h]
      change codedLadderSource (H - 1 + 1) (Scheme.rankProf (I.attachmentBase g).S H a e) = _
      rw [show H - 1 + 1 = H by omega]
  rcases mCopyLadder_exists_shape_coded hH hlad hrowLL hU hP
      (show ((U, 1) : Finset (Fin (m + 2)) × ℕ) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
    hall | ⟨b, gg, σ, hwit, hch, hbot⟩
  · left
    intro e he
    rw [(hread e he).1, hall]
  · by_cases htop0 : P (mCopyLadder hmix hlad hU top) = ⊥
    · left
      intro e he
      rw [(hread e he).1]
      exact le_bot_iff.mp (htop0 ▸ hmax _)
    · right
      have hcut : rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
          (Scheme.rankProf (I.attachmentBase g).S H a) ≠ 0 := by
        intro h0
        apply htop0
        rw [hbot]
        change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
          (Scheme.rankProf (I.attachmentBase g).S H a)) (H - 1 + 1) = 0
        rw [h0]
        exact Nat.zero_min _
      intro e he
      rw [(hread e he).1, (hread e he).2, hbot, codedLadderSource_eq_bot_iff]
      change min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H b)
        (Scheme.rankProf (I.attachmentBase g).S H a))
        (Scheme.rankProf (I.attachmentBase g).S H a e) = 0 ↔ _
      constructor
      · intro h
        rcases Nat.min_eq_zero_iff.mp h with h' | h'
        · exact absurd h' hcut
        · rw [h']; exact Nat.zero_min _
      · intro h
        rcases Nat.min_eq_zero_iff.mp h with h' | h'
        · rw [h']; exact Nat.min_zero _
        · omega

end Seed

end VaughtConjecture
