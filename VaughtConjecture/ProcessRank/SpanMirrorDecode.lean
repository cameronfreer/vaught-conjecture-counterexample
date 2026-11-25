/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanMirrorLadder

/-!
# Decoded readings through the copies at a mixed face, over a pure attachment

Process rank `ω₁`, the finite span of mutual rigidity: the decoded readings of
`VaughtConjecture.MainTheorem.MirrorMixedDecode` (one member reading the ladder, shadow agreement,
twins, the decoder dichotomies), for an attachment scheme `Att`, a family `Pf` of rank profiles and
a family `MF` of mixed faces.
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
  {att : Fin Att.card → Fin T.card}
  {lad : Scheme.LadderPt Att (Pf) H →
    Fin T.card}

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex H (prof) Prod.fst
  (Scheme.ladderCeil (prof))

omit [Finite Pf] [Nonempty Pf] in
/-- **Every cell of full scope reads the ladder through one member**, at every grade `K ≥ 1`: a
ladder point reads the ladder through its own member and the table of its ceiling. -/
theorem exists_mladder_reading
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (prof) p) (idx p.1 v))
    (hrowLA : ∀ p e, Att.toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin N)), 1) →
      ∃ p, x = lad p)
    (hreadMember : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K) → 2 ≤ K →
      ∃ (b : Pf) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, Att.toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (prof b e))
    {K : ℕ} (hK1 : 1 ≤ K) {f : Fin T.card}
    (hf : T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K)) :
    ∃ (b : Pf) (Φ : ℕ → Label.{u}), Monotone Φ ∧
      (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
      ∀ e, Att.toCellScheme.grade e = 1 →
        T.rowAt f (att e) = Φ (prof b e) := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · obtain rfl : K = 1 := by omega
    obtain ⟨p, rfl⟩ := hone f hf
    refine ⟨p.1, ladderSource (Scheme.ladderCeil prof p),
      monotone_ladderSource _, fun v ↦ hrowLL p v, fun e he ↦ ?_⟩
    rw [hrowLA p e he, hrowLL]
    congr 1
    exact ladderIndex_parent (Scheme.ladderCeil_le hprof.out) (p.1, Sum.inr e)
  · obtain ⟨b, Φ, hΦ, -, hl, ha⟩ := hreadMember f K hf hK
    exact ⟨b, Φ, hΦ, hl, fun e he ↦ ha e (by omega)⟩

omit [Finite Pf] [Nonempty Pf] in
/-- **A shadow**: a cell of full scope at the grade `k ≥ 1` reads a cell of the attachment of grade
at most `k` (of grade one when `k = 1`) as some ladder point. -/
theorem exists_mshadow
    (hrowLA : ∀ p e, Att.toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin N)), 1) →
      ∃ p, x = lad p)
    (hreadMember : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K) → 2 ≤ K →
      ∃ (b : Pf) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, Att.toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (prof b e))
    {k : ℕ} (hk1 : 1 ≤ k) (f : Fin T.card)
    (hf : T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), k))
    {e : Fin Att.card} (he : Att.toCellScheme.grade e = k) :
    ∃ v, T.rowAt f (att e) = T.rowAt f (lad v) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by omega
    obtain ⟨p, rfl⟩ := hone f hf
    exact ⟨_, hrowLA p e he⟩
  · obtain ⟨b, Φ, -, -, hl, ha⟩ := hreadMember f k hf hk
    refine ⟨(b, Sum.inr e), ?_⟩
    rw [ha e he.le, hl]
    congr 1
    exact (ladderIndex_parent (Scheme.ladderCeil_le hprof.out) (b, Sum.inr e)).symm

omit [Finite Pf] [Nonempty Pf] in
/-- **The grade-one reading of a cell of the attachment, capped at a cell of full scope, is that
cell's reading**, through capped decoders at the copies at `U`, when the grade-one reading is
through the top rung of a member whose copy dominates the copied ladder. -/
theorem min_decode_eq_decode_one_m (hU : U ∈ MF) (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (prof) p) (idx p.1 v))
    (hrowLA : ∀ p e, Att.toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    (hone : ∀ x, T.toCellScheme.gradedIndex x = ((univ : Finset (Fin N)), 1) →
      ∃ p, x = lad p)
    (hreadMember : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K) → 2 ≤ K →
      ∃ (b : Pf) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, Att.toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (prof b e))
    {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    {K : ℕ} (hK1 : 1 ≤ K) (hKU : K ≤ #U) {f : Fin T.card}
    (hf : T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K))
    (a : Pf)
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
    {e : Fin Att.card} (he : Att.toCellScheme.grade e = 1) :
    min (θ1 (T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e)))
        (P (mCopyFull hmix hU f hf hKU)) = θf (T.rowAt f (att e)) := by
  set top : Scheme.LadderPt Att
    (Pf) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  have hU1 : 1 ≤ #U := hK1.trans hKU
  have r1 : θ1 (T.rowAt (lad top) (att e)) = P (mCopyLadder hmix hlad hU (a, Sum.inr e)) := by
    rw [hrowLA top e he]
    rw [decode_mCopyFull hU (hlad top) ((hMF.out _ hU).1) hθ1 (hlad _) le_rfl]
    exact min_eq_left (hmax _)
  rw [r1]
  obtain ⟨b, Φ, hΦ, hrl, hre⟩ := exists_mladder_reading hrowLL hrowLA hone hreadMember hK1 hf
  set κ := rankCut H (prof b)
    (prof a) with hκ
  have hagr := rankAgree_rankCut H (prof b)
    (prof a) e
  have hidx_sh : idx b ((a, Sum.inr e) : Scheme.LadderPt Att
      (Pf) H) =
      min (prof b e) κ := by
    change min κ (prof a e) = _
    rw [min_comm]
    exact hagr.symm
  have hidx_top : idx b top = κ := by
    unfold ladderIndex
    simp only [top, Scheme.ladderCeil, Sum.elim_inl]
    have hκH := rankCut_le H (prof b)
      (prof a)
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
      exact (ladderIndex_parent (Scheme.ladderCeil_le hprof.out)
        (b, Sum.inr e)).symm
    rw [hsh, decode_mCopyFull hU hf hKU hθf (hlad (b, Sum.inr e)) hK1]
    exact (min_le_left _ _).trans (hmax _)
  have h1 := congrArg θf hrow_sh
  rw [hθf_mono.map_min, hdec_sh, hdec_top, min_eq_left (le_min hle_top (hθf_le _))] at h1
  exact h1

omit [Finite Pf] [Nonempty Pf] hMF in
/-- **The reading of a cell of the attachment by a dominating cell, capped at a cell of full scope,
is that cell's reading**, through capped decoders at the copies at `U`, for grades `K ≥ k ≥ 2`,
when the dominating cell `u` has the largest copy at its grade: the agreement at a shadow and the
twin of `f` at the grade `k`. -/
theorem min_decode_eq_decode_m (hU : U ∈ MF)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hshadow : ∀ f u K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K) →
      T.toCellScheme.gradedIndex u = ((univ : Finset (Fin N)), k) → 2 ≤ k → k ≤ K →
      ∀ e, Att.toCellScheme.grade e = k → ∃ v,
        T.rowAt u (lad v) = T.rowAt u (att e) ∧
        min (T.rowAt f (lad v)) (T.rowAt f u) = min (T.rowAt f (att e)) (T.rowAt f u))
    (htwinAbove : ∀ f K k, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K) →
      2 ≤ k → k ≤ K → ∀ e, Att.toCellScheme.grade e = k →
      ∃ et, T.toCellScheme.gradedIndex et = ((univ : Finset (Fin N)), k) ∧
        T.rowAt f (att e) ≤ T.rowAt f et)
    {P : Fin (Scheme.mirror hmix).card → Label.{u}} {k K : ℕ} (hk2 : 2 ≤ k) (hkK : k ≤ K)
    (hKU : K ≤ #U) {f u : Fin T.card}
    (hf : T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K))
    (hu : T.toCellScheme.gradedIndex u = ((univ : Finset (Fin N)), k))
    (hmax : ∀ w (hw : T.toCellScheme.gradedIndex w = ((univ : Finset (Fin N)), k)),
      P (mCopyFull hmix hU w hw (hkK.trans hKU)) ≤ P (mCopyFull hmix hU u hu (hkK.trans hKU)))
    {θf θu : Label.{u} → Label.{u}} (hθf_mono : Monotone θf)
    (hθf_le : ∀ x, θf x ≤ P (mCopyFull hmix hU f hf hKU))
    (hθf : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU f hf hKU)),
      θf ((Scheme.mirror hmix).rowAt (mCopyFull hmix hU f hf hKU) d) =
        min (P d) (P (mCopyFull hmix hU f hf hKU)))
    (hθu : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU u hu (hkK.trans hKU))),
      θu ((Scheme.mirror hmix).rowAt (mCopyFull hmix hU u hu (hkK.trans hKU)) d) =
        min (P d) (P (mCopyFull hmix hU u hu (hkK.trans hKU))))
    {e : Fin Att.card} (he : Att.toCellScheme.grade e = k) :
    min (θu (T.rowAt u (att e))) (P (mCopyFull hmix hU f hf hKU)) =
      θf (T.rowAt f (att e)) := by
  obtain ⟨v, hrv, hkey⟩ := hshadow f u K k hf hu hk2 hkK e he
  have dec_u : θu (T.rowAt u (att e)) =
      min (P (mCopyFull hmix hU (lad v) (hlad v) ((by omega : 1 ≤ k).trans (hkK.trans hKU))))
        (P (mCopyFull hmix hU u hu (hkK.trans hKU))) := by
    rw [← hrv]
    exact decode_mCopyFull hU hu (hkK.trans hKU) hθu (hlad v) (by omega)
  have dec_fw : θf (T.rowAt f (lad v)) =
      min (P (mCopyFull hmix hU (lad v) (hlad v) ((by omega : 1 ≤ K).trans hKU)))
        (P (mCopyFull hmix hU f hf hKU)) :=
    decode_mCopyFull hU hf hKU hθf (hlad v) (by omega)
  have dec_fA : θf (T.rowAt f u) =
      min (P (mCopyFull hmix hU u hu (hkK.trans hKU))) (P (mCopyFull hmix hU f hf hKU)) :=
    decode_mCopyFull hU hf hKU hθf hu hkK
  obtain ⟨et, het, hle⟩ := htwinAbove f K k hf hk2 hkK e he
  have dec_t : θf (T.rowAt f et) =
      min (P (mCopyFull hmix hU et het (hkK.trans hKU))) (P (mCopyFull hmix hU f hf hKU)) :=
    decode_mCopyFull hU hf hKU hθf het hkK
  have hθRf : θf (T.rowAt f (att e)) ≤ P (mCopyFull hmix hU u hu (hkK.trans hKU)) :=
    (hθf_mono hle).trans (dec_t ▸ (min_le_left _ _).trans (hmax et het))
  have h1 := congrArg θf hkey
  rw [hθf_mono.map_min, hθf_mono.map_min, dec_fw, dec_fA] at h1
  rw [dec_u]
  rw [min_eq_left (le_min hθRf (hθf_le _))] at h1
  rw [← h1]
  have lat : ∀ a b c : Label.{u}, min (min a b) c = min (min a c) (min b c) := fun a b c ↦ by
    rw [min_min_min_comm, min_self]
  exact lat _ _ _

/-- **The bottom pattern of a decoded dominating row**: a capped decoder at the copy of a cell of
full scope of grade `K ≥ 2` sends all its readings of the cells of the attachment of grade at most
`K` to `⊥`, or exactly the readings `⊥`. -/
theorem decode_controller_dichotomy_m (hU : U ∈ MF) (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (prof) p) (idx p.1 v))
    (hreadMember : ∀ f K, T.toCellScheme.gradedIndex f = ((univ : Finset (Fin N)), K) → 2 ≤ K →
      ∃ (b : Pf) (Φ : ℕ → Label.{u}), Monotone Φ ∧
        Φ 0 = ⊥ ∧ (∀ v, T.rowAt f (lad v) = Φ (idx b v)) ∧
        ∀ e, Att.toCellScheme.grade e ≤ K →
          T.rowAt f (att e) = Φ (prof b e))
    {j : ℕ} {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hP : (Scheme.mirror hmix).rows.IsLawfulBelow (U, j) fun d ↦ P d) (hj1 : 1 ≤ j) {K : ℕ}
    (hK2 : 2 ≤ K) (hKU : K ≤ #U) {u : Fin T.card}
    (hu : T.toCellScheme.gradedIndex u = ((univ : Finset (Fin N)), K))
    {θ : Label.{u} → Label.{u}} (hθ_bot : θ ⊥ = ⊥)
    (hθ : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex (mCopyFull hmix hU u hu hKU)),
      θ ((Scheme.mirror hmix).rowAt (mCopyFull hmix hU u hu hKU) d) =
        min (P d) (P (mCopyFull hmix hU u hu hKU))) :
    (∀ e : Fin Att.card, Att.toCellScheme.grade e ≤ K →
        θ (T.rowAt u (att e)) = ⊥) ∨
      ∀ e : Fin Att.card, Att.toCellScheme.grade e ≤ K →
        (θ (T.rowAt u (att e)) = ⊥ ↔ T.rowAt u (att e) = ⊥) := by
  obtain ⟨b, Φ, -, hΦ0, hl, ha⟩ := hreadMember u K hu hK2
  -- the reading of a cell is the reading of a rung of `b`
  have hrung (e : Fin Att.card) (he : Att.toCellScheme.grade e ≤ K)
      (h0 : prof b e ≠ 0) :
      ∃ (i : ℕ) (hi : i < H), θ (T.rowAt u (att e)) =
        min (P (mCopyLadder hmix hlad hU (b, Sum.inl ⟨i, hi⟩)))
          (P (mCopyFull hmix hU u hu hKU)) := by
    have hrH : prof b e ≤ H := hprof.out b e
    have hi : prof b e - 1 < H := by omega
    refine ⟨_, hi, ?_⟩
    have hpt := ladderIndex_parent (H := H) (prof := prof)
      (parent := Prod.fst) (Scheme.ladderCeil_le hprof.out)
      ((b, Sum.inl ⟨_, hi⟩) :
        Scheme.LadderPt Att (Pf) H)
    have hre : T.rowAt u (att e) = T.rowAt u (lad (b, Sum.inl ⟨_, hi⟩)) := by
      rw [ha e he, hl, hpt]
      simp only [Scheme.ladderCeil, Sum.elim_inl]
      congr 1
      omega
    rw [hre, decode_mCopyFull hU hu hKU hθ (hlad _) (by omega)]
    rfl
  have hzero (e : Fin Att.card) (he : Att.toCellScheme.grade e ≤ K)
      (h0 : prof b e = 0) : T.rowAt u (att e) = ⊥ := by
    rw [ha e he, h0, hΦ0]
  rcases mCopyLadder_exists_shape hH hlad hrowLL hU hP
      (show ((U, 1) : Finset (Fin N) × ℕ) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
    hall | ⟨a, gg, σ, hwit, hch, hbot⟩
  · left
    intro e he
    by_cases h0 : prof b e = 0
    · rw [hzero e he h0, hθ_bot]
    · obtain ⟨i, hi, hθe⟩ := hrung e he h0
      rw [hθe, hall, min_eq_left bot_le]
  · by_cases hκ : rankCut H (prof a)
        (prof b) = 0 ∨
        P (mCopyFull hmix hU u hu hKU) = ⊥
    · left
      intro e he
      by_cases h0 : prof b e = 0
      · rw [hzero e he h0, hθ_bot]
      · obtain ⟨i, hi, hθe⟩ := hrung e he h0
        rw [hθe]
        rcases hκ with h0 | h0
        · have hz : idx a ((b, Sum.inl ⟨i, hi⟩) : Scheme.LadderPt Att
              (Pf) H) = 0 := by
            change min (rankCut H (prof a)
              (prof b)) (i + 1) = 0
            rw [h0]
            exact Nat.zero_min _
          rw [(hbot _).mpr hz, min_eq_left bot_le]
        · rw [h0, min_eq_right bot_le]
    · right
      push Not at hκ
      intro e he
      refine ⟨fun h0 ↦ ?_, fun h0 ↦ by rw [h0, hθ_bot]⟩
      by_contra hrow
      have hb0 : prof b e ≠ 0 := fun h ↦ hrow (hzero e he h)
      obtain ⟨i, hi, hθe⟩ := hrung e he hb0
      rw [hθe] at h0
      rcases min_eq_bot.mp h0 with h | h
      · have hpos : idx a ((b, Sum.inl ⟨i, hi⟩) : Scheme.LadderPt Att
            (Pf) H) ≠ 0 := by
          change min (rankCut H (prof a)
            (prof b)) (i + 1) ≠ 0
          have := hκ.1
          omega
        exact hpos ((hbot _).mp h)
      · exact hκ.2 h

/-- **The bottom pattern of the decoded top rung**: a capped decoder at the copy of the top rung of
a member `a` whose copy dominates the copied ladder sends all readings of the cells of the
attachment of grade one by the top rung to `⊥`, or exactly the readings `⊥`. -/
theorem decode_one_dichotomy_m (hU : U ∈ MF) (hH : 0 < H)
    (hlad : ∀ p, T.toCellScheme.gradedIndex (lad p) = ((univ : Finset (Fin N)), 1))
    (hrowLL : ∀ p v, T.rowAt (lad p) (lad v) =
      ladderSource (Scheme.ladderCeil (prof) p) (idx p.1 v))
    (hrowLA : ∀ p e, Att.toCellScheme.grade e = 1 →
      T.rowAt (lad p) (att e) = T.rowAt (lad p) (lad (p.1, Sum.inr e)))
    {j : ℕ} {P : Fin (Scheme.mirror hmix).card → Label.{u}}
    (hP : (Scheme.mirror hmix).rows.IsLawfulBelow (U, j) fun d ↦ P d) (hj1 : 1 ≤ j)
    (a : Pf)
    (hmax : ∀ v, P (mCopyLadder hmix hlad hU v) ≤
      P (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩)))
    {θ : Label.{u} → Label.{u}}
    (hθ : ∀ d ∈ (Scheme.mirror hmix).toCellScheme.below
        ((Scheme.mirror hmix).toCellScheme.gradedIndex
          (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩))),
      θ ((Scheme.mirror hmix).rowAt (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩))
          d) = min (P d) (P (mCopyLadder hmix hlad hU (a, Sum.inl ⟨H - 1, by omega⟩)))) :
    (∀ e : Fin Att.card, Att.toCellScheme.grade e = 1 →
        θ (T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e)) = ⊥) ∨
      ∀ e : Fin Att.card, Att.toCellScheme.grade e = 1 →
        (θ (T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e)) = ⊥ ↔
          T.rowAt (lad (a, Sum.inl ⟨H - 1, by omega⟩)) (att e) = ⊥) := by
  set top : Scheme.LadderPt Att
    (Pf) H := (a, Sum.inl ⟨H - 1, by omega⟩) with htop
  have hreadMember (e : Fin Att.card) (he : Att.toCellScheme.grade e = 1) :
      θ (T.rowAt (lad top) (att e)) = P (mCopyLadder hmix hlad hU (a, Sum.inr e)) ∧
      T.rowAt (lad top) (att e) =
        ladderSource H (prof a e) := by
    rw [hrowLA top e he]
    refine ⟨?_, ?_⟩
    · rw [decode_mCopyFull hU (hlad top) ((hMF.out _ hU).1) hθ (hlad _) le_rfl]
      exact min_eq_left (hmax _)
    · rw [hrowLL]
      have h := ladderIndex_parent (H := H) (prof := prof)
        (parent := Prod.fst) (Scheme.ladderCeil_le hprof.out)
        ((a, Sum.inr e) : Scheme.LadderPt Att
          (Pf) H)
      rw [h]
      change ladderSource (H - 1 + 1) (prof a e) = _
      rw [show H - 1 + 1 = H by omega]
  rcases mCopyLadder_exists_shape hH hlad hrowLL hU hP
      (show ((U, 1) : Finset (Fin N) × ℕ) ≤ (U, j) from ⟨subset_rfl, hj1⟩) with
    hall | ⟨b, gg, σ, hwit, hch, hbot⟩
  · left
    intro e he
    rw [(hreadMember e he).1, hall]
  · by_cases htop0 : P (mCopyLadder hmix hlad hU top) = ⊥
    · left
      intro e he
      rw [(hreadMember e he).1]
      exact le_bot_iff.mp (htop0 ▸ hmax _)
    · right
      have hcut : rankCut H (prof b)
          (prof a) ≠ 0 := by
        intro h0
        apply htop0
        rw [hbot]
        change min (rankCut H (prof b)
          (prof a)) (H - 1 + 1) = 0
        rw [h0]
        exact Nat.zero_min _
      intro e he
      rw [(hreadMember e he).1, (hreadMember e he).2, hbot, ladderSource_eq_bot_iff]
      change min (rankCut H (prof b)
        (prof a))
        (prof a e) = 0 ↔ _
      constructor
      · intro h
        rcases Nat.min_eq_zero_iff.mp h with h' | h'
        · exact absurd h' hcut
        · rw [h']; exact Nat.zero_min _
      · intro h
        rcases Nat.min_eq_zero_iff.mp h with h' | h'
        · rw [h']; exact Nat.min_zero _
        · omega

end ProcessRank.MirrorAttachment

end VaughtConjecture
