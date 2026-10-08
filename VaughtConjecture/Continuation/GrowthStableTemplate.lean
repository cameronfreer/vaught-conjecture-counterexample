/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthStableRequests
import VaughtConjecture.Continuation.GrowthTemplate

/-!
# The encoded template at the stable reads

Roadmap, Layer 3 ((R4), the stable evaluation of the growth carrier).

At a legal stage type `T⁺` at `λ_{ξ+1}` with stable reads `Q` of a legal donor `D`
(`StageType.GrowthRequests.StableReads`), the requests have a **template**
(`StageType.GrowthRequests.HasTemplate`): a lawful donor labelling reading the requests from the
cleaned cap row, equal to it on the root.  With the class calibration of the stable reads this
gives the relative lift on the exact class
(`StageType.GrowthRequests.StableReads.hasRelativeLiftOnClass`).

The template is a **code**, not a label: it is built from the cap row of `T⁺`, whose values are
coded (`Scheme.IsCoded`, below `ω ^ 2`), by a block code (`Label.BlockCode`) whose strips are the
blocks of the codes of the references and whose top code is the marker's code read at the offset
`N`.  Every value of the template is `ω · b + i < ω ^ 2`; it is a different object from the
admitted state, the labels of `T⁺` with those of `D`
(`StageType.GrowthRequests.StableReads.correctAt_label`).

The differences with the actual template (`StageType.HollowReferenceCalibration'.exists_template`)
are three.

* **The cap is not labelled `⊤`.**  It is labelled at least `λ_ξ + N`; the capped decoder of the
  labels of `T⁺` still reads every reference `μ + i` and the marker `λ_ξ + i` exactly, since they
  lie below `λ_ξ + N`.
* **The marker lies in a donor block.**  The marker is labelled `λ_ξ + i`, and a donor label
  `λ_ξ + n` has its reference in the same block; the top code is the marker's code at the offset
  `N`, `blockOf sa + N`, and the block code keeps finite parts up to `N` (it commutes with
  visibility replacement up to `N`, `Label.BlockCode.isWitness_code_of_le`).  So no slack below
  the threshold is used.
* **The cap row need not be clean on the root.**  The template is built on the **cleaned** cap row
  (the cap row, `⊥` where `T⁺` is labelled `⊥`), whose root section is lawful: cleaning is a
  witness (`Label.IsWitness.cleaner`) with the bottom pattern of the labels of `T⁺`
  (`StageType.GrowthRequests.StableReads.isLawful_cleanedCapRow_root`).

## References

The template is the growth step of [Kni26, §4]; the stable labels are those of the continuation
of a model at a limit stage, [Kni26, §4.3].
-/

universe u

namespace VaughtConjecture

open Finset

namespace Label

/-! ### Cleaning -/

/-- The **cleaning** of a map `θ`: `⊥` where `θ` reads `⊥`, the identity elsewhere. -/
noncomputable def cleaner (θ : Label.{u} → Label.{u}) (x : Label.{u}) : Label.{u} :=
  if θ x = ⊥ then ⊥ else x

theorem cleaner_of_eq_bot {θ : Label.{u} → Label.{u}} {x : Label.{u}} (h : θ x = ⊥) :
    cleaner θ x = ⊥ :=
  ite_eq_left h

theorem cleaner_of_ne_bot {θ : Label.{u} → Label.{u}} {x : Label.{u}} (h : θ x ≠ ⊥) :
    cleaner θ x = x :=
  ite_eq_right h

/-- The cleaning of a map fixing `⊥` reads `⊥` exactly where the map does. -/
theorem cleaner_eq_bot_iff {θ : Label.{u} → Label.{u}} (hθ : θ ⊥ = ⊥) (x : Label.{u}) :
    cleaner θ x = ⊥ ↔ θ x = ⊥ := by
  by_cases h : θ x = ⊥
  · exact ⟨fun _ ↦ h, fun _ ↦ cleaner_of_eq_bot h⟩
  · rw [cleaner_of_ne_bot h]
    exact ⟨fun hx ↦ absurd (hx ▸ hθ) h, fun hx ↦ absurd hx h⟩

/-- **The cleaning of a witness bounded by `K` is a witness bounded by `K`.** -/
theorem IsWitness.cleaner {K : ℕ} {θ : Label.{u} → Label.{u}}
    (hθ : IsWitness (stepSuppressor K) θ) : IsWitness (stepSuppressor K) (Label.cleaner θ) where
  antitone := hθ.antitone
  isSelfVisible := hθ.isSelfVisible
  map_bot := cleaner_of_eq_bot hθ.map_bot
  monotone x y hxy := by
    by_cases hy : θ y = ⊥
    · have hx : θ x = ⊥ := le_bot_iff.mp (hy ▸ hθ.monotone hxy)
      rw [cleaner_of_eq_bot hx, cleaner_of_eq_bot hy]
    · rw [cleaner_of_ne_bot hy]
      by_cases hx : θ x = ⊥
      · rw [cleaner_of_eq_bot hx]; exact bot_le
      · rw [cleaner_of_ne_bot hx]; exact hxy
  visibilityReplace_comm x k hx i hi := by
    by_cases h0 : θ x = ⊥
    · have h1 : θ (visibilityReplace k i x) = ⊥ := by
        rw [hθ.visibilityReplace_comm x k (by rw [h0]; exact bot_le) i hi, h0,
          visibilityReplace_bot]
      rw [cleaner_of_eq_bot h0, cleaner_of_eq_bot h1, visibilityReplace_bot]
    · rw [cleaner_of_ne_bot h0] at hx ⊢
      have hg : θ x ≤ stepSuppressor K k := by
        by_cases hk : k ≤ K
        · rw [stepSuppressor_of_le hk]; exact le_top
        · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
          exact absurd (hx ▸ hθ.map_bot) h0
      have h1 : θ (visibilityReplace k i x) ≠ ⊥ := by
        rw [hθ.visibilityReplace_comm x k hg i hi]
        exact fun h ↦ h0 (visibilityReplace_eq_bot_iff.mp h)
      rw [cleaner_of_ne_bot h1]

/-! ### Block codes up to the listed-offset bound -/

namespace BlockCode

variable (B : BlockCode.{u})

/-- **The code commutes with visibility replacement up to the listed-offset bound**: at every
threshold `k` at most `N` and at most the finite part of the top code, with every value
`i ≤ k`. -/
theorem code_visibilityReplace_of_le (x : Label.{u}) {k i : ℕ} (hkN : k ≤ B.N)
    (hkt : k ≤ finNat B.htop) (hi : i ≤ k) :
    B.code (visibilityReplace k i x) = visibilityReplace k i (B.code x) := by
  induction x using Label.recBotCoeTop with
  | bot => rfl
  | top =>
    rw [visibilityReplace_top, code_top, visibilityReplace_coe, visibilityReplace_eq_blockOf,
      ite_eq_right (not_lt.mpr hkt), blockOf_add_finNat]
  | coe a =>
    rw [visibilityReplace_coe, visibilityReplace_eq_blockOf, code_coe, code_coe]
    have hμ := isSuccPrelimit_blockOf a
    by_cases hfa : finNat a < k
    · rw [ite_eq_left hfa]
      have hb : blockOf (blockOf a + i) = blockOf a := blockOf_add_natCast hμ i
      have hf : finNat (blockOf a + i) = i := finNat_add_natCast hμ i
      rcases h : B.Λ (blockOf a) with _ | l
      · rw [B.codeOrd_of_none h, B.codeOrd_of_none (by rw [hb]; exact h)]
        rfl
      · have hl := B.Λ_limit _ l h
        rw [B.codeOrd_of_some h, B.codeOrd_of_some (by rw [hb]; exact h), off, off, hb, hf]
        by_cases hls : B.listed (blockOf a)
        · rw [ite_eq_left hls, ite_eq_left hls, min_eq_left (hi.trans hkN),
            min_eq_left (hfa.le.trans hkN), visibilityReplace_coe_add hl, ite_eq_left hfa]
        · rw [ite_eq_right hls, ite_eq_right hls, visibilityReplace_coe_add hl,
            ite_eq_right (not_lt.mpr hkN)]
    · rw [ite_eq_right hfa, blockOf_add_finNat]
      rcases h : B.Λ (blockOf a) with _ | l
      · rw [B.codeOrd_of_none h]; rfl
      · have hl := B.Λ_limit _ l h
        rw [B.codeOrd_of_some h, visibilityReplace_coe_add hl, ite_eq_right]
        unfold off
        split_ifs
        · exact not_lt.mpr (le_min (not_lt.mp hfa) hkN)
        · exact not_lt.mpr hkN

/-- **The code is a witness bounded by every grade `K`** at most the listed-offset bound and the
finite part of the top code. -/
theorem isWitness_code_of_le {K : ℕ} (hKN : K ≤ B.N) (hKt : K ≤ finNat B.htop) :
    IsWitness (stepSuppressor K) B.code where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := rfl
  monotone := B.monotone_code
  visibilityReplace_comm x k hx i hi := by
    by_cases hk : k ≤ K
    · exact B.code_visibilityReplace_of_le x (hk.trans hKN) (hk.trans hKt) hi
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]
      exact B.code_visibilityReplace_eq_bot hx k i

end BlockCode

end Label

namespace StageType.GrowthRequests

open Label

variable {ξ : Ordinal.{u}} {m k : ℕ} {Tp : StageType.{u} (blockStage (ξ + 1)) m}
  {f : Fin k ↪ Fin m} {P : StageType.{u} (blockStage (ξ + 1)) k}
  {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)}
  (hP : restrictFace f Tp = some P) (hdp : restrictFace Fin.castSuccEmb D = some P)

/-- **The cleaned cap row is lawful on the root**: the root section of the cap row is lawful, and
its cleaning is its image under the cleaning of the capped decoder of the labels of `T⁺`, a
witness with the bottom pattern of the root labels (`CellScheme.Rows.IsLawful.map_of_bot_iff`). -/
theorem StableReads.isLawful_cleanedCapRow_root {Q : GrowthRequests Tp D.toScheme}
    (hQ : Q.StableReads ξ) (hT : Tp.IsLegal) :
    P.rows.IsLawful fun i ↦ Q.cleanedCapRow (Tp.faceCell hP i) := by
  obtain ⟨θ, hW, -, hθr⟩ := Q.exists_capDecoder Tp.isLawful hQ.scope_cap
  have hgi : Tp.toCellScheme.gradedIndex Q.cap = ((univ : Finset (Fin m)), Q.threshold) := by
    rw [← hQ.scope_cap]; rfl
  have hlaw : Tp.rows.IsLawful (Tp.rowAt Q.cap) := Scheme.isLawful_rowAt hT.isConsistent hgi
  have hgr (i : Fin P.card) : Tp.toCellScheme.grade (Tp.faceCell hP i) ≤ Q.threshold :=
    (hQ.classCalibrated hP).root i
  have hcb := hQ.label_cap_ne_bot
  have hbot (i : Fin P.card) :
      cleaner θ (Tp.rowAt Q.cap (Tp.faceCell hP i)) = ⊥ ↔ P.label i = ⊥ := by
    rw [cleaner_eq_bot_iff hW.map_bot, hθr _ (hgr i), label_faceCell hP i]
    constructor
    · intro h
      rcases min_eq_bot.mp h with h | h
      · exact h
      · exact absurd h hcb
    · intro h
      rw [h, min_eq_left bot_le]
  have hr : P.rows.IsLawful fun i ↦ Tp.rowAt Q.cap (Tp.faceCell hP i) := by
    obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff Tp f).mp hP
    exact hlaw.comap (Tp.isLowerEmbedding_comap f)
  have h1 := hr.map_of_bot_iff P.isLawful (K := Q.threshold)
    (fun d ↦ (P.grade_le d).trans (by have := hQ.arity; omega)) hW.cleaner hbot
  convert h1 using 1
  funext i
  simp only [Function.comp_apply]
  by_cases hb : Tp.label (Tp.faceCell hP i) = ⊥
  · have hP0 : P.label i = ⊥ := by rwa [← label_faceCell hP i]
    simp only [cleanedCapRow, hb, ite_true]
    exact ((hbot i).mpr hP0).symm
  · rw [Q.cleanedCapRow_of_ne_bot hb, cleaner_of_ne_bot]
    intro h
    exact hb ((label_faceCell hP i).trans ((hbot i).mp (cleaner_of_eq_bot h)))

/-- **The encoded template at the stable reads.**  At a legal stage type `T⁺` at `λ_{ξ+1}` with
stable reads of a legal donor `D` with a nonempty root, the requests have a template: the image of
the donor's labels under a block code whose strips are the blocks of the reference codes in the
cap row and whose top code is the marker's code read at the threshold, with its root restored to
the cleaned cap row (`StageType.GrowthRequests.exists_template_of_encoding`). -/
theorem StableReads.hasTemplate {Q : GrowthRequests Tp D.toScheme} (hQ : Q.StableReads ξ)
    (hT : Tp.IsLegal) (hD : D.IsLegal) (hk : 0 < k) : Q.HasTemplate hP hdp := by
  classical
  set N := Q.threshold with hNdef
  have hN0 : 0 < N := by have := hQ.arity; omega
  obtain ⟨θ, hW, -, hθr⟩ := Q.exists_capDecoder Tp.isLawful hQ.scope_cap
  have hθm := hW.monotone
  have hθb := hW.map_bot
  have hθv' : ∀ k' ≤ N, ∀ i ≤ k', ∀ x, θ (visibilityReplace k' i x) =
      visibilityReplace k' i (θ x) := fun k' hk' i hi x ↦
    hW.visibilityReplace_comm x k' (by rw [stepSuppressor_of_le hk']; exact le_top) i hi
  have hcb := hQ.label_cap_ne_bot
  have hlam := isSuccPrelimit_blockStage ξ
  -- the codes of the cells below the cap with a label other than `⊥`
  have hcode (x : Fin Tp.card) (hx : Tp.toCellScheme.grade x ≤ N) (hxb : Tp.label x ≠ ⊥) :
      Tp.rowAt Q.cap x = (ordOf (Tp.rowAt Q.cap x) : Label.{u}) := by
    refine eq_coe_ordOf (fun h0 ↦ hxb ?_) (rowAt_ne_top Q.cap x)
    have h1 := hθr x hx
    rw [h0, hθb] at h1
    rcases min_eq_bot.mp h1.symm with h | h
    · exact h
    · exact absurd h hcb
  -- the data of the exact requests
  have hsel : ∀ j : Fin D.card, ∃ (μ : Ordinal.{u}) (i : ℕ), j ∈ Q.exacts →
      Order.IsSuccPrelimit μ ∧ μ ≤ blockStage ξ ∧ i < N ∧
      Tp.label (Q.ref j) = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
      D.label j = ((μ + Q.offset j : Ordinal.{u}) : Label.{u}) ∧
      Tp.toCellScheme.grade (Q.ref j) ≤ N ∧ Q.offset j < N := by
    intro j
    by_cases hj : j ∈ Q.exacts
    · obtain ⟨hg, hoff, μ, i, h1, h2, h3, h4, h5⟩ := hQ.ref j hj
      exact ⟨μ, i, fun _ ↦ ⟨h1, h2, h3, h4, h5, hg, hoff⟩⟩
    · exact ⟨0, 0, fun h ↦ absurd h hj⟩
  choose μ ir hsel using hsel
  obtain ⟨im, him, hml⟩ := hQ.label_marker
  have hmg : Tp.toCellScheme.grade Q.marker ≤ N := hQ.grade_marker
  have hrefb (j : Fin D.card) (hj : j ∈ Q.exacts) : Tp.label (Q.ref j) ≠ ⊥ := by
    rw [(hsel j hj).2.2.2.1]; exact WithBot.coe_ne_bot
  have hmkb : Tp.label Q.marker ≠ ⊥ := by rw [hml]; exact WithBot.coe_ne_bot
  set code : Fin D.card → Ordinal.{u} := fun j ↦ ordOf (Tp.rowAt Q.cap (Q.ref j)) with hcodedef
  set sa : Ordinal.{u} := ordOf (Tp.rowAt Q.cap Q.marker) with hsadef
  have hread (j : Fin D.card) (hj : j ∈ Q.exacts) :
      θ ((code j : Ordinal.{u}) : Label.{u}) = ((μ j + ir j : Ordinal.{u}) : Label.{u}) := by
    obtain ⟨-, hμξ, hi, hl, -, hg, -⟩ := hsel j hj
    rw [← hcode _ hg (hrefb j hj), hθr _ hg, hl, min_eq_left (hQ.lt_label_cap hμξ hi).le]
  have hreadm : θ ((sa : Ordinal.{u}) : Label.{u}) =
      ((blockStage ξ + im : Ordinal.{u}) : Label.{u}) := by
    rw [← hcode _ hmg hmkb, hθr _ hmg, hml, min_eq_left (hQ.lt_label_cap le_rfl him).le]
  have hfm : finNat sa = im := finNat_eq_of_read hθv' hlam him hreadm
  -- the blocks of the references
  set S : Finset Ordinal.{u} := (univ.filter (· ∈ Q.exacts)).image μ with hSdef
  have hmemS {ν : Ordinal.{u}} : ν ∈ S ↔ ∃ j, j ∈ Q.exacts ∧ μ j = ν := by
    simp [hSdef]
  let strip : Ordinal.{u} → Ordinal.{u} := fun ν ↦
    if h : ∃ j, j ∈ Q.exacts ∧ μ j = ν then blockOf (code (Classical.choose h)) else 0
  have hstrip (j : Fin D.card) (hj : j ∈ Q.exacts) : strip (μ j) = blockOf (code j) := by
    have h : ∃ j', j' ∈ Q.exacts ∧ μ j' = μ j := ⟨j, hj, rfl⟩
    have hs : strip (μ j) = blockOf (code (Classical.choose h)) := dite_eq_left h
    obtain ⟨hj', hμj'⟩ := Classical.choose_spec h
    have hr' := hread _ hj'
    rw [hμj'] at hr'
    rw [hs]
    exact blockOf_eq_of_read hθm hθv' hN0 (hsel j hj).1 (hsel _ hj').2.2.1 (hsel j hj).2.2.1 hr'
      (hread j hj)
  have hlim : ∀ ν ∈ S, Order.IsSuccPrelimit (strip ν) := by
    intro ν hν
    obtain ⟨j, hj, rfl⟩ := hmemS.mp hν
    rw [hstrip j hj]; exact isSuccPrelimit_blockOf _
  -- the top code: the marker's code read at the threshold
  set htop : Ordinal.{u} := blockOf sa + N with hhtop
  have hfinTop : finNat htop = N := finNat_add_natCast (isSuccPrelimit_blockOf sa) N
  have hvrm : Ordinal.visibilityReplace N N sa = htop :=
    visibilityReplace_blockOf_of_lt (hfm ▸ him) N
  have hle : ∀ ν ∈ S, strip ν + N ≤ htop := by
    intro ν hν
    obtain ⟨j, hj, rfl⟩ := hmemS.mp hν
    rw [hstrip j hj]
    obtain ⟨hμ, hμξ, hi, -⟩ := hsel j hj
    rcases hμξ.lt_or_eq with hlt | heq
    · have h1 := blockOf_lt_of_read hθm hθv' hμ hlam hlt hi him (hread j hj) hreadm
      exact (add_natCast_lt_of_lt (isSuccPrelimit_blockOf sa) h1 N).le.trans le_self_add
    · have hr := hread j hj
      rw [heq] at hr
      rw [blockOf_eq_of_read hθm hθv' hN0 hlam hi him hr hreadm]
  have hstrict : ∀ ν ∈ S, ∀ ν' ∈ S, ν < ν' → strip ν < strip ν' := by
    intro ν hν ν' hν' hlt
    obtain ⟨j, hj, rfl⟩ := hmemS.mp hν
    obtain ⟨j', hj', rfl⟩ := hmemS.mp hν'
    rw [hstrip j hj, hstrip j' hj']
    exact blockOf_lt_of_read hθm hθv' (hsel j hj).1 (hsel j' hj').1 hlt (hsel j hj).2.2.1
      (hsel j' hj').2.2.1 (hread j hj) (hread j' hj')
  have hRtop : N - 1 ≤ finNat htop := by rw [hfinTop]; omega
  set B := BlockCode.ofFinset N (N - 1) (by omega) S strip htop hlim hle hstrict hRtop with hB
  have hBΛ (j : Fin D.card) (hj : j ∈ Q.exacts) : B.Λ (μ j) = some (strip (μ j)) :=
    BlockCode.ofFinset_Λ N (N - 1) (by omega) S strip htop hlim hle hstrict hRtop
      (hmemS.mpr ⟨j, hj, rfl⟩)
  -- the code of an exact label
  have hencF (j : Fin D.card) (hj : j ∈ Q.exacts) :
      B.code (D.label j) = ((blockOf (code j) + Q.offset j : Ordinal.{u}) : Label.{u}) := by
    obtain ⟨hμ, -, -, -, hd, -, hoff⟩ := hsel j hj
    rw [hd, BlockCode.code_coe, B.codeOrd_listed
      (by rw [blockOf_add_natCast hμ]; exact hmemS.mpr ⟨j, hj, rfl⟩)
      (by rw [blockOf_add_natCast hμ]; exact hBΛ j hj)
      (by rw [finNat_add_natCast hμ]; exact hoff.le),
      finNat_add_natCast hμ, hstrip j hj]
  -- the code is a witness bounded by the arity of the donor, and reads only `⊥` as `⊥`
  have henc : IsWitness (stepSuppressor (k + 1)) B.code :=
    B.isWitness_code_of_le hQ.arity (by rw [show finNat B.htop = N from hfinTop]; exact hQ.arity)
  have hbot (j : Fin D.card) (h : B.code (D.label j) = ⊥) : D.label j = ⊥ := by
    by_contra hb
    by_cases ht : D.label j = ⊤
    · rw [ht, BlockCode.code_top] at h; exact WithBot.coe_ne_bot h
    · rw [hencF j ((hQ.mem_exacts j).mpr ⟨hb, ht⟩)] at h; exact WithBot.coe_ne_bot h
  have hHvis : IsSelfVisible (k + 1) ((htop : Ordinal.{u}) : Label.{u}) :=
    isSelfVisible_coe.mpr (by
      rw [finNat_spec]; exact_mod_cast (show k + 1 ≤ finNat htop by rw [hfinTop]; exact hQ.arity))
  -- the cleaned cap row
  have heC (x : Fin Tp.card) (hx : Tp.label x ≠ ⊥) : Q.cleanedCapRow x = Tp.rowAt Q.cap x :=
    Q.cleanedCapRow_of_ne_bot hx
  have heCb (x : Fin Tp.card) (hx : Tp.label x = ⊥) : Q.cleanedCapRow x = ⊥ := ite_eq_left hx
  have heCr : Q.cleanedCapRow Q.marker = ((sa : Ordinal.{u}) : Label.{u}) := by
    rw [heC _ hmkb]
    exact hcode _ hmg hmkb
  have heCa (j : Fin D.card) (hj : j ∈ Q.exacts) :
      Q.cleanedCapRow (Q.ref j) = ((code j : Ordinal.{u}) : Label.{u}) := by
    rw [heC _ (hrefb j hj)]
    exact hcode _ (hsel j hj).2.2.2.2.2.1 (hrefb j hj)
  have hfinref (j : Fin D.card) (hj : j ∈ Q.exacts) : finNat (code j) = ir j :=
    finNat_eq_of_read hθv' (hsel j hj).1 (hsel j hj).2.2.1 (hread j hj)
  have hFj (j : Fin D.card) (hj : j ∈ Q.exacts) :
      visibilityReplace Q.threshold (Q.offset j) (Q.cleanedCapRow (Q.ref j)) =
        ((blockOf (code j) + Q.offset j : Ordinal.{u}) : Label.{u}) := by
    rw [heCa j hj, visibilityReplace_coe,
      visibilityReplace_blockOf_of_lt (by rw [hfinref j hj]; exact (hsel j hj).2.2.1)]
  have hltH (j : Fin D.card) (hj : j ∈ Q.exacts) :
      ((blockOf (code j) + Q.offset j : Ordinal.{u}) : Label.{u}) <
        ((htop : Ordinal.{u}) : Label.{u}) := by
    rw [coe_lt_coe_iff]
    refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr ?_) (hstrip j hj ▸ hle (μ j)
      (hmemS.mpr ⟨j, hj, rfl⟩))
    exact_mod_cast (hsel j hj).2.2.2.2.2.2
  -- the cells of the root
  have hroot (i : Fin P.card) : min (B.code (D.label (D.faceCell hdp i))) (htop : Label.{u}) =
      min (Q.cleanedCapRow (Tp.faceCell hP i)) (htop : Label.{u}) := by
    set x := Tp.faceCell hP i with hxdef
    have hlx : D.label (D.faceCell hdp i) = Tp.label x := by
      rw [StageType.label_faceCell, StageType.label_faceCell]
    have hxg : Tp.toCellScheme.grade x ≤ N := (hQ.classCalibrated hP).root i
    by_cases hb : Tp.label x = ⊥
    · rw [hlx, hb, BlockCode.code_bot, heCb x hb]
    by_cases ht : Tp.label x = ⊤
    · rw [hlx, ht, BlockCode.code_top]
      change min ((htop : Ordinal.{u}) : Label.{u}) _ = _
      rw [min_self, heC x hb]
      refine (min_eq_right ?_).symm
      -- the code of a root cell labelled `⊤` is at least the top code
      rw [hcode x hxg hb, coe_le_coe_iff]
      by_contra hlt
      rw [not_le] at hlt
      have hsplit : htop = blockOf sa + ((N - 1 : ℕ) : Ordinal.{u}) + 1 := by
        rw [hhtop, add_assoc, ← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ N)]
      rw [hsplit, Order.lt_add_one_iff] at hlt
      have h2 := hθm (coe_le_coe_iff.mpr hlt)
      have h3 : ((blockOf sa + ((N - 1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) =
          visibilityReplace N (N - 1) ((sa : Ordinal.{u}) : Label.{u}) := by
        rw [visibilityReplace_coe, visibilityReplace_blockOf_of_lt (hfm ▸ him)]
      rw [← hcode x hxg hb, hθr x hxg, ht, min_eq_right le_top, h3,
        hθv' N le_rfl (N - 1) (by omega), hreadm,
        visibilityReplace_coe_add_natCast hlam him (N - 1)] at h2
      exact absurd (hQ.le_label_cap.trans h2) (not_le.mpr (coe_lt_coe_iff.mpr
        ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (by omega)))))
    · set j := D.faceCell hdp i
      have hj : j ∈ Q.exacts :=
        (hQ.mem_exacts j).mpr ⟨by rw [hlx]; exact hb, by rw [hlx]; exact ht⟩
      obtain ⟨hμ, hμξ, hi, -, hdl, -, hoff⟩ := hsel j hj
      have hsx : θ ((ordOf (Tp.rowAt Q.cap x) : Ordinal.{u}) : Label.{u}) =
          ((μ j + Q.offset j : Ordinal.{u}) : Label.{u}) := by
        rw [← hcode x hxg hb, hθr x hxg, ← hlx, hdl,
          min_eq_left (hQ.lt_label_cap hμξ hoff).le]
      have hf := finNat_eq_of_read hθv' hμ hoff hsx
      have hbk := blockOf_eq_of_read hθm hθv' hN0 hμ hoff hi hsx (hread j hj)
      have hxo : ordOf (Tp.rowAt Q.cap x) = blockOf (code j) + Q.offset j := by
        rw [← blockOf_add_finNat (ordOf (Tp.rowAt Q.cap x)), hf, hbk]
      rw [hencF j hj, heC x hb, hcode x hxg hb, hxo]
  obtain ⟨V, hV, hVr, hVc, hVf, hVz⟩ := GrowthRequests.exists_template_of_encoding
    (eC := Q.cleanedCapRow) hP hdp Q hD hk (hQ.isLawful_cleanedCapRow_root hP hT) henc hbot
    WithBot.coe_ne_bot hHvis hroot (fun j hj ↦ (hQ.mem_bottoms j).mp hj)
    (fun j hj ↦ by rw [hencF j hj, hFj j hj]) (fun j hj ↦ by rw [hFj j hj]; exact hltH j hj)
    (fun j hj ↦ by rw [(hQ.mem_highs j).mp hj, BlockCode.code_top]; rfl)
    (by
      simp only [GrowthRequests.readMarker]
      rw [hQ.markerOffset_eq, heCr, visibilityReplace_coe, hvrm])
  exact ⟨V, hV, hVr, hVc, hVf, hVz⟩

/-- **The relative lift on the exact class at the stable reads**: the stable reads are calibrated
on the class and have a template, so the relative lift on the exact class holds
(`StageType.GrowthRequests.ClassCalibrated.hasRelativeLiftOnClass`). -/
theorem StableReads.hasRelativeLiftOnClass {Q : GrowthRequests Tp D.toScheme}
    (hQ : Q.StableReads ξ) (hT : Tp.IsLegal) (hD : D.IsLegal) (hk : 0 < k) :
    Q.HasRelativeLiftOnClass hP hdp :=
  (hQ.classCalibrated hP).hasRelativeLiftOnClass hP hdp (hQ.hasTemplate hP hdp hT hD hk) hD hk

end StageType.GrowthRequests

end VaughtConjecture
