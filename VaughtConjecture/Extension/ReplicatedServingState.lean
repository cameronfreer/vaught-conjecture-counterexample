/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedServingCell

/-!
# Toward the serving state: tied cells and the values of codes

Roadmap, Layer 3 ((R3) and (R4), the extension over the tower at a positive cap).

A serving state at the grade `k` (`Seed.ServingStateAt`) has a rank vector agreeing with the
ambient's member `b` over all the cells below the first rank `k_c` where the table of `b` reaches
the cap `c` (`Seed.lt_rankCut_of_ambient`), so cells of one rank in `b` below `k_c` carry one value
of the state, and the decoded readings of two such cells of grade at most `k` must be equal.

**No collision on tied cells** (`Seed.eq_of_tied`): for an ambient `q` lawful below `(univ, j)`, a
cell `u` at `(univ, k)` with `c ≤ q u`, `c ≠ ⊥`, a member `b` whose rungs are below `c` up to the
index `k_c - 1` and reach `c` at `k_c ≥ 2`, and a prescription `P` with the observation of `q` at
`c` at the cells of grade at most `k`: two cells of grade at most `k` with one rank of `b` below
`k_c` carry the same value of `P` (a value of `q` below `c`). The state of `u` agrees with `b` below
`k_c` over all the cells, so it ties the two cells; its capped decoder reads them as `q` capped at
`q u`, which is the reading of a rung of `b` below `k_c`, below `c`.

**The values of codes** (`Label.rankVector_comp`): a map strictly monotone on the values of a
labelling and sending only `⊥` to `⊥` keeps its rank vector; the block compression of the squash
does so on the values of a state, so the code of a state has the rank vector, hence the rank member,
of the state (`Seed.exists_stateCode_rankVector`), and its values lie in the code set fixed by the
seed (`Label.blockCompress_squash_mem_codeSet`).

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

variable {ι : Type*} [Fintype ι]

/-- **A map strictly monotone on the values and sending only `⊥` to `⊥` keeps the rank vector.** -/
theorem rankVector_comp {R : ι → Label.{u}} {θ : Label.{u} → Label.{u}}
    (hθ : StrictMonoOn θ (Set.range R)) (hbot : ∀ d, θ (R d) = ⊥ ↔ R d = ⊥) (d : ι) :
    rankVector (θ ∘ R) d = rankVector R d := by
  classical
  unfold rankVector valueRank
  have hinj : Set.InjOn θ (Set.range R) := hθ.injOn
  have himg : ((univ.image R).filter fun y ↦ y ≠ ⊥ ∧ y ≤ R d).image θ =
      (univ.image (θ ∘ R)).filter fun y ↦ y ≠ ⊥ ∧ y ≤ θ (R d) := by
    ext y
    simp only [mem_image, mem_filter, mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨z, ⟨⟨e, rfl⟩, hz0, hzd⟩, rfl⟩
      exact ⟨⟨e, rfl⟩, fun h ↦ hz0 ((hbot e).mp h), hθ.monotoneOn ⟨e, rfl⟩ ⟨d, rfl⟩ hzd⟩
    · rintro ⟨⟨e, rfl⟩, hy0, hyd⟩
      refine ⟨R e, ⟨⟨e, rfl⟩, fun h ↦ hy0 ((hbot e).mpr h), ?_⟩, rfl⟩
      by_contra hlt
      exact absurd hyd (not_le.mpr (hθ ⟨d, rfl⟩ ⟨e, rfl⟩ (not_le.mp hlt)))
  change #(((univ.image (θ ∘ R)).filter fun y ↦ y ≠ ⊥ ∧ y ≤ θ (R d))) =
    #((univ.image R).filter fun y ↦ y ≠ ⊥ ∧ y ≤ R d)
  rw [← himg, card_image_of_injOn (hinj.mono fun y hy ↦ by
    obtain ⟨e, rfl⟩ := (mem_image.mp (mem_filter.mp hy).1).imp fun _ h ↦ h.2
    exact ⟨e, rfl⟩)]

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

/-- **No collision on tied cells.**  Two cells of grade at most `k` with one rank of `b` below
`k_c` carry the same value of the prescription. -/
theorem eq_of_tied (hcard : (I.attachmentBase g).S.card ≤ H) {j k : ℕ} (hk2 : 2 ≤ k)
    (hkj : k ≤ j) (hkm : k ≤ m + 1) {q : Fin (𝔼).card → Label.{u}}
    (hq : (𝔼).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) fun d ↦ q d)
    {u : Fin (𝔼).card} (hu : (𝔼).toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), k))
    {c : Label.{u}} (hc0 : c ≠ ⊥) (hcu : c ≤ q u) (b : Scheme.RankMember (I.attachmentBase g).S H)
    {kc : ℕ} (hkc : 2 ≤ kc) (hkcH : kc ≤ H)
    (hlow : ∀ i : Fin H, (i : ℕ) + 1 < kc → q (ladderCellE H Γ A B' (b, Sum.inl i)) < c)
    (hreach : c ≤ q (ladderCellE H Γ A B' (b, Sum.inl ⟨kc - 1, by omega⟩)))
    {P : Fin (I.attachment g).card → Label.{u}}
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
      min (P a) c = min (q (I.attachEmb g H Γ A B' a)) c)
    {a₁ a₂ : Fin (I.attachment g).card} (h₁ : (I.attachment g).toCellScheme.grade a₁ ≤ k)
    (h₂ : (I.attachment g).toCellScheme.grade a₂ ≤ k)
    (hb : Scheme.rankProf (I.attachmentBase g).S H b a₁ =
      Scheme.rankProf (I.attachmentBase g).S H b a₂)
    (hbk : Scheme.rankProf (I.attachmentBase g).S H b a₂ < kc) : P a₁ = P a₂ := by
  -- the state of `u` agrees with `b` below `kc`
  have hsep : min (q (ladderCellE H Γ A B' (b, Sum.inl ⟨kc - 2, by omega⟩))) c ≠
      min (q (ladderCellE H Γ A B' (b, Sum.inl ⟨kc - 1, by omega⟩))) c := by
    rw [min_eq_left (hlow ⟨kc - 2, by omega⟩ (by simp only; omega)).le, min_eq_right hreach]
    exact (hlow ⟨kc - 2, by omega⟩ (by simp only; omega)).ne
  obtain ⟨R, -, hR, hread, hcut⟩ := lt_rankCut_of_ambient (B' := B') hcard hk2 hkj hkm hq hu hcu b
    hsep
  set a := Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR with ha
  have hcutk : kc ≤ rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
      (Scheme.rankProf (I.attachmentBase g).S H b) := by
    simp only at hcut; omega
  have hag : RankAgree (rankVector R) (Scheme.rankProf (I.attachmentBase g).S H b) kc :=
    (rankAgree_rankCut H _ _).mono hcutk
  -- the capped decoder of `q` at `u`
  have huY : u ∈ (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) := by
    rw [CellScheme.mem_below, hu]; exact ⟨subset_rfl, hkj⟩
  obtain ⟨θ, hθw, -, hθ⟩ := Scheme.exists_cappedDecoder_below hq huY (congrArg Prod.snd hu)
  have hvis := (I.attachmentBase g).isSelfVisible_one_of_isLawful hR
  -- each tied cell is read as a rung below `kc`, so its value of `q` is below `c`
  have hcell (e : Fin (I.attachment g).card) (he : (I.attachment g).toCellScheme.grade e ≤ k)
      (hek : Scheme.rankProf (I.attachmentBase g).S H b e < kc) :
      θ (R e) = q (I.attachEmb g H Γ A B' e) ∧ P e = q (I.attachEmb g H Γ A B' e) := by
    have hdec : θ (R e) = min (q (I.attachEmb g H Γ A B' e)) (q u) := by
      rw [← hread.1 e he]
      exact hθ _ (by
        rw [hu, CellScheme.mem_below, gradedIndex_attachEmb]
        exact ⟨subset_univ _, he⟩)
    have hre : rankVector R e = Scheme.rankProf (I.attachmentBase g).S H b e :=
      rankVector_eq_of_rankAgree hag hek
    have hlt : min (q (I.attachEmb g H Γ A B' e)) (q u) < c := by
      rw [← hdec]
      rcases Nat.eq_zero_or_pos (rankVector R e) with h0 | hpos
      · rw [(rankVector_eq_zero_iff e).mp h0, hθw.map_bot]
        exact bot_lt_iff_ne_bot.mpr hc0
      · have hr : rankVector R e - 1 < H := by omega
        have hrung := rowAt_rung_of_state hcard hread b ⟨rankVector R e - 1, hr⟩
        simp only at hrung
        have hrc : rankVector R e ≤ rankCut H (Scheme.rankProf (I.attachmentBase g).S H a)
            (Scheme.rankProf (I.attachmentBase g).S H b) := by
          rw [hre]; exact hek.le.trans hcutk
        rw [show rankVector R e - 1 + 1 = rankVector R e by omega, min_eq_right hrc] at hrung
        erw [posTable_rankVector hvis e] at hrung
        rw [← hrung, hθ _ (by rw [hu]; exact ladderCellE_mem_below (by omega) _)]
        exact (min_le_left _ _).trans_lt (hlow _ (by simp only; omega))
    have hqe : q (I.attachEmb g H Γ A B' e) < c := by
      rcases le_total (q (I.attachEmb g H Γ A B' e)) (q u) with h | h
      · rwa [min_eq_left h] at hlt
      · rw [min_eq_right h] at hlt; exact absurd (hcu.trans_lt hlt) (lt_irrefl _)
    refine ⟨hdec.trans (min_eq_left (hqe.le.trans hcu)), ?_⟩
    have h := hPq e he
    rw [min_eq_left hqe.le] at h
    rcases le_total (P e) c with hle | hle
    · rwa [min_eq_left hle] at h
    · rw [min_eq_right hle] at h; exact absurd h hqe.ne'
  obtain ⟨hθ₁, hP₁⟩ := hcell a₁ h₁ (hb ▸ hbk)
  obtain ⟨hθ₂, hP₂⟩ := hcell a₂ h₂ hbk
  have hR12 : R a₁ = R a₂ := eq_of_rankVector_eq ((rankVector_eq_of_rankAgree hag (hb ▸ hbk)).trans
    (hb.trans (rankVector_eq_of_rankAgree hag hbk).symm))
  rw [hP₁, hP₂, ← hθ₁, ← hθ₂, hR12]

variable {d : StageType.{u} α (n + 1)}
  (hd : StageType.restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)

/-- **The code of a state keeps its rank vector**: `Seed.exists_stateCode` with, in addition, the
rank vector of the code equal to that of the state (the compression of the squash is strictly
monotone on the values of the state, being inverted there by the expansion of the unsquash). -/
theorem exists_stateCode_rankVector {p : StageType.{u} α n}
    {hte : StageType.restrictFace (g.trans Fin.castSuccEmb) I.left = some p}
    {Q : StageType.GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hΓ : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : I.attachAdmits g hd Q (m + 2) P) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) (m + 2),
      ∃ σ : Label.{u} → Label.{u}, (∀ j ≤ m + 2, IsWitness (stepSuppressor j) σ) ∧
        (∀ x, σ x = ⊥ → x = ⊥) ∧ (∀ a, σ (R a) = P a) ∧
        ∀ a, rankVector R a = rankVector P a := by
  classical
  set V : Finset Label.{u} := univ.image P with hV
  set W : Finset Label.{u} := V.image (squash V (m + 2)) with hW
  have hPV (a : Fin (I.attachment g).card) : P a ∈ V := mem_image_of_mem _ (mem_univ a)
  have hPW (a : Fin (I.attachment g).card) : squash V (m + 2) (P a) ∈ W :=
    mem_image_of_mem _ (hPV a)
  have hgr (a : Fin (I.attachment g).card) : (I.attachment g).toCellScheme.grade a ≤ m + 2 :=
    (I.attachmentType g).grade_le a
  set θ : Label.{u} → Label.{u} := blockCompress W (m + 2) ∘ squash V (m + 2) with hθdef
  set S : Fin (I.attachment g).card → Label.{u} := squash V (m + 2) ∘ P with hSdef
  have hSl : (I.attachment g).rows.IsLawful S :=
    hP.map_of_bot_iff hP hgr isWitness_squash fun a ↦ squash_eq_bot_iff
  have hSA : I.attachAdmits g hd Q (m + 2) S :=
    attachAdmits_comp hd hQ hPA isWitness_squash (fun a ↦ squash_eq_bot_iff) _
  set R : Fin (I.attachment g).card → Label.{u} := blockCompress W (m + 2) ∘ S with hRdef
  have hRl : (I.attachment g).rows.IsLawful R :=
    hSl.map_of_bot_iff hSl hgr (isWitness_blockCompress (m + 2))
      fun a ↦ blockCompress_eq_bot_iff (hPW a) (m + 2)
  have hRA : I.attachAdmits g hd Q (m + 2) R :=
    attachAdmits_comp hd hQ hSA (isWitness_blockCompress (m + 2))
      (fun a ↦ blockCompress_eq_bot_iff (hPW a) (m + 2)) _
  have hVc : #V ≤ (I.attachment g).card := card_image_le.trans (by simp)
  have hinv (a : Fin (I.attachment g).card) :
      (unsquash V (m + 2) ∘ blockExpand W) (R a) = P a := by
    change unsquash V (m + 2) (blockExpand W (blockCompress W (m + 2)
      (squash V (m + 2) (P a)))) = P a
    rw [blockExpand_blockCompress (hPW a), unsquash_squash (hPV a)]
  have hθmono : Monotone θ :=
    (isWitness_blockCompress (m + 2)).monotone.comp isWitness_squash.monotone
  have hstrict : StrictMonoOn θ (Set.range P) := by
    rintro _ ⟨a₁, rfl⟩ _ ⟨a₂, rfl⟩ hlt
    refine lt_of_le_of_ne (hθmono hlt.le) fun he ↦ hlt.ne ?_
    rw [← hinv a₁, ← hinv a₂]
    exact congrArg _ he
  refine ⟨R, Scheme.LadderBaseData.mem_towerCat.mpr ⟨fun a ↦ hΓ
      (blockCompress_squash_mem_codeSet hVc (hPV a)), hRl, hRA⟩,
    unsquash V (m + 2) ∘ blockExpand W, fun j hj ↦ ?_, fun x hx ↦ ?_, hinv, fun a ↦ ?_⟩
  · exact IsWitness.comp_of_bot_reflecting (isWitness_blockExpand j)
      (isWitness_unsquash.of_le_stepSuppressor hj) fun x hx ↦ unsquash_eq_bot_iff.mp hx
  · exact blockExpand_eq_bot_iff.mp (unsquash_eq_bot_iff.mp hx)
  · exact rankVector_comp hstrict (fun e ↦ (blockCompress_eq_bot_iff (hPW e) (m + 2)).trans
      squash_eq_bot_iff) a

end Seed

end VaughtConjecture
