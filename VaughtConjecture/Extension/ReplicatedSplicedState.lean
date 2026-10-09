/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedServingState
import VaughtConjecture.Extension.LadderTowerContextLiftAmbient

/-!
# The spliced state: the prescription up to a grade, the ambient capped above

Roadmap, Layer 3 ((R3) and (R4), the extension over the tower at a positive cap).

The **spliced state** (`Seed.splicedState k P q c`): the prescription `P` at the cells of grade
at most `k`, the ambient's state capped at the cap `c` above.

* **Lawful** (`Seed.isLawful_splicedState`), with no further condition: a splice at the grade `k`
  (`CellScheme.Rows.IsLawfulBelow.splice`) of `P` and of the ambient's state capped at `c` (a
  witness bounded by the grade of the ambient, `c` being self-visible there), which agree capped at
  `c` below the grade; a cell above the grade reads the cells below it only up to `c`.
* **Admitted** (`Seed.attachAdmits_splicedState`): at a threshold `N ≤ k` the requests read only the
  admitted prescription; above `k` the cap value is at most `c` and the reads are those of the
  admitted ambient (`Seed.ambientAdmitted`) capped at `c`; above the grade of the ambient the cap
  value is `⊥`.
* **Rank agreement** (`Seed.rankAgree_splicedState`, from `Label.rankAgree_of_separates`): below
  `c` the spliced state is the ambient's state (`Seed.splicedState_cases`), so its rank vector
  agrees with a dense rank vector `b` below `kc` exactly when the ambient's state separates `b`
  below `kc` at `c` (below `c` exactly at the ranks below `kc`, ordered as `b` there, `⊥` exactly
  at rank `0`, so in particular `b` vanishes above the grade of the ambient).  **A tie breaks it**
  (`Seed.not_rankAgree_splicedState`, `Label.not_rankAgree_of_tie`): two cells below `c` with one
  value of the ambient's state and distinct ranks of `b` below `kc`.
* **The code** (`Seed.exists_splicedCode`): a state of the catalogue at `k` (values in the code
  set), a witness bounded by `k` reading it as `P` capped at `x` below the grade, and its rank
  vector, that of the spliced state (`Seed.exists_stateCode_rankVector`), agreeing with `b` below
  `kc` under the separation.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Label

variable {ι : Type*} [Fintype ι]

/-- **Rank agreement from separation below a cap.**  If `Z` is below `c` exactly at the cells of
rank below `kc` in a dense rank vector `b`, at least `c` elsewhere, orders the cells of rank below
`kc` as `b` does, and is `⊥` exactly at rank `0`, then the rank vector of `Z` agrees with `b` below
`kc`. -/
theorem rankAgree_of_separates {Z : ι → Label.{u}} {b : ι → ℕ} {kc : ℕ} {c : Label.{u}}
    (hdense : ∀ i, 0 < i → ∀ d, i ≤ b d → ∃ e, b e = i)
    (hlow : ∀ a, b a < kc → Z a < c) (hhigh : ∀ a, kc ≤ b a → c ≤ Z a)
    (hord : ∀ a₁ a₂, b a₁ < kc → b a₂ < kc → (Z a₁ ≤ Z a₂ ↔ b a₁ ≤ b a₂))
    (hbot : ∀ a, Z a = ⊥ ↔ b a = 0) : RankAgree (rankVector Z) b kc := by
  classical
  have hlowb (e : ι) (hz : Z e < c) : b e < kc := by
    by_contra h; exact absurd (hhigh e (not_lt.mp h)) (not_le.mpr hz)
  -- below `kc` the rank is the rank of `b`
  have hrank (d : ι) (hd : b d < kc) : rankVector Z d = b d := by
    unfold rankVector valueRank
    have hI : b d = #(Icc 1 (b d)) := by simp
    rw [hI]
    refine Finset.card_bij (s := (univ.image Z).filter fun y ↦ y ≠ ⊥ ∧ y ≤ Z d)
      (t := Icc 1 (b d))
      (fun y hy ↦ b (Classical.choose (mem_image.mp (mem_filter.mp hy).1)))
      (fun y hy ↦ ?_) (fun y₁ hy₁ y₂ hy₂ h ↦ ?_) (fun r hr ↦ ?_)
    · obtain ⟨-, hy0, hyd⟩ := mem_filter.mp hy
      have hs := Classical.choose_spec (mem_image.mp (mem_filter.mp hy).1)
      set e := Classical.choose (mem_image.mp (mem_filter.mp hy).1)
      have he : b e < kc := hlowb e (hs.2 ▸ hyd.trans_lt (hlow d hd))
      refine mem_Icc.mpr ⟨Nat.pos_of_ne_zero fun h0 ↦ hy0 (hs.2 ▸ (hbot e).mpr h0), ?_⟩
      exact (hord e d he hd).mp (hs.2 ▸ hyd)
    · have hs₁ := Classical.choose_spec (mem_image.mp (mem_filter.mp hy₁).1)
      have hs₂ := Classical.choose_spec (mem_image.mp (mem_filter.mp hy₂).1)
      set e₁ := Classical.choose (mem_image.mp (mem_filter.mp hy₁).1)
      set e₂ := Classical.choose (mem_image.mp (mem_filter.mp hy₂).1)
      have he₁ : b e₁ < kc := hlowb e₁ (hs₁.2 ▸ (mem_filter.mp hy₁).2.2.trans_lt (hlow d hd))
      have he₂ : b e₂ < kc := hlowb e₂ (hs₂.2 ▸ (mem_filter.mp hy₂).2.2.trans_lt (hlow d hd))
      rw [← hs₁.2, ← hs₂.2]
      exact le_antisymm ((hord e₁ e₂ he₁ he₂).mpr h.le) ((hord e₂ e₁ he₂ he₁).mpr h.ge)
    · obtain ⟨hr1, hrd⟩ := mem_Icc.mp hr
      obtain ⟨e, he⟩ := hdense r hr1 d hrd
      have hek : b e < kc := he ▸ hrd.trans_lt hd
      refine ⟨Z e, mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ e),
        fun h0 ↦ by have := (hbot e).mp h0; omega, (hord e d hek hd).mpr (he ▸ hrd)⟩, ?_⟩
      have hs := Classical.choose_spec (mem_image.mp
        (mem_filter.mp (mem_filter.mpr ⟨mem_image_of_mem Z (mem_univ e),
          fun h0 ↦ by have := (hbot e).mp h0; omega, (hord e d hek hd).mpr (he ▸ hrd)⟩ :
            Z e ∈ (univ.image Z).filter fun y ↦ y ≠ ⊥ ∧ y ≤ Z d)).1)
      set e' := Classical.choose (mem_image.mp (mem_filter.mp
        (mem_filter.mpr ⟨mem_image_of_mem Z (mem_univ e),
          fun h0 ↦ by have := (hbot e).mp h0; omega, (hord e d hek hd).mpr (he ▸ hrd)⟩ :
            Z e ∈ (univ.image Z).filter fun y ↦ y ≠ ⊥ ∧ y ≤ Z d)).1)
      have he' : b e' < kc := hlowb e' (hs.2 ▸ hlow e hek)
      rw [← he]
      exact le_antisymm ((hord e' e he' hek).mp hs.2.le) ((hord e e' hek he').mp hs.2.ge)
  intro d
  rcases lt_or_ge (b d) kc with hd | hd
  · rw [hrank d hd]
  · rw [min_eq_right hd]
    rcases Nat.eq_zero_or_pos kc with h0 | hkc
    · subst h0; simp
    have hd0 : Z d ≠ ⊥ := fun h ↦ by have := (hbot d).mp h; omega
    refine min_eq_right ?_
    rcases Nat.lt_or_ge kc 2 with hk1 | hk2
    · have := (rankVector_eq_zero_iff (R := Z) d).not.mpr hd0
      omega
    obtain ⟨e, he⟩ := hdense (kc - 1) (by omega) d (by omega)
    have hre := hrank e (by omega)
    have hlt : rankVector Z e < rankVector Z d :=
      valueRank_lt_valueRank hd0 ((hlow e (by omega)).trans_le (hhigh d hd))
    omega

/-- **A tie breaks rank agreement**: two cells with one value of `Z` and distinct ranks of `b`
below `kc`. -/
theorem not_rankAgree_of_tie {Z : ι → Label.{u}} {b : ι → ℕ} {kc : ℕ} {a₁ a₂ : ι}
    (hZ : Z a₁ = Z a₂) (hb : b a₁ ≠ b a₂) (h₁ : b a₁ < kc) (h₂ : b a₂ < kc) :
    ¬ RankAgree (rankVector Z) b kc := fun hag ↦ hb <|
  (rankVector_eq_of_rankAgree hag h₁).symm.trans
    ((show rankVector Z a₁ = rankVector Z a₂ by unfold rankVector; rw [hZ]).trans
      (rankVector_eq_of_rankAgree hag h₂))

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The replicated scheme. -/
local notation "𝔼" => Seed.replicated I g H Γ A B'

variable (H Γ A B') in
/-- **The spliced state**: the prescription `P` at the cells of grade at most `k`, the ambient's
state capped at `c` above. -/
noncomputable def splicedState {j : ℕ} (k : ℕ) (P : Fin (I.attachment g).card → Label.{u})
    (q : (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) → Label.{u}) (c : Label.{u}) :
    Fin (I.attachment g).card → Label.{u} := fun a ↦
  if (I.attachment g).toCellScheme.grade a ≤ k then P a
    else min (ambientState H Γ A B' q a) c

/-- **The spliced state is lawful** (a splice at the grade `k` of `P` and of the ambient's state
capped at `c`, which agree capped at `c` below the grade). -/
theorem isLawful_splicedState {j k : ℕ}
    {q : (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (hq : (𝔼).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q) {c : Label.{u}}
    (hc : IsSelfVisible j c) (hc0 : c ≠ ⊥) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : (I.attachment g).rows.IsLawful P)
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
      min (P a) c = min (ambientState H Γ A B' q a) c) :
    (I.attachment g).rows.IsLawful (splicedState H Γ A B' k P q c) := by
  have h1 := isLawful_ambientState hq
  have h2 : (I.attachment g).rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ min (ambientState H Γ A B' q d) c := by
    have h := (h1.isLawfulBelow ((univ : Finset (Fin (m + 2))), j)).map_of_bot_iff
      (h1.isLawfulBelow _) (fun d ↦ d.2.2) (ν := fun x ↦ min (id x) c)
      ((IsWitness.id_step j).min_const hc) fun d ↦
        ⟨fun h ↦ (min_eq_bot.mp h).resolve_right hc0, fun h ↦ by
          change min (ambientState H Γ A B' q d) c = ⊥
          rw [h, min_bot_left]⟩
    exact h
  have h3 := CellScheme.Rows.isLawfulBelow_extendAbove (K := m + 2)
    (w := fun d ↦ min (ambientState H Γ A B' q d) c) h2
  set U : Fin (I.attachment g).card → Label.{u} := fun d ↦
    if (I.attachment g).toCellScheme.grade d ≤ j then min (ambientState H Γ A B' q d) c else ⊥
    with hU
  have hUe (d : Fin (I.attachment g).card) : U d = min (ambientState H Γ A B' q d) c := by
    rw [hU]
    beta_reduce
    by_cases h : (I.attachment g).toCellScheme.grade d ≤ j
    · exact ite_eq_left h
    · rw [ite_eq_right h, ambientState_of_lt d (not_le.mp h), min_bot_left]
  have h4 := CellScheme.Rows.IsLawfulBelow.splice (B := univ) (J := m + 2) (j := k) (M := c)
    (q := U) (v := P) h3 (hP.isLawfulBelow _)
    (fun d _ _ ↦ by rw [hUe]; exact min_le_right _ _)
    (fun d hd ↦ by rw [hUe, min_assoc, min_self]; exact hPq d hd.2)
  refine CellScheme.Rows.isLawful_of_isLawfulBelow attachment_mem_below_top
    ((CellScheme.Rows.isLawfulBelow_congr
      (w := fun d ↦ (I.attachment g).toCellScheme.splice k U P d) fun d _ ↦ ?_).mp h4)
  unfold splicedState CellScheme.splice
  split_ifs
  · rfl
  · exact hUe d

/-- Below the cap the spliced state is the ambient's state; at or above it, at least the cap. -/
theorem splicedState_cases {j k : ℕ}
    {q : (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) → Label.{u}} {c : Label.{u}}
    {P : Fin (I.attachment g).card → Label.{u}}
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
      min (P a) c = min (ambientState H Γ A B' q a) c) (a : Fin (I.attachment g).card) :
    (ambientState H Γ A B' q a < c → splicedState H Γ A B' k P q c a = ambientState H Γ A B' q a) ∧
      (c ≤ ambientState H Γ A B' q a → c ≤ splicedState H Γ A B' k P q c a) := by
  unfold splicedState
  split_ifs with h
  · have e := hPq a h
    constructor
    · intro hlt
      rw [min_eq_left hlt.le] at e
      rcases le_total (P a) c with hle | hle
      · rwa [min_eq_left hle] at e
      · rw [min_eq_right hle] at e; exact absurd e hlt.ne'
    · intro hle
      rw [min_eq_right hle] at e
      rcases le_total (P a) c with hle' | hle'
      · rw [min_eq_left hle'] at e; exact e ▸ le_rfl
      · exact hle'
  · exact ⟨fun hlt ↦ min_eq_left hlt.le, fun hle ↦ (min_eq_right hle).symm.le⟩

/-- **Rank agreement of the spliced state** with a dense rank vector `b` below `kc`, when the
ambient's state separates `b` below `kc` at the cap `c`: below `c` exactly at the ranks below `kc`,
ordered as `b` there, `⊥` exactly at rank `0`.  Below `c` the spliced state is the ambient's
state, and at or above `c` it stays there (`Label.rankAgree_of_separates`). -/
theorem rankAgree_splicedState {j k : ℕ}
    {q : (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) → Label.{u}} {c : Label.{u}}
    (hc0 : c ≠ ⊥) {P : Fin (I.attachment g).card → Label.{u}}
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
      min (P a) c = min (ambientState H Γ A B' q a) c)
    {b : Fin (I.attachment g).card → ℕ} {kc : ℕ}
    (hdense : ∀ i, 0 < i → ∀ d, i ≤ b d → ∃ e, b e = i)
    (hlow : ∀ a, b a < kc → ambientState H Γ A B' q a < c)
    (hhigh : ∀ a, kc ≤ b a → c ≤ ambientState H Γ A B' q a)
    (hord : ∀ a₁ a₂, b a₁ < kc → b a₂ < kc →
      (ambientState H Γ A B' q a₁ ≤ ambientState H Γ A B' q a₂ ↔ b a₁ ≤ b a₂))
    (hbot : ∀ a, ambientState H Γ A B' q a = ⊥ ↔ b a = 0) :
    RankAgree (rankVector (splicedState H Γ A B' k P q c)) b kc := by
  have hlow' (a) (ha : b a < kc) : splicedState H Γ A B' k P q c a = ambientState H Γ A B' q a :=
    (splicedState_cases hPq a).1 (hlow a ha)
  refine rankAgree_of_separates hdense (fun a ha ↦ (hlow' a ha).symm ▸ hlow a ha)
    (fun a ha ↦ (splicedState_cases hPq a).2 (hhigh a ha))
    (fun a₁ a₂ h₁ h₂ ↦ by rw [hlow' a₁ h₁, hlow' a₂ h₂]; exact hord a₁ a₂ h₁ h₂)
    fun a ↦ ?_
  rcases lt_or_ge (b a) kc with ha | ha
  · rw [hlow' a ha]; exact hbot a
  · have h1 := (splicedState_cases hPq a).2 (hhigh a ha)
    have h2 : b a ≠ 0 := fun h0 ↦ by
      have := hhigh a ha
      rw [(hbot a).mpr h0, le_bot_iff] at this
      exact hc0 this
    exact ⟨fun h0 ↦ absurd (le_bot_iff.mp (h0 ▸ h1)) hc0, fun h0 ↦ absurd h0 h2⟩

/-- **A tie of the ambient's state breaks the rank agreement of the spliced state**: two cells
below `c` with one value of the ambient's state and distinct ranks of `b` below `kc`. -/
theorem not_rankAgree_splicedState {j k : ℕ}
    {q : (𝔼).toCellScheme.below ((univ : Finset (Fin (m + 2))), j) → Label.{u}} {c : Label.{u}}
    {P : Fin (I.attachment g).card → Label.{u}}
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
      min (P a) c = min (ambientState H Γ A B' q a) c)
    {b : Fin (I.attachment g).card → ℕ} {kc : ℕ} {a₁ a₂ : Fin (I.attachment g).card}
    (hlt : ambientState H Γ A B' q a₁ < c)
    (htie : ambientState H Γ A B' q a₁ = ambientState H Γ A B' q a₂) (hb : b a₁ ≠ b a₂)
    (h₁ : b a₁ < kc) (h₂ : b a₂ < kc) :
    ¬ RankAgree (rankVector (splicedState H Γ A B' k P q c)) b kc :=
  not_rankAgree_of_tie (by
    rw [(splicedState_cases hPq a₁).1 hlt, (splicedState_cases hPq a₂).1 (htie ▸ hlt), htie]) hb
    h₁ h₂

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The spliced state is admitted.**  At a threshold `N ≤ k` the requests read only cells of
grade at most `k`, where the spliced state is the admitted prescription; at `k < N ≤ j` the cap
value is at most `c` and the reads are those of the admitted ambient capped at `c`
(`Seed.ambientAdmitted`, `StageType.GrowthRequests.CorrectAt.of_min`); above `j` the cap value
is `⊥`. -/
theorem attachAdmits_splicedState (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hte : StageType.restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hn : 0 < n)
    (hd : StageType.restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : StageType.GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {j k : ℕ}
    {q : (Seed.replicated I g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (hq : (Seed.replicated I g H Γ (I.attachAdmits g hd Q) B').rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), j) q) {c : Label.{u}} (hc : IsSelfVisible j c)
    (hc0 : c ≠ ⊥) {P : Fin (I.attachment g).card → Label.{u}}
    (hPA : I.attachAdmits g hd Q (m + 2) P)
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
      min (P a) c = min (ambientState H Γ (I.attachAdmits g hd Q) B' q a) c) (K : ℕ) :
    I.attachAdmits g hd Q K (splicedState H Γ (I.attachAdmits g hd Q) B' k P q c) := by
  classical
  set P' := splicedState H Γ (I.attachAdmits g hd Q) B' k P q c with hP'def
  set amb := ambientState H Γ (I.attachAdmits g hd Q) B' q with hamb
  refine attachAdmits_of_admitsOnClass hd hQ K fun hcls hcap y ↦ ?_
  have hthr : Q.threshold ≤ m + 2 := (I.left.grade_le Q.cap).trans (Nat.le_succ _)
  have hdg (y : Fin d.card) : (I.attachment g).toCellScheme.grade (I.attachDonCell g hd y) ≤
      Q.threshold :=
    (Scheme.grade_faceCell (StageType.comap_toScheme_of_restrictFace
      (I.restrictFace_donor_attachmentType g hd)) y).le.trans ((d.grade_le y).trans hQ.arity)
  have hcg (x : Fin I.left.card) (hx : I.left.toCellScheme.grade x ≤ Q.threshold) :
      (I.attachment g).toCellScheme.grade (I.attachCtxCell g x) ≤ Q.threshold := by
    rw [grade_attachCtxCell]; exact hx
  -- the spliced state agrees with the ambient's state capped at `c` everywhere
  have hagr (a : Fin (I.attachment g).card) : min (P' a) c = min (amb a) c := by
    rw [hP'def]
    unfold splicedState
    split_ifs with h
    · exact hPq a h
    · rw [min_assoc, min_self]
  rcases le_or_gt Q.threshold k with hNk | hNk
  · -- the requests read the prescription
    have hhat (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a ≤
        Q.threshold) : I.attachHatAt g Q.threshold P a = P' a := by
      unfold attachHatAt
      rw [ite_eq_left ha, hP'def]
      unfold splicedState
      rw [ite_eq_left (ha.trans hNk)]
    have h := hPA hthr (fun x hx ↦ by beta_reduce; rw [hhat _ (hcg x hx.2)]; exact hcls x hx)
      (by beta_reduce; rw [hhat _ (hcg _ le_rfl)]; exact hcap) y
    beta_reduce at h
    rw [hhat _ (hdg y)] at h
    exact h.congr (hhat _ (hcg _ le_rfl)) (fun hy ↦ hhat _ (hcg _ (hQ.ref y hy).1))
      (hhat _ (hcg _ hQ.marker.1))
  -- the cap cell is capped at `c`
  have hcapk : ¬ (I.attachment g).toCellScheme.grade (I.attachCtxCell g Q.cap) ≤ k := by
    rw [grade_attachCtxCell]; exact not_le.mpr hNk
  have hcapv : P' (I.attachCtxCell g Q.cap) = min (amb (I.attachCtxCell g Q.cap)) c := by
    rw [hP'def]; unfold splicedState; rw [ite_eq_right hcapk]
  rcases le_or_gt Q.threshold j with hNj | hNj
  swap
  · exfalso
    apply hcap
    beta_reduce
    rw [hcapv, hamb]
    erw [ambientState_of_lt _ (by rw [grade_attachCtxCell]; exact hNj)]
    exact min_bot_left c
  have hbot (a : Fin (I.attachment g).card) : P' a = ⊥ ↔ amb a = ⊥ := by
    have h := hagr a
    constructor
    · intro h0
      rw [h0, min_bot_left] at h
      exact (min_eq_bot.mp h.symm).resolve_right hc0
    · intro h0
      rw [h0, min_bot_left] at h
      exact (min_eq_bot.mp h).resolve_right hc0
  have hambA := ambientAdmitted hH hcard hΓ0 hd hQ hn j hNj q hq
    (fun x hx ↦ (hbot _).symm.trans (hcls x hx)) (fun h0 ↦ hcap ((hbot _).mpr h0)) y
  have hcN : IsSelfVisible Q.threshold c := hc.mono hNj
  have hmap := hambA.map (θ := fun x ↦ min x c) (fun _ _ h ↦ min_le_min_right c h)
    (min_bot_left c) (fun i hi x ↦ (visibilityReplace_min_of_isSelfVisible hi hcN x).symm)
    (fun hj ↦ (hQ.ref y hj).2.1) hQ.marker.2.1
  have hmap' : Q.CorrectAt (fun x ↦ min (P' (I.attachCtxCell g x)) c) y
      (min (P' (I.attachDonCell g hd y)) c) := by
    have e1 : (fun x ↦ min (P' (I.attachCtxCell g x)) c) =
        (fun x ↦ min x c) ∘ fun x ↦ amb (I.attachCtxCell g x) := funext fun x ↦ hagr _
    rw [e1, hagr]
    exact hmap
  exact hmap'.of_min (by rw [hcapv]; exact min_le_right _ _) hcN (fun hj ↦ (hQ.ref y hj).2.1)
    hQ.marker.2.1

/-- **The code of the spliced state**: for requests calibrated on the class over a nonempty root,
values containing the code set, an ambient lawful below `(univ, j)`, a cap `c ≠ ⊥` self-visible at
`j`, a lawful admitted prescription `P` with the observation of the ambient at `c` up to the grade
`k ≤ m + 1`, and a label `x` self-visible at `k`: a state `R` of the catalogue at `k` and a witness
bounded by `k` reading `R` as `P` capped at `x` at the cells of grade at most `k`; when the
ambient's state separates a dense rank vector `b` below `kc` at `c`, the rank vector of `R` agrees
with `b` below `kc`. -/
theorem exists_splicedCode (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    (hte : StageType.restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hn : 0 < n)
    (hd : StageType.restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : StageType.GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte) {j k : ℕ}
    (hkm : k ≤ m + 1)
    {q : (Seed.replicated I g H Γ (I.attachAdmits g hd Q) B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (hq : (Seed.replicated I g H Γ (I.attachAdmits g hd Q) B').rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), j) q) {c : Label.{u}} (hc : IsSelfVisible j c)
    (hc0 : c ≠ ⊥) {P : Fin (I.attachment g).card → Label.{u}}
    (hP : (I.attachment g).rows.IsLawful P) (hPA : I.attachAdmits g hd Q (m + 2) P)
    (hPq : ∀ a, (I.attachment g).toCellScheme.grade a ≤ k →
      min (P a) c = min (ambientState H Γ (I.attachAdmits g hd Q) B' q a) c)
    {x : Label.{u}} (hx : IsSelfVisible k x) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ (I.attachAdmits g hd Q) k,
      ∃ σ : Label.{u} → Label.{u}, IsWitness (stepSuppressor k) σ ∧
        (∀ a, (I.attachment g).toCellScheme.grade a ≤ k → σ (R a) = min (P a) x) ∧
        ∀ (b : Fin (I.attachment g).card → ℕ) (kc : ℕ),
          (∀ i, 0 < i → ∀ d, i ≤ b d → ∃ e, b e = i) →
          (∀ a, b a < kc → ambientState H Γ (I.attachAdmits g hd Q) B' q a < c) →
          (∀ a, kc ≤ b a → c ≤ ambientState H Γ (I.attachAdmits g hd Q) B' q a) →
          (∀ a₁ a₂, b a₁ < kc → b a₂ < kc →
            (ambientState H Γ (I.attachAdmits g hd Q) B' q a₁ ≤
              ambientState H Γ (I.attachAdmits g hd Q) B' q a₂ ↔ b a₁ ≤ b a₂)) →
          (∀ a, ambientState H Γ (I.attachAdmits g hd Q) B' q a = ⊥ ↔ b a = 0) →
          RankAgree (rankVector R) b kc := by
  set P' := splicedState H Γ (I.attachAdmits g hd Q) B' k P q c with hP'def
  have hP'l : (I.attachment g).rows.IsLawful P' := isLawful_splicedState hq hc hc0 hP hPq
  have hP'A : I.attachAdmits g hd Q (m + 2) P' :=
    attachAdmits_splicedState hH hcard hΓ0 hte hn hd hQ hq hc hc0 hPA hPq _
  obtain ⟨R, hR, σ, hσ, -, hσR, hrank⟩ := exists_stateCode_rankVector hd hQ hΓc hP'l hP'A
  obtain ⟨hRΓ, hRl, hRA⟩ := Scheme.LadderBaseData.mem_towerCat.mp hR
  refine ⟨R, Scheme.LadderBaseData.mem_towerCat.mpr ⟨hRΓ, hRl, fun hN ↦ hRA (by omega)⟩,
    fun y ↦ min (σ y) x, (hσ k (by omega)).min_const hx, fun a ha ↦ ?_,
    fun b kc hdense hlow hhigh hord hbot ↦ ?_⟩
  · change min (σ (R a)) x = _
    rw [hσR a, hP'def]
    unfold splicedState
    rw [ite_eq_left ha]
  · have e : rankVector R = rankVector P' := funext hrank
    rw [e]
    exact rankAgree_splicedState hc0 hPq hdense hlow hhigh hord hbot

end Seed

end VaughtConjecture
