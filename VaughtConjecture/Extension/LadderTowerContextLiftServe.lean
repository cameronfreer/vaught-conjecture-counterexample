/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftCap
import VaughtConjecture.Extension.ReplicatedRankAgreement

/-!
# The extension over the tower at a positive cap, from a serving code

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

At a positive cap `c` that the state `P` exceeds, the extension over the tower
(`Seed.TowerExtensionPos`) is the decoded writing `σ ∘ replicatedWriting R` of a **serving code**:
a catalogue state `R` and a witness `σ` reading `R` as `P` below the grade, whose decoded writing
has the observation of the ambient `q` at `c` on the ladder and on the layers
(`Seed.HasServingCode`, `Seed.towerExtensionPos_of_serve`).

* **The ladder** (`Seed.exists_ladder_shape`): on the ladder a section lawful below `(univ, j)`
  is `⊥`, or the table `F` of one member `b` read at the indices of `b`
  (`Scheme.exists_render_of_isLawful` on the padded base).  The bottom case does not occur when
  the state exceeds a positive cap: the ambient is then positive at a cell of the attachment, hence
  at a rung (`Seed.exists_copiedTopRung_ne_bot`).  In the table case the decoded writing reads the
  rungs through the member `a` of `R` (`Seed.replicatedWriting_ladder`), and the indices of `a` and
  `b` agree capped at the cut of their rank vectors (`ladderIndex_agree`); so **rank agreement of
  `a` and `b` up to the cap rank of `F`** (`Seed.capRank`: the first index where `F` reaches `c`),
  with the tables agreeing capped at `c`, gives the observation of the ambient on the ladder
  (`Seed.min_eq_min_of_cut`).
* **The layers**: the observation of the ambient at the cells of full scope of grades `2, …, j` is
  asked of the serving code directly (the agreement heights of the writing of `R` with the
  catalogue states read through `σ`).
* **The copies** read their originals (`Seed.exists_orig_mem_below_univ`).
* **Lawfulness**: at a positive cap the ambient is a lawful companion
  (`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`).

**Serving at the top grade** (`Seed.towerExtensionPos_of_serveTop`): the serving code is asked at
the largest grade `K` where the state exceeds the cap, with a decoder bounded by `K`; above `K` the
state is at most the cap and the ambient capped at the cap is spliced on
(`CellScheme.Rows.IsLawfulBelow.splice`).  Rank agreement then pins the state only at `K`
(`Seed.isSelfVisible_of_serving_twin`): two cells of one rank in `b` below the cap rank, one of
grade at least `K`, ask the value at the other to be self-visible at `K`, not at the grade of the
first
(the obstruction `Seed.not_exists_coded_rankAgree` is for a code reading a lawful state at every
cell, which the serving code is not asked to be).

The serving code is an explicit hypothesis here; it is not proved.

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

/-! ### The cap rank and the arithmetic on the ladder -/

open Classical in
/-- The **cap rank** of a table `F` at a cap `c`: the first index at most `H` where `F` reaches
`c`, and `H` if there is none. -/
noncomputable def capRank (H : ℕ) (F : ℕ → Label.{u}) (c : Label.{u}) : ℕ :=
  if h : ∃ i, i ≤ H ∧ c ≤ F i then Nat.find h else H

theorem capRank_le (H : ℕ) (F : ℕ → Label.{u}) (c : Label.{u}) : capRank H F c ≤ H := by
  classical
  unfold capRank
  split_ifs with h
  · exact (Nat.find_spec h).1.trans' (Nat.find_min' h (Nat.find_spec h))
  · exact le_rfl

/-- **Two indices agreeing capped at a cut above the cap rank are read alike capped at the cap**,
by two monotone tables agreeing capped at the cap up to `H`. -/
theorem min_eq_min_of_cut {H : ℕ} {F G : ℕ → Label.{u}} (hF : Monotone F) (hG : Monotone G)
    {c : Label.{u}} (htab : ∀ i ≤ H, min (G i) c = min (F i) c) {cut x y : ℕ}
    (hk : capRank H F c ≤ cut) (hx : x ≤ H) (hy : y ≤ H) (hxy : min x cut = min y cut) :
    min (G x) c = min (F y) c := by
  classical
  by_cases he : x = y
  · subst he; exact htab x hx
  have hcx : cut ≤ x ∧ cut ≤ y := by
    constructor
    · by_contra h
      push Not at h
      rw [min_eq_left h.le] at hxy
      rcases le_total y cut with h' | h'
      · rw [min_eq_left h'] at hxy; exact he hxy
      · rw [min_eq_right h'] at hxy; omega
    · by_contra h
      push Not at h
      rw [min_eq_left h.le] at hxy
      rcases le_total x cut with h' | h'
      · rw [min_eq_left h'] at hxy; exact he hxy
      · rw [min_eq_right h'] at hxy; omega
  unfold capRank at hk
  split_ifs at hk with h
  · have hkx : Nat.find h ≤ x := hk.trans hcx.1
    have hky : Nat.find h ≤ y := hk.trans hcx.2
    have hcF : c ≤ F (Nat.find h) := (Nat.find_spec h).2
    have hcG : c ≤ G (Nat.find h) := by
      have := htab _ (Nat.find_spec h).1
      rw [min_eq_right hcF] at this
      exact this.symm.le.trans (min_le_left _ _)
    rw [min_eq_right ((hcG.trans (hG hkx))), min_eq_right (hcF.trans (hF hky))]
  · omega

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

/-- The ladder index of a member at a ladder point. -/
noncomputable abbrev ladIdx
    (a : Scheme.RankMember (I.attachmentBase g).S H)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    ℕ :=
  ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
    (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H)) a p

/-! ### The shape of a section on the ladder -/

/-- **The shape of a section lawful below `(univ, j)` on the ladder**: `⊥` at every ladder point
and every cell of grade one of the attachment, or the table of one member read at its indices. -/
theorem exists_ladder_shape (hH : 0 < H) {j : ℕ} (hj : 1 ≤ j)
    {q : Fin (I.replicated g H Γ A B').card → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ q d) :
    ((∀ p, q (Fin.castAdd _ (ladCell H Γ A B' p)) = ⊥) ∧
      ∀ a, (I.attachment g).toCellScheme.grade a = 1 → q (I.attachEmb g H Γ A B' a) = ⊥) ∨
    ∃ (b : Scheme.RankMember (I.attachmentBase g).S H) (F : ℕ → Label.{u}), Monotone F ∧
      F 0 = ⊥ ∧ (∀ i, IsSelfVisible 1 (F i)) ∧ (∀ i, 0 < i → i ≤ H → F i ≠ ⊥) ∧
      ∀ p, q (Fin.castAdd _ (ladCell H Γ A B' p)) = F (ladIdx b p) := by
  classical
  have hT := isLawfulBelow_castAdd_replicated hq
  have hφ := Scheme.isLowerEmbedding_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') m
  have hsc := fun t ↦ Scheme.scope_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') t m
  have hB := Rows.IsLawfulBelow.comap_of_scope_eq hφ hsc hT
  rw [Scheme.comap_rows_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') m] at hB
  set v : Fin ((I.attachmentBase g).ladderBase H).card → Label.{u} := fun t ↦
    q (Fin.castAdd _ ((I.attachmentBase g).towerEmb (H := H) (Γ := Γ) (A := A) (B' := B') m t))
    with hv
  have hB1 : ((I.attachmentBase g).ladderBase H).rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), 1) fun t ↦ v t :=
    hB.mono (show (((univ : Finset (Fin (m + 2))), 1) : Finset (Fin (m + 2)) × ℕ) ≤
      ((univ : Finset (Fin (m + 2))), j) from ⟨subset_rfl, hj⟩)
  have hsp := Scheme.isLawful_splice_bot (S := (I.attachmentBase g).ladderBase H) (k := 1) hB1
  have hgsp (t) (ht : ((I.attachmentBase g).ladderBase H).toCellScheme.grade t = 1) :
      ((I.attachmentBase g).ladderBase H).toCellScheme.splice 1 (fun _ ↦ ⊥) v t = v t :=
    CellScheme.splice_of_le ht.le
  rcases Scheme.exists_render_of_isLawful (I.attachmentBase g).wf hH
      (Scheme.rankProf_le _ H) hsp with hzero | ⟨b, F, hF, hF0, hFv, hFp, hFv0⟩
  · left
    refine ⟨fun p ↦ ?_, fun a ha ↦ ?_⟩
    · have hg : ((I.attachmentBase g).ladderBase H).toCellScheme.grade
          (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p)) = 1 :=
        Scheme.appendFullCellsScheme_grade_natAdd _ _ _ _
      have := hzero _ hg
      rw [hgsp _ hg] at this
      exact this
    · have hg : ((I.attachmentBase g).ladderBase H).toCellScheme.grade (Fin.castAdd _ a) = 1 :=
        (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans ha
      have := hzero _ hg
      rw [hgsp _ hg] at this
      exact this
  · right
    refine ⟨b, F, hF, hF0, hFv, hFp, fun p ↦ ?_⟩
    have hg : ((I.attachmentBase g).ladderBase H).toCellScheme.grade
        (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p)) = 1 :=
      Scheme.appendFullCellsScheme_grade_natAdd _ _ _ _
    have := hFv0 _ hg
    rw [hgsp _ hg, Scheme.baseIndex_natAdd, Equiv.symm_apply_apply] at this
    exact this

/-! ### The serving code -/

variable (I g H Γ A B') in
/-- **A serving code at the grade `j`** (hypothesis): at every positive cap `c` self-visible at
`j`, for every ambient `q` lawful below `(univ, j)` whose ladder is the table `F` of a member `b`,
and every lawful state `P` satisfying `A (m + 2)`, with the observation of `q` at `c` on the cells
of the attachment below the grade and exceeding `c` at one of them: a catalogue state `R` and a
witness `σ` bounded by `j` such that

* `σ` reads `R` as `P` at the cells of the attachment below the grade;
* the rank member of `R` agrees with `b` up to the cap rank of `F` at `c`;
* `σ` reads the positive table of `R` as `F` capped at `c`, up to `H`;
* the decoded writing of `R` has the observation of `q` at `c` at every cell of full scope of the
  tower of grade `2, …, j` (the agreement heights on the layers). -/
def HasServingCode (hcard : (I.attachmentBase g).S.card ≤ H) (j : ℕ) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible j c → c ≠ ⊥ →
    ∀ q : Fin (I.replicated g H Γ A B').card → Label.{u},
      (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
        (fun d ↦ q d) →
      ∀ P : Fin (I.attachment g).card → Label.{u}, (I.attachment g).rows.IsLawful P →
      A (m + 2) P →
      (∀ a, (I.attachment g).toCellScheme.grade a ≤ j →
        min (P a) c = min (q (I.attachEmb g H Γ A B' a)) c) →
      (∃ a, (I.attachment g).toCellScheme.grade a ≤ j ∧ ¬ P a ≤ c) →
      ∀ (b : Scheme.RankMember (I.attachmentBase g).S H) (F : ℕ → Label.{u}), Monotone F →
        F 0 = ⊥ → (∀ i, IsSelfVisible 1 (F i)) → (∀ i, 0 < i → i ≤ H → F i ≠ ⊥) →
        (∀ p, q (Fin.castAdd _ (ladCell H Γ A B' p)) = F (ladIdx b p)) →
        ∃ R ∈ (I.attachmentBase g).towerCat Γ A (m + 2),
          ∃ hR : (I.attachment g).rows.IsLawful R, ∃ σ : Label.{u} → Label.{u},
            IsWitness (stepSuppressor j) σ ∧
            (∀ a, (I.attachment g).toCellScheme.grade a ≤ j → σ (R a) = P a) ∧
            RankAgree (Scheme.rankProf (I.attachmentBase g).S H
                (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
              (Scheme.rankProf (I.attachmentBase g).S H b) (capRank H F c) ∧
            (∀ i ≤ H, min (σ (posTable R i)) c = min (F i) c) ∧
            ∀ (t : Fin (I.attachTower g H Γ A B').card) (k : ℕ), 2 ≤ k → k ≤ j →
              (I.attachTower g H Γ A B').toCellScheme.gradedIndex t =
                ((univ : Finset (Fin (m + 2))), k) →
              min (σ (I.replicatedWriting g H Γ A B' R (Fin.castAdd _ t))) c =
                min (q (Fin.castAdd _ t)) c

/-- **The extension over the tower at a positive cap from a serving code**: the decoded writing of
the serving code is lawful (the ambient is a lawful companion at the positive cap), reads the
state on the attachment, and keeps the observation of the ambient at the cap on the attachment,
the ladder (rank agreement through `ladderIndex_agree`), the layers and the copies. -/
theorem towerExtensionPos_of_serve (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty) {j : ℕ}
    (hj1 : 1 ≤ j) (hjm : j ≤ m + 1) (hS : HasServingCode I g H Γ A B' hcard j) :
    TowerExtensionPos I g H Γ A B' j := by
  classical
  intro c hc hc0 q hq P hP hPA hPq hhigh
  let qt : Fin (I.replicated g H Γ A B').card → Label.{u} := CellScheme.Rows.extendBot _ q
  have hqtd (d : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j)) : qt d = q d :=
    CellScheme.Rows.extendBot_of_mem q d.2
  have hqt : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ qt d :=
    CellScheme.Rows.isLawfulBelow_extendBot.mpr hq
  have hPq' (a : Fin (I.attachment g).card) (ha : (I.attachment g).toCellScheme.grade a ≤ j) :
      min (P a) c = min (qt (I.attachEmb g H Γ A B' a)) c := by
    rw [hPq ⟨_, attachEmb_mem_below_univ a ha⟩ a rfl,
      ← hqtd ⟨_, attachEmb_mem_below_univ a ha⟩]
  obtain ⟨a0, ha0j, ha0⟩ := hhigh
  have hq0 : qt (I.attachEmb g H Γ A B' a0) ≠ ⊥ := by
    have h1 := hPq' a0 ha0j
    rw [min_eq_right (le_of_lt (not_le.mp ha0))] at h1
    intro h0
    rw [h0, min_eq_left bot_le] at h1
    exact hc0 h1
  rcases exists_ladder_shape hH (by omega) hqt with ⟨hz1, hz2⟩ |
    ⟨b, F, hF, hF0, hFv, hFp, hshape⟩
  · exfalso
    have hg1 := (I.isWellFormed_attachment g).isWellFormed.grade_pos a0
    rcases Nat.lt_or_ge ((I.attachment g).toCellScheme.grade a0) 2 with hlt | hge
    · exact hq0 (hz2 a0 (by omega))
    · obtain ⟨R, -, hR, htop, -⟩ := exists_copiedTopRung_ne_bot hH hcard hne hge ha0j
        (ha0j.trans hjm) hqt rfl hq0
      exact htop (hz1 _)
  obtain ⟨R, hRC, hR, σ, hσ, hσR, hrank, htab, hlay⟩ :=
    hS c hc hc0 qt hqt P hP hPA hPq' ⟨a0, ha0j, ha0⟩ b F hF hF0 hFv hFp hshape
  -- the observation at the cells of the tower
  have hcapT (t : Fin (I.attachTower g H Γ A B').card)
      (ht : (Fin.castAdd _ t : Fin (I.replicated g H Γ A B').card) ∈
        (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) :
      min (σ (I.replicatedWriting g H Γ A B' R (Fin.castAdd _ t))) c =
        min (qt (Fin.castAdd _ t)) c := by
    have hgi : (I.replicated g H Γ A B').toCellScheme.gradedIndex (Fin.castAdd _ t) =
        (I.attachTower g H Γ A B').toCellScheme.gradedIndex t := gradedIndex_replicated_castAdd t
    by_cases hs : (I.attachTower g H Γ A B').toCellScheme.scope t = univ
    · set k := (I.attachTower g H Γ A B').toCellScheme.grade t with hk
      have hgt : (I.attachTower g H Γ A B').toCellScheme.gradedIndex t =
          ((univ : Finset (Fin (m + 2))), k) := Prod.ext hs rfl
      have hkj : k ≤ j := by
        have := ht.2
        rw [hgi, hgt] at this
        exact this
      have hk1 : 1 ≤ k :=
        ((isWellFormed_replicated (I := I) (g := g) (H := H) (Γ := Γ) (A := A)
          (B' := B')).isWellFormed.grade_pos (Fin.castAdd _ t)).trans_eq
          (congrArg Prod.snd (hgi.trans hgt))
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain ⟨v, hv⟩ := exists_eq_castAdd_ladCell
          (Fin.castAdd _ t : Fin (I.replicated g H Γ A B').card)
          (hgi.trans (hgt.trans (by rw [show k = 1 by omega])))
        rw [hv, replicatedWriting_ladder hcard hR, hshape v]
        refine min_eq_min_of_cut (F := F) (G := fun i ↦ σ (posTable R i)) hF
          (fun i i' hii' ↦ hσ.monotone (monotone_posTable hii')) htab
          (le_rankCut (capRank_le H F c) hrank) (ladderIndex_le _ _) (ladderIndex_le _ _)
          (ladderIndex_agree _ _ _)
      · exact hlay t k hk2 hkj hgt
    · obtain ⟨a, rfl⟩ := (I.attachmentBase g).mem_range_baseCellEmb m t hs
      have ha : (I.attachment g).toCellScheme.grade a ≤ j :=
        ((attachEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') a
          ((univ : Finset (Fin (m + 2))), j)).mp ht).2
      change min (σ (I.replicatedWriting g H Γ A B' R (I.attachEmb g H Γ A B' a))) c =
        min (qt (I.attachEmb g H Γ A B' a)) c
      refine (congrArg (fun z ↦ min (σ z) c) (replicatedWriting_attachEmb (Γ := Γ) (A := A)
        (B' := B') hcard hR a)).trans ?_
      rw [hσR a ha]
      exact hPq' a ha
  -- the observation at every cell, the copies through their originals
  have hcap (d : (I.replicated g H Γ A B').toCellScheme.below ((univ : Finset (Fin (m + 2))), j)) :
      min (σ (I.replicatedWriting g H Γ A B' R d)) c = min (q d) c := by
    obtain ⟨hmem, hsc⟩ := exists_orig_mem_below_univ d.2
    have hqd : qt d = qt (Fin.castAdd _
        ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) d)) :=
      Scheme.eq_of_mirrorOrig_eq hqt (Scheme.mirrorOrig_castAdd _ _ _).symm hsc hmem
    have hwd : I.replicatedWriting g H Γ A B' R d =
        I.replicatedWriting g H Γ A B' R (Fin.castAdd _
          ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) d)) := by
      change ((I.attachmentBase g).ladderTower H Γ A B' m).v R _ =
        ((I.attachmentBase g).ladderTower H Γ A B' m).v R _
      rw [Scheme.mirrorOrig_castAdd]
    rw [← hqtd, hwd, hqd]
    exact hcapT _ hmem
  refine ⟨fun d ↦ σ (I.replicatedWriting g H Γ A B' R d),
    ((isLawful_replicatedWriting hH hcard hΓ hA hRC).isLawfulBelow _).map_of_min_eq hq
      (fun d ↦ d.2.2) hσ hc0 hcap, fun d a ha ↦ ?_, hcap⟩
  have hag : (I.attachment g).toCellScheme.grade a ≤ j :=
    ((attachEmb_mem_below_iff (H := H) (Γ := Γ) (A := A) (B' := B') a
      ((univ : Finset (Fin (m + 2))), j)).mp (ha ▸ d.2)).2
  change σ (I.replicatedWriting g H Γ A B' R d.1) = P a
  rw [← ha, replicatedWriting_attachEmb hcard hR, hσR a hag]

/-! ### Serving at the top grade where the state exceeds the cap -/

/-- **The extension over the tower at a positive cap from serving codes at the top grade where
the state exceeds the cap**: let `K` be the largest grade of a cell of the attachment where the
state exceeds the cap.  The serving code at `K` extends the state below `(univ, K)`
(`Seed.towerExtensionPos_of_serve`); above `K` the state is at most the cap, and the ambient capped
at the cap is spliced on (`CellScheme.Rows.IsLawfulBelow.splice`).  The decoder of the serving
code is bounded by `K`, not by the grade of the extension. -/
theorem towerExtensionPos_of_serveTop (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B') (hA : ∀ k R, A (k + 3) R → A (k + 2) R)
    (hne : ∀ k, ((I.attachmentBase g).towerCat Γ A (k + 2)).Nonempty) {j : ℕ}
    (hjm : j ≤ m + 1)
    (hS : ∀ k, 1 ≤ k → k ≤ j → HasServingCode I g H Γ A B' hcard k) :
    TowerExtensionPos I g H Γ A B' j := by
  classical
  intro c hc hc0 q hq P hP hPA hPq hhigh
  have hex : ∃ k, ∀ a, (I.attachment g).toCellScheme.grade a ≤ j →
      k < (I.attachment g).toCellScheme.grade a → P a ≤ c :=
    ⟨j, fun a h1 h2 ↦ absurd h1 (not_le.mpr h2)⟩
  have hKspec := Nat.find_spec hex
  have hKj : Nat.find hex ≤ j := Nat.find_min' hex fun a h1 h2 ↦ absurd h1 (not_le.mpr h2)
  set K := Nat.find hex with hKdef
  obtain ⟨a0, ha0j, ha0⟩ := hhigh
  have ha0K : (I.attachment g).toCellScheme.grade a0 ≤ K := by
    by_contra h
    exact ha0 (hKspec a0 ha0j (not_le.mp h))
  have hK1 : 1 ≤ K := ((I.isWellFormed_attachment g).isWellFormed.grade_pos a0).trans_le ha0K
  have hKY : (((univ : Finset (Fin (m + 2))), K) : Finset (Fin (m + 2)) × ℕ) ≤
      ((univ : Finset (Fin (m + 2))), j) := ⟨subset_rfl, hKj⟩
  -- the serving code below `(univ, K)`
  obtain ⟨v, hv, hvP, hvc⟩ := towerExtensionPos_of_serve hH hcard hΓ hA hne hK1
    (hKj.trans hjm) (hS K hK1 hKj) c (hc.mono hKj) hc0
    (fun d ↦ q (Set.inclusion (CellScheme.below_mono _ hKY) d)) (hq.mono hKY) P hP hPA
    (fun d a ha ↦ hPq _ a ha) ⟨a0, ha0K, ha0⟩
  -- the splice with the ambient capped above `K`
  set qt : Fin (I.replicated g H Γ A B').card → Label.{u} := CellScheme.Rows.extendBot _ q
  set vt : Fin (I.replicated g H Γ A B').card → Label.{u} := CellScheme.Rows.extendBot _ v
  have hqtd (d) (hd : d ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j)) : qt d = q ⟨d, hd⟩ :=
    CellScheme.Rows.extendBot_of_mem q hd
  have hvtd (d) (hd : d ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), K)) : vt d = v ⟨d, hd⟩ :=
    CellScheme.Rows.extendBot_of_mem v hd
  have hup : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j)
      fun d ↦ min (qt d) c :=
    (CellScheme.Rows.isLawfulBelow_extendBot.mpr hq).min_const_of_isSelfVisible hc
  have hvt : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), K)
      fun d ↦ vt d := CellScheme.Rows.isLawfulBelow_extendBot.mpr hv
  have hag (d) (hd : d ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), K)) : min (vt d) c = min (min (qt d) c) c := by
    rw [hvtd d hd, hvc ⟨d, hd⟩, min_assoc, min_self, hqtd d (CellScheme.below_mono _ hKY hd)]
  have hsp := CellScheme.Rows.IsLawfulBelow.splice hup hvt (fun _ _ _ ↦ min_le_right _ _) hag
  refine ⟨fun d ↦ (I.replicated g H Γ A B').toCellScheme.splice K (fun d ↦ min (qt d) c) vt d,
    hsp, fun d a ha ↦ ?_, fun d ↦ ?_⟩
  · have hga : (I.replicated g H Γ A B').toCellScheme.grade d.1 =
        (I.attachment g).toCellScheme.grade a := by
      rw [← ha]; exact congrArg Prod.snd (gradedIndex_attachEmb a)
    have haj : (I.attachment g).toCellScheme.grade a ≤ j := hga ▸ d.2.2
    by_cases hk : (I.attachment g).toCellScheme.grade a ≤ K
    · have hdK : d.1 ∈ (I.replicated g H Γ A B').toCellScheme.below
          ((univ : Finset (Fin (m + 2))), K) := ⟨subset_univ _, (hga.trans_le hk :)⟩
      change (I.replicated g H Γ A B').toCellScheme.splice K _ vt d.1 = P a
      rw [CellScheme.splice_of_le (hga ▸ hk), hvtd _ hdK]
      exact hvP ⟨d.1, hdK⟩ a ha
    · change (I.replicated g H Γ A B').toCellScheme.splice K _ vt d.1 = P a
      rw [CellScheme.splice_of_lt (hga ▸ not_le.mp hk), hqtd _ d.2, ← hPq d a ha,
        min_eq_left (hKspec a haj (not_le.mp hk))]
  · change min ((I.replicated g H Γ A B').toCellScheme.splice K (fun d ↦ min (qt d) c) vt d.1)
      c = min (q d) c
    rw [CellScheme.min_splice_eq hag (subset_univ _), min_assoc, min_self, hqtd _ d.2]

variable {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The context lift of the replicated scheme from serving codes at the grades `1, …, m + 1`**,
for a set of values containing `⊥` and the code set of the attachment
(`Seed.hasContextLift_attachAdmits_pos`, `Seed.towerExtensionPos_of_serveTop`). -/
theorem hasContextLift_attachAdmits_serve (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hΓ0 : ⊥ ∈ Γ) (hΓ : ∀ x ∈ Γ, x ≤ gridPoint 2 B')
    (hΓc : codeSet (I.attachment g).card (m + 2) ⊆ Γ)
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb))))
    (hS : ∀ k, 1 ≤ k → k ≤ m + 1 →
      HasServingCode I g H Γ (I.attachAdmits g hd Q) B' hcard k) :
    I.HasContextLift g H Γ (I.attachAdmits g hd Q) B' :=
  hasContextLift_attachAdmits_pos hH hcard hΓ0 hΓ hΓc hte hdp hdL hn hd hQ hpair hrel hrF hr1
    fun _ _ hjm ↦ towerExtensionPos_of_serveTop hH hcard hΓ
      (fun k R h ↦ I.attachAdmits_succ g hd Q k R h)
      (fun _ ↦ ⟨fun _ ↦ ⊥, Scheme.LadderBaseData.mem_towerCat.mpr
        ⟨fun _ ↦ hΓ0, Rows.isLawful_const_bot, I.attachAdmits_bot g hd Q _⟩⟩)
      hjm fun k hk1 hkj ↦ hS k hk1 (hkj.trans hjm)

/-! ### The pin of the serving code -/

/-- **The serving code pins only at its grade**: if the rank vector of the lawful state `R`
agrees with `b` below `k`, and two cells `d₁`, `d₂` have the same rank in `b` below `k`, with `d₂`
of grade at least `K`, then a witness bounded by `K` reads `R d₁` as a label self-visible at `K`.
The serving code at the top grade `K` where the state exceeds the cap thus asks the state at `d₁`
to be self-visible at `K` only, not at the grade of `d₂` (compare
`Seed.not_exists_coded_rankAgree`, where the code reads a lawful state at every cell). -/
theorem isSelfVisible_of_serving_twin {R : Fin (I.attachment g).card → Label.{u}}
    (hR : (I.attachment g).rows.IsLawful R) {σ : Label.{u} → Label.{u}} {K : ℕ}
    (hσ : IsWitness (stepSuppressor K) σ) {b : Fin (I.attachment g).card → ℕ} {k : ℕ}
    (hag : RankAgree (rankVector R) b k) {d₁ d₂ : Fin (I.attachment g).card}
    (hb : b d₁ = b d₂) (hk : b d₂ < k) (hd₂ : K ≤ (I.attachment g).toCellScheme.grade d₂) :
    IsSelfVisible K (σ (R d₁)) := by
  have h1 := rankVector_eq_of_rankAgree hag (hb ▸ hk)
  have h2 := rankVector_eq_of_rankAgree hag hk
  have he : R d₁ = R d₂ := eq_of_rankVector_eq (h1.trans (hb.trans h2.symm))
  rw [he]
  exact hσ.isSelfVisible_apply ((hR.orderly d₂).mono hd₂) (by simp)

end Seed

end VaughtConjecture
