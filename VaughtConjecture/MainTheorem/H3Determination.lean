/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.RootBottomRoute
import VaughtConjecture.Continuation.ReadingLayerDetermination
import VaughtConjecture.Extension.AdmittedTower
import VaughtConjecture.Extension.CapRequestsGrade
import VaughtConjecture.Extension.CapRequestsFill

/-!
# Hollow coatom cutoff determination at contexts respecting the root bottoms (work file)

Work file for `h3`: `HollowCoatomCutoffDetermination MarkedCapContextBelow'`.

* `H3.requests`: the cap requests of an input (cap and marker of the context, the new tops of the
  donor read from below).
* `H3.isDeterminedWithin_of_hasAdmittedRows`: a completion of the seed of the context and the
  coatom coface whose rows from the grade of the cap are correct determines the donor at a
  permitted cutoff (recognition at the cell reached by availability from the cap).
* `H3.exists_correctCompletion`: SCAFFOLD (`sorry`): such a completion exists.
* `H3.hollowCoatomCutoffDetermination`, `H3.receivingHollowReceiving`: the assembly.
-/

universe u w

namespace VaughtConjecture

open Finset Label StageType

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- A lawful labelling of the completion is lawful on the old cells of the completed scheme. -/
theorem isLawful_comp_castSucc_completion {a' : Fin (F.completion hα).card → Label.{u}}
    (ha' : (F.completion hα).rows.IsLawful a') : F.scheme.rows.IsLawful fun d ↦ a' d.castSucc := by
  have h₀ : ((F.truncate hα).toScheme.appendFullCell (m + 2)
      (StageType.apexRow (t := F.truncate hα) F.isLegalBelowFullGrade)
      F.isLegalBelowFullGrade.not_le).rows.IsLawful a' := ha'
  have h₁ := h₀.comap (Scheme.isLowerEmbedding_castSucc (m + 2)
    (StageType.apexRow (t := F.truncate hα) F.isLegalBelowFullGrade)
    F.isLegalBelowFullGrade.not_le)
  rw [Scheme.comap_rows_castSucc (S := (F.truncate hα).toScheme)
    (h := F.isLegalBelowFullGrade.not_le)] at h₁
  exact h₁

end CompletionBelowFullGrade

namespace CapRequests

open ProfileTower CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

/-- **The donor raise at `⊥`** at the grade `k`: every labelling `f` lawful below the private
coatom at `k`, with the cap of grade at most `k` and not `⊥`, agrees on the common face below `k`
with some labelling lawful below the donor coatom at `k` that is at least the marker value of `f`
at every cell of `T`. -/
def DonorRaiseBotAt (r : CapRequests (Fin I.amalgam.card)) (xp xd : Fin (m + 2)) (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
    I.amalgam.toCellScheme.grade r.cap ≤ k → f r.cap ≠ ⊥ →
    ∃ v : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ v d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k),
        d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) → v d = f d) ∧
      ∀ y ∈ r.T, r.markerValue f ≤ v y

/-- **The fill at `⊥` from the donor raise**: the prescription on the private coatom, the donor
raise elsewhere; lawful on both coatoms (they agree on the common face), correct (the cells of `T`
are off the private coatom and read at least the marker value). -/
theorem capFillBotAt_of_donorRaiseBotAt (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {k : ℕ} (hk : 0 < k)
    (hkm : k ≤ m + 1) (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : r.Z = ∅) (hF : r.F = ∅) (hraise : DonorRaiseBotAt r xp xd k) :
    CapFillBotAt r xp k := by
  classical
  intro f hf
  by_cases hck : I.amalgam.toCellScheme.grade r.cap ≤ k ∧ f r.cap ≠ ⊥
  swap
  · obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk hkm hxp (isSelfVisible_bot k)
      (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
      fun _ _ ↦ by simp
    refine ⟨W, hW, hWf, isCorrect_of_cap_eq_bot ?_⟩
    by_cases hg : I.amalgam.toCellScheme.grade r.cap ≤ k
    · rw [hat_of_le hg, hWf _ ⟨hcapC, hg⟩]
      exact not_not.mp fun h ↦ hck ⟨hg, h⟩
    · exact hat_of_lt (not_le.mp hg)
  obtain ⟨hg, hc⟩ := hck
  obtain ⟨v, hv, hvf, hvT⟩ := hraise f hf hg hc
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) then f d else v d with hW
  have hWf (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)) : W d = f d := by
    rw [hW]; simp only [hd, ite_true]
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr (w := f) (w' := W) fun d hd ↦ (hWf d hd).symm).mp hf
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d := by
    refine (Rows.isLawfulBelow_congr (w := v) (w' := W) fun d hd ↦ ?_).mp hv
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)
    · rw [hWf d hdC]
      exact hvf d hdC hd
    · rw [hW]; simp only [hdC, ite_false]
  have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hg
  refine ⟨W, lawful_pair hxp hxd hne.symm hWC hWD, hWf, ?_⟩
  refine isCorrect_of_forall (fun z hz ↦ by simp [hZ] at hz) (fun f' hf' ↦ by simp [hF] at hf')
    fun y hy ↦ ?_
  have hyg : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hg
  have hmv : r.markerValue (hat I k W) = r.markerValue f := by
    unfold markerValue
    rw [hat_of_le hmg, hat_of_le hg, hWf _ ⟨hmarkC, hmg⟩, hWf _ ⟨hcapC, hg⟩]
  rw [hmv, hat_of_le hyg]
  have hyW : W y = v y := by
    rw [hW]
    exact ite_eq_right fun h ↦ hT y hy h.1
  rw [hyW]
  exact hvT y hy

end CapRequests

namespace Realization

open StageType

/-- **Hollow coatom cutoff determination, existential form**: over every legal `t'` on `k + 1`
points with `P t' (g.trans Fin.castSuccEmb)` and face `p` along `Fin.castSuccEmb`, every coface `d`
of the root face has some coface `tb` of `p` with face `d` along `extendByLast g`, and some coface
`D'` of `t'` with face `tb`, determining `d` at a permitted cutoff.  The donor coface `tb` is
chosen with the carrier, before any member of the family. -/
structure HollowCoatomCutoffDeterminationExists
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop) : Prop where
  /-- Every coface of the root face is determined through some coface of the coatom face. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α (k + 1))
    (g : Fin n ↪ Fin k) (p : StageType.{u} α k) :
    Order.IsSuccLimit α → t'.IsLegal → P t' (g.trans Fin.castSuccEmb) →
      restrictFace Fin.castSuccEmb t' = some p → ∀ t : StageType.{u} α n,
        restrictFace (g.trans Fin.castSuccEmb) t' = some t → ∀ d ∈ t.cofaces,
          ∃ tb ∈ p.cofaces, restrictFace (extendByLast g) tb = some d ∧
            ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
              ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
                IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **Hollow cutoff determination from its existential coatom form**, under the hypotheses of
`HollowCoatomCutoffDetermination.hollowCutoffDetermination` on the predicate (the relabelling
putting the root in the first coatom). -/
theorem HollowCoatomCutoffDeterminationExists.hollowCutoffDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hdet : HollowCoatomCutoffDeterminationExists.{u} P)
    (hns : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
      P t' h → ¬ Function.Surjective h)
    (hinv : ∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
      (σ : Equiv.Perm (Fin k)), P t' h → P (t'.reindex σ) (h.trans σ.symm.toEmbedding)) :
    HollowCutoffDetermination.{u} P where
  exists_coface α n k t' h hα ht' hP t ht d hd := by
    have hs := hns t' h hP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      obtain ⟨x, -⟩ : ∃ x, x ∉ Set.range h := by
        by_contra! hall
        exact hs hall
      exact ⟨k - 1, by have := x.2; omega⟩
    obtain ⟨σ, g, p, rfl, hp⟩ := exists_perm_root_eq ht hs
    have hroot : ((g.trans Fin.castSuccEmb).trans σ.toEmbedding).trans σ.symm.toEmbedding =
        g.trans Fin.castSuccEmb :=
      Function.Embedding.ext fun i ↦ by simp
    have hP' := hinv t' _ σ hP
    rw [hroot] at hP'
    have ht'' : restrictFace (g.trans Fin.castSuccEmb) (t'.reindex σ) = some t := by
      rw [restrictFace_reindex]
      exact ht
    obtain ⟨-, -, -, D'', hD'', -, δ, hδ, hdet''⟩ :=
      hdet.exists_coface (t'.reindex σ) g p hα (ht'.reindex σ) hP' hp t ht'' d hd
    exact ⟨_, reindex_extendPerm_symm_mem_cofaces hD'', δ, hδ, hdet''.reindex_extendPerm⟩

end Realization

namespace H3

variable {α : Ordinal.{u}} {n k : ℕ}

/-- The seed of the context `t'` and the coface `tb` of its face `p`. -/
noncomputable abbrev seed {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
    {tb : StageType.{u} α (k + 1)} (ht' : t'.IsLegal)
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces) : Seed.{u} α k :=
  Seed.ofCoatoms ht' htb.1 hp htb.2

section Requests

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}

theorem restrictFace_left_seed :
    restrictFace Fin.castSuccEmb (seed ht' hp htb).amalgam = some t' :=
  (seed ht' hp htb).restrictFace_left

theorem restrictFace_donor_seed (hd : restrictFace (extendByLast g) tb = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (seed ht' hp htb).amalgam = some d := by
  rw [← extendByLast_trans, ← restrictFace_trans _ _ _ (seed ht' hp htb).restrictFace_right]
  exact hd

/-- **The cap requests of an input**: the cap `c` of the context (threshold its grade), marker
offset `0` and marker `r`, and the new tops of the donor (cells labelled `⊤` with the new point in
their scope) read from below. -/
noncomputable def requests (hd : restrictFace (extendByLast g) tb = some d) (c r : Fin t'.card)
    (hc : 0 < t'.toCellScheme.grade c) : CapRequests (Fin (seed ht' hp htb).amalgam.card) where
  cap := faceCell (restrictFace_left_seed ht' hp htb) c
  N := t'.toCellScheme.grade c
  R := 0
  R_lt_N := hc
  Z := ∅
  F := ∅
  T := {y | ∃ j, d.label j = ⊤ ∧ Fin.last n ∈ d.toCellScheme.scope j ∧
    y = faceCell (restrictFace_donor_seed ht' hp htb hd) j}
  ref := id
  off := fun _ ↦ 0
  marker := faceCell (restrictFace_left_seed ht' hp htb) r

/-- **The requests are graded** when the marker lies below the cap and the donor's cells lie below
the grade of the cap. -/
theorem isGraded_requests (hd : restrictFace (extendByLast g) tb = some d) {c r : Fin t'.card}
    (hc : 0 < t'.toCellScheme.grade c)
    (hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c)
    (hn : n + 1 < t'.toCellScheme.grade c) :
    (requests ht' hp htb hd c r hc).IsGraded (seed ht' hp htb).amalgam.toCellScheme.grade where
  le_grade_cap := (grade_faceCell (restrictFace_left_seed ht' hp htb) c).ge
  off_le _ h := absurd h (Set.notMem_empty _)
  grade_le_of_mem_Z _ h := absurd h (Set.notMem_empty _)
  grade_le_of_mem_F _ h := absurd h (Set.notMem_empty _)
  grade_le_of_mem_T y hy := by
    obtain ⟨j, -, -, rfl⟩ := hy
    change (seed ht' hp htb).amalgam.toCellScheme.grade
        (faceCell (restrictFace_donor_seed ht' hp htb hd) j) ≤
      (seed ht' hp htb).amalgam.toCellScheme.grade
        (faceCell (restrictFace_left_seed ht' hp htb) c)
    rw [grade_faceCell, grade_faceCell]
    exact (d.grade_le j).trans hn.le
  grade_ref_le _ h := absurd h (Set.notMem_empty _)
  grade_marker_le := by
    change (seed ht' hp htb).amalgam.toCellScheme.grade
        (faceCell (restrictFace_left_seed ht' hp htb) r) ≤
      (seed ht' hp htb).amalgam.toCellScheme.grade
        (faceCell (restrictFace_left_seed ht' hp htb) c)
    rw [grade_faceCell, grade_faceCell]
    exact hrc

end Requests

/-! ### Determination from a completion with correct rows -/

section Determination

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}

/-- **Determination from a completion with correct rows.**  Let `c` be a top cap of `t'` with
marker `r`, of grade `N > n + 1`, and `F` a completion of the seed of `t'` and `tb` whose rows of
full scope from the grade `N` are correct for the requests.  Then the completion determines the
donor over `t'` along `g` followed by the first points, at a permitted cutoff: in a member literal
on `t'` the cap is `⊤`, availability gives a cell of graded index `(univ, N)` labelled `⊤`, and
recognition there gives a correct state with cap and marker `⊤`, `⊤` at the new tops. -/
theorem isDeterminedWithin_of_hasAdmittedRows (hα : Order.IsSuccLimit α)
    (hd : restrictFace (extendByLast g) tb = some d) {c r : Fin t'.card}
    (hc : t'.IsTopCap c) (hr : t'.IsMarker c r) (hn : n + 1 < t'.toCellScheme.grade c)
    (F : CompletionBelowFullGrade (seed ht' hp htb))
    (hF : F.HasAdmittedRows (t'.toCellScheme.grade c)
      (requests ht' hp htb hd c r (by omega)).IsCorrect) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily (F.completion hα.isSuccPrelimit) δ) t'
        (g.trans Fin.castSuccEmb) d := by
  have hα' := hα.isSuccPrelimit
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hr.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hmap : (seed ht' hp htb).IsTransformClosed
      (requests ht' hp htb hd c r (by omega)).IsCorrect := fun _ _ _ hs hw ↦ hs.map hgr hw
  have h₁ : restrictFace Fin.castSuccEmb (F.completion hα') = some t' :=
    F.restrictFace_left_completion hα'
  have hR : restrictFace (extendByLast Fin.castSuccEmb) (F.completion hα') = some tb :=
    F.restrictFace_right_completion hα'
  have h₂ : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (F.completion hα') =
      some d := by
    rw [← extendByLast_trans, ← restrictFace_trans _ _ _ hR]
    exact hd
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hnk : n ≤ k := by simpa using Fintype.card_le_of_embedding g
  have hf₂ : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ≠ univ := fun he ↦ by
    have := congrArg Finset.card he
    rw [card_map, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at this
    omega
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα (F.completion hα')
  refine ⟨δ, hδ, (isDeterminedWithin_receivingFamily_iff h₂ hδD).mpr ?_⟩
  rintro ⟨S, ℓ, hw, hcod, hl, hat⟩ hq hq₁ i j hij hj
  obtain ⟨hS, -⟩ := hq
  change S = (F.completion hα').toScheme at hS
  subst hS
  obtain rfl : i = faceCell h₂ j := Fin.ext hij
  have hold (z : Fin t'.card) : ℓ (faceCell h₁ z) = t'.label z := label_faceCell hq₁ z
  by_cases hjl : Fin.last n ∈ d.toCellScheme.scope j
  · -- a new top: recognition at a cell of `(univ, N)` labelled `⊤`
    have hcap : ℓ (faceCell h₁ c) = ⊤ := (hold c).trans hc.2.1
    have hmark : ℓ (faceCell h₁ r) = ⊤ := (hold r).trans hr.1
    rw [F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL c] at hcap
    rw [F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL r] at hmark
    have hcg : (F.completion hα').toCellScheme.grade (faceCell h₁ c) = t'.toCellScheme.grade c :=
      grade_faceCell h₁ c
    have hN0 : 0 < t'.toCellScheme.grade c := by omega
    have hNk : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
    obtain ⟨u₀, hu₀⟩ := (F.isLegal_completion hα').isComplete
      ((univ : Finset (Fin (k + 2))), t'.toCellScheme.grade c)
      ⟨(F.completion hα').univ_mem_faces, hN0, by simp; omega⟩
    obtain ⟨u, hu, hcu⟩ := hl.availability (faceCell h₁ c) u₀
      (by rw [show (F.completion hα').toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
          exact subset_univ _)
      (hcg.trans (congrArg Prod.snd hu₀).symm)
    have hℓu : ℓ u = ⊤ := by
      have h' : ℓ (faceCell h₁ c) ≤ ℓ u := hcu
      rw [hold, hc.2.1] at h'
      exact top_le_iff.mp h'
    obtain ⟨w, rfl, hw'⟩ := F.exists_castSucc_of_gradedIndex_completion hα' (by omega)
      (hu.trans hu₀)
    -- the labelling read on the scheme below the full grade
    have hq' := (F.isLawful_comp_castSucc_completion hα' hl).isLawfulBelow
      ((univ : Finset (Fin (k + 2))), t'.toCellScheme.grade c)
    have hrec := CompletionBelowFullGrade.adm_of_isLawfulBelow hmap hF le_rfl
      (q := fun z ↦ ℓ (Fin.castSucc z)) hq' hw'
    simp only [hℓu, min_top_right] at hrec
    have hcapN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) ≤
        t'.toCellScheme.grade c := (grade_faceCell hL c).le
    have hmarkN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL r) ≤
        t'.toCellScheme.grade c := (grade_faceCell hL r).trans_le hrc
    have hyT : faceCell hA j ∈ (requests ht' hp htb hd c r (by omega)).T := ⟨j, hj, hjl, rfl⟩
    have htop := hrec.eq_top_of_mem_T hyT
      (by change ProfileTower.hat (seed ht' hp htb) _ _ (faceCell hL c) = ⊤
          rw [ProfileTower.hat_of_le hcapN]; exact hcap)
      (by change ProfileTower.hat (seed ht' hp htb) _ _ (faceCell hL r) = ⊤
          rw [ProfileTower.hat_of_le hmarkN]; exact hmark)
    have hyN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hA j) ≤
        t'.toCellScheme.grade c := by
      rw [grade_faceCell]
      exact (d.grade_le j).trans hn.le
    rw [ProfileTower.hat_of_le hyN] at htop
    change ℓ (faceCell h₂ j) = ⊤
    rw [F.faceCell_completion hα' hf₂ h₂ hA j]
    exact htop
  · -- an old cell: visible through the first points, literal on `t'`
    have hvis : faceCell h₂ j ∈ (F.completion hα').visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      intro y hy
      rw [scope_faceCell] at hy
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
      induction x using Fin.lastCases with
      | last => exact absurd hx hjl
      | cast x => exact ⟨Fin.castSucc (g x), by simp⟩
    obtain ⟨z, hz⟩ := exists_faceCell_eq h₁ hvis
    change ℓ (faceCell h₂ j) = ⊤
    rw [← hz, hold]
    have h1 := label_faceCell h₁ z
    have h2 := label_faceCell h₂ j
    rw [hz] at h1
    rw [← h1, h2]
    exact hj

end Determination

/-! ### The completion with correct rows -/

section Completion

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d)

/-- **The correct completion from the engine** (`Seed.exists_correctCompletion_T`): with `k ≥ 2`,
the grade `N` of the cap at least `3`, the common face carrying no cell of grade at least `N`, and
the fills (a dead common face, or the donor following the root with the fill at the positive
caps), the seed has a completion whose rows of full scope from `N` are correct. -/
theorem exists_correctCompletion_of {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) (hk : 2 ≤ k)
    (hN3 : 3 ≤ t'.toCellScheme.grade c)
    (hface : ∀ e, (seed ht' hp htb).amalgam.toCellScheme.scope e ⊆
        univ.erase (Fin.last (k + 1)) ∩ univ.erase (Fin.castSucc (Fin.last k)) →
      (seed ht' hp htb).amalgam.toCellScheme.grade e < t'.toCellScheme.grade c)
    (hfill : CapRequests.IsDeadFace (seed ht' hp htb) (Fin.last (k + 1))
        (Fin.castSucc (Fin.last k)) ∨
      ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        CapRequests.DonorFollowsRoot (requests ht' hp htb hd c r (by omega)) (Fin.last (k + 1))
          (Fin.castSucc (Fin.last k)) k' ∧
        CapRequests.CapFillPosAt (requests ht' hp htb hd c r (by omega)) (Fin.last (k + 1)) k') :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        (requests ht' hp htb hd c r (by omega)).IsCorrect := by
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hcapg : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) =
      t'.toCellScheme.grade c := grade_faceCell hL c
  have hcapC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) =
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, hctx.1.1]
    exact Coatom.univ_map_left
  have h := (seed ht' hp htb).exists_correctCompletion_T hk (r := requests ht' hp htb hd c r
    (by omega)) hgr (xp := Fin.last (k + 1)) (xd := Fin.castSucc (Fin.last k)) (by simp)
    (by simp) Seed.last_ne_castSucc.symm hcapC (hcapg ▸ hN3)
    (fun x hx hxe e he ↦ by
      have hx' : x = Fin.castSucc (Fin.last k) := by
        simp only [ProfileTower.Pts, mem_insert, mem_singleton] at hx
        exact hx.resolve_left hxe
      subst hx'
      exact (hface e he).trans_eq hcapg.symm)
    (fun y hy ↦ by
      obtain ⟨j, hj, hjl, rfl⟩ := hy
      refine ⟨(label_faceCell hA j).trans hj, fun hsub ↦ ?_, ?_⟩
      · have hmem : Fin.last (k + 1) ∈
            (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hA j) := by
          rw [scope_faceCell]
          exact mem_map.mpr ⟨Fin.last n, hjl, by simp⟩
        simpa using hsub hmem
      · change (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hA j) <
          (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c)
        rw [grade_faceCell, grade_faceCell]
        exact (d.grade_le j).trans_lt hn)
    (fun z hz ↦ absurd hz (Set.notMem_empty _)) rfl
    (hfill.imp id fun hf k' hk' hkm ↦ hf k' (hcapg ▸ hk') hkm)
  have hcapg' : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap = t'.toCellScheme.grade c := hcapg
  rwa [hcapg'] at h

/-- **The correct completion from the donor raise** (`Seed.exists_correctCompletion` with
`CapRequests.capFillBotAt_of_donorRaiseBotAt`): with `k ≥ 2`, the grade `N` of the cap at least
`3`, the common face carrying no cell of grade at least `N`, the donor raise at `⊥` and the fill at
the positive caps from the private coatom at every grade `N ≤ k' ≤ k + 1`. -/
theorem exists_correctCompletion_of_raise {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r) (hk : 2 ≤ k)
    (hN3 : 3 ≤ t'.toCellScheme.grade c)
    (hface : ∀ e, (seed ht' hp htb).amalgam.toCellScheme.scope e ⊆
        univ.erase (Fin.last (k + 1)) ∩ univ.erase (Fin.castSucc (Fin.last k)) →
      (seed ht' hp htb).amalgam.toCellScheme.grade e < t'.toCellScheme.grade c)
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAt (requests ht' hp htb hd c r (by omega)) (Fin.last (k + 1))
        (Fin.castSucc (Fin.last k)) k')
    (hpos : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.CapFillPosAt (requests ht' hp htb hd c r (by omega)) (Fin.last (k + 1)) k') :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        (requests ht' hp htb hd c r (by omega)).IsCorrect := by
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hcapg : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) =
      t'.toCellScheme.grade c := grade_faceCell hL c
  have hcapg' : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap = t'.toCellScheme.grade c := hcapg
  have hcapC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) =
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, hctx.1.1]
    exact Coatom.univ_map_left
  have hmarkC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL r) ⊆
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, ← Coatom.univ_map_left]
    exact map_subset_map.mpr (subset_univ _)
  have hTlab (y) (hy : y ∈ (requests ht' hp htb hd c r (by omega)).T) :
      (seed ht' hp htb).amalgam.label y = ⊤ ∧
        ¬ (seed ht' hp htb).amalgam.toCellScheme.scope y ⊆ univ.erase (Fin.last (k + 1)) := by
    obtain ⟨j, hj, hjl, rfl⟩ := hy
    refine ⟨(label_faceCell hA j).trans hj, fun hsub ↦ ?_⟩
    have hmem : Fin.last (k + 1) ∈
        (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hA j) := by
      rw [scope_faceCell]
      exact mem_map.mpr ⟨Fin.last n, hjl, by simp⟩
    simpa using hsub hmem
  have hglued : (requests ht' hp htb hd c r (by omega)).IsCorrect
      fun e ↦ (seed ht' hp htb).amalgam.label e :=
    CapRequests.isCorrect_of_forall (fun z hz ↦ absurd hz (Set.notMem_empty _))
      (fun f hf ↦ absurd hf (Set.notMem_empty _))
      fun y hy ↦ by rw [(hTlab y hy).1]; exact le_top
  have hlab := (hglued.code hgr (k + 1)).hat hgr (k + 1)
  have h := (seed ht' hp htb).exists_correctCompletion hk hgr (xp := Fin.last (k + 1)) (by simp)
    hcapC (by rw [hcapg']; exact hN3)
    (fun x hx hxe e he ↦ by
      have hx' : x = Fin.castSucc (Fin.last k) := by
        simp only [ProfileTower.Pts, mem_insert, mem_singleton] at hx
        exact hx.resolve_left hxe
      subst hx'
      exact (hface e he).trans_eq hcapg.symm)
    (fun k' hk' hkm ↦ CapRequests.capFillBotAt_of_donorRaiseBotAt hgr (by omega) (by simp)
      (by simp) Seed.last_ne_castSucc.symm (by rw [hcapg'] at hk'; omega) hkm hcapC.le hmarkC
      (fun y hy ↦ (hTlab y hy).2) rfl rfl (hraise k' (hcapg' ▸ hk') hkm))
    (fun k' hk' hkm ↦ hpos k' (hcapg' ▸ hk') hkm) hlab
  rwa [hcapg'] at h

end Completion

/-! ### The open inputs (SCAFFOLD) -/

set_option warningAsError false in
/-- **SCAFFOLD (`sorry`)**: at an acquired context, the seed of the context and the coatom coface
has a completion whose rows of full scope from the grade of the cap are correct.  Reduced by
`H3.exists_correctCompletion_of` to: `k ≥ 2` and `N ≥ 3` (the small cases), the common face
carrying no cell of grade at least `N` (`hface`), and the fills. -/
theorem exists_correctCompletion (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)} (ht' : t'.IsLegal)
    (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces) {g : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c) :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        (requests ht' hp htb hd c r (by have := hctx.2.2.1; omega)).IsCorrect := by
  by_cases hsmall : 2 ≤ k ∧ 3 ≤ t'.toCellScheme.grade c
  · refine exists_correctCompletion_of_raise ht' hp htb hd hctx hsmall.1 hsmall.2 ?_ ?_ ?_
    · -- `hface`: the common face carries no cell of grade at least the grade of the cap
      -- (to be replaced by the donor provisions without `hface`, from the h4 lane)
      sorry
    · -- the donor raise at `⊥` (the fill at `⊥` from the private coatom)
      sorry
    · -- the fill at the positive caps from the private coatom
      sorry
  · -- the small cases: `k ≤ 1` or the cap of grade `2`
    sorry

/-! ### Assembly -/

/-- **The existential coatom form at the contexts respecting the root bottoms** (through the
SCAFFOLD `H3.exists_correctCompletion`; the donor coface is, for now, the pinned extension). -/
theorem hollowCoatomCutoffDeterminationExists :
    Realization.HollowCoatomCutoffDeterminationExists.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) where
  exists_coface α n k t' g p hα ht' hP hp t ht d hd := by
    obtain ⟨c, r, hctx, hoff, hbot⟩ := hP
    obtain ⟨tb, htb, htbd⟩ := Realization.exists_mem_cofaces_restrictFace_eq hα ht' hp ht hd
    obtain ⟨F, hF⟩ := exists_correctCompletion hα ht' hp htb htbd hctx hoff hbot
    obtain ⟨δ, hδ, hdet⟩ := isDeterminedWithin_of_hasAdmittedRows ht' hp htb hα htbd hctx.1
      hctx.2.1 hctx.2.2.1 F hF
    exact ⟨tb, htb, htbd, F.completion hα.isSuccPrelimit,
      ⟨F.isLegal_completion _, F.restrictFace_left_completion _⟩,
      F.restrictFace_right_completion _, δ, hδ, hdet⟩

/-- **The coatom form** (through the SCAFFOLD; every donor coface). -/
theorem hollowCoatomCutoffDetermination :
    Realization.HollowCoatomCutoffDetermination.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) where
  exists_coface α n k t' g p hα ht' hP hp tb htb d hd := by
    obtain ⟨c, r, hctx, hoff, hbot⟩ := hP
    obtain ⟨F, hF⟩ := exists_correctCompletion hα ht' hp htb hd hctx hoff hbot
    obtain ⟨δ, hδ, hdet⟩ := isDeterminedWithin_of_hasAdmittedRows ht' hp htb hα hd hctx.1
      hctx.2.1 hctx.2.2.1 F hF
    exact ⟨F.completion hα.isSuccPrelimit,
      ⟨F.isLegal_completion _, F.restrictFace_left_completion _⟩,
      F.restrictFace_right_completion _, δ, hδ, hdet⟩

/-- **(R3) for receiving models** through the existential coatom form (SCAFFOLD). -/
theorem receivingHollowReceiving :
    Realization.HollowReceiving.{u, w} Realization.IsReceivingCoverHollowAtBlock :=
  Realization.receivingHollowReceiving_of_markedCapContextBelow'
    (hollowCoatomCutoffDeterminationExists.hollowCutoffDetermination
      (Realization.markedCapContextBelow'_routeInputs.{u, w}).2.1
      (Realization.markedCapContextBelow'_routeInputs.{u, w}).2.2)

end H3

end VaughtConjecture
