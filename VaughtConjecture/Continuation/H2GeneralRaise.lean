/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2General

/-!
# h2 at every arity: donor raising on the grade-`K` faces

Roadmap, Layer 3 ((R2) of the table of 3.4: coatom cutoff determination at source-gap contexts,
`Realization.CoatomCutoffDetermination`, written **h2** in the names of this family of modules).
Every declaration is proved, with no hypothesis beyond the designation.

**Donor raising with the gap on the grade-`K` faces** (`H2.donorRaisingAt`, the input
`H2.DonorRaisingAt` at every arity), generalizing `H2.donorRaisingGap_oneFace` (two points, grade
`1`) and `H2.donorRaising_two_of_root` (two points, grade `2`):
* the capped lift from the root (`H2.hasCappedLifts_lawfulAt`): bountifulness of the donor from
  the root face at the grade `min k K` to `(univ, K)`, the root cells of grade above `K` being `⊥`
  on both faces;
* witnesses bounded by `K` above the identity keep the grade-`K` faces (`H2.lawfulAt_map`);
* every cell of the donor is low, designated, a root cell, or determined by the root on the
  grade-`K` faces (`H2.RootDetAt`; cells of grade above `K` are `⊥` there);
* the band raise (`H2.donorRaisingGap_of_cappedLift`), with the low cells unfiltered, and then
  filtered at the grades at most `K` (the cells above are `⊥`: `H2.donorRaisingGap_congr_sup`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-- Donor raising with the gap passes between low sets with the same maxima on the served faces. -/
theorem donorRaisingGap_congr_sup {ιC ιD ιR : Type*} {rc : ιR → ιC} {rd : ιR → ιD} {K : ℕ}
    {C : (ιC → Label.{u}) → Prop} {D : (ιD → Label.{u}) → Prop} {A : Set ιR}
    {Lo Lo' Tops : Finset ιD} (hsup : ∀ W, D W → Lo.sup W = Lo'.sup W)
    (hDR : DonorRaisingGap rc rd K C D A Lo Tops) : DonorRaisingGap rc rd K C D A Lo' Tops := by
  intro h c hh hc R f hR hf hagr hA hgap
  obtain ⟨W, hW, hWr, hWR, hWt⟩ := hDR hh hc hR hf hagr hA fun t ht hlt ↦
    hgap t ht (by rwa [← hsup R hR])
  exact ⟨W, hW, hWr, hWR, fun t ht hRt ↦ by rw [← hsup W hW]; exact hWt t ht hRt⟩

/-- **Witnesses bounded by the grade `K` keep the grade-`K` faces.** -/
theorem lawfulAt_map {m K : ℕ} {t : StageType.{u} α m} {ν : Label.{u} → Label.{u}}
    (hν : IsWitness (stepSuppressor K) ν) (hle : ∀ x, x ≤ ν x) {W : Fin t.card → Label.{u}}
    (hW : LawfulAt t K W) : LawfulAt t K (fun d ↦ ν (W d)) := by
  refine ⟨?_, fun d hd ↦ (congrArg ν (hW.2 d hd)).trans hν.map_bot⟩
  exact hW.1.map_of_apply_eq_bot (fun d ↦ d.2.2) hν fun d h0 ↦ le_bot_iff.mp (h0 ▸ hle _)

/-- **The capped lift from the root into the grade-`K` faces** (bountifulness of the donor from
the root face at the grade `min k K`). -/
theorem hasCappedLifts_lawfulAt {k K : ℕ} (hk : 0 < k) (hK0 : 0 < K) (hKk : K ≤ k + 1)
    {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α (k + 1)}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p) :
    HasCappedLifts (StageType.faceCell hp) (StageType.faceCell htbp) K (LawfulAt t' K)
      (LawfulAt tb K) := by
  classical
  intro h hh R f hR hf hagr
  obtain ⟨f', hf', hf'f⟩ := exists_ext_bot_at hleg hK0 hKk hf
  have hy := StageType.isLawful_comp_faceCell hp hf'
  obtain ⟨hfm, -⟩ := (StageType.restrictFace_eq_some_iff (t := tb) (f := Fin.castSuccEmb)).mp htbp
  have he := StageType.comap_toScheme_of_restrictFace htbp
  have hinj : Function.Injective (StageType.faceCell htbp) := by
    intro i j hij
    have := (tb.toScheme.cellMap Fin.castSuccEmb).injective hij
    exact Fin.cast_injective _ this
  set j := min k K with hj
  have hj0 : 0 < j := lt_min hk hK0
  set x : Fin tb.card → Label.{u} := Function.extend (StageType.faceCell htbp)
    (fun i ↦ f' (StageType.faceCell hp i)) (fun _ ↦ ⊥)
  have hx (i : Fin p.card) : x (StageType.faceCell htbp i) = f' (StageType.faceCell hp i) :=
    hinj.extend_apply _ _ i
  have hpX : tb.rows.IsLawfulBelow
      (Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), j)) (fun d ↦ x d) := by
    refine (Scheme.isLawfulBelow_faceCell_iff he _ x).mp ?_
    convert hy.isLawfulBelow ((univ : Finset (Fin k)), j) using 2 with i
    exact hx i.1
  have hXY : Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), j) ≤
      ((univ : Finset (Fin (k + 1))), K) := ⟨subset_univ _, min_le_right _ _⟩
  have hX : Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), j) ∈
      tb.toCellScheme.gradedFaces := ⟨hfm, hj0, by simp [hj]⟩
  have hY : ((univ : Finset (Fin (k + 1))), K) ∈ tb.toCellScheme.gradedFaces :=
    ⟨tb.univ_mem_faces, hK0, by simpa using hKk⟩
  have hgr (i : Fin p.card) (hi : tb.toCellScheme.grade (StageType.faceCell htbp i) ≤ K) :
      tb.toCellScheme.grade (StageType.faceCell htbp i) ≤ j := by
    refine le_min ?_ hi
    rw [StageType.grade_faceCell]
    exact p.grade_le i
  have hlift := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (htbleg.isBountiful hX hY hXY) h hh (fun d ↦ x d) (fun d ↦ R d) hpX hR.1 (fun d ↦ ?_)
  rotate_left
  · have hvis : d.1 ∈ tb.toScheme.visibleCells Fin.castSuccEmb := by
      refine Scheme.mem_visibleCells.mpr fun y hy ↦ ?_
      have hy' : y ∈ (univ : Finset (Fin k)).map Fin.castSuccEmb := d.2.1 (mem_coe.mp hy)
      obtain ⟨i, -, hi⟩ := mem_map.mp hy'
      exact ⟨i, hi⟩
    obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hvis
    have hdg : tb.toCellScheme.grade d.1 ≤ K := d.2.2.trans (min_le_right _ _)
    change min (R d.1) h = min (x d.1) h
    rw [← hi] at hdg ⊢
    change min (R (StageType.faceCell htbp i)) h = min (x (StageType.faceCell htbp i)) h
    have hg' : tb.toCellScheme.grade (StageType.faceCell htbp i) ≤ K := hdg
    have hgi : t'.toCellScheme.grade (StageType.faceCell hp i) ≤ K := by
      rw [StageType.grade_faceCell]
      rw [StageType.grade_faceCell] at hg'
      exact hg'
    rw [hx, hf'f _ hgi]
    exact (hagr i).symm
  obtain ⟨q', hq', hq'R, hq'p⟩ := hlift
  refine ⟨fun d ↦ if hd : d ∈ tb.toCellScheme.below ((univ : Finset (Fin (k + 1))), K) then
    q' ⟨d, hd⟩ else ⊥, ⟨?_, fun d hd ↦ dite_eq_right fun h' ↦ hd h'.2⟩, fun i ↦ ?_, fun d ↦ ?_⟩
  · convert hq' using 1
    exact funext fun d ↦ dite_eq_left d.2
  · by_cases hiK : tb.toCellScheme.grade (StageType.faceCell htbp i) ≤ K
    · have hvX : StageType.faceCell htbp i ∈ tb.toCellScheme.below
          (Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), j)) :=
        (CellScheme.mem_below _).mpr
          ⟨show tb.toCellScheme.scope (StageType.faceCell htbp i) ⊆
              (univ : Finset (Fin k)).map Fin.castSuccEmb by
            rw [StageType.scope_faceCell]; exact map_subset_map.mpr (subset_univ _),
          hgr i hiK⟩
      have := hq'p ⟨_, hvX⟩
      refine (dite_eq_left (Set.inclusion (tb.toCellScheme.below_mono hXY) ⟨_, hvX⟩).2).trans ?_
      refine this.trans ((hx i).trans (hf'f _ ?_))
      rw [StageType.grade_faceCell] at hiK ⊢
      exact hiK
    · refine (dite_eq_right fun h' ↦ hiK h'.2).trans (hf.2 _ ?_).symm
      rw [StageType.grade_faceCell] at hiK ⊢
      exact hiK
  · by_cases hd : d ∈ tb.toCellScheme.below ((univ : Finset (Fin (k + 1))), K)
    · exact (congrArg (min · h) (dite_eq_left hd)).trans (hq'R ⟨d, hd⟩)
    · refine (congrArg (min · h) (dite_eq_right hd)).trans ?_
      rw [hR.2 d fun h' ↦ hd ⟨subset_univ _, h'⟩]

/-- A stage type on no points has no cells. -/
theorem isEmpty_card_zero (p : StageType.{u} α 0) : IsEmpty (Fin p.card) := by
  refine ⟨fun i ↦ ?_⟩
  have h1 := p.isWellFormed.isWellFormed.grade_pos i
  have h2 := p.grade_le i
  omega

/-- **The capped lift from the root into the grade-`K` faces** at every arity (no root cells on
`0` points). -/
theorem hasCappedLifts_lawfulAt' {k K : ℕ} (hK0 : 0 < K) (hKk : K ≤ k + 1)
    {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α (k + 1)}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p) :
    HasCappedLifts (StageType.faceCell hp) (StageType.faceCell htbp) K (LawfulAt t' K)
      (LawfulAt tb K) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := isEmpty_card_zero p
    intro h hh R f hR hf hagr
    exact ⟨R, hR, fun x ↦ isEmptyElim x, fun _ ↦ rfl⟩
  · exact hasCappedLifts_lawfulAt hk hK0 hKk hleg hp htbleg htbp

/-- **Donor raising with the gap on the grade-`K` faces** at a source-gap context on `k + 1`
points with the lost point last, at every arity (the input `H2.DonorRaisingAt`). -/
theorem donorRaisingAt (k : ℕ) : DonorRaisingAt.{u} k := by
  intro α K n t' hleg g o r hs p hp tb htbleg htbp Lo Tops hLo hTops
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hKk : K ≤ k + 1 := hs.grade_owner ▸ t'.grade_le o
  have he := StageType.comap_toScheme_of_restrictFace htbp
  -- every root cell is low or a root top
  have hroot (x : Fin p.card) : StageType.faceCell htbp x ∈ Lo ∨ x ∈ rootTops' hp := by
    by_cases hx : p.label x = ⊤
    · refine .inr ⟨hx, ?_⟩
      simp [StageType.scope_faceCell, Fin.ext_iff]
      omega
    · exact .inl (hLo _ (by rwa [StageType.label_faceCell]))
  have hcls : ∀ d, d ∈ Lo ∨ d ∈ Tops ∨ (∃ x, StageType.faceCell htbp x = d) ∨
      IsRootDet (StageType.faceCell htbp) (LawfulAt tb K) d := by
    intro d
    by_cases hdg : tb.toCellScheme.grade d ≤ K
    swap
    · exact .inr (.inr (.inr fun W W' hW hW' _ ↦ (hW.2 d hdg).trans (hW'.2 d hdg).symm))
    by_cases hdt : tb.label d = ⊤
    swap
    · exact .inl (hLo d hdt)
    by_cases hdv : d ∈ tb.toScheme.visibleCells Fin.castSuccEmb
    · obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hdv
      exact .inr (.inr (.inl ⟨i, hi⟩))
    by_cases hdr : RootDetAt tb K d
    · refine .inr (.inr (.inr fun W W' hW hW' hag ↦ hdr W W' hW hW' fun y hy ↦ ?_))
      obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq he hy
      exact hag i
    · exact .inr (.inl (hTops d hdt hdg hdv hdr))
  have hDR := @donorRaisingGap_of_cappedLift _ _ _ _ _ _ _ _ _ _ _
    (hasCappedLifts_lawfulAt' hK0 hKk hleg hp htbleg htbp)
    (fun hν hle _ hW ↦ lawfulAt_map hν hle hW) hroot hcls
  have hsup : ∀ W, LawfulAt tb K W →
      Lo.sup W = (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K).sup W := by
    intro W hW
    refine le_antisymm (Finset.sup_le fun d hd ↦ ?_) (Finset.sup_mono (filter_subset _ _))
    by_cases hdg : tb.toCellScheme.grade d ≤ K
    · exact Finset.le_sup (f := W) (mem_filter.mpr ⟨hd, hdg⟩)
    · rw [hW.2 d hdg]
      exact bot_le
  exact @donorRaisingGap_congr_sup _ _ _ _ _ _ _ _ _ _ _ _ hsup hDR

/-- **h2 with the lost point last at every arity from owner lowering and the engine** on the
grade-`K` faces (donor raising is `H2.donorRaisingAt`). -/
theorem coatomCutoffDeterminationLast_of_ownerLowering_engine (hOL : ∀ k, OwnerLoweringAt.{u} k)
    (hEN : ∀ k, AdmittedCompletionsAt.{u} k) : CoatomCutoffDeterminationLast.{u} :=
  coatomCutoffDeterminationLast_of_inputs donorRaisingAt hOL hEN

end VaughtConjecture.H2
