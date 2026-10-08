/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2Collapse
import VaughtConjecture.Continuation.H2Engine
import VaughtConjecture.Continuation.TwoCoatomLift

/-!
# h2 at two points: the assembly (work file)

WORK FILE (branch `research/work-h2`).  `H2.coatomCutoffDeterminationTwo` from two SCAFFOLD
statements (each with `sorry`): `H2.donorRaising_two_lostZero` (lost point `0`, root on no point)
and `H2.exists_completion_recProp_one` (top grade `1`).  Donor raising with the gap
`H2.donorRaising_two` is proved at lost point `1` from capped lifts and the band raise
(`H2.donorRaisingGap_of_cappedLift`), with every top cell not on the root and not determined by the
root designated.  The two-coatom lift `H2.hasTwoCoatomLift_two` is proved
(`Seed.hasTwoCoatomLift`).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-! ### The completion with the reading property -/

/-- The root cells of the coatom face carrying `⊤` and avoiding the lost point. -/
def rootTops {t' : StageType.{u} α 2} {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) (l : Fin 2) : Set (Fin p.card) :=
  {a | p.label a = ⊤ ∧ l ∉ t'.toCellScheme.scope (StageType.faceCell hp a)}

/-- **The state-level provisions at grade `2`**, from donor raising: the order law at the owner,
the frontier bound (`StageType.IsSourceGapContextAt.frontier_le`) and owner lowering
(`FieldAdmission.ownerLowering_of_isLegal`) come from the context. -/
theorem stateAdmission_two {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 2 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)}
    (hDR : DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) Lo Tops) :
    IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (SelfLowG o r 2 Lo Tops) := by
  refine selfLow_isStateAdmissionGap (rootTops hp l) (fun f hf ↦ ?_) (fun f hf a ha ↦ ?_) hDR
    (ownerLowering_of_isLegal hleg hp htbp hs.grade_owner Nat.one_pos (by omega) t'.grade_le)
  · have := hf.orderly o
    rwa [hs.grade_owner] at this
  · exact hs.frontier_le hf ((StageType.label_faceCell hp a).trans ha.1) ha.2

set_option warningAsError false in
/-- **SCAFFOLD (contains `sorry`): donor raising at lost point `0`.**  The root is then on no
point (`n = 0`: the lost point is not on the root), and the root cells labelled `⊤` with scope the
point `0` are not designated root tops, so the band raise need not fix them. -/
theorem donorRaising_two_lostZero {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 2 (g.trans Fin.castSuccEmb) 0 o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, tb.label x = ⊤ → x ∉ tb.toScheme.visibleCells Fin.castSuccEmb →
      ¬ RootDet tb x → x ∈ Tops) :
    DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp 0) Lo Tops := by
  sorry

/-- **Donor raising with the gap at two points** (`H2.DonorRaisingGap`): at lost point `1`, from
capped lifts into `tb` and the band raise (`H2.donorRaisingGap_of_cappedLift`), every top cell of
`tb` off the root and not determined by the root being designated; at lost point `0`,
`H2.donorRaising_two_lostZero`. -/
theorem donorRaising_two {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 2 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x, tb.label x = ⊤ → x ∉ tb.toScheme.visibleCells Fin.castSuccEmb →
      ¬ RootDet tb x → x ∈ Tops) :
    DonorRaisingGap (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) Lo Tops := by
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact donorRaising_two_lostZero hleg hs hp htbleg htbp hLo hTops
  have he := comap_toScheme_of_restrictFace htbp
  have hroot : ∀ x, StageType.faceCell htbp x ∈ Lo ∨ x ∈ rootTops hp 1 := by
    intro x
    by_cases hx : p.label x = ⊤
    · refine .inr ⟨hx, ?_⟩
      simp [StageType.scope_faceCell, Fin.ext_iff]
    · exact .inl (hLo _ (by rwa [StageType.label_faceCell]))
  have hcls : ∀ d, d ∈ Lo ∨ d ∈ Tops ∨ (∃ x, StageType.faceCell htbp x = d) ∨
      IsRootDet (StageType.faceCell htbp) tb.rows.IsLawful d := by
    intro d
    by_cases hdt : tb.label d = ⊤
    swap
    · exact .inl (hLo d hdt)
    by_cases hdv : d ∈ tb.toScheme.visibleCells Fin.castSuccEmb
    · obtain ⟨i, hi⟩ := Scheme.exists_faceCell_eq he hdv
      exact .inr (.inr (.inl ⟨i, hi⟩))
    by_cases hdr : RootDet tb d
    · refine .inr (.inr (.inr fun W W' hW hW' hag ↦ hdr W W' hW hW' fun y hy ↦ ?_))
      obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq he hy
      exact hag i
    · exact .inr (.inl (hTops d hdt hdv hdr))
  have hmap : ∀ {ν : Label.{u} → Label.{u}}, IsWitness (stepSuppressor 2) ν → (∀ x, x ≤ ν x) →
      ∀ {W : Fin tb.card → Label.{u}}, tb.rows.IsLawful W → tb.rows.IsLawful fun d ↦ ν (W d) :=
    fun hν hle _ hW ↦ hW.map_of_apply_eq_bot tb.grade_le hν fun d h0 ↦ le_bot_iff.mp (h0 ▸ hle _)
  exact @donorRaisingGap_of_cappedLift _ _ _ _ _ _ _ _ _ _ _
    (hasCappedLifts_of_isLegal hp htbleg htbp Nat.one_pos one_lt_two le_rfl tb.grade_le) hmap
    hroot hcls

/-- **The two-coatom lift** on the canonical lower layer of the seed of two legal stage types on
two points with one common face (`Seed.HasTwoCoatomLift`; every seed on three points has it,
`Seed.hasTwoCoatomLift`). -/
theorem hasTwoCoatomLift_two {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p) :
    (Seed.ofCoatoms hleg htbleg hp htbp).HasTwoCoatomLift :=
  Seed.hasTwoCoatomLift _

/-- **The admitted completion at two points and grade `2`**, from the state-level provisions of
the clause and the two-coatom lift: the canonical layer at grade `1` of the amalgam, then the
admitted field layer at grade `2` on the states satisfying the clause (`Seed.admCompletion`). -/
theorem exists_completion_of_stateAdmission {t' : StageType.{u} α 2} (hleg : t'.IsLegal)
    {o r : Fin t'.card} (ho : t'.toCellScheme.grade o = 2) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hTops : ∀ x ∈ Tops, tb.label x = ⊤)
    (hA : IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (SelfLowG o r 2 Lo Tops)) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r 2 Lo Tops := by
  have hst : SelfLowG o r 2 Lo Tops t'.label tb.label := fun t ht _ ↦ (hTops t ht).symm ▸ le_top
  exact ⟨Seed.admCompletion (I := Seed.ofCoatoms hleg htbleg hp htbp) hA hst
    (hasTwoCoatomLift_two hleg hp htbleg htbp), fun q hq hqo ↦
      Seed.admL_of_isLawful (I := Seed.ofCoatoms hleg htbleg hp htbp) hA hst
        (hasTwoCoatomLift_two hleg hp htbleg htbp) ho hq hqo⟩

set_option warningAsError false in
/-- **SCAFFOLD (contains `sorry`): the case of top grade `1`.** -/
theorem exists_completion_recProp_one {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 1 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤)
    (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ 1 ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r 1 Lo Tops := by
  sorry

/-- **The completion with the reading property** (from the SCAFFOLD statements above). -/
theorem exists_completion_recProp {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {K n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤)
    (hLo' : ∀ x, tb.label x ≠ ⊤ → x ∈ Lo)
    (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb)
    (hTops' : ∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r K Lo Tops := by
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hK2 : K ≤ 2 := hs.grade_owner ▸ t'.grade_le o
  rcases (show K = 1 ∨ K = 2 by omega) with rfl | rfl
  · exact exists_completion_recProp_one hleg hs hp htbleg htbp hLo hTops
  · exact exists_completion_of_stateAdmission hleg hs.grade_owner hp htbleg htbp
      (fun x hx ↦ (hTops x hx).1) (stateAdmission_two hleg hs hp htbp
        (donorRaising_two hleg hs hp htbleg htbp hLo' fun x h1 h3 h4 ↦
          hTops' x h1 (tb.grade_le x) h3 h4))

/-! ### h2 at two points, from the scaffold -/

/-- **h2 at two points** (modulo the three SCAFFOLD statements of this file). -/
theorem coatomCutoffDeterminationTwo : CoatomCutoffDeterminationTwo.{u} := by
  intro α K n t' g p hα hleg ⟨l, o, r, hs⟩ hp tb ⟨htbleg, htbp⟩ d hd hdK
  have hα' := hα.isSuccPrelimit
  set Lo : Finset (Fin tb.card) := univ.filter fun x ↦ tb.label x ≠ ⊤
  have := Classical.decPred (RootDet tb)
  set Tops : Finset (Fin tb.card) := ((univ.filter fun x ↦ tb.label x = ⊤ ∧
    tb.toCellScheme.grade x ≤ K) \ tb.toScheme.visibleCells Fin.castSuccEmb) \
      (univ.filter (RootDet tb))
  have hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤ := fun x hx ↦ (mem_filter.mp hx).2
  have hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb := by
    intro x hx
    simp only [Tops, mem_sdiff, mem_filter, mem_univ, true_and] at hx
    exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2⟩
  have hmem : ∀ x, tb.label x = ⊤ → x ∈ tb.toScheme.visibleCells (extendByLast g) →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops := by
    intro x hxt hxv hxr hxd
    have hg : tb.toCellScheme.grade x ≤ K := by
      obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hd) hxv
      have hdi : d.label i = ⊤ := (StageType.label_faceCell hd i).symm.trans hxt
      exact (StageType.grade_faceCell hd i).trans_le ((grade_le_topGrade hdi).trans hdK)
    simp [Tops, hxt, hg, hxr, hxd]
  obtain ⟨F, hF⟩ := exists_completion_recProp hleg hs hp htbleg htbp hLo
    (fun x hx ↦ by simp [Lo, hx]) hTops fun x h1 h2 h3 h4 ↦ by simp [Tops, h1, h2, h3, h4]
  obtain ⟨c, δ, hc, hδlab, hδ, hcδ⟩ := exists_cutoff K hα tb
  have hR := F.restrictFace_right_completion hα'
  refine ⟨F.completion hα', ⟨F.isLegal_completion hα', F.restrictFace_left_completion hα'⟩, hR,
    δ, hδ, ?_⟩
  have hd' : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (F.completion hα') = some d := by
    rw [← extendByLast_trans, ← restrictFace_trans _ _ _ hR]
    exact hd
  refine isDeterminedWithin_of_key (F.restrictFace_left_completion hα') hd'
    fun ℓ hℓ hleft hcap ↦ key_completion F hα' hs.label_owner hs.label_lost hF hc hδlab hcδ hLo
      hmem ℓ hℓ hleft hcap

end VaughtConjecture.H2
