/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2Engine
import VaughtConjecture.Continuation.TwoCoatomLift

/-!
# h2 at two points: the assembly (work file)

WORK FILE (branch `research/work-h2`).  `H2.coatomCutoffDeterminationTwo` from two SCAFFOLD
statements (each with `sorry`): `H2.donorRaising_two`, `H2.exists_completion_recProp_one`.  The
two-coatom lift `H2.hasTwoCoatomLift_two` is proved (`Seed.hasTwoCoatomLift`).
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
    (hDR : DonorRaising (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) Tops) :
    IsStateAdmission (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (SelfLowG o r 2 Lo Tops) := by
  refine selfLow_isStateAdmission (rootTops hp l) (fun f hf ↦ ?_) (fun f hf a ha ↦ ?_) hDR
    (ownerLowering_of_isLegal hleg hp htbp hs.grade_owner Nat.one_pos (by omega) t'.grade_le)
  · have := hf.orderly o
    rwa [hs.grade_owner] at this
  · exact hs.frontier_le hf ((StageType.label_faceCell hp a).trans ha.1) ha.2

set_option warningAsError false in
/-- **SCAFFOLD (contains `sorry`): donor raising at two points**, for the designated tops of
`tb` (cells labelled `⊤`, not on the root). -/
theorem donorRaising_two {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 2 (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Tops : Finset (Fin tb.card)} (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) :
    DonorRaising (StageType.faceCell hp) (StageType.faceCell htbp) 2 t'.rows.IsLawful
      tb.rows.IsLawful (rootTops hp l) Tops := by
  sorry

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

/-- **The completion with the reading property** (from the three scaffolds above). -/
theorem exists_completion_recProp {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {K n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤)
    (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r K Lo Tops := by
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hK2 : K ≤ 2 := hs.grade_owner ▸ t'.grade_le o
  rcases (show K = 1 ∨ K = 2 by omega) with rfl | rfl
  · exact exists_completion_recProp_one hleg hs hp htbleg htbp hLo hTops
  · exact exists_completion_of_stateAdmission hleg hs.grade_owner hp htbleg htbp
      (fun x hx ↦ (hTops x hx).1) (stateAdmission_two hleg hs hp htbp
        (donorRaising_two hleg hs hp htbleg htbp fun x hx ↦ ⟨(hTops x hx).1, (hTops x hx).2.2⟩))

/-! ### h2 at two points, from the scaffold -/

/-- **h2 at two points** (modulo the three SCAFFOLD statements of this file). -/
theorem coatomCutoffDeterminationTwo : CoatomCutoffDeterminationTwo.{u} := by
  intro α K n t' g p hα hleg ⟨l, o, r, hs⟩ hp tb ⟨htbleg, htbp⟩ d hd hdK
  have hα' := hα.isSuccPrelimit
  set Lo : Finset (Fin tb.card) := univ.filter fun x ↦ tb.label x ≠ ⊤
  have := Classical.decPred (RootDet tb)
  set Tops : Finset (Fin tb.card) := (((univ.filter fun x ↦ tb.label x = ⊤) ∩
    tb.toScheme.visibleCells (extendByLast g)) \ tb.toScheme.visibleCells Fin.castSuccEmb) \
      (univ.filter (RootDet tb))
  have hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤ := fun x hx ↦ (mem_filter.mp hx).2
  have hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb := by
    intro x hx
    obtain ⟨hx1, hxr⟩ := mem_sdiff.mp (mem_sdiff.mp hx).1
    obtain ⟨hx2, hxv⟩ := mem_inter.mp hx1
    have hxt := (mem_filter.mp hx2).2
    refine ⟨hxt, ?_, hxr⟩
    obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hd) hxv
    have hdi : d.label i = ⊤ := (StageType.label_faceCell hd i).symm.trans hxt
    exact (StageType.grade_faceCell hd i).trans_le ((grade_le_topGrade hdi).trans hdK)
  have hmem : ∀ x, tb.label x = ⊤ → x ∈ tb.toScheme.visibleCells (extendByLast g) →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops := by
    intro x hxt hxv hxr hxd
    simp [Tops, hxt, hxv, hxr, hxd]
  obtain ⟨F, hF⟩ := exists_completion_recProp hleg hs hp htbleg htbp hLo hTops
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
