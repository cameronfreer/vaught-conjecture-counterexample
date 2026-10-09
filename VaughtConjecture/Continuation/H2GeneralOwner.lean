/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralRaise
import VaughtConjecture.Continuation.H2OwnerOne

/-!
# h2 at every arity: owner lowering on the grade-`K` faces (work file)

WORK FILE (branch `research/work-h2`).  Every declaration here is proved.

**Owner lowering at the full grade** (`H2.ownerLoweringAt_full`): at `K = k + 1` the grade-`K`
faces are the lawful labellings (`H2.lawfulAt_iff_isLawful`), and owner lowering is
`FieldAdmission.ownerLowering_of_isLegal` (the capped lift from the root, which has grade at most
`k < K`, then the cap at `h` at the grade `K`); on one point (`k = 0`) there is no root and the cap
alone suffices.

**Below the full grade** (`K ≤ k`) the root has cells of grade `K`, which the cap at the grade `K`
would move; there owner lowering itself fails at some legal context (`OwnerGradeOne`), and the
named input is owner lowering below the designated tops (`H2.OwnerLoweringBelowAt`, in the form
`H2.OwnerLoweringBelow`).  `H2.hasRecCompletions_of_below` assembles it with the full grade.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

variable {α : Ordinal.{u}}

/-- When every cell has grade at most `K`, the grade-`K` faces are the lawful labellings. -/
theorem lawfulAt_iff_isLawful {m K : ℕ} {t : StageType.{u} α m}
    (hall : ∀ d, t.toCellScheme.grade d ≤ K) {W : Fin t.card → Label.{u}} :
    LawfulAt t K W ↔ t.rows.IsLawful W := by
  refine ⟨fun hW ↦ ?_, fun hW ↦ ⟨hW.isLawfulBelow _, fun d hd ↦ absurd (hall d) hd⟩⟩
  exact hW.1.isLawful fun d ↦ ⟨subset_univ _, hall d⟩

/-- Owner lowering passes along equivalent classes of faces. -/
theorem ownerLowering_congr {ιC ιD ιR : Type*} {rc : ιR → ιC} {rd : ιR → ιD} {o r : ιC} {K : ℕ}
    {C C' : (ιC → Label.{u}) → Prop} {D D' : (ιD → Label.{u}) → Prop} (hC : ∀ f, C f ↔ C' f)
    (hD : ∀ f, D f ↔ D' f) (h : OwnerLowering rc rd o r K C D) :
    OwnerLowering rc rd o r K C' D' := by
  intro c hc L g hL hg hroot
  obtain ⟨W, hW, hWr, hWL, hWF⟩ := h hc ((hC L).mpr hL) ((hD g).mpr hg) hroot
  exact ⟨W, (hC W).mp hW, hWr, hWL, hWF⟩

/-- **Owner lowering on the grade-`K` faces at the full grade** `K = k + 1`. -/
theorem ownerLoweringAt_full {k n : ℕ} {t' : StageType.{u} α (k + 1)} (hleg : t'.IsLegal)
    {g : Fin n ↪ Fin k} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt (k + 1) (g.trans Fin.castSuccEmb) (Fin.last k) o r)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
    {tb : StageType.{u} α (k + 1)} (htbp : restrictFace Fin.castSuccEmb tb = some p) :
    OwnerLowering (StageType.faceCell hp) (StageType.faceCell htbp) o r (k + 1)
      (LawfulAt t' (k + 1)) (LawfulAt tb (k + 1)) := by
  refine ownerLowering_congr (fun f ↦ (lawfulAt_iff_isLawful t'.grade_le).symm)
    (fun f ↦ (lawfulAt_iff_isLawful tb.grade_le).symm) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- one point: no root; cap the cells of the top grade at `h`
    have := isEmpty_card_zero p
    intro h hh L _ hL _ _
    refine ⟨fun d ↦ if t'.toCellScheme.grade d = 1 then min (L d) h else L d,
      hL.capTopGrade t'.grade_le hh, fun x ↦ isEmptyElim x, fun d ↦ ?_, ?_⟩
    · change min (if t'.toCellScheme.grade d = 1 then min (L d) h else L d) h = min (L d) h
      split_ifs
      · rw [min_assoc, min_self]
      · rfl
    · refine (min_le_left _ _).trans ?_
      simp only [hs.grade_owner, ite_true]
      exact min_le_right _ _
  · exact ownerLowering_of_isLegal hleg hp htbp hs.grade_owner hk (Nat.lt_succ_self k)
      t'.grade_le

/-- **Owner lowering below the designated tops on the grade-`K` faces, below the full grade**
(`K ≤ k`), at a source-gap context on `k + 1` points with the lost point last (a named input), in
the form `H2.OwnerLoweringBelow` of `VaughtConjecture.Continuation.H2OwnerOne`, for every
designation (non-top cells low, top cells of grade at most `K` off the root and not determined by
the root on the grade-`K` faces designated).  At `k = 1` it is owner lowering below the designated
tops between the grade-`1` faces (`H2.LawfulOne` is `H2.LawfulAt _ 1`).  Owner lowering itself
(`H2.OwnerLoweringAt`) fails at some legal context of grade `1`
(`OwnerGradeOne.not_ownerLowering_one`, on the lawful labellings; its obstruction is at cells of
grade `1`). -/
def OwnerLoweringBelowAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)), t'.IsLegal →
    ∀ (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r → K ≤ k →
    ∀ {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)}, tb.IsLegal →
      ∀ (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x, tb.label x ≠ ⊤ → x ∈ Lo) →
      (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDetAt tb K x → x ∈ Tops) →
      OwnerLoweringBelow (StageType.faceCell hp) (StageType.faceCell htbp) o r K (LawfulAt t' K)
        (LawfulAt tb K) (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops

/-- **Completions with the reading property from owner lowering below the designated tops (below
the full grade) and the engine**: donor raising is `H2.donorRaisingAt`, owner lowering at the full
grade is `H2.ownerLoweringAt_full`, and the clause is an admission of states between the grade-`K`
faces (`H2.selfLow_isStateAdmissionGap_of_below`). -/
theorem hasRecCompletions_of_below {k : ℕ} (hOL : OwnerLoweringBelowAt.{u} k)
    (hEN : AdmittedCompletionsAt.{u} k) : HasRecCompletions.{u} k := by
  intro α K n t' hleg g o r hs p hp tb htbleg htbp Lo Tops hLo hLo' hTops _ hTops'
  refine hEN t' hleg g hs hp htbleg htbp hLo hTops ?_
  have hKk : K ≤ k + 1 := hs.grade_owner ▸ t'.grade_le o
  have hOLb : OwnerLoweringBelow (StageType.faceCell hp) (StageType.faceCell htbp) o r K
      (LawfulAt t' K) (LawfulAt tb K) (Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K) Tops := by
    rcases Nat.lt_or_ge K (k + 1) with hlt | hge
    · exact hOL t' hleg g hs (Nat.lt_succ_iff.mp hlt) hp htbleg htbp hLo' hTops'
    · obtain rfl : K = k + 1 := le_antisymm hKk hge
      exact ownerLoweringBelow_of_ownerLowering (ownerLoweringAt_full hleg hs hp htbp) _ _
  refine selfLow_isStateAdmissionGap_of_below (rootTops' hp)
    (fun _ hf ↦ (frontier_le_lawfulAt hleg hs hf).1) (fun _ hf a ha ↦ ?_)
    (donorRaisingAt k t' hleg g hs hp htbleg htbp hLo' hTops') hOLb
  exact (frontier_le_lawfulAt hleg hs hf).2 _ ((StageType.label_faceCell hp a).trans ha.1) ha.2

/-- **h2 with the lost point last at every arity from owner lowering below the designated tops
(below the full grade) and the engine** on the grade-`K` faces. -/
theorem coatomCutoffDeterminationLast_of_below_engine (hOL : ∀ k, OwnerLoweringBelowAt.{u} k)
    (hEN : ∀ k, AdmittedCompletionsAt.{u} k) : CoatomCutoffDeterminationLast.{u} :=
  coatomCutoffDeterminationLast_of_hasRecCompletions fun k ↦
    hasRecCompletions_of_below (hOL k) (hEN k)

end VaughtConjecture.H2
