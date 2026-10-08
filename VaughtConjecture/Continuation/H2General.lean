/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2Two

/-!
# h2 at every arity, with the lost point last (work file)

WORK FILE (branch `research/work-h2`).  No `sorry` in this file.

**The target** (`H2.CoatomCutoffDeterminationLast`): the coatom form of cutoff determination
(`Realization.CoatomCutoffDetermination`, on `main`) for source-gap contexts with the lost point
last (`StageType.IsSourceGapContextLast`, branch `research/h2-last-reduction`), on `k + 1` points.

**The implication** (`H2.coatomCutoffDeterminationLast_of_hasRecCompletions`): the target follows
from completions with the reading property (`H2.HasRecCompletions`): for every legal source-gap
context `t'` with the lost point last and every legal coface `tb` of its coatom face, and every
designation (non-top cells low; top cells of grade at most `K` off the root and not determined by
the root designated), a completion below the full grade of the seed of `t'` and `tb` whose lawful
labellings with the owner at `⊤` satisfy the clause (`H2.RecProp`).  The rest (designation,
cutoff, the coface `F.completion`, the key step `H2.key_completion`) holds at every arity.

**At two points** the completions are `H2.exists_completion_recProp` at the lost point `1`
(`H2.hasRecCompletions_one`, modulo the SCAFFOLD `H2.exists_completion_recProp_one` of
`VaughtConjecture.Continuation.H2Two`).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

/-! ### The target and its input -/

/-- **Coatom cutoff determination for source-gap contexts with the lost point last**, on `k + 1`
points (the clause of `Realization.CoatomCutoffDetermination` for
`StageType.IsSourceGapContextLast`). -/
def CoatomCutoffDeterminationLast : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n k : ℕ⦄ (t' : StageType.{u} α (k + 1)) (g : Fin n ↪ Fin k)
    (p : StageType.{u} α k), Order.IsSuccLimit α → t'.IsLegal →
    (∃ o r, t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r) →
    restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
      restrictFace (extendByLast g) tb = some d → d.topGrade ≤ K →
        ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-- **Completions with the reading property** at a source-gap context `t'` on `k + 1` points with
the lost point last, for every legal coface `tb` of its coatom face and every designation. -/
def HasRecCompletions (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)) (hleg : t'.IsLegal)
    (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r →
    ∀ {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p)
      {tb : StageType.{u} α (k + 1)} (htbleg : tb.IsLegal)
      (htbp : restrictFace Fin.castSuccEmb tb = some p) {Lo Tops : Finset (Fin tb.card)},
      (∀ x ∈ Lo, tb.label x ≠ ⊤) → (∀ x, tb.label x ≠ ⊤ → x ∈ Lo) →
      (∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) →
      (∀ x, tb.label x = ⊤ → tb.toCellScheme.grade x ≤ K →
        x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet tb x → x ∈ Tops) →
      ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
        RecProp F o r K Lo Tops

/-! ### The implication -/

/-- **h2 at one context with the lost point last**, from completions with the reading property at
its arity. -/
theorem exists_coface_last {α : Ordinal.{u}} {K n k : ℕ} (hrec : HasRecCompletions.{u} k)
    {t' : StageType.{u} α (k + 1)} {g : Fin n ↪ Fin k} {p : StageType.{u} α k}
    (hα : Order.IsSuccLimit α) (hleg : t'.IsLegal) {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r)
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α (k + 1)}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d)
    (hdK : d.topGrade ≤ K) :
    ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d := by
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
  obtain ⟨F, hF⟩ := hrec t' hleg g hs hp htbleg htbp hLo (fun x hx ↦ by simp [Lo, hx]) hTops
    fun x h1 h2 h3 h4 ↦ by simp [Tops, h1, h2, h3, h4]
  obtain ⟨c, δ, hc, hδlab, hδ, hcδ⟩ := exists_cutoff K hα tb
  have hR := F.restrictFace_right_completion hα'
  refine ⟨F.completion hα', ⟨F.isLegal_completion hα', F.restrictFace_left_completion hα'⟩, hR,
    δ, hδ, ?_⟩
  have hd' : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (F.completion hα') = some d := by
    rw [← extendByLast_trans, ← restrictFace_trans _ _ _ hR]
    exact hd
  exact isDeterminedWithin_of_key (F.restrictFace_left_completion hα') hd'
    fun ℓ hℓ hleft hcap ↦ key_completion F hα' hs.label_owner hs.label_lost hF hc hδlab hcδ hLo
      hmem ℓ hℓ hleft hcap

/-- **h2 with the lost point last, from completions with the reading property** at every
arity. -/
theorem coatomCutoffDeterminationLast_of_hasRecCompletions
    (hrec : ∀ k, HasRecCompletions.{u} k) : CoatomCutoffDeterminationLast.{u} := by
  intro α K n k t' g p hα hleg ⟨o, r, hs⟩ hp tb ⟨htbleg, htbp⟩ d hd hdK
  exact exists_coface_last (hrec k) hα hleg hs hp htbleg htbp hd hdK

/-! ### Two points -/

/-- **Completions with the reading property at two points** (`H2.exists_completion_recProp` at the
lost point `1`, modulo the SCAFFOLD `H2.exists_completion_recProp_one`). -/
theorem hasRecCompletions_one : HasRecCompletions.{u} 1 := by
  intro α K n t' hleg g o r hs p hp tb htbleg htbp Lo Tops hLo hLo' hTops hTops'
  refine exists_completion_recProp hleg hs hp htbleg htbp hTops hTops' (fun hK ↦ ?_)
    fun _ hT ↦ donorRaising_two_one hp htbleg htbp hLo' hT
  subst hK
  exact exists_completion_recProp_one hleg hs hp htbleg htbp hLo hLo' hTops hTops'
    (root_one hp htbp hLo')

end VaughtConjecture.H2
