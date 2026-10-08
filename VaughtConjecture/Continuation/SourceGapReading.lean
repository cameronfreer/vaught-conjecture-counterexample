/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapSeparatedInstance
import VaughtConjecture.Expansion.BlockResidualLosses

/-!
# Reading each new top through a private top

Roadmap, Layer 3 ((R2) of the table of 3.4); the source-gap contexts of
`VaughtConjecture.Continuation.SourceGapContext`.

Separation through the lost top alone is refuted
(`SeparationObstruction.not_hasSeparatedPinnedExtensions`).  This file states the variant in which
each new top is read through a private top chosen with it, the hypothesis of the compiled
`StageType.isDeterminedWithin_receivingFamily_of_forall_rowAt_le`.

**Reading each new top** (`StageType.ReadsEachNewTop`).  A one-point coface `D'` of `t'` reads
each new top along `h` when for every new cell `x` of `D'` visible through `h` followed by the new
point and labelled `⊤` there are two cells `w` and `s` of `t'` labelled `⊤`, with `s` and `x` of
grade at most that of `w`, such that every cell of `D'` of graded index `(univ, grade w)` reads `x`
at least as (the cell of `D'` at) `s`.

**The reading pinned extension property** (`StageType.HasReadingPinnedExtensions α`; status:
defined, open).  The quantifier order is: for every legal source-gap context `t'` of grade `K`
along `h` (with its lost point, owner and lost top), every face `t` of `t'` along `h`, and every
legal one-point coface `d` of `t` of top grade at most `K`, there is **one** legal one-point coface
`D'` of `t'` with face `d` along `h` followed by the new point that reads each new top; the pair of
private cells `(w, s)` may depend on the new top `x` (and on `D'`), and the reading is asked at
every cell of graded index `(univ, grade w)`.  No cutoff and no labelling enter: the cutoff is
chosen afterwards, above the labels of `D'` other than `⊤`.

**From it** (compiled in this repository):
* cutoff determination for source-gap contexts
  (`Realization.cutoffDetermination_isSourceGapContext_of_reading`), from the property at every
  limit stage;
* exact one-point residual receiving in one model from (R1) for that model and the property at its
  stage (`Realization.exists_covers_snoc_of_hasReadingPinnedExtensions`);
* (R2) from (R1) for every model at every limit stage and the property at every limit stage
  (`Realization.residualReceiving_of_hasReadingPinnedExtensions`), and (R2) at the countable block
  stages from (R1) in the library's form and the property at the countable block stages
  (`Realization.blockResidualReceiving_of_hasReadingPinnedExtensions`).

**Separation through the lost top is a special case**
(`StageType.SeparatesThrough.readsEachNewTop`): with the owner as `w` and the lost top as `s`.
So the separated instance (`SeparatedInstance.exists_separatesThrough`) gives the conclusion of the
property at its input (`SeparatedInstance.exists_readsEachNewTop`).  At the input refuting
separation through the lost top, `SeparationObstruction.T α` with itself as donor, the conclusion
holds too, with a different choice of private top for each new top
(`ReadingInstance.exists_readsEachNewTop_T`, in
`VaughtConjecture.Continuation.SourceGapReadingInstance`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- A one-point coface `D'` of `t'` (with `hD'` its face along the initial segment) **reads each
new top along `h`**: for every new cell `x` visible through `h` followed by the new point and
labelled `⊤` there are cells `w` and `s` of `t'` labelled `⊤`, with `s` and `x` of grade at most
that of `w`, such that every cell of `D'` of graded index `(univ, grade w)` reads `x` at least as
the cell at `s`. -/
def ReadsEachNewTop {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : restrictFace Fin.castSuccEmb D' = some t') (h : Fin n ↪ Fin k) : Prop :=
  ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
    D'.label x = ⊤ → ∃ w s : Fin t'.card, t'.label w = ⊤ ∧ t'.label s = ⊤ ∧
      t'.toCellScheme.grade s ≤ t'.toCellScheme.grade w ∧
      D'.toCellScheme.grade x ≤ t'.toCellScheme.grade w ∧
      ∀ u, D'.toCellScheme.gradedIndex u = (univ, t'.toCellScheme.grade w) →
        D'.rowAt u (faceCell hD' s) ≤ D'.rowAt u x

variable (α) in
/-- The **reading pinned extension property** at stage `α`: for every legal source-gap context
`t'` of grade `K` along `h`, every face `t` of `t'` along `h`, and every legal one-point coface `d`
of `t` of top grade at most `K`, one legal one-point coface `D'` of `t'` has face `d` along `h`
followed by the new point and reads each new top along `h` (`StageType.ReadsEachNewTop`).
Defined; open. -/
def HasReadingPinnedExtensions : Prop :=
  ∀ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (l : Fin k) (o r : Fin t'.card),
    t'.IsLegal → t'.IsSourceGapContextAt K h l o r → ∀ t : StageType.{u} α n,
      restrictFace h t' = some t → ∀ d ∈ t.cofaces, d.topGrade ≤ K →
        ∃ (D' : StageType.{u} α (k + 1)) (hD' : D' ∈ t'.cofaces),
          restrictFace (extendByLast h) D' = some d ∧ ReadsEachNewTop hD'.2 h

/-- **Determination over a coface reading each new top**: at a cutoff above every label of `D'`
other than `⊤`, the face along `h` followed by the new point is determined. -/
theorem ReadsEachNewTop.isDeterminedWithin {t' : StageType.{u} α k}
    {D' : StageType.{u} α (k + 1)} (hD' : D' ∈ t'.cofaces) {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hD'd : restrictFace (extendByLast h) D' = some d)
    (hread : ReadsEachNewTop hD'.2 h) {δ : Ordinal.{u}}
    (hδ : ∀ j, D'.label j ≠ ⊤ → D'.label j < (δ : Label.{u})) :
    IsDeterminedWithin (receivingFamily D' δ) t' h d := by
  refine isDeterminedWithin_receivingFamily_of_forall_rowAt_le hD'.1 hD'.2 hD'd
    (fun x hx hxl hxt ↦ ?_) hδ
  obtain ⟨w, s, hw, hs, hsw, hxw, hu⟩ := hread x hx hxl hxt
  refine ⟨faceCell hD'.2 w, faceCell hD'.2 s, last_notMem_scope_faceCell _ _,
    last_notMem_scope_faceCell _ _, by rw [label_faceCell, hw], by rw [label_faceCell, hs], ?_,
    ?_, ?_⟩
  · rw [grade_faceCell, grade_faceCell]; exact hsw
  · rw [grade_faceCell]; exact hxw
  · intro u hu'
    rw [grade_faceCell] at hu'
    exact hu u hu'

/-- **Separation through the lost top reads each new top**, with the owner as the grade witness
and the lost top as the cell read. -/
theorem SeparatesThrough.readsEachNewTop {K : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {l : Fin k} {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K h l o r)
    {D' : StageType.{u} α (k + 1)} (hD' : restrictFace Fin.castSuccEmb D' = some t')
    {d : StageType.{u} α (n + 1)} (hdK : d.topGrade ≤ K)
    (hD'd : restrictFace (extendByLast h) D' = some d) (hsep : SeparatesThrough hD' h K r) :
    ReadsEachNewTop hD' h := by
  intro x hx hxl hxt
  refine ⟨o, r, hs.label_owner, hs.label_lost, ?_, ?_, ?_⟩
  · rw [hs.grade_owner, ← hs.topGrade_eq]
    exact grade_le_topGrade hs.label_lost
  · obtain ⟨y, rfl⟩ := D'.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hD'd) hx
    have hy : d.label y = ⊤ := (label_faceCell hD'd y).symm.trans hxt
    rw [hs.grade_owner]
    exact ((D'.toScheme.grade_faceCell _ y).trans_le (grade_le_topGrade hy)).trans hdK
  · intro u hu
    rw [hs.grade_owner] at hu
    exact hsep x hx hxl hxt u hu

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {n : ℕ}

/-- **Cutoff determination for source-gap contexts from reading pinned extensions** at every limit
stage. -/
theorem cutoffDetermination_isSourceGapContext_of_reading
    (hread : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasReadingPinnedExtensions α) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h where
  exists_coface _ _ _ _ t' h hα ht' hP t ht d hd hdK := by
    obtain ⟨l, o, r, hs⟩ := hP
    obtain ⟨D', hD', hD'd, hrd⟩ := hread hα t' h l o r ht' hs t ht d hd hdK
    obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
    exact ⟨D', hD', δ, isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩, hrd.isDeterminedWithin hD' hD'd hδ⟩

/-- **Exact residual receiving in one model from reading pinned extensions at its stage**, with
(R1) for that model only. -/
theorem exists_covers_snoc_of_hasReadingPinnedExtensions (hα : Order.IsSuccLimit α)
    (hR : R.IsModel) (hrec : R.HasFiniteCutReceiving)
    (hread : StageType.HasReadingPinnedExtensions α)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (hdK : d.topGrade ≤ K) :
    ∃ y : M, R.Covers d (Fin.snoc c y) := by
  obtain ⟨k, t', c', e, hc', hcc', -, o, r, hs⟩ :=
    exists_covers_isSourceGapContextAt hα hR hcore hK hc
  obtain ⟨D', hD', hD'd, hrd⟩ := hread t' _ _ o r (hR.isLegal _ _ hc'.eval_eq) hs t
    (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd hdK
  obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
  rw [← hcc']
  exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
    (hrec.realizesOver_receivingFamily hc' hD' (isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩))
    (hrd.isDeterminedWithin hD' hD'd hδ)

/-- **(R2) from (R1) and reading pinned extensions**, both at every limit stage. -/
theorem residualReceiving_of_hasReadingPinnedExtensions
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hread : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasReadingPinnedExtensions α) :
    ResidualReceiving.{u, w} :=
  residualReceiving_of_cutoffDetermination_isSourceGapContext hrec
    (cutoffDetermination_isSourceGapContext_of_reading hread)

open Ordinal in
/-- **(R2) at the countable block stages from (R1) in the library's form and reading pinned
extensions at the countable block stages.** -/
theorem blockResidualReceiving_of_hasReadingPinnedExtensions
    (hrec : Expansion.FiniteCutReceiving.{w})
    (hread : ∀ ξ : Ordinal.{0}, ξ < ω₁ → StageType.HasReadingPinnedExtensions (blockStage ξ)) :
    BlockResidualReceiving.{w} where
  exists_covers ξ _ R _ hξ hR hcore hK _ _ _ hc _ hD hDK :=
    exists_covers_snoc_of_hasReadingPinnedExtensions (isSuccLimit_blockStage ξ) hR
      (hrec.receive (isSuccLimit_blockStage ξ) (blockStage_lt_omega_one hξ) R hR) (hread ξ hξ)
      hcore hK hc hD hDK

end Realization

namespace SeparatedInstance

/-- The separated instance reads each new top. -/
theorem exists_readsEachNewTop (α : Ordinal.{u}) {r : Fin (context α).card}
    (hr : StageType.faceCell (restrictFace_context α) r = cellD α 0) :
    ∃ (D' : StageType.{u} α 2) (hD' : D' ∈ (context α).cofaces),
      StageType.restrictFace (extendByLast emptyRoot) D' = some (donor α) ∧
        StageType.ReadsEachNewTop hD'.2 emptyRoot := by
  obtain ⟨o, ho⟩ := StageType.exists_faceCell_eq_of_last_notMem (restrictFace_context α)
    (s := cellD α 1) (by
      -- the scope of the cell `1` of the display is `{0}`
      change Fin.last 1 ∉ cells.scope 1
      decide)
  exact ⟨D α, ⟨isLegal_D α, restrictFace_context α⟩, restrictFace_donor α,
    (separatesThrough_D α hr).readsEachNewTop (isSourceGapContextAt_context α ho hr)
      (restrictFace_context α) (topGrade_donor_le α) (restrictFace_donor α)⟩

end SeparatedInstance

end VaughtConjecture
