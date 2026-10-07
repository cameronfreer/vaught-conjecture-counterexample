/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapContext

/-!
# Cutoff determination for source-gap contexts, from separated pinned extensions

Roadmap, Layer 3 ((R2) of the table of 3.4: exact residual receiving, reduced in
`VaughtConjecture.Continuation.ExactReceiving` to residual acquisition and cutoff determination,
with residual acquisition for source-gap contexts compiled in
`VaughtConjecture.Continuation.SourceGapContext`); semantic contract, items 4 and 8.

**Reading a top through a top.**  In a lawful section `τ`, if a cell `w` is labelled `⊤` and its
row reads a cell `x` at least as a cell `s` labelled `⊤` (both below `w`), then `x` is labelled
`⊤` (`CellScheme.Rows.IsLawful.eq_top_of_row_le`): the witness of locality at `w` has suppressor
`⊤` up to the grade of `w` and shifter `⊤` at the row value of `s`.  In a legal stage type the
reading cell need not be given: if `w` is labelled `⊤` and every cell of graded index
`(univ, grade w)` reads `x` at least as `s`, with `s` and `x` of grade at most that of `w`, then
`x` is labelled `⊤` (`StageType.label_eq_top_of_forall_rowAt_le`, compiled in this repository);
completeness gives a cell of that graded index and availability makes one of them `⊤`.  The
grade of `x` is bounded by the grade of the witness `w`, not by that of `s`.

**Determination over a separating coface** (`StageType.isDeterminedWithin_receivingFamily_of_
forall_rowAt_le`, compiled in this repository).  Let a legal `D'` on `k + 1` points have face `t'`
along the initial segment and `d` along `h` followed by the new point, and let every new cell `x`
of `D'` visible in that face and labelled `⊤` be read, by every cell of graded index
`(univ, grade w)`, at least as a cell `s`, for two cells `w` and `s` of `t'` labelled `⊤` with
`grade s ≤ grade w` and `grade x ≤ grade w`.  Then `d` is determined over `t'` along `h` within
the receiving family of `D'` at every cutoff above the labels of `D'` other than `⊤`: those labels
are kept by the cutoff, the cells of `t'` by the face, and the new tops by the reading.

**Separated pinned extensions** (`StageType.HasSeparatedPinnedExtensions α`, a hypothesis here,
not a theorem).  At stage `α`: for every legal source-gap context `t'` of grade `K` along `h`,
with lost top `r`, and every legal one-point coface `d` of top grade at most `K` of the face of
`t'` along `h`, some legal one-point coface `D'` of `t'` has face `d` along `h` followed by the new
point (a pinned extension exact over `h`, as in `VaughtConjecture.Extension.PinnedExtension`), and
every cell of `D'` of graded index `(univ, K)` reads every new cell visible in that face and
labelled `⊤` at least as it reads the lost top.  With the owner as the witness `w` (grade `K`) and
the lost top as `s`, the reading above applies, so **cutoff determination for source-gap contexts
follows from separated pinned extensions at every limit stage**
(`Realization.cutoffDetermination_isSourceGapContext`, compiled in this repository), and with
(R1) for every model at every limit stage, **(R2) follows**
(`Realization.residualReceiving_of_hasSeparatedPinnedExtensions`, compiled in this repository,
both hypotheses explicit).

**One model at a time.**  The same argument works in a single model: in a model `R` at a limit
stage `α` with finite-cut receiving ((R1) for `R` alone), with no cover that is a globally rigid
core and with top-grade supremum `K`, the separated pinned extension property at `α` gives exact
one-point receiving of the cofaces of top grade at most `K`
(`Realization.exists_covers_snoc_of_hasSeparatedPinnedExtensions`, compiled in this repository).
Neither (R1) for other models nor the property at other stages is used.

Status of the hypothesis: **false at every stage**
(`SeparationObstruction.not_hasSeparatedPinnedExtensions`, in
`VaughtConjecture.Continuation.SourceGapSeparationObstruction`): a legal source-gap context with a
lawful labelling that keeps the lost top at `⊤` and lowers a root top, and a donor bounding a new
top by that root top, have no separating coface.  The reductions above are correct, with a false
hypothesis; determination for source-gap contexts is not refuted.  The coatom extension property
`StageType.HasCoatomExtensions α` gives the pinned extension (`StageType.exists_pinned_extension`)
but says nothing about the rows of the cells of full scope; it gives the separated pinned
extension at donors without a new top, where the reading is vacuous
(`StageType.exists_separated_of_hasCoatomExtensions`, in
`VaughtConjecture.Continuation.SourceGapPinned`).  The strict source gaps of the
context are not used by the determination; they are what the legality of such a `D'` is expected
to need (argued, not formalized): in a lawful labelling of `D'` in which a cell of graded index
`(univ, K)` dominates the lost top and a new top, the reading keeps the lost top at most the new
top, so a donor labelling lowering a new top must be met by a labelling of `t'` lowering the lost
top while the retained top cells stay `⊤`; below the owner, the strict gaps give such a labelling
(`StageType.IsSourceGapContextAt.exists_isLawfulBelow`, in
`VaughtConjecture.Continuation.SourceGapLowering`).

**The compiled determination counterexamples.**  The hypothesis is stated only over source-gap
contexts, which exclude the apex point over the empty root and the top-free contexts
(`StageType.not_isSourceGapContext_of_isTopFree`, `StageType.not_isSourceGapContext_of_surjective`,
`StageType.not_isSourceGapContext_addApex`).  The determination itself needs a cell `w` of `t'`
labelled `⊤` with every new top of grade at most the grade of `w`; at a top-free context there is
no such `w`, and at a context of top grade below the grade of a new top there is none of large
enough grade; this is where the counterexamples fail, and the source-gap context provides `w` (the
owner, of grade `K`, with `d.topGrade ≤ K`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

/-! ### Reading a top through a top -/

namespace CellScheme.Rows.IsLawful

variable {ι β : Type*} {D : CellScheme ι β} {R : D.Rows} {τ : ι → Label.{u}}

/-- **A top read at least as a top is a top**: in a lawful section `τ`, if `τ w = ⊤`, a cell `s`
below `w` has `τ s = ⊤`, and the row of `w` reads a cell `x` below `w` at least as `s`, then
`τ x = ⊤`.  The witness of locality at `w` has suppressor `⊤` up to the grade of `w` and shifter
`⊤` at the row value of `s`; the shifter is monotone and the suppressor antitone. -/
theorem eq_top_of_row_le (hτ : R.IsLawful τ) {w : ι} (hw : τ w = ⊤)
    {s x : D.below (D.gradedIndex w)} (hs : τ s = ⊤) (hsx : R.row w s ≤ R.row w x) : τ x = ⊤ := by
  obtain ⟨g, σ, hwit, heq⟩ := hτ.locality w
  -- below `w`, the target of locality is `τ` itself, since `τ w = ⊤`
  have hq (d : D.below (D.gradedIndex w)) : τ d = min (σ (R.row w d)) (g (D.grade d)) := by
    have := heq d
    simp only [hw, min_top_right] at this
    exact this
  have hgw : g (D.grade w) = ⊤ :=
    (_root_.min_eq_top.mp ((hq ⟨w, D.mem_below_gradedIndex w⟩).symm.trans hw)).2
  have hσs : σ (R.row w s) = ⊤ := (_root_.min_eq_top.mp ((hq s).symm.trans hs)).1
  rw [hq x, _root_.min_eq_top]
  exact ⟨top_le_iff.mp (hσs ▸ hwit.monotone hsx), top_le_iff.mp (hgw ▸ hwit.antitone x.2.2)⟩

end CellScheme.Rows.IsLawful

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- **A top read at least as a top, through a witness of larger grade**: in a legal stage type
`D`, let `w` and `s` be labelled `⊤`, with `s` and `x` of grade at most that of `w`.  If every cell
of graded index `(univ, grade w)` reads `x` at least as `s` (`Scheme.rowAt`), then `x` is labelled
`⊤`.  Completeness gives a cell of that graded index, availability of the labelling makes one of
them `⊤`, and `CellScheme.Rows.IsLawful.eq_top_of_row_le` applies to it.  The grade of `x` is
bounded by that of `w`, not by that of `s`. -/
theorem label_eq_top_of_forall_rowAt_le {D : StageType.{u} α m} (hD : D.IsLegal)
    {w s x : Fin D.card} (hw : D.label w = ⊤) (hs : D.label s = ⊤)
    (hsw : D.toCellScheme.grade s ≤ D.toCellScheme.grade w)
    (hxw : D.toCellScheme.grade x ≤ D.toCellScheme.grade w)
    (hread : ∀ u, D.toCellScheme.gradedIndex u = (univ, D.toCellScheme.grade w) →
      D.rowAt u s ≤ D.rowAt u x) : D.label x = ⊤ := by
  have hg : D.toCellScheme.grade w ≤ #(univ : Finset (Fin m)) := by
    rw [card_univ, Fintype.card_fin]
    exact D.grade_le w
  obtain ⟨u₀, hu₀⟩ := (isLegal_iff.mp hD).2.2 (univ, D.toCellScheme.grade w)
    ⟨D.univ_mem_faces, D.isWellFormed.isWellFormed.grade_pos w, hg⟩
  have hsc : D.toCellScheme.scope w ⊆ D.toCellScheme.scope u₀ := by
    have hsu₀ : D.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
    rw [hsu₀]
    exact subset_univ _
  obtain ⟨u, hu, hwu⟩ := D.isLawful.availability w u₀ hsc (congrArg Prod.snd hu₀).symm
  rw [hu₀] at hu
  rw [hw, top_le_iff] at hwu
  have hb {y : Fin D.card} (hy : D.toCellScheme.grade y ≤ D.toCellScheme.grade w) :
      y ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu]
    exact ⟨subset_univ _, hy⟩
  have hr := hread u hu
  rw [Scheme.rowAt_of_mem (hb hsw), Scheme.rowAt_of_mem (hb hxw)] at hr
  exact D.isLawful.eq_top_of_row_le (s := ⟨s, hb hsw⟩) (x := ⟨x, hb hxw⟩) hwu hs hr

/-! ### Determination over a separating coface -/

/-- **Stage types on one scheme with a common face agree at the cells visible through it.** -/
private theorem label_eq_of_restrictFace_eq {S : Scheme.{u} m}
    {ℓ ℓ' : Fin S.card → Label.{u}} {hw hw' : S.IsWellFormed} {hc hc' : S.IsCoded}
    {hl : S.rows.IsLawful ℓ} {hl' : S.rows.IsLawful ℓ'} {ha : ∀ d, AtStage α (ℓ d)}
    {ha' : ∀ d, AtStage α (ℓ' d)} {g : Fin n ↪ Fin m} {t : StageType.{u} α n}
    (hq : restrictFace g (⟨S, ℓ, hw, hc, hl, ha⟩ : StageType.{u} α m) = some t)
    (hD : restrictFace g (⟨S, ℓ', hw', hc', hl', ha'⟩ : StageType.{u} α m) = some t)
    {y : Fin S.card} (hy : y ∈ S.visibleCells g) : ℓ y = ℓ' y := by
  obtain ⟨hfq, hq⟩ := (restrictFace_eq_some_iff _ g).mp hq
  obtain ⟨hfD, hD⟩ := (restrictFace_eq_some_iff _ g).mp hD
  obtain ⟨i, rfl⟩ : y ∈ Set.range (S.cellMap g) := by
    rw [Scheme.range_cellMap]
    exact hy
  exact label_congr (hq.trans hD.symm) (i := i) (j := i) rfl

/-- **Determination over a separating coface.**  Let a legal `D'` have face `t'` along the initial
segment and `d` along `h` followed by the new point, and suppose that for every new cell `x` of
`D'` visible in that face and labelled `⊤` there are cells `w` and `s` avoiding the new point and
labelled `⊤`, with `s` and `x` of grade at most that of `w`, such that every cell of graded index
`(univ, grade w)` reads `x` at least as `s`.  Then `d` is determined over `t'` along `h` within the
receiving family of `D'` at a cutoff above every label of `D'` other than `⊤`: the labels other
than `⊤` are kept by the cutoff, the cells avoiding the new point by the face `t'`, and the new
tops by `label_eq_top_of_forall_rowAt_le`. -/
theorem isDeterminedWithin_receivingFamily_of_forall_rowAt_le {t' : StageType.{u} α k}
    {D' : StageType.{u} α (k + 1)} (hD' : D'.IsLegal)
    (hD't' : restrictFace Fin.castSuccEmb D' = some t') {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hD'd : restrictFace (extendByLast h) D' = some d)
    (hread : ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
      D'.label x = ⊤ → ∃ w s, Fin.last k ∉ D'.toCellScheme.scope w ∧
        Fin.last k ∉ D'.toCellScheme.scope s ∧ D'.label w = ⊤ ∧ D'.label s = ⊤ ∧
        D'.toCellScheme.grade s ≤ D'.toCellScheme.grade w ∧
        D'.toCellScheme.grade x ≤ D'.toCellScheme.grade w ∧
        ∀ u, D'.toCellScheme.gradedIndex u = (univ, D'.toCellScheme.grade w) →
          D'.rowAt u s ≤ D'.rowAt u x)
    {δ : Ordinal.{u}} (hδ : ∀ j, D'.label j ≠ ⊤ → D'.label j < (δ : Label.{u})) :
    IsDeterminedWithin (receivingFamily D' δ) t' h d := fun q hq hqt ↦ by
  obtain ⟨hs, hl⟩ := hq
  obtain ⟨S, ℓ, hw, hc, hlaw, hat⟩ := q
  obtain ⟨S', ℓ', hw', hc', hlaw', hat'⟩ := D'
  obtain rfl : S = S' := hs
  have hl (j : Fin S.card) : min (ℓ j) δ = min (ℓ' j) δ := hl j j rfl
  -- the labels other than `⊤` are kept
  have hnt (j : Fin S.card) (hj : ℓ' j ≠ ⊤) : ℓ j = ℓ' j := by
    have h := hl j
    rw [min_eq_left (hδ j hj).le] at h
    rcases le_total (ℓ j) δ with h' | h'
    · rwa [min_eq_left h'] at h
    · rw [min_eq_right h'] at h
      exact absurd (h ▸ hδ j hj) (lt_irrefl _)
  -- the cells avoiding the new point are kept
  have hpriv (y : Fin S.card) (hy : Fin.last k ∉ S.toCellScheme.scope y) : ℓ y = ℓ' y :=
    label_eq_of_restrictFace_eq hqt hD't' (Scheme.mem_visibleCells.mpr fun z hz ↦
      Fin.exists_castSucc_eq.mpr fun hzl ↦ hy (hzl ▸ hz))
  -- legality concerns only the scheme
  have hq' : (⟨S, ℓ, hw, hc, hlaw, hat⟩ : StageType.{u} α (k + 1)).IsLegal := hD'
  have hvis (x : Fin S.card) (hx : x ∈ S.visibleCells (extendByLast h)) : ℓ x = ℓ' x := by
    by_cases hxt : ℓ' x = ⊤
    · by_cases hxl : Fin.last k ∈ S.toCellScheme.scope x
      · obtain ⟨w, s, hwl, hsl, hwt, hst, hsw, hxw, hrd⟩ := hread x hx hxl hxt
        rw [hxt]
        exact label_eq_top_of_forall_rowAt_le (D := ⟨S, ℓ, hw, hc, hlaw, hat⟩) hq'
          ((hpriv w hwl).trans hwt) ((hpriv s hsl).trans hst) hsw hxw hrd
      · exact hpriv x hxl
    · exact hnt x hxt
  rw [← hD'd]
  by_cases hfm : univ.map (extendByLast h) ∈ S.toCellScheme.faces
  · rw [restrictFace_of_mem _ _ hfm, restrictFace_of_mem _ _ hfm]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    exact hvis _ (S.cellMap_mem _ i)
  · rw [restrictFace_of_notMem _ _ hfm, restrictFace_of_notMem _ _ hfm]

/-! ### Separated pinned extensions -/

/-- A one-point coface `D'` of `t'` (with `hD'` its face along the initial segment) **separates the
new tops along `h` through the cell `r` of `t'` at grade `K`**: every cell of `D'` of graded index
`(univ, K)` reads every new cell visible through `h` followed by the new point and labelled `⊤` at
least as it reads `r`. -/
def SeparatesThrough {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : restrictFace Fin.castSuccEmb D' = some t') (h : Fin n ↪ Fin k) (K : ℕ)
    (r : Fin t'.card) : Prop :=
  ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
    D'.label x = ⊤ → ∀ u, D'.toCellScheme.gradedIndex u = (univ, K) →
      D'.rowAt u (faceCell hD' r) ≤ D'.rowAt u x

variable (α) in
/-- The **separated pinned extension property** at stage `α`: for every legal source-gap context
`t'` of grade `K` along `h`, with lost top `r`, and every legal one-point coface `d` of top grade at
most `K` of the face `t` of `t'` along `h`, some legal one-point coface `D'` of `t'` has face `d`
along `h` followed by the new point and separates the new tops along `h` through `r` at grade `K`
(`StageType.SeparatesThrough`).  False at every stage
(`SeparationObstruction.not_hasSeparatedPinnedExtensions`); from the coatom extension property it
is compiled only at donors without a new top. -/
def HasSeparatedPinnedExtensions : Prop :=
  ∀ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (l : Fin k) (o r : Fin t'.card),
    t'.IsLegal → t'.IsSourceGapContextAt K h l o r → ∀ t : StageType.{u} α n,
      restrictFace h t' = some t → ∀ d ∈ t.cofaces, d.topGrade ≤ K →
        ∃ (D' : StageType.{u} α (k + 1)) (hD' : D' ∈ t'.cofaces),
          restrictFace (extendByLast h) D' = some d ∧ SeparatesThrough hD'.2 h K r

/-- **Determination over a separated pinned extension of a source-gap context**: with the owner
as the witness and the lost top as the cell read, every new top is read through cells of `t'`
labelled `⊤`; its grade is at most the top grade of `d`, hence at most `K`. -/
theorem isDeterminedWithin_of_separatesThrough {K : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {l : Fin k} {o r : Fin t'.card} (hs : t'.IsSourceGapContextAt K h l o r)
    {D' : StageType.{u} α (k + 1)} (hD' : D' ∈ t'.cofaces) {d : StageType.{u} α (n + 1)}
    (hdK : d.topGrade ≤ K) (hD'd : restrictFace (extendByLast h) D' = some d)
    (hsep : SeparatesThrough hD'.2 h K r) {δ : Ordinal.{u}}
    (hδ : ∀ j, D'.label j ≠ ⊤ → D'.label j < (δ : Label.{u})) :
    IsDeterminedWithin (receivingFamily D' δ) t' h d := by
  refine isDeterminedWithin_receivingFamily_of_forall_rowAt_le hD'.1 hD'.2 hD'd
    (fun x hx hxl hxt ↦ ⟨faceCell hD'.2 o, faceCell hD'.2 r, last_notMem_scope_faceCell _ _,
      last_notMem_scope_faceCell _ _, by rw [label_faceCell, hs.label_owner],
      by rw [label_faceCell, hs.label_lost], ?_, ?_, ?_⟩) hδ
  · rw [grade_faceCell, grade_faceCell, hs.grade_owner, ← hs.topGrade_eq]
    exact grade_le_topGrade hs.label_lost
  · -- a new top is a top of `d`
    obtain ⟨y, rfl⟩ := D'.toScheme.exists_faceCell_eq
      (comap_toScheme_of_restrictFace hD'd) hx
    have hy : d.label y = ⊤ := (label_faceCell hD'd y).symm.trans hxt
    rw [grade_faceCell hD'.2 o, hs.grade_owner]
    exact ((D'.toScheme.grade_faceCell _ y).trans_le (grade_le_topGrade hy)).trans hdK
  · intro u hu
    rw [grade_faceCell, hs.grade_owner] at hu
    exact hsep x hx hxl hxt u hu

end StageType

namespace Realization

/-- **Cutoff determination for source-gap contexts from separated pinned extensions**: if the
separated pinned extension property holds at every limit stage, cutoff determination holds for
source-gap contexts, at a cutoff above every label of the separating coface other than `⊤`. -/
theorem cutoffDetermination_isSourceGapContext
    (hsep : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasSeparatedPinnedExtensions α) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h where
  exists_coface _ _ _ _ t' h hα ht' hP t ht d hd hdK := by
    obtain ⟨l, o, r, hs⟩ := hP
    obtain ⟨D', hD', hD'd, hsp⟩ := hsep hα t' h l o r ht' hs t ht d hd hdK
    obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
    exact ⟨D', hD', δ, isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩,
      StageType.isDeterminedWithin_of_separatesThrough hs hD' hdK hD'd hsp hδ⟩

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {n : ℕ}

/-- The face of an acquired context along `h` is the type of the original cover. -/
private theorem restrictFace_of_covers' (hR : R.IsConsistent) {t : StageType.{u} α n}
    {c : Fin n → M} (hc : R.Covers t c) {k : ℕ} {t' : StageType.{u} α k} {c' : Fin k → M}
    (hc' : R.Covers t' c') {h : Fin n ↪ Fin k} (hcc' : c' ∘ h = c) :
    StageType.restrictFace h t' = some t := by
  rw [← hR ⟨c', hc'.injective⟩ t' h hc'.eval_eq, ← hc.eval_eq]
  congr 1
  ext i
  exact congrFun hcc' i

/-- **Exact residual receiving in one model, from separated pinned extensions at its stage**: in a
model `R` at a limit stage `α` with finite-cut receiving ((R1) for `R` alone), with no cover that is
a globally rigid core and with top-grade supremum `K`, if the separated pinned extension property
holds at `α`, then every one-point coface of top grade at most `K` of the type of a cover is the
type of the cover extended by one point.  The compiled acquisition of a source-gap context, the
determination over a separated pinned extension, and finite-cut receiving of `R`. -/
theorem exists_covers_snoc_of_hasSeparatedPinnedExtensions (hα : Order.IsSuccLimit α)
    (hR : R.IsModel) (hrec : R.HasFiniteCutReceiving)
    (hsep : StageType.HasSeparatedPinnedExtensions α)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (hdK : d.topGrade ≤ K) :
    ∃ y : M, R.Covers d (Fin.snoc c y) := by
  obtain ⟨k, t', c', e, hc', hcc', o, r, hs⟩ :=
    exists_covers_isSourceGapContextAt hα hR hcore hK hc
  obtain ⟨D', hD', hD'd, hsp⟩ := hsep t' _ _ o r (hR.isLegal _ _ hc'.eval_eq) hs t
    (restrictFace_of_covers' hR.isConsistent hc hc' hcc') d hd hdK
  obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
  rw [← hcc']
  exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
    (hrec.realizesOver_receivingFamily hc' hD' (isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩))
    (StageType.isDeterminedWithin_of_separatesThrough hs hD' hdK hD'd hsp hδ)

/-- **(R2) from (R1) and separated pinned extensions**: (R1) for every model at every limit stage
and the separated pinned extension property at every limit stage give (R2), through the compiled
residual acquisition of source-gap contexts.  The second hypothesis is false
(`SeparationObstruction.not_hasSeparatedPinnedExtensions`). -/
theorem residualReceiving_of_hasSeparatedPinnedExtensions
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hsep : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasSeparatedPinnedExtensions α) :
    ResidualReceiving.{u, w} :=
  residualReceiving_of_cutoffDetermination_isSourceGapContext hrec
    (cutoffDetermination_isSourceGapContext hsep)

end Realization

end VaughtConjecture
