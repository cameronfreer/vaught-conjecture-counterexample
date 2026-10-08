/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapReading

/-!
# Reading each new top at the cells labelled `⊤`

Roadmap, Layer 3 ((R2) of the table of 3.4); the reading pinned extensions of
`VaughtConjecture.Continuation.SourceGapReading`.

The cutoff form of determination keeps every label of the coface other than `⊤`
(`StageType.isDeterminedWithin_receivingFamily_of_forall_rowAt_le`), so a cell of full scope that
availability makes `⊤` in a member of the receiving family is labelled `⊤` in the coface itself.
So the reading of the new tops is needed only at the cells of full scope **labelled `⊤` in the
coface**.  In a leaf-and-marked layer, every catalogue entry is the entry of a leaf
(`Scheme.markedLayer_leaf_not_readsPairs`, in
`VaughtConjecture.Continuation.SourceGapReadingCatalogue`), so a reading asked at every cell of
full scope cannot come from such a layer when an entry does not read; the reading asked at the
cells labelled `⊤` can.

**Reading each new top at the tops** (`StageType.ReadsEachNewTopAtTops`): as
`StageType.ReadsEachNewTop`, with the reading asked only at the cells of graded index
`(univ, grade w)` labelled `⊤` in the coface.  It is implied by reading at every cell
(`StageType.ReadsEachNewTop.atTops`).

**The top-reading pinned extension property** (`StageType.HasTopReadingPinnedExtensions α`;
defined, open), with the quantifier order of `StageType.HasReadingPinnedExtensions`: one coface
per context and donor, the private cells chosen with each new top.  It follows from the reading
pinned extension property (`StageType.HasReadingPinnedExtensions.hasTopReadingPinnedExtensions`),
and gives (compiled in this repository) determination at a cutoff
(`StageType.ReadsEachNewTopAtTops.isDeterminedWithin`), cutoff determination for source-gap
contexts (`Realization.cutoffDetermination_isSourceGapContext_of_topReading`), exact residual
receiving in one model (`Realization.exists_covers_snoc_of_hasTopReadingPinnedExtensions`), and
(R2) at the countable block stages with (R1) in the library's form
(`Realization.blockResidualReceiving_of_hasTopReadingPinnedExtensions`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- A one-point coface `D'` of `t'` **reads each new top along `h` at its tops**: as
`ReadsEachNewTop`, with the reading asked only at the cells labelled `⊤` in `D'`. -/
def ReadsEachNewTopAtTops {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : restrictFace Fin.castSuccEmb D' = some t') (h : Fin n ↪ Fin k) : Prop :=
  ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
    D'.label x = ⊤ → ∃ w s : Fin t'.card, t'.label w = ⊤ ∧ t'.label s = ⊤ ∧
      t'.toCellScheme.grade s ≤ t'.toCellScheme.grade w ∧
      D'.toCellScheme.grade x ≤ t'.toCellScheme.grade w ∧
      ∀ u, D'.toCellScheme.gradedIndex u = (univ, t'.toCellScheme.grade w) → D'.label u = ⊤ →
        D'.rowAt u (faceCell hD' s) ≤ D'.rowAt u x

/-- Reading at every cell gives reading at the tops. -/
theorem ReadsEachNewTop.atTops {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    {hD' : restrictFace Fin.castSuccEmb D' = some t'} {h : Fin n ↪ Fin k}
    (hr : ReadsEachNewTop hD' h) : ReadsEachNewTopAtTops hD' h := fun x hx hxl hxt ↦
  let ⟨w, s, hw, hs, hsw, hxw, hu⟩ := hr x hx hxl hxt
  ⟨w, s, hw, hs, hsw, hxw, fun u hu' _ ↦ hu u hu'⟩

/-- **Stage types on one scheme with a common face agree at the cells visible through it.** -/
private theorem label_eq_of_restrictFace_eq {m : ℕ} {S : Scheme.{u} m}
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

/-- **Determination over a coface reading each new top at its tops**, at a cutoff above every
label of `D'` other than `⊤`.  In a member `q` of the receiving family, availability from the
private top `w` gives a cell `u` of graded index `(univ, grade w)` labelled `⊤` in `q`; its label
in `D'` is `⊤` (the cutoff keeps the other labels), so `u` reads the new top at least as `s`, and
the new top is `⊤` in `q` (`CellScheme.Rows.IsLawful.label_eq_top_of_row_le`). -/
theorem ReadsEachNewTopAtTops.isDeterminedWithin {t' : StageType.{u} α k}
    {D' : StageType.{u} α (k + 1)} (hD' : D' ∈ t'.cofaces) {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hD'd : restrictFace (extendByLast h) D' = some d)
    (hread : ReadsEachNewTopAtTops hD'.2 h) {δ : Ordinal.{u}}
    (hδ : ∀ j, D'.label j ≠ ⊤ → D'.label j < (δ : Label.{u})) :
    IsDeterminedWithin (receivingFamily D' δ) t' h d := fun q hq hqt ↦ by
  obtain ⟨hD'l, hD't'⟩ := hD'
  obtain ⟨hs, hl⟩ := hq
  -- the reading, unpacked through the faces of `D'`
  have hread' : ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
      D'.label x = ⊤ → ∃ w s, Fin.last k ∉ D'.toCellScheme.scope w ∧
        Fin.last k ∉ D'.toCellScheme.scope s ∧ D'.label w = ⊤ ∧ D'.label s = ⊤ ∧
        D'.toCellScheme.grade s ≤ D'.toCellScheme.grade w ∧
        D'.toCellScheme.grade x ≤ D'.toCellScheme.grade w ∧
        ∀ u, D'.toCellScheme.gradedIndex u = (univ, D'.toCellScheme.grade w) → D'.label u = ⊤ →
          D'.rowAt u s ≤ D'.rowAt u x := by
    intro x hx hxl hxt
    obtain ⟨w, s, hw, hs', hsw, hxw, hu⟩ := hread x hx hxl hxt
    refine ⟨faceCell hD't' w, faceCell hD't' s, last_notMem_scope_faceCell _ _,
      last_notMem_scope_faceCell _ _, by rw [label_faceCell, hw], by rw [label_faceCell, hs'],
      ?_, ?_, fun u hu' hut ↦ ?_⟩
    · rw [grade_faceCell, grade_faceCell]; exact hsw
    · rw [grade_faceCell]; exact hxw
    · rw [grade_faceCell] at hu'
      exact hu u hu' hut
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
  have hvis (x : Fin S.card) (hx : x ∈ S.visibleCells (extendByLast h)) : ℓ x = ℓ' x := by
    by_cases hxt : ℓ' x = ⊤
    · by_cases hxl : Fin.last k ∈ S.toCellScheme.scope x
      · obtain ⟨w, s, hwl, hsl, hwt, hst, hsw, hxw, hrd⟩ := hread' x hx hxl hxt
        rw [hxt]
        have hwq : ℓ w = ⊤ := (hpriv w hwl).trans hwt
        have hsq : ℓ s = ⊤ := (hpriv s hsl).trans hst
        -- a cell of graded index `(univ, grade w)` labelled `⊤` in `q`
        have hG : S.toCellScheme.grade w ≤ #(univ : Finset (Fin (k + 1))) := by
          rw [card_univ, Fintype.card_fin]
          exact (hw'.isWellFormed.grade_le_card w).trans ((card_le_univ _).trans_eq (by simp))
        obtain ⟨u₀, hu₀⟩ := hD'l.isComplete (univ, S.toCellScheme.grade w)
          ⟨hw'.univ_mem_faces, hw'.isWellFormed.grade_pos w, hG⟩
        obtain ⟨u, hu, hwu⟩ := hlaw.availability w u₀
          (by rw [show S.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
              exact subset_univ _)
          (congrArg Prod.snd hu₀).symm
        rw [hu₀] at hu
        rw [hwq, top_le_iff] at hwu
        -- its label in `D'` is `⊤`: the cutoff keeps the other labels
        have hu' : ℓ' u = ⊤ := by
          by_contra hne
          exact hne ((hnt u hne).symm.trans hwu)
        have hr := hrd u hu hu'
        have hb {y : Fin S.card} (hy : S.toCellScheme.grade y ≤ S.toCellScheme.grade w) :
            y ∈ S.toCellScheme.below (S.toCellScheme.gradedIndex u) := by
          rw [CellScheme.mem_below, hu]
          exact ⟨subset_univ _, hy⟩
        -- the rows of `q` and of `D'` are those of `S`
        change S.rowAt u s ≤ S.rowAt u x at hr
        rw [Scheme.rowAt_of_mem (hb hsw), Scheme.rowAt_of_mem (hb hxw)] at hr
        exact hlaw.label_eq_top_of_row_le (s := ⟨s, hb hsw⟩) (x := ⟨x, hb hxw⟩) hwu hsq hr
      · exact hpriv x hxl
    · exact hnt x hxt
  rw [← hD'd]
  by_cases hfm : univ.map (extendByLast h) ∈ S.toCellScheme.faces
  · rw [restrictFace_of_mem _ _ hfm, restrictFace_of_mem _ _ hfm]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    exact hvis _ (S.cellMap_mem _ i)
  · rw [restrictFace_of_notMem _ _ hfm, restrictFace_of_notMem _ _ hfm]

variable (α) in
/-- The **top-reading pinned extension property** at stage `α`: as
`HasReadingPinnedExtensions`, with the reading asked only at the cells labelled `⊤` in the
coface (`StageType.ReadsEachNewTopAtTops`).  Defined; open. -/
def HasTopReadingPinnedExtensions : Prop :=
  ∀ ⦃K n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (l : Fin k) (o r : Fin t'.card),
    t'.IsLegal → t'.IsSourceGapContextAt K h l o r → ∀ t : StageType.{u} α n,
      restrictFace h t' = some t → ∀ d ∈ t.cofaces, d.topGrade ≤ K →
        ∃ (D' : StageType.{u} α (k + 1)) (hD' : D' ∈ t'.cofaces),
          restrictFace (extendByLast h) D' = some d ∧ ReadsEachNewTopAtTops hD'.2 h

/-- Reading pinned extensions are top-reading pinned extensions. -/
theorem HasReadingPinnedExtensions.hasTopReadingPinnedExtensions
    (hr : HasReadingPinnedExtensions α) : HasTopReadingPinnedExtensions α :=
  fun _ _ _ t' h l o r ht' hs t ht d hd hdK ↦
    let ⟨D', hD', hD'd, hrd⟩ := hr t' h l o r ht' hs t ht d hd hdK
    ⟨D', hD', hD'd, hrd.atTops⟩

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type w} {R : Realization.{u, w} α M} {n : ℕ}

/-- **Cutoff determination for source-gap contexts from top-reading pinned extensions** at every
limit stage. -/
theorem cutoffDetermination_isSourceGapContext_of_topReading
    (hread : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α →
      StageType.HasTopReadingPinnedExtensions α) :
    CutoffDetermination.{u} fun K t' h ↦ t'.IsSourceGapContext K h where
  exists_coface _ _ _ _ t' h hα ht' hP t ht d hd hdK := by
    obtain ⟨l, o, r, hs⟩ := hP
    obtain ⟨D', hD', hD'd, hrd⟩ := hread hα t' h l o r ht' hs t ht d hd hdK
    obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
    exact ⟨D', hD', δ, isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩, hrd.isDeterminedWithin hD' hD'd hδ⟩

/-- **Exact residual receiving in one model from top-reading pinned extensions at its stage**,
with (R1) for that model only. -/
theorem exists_covers_snoc_of_hasTopReadingPinnedExtensions (hα : Order.IsSuccLimit α)
    (hR : R.IsModel) (hrec : R.HasFiniteCutReceiving)
    (hread : StageType.HasTopReadingPinnedExtensions α)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (hdK : d.topGrade ≤ K) :
    ∃ y : M, R.Covers d (Fin.snoc c y) := by
  obtain ⟨k, t', c', e, hc', hcc', o, r, hs⟩ :=
    exists_covers_isSourceGapContextAt hα hR hcore hK hc
  obtain ⟨D', hD', hD'd, hrd⟩ := hread t' _ _ o r (hR.isLegal _ _ hc'.eval_eq) hs t
    (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd hdK
  obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
  rw [← hcc']
  exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
    (hrec.realizesOver_receivingFamily hc' hD' (isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩))
    (hrd.isDeterminedWithin hD' hD'd hδ)

open Ordinal in
/-- **(R2) at the countable block stages from (R1) in the library's form and top-reading pinned
extensions at the countable block stages.** -/
theorem blockResidualReceiving_of_hasTopReadingPinnedExtensions
    (hrec : Expansion.FiniteCutReceiving.{w})
    (hread : ∀ ξ : Ordinal.{0}, ξ < ω₁ →
      StageType.HasTopReadingPinnedExtensions (blockStage ξ)) :
    BlockResidualReceiving.{w} where
  exists_covers ξ _ R _ hξ hR hcore hK _ _ _ hc _ hD hDK :=
    exists_covers_snoc_of_hasTopReadingPinnedExtensions (isSuccLimit_blockStage ξ) hR
      (hrec.receive (isSuccLimit_blockStage ξ) (blockStage_lt_omega_one hξ) R hR) (hread ξ hξ)
      hcore hK hc hD hDK

end Realization

end VaughtConjecture
