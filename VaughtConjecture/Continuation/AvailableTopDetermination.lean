/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.AnchoredDetermination
import VaughtConjecture.Extension.PinnedExtension

/-!
# Determination over anchored contexts with an available private top

Roadmap, Layer 3 ((R2) and (R3) of the table of 3.4, exact residual and exact hollow-growth
receiving; the private context of 3.3; the exact pinned extension of row 6); semantic contract,
items 5 and 8.

`VaughtConjecture.Continuation.AnchoredDetermination` reduces (R2) and (R3), given (R1) for every
model at every limit stage, to donor acquisition and cutoff determination with a donor for a
predicate on contexts, refutes determination for the anchored context
(`StageType.IsAnchoredContext`), and shows that a predicate `P` for which determination holds must
give, at a limit stage, over a legal context `t'` with `P t' h d` at a non-rigid donor `d` (a legal
one-point coface of the face of `t'` along `h` in which the root is not a rigid core), a legal
coface of `t'` carrying the donor with a private top available to a new cell
(`Realization.CutoffDonorDetermination.exists_hasAvailablePrivateTop`).  This file builds that
condition into the predicate, proves acquisition for it under the coatom extension property,
refutes determination for it, and isolates a further condition, on grades.  The refutation is of
this predicate, not of (R2) or (R3); (R2) and (R3) are still to be proved.

**The predicate.**  A stage type `t'` on `k` points is an **anchored context with a top** for a
one-point type `d` along `h : Fin n ↪ Fin k` (`StageType.IsAnchoredContextWithTop`) when it is an
anchored context for `d` and some legal one-point coface of `t'` has face `d` along `h` followed by
the new point and a private top available to a new cell (`StageType.HasAvailablePrivateTop`: a
cell labelled `⊤` avoiding the new point whose scope lies in the scope of a cell of the same grade
containing it).  In a legal coface every top of `t'` is available: completeness gives a cell of
graded index `(univ, g)` for its grade `g` (`StageType.hasAvailablePrivateTop_iff_not_isTopFree`).
So the predicate says: an anchored context, not top-free, with a legal one-point coface carrying
the donor (`StageType.isAnchoredContextWithTop_iff`).

**Acquisition** (`Realization.IsModel.exists_isAnchoredContextWithTop`).  Hypotheses, each used:

* modelhood at a nonzero stage: uniformity, high-arity dominance, and exact consistency for the
  anchored private context (`Realization.IsModel.exists_privateContext_isAnchored`, applied to an
  occurrence containing the cover), covering and exact consistency for an occurrence of top grade
  at least `N` containing the cover (`Realization.IsModel.exists_le_topGrade`), and legality of the
  types for the context;
* a natural number `1 ≤ N` at most the top-grade supremum, so that the context has top grade at
  least `N`, hence a cell labelled `⊤`.  In the residual case (no cover is a globally
  rigid core, top-grade supremum `K`) `K ≥ 1` (`Realization.IsModel.one_le_topGradeSup`); in the
  hollow case the supremum is `⊤`.  The top comes from an occurrence inside the context, not from
  the private cap; in the residual case its grade is at most `K`;
* the coatom extension property at the stage (`StageType.HasCoatomExtensions α`, [Kni26,
  Corollary 4.3.22] without the apex; still to be proved), for the coface carrying the donor: the
  exact pinned extension (`StageType.exists_pinned_extension`).  It is the plain form, not the
  form with the apex (`StageType.HasApexCoatomExtensions α`); the form with the apex implies it
  (`StageType.HasApexCoatomExtensions.hasCoatomExtensions`).

The last hypothesis is not particular to this predicate.  Determination at a coface needs the
coface to carry the donor (it is a member of its own receiving family), so for every predicate `P`
for which cutoff determination with a donor holds, at a limit stage, over a legal context `t'` with
`P t' h d` at a non-rigid donor `d` (a legal one-point coface of the face of `t'` along `h`), the
context has a legal one-point coface carrying the donor
(`Realization.CutoffDonorDetermination.exists_hasAvailablePrivateTop`).  The acquisition uses the
coatom extension property at every donor, the rigid ones included, at which determination asks
nothing.  The donor is not assumed realized over the cover, and (informally; no non-implication is
compiled) each route examined from the clauses of modelhood to such a coface uses a condition on
rows.  For contexts on at most three points the coface exists at every limit stage without
hypothesis (`AvailableTopDeterminationCounterexample.exists_pinned_extension_of_le_three`).  Given
the coatom extension property at every limit stage, donor acquisition holds in the residual case
(`Realization.donorAcquisition_isAnchoredContextWithTop`, every donor) and in the hollow case
(`Realization.donorAcquisition_isAnchoredContextWithTop_of_topGradeSup_eq_top`, a weakening of
the acquisition of the graded predicate below).

**Determination fails for this predicate**
(`AvailableTopDeterminationCounterexample.not_cutoffDonorDetermination`).  The failing clause is
the grade of the top.  If `d` has a new cell labelled `⊤` of grade above the top grade of `t'`,
then `d` is not determined over `t'` within the receiving family of any coface with face `t'`, at
any permitted cutoff (`StageType.not_isDeterminedWithin_receivingFamily_of_topGrade_lt`), nor within
the stage types on its scheme.  The new cells of grade above the top grade of `t'` form a set
closed upward in the graded order, and a cell outside it lying in the scope of a cell of it of the
same grade avoids the new point, so it is a cell of `t'` of grade above its top grade, not labelled
`⊤`; capping the set (`StageType.capOn`, `CellScheme.Rows.IsLawful.min_const_of_upper`) is lawful,
keeps the face `t'` and the receiving family, and lowers the new top.  The refuting instance has a
context on three points whose tops have grade `1` and a donor on two points with a new top of grade
`2`.

**What a predicate must have, refined.**  If cutoff determination with a donor holds for `P`, then
at a limit stage, over a legal context `t'` with `P t' h d` at a non-rigid donor `d` (a legal
one-point coface of the face of `t'` along `h`), every new top of `d` has grade at most the top
grade of `t'` (`Realization.CutoffDonorDetermination.grade_le_topGrade`), so the top grade of `d`
is at most that of `t'` (`Realization.CutoffDonorDetermination.topGrade_le`).  This sharpens
`Realization.CutoffDonorDetermination.not_isTopFree`, under the same hypotheses.  In the residual
case the top grade of `t'`, the type of a cover, is at most `K`, and (R2) concerns only donors of
top grade at most `K`.

**The graded predicate** (`StageType.IsGradedTopContext`): an anchored context with a top whose top
grade is at least that of the donor.

* Acquisition, under the coatom extension property at every limit stage: in the residual case for
  the donors of top grade at most `K` (`Realization.ResidualDonorAcquisition`, the form of donor
  acquisition that (R2) needs; `Realization.residualDonorAcquisition_isGradedTopContext`), and in
  the hollow case for every donor (`Realization.donorAcquisition_isGradedTopContext`).
* Determination: open.  It holds at a non-rigid donor of a compiled instance
  (`AvailableTopDeterminationCounterexample.exists_isGradedTopContext_isDeterminedWithin`).  A
  sufficient condition is compiled: a legal coface carrying the donor in which every cell of graded
  index `(univ, g)` reads each new top of the donor in its row at least as it reads a private top of
  grade `g` (`StageType.ReadsAtLeast`); availability makes one such cell `⊤` and locality then
  forces the new top (`StageType.ReadsAtLeast.label_eq_top`,
  `StageType.isDeterminedWithin_receivingFamily_of_readsAtLeast`,
  `Realization.cutoffDonorDetermination_isReadingContext`).  Passing from a graded context with a
  top to a reading context, and so acquisition of reading contexts, is an existence statement for
  a pinned extension with a condition on the rows of its new cells of full scope (open; not stated
  in the library).  Informally (no implication is compiled), this condition is of the same kind as
  the twin–gate coupling `CellScheme.Rows.TwinsReadGate` of the coupled gated pinned extension
  property (`StageType.HasCoupledGatedPinnedExtensions`), which is false at every stage above `1`
  (`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`).

**Templates** (`Realization.residualReceiving_of_residualDonorAcquisition`,
`Realization.residualReceiving_of_cutoffDonorDetermination_isGradedTopContext`,
`Realization.hollowReceiving_of_cutoffDonorDetermination_isGradedTopContext`).  (R2), and (R3) for
any predicate `H`, follow from (R1) for every model at every limit stage, the coatom extension
property at every limit stage, and cutoff determination with a donor for the graded predicate.  (R1)
is assumed in the universes of the conclusion, stronger in stage range than
`Expansion.FiniteCutReceiving` (limit stages below `ω₁`, universe `0`), which does not supply it;
the coatom extension property is still to be proved; determination for the graded predicate is
open.  These are templates, not reductions: the acquisitions are proved under the coatom extension
property; the other hypotheses are not.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

The private context is that of [Kni26, Lemma 8.1.1]; uniformity and high-arity dominance are
clauses 4(b) and 4(c) of [Kni26, Definition 3.2.1]; the coatom extension property is
[Kni26, Corollary 4.3.22] without the apex.
-/

universe u w

namespace VaughtConjecture

open Finset Label

variable {α : Ordinal.{u}} {n k : ℕ}

namespace StageType

/-! ### Available private tops in legal cofaces -/

/-- A point of a cell of the face along the initial segment is not the last point. -/
private theorem last_notMem_scope_cellMap_castSuccEmb (D : StageType.{u} α (k + 1))
    (i : Fin (D.toScheme.comap Fin.castSuccEmb).card) :
    Fin.last k ∉ D.toCellScheme.scope (D.cellMap Fin.castSuccEmb i) := fun hl ↦ by
  have hm := Scheme.mem_visibleCells.mp (D.cellMap_mem Fin.castSuccEmb i) (mem_coe.mpr hl)
  obtain ⟨j, hj⟩ := hm
  exact (Fin.castSucc_lt_last j).ne hj

/-- A cell whose scope avoids the last point is a cell of the face along the initial segment. -/
private theorem mem_range_cellMap_castSuccEmb {D : StageType.{u} α (k + 1)} {s : Fin D.card}
    (hs : Fin.last k ∉ D.toCellScheme.scope s) :
    s ∈ Set.range (D.cellMap Fin.castSuccEmb) := by
  rw [Scheme.range_cellMap]
  exact Scheme.mem_visibleCells.mpr fun x hx ↦ by
    have hxl : x ≠ Fin.last k := fun h ↦ hs (h ▸ hx)
    obtain ⟨y, rfl⟩ := Fin.exists_castSucc_eq.mpr hxl
    simp

/-- **In a legal coface every top of the private face is available to a new cell**: if a legal
`D'` has face `t'` along the initial segment, every cell of `t'` labelled `⊤` is a private top
available to a new cell of `D'`, the new cell being a cell of graded index `(univ, g)` for its
grade `g`, which exists by completeness. -/
theorem hasAvailablePrivateTop_of_label_eq_top {t' : StageType.{u} α k}
    {D' : StageType.{u} α (k + 1)} (hD' : D'.IsLegal)
    (hD't' : restrictFace Fin.castSuccEmb D' = some t') {i : Fin t'.card} (hi : t'.label i = ⊤) :
    D'.HasAvailablePrivateTop := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D' _).mp hD't'
  set s := D'.cellMap Fin.castSuccEmb i
  have hg : D'.toCellScheme.grade s ≤ #(univ : Finset (Fin (k + 1))) := by
    rw [card_univ, Fintype.card_fin]
    exact D'.grade_le s
  obtain ⟨s', hs'⟩ := (isLegal_iff.mp hD').2.2 (univ, D'.toCellScheme.grade s)
    ⟨D'.univ_mem_faces, D'.isWellFormed.isWellFormed.grade_pos s, hg⟩
  have hscope : D'.toCellScheme.scope s' = univ := congrArg Prod.fst hs'
  have hgrade : D'.toCellScheme.grade s' = D'.toCellScheme.grade s := congrArg Prod.snd hs'
  exact ⟨s, s', hscope ▸ subset_univ _, hgrade.symm,
    last_notMem_scope_cellMap_castSuccEmb D' i, hscope ▸ mem_univ _, hi⟩

/-- **For a legal coface, an available private top is a top of the private face**: a legal `D'`
with face `t'` along the initial segment has a private top available to a new cell exactly when
`t'` is not top-free. -/
theorem hasAvailablePrivateTop_iff_not_isTopFree {t' : StageType.{u} α k}
    {D' : StageType.{u} α (k + 1)} (hD' : D'.IsLegal)
    (hD't' : restrictFace Fin.castSuccEmb D' = some t') :
    D'.HasAvailablePrivateTop ↔ ¬ t'.IsTopFree := by
  refine ⟨fun hav htf ↦ not_hasAvailablePrivateTop_of_isTopFree hD't' htf hav, fun h ↦ ?_⟩
  simp only [IsTopFree, not_forall, not_not] at h
  obtain ⟨i, hi⟩ := h
  exact hasAvailablePrivateTop_of_label_eq_top hD' hD't' hi

/-! ### Capping the new cells above the top grade of the private face -/

/-- **No determination of a new top above the top grade of the context.**  At a limit stage, let
`D'` have face `t'` along the initial segment, and let `d` have a new cell labelled `⊤` whose grade
exceeds the top grade of `t'`.  Then for every `h` and every permitted cutoff `δ`, `d` is not
determined over `t'` along `h` within the receiving family of `D'` at `δ`.  The cells of `D'`
containing the new point and of grade above the top grade of `t'` form a set closed upward in the
graded order; a cell outside it in the scope of a cell of it of the same grade avoids the new point,
so it is a cell of `t'` of grade above its top grade, not labelled `⊤`.  Capping that set at an
ordinal above every proper label of `D'` and the cutoff is lawful (`StageType.capOn`), keeps the
face `t'` and the receiving family, and lowers the new top of `d` to an ordinal. -/
theorem not_isDeterminedWithin_receivingFamily_of_topGrade_lt
    (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : restrictFace Fin.castSuccEmb D' = some t') {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)}
    (hd : ∃ j, Fin.last n ∈ d.toCellScheme.scope j ∧ t'.topGrade < d.toCellScheme.grade j ∧
      d.label j = ⊤) {δ : Label.{u}} (hδ : IsPermittedCutoff α δ) :
    ¬ IsDeterminedWithin (receivingFamily D' δ) t' h d := by
  intro hdet
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D' _).mp hD'
  obtain ⟨o₀, ho₀, rfl⟩ := isPermittedCutoff_iff.mp hδ
  obtain ⟨o, hoα, ho⟩ := D'.exists_label_le hα.bot_lt
  obtain ⟨c, hoc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit (max_lt hoα ho₀) (k + 1)
  have hoc' : ((o : Ordinal.{u}) : Label.{u}) ≤ c := by
    exact_mod_cast (le_max_left o o₀).trans hoc.le
  have ho₀c : ((o₀ : Ordinal.{u}) : Label.{u}) ≤ c := by
    exact_mod_cast (le_max_right o o₀).trans hoc.le
  set G := (D'.comap Fin.castSuccEmb hf).topGrade
  -- the new cells of grade above `G` form an upper set
  have hZ : ∀ x s, (Fin.last k ∈ D'.toCellScheme.scope x ∧ G < D'.toCellScheme.grade x) →
      D'.toCellScheme.gradedIndex x ≤ D'.toCellScheme.gradedIndex s →
        Fin.last k ∈ D'.toCellScheme.scope s ∧ G < D'.toCellScheme.grade s :=
    fun _ _ hx hle ↦ ⟨hle.1 hx.1, hx.2.trans_le hle.2⟩
  -- availability carries no top into it: the cells outside it in question are private
  have hav : ∀ s s', D'.toCellScheme.scope s ⊆ D'.toCellScheme.scope s' →
      D'.toCellScheme.grade s = D'.toCellScheme.grade s' →
      ¬ (Fin.last k ∈ D'.toCellScheme.scope s ∧ G < D'.toCellScheme.grade s) →
      (Fin.last k ∈ D'.toCellScheme.scope s' ∧ G < D'.toCellScheme.grade s') →
        D'.label s ≤ c := by
    intro s s' _ hg hs hs'
    have hl : Fin.last k ∉ D'.toCellScheme.scope s := fun hl ↦ hs ⟨hl, hg ▸ hs'.2⟩
    refine (ho s fun htop ↦ ?_).trans hoc'
    obtain ⟨i, rfl⟩ := mem_range_cellMap_castSuccEmb hl
    -- the private cell `i` is labelled `⊤`, so its grade is at most the top grade `G`
    have hle := grade_le_topGrade (t := D'.comap Fin.castSuccEmb hf) (d := i) htop
    exact absurd ((hg ▸ hs'.2).trans_le hle) (lt_irrefl _)
  set q := D'.capOn (fun x ↦ Fin.last k ∈ D'.toCellScheme.scope x ∧
    G < D'.toCellScheme.grade x) c hc hcα hZ hav
  have hq : q ∈ receivingFamily D' o₀ := by
    refine ⟨rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    -- unfold the label of `q` at `i` inside the cutoff (`StageType.capOn_label` does not apply
    -- here: `i` is a cell of `D'`, a cell of `q` only up to unfolding)
    change min (if Fin.last k ∈ D'.toCellScheme.scope i ∧ G < D'.toCellScheme.grade i then
      min (D'.label i) c else D'.label i) _ = _
    split_ifs
    · rw [min_assoc, min_eq_right ho₀c]
    · rfl
  have hqt : restrictFace Fin.castSuccEmb q = some (D'.comap Fin.castSuccEmb hf) := by
    rw [restrictFace_capOn fun x hx hZx ↦ ?_]
    · exact hD'
    obtain ⟨i, rfl⟩ : x ∈ Set.range (D'.cellMap Fin.castSuccEmb) := by
      rw [Scheme.range_cellMap]; exact hx
    exact last_notMem_scope_cellMap_castSuccEmb D' i hZx.1
  obtain ⟨j, hjs, hjg, hjt⟩ := hd
  obtain ⟨hf', rfl⟩ := (restrictFace_eq_some_iff D' _).mp
    (hdet D' (self_mem_receivingFamily D' _) hD')
  obtain ⟨hfq, hq'⟩ := (restrictFace_eq_some_iff q _).mp (hdet q hq hqt)
  -- the cell of `D'` under `j` contains the new point, has grade above `G`, and is labelled `⊤`
  set x := D'.cellMap (extendByLast h) j
  have hlast : Fin.last k ∈ D'.toCellScheme.scope x := by
    have hm := Scheme.map_comap_scope D'.toScheme (extendByLast h) j
    rw [← hm, ← extendByLast_last h]
    exact mem_map_of_mem _ hjs
  have hl := label_congr hq' (i := j) (j := j) rfl
  -- `q` has the scheme of `D'`, so its cell under `j` is `x`; unfold its label there (by `change`:
  -- `StageType.capOn_label` does not apply at a cell of `D'`), and the label and grade of `d` at
  -- `j` as those of `D'` at `x`
  change (if Fin.last k ∈ D'.toCellScheme.scope x ∧ G < D'.toCellScheme.grade x then
    min (D'.label x) c else D'.label x) = D'.label x at hl
  change D'.label x = ⊤ at hjt
  change G < D'.toCellScheme.grade x at hjg
  simp only [hlast, hjg, and_self, ↓reduceIte, hjt, min_top_left] at hl
  exact WithBot.coe_injective.ne WithTop.coe_ne_top hl

/-- **No determination of a new top above the top grade of the context by a scheme**: under the
hypotheses of `not_isDeterminedWithin_receivingFamily_of_topGrade_lt`, `d` is not determined within
the stage types on the scheme of `D'` either, which contain its receiving families. -/
theorem not_isDeterminedWithin_saturationFamily_of_topGrade_lt
    (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : restrictFace Fin.castSuccEmb D' = some t') {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)}
    (hd : ∃ j, Fin.last n ∈ d.toCellScheme.scope j ∧ t'.topGrade < d.toCellScheme.grade j ∧
      d.label j = ⊤) :
    ¬ IsDeterminedWithin (saturationFamily D'.toScheme) t' h d := fun hdet ↦
  not_isDeterminedWithin_receivingFamily_of_topGrade_lt hα hD' hd
    (isPermittedCutoff_iff.mpr ⟨0, hα.bot_lt, rfl⟩)
    (hdet.mono (receivingFamily_subset_saturationFamily (d := D') rfl _))

/-- **The top grade of a one-point coface is bounded by its new tops and its root**: if the new
cells of `d` labelled `⊤` have grade at most `N` and the root `t` of `d` has top grade at most `N`,
then so does `d`.  A cell avoiding the new point is a cell of the root. -/
theorem topGrade_le_of_forall_new {d : StageType.{u} α (n + 1)} {t : StageType.{u} α n}
    (hdt : restrictFace Fin.castSuccEmb d = some t) {N : ℕ} (htN : t.topGrade ≤ N)
    (hnew : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ →
      d.toCellScheme.grade j ≤ N) : d.topGrade ≤ N := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff d _).mp hdt
  refine topGrade_le_iff.mpr fun j hj ↦ ?_
  by_cases hl : Fin.last n ∈ d.toCellScheme.scope j
  · exact hnew j hl hj
  · obtain ⟨i, rfl⟩ := mem_range_cellMap_castSuccEmb hl
    exact (grade_le_topGrade (t := d.comap Fin.castSuccEmb hf) (d := i) hj).trans htN

/-! ### The anchored context with a top -/

/-- A stage type `t'` on `k` points is an **anchored context with a top** for a one-point type `d`
along `h`: an anchored context for `d` (`StageType.IsAnchoredContext`) with a legal one-point
coface carrying `d` along `h` followed by the new point that has a private top available to a new
cell (`StageType.HasAvailablePrivateTop`). -/
def IsAnchoredContextWithTop (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) : Prop :=
  t'.IsAnchoredContext d ∧ ∃ D' ∈ t'.cofaces, restrictFace (extendByLast h) D' = some d ∧
    D'.HasAvailablePrivateTop

/-- **An anchored context with a top is an anchored context that is not top-free and has a legal
one-point coface carrying the donor**: the available private top is any top of the context, by
completeness of the coface (`StageType.hasAvailablePrivateTop_iff_not_isTopFree`). -/
theorem isAnchoredContextWithTop_iff {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} :
    t'.IsAnchoredContextWithTop h d ↔ t'.IsAnchoredContext d ∧ ¬ t'.IsTopFree ∧
      ∃ D' ∈ t'.cofaces, restrictFace (extendByLast h) D' = some d := by
  refine ⟨fun ⟨hanc, D', hD', hD'd, hav⟩ ↦ ⟨hanc,
    (hasAvailablePrivateTop_iff_not_isTopFree hD'.1 hD'.2).mp hav, D', hD', hD'd⟩,
    fun ⟨hanc, htf, D', hD', hD'd⟩ ↦ ⟨hanc, D', hD', hD'd,
      (hasAvailablePrivateTop_iff_not_isTopFree hD'.1 hD'.2).mpr htf⟩⟩

/-- A stage type `t'` is a **graded anchored context with a top** for `d` along `h`: an anchored
context with a top whose top grade is at least that of `d`. -/
def IsGradedTopContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) : Prop :=
  t'.IsAnchoredContextWithTop h d ∧ d.topGrade ≤ t'.topGrade

/-! ### Reading the new tops through a private top -/

/-- A stage type `D` **reads the cell `x` at least as the cell `s`**: `x` has grade at most that of
`s`, and every cell of graded index `(univ, g)`, for `g` the grade of `s`, reads `x` in its row at
least as it reads `s`. -/
def ReadsAtLeast {m : ℕ} (D : StageType.{u} α m) (s x : Fin D.card) : Prop :=
  D.toCellScheme.grade x ≤ D.toCellScheme.grade s ∧
    ∀ u, D.toCellScheme.gradedIndex u = (univ, D.toCellScheme.grade s) →
      ∀ a b : D.toCellScheme.below (D.toCellScheme.gradedIndex u), a.1 = s → b.1 = x →
        D.rows.row u a ≤ D.rows.row u b

/-- **A top read at least as a top is a top**: in a legal stage type `D`, if `D` reads `x` at least
as `s` and `s` is labelled `⊤`, then `x` is labelled `⊤`.  By completeness some cell has graded
index `(univ, g)`, `g` the grade of `s`; availability makes a cell `u` of that graded index `⊤`;
locality at `u` reads `s` as `⊤`, so its shifter is `⊤` at the row value of `s` and its suppressor
is `⊤` at `g`, and the shifter is monotone and the suppressor antitone. -/
theorem ReadsAtLeast.label_eq_top {m : ℕ} {D : StageType.{u} α m} (hD : D.IsLegal)
    {s x : Fin D.card} (hread : D.ReadsAtLeast s x) (hs : D.label s = ⊤) : D.label x = ⊤ := by
  obtain ⟨hgx, hrow⟩ := hread
  have hg : D.toCellScheme.grade s ≤ #(univ : Finset (Fin m)) := by
    rw [card_univ, Fintype.card_fin]
    exact D.grade_le s
  obtain ⟨u₀, hu₀⟩ := (isLegal_iff.mp hD).2.2 (univ, D.toCellScheme.grade s)
    ⟨D.univ_mem_faces, D.isWellFormed.isWellFormed.grade_pos s, hg⟩
  have hsc : D.toCellScheme.scope s ⊆ D.toCellScheme.scope u₀ := by
    have hsu₀ : D.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
    rw [hsu₀]
    exact subset_univ _
  obtain ⟨u, hu, hsu⟩ := D.isLawful.availability s u₀ hsc (congrArg Prod.snd hu₀).symm
  rw [hu₀] at hu
  rw [hs, top_le_iff] at hsu
  obtain ⟨g, σ, hw, heq⟩ := D.isLawful.locality u
  have hsb : s ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
    rw [hu]
    exact ⟨subset_univ _, le_rfl⟩
  have hxb : x ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
    rw [hu]
    exact ⟨subset_univ _, hgx⟩
  have hes := heq ⟨s, hsb⟩
  have hex := heq ⟨x, hxb⟩
  simp only [hs, hsu, min_self] at hes
  simp only [hsu, min_top_right] at hex
  have hσ : σ (D.rows.row u ⟨s, hsb⟩) = ⊤ := (_root_.min_eq_top.mp hes.symm).1
  have hgs : g (D.toCellScheme.grade s) = ⊤ := (_root_.min_eq_top.mp hes.symm).2
  rw [hex, _root_.min_eq_top]
  exact ⟨top_le_iff.mp (hσ ▸ hw.monotone (hrow u hu ⟨s, hsb⟩ ⟨x, hxb⟩ rfl rfl)),
    top_le_iff.mp (hgs ▸ hw.antitone hgx)⟩

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

/-- **Determination over a reading coface.**  Let a legal `D'` have face `t'` along the initial
segment and `d` along `h` followed by the new point, and suppose every new cell of `D'` visible in
that face and labelled `⊤` is read at least as some private cell labelled `⊤`
(`StageType.ReadsAtLeast`).  Then `d` is determined over `t'` along `h` within the receiving family
of `D'` at a cutoff above every label of `D'` other than `⊤`: the labels other than `⊤` are kept
by the cutoff, the private tops by the face `t'`, and the new tops are forced by
`StageType.ReadsAtLeast.label_eq_top`. -/
theorem isDeterminedWithin_receivingFamily_of_readsAtLeast {t' : StageType.{u} α k}
    {D' : StageType.{u} α (k + 1)} (hD' : D'.IsLegal)
    (hD't' : restrictFace Fin.castSuccEmb D' = some t') {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (hD'd : restrictFace (extendByLast h) D' = some d)
    (hread : ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
      D'.label x = ⊤ → ∃ s, Fin.last k ∉ D'.toCellScheme.scope s ∧ D'.label s = ⊤ ∧
        D'.ReadsAtLeast s x)
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
  -- the private cells are kept
  have hpriv (y : Fin S.card) (hy : Fin.last k ∉ S.toCellScheme.scope y) : ℓ y = ℓ' y :=
    label_eq_of_restrictFace_eq hqt hD't' (Scheme.mem_visibleCells.mpr fun z hz ↦
      Fin.exists_castSucc_eq.mpr fun hzl ↦ hy (hzl ▸ hz))
  -- legality concerns only the scheme
  have hq' : (⟨S, ℓ, hw, hc, hlaw, hat⟩ : StageType.{u} α (k + 1)).IsLegal := hD'
  have hvis (x : Fin S.card) (hx : x ∈ S.visibleCells (extendByLast h)) : ℓ x = ℓ' x := by
    by_cases hxt : ℓ' x = ⊤
    · by_cases hxl : Fin.last k ∈ S.toCellScheme.scope x
      · obtain ⟨s, hsl, hst, hsx⟩ := hread x hx hxl hxt
        rw [hxt]
        refine ReadsAtLeast.label_eq_top (D := ⟨S, ℓ, hw, hc, hlaw, hat⟩) hq' hsx ?_
        exact (hpriv s hsl).trans hst
      · exact hpriv x hxl
    · exact hnt x hxt
  rw [← hD'd]
  by_cases hfm : univ.map (extendByLast h) ∈ S.toCellScheme.faces
  · rw [restrictFace_of_mem _ _ hfm, restrictFace_of_mem _ _ hfm]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    obtain rfl : i = j := Fin.ext hij
    exact hvis _ (S.cellMap_mem _ i)
  · rw [restrictFace_of_notMem _ _ hfm, restrictFace_of_notMem _ _ hfm]

/-- A stage type `t'` is a **reading context** for `d` along `h`: some legal one-point coface of
`t'` has face `d` along `h` followed by the new point, and reads each of its new cells visible in
that face and labelled `⊤` at least as some private cell labelled `⊤`
(`StageType.ReadsAtLeast`). -/
def IsReadingContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1)) :
    Prop :=
  ∃ D' ∈ t'.cofaces, restrictFace (extendByLast h) D' = some d ∧
    ∀ x ∈ D'.visibleCells (extendByLast h), Fin.last k ∈ D'.toCellScheme.scope x →
      D'.label x = ⊤ → ∃ s, Fin.last k ∉ D'.toCellScheme.scope s ∧ D'.label s = ⊤ ∧
        D'.ReadsAtLeast s x

end StageType

namespace Realization

variable {M : Type w} {R : Realization.{u, w} α M}

/-! ### What determination needs: the grades of the new tops -/

/-- **Determination needs the context to reach the grades of the new tops**: if cutoff
determination with a donor holds for `P` at a limit stage, then over every legal `t'` with face `t`
along `h`, and every legal non-rigid one-point coface `d` of `t` with `P t' h d`, every new cell of
`d` labelled `⊤` has grade at most the top grade of `t'`. -/
theorem CutoffDonorDetermination.grade_le_topGrade
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hdet : CutoffDonorDetermination.{u} P) (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k}
    (ht' : t'.IsLegal) {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} (hP : P t' h d)
    {t : StageType.{u} α n} (ht : StageType.restrictFace h t' = some t) (hd : d ∈ t.cofaces)
    (hnr : ¬ d.IsRigidCoreIn Fin.castSuccEmb) {j : Fin d.card}
    (hj : Fin.last n ∈ d.toCellScheme.scope j) (htop : d.label j = ⊤) :
    d.toCellScheme.grade j ≤ t'.topGrade := by
  by_contra hlt
  obtain ⟨D', hD', δ, hδ, hdet'⟩ := hdet.exists_coface t' h d hα ht' hP t ht hd hnr
  exact StageType.not_isDeterminedWithin_receivingFamily_of_topGrade_lt hα hD'.2
    ⟨j, hj, not_le.mp hlt, htop⟩ hδ hdet'

/-- **Determination needs the context to reach the top grade of the donor**: under cutoff
determination with a donor for `P` at a limit stage, over a legal `t'`, the top grade of a legal
non-rigid one-point coface `d` of its face along `h` with `P t' h d` is at most that of `t'`.  The
new tops by `CutoffDonorDetermination.grade_le_topGrade`; the root tops are
tops of `t'`. -/
theorem CutoffDonorDetermination.topGrade_le
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hdet : CutoffDonorDetermination.{u} P) (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k}
    (ht' : t'.IsLegal) {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} (hP : P t' h d)
    {t : StageType.{u} α n} (ht : StageType.restrictFace h t' = some t) (hd : d ∈ t.cofaces)
    (hnr : ¬ d.IsRigidCoreIn Fin.castSuccEmb) : d.topGrade ≤ t'.topGrade :=
  StageType.topGrade_le_of_forall_new hd.2 (StageType.topGrade_le_of_restrictFace ht)
    fun _ hj htop ↦ hdet.grade_le_topGrade hα ht' hP ht hd hnr hj htop

/-- **Cutoff determination with a donor holds for reading contexts**
(`StageType.IsReadingContext`), at a cutoff above every label of the coface other than `⊤`, at
every coface, rigid or not.  A diagnosis, not a reduction: acquisition of reading contexts is not
proved. -/
theorem cutoffDonorDetermination_isReadingContext :
    CutoffDonorDetermination.{u} fun t' h d ↦ t'.IsReadingContext h d where
  exists_coface _ _ _ t' h d hα _ hP _ _ _ _ := by
    obtain ⟨D', hD', hD'd, hread⟩ := hP
    obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
    exact ⟨D', hD', δ, isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩,
      StageType.isDeterminedWithin_receivingFamily_of_readsAtLeast hD'.1 hD'.2 hD'd hread hδ⟩

/-! ### Acquisition -/

/-- **Occurrences of large top grade**: in a model, if `N` is at most the top-grade supremum, every
occurrence lies in one of top grade at least `N`.  Some occurrence has top grade at least `N` (the
supremum is attained when finite), and by covering and exact consistency an occurrence containing
both has top grade at least as large (`Realization.Occurrence.topGrade_mono`). -/
theorem IsModel.exists_le_topGrade (hR : R.IsModel) {N : ℕ} (hN : (N : ℕ∞) ≤ R.topGradeSup)
    (x : R.Occurrence) : ∃ y : R.Occurrence, x ≤ y ∧ N ≤ y.type.topGrade := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : R.Occurrence, N ≤ z.type.topGrade := by
    rcases eq_or_ne R.topGradeSup ⊤ with htop | htop
    · have hlt : (N : ℕ∞) < ⨆ z : R.Occurrence, (z.type.topGrade : ℕ∞) := by
        change (N : ℕ∞) < R.topGradeSup
        rw [htop]
        exact ENat.natCast_lt_top N
      obtain ⟨z, hz⟩ := lt_iSup_iff.mp hlt
      exact ⟨z, by exact_mod_cast hz.le⟩
    · have := hR.nonempty_occurrence
      obtain ⟨z, hz⟩ := ENat.exists_eq_iSup_of_lt_top
        (f := fun y : R.Occurrence ↦ (y.type.topGrade : ℕ∞)) (lt_top_iff_ne_top.mpr htop)
      refine ⟨z, ?_⟩
      have : (N : ℕ∞) ≤ (z.type.topGrade : ℕ∞) := hN.trans hz.symm.le
      exact_mod_cast this
  obtain ⟨y, hy⟩ := hR.isCovering.exists_subset_support (x.support ∪ z.support)
  exact ⟨y, subset_union_left.trans hy,
    hz.trans (Occurrence.topGrade_mono hR.isConsistent (subset_union_right.trans hy))⟩

/-- **Acquisition of an anchored context with a top**, under the coatom extension property: in a
model at a nonzero stage `α` at which `StageType.HasCoatomExtensions α` holds, for every `N ≥ 1`
at most the top-grade supremum, every cover `c` of `t` and every legal one-point coface `d` of `t`
give a cover `c'` of an anchored context with a top `t'` for `d` along some `h` with `c' ∘ h = c`
and top grade at least `N`.  The anchored private context
(`Realization.IsModel.exists_privateContext_isAnchored`) is taken over an occurrence containing
the cover and one of top grade at least `N` (`Realization.IsModel.exists_le_topGrade`); the coface
carrying the donor is the exact pinned extension (`StageType.exists_pinned_extension`), and its
private top is available by completeness. -/
theorem IsModel.exists_isAnchoredContextWithTop (hR : R.IsModel) (hα : 0 < α)
    (hext : StageType.HasCoatomExtensions.{u} α) {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) {N : ℕ}
    (hN : (N : ℕ∞) ≤ R.topGradeSup) (hN1 : 0 < N) :
    ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ h = c ∧ t'.IsAnchoredContextWithTop h d ∧ N ≤ t'.topGrade := by
  set x : R.Occurrence := ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩
  obtain ⟨x₀, hxx₀, hx₀⟩ := hR.exists_le_topGrade hN x
  obtain ⟨e, he, -⟩ := (Occurrence.le_iff_exists_restrictFace hR.isConsistent).mp hxx₀
  obtain ⟨o, hoα, ho⟩ := d.exists_label_le hα
  obtain ⟨y, f, C, hf, hfy, hn, hC, hoC, hanc⟩ := hR.exists_privateContext_isAnchored x₀ d hoα
  have hcc' : y.tuple ∘ (e.trans f) = c := by
    funext i
    have h₁ := DFunLike.congr_fun hf (e i)
    have h₂ := DFunLike.congr_fun he i
    simp only [Function.Embedding.trans_apply] at h₁ h₂
    simp only [Function.comp_apply, Function.Embedding.trans_apply, h₁, h₂]
    rfl
  have hc' : R.Covers y.type y.tuple := covers_of_eval _ y.eval_tuple
  have ht' := restrictFace_of_covers hR.isConsistent hc hc' hcc'
  obtain ⟨D', hD', hD't', hD'd⟩ :=
    StageType.exists_pinned_extension hext (hR.isLegal _ _ y.eval_tuple) ht' hd.1 hd.2
  have htopy : N ≤ y.type.topGrade := hx₀.trans (StageType.topGrade_le_of_restrictFace hfy)
  have hntf : ¬ y.type.IsTopFree := fun htf ↦ by
    rw [← StageType.topGrade_eq_zero_iff] at htf
    omega
  have hnx : n ≤ x₀.arity := by simpa using Fintype.card_le_of_embedding e
  exact ⟨y.arity, y.type, y.tuple, e.trans f, hc', hcc',
    StageType.isAnchoredContextWithTop_iff.mpr ⟨⟨by omega, C, hC,
      fun j hj ↦ (ho j hj).trans_lt hoC, hanc⟩, hntf, D', ⟨hD', hD't'⟩, hD'd⟩, htopy⟩

/-- In a model at a limit stage with no cover that is a globally rigid core, the top-grade
supremum is not `0`: otherwise the empty tuple is a globally rigid core
(`Realization.IsModel.isGloballyRigidCore_empty_iff`). -/
theorem IsModel.one_le_topGradeSup (hR : R.IsModel) (hα : Order.IsSuccLimit α)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c) : (1 : ℕ∞) ≤ R.topGradeSup := by
  refine Order.one_le_iff_ne_zero.mpr fun h0 ↦ hcore ?_
  obtain ⟨p, hp⟩ := hR.exists_covers_zero
  exact ⟨0, p, ![], hp, (hR.isGloballyRigidCore_empty_iff hα).mpr h0⟩

/-- **Donor acquisition of anchored contexts with a top in the residual case**, under the coatom
extension property at every limit stage: in every model at a limit stage with no cover that is a
globally rigid core.  The top-grade supremum is then at least `1`. -/
theorem donorAcquisition_isAnchoredContextWithTop
    (hext : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasCoatomExtensions.{u} α) :
    DonorAcquisition.{u, w} (fun {α} {M} R ↦ ¬ ∃ (k : ℕ) (p : StageType.{u} α k)
      (c : Fin k → M), R.Covers p c ∧ R.IsGloballyRigidCore c)
      fun t' h d ↦ t'.IsAnchoredContextWithTop h d where
  exists_context _ _ _ hα hR hcore _ _ _ hc _ hd :=
    let ⟨k, t', c', h, hc', hcc', hP, _⟩ := hR.exists_isAnchoredContextWithTop hα.bot_lt
      (hext hα) hc hd (hR.one_le_topGradeSup hα hcore) one_pos
    ⟨k, t', c', h, hc', hcc', hP⟩

/-- **Acquisition of a graded anchored context with a top**: under the hypotheses of
`Realization.IsModel.exists_isAnchoredContextWithTop`, if the top grade of the donor and `1` are
at most the top-grade supremum, the context can be taken of top grade at least that of the donor
(`StageType.IsGradedTopContext`). -/
theorem IsModel.exists_isGradedTopContext (hR : R.IsModel) (hα : 0 < α)
    (hext : StageType.HasCoatomExtensions.{u} α) {t : StageType.{u} α n} {c : Fin n → M}
    (hc : R.Covers t c) {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces)
    (h1 : (1 : ℕ∞) ≤ R.topGradeSup) (hdN : (d.topGrade : ℕ∞) ≤ R.topGradeSup) :
    ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ h = c ∧ t'.IsGradedTopContext h d := by
  obtain ⟨k, t', c', h, hc', hcc', hP, hN⟩ := hR.exists_isAnchoredContextWithTop hα hext hc hd
    (N := max 1 d.topGrade)
    (by rcases max_cases 1 d.topGrade with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> assumption_mod_cast)
    (lt_max_of_lt_left one_pos)
  exact ⟨k, t', c', h, hc', hcc', hP, (le_max_right _ _).trans hN⟩

/-- **Donor acquisition of graded anchored contexts with a top in the hollow case**, under the
coatom extension property at every limit stage: in every model at a limit stage satisfying any
`H` with top-grade supremum `⊤`. -/
theorem donorAcquisition_isGradedTopContext
    (hext : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasCoatomExtensions.{u} α)
    (H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop) :
    DonorAcquisition.{u, w} (fun R ↦ H R ∧ R.topGradeSup = ⊤)
      fun t' h d ↦ t'.IsGradedTopContext h d where
  exists_context _ _ _ hα hR hH _ _ _ hc _ hd :=
    hR.exists_isGradedTopContext hα.bot_lt (hext hα) hc hd (hH.2 ▸ le_top) (hH.2 ▸ le_top)

/-- **Donor acquisition of anchored contexts with a top in the hollow case**, under the coatom
extension property at every limit stage: in every model at a limit stage satisfying any `H` with
top-grade supremum `⊤`.  A weakening of `Realization.donorAcquisition_isGradedTopContext`. -/
theorem donorAcquisition_isAnchoredContextWithTop_of_topGradeSup_eq_top
    (hext : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasCoatomExtensions.{u} α)
    (H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop) :
    DonorAcquisition.{u, w} (fun R ↦ H R ∧ R.topGradeSup = ⊤)
      fun t' h d ↦ t'.IsAnchoredContextWithTop h d where
  exists_context _ _ _ hα hR hH _ t c hc d hd :=
    let ⟨k, t', c', h, hc', hcc', hP⟩ :=
      (donorAcquisition_isGradedTopContext hext H).exists_context hα hR hH t c hc d hd
    ⟨k, t', c', h, hc', hcc', hP.1⟩

/-! ### The residual template with donors of bounded top grade -/

/-- **Residual donor acquisition** for a predicate `P` on contexts and donors: in every model at a
limit stage with no cover that is a globally rigid core and with top-grade supremum `K`, every
cover `c` of a stage type `t` and every one-point coface `d` of `t` of top grade at most `K` give a
cover `c'` of some `t'` along some `h` (`c' ∘ h = c`) with `P t' h d`.  A statement about models;
(R2) concerns only the donors of top grade at most `K` (`Realization.ResidualReceiving`). -/
structure ResidualDonorAcquisition
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop where
  /-- Every cover and donor of top grade at most `K` give a cover of an acquired context. -/
  exists_context ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄ :
    Order.IsSuccLimit α → R.IsModel →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∀ d ∈ t.cofaces, d.topGrade ≤ K →
          ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
            R.Covers t' c' ∧ c' ∘ h = c ∧ P t' h d

/-- **(R2) from (R1), residual donor acquisition, and cutoff determination with a donor**, for any
`P`.  (R1) is assumed for every model at every limit stage, in the universes of the conclusion:
stronger in stage range than `Expansion.FiniteCutReceiving` (limit stages below `ω₁`, universe
`0`), which does not supply it.  A template: no predicate is known for which both other hypotheses
hold. -/
theorem residualReceiving_of_residualDonorAcquisition
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hacq : ResidualDonorAcquisition.{u, w} P) (hdet : CutoffDonorDetermination.{u} P) :
    ResidualReceiving.{u, w} :=
  ResidualReceiving.of_not_isRigidCoreIn hrec fun _ _ _ _ hα hR hcore hK _ t c hc d hd hdK hnr ↦
    exists_covers_snoc_of_cutoffDonorDetermination hdet hα hR (hrec hα hR) hc hd hnr
      (hacq.exists_context hα hR hcore hK t c hc d hd hdK)

/-- **Residual donor acquisition of graded anchored contexts with a top**, under the coatom
extension property at every limit stage: the top-grade supremum `K` is at least `1` and at least
the top grade of the donor. -/
theorem residualDonorAcquisition_isGradedTopContext
    (hext : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasCoatomExtensions.{u} α) :
    ResidualDonorAcquisition.{u, w} fun t' h d ↦ t'.IsGradedTopContext h d where
  exists_context _ _ _ _ hα hR hcore hK _ _ _ hc d hd hdK :=
    hR.exists_isGradedTopContext hα.bot_lt (hext hα) hc hd (hR.one_le_topGradeSup hα hcore)
      (hK ▸ by exact_mod_cast hdK)

/-- **(R2) from (R1), the coatom extension property, and determination over graded contexts with a
top**: a template whose remaining hypothesis, cutoff determination with a donor for
`StageType.IsGradedTopContext`, is open.  (R1) and the coatom extension property are assumed at
every limit stage; (R1) in the universes of the conclusion, stronger in stage range than
`Expansion.FiniteCutReceiving` (limit stages below `ω₁`, universe `0`), which does not supply it. -/
theorem residualReceiving_of_cutoffDonorDetermination_isGradedTopContext
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hext : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasCoatomExtensions.{u} α)
    (hdet : CutoffDonorDetermination.{u} fun t' h d ↦ t'.IsGradedTopContext h d) :
    ResidualReceiving.{u, w} :=
  residualReceiving_of_residualDonorAcquisition hrec
    (residualDonorAcquisition_isGradedTopContext hext) hdet

/-- **(R3) from (R1), the coatom extension property, and determination over graded contexts with a
top**, for any predicate `H` on models: a template whose remaining hypothesis, cutoff
determination with a donor for `StageType.IsGradedTopContext`, is open.  (R1) and the coatom
extension property are assumed at every limit stage; (R1) in the universes of the conclusion,
stronger in stage range than `Expansion.FiniteCutReceiving` (limit stages below `ω₁`, universe
`0`), which does not supply it. -/
theorem hollowReceiving_of_cutoffDonorDetermination_isGradedTopContext
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hext : ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → StageType.HasCoatomExtensions.{u} α)
    (hdet : CutoffDonorDetermination.{u} fun t' h d ↦ t'.IsGradedTopContext h d) :
    HollowReceiving.{u, w} H :=
  hollowReceiving_of_cutoffDonorDetermination hrec (donorAcquisition_isGradedTopContext hext H)
    hdet

end Realization

end VaughtConjecture
