/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.Realization.CapToModel
import VaughtConjecture.Realization.PrivateContext

/-!
# Determination over anchored contexts: acquisition holds, determination fails

Roadmap, Layer 3 ((R2) and (R3) of the table of 3.4, exact residual and exact hollow-growth
receiving; the private context of 3.3); semantic contract, items 5 and 8.

`VaughtConjecture.Continuation.ExactReceiving` reduces (R2) and (R3), given (R1) for every model at
every limit stage, to receiving at the one-point cofaces in which the root is not a rigid core, and
reduces that to an acquisition statement about models and a determination statement about stage
types, for a predicate `P` on acquired contexts that it leaves undefined.  This file fixes the
predicate suggested by the private context of the ordinary construction, proves acquisition for it
from modelhood, and refutes determination for it.  The refutation is of this predicate, not of
(R2) or (R3).

**Templates with a donor.**  The private context is acquired for a given donor
(`Realization.IsModel.exists_privateContext` takes the donor as input), so the predicate takes the
donor: `P t' h d` for a context `t'` on `k` points, a face `h : Fin n ↪ Fin k` (the root), and a
one-point coface `d` of the root.

* **Donor acquisition** (`Realization.DonorAcquisition Q P`), a statement about models: in every
  model at a limit stage satisfying `Q`, every cover `c` of a stage type `t` and every one-point
  coface `d` of `t` give a cover `c'` of some `t'` along some `h` (`c' ∘ h = c`) with `P t' h d`.
* **Cutoff determination with a donor** (`Realization.CutoffDonorDetermination P`), a statement
  about stage types: at a limit stage, over every legal `t'` with face `t` along `h` and every
  legal one-point coface `d` of `t` in which the root is not a rigid core, if `P t' h d` then `d`
  is determined over `t'` along `h` within the receiving family, at a permitted cutoff, of some
  coface of `t'` (`StageType.IsDeterminedWithin`).

Given (R1) for every model at every limit stage (in the universes of the conclusion; stronger in
stage range than `Expansion.FiniteCutReceiving`, which covers the limit stages below `ω₁` in
universe `0` and does not supply it), (R2) follows from donor acquisition in the models with no
globally rigid core and cutoff determination with a donor
(`Realization.residualReceiving_of_cutoffDonorDetermination`), and (R3) for a predicate `H` from
donor acquisition in the models satisfying `H` with unbounded growth and the same determination
(`Realization.hollowReceiving_of_cutoffDonorDetermination`).  The rigid cofaces come from (R1);
determination is asked only at the cofaces in which the root is not a rigid core, and for every top
grade, so in the residual case it asks more than (R2) needs.  These are templates: they are
reductions only for a predicate for which both hypotheses are proved, and none is known.

**The anchored context.**  A stage type `t'` on `k` points is an **anchored context** for a
one-point type `d` on `n + 1` points (`StageType.IsAnchoredContext`) when `n + 1 < k` and `t'` has
a cell `C` of graded index `(univ, k)` (a **private cap**) labelled above every label of `d` other
than `⊤`, below which `d` is anchored (`StageType.IsAnchored`): every label of a new cell of `d`
that is neither `⊥` nor `⊤` is a visibility replacement at the threshold `k` of the label of a cell
of `t'`, its anchor.  So every proper label of a new cell of the donor is obtained from a label of
the context.

**Acquisition holds, from modelhood** (`Realization.IsModel.exists_isAnchoredContext`,
`Realization.donorAcquisition_isAnchoredContext`, for every `Q`): the anchored private context
(`Realization.IsModel.exists_privateContext_isAnchored`) with its floor above every proper label of
the donor.  It corresponds to the context of [Kni26, Lemma 8.1.1], clauses 3 (the anchors) and 4
(the private cap), where the cell of clause 4 is labelled above the labels of the donor other than
`⊤` (the lemma labels it `⊤` when the characteristic arity is infinite).  By label class:

* proper labels: the anchors are the reference cells, from uniformity, clause 4(b) of modelhood
  ([Kni26, Definition 3.2.1, clause 4(b)]);
* the private cap: from high-arity dominance, clause 4(c) ([Kni26, Definition 3.2.1,
  clause 4(c)]); it is a cell labelled above a requested floor, not necessarily `⊤`;
* `⊥`: anchoring asks nothing of a label `⊥`, and no clause is used;
* `⊤`: no clause of modelhood is used, and the context need not contain `⊤`.

Exact consistency is used by the private context.  Neither generalized saturation, nor the bottom
pattern, nor the absence of a rigid core, nor any growth hypothesis is used.

**Determination fails** (`AnchoredDeterminationCounterexample.not_cutoffDonorDetermination`): at
every limit stage, over the empty root, with the donor on one point whose only cell is an apex
labelled `⊤` (the root is not a rigid core in it), the legal two-point context obtained by capping
a legal type with a cell of graded index `(univ, 2)` is an anchored context, and over it the donor
is determined neither within the receiving family of any coface at any permitted cutoff nor within
the stage types on the scheme of any coface.  The context
is top-free, and nothing in a top-free context forces a top.  What fails is the class `⊤`.
Determination at a cutoff persists at every larger cutoff
(`StageType.IsDeterminedWithin.receivingFamily_of_le`), and at a cutoff above every label of the
coface other than `⊤` the members of its receiving family agree with it at every cell not labelled
`⊤` (the definition of the receiving family).  So in the cutoff form the labels `⊥` and the proper
labels, the anchors included, are fixed by the cutoff, and determination concerns only the top
cells.  The reading of the proper labels of the donor against their anchors by a gate (the gated
extensions of `VaughtConjecture.Extension.GatedExtension`, whose universal form fails,
`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`) is not needed in this form.

**The obstruction: without an available private top no new top is forced.**  Let `D'` be a stage
type on `k + 1` points with face `t'` along the initial segment.  A **private top available to a new
cell** of `D'` (`StageType.HasAvailablePrivateTop`) is a cell labelled `⊤` whose scope avoids the
new point and lies in the scope of a cell of the same grade containing it; by availability some
cell of that graded index is then labelled `⊤`.  If `D'` has none, capping the new cells (those
whose scope contains the new point) at an ordinal above every proper label and the cutoff keeps
the labels lawful (`StageType.capThrough`, `CellScheme.Rows.IsLawful.min_const_of_mem_scope`):
locality at a new cell is capped, and locality at a private cell is unchanged.  The capped type is
in the receiving family of `D'` and has face `t'`, so no one-point type with a new cell labelled
`⊤` is determined over `t'` within the receiving family of `D'` at any permitted cutoff
(`StageType.not_isDeterminedWithin_receivingFamily_of_not_hasAvailablePrivateTop`), nor within the
stage types on its scheme.  A coface in which the root is not a rigid core has a new cell labelled
`⊤` (`StageType.exists_new_top_of_not_isRigidCoreIn`).

**What a predicate must have.**

* *Necessary* (`Realization.CutoffDonorDetermination.exists_hasAvailablePrivateTop`): if cutoff
  determination with a donor holds for `P`, then over every legal `t'` with `P t' h d` at a
  non-rigid coface `d`, some coface `D'` of `t'` has face `d` along `h` followed by the new point
  and a private top available to a new cell; in particular `t'` is not top-free
  (`Realization.CutoffDonorDetermination.not_isTopFree`).  The private cells of `D'` are the cells
  of `t'`.  For a realization with top-grade supremum `K` every cell labelled `⊤` of the type of a
  cover has grade at most `K` (`Realization.Covers.label_ne_top_of_topGradeSup_eq`).  So,
  combining the two informally (no single statement is compiled), in the residual case the
  available top is a cell of grade at most `K` of an acquired context, and the private cap, of
  grade the arity of the context, is not it once the arity exceeds `K`.
* *Sufficient* (`StageType.isDeterminedWithin_receivingFamily_of_isRigidCoreIn_castSucc`): if
  some legal coface `D'` of `t'` has face `d` along `h` followed by the new point and the private
  face is a rigid core of `D'`, then `d` is determined over `t'` along `h` within the receiving
  family of `D'` at a cutoff above its proper labels; so cutoff determination with a donor holds for
  the predicate asking for such a coface (`Realization.cutoffDonorDetermination_isRigidContext`).
  This is the rigid-core instance along `h`; it moves the whole content into acquisition, which is
  not proved for it, so it is a diagnosis, not a reduction.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

variable {α : Ordinal.{u}} {n k : ℕ}

namespace StageType

/-! ### Available private tops -/

/-- A point other than the last lies in the initial segment. -/
private theorem mem_range_castSuccEmb {x : Fin (k + 1)} (hx : x ≠ Fin.last k) :
    x ∈ Set.range (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) :=
  Fin.exists_castSucc_eq.mpr hx

/-- A cell whose scope avoids the last point is visible through the initial segment. -/
private theorem mem_visibleCells_castSuccEmb {D : StageType.{u} α (k + 1)} {s : Fin D.card}
    (hs : Fin.last k ∉ D.toCellScheme.scope s) : s ∈ D.visibleCells Fin.castSuccEmb :=
  Scheme.mem_visibleCells.mpr fun _ hx ↦ mem_range_castSuccEmb fun h ↦ hs (h ▸ hx)

/-- A stage type `D` on `k + 1` points has a **private top available to a new cell**: a cell
labelled `⊤` whose scope avoids the new (last) point and lies in the scope of a cell of the same
grade containing it. -/
def HasAvailablePrivateTop (D : StageType.{u} α (k + 1)) : Prop :=
  ∃ s s', D.toCellScheme.scope s ⊆ D.toCellScheme.scope s' ∧
    D.toCellScheme.grade s = D.toCellScheme.grade s' ∧ Fin.last k ∉ D.toCellScheme.scope s ∧
      Fin.last k ∈ D.toCellScheme.scope s' ∧ D.label s = ⊤

/-- **Over a top-free private face no private top is available**: a cell whose scope avoids the
new point is a cell of the face along the initial segment. -/
theorem not_hasAvailablePrivateTop_of_isTopFree {t' : StageType.{u} α k}
    {D' : StageType.{u} α (k + 1)} (hD' : restrictFace Fin.castSuccEmb D' = some t')
    (ht' : t'.IsTopFree) : ¬ D'.HasAvailablePrivateTop := by
  rintro ⟨s, -, -, -, hs, -, htop⟩
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D' _).mp hD'
  have hmem : s ∈ Set.range (D'.cellMap Fin.castSuccEmb) := by
    rw [Scheme.range_cellMap]
    exact mem_visibleCells_castSuccEmb hs
  obtain ⟨i, rfl⟩ := hmem
  exact ht' i htop

/-- **A non-rigid coface has a new top**: if the root of a one-point type `d` is not a rigid core
of it, some cell of `d` whose scope contains the new point is labelled `⊤`.  A top cell missing
from an admissible top support containing the top cells of the root is not a cell of the root. -/
theorem exists_new_top_of_not_isRigidCoreIn {d : StageType.{u} α (n + 1)}
    (hnr : ¬ d.IsRigidCoreIn Fin.castSuccEmb) :
    ∃ j, Fin.last n ∈ d.toCellScheme.scope j ∧ d.label j = ⊤ := by
  simp only [IsRigidCoreIn, not_forall] at hnr
  obtain ⟨H, -, hcore, j, hj, hjH⟩ := hnr
  exact ⟨j, by_contra fun hl ↦ hjH (hcore j (mem_visibleCells_castSuccEmb hl) hj), hj⟩

/-! ### Capping the new cells -/

/-- **No determination without an available private top.**  At a limit stage, let `D'` have face
`t'` along the initial segment and no private top available to a new cell, and let `d` have a new
cell labelled `⊤`.  Then for every `h` and every permitted cutoff `δ`, `d` is not determined over
`t'` along `h` within the receiving family of `D'` at `δ`.  Capping the new cells of `D'` at an
ordinal above `δ` and above every proper label of `D'` is lawful (`StageType.capThrough`), keeps
the face `t'` and the receiving family, and lowers the top of `d` to an ordinal. -/
theorem not_isDeterminedWithin_receivingFamily_of_not_hasAvailablePrivateTop
    (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : restrictFace Fin.castSuccEmb D' = some t') (hav : ¬ D'.HasAvailablePrivateTop)
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
    (hd : ∃ j, Fin.last n ∈ d.toCellScheme.scope j ∧ d.label j = ⊤) {δ : Label.{u}}
    (hδ : IsPermittedCutoff α δ) :
    ¬ IsDeterminedWithin (receivingFamily D' δ) t' h d := by
  intro hdet
  obtain ⟨o₀, ho₀, rfl⟩ := isPermittedCutoff_iff.mp hδ
  obtain ⟨o, hoα, ho⟩ := D'.exists_label_le hα.bot_lt
  obtain ⟨c, hoc, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit (max_lt hoα ho₀) (k + 1)
  have hoc' : ((o : Ordinal.{u}) : Label.{u}) ≤ c := by
    exact_mod_cast (le_max_left o o₀).trans hoc.le
  have ho₀c : ((o₀ : Ordinal.{u}) : Label.{u}) ≤ c := by
    exact_mod_cast (le_max_right o o₀).trans hoc.le
  set q := D'.capThrough (Fin.last k) c hc hcα fun s s' h₁ h₂ h₃ h₄ ↦
    (ho s fun htop ↦ hav ⟨s, s', h₁, h₂, h₃, h₄, htop⟩).trans hoc'
  have hq : q ∈ receivingFamily D' o₀ := by
    refine ⟨rfl, fun i j hij ↦ ?_⟩
    obtain rfl : i = j := Fin.ext hij
    -- unfold the label of `q` at `i` (`StageType.capThrough_label`) inside the cutoff
    change min (if Fin.last k ∈ D'.toCellScheme.scope i then min (D'.label i) c else D'.label i)
      _ = _
    split_ifs
    · rw [min_assoc, min_eq_right ho₀c]
    · rfl
  have hqt : restrictFace Fin.castSuccEmb q = some t' := by
    rw [restrictFace_capThrough fun ⟨i, hi⟩ ↦ (Fin.castSucc_lt_last i).ne hi]
    exact hD'
  obtain ⟨j, hjs, hjt⟩ := hd
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D' _).mp
    (hdet D' (self_mem_receivingFamily D' _) hD')
  obtain ⟨hf', hq'⟩ := (restrictFace_eq_some_iff q _).mp (hdet q hq hqt)
  -- the cell of `D'` under `j` contains the new point and is labelled `⊤`
  have hlast : Fin.last k ∈ D'.toCellScheme.scope (D'.cellMap (extendByLast h) j) := by
    have hm := Scheme.map_comap_scope D'.toScheme (extendByLast h) j
    rw [← hm, ← extendByLast_last h]
    exact mem_map_of_mem _ hjs
  set x := D'.cellMap (extendByLast h) j
  have hl := label_congr hq' (i := j) (j := j) rfl
  -- `q` has the scheme of `D'`, so its cell under `j` is `x`; unfold its label there, and the
  -- label of `d` at `j` as that of `D'` at `x`
  change (if Fin.last k ∈ D'.toCellScheme.scope x then min (D'.label x) c else D'.label x) =
    D'.label x at hl
  change D'.label x = ⊤ at hjt
  simp only [hlast, ↓reduceIte, hjt, min_top_left] at hl
  exact WithBot.coe_injective.ne WithTop.coe_ne_top hl

/-- **No determination by a scheme without an available private top**: under the hypotheses of
`not_isDeterminedWithin_receivingFamily_of_not_hasAvailablePrivateTop`, `d` is not determined
within the stage types on the scheme of `D'` either, which contain its receiving families. -/
theorem not_isDeterminedWithin_saturationFamily_of_not_hasAvailablePrivateTop
    (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k} {D' : StageType.{u} α (k + 1)}
    (hD' : restrictFace Fin.castSuccEmb D' = some t') (hav : ¬ D'.HasAvailablePrivateTop)
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}
    (hd : ∃ j, Fin.last n ∈ d.toCellScheme.scope j ∧ d.label j = ⊤) :
    ¬ IsDeterminedWithin (saturationFamily D'.toScheme) t' h d := fun hdet ↦
  not_isDeterminedWithin_receivingFamily_of_not_hasAvailablePrivateTop hα hD' hav hd
    (isPermittedCutoff_iff.mpr ⟨0, hα.bot_lt, rfl⟩)
    (hdet.mono (receivingFamily_subset_saturationFamily (d := D') rfl _))

/-! ### A rigid context determines -/

/-- A **rigid context** for `d` along `h`: some legal coface of `t'` has face `d` along `h`
followed by the new point, and the private face is a rigid core of it. -/
def IsRigidContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (d : StageType.{u} α (n + 1)) :
    Prop :=
  ∃ D' ∈ t'.cofaces, restrictFace (extendByLast h) D' = some d ∧
    D'.IsRigidCoreIn Fin.castSuccEmb

/-! ### The anchored context -/

/-- A stage type `t'` on `k` points is an **anchored context** for a one-point type `d` on `n + 1`
points: `n + 1 < k`, and some cell `C` of `t'` of graded index `(univ, k)`, labelled above every
label of `d` other than `⊤`, has `d` anchored below it (`StageType.IsAnchored`). -/
def IsAnchoredContext (t' : StageType.{u} α k) (d : StageType.{u} α (n + 1)) : Prop :=
  n + 1 < k ∧ ∃ C : Fin t'.card, t'.toCellScheme.gradedIndex C = (univ, k) ∧
    (∀ j, d.label j ≠ ⊤ → d.label j < t'.label C) ∧ IsAnchored t' C d

end StageType

namespace Realization

variable {M : Type w} {R : Realization.{u, w} α M}

/-! ### Templates with a donor -/

/-- **Donor acquisition** for a predicate `P` on contexts and donors, in the models satisfying
`Q`: in every model at a limit stage satisfying `Q`, every cover `c` of a stage type `t` and every
one-point coface `d` of `t` give a cover `c'` of some `t'` along some `h` (`c' ∘ h = c`) with
`P t' h d`.  A statement about models. -/
structure DonorAcquisition (Q : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop)
    (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop) : Prop where
  /-- Every cover and donor give a cover of an acquired context. -/
  exists_context ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ :
    Order.IsSuccLimit α → R.IsModel → Q R →
      ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c → ∀ d ∈ t.cofaces,
        ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
          R.Covers t' c' ∧ c' ∘ h = c ∧ P t' h d

/-- **Cutoff determination with a donor** for `P`, a statement about stage types: at a limit
stage, over every legal `t'` with face `t` along `h`, every legal one-point coface `d` of `t` in
which the root is not a rigid core, with `P t' h d`, is determined over `t'` along `h` within the
receiving family, at a permitted cutoff, of some coface of `t'`. -/
structure CutoffDonorDetermination (P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k →
    (Fin n ↪ Fin k) → StageType.{u} α (n + 1) → Prop) : Prop where
  /-- Every non-rigid coface with an acquired context is determined at a cutoff. -/
  exists_coface ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) :
    Order.IsSuccLimit α → t'.IsLegal → P t' h d → ∀ t : StageType.{u} α n,
      StageType.restrictFace h t' = some t → d ∈ t.cofaces →
        ¬ d.IsRigidCoreIn Fin.castSuccEmb →
          ∃ D' ∈ t'.cofaces, ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            StageType.IsDeterminedWithin (StageType.receivingFamily D' δ) t' h d

/-- Receiving at a non-rigid coface from an acquired context and cutoff determination. -/
private theorem exists_covers_snoc_of_cutoffDonorDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hdet : CutoffDonorDetermination.{u} P) (hα : Order.IsSuccLimit α) (hR : R.IsModel)
    (hrec : R.HasFiniteCutReceiving) {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c)
    {d : StageType.{u} α (n + 1)} (hd : d ∈ t.cofaces) (hnr : ¬ d.IsRigidCoreIn Fin.castSuccEmb)
    (hctx : ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ h = c ∧ P t' h d) :
    ∃ y : M, R.Covers d (Fin.snoc c y) := by
  obtain ⟨k, t', c', h, hc', hcc', hP⟩ := hctx
  obtain ⟨D', hD', δ, hδ, hdet'⟩ := hdet.exists_coface t' h d hα (hR.isLegal _ _ hc'.eval_eq) hP t
    (restrictFace_of_covers hR.isConsistent hc hc' hcc') hd hnr
  rw [← hcc']
  exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
    (hrec.realizesOver_receivingFamily hc' hD' hδ) hdet'

/-- **(R2) from (R1), donor acquisition, and cutoff determination with a donor**, for any `P`.
(R1) is assumed for every model at every limit stage, in the universes of the conclusion: stronger
in stage range than `Expansion.FiniteCutReceiving` (limit stages below `ω₁`, universe `0`), which
does not supply it.  A template: no predicate is known for which both hypotheses hold. -/
theorem residualReceiving_of_cutoffDonorDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hacq : DonorAcquisition.{u, w} (fun {α} {M} R ↦ ¬ ∃ (k : ℕ) (p : StageType.{u} α k)
      (c : Fin k → M), R.Covers p c ∧ R.IsGloballyRigidCore c) P)
    (hdet : CutoffDonorDetermination.{u} P) : ResidualReceiving.{u, w} :=
  ResidualReceiving.of_not_isRigidCoreIn hrec fun _ _ _ _ hα hR hcore _ _ t c hc d hd _ hnr ↦
    exists_covers_snoc_of_cutoffDonorDetermination hdet hα hR (hrec hα hR) hc hd hnr
      (hacq.exists_context hα hR hcore t c hc d hd)

/-- **(R3) from (R1), donor acquisition, and cutoff determination with a donor**, for any `P` and
any predicate `H` on models (for instance `Realization.IsCoverHollowAtBlock`, or its restriction
`Realization.IsCoverHollowWithoutRigidCoreAtBlock` in `Continuation/RestrictedHollow`).  (R1) is assumed for
every model at every limit stage, in the universes of the conclusion: stronger in stage range than
`Expansion.FiniteCutReceiving` (limit stages below `ω₁`, universe `0`), which does not supply it.
A template: no predicate is known for which both hypotheses hold. -/
theorem hollowReceiving_of_cutoffDonorDetermination
    {H : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hrec : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄,
      Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving)
    (hacq : DonorAcquisition.{u, w} (fun R ↦ H R ∧ R.topGradeSup = ⊤) P)
    (hdet : CutoffDonorDetermination.{u} P) : HollowReceiving.{u, w} H :=
  HollowReceiving.of_not_isRigidCoreIn hrec fun _ _ _ hα hR hH htop _ t c hc d hd hnr ↦
    exists_covers_snoc_of_cutoffDonorDetermination hdet hα hR (hrec hα hR) hc hd hnr
      (hacq.exists_context hα hR ⟨hH, htop⟩ t c hc d hd)

/-! ### What determination needs -/

/-- **Determination needs an available private top**: if cutoff determination with a donor holds
for `P`, then over every legal `t'` with face `t` along `h`, and every legal non-rigid one-point
coface `d` of `t` with `P t' h d`, some coface `D'` of `t'` has face `d` along `h` followed by the
new point and a private top available to a new cell. -/
theorem CutoffDonorDetermination.exists_hasAvailablePrivateTop
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hdet : CutoffDonorDetermination.{u} P) (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k}
    (ht' : t'.IsLegal) {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} (hP : P t' h d)
    {t : StageType.{u} α n} (ht : StageType.restrictFace h t' = some t) (hd : d ∈ t.cofaces)
    (hnr : ¬ d.IsRigidCoreIn Fin.castSuccEmb) :
    ∃ D' ∈ t'.cofaces, StageType.restrictFace (extendByLast h) D' = some d ∧
      D'.HasAvailablePrivateTop := by
  obtain ⟨D', hD', δ, hδ, hdet'⟩ := hdet.exists_coface t' h d hα ht' hP t ht hd hnr
  refine ⟨D', hD', hdet' D' (StageType.self_mem_receivingFamily D' δ) hD'.2, by_contra fun hav ↦ ?_⟩
  exact StageType.not_isDeterminedWithin_receivingFamily_of_not_hasAvailablePrivateTop hα hD'.2
    hav (StageType.exists_new_top_of_not_isRigidCoreIn hnr) hδ hdet'

/-- **Determination needs a top in the context**: under cutoff determination with a donor for `P`,
a legal `t'` with `P t' h d` at a non-rigid coface `d` of its face along `h` is not top-free. -/
theorem CutoffDonorDetermination.not_isTopFree
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) →
      StageType.{u} α (n + 1) → Prop}
    (hdet : CutoffDonorDetermination.{u} P) (hα : Order.IsSuccLimit α) {t' : StageType.{u} α k}
    (ht' : t'.IsLegal) {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} (hP : P t' h d)
    {t : StageType.{u} α n} (ht : StageType.restrictFace h t' = some t) (hd : d ∈ t.cofaces)
    (hnr : ¬ d.IsRigidCoreIn Fin.castSuccEmb) : ¬ t'.IsTopFree := fun htf ↦
  let ⟨_, hD', _, hav⟩ := hdet.exists_hasAvailablePrivateTop hα ht' hP ht hd hnr
  StageType.not_hasAvailablePrivateTop_of_isTopFree hD'.2 htf hav

/-- **Cutoff determination with a donor holds for rigid contexts**
(`StageType.IsRigidContext`): the rigid-core instance along a face, at a cutoff above every
label of the coface other than `⊤`.  A diagnosis, not a reduction: acquisition of rigid contexts
is not proved. -/
theorem cutoffDonorDetermination_isRigidContext :
    CutoffDonorDetermination.{u} fun t' h d ↦ t'.IsRigidContext h d where
  exists_coface _ _ _ t' h d hα _ hP _ _ _ _ := by
    obtain ⟨D', hD', hD'd, hrig⟩ := hP
    obtain ⟨δ, hδα, hδ⟩ := D'.exists_lt_forall_label_lt hα
    exact ⟨D', hD', δ, isPermittedCutoff_iff.mpr ⟨δ, hδα, rfl⟩,
      StageType.isDeterminedWithin_receivingFamily_of_isRigidCoreIn_castSucc hD'.1 hD'.2 hD'd
        hrig hδ⟩

/-- **For a realization with top-grade supremum `K`, a cell of grade above `K` of the type of a
cover is not `⊤`.**  No modelhood is assumed.  So in the residual case the private cap of an
acquired context, of grade the arity of the context, is a proper label or `⊥` once that arity
exceeds `K`. -/
theorem Covers.label_ne_top_of_topGradeSup_eq {t' : StageType.{u} α k} {c' : Fin k → M}
    (hc' : R.Covers t' c') {K : ℕ} (hK : R.topGradeSup = K) {j : Fin t'.card}
    (hj : K < t'.toCellScheme.grade j) : t'.label j ≠ ⊤ := fun htop ↦ by
  have hle : t'.topGrade ≤ K := by
    have := (⟨k, ⟨c', hc'.injective⟩, t', hc'.eval_eq⟩ : R.Occurrence).topGrade_le_topGradeSup
    rw [hK] at this
    exact_mod_cast this
  exact absurd ((StageType.grade_le_topGrade htop).trans hle) hj.not_ge

/-! ### Acquisition of anchored contexts -/

/-- **Acquisition of an anchored context**: in a model at a nonzero stage, every cover `c` of `t`
and every one-point type `d` over it give a cover `c'` of an anchored context `t'` for `d` along
some `h` with `c' ∘ h = c`.  The anchored private context
(`Realization.IsModel.exists_privateContext_isAnchored`) at a floor above every label of `d` other
than `⊤`; it uses uniformity, high-arity dominance, and exact consistency. -/
theorem IsModel.exists_isAnchoredContext (hR : R.IsModel) (hα : 0 < α)
    {t : StageType.{u} α n} {c : Fin n → M} (hc : R.Covers t c) (d : StageType.{u} α (n + 1)) :
    ∃ (k : ℕ) (t' : StageType.{u} α k) (c' : Fin k → M) (h : Fin n ↪ Fin k),
      R.Covers t' c' ∧ c' ∘ h = c ∧ t'.IsAnchoredContext d := by
  obtain ⟨o, hoα, ho⟩ := d.exists_label_le hα
  obtain ⟨y, f, C, hf, -, hn, hC, hoC, hanc⟩ :=
    hR.exists_privateContext_isAnchored ⟨n, ⟨c, hc.injective⟩, t, hc.eval_eq⟩ d hoα
  refine ⟨y.arity, y.type, y.tuple, f, covers_of_eval _ y.eval_tuple, ?_, hn, C, hC,
    fun j hj ↦ (ho j hj).trans_lt hoC, hanc⟩
  funext i
  exact DFunLike.congr_fun hf i

/-- **Donor acquisition holds for anchored contexts**, in the models satisfying any `Q`: modelhood
alone suffices. -/
theorem donorAcquisition_isAnchoredContext
    (Q : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop) :
    DonorAcquisition.{u, w} Q fun t' _ d ↦ t'.IsAnchoredContext d where
  exists_context _ _ _ hα hR _ _ _ _ hc d _ := hR.exists_isAnchoredContext hα.bot_lt hc d

end Realization

end VaughtConjecture
