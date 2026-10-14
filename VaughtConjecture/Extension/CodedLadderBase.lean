/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CodedLadderSource
import VaughtConjecture.Extension.LadderRendering
import VaughtConjecture.Extension.StronglyCodedCompletion

/-!
# The strongly coded grade-one base

Roadmap, Layer 3 ((R3) and (R4), the first layer of the recognizing growth carrier) and
Correspondence, item 1 (the strongly coded legal stage types).  All results here are native
constructions of this repository.

The padded grade-one base (`Scheme.ladderBase`) is not strongly coded at heights `H ≥ 2`
(`Scheme.LadderBaseData.not_isStronglyCoded_ladderBase`): its rows read the codes
`Label.ladderSource`.  The **coded ladder base** (`Scheme.codedLadderBase`) appends the same
ladder points to `S` at `(univ, 1)`, with the rows `Scheme.codedBaseRow`: the coded ladder sources
(`Label.codedLadderSource`), at the ceiling of the point, of the same base indices
(`Scheme.baseIndex`).  Its cell scheme is that of the padded base
(`Scheme.codedLadderBase_toCellScheme`): the same cells, scopes, grades and faces.

## Main statements

* `Scheme.isConsistent_codedLadderBase`, `Scheme.isWellFormed_codedLadderBase`,
  `Scheme.isCoded_codedLadderBase`: as for the padded base, given lawful rank tables
  (`Scheme.RankTablesLawful`).
* `Scheme.isStronglyCoded_codedLadderBase`: **strong coding**, given a strongly coded `S`.
* `Scheme.isLawful_codedRender`: rendered tables (`Scheme.render`) are lawful sections; the row of
  a ladder point is the rendering of its code table (`Scheme.codedBaseRow_eq_render`).
* `Scheme.isLawfulBelow_codedLadderBase_iff`, `Scheme.cappedLift_codedLadderBase_iff`: off
  `(univ, 1)` the base is `S`.
* `Scheme.codedLadderLawful_of_isLawful`, `Scheme.codedLadderBase_exists_shape`,
  `Scheme.exists_codedRender_of_isLawful`: **recognition** on the ladder and at grade one.
* `Scheme.rowAt_codedLadderBase_old`, `Scheme.rowAt_codedLadderBase_ladder`: the literal row
  values at the ladder points.

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9]; strong coding is the
range of [Kni26, Lemma 2.5.13].

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} {S : Scheme.{u} n} {Q : Type} [Fintype Q] (H : ℕ) (prof : Q → Fin S.card → ℕ)

/-- The **row of a ladder point** of the coded ladder base (native construction): the coded
ladder sources, at its ceiling, of the base indices of its member, `⊥` at the old cells of grade
other than one. -/
noncomputable def codedBaseRow (i : Fin (ladderCard S Q H))
    (t : Fin (S.card + ladderCard S Q H)) : Label.{u} :=
  Fin.append (fun d ↦ if S.toCellScheme.grade d = 1 then
      codedLadderSource (ladderCeil prof ((ladderEquiv S Q H).symm i))
        (baseIndex H prof ((ladderEquiv S Q H).symm i).1 (Fin.castAdd _ d)) else ⊥)
    (fun j ↦ codedLadderSource (ladderCeil prof ((ladderEquiv S Q H).symm i))
      (baseIndex H prof ((ladderEquiv S Q H).symm i).1 (Fin.natAdd _ j))) t

/-- **The coded ladder base** (native construction): `S` with the ladder points at `(univ, 1)`,
whose rows are the coded ladder sources of the base indices. -/
noncomputable abbrev codedLadderBase (hS : S.NoFullOne) : Scheme.{u} n :=
  S.appendFullCells 1 (ladderCard S Q H) (codedBaseRow H prof) hS

variable {H prof}

/-- **The coded ladder base has the cell scheme of the padded base**: the same cells, scopes,
grades and faces; only the rows of the ladder points differ. -/
theorem codedLadderBase_toCellScheme (hS : S.NoFullOne) :
    (codedLadderBase H prof hS).toCellScheme = (ladderBase H prof hS).toCellScheme := rfl

/-- On the cells below `(univ, 1)` the row of a ladder point is the coded ladder source of the
base index. -/
theorem codedBaseRow_of_mem {hS : S.NoFullOne} (hwf : S.IsWellFormed) (i : Fin (ladderCard S Q H))
    {t : Fin (S.card + ladderCard S Q H)}
    (ht : t ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1)) :
    codedBaseRow H prof i t = codedLadderSource (ladderCeil prof ((ladderEquiv S Q H).symm i))
      (baseIndex H prof ((ladderEquiv S Q H).symm i).1 t) := by
  have hg := grade_eq_one_of_mem_below (prof := prof) (hS := hS) hwf ht
  induction t using Fin.addCases with
  | left d =>
    rw [appendFullCellsScheme_grade_castAdd] at hg
    unfold codedBaseRow
    rw [Fin.append_left, ite_eq_left hg]
  | right j => unfold codedBaseRow; rw [Fin.append_right]

/-- **The row of a ladder point is the rendering of its code table**: the coded ladder sources at
its ceiling, read at the base indices of its member. -/
theorem codedBaseRow_eq_render (i : Fin (ladderCard S Q H)) :
    codedBaseRow H prof i = render S H prof ((ladderEquiv S Q H).symm i).1
      (codedLadderSource (ladderCeil prof ((ladderEquiv S Q H).symm i))) := by
  funext t
  induction t using Fin.addCases with
  | left d => unfold codedBaseRow; rw [Fin.append_left, render_castAdd, baseIndex_castAdd]
  | right j => unfold codedBaseRow; rw [Fin.append_right, render_natAdd]

/-! ### Rendered tables are lawful -/

/-- **Rendered tables are lawful sections of the coded ladder base**: for a positive table `f`
(monotone, `⊥` at `0`, self-visible at `1`, positive at `1, …, H`) whose table at the ranks of `a`
is lawful on `S` at grade one, the rendering of `f` for `a` is lawful.  Locality at a ladder point
is `Label.transformsTo_codedLadderSource`. -/
theorem isLawful_codedRender {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hH : 0 < H)
    (hprof : ∀ a d, prof a d ≤ H) (a : Q) {f : ℕ → Label.{u}} (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, IsSelfVisible 1 (f i)) (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥)
    (hold : S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then f (prof a d) else ⊥) :
    (codedLadderBase H prof hS).rows.IsLawful (render S H prof a f) := by
  classical
  refine isLawful_appendFullCells ?_ (fun j ↦ by rw [render_natAdd]; exact hv _)
    (fun i' ↦ ?_) (fun s hs ↦ ?_)
  · -- on the old cells: the table of `a`
    convert hold using 1
    funext d
    simp only [Function.comp_apply, render_castAdd]
  · -- locality at the ladder point `i'`
    set c' := (ladderEquiv S Q H).symm i' with hc'
    set e := baseIndex H prof a (Fin.natAdd _ i') with he
    have hec : e ≤ ladderCeil prof c' := by
      rw [he, baseIndex_natAdd]; exact min_le_right _ _
    have hecut : e ≤ rankCut H (prof a) (prof c'.1) := by
      rw [he, baseIndex_natAdd]; exact min_le_left _ _
    have hmem (t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i'))) :
        t.1 ∈ (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      refine ⟨subset_univ _, ?_⟩
      have h2 := t.2.2
      simp only [appendFullCellsScheme_gradedIndex_natAdd] at h2
      exact h2
    have hgr (t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i'))) :
        (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 :=
      grade_eq_one_of_mem_below (prof := prof) (hS := hS) hwf (hmem t)
    have htarget : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          min (render S H prof a f t) (render S H prof a f (Fin.natAdd _ i'))) =
        fun t ↦ f (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e) := by
      funext t
      rw [render, ite_eq_left (hgr t), render_natAdd, ← he, ← hf.map_min, min_assoc,
        min_eq_right hec, ← min_eq_right hecut, ← min_assoc, baseIndex_agree a c'.1 t.1,
        min_assoc]
    have hsource : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          codedBaseRow H prof i' t.1) =
        fun t ↦ codedLadderSource (ladderCeil prof c') (baseIndex H prof c'.1 t.1) := by
      funext t
      exact codedBaseRow_of_mem hwf i' (hmem t)
    have hgrade : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t) = fun _ ↦ 1 :=
      funext hgr
    rw [hsource, htarget, hgrade]
    by_cases he0 : e = 0
    · have hz : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            f (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e)) =
          fun _ ↦ ⊥ := by
        funext t; rw [he0, Nat.min_zero, h0]
      rw [hz]
      exact TransformsTo.bot _ _
    · exact transformsTo_codedLadderSource
        (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            baseIndex H prof c'.1 t.1)
        (f := fun k ↦ f (min k e)) (fun _ _ h ↦ hf (min_le_min_right _ h)) (by simp [h0])
        (fun _ ↦ hv _) fun k hk _ ↦ hp _ (by omega) ((min_le_right _ _).trans
          (hecut.trans (rankCut_le H _ _)))
  · -- availability: the top rung of `a` dominates
    have hHl : H - 1 < H := by omega
    refine ⟨ladderEquiv S Q H (a, Sum.inl ⟨H - 1, hHl⟩), ?_⟩
    rw [render, ite_eq_left hs, render_natAdd, baseIndex_self hprof (a, Sum.inl ⟨H - 1, hHl⟩)]
    exact hf ((baseIndex_le hprof a s).trans (by simp only [ladderCeil, Sum.elim_inl]; omega))

/-! ### Consistency and coding -/

/-- **The row of every ladder point is a lawful section of the coded ladder base**, given lawful
rank tables. -/
theorem isLawful_codedBaseRow {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hH : 0 < H)
    (hprof : ∀ a d, prof a d ≤ H) (hrank : RankTablesLawful S H prof)
    (i : Fin (ladderCard S Q H)) :
    (codedLadderBase H prof hS).rows.IsLawful (codedBaseRow H prof i) := by
  set c := (ladderEquiv S Q H).symm i with hc
  set tc := ladderCeil prof c with htc
  by_cases htc0 : tc = 0
  · -- the zero row
    have hz : codedBaseRow H prof i = fun _ ↦ ⊥ := by
      rw [codedBaseRow_eq_render, ← hc, ← htc, htc0]
      funext t
      unfold render
      split_ifs <;> simp [codedLadderSource]
    rw [hz]
    exact CellScheme.Rows.isLawful_const_bot
  rw [codedBaseRow_eq_render, ← hc, ← htc]
  have hpos (k : ℕ) (hk : 0 < k) (_ : k ≤ H) : codedLadderSource.{u} tc k ≠ ⊥ := fun h0 ↦ by
    rw [codedLadderSource_eq_bot_iff] at h0; omega
  exact isLawful_codedRender hwf hH hprof c.1 (monotone_codedLadderSource tc)
    (codedLadderSource_zero tc) (isSelfVisible_codedLadderSource tc) hpos
    (hrank c.1 _ (monotone_codedLadderSource tc) (codedLadderSource_zero tc)
      (isSelfVisible_codedLadderSource tc) hpos)

/-- **The coded ladder base is consistent**, given a consistent `S` and lawful rank tables. -/
theorem isConsistent_codedLadderBase {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hcons : S.rows.IsConsistent) (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H)
    (hrank : RankTablesLawful S H prof) : (codedLadderBase H prof hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦ isLawful_codedBaseRow hwf hH hprof hrank i

/-- **The coded ladder base is well formed**, on at least one point. -/
theorem isWellFormed_codedLadderBase {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hn : 1 ≤ n) :
    (codedLadderBase H prof hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf (by omega) hn

/-- Every value of the row of a ladder point is strongly coded at grade one. -/
theorem isStronglyCoded_codedBaseRow (i : Fin (ladderCard S Q H))
    (t : Fin (S.card + ladderCard S Q H)) : IsStronglyCoded 1 (codedBaseRow H prof i t) := by
  induction t using Fin.addCases with
  | left d =>
    unfold codedBaseRow
    rw [Fin.append_left]
    split_ifs
    · exact isStronglyCoded_codedLadderSource le_rfl _ _
    · exact isStronglyCoded_bot _
  | right j =>
    unfold codedBaseRow
    rw [Fin.append_right]
    exact isStronglyCoded_codedLadderSource le_rfl _ _

/-- **The coded ladder base is coded**, given a coded `S`. -/
theorem isCoded_codedLadderBase {hS : S.NoFullOne} (hc : S.IsCoded) :
    (codedLadderBase H prof hS).IsCoded :=
  isCoded_appendFullCells hc fun i t ↦ (isStronglyCoded_codedBaseRow i t).lt_omega0_sq

/-- **The coded ladder base is strongly coded** (native construction), given a strongly coded `S`:
the rows of the ladder points, of grade one, take strongly coded values at grade one (finite part
at most `2`). -/
theorem isStronglyCoded_codedLadderBase {hS : S.NoFullOne} (hsc : S.rows.IsStronglyCoded) :
    (codedLadderBase H prof hS).rows.IsStronglyCoded :=
  isStronglyCoded_appendFullCells hsc isStronglyCoded_codedBaseRow

/-! ### Off the full face the base is `S` -/

/-- **Lawfulness below a pair not above `(univ, 1)`** in the coded ladder base is lawfulness in
`S`. -/
theorem isLawfulBelow_codedLadderBase_iff {hS : S.NoFullOne} {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), 1) ≤ X) {v : Fin (S.card + ladderCard S Q H) → Label.{u}} :
    (codedLadderBase H prof hS).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd _ d)) :=
  isLawfulBelow_appendFullCells_iff hX

/-- **Capped lifts below a pair not above `(univ, 1)`** in the coded ladder base are those of
`S`. -/
theorem cappedLift_codedLadderBase_iff {hS : S.NoFullOne} {X Y : Finset (Fin n) × ℕ}
    (hXY : X ≤ Y) (hY : ¬ ((univ : Finset (Fin n)), 1) ≤ Y) :
    (codedLadderBase H prof hS).rows.CappedLift hXY ↔ S.rows.CappedLift hXY := by
  have h : S.toCellScheme.IsSourcePrefix (codedLadderBase H prof hS).toCellScheme
      (Fin.castAdd _) Y :=
    ⟨isLowerEmbedding_castAdd (S := S) 1 (ladderCard S Q H) (codedBaseRow H prof) hS,
      appendFullCellsScheme_scope_castAdd S 1 _,
      fun d hd ↦ ⟨⟨d, lt_card_of_mem_below hY hd⟩, rfl⟩⟩
  rw [← h.cappedLift_iff hXY le_rfl, comap_rows_castAdd]

/-! ### Literal rows at the ladder points -/

/-- **A ladder point reads an old cell of grade one** through the coded ladder source, at its
ceiling, of the rank of the cell for its member. -/
theorem rowAt_codedLadderBase_old {hS : S.NoFullOne} (hwf : S.IsWellFormed) (p : LadderPt S Q H)
    {e : Fin S.card} (he : S.toCellScheme.grade e = 1) :
    (codedLadderBase H prof hS).rowAt (Fin.natAdd _ (ladderEquiv S Q H p)) (Fin.castAdd _ e) =
      codedLadderSource (ladderCeil prof p) (prof p.1 e) := by
  have hq : (Fin.castAdd _ e : Fin (S.card + ladderCard S Q H)) ∈
      (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
    change (S.appendFullCellsScheme 1 _).gradedIndex _ ≤ _
    rw [appendFullCellsScheme_gradedIndex_castAdd]
    exact ⟨subset_univ _, he.le⟩
  have hmem : (Fin.castAdd _ e : Fin (S.card + ladderCard S Q H)) ∈
      (codedLadderBase H prof hS).toCellScheme.below
        ((codedLadderBase H prof hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (ladderEquiv S Q H p))) := by
    change (S.appendFullCellsScheme 1 _).gradedIndex _ ≤ (S.appendFullCellsScheme 1 _).gradedIndex _
    rw [appendFullCellsScheme_gradedIndex_natAdd]
    exact hq
  rw [rowAt_of_mem hmem]
  have h1 := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
    (r := codedBaseRow H prof) (h := hS) (ladderEquiv S Q H p) ⟨_, hmem⟩
  rw [h1, codedBaseRow_of_mem hwf _ hq, Equiv.symm_apply_apply, baseIndex_castAdd]

/-- **A ladder point reads another** through the coded ladder source, at its ceiling, of the base
index of its member. -/
theorem rowAt_codedLadderBase_ladder {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (p q : LadderPt S Q H) :
    (codedLadderBase H prof hS).rowAt (Fin.natAdd _ (ladderEquiv S Q H p))
      (Fin.natAdd _ (ladderEquiv S Q H q)) =
    codedLadderSource (ladderCeil prof p)
      (baseIndex H prof p.1 (Fin.natAdd _ (ladderEquiv S Q H q))) := by
  have hq : Fin.natAdd S.card (ladderEquiv S Q H q) ∈
      (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd]
  have hmem : Fin.natAdd S.card (ladderEquiv S Q H q) ∈
      (codedLadderBase H prof hS).toCellScheme.below
        ((codedLadderBase H prof hS).toCellScheme.gradedIndex
          (Fin.natAdd S.card (ladderEquiv S Q H p))) := by
    change (S.appendFullCellsScheme 1 _).gradedIndex _ ≤ (S.appendFullCellsScheme 1 _).gradedIndex _
    rw [appendFullCellsScheme_gradedIndex_natAdd, appendFullCellsScheme_gradedIndex_natAdd]
  rw [rowAt_of_mem hmem]
  have h1 := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
    (r := codedBaseRow H prof) (h := hS) (ladderEquiv S Q H p) ⟨_, hmem⟩
  rw [h1, codedBaseRow_of_mem hwf _ hq, Equiv.symm_apply_apply]

/-- **The diagonal of a rung**: the rung `i` of a member reads itself at the coded ladder source
`codedLadderSource (i + 1) (i + 1)`, which is `ω · i + 2` for `i ≥ 1`
(`Label.codedLadderSource_self`), strongly coded at grade one. -/
theorem rowAt_codedLadderBase_rung {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hprof : ∀ a d, prof a d ≤ H) (a : Q) (i : Fin H) :
    (codedLadderBase H prof hS).rowAt (Fin.natAdd _ (ladderEquiv S Q H (a, Sum.inl i)))
      (Fin.natAdd _ (ladderEquiv S Q H (a, Sum.inl i))) =
    codedLadderSource (i.1 + 1) (i.1 + 1) := by
  rw [rowAt_codedLadderBase_ladder hwf, baseIndex_self hprof]
  rfl

/-- **The rung below**: the rung `i ≥ 1` of a member reads the rung `i - 1` at the coded ladder
source `codedLadderSource (i + 1) i`, which is `ω · i + 1`, in the block of the diagonal. -/
theorem rowAt_codedLadderBase_rung_pred {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hprof : ∀ a d, prof a d ≤ H) (a : Q) (i : ℕ) (hi : i < H) (hi0 : 0 < i) :
    (codedLadderBase H prof hS).rowAt (Fin.natAdd _ (ladderEquiv S Q H (a, Sum.inl ⟨i, hi⟩)))
      (Fin.natAdd _ (ladderEquiv S Q H (a, Sum.inl ⟨i - 1, by omega⟩))) =
    codedLadderSource (i + 1) i := by
  rw [rowAt_codedLadderBase_ladder hwf]
  have h := baseIndex_self hprof ((a, Sum.inl ⟨i - 1, by omega⟩) : LadderPt S Q H)
  simp only [ladderCeil, Sum.elim_inl] at h ⊢
  rw [h, Nat.sub_add_cancel hi0]

/-! ### Recognition on the ladder -/

/-- **A lawful section of the coded ladder base is lawful on the coded ladder table**: read on the
ladder points, it is self-visible at grade one and local at every ladder point for its row
(`Label.CodedLadderLawful`). -/
theorem codedLadderLawful_of_isLawful {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (codedLadderBase H prof hS).rows.IsLawful v) :
    CodedLadderLawful H prof Prod.fst (ladderCeil prof)
      fun p ↦ v (Fin.natAdd _ (ladderEquiv S Q H p)) := by
  have hmemp (p : LadderPt S Q H) : Fin.natAdd S.card (ladderEquiv S Q H p) ∈
      (codedLadderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd]
  refine ⟨fun p ↦ ?_, fun c ↦ ?_⟩
  · have h := hv.orderly (Fin.natAdd S.card (ladderEquiv S Q H p))
    rwa [appendFullCellsScheme_grade_natAdd] at h
  · have hloc := hv.locality (Fin.natAdd S.card (ladderEquiv S Q H c))
    have hb (p : LadderPt S Q H) : Fin.natAdd S.card (ladderEquiv S Q H p) ∈
        (codedLadderBase H prof hS).toCellScheme.below
          ((codedLadderBase H prof hS).toCellScheme.gradedIndex
            (Fin.natAdd S.card (ladderEquiv S Q H c))) := by
      rw [appendFullCellsScheme_gradedIndex_natAdd]; exact hmemp p
    have h := hloc.reindex fun p ↦ ⟨_, hb p⟩
    convert h using 1
    · funext p
      simp only [Function.comp_apply, appendFullCellsScheme_grade_natAdd]
    · funext p
      have h1 := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
        (r := codedBaseRow H prof) (h := hS) (ladderEquiv S Q H c) ⟨_, hb p⟩
      change _ = (codedLadderBase H prof hS).rows.row _ ⟨_, hb p⟩
      rw [h1, codedBaseRow_of_mem hwf _ (hmemp p), Equiv.symm_apply_apply, baseIndex_natAdd,
        Equiv.symm_apply_apply]
      rfl
    · rfl

/-- **Recognition on the ladder of the coded ladder base** (native construction): every lawful
section of the base is `⊥` on the ladder points, or there, for the member with the largest top
rung, the chart image of that member's coded table, `⊥` exactly at its index `0`
(`Label.CodedLadderLawful.exists_shape`). -/
theorem codedLadderBase_exists_shape [Nonempty Q] {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H)
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (codedLadderBase H prof hS).rows.IsLawful v) :
    (∀ p, v (Fin.natAdd _ (ladderEquiv S Q H p)) = ⊥) ∨
      ∃ (a : Q) (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ ∧
        (∀ p, v (Fin.natAdd _ (ladderEquiv S Q H p)) =
          min (σ (codedLadderSource H (ladderIndex H prof Prod.fst (ladderCeil prof) a p)))
            (g 1)) ∧
        ∀ p, v (Fin.natAdd _ (ladderEquiv S Q H p)) = ⊥ ↔
          ladderIndex H prof Prod.fst (ladderCeil prof) a p = 0 :=
  (codedLadderLawful_of_isLawful hwf hv).exists_shape hH (ladderCeil_le hprof)
    (fun a i ↦ (a, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ _ ↦ rfl)
    fun _ i hi ↦ by simp only [ladderCeil, Sum.elim_inl]; omega

end VaughtConjecture.Scheme
