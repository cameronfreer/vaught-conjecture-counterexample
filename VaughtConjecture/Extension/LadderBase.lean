/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FieldLayer
import VaughtConjecture.Label.FieldLadder

/-!
# The padded grade-one base: a scheme carrying the field ladder

Roadmap, Layer 3 ((R3) and (R4), the first layer of the recognizing growth carrier).

Let `S` be a scheme on `n` points with no cell above `(univ, 1)` (no cell of full scope), `Q` a
finite family of **members**, each with a rank vector `prof a : Fin S.card → ℕ` on all the cells of
`S` (the **complete table**: every cell, every grade), bounded by a height `H ≥ 1`.  The
**ladder base** (`Scheme.ladderBase`) appends to `S`, at `(univ, 1)`, the ladder points of
`Label.FieldLadder`: for each member `a`, the rungs `(a, i)` (`i < H`, ceiling `i + 1`) and the
shadows `(a, d)` of all cells `d` of `S` (ceiling `prof a d`). The row of a ladder point `c` of
member `a` reads the code (`Label.ladderSource`), at the ceiling of `c`, of the **base index** of
`a` (`Scheme.baseIndex`): at a ladder point its index `Label.ladderIndex` (the ceiling capped at
the cut of the rank vectors), at an old cell `d` of grade one the reader's own rank `prof a d`.
Base indices for two members agree capped at the cut of their rank vectors
(`Scheme.baseIndex_agree`, from `Label.rankAgree_rankCut` and `Label.ladderIndex_agree`).

## Main statements

* `Scheme.isLawful_baseRow`, `Scheme.isConsistent_ladderBase`: **consistency** — every row of a
  ladder point is lawful, given the **rank tables are lawful at grade one**
  (`Scheme.RankTablesLawful`: for each member, every positive table read at the member's ranks on
  the cells of grade one, `⊥` above, is lawful on `S`).
* `Scheme.isWellFormed_ladderBase`.
* `Scheme.isLawfulBelow_ladderBase_iff`, `Scheme.cappedLift_ladderBase_iff`: **off `(univ, 1)` the
  base is `S`**: lawfulness and capped lifts below pairs not above `(univ, 1)`, in particular from
  and between the original faces, are those of `S`.
* `Scheme.ladderLawful_of_isLawful`, `Scheme.ladderBase_exists_shape`: **recognition on the
  ladder** — every lawful section of the base, read on the ladder points, is lawful on the ladder
  table (`Label.LadderLawful`), hence is `⊥` there or the chart image of the table of the member
  with the largest top rung, `⊥` exactly at its index `0` (`Label.LadderLawful.exists_shape`).

## References

Witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9].
-/

universe u

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (Q : Type) [Fintype Q] (H : ℕ)

/-- The **ladder points**: for each member, the rungs and the shadows of all cells of `S`. -/
abbrev LadderPt : Type := Q × (Fin H ⊕ Fin S.card)

/-- The number of ladder points. -/
noncomputable abbrev ladderCard : ℕ := Fintype.card (LadderPt S Q H)

/-- The enumeration of the ladder points. -/
noncomputable def ladderEquiv : LadderPt S Q H ≃ Fin (ladderCard S Q H) := Fintype.equivFin _

variable {S Q} (prof : Q → Fin S.card → ℕ)

/-- The **ceiling** of a ladder point: `i + 1` at the rung `i`, the rank of the cell at a
shadow. -/
def ladderCeil {H : ℕ} (p : LadderPt S Q H) : ℕ :=
  Sum.elim (fun i : Fin H ↦ i.1 + 1) (fun d ↦ prof p.1 d) p.2

/-- The **base index** of the member `a` at a cell of the base: its rank at an old cell, the
ladder index at a ladder point. -/
noncomputable def baseIndex (a : Q) : Fin (S.card + ladderCard S Q H) → ℕ :=
  Fin.append (fun d ↦ prof a d)
    fun j ↦ ladderIndex H prof Prod.fst (ladderCeil prof) a ((ladderEquiv S Q H).symm j)

/-- The **row of a ladder point** of the base: the codes, at its ceiling, of the base indices of
its member, `⊥` at the old cells of grade other than one. -/
noncomputable def baseRow (i : Fin (ladderCard S Q H)) (t : Fin (S.card + ladderCard S Q H)) :
    Label.{u} :=
  Fin.append (fun d ↦ if S.toCellScheme.grade d = 1 then
      ladderSource (ladderCeil prof ((ladderEquiv S Q H).symm i))
        (baseIndex H prof ((ladderEquiv S Q H).symm i).1 (Fin.castAdd _ d)) else ⊥)
    (fun j ↦ ladderSource (ladderCeil prof ((ladderEquiv S Q H).symm i))
      (baseIndex H prof ((ladderEquiv S Q H).symm i).1 (Fin.natAdd _ j))) t

variable (S) in
/-- The scheme has no cell of full scope at grade one or above. -/
abbrev NoFullOne : Prop := ∀ d, ¬ ((univ : Finset (Fin n)), 1) ≤ S.toCellScheme.gradedIndex d

/-- **The ladder base**: `S` with the ladder points at `(univ, 1)`. -/
noncomputable abbrev ladderBase (hS : S.NoFullOne) : Scheme.{u} n :=
  S.appendFullCells 1 (ladderCard S Q H) (baseRow H prof) hS

/-! ### The base index -/

variable {H}

@[simp] theorem baseIndex_castAdd (a : Q) (d : Fin S.card) :
    baseIndex H prof a (Fin.castAdd _ d) = prof a d := Fin.append_left _ _ d

@[simp] theorem baseIndex_natAdd (a : Q) (j : Fin (ladderCard S Q H)) :
    baseIndex H prof a (Fin.natAdd _ j) =
      ladderIndex H prof Prod.fst (ladderCeil prof) a ((ladderEquiv S Q H).symm j) :=
  Fin.append_right _ _ j

variable {prof}

omit [Fintype Q] in
theorem ladderCeil_le (hprof : ∀ a d, prof a d ≤ H) (p : LadderPt S Q H) :
    ladderCeil prof p ≤ H := by
  rcases p with ⟨a, i | d⟩
  · exact i.isLt
  · exact hprof a d

theorem baseIndex_le (hprof : ∀ a d, prof a d ≤ H) (a : Q) (t : Fin (S.card + ladderCard S Q H)) :
    baseIndex H prof a t ≤ H := by
  induction t using Fin.addCases with
  | left d => rw [baseIndex_castAdd]; exact hprof a d
  | right j => rw [baseIndex_natAdd]; exact ladderIndex_le a _

/-- **Base indices of two members agree capped at the cut of their rank vectors.** -/
theorem baseIndex_agree (a b : Q) (t : Fin (S.card + ladderCard S Q H)) :
    min (baseIndex H prof a t) (rankCut H (prof a) (prof b)) =
      min (baseIndex H prof b t) (rankCut H (prof a) (prof b)) := by
  induction t using Fin.addCases with
  | left d => rw [baseIndex_castAdd, baseIndex_castAdd]; exact rankAgree_rankCut H _ _ d
  | right j => rw [baseIndex_natAdd, baseIndex_natAdd]; exact ladderIndex_agree a b _

/-- At its own ladder point a member's base index is the ceiling. -/
theorem baseIndex_self (hprof : ∀ a d, prof a d ≤ H) (p : LadderPt S Q H) :
    baseIndex H prof p.1 (Fin.natAdd _ (ladderEquiv S Q H p)) = ladderCeil prof p := by
  rw [baseIndex_natAdd, Equiv.symm_apply_apply]
  exact ladderIndex_parent (ladderCeil_le hprof) p

/-- A cell below `(univ, 1)` has grade one. -/
theorem grade_eq_one_of_mem_below {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    {t : Fin (S.card + ladderCard S Q H)}
    (ht : t ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1)) :
    (ladderBase H prof hS).toCellScheme.grade t = 1 := by
  have h1 : (ladderBase H prof hS).toCellScheme.grade t ≤ 1 := ht.2
  have h2 : 0 < (ladderBase H prof hS).toCellScheme.grade t := by
    induction t using Fin.addCases with
    | left d =>
      rw [appendFullCellsScheme_grade_castAdd]
      exact hwf.isWellFormed.grade_pos d
    | right j => rw [appendFullCellsScheme_grade_natAdd]; omega
  omega

/-- On the cells below `(univ, 1)` the row of a ladder point is the code of the base index. -/
theorem baseRow_of_mem {hS : S.NoFullOne} (hwf : S.IsWellFormed) (i : Fin (ladderCard S Q H))
    {t : Fin (S.card + ladderCard S Q H)}
    (ht : t ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1)) :
    baseRow H prof i t = ladderSource (ladderCeil prof ((ladderEquiv S Q H).symm i))
      (baseIndex H prof ((ladderEquiv S Q H).symm i).1 t) := by
  have hg := grade_eq_one_of_mem_below hwf ht
  induction t using Fin.addCases with
  | left d =>
    rw [appendFullCellsScheme_grade_castAdd] at hg
    unfold baseRow
    rw [Fin.append_left, ite_eq_left hg]
  | right j => unfold baseRow; rw [Fin.append_right]

/-! ### Consistency -/

variable (S H prof) in
/-- **The rank tables are lawful at grade one**: for each member, every positive table `f`
(monotone, `⊥` at `0`, self-visible at grade one, positive at `1, …, H`) read at the member's ranks
on the cells of grade one, `⊥` above, is a lawful section of `S`. -/
def RankTablesLawful : Prop :=
  ∀ (a : Q) (f : ℕ → Label.{u}), Monotone f → f 0 = ⊥ → (∀ i, IsSelfVisible 1 (f i)) →
    (∀ i, 0 < i → i ≤ H → f i ≠ ⊥) →
    S.rows.IsLawful fun d ↦ if S.toCellScheme.grade d = 1 then f (prof a d) else ⊥

/-- **The row of every ladder point is a lawful section of the base**, given lawful rank
tables. -/
theorem isLawful_baseRow {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hH : 0 < H)
    (hprof : ∀ a d, prof a d ≤ H) (hrank : RankTablesLawful S H prof)
    (i : Fin (ladderCard S Q H)) : (ladderBase H prof hS).rows.IsLawful (baseRow H prof i) := by
  classical
  set c := (ladderEquiv S Q H).symm i with hc
  set a := c.1 with ha
  set tc := ladderCeil prof c with htc
  -- the positive table of the row
  by_cases htc0 : tc = 0
  · -- the zero row
    have hz : baseRow H prof i = fun _ ↦ ⊥ := by
      funext t
      unfold baseRow
      induction t using Fin.addCases with
      | left d =>
        rw [Fin.append_left]
        split_ifs
        · rw [← hc, ← htc, htc0, (ladderSource_eq_bot_iff _ _).mpr (Nat.min_zero _)]
        · rfl
      | right j =>
        rw [Fin.append_right, ← hc, ← htc, htc0, (ladderSource_eq_bot_iff _ _).mpr (Nat.min_zero _)]
    rw [hz]
    exact CellScheme.Rows.isLawful_const_bot
  have hpos (k : ℕ) (hk : 0 < k) (_ : k ≤ H) : ladderSource.{u} tc k ≠ ⊥ := fun h0 ↦ by
    rw [ladderSource_eq_bot_iff] at h0; omega
  refine isLawful_appendFullCells ?_ (fun j ↦ by
      unfold baseRow; rw [Fin.append_right]; exact isSelfVisible_ladderSource _ _)
    (fun i' ↦ ?_) (fun s hs ↦ ?_)
  · -- on the old cells: a rank table
    have h := hrank a (ladderSource tc) (monotone_ladderSource _) (ladderSource_zero _)
      (isSelfVisible_ladderSource _) hpos
    convert h using 1
    funext d
    simp only [Function.comp_apply]
    unfold baseRow
    rw [Fin.append_left, baseIndex_castAdd]
  · -- locality at the ladder point `i'`
    set c' := (ladderEquiv S Q H).symm i' with hc'
    set e := baseIndex H prof a (Fin.natAdd _ i') with he
    have hec : e ≤ ladderCeil prof c' := by
      rw [he, baseIndex_natAdd]; exact min_le_right _ _
    have hecut : e ≤ rankCut H (prof a) (prof c'.1) := by
      rw [he, baseIndex_natAdd]; exact min_le_left _ _
    have hmem (t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i'))) :
        t.1 ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      refine ⟨subset_univ _, ?_⟩
      have h2 := t.2.2
      simp only [appendFullCellsScheme_gradedIndex_natAdd] at h2
      exact h2
    have hgr (t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i'))) :
        (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t = 1 :=
      grade_eq_one_of_mem_below hwf (hmem t)
    have hown : Fin.natAdd S.card i' ∈
        (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd]
    have htarget : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          min (baseRow H prof i t) (baseRow H prof i (Fin.natAdd _ i'))) =
        fun t ↦ ladderSource tc (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e) := by
      funext t
      rw [baseRow_of_mem hwf i (hmem t), baseRow_of_mem hwf i hown, ← hc, ← htc, ← ha, ← he,
        ← (monotone_ladderSource tc).map_min, min_assoc, min_eq_right hec,
        ← min_eq_right hecut, ← min_assoc, baseIndex_agree a c'.1 t.1, min_assoc]
    have hsource : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          baseRow H prof i' t.1) =
        fun t ↦ ladderSource (ladderCeil prof c') (baseIndex H prof c'.1 t.1) := by
      funext t
      exact baseRow_of_mem hwf i' (hmem t)
    have hgrade : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
        ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
          (S.appendFullCellsScheme 1 (ladderCard S Q H)).grade t) = fun _ ↦ 1 :=
      funext hgr
    rw [hsource, htarget, hgrade]
    by_cases he0 : e = 0
    · have hz : (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            ladderSource.{u} tc (min (min (baseIndex H prof c'.1 t.1) (ladderCeil prof c')) e)) =
          fun _ ↦ ⊥ := by
        funext t; rw [he0, Nat.min_zero, ladderSource_zero]
      rw [hz]
      exact TransformsTo.bot _ _
    · exact transformsTo_ladderSource (fun t : (S.appendFullCellsScheme 1 (ladderCard S Q H)).below
          ((S.appendFullCellsScheme 1 (ladderCard S Q H)).gradedIndex (Fin.natAdd _ i')) ↦
            baseIndex H prof c'.1 t.1) (by omega)
        (f := fun k ↦ ladderSource tc (min k e))
        (fun _ _ h ↦ monotone_ladderSource tc (min_le_min_right _ h))
        (by simp) (fun _ ↦ isSelfVisible_ladderSource _ _)
        fun k hk _ ↦ hpos _ (by omega) ((min_le_right _ _).trans
          (hecut.trans (rankCut_le H _ _)))
  · -- availability: the top rung of the member dominates
    have hHl : H - 1 < H := by omega
    refine ⟨ladderEquiv S Q H (a, Sum.inl ⟨H - 1, hHl⟩), ?_⟩
    have hs' : s ∈ (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) :=
      ⟨subset_univ _, hs.le⟩
    have htop : Fin.natAdd S.card (ladderEquiv S Q H (a, Sum.inl ⟨H - 1, hHl⟩)) ∈
        (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
      rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd]
    rw [baseRow_of_mem hwf i hs', baseRow_of_mem hwf i htop, ← hc, ← htc, ← ha,
      baseIndex_self hprof (a, Sum.inl ⟨H - 1, hHl⟩)]
    exact monotone_ladderSource tc ((baseIndex_le hprof a s).trans (by
      simp only [ladderCeil, Sum.elim_inl]; omega))

/-- **The ladder base is consistent**, given a consistent `S` and lawful rank tables. -/
theorem isConsistent_ladderBase {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hcons : S.rows.IsConsistent) (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H)
    (hrank : RankTablesLawful S H prof) : (ladderBase H prof hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦ isLawful_baseRow hwf hH hprof hrank i

/-- **The ladder base is well formed**, on at least one point. -/
theorem isWellFormed_ladderBase {hS : S.NoFullOne} (hwf : S.IsWellFormed) (hn : 1 ≤ n) :
    (ladderBase H prof hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf (by omega) hn

/-! ### Off the full face the base is `S` -/

/-- **Lawfulness below a pair not above `(univ, 1)`** in the base is lawfulness in `S`. -/
theorem isLawfulBelow_ladderBase_iff {hS : S.NoFullOne} {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), 1) ≤ X) {v : Fin (S.card + ladderCard S Q H) → Label.{u}} :
    (ladderBase H prof hS).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd _ d)) :=
  isLawfulBelow_appendFullCells_iff hX

/-- **Capped lifts below a pair not above `(univ, 1)`** in the base are those of `S`: in
particular the lifts from and between the original faces. -/
theorem cappedLift_ladderBase_iff {hS : S.NoFullOne} {X Y : Finset (Fin n) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin n)), 1) ≤ Y) :
    (ladderBase H prof hS).rows.CappedLift hXY ↔ S.rows.CappedLift hXY := by
  have h : S.toCellScheme.IsSourcePrefix (ladderBase H prof hS).toCellScheme (Fin.castAdd _) Y :=
    ⟨isLowerEmbedding_castAdd (S := S) 1 (ladderCard S Q H) (baseRow H prof) hS,
      appendFullCellsScheme_scope_castAdd S 1 _,
      fun d hd ↦ ⟨⟨d, lt_card_of_mem_below hY hd⟩, rfl⟩⟩
  rw [← h.cappedLift_iff hXY le_rfl, comap_rows_castAdd]

/-! ### Recognition on the ladder -/

/-- **A lawful section of the base is lawful on the ladder table**: read on the ladder points, it
is self-visible at grade one and local at every ladder point for its row
(`Label.LadderLawful`). -/
theorem ladderLawful_of_isLawful {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (ladderBase H prof hS).rows.IsLawful v) :
    LadderLawful H prof Prod.fst (ladderCeil prof)
      fun p ↦ v (Fin.natAdd _ (ladderEquiv S Q H p)) := by
  have hmemp (p : LadderPt S Q H) : Fin.natAdd S.card (ladderEquiv S Q H p) ∈
      (ladderBase H prof hS).toCellScheme.below ((univ : Finset (Fin n)), 1) := by
    rw [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd]
  refine ⟨fun p ↦ ?_, fun c ↦ ?_⟩
  · have h := hv.orderly (Fin.natAdd S.card (ladderEquiv S Q H p))
    rwa [appendFullCellsScheme_grade_natAdd] at h
  · have hloc := hv.locality (Fin.natAdd S.card (ladderEquiv S Q H c))
    have hb (p : LadderPt S Q H) : Fin.natAdd S.card (ladderEquiv S Q H p) ∈
        (ladderBase H prof hS).toCellScheme.below
          ((ladderBase H prof hS).toCellScheme.gradedIndex
            (Fin.natAdd S.card (ladderEquiv S Q H c))) := by
      rw [appendFullCellsScheme_gradedIndex_natAdd]; exact hmemp p
    have h := hloc.reindex fun p ↦ ⟨_, hb p⟩
    convert h using 1
    · funext p
      simp only [Function.comp_apply, appendFullCellsScheme_grade_natAdd]
    · funext p
      have h1 := appendFullCells_row_natAdd (S := S) (k := 1) (M := ladderCard S Q H)
        (r := baseRow H prof) (h := hS) (ladderEquiv S Q H c) ⟨_, hb p⟩
      change _ = (ladderBase H prof hS).rows.row _ ⟨_, hb p⟩
      rw [h1, baseRow_of_mem hwf _ (hmemp p), Equiv.symm_apply_apply, baseIndex_natAdd,
        Equiv.symm_apply_apply]
      rfl
    · rfl

/-- **Recognition on the ladder of the base**: every lawful section of the base is `⊥` on the
ladder points, or there, for the member with the largest top rung, the chart image of that member's
table, `⊥` exactly at its index `0` (`Label.LadderLawful.exists_shape`). -/
theorem ladderBase_exists_shape [Nonempty Q] {hS : S.NoFullOne} (hwf : S.IsWellFormed)
    (hH : 0 < H) (hprof : ∀ a d, prof a d ≤ H)
    {v : Fin (S.card + ladderCard S Q H) → Label.{u}}
    (hv : (ladderBase H prof hS).rows.IsLawful v) :
    (∀ p, v (Fin.natAdd _ (ladderEquiv S Q H p)) = ⊥) ∨
      ∃ (a : Q) (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}), IsWitness g σ ∧
        (∀ p, v (Fin.natAdd _ (ladderEquiv S Q H p)) =
          min (σ (ladderSource H (ladderIndex H prof Prod.fst (ladderCeil prof) a p))) (g 1)) ∧
        ∀ p, v (Fin.natAdd _ (ladderEquiv S Q H p)) = ⊥ ↔
          ladderIndex H prof Prod.fst (ladderCeil prof) a p = 0 :=
  (ladderLawful_of_isLawful hwf hv).exists_shape hH (ladderCeil_le hprof)
    (fun a i ↦ (a, Sum.inl ⟨min i (H - 1), by omega⟩)) (fun _ _ _ ↦ rfl)
    fun _ i hi ↦ by simp only [ladderCeil, Sum.elim_inl]; omega

end VaughtConjecture.Scheme
