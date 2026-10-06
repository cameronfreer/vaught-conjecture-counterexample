/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerStep
import VaughtConjecture.Extension.ThinCompletion

/-!
# The ordered-layer step for the seeds of `T5` with itself, below the top grade

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: the
ordered-layer step of `VaughtConjecture.Extension.OrderedLayerStep` for the seeds whose two coatom
types are `T5`, at the grades `k ≤ 3`); semantic contract, items 2–4.

Let `I` be a seed on five points whose two coatom types are `CaseSplitCounterexample.T5`, with
coatoms `C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}`; the seed `CaseSplitCounterexample.seed5` is one.

**The layer rows** (`rows5`): read off the kinds of `ThinCompletion.thinKind` (the dead cells, the
live cells of grade `1` of `C` carrying `A_C`, those of `D` carrying `A_D`, the live cells of
grade `2` carrying `F`, those of grade `3` carrying `G`, and the cells of grade `4`):

* at `(univ, 1)` and `(univ, 2)`, the ordered rows `ThinCompletion.thinRow 1` and
  `ThinCompletion.thinRow 2` of the thin completion of `seedL` (the live cells of grade `1` of `C`
  at `1`, strictly below those of `D` at `ω + 1`; the live cells of grade `2` at `ω·2 + 2`);
* at `(univ, 3)`, every live kind at the one value `ω + 3` (`rowThree`): `T5` on `C` couples
  `G ≤ A_C`, so the row of the thin completion of `seedL`, which reads `A_C` at `1` and the others
  at `ω + 3`, is not consistent here (its own labelling has `A_C = 1 < ω + 3 = G`);
* at `(univ, 4)`, the top row `OrderedLayer.topRow`.

**The lawful labellings below `(univ, 3)`** are exactly the thin labellings
(`ThinCompletion.thinLabel`) of parameters satisfying `IsThin5`: the constraints
`ThinCompletion.IsThinLawfulBelow` and the coupling `G ≤ A_C` of `T5` on `C`
(`isLawfulBelow_thinLabelling`, `exists_of_isLawfulBelow_three`).  At `(univ, 3)` the witness is the
top shifter: every live cell below it carries a label at least `G`.

**The lifts** (`exists_thin5Lift`): the parameter-level lift of `ThinCompletion.exists_thinLift`,
which also keeps `G ≤ A_C` (an unprescribed `A_C` at or above the cap is set to `max c G`).  The
lifts from `(C, 3)` and `(D, 3)` to `(univ, 3)` (`exists_lift_left`, `exists_lift_right`) are its
instances; the capped lifts at the grades `k ≤ 3` follow by `OrderedLayer.cappedLift_of_lift_three`.

**The theorem** (`orderedLayerStepBelowTop_of`, `orderedLayerStepBelowTop_seed5`): the
ordered-layer step below the top grade holds for every seed whose coatom types are `T5`, with the
rows `rows5`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.OrderedLayer.Seed5

open Finset Label CellScheme
open Ordinal hiding univ
open ThinCompletion (thinKind thinLabel kindLabel thinRow IsThinLawfulBelow thinKind_le
  snd_eq_kindGrade thinLabel_le thinLabel_eq_tripleLabelling thinKind_ne_one thinKind_ne_two
  thinLabel_congr_one thinLabel_congr_two min_thinLabel_eq transformsTo_rowOne transformsTo_rowTwo
  transformsTo_topShifter thinRow_lt)
open TwoFaceLiftExistsCounterexample (VisibilityReplaceFixedOfLT)
open CaseSplitCounterexample (T5 tripleLabelling)

/-! ### The layer rows -/

/-- The row at `(univ, 3)`, by kinds: every live kind of grade at most `3` at `ω + 3`. -/
noncomputable def rowThree : Fin 6 → Label.{u} :=
  kindLabel (gridPoint 3 1) (gridPoint 3 1) (gridPoint 3 1) (gridPoint 3 1) ⊥

/-- **The layer rows for the seeds of `T5` with itself**: the ordered rows of the thin completion
at `(univ, 1)` and `(univ, 2)`, `rowThree` at `(univ, 3)`, and the top row at `(univ, 4)`. -/
noncomputable def rows5 : LayerRows.{u}
  | 1 => fun X ↦ thinRow 1 (thinKind X)
  | 2 => fun X ↦ thinRow 2 (thinKind X)
  | 3 => fun X ↦ rowThree (thinKind X)
  | _ => topRow

/-- The layer row at `(univ, 4)` is the top row. -/
theorem rows5_four : rows5.{u} 4 = topRow := rfl

/-- The row at `(univ, 3)` is a thin labelling. -/
theorem rowThree_eq (X : Finset (Fin 5) × ℕ) :
    rowThree.{u} (thinKind X) =
      thinLabel (gridPoint 3 1) (gridPoint 3 1) (gridPoint 3 1) (gridPoint 3 1) ⊥ X := rfl

/-- The row at `(univ, 3)` is coded. -/
theorem rowThree_lt (i : Fin 6) :
    rowThree.{u} i < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have hb : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    WithBot.bot_lt_coe _
  fin_cases i <;> first | exact hb | exact gridPoint_lt_omega0_sq _ _

/-! ### The constraints -/

/-- **The constraints of the layer scheme of `rows5` below `(univ, 3)`**: those of the thin
completion, `ThinCompletion.IsThinLawfulBelow`, and the coupling `G ≤ A_C` of `T5` on `C`. -/
structure IsThin5 (AC AD F G : Label.{u}) : Prop where
  /-- The constraints of the thin completion. -/
  thin : IsThinLawfulBelow AC AD F G
  /-- The coupling of `T5` on `C`: `G ≤ A_C`. -/
  G_le_AC : G ≤ AC

/-- The row at `(univ, 3)` satisfies the constraints. -/
theorem isThin5_row_three :
    IsThin5 (gridPoint.{u} 3 1) (gridPoint 3 1) (gridPoint 3 1) (gridPoint 3 1) where
  thin :=
    { svAC := (isSelfVisible_gridPoint 3 1).mono (by omega)
      svAD := (isSelfVisible_gridPoint 3 1).mono (by omega)
      svF := (isSelfVisible_gridPoint 3 1).mono (by omega)
      svG := isSelfVisible_gridPoint 3 1
      le_AD := le_rfl
      G_le_F := le_rfl
      G_le_AD := le_rfl
      visibilityReplaceFixed := fun h ↦ absurd h (lt_irrefl _)
      noCollision := fun _ h ↦ absurd h (lt_irrefl _) }
  G_le_AC := le_rfl

/-- The row at `(univ, 2)` satisfies the constraints. -/
theorem isThin5_row_two : IsThin5 (gridPoint.{u} 1 0) (gridPoint 1 1) (gridPoint 2 2) ⊥ :=
  ⟨ThinCompletion.isThinLawfulBelow_row_two, bot_le⟩

/-- The row at `(univ, 1)` satisfies the constraints. -/
theorem isThin5_row_one : IsThin5 (gridPoint.{u} 1 0) (gridPoint 1 1) ⊥ ⊥ :=
  ⟨ThinCompletion.isThinLawfulBelow_row_one, bot_le⟩

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-! ### The rows of the new cells -/

/-- The row of the new cell at `(univ, k)`, `k ≤ 3`, is the thin labelling of the parameters of
its row. -/
theorem row_newCell_eq_thinLabel {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    ∃ AC AD F G : Label.{u}, IsThin5 AC AD F G ∧ ∀ X, rows5 k X = thinLabel AC AD F G ⊥ X := by
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · exact ⟨_, _, _, _, isThin5_row_one, fun _ ↦ rfl⟩
  · exact ⟨_, _, _, _, isThin5_row_two, fun _ ↦ rfl⟩
  · exact ⟨_, _, _, _, isThin5_row_three, fun _ ↦ rfl⟩

/-! ### Kinds and grades -/

/-- A cell below the new cell at `(univ, k)` has grade at most `k`. -/
theorem grade_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I rows5).toCellScheme.below
      ((layerScheme I rows5).toCellScheme.gradedIndex (newCell I rows5 k))) :
    (layerScheme I rows5).toCellScheme.grade t.1 ≤ k := by
  have h : (layerScheme I rows5).toCellScheme.gradedIndex t.1 ≤ ((univ : Finset (Fin 5)), k) :=
    gradedIndex_newCell hk1 hk4 ▸ t.2
  exact h.2

/-- The kind of a cell below the new cell at `(univ, k)` is at most `k + 1`. -/
theorem thinKind_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I rows5).toCellScheme.below
      ((layerScheme I rows5).toCellScheme.gradedIndex (newCell I rows5 k))) :
    (thinKind ((layerScheme I rows5).toCellScheme.gradedIndex t.1) : ℕ) ≤ k + 1 :=
  (thinKind_le _).trans (Nat.succ_le_succ (grade_le_of_mem_below_newCell hk1 hk4 t))

/-- The new cell at `(univ, k)` is below itself. -/
theorem newCell_mem_below_self {k : ℕ} :
    newCell I rows5 k ∈ (layerScheme I rows5).toCellScheme.below
      ((layerScheme I rows5).toCellScheme.gradedIndex (newCell I rows5 k)) :=
  (layerScheme I rows5).toCellScheme.mem_below_gradedIndex _

/-- An old cell below the new cell at `(univ, k)`, of grade at most `k`. -/
theorem oldCell_mem_below_newCell {d : Fin I.amalgam.card} {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hd : I.amalgam.toCellScheme.grade d ≤ k) :
    oldCell I rows5 d ∈ (layerScheme I rows5).toCellScheme.below
      ((layerScheme I rows5).toCellScheme.gradedIndex (newCell I rows5 k)) := by
  rw [gradedIndex_newCell hk1 hk4]
  exact oldCell_mem_below ⟨subset_univ _, hd⟩

/-- A cell below `(C, k)` misses the point `4`. -/
theorem four_notMem_of_mem_below {z : Fin (layerScheme I rows5).card} {k : ℕ}
    (hz : z ∈ (layerScheme I rows5).toCellScheme.below (coatomC, k)) :
    (4 : Fin 5) ∉ ((layerScheme I rows5).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.last 4) univ) (hz.1 h)

/-- A cell below `(D, k)` misses the point `3`. -/
theorem three_notMem_of_mem_below {z : Fin (layerScheme I rows5).card} {k : ℕ}
    (hz : z ∈ (layerScheme I rows5).toCellScheme.below (coatomD, k)) :
    (3 : Fin 5) ∉ ((layerScheme I rows5).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.castSucc (Fin.last 3)) univ) (hz.1 h)

/-! ### Lawful labellings below the two coatoms -/

variable (I) in
/-- The **thin labelling** of the cells of the layer scheme, read off their graded indices. -/
noncomputable def thinLabelling (AC AD F G Ω : Label.{u})
    (z : Fin (layerScheme I rows5).card) : Label.{u} :=
  thinLabel AC AD F G Ω ((layerScheme I rows5).toCellScheme.gradedIndex z)

/-- The thin labelling at the new cell at `(univ, k)`. -/
theorem thinLabelling_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (AC AD F G Ω : Label.{u}) :
    thinLabelling I AC AD F G Ω (newCell I rows5 k) =
      kindLabel AC AD F G Ω (thinKind ((univ : Finset (Fin 5)), k)) := by
  rw [thinLabelling, gradedIndex_newCell hk1 hk4]; rfl

variable (hIL : I.left = T5 α) (hIR : I.right = T5 α)

include hIL in
/-- **Lawful labellings below `(C, 3)`**: `thinLabel A ⊥ F G ⊥` with the constraints of `T5`. -/
theorem exists_of_isLawfulBelow_left {w : Fin (layerScheme I rows5).card → Label.{u}}
    (hw : (layerScheme I rows5).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧
      G ≤ F ∧ ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3),
        w z = thinLabel A ⊥ F G ⊥ ((layerScheme I rows5).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomC_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hall⟩ :=
    CaseSplitCounterexample.exists_labelling_of_comap (hIL ▸ I.restrictFace_left) le_rfl
      (fun d ↦ w (oldCell I rows5 d)) hw'
  refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ :=
    (image_oldCell_below (I := I) (ρ := rows5) (X := (coatomC, 3)) (by decide)).symm ▸ hz
  rw [coatomC_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, thinLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_left]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

include hIR in
/-- **Lawful labellings below `(D, 3)`**: `thinLabel ⊥ A F G ⊥` with the constraints of `T5`. -/
theorem exists_of_isLawfulBelow_right {w : Fin (layerScheme I rows5).card → Label.{u}}
    (hw : (layerScheme I rows5).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧
      G ≤ F ∧ ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3),
        w z = thinLabel ⊥ A F G ⊥ ((layerScheme I rows5).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomD_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hall⟩ :=
    CaseSplitCounterexample.exists_labelling_of_comap (hIR ▸ I.restrictFace_right) le_rfl
      (fun d ↦ w (oldCell I rows5 d)) hw'
  refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ :=
    (image_oldCell_below (I := I) (ρ := rows5) (X := (coatomD, 3)) (by decide)).symm ▸ hz
  rw [coatomD_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, thinLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_right]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

/-! ### Sufficiency: the thin labellings are lawful below `(univ, 3)` -/

include hIL hIR in
/-- **The thin labellings are lawful below the coatoms** at the grade `3`: on the old cells they
are the labellings `tripleLabelling A_C F A_D F G`. -/
theorem isLawfulBelow_coatom_thinLabelling {AC AD F G Ω : Label.{u}} (h : IsThin5 AC AD F G) :
    (layerScheme I rows5).rows.IsLawfulBelow (coatomC, 3)
        (fun z ↦ thinLabelling I AC AD F G Ω z) ∧
      (layerScheme I rows5).rows.IsLawfulBelow (coatomD, 3)
        (fun z ↦ thinLabelling I AC AD F G Ω z) := by
  have hCD := CaseSplitCounterexample.isLawfulBelow_tripleLabelling (I := I) hIL hIR h.thin.svAC
    h.thin.svF h.thin.svAD h.thin.svF h.thin.svG h.G_le_AC h.thin.G_le_F h.thin.G_le_AD
    h.thin.G_le_F
  have key (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      thinLabelling I AC AD F G Ω (oldCell I rows5 d) =
        tripleLabelling AC F AD F G (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [thinLabelling, gradedIndex_oldCell]
    exact thinLabel_eq_tripleLabelling (I.scope_ne_univ d)
      (show I.amalgam.toCellScheme.grade d ≠ 4 by omega) _ _ _ _ _
  constructor
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomC, 3))
      fun d hd ↦ (key d hd.2).symm).mp hCD.1
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomD, 3))
      fun d hd ↦ (key d hd.2).symm).mp hCD.2

/-- The row at `(univ, 3)` transforms, through the top shifter, to `G` at every live kind of grade
at most `3`, under `G ≤ A_C`, `G ≤ A_D` and `G ≤ F`. -/
theorem transformsTo_rowThree {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 3) (hk : ∀ d, (kind d : ℕ) ≤ 4) {AC AD F G Ω : Label.{u}}
    (hG : IsSelfVisible 3 G) (hGAC : G ≤ AC) (hGAD : G ≤ AD) (hGF : G ≤ F) :
    TransformsTo grade (fun d ↦ rowThree (kind d))
      (fun d ↦ min (kindLabel AC AD F G Ω (kind d)) G) := by
  refine transformsTo_topShifter grade hgr hG _ _ fun d ↦ ?_
  have h := hk d
  generalize kind d = k at h ⊢
  fin_cases k
  · simp [rowThree, kindLabel]
  · simp [rowThree, kindLabel, gridPoint_ne_bot, hGAC]
  · simp [rowThree, kindLabel, gridPoint_ne_bot, hGAD]
  · simp [rowThree, kindLabel, gridPoint_ne_bot, hGF]
  · simp [rowThree, kindLabel, gridPoint_ne_bot]
  · exact absurd h (by decide)

include hIL hIR in
/-- **Sufficiency**: the thin labelling of parameters satisfying `IsThin5` is lawful below
`(univ, 3)`. -/
theorem isLawfulBelow_thinLabelling {AC AD F G Ω : Label.{u}} (h : IsThin5 AC AD F G) :
    (layerScheme I rows5).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      (fun z ↦ thinLabelling I AC AD F G Ω z) := by
  obtain ⟨hC, hD⟩ := isLawfulBelow_coatom_thinLabelling hIL hIR (Ω := Ω) h
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hD
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hne : (layerScheme I rows5).toCellScheme.scope d = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hd.2
      rw [grade_newCell hj1 hj4, thinLabelling_newCell hj1 hj4]
      obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact h.thin.svAD
      · exact h.thin.svF
      · exact h.thin.svG
    · exact (mem_below_coatom_of_ne hd hne).elim (hoC d) (hoD d)
  · rcases cell_cases s with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
    · exact (mem_below_coatom_of_ne hs (scope_oldCell_ne d)).elim (hlC _) (hlD _)
    · rw [row_newCell_eq le_rfl (by omega), thinLabelling_newCell le_rfl (by omega)]
      exact transformsTo_rowOne _
        (fun t ↦ thinKind ((layerScheme I rows5).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell le_rfl (by omega))
        (thinKind_le_of_mem_below_newCell le_rfl (by omega)) h.thin.svAC h.thin.svAD h.thin.le_AD
    · rw [row_newCell_eq (by omega) (by omega), thinLabelling_newCell (by omega) (by omega)]
      exact transformsTo_rowTwo _
        (fun t ↦ thinKind ((layerScheme I rows5).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (thinKind_le_of_mem_below_newCell (by omega) (by omega)) h.thin.svAC h.thin.svAD
        h.thin.svF h.thin.le_AD h.thin.noCollision
    · rw [row_newCell_eq (by omega) (by omega), thinLabelling_newCell (by omega) (by omega)]
      exact transformsTo_rowThree _
        (fun t ↦ thinKind ((layerScheme I rows5).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (thinKind_le_of_mem_below_newCell (by omega) (by omega)) h.thin.svG h.G_le_AC
        h.thin.G_le_AD h.thin.G_le_F
    · have h4 : (layerScheme I rows5).toCellScheme.gradedIndex (newCell I rows5 4) ≤
          ((univ : Finset (Fin 5)), 3) := hs
      rw [gradedIndex_newCell (by omega) le_rfl] at h4
      exact absurd h4.2 (by decide)
  · by_cases hne : (layerScheme I rows5).toCellScheme.scope t = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      refine ⟨newCell I rows5 j, rfl, ?_⟩
      rw [thinLabelling_newCell hj1 hj4]
      exact thinLabel_le h.thin.le_AD (hg.trans (grade_newCell hj1 hj4)) hj1 hj4
    · exact (mem_below_coatom_of_ne ht hne).elim (haC s t · hst hg) (haD s t · hst hg)

/-! ### Necessity: the lawful labellings below `(univ, 3)` are thin -/

include hIL hIR in
/-- **Necessity**: every labelling lawful below `(univ, 3)` is a thin labelling, of parameters
satisfying `IsThin5`.  On each coatom it is a labelling of `T5`; locality and availability at the
new cells identify `A_D`, `F` (on both coatoms) and `G` with their labels, and give `A_C ≤ A_D`;
the collision lemma at the new cell at `(univ, 2)` excludes collisions. -/
theorem exists_of_isLawfulBelow_three {w : Fin (layerScheme I rows5).card → Label.{u}}
    (hw : (layerScheme I rows5).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ w z) :
    ∃ AC AD F G : Label.{u}, IsThin5 AC AD F G ∧
      ∀ z ∈ (layerScheme I rows5).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        w z = thinLabelling I AC AD F G ⊥ z := by
  -- Step 1: below each coatom, `w` is a labelling of `T5`.
  have hC : (layerScheme I rows5).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z :=
    hw.mono (X := (coatomC, 3)) ⟨subset_univ _, le_rfl⟩
  have hD : (layerScheme I rows5).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z :=
    hw.mono (X := (coatomD, 3)) ⟨subset_univ _, le_rfl⟩
  obtain ⟨AC, FC, GC, hAC, hFC, hGC, hGAC, hGFC, hC'⟩ := exists_of_isLawfulBelow_left hIL hC
  obtain ⟨AD, FD, GD, hAD, hFD, hGD, hGAD, hGFD, hD'⟩ := exists_of_isLawfulBelow_right hIR hD
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  -- Step 2: the old cells used, one of each live kind, and their labels.
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hw₁ : w (oldCell I rows5 d₁) = AC := by
    rw [hC' _ (oldCell_mem_below (by rw [hd₁]; decide)), gradedIndex_oldCell, hd₁]; rfl
  have hwsC : w (oldCell I rows5 sC) = FC := by
    rw [hC' _ (oldCell_mem_below (by rw [hsC]; decide)), gradedIndex_oldCell, hsC]; rfl
  have hwgC : w (oldCell I rows5 gE) = GC := by
    rw [hC' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hwgD : w (oldCell I rows5 gE) = GD := by
    rw [hD' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hw₂ : w (oldCell I rows5 d₂) = AD := by
    rw [hD' _ (oldCell_mem_below (by rw [hd₂]; decide)), gradedIndex_oldCell, hd₂]; rfl
  have hwsD : w (oldCell I rows5 sD) = FD := by
    rw [hD' _ (oldCell_mem_below (by rw [hsD]; decide)), gradedIndex_oldCell, hsD]; rfl
  have hGCD : GC = GD := hwgC.symm.trans hwgD
  -- Step 3: locality (`hle`) and availability (`hge`) at the new cell at `(univ, k)` compare its
  -- label with that of an old cell of grade `k`.
  have hrow {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      (layerScheme I rows5).rows.row (newCell I rows5 k)
          ⟨oldCell I rows5 d, oldCell_mem_below_newCell hk1 hk4 hd⟩ =
        rows5 k (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [row_newCell hk1 hk4, gradedIndex_oldCell]
  have hrowself {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
      (layerScheme I rows5).rows.row (newCell I rows5 k) ⟨newCell I rows5 k, newCell_mem_below_self⟩
        = rows5 k ((univ : Finset (Fin 5)), k) := by
    rw [row_newCell hk1 hk4, gradedIndex_newCell hk1 hk4]
  have hle {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k)
      (hr : rows5 k ((univ : Finset (Fin 5)), k) ≤
        rows5 k (I.amalgam.toCellScheme.gradedIndex d)) :
      w (newCell I rows5 k) ≤ w (oldCell I rows5 d) := by
    have := (hl _ (newCell_mem_below hk1 (by omega) hk3)).le_of_le
      (d := ⟨newCell I rows5 k, newCell_mem_below_self⟩)
      (d' := ⟨oldCell I rows5 d, oldCell_mem_below_newCell hk1 (by omega) hd.le⟩)
      (by rw [hrowself hk1 (by omega), hrow hk1 (by omega) hd.le]; exact hr)
      (show (layerScheme I rows5).toCellScheme.grade (oldCell I rows5 d) ≤
          (layerScheme I rows5).toCellScheme.grade (newCell I rows5 k) by
        rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have hge {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k) :
      w (oldCell I rows5 d) ≤ w (newCell I rows5 k) := by
    obtain ⟨u, hu, hle⟩ := ha (oldCell I rows5 d) (newCell I rows5 k)
      (newCell_mem_below hk1 (by omega) hk3)
      (by rw [scope_newCell hk1 (by omega)]; exact subset_univ _)
      (by rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    rwa [eq_newCell hk1 (by omega) (hu.trans (gradedIndex_newCell hk1 (by omega)))] at hle
  have hn₁ : w (newCell I rows5 1) = AD := by
    rw [← hw₂]
    exact le_antisymm (hle le_rfl (by omega) (congrArg Prod.snd hd₂) (by rw [hd₂]; rfl))
      (hge le_rfl (by omega) (congrArg Prod.snd hd₂))
  have hn₂C : w (newCell I rows5 2) = FC := by
    rw [← hwsC]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsC) (by rw [hsC]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsC))
  have hn₂D : w (newCell I rows5 2) = FD := by
    rw [← hwsD]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsD) (by rw [hsD]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsD))
  have hn₃ : w (newCell I rows5 3) = GC := by
    rw [← hwgC]
    exact le_antisymm (hle (by omega) le_rfl (congrArg Prod.snd hgE) (by rw [hgE]; rfl))
      (hge (by omega) le_rfl (congrArg Prod.snd hgE))
  have hACAD : AC ≤ AD := hw₁ ▸ hn₁ ▸ hge le_rfl (by omega) (congrArg Prod.snd hd₁)
  have hFCD : FC = FD := hn₂C.symm.trans hn₂D
  -- Step 4: no collision, by the collision lemma at the new cell at `(univ, 2)`.
  have hnc : AC = AD → AC < FC → IsSelfVisible 2 AC := by
    intro heq hlt
    by_contra hev
    have hg₁' : I.amalgam.toCellScheme.grade d₁ = 1 := congrArg Prod.snd hd₁
    have hg₂' : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
    have hg₁ : I.amalgam.toCellScheme.grade d₁ ≤ 2 := by omega
    have hg₂ : I.amalgam.toCellScheme.grade d₂ ≤ 2 := by omega
    have := eq_of_transformsTo_collision
      (hl _ (newCell_mem_below (by omega) (by omega) (by omega)))
      (d₁ := ⟨oldCell I rows5 d₁, oldCell_mem_below_newCell (by omega) (by omega) hg₁⟩)
      (d₂ := ⟨oldCell I rows5 d₂, oldCell_mem_below_newCell (by omega) (by omega) hg₂⟩)
      (z := ⟨newCell I rows5 2, newCell_mem_below_self⟩)
      ((grade_oldCell d₁).trans hg₁') ((grade_oldCell d₂).trans hg₂')
      (grade_newCell (by omega) (by omega))
      (by rw [hrow (by omega) (by omega) hg₁, hd₁]; exact isSelfVisible_gridPoint 1 0)
      (by rw [hrow (by omega) (by omega) hg₂, hd₂]; exact isSelfVisible_gridPoint 1 1)
      (e := AC) (by simp only; rw [hw₁, hn₂C, min_eq_left hlt.le])
      (by simp only; rw [hw₂, hn₂C, ← heq, min_eq_left hlt.le]) hev
      (by simp only; rw [hn₂C, min_self]; exact hlt)
    rw [hrow (by omega) (by omega) hg₁, hrow (by omega) (by omega) hg₂, hd₁, hd₂] at this
    exact absurd this (gridPoint_lt_gridPoint.mpr (by omega)).ne
  -- Step 5: `w` is the thin labelling of these parameters.
  refine ⟨AC, AD, FC, GC, ⟨⟨hAC, hAD, hFC, hGC, hACAD, hGFC, hGCD ▸ hGAD,
    fun hlt ↦ absurd hlt (not_lt.mpr hGAC), hnc⟩, hGAC⟩, fun z hz ↦ ?_⟩
  by_cases hne : (layerScheme I rows5).toCellScheme.scope z = univ
  · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
    have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hz.2
    rw [thinLabelling_newCell hj1 hj4]
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · exact hn₁
    · exact hn₂C
    · exact hn₃
  · rcases mem_below_coatom_of_ne hz hne with h | h
    · rw [hC' z h, thinLabelling]
      exact thinLabel_congr_two (thinKind_ne_two (four_notMem_of_mem_below h)) _ _ _ _ _ _
    · rw [hD' z h, thinLabelling, ← hFCD, ← hGCD]
      exact thinLabel_congr_one (thinKind_ne_one (three_notMem_of_mem_below h)) _ _ _ _ _ _

/-! ### The parameter-level capped lift -/

/-- The lifted value of a parameter: the prescription if there is one; otherwise the ambient
value if it lies below the cap, and the value `hi ≥ c` otherwise. -/
private noncomputable def liftedParam (P : Option Label.{u}) (qz c hi : Label.{u}) : Label.{u} :=
  open Classical in P.getD (if qz < c then qz else hi)

section Choose

variable {P : Option Label.{u}} {qz c hi : Label.{u}}

/-- The chosen value agrees with the ambient value capped at `c`. -/
private theorem min_liftedParam (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi) :
    min (liftedParam P qz c hi) c = min qz c := by
  unfold liftedParam
  cases P with
  | some a => exact hP a rfl
  | none =>
    simp only [Option.getD_none]
    split_ifs with h
    · rfl
    · rw [min_eq_right hhi, min_eq_right (not_lt.mp h)]

/-- A chosen value below the cap is the ambient value. -/
private theorem liftedParam_eq_of_lt (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi)
    (h : liftedParam P qz c hi < c) : liftedParam P qz c hi = qz := by
  have hm := min_liftedParam hP hhi
  rw [min_eq_left h.le] at hm
  rcases lt_or_ge qz c with hq | hq
  · rw [min_eq_left hq.le] at hm; exact hm
  · rw [min_eq_right hq] at hm; exact absurd hm h.ne

/-- At an ambient value below the cap, the chosen value is the ambient value. -/
private theorem liftedParam_eq_of_q_lt (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi)
    (h : qz < c) : liftedParam P qz c hi = qz := by
  have hm := min_liftedParam hP hhi
  rw [min_eq_left h.le] at hm
  rcases lt_or_ge (liftedParam P qz c hi) c with hx | hx
  · rw [min_eq_left hx.le] at hm; exact hm
  · rw [min_eq_right hx] at hm; exact absurd hm h.ne'

/-- A chosen value at least the cap comes from an ambient value at least the cap. -/
private theorem le_of_le_liftedParam (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi)
    (h : c ≤ liftedParam P qz c hi) : c ≤ qz := by
  have hm := min_liftedParam hP hhi
  rw [min_eq_right h] at hm
  exact min_eq_right_iff.mp hm.symm

/-- Unprescribed, at an ambient value at least the cap, the chosen value is `hi`. -/
private theorem liftedParam_none_of_le (h : c ≤ qz) : liftedParam none qz c hi = hi := by
  unfold liftedParam; simp [not_lt.mpr h]

/-- A prescribed value is chosen. -/
private theorem liftedParam_some (a : Label.{u}) : liftedParam (some a) qz c hi = a := rfl

end Choose

/-- A monotone constraint survives the choice if it holds for the ambient and for the values at
or above the cap. -/
private theorem le_of_approx {c xz xw qz qw : Label.{u}} (hq : qz ≤ qw)
    (hz' : qz < c → xz = qz) (hw : xw < c → xw = qw)
    (hhigh : c ≤ xz → c ≤ xw → xz ≤ xw) : xz ≤ xw := by
  by_cases hwc : xw < c
  · rw [hw hwc]
    have : qz < c := hq.trans_lt ((hw hwc) ▸ hwc)
    rw [hz' this]; exact hq
  · by_cases hzc : xz < c
    · exact hzc.le.trans (not_lt.mp hwc)
    · exact hhigh (not_lt.mp hzc) (not_lt.mp hwc)

/-- **The parameter-level capped lift for `IsThin5`.**  As `ThinCompletion.exists_thinLift`, with
the coupling `G ≤ A_C` in place of `VisibilityReplaceFixedOfLT A_C G` (which it implies): let the
ambient `q` satisfy `IsThin5`, `c` be a cap, and a prescription fix some of the parameters, subject
to the constraints among themselves and agreeing with `q` capped at `c`.  Then some `x` satisfies
`IsThin5`, agrees with `q` capped at `c`, and equals the prescription where it is given.  The
choice: an unprescribed parameter keeps its ambient value below the cap; at or above the cap,
`G := c`, `A_D := ⊤`, and `F, A_C := max c G`. -/
theorem exists_thin5Lift {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {PAC PAD PF PG : Option Label.{u}}
    (hc2 : IsSelfVisible 2 c ∨ PF = some ⊥) (hc3 : IsSelfVisible 3 c ∨ PG.isSome)
    {qAC qAD qF qG : Label.{u}} (hq : IsThin5 qAC qAD qF qG)
    (svAC : ∀ a ∈ PAC, IsSelfVisible 1 a) (svAD : ∀ a ∈ PAD, IsSelfVisible 1 a)
    (svF : ∀ a ∈ PF, IsSelfVisible 2 a) (svG : ∀ a ∈ PG, IsSelfVisible 3 a)
    (pleAD : ∀ a ∈ PAC, ∀ b ∈ PAD, a ≤ b) (pGF : ∀ g ∈ PG, ∀ f ∈ PF, g ≤ f)
    (pGAD : ∀ g ∈ PG, ∀ b ∈ PAD, g ≤ b) (pGAC : ∀ g ∈ PG, ∀ a ∈ PAC, g ≤ a)
    (pnc : ∀ a ∈ PAC, ∀ b ∈ PAD, ∀ f ∈ PF, a = b → a < f → IsSelfVisible 2 a)
    (hAC : ∀ a ∈ PAC, min a c = min qAC c) (hAD : ∀ a ∈ PAD, min a c = min qAD c)
    (hF : ∀ a ∈ PF, min a c = min qF c) (hG : ∀ a ∈ PG, min a c = min qG c) :
    ∃ xAC xAD xF xG : Label.{u}, IsThin5 xAC xAD xF xG ∧
      min xAC c = min qAC c ∧ min xAD c = min qAD c ∧ min xF c = min qF c ∧
      min xG c = min qG c ∧
      (∀ a ∈ PAC, xAC = a) ∧ (∀ a ∈ PAD, xAD = a) ∧ (∀ a ∈ PF, xF = a) ∧ (∀ a ∈ PG, xG = a) := by
  set xG := liftedParam PG qG c c with hxG
  set xAD := liftedParam PAD qAD c ⊤ with hxAD
  set xF := liftedParam PF qF c (max c xG) with hxF
  set xAC := liftedParam PAC qAC c (max c xG) with hxAC
  have hcG : c ≤ c := le_rfl
  have hcT : c ≤ ⊤ := le_top
  have hcM : c ≤ max c xG := le_max_left _ _
  -- The approximation facts.
  have eG : xG < c → xG = qG := liftedParam_eq_of_lt hG hcG
  have eG' : qG < c → xG = qG := liftedParam_eq_of_q_lt hG hcG
  have eAD : xAD < c → xAD = qAD := liftedParam_eq_of_lt hAD hcT
  have eF : xF < c → xF = qF := liftedParam_eq_of_lt hF hcM
  have eAC : xAC < c → xAC = qAC := liftedParam_eq_of_lt hAC hcM
  have eAC' : qAC < c → xAC = qAC := liftedParam_eq_of_q_lt hAC hcM
  -- Values at or above the cap, unprescribed.
  have hiG : PG = none → c ≤ xG → xG = c := fun h hle ↦ by
    have hq' : c ≤ qG := le_of_le_liftedParam hG hcG hle
    rw [hxG, h]; exact liftedParam_none_of_le hq'
  have hiAD : PAD = none → c ≤ xAD → xAD = ⊤ := fun h hle ↦ by
    have hq' : c ≤ qAD := le_of_le_liftedParam hAD hcT hle
    rw [hxAD, h]; exact liftedParam_none_of_le hq'
  have hiF : PF = none → c ≤ xF → xF = max c xG := fun h hle ↦ by
    have hq' : c ≤ qF := le_of_le_liftedParam hF hcM hle
    rw [hxF, h]; exact liftedParam_none_of_le hq'
  have hiAC : PAC = none → c ≤ xAC → xAC = max c xG := fun h hle ↦ by
    have hq' : c ≤ qAC := le_of_le_liftedParam hAC hcM hle
    rw [hxAC, h]; exact liftedParam_none_of_le hq'
  -- Self-visibility.
  have hsvG : IsSelfVisible 3 xG := by
    cases hPG : PG with
    | some g => rw [hxG, hPG, liftedParam_some]; exact svG g hPG
    | none =>
      rcases lt_or_ge xG c with h | h
      · rw [eG h]; exact hq.thin.svG
      · rw [hiG hPG h]
        exact hc3.resolve_right (by rw [hPG]; simp)
  have hsvAD : IsSelfVisible 1 xAD := by
    cases hPAD : PAD with
    | some b => rw [hxAD, hPAD, liftedParam_some]; exact svAD b hPAD
    | none =>
      rcases lt_or_ge xAD c with h | h
      · rw [eAD h]; exact hq.thin.svAD
      · rw [hiAD hPAD h]; exact isSelfVisible_top 1
  have hsvF : IsSelfVisible 2 xF := by
    cases hPF : PF with
    | some f => rw [hxF, hPF, liftedParam_some]; exact svF f hPF
    | none =>
      rcases lt_or_ge xF c with h | h
      · rw [eF h]; exact hq.thin.svF
      · rw [hiF hPF h]
        exact (hc2.resolve_right (by rw [hPF]; simp)).max (hsvG.mono (by omega))
  have hsvAC : IsSelfVisible 1 xAC := by
    cases hPAC : PAC with
    | some a => rw [hxAC, hPAC, liftedParam_some]; exact svAC a hPAC
    | none =>
      rcases lt_or_ge xAC c with h | h
      · rw [eAC h]; exact hq.thin.svAC
      · rw [hiAC hPAC h]; exact hc1.max (hsvG.mono (by omega))
  -- `G ≤ A_D`.
  have hGAD : xG ≤ xAD := le_of_approx hq.thin.G_le_AD eG' eAD fun hz hw ↦ by
    cases hPAD : PAD with
    | none => rw [hiAD hPAD hw]; exact le_top
    | some b =>
      have hxb : xAD = b := by rw [hxAD, hPAD, liftedParam_some]
      cases hPG : PG with
      | some g =>
        have hxg : xG = g := by rw [hxG, hPG, liftedParam_some]
        rw [hxg, hxb]; exact pGAD g hPG b hPAD
      | none => rw [hiG hPG hz]; exact hw
  -- `G ≤ A_C`.
  have hGAC : xG ≤ xAC := le_of_approx hq.G_le_AC eG' eAC fun hz hw ↦ by
    cases hPAC : PAC with
    | none => rw [hiAC hPAC hw]; exact le_max_right _ _
    | some a =>
      have hxa : xAC = a := by rw [hxAC, hPAC, liftedParam_some]
      cases hPG : PG with
      | some g =>
        have hxg : xG = g := by rw [hxG, hPG, liftedParam_some]
        rw [hxg, hxa]; exact pGAC g hPG a hPAC
      | none => rw [hiG hPG hz]; exact hw
  -- `A_C ≤ A_D`.
  have hACAD : xAC ≤ xAD := le_of_approx hq.thin.le_AD eAC' eAD fun hz hw ↦ by
    cases hPAD : PAD with
    | none => rw [hiAD hPAD hw]; exact le_top
    | some b =>
      have hxb : xAD = b := by rw [hxAD, hPAD, liftedParam_some]
      cases hPAC : PAC with
      | some a =>
        have hxa : xAC = a := by rw [hxAC, hPAC, liftedParam_some]
        rw [hxa, hxb]; exact pleAD a hPAC b hPAD
      | none => rw [hiAC hPAC hz]; exact max_le hw hGAD
  -- `G ≤ F`.
  have hGF : xG ≤ xF := le_of_approx hq.thin.G_le_F eG' eF fun hz hw ↦ by
    cases hPF : PF with
    | none => rw [hiF hPF hw]; exact le_max_right _ _
    | some f =>
      have hxf : xF = f := by rw [hxF, hPF, liftedParam_some]
      cases hPG : PG with
      | some g =>
        have hxg : xG = g := by rw [hxG, hPG, liftedParam_some]
        rw [hxg, hxf]; exact pGF g hPG f hPF
      | none => rw [hiG hPG hz]; exact hw
  -- No collision.
  have hnc : xAC = xAD → xAC < xF → IsSelfVisible 2 xAC := by
    intro heq hlt
    rcases lt_or_ge xAC c with hz | hz
    · have hqAC := eAC hz
      have hqAD : xAD = qAD := eAD (heq ▸ hz)
      have hqlt : qAC < qF := by
        rcases lt_or_ge xF c with hf | hf
        · rw [← hqAC, ← eF hf]; exact hlt
        · exact (hqAC ▸ hz).trans_le (le_of_le_liftedParam hF hcM hf)
      rw [hqAC]
      exact hq.thin.noCollision (by rw [← hqAC, ← hqAD]; exact heq) hqlt
    · have hw : c ≤ xAD := heq ▸ hz
      cases hPAD : PAD with
      | none => rw [heq, hiAD hPAD hw]; exact isSelfVisible_top 2
      | some b =>
        cases hPF : PF with
        | none =>
          exfalso
          refine absurd hlt (not_lt.mpr ?_)
          rw [heq]
          rcases lt_or_ge xF c with hf | hf
          · exact hf.le.trans hw
          · rw [hiF hPF hf]; exact max_le hw hGAD
        | some f =>
          have hxf : xF = f := by rw [hxF, hPF, liftedParam_some]
          cases hPAC : PAC with
          | some a =>
            have hxa : xAC = a := by rw [hxAC, hPAC, liftedParam_some]
            have hxb : xAD = b := by rw [hxAD, hPAD, liftedParam_some]
            rw [hxa] at heq hlt ⊢; rw [hxb] at heq; rw [hxf] at hlt
            exact pnc a hPAC b hPAD f hPF heq hlt
          | none =>
            rw [hiAC hPAC hz]
            rcases hc2 with hc2 | hc2
            · exact hc2.max (hsvG.mono (by omega))
            · rw [hPF] at hc2
              rw [hxf, Option.some_inj.mp hc2] at hlt
              exact absurd hlt (not_lt.mpr bot_le)
  refine ⟨xAC, xAD, xF, xG,
    ⟨⟨hsvAC, hsvAD, hsvF, hsvG, hACAD, hGF, hGAD,
      fun hlt ↦ absurd hlt (not_lt.mpr hGAC), hnc⟩, hGAC⟩,
    min_liftedParam hAC hcM, min_liftedParam hAD hcT, min_liftedParam hF hcM,
    min_liftedParam hG hcG,
    fun a ha ↦ by rw [hxAC, Option.mem_def.mp ha, liftedParam_some],
    fun a ha ↦ by rw [hxAD, Option.mem_def.mp ha, liftedParam_some],
    fun a ha ↦ by rw [hxF, Option.mem_def.mp ha, liftedParam_some],
    fun a ha ↦ by rw [hxG, Option.mem_def.mp ha, liftedParam_some]⟩

/-! ### The lifts from the coatoms at the grade `3` -/

/-- A property of `a` holds at every member of `some a`. -/
private theorem forall_mem_some {β : Type*} {a : β} {P : β → Prop} (h : P a) : ∀ b ∈ some a, P b :=
  fun _ hb ↦ (Option.some_inj.mp hb) ▸ h

/-- Every property holds at every member of `none`. -/
private theorem forall_mem_none {β : Type*} {P : β → Prop} : ∀ b ∈ (none : Option β), P b :=
  fun _ hb ↦ by cases hb

include hIL hIR in
/-- **The lift from `(C, 3)` to `(univ, 3)`**, for a cap `c` self-visible at `1`, and at `2` unless
the prescription is `⊥` at the grade `2`: the parameters of the prescription (`T5`) and of the
ambient (`IsThin5`) are lifted by `exists_thin5Lift`, with `A_D` unprescribed. -/
theorem exists_lift_left {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {p q : Fin (layerScheme I rows5).card → Label.{u}}
    (hp : (layerScheme I rows5).rows.IsLawfulBelow (coatomC, 3) fun z ↦ p z)
    (hq : (layerScheme I rows5).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3),
      min (q z) c = min (p z) c)
    (hc2 : IsSelfVisible 2 c ∨ ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3),
      (layerScheme I rows5).toCellScheme.grade z = 2 → p z = ⊥) :
    ∃ x : Fin (layerScheme I rows5).card → Label.{u},
      (layerScheme I rows5).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I rows5).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3), x z = p z := by
  -- Step 1: the parameters of the prescription (a labelling of `T5`) and of the ambient.
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGAp, hGFp, hp'⟩ := exists_of_isLawfulBelow_left hIL hp
  obtain ⟨qAC, qAD, qF, qG, hq', hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
  -- Step 2: the cells `({3}, 1)`, `(C, 2)` and `(E, 3)`, one of each live kind on `C`.
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₁ : oldCell I rows5 d₁ ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hd₁]; decide)
  have hs : oldCell I rows5 sC ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hsC]; decide)
  have hg : oldCell I rows5 gE ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I rows5).toCellScheme.below (coatomC, 3)) :
      z ∈ (layerScheme I rows5).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  -- Step 3: at those cells, the prescribed parameters agree with the ambient capped at `c`.
  have hAq : min Ap c = min qAC c := by
    have := hpq _ h₁
    rw [hp' _ h₁, hqz _ (hmem h₁), thinLabelling, gradedIndex_oldCell, hd₁] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), thinLabelling, gradedIndex_oldCell, hsC] at this
    exact this.symm
  have hGq : min Gp c = min qG c := by
    have := hpq _ hg
    rw [hp' _ hg, hqz _ (hmem hg), thinLabelling, gradedIndex_oldCell, hgE] at this
    exact this.symm
  -- Step 4: the parameter-level lift, with `A_D` unprescribed; its thin labelling is the lift.
  have hc2' : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    refine hc2.imp_right fun h ↦ ?_
    have := h _ hs (by rw [grade_oldCell]; exact congrArg Prod.snd hsC)
    rw [hp' _ hs, gradedIndex_oldCell, hsC] at this
    exact congrArg some this
  obtain ⟨xAC, xAD, xF, xG, hx, hxAC, hxAD, hxF, hxG, hpAC, -, hpF, hpG⟩ :=
    exists_thin5Lift hc1 (PAC := some Ap) (PAD := none) (PF := some Fp) (PG := some Gp) hc2'
      (.inr rfl) hq' (forall_mem_some hAp) forall_mem_none (forall_mem_some hFp)
      (forall_mem_some hGp) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some hGFp)) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some hGAp)) (forall_mem_some forall_mem_none)
      (forall_mem_some hAq) forall_mem_none (forall_mem_some hFq) (forall_mem_some hGq)
  refine ⟨thinLabelling I xAC xAD xF xG ⊥, isLawfulBelow_thinLabelling hIL hIR hx,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_thinLabel_eq hxAC hxAD hxF hxG _
  · rw [hp' z hz, thinLabelling, hpAC Ap rfl, hpF Fp rfl, hpG Gp rfl]
    exact thinLabel_congr_two (thinKind_ne_two (four_notMem_of_mem_below hz)) _ _ _ _ _ _

include hIL hIR in
/-- **The lift from `(D, 3)` to `(univ, 3)`**, for a cap `c` self-visible at `1`, and at `2` unless
the prescription is `⊥` at the grade `2`: the parameters of the prescription (`T5`) and of the
ambient (`IsThin5`) are lifted by `exists_thin5Lift`, with `A_C` unprescribed. -/
theorem exists_lift_right {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {p q : Fin (layerScheme I rows5).card → Label.{u}}
    (hp : (layerScheme I rows5).rows.IsLawfulBelow (coatomD, 3) fun z ↦ p z)
    (hq : (layerScheme I rows5).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3),
      min (q z) c = min (p z) c)
    (hc2 : IsSelfVisible 2 c ∨ ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3),
      (layerScheme I rows5).toCellScheme.grade z = 2 → p z = ⊥) :
    ∃ x : Fin (layerScheme I rows5).card → Label.{u},
      (layerScheme I rows5).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I rows5).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3), x z = p z := by
  -- Step 1: the parameters of the prescription (a labelling of `T5`) and of the ambient.
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGAp, hGFp, hp'⟩ := exists_of_isLawfulBelow_right hIR hp
  obtain ⟨qAC, qAD, qF, qG, hq', hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
  -- Step 2: the cells `({4}, 1)`, `(D, 2)` and `(E, 3)`, one of each live kind on `D`.
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₂ : oldCell I rows5 d₂ ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hd₂]; decide)
  have hs : oldCell I rows5 sD ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hsD]; decide)
  have hg : oldCell I rows5 gE ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I rows5).toCellScheme.below (coatomD, 3)) :
      z ∈ (layerScheme I rows5).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  -- Step 3: at those cells, the prescribed parameters agree with the ambient capped at `c`.
  have hAq : min Ap c = min qAD c := by
    have := hpq _ h₂
    rw [hp' _ h₂, hqz _ (hmem h₂), thinLabelling, gradedIndex_oldCell, hd₂] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), thinLabelling, gradedIndex_oldCell, hsD] at this
    exact this.symm
  have hGq : min Gp c = min qG c := by
    have := hpq _ hg
    rw [hp' _ hg, hqz _ (hmem hg), thinLabelling, gradedIndex_oldCell, hgE] at this
    exact this.symm
  -- Step 4: the parameter-level lift, with `A_C` unprescribed; its thin labelling is the lift.
  have hc2' : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    refine hc2.imp_right fun h ↦ ?_
    have := h _ hs (by rw [grade_oldCell]; exact congrArg Prod.snd hsD)
    rw [hp' _ hs, gradedIndex_oldCell, hsD] at this
    exact congrArg some this
  obtain ⟨xAC, xAD, xF, xG, hx, hxAC, hxAD, hxF, hxG, -, hpAD, hpF, hpG⟩ :=
    exists_thin5Lift hc1 (PAC := none) (PAD := some Ap) (PF := some Fp) (PG := some Gp) hc2'
      (.inr rfl) hq' forall_mem_none (forall_mem_some hAp) (forall_mem_some hFp)
      (forall_mem_some hGp) forall_mem_none
      (forall_mem_some (forall_mem_some hGFp)) (forall_mem_some (forall_mem_some hGAp))
      (forall_mem_some forall_mem_none) forall_mem_none
      forall_mem_none (forall_mem_some hAq) (forall_mem_some hFq) (forall_mem_some hGq)
  refine ⟨thinLabelling I xAC xAD xF xG ⊥, isLawfulBelow_thinLabelling hIL hIR hx,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_thinLabel_eq hxAC hxAD hxF hxG _
  · rw [hp' z hz, thinLabelling, hpAD Ap rfl, hpF Fp rfl, hpG Gp rfl]
    exact thinLabel_congr_one (thinKind_ne_one (three_notMem_of_mem_below hz)) _ _ _ _ _ _

/-! ### Capped lifts from the coatoms to the full scope -/

include hIL hIR in
/-- **The capped lift from `(C, k)` to `(univ, k)`**, `1 ≤ k ≤ 3`. -/
theorem cappedLift_left {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (layerScheme I rows5).rows.CappedLift (X := (coatomC, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_lift_three hk3 fun _ hc _ _ hp hq hp0 _ hpq ↦
    exists_lift_left hIL hIR (hc.mono hk1) hp hq hpq
      (if h : 2 ≤ k then .inl (hc.mono h) else .inr fun z _ hz ↦ hp0 z (by omega))

include hIL hIR in
/-- **The capped lift from `(D, k)` to `(univ, k)`**, `1 ≤ k ≤ 3`. -/
theorem cappedLift_right {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (layerScheme I rows5).rows.CappedLift (X := (coatomD, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_lift_three hk3 fun _ hc _ _ hp hq hp0 _ hpq ↦
    exists_lift_right hIL hIR (hc.mono hk1) hp hq hpq
      (if h : 2 ≤ k then .inl (hc.mono h) else .inr fun z _ hz ↦ hp0 z (by omega))

/-! ### The ordered-layer step below the top grade -/

include hIL hIR in
/-- **The rows of the new cells at the grades `k ≤ 3` are consistent**: each is the thin labelling
of parameters satisfying `IsThin5`. -/
theorem isLawfulBelow_row {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (layerScheme I rows5).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ rows5 k ((layerScheme I rows5).toCellScheme.gradedIndex z) := by
  obtain ⟨AC, AD, F, G, h, hX⟩ := row_newCell_eq_thinLabel.{u} hk1 hk3
  have he : (fun z : (layerScheme I rows5).toCellScheme.below ((univ : Finset (Fin 5)), k) ↦
      rows5 k ((layerScheme I rows5).toCellScheme.gradedIndex z)) =
      fun z ↦ thinLabelling I AC AD F G ⊥ z.1 := funext fun z ↦ hX _
  rw [he]
  exact (isLawfulBelow_thinLabelling hIL hIR h).mono
    (X := ((univ : Finset (Fin 5)), k)) ⟨subset_rfl, hk3⟩

include hIL hIR in
/-- **The ordered-layer step below the top grade for the seeds of `T5` with itself**: with the
rows `rows5`, the rows at the grades `k ≤ 3` are coded and consistent, and the capped lifts from
both coatoms into `(univ, k)`, `1 ≤ k ≤ 3`, exist. -/
theorem orderedLayerStepBelowTop_of : I.OrderedLayerStepBelowTop rows5 where
  row_lt k hk1 hk3 z _ := by
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact thinRow_lt 1 _
    · exact thinRow_lt 2 _
    · exact rowThree_lt _
  isLawfulBelow_row _ hk1 hk3 := isLawfulBelow_row hIL hIR hk1 hk3
  cappedLift_left _ hk1 hk3 := cappedLift_left hIL hIR hk1 hk3
  cappedLift_right _ hk1 hk3 := cappedLift_right hIL hIR hk1 hk3

/-- **The ordered-layer step below the top grade for `seed5`**, the seed of `T5` with itself. -/
theorem orderedLayerStepBelowTop_seed5 :
    (CaseSplitCounterexample.seed5 α).OrderedLayerStepBelowTop rows5 :=
  orderedLayerStepBelowTop_of rfl rfl

end VaughtConjecture.OrderedLayer.Seed5
