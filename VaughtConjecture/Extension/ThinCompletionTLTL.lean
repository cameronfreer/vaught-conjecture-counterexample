/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerTop
import VaughtConjecture.Extension.ThinCompletion

/-!
# The ordered-layer step for the seeds of `TL` with itself

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: the
ordered-layer step of `VaughtConjecture.Extension.OrderedLayerStep` for the seeds whose two coatom
types are `TL`); semantic contract, items 2–4.

Let `I` be a seed on five points whose two coatom types are `TwoFaceLiftExistsCounterexample.TL`,
with coatoms `C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}`; the seed `seedLL` is one.  Neither
coatom type couples its parameter `G` of grade `3` to its parameter `A` of grade `1` (`TL` imposes
`G ≤ F` and `VisibilityReplaceFixedOfLT A G` only), so the argument of
`VaughtConjecture.Extension.SeparatingCell` forces no separation.  The rows of the thin completion
of `seedL` do not serve here (argued, not formalized): its row at `(univ, 3)` reads `A_D` at
`ω + 3`, which forces `G ≤ A_D`, and `TL` on `D` allows `A_D < G`.  Reading `A_C` and `A_D` at
different values also fails (argued, not formalized): with `A_C` forced to `A_D` below `G` at
`(univ, 3)` and both read apart at `(univ, 2)`, the prescription `(A, F, G) = (1, ⊤, ⊤)` on `C`
has no lift (a collision at `(univ, 2)`).

**The merged rows** (`rowsLL`).  Every row of a new cell reads the live cells of grade `1` of both
coatoms at one value, `1`: the row at `(univ, k)` is the thin labelling (`ThinCompletion.thinLabel`)
of parameters with `A_C = A_D`.  At `(univ, 1)` the live cells of grade `1` at `1`; at `(univ, 2)`
those at `1` and the live cells of grade `2` at `ω + 2`; at `(univ, 3)` those at `1` and every
other live cell at `ω + 3` (the row of the cell `18` of `TL`); at `(univ, 4)` the top row
`OrderedLayer.topRow`.  The witnesses are the top shifter, the strip shifter of
`TwoFaceLiftCounterexample`, and the strip shifter at the grade `3`.

**The lawful labellings below `(univ, 3)`** are exactly the thin labellings with `A_C = A_D`
(`thinLabelling I A A F G ⊥`) of parameters satisfying `IsThinLL` (`A`, `F`, `G` self-visible at
`1`, `2`, `3`, `G ≤ F`, `VisibilityReplaceFixedOfLT A G`: the constraints of `TL`)
(`isLawfulBelow_thinLabelling`, `exists_of_isLawfulBelow_three`).  So a lawful labelling is a
labelling of `TL` repeated on both coatoms.

**The lifts** need no parameter choice: a prescription below `(C, 3)` or `(D, 3)` is a labelling of
`TL` with parameters `(A, F, G)`, and its repetition on both coatoms is the lift, agreeing with the
ambient capped at the cap since the parameters do (`exists_lift_left`, `exists_lift_right`).

**The theorem** (`orderedLayerStepBelowTop_of`, `Seed.orderedLayerStep_of_TL_TL`,
`Seed.orderedLayerStep_seedLL`, `Seed.nonempty_completionBelowFullGrade_seedLL`): every seed whose
coatom types are both `TL` has the ordered-layer step with the rows `rowsLL`, hence a completion
below the full grade.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.OrderedLayer.SeedLL

open Finset Label CellScheme
open Ordinal hiding univ
open ThinCompletion (thinKind thinLabel kindLabel thinKind_le
  thinLabel_le thinLabel_eq_tripleLabelling thinKind_ne_one thinKind_ne_two
  thinLabel_congr_one thinLabel_congr_two min_thinLabel_eq transformsTo_topShifter)
open TwoFaceLiftExistsCounterexample (TL VisibilityReplaceFixedOfLT strip3 isWitness_strip3
  strip3_natCast strip3_of_not_lt strip3_bot min_visibilityReplace_three_one)
open CaseSplitCounterexample (tripleLabelling)

/-! ### The layer rows -/

/-- **The layer rows for the seeds of `TL` with itself**: the thin labellings with `A_C = A_D` at
`1`; the live cells of grade `2` at `ω + 2` at `(univ, 2)`; the other live cells at `ω + 3` at
`(univ, 3)`; and the top row at `(univ, 4)`. -/
noncomputable def rowsLL : LayerRows.{u}
  | 1 => thinLabel (gridPoint 1 0) (gridPoint 1 0) ⊥ ⊥ ⊥
  | 2 => thinLabel (gridPoint 1 0) (gridPoint 1 0) (gridPoint 2 1) ⊥ ⊥
  | 3 => thinLabel (gridPoint 1 0) (gridPoint 1 0) (gridPoint 3 1) (gridPoint 3 1) ⊥
  | _ => topRow

/-- The layer row at `(univ, 4)` is the top row. -/
theorem rowsLL_four : rowsLL.{u} 4 = topRow := rfl

/-! ### The constraints -/

/-- **The constraints of the layer scheme of `rowsLL` below `(univ, 3)`**, on the parameters `A`
(the live cells of grade `1` of both coatoms), `F` and `G`: those of `TL`. -/
structure IsThinLL (A F G : Label.{u}) : Prop where
  /-- `A` is self-visible at `1`. -/
  svA : IsSelfVisible 1 A
  /-- `F` is self-visible at `2`. -/
  svF : IsSelfVisible 2 F
  /-- `G` is self-visible at `3`. -/
  svG : IsSelfVisible 3 G
  /-- The coupling of `TL`: `G ≤ F`. -/
  G_le_F : G ≤ F
  /-- The condition of `TL` on the finite part of `A` below `G`. -/
  visibilityReplaceFixed : VisibilityReplaceFixedOfLT A G

/-- The row at `(univ, 3)` satisfies the constraints. -/
theorem isThinLL_row_three : IsThinLL (gridPoint.{u} 1 0) (gridPoint 3 1) (gridPoint 3 1) where
  svA := isSelfVisible_gridPoint 1 0
  svF := (isSelfVisible_gridPoint 3 1).mono (by omega)
  svG := isSelfVisible_gridPoint 3 1
  G_le_F := le_rfl
  visibilityReplaceFixed _ := by rw [gridPoint, visibilityReplace_block]; simp

/-- The row at `(univ, 2)` satisfies the constraints. -/
theorem isThinLL_row_two : IsThinLL (gridPoint.{u} 1 0) (gridPoint 2 1) ⊥ where
  svA := isSelfVisible_gridPoint 1 0
  svF := isSelfVisible_gridPoint 2 1
  svG := isSelfVisible_bot 3
  G_le_F := bot_le
  visibilityReplaceFixed h := absurd h (not_lt.mpr bot_le)

/-- The row at `(univ, 1)` satisfies the constraints. -/
theorem isThinLL_row_one : IsThinLL (gridPoint.{u} 1 0) ⊥ ⊥ where
  svA := isSelfVisible_gridPoint 1 0
  svF := isSelfVisible_bot 2
  svG := isSelfVisible_bot 3
  G_le_F := le_rfl
  visibilityReplaceFixed h := absurd h (not_lt.mpr bot_le)

/-- The row of the new cell at `(univ, k)`, `k ≤ 3`, is the thin labelling of parameters with
`A_C = A_D` satisfying the constraints. -/
theorem rowsLL_eq_thinLabel {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    ∃ A F G : Label.{u}, IsThinLL A F G ∧ ∀ X, rowsLL k X = thinLabel A A F G ⊥ X := by
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · exact ⟨_, _, _, isThinLL_row_one, fun _ ↦ rfl⟩
  · exact ⟨_, _, _, isThinLL_row_two, fun _ ↦ rfl⟩
  · exact ⟨_, _, _, isThinLL_row_three, fun _ ↦ rfl⟩

/-- The rows at `(univ, k)`, `k ≤ 3`, are coded. -/
theorem rowsLL_lt {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (X : Finset (Fin 5) × ℕ) :
    rowsLL.{u} k X < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have hb : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    WithBot.bot_lt_coe _
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals
    -- The row `rowsLL k` at `X` is a thin labelling.
    change thinLabel _ _ _ _ _ X < _
    unfold thinLabel
    generalize thinKind X = c
    fin_cases c <;> first | exact hb | exact gridPoint_lt_omega0_sq _ _

/-! ### The witnesses at the new cells -/

/-- The row at `(univ, 1)` transforms, through the top shifter, to `A` at the live cells of
grade `1`. -/
theorem transformsTo_rowOne {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 1) (hk : ∀ d, (kind d : ℕ) ≤ 2) {A F G Ω : Label.{u}}
    (hA : IsSelfVisible 1 A) :
    TransformsTo grade (fun d ↦ kindLabel (gridPoint 1 0) (gridPoint 1 0) ⊥ ⊥ ⊥ (kind d))
      (fun d ↦ min (kindLabel A A F G Ω (kind d)) A) := by
  refine transformsTo_topShifter grade hgr hA _ _ fun d ↦ ?_
  have h := hk d
  generalize kind d = k at h ⊢
  fin_cases k
  · simp [kindLabel]
  · simp [kindLabel, gridPoint_ne_bot]
  · simp [kindLabel, gridPoint_ne_bot]
  all_goals exact absurd h (by decide)

/-- The row at `(univ, 2)` transforms, through the strip shifter of `A` with the suppressor `F`, to
`A ∧ F` at the live cells of grade `1` and `F` at those of grade `2`. -/
theorem transformsTo_rowTwo {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 2) (hk : ∀ d, (kind d : ℕ) ≤ 3) {A F G Ω : Label.{u}}
    (hA : IsSelfVisible 1 A) (hF : IsSelfVisible 2 F) :
    TransformsTo grade
      (fun d ↦ kindLabel (gridPoint 1 0) (gridPoint 1 0) (gridPoint 2 1) ⊥ ⊥ (kind d))
      (fun d ↦ min (kindLabel A A F G Ω (kind d)) F) := by
  refine ⟨constStepSuppressor 2 F, TwoFaceLiftCounterexample.stripShifter A,
    TwoFaceLiftCounterexample.isWitness_stripShifter hF, fun d ↦ ?_⟩
  have hg : constStepSuppressor 2 F (grade d) = F := by
    unfold constStepSuppressor; rw [ite_eq_left (hgr d)]
  rw [hg]
  dsimp only
  have h := hk d
  generalize kind d = k at h ⊢
  -- In each case, `change` evaluates `kindLabel` at the kind.
  fin_cases k
  · change min ⊥ F = min (TwoFaceLiftCounterexample.stripShifter A ⊥) F
    rw [TwoFaceLiftCounterexample.stripShifter_bot]
  · change min A F = min (TwoFaceLiftCounterexample.stripShifter A TwoFaceLiftCounterexample.v1) F
    rw [TwoFaceLiftCounterexample.stripShifter_v1 hA]
  · change min A F = min (TwoFaceLiftCounterexample.stripShifter A TwoFaceLiftCounterexample.v1) F
    rw [TwoFaceLiftCounterexample.stripShifter_v1 hA]
  · change min F F = min (TwoFaceLiftCounterexample.stripShifter A TwoFaceLiftCounterexample.v2) F
    rw [TwoFaceLiftCounterexample.stripShifter_v2, min_top_left, min_self]
  all_goals exact absurd h (by decide)

/-- The row at `(univ, 3)` transforms, through the strip shifter at the grade `3` of `A` with the
suppressor `G`, under `VisibilityReplaceFixedOfLT A G` and `G ≤ F`. -/
theorem transformsTo_rowThree {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 3) (hk : ∀ d, (kind d : ℕ) ≤ 4) {A F G Ω : Label.{u}}
    (hG : IsSelfVisible 3 G) (hc : VisibilityReplaceFixedOfLT A G) (hGF : G ≤ F) :
    TransformsTo grade
      (fun d ↦ kindLabel (gridPoint 1 0) (gridPoint 1 0) (gridPoint 3 1) (gridPoint 3 1) ⊥
        (kind d))
      (fun d ↦ min (kindLabel A A F G Ω (kind d)) G) := by
  refine ⟨constStepSuppressor 3 G, strip3 A, isWitness_strip3 hG, fun d ↦ ?_⟩
  have hg : constStepSuppressor 3 G (grade d) = G := by
    unfold constStepSuppressor; rw [ite_eq_left (hgr d)]
  rw [hg]
  have hnl : ¬ (gridPoint 3 1 : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
    rw [not_lt, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
    calc (ω : Ordinal.{u}) = ω * ((1 : ℕ) : Ordinal.{u}) := by simp
      _ ≤ _ := le_self_add
  have htop : strip3 A (gridPoint 3 1) = ⊤ := strip3_of_not_lt (gridPoint_ne_bot 3 1) hnl
  have hone : min (strip3 A (gridPoint 1 0)) G = min A G := by
    rw [show (gridPoint 1 0 : Label.{u}) = ((1 : ℕ) : Label.{u}) from
      TwoFaceLiftCounterexample.v1_eq, strip3_natCast, show min 1 3 = 1 from rfl,
      min_visibilityReplace_three_one hG hc]
  dsimp only
  have h := hk d
  generalize kind d = k at h ⊢
  -- In each case, `change` evaluates `kindLabel` at the kind.
  fin_cases k
  · change min ⊥ G = min (strip3 A ⊥) G
    rw [strip3_bot]
  · change min A G = min (strip3 A (gridPoint 1 0)) G
    exact hone.symm
  · change min A G = min (strip3 A (gridPoint 1 0)) G
    exact hone.symm
  · change min F G = min (strip3 A (gridPoint 3 1)) G
    rw [htop, min_top_left, min_eq_right hGF]
  · change min G G = min (strip3 A (gridPoint 3 1)) G
    rw [htop, min_top_left, min_self]
  · exact absurd h (by decide)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-! ### Kinds and grades -/

/-- A cell below the new cell at `(univ, k)` has grade at most `k`. -/
theorem grade_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I rowsLL).toCellScheme.below
      ((layerScheme I rowsLL).toCellScheme.gradedIndex (newCell I rowsLL k))) :
    (layerScheme I rowsLL).toCellScheme.grade t.1 ≤ k := by
  have h : (layerScheme I rowsLL).toCellScheme.gradedIndex t.1 ≤ ((univ : Finset (Fin 5)), k) :=
    gradedIndex_newCell hk1 hk4 ▸ t.2
  exact h.2

/-- The kind of a cell below the new cell at `(univ, k)` is at most `k + 1`. -/
theorem thinKind_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I rowsLL).toCellScheme.below
      ((layerScheme I rowsLL).toCellScheme.gradedIndex (newCell I rowsLL k))) :
    (thinKind ((layerScheme I rowsLL).toCellScheme.gradedIndex t.1) : ℕ) ≤ k + 1 :=
  (thinKind_le _).trans (Nat.succ_le_succ (grade_le_of_mem_below_newCell hk1 hk4 t))

/-- The new cell at `(univ, k)` is below itself. -/
theorem newCell_mem_below_self {k : ℕ} :
    newCell I rowsLL k ∈ (layerScheme I rowsLL).toCellScheme.below
      ((layerScheme I rowsLL).toCellScheme.gradedIndex (newCell I rowsLL k)) :=
  (layerScheme I rowsLL).toCellScheme.mem_below_gradedIndex _

/-- An old cell below the new cell at `(univ, k)`, of grade at most `k`. -/
theorem oldCell_mem_below_newCell {d : Fin I.amalgam.card} {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hd : I.amalgam.toCellScheme.grade d ≤ k) :
    oldCell I rowsLL d ∈ (layerScheme I rowsLL).toCellScheme.below
      ((layerScheme I rowsLL).toCellScheme.gradedIndex (newCell I rowsLL k)) := by
  rw [gradedIndex_newCell hk1 hk4]
  exact oldCell_mem_below ⟨subset_univ _, hd⟩

/-- A cell below `(C, k)` misses the point `4`. -/
theorem four_notMem_of_mem_below {z : Fin (layerScheme I rowsLL).card} {k : ℕ}
    (hz : z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, k)) :
    (4 : Fin 5) ∉ ((layerScheme I rowsLL).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.last 4) univ) (hz.1 h)

/-- A cell below `(D, k)` misses the point `3`. -/
theorem three_notMem_of_mem_below {z : Fin (layerScheme I rowsLL).card} {k : ℕ}
    (hz : z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, k)) :
    (3 : Fin 5) ∉ ((layerScheme I rowsLL).toCellScheme.gradedIndex z).1 := fun h ↦
  (notMem_erase (Fin.castSucc (Fin.last 3)) univ) (hz.1 h)

/-! ### Lawful labellings below the two coatoms -/

variable (I) in
/-- The **thin labelling** of the cells of the layer scheme, read off their graded indices. -/
noncomputable def thinLabelling (AC AD F G Ω : Label.{u})
    (z : Fin (layerScheme I rowsLL).card) : Label.{u} :=
  thinLabel AC AD F G Ω ((layerScheme I rowsLL).toCellScheme.gradedIndex z)

/-- The thin labelling at the new cell at `(univ, k)`. -/
theorem thinLabelling_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (AC AD F G Ω : Label.{u}) :
    thinLabelling I AC AD F G Ω (newCell I rowsLL k) =
      kindLabel AC AD F G Ω (thinKind ((univ : Finset (Fin 5)), k)) := by
  rw [thinLabelling, gradedIndex_newCell hk1 hk4]; rfl

variable (hIL : I.left = TL α) (hIR : I.right = TL α)

include hIL in
/-- **Lawful labellings below `(C, 3)`**: `thinLabel A ⊥ F G ⊥` with the constraints of `TL`. -/
theorem exists_of_isLawfulBelow_left {w : Fin (layerScheme I rowsLL).card → Label.{u}}
    (hw : (layerScheme I rowsLL).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsThinLL A F G ∧
      ∀ z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, 3),
        w z = thinLabel A ⊥ F G ⊥ ((layerScheme I rowsLL).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomC_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGF, hc, hall⟩ :=
    TwoFaceLiftExistsCounterexample.exists_labelling_of_comap_TL (hIL ▸ I.restrictFace_left)
      le_rfl (fun d ↦ w (oldCell I rowsLL d)) hw'
  refine ⟨A, F, G, ⟨hA, hF, hG, hGF, hc⟩, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ :=
    (image_oldCell_below (I := I) (ρ := rowsLL) (X := (coatomC, 3)) (by decide)).symm ▸ hz
  rw [coatomC_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, thinLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_left]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

include hIR in
/-- **Lawful labellings below `(D, 3)`**: `thinLabel ⊥ A F G ⊥` with the constraints of `TL`. -/
theorem exists_of_isLawfulBelow_right {w : Fin (layerScheme I rowsLL).card → Label.{u}}
    (hw : (layerScheme I rowsLL).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsThinLL A F G ∧
      ∀ z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, 3),
        w z = thinLabel ⊥ A F G ⊥ ((layerScheme I rowsLL).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomD_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGF, hc, hall⟩ :=
    TwoFaceLiftExistsCounterexample.exists_labelling_of_comap_TL (hIR ▸ I.restrictFace_right)
      le_rfl (fun d ↦ w (oldCell I rowsLL d)) hw'
  refine ⟨A, F, G, ⟨hA, hF, hG, hGF, hc⟩, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ :=
    (image_oldCell_below (I := I) (ρ := rowsLL) (X := (coatomD, 3)) (by decide)).symm ▸ hz
  rw [coatomD_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, thinLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_right]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

/-! ### Sufficiency: the merged thin labellings are lawful below `(univ, 3)` -/

/-- A labelling of graded indices whose reading along `f` is `labelling A F G` is lawful below the
coatom `univ.map f` at the grade `3`, for a stage type whose face along `f` is `TL`. -/
theorem isLawfulBelow_coatom_TL {A F G : Label.{u}} (h : IsThinLL A F G)
    {f : Fin 4 ↪ Fin 5} {Am : StageType.{u} α 5}
    (hf : StageType.restrictFace f Am = some (TL α)) {Lf : Finset (Fin 5) × ℕ → Label.{u}}
    (hL : ∀ d, Lf (Prod.map (Finset.map f) id (TwoFaceLiftCounterexample.cells.gradedIndex d)) =
      CaseSplitCounterexample.labelling A F G d) :
    Am.rows.IsLawfulBelow (univ.map f, 3) (fun d ↦ Lf (Am.toCellScheme.gradedIndex d)) := by
  obtain ⟨hf', he⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  have heq : Am.toScheme.comap f = (TL α).toScheme := congrArg StageType.toScheme he
  have hlaw : ∀ x : Fin (Am.toScheme.comap f).card → Label.{u},
      (∀ i, x i = Lf (Prod.map (Finset.map f) id
        ((Am.toScheme.comap f).toCellScheme.gradedIndex i))) →
      (Am.toScheme.comap f).rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun i ↦ x i) := by
    rw [heq]
    intro x hx
    refine (TwoFaceLiftExistsCounterexample.isLawfulBelow_TL_iff
      (fun h ↦ absurd h.2 (by decide))).mpr ?_
    convert (TwoFaceLiftExistsCounterexample.isLawful_labelling h.svA h.svF h.svG h.G_le_F
      h.visibilityReplaceFixed).isLawfulBelow ((univ : Finset (Fin 4)), 3) using 1
    funext d
    refine (hx _).trans ?_
    rw [TwoFaceLiftExistsCounterexample.gradedIndex_TL_castSucc]
    exact hL d.1
  exact (Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 4)), 3)
    fun d ↦ Lf (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg Lf (Am.toScheme.map_comap_gradedIndex f i).symm)

include hIL hIR in
/-- **The merged thin labellings are lawful below the coatoms** at the grade `3`: on the old cells
they are the labellings `tripleLabelling A F A F G`, a labelling of `TL` on each coatom. -/
theorem isLawfulBelow_coatom_thinLabelling {A F G Ω : Label.{u}} (h : IsThinLL A F G) :
    (layerScheme I rowsLL).rows.IsLawfulBelow (coatomC, 3)
        (fun z ↦ thinLabelling I A A F G Ω z) ∧
      (layerScheme I rowsLL).rows.IsLawfulBelow (coatomD, 3)
        (fun z ↦ thinLabelling I A A F G Ω z) := by
  have hC := isLawfulBelow_coatom_TL h (hIL ▸ I.restrictFace_left)
    (CaseSplitCounterexample.tripleLabelling_left A F A F G)
  have hD := isLawfulBelow_coatom_TL h (hIR ▸ I.restrictFace_right)
    (CaseSplitCounterexample.tripleLabelling_right A F A F G)
  rw [← coatomC_eq] at hC
  rw [← coatomD_eq] at hD
  have key (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      thinLabelling I A A F G Ω (oldCell I rowsLL d) =
        tripleLabelling A F A F G (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [thinLabelling, gradedIndex_oldCell]
    exact thinLabel_eq_tripleLabelling (I.scope_ne_univ d)
      (show I.amalgam.toCellScheme.grade d ≠ 4 by omega) _ _ _ _ _
  constructor
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomC, 3))
      fun d hd ↦ (key d hd.2).symm).mp hC
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomD, 3))
      fun d hd ↦ (key d hd.2).symm).mp hD

include hIL hIR in
/-- **Sufficiency**: the thin labelling with `A_C = A_D` of parameters satisfying `IsThinLL` is
lawful below `(univ, 3)`. -/
theorem isLawfulBelow_thinLabelling {A F G Ω : Label.{u}} (h : IsThinLL A F G) :
    (layerScheme I rowsLL).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      (fun z ↦ thinLabelling I A A F G Ω z) := by
  obtain ⟨hC, hD⟩ := isLawfulBelow_coatom_thinLabelling hIL hIR (Ω := Ω) h
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hD
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hne : (layerScheme I rowsLL).toCellScheme.scope d = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hd.2
      rw [grade_newCell hj1 hj4, thinLabelling_newCell hj1 hj4]
      obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact h.svA
      · exact h.svF
      · exact h.svG
    · exact (mem_below_coatom_of_ne hd hne).elim (hoC d) (hoD d)
  · rcases cell_cases s with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
    · exact (mem_below_coatom_of_ne hs (scope_oldCell_ne d)).elim (hlC _) (hlD _)
    · rw [row_newCell_eq le_rfl (by omega), thinLabelling_newCell le_rfl (by omega)]
      exact transformsTo_rowOne _
        (fun t ↦ thinKind ((layerScheme I rowsLL).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell le_rfl (by omega))
        (thinKind_le_of_mem_below_newCell le_rfl (by omega)) h.svA
    · rw [row_newCell_eq (by omega) (by omega), thinLabelling_newCell (by omega) (by omega)]
      exact transformsTo_rowTwo _
        (fun t ↦ thinKind ((layerScheme I rowsLL).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (thinKind_le_of_mem_below_newCell (by omega) (by omega)) h.svA h.svF
    · rw [row_newCell_eq (by omega) (by omega), thinLabelling_newCell (by omega) (by omega)]
      exact transformsTo_rowThree _
        (fun t ↦ thinKind ((layerScheme I rowsLL).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (thinKind_le_of_mem_below_newCell (by omega) (by omega)) h.svG h.visibilityReplaceFixed
        h.G_le_F
    · have h4 : (layerScheme I rowsLL).toCellScheme.gradedIndex (newCell I rowsLL 4) ≤
          ((univ : Finset (Fin 5)), 3) := hs
      rw [gradedIndex_newCell (by omega) le_rfl] at h4
      exact absurd h4.2 (by decide)
  · by_cases hne : (layerScheme I rowsLL).toCellScheme.scope t = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      refine ⟨newCell I rowsLL j, rfl, ?_⟩
      rw [thinLabelling_newCell hj1 hj4]
      exact thinLabel_le le_rfl (hg.trans (grade_newCell hj1 hj4)) hj1 hj4
    · exact (mem_below_coatom_of_ne ht hne).elim (haC s t · hst hg) (haD s t · hst hg)

/-! ### Necessity: the lawful labellings below `(univ, 3)` are merged thin labellings -/

include hIL hIR in
/-- **Necessity**: every labelling lawful below `(univ, 3)` is a thin labelling with `A_C = A_D`,
of parameters satisfying `IsThinLL`.  On each coatom it is a labelling of `TL`; locality and
availability at the new cells identify the label of the new cell at `(univ, 1)` with both `A_C`
and `A_D` (its row reads both at its own value), and those at `(univ, 2)` and `(univ, 3)` with `F`
(on both coatoms) and `G`. -/
theorem exists_of_isLawfulBelow_three {w : Fin (layerScheme I rowsLL).card → Label.{u}}
    (hw : (layerScheme I rowsLL).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsThinLL A F G ∧
      ∀ z ∈ (layerScheme I rowsLL).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        w z = thinLabelling I A A F G ⊥ z := by
  -- Step 1: below each coatom, `w` is a labelling of `TL`.
  have hC : (layerScheme I rowsLL).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z :=
    hw.mono (X := (coatomC, 3)) ⟨subset_univ _, le_rfl⟩
  have hD : (layerScheme I rowsLL).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z :=
    hw.mono (X := (coatomD, 3)) ⟨subset_univ _, le_rfl⟩
  obtain ⟨AC, FC, GC, hTC, hC'⟩ := exists_of_isLawfulBelow_left hIL hC
  obtain ⟨AD, FD, GD, -, hD'⟩ := exists_of_isLawfulBelow_right hIR hD
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  -- Step 2: the old cells used, one of each live kind, and their labels.
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIL ▸ I.restrictFace_left) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIR ▸ I.restrictFace_right) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hw₁ : w (oldCell I rowsLL d₁) = AC := by
    rw [hC' _ (oldCell_mem_below (by rw [hd₁]; decide)), gradedIndex_oldCell, hd₁]; rfl
  have hwsC : w (oldCell I rowsLL sC) = FC := by
    rw [hC' _ (oldCell_mem_below (by rw [hsC]; decide)), gradedIndex_oldCell, hsC]; rfl
  have hwgC : w (oldCell I rowsLL gE) = GC := by
    rw [hC' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hwgD : w (oldCell I rowsLL gE) = GD := by
    rw [hD' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hw₂ : w (oldCell I rowsLL d₂) = AD := by
    rw [hD' _ (oldCell_mem_below (by rw [hd₂]; decide)), gradedIndex_oldCell, hd₂]; rfl
  have hwsD : w (oldCell I rowsLL sD) = FD := by
    rw [hD' _ (oldCell_mem_below (by rw [hsD]; decide)), gradedIndex_oldCell, hsD]; rfl
  have hGCD : GC = GD := hwgC.symm.trans hwgD
  -- Step 3: locality (`hle`) and availability (`hge`) at the new cell at `(univ, k)` compare its
  -- label with that of an old cell of grade `k`.
  have hrow {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      (layerScheme I rowsLL).rows.row (newCell I rowsLL k)
          ⟨oldCell I rowsLL d, oldCell_mem_below_newCell hk1 hk4 hd⟩ =
        rowsLL k (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [row_newCell hk1 hk4, gradedIndex_oldCell]
  have hrowself {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
      (layerScheme I rowsLL).rows.row (newCell I rowsLL k)
          ⟨newCell I rowsLL k, newCell_mem_below_self⟩ =
        rowsLL k ((univ : Finset (Fin 5)), k) := by
    rw [row_newCell hk1 hk4, gradedIndex_newCell hk1 hk4]
  have hle {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k)
      (hr : rowsLL k ((univ : Finset (Fin 5)), k) ≤
        rowsLL k (I.amalgam.toCellScheme.gradedIndex d)) :
      w (newCell I rowsLL k) ≤ w (oldCell I rowsLL d) := by
    have := (hl _ (newCell_mem_below hk1 (by omega) hk3)).le_of_le
      (d := ⟨newCell I rowsLL k, newCell_mem_below_self⟩)
      (d' := ⟨oldCell I rowsLL d, oldCell_mem_below_newCell hk1 (by omega) hd.le⟩)
      (by rw [hrowself hk1 (by omega), hrow hk1 (by omega) hd.le]; exact hr)
      (show (layerScheme I rowsLL).toCellScheme.grade (oldCell I rowsLL d) ≤
          (layerScheme I rowsLL).toCellScheme.grade (newCell I rowsLL k) by
        rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have hge {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k) :
      w (oldCell I rowsLL d) ≤ w (newCell I rowsLL k) := by
    obtain ⟨u, hu, hle⟩ := ha (oldCell I rowsLL d) (newCell I rowsLL k)
      (newCell_mem_below hk1 (by omega) hk3)
      (by rw [scope_newCell hk1 (by omega)]; exact subset_univ _)
      (by rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    rwa [eq_newCell hk1 (by omega) (hu.trans (gradedIndex_newCell hk1 (by omega)))] at hle
  have hn₁C : w (newCell I rowsLL 1) = AC := by
    rw [← hw₁]
    exact le_antisymm (hle le_rfl (by omega) (congrArg Prod.snd hd₁) (by rw [hd₁]; rfl))
      (hge le_rfl (by omega) (congrArg Prod.snd hd₁))
  have hn₁D : w (newCell I rowsLL 1) = AD := by
    rw [← hw₂]
    exact le_antisymm (hle le_rfl (by omega) (congrArg Prod.snd hd₂) (by rw [hd₂]; rfl))
      (hge le_rfl (by omega) (congrArg Prod.snd hd₂))
  have hn₂C : w (newCell I rowsLL 2) = FC := by
    rw [← hwsC]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsC) (by rw [hsC]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsC))
  have hn₂D : w (newCell I rowsLL 2) = FD := by
    rw [← hwsD]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsD) (by rw [hsD]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsD))
  have hn₃ : w (newCell I rowsLL 3) = GC := by
    rw [← hwgC]
    exact le_antisymm (hle (by omega) le_rfl (congrArg Prod.snd hgE) (by rw [hgE]; rfl))
      (hge (by omega) le_rfl (congrArg Prod.snd hgE))
  have hACD : AC = AD := hn₁C.symm.trans hn₁D
  have hFCD : FC = FD := hn₂C.symm.trans hn₂D
  -- Step 4: `w` is the merged thin labelling of these parameters.
  refine ⟨AC, FC, GC, hTC, fun z hz ↦ ?_⟩
  by_cases hne : (layerScheme I rowsLL).toCellScheme.scope z = univ
  · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
    have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hz.2
    rw [thinLabelling_newCell hj1 hj4]
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · exact hn₁C
    · exact hn₂C
    · exact hn₃
  · rcases mem_below_coatom_of_ne hz hne with h | h
    · rw [hC' z h, thinLabelling]
      exact thinLabel_congr_two (thinKind_ne_two (four_notMem_of_mem_below h)) _ _ _ _ _ _
    · rw [hD' z h, thinLabelling, ← hFCD, ← hGCD, ← hACD]
      exact thinLabel_congr_one (thinKind_ne_one (three_notMem_of_mem_below h)) _ _ _ _ _ _

/-! ### The lifts -/

include hIL hIR in
/-- **The lift from `(C, 3)` to `(univ, 3)`**, at every cap: the prescription is a labelling of
`TL` with parameters `(A, F, G)`, and the merged thin labelling of these parameters is the lift;
it agrees with the ambient capped at `c` since the parameters do, at the cells `({3}, 1)`,
`(C, 2)` and `(E, 3)`. -/
theorem exists_lift_left {c : Label.{u}} {p q : Fin (layerScheme I rowsLL).card → Label.{u}}
    (hp : (layerScheme I rowsLL).rows.IsLawfulBelow (coatomC, 3) fun z ↦ p z)
    (hq : (layerScheme I rowsLL).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, 3),
      min (q z) c = min (p z) c) :
    ∃ x : Fin (layerScheme I rowsLL).card → Label.{u},
      (layerScheme I rowsLL).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I rowsLL).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, 3), x z = p z := by
  obtain ⟨Ap, Fp, Gp, hTp, hp'⟩ := exists_of_isLawfulBelow_left hIL hp
  obtain ⟨qA, qF, qG, -, hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIL ▸ I.restrictFace_left) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₁ : oldCell I rowsLL d₁ ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hd₁]; decide)
  have hs : oldCell I rowsLL sC ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hsC]; decide)
  have hg : oldCell I rowsLL gE ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomC, 3)) :
      z ∈ (layerScheme I rowsLL).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  have hAq : min Ap c = min qA c := by
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
  refine ⟨thinLabelling I Ap Ap Fp Gp ⊥, isLawfulBelow_thinLabelling hIL hIR hTp,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_thinLabel_eq hAq hAq hFq hGq _
  · rw [hp' z hz, thinLabelling]
    exact thinLabel_congr_two (thinKind_ne_two (four_notMem_of_mem_below hz)) _ _ _ _ _ _

include hIL hIR in
/-- **The lift from `(D, 3)` to `(univ, 3)`**, at every cap: the merged thin labelling of the
parameters of the prescription, a labelling of `TL`. -/
theorem exists_lift_right {c : Label.{u}} {p q : Fin (layerScheme I rowsLL).card → Label.{u}}
    (hp : (layerScheme I rowsLL).rows.IsLawfulBelow (coatomD, 3) fun z ↦ p z)
    (hq : (layerScheme I rowsLL).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, 3),
      min (q z) c = min (p z) c) :
    ∃ x : Fin (layerScheme I rowsLL).card → Label.{u},
      (layerScheme I rowsLL).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I rowsLL).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, 3), x z = p z := by
  obtain ⟨Ap, Fp, Gp, hTp, hp'⟩ := exists_of_isLawfulBelow_right hIR hp
  obtain ⟨qA, qF, qG, -, hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIR ▸ I.restrictFace_right) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL
      (hIR ▸ I.restrictFace_right) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₂ : oldCell I rowsLL d₂ ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hd₂]; decide)
  have hs : oldCell I rowsLL sD ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hsD]; decide)
  have hg : oldCell I rowsLL gE ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I rowsLL).toCellScheme.below (coatomD, 3)) :
      z ∈ (layerScheme I rowsLL).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  have hAq : min Ap c = min qA c := by
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
  refine ⟨thinLabelling I Ap Ap Fp Gp ⊥, isLawfulBelow_thinLabelling hIL hIR hTp,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_thinLabel_eq hAq hAq hFq hGq _
  · rw [hp' z hz, thinLabelling]
    exact thinLabel_congr_one (thinKind_ne_one (three_notMem_of_mem_below hz)) _ _ _ _ _ _

/-! ### The ordered-layer step -/

include hIL hIR in
/-- **The capped lift from `(C, k)` to `(univ, k)`**, `1 ≤ k ≤ 3`. -/
theorem cappedLift_left {k : ℕ} (hk3 : k ≤ 3) :
    (layerScheme I rowsLL).rows.CappedLift (X := (coatomC, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_lift_three hk3 fun _ _ _ _ hp hq _ _ hpq ↦ exists_lift_left hIL hIR hp hq hpq

include hIL hIR in
/-- **The capped lift from `(D, k)` to `(univ, k)`**, `1 ≤ k ≤ 3`. -/
theorem cappedLift_right {k : ℕ} (hk3 : k ≤ 3) :
    (layerScheme I rowsLL).rows.CappedLift (X := (coatomD, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_lift_three hk3 fun _ _ _ _ hp hq _ _ hpq ↦ exists_lift_right hIL hIR hp hq hpq

include hIL hIR in
/-- **The rows of the new cells at the grades `k ≤ 3` are consistent**: each is the merged thin
labelling of parameters satisfying `IsThinLL`. -/
theorem isLawfulBelow_row {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (layerScheme I rowsLL).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ rowsLL k ((layerScheme I rowsLL).toCellScheme.gradedIndex z) := by
  obtain ⟨A, F, G, h, hX⟩ := rowsLL_eq_thinLabel.{u} hk1 hk3
  have he : (fun z : (layerScheme I rowsLL).toCellScheme.below ((univ : Finset (Fin 5)), k) ↦
      rowsLL k ((layerScheme I rowsLL).toCellScheme.gradedIndex z)) =
      fun z ↦ thinLabelling I A A F G ⊥ z.1 := funext fun z ↦ hX _
  rw [he]
  exact (isLawfulBelow_thinLabelling hIL hIR h).mono
    (X := ((univ : Finset (Fin 5)), k)) ⟨subset_rfl, hk3⟩

include hIL hIR in
/-- **The ordered-layer step below the top grade for the seeds of `TL` with itself**: with the
rows `rowsLL`, the rows at the grades `k ≤ 3` are coded and consistent, and the capped lifts from
both coatoms into `(univ, k)`, `1 ≤ k ≤ 3`, exist. -/
theorem orderedLayerStepBelowTop_of : I.OrderedLayerStepBelowTop rowsLL where
  row_lt _ hk1 hk3 _ _ := rowsLL_lt hk1 hk3 _
  isLawfulBelow_row _ hk1 hk3 := isLawfulBelow_row hIL hIR hk1 hk3
  cappedLift_left _ _ hk3 := cappedLift_left hIL hIR hk3
  cappedLift_right _ _ hk3 := cappedLift_right hIL hIR hk3

end VaughtConjecture.OrderedLayer.SeedLL

namespace VaughtConjecture

open TwoFaceLiftExistsCounterexample

/-- **The seed of `TL` with itself** over its face `{0, 1, 2}`. -/
noncomputable def seedLL (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_TL α) (isLegal_TL α) (restrictFace_TL α) (restrictFace_TL α)

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **A seed whose coatom types are both `TL` has bottom apexes.** -/
theorem hasBottomApexes_of_TL_TL (hIL : I.left = TL α) (hIR : I.right = TL α) :
    I.HasBottomApexes :=
  hasBottomApexes_of_addApex isLegalBelowFullGrade_SL isLegalBelowFullGrade_SL (fun _ ↦ rfl)
    (fun _ ↦ rfl) hIL hIR

/-- **The ordered-layer step of a seed whose coatom types are both `TL`**, with the layer rows
`OrderedLayer.SeedLL.rowsLL`. -/
theorem orderedLayerStep_of_TL_TL (hIL : I.left = TL α) (hIR : I.right = TL α) :
    I.OrderedLayerStep OrderedLayer.SeedLL.rowsLL :=
  (OrderedLayer.SeedLL.orderedLayerStepBelowTop_of hIL hIR).orderedLayerStep
    (hasBottomApexes_of_TL_TL hIL hIR) fun _ ↦ rfl

/-- **The ordered-layer step of `seedLL`.** -/
theorem orderedLayerStep_seedLL : (seedLL α).OrderedLayerStep OrderedLayer.SeedLL.rowsLL :=
  orderedLayerStep_of_TL_TL rfl rfl

/-- **`seedLL` has an ordered-layer step.** -/
theorem hasOrderedLayerStep_seedLL : (seedLL α).HasOrderedLayerStep :=
  ⟨_, orderedLayerStep_seedLL⟩

/-- **`seedLL` has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_seedLL :
    Nonempty (CompletionBelowFullGrade (seedLL α)) :=
  orderedLayerStep_seedLL.nonempty_completionBelowFullGrade

end Seed

end VaughtConjecture
