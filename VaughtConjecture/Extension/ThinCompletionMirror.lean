/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerStep
import VaughtConjecture.Extension.ThinCompletion

/-!
# The ordered-layer step for the mirror of the asymmetric seed, below the top grade

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: the
ordered-layer step of `VaughtConjecture.Extension.OrderedLayerStep` for the seeds whose first
coatom type is `T5` and whose second is `TL`, at the grades `k ≤ 3`); semantic contract,
items 2–4.

Let `I` be a seed on five points with `I.left = T5` and `I.right = TL`, with coatoms
`C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}`: the asymmetric seed `seedL` with its two coatom types
exchanged.  The coupling `G ≤ A` of `T5` is now on `C`, and the condition
`VisibilityReplaceFixedOfLT A G` of `TL` on `D`.

**The kinds** (`mirrorKind`): the kinds of `ThinCompletion.thinKind` with the kinds `1` and `2`
exchanged off the full scope (`swapKind`).  So the kind `1` (the *first* class) is now the live
cells of grade `1` of `D`, carrying `A_D`, and the kind `2` (the *second* class) the live cells of
grade `1` of `C` and the new cell at `(univ, 1)`, carrying `A_C`.  The labelling `mirrorLabel A_D
A_C F G Ω` reads a graded index by the kind, through `ThinCompletion.kindLabel`.

**The layer rows** (`rowsLM`): `ThinCompletion.thinRow k` read through `mirrorKind`, for
`k = 1, 2, 3`, and the top row at `(univ, 4)`.  They are the ordered rows of the thin completion of
`seedL` with the orientation reversed: `D` before `C`.  The row at `(univ, 3)` reads `A_D` at `1`
(the strip at the grade `3` of `TL`, now on `D`) and every other live kind at `ω + 3`.

**The lawful labellings below `(univ, 3)`** are exactly the labellings `mirrorLabel A_D A_C F G ⊥`
with `ThinCompletion.IsThinLawfulBelow A_D A_C F G`: `A_D ≤ A_C`, `G ≤ F`, `G ≤ A_C` (the coupling
of `T5` on `C`), `VisibilityReplaceFixedOfLT A_D G` (the condition of `TL` on `D`), and no
collision (`isLawfulBelow_mirrorLabelling`, `exists_of_isLawfulBelow_three`).  These are the
constraints of the thin completion of `seedL` with the roles of the two classes of grade `1`
exchanged, so the row witnesses (`ThinCompletion.transformsTo_rowOne`, `transformsTo_rowTwo`,
`transformsTo_rowThree`) and the parameter lift (`ThinCompletion.exists_thinLift`) apply with the
first class `A_D` and the second `A_C`.

**The theorem** (`orderedLayerStepBelowTop_of`): the ordered-layer step below the top grade holds
for every such seed, with the rows `rowsLM`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.OrderedLayer.Mirror

open Finset Label CellScheme
open Ordinal hiding univ
open ThinCompletion (thinKind thinLabel kindLabel thinRow IsThinLawfulBelow kindGrade
  snd_eq_kindGrade thinLabel_eq_tripleLabelling thinKind_ne_one thinKind_ne_two
  transformsTo_rowOne transformsTo_rowTwo transformsTo_rowThree thinRow_lt exists_thinLift
  isThinLawfulBelow_row_one isThinLawfulBelow_row_two isThinLawfulBelow_row_three)
open TwoFaceLiftExistsCounterexample (VisibilityReplaceFixedOfLT TL)
open CaseSplitCounterexample (T5 tripleLabelling)

/-! ### Kinds -/

/-- The exchange of the kinds `1` and `2`. -/
def swapKind : Fin 6 → Fin 6 := ![0, 2, 1, 3, 4, 5]

/-- The **mirrored kind** of a graded index on five points: the kind of `ThinCompletion.thinKind`
at the full scope, and that kind with `1` and `2` exchanged at another scope. -/
def mirrorKind (X : Finset (Fin 5) × ℕ) : Fin 6 :=
  if X.1 = univ then thinKind X else swapKind (thinKind X)

/-- The **mirrored labelling** of graded indices with the parameters `A_D` (the first class),
`A_C` (the second class), `F`, `G`, `Ω`. -/
noncomputable def mirrorLabel (AD AC F G Ω : Label.{u}) (X : Finset (Fin 5) × ℕ) : Label.{u} :=
  kindLabel AD AC F G Ω (mirrorKind X)

/-- Exchanging the kinds `1` and `2` exchanges the first two parameters. -/
theorem kindLabel_swapKind (a b F G Ω : Label.{u}) (c : Fin 6) :
    kindLabel a b F G Ω (swapKind c) = kindLabel b a F G Ω c := by
  fin_cases c <;> rfl

/-- Exchanging the kinds `1` and `2` keeps the grade of the kind. -/
theorem kindGrade_swapKind (c : Fin 6) : kindGrade (swapKind c) = kindGrade c := by
  fin_cases c <;> rfl

/-- At the full scope the mirrored kind is the kind. -/
theorem mirrorKind_univ (k : ℕ) :
    mirrorKind ((univ : Finset (Fin 5)), k) = thinKind ((univ : Finset (Fin 5)), k) :=
  ite_eq_left rfl

/-- A graded index of a live mirrored kind has the grade of its kind. -/
theorem snd_eq_kindGrade_mirror {X : Finset (Fin 5) × ℕ} (hX : mirrorKind X ≠ 0) :
    X.2 = kindGrade (mirrorKind X) := by
  unfold mirrorKind at hX ⊢
  split_ifs at hX ⊢ with h
  · exact snd_eq_kindGrade hX
  · rw [kindGrade_swapKind]
    exact snd_eq_kindGrade fun h0 ↦ hX (by rw [h0]; rfl)

/-- The mirrored kind of a graded index is at most one more than its grade. -/
theorem mirrorKind_le (X : Finset (Fin 5) × ℕ) : (mirrorKind X : ℕ) ≤ X.2 + 1 := by
  by_cases h : mirrorKind X = 0
  · rw [h]; exact Nat.zero_le _
  · rw [snd_eq_kindGrade_mirror h]
    generalize mirrorKind X = c
    fin_cases c <;> decide

/-- A graded index whose scope misses the point `4` (on the coatom `C`) is not of the first
class. -/
theorem mirrorKind_ne_one {X : Finset (Fin 5) × ℕ} (hX : (4 : Fin 5) ∉ X.1) : mirrorKind X ≠ 1 := by
  have hne : X.1 ≠ univ := fun h ↦ hX (h ▸ mem_univ _)
  rw [mirrorKind, ite_eq_right hne]
  exact (by decide : ∀ c : Fin 6, c ≠ 2 → swapKind c ≠ 1) _ (thinKind_ne_two hX)

/-- A graded index whose scope misses the point `3` (on the coatom `D`) is not of the second
class. -/
theorem mirrorKind_ne_two {X : Finset (Fin 5) × ℕ} (hX : (3 : Fin 5) ∉ X.1) : mirrorKind X ≠ 2 := by
  have hne : X.1 ≠ univ := fun h ↦ hX (h ▸ mem_univ _)
  rw [mirrorKind, ite_eq_right hne]
  exact (by decide : ∀ c : Fin 6, c ≠ 1 → swapKind c ≠ 2) _ (thinKind_ne_one hX)

/-- Below the full scope and below the grade `4`, the mirrored labelling is the labelling
`tripleLabelling A_C F A_D F G` of the amalgam. -/
theorem mirrorLabel_eq_tripleLabelling {X : Finset (Fin 5) × ℕ} (h1 : X.1 ≠ univ) (h4 : X.2 ≠ 4)
    (AD AC F G Ω : Label.{u}) :
    mirrorLabel AD AC F G Ω X = tripleLabelling AC F AD F G X := by
  rw [mirrorLabel, mirrorKind, ite_eq_right h1, kindLabel_swapKind]
  exact thinLabel_eq_tripleLabelling h1 h4 AC AD F G Ω

/-- The kind labelling does not read the first parameter at another kind. -/
theorem kindLabel_congr_one {c : Fin 6} (hc : c ≠ 1) (a a' b F G Ω : Label.{u}) :
    kindLabel a b F G Ω c = kindLabel a' b F G Ω c := by
  fin_cases c <;> first | rfl | exact (hc rfl).elim

/-- The kind labelling does not read the second parameter at another kind. -/
theorem kindLabel_congr_two {c : Fin 6} (hc : c ≠ 2) (a b b' F G Ω : Label.{u}) :
    kindLabel a b F G Ω c = kindLabel a b' F G Ω c := by
  fin_cases c <;> first | rfl | exact (hc rfl).elim

/-- Two kind labellings whose parameters agree capped at `c` agree capped at `c` (with `Ω = ⊥`). -/
theorem min_kindLabel_eq {c a b F G a' b' F' G' : Label.{u}}
    (ha : min a c = min a' c) (hb : min b c = min b' c) (hF : min F c = min F' c)
    (hG : min G c = min G' c) (k : Fin 6) :
    min (kindLabel a b F G ⊥ k) c = min (kindLabel a' b' F' G' ⊥ k) c := by
  fin_cases k
  exacts [rfl, ha, hb, hF, hG, rfl]

/-- At a graded index of grade `k`, the mirrored labelling is at most the parameter of the grade
`k`, when `A_D ≤ A_C`. -/
theorem mirrorLabel_le {AD AC F G Ω : Label.{u}} (hle : AD ≤ AC) {X : Finset (Fin 5) × ℕ}
    {k : ℕ} (hX : X.2 = k) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    mirrorLabel AD AC F G Ω X ≤ kindLabel AD AC F G Ω (thinKind ((univ : Finset (Fin 5)), k)) := by
  unfold mirrorLabel
  by_cases h : mirrorKind X = 0
  · rw [h]; exact bot_le
  have hg := snd_eq_kindGrade_mirror h
  rw [hX] at hg
  obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  all_goals
    simp only [ThinCompletion.thinKind_univ_one, ThinCompletion.thinKind_univ_two,
      ThinCompletion.thinKind_univ_three, ThinCompletion.thinKind_univ_four]
    generalize mirrorKind X = c at h hg
    fin_cases c <;> first | exact absurd hg (by decide) | exact (h rfl).elim | exact le_rfl | skip
  exact hle

/-! ### The layer rows -/

/-- **The layer rows of the mirror seed**: the ordered rows of the thin completion read through
the mirrored kinds at `(univ, k)`, `k = 1, 2, 3` (the live cells of grade `1` of `D` before those
of `C`), and the top row at `(univ, 4)`. -/
noncomputable def rowsLM : LayerRows.{u}
  | 1 => fun X ↦ thinRow 1 (mirrorKind X)
  | 2 => fun X ↦ thinRow 2 (mirrorKind X)
  | 3 => fun X ↦ thinRow 3 (mirrorKind X)
  | _ => topRow

/-- The layer row at `(univ, 4)` is the top row. -/
theorem rowsLM_four : rowsLM.{u} 4 = topRow := rfl

/-- The row of the new cell at `(univ, k)`, `k ≤ 3`, is the mirrored labelling of the parameters
of its row, which satisfy the constraints. -/
theorem rowsLM_eq_mirrorLabel {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    ∃ AD AC F G : Label.{u}, IsThinLawfulBelow AD AC F G ∧
      ∀ X, rowsLM k X = mirrorLabel AD AC F G ⊥ X := by
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · exact ⟨_, _, _, _, isThinLawfulBelow_row_one, fun _ ↦ rfl⟩
  · exact ⟨_, _, _, _, isThinLawfulBelow_row_two, fun _ ↦ rfl⟩
  · exact ⟨_, _, _, _, isThinLawfulBelow_row_three, fun _ ↦ rfl⟩

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-! ### Cells of the layer scheme -/

/-- The mirrored kind of a cell below the new cell at `(univ, k)` is at most `k + 1`. -/
theorem mirrorKind_le_of_mem_below_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (t : (layerScheme I rowsLM).toCellScheme.below
      ((layerScheme I rowsLM).toCellScheme.gradedIndex (newCell I rowsLM k))) :
    (mirrorKind ((layerScheme I rowsLM).toCellScheme.gradedIndex t.1) : ℕ) ≤ k + 1 :=
  (mirrorKind_le _).trans (Nat.succ_le_succ (grade_le_of_mem_below_newCell hk1 hk4 t))

variable (I) in
/-- The **mirrored labelling** of the cells of the layer scheme, read off their graded indices. -/
noncomputable def mirrorLabelling (AD AC F G Ω : Label.{u})
    (z : Fin (layerScheme I rowsLM).card) : Label.{u} :=
  mirrorLabel AD AC F G Ω ((layerScheme I rowsLM).toCellScheme.gradedIndex z)

/-- The mirrored labelling at the new cell at `(univ, k)`. -/
theorem mirrorLabelling_newCell {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (AD AC F G Ω : Label.{u}) :
    mirrorLabelling I AD AC F G Ω (newCell I rowsLM k) =
      kindLabel AD AC F G Ω (thinKind ((univ : Finset (Fin 5)), k)) := by
  rw [mirrorLabelling, gradedIndex_newCell hk1 hk4, mirrorLabel, mirrorKind_univ]

/-! ### The coupling of `TL` on a coatom -/

/-- A labelling of graded indices whose reading along `f` is `labelling A F G` is lawful below the
coatom `univ.map f` at the grade `3`, for a stage type whose face along `f` is `TL`, under
`G ≤ F` and `VisibilityReplaceFixedOfLT A G`. -/
private theorem isLawfulBelow_coatomTL {A F G : Label.{u}} (hA : IsSelfVisible 1 A)
    (hF : IsSelfVisible 2 F) (hG : IsSelfVisible 3 G) (hGF : G ≤ F)
    (hc : VisibilityReplaceFixedOfLT A G)
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
    convert (TwoFaceLiftExistsCounterexample.isLawful_labelling hA hF hG hGF hc).isLawfulBelow
      ((univ : Finset (Fin 4)), 3) using 1
    funext d
    refine (hx _).trans ?_
    rw [TwoFaceLiftExistsCounterexample.gradedIndex_TL_castSucc]
    exact hL d.1
  exact (Scheme.isLawfulBelow_comap_cellMap_iff Am.toScheme f ((univ : Finset (Fin 4)), 3)
    fun d ↦ Lf (Am.toCellScheme.gradedIndex d)).mp
    (hlaw _ fun i ↦ congrArg Lf (Am.toScheme.map_comap_gradedIndex f i).symm)

/-- **`tripleLabelling` is lawful below both coatoms at the grade `3`** on a seed whose first type
is `T5` and second `TL`: on the first under `G ≤ A_C`, `G ≤ F_C`; on the second under `G ≤ F_D`
and `VisibilityReplaceFixedOfLT A_D G`. -/
theorem isLawfulBelow_tripleLabelling (hIL : I.left = T5 α) (hIR : I.right = TL α)
    {AC FC AD FD G : Label.{u}} (hAC : IsSelfVisible 1 AC) (hFC : IsSelfVisible 2 FC)
    (hAD : IsSelfVisible 1 AD) (hFD : IsSelfVisible 2 FD) (hG : IsSelfVisible 3 G)
    (hGAC : G ≤ AC) (hGFC : G ≤ FC) (hGFD : G ≤ FD) (hcD : VisibilityReplaceFixedOfLT AD G) :
    I.amalgam.rows.IsLawfulBelow (coatomC, 3)
        (fun d ↦ tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d)) ∧
      I.amalgam.rows.IsLawfulBelow (coatomD, 3)
        (fun d ↦ tripleLabelling AC FC AD FD G (I.amalgam.toCellScheme.gradedIndex d)) := by
  constructor
  · rw [coatomC_eq]
    exact CaseSplitCounterexample.isLawfulBelow_coatom hAC hFC hG hGAC hGFC
      (hIL ▸ I.restrictFace_left) (CaseSplitCounterexample.tripleLabelling_left AC FC AD FD G)
  · rw [coatomD_eq]
    exact isLawfulBelow_coatomTL hAD hFD hG hGFD hcD (hIR ▸ I.restrictFace_right)
      (CaseSplitCounterexample.tripleLabelling_right AC FC AD FD G)

/-! ### Lawful labellings below the two coatoms -/

variable (hIL : I.left = T5 α) (hIR : I.right = TL α)

include hIL in
/-- **Lawful labellings below `(C, 3)`**: `mirrorLabel ⊥ A F G ⊥` with the constraints of `T5`. -/
theorem exists_of_isLawfulBelow_left {w : Fin (layerScheme I rowsLM).card → Label.{u}}
    (hw : (layerScheme I rowsLM).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ A ∧
      G ≤ F ∧ ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3),
        w z = mirrorLabel ⊥ A F G ⊥ ((layerScheme I rowsLM).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomC_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGA, hGF, hall⟩ :=
    CaseSplitCounterexample.exists_labelling_of_comap (hIL ▸ I.restrictFace_left) le_rfl
      (fun d ↦ w (oldCell I rowsLM d)) hw'
  refine ⟨A, F, G, hA, hF, hG, hGA, hGF, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ :=
    (image_oldCell_below (I := I) (ρ := rowsLM) (X := (coatomC, 3)) (by decide)).symm ▸ hz
  rw [coatomC_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, mirrorLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_left]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

include hIR in
/-- **Lawful labellings below `(D, 3)`**: `mirrorLabel A ⊥ F G ⊥` with the constraints of `TL`. -/
theorem exists_of_isLawfulBelow_right {w : Fin (layerScheme I rowsLM).card → Label.{u}}
    (hw : (layerScheme I rowsLM).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z) :
    ∃ A F G : Label.{u}, IsSelfVisible 1 A ∧ IsSelfVisible 2 F ∧ IsSelfVisible 3 G ∧ G ≤ F ∧
      VisibilityReplaceFixedOfLT A G ∧ ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3),
        w z = mirrorLabel A ⊥ F G ⊥ ((layerScheme I rowsLM).toCellScheme.gradedIndex z) := by
  have hw' := (isLawfulBelow_oldCell_iff (by decide)).mp hw
  rw [coatomD_eq] at hw'
  obtain ⟨A, F, G, hA, hF, hG, hGF, hc, hall⟩ :=
    TwoFaceLiftExistsCounterexample.exists_labelling_of_comap_TL (hIR ▸ I.restrictFace_right)
      le_rfl (fun d ↦ w (oldCell I rowsLM d)) hw'
  refine ⟨A, F, G, hA, hF, hG, hGF, hc, fun z hz ↦ ?_⟩
  obtain ⟨d, hd, rfl⟩ :=
    (image_oldCell_below (I := I) (ρ := rowsLM) (X := (coatomD, 3)) (by decide)).symm ▸ hz
  rw [coatomD_eq] at hd
  obtain ⟨c, hgi, hpc⟩ := hall d hd
  rw [hpc, gradedIndex_oldCell, hgi, mirrorLabel_eq_tripleLabelling, ← hgi]
  · rw [hgi, CaseSplitCounterexample.tripleLabelling_right]
  · rw [← hgi]; exact I.scope_ne_univ d
  · rw [← hgi]; have := hd.2; simp only at this; omega

/-! ### Sufficiency: the mirrored labellings are lawful below `(univ, 3)` -/

include hIL hIR in
/-- **The mirrored labellings are lawful below the coatoms** at the grade `3`: on the old cells
they are the labellings `tripleLabelling A_C F A_D F G`. -/
theorem isLawfulBelow_coatom_mirrorLabelling {AD AC F G Ω : Label.{u}}
    (h : IsThinLawfulBelow AD AC F G) :
    (layerScheme I rowsLM).rows.IsLawfulBelow (coatomC, 3)
        (fun z ↦ mirrorLabelling I AD AC F G Ω z) ∧
      (layerScheme I rowsLM).rows.IsLawfulBelow (coatomD, 3)
        (fun z ↦ mirrorLabelling I AD AC F G Ω z) := by
  have hCD := isLawfulBelow_tripleLabelling (I := I) hIL hIR h.svAD h.svF h.svAC h.svF h.svG
    h.G_le_AD h.G_le_F h.G_le_F h.visibilityReplaceFixed
  have key (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      mirrorLabelling I AD AC F G Ω (oldCell I rowsLM d) =
        tripleLabelling AC F AD F G (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [mirrorLabelling, gradedIndex_oldCell]
    exact mirrorLabel_eq_tripleLabelling (I.scope_ne_univ d)
      (show I.amalgam.toCellScheme.grade d ≠ 4 by omega) _ _ _ _ _
  constructor
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomC, 3))
      fun d hd ↦ (key d hd.2).symm).mp hCD.1
  · rw [isLawfulBelow_oldCell_iff (by decide)]
    exact (Rows.isLawfulBelow_congr (D := I.amalgam.toCellScheme) (X := (coatomD, 3))
      fun d hd ↦ (key d hd.2).symm).mp hCD.2

include hIL hIR in
/-- **Sufficiency**: the mirrored labelling of parameters satisfying
`ThinCompletion.IsThinLawfulBelow A_D A_C F G` is lawful below `(univ, 3)`. -/
theorem isLawfulBelow_mirrorLabelling {AD AC F G Ω : Label.{u}}
    (h : IsThinLawfulBelow AD AC F G) :
    (layerScheme I rowsLM).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      (fun z ↦ mirrorLabelling I AD AC F G Ω z) := by
  obtain ⟨hC, hD⟩ := isLawfulBelow_coatom_mirrorLabelling hIL hIR (Ω := Ω) h
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp hC
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp hD
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hne : (layerScheme I rowsLM).toCellScheme.scope d = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hd.2
      rw [grade_newCell hj1 hj4, mirrorLabelling_newCell hj1 hj4]
      obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      · exact h.svAD
      · exact h.svF
      · exact h.svG
    · exact (mem_below_coatom_of_ne hd hne).elim (hoC d) (hoD d)
  · rcases cell_cases s with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
    · exact (mem_below_coatom_of_ne hs (scope_oldCell_ne d)).elim (hlC _) (hlD _)
    · rw [row_newCell_eq le_rfl (by omega), mirrorLabelling_newCell le_rfl (by omega)]
      exact transformsTo_rowOne _
        (fun t ↦ mirrorKind ((layerScheme I rowsLM).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell le_rfl (by omega))
        (mirrorKind_le_of_mem_below_newCell le_rfl (by omega)) h.svAC h.svAD h.le_AD
    · rw [row_newCell_eq (by omega) (by omega), mirrorLabelling_newCell (by omega) (by omega)]
      exact transformsTo_rowTwo _
        (fun t ↦ mirrorKind ((layerScheme I rowsLM).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (mirrorKind_le_of_mem_below_newCell (by omega) (by omega)) h.svAC h.svAD h.svF h.le_AD
        h.noCollision
    · rw [row_newCell_eq (by omega) (by omega), mirrorLabelling_newCell (by omega) (by omega)]
      exact transformsTo_rowThree _
        (fun t ↦ mirrorKind ((layerScheme I rowsLM).toCellScheme.gradedIndex t.1))
        (grade_le_of_mem_below_newCell (by omega) (by omega))
        (mirrorKind_le_of_mem_below_newCell (by omega) (by omega)) h.svG
        h.visibilityReplaceFixed h.G_le_AD h.G_le_F
    · have h4 : (layerScheme I rowsLM).toCellScheme.gradedIndex (newCell I rowsLM 4) ≤
          ((univ : Finset (Fin 5)), 3) := hs
      rw [gradedIndex_newCell (by omega) le_rfl] at h4
      exact absurd h4.2 (by decide)
  · by_cases hne : (layerScheme I rowsLM).toCellScheme.scope t = univ
    · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
      refine ⟨newCell I rowsLM j, rfl, ?_⟩
      rw [mirrorLabelling_newCell hj1 hj4]
      exact mirrorLabel_le h.le_AD (hg.trans (grade_newCell hj1 hj4)) hj1 hj4
    · exact (mem_below_coatom_of_ne ht hne).elim (haC s t · hst hg) (haD s t · hst hg)

/-! ### Necessity: the lawful labellings below `(univ, 3)` are mirrored labellings -/

include hIL hIR in
/-- **Necessity**: every labelling lawful below `(univ, 3)` is a mirrored labelling, of parameters
satisfying `ThinCompletion.IsThinLawfulBelow A_D A_C F G`.  On `C` it is a labelling of `T5`, on
`D` one of `TL`; locality and availability at the new cells identify `A_C`, `F` (on both coatoms)
and `G` with their labels, and give `A_D ≤ A_C`; the collision lemma at the new cell at
`(univ, 2)` excludes collisions. -/
theorem exists_of_isLawfulBelow_three {w : Fin (layerScheme I rowsLM).card → Label.{u}}
    (hw : (layerScheme I rowsLM).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ w z) :
    ∃ AD AC F G : Label.{u}, IsThinLawfulBelow AD AC F G ∧
      ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        w z = mirrorLabelling I AD AC F G ⊥ z := by
  -- Step 1: below `C`, `w` is a labelling of `T5`; below `D`, one of `TL`.
  have hC : (layerScheme I rowsLM).rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z :=
    hw.mono (X := (coatomC, 3)) ⟨subset_univ _, le_rfl⟩
  have hD : (layerScheme I rowsLM).rows.IsLawfulBelow (coatomD, 3) fun z ↦ w z :=
    hw.mono (X := (coatomD, 3)) ⟨subset_univ _, le_rfl⟩
  obtain ⟨AC, FC, GC, hAC, hFC, hGC, hGAC, hGFC, hC'⟩ := exists_of_isLawfulBelow_left hIL hC
  obtain ⟨AD, FD, GD, hAD, hFD, hGD, hGFD, hcD, hD'⟩ := exists_of_isLawfulBelow_right hIR hD
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
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ :=
      TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hw₁ : w (oldCell I rowsLM d₁) = AC := by
    rw [hC' _ (oldCell_mem_below (by rw [hd₁]; decide)), gradedIndex_oldCell, hd₁]; rfl
  have hwsC : w (oldCell I rowsLM sC) = FC := by
    rw [hC' _ (oldCell_mem_below (by rw [hsC]; decide)), gradedIndex_oldCell, hsC]; rfl
  have hwgC : w (oldCell I rowsLM gE) = GC := by
    rw [hC' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hwgD : w (oldCell I rowsLM gE) = GD := by
    rw [hD' _ (oldCell_mem_below (by rw [hgE]; decide)), gradedIndex_oldCell, hgE]; rfl
  have hw₂ : w (oldCell I rowsLM d₂) = AD := by
    rw [hD' _ (oldCell_mem_below (by rw [hd₂]; decide)), gradedIndex_oldCell, hd₂]; rfl
  have hwsD : w (oldCell I rowsLM sD) = FD := by
    rw [hD' _ (oldCell_mem_below (by rw [hsD]; decide)), gradedIndex_oldCell, hsD]; rfl
  have hGCD : GC = GD := hwgC.symm.trans hwgD
  -- Step 3: locality (`hle`) and availability (`hge`) at the new cell at `(univ, k)` compare its
  -- label with that of an old cell of grade `k`.
  have hrow {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      (layerScheme I rowsLM).rows.row (newCell I rowsLM k)
          ⟨oldCell I rowsLM d, oldCell_mem_below_newCell hk1 hk4 hd⟩ =
        rowsLM k (I.amalgam.toCellScheme.gradedIndex d) := by
    rw [row_newCell hk1 hk4, gradedIndex_oldCell]
  have hrowself {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
      (layerScheme I rowsLM).rows.row (newCell I rowsLM k)
          ⟨newCell I rowsLM k, newCell_mem_below_self⟩ =
        rowsLM k ((univ : Finset (Fin 5)), k) := by
    rw [row_newCell hk1 hk4, gradedIndex_newCell hk1 hk4]
  have hle {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k)
      (hr : rowsLM k ((univ : Finset (Fin 5)), k) ≤
        rowsLM k (I.amalgam.toCellScheme.gradedIndex d)) :
      w (newCell I rowsLM k) ≤ w (oldCell I rowsLM d) := by
    have := (hl _ (newCell_mem_below hk1 (by omega) hk3)).le_of_le
      (d := ⟨newCell I rowsLM k, newCell_mem_below_self⟩)
      (d' := ⟨oldCell I rowsLM d, oldCell_mem_below_newCell hk1 (by omega) hd.le⟩)
      (by rw [hrowself hk1 (by omega), hrow hk1 (by omega) hd.le]; exact hr)
      (show (layerScheme I rowsLM).toCellScheme.grade (oldCell I rowsLM d) ≤
          (layerScheme I rowsLM).toCellScheme.grade (newCell I rowsLM k) by
        rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have hge {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) {d : Fin I.amalgam.card}
      (hd : I.amalgam.toCellScheme.grade d = k) :
      w (oldCell I rowsLM d) ≤ w (newCell I rowsLM k) := by
    obtain ⟨u, hu, hle⟩ := ha (oldCell I rowsLM d) (newCell I rowsLM k)
      (newCell_mem_below hk1 (by omega) hk3)
      (by rw [scope_newCell hk1 (by omega)]; exact subset_univ _)
      (by rw [grade_oldCell, hd, grade_newCell hk1 (by omega)])
    rwa [eq_newCell hk1 (by omega) (hu.trans (gradedIndex_newCell hk1 (by omega)))] at hle
  have hn₁ : w (newCell I rowsLM 1) = AC := by
    rw [← hw₁]
    exact le_antisymm (hle le_rfl (by omega) (congrArg Prod.snd hd₁) (by rw [hd₁]; rfl))
      (hge le_rfl (by omega) (congrArg Prod.snd hd₁))
  have hn₂C : w (newCell I rowsLM 2) = FC := by
    rw [← hwsC]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsC) (by rw [hsC]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsC))
  have hn₂D : w (newCell I rowsLM 2) = FD := by
    rw [← hwsD]
    exact le_antisymm (hle (by omega) (by omega) (congrArg Prod.snd hsD) (by rw [hsD]; rfl))
      (hge (by omega) (by omega) (congrArg Prod.snd hsD))
  have hn₃ : w (newCell I rowsLM 3) = GC := by
    rw [← hwgC]
    exact le_antisymm (hle (by omega) le_rfl (congrArg Prod.snd hgE) (by rw [hgE]; rfl))
      (hge (by omega) le_rfl (congrArg Prod.snd hgE))
  have hADAC : AD ≤ AC := hw₂ ▸ hn₁ ▸ hge le_rfl (by omega) (congrArg Prod.snd hd₂)
  have hFCD : FC = FD := hn₂C.symm.trans hn₂D
  -- Step 4: no collision, by the collision lemma at the new cell at `(univ, 2)`.
  have hnc : AD = AC → AD < FC → IsSelfVisible 2 AD := by
    intro heq hlt
    by_contra hev
    have hg₁' : I.amalgam.toCellScheme.grade d₁ = 1 := congrArg Prod.snd hd₁
    have hg₂' : I.amalgam.toCellScheme.grade d₂ = 1 := congrArg Prod.snd hd₂
    have hg₁ : I.amalgam.toCellScheme.grade d₁ ≤ 2 := by omega
    have hg₂ : I.amalgam.toCellScheme.grade d₂ ≤ 2 := by omega
    have := eq_of_transformsTo_collision
      (hl _ (newCell_mem_below (by omega) (by omega) (by omega)))
      (d₁ := ⟨oldCell I rowsLM d₂, oldCell_mem_below_newCell (by omega) (by omega) hg₂⟩)
      (d₂ := ⟨oldCell I rowsLM d₁, oldCell_mem_below_newCell (by omega) (by omega) hg₁⟩)
      (z := ⟨newCell I rowsLM 2, newCell_mem_below_self⟩)
      ((grade_oldCell d₂).trans hg₂') ((grade_oldCell d₁).trans hg₁')
      (grade_newCell (by omega) (by omega))
      (by rw [hrow (by omega) (by omega) hg₂, hd₂]; exact isSelfVisible_gridPoint 1 0)
      (by rw [hrow (by omega) (by omega) hg₁, hd₁]; exact isSelfVisible_gridPoint 1 1)
      (e := AD) (by simp only; rw [hw₂, hn₂C, min_eq_left hlt.le])
      (by simp only; rw [hw₁, hn₂C, ← heq, min_eq_left hlt.le]) hev
      (by simp only; rw [hn₂C, min_self]; exact hlt)
    rw [hrow (by omega) (by omega) hg₂, hrow (by omega) (by omega) hg₁, hd₂, hd₁] at this
    exact absurd this (gridPoint_lt_gridPoint.mpr (by omega)).ne
  -- Step 5: `w` is the mirrored labelling of these parameters.
  refine ⟨AD, AC, FC, GC, ⟨hAD, hAC, hFC, hGC, hADAC, hGFC, hGAC, hGCD ▸ hcD, hnc⟩,
    fun z hz ↦ ?_⟩
  by_cases hne : (layerScheme I rowsLM).toCellScheme.scope z = univ
  · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
    have hj3 : j ≤ 3 := (grade_newCell hj1 hj4).symm.trans_le hz.2
    rw [mirrorLabelling_newCell hj1 hj4]
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · exact hn₁
    · exact hn₂C
    · exact hn₃
  · rcases mem_below_coatom_of_ne hz hne with h | h
    · rw [hC' z h, mirrorLabelling, mirrorLabel, mirrorLabel]
      exact kindLabel_congr_one (mirrorKind_ne_one (four_notMem_of_mem_below h)) _ _ _ _ _ _
    · rw [hD' z h, mirrorLabelling, ← hFCD, ← hGCD, mirrorLabel, mirrorLabel]
      exact kindLabel_congr_two (mirrorKind_ne_two (three_notMem_of_mem_below h)) _ _ _ _ _ _

/-! ### The lifts from the coatoms at the grade `3` -/

/-- A property of `a` holds at every member of `some a`. -/
private theorem forall_mem_some {β : Type*} {a : β} {P : β → Prop} (h : P a) : ∀ b ∈ some a, P b :=
  fun _ hb ↦ (Option.some_inj.mp hb) ▸ h

/-- Every property holds at every member of `none`. -/
private theorem forall_mem_none {β : Type*} {P : β → Prop} : ∀ b ∈ (none : Option β), P b :=
  fun _ hb ↦ by cases hb

include hIL hIR in
/-- **The lift from `(C, 3)` to `(univ, 3)`**, for a cap `c` self-visible at `1`, and at `2` unless
the prescription is `⊥` at the grade `2`: the parameters of the prescription (`T5`, the second
class) and of the ambient are lifted by `ThinCompletion.exists_thinLift`, with `A_D` (the first
class) unprescribed. -/
theorem exists_lift_left {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {p q : Fin (layerScheme I rowsLM).card → Label.{u}}
    (hp : (layerScheme I rowsLM).rows.IsLawfulBelow (coatomC, 3) fun z ↦ p z)
    (hq : (layerScheme I rowsLM).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3),
      min (q z) c = min (p z) c)
    (hc2 : IsSelfVisible 2 c ∨ ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3),
      (layerScheme I rowsLM).toCellScheme.grade z = 2 → p z = ⊥) :
    ∃ x : Fin (layerScheme I rowsLM).card → Label.{u},
      (layerScheme I rowsLM).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I rowsLM).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3), x z = p z := by
  -- Step 1: the parameters of the prescription (a labelling of `T5`) and of the ambient.
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGAp, hGFp, hp'⟩ := exists_of_isLawfulBelow_left hIL hp
  obtain ⟨qAD, qAC, qF, qG, hq', hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
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
  have h₁ : oldCell I rowsLM d₁ ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hd₁]; decide)
  have hs : oldCell I rowsLM sC ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hsC]; decide)
  have hg : oldCell I rowsLM gE ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomC, 3)) :
      z ∈ (layerScheme I rowsLM).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  -- Step 3: at those cells, the prescribed parameters agree with the ambient capped at `c`.
  have hAq : min Ap c = min qAC c := by
    have := hpq _ h₁
    rw [hp' _ h₁, hqz _ (hmem h₁), mirrorLabelling, gradedIndex_oldCell, hd₁] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), mirrorLabelling, gradedIndex_oldCell, hsC] at this
    exact this.symm
  have hGq : min Gp c = min qG c := by
    have := hpq _ hg
    rw [hp' _ hg, hqz _ (hmem hg), mirrorLabelling, gradedIndex_oldCell, hgE] at this
    exact this.symm
  -- Step 4: the parameter-level lift, with the first class unprescribed.
  have hc2' : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    refine hc2.imp_right fun h ↦ ?_
    have := h _ hs (by rw [grade_oldCell]; exact congrArg Prod.snd hsC)
    rw [hp' _ hs, gradedIndex_oldCell, hsC] at this
    exact congrArg some this
  obtain ⟨xAD, xAC, xF, xG, hx, hxAD, hxAC, hxF, hxG, -, hpAC, hpF, hpG⟩ :=
    exists_thinLift hc1 (PAC := none) (PAD := some Ap) (PF := some Fp) (PG := some Gp) hc2'
      (.inr rfl) hq' forall_mem_none (forall_mem_some hAp) (forall_mem_some hFp)
      (forall_mem_some hGp) forall_mem_none
      (forall_mem_some (forall_mem_some hGFp)) (forall_mem_some (forall_mem_some hGAp))
      forall_mem_none forall_mem_none
      forall_mem_none (forall_mem_some hAq) (forall_mem_some hFq) (forall_mem_some hGq)
  refine ⟨mirrorLabelling I xAD xAC xF xG ⊥, isLawfulBelow_mirrorLabelling hIL hIR hx,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_kindLabel_eq hxAD hxAC hxF hxG _
  · rw [hp' z hz, mirrorLabelling, hpAC Ap rfl, hpF Fp rfl, hpG Gp rfl, mirrorLabel, mirrorLabel]
    exact kindLabel_congr_one (mirrorKind_ne_one (four_notMem_of_mem_below hz)) _ _ _ _ _ _

include hIL hIR in
/-- **The lift from `(D, 3)` to `(univ, 3)`**, for a cap `c` self-visible at `1`, and at `2` unless
the prescription is `⊥` at the grade `2`: the parameters of the prescription (`TL`, the first
class) and of the ambient are lifted by `ThinCompletion.exists_thinLift`, with `A_C` (the second
class) unprescribed. -/
theorem exists_lift_right {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {p q : Fin (layerScheme I rowsLM).card → Label.{u}}
    (hp : (layerScheme I rowsLM).rows.IsLawfulBelow (coatomD, 3) fun z ↦ p z)
    (hq : (layerScheme I rowsLM).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3),
      min (q z) c = min (p z) c)
    (hc2 : IsSelfVisible 2 c ∨ ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3),
      (layerScheme I rowsLM).toCellScheme.grade z = 2 → p z = ⊥) :
    ∃ x : Fin (layerScheme I rowsLM).card → Label.{u},
      (layerScheme I rowsLM).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (layerScheme I rowsLM).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3), x z = p z := by
  -- Step 1: the parameters of the prescription (a labelling of `TL`) and of the ambient.
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGFp, hcp, hp'⟩ := exists_of_isLawfulBelow_right hIR hp
  obtain ⟨qAD, qAC, qF, qG, hq', hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
  -- Step 2: the cells `({4}, 1)`, `(D, 2)` and `(E, 3)`, one of each live kind on `D`.
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ :=
      TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ :=
      TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₂ : oldCell I rowsLM d₂ ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hd₂]; decide)
  have hs : oldCell I rowsLM sD ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hsD]; decide)
  have hg : oldCell I rowsLM gE ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (layerScheme I rowsLM).toCellScheme.below (coatomD, 3)) :
      z ∈ (layerScheme I rowsLM).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  -- Step 3: at those cells, the prescribed parameters agree with the ambient capped at `c`.
  have hAq : min Ap c = min qAD c := by
    have := hpq _ h₂
    rw [hp' _ h₂, hqz _ (hmem h₂), mirrorLabelling, gradedIndex_oldCell, hd₂] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), mirrorLabelling, gradedIndex_oldCell, hsD] at this
    exact this.symm
  have hGq : min Gp c = min qG c := by
    have := hpq _ hg
    rw [hp' _ hg, hqz _ (hmem hg), mirrorLabelling, gradedIndex_oldCell, hgE] at this
    exact this.symm
  -- Step 4: the parameter-level lift, with the second class unprescribed.
  have hc2' : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    refine hc2.imp_right fun h ↦ ?_
    have := h _ hs (by rw [grade_oldCell]; exact congrArg Prod.snd hsD)
    rw [hp' _ hs, gradedIndex_oldCell, hsD] at this
    exact congrArg some this
  obtain ⟨xAD, xAC, xF, xG, hx, hxAD, hxAC, hxF, hxG, hpAD, -, hpF, hpG⟩ :=
    exists_thinLift hc1 (PAC := some Ap) (PAD := none) (PF := some Fp) (PG := some Gp) hc2'
      (.inr rfl) hq' (forall_mem_some hAp) forall_mem_none (forall_mem_some hFp)
      (forall_mem_some hGp) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some hGFp)) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some hcp)) (forall_mem_some forall_mem_none)
      (forall_mem_some hAq) forall_mem_none (forall_mem_some hFq) (forall_mem_some hGq)
  refine ⟨mirrorLabelling I xAD xAC xF xG ⊥, isLawfulBelow_mirrorLabelling hIL hIR hx,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_kindLabel_eq hxAD hxAC hxF hxG _
  · rw [hp' z hz, mirrorLabelling, hpAD Ap rfl, hpF Fp rfl, hpG Gp rfl, mirrorLabel, mirrorLabel]
    exact kindLabel_congr_two (mirrorKind_ne_two (three_notMem_of_mem_below hz)) _ _ _ _ _ _

/-! ### Capped lifts from the coatoms to the full scope -/

include hIL hIR in
/-- **The capped lift from `(C, k)` to `(univ, k)`**, `1 ≤ k ≤ 3`. -/
theorem cappedLift_left {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (layerScheme I rowsLM).rows.CappedLift (X := (coatomC, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_lift_three hk3 fun _ hc _ _ hp hq hp0 _ hpq ↦
    exists_lift_left hIL hIR (hc.mono hk1) hp hq hpq
      (if h : 2 ≤ k then .inl (hc.mono h) else .inr fun z _ hz ↦ hp0 z (by omega))

include hIL hIR in
/-- **The capped lift from `(D, k)` to `(univ, k)`**, `1 ≤ k ≤ 3`. -/
theorem cappedLift_right {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (layerScheme I rowsLM).rows.CappedLift (X := (coatomD, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_lift_three hk3 fun _ hc _ _ hp hq hp0 _ hpq ↦
    exists_lift_right hIL hIR (hc.mono hk1) hp hq hpq
      (if h : 2 ≤ k then .inl (hc.mono h) else .inr fun z _ hz ↦ hp0 z (by omega))

/-! ### The ordered-layer step below the top grade -/

include hIL hIR in
/-- **The rows of the new cells at the grades `k ≤ 3` are consistent**: each is the mirrored
labelling of parameters satisfying the constraints. -/
theorem isLawfulBelow_row {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (layerScheme I rowsLM).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k)
      fun z ↦ rowsLM k ((layerScheme I rowsLM).toCellScheme.gradedIndex z) := by
  obtain ⟨AD, AC, F, G, h, hX⟩ := rowsLM_eq_mirrorLabel.{u} hk1 hk3
  have he : (fun z : (layerScheme I rowsLM).toCellScheme.below ((univ : Finset (Fin 5)), k) ↦
      rowsLM k ((layerScheme I rowsLM).toCellScheme.gradedIndex z)) =
      fun z ↦ mirrorLabelling I AD AC F G ⊥ z.1 := funext fun z ↦ hX _
  rw [he]
  exact (isLawfulBelow_mirrorLabelling hIL hIR h).mono
    (X := ((univ : Finset (Fin 5)), k)) ⟨subset_rfl, hk3⟩

include hIL hIR in
/-- **The ordered-layer step below the top grade for the mirror seeds**: with the rows `rowsLM`,
oriented `D` before `C`, the rows at the grades `k ≤ 3` are coded and consistent, and the capped
lifts from both coatoms into `(univ, k)`, `1 ≤ k ≤ 3`, exist. -/
theorem orderedLayerStepBelowTop_of : I.OrderedLayerStepBelowTop rowsLM where
  row_lt k hk1 hk3 z _ := by
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact thinRow_lt 1 _
    · exact thinRow_lt 2 _
    · exact thinRow_lt 3 _
  isLawfulBelow_row _ hk1 hk3 := isLawfulBelow_row hIL hIR hk1 hk3
  cappedLift_left _ hk1 hk3 := cappedLift_left hIL hIR hk1 hk3
  cappedLift_right _ hk1 hk3 := cappedLift_right hIL hIR hk1 hk3

end VaughtConjecture.OrderedLayer.Mirror
