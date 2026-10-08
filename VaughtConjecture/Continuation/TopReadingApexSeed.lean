/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCap
import VaughtConjecture.Continuation.TopReadingApex
import VaughtConjecture.Extension.ThinCompletionTLTL

/-!
# An isolated marker at a seed: the sheet layers do not carry the top reading at `TL`

Roadmap, Layer 3 ((R3) of the table of 3.4).

`TowerProfile.exists_top_reads_lt_markedTop_of_isolated` needs an isolated cell `r` of the grade `4`
in a coatom of the profile layer.  This file carries such a cell from the left coatom type of a seed
(`TowerProfile.isolated_of_left`): a cell of the left type of graded index `(univ, 4)`, the only one
there, whose row reads every other cell below it as `⊥` and itself not as `⊥`, is isolated in the
profile layer below the coatom `(univ.erase (Fin.last 4), 4)`.  The apex added to a type labelled
`⊥` is such a cell (`StageType.rowAt_addApex_last_of_ne`, `StageType.rowAt_addApex_last_last`,
`StageType.eq_last_of_gradedIndex_addApex`), and such a type is a marked-cap context along every
embedding of `n'` points with `n' + 1 < n`, with the apex as top cap and marker
(`StageType.isMarkedCapContext_addApex`, in `Continuation/MarkedCap.lean`); for
`TwoFaceLiftExistsCounterexample.TL`, `TowerProfile.isMarkedCapContext_TL` (embeddings of at most
two points).

* **The obstruction over `TL`** (`TowerProfile.exists_top_reads_lt_markedTop_TL`, compiled in this
  repository (theorem named)): for every seed with left coatom type `TL` and any legal right coatom
  type over the face of `T5`, every marked specification, every lawful section of the marked top
  labelling the apex of `TL` with `⊤`, and every cell `x` of grade at most `3`, some new cell of
  graded index `(univ, 4)` labelled `⊤` has an entry reading `x` strictly below the apex.  At
  `seedLL`: `TowerProfile.exists_top_reads_lt_markedTop_seedLL`.
* **A right coatom type with a new top** (`TopReadingApexExample.rightType`): the scheme `S` of
  `CaseSplitCounterexample` labelled `⊤` at its live cells of grade at most `2`, with the apex
  added; legal, with the face of `T5` (its labels on `{0, 1, 2}` are `⊥`,
  `StageType.restrictFace_congr_label`), and `⊤` at its cell `{3}`.
* **A reading obstruction for the completion family at `seedTR`**
  (`TowerProfile.exists_top_reads_lt_markedCompletion_seedTR`, compiled in this repository (theorem
  named)): in the seed `seedTR α` of `TL` and `rightType α`, for every marked specification `D`,
  the leaf-and-marked completion labels `⊤` a cell `x` of grade `1` on the new point (the image of
  `{3}`), and labels `⊤` some new cell of graded index `(univ, 4)` whose entry reads `x` strictly
  below the apex of `TL`.  So no leaf-and-marked completion over `seedTR` (any marked subset, any
  cap) reads the new top `x` at least as the apex of `TL` through its labelling.  For the reading
  specification (`TowerProfile.MarkedSpec.reading` with `x` among the read cells) the cell reading
  `x` below the apex is a leaf (argued, not formalized: its entry is not a reading mark).

**Scope.**  `seedTR` is not a marked-cap donor input: the full donor `rightType α` lies over the
common face on three points, a root of size `n = 3`, while the top cap of `TL` has grade `N = 4`,
so the bound `n + 1 < N` of `StageType.IsMarkedCapContext` fails (`TL` is a marked-cap context only
along embeddings of at most two points).  The result is a reading obstruction for the
leaf-and-marked completion family at this seed, through the labelling of
`TowerProfile.markedCompletion`.  It
refutes no universal carrier statement: neither `StageType.HasTopReadingCarriers`, nor top-marked
carriers, nor (R3).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TopReadingApexExample

open CaseSplitCounterexample TwoFaceLiftExistsCounterexample

/-- The labels `labelling ⊤ ⊤ ⊥` of the type `S` of `CaseSplitCounterexample` are at the stage. -/
private theorem atStage_labelling (α : Ordinal.{u}) (d : Fin 19) :
    AtStage α (CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ d) := by
  unfold CaseSplitCounterexample.labelling
  split_ifs <;> simp

/-- The type `S` of `CaseSplitCounterexample` labelled `⊤` at its live cells of grade at most `2`
and `⊥` elsewhere. -/
noncomputable def rightBase (α : Ordinal.{u}) : StageType.{u} α 4 where
  toScheme := S
  label := CaseSplitCounterexample.labelling ⊤ ⊤ ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_labelling (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_bot 3)
    bot_le bot_le
  atStage := atStage_labelling α

/-- **The right coatom type**: `rightBase` with the apex added. -/
noncomputable def rightType (α : Ordinal.{u}) : StageType.{u} α 4 :=
  (rightBase α).addApex isLegalBelowFullGrade_S (by omega)

/-- The right coatom type is legal. -/
theorem isLegal_rightType (α : Ordinal.{u}) : (rightType α).IsLegal :=
  StageType.isLegal_addApex _ _

/-- The cells of `S` off the point `3` are labelled `⊥` by `labelling ⊤ ⊤ ⊥`. -/
private theorem labelling_eq_bot_of_notMem (d : Fin 19)
    (hd : (3 : Fin 4) ∉ TwoFaceLiftCounterexample.cellScope d) :
    CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ d = ⊥ := by
  have key : ∀ d : Fin 19, (3 : Fin 4) ∉ TwoFaceLiftCounterexample.cellScope d →
      CaseSplitCounterexample.live d = false ∨ TwoFaceLiftCounterexample.cellGrade d = 3 := by
    decide
  unfold CaseSplitCounterexample.labelling
  rcases key d hd with h | h
  · simp [h]
  · simp [h]

/-- **The right coatom type has the face of `T5`**: on the face `{0, 1, 2}` its labels are `⊥`. -/
theorem restrictFace_rightType (α : Ordinal.{u}) :
    StageType.restrictFace (Coatom.face 3) (rightType α) = some (faceT5 α) := by
  have hne : univ.map (Coatom.face 3) ≠ (univ : Finset (Fin 4)) := by decide
  rw [rightType, StageType.restrictFace_addApex (t := rightBase α) isLegalBelowFullGrade_S
    (by omega) (Coatom.face 3) hne, ← restrictFace_T5, T5,
    StageType.restrictFace_addApex (t := T5₀ α) isLegalBelowFullGrade_S (by omega) (Coatom.face 3)
      hne]
  refine StageType.restrictFace_congr_label rfl fun i j hij hi ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  -- `T5₀` is labelled `⊥`; a visible cell avoids the point `3`
  change CaseSplitCounterexample.labelling ⊤ ⊤ ⊥ i = ⊥
  refine labelling_eq_bot_of_notMem i fun h3 ↦ ?_
  obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hi (mem_coe.mpr h3)
  exact (Fin.castSucc_lt_last y).ne hy

/-- The seed of `TL` and the right coatom type. -/
noncomputable def seedTR (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_TL α) (isLegal_rightType α) (restrictFace_TL α)
    (restrictFace_rightType α)

end TopReadingApexExample

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-! ### The obstruction at `seedLL` -/

open TwoFaceLiftExistsCounterexample in
/-- **`TL` is a marked-cap context with its apex as top cap and marker**, along every embedding of
at most two points. -/
theorem isMarkedCapContext_TL (α : Ordinal.{u}) {n' : ℕ} (h : Fin n' ↪ Fin 4) (hn' : n' ≤ 2) :
    (TL α).IsTopCap (Fin.last _) ∧ (TL α).IsMarker (Fin.last _) (Fin.last _) ∧
      (TL α).IsMarkedCapContext h :=
  StageType.isMarkedCapContext_addApex (t := TL₀ α) isLegalBelowFullGrade_SL (by omega)
    (fun _ ↦ rfl) h (by omega)

open TwoFaceLiftExistsCounterexample in
/-- **The obstruction over `TL`.**  For every seed whose left coatom type is `TL` (over the face
`CaseSplitCounterexample.faceT5`, with any legal right coatom type `tb`), every marked
specification `D`, every lawful section `q` of the marked top labelling the apex of `TL` with `⊤`,
and every cell `x` of the profile layer of grade at most `3`, some new cell labelled `⊤` has an
entry reading `x` strictly below the apex. -/
theorem exists_top_reads_lt_markedTop_TL {α : Ordinal.{u}} {tb : StageType.{u} α 4}
    (hlb : tb.IsLegal)
    (hpb : StageType.restrictFace (Coatom.face 3) tb = some (CaseSplitCounterexample.faceT5 α))
    (D : MarkedSpec (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb))
    {q : Fin (markedTop _ D).card → Label.{u}} (hq : (markedTop _ D).rows.IsLawful q)
    (hqr : q (Fin.castAdd _ (leftCell _ (Fin.last _))) = ⊤)
    {x : Fin (scheme (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)).card}
    (hgx : (scheme (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)).toCellScheme.grade
      x ≤ 3) :
    ∃ j, q (Fin.natAdd _ j) = ⊤ ∧
      (scheme _).markedEntry 4 D.marks j x <
        (scheme _).markedEntry 4 D.marks j (leftCell _ (Fin.last _)) := by
  obtain ⟨hg, hrC, huniq, hrow, hrr⟩ := isolated_of_left
    (I := Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb) (a := Fin.last _)
    (StageType.addApex_gradedIndex_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))
    (fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := TL₀ α) isLegalBelowFullGrade_SL
      (by omega) hz)
    (fun _ hz ↦ StageType.rowAt_addApex_last_of_ne (t := TL₀ α) isLegalBelowFullGrade_SL
      (by omega) (fun _ ↦ rfl) hz)
    (StageType.rowAt_addApex_last_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))
  exact exists_top_reads_lt_markedTop_of_isolated D hq hg hgx hqr (z₁ := Fin.last 4)
    (z₂ := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hrC huniq hrow hrr

open TwoFaceLiftExistsCounterexample in
/-- **The obstruction at `seedLL`.**  For every marked specification `D` of `seedLL α`, every lawful
section `q` of the marked top labelling the apex of the left coatom type `TL` with `⊤`, and every
cell `x` of the profile layer of grade at most `3`, some new cell labelled `⊤` has an entry reading
`x` strictly below the apex. -/
theorem exists_top_reads_lt_markedTop_seedLL {α : Ordinal.{u}} (D : MarkedSpec (seedLL α))
    {q : Fin (markedTop (seedLL α) D).card → Label.{u}}
    (hq : (markedTop (seedLL α) D).rows.IsLawful q)
    (hqr : q (Fin.castAdd _ (leftCell (seedLL α) (Fin.last _))) = ⊤)
    {x : Fin (scheme (seedLL α)).card} (hgx : (scheme (seedLL α)).toCellScheme.grade x ≤ 3) :
    ∃ j, q (Fin.natAdd _ j) = ⊤ ∧
      (scheme (seedLL α)).markedEntry 4 D.marks j x <
        (scheme (seedLL α)).markedEntry 4 D.marks j (leftCell (seedLL α) (Fin.last _)) :=
  exists_top_reads_lt_markedTop_TL (isLegal_TL α) (restrictFace_TL α) D hq hqr hgx

open TwoFaceLiftExistsCounterexample in
/-- **The leaf-and-marked completion of `seedLL` has a top reading every low cell below the
marker**: its labelling extends the glued labels, so it labels the apex of `TL` with `⊤`, and
`exists_top_reads_lt_markedTop_seedLL` applies. -/
theorem exists_top_reads_lt_markedCompletion_seedLL {α : Ordinal.{u}} (D : MarkedSpec (seedLL α))
    {x : Fin (scheme (seedLL α)).card} (hgx : (scheme (seedLL α)).toCellScheme.grade x ≤ 3) :
    ∃ j, (markedCompletion (seedLL α) D).label (Fin.natAdd _ j) = ⊤ ∧
      (scheme (seedLL α)).markedEntry 4 D.marks j x <
        (scheme (seedLL α)).markedEntry 4 D.marks j (leftCell (seedLL α) (Fin.last _)) := by
  refine exists_top_reads_lt_markedTop_seedLL D (markedCompletion (seedLL α) D).isLawful ?_ hgx
  have h := (markedCompletion (seedLL α) D).label_embed
    (StageType.faceCell (seedLL α).restrictFace_left (Fin.last _))
  exact h.trans ((StageType.label_faceCell (seedLL α).restrictFace_left (Fin.last _)).trans
    (StageType.addApex_label_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega)))

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- **A reading obstruction for the completion family at `seedTR`.**  In the seed `seedTR α` (left
coatom `TL`, right coatom `rightType α`), for every marked specification `D`, the leaf-and-marked
completion labels `⊤` a cell `x` of grade `1` whose scope is the new point `4` (the cell `{3}` of
the right type), and labels `⊤` some new cell of graded index `(univ, 4)` whose entry reads `x`
strictly below the apex of `TL`.  This is not a marked-cap donor input (the donor's root has three
points and the cap of `TL` grade `4`, so `n + 1 < N` fails); it bears on the completion family
only, not on carriers in general or on (R3). -/
theorem exists_top_reads_lt_markedCompletion_seedTR {α : Ordinal.{u}} (D : MarkedSpec (seedTR α)) :
    ∃ x : Fin (scheme (seedTR α)).card, (scheme (seedTR α)).toCellScheme.grade x = 1 ∧
      Fin.last 4 ∈ (scheme (seedTR α)).toCellScheme.scope x ∧
      (markedCompletion (seedTR α) D).label (Fin.castAdd _ x) = ⊤ ∧
      ∃ j, (markedCompletion (seedTR α) D).label (Fin.natAdd _ j) = ⊤ ∧
        (scheme (seedTR α)).markedEntry 4 D.marks j x <
          (scheme (seedTR α)).markedEntry 4 D.marks j (leftCell (seedTR α) (Fin.last _)) := by
  let z₀ : Fin CaseSplitCounterexample.S.{u}.card := ⟨3, by decide⟩
  let z : Fin (seedTR α).right.card := Fin.castSucc z₀
  let x := embed3 (seedTR α) (StageType.faceCell (seedTR α).restrictFace_right z)
  have hgz : (seedTR α).right.toCellScheme.grade z = 1 := by
    -- the right type is `appendFullCell` over `S`
    change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).grade (Fin.castSucc z₀) = 1
    rw [Scheme.appendFullCellScheme_grade_castSucc]
    rfl
  have hgx : (scheme (seedTR α)).toCellScheme.grade x = 1 := by
    have h2 := congrArg Prod.snd (gradedIndex_embed3 (I := seedTR α)
      (StageType.faceCell (seedTR α).restrictFace_right z))
    simp only [CellScheme.gradedIndex_snd] at h2
    rw [h2, StageType.grade_faceCell]
    exact hgz
  have hlz : (seedTR α).right.label z = ⊤ := by
    -- the right type is `rightBase` with the apex added
    change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]
  refine ⟨x, hgx, ?_, ?_, ?_⟩
  · change Fin.last 4 ∈ (scheme (seedTR α)).toCellScheme.scope
      (embed3 (seedTR α) (StageType.faceCell (seedTR α).restrictFace_right z))
    rw [scope_embed3, StageType.scope_faceCell]
    -- the scope of `z` is `{3}`, sent to `{4}` by the second coatom
    change Fin.last 4 ∈ ((Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).scope
      (Fin.castSucc z₀)).map (Coatom.right 3)
    rw [Scheme.appendFullCellScheme_scope_castSucc]
    decide
  · exact ((markedCompletion (seedTR α) D).label_embed _).trans
      ((StageType.label_faceCell _ z).trans hlz)
  · refine exists_top_reads_lt_markedTop_TL (isLegal_rightType α) (restrictFace_rightType α) D
      (markedCompletion (seedTR α) D).isLawful ?_ (hgx.trans_le (by omega))
    have h := (markedCompletion (seedTR α) D).label_embed
      (StageType.faceCell (seedTR α).restrictFace_left (Fin.last _))
    exact h.trans ((StageType.label_faceCell (seedTR α).restrictFace_left (Fin.last _)).trans
      (StageType.addApex_label_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega)))

end TowerProfile

end VaughtConjecture
