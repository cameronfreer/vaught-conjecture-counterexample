/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
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
(`StageType.isMarkedCapContext_addApex`); for `TwoFaceLiftExistsCounterexample.TL`,
`TowerProfile.isMarkedCapContext_TL` (embeddings of at most two points).

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
* **The obstruction at a marked-cap context with a new top**
  (`TowerProfile.exists_top_reads_lt_markedCompletion_seedTR`, compiled in this repository (theorem
  named)): in the seed `seedTR α` of `TL` and `rightType α`, for every marked specification `D`,
  the leaf-and-marked completion labels `⊤` a cell `x` of grade `1` on the new point (the image of
  `{3}`), and labels `⊤` some new cell of graded index `(univ, 4)` whose entry reads `x` strictly
  below the apex of `TL`, the marker.  So no leaf-and-marked completion over `seedTR` (any marked
  subset, any cap) carries the top reading of the new top `x` against the marker through its
  labelling.  For the reading specification (`TowerProfile.MarkedSpec.reading` with `x` among the
  read cells) the cell reading `x` below the marker is a leaf (argued, not formalized: its entry is
  not a reading mark).

This refutes the leaf-and-marked family at this context, through the labelling of
`TowerProfile.markedCompletion`; it does not refute `StageType.HasTopReadingCarriers`, which
quantifies over all legal carriers (argued, not formalized: a carrier outside the family may avoid
the separating raise).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Rows of a face -/

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} {D : StageType.{u} α n} {f : Fin m ↪ Fin n}
  {t : StageType.{u} α m}

/-- **The rows of a face are the rows of its cells.** -/
theorem rowAt_faceCell (h : restrictFace f D = some t) (i j : Fin t.card) :
    D.toScheme.rowAt (faceCell h i) (faceCell h j) = t.toScheme.rowAt i j := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff D f).mp h
  have hmem : faceCell h j ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex (faceCell h i)) ↔
      j ∈ (D.comap f hf).toCellScheme.below ((D.comap f hf).toCellScheme.gradedIndex i) := by
    rw [CellScheme.mem_below, CellScheme.mem_below]
    simp only [CellScheme.gradedIndex, Prod.mk_le_mk, scope_faceCell, grade_faceCell,
      map_subset_map]
  by_cases hj : j ∈ (D.comap f hf).toCellScheme.below ((D.comap f hf).toCellScheme.gradedIndex i)
  · rw [Scheme.rowAt_of_mem (hmem.mpr hj), Scheme.rowAt_of_mem hj]
    rfl
  · rw [Scheme.rowAt_of_notMem (fun h' ↦ hj (hmem.mp h')), Scheme.rowAt_of_notMem hj]

/-- **Faces depend on the labels of the visible cells only**: two stage types on one scheme whose
labels agree at the cells visible through `f` have the same face along `f`. -/
theorem restrictFace_congr_label {t s : StageType.{u} α n} (hS : t.toScheme = s.toScheme)
    (hl : ∀ (i : Fin t.card) (j : Fin s.card), (i : ℕ) = j → i ∈ t.toScheme.visibleCells f →
      t.label i = s.label j) :
    restrictFace f t = restrictFace f s := by
  obtain ⟨S, p, _, _, _, _⟩ := t
  obtain ⟨S', p', _, _, _, _⟩ := s
  obtain rfl : S = S' := hS
  by_cases hf : univ.map f ∈ S.toCellScheme.faces
  · rw [restrictFace_of_mem _ f hf, restrictFace_of_mem _ f hf]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    simp only [comap_label]
    obtain rfl : i = j := Fin.ext hij
    exact hl _ _ rfl (S.cellMap_mem f i)
  · rw [restrictFace_of_notMem _ f hf, restrictFace_of_notMem _ f hf]

/-! ### The apex of a type labelled `⊥` -/

section Apex

variable {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade) (hn : 0 < n)

/-- The apex has graded index `(univ, n)`. -/
theorem addApex_gradedIndex_last :
    (t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _) = (univ, n) :=
  Scheme.appendFullCellScheme_gradedIndex_last _ _

/-- The apex is the only cell of graded index `(univ, n)`. -/
theorem eq_last_of_gradedIndex_addApex {z : Fin (t.addApex ht hn).card}
    (hz : (t.addApex ht hn).toCellScheme.gradedIndex z = (univ, n)) : z = Fin.last _ :=
  eq_of_grade_addApex ht hn (congrArg Prod.snd hz)

/-- **The apex row of a type labelled `⊥` reads every other cell as `⊥`.** -/
theorem rowAt_addApex_last_of_ne (hbot : ∀ d, t.label d = ⊥) {z : Fin (t.addApex ht hn).card}
    (hz : z ≠ Fin.last _) : (t.addApex ht hn).toScheme.rowAt (Fin.last _) z = ⊥ := by
  -- `t.addApex` has the cells of `t` and the apex
  change Fin (t.card + 1) at z
  induction z using Fin.lastCases with
  | last => exact absurd rfl hz
  | cast d =>
    by_cases hd : d.castSucc ∈ (t.addApex ht hn).toCellScheme.below
        ((t.addApex ht hn).toCellScheme.gradedIndex (Fin.last _))
    · rw [Scheme.rowAt_of_mem hd]
      -- the rows of `t.addApex` are those of `appendFullCell`
      change (t.toScheme.appendFullCell n (apexRow ht) ht.not_le).rows.row (Fin.last _)
        ⟨d.castSucc, hd⟩ = ⊥
      rw [Scheme.appendFullCell_row_last, apexRow_castSucc, hbot d]
      rfl
    · exact Scheme.rowAt_of_notMem hd

/-- **The apex row reads the apex not as `⊥`.** -/
theorem rowAt_addApex_last_last :
    (t.addApex ht hn).toScheme.rowAt (Fin.last _) (Fin.last _) ≠ ⊥ := by
  rw [Scheme.rowAt_of_mem (S := (t.addApex ht hn).toScheme) (u := Fin.last _) (x := Fin.last _)
    ((t.addApex ht hn).toCellScheme.mem_below_gradedIndex _)]
  -- the rows of `t.addApex` are those of `appendFullCell`
  change (t.toScheme.appendFullCell n (apexRow ht) ht.not_le).rows.row (Fin.last _)
    ⟨Fin.last _, _⟩ ≠ ⊥
  rw [Scheme.appendFullCell_row_last, apexRow_last, blockEncode_top]
  exact WithBot.coe_ne_bot

/-- **The apex of a type labelled `⊥` is a top cap and its own marker, and the type is a marked-cap
context along every embedding of `n'` points with `n' + 1 < n`.** -/
theorem isMarkedCapContext_addApex (hbot : ∀ d, t.label d = ⊥) {n' : ℕ} (h : Fin n' ↪ Fin n)
    (hn' : n' + 1 < n) :
    (t.addApex ht hn).IsTopCap (Fin.last _) ∧ (t.addApex ht hn).IsMarker (Fin.last _) (Fin.last _) ∧
      (t.addApex ht hn).IsMarkedCapContext h := by
  have hlab (x : Fin (t.addApex ht hn).card) (hx : (t.addApex ht hn).label x = ⊤) :
      x = Fin.last _ := by
    -- `t.addApex` has the cells of `t` and the apex
    change Fin (t.card + 1) at x
    induction x using Fin.lastCases with
    | last => rfl
    | cast d =>
      rw [addApex_label_castSucc, hbot d] at hx
      exact absurd hx bot_ne_top
  have hg : (t.addApex ht hn).toCellScheme.grade (Fin.last _) = n :=
    congrArg Prod.snd (addApex_gradedIndex_last ht hn)
  have hc : (t.addApex ht hn).IsTopCap (Fin.last _) :=
    ⟨addApex_scope_last ht hn, addApex_label_last ht hn, fun x _ ↦ by
      rw [hg]
      exact (t.addApex ht hn).grade_le x⟩
  have hr : (t.addApex ht hn).IsMarker (Fin.last _) (Fin.last _) :=
    ⟨addApex_label_last ht hn, (t.addApex ht hn).toCellScheme.mem_below_gradedIndex _,
      fun x hx _ ↦ by rw [hlab x hx]⟩
  refine ⟨hc, hr, ⟨_, _, hc, hr, by rw [hg]; exact hn', fun a ha hat ↦ ?_⟩⟩
  -- the only cell labelled `⊤` is the apex, of full scope, not visible through `n' < n` points
  obtain rfl := hlab a hat
  exfalso
  have hsurj : Function.Surjective h := fun y ↦ by
    have := Scheme.mem_visibleCells.mp ha
    rw [addApex_scope_last] at this
    exact this (mem_coe.mpr (mem_univ y))
  have := Fintype.card_le_of_surjective _ hsurj
  simp only [Fintype.card_fin] at this
  omega

end Apex

end StageType

/-! ### A right coatom type with a new top -/

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

/-! ### An isolated cell carried from the left coatom -/

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The rows of the profile layer at old cells are those of the amalgam. -/
theorem rowAt_embed3 (a b : Fin I.amalgam.card) :
    (scheme I).rowAt (embed3 I a) (embed3 I b) = I.amalgam.toScheme.rowAt a b := by
  have hmem : embed3 I b ∈ (scheme I).toCellScheme.below
      ((scheme I).toCellScheme.gradedIndex (embed3 I a)) ↔
      b ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex a) := by
    rw [CellScheme.mem_below, CellScheme.mem_below, gradedIndex_embed3, gradedIndex_embed3]
  by_cases hb : b ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex a)
  · rw [Scheme.rowAt_of_mem (hmem.mpr hb), Scheme.rowAt_of_mem hb]
    have h := congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row a ⟨b, hb⟩)
      (comap_rows_embed3 (I := I))
    exact h
  · rw [Scheme.rowAt_of_notMem (fun h' ↦ hb (hmem.mp h')), Scheme.rowAt_of_notMem hb]

/-- The first coatom of `Fin 5` is the ground set without the last point. -/
theorem univ_map_left_eq :
    (univ : Finset (Fin 4)).map (Coatom.left 3) = univ.erase (Fin.last 4) := by
  decide

variable (I) in
/-- The cell of the profile layer at a cell of the left coatom type. -/
noncomputable def leftCell (a : Fin I.left.card) : Fin (scheme I).card :=
  embed3 I (StageType.faceCell I.restrictFace_left a)

/-- A cell of the profile layer avoiding the last point is the cell of a cell of the left type. -/
theorem exists_leftCell_eq {y : Fin (scheme I).card}
    (hy : Fin.last 4 ∉ (scheme I).toCellScheme.scope y) : ∃ z, leftCell I z = y := by
  obtain ⟨d, rfl⟩ := mem_range_embed3 y fun h ↦ hy (h ▸ mem_univ _)
  have hd : Fin.last 4 ∉ I.amalgam.toCellScheme.scope d := by
    rwa [scope_embed3] at hy
  obtain ⟨z, rfl⟩ := StageType.exists_faceCell_eq_of_last_notMem I.restrictFace_left hd
  exact ⟨z, rfl⟩

/-- The graded index of the cell of a cell of the left type. -/
theorem gradedIndex_leftCell (z : Fin I.left.card) :
    (scheme I).toCellScheme.gradedIndex (leftCell I z) =
      ((I.left.toCellScheme.scope z).map (Coatom.left 3), I.left.toCellScheme.grade z) := by
  rw [leftCell, gradedIndex_embed3]
  exact Prod.ext (StageType.scope_faceCell _ z) (StageType.grade_faceCell _ z)

/-- The rows of the profile layer at the cells of the left type are those of the left type. -/
theorem rowAt_leftCell (a z : Fin I.left.card) :
    (scheme I).rowAt (leftCell I a) (leftCell I z) = I.left.toScheme.rowAt a z := by
  rw [leftCell, leftCell, rowAt_embed3, StageType.rowAt_faceCell]

/-- The cells of the left type map injectively. -/
theorem leftCell_injective : Function.Injective (leftCell I) := fun _ _ h ↦
  Scheme.faceCell_injective _ ((embed3 I).injective h)

/-- **An isolated cell of the left type is isolated in the profile layer** below the coatom
`(univ.erase (Fin.last 4), 4)`: a cell `a` of the left type of graded index `(univ, 4)`, the only
one there, whose row reads every other cell as `⊥` and itself not as `⊥`. -/
theorem isolated_of_left {a : Fin I.left.card}
    (ha : I.left.toCellScheme.gradedIndex a = (univ, 4))
    (hu : ∀ z, I.left.toCellScheme.gradedIndex z = (univ, 4) → z = a)
    (hrow : ∀ z, z ≠ a → I.left.toScheme.rowAt a z = ⊥) (hrr : I.left.toScheme.rowAt a a ≠ ⊥) :
    (scheme I).toCellScheme.grade (leftCell I a) = 4 ∧
      leftCell I a ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) ∧
      (∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.gradedIndex (leftCell I a) ≤
          (scheme I).toCellScheme.gradedIndex y → y = leftCell I a) ∧
      (∀ y (hy : y ∈ (scheme I).toCellScheme.below
          ((scheme I).toCellScheme.gradedIndex (leftCell I a))),
        y ≠ leftCell I a → (scheme I).rows.row (leftCell I a) ⟨y, hy⟩ = ⊥) ∧
      (scheme I).rows.row (leftCell I a)
        ⟨leftCell I a, (scheme I).toCellScheme.mem_below_gradedIndex _⟩ ≠ ⊥ := by
  have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst ha
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hgi : (scheme I).toCellScheme.gradedIndex (leftCell I a) = (univ.erase (Fin.last 4), 4) := by
    rw [gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
  -- a cell below the coatom avoids the last point, so it is a cell of the left type
  have hleft {y : Fin (scheme I).card}
      (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) :
      ∃ z, leftCell I z = y :=
    exists_leftCell_eq fun h ↦ by simpa using hy.1 h
  refine ⟨congrArg Prod.snd hgi, by rw [CellScheme.mem_below, hgi], fun y hy hle ↦ ?_,
    fun y hy hne ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := hleft hy
    have heq : (scheme I).toCellScheme.gradedIndex (leftCell I z) = (univ.erase (Fin.last 4), 4) :=
      le_antisymm hy (hgi ▸ hle)
    rw [gradedIndex_leftCell, ← univ_map_left_eq] at heq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
    rw [map_inj] at h1
    exact congrArg (leftCell I) (hu z (Prod.ext h1 h2))
  · rw [hgi] at hy
    obtain ⟨z, rfl⟩ := hleft hy
    rw [← Scheme.rowAt_of_mem, rowAt_leftCell]
    exact hrow z fun h ↦ hne (h ▸ rfl)
  · rw [← Scheme.rowAt_of_mem, rowAt_leftCell]
    exact hrr

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
/-- **The obstruction at a marked-cap context with a new top.**  In the seed `seedTR α` (left
coatom `TL`, a marked-cap context along every embedding of at most two points with its apex as top
cap and marker, `isMarkedCapContext_TL`; right coatom `rightType α`), for every marked
specification `D`, the leaf-and-marked completion labels `⊤` a cell `x` of grade `1` whose scope is
the new point `4` (the cell `{3}` of the right type), and labels `⊤` some new cell of graded index
`(univ, 4)` whose entry reads `x` strictly below the apex of `TL`. -/
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
