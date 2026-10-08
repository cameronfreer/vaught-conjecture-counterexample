/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerDetermination

/-!
# The reading layer at several new tops

Roadmap, Layer 3 ((R3) of the table of 3.4).

The restricted reading layer reading every cell of a set `Z` of new tops of the right coatom type
at least as the marker, and the clause of hollow coatom cutoff determination at `oneType` and
`rightType` at every root.

* **Legality at several new tops** (`TowerProfile.isLegalBelowFullGrade_readingTop_of_rightNewTops`,
  compiled): at a seed on five points whose left coatom type has a tie-keeping marker
  (`TowerProfile.LeftTie`) and whose right coatom type has a set `Z` of new tops through the point
  `3`, labelled `⊤`, below one of grade `1` (`TowerProfile.RightNewTops`), the reading layer
  reading every new top at least as the marker is legal below the full grade.  The fill from the
  left coatom reads a server at the largest new top `x₀`; the server reads every new top below
  `x₀` at least as `x₀` (`TowerProfile.rowAt_le_rowAt_of_raise`), so the fill is `⊤` at all of
  them.
* **At `seedOne`** (`TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedOne_two`,
  `TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedOne_oneTwo`, compiled): at the new
  tops `{3}`, `{2, 3}` and `{3}`, `{2, 3}`, `{1, 2, 3}` of `rightType`.
* **The carrier at a set of new tops** (`TopReadingApexExample.carrierOf`, defined here;
  `TopReadingApexExample.isTopReadingCarrier_carrierOf`, compiled): a top-reading carrier for every
  donor of `rightType` whose new tops labelled `⊤` lie in the set.
* **Every root** (`TopReadingApexExample.exists_coface_oneType_rightType`, compiled; feasibility at
  the context `oneType` and the coface `rightType`): for every root `g` along which `oneType` is an
  acquired context respecting the root bottoms (`TiedRootCapRelabel.MarkedCapContextBelow'`) and
  every donor `d` of `rightType` along `extendByLast g`, the carrier at the new tops of `rightType`
  inside the point set of the root determines `d` at a permitted cutoff.  `oneType` is acquired
  along exactly the roots of at most two points
  (`TopReadingApexExample.markedCapContextBelow'_oneType_of`,
  `TopReadingApexExample.not_markedCapContextBelow'_oneType_of`); donors exist along `{2}` and
  `{1, 2}` (`TopReadingApexExample.hollowCoatomCutoffDetermination_rootTwo`,
  `TopReadingApexExample.hollowCoatomCutoffDetermination_rootOneTwo`).
* **Every seed with a tie-keeping marker and new tops** (`TowerProfile.exists_coface_of_leftTie`,
  `TowerProfile.exists_coface_of_coatoms`, compiled under the hypotheses named): the same carrier
  over any seed on five points whose left coatom type has a tie-keeping marker
  (`TowerProfile.LeftTie`) and whose right coatom type has new tops `Z`
  (`TowerProfile.RightNewTops`), for every root of at most two points and every donor whose new
  tops labelled `⊤` lie in `Z`.
* **Every acquired apex context** (`TowerProfile.exists_coface_of_addApex`, compiled under the
  hypotheses named): at `t₀.addApex` with the conditions of
  `StageType.markedCapContextBelow'_addApex` along a root `ι`, the common face labelled `⊥`, and
  the tie shape (`htie`, `htwo`, `hthree`, `hlab`); the uniqueness of the apex, its grade and the
  root bottoms are those of the apex row.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Faces along composites -/

namespace StageType

variable {α : Ordinal.{u}} {n m k : ℕ}

/-- The cells of a face along equal embeddings agree. -/
theorem faceCell_congr {t : StageType.{u} α n} {f f' : Fin m ↪ Fin n} (hff : f = f')
    {s : StageType.{u} α m} (h : restrictFace f t = some s) (h' : restrictFace f' t = some s)
    (i : Fin s.card) : faceCell h i = faceCell h' i := by
  subst hff
  rfl

/-- **The cells of a face of a face**: the cell of `t` at a cell of its face along `g.trans f` is
the cell at the cell of the face along `g` of the face along `f`. -/
theorem faceCell_trans {t : StageType.{u} α n} {f : Fin m ↪ Fin n} {u : StageType.{u} α m}
    {g : Fin k ↪ Fin m} {v : StageType.{u} α k} (hu : restrictFace f t = some u)
    (hv : restrictFace g u = some v) (h : restrictFace (g.trans f) t = some v) (i : Fin v.card) :
    faceCell h i = faceCell hu (faceCell hv i) := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  obtain ⟨hg, rfl⟩ := (restrictFace_eq_some_iff _ g).mp hv
  exact (Scheme.cellMap_cellMap _ _ (i := Fin.cast rfl i) rfl).symm

end StageType

namespace TowerProfile

open TopReadingApexExample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The new tops: the cells of a set `Z` of cells of the right coatom type, in the profile layer. -/
noncomputable abbrev newTopsOf (I : Seed.{u} α 3) (Z : Finset (Fin I.right.card)) :
    Finset (Fin (scheme I).card) :=
  Z.image fun z ↦ embed3 I (StageType.faceCell I.restrictFace_right z)

/-- **A right coatom type with a set of new tops** `Z` below a cell `x₀`: its rows raise at the
point `3` (`StageType.RowsRaiseAt`), every cell of `Z` lies through `3`, is labelled `⊤`, and lies
below `x₀ ∈ Z`, a cell of grade `1`. -/
structure RightNewTops (tb : StageType.{u} α 4) (Z : Finset (Fin tb.card)) (x₀ : Fin tb.card) :
    Prop where
  rowsRaiseAt : tb.RowsRaiseAt 3
  mem : x₀ ∈ Z
  mem_scope : ∀ z ∈ Z, (3 : Fin 4) ∈ tb.toCellScheme.scope z
  grade_eq : tb.toCellScheme.grade x₀ = 1
  label_eq : ∀ z ∈ Z, tb.label z = ⊤
  le : ∀ z ∈ Z, tb.toCellScheme.gradedIndex z ≤ tb.toCellScheme.gradedIndex x₀

/-- One new top is a set of new tops. -/
theorem RightNewTop.rightNewTops {tb : StageType.{u} α 4} {x₀ : Fin tb.card}
    (hR : RightNewTop tb x₀) : RightNewTops tb {x₀} x₀ where
  rowsRaiseAt := hR.rowsRaiseAt
  mem := mem_singleton_self _
  mem_scope z hz := by rw [mem_singleton.mp hz]; exact hR.mem_scope
  grade_eq := hR.grade_eq
  label_eq z hz := by rw [mem_singleton.mp hz]; exact hR.label_eq
  le z hz := by rw [mem_singleton.mp hz]

/-- The new tops of the profile layer have grade at most `1`. -/
theorem grade_le_one_of_rightNewTops {Z : Finset (Fin I.right.card)} {x₀ : Fin I.right.card}
    (hR : RightNewTops I.right Z x₀) {x : Fin (scheme I).card} (hx : x ∈ newTopsOf I Z) :
    (scheme I).toCellScheme.grade x ≤ 1 := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
  rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd,
    StageType.grade_faceCell]
  exact (Prod.mk_le_mk.mp (hR.le z hz)).2.trans_eq hR.grade_eq

/-- **The fill at the short positive caps from the left coatom at several new tops**
(`TowerProfile.readingFillPos_left_of_rowTie`, the server read at the largest new top `x₀`). -/
theorem readingFillPos_left_of_rightNewTops {a z₁ z₂ : Fin I.left.card} {n : ℕ}
    {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {Z : Finset (Fin I.right.card)}
    {x₀ : Fin I.right.card} (hR : RightNewTops I.right Z x₀) :
    ReadingFillPos I (leftCell I a) (newTopsOf I Z) (Fin.last 4) := by
  obtain ⟨hgr, hrC, -⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hfr0 {f : Fin (scheme I).card → Label.{u}}
      (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
      (hfr : f (leftCell I a) ≠ ⊥) (z : Fin I.left.card) (hz : I.left.label z = ⊥) :
      f (leftCell I z) = ⊥ := by
    refine eq_bot_of_row_eq_bot hrC hf hfr (mem_below_marker hgr hrC (leftCell_mem z)) ?_
    rw [← Scheme.rowAt_of_mem, rowAt_leftCell]
    exact hL.rowAt_apex z hz
  have hcell {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) :
      ∃ z, leftCell I z = d :=
    exists_leftCell_eq (I := I) (TopReadingApexExample.last_notMem_of_subset
      ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd)).1)
  have hbelowApex (z : Fin I.left.card) : leftCell I z ∈ (scheme I).toCellScheme.below
      ((scheme I).toCellScheme.gradedIndex (leftCell I a)) := by
    have h := leftCell_mem (I := I) z
    rw [CellScheme.mem_below] at h ⊢
    have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst hL.gradedIndex_apex
    have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd hL.gradedIndex_apex
    rw [gradedIndex_leftCell, gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
    rw [gradedIndex_leftCell] at h
    exact h
  have hP (z : Fin I.right.card) (hz : z ∈ Z) : Fin.last 4 ∈ I.amalgam.toCellScheme.scope
      (StageType.faceCell I.restrictFace_right z) :=
    (last_mem_scope_right I.restrictFace_right z).mpr (hR.mem_scope z hz)
  refine readingFillPos_left_of_rowTie hR.rowsRaiseAt hgr hrC (hP x₀ hR.mem)
    ((StageType.grade_faceCell _ _).trans hR.grade_eq)
    (mem_image_of_mem _ hR.mem)
    (fun x hx ↦ by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      refine ⟨_, rfl, hP z hz, (CellScheme.mem_below _).mpr (Prod.mk_le_mk.mpr ⟨?_, ?_⟩)⟩
      · rw [StageType.scope_faceCell, StageType.scope_faceCell]
        exact map_subset_map.mpr (Prod.mk_le_mk.mp (hR.le z hz)).1
      · rw [StageType.grade_faceCell, StageType.grade_faceCell]
        exact (Prod.mk_le_mk.mp (hR.le z hz)).2)
    (leftCell_mem z₁) ((grade_leftCell z₁).trans hL.grade_one)
    (leftCell_mem z₂) ((grade_leftCell z₂).trans hL.grade_two)
    (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg ↦ ?_)
    (hbelowApex z₁) (hbelowApex z₂) (by rw [rowAt_leftCell, rowAt_leftCell]; exact hL.row_tie)
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hL.tie_one _ (isLawful_left_of_isLawfulBelow hf) z ((grade_leftCell z).symm.trans hg)
      fun hz ↦ h0 (hfr0 hf hfr z hz)
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hL.tie_two _ (isLawful_left_of_isLawfulBelow hf) z ((grade_leftCell z).symm.trans hg)
      fun hz ↦ h0 (hfr0 hf hfr z hz)
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hfr0 hf hfr z (hL.label_three z ((grade_leftCell z).symm.trans hg))

/-- **The restricted reading layer at several new tops is legal below the full grade** at every
seed on five points whose left coatom type has a tie-keeping marker and whose right coatom type
has a set of new tops below one of grade `1`: the four fill conditions. -/
theorem isLegalBelowFullGrade_readingTop_of_rightNewTops {a z₁ z₂ : Fin I.left.card}
    {n : ℕ} {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {Z : Finset (Fin I.right.card)}
    {x₀ : Fin I.right.card} (hR : RightNewTops I.right Z x₀) :
    (readingTop I (leftCell I a) (newTopsOf I Z)).IsLegalBelowFullGrade := by
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hX3 : ∀ x ∈ newTopsOf I Z, (scheme I).toCellScheme.grade x ≤ 3 :=
    fun x hx ↦ (grade_le_one_of_rightNewTops hR hx).trans (by omega)
  refine (isLegalBelowFullGrade_readingTop_iff hgr fun x hx ↦ (hX3 x hx).trans (by omega)).mpr
    ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillBot_left_of_left hL.gradedIndex_apex hL.rowAt_apex hL.face_bot _
        hR.label_eq
    · rw [mem_singleton.mp hz]
      exact readingFillBot_right_of_unique hgr hrC huniq
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillPos_left_of_rightNewTops hL hR
    · rw [mem_singleton.mp hz]
      exact readingFillPos_right_of_unique hgr hrC huniq hX3

end TowerProfile

/-! ### Several new tops of `rightType` at `seedOne` -/

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile StageType

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

theorem gradedIndex_rightType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (rightType α).toCellScheme.gradedIndex (Fin.castSucc a) =
      (TwoFaceLiftCounterexample.cellScope a, TwoFaceLiftCounterexample.cellGrade a) :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc CaseSplitCounterexample.S 4 a

theorem label_rightType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (rightType α).label (Fin.castSucc a) = CaseSplitCounterexample.labelling ⊤ ⊤ ⊥ a :=
  StageType.addApex_label_castSucc (t := rightBase α) isLegalBelowFullGrade_S (by omega) a

/-- The live cells of grade `1` are labelled `⊤` by `labelling ⊤ ⊤ ⊥`. -/
theorem labelling_top_of_live {a : Fin 19} (hl : CaseSplitCounterexample.live a = true)
    (hg : TwoFaceLiftCounterexample.cellGrade a = 1) :
    CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ a = ⊤ := by
  simp [CaseSplitCounterexample.labelling, hl, hg]

/-- **Sets of new tops of `rightType`**: live cells of grade `1` of `S` (so through the point `3`
and labelled `⊤`) whose scopes lie in that of one of them, `a₀`. -/
theorem rightNewTops_rightType {A : Finset (Fin CaseSplitCounterexample.S.{u}.card)}
    {a₀ : Fin CaseSplitCounterexample.S.{u}.card} (ha₀ : a₀ ∈ A)
    (hA : ∀ a ∈ A, CaseSplitCounterexample.live a = true ∧
      TwoFaceLiftCounterexample.cellGrade a = 1 ∧
      TwoFaceLiftCounterexample.cellScope a ⊆ TwoFaceLiftCounterexample.cellScope a₀) :
    RightNewTops (rightType α) (A.image Fin.castSucc) (Fin.castSucc a₀) where
  rowsRaiseAt := rowsRaiseAt_rightType
  mem := mem_image_of_mem _ ha₀
  mem_scope z hz := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
    exact Eq.mpr (congrArg ((3 : Fin 4) ∈ ·) (congrArg Prod.fst (gradedIndex_rightType_castSucc a)))
      ((live_iff_three_mem a (hA a ha).2.1).mp (hA a ha).1)
  grade_eq := (congrArg Prod.snd (gradedIndex_rightType_castSucc a₀)).trans (hA a₀ ha₀).2.1
  label_eq z hz := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
    exact (label_rightType_castSucc a).trans (labelling_top_of_live (hA a ha).1 (hA a ha).2.1)
  le z hz := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
    exact (gradedIndex_rightType_castSucc a).trans_le (le_of_le_of_eq
      (Prod.mk_le_mk.mpr ⟨(hA a ha).2.2, by rw [(hA a ha).2.1, (hA a₀ ha₀).2.1]⟩)
      (gradedIndex_rightType_castSucc a₀).symm)

/-- The new tops through `{2, 3}`: the cells `{3}` and `{2, 3}` of `rightType`. -/
noncomputable abbrev topsTwo : Finset (Fin (rightType α).card) :=
  ({⟨3, by decide⟩, ⟨6, by decide⟩} : Finset (Fin CaseSplitCounterexample.S.{u}.card)).image
    Fin.castSucc

/-- The new tops through `{1, 2, 3}`: the cells `{3}`, `{2, 3}` and `{1, 2, 3}` of
`rightType`. -/
noncomputable abbrev topsOneTwo : Finset (Fin (rightType α).card) :=
  ({⟨3, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩} :
    Finset (Fin CaseSplitCounterexample.S.{u}.card)).image Fin.castSucc

theorem rightNewTops_topsTwo :
    RightNewTops (rightType α) (topsTwo (α := α))
      (Fin.castSucc (⟨6, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) :=
  rightNewTops_rightType (by decide) fun a ha ↦ by
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> decide

theorem rightNewTops_topsOneTwo :
    RightNewTops (rightType α) (topsOneTwo (α := α))
      (Fin.castSucc (⟨8, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) :=
  rightNewTops_rightType (by decide) fun a ha ↦ by
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> decide

/-- **The restricted reading layer at the new tops `{3}`, `{2, 3}` is legal at `seedOne`.** -/
theorem isLegalBelowFullGrade_readingTop_seedOne_two :
    (readingTop (seedOne hα) (leftCell (seedOne hα) (Fin.last _))
      (newTopsOf (seedOne hα) (topsTwo (α := α)))).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_readingTop_of_rightNewTops (leftTie_seedOne hα) rightNewTops_topsTwo

/-- **The restricted reading layer at the new tops `{3}`, `{2, 3}`, `{1, 2, 3}` is legal at
`seedOne`.** -/
theorem isLegalBelowFullGrade_readingTop_seedOne_oneTwo :
    (readingTop (seedOne hα) (leftCell (seedOne hα) (Fin.last _))
      (newTopsOf (seedOne hα) (topsOneTwo (α := α)))).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_readingTop_of_rightNewTops (leftTie_seedOne hα) rightNewTops_topsOneTwo

/-! ### The carrier at a set of new tops -/

variable (Z : Finset (Fin (rightType α).card))

theorem grade_newTopsOf_one {x : Fin (scheme (seedOne hα)).card}
    (hx : x ∈ newTopsOf (seedOne hα) Z) : (scheme (seedOne hα)).toCellScheme.grade x ≤ 4 := by
  obtain ⟨z, -, rfl⟩ := mem_image.mp hx
  rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd]
  exact (StageType.grade_faceCell _ _).trans_le ((seedOne hα).right.grade_le _)

variable (hZ : ∀ z ∈ Z, (rightType α).label z = ⊤)
  (hleg : (readingTop (seedOne hα) (leftCell (seedOne hα) (Fin.last _))
    (newTopsOf (seedOne hα) Z)).IsLegalBelowFullGrade)

/-- **The completion below the full grade at `seedOne` through the restricted reading layer at the
new tops `Z`**, with the glued labelling. -/
noncomputable def completionOf : CompletionBelowFullGrade (seedOne hα) :=
  readingCompletion (seedOne hα) _ _ hleg (grade_marker_one hα).le
    (fun _ hx ↦ grade_newTopsOf_one hα Z hx) (gluedOne hα) (isLawfulBelow_gluedOne hα)
    (fun x hx ↦ by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      rw [gluedOne_embed3]
      exact le_of_le_of_eq le_top ((StageType.label_faceCell _ _).trans (hZ z hz)).symm)
    (gluedOne_embed3 hα)

/-- **The carrier at the new tops `Z`**: the completion, the apex added. -/
noncomputable def carrierOf : StageType.{u} α 5 :=
  (completionOf hα Z hZ hleg).completion hα.isSuccPrelimit

theorem carrierOf_mem_cofaces : carrierOf hα Z hZ hleg ∈ (oneType hα).cofaces :=
  ⟨(completionOf hα Z hZ hleg).isLegal_completion _,
    (completionOf hα Z hZ hleg).restrictFace_left_completion _⟩

theorem restrictFace_right_carrierOf :
    restrictFace (extendByLast Fin.castSuccEmb) (carrierOf hα Z hZ hleg) = some (rightType α) :=
  (completionOf hα Z hZ hleg).restrictFace_right_completion _

theorem faceCell_marker_carrierOf :
    faceCell (carrierOf_mem_cofaces hα Z hZ hleg).2 (Fin.last _) =
      Fin.castSucc (Fin.castAdd _ (leftCell (seedOne hα) (Fin.last _))) :=
  (completionOf hα Z hZ hleg).faceCell_completion hα.isSuccPrelimit Coatom.univ_map_left_ne _
    (seedOne hα).restrictFace_left _

variable {n : ℕ} {g : Fin n ↪ Fin 3} {d : StageType.{u} α (n + 1)}

/-- The face of the amalgam of `seedOne` along `extendByLast g` through the new point. -/
theorem restrictFace_amalgam_of (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (seedOne hα).amalgam = some d :=
  (congrArg (restrictFace · (seedOne hα).amalgam) (extendByLast_trans g Fin.castSuccEmb)).symm.trans
    ((restrictFace_trans _ _ _ (seedOne hα).restrictFace_right).symm.trans hd)

theorem restrictFace_carrierOf (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (carrierOf hα Z hZ hleg) = some d :=
  (congrArg (restrictFace · (carrierOf hα Z hZ hleg))
    (extendByLast_trans g Fin.castSuccEmb)).symm.trans
    ((restrictFace_trans _ _ _ (restrictFace_right_carrierOf hα Z hZ hleg)).symm.trans hd)

/-- The point set of a root through the new point is a proper face. -/
theorem univ_map_extendByLast_ne (hn : n ≤ 2) :
    univ.map (extendByLast (g.trans Fin.castSuccEmb)) ≠ univ := by
  intro h
  have := congrArg Finset.card h
  simp at this
  omega

/-- **The cells of the donor in the carrier** are the old cells of their cells in `rightType`. -/
theorem faceCell_carrierOf (hn : n ≤ 2)
    (hd : restrictFace (extendByLast g) (rightType α) = some d) (j : Fin d.card) :
    faceCell (restrictFace_carrierOf hα Z hZ hleg hd) j =
      Fin.castSucc (Fin.castAdd _ (embed3 (seedOne hα)
        (faceCell (seedOne hα).restrictFace_right (faceCell hd j)))) := by
  refine ((completionOf hα Z hZ hleg).faceCell_completion hα.isSuccPrelimit
    (univ_map_extendByLast_ne hn) _ (restrictFace_amalgam_of hα hd) j).trans ?_
  refine congrArg (fun x ↦ Fin.castSucc (Fin.castAdd _ (embed3 (seedOne hα) x))) ?_
  have hcomp : restrictFace ((extendByLast g).trans (Coatom.right 3)) (seedOne hα).amalgam =
      some d := (restrictFace_trans _ _ _ (seedOne hα).restrictFace_right).symm.trans hd
  exact (faceCell_congr (extendByLast_trans g Fin.castSuccEmb).symm _ hcomp j).trans
    (faceCell_trans (seedOne hα).restrictFace_right hd hcomp j)

/-- **The carrier at `Z` is a top-reading carrier** for every donor `d` of `rightType` along
`extendByLast g` whose new tops labelled `⊤` lie in `Z`. -/
theorem isTopReadingCarrier_carrierOf (hn : n ≤ 2)
    (hd : restrictFace (extendByLast g) (rightType α) = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    (oneType hα).IsTopReadingCarrier (g.trans Fin.castSuccEmb) d (Fin.last _) (Fin.last _)
      (carrierOf hα Z hZ hleg) where
  isLegal := (carrierOf_mem_cofaces hα Z hZ hleg).1
  restrictFace_castSucc := (carrierOf_mem_cofaces hα Z hZ hleg).2
  restrictFace_extendByLast := restrictFace_carrierOf hα Z hZ hleg hd
  reads u hu _ j hj hjt := by
    obtain ⟨w, rfl, hw⟩ := (completionOf hα Z hZ hleg).exists_castSucc_of_gradedIndex_completion
      hα.isSuccPrelimit (k := 4) (by omega) (hu.trans (by rw [grade_oneType_last]))
    rw [faceCell_marker_carrierOf, faceCell_carrierOf hα Z hZ hleg hn hd j]
    exact ((completionOf hα Z hZ hleg).rowAt_completion hα.isSuccPrelimit w _).trans_le
      ((rowAt_readingTop_le (grade_marker_one hα).le (fun _ hx ↦ grade_newTopsOf_one hα Z hx) hw
        (mem_image_of_mem _ (hcover j hj hjt))).trans_eq
        ((completionOf hα Z hZ hleg).rowAt_completion hα.isSuccPrelimit w _).symm)

/-! ### Every root at `oneType` and `rightType` -/

theorem univ_map_trans_castSuccEmb (g : Fin n ↪ Fin 3) :
    univ.map (g.trans Fin.castSuccEmb) =
      univ.map (extendByLast g) ⊓ univ.map (Fin.castSuccEmb : Fin 3 ↪ Fin 4) := by
  ext x
  simp only [mem_map, mem_univ, true_and, Finset.inf_eq_inter, mem_inter,
    Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨Fin.castSucc i, extendByLast_castSucc g i⟩, ⟨g i, rfl⟩⟩
  · rintro ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    induction y using Fin.lastCases with
    | last =>
      rw [extendByLast_last] at hz
      exact absurd hz (Fin.castSucc_lt_last z).ne
    | cast i => exact ⟨i, (extendByLast_castSucc g i).symm⟩

/-- **The common face along a root**: the face of `oneType` along `g` and the face of the donor
along its first points agree. -/
theorem exists_root_face_of (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    ∃ t, restrictFace (g.trans Fin.castSuccEmb) (oneType hα) = some t ∧
      restrictFace Fin.castSuccEmb d = some t := by
  have h₁ := ((restrictFace_eq_some_iff _ _).mp hd).1
  have h₂ := ((restrictFace_eq_some_iff _ _).mp (restrictFace_rightType α)).1
  have hf : univ.map (g.trans Fin.castSuccEmb) ∈ (rightType α).toCellScheme.faces := by
    rw [univ_map_trans_castSuccEmb]
    exact (rightType α).isWellFormed.isPlan.infClosed h₁ h₂
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr hf)
  have hgt : restrictFace g (faceT5 α) = some t :=
    (restrictFace_trans _ _ _ (restrictFace_rightType α)).trans ht
  refine ⟨t, (restrictFace_trans _ _ _ (restrictFace_oneType hα)).symm.trans hgt, ?_⟩
  exact (restrictFace_trans _ _ _ hd).trans ((congrArg (restrictFace · (rightType α))
    (castSuccEmb_trans_extendByLast g)).trans ht)

/-- The cells of `S` labelled `⊤` by `labelling ⊤ ⊤ ⊥` are live of grade other than `3`. -/
theorem live_of_labelling_top {a : Fin 19}
    (h : CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ a = ⊤) :
    CaseSplitCounterexample.live a = true ∧ TwoFaceLiftCounterexample.cellGrade a ≠ 3 := by
  unfold CaseSplitCounterexample.labelling at h
  split_ifs at h with h1 h2 h3 <;> simp_all

/-- The cells of `S` through the point `3` labelled `⊤` inside a set `M`. -/
def topCells (M : Finset (Fin 4)) (a : Fin 19) : Prop :=
  CaseSplitCounterexample.live a = true ∧ TwoFaceLiftCounterexample.cellGrade a ≠ 3 ∧
    TwoFaceLiftCounterexample.cellScope a ⊆ M ∧ (3 : Fin 4) ∈ TwoFaceLiftCounterexample.cellScope a

instance (M : Finset (Fin 4)) : DecidablePred (topCells M) := fun _ ↦ by
  unfold topCells; infer_instance

/-- **Inside a proper set through the point `3`, the cells of `S` through `3` labelled `⊤` are of
grade `1` and lie below one of them.** -/
theorem exists_top_topCells : ∀ M : Finset (Fin 4), M ≠ univ → (3 : Fin 4) ∈ M →
    ∃ a₀ : Fin 19, topCells M a₀ ∧ ∀ a, topCells M a →
      CaseSplitCounterexample.live a = true ∧ TwoFaceLiftCounterexample.cellGrade a = 1 ∧
        TwoFaceLiftCounterexample.cellScope a ⊆ TwoFaceLiftCounterexample.cellScope a₀ := by
  unfold topCells
  decide

/-- A cell of `S` by its index. -/
abbrev toS (a : Fin 19) : Fin CaseSplitCounterexample.S.{u}.card := a

theorem cellGrade_le_three : ∀ a : Fin 19, TwoFaceLiftCounterexample.cellGrade a ≤ 3 := by
  decide

/-- The new tops of `rightType` inside `M`. -/
noncomputable def topsOf (M : Finset (Fin 4)) : Finset (Fin (rightType α).card) :=
  (((univ : Finset (Fin 19)).filter (topCells M)).image toS.{u}).image Fin.castSucc

theorem rightNewTops_topsOf {M : Finset (Fin 4)} (hM : M ≠ univ) (h3 : (3 : Fin 4) ∈ M) :
    ∃ x₀, RightNewTops (rightType α) (topsOf M) x₀ := by
  obtain ⟨a₀, ha₀, hA⟩ := exists_top_topCells M hM h3
  refine ⟨_, rightNewTops_rightType (a₀ := toS a₀)
    (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, ha₀⟩)) fun a ha ↦ ?_⟩
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
  exact hA b (mem_filter.mp hb).2

theorem label_topsOf {M : Finset (Fin 4)} (z : Fin (rightType α).card) (hz : z ∈ topsOf M) :
    (rightType α).label z = ⊤ := by
  obtain ⟨a', ha', rfl⟩ := mem_image.mp hz
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
  obtain ⟨hl, hg, -, -⟩ := (mem_filter.mp ha).2
  refine (label_rightType_castSucc (toS a)).trans ?_
  have h12 : TwoFaceLiftCounterexample.cellGrade a = 1 ∨
      TwoFaceLiftCounterexample.cellGrade a = 2 := by
    have := cellGrade_pos a
    have := cellGrade_le_three a
    omega
  unfold CaseSplitCounterexample.labelling
  rcases h12 with h | h <;> simp [hl, h]

theorem cases_rightType (z : Fin (rightType α).card) :
    z = Fin.last _ ∨ ∃ a : Fin CaseSplitCounterexample.S.{u}.card, z = Fin.castSucc a := by
  change Fin ((rightBase α).card + 1) at z
  induction z using Fin.lastCases with
  | last => exact .inl rfl
  | cast a => exact .inr ⟨a, rfl⟩

theorem mem_topsOf {M : Finset (Fin 4)} {a : Fin CaseSplitCounterexample.S.{u}.card}
    (ha : topCells M a) : (Fin.castSucc a : Fin (rightType α).card) ∈ topsOf M :=
  mem_image_of_mem _ (mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩, rfl⟩)

/-- **The new tops of a donor of `rightType` lie in `topsOf`** of the point set of its root. -/
theorem faceCell_mem_topsOf (hd : restrictFace (extendByLast g) (rightType α) = some d)
    (hM : univ.map (extendByLast g) ≠ univ) (j : Fin d.card)
    (hj : Fin.last n ∈ d.toCellScheme.scope j) (hjt : d.label j = ⊤) :
    faceCell hd j ∈ topsOf (univ.map (extendByLast g)) := by
  have hsub : (rightType α).toCellScheme.scope (faceCell hd j) ⊆ univ.map (extendByLast g) := by
    rw [scope_faceCell]
    exact map_subset_map.mpr (subset_univ _)
  have h3 : (3 : Fin 4) ∈ (rightType α).toCellScheme.scope (faceCell hd j) := by
    rw [scope_faceCell]
    exact mem_map.mpr ⟨_, hj, extendByLast_last g⟩
  have hlab : (rightType α).label (faceCell hd j) = ⊤ := (label_faceCell hd j).trans hjt
  rcases cases_rightType (faceCell hd j) with h | ⟨a, h⟩
  · have hs : (rightType α).toCellScheme.scope (faceCell hd j) = univ :=
      (congrArg (rightType α).toCellScheme.scope h).trans
        (StageType.addApex_scope_last (t := rightBase α) isLegalBelowFullGrade_S (by omega))
    exact absurd (univ_subset_iff.mp (le_of_eq_of_le hs.symm hsub)) hM
  · have hsc : (rightType α).toCellScheme.scope (faceCell hd j) =
        TwoFaceLiftCounterexample.cellScope a :=
      (congrArg (rightType α).toCellScheme.scope h).trans
        (congrArg Prod.fst (gradedIndex_rightType_castSucc a))
    obtain ⟨hl, hg⟩ := live_of_labelling_top
      ((label_rightType_castSucc a).symm.trans ((congrArg (rightType α).label h).symm.trans hlab))
    exact h ▸ mem_topsOf ⟨hl, hg, hsc ▸ hsub, hsc ▸ h3⟩

/-- The cells of `oneType` visible through a root inside the common face are labelled `⊥`. -/
theorem label_eq_bot_of_mem_visibleCells {y : Fin (oneType hα).card}
    (hy : y ∈ (oneType hα).visibleCells (g.trans Fin.castSuccEmb)) : (oneType hα).label y = ⊥ := by
  have hnot : (3 : Fin 4) ∉ (oneType hα).toCellScheme.scope y := fun h3 ↦ by
    obtain ⟨i, hi⟩ := Scheme.mem_visibleCells.mp hy (mem_coe.mpr h3)
    exact absurd hi (Fin.castSucc_lt_last (g i)).ne
  rcases cases_oneType hα y with rfl | ⟨a, rfl⟩
  · exact absurd (Eq.mpr (congrArg ((3 : Fin 4) ∈ ·) (StageType.addApex_scope_last
      (t := oneBase hα) isLegalBelowFullGrade_S (by omega))) (mem_univ _)) hnot
  · refine (label_oneType_castSucc hα a).trans (labelling_bot_eq_bot_of_notMem a fun h3 ↦ hnot ?_)
    exact Eq.mpr (congrArg ((3 : Fin 4) ∈ ·)
      (congrArg Prod.fst (gradedIndex_oneType_castSucc hα a))) h3

/-- **`oneType` is an acquired context along every root of at most two points inside the common
face** (`StageType.markedCapContextBelow'_addApex`; the root cells are labelled `⊥`). -/
theorem markedCapContextBelow'_oneType_of (hn : n ≤ 2) :
    TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) (g.trans Fin.castSuccEmb) :=
  StageType.markedCapContextBelow'_addApex (t₀ := oneBase hα) isLegalBelowFullGrade_S
    (by omega) (by omega)
    (fun y hy ↦ (label_eq_bot_of_mem_visibleCells hα hy).trans_ne bot_ne_top)
    fun y hy μ f _ hyf ↦ absurd ((label_eq_bot_of_mem_visibleCells hα hy).symm.trans hyf)
      (WithBot.bot_ne_coe)

/-- **`oneType` is not an acquired context along a root of three points**: the top cap has grade
above the arity plus one. -/
theorem not_markedCapContextBelow'_oneType_of (hn : 2 < n) :
    ¬ TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) (g.trans Fin.castSuccEmb) :=
  fun ⟨_, _, hctx, _⟩ ↦ absurd (arity_le_two_of_isMarkedCapContextAt hctx) (by omega)

/-- **The clause of hollow coatom cutoff determination at `oneType` and `rightType`, at every
root** (feasibility at one context and one coface, every root): for every root `g` along which
`oneType` is an acquired context respecting the root bottoms and every donor `d` of `rightType`
along `extendByLast g`, the carrier at the new tops of `rightType` inside the point set of the root
(`TopReadingApexExample.carrierOf`, the reading layer legal by
`TowerProfile.isLegalBelowFullGrade_readingTop_of_rightNewTops`) is a coface of `oneType` with face
`rightType` determining `d` at a permitted cutoff. -/
theorem exists_coface_oneType_rightType (g : Fin n ↪ Fin 3)
    (hP : TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) (g.trans Fin.castSuccEmb))
    (d : StageType.{u} α (n + 1)) (hd : restrictFace (extendByLast g) (rightType α) = some d) :
    ∃ D' ∈ (oneType hα).cofaces,
      restrictFace (extendByLast Fin.castSuccEmb) D' = some (rightType α) ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) (oneType hα) (g.trans Fin.castSuccEmb) d := by
  obtain ⟨c, r, hctx, -, -⟩ := hP
  have hn : n ≤ 2 := arity_le_two_of_isMarkedCapContextAt hctx
  have hM : univ.map (extendByLast g) ≠ univ := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  have h3 : (3 : Fin 4) ∈ univ.map (extendByLast g) :=
    mem_map.mpr ⟨Fin.last n, mem_univ _, extendByLast_last g⟩
  obtain ⟨x₀, hR⟩ := rightNewTops_topsOf (α := α) hM h3
  have hleg : (readingTop (seedOne hα) (leftCell (seedOne hα) (Fin.last _))
      (newTopsOf (seedOne hα) (topsOf (univ.map (extendByLast g))))).IsLegalBelowFullGrade :=
    isLegalBelowFullGrade_readingTop_of_rightNewTops (leftTie_seedOne hα) hR
  have hZ : ∀ z ∈ topsOf (α := α) (univ.map (extendByLast g)), (rightType α).label z = ⊤ :=
    label_topsOf
  have hD := isTopReadingCarrier_carrierOf hα _ hZ hleg hn hd
    fun j hj hjt ↦ faceCell_mem_topsOf hd hM j hj hjt
  obtain ⟨t, ht, htd⟩ := exists_root_face_of hα hd
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα (carrierOf hα _ hZ hleg)
  refine ⟨carrierOf hα _ hZ hleg, carrierOf_mem_cofaces hα _ hZ hleg,
    restrictFace_right_carrierOf hα _ hZ hleg, δ, hδ, ?_⟩
  exact isDeterminedWithin_receivingFamily_of_isTopReadingCarrier ht htd
    (isTopCap_oneType_last hα) (label_oneType_last hα) (by rw [grade_oneType_last]; omega) hD hδD

/-- The root `{2}` of the common face. -/
def rootTwo : Fin 1 ↪ Fin 3 := ⟨![2], fun a b _ ↦ Subsingleton.elim a b⟩

/-- The root `{1, 2}` of the common face. -/
def rootOneTwo : Fin 2 ↪ Fin 3 := ⟨![1, 2], by decide⟩

theorem univ_map_rootTwo : univ.map (extendByLast rootTwo) = ({2, 3} : Finset (Fin 4)) := by
  decide

theorem univ_map_rootOneTwo :
    univ.map (extendByLast rootOneTwo) = ({1, 2, 3} : Finset (Fin 4)) := by
  decide

/-- A scope of a cell of `rightType` is a face. -/
theorem scope_mem_faces_rightType (a : Fin CaseSplitCounterexample.S.{u}.card) :
    TwoFaceLiftCounterexample.cellScope a ∈ (rightType α).toCellScheme.faces :=
  Eq.mpr (congrArg (· ∈ (rightType α).toCellScheme.faces)
    (congrArg Prod.fst (gradedIndex_rightType_castSucc a)).symm)
    ((rightType α).isWellFormed.isWellFormed.scope_mem _)

/-- `rightType` has a donor along `{2, 3}`. -/
theorem exists_donor_rootTwo :
    ∃ d : StageType.{u} α 2, restrictFace (extendByLast rootTwo) (rightType α) = some d :=
  Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr
    (univ_map_rootTwo ▸ scope_mem_faces_rightType (α := α) (toS 6)))

/-- `rightType` has a donor along `{1, 2, 3}`. -/
theorem exists_donor_rootOneTwo :
    ∃ d : StageType.{u} α 3, restrictFace (extendByLast rootOneTwo) (rightType α) = some d :=
  Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr
    (univ_map_rootOneTwo ▸ scope_mem_faces_rightType (α := α) (toS 8)))

/-- **The clause of hollow coatom cutoff determination at `oneType`, the root `{2}` and
`rightType`** (feasibility): the context is acquired along the root, a donor exists, and every
donor is determined at a permitted cutoff in a coface with face `rightType`. -/
theorem hollowCoatomCutoffDetermination_rootTwo :
    TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) (rootTwo.trans Fin.castSuccEmb) ∧
      (∃ d : StageType.{u} α 2, restrictFace (extendByLast rootTwo) (rightType α) = some d) ∧
      ∀ d : StageType.{u} α 2, restrictFace (extendByLast rootTwo) (rightType α) = some d →
        ∃ D' ∈ (oneType hα).cofaces,
          restrictFace (extendByLast Fin.castSuccEmb) D' = some (rightType α) ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) (oneType hα)
              (rootTwo.trans Fin.castSuccEmb) d :=
  ⟨markedCapContextBelow'_oneType_of hα (by omega), exists_donor_rootTwo,
    fun d hd ↦ exists_coface_oneType_rightType hα rootTwo
      (markedCapContextBelow'_oneType_of hα (by omega)) d hd⟩

/-- **The clause of hollow coatom cutoff determination at `oneType`, the root `{1, 2}` and
`rightType`** (feasibility). -/
theorem hollowCoatomCutoffDetermination_rootOneTwo :
    TiedRootCapRelabel.MarkedCapContextBelow' (oneType hα) (rootOneTwo.trans Fin.castSuccEmb) ∧
      (∃ d : StageType.{u} α 3, restrictFace (extendByLast rootOneTwo) (rightType α) = some d) ∧
      ∀ d : StageType.{u} α 3, restrictFace (extendByLast rootOneTwo) (rightType α) = some d →
        ∃ D' ∈ (oneType hα).cofaces,
          restrictFace (extendByLast Fin.castSuccEmb) D' = some (rightType α) ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) (oneType hα)
              (rootOneTwo.trans Fin.castSuccEmb) d :=
  ⟨markedCapContextBelow'_oneType_of hα (by omega), exists_donor_rootOneTwo,
    fun d hd ↦ exists_coface_oneType_rightType hα rootOneTwo
      (markedCapContextBelow'_oneType_of hα (by omega)) d hd⟩

end TopReadingApexExample

/-! ### The clause at every seed with a tie-keeping marker and new tops -/

namespace TowerProfile

open TopReadingApexExample StageType

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- The glued labelling of a seed on the profile layer. -/
noncomputable def gluedOf : Fin (scheme I).card → Label.{u} :=
  fun d ↦ (exists_isLawful_top (I := I)).choose (Fin.castAdd _ d)

theorem isLawfulBelow_gluedOf :
    (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ gluedOf I d := by
  have hq := (exists_isLawful_top (I := I)).choose_spec.1
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  exact hL.isLawfulBelow _

theorem gluedOf_embed3 (d : Fin I.amalgam.card) : gluedOf I (embed3 I d) = I.amalgam.label d :=
  (exists_isLawful_top (I := I)).choose_spec.2 d

/-- The new tops of the profile layer have grade at most `4`. -/
theorem grade_newTopsOf_le {Z : Finset (Fin I.right.card)} {x : Fin (scheme I).card}
    (hx : x ∈ newTopsOf I Z) : (scheme I).toCellScheme.grade x ≤ 4 := by
  obtain ⟨z, -, rfl⟩ := mem_image.mp hx
  rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd]
  exact (StageType.grade_faceCell _ _).trans_le (I.right.grade_le _)

/-- **An apex cell** of a type on four points: the only cell at `(univ, 4)`, labelled `⊤`. -/
structure ApexCell {β : Ordinal.{u}} (t' : StageType.{u} β 4) (a : Fin t'.card) : Prop where
  gradedIndex_apex : t'.toCellScheme.gradedIndex a = (univ, 4)
  eq_apex : ∀ z, t'.toCellScheme.gradedIndex z = (univ, 4) → z = a
  label_apex : t'.label a = ⊤

/-- The marker of a tie-keeping marker is an apex cell. -/
theorem LeftTie.apexCell {β : Ordinal.{u}} {t' : StageType.{u} β 4} {m : ℕ}
    {ι : Fin m ↪ Fin 4} {a z₁ z₂ : Fin t'.card} (hL : LeftTie t' ι a z₁ z₂) : ApexCell t' a :=
  ⟨hL.gradedIndex_apex, hL.eq_apex, hL.label_apex⟩

variable {I} {a : Fin I.left.card}
  (hL : ApexCell I.left a) {Z : Finset (Fin I.right.card)}
  (hZ : ∀ z ∈ Z, I.right.label z = ⊤)
  (hleg : (readingTop I (leftCell I a) (newTopsOf I Z)).IsLegalBelowFullGrade)

/-- **The completion at a seed with a tie-keeping marker and new tops**: the restricted reading
layer at the new tops `Z`, legal by `TowerProfile.isLegalBelowFullGrade_readingTop_of_rightNewTops`,
with the glued labelling. -/
noncomputable def completionAt : CompletionBelowFullGrade I :=
  readingCompletion I _ _ hleg
    (leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex).1.le
    (fun _ hx ↦ grade_newTopsOf_le _ hx) (gluedOf I)
    (isLawfulBelow_gluedOf I)
    (fun x hx ↦ by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      rw [gluedOf_embed3]
      exact le_of_le_of_eq le_top ((StageType.label_faceCell _ _).trans (hZ z hz)).symm)
    (gluedOf_embed3 I)

variable (hα : Order.IsSuccLimit α)

/-- **The carrier at a seed with a tie-keeping marker and new tops**: the completion, the apex
added. -/
noncomputable def carrierAt : StageType.{u} α 5 :=
  (completionAt hL hZ hleg).completion hα.isSuccPrelimit

theorem carrierAt_mem_cofaces : carrierAt hL hZ hleg hα ∈ I.left.cofaces :=
  ⟨(completionAt hL hZ hleg).isLegal_completion _,
    (completionAt hL hZ hleg).restrictFace_left_completion _⟩

theorem restrictFace_right_carrierAt :
    restrictFace (extendByLast Fin.castSuccEmb) (carrierAt hL hZ hleg hα) = some I.right :=
  (completionAt hL hZ hleg).restrictFace_right_completion _

variable {n : ℕ} {g : Fin n ↪ Fin 3} {d : StageType.{u} α (n + 1)}

theorem restrictFace_amalgam_at (hd : restrictFace (extendByLast g) I.right = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d :=
  (congrArg (restrictFace · I.amalgam) (extendByLast_trans g Fin.castSuccEmb)).symm.trans
    ((restrictFace_trans _ _ _ I.restrictFace_right).symm.trans hd)

theorem restrictFace_carrierAt (hd : restrictFace (extendByLast g) I.right = some d) :
    restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (carrierAt hL hZ hleg hα) = some d :=
  (congrArg (restrictFace · (carrierAt hL hZ hleg hα))
    (extendByLast_trans g Fin.castSuccEmb)).symm.trans
    ((restrictFace_trans _ _ _ (restrictFace_right_carrierAt hL hZ hleg hα)).symm.trans hd)

theorem faceCell_carrierAt (hn : n ≤ 2) (hd : restrictFace (extendByLast g) I.right = some d)
    (j : Fin d.card) :
    faceCell (restrictFace_carrierAt hL hZ hleg hα hd) j =
      Fin.castSucc (Fin.castAdd _ (embed3 I (faceCell I.restrictFace_right (faceCell hd j)))) := by
  refine ((completionAt hL hZ hleg).faceCell_completion hα.isSuccPrelimit
    (univ_map_extendByLast_ne hn) _ (restrictFace_amalgam_at hd) j).trans ?_
  refine congrArg (fun x ↦ Fin.castSucc (Fin.castAdd _ (embed3 I x))) ?_
  have hcomp : restrictFace ((extendByLast g).trans (Coatom.right 3)) I.amalgam = some d :=
    (restrictFace_trans _ _ _ I.restrictFace_right).symm.trans hd
  exact (faceCell_congr (extendByLast_trans g Fin.castSuccEmb).symm _ hcomp j).trans
    (faceCell_trans I.restrictFace_right hd hcomp j)

theorem faceCell_marker_carrierAt :
    faceCell (carrierAt_mem_cofaces hL hZ hleg hα).2 a =
      Fin.castSucc (Fin.castAdd _ (leftCell I a)) :=
  (completionAt hL hZ hleg).faceCell_completion hα.isSuccPrelimit Coatom.univ_map_left_ne _
    I.restrictFace_left _

/-- **The carrier is a top-reading carrier** at the apex `a` of the left coatom type (cap and
marker) for every donor of the right coatom type whose new tops labelled `⊤` lie in `Z`. -/
theorem isTopReadingCarrier_carrierAt (hn : n ≤ 2)
    (hd : restrictFace (extendByLast g) I.right = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    I.left.IsTopReadingCarrier (g.trans Fin.castSuccEmb) d a a (carrierAt hL hZ hleg hα) where
  isLegal := (carrierAt_mem_cofaces hL hZ hleg hα).1
  restrictFace_castSucc := (carrierAt_mem_cofaces hL hZ hleg hα).2
  restrictFace_extendByLast := restrictFace_carrierAt hL hZ hleg hα hd
  reads u hu _ j hj hjt := by
    have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd hL.gradedIndex_apex
    obtain ⟨w, rfl, hw⟩ := (completionAt hL hZ hleg).exists_castSucc_of_gradedIndex_completion
      hα.isSuccPrelimit (k := 4) (by omega) (hu.trans (by rw [hga]))
    rw [faceCell_marker_carrierAt, faceCell_carrierAt hL hZ hleg hα hn hd j]
    exact ((completionAt hL hZ hleg).rowAt_completion hα.isSuccPrelimit w _).trans_le
      ((rowAt_readingTop_le (leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex).1.le
        (fun _ hx ↦ grade_newTopsOf_le _ hx) hw
        (mem_image_of_mem _ (hcover j hj hjt))).trans_eq
        ((completionAt hL hZ hleg).rowAt_completion hα.isSuccPrelimit w _).symm)

/-- `univ.map (g.trans Fin.castSuccEmb)` is the meet of the point sets of `extendByLast g` and of
`Fin.castSuccEmb`. -/
theorem univ_map_trans_castSuccEmb' {k : ℕ} (g : Fin n ↪ Fin k) :
    univ.map (g.trans Fin.castSuccEmb) =
      univ.map (extendByLast g) ⊓ univ.map (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) := by
  ext x
  simp only [mem_map, mem_univ, true_and, Finset.inf_eq_inter, mem_inter,
    Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨Fin.castSucc i, extendByLast_castSucc g i⟩, ⟨g i, rfl⟩⟩
  · rintro ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    induction y using Fin.lastCases with
    | last =>
      rw [extendByLast_last] at hz
      exact absurd hz (Fin.castSucc_lt_last z).ne
    | cast i => exact ⟨i, (extendByLast_castSucc g i).symm⟩

/-- **The common face along a root at a seed**: the face of the left coatom type along `g` and the
face of the donor along its first points agree (the meet of two faces of the amalgam is a face). -/
theorem exists_root_face_at (hd : restrictFace (extendByLast g) I.right = some d) :
    ∃ t, restrictFace (g.trans Fin.castSuccEmb) I.left = some t ∧
      restrictFace Fin.castSuccEmb d = some t := by
  have hA := restrictFace_amalgam_at hd
  have h₁ := ((restrictFace_eq_some_iff _ _).mp hA).1
  have h₂ := ((restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hf : univ.map ((g.trans Fin.castSuccEmb).trans Fin.castSuccEmb) ∈
      I.amalgam.toCellScheme.faces := by
    rw [univ_map_trans_castSuccEmb']
    exact I.amalgam.isWellFormed.isPlan.infClosed h₁ h₂
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr hf)
  refine ⟨t, (restrictFace_trans _ _ _ I.restrictFace_left).trans ht, ?_⟩
  exact (restrictFace_trans _ _ _ hA).trans ((congrArg (restrictFace · I.amalgam)
    (castSuccEmb_trans_extendByLast (g.trans Fin.castSuccEmb))).trans ht)

include hL hZ hleg hα in
/-- **The clause of hollow coatom cutoff determination at every seed with a tie-keeping marker and
new tops** (compiled under the hypotheses named): let the left coatom type of a seed on five points
have a tie-keeping marker at its apex `a` (`TowerProfile.LeftTie`) and the right coatom type a set
`Z` of new tops below one of grade `1` (`TowerProfile.RightNewTops`).  For every root `g` of at most
two points and every donor `d` of the right coatom type along `extendByLast g` whose new tops
labelled `⊤` lie in `Z`, the carrier `TowerProfile.carrierAt` is a coface of the left coatom type
with face the right coatom type, determining `d` at a permitted cutoff. -/
theorem exists_coface_of_legal (hn : n ≤ 2)
    (hd : restrictFace (extendByLast g) I.right = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    ∃ D' ∈ I.left.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some I.right ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) I.left (g.trans Fin.castSuccEmb) d := by
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd hL.gradedIndex_apex
  have hcap : I.left.IsTopCap a :=
    ⟨congrArg Prod.fst hL.gradedIndex_apex, hL.label_apex,
      fun x _ ↦ (I.left.grade_le x).trans_eq hga.symm⟩
  obtain ⟨t, ht, htd⟩ := exists_root_face_at hd
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα (carrierAt hL hZ hleg hα)
  exact ⟨carrierAt hL hZ hleg hα, carrierAt_mem_cofaces hL hZ hleg hα,
    restrictFace_right_carrierAt hL hZ hleg hα,
    δ, hδ, isDeterminedWithin_receivingFamily_of_isTopReadingCarrier ht htd hcap hL.label_apex
      (by rw [hga]; omega) (isTopReadingCarrier_carrierAt hL hZ hleg hα hn hd hcover) hδD⟩


omit hZ hleg in
include hα in
/-- `TowerProfile.exists_coface_of_legal` with the legality from new tops below one of grade `1`
(`TowerProfile.isLegalBelowFullGrade_readingTop_of_rightNewTops`). -/
theorem exists_coface_of_leftTie {z₁ z₂ : Fin I.left.card} {m : ℕ} {ι : Fin m ↪ Fin 4}
    (hLT : LeftTie I.left ι a z₁ z₂) {x₀ : Fin I.right.card} (hR : RightNewTops I.right Z x₀)
    (hn : n ≤ 2) (hd : restrictFace (extendByLast g) I.right = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    ∃ D' ∈ I.left.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some I.right ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) I.left (g.trans Fin.castSuccEmb) d :=
  exists_coface_of_legal hLT.apexCell hR.label_eq
    (isLegalBelowFullGrade_readingTop_of_rightNewTops hLT hR) hα hn hd hcover

end TowerProfile

end VaughtConjecture
