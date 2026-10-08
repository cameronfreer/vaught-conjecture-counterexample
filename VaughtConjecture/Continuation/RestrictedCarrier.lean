/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TopReadingApexSeed
import VaughtConjecture.Extension.ReadingMarks

/-!
# A restricted catalogue at the reading grade: the boundary extension fails

Roadmap, Layer 3 ((R3) of the table of 3.4).

The obstruction at `seedTR` (`TowerProfile.exists_top_reads_lt_markedCompletion_seedTR`) comes from
the catalogue entries at `(univ, 4)` that read a new top `x` below the marker `r`.  A **restricted**
layer keeps only reading entries: every new row reads `r` at most as `x`.  This file records what
that costs.

* **Reading rows tie every lawful labelling** (`CellScheme.Rows.IsLawfulBelow.le_of_forall_reads`,
  compiled in this repository (theorem named)): if every cell of the graded index `Y` reads `r` at
  most as `x` (`r` of the grade of `Y`, `x` of grade at most that), then every labelling lawful
  below `Y` labels `r` at most as `x`.  Availability at `r` gives a cell `v` of graded index `Y`
  with `w r ≤ w v`, and locality at `v` is monotone in the row and antitone in the grade.
* **The boundary extension fails** (`TowerProfile.not_extendsFromBoundary_sheetLayer_of_reads`,
  compiled in this repository (theorem named)): over the profile layer of any seed, let `r` be an
  isolated cell of the grade `4` of the coatom `(univ.erase (Fin.last 4), 4)` and `x` a cell of
  grade at most `3`.  In every sheet layer at the grade `4` all of whose entries read `r` at most
  as `x` (each entry lawful and not `⊤` at `x`, as every catalogue entry is), the extension from
  the boundary of `(univ.erase (Fin.last 4), 4)` and `(univ, 3)` into
  `(univ, 4)` fails along every new cell `i` at every cap `h` with `⊥ < h ≤ ε i r`.  The boundary
  labelling is the entry of `i` raised to `⊤` at `r` (`CellScheme.Rows.IsLawfulBelow.update_top`):
  lawful on both boundary faces and in the cap ball of the row of `i`; an extension would label
  `r` with `⊤` and `x` (below `(univ, 3)`) with the entry's value, which is not `⊤`, against the
  tie.
* **Over `TL` and at `seedTR`** (`TowerProfile.not_extendsFromBoundary_TL`,
  `TowerProfile.not_extendsFromBoundary_seedTR`): `r` the apex of `TL` and, at `seedTR`, `x` the
  new top `{3}` of the right coatom type (`TowerProfile.newTop`).  A layer whose entries are the
  reading marks (`Scheme.readingMarks`) is one; the leaf-and-marked layer of the reading
  specification is not (its leaves carry every catalogue entry, the forcing one included).

So the step of the bountifulness proof of the completion at the grade `4` that extends from the
two boundaries (`TowerProfile.extendsFromBoundary_top`, `TowerProfile.cappedLift_top_four`) cannot
be carried out for a restricted layer at `seedTR`: the forcing entry is excluded, and the labelling
it served (the raise at `r`) has no extension.  Whether a restricted layer is bountiful through
another lift is not settled here: a lift from the coatom `(univ.erase (Fin.last 4), 4)` alone does
not fix `x`, and an extension would have to label `x` with `⊤` (prospective).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

open Scheme

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {M : ℕ}
  {ε : Fin M → Fin (scheme I).card → Label.{u}} {σ : Fin M → Bool}
  {κ : (Fin (scheme I).card → Label.{u}) → Label.{u}}

/-- **The boundary extension fails for a reading layer.**  Over the profile layer of a seed, let
`r` be an isolated cell of the grade `4` below the coatom `(univ.erase (Fin.last 4), 4)` and `x` a
cell of grade at most `3`.  In a sheet layer at the grade `4` whose entries all read `r` at most as
`x`, along every new cell `i` and at every cap `h` with `⊥ < h ≤ ε i r`, the rows do not extend
from the boundary of `(univ.erase (Fin.last 4), 4)` and `(univ, 3)` into `(univ, 4)`. -/
theorem not_extendsFromBoundary_sheetLayer_of_reads
    {x r : Fin (scheme I).card} (hgr : (scheme I).toCellScheme.grade r = 4)
    (hgx : (scheme I).toCellScheme.grade x ≤ 3)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (huniq : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.gradedIndex r ≤ (scheme I).toCellScheme.gradedIndex y → y = r)
    (hrow : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
      y ≠ r → (scheme I).rows.row r ⟨y, hy⟩ = ⊥)
    (hrr : (scheme I).rows.row r ⟨r, (scheme I).toCellScheme.mem_below_gradedIndex r⟩ ≠ ⊥)
    (hreads : ∀ i, ε i r ≤ ε i x) (i : Fin M) (hlaw : (scheme I).rows.IsLawful (ε i))
    (hxtop : ε i x ≠ ⊤) {h : Label.{u}} (hbot : ⊥ < h) (hh : h ≤ ε i r)
    (hu : ((scheme I).sheetLayer 4 ε σ κ not_univ_four_le).toCellScheme.gradedIndex
      (Fin.natAdd _ i) = (univ, 4)) :
    ¬ ((scheme I).sheetLayer 4 ε σ κ not_univ_four_le).rows.ExtendsFromBoundary
      (univ.erase (Fin.last 4), 4) (univ, 3) (univ, 4) h
      (((scheme I).sheetLayer 4 ε σ κ not_univ_four_le).rows.rowBelow (Fin.natAdd _ i) hu) := by
  classical
  intro hE
  set T := (scheme I).sheetLayer 4 ε σ κ not_univ_four_le
  have he : (scheme I).rows.IsLawful (ε i) := hlaw
  have hxr : x ≠ r := fun h' ↦ by rw [h', hgr] at hgx; omega
  have hr3 : r ∉ (scheme I).toCellScheme.below (univ, 3) := fun h' ↦ by
    have := h'.2
    change (scheme I).toCellScheme.grade r ≤ 3 at this
    omega
  have hτ : ε i r ≠ ⊥ := (hbot.trans_le hh).ne'
  -- the boundary labelling: the entry raised to `⊤` at `r`, and `⊥` at the new cells
  set a := Function.update (ε i) r ⊤
  have har : a r = ⊤ := Function.update_self _ _ _
  have hae (e : Fin (scheme I).card) (he : e ≠ r) : a e = ε i e := Function.update_of_ne he _ _
  set w : Fin T.card → Label.{u} := Fin.append a fun _ ↦ ⊥
  have hwa (e : Fin (scheme I).card) : w (Fin.castAdd M e) = a e := Fin.append_left _ _ e
  have hU : ¬ ((univ : Finset (Fin 5)), 4) ≤ (univ.erase (Fin.last 4), 4) :=
    fun h' ↦ Seed.ne_univ_erase _ (univ_subset_iff.mp h'.1)
  have hV : ¬ ((univ : Finset (Fin 5)), 4) ≤ ((univ : Finset (Fin 5)), 3) :=
    fun h' ↦ absurd h'.2 (by simp)
  have hwU : T.rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d := by
    refine (isLawfulBelow_appendFullCells_iff hU).mpr ?_
    simp only [hwa]
    exact (he.isLawfulBelow _).update_top hrC huniq hrow hrr hτ
  have hwV : T.rows.IsLawfulBelow (univ, 3) fun d ↦ w d := by
    refine (isLawfulBelow_appendFullCells_iff hV).mpr ?_
    simp only [hwa]
    exact (CellScheme.Rows.isLawfulBelow_congr (w := a) (w' := ε i) fun d hd ↦
      Function.update_of_ne (fun hdr ↦ hr3 (by rw [← hdr]; exact hd)) _ _).mpr (he.isLawfulBelow _)
  have hmemB {X : Finset (Fin 5) × ℕ} (e : Fin (scheme I).card) :
      Fin.castAdd M e ∈ T.toCellScheme.below X ↔ e ∈ (scheme I).toCellScheme.below X := by
    rw [CellScheme.mem_below, CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd]
  have hwS : ∀ d : T.toCellScheme.below (univ, 4),
      (d : Fin T.card) ∈ T.toCellScheme.below (univ.erase (Fin.last 4), 4) ∨
        (d : Fin T.card) ∈ T.toCellScheme.below (univ, 3) →
      min (w d) h = min (T.rows.rowBelow (Fin.natAdd _ i) hu d) h := by
    intro d hd
    obtain ⟨e, -, rfl⟩ := exists_castAdd_eq_of_boundary_sheetLayer (hS := not_univ_four_le) hU hV hd
    -- the row of the new cell `i` reads the old cell `e` by the entry
    change min (w (Fin.castAdd M e)) h = min (T.rows.row (Fin.natAdd _ i) ⟨Fin.castAdd M e, _⟩) h
    rw [sheetLayer_row_natAdd (hS := not_univ_four_le), sheetRow_castAdd, hwa]
    by_cases her : e = r
    · rw [her, har, min_eq_right le_top, min_eq_right hh]
    · rw [hae e her]
  obtain ⟨ext, hext, hextw, -⟩ := hE w hwU hwV hwS
  have hrb : Fin.castAdd M r ∈ T.toCellScheme.below (univ, 4) :=
    castAdd_mem_below_sheetLayer (hS := not_univ_four_le) hgr.le
  have hxb : Fin.castAdd M x ∈ T.toCellScheme.below (univ, 4) :=
    castAdd_mem_below_sheetLayer (hS := not_univ_four_le) (hgx.trans (by omega))
  have htie := (CellScheme.Rows.isLawfulBelow_extendBot.mpr hext).le_of_forall_reads hrb hxb hu
    (by rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_natAdd, hgr])
    (by rw [appendFullCellsScheme_grade_castAdd, appendFullCellsScheme_grade_castAdd, hgr]
        exact hgx.trans (by omega))
    (fun v hv ↦ by
      obtain ⟨j, rfl⟩ := exists_natAdd_eq_sheetLayer (hS := not_univ_four_le) hv
      rw [sheetLayer_row_natAdd (hS := not_univ_four_le),
        sheetLayer_row_natAdd (hS := not_univ_four_le), sheetRow_castAdd, sheetRow_castAdd]
      exact hreads j)
  rw [CellScheme.Rows.extendBot_of_mem ext hrb, CellScheme.Rows.extendBot_of_mem ext hxb,
    hextw ⟨_, hrb⟩ (.inl ((hmemB r).mpr hrC)),
    hextw ⟨_, hxb⟩ (.inr ((hmemB x).mpr ⟨subset_univ _, hgx⟩)), hwa, hwa,
    har, hae x hxr, top_le_iff] at htie
  exact hxtop htie

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- The new top of `seedTR`: the cell `{3}` of the right coatom type, on the new point `4`. -/
noncomputable def newTop (α : Ordinal.{u}) : Fin (scheme (seedTR α)).card :=
  embed3 (seedTR α) (StageType.faceCell (seedTR α).restrictFace_right
    (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)))

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- The new top of `seedTR` has the grade `1`. -/
theorem grade_newTop (α : Ordinal.{u}) : (scheme (seedTR α)).toCellScheme.grade (newTop α) = 1 := by
  have hgz : (seedTR α).right.toCellScheme.grade
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) = 1 := by
    -- the right type is `appendFullCell` over `S`
    change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).grade (Fin.castSucc _) = 1
    rw [Scheme.appendFullCellScheme_grade_castSucc]
    rfl
  have h2 := congrArg Prod.snd (gradedIndex_embed3 (I := seedTR α)
    (StageType.faceCell (seedTR α).restrictFace_right
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))))
  simp only [CellScheme.gradedIndex_snd] at h2
  -- `newTop` is the cell of the profile layer at the cell `{3}` of the right type
  change (scheme (seedTR α)).toCellScheme.grade (embed3 (seedTR α)
    (StageType.faceCell (seedTR α).restrictFace_right
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)))) = 1
  rw [h2]
  exact (StageType.grade_faceCell _ _).trans hgz

open TwoFaceLiftExistsCounterexample in
/-- The apex of `TL`. -/
noncomputable def apexTL (α : Ordinal.{u}) : Fin (TL α).card := Fin.last _

open TwoFaceLiftExistsCounterexample in
/-- **Over `TL`, no reading layer extends from the boundary.**  For every seed with left coatom
type `TL` (any legal right coatom type over the face of `T5`) and every cell `x` of grade at most
`3`: in every sheet layer at the grade `4` whose entries all read `x` at least as the apex of `TL`,
along every new cell `i` and at every cap `h` with `⊥ < h ≤ ε i r`, the rows do not extend from
the boundary of `(univ.erase (Fin.last 4), 4)` and `(univ, 3)` into `(univ, 4)`. -/
theorem not_extendsFromBoundary_TL {α : Ordinal.{u}} {tb : StageType.{u} α 4} (hlb : tb.IsLegal)
    (hpb : StageType.restrictFace (Coatom.face 3) tb = some (CaseSplitCounterexample.faceT5 α))
    {M : ℕ}
    {ε : Fin M → Fin (scheme (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)).card →
      Label.{u}} {σ : Fin M → Bool}
    {κ : (Fin (scheme (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)).card →
      Label.{u}) → Label.{u}}
    (hlaw : ∀ i, (scheme (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)).rows.IsLawful
      (ε i))
    {x : Fin (scheme (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)).card}
    (hxtop : ∀ i, ε i x ≠ ⊤)
    (hgx : (scheme (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)).toCellScheme.grade
      x ≤ 3)
    (hreads : ∀ i, ε i (leftCell _ (apexTL α)) ≤ ε i x) (i : Fin M)
    {h : Label.{u}} (hbot : ⊥ < h) (hh : h ≤ ε i (leftCell _ (apexTL α)))
    (hu : ((scheme _).sheetLayer 4 ε σ κ not_univ_four_le).toCellScheme.gradedIndex
      (Fin.natAdd _ i) = (univ, 4)) :
    ¬ ((scheme _).sheetLayer 4 ε σ κ not_univ_four_le).rows.ExtendsFromBoundary
      (univ.erase (Fin.last 4), 4) (univ, 3) (univ, 4) h
      (((scheme _).sheetLayer 4 ε σ κ not_univ_four_le).rows.rowBelow (Fin.natAdd _ i) hu) := by
  obtain ⟨hg, hrC, huniq, hrow, hrr⟩ := isolated_of_left
    (I := Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb) (a := apexTL α)
    (StageType.addApex_gradedIndex_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))
    (fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := TL₀ α) isLegalBelowFullGrade_SL
      (by omega) hz)
    (fun _ hz ↦ StageType.rowAt_addApex_last_of_ne (t := TL₀ α) isLegalBelowFullGrade_SL
      (by omega) (fun _ ↦ rfl) hz)
    (StageType.rowAt_addApex_last_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))
  exact not_extendsFromBoundary_sheetLayer_of_reads hg hgx hrC huniq hrow hrr hreads i (hlaw i)
    (hxtop i) hbot hh hu

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- **At `seedTR`, no reading layer extends from the boundary**: `not_extendsFromBoundary_TL` with
the right coatom type `rightType α` and its new top. -/
theorem not_extendsFromBoundary_seedTR {α : Ordinal.{u}} {M : ℕ}
    {ε : Fin M → Fin (scheme (seedTR α)).card → Label.{u}} {σ : Fin M → Bool}
    {κ : (Fin (scheme (seedTR α)).card → Label.{u}) → Label.{u}}
    (hlaw : ∀ i, (scheme (seedTR α)).rows.IsLawful (ε i)) (hxtop : ∀ i, ε i (newTop α) ≠ ⊤)
    (hreads : ∀ i, ε i (leftCell (seedTR α) (apexTL α)) ≤ ε i (newTop α)) (i : Fin M)
    {h : Label.{u}} (hbot : ⊥ < h) (hh : h ≤ ε i (leftCell (seedTR α) (apexTL α)))
    (hu : ((scheme (seedTR α)).sheetLayer 4 ε σ κ not_univ_four_le).toCellScheme.gradedIndex
      (Fin.natAdd _ i) = (univ, 4)) :
    ¬ ((scheme (seedTR α)).sheetLayer 4 ε σ κ not_univ_four_le).rows.ExtendsFromBoundary
      (univ.erase (Fin.last 4), 4) (univ, 3) (univ, 4) h
      (((scheme (seedTR α)).sheetLayer 4 ε σ κ not_univ_four_le).rows.rowBelow
        (Fin.natAdd _ i) hu) :=
  not_extendsFromBoundary_TL (isLegal_rightType α) (restrictFace_rightType α) hlaw hxtop
    ((grade_newTop α).trans_le (by omega)) hreads i hbot hh hu

end TowerProfile

end VaughtConjecture
