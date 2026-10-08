/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.RaisedNewTops
import VaughtConjecture.Continuation.RestrictedCarrier

/-!
# A reading layer at the grade `4`, legal by lifts from the coatoms

Roadmap, Layer 3 ((R3) of the table of 3.4).

**The reading layer** (`TowerProfile.readingTop I r X`).  Over the profile layer of a seed `I` on
five points (the tower `T 2` and the profile layer at the grade `3`), one cell of full scope and
grade `4` for every **reading mark** (`Scheme.readingMarks`: a catalogue entry reading every cell
of `X` at least as `r`), in one sheet, and no other cell at the grade `4`.  Every cell of full
scope and grade `4` reads every cell of `X` at least as `r` (`TowerProfile.rowAt_readingTop_le`),
so every labelling lawful below `(univ, 4)` ties them
(`TowerProfile.le_of_isLawfulBelow_readingTop`).

**Legality by lifts from the coatoms** (compiled in this repository (theorem named)).  The lift
from a coatom at the grade `4` is the one-grade lift
(`CellScheme.Rows.cappedLift_of_ownerCappedLift`)
with the owner-capped lifts at `⊥` by a **fill at `⊥`** (`TowerProfile.ReadingFillBot`) and at the
short positive caps, from the serving cells, by a **fill along each reading mark**
(`TowerProfile.ReadingFillPos`): a labelling of the profile layer extending the given one below the
coatom, reading `X` at least as `r` (and agreeing with the mark capped at the cap); the template
of its orbit code is then a cell of the layer (`TowerProfile.exists_readingEntry_eq`).  No extension
from a boundary at the grade `4` is used (the step that fails for every reading layer,
`TowerProfile.not_extendsFromBoundary_seedTR`).

* `TowerProfile.isLegalBelowFullGrade_readingTop_iff`: for `r` of grade `4` and `X` of grade at
  most `4`, the reading layer is legal below the full grade **exactly when** the four fill
  conditions hold (at `⊥` and at the short positive caps, from each coatom): the fills are the
  seed-level form of the raise requirement (`StageType.RaisesNewTops`), and the necessity uses
  the tie.
* `TowerProfile.exists_isLawful_readingTop`: every labelling lawful below `(univ, 4)` of the profile
  layer reading `X` at least as `r` extends through the layer (lawfulness preserved);
  `TowerProfile.readingCompletion`: the completion below the full grade through the layer.
* **The fills at an isolated left marker** (`TowerProfile.readingFillBot_left`,
  `TowerProfile.readingFillBot_right`, `TowerProfile.readingFillPos_left`,
  `TowerProfile.readingFillPos_right`, `TowerProfile.isLegalBelowFullGrade_readingTop_of_isolated`):
  `r` of grade `4` on the left coatom, isolated (its row reads every other cell as `⊥`), `X` of
  grade at most `3`, given a lawful labelling `⊥` on the left coatom off `r` and `⊤` on `X`.  The
  fills are the fill of the profile layer (`TowerProfile.exists_fill_four`), the isolated cell moved
  (`CellScheme.Rows.IsLawfulBelow.update_isolated`), and, from the left coatom at or above the cap
  at `r`, the reading mark raised to `⊤` above the cap on the cells of grade at most `3`
  (`Label.raise`, a witness bounded by the grade `3`).
* **At `seedTR` and over `TL`**: `TowerProfile.isLegalBelowFullGrade_readingTop_seedTR`,
  `TowerProfile.rowAt_readingTop_seedTR_le`, `TowerProfile.exists_readingCompletion_seedTR` (the
  restricted layer at `seedTR` is legal below the full grade, reads the new top at least as the
  apex of `TL` at every cell of full scope and grade `4`, and carries the glued labelling); and
  `TowerProfile.isLegalBelowFullGrade_readingTop_TL`: for **every** legal right coatom type over
  the face of `T5` and every set of its new tops of grade at most `3`.

**Where the general construction stops** (argued, not formalized).  The construction is at the
arity of seeds on five points with the reading at the grade `4`; a marked-cap context in general
needs (i) a completion below the grade of the reading at other arities (not available here without
the coatom extension property), (ii) layers above the reading grade when the top cap is below the
top grade, and (iii) the four fills, which are stronger than `StageType.RaisesNewTops` (every value
at `r`, not only `⊤`; the agreement with the mark capped at the cap; the cells of full scope below
the reading grade).  At an isolated marker the fills hold for every donor; at other markers they
are open.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### An isolated cell -/

namespace CellScheme.Rows.IsLawfulBelow

variable {ι κ : Type*} {D : CellScheme ι κ} {R : D.Rows.{u}}

/-- **An isolated cell not at `⊥` puts every other cell below it at `⊥`**: its row reads them as
`⊥` (locality at the isolated cell). -/
theorem eq_bot_of_isolated {X : Finset κ × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {r : ι} (hrX : r ∈ D.below X)
    (hrow : ∀ y (hy : y ∈ D.below (D.gradedIndex r)), y ≠ r → R.row r ⟨y, hy⟩ = ⊥)
    (hwr : w r ≠ ⊥) {y : ι} (hy : y ∈ D.below (D.gradedIndex r)) (hyr : y ≠ r) : w y = ⊥ := by
  obtain ⟨-, hloc, -⟩ := isLawfulBelow_iff_forall.mp hw
  have h := (hloc r hrX).eq_bot (d := ⟨y, hy⟩) (hrow y hy hyr)
  change min (w y) (w r) = ⊥ at h
  exact (min_eq_bot.mp h).resolve_right hwr

/-- **Moving an isolated cell.**  Let `r` lie below `X`, the only cell below `X` at or above its
graded index and the only cell below `X` of its grade inside its scope, with a row reading every
other cell as `⊥` and itself not as `⊥`.  The labelling `w` with `r` sent to a label `v`
self-visible at the grade of `r` stays lawful below `X`, provided `w` is `⊥` at the other cells
below `r` when `v` is not `⊥`. -/
theorem update_isolated [DecidableEq ι] {X : Finset κ × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {r : ι} (hrX : r ∈ D.below X)
    (huniq : ∀ y ∈ D.below X, D.gradedIndex r ≤ D.gradedIndex y → y = r)
    (hsame : ∀ y ∈ D.below X, D.grade y = D.grade r → D.scope y ⊆ D.scope r → y = r)
    (hrow : ∀ y (hy : y ∈ D.below (D.gradedIndex r)), y ≠ r → R.row r ⟨y, hy⟩ = ⊥)
    (hrr : R.row r ⟨r, D.mem_below_gradedIndex r⟩ ≠ ⊥) {v : Label.{u}}
    (hv : IsSelfVisible (D.grade r) v)
    (hbot : v ≠ ⊥ → ∀ y ∈ D.below (D.gradedIndex r), y ≠ r → w y = ⊥) :
    R.IsLawfulBelow X fun d ↦ Function.update w r v d := by
  obtain ⟨hvis, hloc, havail⟩ := isLawfulBelow_iff_forall.mp hw
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hdr : d = r
    · rw [hdr, Function.update_self]; exact hv
    · rw [Function.update_of_ne hdr]; exact hvis d hd
  · by_cases hsr : s = r
    · subst hsr
      refine transformsTo_of_eq_bot_iff _ (K := D.grade s) (fun d ↦ d.2.2) hv _ _ fun d ↦ ?_
      rw [Function.update_self]
      by_cases hds : (d : ι) = s
      · have hd : d = ⟨s, D.mem_below_gradedIndex s⟩ := Subtype.ext hds
        subst hd
        rw [Function.update_self, min_self, ite_eq_right hrr]
      · rw [Function.update_of_ne hds, ite_eq_left (hrow d d.2 hds)]
        by_cases hv0 : v = ⊥
        · rw [hv0, min_bot_right]
        · rw [hbot hv0 d d.2 hds, min_bot_left]
    · -- no cell below `s` is `r`, so the labelling below `s` is unchanged
      have hrs (d : D.below (D.gradedIndex s)) : (d : ι) ≠ r := fun hdr ↦
        hsr (huniq s hs (hdr ▸ d.2))
      have heq : (fun d : D.below (D.gradedIndex s) ↦
          min (Function.update w r v d) (Function.update w r v s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s) := funext fun d ↦ by
        rw [Function.update_of_ne (hrs d), Function.update_of_ne hsr]
      rw [heq]
      exact hloc s hs
  · by_cases hsr : s = r
    · rw [hsr] at hst hg ⊢
      have htr : t = r := huniq t ht ⟨hst, hg.le⟩
      exact ⟨r, by rw [htr], le_of_eq (by rw [Function.update_self])⟩
    · obtain ⟨u, hu, hsu⟩ := havail s t ht hst hg
      by_cases hur : u = r
      · -- the target has the graded index of `r`, so it is `r`, and so is the source
        have htr : t = r := huniq t ht (by rw [← hu, hur])
        rw [htr] at hst hg ht
        exact absurd (hsame s ⟨hst.trans ht.1, hg.trans_le ht.2⟩ hg hst) hsr
      · exact ⟨u, hu, by rw [Function.update_of_ne hsr, Function.update_of_ne hur]; exact hsu⟩

end CellScheme.Rows.IsLawfulBelow

/-! ### Fills of the profile layer at the grade `4` -/

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The lift at the grade `3` of the profile layer, from either coatom. -/
theorem cappedLift_scheme_three {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
    (scheme I).rows.CappedLift (X := (univ.erase x, 3)) (Y := ((univ : Finset (Fin 5)), 3))
      ⟨erase_subset _ _, le_rfl⟩ :=
  (cappedLift_top_iff (I := I) _ fun h ↦ absurd h.2 (by simp)).mp
    (cappedLift_top_le_three hx le_rfl)

/-- **Extension from the boundary in the profile layer**, at the grade `4`, along a lawful
section: `TowerProfile.exists_isLawfulBelow_four` in the form of
`CellScheme.Rows.ExtendsFromBoundary`. -/
theorem extendsFromBoundary_scheme_four {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y)
    {a : Fin (scheme I).card → Label.{u}} (ha : (scheme I).rows.IsLawful a) {h : Label.{u}}
    (hh : IsSelfVisible 4 h) :
    (scheme I).rows.ExtendsFromBoundary (univ.erase x, 4) (univ, 3) (univ, 4) h
      fun d ↦ a d := by
  intro w hwU hwV hwS
  obtain ⟨g, hg, hgw, hga⟩ := exists_isLawfulBelow_four hx hy hxy hwU hwV ha hh fun e he ↦
    hwS ⟨e, he.elim (fun h' ↦ ⟨h'.1.trans (erase_subset _ _), h'.2⟩)
      fun h' ↦ ⟨h'.1, h'.2.trans (by omega)⟩⟩ he
  exact ⟨fun d ↦ g d, hg, fun d hd ↦ hgw d hd, fun d ↦ hga d d.2⟩

/-- Every cell of the profile layer lies below `(univ, 4)`. -/
theorem mem_below_univ_four (d : Fin (scheme I).card) :
    d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 4) := by
  have hg : (scheme I).toCellScheme.grade d ≤ 4 := by
    by_contra hd
    have h1 := isWellFormed_scheme.isWellFormed.grade_le_card d
    have h2 : #((scheme I).toCellScheme.scope d) ≤ 5 := by
      simpa using card_le_univ ((scheme I).toCellScheme.scope d)
    have h5 : #((scheme I).toCellScheme.scope d) = 5 := by omega
    have hs : (scheme I).toCellScheme.scope d = univ :=
      eq_univ_of_card _ (h5.trans (Fintype.card_fin 5).symm)
    exact not_univ_four_le d ⟨hs.ge, by change 4 ≤ (scheme I).toCellScheme.grade d; omega⟩
  exact ⟨subset_univ _, hg⟩

/-- **The fill from a coatom at the grade `4`**: a labelling lawful below a coatom at the grade `4`
that agrees capped at `h` with a lawful section `a` extends, unchanged below the coatom, to a
labelling lawful below `(univ, 4)` that agrees with `a` capped at `h` everywhere (the lift across
the boundary, `CellScheme.Rows.exists_lift_of_boundary`). -/
theorem exists_fill_four {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y)
    {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase x, 4) fun d ↦ f d)
    {a : Fin (scheme I).card → Label.{u}} (ha : (scheme I).rows.IsLawful a) {h : Label.{u}}
    (hh : IsSelfVisible 4 h)
    (hfa : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase x, 4), min (f d) h = min (a d) h) :
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase x, 4), g d = f d) ∧
      ∀ d, min (g d) h = min (a d) h := by
  classical
  obtain ⟨r, hr, hrf, hra⟩ := CellScheme.Rows.exists_lift_of_boundary
    (I := (univ.erase x, 4)) (U := (univ.erase x, 4)) (V := ((univ : Finset (Fin 5)), 3))
    (O := (univ.erase x, 3)) (Y := ((univ : Finset (Fin 5)), 4)) le_rfl
    ⟨subset_rfl, by omega⟩ ⟨erase_subset _ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, by omega⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (CellScheme.Rows.cappedLift_refl _)
    (cappedLift_scheme_three hx) hh (ha.isLawfulBelow _)
    (extendsFromBoundary_scheme_four hx hy hxy ha hh)
    hf fun e ↦ hfa e e.2
  refine ⟨fun d ↦ r ⟨d, mem_below_univ_four d⟩, ?_, fun d hd ↦ hrf ⟨d, hd⟩,
    fun d ↦ hra ⟨d, mem_below_univ_four d⟩⟩
  convert hr using 1


/-! ### The reading layer -/

variable (I) in
/-- The entries of the **reading layer**: the reading marks (`Scheme.readingMarks`), the catalogue
entries of the profile layer at the grade `4` that read every cell of `X` at least as `r`. -/
noncomputable abbrev readingEntry (r : Fin (scheme I).card) (X : Finset (Fin (scheme I).card)) :
    Fin ((scheme I).readingMarks 4 r X).card → Fin (scheme I).card → Label.{u} :=
  (scheme I).markEntry ((scheme I).readingMarks 4 r X)

variable (I) in
/-- **The reading layer**: the profile layer with one cell of full scope and grade `4` for every
reading mark, in one sheet.  No other entry of the catalogue has a cell. -/
noncomputable abbrev readingTop (r : Fin (scheme I).card) (X : Finset (Fin (scheme I).card)) :
    Scheme.{u} 5 :=
  (scheme I).sheetLayer 4 (readingEntry I r X) (fun _ ↦ false) (fun _ ↦ ⊥) not_univ_four_le

variable {r : Fin (scheme I).card} {X : Finset (Fin (scheme I).card)}

/-- The entries of the reading layer lie in the catalogue. -/
theorem readingEntry_mem (i : Fin ((scheme I).readingMarks 4 r X).card) :
    readingEntry I r X i ∈ (scheme I).catalogue 4 :=
  Scheme.readingMarks_subset r X (Scheme.markEntry_mem _ i)

/-- The entries of the reading layer read every cell of `X` at least as `r`. -/
theorem readingEntry_reads (i : Fin ((scheme I).readingMarks 4 r X).card) {x : Fin (scheme I).card}
    (hx : x ∈ X) : readingEntry I r X i r ≤ readingEntry I r X i x :=
  Scheme.le_of_mem_readingMarks (Scheme.markEntry_mem _ i) hx

/-- **A template for a reading labelling**: the orbit code of the splice of a labelling lawful
below `(univ, 4)` that reads every cell of `X` at least as `r` is the entry of a cell of the
reading layer. -/
theorem exists_readingEntry_eq (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) {g : Fin (scheme I).card → Label.{u}}
    (hg : (scheme I).rows.IsLawfulBelow (univ, 4) fun e ↦ g e) (hreads : ∀ x ∈ X, g r ≤ g x) :
    ∃ j₀, readingEntry I r X j₀ =
      orbitCode 4 ((scheme I).toCellScheme.splice 4 (fun _ ↦ ⊥) g) := by
  have hb := Scheme.orbitCode_splice_bot_mem_catalogue (S := scheme I) (k := 4) hg
  refine Scheme.exists_markEntry_eq ?_
  unfold Scheme.readingMarks
  refine mem_filter.mpr ⟨hb, fun x hx ↦ ?_⟩
  rw [orbitCode_apply, orbitCode_apply, CellScheme.splice_of_le hgr,
    CellScheme.splice_of_le (hX x hx)]
  exact monotone_orbitMap _ _ (hreads x hx)

/-- **Every cell of full scope of the reading layer reads every cell of `X` at least as `r`.** -/
theorem rowAt_readingTop_le (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) {u : Fin (readingTop I r X).card}
    (hu : (readingTop I r X).toCellScheme.gradedIndex u = (univ, 4)) {x : Fin (scheme I).card}
    (hx : x ∈ X) :
    (readingTop I r X).rowAt u (Fin.castAdd _ r) ≤
      (readingTop I r X).rowAt u (Fin.castAdd _ x) := by
  obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq_sheetLayer (S := scheme I) (k := 4)
    (hS := not_univ_four_le) hu
  have hrb := Scheme.castAdd_mem_below_sheetLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
    (ε := readingEntry I r X) (σ := fun _ ↦ false) (κ := fun _ ↦ ⊥) hgr
  have hxb := Scheme.castAdd_mem_below_sheetLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
    (ε := readingEntry I r X) (σ := fun _ ↦ false) (κ := fun _ ↦ ⊥) (hX x hx)
  rw [← hu] at hrb hxb
  rw [Scheme.rowAt_of_mem hrb, Scheme.rowAt_of_mem hxb, Scheme.sheetLayer_row_natAdd,
    Scheme.sheetLayer_row_natAdd, Scheme.sheetRow_castAdd, Scheme.sheetRow_castAdd]
  exact readingEntry_reads i hx

/-! ### The fill conditions -/

variable (I r X) in
/-- **The fill at the cap `⊥`** from the coatom `univ.erase z` at the grade `4`: every labelling
lawful below the coatom extends, unchanged below it, to a labelling lawful below `(univ, 4)` in the
profile layer that reads every cell of `X` at least as `r`. -/
def ReadingFillBot (z : Fin 5) : Prop :=
  ∀ f : Fin (scheme I).card → Label.{u},
    (scheme I).rows.IsLawfulBelow (univ.erase z, 4) (fun d ↦ f d) →
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase z, 4), g d = f d) ∧ ∀ x ∈ X, g r ≤ g x

variable (I r X) in
/-- **The fill at the short positive caps** from the coatom `univ.erase z` at the grade `4`, along
every reading mark `e`: every labelling lawful below the coatom that agrees with `e` capped at `h`
extends, unchanged below it, to a labelling lawful below `(univ, 4)` that agrees with `e` capped at
`h` everywhere and reads every cell of `X` at least as `r`. -/
def ReadingFillPos (z : Fin 5) : Prop :=
  ∀ e ∈ (scheme I).readingMarks 4 r X, ∀ h : Label.{u}, IsSelfVisible 4 h → IsShort 4 h → ⊥ < h →
    ∀ f : Fin (scheme I).card → Label.{u},
    (scheme I).rows.IsLawfulBelow (univ.erase z, 4) (fun d ↦ f d) →
    (∀ d ∈ (scheme I).toCellScheme.below (univ.erase z, 4), min (f d) h = min (e d) h) →
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase z, 4), g d = f d) ∧
      (∀ d, min (g d) h = min (e d) h) ∧ ∀ x ∈ X, g r ≤ g x

/-! ### The lifts of the reading layer -/

/-- An old cell lies below a pair in the reading layer exactly when it does in the profile
layer. -/
theorem castAdd_mem_below_readingTop_iff {Y : Finset (Fin 5) × ℕ} (e : Fin (scheme I).card) :
    Fin.castAdd _ e ∈ (readingTop I r X).toCellScheme.below Y ↔
      e ∈ (scheme I).toCellScheme.below Y := by
  rw [CellScheme.mem_below, CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]

/-- **Lifts below a pair not above `(univ, 4)`** are those of the profile layer. -/
theorem cappedLift_readingTop_iff {X' Y : Finset (Fin 5) × ℕ} (hXY : X' ≤ Y)
    (hY : ¬ ((univ : Finset (Fin 5)), 4) ≤ Y) :
    (readingTop I r X).rows.CappedLift hXY ↔ (scheme I).rows.CappedLift hXY := by
  have h := Scheme.isSourcePrefix_sheetLayer (scheme I) 4 (readingEntry I r X) (fun _ ↦ false)
    (fun _ ↦ ⊥) not_univ_four_le hY
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_castAdd]

/-- The faces of the reading layer are those of the amalgam. -/
theorem faces_readingTop :
    (readingTop I r X).toCellScheme.faces = I.amalgam.toCellScheme.faces :=
  I.faces_tower 2

/-- The graded faces of the reading layer are those of the amalgam. -/
theorem gradedFaces_readingTop :
    (readingTop I r X).toCellScheme.gradedFaces = I.amalgam.toCellScheme.gradedFaces := by
  unfold CellScheme.gradedFaces
  rw [faces_readingTop]

/-- **Lifts between graded faces off the ground set** are lifts of the amalgam. -/
theorem cappedLift_readingTop_old {X' Y : Finset (Fin 5) × ℕ}
    (hX : X' ∈ (readingTop I r X).toCellScheme.gradedFaces)
    (hY : Y ∈ (readingTop I r X).toCellScheme.gradedFaces) (h : X' ≤ Y) (hY1 : Y.1 ≠ univ) :
    (readingTop I r X).rows.CappedLift h :=
  (cappedLift_readingTop_iff h fun h' ↦ hY1 (univ_subset_iff.mp h'.1)).mpr
    ((cappedLift_scheme_old_iff h hY1).mpr
      (I.isBountiful (gradedFaces_readingTop (r := r) (X := X) ▸ hX)
        (gradedFaces_readingTop (r := r) (X := X) ▸ hY) h))

/-- **The lifts at the grades `j ≤ 3`**, from either coatom: those of the profile layer. -/
theorem cappedLift_readingTop_le_three {z : Fin 5}
    (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) {j : ℕ} (hj : j ≤ 3) :
    (readingTop I r X).rows.CappedLift (X := (univ.erase z, j))
      (Y := ((univ : Finset (Fin 5)), j)) ⟨erase_subset _ _, le_rfl⟩ := by
  have hY : ¬ ((univ : Finset (Fin 5)), 4) ≤ ((univ : Finset (Fin 5)), j) :=
    fun h ↦ absurd h.2 (by simp only; omega)
  exact (cappedLift_readingTop_iff _ hY).mpr ((cappedLift_top_iff (I := I) _ hY).mp
    (cappedLift_top_le_three hz hj))


/-- A cell of full scope and grade `4` of the reading layer: the reading mark of the labelling
constantly `⊥`. -/
theorem exists_gradedIndex_univ_four_readingTop (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) :
    ∃ t, (readingTop I r X).toCellScheme.gradedIndex t = ((univ : Finset (Fin 5)), 4) := by
  obtain ⟨j₁, -⟩ := exists_readingEntry_eq (g := fun _ ↦ ⊥) hgr hX
    (CellScheme.Rows.isLawfulBelow_const_bot _) fun _ _ ↦ le_rfl
  exact ⟨Fin.natAdd _ j₁, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _⟩

/-- **The lift at the grade `4`** of the reading layer, from the coatom `univ.erase z` into
`(univ, 4)`, from the two fill conditions (`TowerProfile.ReadingFillBot`,
`TowerProfile.ReadingFillPos`): the one-grade lift `CellScheme.Rows.cappedLift_of_ownerCappedLift`,
with the owner-capped lifts at `⊥` by the fill at `⊥` and a template at `⊥`
(`Scheme.exists_isLawfulBelow_sheetLayer`), and at the positive caps from the serving cells
(`CellScheme.Rows.hasOwnerCappedLifts_of_rows_short`) by the fill at the short caps and a template
(`Scheme.exists_extension_sheetLayer`).  No extension from a boundary is used. -/
theorem cappedLift_readingTop_four {z : Fin 5}
    (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4)
    (hbot : ReadingFillBot I r X z) (hpos : ReadingFillPos I r X z) :
    (readingTop I r X).rows.CappedLift (X := (univ.erase z, 4))
      (Y := ((univ : Finset (Fin 5)), 4)) ⟨erase_subset _ _, le_rfl⟩ := by
  classical
  have hcard : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hU : ¬ ((univ : Finset (Fin 5)), 4) ≤ (univ.erase z, 4) :=
    fun h ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h.1)
  have hε := readingEntry_mem (I := I) (r := r) (X := X)
  have hκ : ∀ e : Fin (scheme I).card → Label.{u}, (fun _ ↦ (⊥ : Label.{u})) e ∈
      (scheme I).fieldGrid 4 := fun _ ↦ bot_mem_grid _ _
  have hκr : Scheme.CapRespects (scheme I) 4 fun _ ↦ (⊥ : Label.{u}) := Scheme.capRespects_const ⊥
  -- a cell at the coatom
  obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq_tower 2 (X := (univ.erase z, 4))
    ⟨I.erase_mem_faces hz, by omega, by rw [hcard]⟩ (Seed.ne_univ_erase z)
  -- the old cells below the coatom
  have hold (e : (readingTop I r X).toCellScheme.below (univ.erase z, 4)) :
      ∃ e' : Fin (scheme I).card, Fin.castAdd _ e' = (e : Fin (readingTop I r X).card) ∧
        e' ∈ (scheme I).toCellScheme.below (univ.erase z, 4) := by
    obtain ⟨e', he'⟩ := Scheme.exists_castAdd_eq_sheetLayer (S := scheme I) (k := 4)
      (hS := not_univ_four_le) hU e.2
    exact ⟨e', he', (castAdd_mem_below_readingTop_iff e').mp (he' ▸ e.2)⟩
  refine CellScheme.Rows.cappedLift_of_ownerCappedLift (j := 3) (erase_subset _ _)
    ⟨Fin.castAdd _ (Fin.castAdd _ c), ?_⟩ (cappedLift_readingTop_le_three hz le_rfl)
    fun cap hcap ↦ ?_
  · rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd, hc]
  rcases eq_bot_or_bot_lt cap with rfl | hcbot
  · -- the cap `⊥`: the fill at `⊥` and a template
    intro p q hp _ _ o ho _ _
    have hp' := hp.min_const_of_isSelfVisible (hp.isSelfVisible_of_gradedIndex_eq ho)
    set f : Fin (scheme I).card → Label.{u} := fun e ↦
      CellScheme.Rows.extendBot (univ.erase z, 4) (fun d ↦ min (p d) (p o)) (Fin.castAdd _ e)
    have hf : (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun e ↦ f e :=
      (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4)
        (h := not_univ_four_le) hU).mp (CellScheme.Rows.isLawfulBelow_extendBot.mpr hp')
    obtain ⟨g, hg, hgf, hgr'⟩ := hbot f hf
    obtain ⟨j₀, hj₀⟩ := exists_readingEntry_eq hgr hX hg hgr'
    obtain ⟨w, hw, hwg, -⟩ := Scheme.exists_isLawfulBelow_sheetLayer (hS := not_univ_four_le)
      (σ := fun _ ↦ false) hε hκ hκr hj₀
    refine ⟨w, hw, fun e ↦ ?_, fun _ ↦ by simp⟩
    obtain ⟨e', he', hbe⟩ := hold e
    have hg4 : (scheme I).toCellScheme.grade e' ≤ 4 := hbe.2
    change w ⟨(e : Fin (readingTop I r X).card), _⟩ = _
    simp only [← he']
    rw [hwg e' hg4, hgf e' hbe]
    change CellScheme.Rows.extendBot _ _ _ = _
    rw [CellScheme.Rows.extendBot_of_mem _ ((castAdd_mem_below_readingTop_iff e').mpr hbe)]
    congr 2
    exact Subtype.ext he'
  · -- the positive caps: the serving cells, the fill at the short caps, and a template
    refine CellScheme.Rows.hasOwnerCappedLifts_of_rows_short (erase_subset _ _) hcbot hcap
      (exists_gradedIndex_univ_four_readingTop hgr hX) fun u hu ↦ ?_
    obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq_sheetLayer (S := scheme I) (k := 4)
      (hS := not_univ_four_le) hu
    refine ⟨Scheme.isConsistent_sheetLayer (hS := not_univ_four_le) isConsistent_scheme hε hκ
        hκr _,
      fun d ↦ (Scheme.isShort_ne_top_row_sheetLayer (hS := not_univ_four_le) hε hκ i _).1,
      fun d ↦ (Scheme.isShort_ne_top_row_sheetLayer (hS := not_univ_four_le) hε hκ i _).2,
      fun h hh hs hhb f hf _ hfS ↦ ?_⟩
    set f₀ : Fin (scheme I).card → Label.{u} := fun e ↦
      CellScheme.Rows.extendBot (univ.erase z, 4) f (Fin.castAdd _ e)
    have hf₀ : (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun e ↦ f₀ e :=
      (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4)
        (h := not_univ_four_le) hU).mp (CellScheme.Rows.isLawfulBelow_extendBot.mpr hf)
    have hagree (d : Fin (scheme I).card)
        (hd : d ∈ (scheme I).toCellScheme.below (univ.erase z, 4)) :
        min (f₀ d) h = min (readingEntry I r X i d) h := by
      have hd' := (castAdd_mem_below_readingTop_iff (r := r) (X := X) d).mpr hd
      have := hfS ⟨_, hd'⟩
      rw [CellScheme.Rows.rowBelow, Scheme.sheetLayer_row_natAdd] at this
      change min (CellScheme.Rows.extendBot _ f (Fin.castAdd _ d)) h = _
      rw [CellScheme.Rows.extendBot_of_mem f hd']
      convert this using 2
      exact (Scheme.sheetRow_castAdd i d).symm
    obtain ⟨g, hg, hgf, hga, hgr'⟩ := hpos _ (Scheme.markEntry_mem _ i) h hh hs hhb f₀ hf₀ hagree
    obtain ⟨j₀, hj₀⟩ := exists_readingEntry_eq hgr hX hg hgr'
    obtain ⟨w, hw, hwg, hwS⟩ := Scheme.exists_extension_sheetLayer (hS := not_univ_four_le)
      (σ := fun _ ↦ false) hε hκ hκr hh hs hhb (j := i) (fun d _ ↦ hga d) hj₀ (.inl rfl)
    refine ⟨w, hw, fun e ↦ ?_, fun d ↦ ?_⟩
    · obtain ⟨e', he', hbe⟩ := hold e
      have hg4 : (scheme I).toCellScheme.grade e' ≤ 4 := hbe.2
      change w ⟨(e : Fin (readingTop I r X).card), _⟩ = _
      simp only [← he']
      rw [hwg e' hg4, hgf e' hbe]
      change CellScheme.Rows.extendBot _ _ _ = _
      rw [CellScheme.Rows.extendBot_of_mem _ ((castAdd_mem_below_readingTop_iff e').mpr hbe)]
      congr 1
      exact Subtype.ext he'
    · rw [CellScheme.Rows.rowBelow, Scheme.sheetLayer_row_natAdd]
      exact hwS d


/-! ### Legality below the full grade -/

/-- **The reading layer is bountiful**, given the two fill conditions at both coatoms
(`CellScheme.Rows.isBountiful_of_coatoms`). -/
theorem isBountiful_readingTop (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4)
    (hbot : ∀ z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)),
      ReadingFillBot I r X z)
    (hpos : ∀ z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)),
      ReadingFillPos I r X z) :
    (readingTop I r X).rows.IsBountiful := by
  have hcard (z : Fin 5) : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hfull {z : Fin 5} (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
      (j : ℕ) (hj : j ≤ #(univ.erase z)) :
      (readingTop I r X).rows.CappedLift (X := (univ.erase z, j))
        (Y := ((univ : Finset (Fin 5)), j)) ⟨erase_subset _ _, le_rfl⟩ := by
    rw [hcard] at hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact cappedLift_readingTop_le_three hz (by omega)
    · exact cappedLift_readingTop_four hz hgr hX (hbot z hz) (hpos z hz)
  exact CellScheme.Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 4)
    (b := Fin.castSucc (Fin.last 3)) (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ I.subset_or_subset B (faces_readingTop (r := r) (X := X) ▸ hB) hne)
    (faces_readingTop (r := r) (X := X) ▸ I.erase_last_mem_faces)
    (faces_readingTop (r := r) (X := X) ▸ I.erase_castSucc_mem_faces)
    (fun _ _ hX' hY h hYne ↦ cappedLift_readingTop_old hX' hY h hYne)
    (hfull (by simp)) (hfull (by simp))

/-- Every cell of the reading layer has grade below `5`. -/
theorem grade_readingTop_lt (z : Fin (readingTop I r X).card) :
    (readingTop I r X).toCellScheme.grade z < 5 := by
  induction z using Fin.addCases with
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  | left z =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    induction z using Fin.addCases with
    | right j => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
    | left e =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      exact I.grade_tower_lt (by omega) e

/-- **Completeness below the full grade** of the reading layer: the cell at `(univ, 4)` is the
reading mark of the labelling constantly `⊥`. -/
theorem exists_gradedIndex_eq_readingTop (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) (X' : Finset (Fin 5) × ℕ)
    (hX' : X' ∈ (readingTop I r X).toCellScheme.gradedFaces) (hX2 : X'.2 < 5) :
    ∃ d, (readingTop I r X).toCellScheme.gradedIndex d = X' := by
  obtain ⟨B, j⟩ := X'
  have hgi (e : Fin (I.tower 2).card) :
      (readingTop I r X).toCellScheme.gradedIndex (Fin.castAdd _ (Fin.castAdd _ e)) =
        (I.tower 2).toCellScheme.gradedIndex e := by
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  by_cases hB : B = univ
  · subst hB
    have hj0 : 0 < j := hX'.2.1
    simp only at hX2
    rcases (show j ≤ 2 ∨ j = 3 ∨ j = 4 by omega) with hj | rfl | rfl
    · obtain ⟨t, ht⟩ := I.exists_gradedIndex_eq_univ_tower_of_le hj0 2 hj
      exact ⟨_, (hgi t).trans ht⟩
    · obtain ⟨i₀, -⟩ := exists_entry_eq (RankProfile.bot_mem_rankCat (I := I) 3)
      exact ⟨Fin.castAdd _ (Fin.natAdd _ i₀), by
        rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd]⟩
    · exact exists_gradedIndex_univ_four_readingTop hgr hX
  · obtain ⟨e, he⟩ := I.exists_gradedIndex_eq_tower 2
      (gradedFaces_readingTop (r := r) (X := X) ▸ hX') hB
    exact ⟨_, (hgi e).trans he⟩

/-- **The reading layer is legal below the full grade**, given the two fill conditions at both
coatoms. -/
theorem isLegalBelowFullGrade_readingTop (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4)
    (hbot : ∀ z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)),
      ReadingFillBot I r X z)
    (hpos : ∀ z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)),
      ReadingFillPos I r X z) :
    (readingTop I r X).IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_sheetLayer (hS := not_univ_four_le) isWellFormed_scheme
    (by omega) (by omega)
  isCoded := Scheme.isCoded_sheetLayer (hS := not_univ_four_le) isCoded_scheme readingEntry_mem
    fun _ ↦ bot_mem_grid _ _
  isConsistent := Scheme.isConsistent_sheetLayer (hS := not_univ_four_le) isConsistent_scheme
    readingEntry_mem (fun _ ↦ bot_mem_grid _ _) (Scheme.capRespects_const ⊥)
  isBountiful := isBountiful_readingTop hgr hX hbot hpos
  grade_lt := grade_readingTop_lt
  exists_gradedIndex_eq := exists_gradedIndex_eq_readingTop hgr hX


/-! ### The fill conditions are necessary -/

/-- Every cell of the reading layer lies below `(univ, 4)`. -/
theorem mem_below_univ_four_readingTop (z : Fin (readingTop I r X).card) :
    z ∈ (readingTop I r X).toCellScheme.below ((univ : Finset (Fin 5)), 4) :=
  ⟨subset_univ _, by
    have := grade_readingTop_lt z
    change (readingTop I r X).toCellScheme.grade z ≤ 4
    omega⟩

/-- **The tie of the reading layer**: every labelling lawful below `(univ, 4)` in the reading
layer labels each cell of `X` at least as `r` (`CellScheme.Rows.IsLawfulBelow.le_of_forall_reads`,
every cell of full scope and grade `4` reading `X` at least as `r`). -/
theorem le_of_isLawfulBelow_readingTop (hgr : (scheme I).toCellScheme.grade r = 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4)
    {w : Fin (readingTop I r X).card → Label.{u}}
    (hw : (readingTop I r X).rows.IsLawfulBelow (univ, 4) fun d ↦ w d) {x : Fin (scheme I).card}
    (hx : x ∈ X) : w (Fin.castAdd _ r) ≤ w (Fin.castAdd _ x) := by
  obtain ⟨t, ht⟩ := exists_gradedIndex_univ_four_readingTop hgr.le hX
  have hrb := Scheme.castAdd_mem_below_sheetLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
    (ε := readingEntry I r X) (σ := fun _ ↦ false) (κ := fun _ ↦ ⊥) hgr.le
  have hxb := Scheme.castAdd_mem_below_sheetLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
    (ε := readingEntry I r X) (σ := fun _ ↦ false) (κ := fun _ ↦ ⊥) (hX x hx)
  refine hw.le_of_forall_reads hrb hxb ht ?_ ?_ fun v hv ↦ ?_
  · rw [Scheme.appendFullCellsScheme_grade_castAdd, hgr]
    exact (congrArg Prod.snd ht).symm
  · rw [Scheme.appendFullCellsScheme_grade_castAdd, Scheme.appendFullCellsScheme_grade_castAdd,
      hgr]
    exact (hX x hx).trans le_rfl
  · rw [← Scheme.rowAt_of_mem, ← Scheme.rowAt_of_mem]
    exact rowAt_readingTop_le hgr.le hX hv hx

/-- A labelling lawful below `(univ, 4)` in the reading layer is, on the old cells, lawful below
`(univ, 4)` in the profile layer. -/
theorem isLawfulBelow_old_readingTop
    {w : (readingTop I r X).toCellScheme.below ((univ : Finset (Fin 5)), 4) → Label.{u}}
    (hw : (readingTop I r X).rows.IsLawfulBelow (univ, 4) w) :
    (scheme I).rows.IsLawfulBelow (univ, 4)
      fun d ↦ w ⟨Fin.castAdd _ d.1, mem_below_univ_four_readingTop _⟩ := by
  have h := (hw.isLawful (fun z ↦ mem_below_univ_four_readingTop z)).comap
    (Scheme.isLowerEmbedding_castAdd 4 _ _ not_univ_four_le)
  rw [Scheme.comap_rows_castAdd (h := not_univ_four_le)] at h
  exact h.isLawfulBelow _

/-- **The fill at `⊥` is necessary**: if the reading layer is legal below the full grade, the fill
at `⊥` holds from every coatom (the lift at `⊥` and the tie). -/
theorem readingFillBot_of_isLegal (hgr : (scheme I).toCellScheme.grade r = 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4)
    (hleg : (readingTop I r X).IsLegalBelowFullGrade) {z : Fin 5}
    (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
    ReadingFillBot I r X z := by
  classical
  intro f hf
  have hcard : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hU : ¬ ((univ : Finset (Fin 5)), 4) ≤ (univ.erase z, 4) :=
    fun h ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h.1)
  set v : Fin (readingTop I r X).card → Label.{u} := Fin.append f fun _ ↦ ⊥ with hv
  have hvf (d : Fin (scheme I).card) : v (Fin.castAdd _ d) = f d := Fin.append_left _ _ d
  have hvl : (readingTop I r X).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ v d :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4) (h := not_univ_four_le)
      hU).mpr (by simp only [hvf]; exact hf)
  have hl := hleg.isBountiful.cappedLift
    (gradedFaces_readingTop (r := r) (X := X) ▸ ⟨I.erase_mem_faces hz, by omega, by rw [hcard]⟩)
    ⟨hleg.isWellFormed.univ_mem_faces, by omega, by simp⟩
    (show ((univ.erase z, 4) : Finset (Fin 5) × ℕ) ≤ (univ, 4) from ⟨erase_subset _ _, le_rfl⟩)
  obtain ⟨q, hq, -, hqv⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp hl ⊥
    (isSelfVisible_bot 4) _ (fun _ ↦ ⊥) hvl (CellScheme.Rows.isLawfulBelow_const_bot _)
    fun _ ↦ by simp
  refine ⟨fun d ↦ q ⟨Fin.castAdd _ d, mem_below_univ_four_readingTop _⟩,
    isLawfulBelow_old_readingTop hq, fun d hd ↦ ?_, fun x hx ↦ ?_⟩
  · have := hqv ⟨Fin.castAdd _ d, (castAdd_mem_below_readingTop_iff d).mpr hd⟩
    exact this.trans (hvf d)
  · exact le_of_isLawfulBelow_readingTop (w := fun z ↦ q ⟨z, mem_below_univ_four_readingTop z⟩)
      hgr hX hq hx

/-- **The fill at the short positive caps is necessary**: if the reading layer is legal below the
full grade, the fill holds from every coatom along every reading mark (the lift at the ambient of
the cell of that mark, and the tie). -/
theorem readingFillPos_of_isLegal (hgr : (scheme I).toCellScheme.grade r = 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4)
    (hleg : (readingTop I r X).IsLegalBelowFullGrade) {z : Fin 5}
    (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
    ReadingFillPos I r X z := by
  classical
  intro e he h hh _ _ f hf hfe
  have hcard : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hU : ¬ ((univ : Finset (Fin 5)), 4) ≤ (univ.erase z, 4) :=
    fun h ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h.1)
  obtain ⟨j, hj⟩ := Scheme.exists_markEntry_eq he
  have hu : (readingTop I r X).toCellScheme.gradedIndex (Fin.natAdd _ j) = (univ, 4) :=
    Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  have hrowj (d : Fin (scheme I).card) :
      (readingTop I r X).rows.rowBelow (Fin.natAdd _ j) hu
        ⟨Fin.castAdd _ d, mem_below_univ_four_readingTop _⟩ = e d := by
    rw [CellScheme.Rows.rowBelow, Scheme.sheetLayer_row_natAdd, Scheme.sheetRow_castAdd, ← hj]
  set v : Fin (readingTop I r X).card → Label.{u} := Fin.append f fun _ ↦ ⊥ with hv
  have hvf (d : Fin (scheme I).card) : v (Fin.castAdd _ d) = f d := Fin.append_left _ _ d
  have hvl : (readingTop I r X).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ v d :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4) (h := not_univ_four_le)
      hU).mpr (by simp only [hvf]; exact hf)
  have hl := hleg.isBountiful.cappedLift
    (gradedFaces_readingTop (r := r) (X := X) ▸ ⟨I.erase_mem_faces hz, by omega, by rw [hcard]⟩)
    ⟨hleg.isWellFormed.univ_mem_faces, by omega, by simp⟩
    (show ((univ.erase z, 4) : Finset (Fin 5) × ℕ) ≤ (univ, 4) from ⟨erase_subset _ _, le_rfl⟩)
  have hS := CellScheme.Rows.isLawfulBelow_rowBelow hu
    (hleg.isConsistent (Fin.natAdd _ j))
  obtain ⟨q, hq, hqS, hqv⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp hl h hh _ _ hvl hS
    fun d ↦ by
      obtain ⟨d', hd', hbd⟩ : ∃ d' : Fin (scheme I).card,
          Fin.castAdd _ d' = (d : Fin (readingTop I r X).card) ∧
            d' ∈ (scheme I).toCellScheme.below (univ.erase z, 4) := by
        obtain ⟨d', hd'⟩ := Scheme.exists_castAdd_eq_sheetLayer (S := scheme I) (k := 4)
          (hS := not_univ_four_le) hU d.2
        exact ⟨d', hd', (castAdd_mem_below_readingTop_iff d').mp (hd' ▸ d.2)⟩
      have h1 := hrowj d'
      have h2 := hvf d'
      simp only [hd'] at h1 h2
      change min ((readingTop I r X).rows.rowBelow _ hu ⟨(d : Fin _), _⟩) h = min (v d) h
      rw [h1, h2, hfe d' hbd]
  refine ⟨fun d ↦ q ⟨Fin.castAdd _ d, mem_below_univ_four_readingTop _⟩,
    isLawfulBelow_old_readingTop hq, fun d hd ↦ ?_, fun d ↦ ?_, fun x hx ↦ ?_⟩
  · have := hqv ⟨Fin.castAdd _ d, (castAdd_mem_below_readingTop_iff d).mpr hd⟩
    exact this.trans (hvf d)
  · rw [hqS, hrowj]
  · exact le_of_isLawfulBelow_readingTop (w := fun z ↦ q ⟨z, mem_below_univ_four_readingTop z⟩)
      hgr hX hq hx

/-- **The reading layer is legal below the full grade exactly when the four fill conditions hold**
(at the cap `⊥` and at the short positive caps, from each coatom).  This is the seed-level form of
the raise requirement: the generalisation of the reading layer reduces to it. -/
theorem isLegalBelowFullGrade_readingTop_iff (hgr : (scheme I).toCellScheme.grade r = 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) :
    (readingTop I r X).IsLegalBelowFullGrade ↔
      (∀ z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)),
        ReadingFillBot I r X z) ∧
      ∀ z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)), ReadingFillPos I r X z :=
  ⟨fun hleg ↦ ⟨fun _ hz ↦ readingFillBot_of_isLegal hgr hX hleg hz,
      fun _ hz ↦ readingFillPos_of_isLegal hgr hX hleg hz⟩,
    fun ⟨hb, hp⟩ ↦ isLegalBelowFullGrade_readingTop hgr.le hX hb hp⟩

/-! ### The fills at an isolated marker on the left coatom -/

section Isolated

variable (hgr : (scheme I).toCellScheme.grade r = 4)
  (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
  (huniq : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
    (scheme I).toCellScheme.gradedIndex r ≤ (scheme I).toCellScheme.gradedIndex y → y = r)
  (hrow : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
    y ≠ r → (scheme I).rows.row r ⟨y, hy⟩ = ⊥)
  (hrr : (scheme I).rows.row r ⟨r, (scheme I).toCellScheme.mem_below_gradedIndex r⟩ ≠ ⊥)
  (hX3 : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 3)

include hgr hrC in
/-- An isolated cell of the grade `4` below the left coatom has the graded index of the coatom. -/
theorem gradedIndex_eq_of_isolated :
    (scheme I).toCellScheme.gradedIndex r = (univ.erase (Fin.last 4), 4) := by
  have h1 := isWellFormed_scheme (I := I).isWellFormed.grade_le_card r
  have hc : #(univ.erase (Fin.last 4) : Finset (Fin 5)) = 4 := by decide
  refine Prod.ext (eq_of_subset_of_card_le hrC.1 ?_) hgr
  rw [hc]
  change 4 ≤ #((scheme I).toCellScheme.scope r)
  omega

include hgr hrC huniq in
/-- A cell below `(univ, 4)` at or above an isolated cell is that cell. -/
theorem eq_of_le_gradedIndex_of_isolated {y : Fin (scheme I).card}
    (hy : (scheme I).toCellScheme.gradedIndex r ≤ (scheme I).toCellScheme.gradedIndex y) :
    y = r := by
  rw [gradedIndex_eq_of_isolated hgr hrC] at hy
  refine huniq y ⟨?_, (mem_below_univ_four y).2⟩ ?_
  · -- the scope contains the coatom and is not the ground set
    by_cases hl : Fin.last 4 ∈ (scheme I).toCellScheme.scope y
    · refine absurd ⟨fun a _ ↦ ?_, hy.2⟩ (not_univ_four_le y)
      by_cases ha : a = Fin.last 4
      · rw [ha]; exact hl
      · exact hy.1 (mem_erase.mpr ⟨ha, mem_univ _⟩)
    · exact fun a ha ↦ mem_erase.mpr ⟨fun h' ↦ hl (h' ▸ ha), mem_univ _⟩
  · rw [gradedIndex_eq_of_isolated hgr hrC]; exact hy

include hgr hrC huniq in
/-- A cell of the grade `4` inside the scope of an isolated cell is that cell. -/
theorem eq_of_grade_of_isolated {y : Fin (scheme I).card}
    (hgy : (scheme I).toCellScheme.grade y = (scheme I).toCellScheme.grade r)
    (hsy : (scheme I).toCellScheme.scope y ⊆ (scheme I).toCellScheme.scope r) : y = r := by
  have h1 := isWellFormed_scheme (I := I).isWellFormed.grade_le_card y
  have hsr : (scheme I).toCellScheme.scope r = univ.erase (Fin.last 4) :=
    congrArg Prod.fst (gradedIndex_eq_of_isolated hgr hrC)
  have hc : #(univ.erase (Fin.last 4) : Finset (Fin 5)) = 4 := by decide
  have heq : (scheme I).toCellScheme.scope y = (scheme I).toCellScheme.scope r := by
    refine eq_of_subset_of_card_le hsy ?_
    rw [hsr, hc]
    omega
  exact eq_of_le_gradedIndex_of_isolated hgr hrC huniq (Prod.mk_le_mk.mpr ⟨heq.ge, hgy.ge⟩)

include hgr hrC huniq hrow hrr in
/-- **Moving the isolated cell** in a labelling lawful below `(univ, 4)` of the profile layer. -/
theorem isLawfulBelow_update_of_isolated {w : Fin (scheme I).card → Label.{u}}
    (hw : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ w d) {v : Label.{u}}
    (hv : IsSelfVisible 4 v)
    (hbot : v ≠ ⊥ → ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), y ≠ r →
      w y = ⊥) :
    (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ Function.update w r v d := by
  classical
  refine CellScheme.Rows.IsLawfulBelow.update_isolated hw (mem_below_univ_four r)
    (fun y _ hy ↦ eq_of_le_gradedIndex_of_isolated hgr hrC huniq hy)
    (fun y _ hgy hsy ↦ eq_of_grade_of_isolated hgr hrC huniq hgy hsy) hrow hrr
    (by rw [hgr]; exact hv) fun hv0 y hy hyr ↦ hbot hv0 y
      (by rw [← gradedIndex_eq_of_isolated hgr hrC]; exact hy) hyr

include hgr hrC hrow in
/-- **The isolated cell, when not `⊥`, puts every other cell of the left coatom at `⊥`.** -/
theorem eq_bot_of_isolated_left {w : Fin (scheme I).card → Label.{u}}
    (hw : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d)
    (hwr : w r ≠ ⊥) {y : Fin (scheme I).card}
    (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) (hyr : y ≠ r) :
    w y = ⊥ :=
  hw.eq_bot_of_isolated hrC hrow hwr (by rw [gradedIndex_eq_of_isolated hgr hrC]; exact hy) hyr

/-- **Reading below the cap**: if `g` agrees with a reading mark `e` capped at `h` and `e` reads
`r` below `h`, then `g` reads every cell of `X` at least as `r`. -/
theorem reads_of_lt {e g : Fin (scheme I).card → Label.{u}} (he : e ∈ (scheme I).readingMarks 4 r X)
    {h : Label.{u}} (hlt : e r < h) (hag : ∀ d, min (g d) h = min (e d) h) :
    ∀ x ∈ X, g r ≤ g x := by
  intro x hx
  have hgr' : g r = e r := by
    have := hag r
    rw [min_eq_left hlt.le] at this
    rcases le_or_gt h (g r) with hle | hgt
    · rw [min_eq_right hle] at this; exact absurd this hlt.ne'
    · rwa [min_eq_left hgt.le] at this
  rw [hgr']
  calc e r = min (e r) h := (min_eq_left hlt.le).symm
    _ ≤ min (e x) h := min_le_min_right h (Scheme.le_of_mem_readingMarks he hx)
    _ = min (g x) h := (hag x).symm
    _ ≤ g x := min_le_left _ _

/-- The left coatom and the right coatom. -/
private theorem pair_left :
    Fin.last 4 ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)) := by simp

private theorem pair_right :
    Fin.castSucc (Fin.last 3) ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)) := by
  simp

include hgr hrC in
/-- The isolated cell is not below the right coatom. -/
theorem notMem_below_right_of_isolated :
    r ∉ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4) := fun h ↦ by
  have hsr : (scheme I).toCellScheme.scope r = univ.erase (Fin.last 4) :=
    congrArg Prod.fst (gradedIndex_eq_of_isolated hgr hrC)
  have := h.1 (hsr ▸ (by decide : Fin.castSucc (Fin.last 3) ∈ univ.erase (Fin.last 4)))
  simp at this

include hgr hrC huniq hrow hrr hX3 in
/-- **The fill at `⊥` from the left coatom**: a labelling with the isolated cell at `⊥` is filled
in the profile layer (`TowerProfile.exists_fill_four`); otherwise the given labelling `L` (lawful
below `(univ, 4)`, `⊥` at the other cells of the left coatom and `⊤` on `X`) with the isolated cell
moved to its label. -/
theorem readingFillBot_left {L : Fin (scheme I).card → Label.{u}}
    (hL : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ L d)
    (hLC : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), y ≠ r → L y = ⊥)
    (hLX : ∀ x ∈ X, L x = ⊤) : ReadingFillBot I r X (Fin.last 4) := by
  classical
  intro f hf
  by_cases hfr : f r = ⊥
  · obtain ⟨g, hg, hgf, -⟩ := exists_fill_four pair_left pair_right (by decide) hf
      (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot (isSelfVisible_bot 4)
      fun _ _ ↦ by simp
    exact ⟨g, hg, hgf, fun x _ ↦ by rw [hgf r hrC, hfr]; exact bot_le⟩
  · have hv : IsSelfVisible 4 (f r) := by
      have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hf).1 r hrC
      rwa [hgr] at this
    refine ⟨Function.update L r (f r),
      isLawfulBelow_update_of_isolated hgr hrC huniq hrow hrr hL hv fun _ ↦ hLC,
      fun d hd ↦ ?_, fun x hx ↦ ?_⟩
    · by_cases hdr : d = r
      · rw [hdr, Function.update_self]
      · rw [Function.update_of_ne hdr, hLC d hd hdr,
          eq_bot_of_isolated_left hgr hrC hrow hf hfr hd hdr]
    · have hxr : x ≠ r := fun h' ↦ by have := hX3 x hx; rw [h', hgr] at this; omega
      rw [Function.update_of_ne hxr, hLX x hx]
      exact le_top

include hgr hrC huniq hrow hrr in
/-- **The fill at `⊥` from the right coatom**: the fill in the profile layer, with the isolated
cell moved to `⊥`. -/
theorem readingFillBot_right : ReadingFillBot I r X (Fin.castSucc (Fin.last 3)) := by
  classical
  intro f hf
  obtain ⟨g, hg, hgf, -⟩ := exists_fill_four pair_right pair_left (by decide) hf
    (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot (isSelfVisible_bot 4) fun _ _ ↦ by simp
  refine ⟨Function.update g r ⊥, isLawfulBelow_update_of_isolated hgr hrC huniq hrow hrr hg
      (isSelfVisible_bot 4) fun h' ↦ absurd rfl h', fun d hd ↦ ?_, fun x _ ↦ ?_⟩
  · have hdr : d ≠ r := fun h' ↦ notMem_below_right_of_isolated hgr hrC (h' ▸ hd)
    rw [Function.update_of_ne hdr, hgf d hd]
  · rw [Function.update_self]; exact bot_le

include hgr hrC huniq hrow hrr hX3 in
/-- **The fill at the short positive caps from the right coatom**: the fill in the profile layer
along the reading mark; above the cap at `r`, the isolated cell is moved to the cap. -/
theorem readingFillPos_right : ReadingFillPos I r X (Fin.castSucc (Fin.last 3)) := by
  classical
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset r X he)).1
  obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four pair_right pair_left (by decide) hf hel hh hfe
  by_cases hre : h ≤ e r
  · have heC (y : Fin (scheme I).card)
        (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) (hyr : y ≠ r) :
        e y = ⊥ :=
      eq_bot_of_isolated_left hgr hrC hrow (hel.isLawfulBelow _) (hhb.trans_le hre).ne' hy hyr
    refine ⟨Function.update g r h, isLawfulBelow_update_of_isolated hgr hrC huniq hrow hrr hg hh
      fun _ y hy hyr ↦ ?_, fun d hd ↦ ?_, fun d ↦ ?_, fun x hx ↦ ?_⟩
    · have := hga y
      rw [heC y hy hyr, min_bot_left] at this
      exact (min_eq_bot.mp this).resolve_right hhb.ne'
    · have hdr : d ≠ r := fun h' ↦ notMem_below_right_of_isolated hgr hrC (h' ▸ hd)
      rw [Function.update_of_ne hdr, hgf d hd]
    · by_cases hdr : d = r
      · rw [hdr, Function.update_self, min_self, min_eq_right hre]
      · rw [Function.update_of_ne hdr]; exact hga d
    · have hxr : x ≠ r := fun h' ↦ by have := hX3 x hx; rw [h', hgr] at this; omega
      rw [Function.update_self, Function.update_of_ne hxr]
      have := hga x
      rw [min_eq_right (hre.trans (Scheme.le_of_mem_readingMarks he hx))] at this
      exact this ▸ min_le_left _ _
  · exact ⟨g, hg, hgf, hga, reads_of_lt he (not_le.mp hre) hga⟩

include hgr hrC hrow hX3 in
/-- **The fill at the short positive caps from the left coatom.**  Below the cap at `r`, the fill
in the profile layer; at or above it, the reading mark raised to `⊤` above the cap on the cells of
grade at most `3` (`Label.raise`, a witness bounded by the grade `3`), with the isolated cell at its
prescribed label, completed on the right coatom (`TowerProfile.exists_isLawfulBelow_four`): every
cell of `X` is then `⊤`. -/
theorem readingFillPos_left : ReadingFillPos I r X (Fin.last 4) := by
  classical
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset r X he)).1
  by_cases hre : h ≤ e r
  · have hfr : h ≤ f r := by
      have := hfe r hrC
      rw [min_eq_right hre] at this
      exact min_eq_right_iff.mp this
    have heC (y : Fin (scheme I).card)
        (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) (hyr : y ≠ r) :
        e y = ⊥ :=
      eq_bot_of_isolated_left hgr hrC hrow (hel.isLawfulBelow _) (hhb.trans_le hre).ne' hy hyr
    have hfC (y : Fin (scheme I).card)
        (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) (hyr : y ≠ r) :
        f y = ⊥ :=
      eq_bot_of_isolated_left hgr hrC hrow hf (hhb.trans_le hfr).ne' hy hyr
    set w : Fin (scheme I).card → Label.{u} := Function.update (fun d ↦ raise h (e d)) r (f r)
      with hwdef
    have hwf (d : Fin (scheme I).card)
        (hd : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) : w d = f d := by
      rw [hwdef]
      by_cases hdr : d = r
      · rw [hdr, Function.update_self]
      · rw [Function.update_of_ne hdr, heC d hd hdr, hfC d hd hdr, raise_bot hhb]
    have hr3 : r ∉ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) := fun h' ↦ by
      have := h'.2
      change (scheme I).toCellScheme.grade r ≤ 3 at this
      omega
    have hwU : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d :=
      (CellScheme.Rows.isLawfulBelow_congr hwf).mpr hf
    have hwV : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun d ↦ w d := by
      refine (CellScheme.Rows.isLawfulBelow_congr (w' := fun d ↦ raise h (e d)) fun d hd ↦ ?_).mpr
        ((hel.isLawfulBelow _).map_of_min_eq (hel.isLawfulBelow _) (fun d ↦ d.2.2)
          (isWitness_raise (K := 3) hh hhb) hhb.ne' fun d ↦ min_raise h (e d))
      exact Function.update_of_ne (fun hdr ↦ hr3 (by rw [← hdr]; exact hd)) _ _
    obtain ⟨g, hg, hgw, hga⟩ := exists_isLawfulBelow_four pair_left pair_right (by decide) hwU hwV
      hel hh fun d hd ↦ by
        rw [hwdef]
        by_cases hdr : d = r
        · rw [hdr, Function.update_self, min_eq_right hfr, min_eq_right hre]
        · rw [Function.update_of_ne hdr]; exact min_raise h (e d)
    refine ⟨g, hg, fun d hd ↦ (hgw d (.inl hd)).trans (hwf d hd),
      fun d ↦ hga d (mem_below_univ_four d), fun x hx ↦ ?_⟩
    have hxr : x ≠ r := fun h' ↦ by have := hX3 x hx; rw [h', hgr] at this; omega
    have hx3 : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
      ⟨subset_univ _, hX3 x hx⟩
    rw [hgw x (.inr hx3), hwdef, Function.update_of_ne hxr,
      show raise h (e x) = ⊤ from ite_eq_left (hre.trans (Scheme.le_of_mem_readingMarks he hx))]
    exact le_top
  · obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four pair_left pair_right (by decide) hf hel hh hfe
    exact ⟨g, hg, hgf, hga, reads_of_lt he (not_le.mp hre) hga⟩

include hgr hrC huniq hrow hrr hX3 in
/-- **The reading layer over a seed with an isolated marker on the left coatom is legal below the
full grade**, given a labelling `L` lawful below `(univ, 4)` that is `⊥` at the other cells of the
left coatom and `⊤` on `X`. -/
theorem isLegalBelowFullGrade_readingTop_of_isolated {L : Fin (scheme I).card → Label.{u}}
    (hL : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ L d)
    (hLC : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), y ≠ r → L y = ⊥)
    (hLX : ∀ x ∈ X, L x = ⊤) : (readingTop I r X).IsLegalBelowFullGrade := by
  have hpair (z : Fin 5) (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
      z = Fin.last 4 ∨ z = Fin.castSucc (Fin.last 3) := by
    simpa only [mem_insert, mem_singleton] using hz
  refine isLegalBelowFullGrade_readingTop hgr.le (fun x hx ↦ (hX3 x hx).trans (by omega))
    (fun z hz ↦ ?_) fun z hz ↦ ?_
  · rcases hpair z hz with rfl | rfl
    · exact readingFillBot_left hgr hrC huniq hrow hrr hX3 hL hLC hLX
    · exact readingFillBot_right hgr hrC huniq hrow hrr
  · rcases hpair z hz with rfl | rfl
    · exact readingFillPos_left hgr hrC hrow hX3
    · exact readingFillPos_right hgr hrC huniq hrow hrr hX3

end Isolated


/-! ### At `seedTR` -/

/-! ### The completion through the reading layer -/

variable (I r X) in
/-- The old cells of the reading layer. -/
noncomputable def readingEmbed : Fin I.amalgam.card ↪o Fin (readingTop I r X).card :=
  (embed3 I).trans (Fin.castAddOrderEmb _)

@[simp] theorem readingEmbed_apply (d : Fin I.amalgam.card) :
    readingEmbed I r X d = Fin.castAdd _ (embed3 I d) := rfl

/-- The old cells of the reading layer form a lower embedding of the amalgam. -/
theorem isLowerEmbedding_readingEmbed :
    I.amalgam.toCellScheme.IsLowerEmbedding (readingTop I r X).toCellScheme
      (readingEmbed I r X) :=
  (Scheme.isLowerEmbedding_castAdd 4 _ _ not_univ_four_le).comp isLowerEmbedding_embed3

/-- The rows of the reading layer pull back to those of the amalgam. -/
theorem comap_rows_readingEmbed :
    (readingTop I r X).rows.comap (isLowerEmbedding_readingEmbed (r := r) (X := X)) =
      I.amalgam.rows := by
  have h := CellScheme.Rows.comap_comap (readingTop I r X).rows
    (Scheme.isLowerEmbedding_castAdd 4 _ _ not_univ_four_le) isLowerEmbedding_embed3
  rw [Scheme.comap_rows_castAdd (h := not_univ_four_le), comap_rows_embed3] at h
  exact h.symm

/-- The old cells of the reading layer keep their graded indices. -/
theorem gradedIndex_readingEmbed (d : Fin I.amalgam.card) :
    (readingTop I r X).toCellScheme.gradedIndex (readingEmbed I r X d) =
      I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (gradedIndex_embed3 d)

/-- Every cell of the reading layer of scope other than the ground set is old. -/
theorem mem_range_readingEmbed (z : Fin (readingTop I r X).card)
    (hz : (readingTop I r X).toCellScheme.scope z ≠ univ) :
    z ∈ Set.range (readingEmbed I r X) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  | left z =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hz
    obtain ⟨d, rfl⟩ := mem_range_embed3 z hz
    exact ⟨d, rfl⟩

/-- **A reading labelling of the profile layer extends through the reading layer**, unchanged at
the old cells: by the template of its orbit code, at `⊥` (`Scheme.exists_isLawfulBelow_sheetLayer`).
-/
theorem exists_isLawful_readingTop (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) {L : Fin (scheme I).card → Label.{u}}
    (hL : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ L d) (hLr : ∀ x ∈ X, L r ≤ L x) :
    ∃ q : Fin (readingTop I r X).card → Label.{u}, (readingTop I r X).rows.IsLawful q ∧
      ∀ d, q (Fin.castAdd _ d) = L d := by
  obtain ⟨j₀, hj₀⟩ := exists_readingEntry_eq hgr hX hL hLr
  obtain ⟨w, hw, hwL, -⟩ := Scheme.exists_isLawfulBelow_sheetLayer (hS := not_univ_four_le)
    (σ := fun _ ↦ false) readingEntry_mem (fun _ ↦ bot_mem_grid _ _) (Scheme.capRespects_const ⊥)
    hj₀
  have hall (z : Fin (readingTop I r X).card) :
      z ∈ (readingTop I r X).toCellScheme.below (univ, 4) :=
    ⟨subset_univ _, by
      have := grade_readingTop_lt z
      change (readingTop I r X).toCellScheme.grade z ≤ 4
      omega⟩
  exact ⟨fun z ↦ w ⟨z, hall z⟩, hw.isLawful hall, fun d ↦ hwL d (mem_below_univ_four d).2⟩

variable (I r X) in
/-- **The completion below the full grade through the reading layer**, given its legality and a
reading labelling of the profile layer that is the glued labelling on the old cells. -/
noncomputable def readingCompletion (hleg : (readingTop I r X).IsLegalBelowFullGrade)
    (hgr : (scheme I).toCellScheme.grade r ≤ 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) (L : Fin (scheme I).card → Label.{u})
    (hL : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ L d) (hLr : ∀ x ∈ X, L r ≤ L x)
    (hLa : ∀ d, L (embed3 I d) = I.amalgam.label d) : CompletionBelowFullGrade I where
  scheme := readingTop I r X
  embed := readingEmbed I r X
  isLowerEmbedding := isLowerEmbedding_readingEmbed
  scope_embed d := congrArg Prod.fst (gradedIndex_readingEmbed d)
  comap_rows := comap_rows_readingEmbed
  mem_range_embed := mem_range_readingEmbed
  faces_eq := faces_readingTop
  isLegalBelowFullGrade := hleg
  label := (exists_isLawful_readingTop hgr hX hL hLr).choose
  isLawful := (exists_isLawful_readingTop hgr hX hL hLr).choose_spec.1
  label_embed d := ((exists_isLawful_readingTop hgr hX hL hLr).choose_spec.2 _).trans (hLa d)

/-- **The glued labelling on the profile layer**: for a seed whose left coatom type is labelled `⊥`
off the cell `a`, the labelling of the completion (`TowerProfile.exists_isLawful_top`) read on the
profile layer is lawful below `(univ, 4)`, `⊥` at the cells of the left coatom other than the cell
of `a`, and at the cell of a cell `z` of the right type its label there. -/
theorem exists_glued {a : Fin I.left.card} (ha : ∀ z, z ≠ a → I.left.label z = ⊥)
    (zR : Fin I.right.card) :
    ∃ L : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ L d) ∧
      (∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        y ≠ leftCell I a → L y = ⊥) ∧
      L (embed3 I (StageType.faceCell I.restrictFace_right zR)) = I.right.label zR ∧
      ∀ d, L (embed3 I d) = I.amalgam.label d := by
  obtain ⟨q, hq, hqe⟩ := exists_isLawful_top (I := I)
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  have hold (d : Fin I.amalgam.card) :
      q (Fin.castAdd _ (embed3 I d)) = I.amalgam.label d := hqe d
  refine ⟨fun d ↦ q (Fin.castAdd _ d), hL.isLawfulBelow _, fun y hy hyr ↦ ?_, ?_, hold⟩
  · obtain ⟨z, rfl⟩ := exists_leftCell_eq (I := I) fun h' ↦ (notMem_erase _ _) (hy.1 h')
    have hz : z ≠ a := fun h' ↦ hyr (by rw [h'])
    change q (Fin.castAdd _ (embed3 I (StageType.faceCell I.restrictFace_left z))) = ⊥
    rw [hold, StageType.label_faceCell]
    exact ha z hz
  · change q (Fin.castAdd _ (embed3 I (StageType.faceCell I.restrictFace_right zR))) = _
    rw [hold, StageType.label_faceCell]

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- The isolation of the apex of `TL` at `seedTR` (`TowerProfile.isolated_of_left`). -/
theorem isolated_seedTR (α : Ordinal.{u}) :
    (scheme (seedTR α)).toCellScheme.grade (leftCell (seedTR α) (apexTL α)) = 4 ∧
      leftCell (seedTR α) (apexTL α) ∈
        (scheme (seedTR α)).toCellScheme.below (univ.erase (Fin.last 4), 4) ∧
      (∀ y ∈ (scheme (seedTR α)).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme (seedTR α)).toCellScheme.gradedIndex (leftCell (seedTR α) (apexTL α)) ≤
          (scheme (seedTR α)).toCellScheme.gradedIndex y → y = leftCell (seedTR α) (apexTL α)) ∧
      (∀ y (hy : y ∈ (scheme (seedTR α)).toCellScheme.below
          ((scheme (seedTR α)).toCellScheme.gradedIndex (leftCell (seedTR α) (apexTL α)))),
        y ≠ leftCell (seedTR α) (apexTL α) →
          (scheme (seedTR α)).rows.row (leftCell (seedTR α) (apexTL α)) ⟨y, hy⟩ = ⊥) ∧
      (scheme (seedTR α)).rows.row (leftCell (seedTR α) (apexTL α))
        ⟨leftCell (seedTR α) (apexTL α), (scheme (seedTR α)).toCellScheme.mem_below_gradedIndex _⟩
          ≠ ⊥ :=
  isolated_of_left (I := seedTR α) (a := apexTL α)
    (StageType.addApex_gradedIndex_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))
    (fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := TL₀ α) isLegalBelowFullGrade_SL
      (by omega) hz)
    (fun _ hz ↦ StageType.rowAt_addApex_last_of_ne (t := TL₀ α) isLegalBelowFullGrade_SL
      (by omega) (fun _ ↦ rfl) hz)
    (StageType.rowAt_addApex_last_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- The glued labelling at `seedTR`: `⊥` at the left coatom off the apex of `TL`, `⊤` at the new
top. -/
theorem exists_glued_seedTR (α : Ordinal.{u}) :
    ∃ L : Fin (scheme (seedTR α)).card → Label.{u},
      (scheme (seedTR α)).rows.IsLawfulBelow (univ, 4) (fun d ↦ L d) ∧
      (∀ y ∈ (scheme (seedTR α)).toCellScheme.below (univ.erase (Fin.last 4), 4),
        y ≠ leftCell (seedTR α) (apexTL α) → L y = ⊥) ∧
      L (newTop α) = ⊤ ∧ (∀ d, L (embed3 (seedTR α) d) = (seedTR α).amalgam.label d) := by
  have ha (z : Fin (seedTR α).left.card) (hz : z ≠ apexTL α) : (seedTR α).left.label z = ⊥ := by
    change (TL α).label z = ⊥
    change Fin ((TL₀ α).card + 1) at z
    induction z using Fin.lastCases with
    | last => exact absurd rfl hz
    | cast d =>
      exact StageType.addApex_label_castSucc (t := TL₀ α) isLegalBelowFullGrade_SL (by omega) d
  obtain ⟨L, hL, hLC, hLx, hLa⟩ := exists_glued ha
    (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
  refine ⟨L, hL, hLC, ?_, hLa⟩
  refine hLx.trans ?_
  change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
  simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
    TwoFaceLiftCounterexample.cellGrade]

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- **The reading layer at `seedTR` is legal below the full grade**: the restricted layer at the
grade `4` whose cells are the reading marks of the apex of `TL` (the marker) and the new top (one
cell per entry of the catalogue reading the new top at least as the marker, and no other), over the
profile layer of `seedTR`.  Bountiful by the lifts from the two coatoms
(`TowerProfile.isLegalBelowFullGrade_readingTop_of_isolated`); no extension from a boundary at the
grade `4` is used. -/
theorem isLegalBelowFullGrade_readingTop_seedTR (α : Ordinal.{u}) :
    (readingTop (seedTR α) (leftCell (seedTR α) (apexTL α)) {newTop α}).IsLegalBelowFullGrade := by
  obtain ⟨hg, hrC, huniq, hrow, hrr⟩ := isolated_seedTR α
  obtain ⟨L, hL, hLC, hLx, -⟩ := exists_glued_seedTR α
  exact isLegalBelowFullGrade_readingTop_of_isolated hg hrC huniq hrow hrr
    (fun x hx ↦ by rw [mem_singleton.mp hx, grade_newTop]; omega) hL hLC
    fun x hx ↦ by rw [mem_singleton.mp hx]; exact hLx

open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- **The reading at `seedTR`**: every cell of full scope and grade `4` of the reading layer reads
the new top at least as the apex of `TL`. -/
theorem rowAt_readingTop_seedTR_le (α : Ordinal.{u})
    {u : Fin (readingTop (seedTR α) (leftCell (seedTR α) (apexTL α)) {newTop α}).card}
    (hu : (readingTop (seedTR α) (leftCell (seedTR α) (apexTL α))
      {newTop α}).toCellScheme.gradedIndex u = (univ, 4)) :
    (readingTop (seedTR α) (leftCell (seedTR α) (apexTL α)) {newTop α}).rowAt u
        (Fin.castAdd _ (leftCell (seedTR α) (apexTL α))) ≤
      (readingTop (seedTR α) (leftCell (seedTR α) (apexTL α)) {newTop α}).rowAt u
        (Fin.castAdd _ (newTop α)) :=
  rowAt_readingTop_le (isolated_seedTR α).1.le
    (fun x hx ↦ by rw [mem_singleton.mp hx, grade_newTop]; omega) hu (mem_singleton_self _)


open TwoFaceLiftExistsCounterexample TopReadingApexExample in
/-- **The completion of `seedTR` through the reading layer**: legal below the full grade, with the
glued labelling extended, and every cell of full scope and grade `4` reading the new top at least
as the apex of `TL` (`TowerProfile.rowAt_readingTop_seedTR_le`). -/
theorem exists_readingCompletion_seedTR (α : Ordinal.{u}) :
    ∃ F : CompletionBelowFullGrade (seedTR α),
      F.scheme = readingTop (seedTR α) (leftCell (seedTR α) (apexTL α)) {newTop α} := by
  obtain ⟨L, hL, -, hLx, hLa⟩ := exists_glued_seedTR α
  have hg := (isolated_seedTR α).1
  exact ⟨readingCompletion (seedTR α) _ _ (isLegalBelowFullGrade_readingTop_seedTR α) hg.le
    (fun x hx ↦ by rw [mem_singleton.mp hx, grade_newTop]; omega) L hL
    (fun x hx ↦ by rw [mem_singleton.mp hx, hLx]; exact le_top) hLa, rfl⟩


/-- **The reading layer of an isolated left marker and new tops of the right type**: for a seed
whose left coatom type has a cell `a` with an isolated cell in the profile layer and is labelled
`⊥` off `a`, and every set `Z` of cells of the right type labelled `⊤` of grade at most `3`, the
reading layer of the cell of `a` and the cells of `Z` is legal below the full grade. -/
theorem isLegalBelowFullGrade_readingTop_of_left {a : Fin I.left.card}
    (hg : (scheme I).toCellScheme.grade (leftCell I a) = 4)
    (hrC : leftCell I a ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (huniq : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.gradedIndex (leftCell I a) ≤ (scheme I).toCellScheme.gradedIndex y →
        y = leftCell I a)
    (hrow : ∀ y (hy : y ∈ (scheme I).toCellScheme.below
        ((scheme I).toCellScheme.gradedIndex (leftCell I a))),
      y ≠ leftCell I a → (scheme I).rows.row (leftCell I a) ⟨y, hy⟩ = ⊥)
    (hrr : (scheme I).rows.row (leftCell I a)
      ⟨leftCell I a, (scheme I).toCellScheme.mem_below_gradedIndex _⟩ ≠ ⊥)
    (ha : ∀ z, z ≠ a → I.left.label z = ⊥) (Z : Finset (Fin I.right.card))
    (hZ : ∀ z ∈ Z, I.right.label z = ⊤ ∧ I.right.toCellScheme.grade z ≤ 3) :
    (readingTop I (leftCell I a)
      (Z.image fun z ↦ embed3 I
        (StageType.faceCell I.restrictFace_right z))).IsLegalBelowFullGrade := by
  obtain ⟨q, hq, hqe⟩ := exists_isLawful_top (I := I)
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  have hold (d : Fin I.amalgam.card) :
      q (Fin.castAdd _ (embed3 I d)) = I.amalgam.label d := hqe d
  refine isLegalBelowFullGrade_readingTop_of_isolated hg hrC huniq hrow hrr (fun x hx ↦ ?_)
    (L := fun d ↦ q (Fin.castAdd _ d)) (hL.isLawfulBelow _) (fun y hy hyr ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    have h2 := congrArg Prod.snd (gradedIndex_embed3 (I := I)
      (StageType.faceCell I.restrictFace_right z))
    simp only [CellScheme.gradedIndex_snd] at h2
    rw [h2, StageType.grade_faceCell]
    exact (hZ z hz).2
  · obtain ⟨z, rfl⟩ := exists_leftCell_eq (I := I) fun h' ↦ (notMem_erase _ _) (hy.1 h')
    have hz : z ≠ a := fun h' ↦ hyr (by rw [h'])
    change q (Fin.castAdd _ (embed3 I (StageType.faceCell I.restrictFace_left z))) = ⊥
    rw [hold, StageType.label_faceCell]
    exact ha z hz
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [hold, StageType.label_faceCell]
    exact (hZ z hz).1

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample in
/-- **Every donor over `TL`**: for every seed whose left coatom type is `TL` and whose right coatom
type `tb` is any legal type over the face of `T5`, and every set `Z` of cells of `tb` labelled `⊤`
of grade at most `3` (new tops), the reading layer of the apex of `TL` and the cells of `Z` is legal
below the full grade (and every cell of full scope and grade `4` reads each of them at least as
the apex, `TowerProfile.rowAt_readingTop_le`). -/
theorem isLegalBelowFullGrade_readingTop_TL {tb : StageType.{u} α 4} (hlb : tb.IsLegal)
    (hpb : StageType.restrictFace (Coatom.face 3) tb = some (faceT5 α)) (Z : Finset (Fin tb.card))
    (hZ : ∀ z ∈ Z, tb.label z = ⊤ ∧ tb.toCellScheme.grade z ≤ 3) :
    (readingTop (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)
      (leftCell _ (apexTL α))
      (Z.image fun z ↦ embed3 (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)
        (StageType.faceCell (Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α)
          hpb).restrictFace_right z))).IsLegalBelowFullGrade := by
  obtain ⟨hg, hrC, huniq, hrow, hrr⟩ :=
    isolated_of_left (I := Seed.ofCoatoms (isLegal_TL α) hlb (restrictFace_TL α) hpb)
      (a := apexTL α)
      (StageType.addApex_gradedIndex_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))
      (fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := TL₀ α) isLegalBelowFullGrade_SL
        (by omega) hz)
      (fun _ hz ↦ StageType.rowAt_addApex_last_of_ne (t := TL₀ α) isLegalBelowFullGrade_SL
        (by omega) (fun _ ↦ rfl) hz)
      (StageType.rowAt_addApex_last_last (t := TL₀ α) isLegalBelowFullGrade_SL (by omega))
  refine isLegalBelowFullGrade_readingTop_of_left hg hrC huniq hrow hrr (fun z hz ↦ ?_) Z hZ
  change (TL α).label z = ⊥
  change Fin ((TL₀ α).card + 1) at z
  induction z using Fin.lastCases with
  | last => exact absurd rfl hz
  | cast d =>
    exact StageType.addApex_label_castSucc (t := TL₀ α) isLegalBelowFullGrade_SL (by omega) d

end TowerProfile

end VaughtConjecture
