/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerTwoValued

/-!
# The fills of the reading layer and the ties of the common face

Roadmap, Layer 3 ((R3) of the table of 3.4).

The four fill conditions of the reading layer (`TowerProfile.isLegalBelowFullGrade_readingTop_iff`)
against the ties of the common face, at markers whose row reads cells strictly between `⊥` and
itself.

* **A failing fill** (`TowerProfile.not_readingFillBot_left_of_inversion`,
  `TowerProfile.not_isLegalBelowFullGrade_readingTop_of_inversion`, compiled in this repository
  (theorem named)): if a cell `x ∈ X` reads two cells `y₁`, `y₂` of the left coatom with `y₁` at
  most as `y₂` (the second of grade at most the first), and a labelling `f` lawful below the left
  coatom inverts them below its value at the marker (`f y₂ < f y₁ ≤ f r`), the fill at `⊥` from the
  left coatom fails at `f`, and the reading layer is not legal.  This is the seed-level form of the
  refutation schema `StageType.not_raisesNewTops_of_row_le`; no instance at five points is
  compiled here.
* **A marker that keeps the tie excludes it** (`TowerProfile.le_of_row_le_marker`, compiled): if
  the row of the marker reads `y₁` at most as `y₂`, every lawful `f` with `f y₁ ≤ f r` has
  `f y₁ ≤ f y₂`.
* **The fill at `⊥` from the left coatom when the marker reads the common face as `⊥`**
  (`TowerProfile.exists_glue_four`, `TowerProfile.readingFillBot_left_of_face_bot`,
  `TowerProfile.readingFillBot_left_of_left`, compiled): the given labelling is `⊥` on the common
  face and is glued to a labelling `⊤` on `X`; no condition on the other readings of the marker.
* **A proper-labelled marker** (`TopReadingApexExample.threeType`,
  `TopReadingApexExample.seedThree`,
  `TopReadingApexExample.rowAt_threeType_three`, `TopReadingApexExample.readingFills_seedThree`,
  compiled): the type `S` labelled `3` at its live cells of grade at most `2`, with the apex; the
  apex reads the cell `{3}` at the code of `3`, strictly between `⊥` and its reading of itself.
  At the seed with `rightType`, three of the four fills hold: at `⊥` from the left coatom (the
  apex reads the common face as `⊥`) and both fills from the right coatom
  (`TowerProfile.readingFillBot_right_of_unique`, `TowerProfile.readingFillPos_right_of_unique`).
  **Open**: the fill at the short positive caps from the left coatom.
* **That fill outside the band** (`TowerProfile.exists_fillPos_left_of_noBand`,
  `TowerProfile.readingFillPos_left_of_noBand`, compiled): for a reading mark `e`, a cap `h` at or
  below `e r` and `f` agreeing with `e` capped at `h`, if `f` has no value in the band `[h, f r)` at
  the cells of the left coatom of grade at most `3`, the fill exists: the grade-`3` part of `f` is
  lifted along the mark raised above `h`, capped at `f r`, and completed on the right coatom.  At
  `seedThree` this decides every case but the band: a labelling `f` with a left cell of grade `1`
  or `2` (the cells labelled `3`) valued in `[h, f r)`.  There the fill needs a labelling lawful
  below `(univ, 3)` equal to `f` on the left coatom, at least `f r` on `X`, and agreeing with `e`
  capped at `h`: a union of the two coatoms at the grade `3` capped at `h` along the arbitrary
  ambient `e`.  The profile layer gives the union at the cap `⊥`
  (`TowerProfile.exists_extension_bot`) and at positive caps along its own rows
  (`TowerProfile.extendsFromBoundary_row`), not along an arbitrary ambient.
* **The band reduces to servers** (`TowerProfile.not_exists_fill_of_noServer`,
  `TowerProfile.not_readingFillPos_left_of_noServer`, `TowerProfile.exists_server_of_lt`,
  compiled): in the band (`f y < f r` at a left cell `y` of grade at most that of `x ∈ X`), a fill
  needs a **server**: a cell `u` of graded index `(univ, grade x)` with `h ≤ e u` whose row reads
  `x` strictly above `y`.  Without one the fill fails (availability at `x`, locality at `u`).
  A mark
  with `e y < e x` always has one (its own availability at `x`); so a failure needs a mark with
  `e x ≤ e y`, low at every cell of `(univ, grade x)` ordering `y` below `x`.  So the union along
  an arbitrary ambient fails at any such mark, and the band case at `seedThree` is decided by the
  existence of such a mark (not decided here).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {r : Fin (scheme I).card}
  {X : Finset (Fin (scheme I).card)}

/-! ### A failing fill: an inversion under a tie of a new top -/

/-- **The fill at `⊥` from the left coatom fails at an inversion under a tie.**  Let `f` be lawful
below the left coatom, `x ∈ X` a cell whose row reads two cells `y₁`, `y₂` of the left coatom
(the second of grade at most the first) with `y₁` at most as `y₂`, and suppose `f` inverts them
below its value at the marker: `f y₂ < f y₁ ≤ f r`.  Then no fill at `⊥` extends `f`: a fill reads
`x` at least as `r`, so at least as `f y₁`, and locality at `x` puts `y₁` at most at `y₂`. -/
theorem not_readingFillBot_left_of_inversion {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {x : Fin (scheme I).card} (hx : x ∈ X) {y₁ y₂ : Fin (scheme I).card}
    (hy₁ : y₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hy₂ : y₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hC₁ : y₁ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hC₂ : y₂ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hrow : (scheme I).rows.row x ⟨y₁, hy₁⟩ ≤ (scheme I).rows.row x ⟨y₂, hy₂⟩)
    (hg : (scheme I).toCellScheme.grade y₂ ≤ (scheme I).toCellScheme.grade y₁)
    (hinv : f y₂ < f y₁) (hfr : f y₁ ≤ f r) : ¬ ReadingFillBot I r X (Fin.last 4) := by
  intro hfill
  obtain ⟨g, hg', hgf, hgr⟩ := hfill f hf
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hg'
  have h := (hloc x (mem_below_univ_four x)).le_of_le (d := ⟨y₁, hy₁⟩) (d' := ⟨y₂, hy₂⟩) hrow hg
  change min (g y₁) (g x) ≤ min (g y₂) (g x) at h
  rw [hgf y₁ hC₁, hgf y₂ hC₂] at h
  have hx' : f y₁ ≤ g x := hfr.trans ((hgf r hrC).symm.trans_le (hgr x hx))
  rw [min_eq_left hx'] at h
  exact absurd (h.trans (min_le_left _ _)) (not_le.mpr hinv)

/-- **The reading layer is not legal at an inversion under a tie**
(`TowerProfile.not_readingFillBot_left_of_inversion`,
`TowerProfile.isLegalBelowFullGrade_readingTop_iff`). -/
theorem not_isLegalBelowFullGrade_readingTop_of_inversion
    (hgr : (scheme I).toCellScheme.grade r = 4)
    (hX : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 4) {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {x : Fin (scheme I).card} (hx : x ∈ X) {y₁ y₂ : Fin (scheme I).card}
    (hy₁ : y₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hy₂ : y₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex x))
    (hC₁ : y₁ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hC₂ : y₂ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hrow : (scheme I).rows.row x ⟨y₁, hy₁⟩ ≤ (scheme I).rows.row x ⟨y₂, hy₂⟩)
    (hg : (scheme I).toCellScheme.grade y₂ ≤ (scheme I).toCellScheme.grade y₁)
    (hinv : f y₂ < f y₁) (hfr : f y₁ ≤ f r) : ¬ (readingTop I r X).IsLegalBelowFullGrade :=
  fun hleg ↦ not_readingFillBot_left_of_inversion hf hrC hx hy₁ hy₂ hC₁ hC₂ hrow hg hinv hfr
    (((isLegalBelowFullGrade_readingTop_iff hgr hX).mp hleg).1 _ (by simp))

/-- **A marker whose row keeps the tie excludes the inversion**: if the row of the marker reads
`y₁` at most as `y₂` (the second of grade at most the first, both below the marker), then every
labelling lawful below the left coatom with `f y₁ ≤ f r` has `f y₁ ≤ f y₂` (locality at the marker).
So `TowerProfile.not_readingFillBot_left_of_inversion` never applies to a tie that the row of the
marker keeps. -/
theorem le_of_row_le_marker {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {y₁ y₂ : Fin (scheme I).card}
    (hy₁ : y₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hy₂ : y₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hrow : (scheme I).rows.row r ⟨y₁, hy₁⟩ ≤ (scheme I).rows.row r ⟨y₂, hy₂⟩)
    (hg : (scheme I).toCellScheme.grade y₂ ≤ (scheme I).toCellScheme.grade y₁)
    (hfr : f y₁ ≤ f r) : f y₁ ≤ f y₂ := by
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  have h := (hloc r hrC).le_of_le (d := ⟨y₁, hy₁⟩) (d' := ⟨y₂, hy₂⟩) hrow hg
  change min (f y₁) (f r) ≤ min (f y₂) (f r) at h
  rw [min_eq_left hfr] at h
  exact h.trans (min_le_left _ _)

/-! ### The fill at the short caps from the left coatom, outside the band -/

/-- **The fill at the short caps from the left coatom, outside the band.**  Let `e` be a reading
mark, `h` a short positive cap at or below `e r`, and `f` lawful below the left coatom agreeing
with `e` capped at `h`.  If `f` has no value in the band `[h, f r)` at the cells of the left
coatom of grade at most `3`, the fill exists: the given labelling at the grade `3` is lifted to
`(univ, 3)` along the mark raised above `h` (`Label.raise`), capped at `f r`
(`TowerProfile.cappedLift_scheme_three`), so the cells of `X` are at least `f r`, and completed on
the right coatom along the mark (`TowerProfile.exists_isLawfulBelow_four`). -/
theorem exists_fillPos_left_of_noBand (hgr : (scheme I).toCellScheme.grade r = 4)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hX3 : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 3)
    {e : Fin (scheme I).card → Label.{u}} (he : e ∈ (scheme I).readingMarks 4 r X)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hhb : ⊥ < h)
    {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hfe : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      min (f d) h = min (e d) h) (hre : h ≤ e r)
    (hband : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 3),
      h ≤ f d → f r ≤ f d) :
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), g d = f d) ∧
      (∀ d, min (g d) h = min (e d) h) ∧ ∀ x ∈ X, g r ≤ g x := by
  classical
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset r X he)).1
  set v := f r with hvdef
  have hfr : h ≤ v := by
    have := hfe r hrC
    rw [min_eq_right hre] at this
    exact min_eq_right_iff.mp this
  have hv : IsSelfVisible 4 v := by
    have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hf).1 r hrC
    rwa [hgr] at this
  -- the mark raised above `h`, below `(univ, 3)`
  have hq : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
      fun d ↦ raise h (e d) :=
    (hel.isLawfulBelow _).map_of_min_eq (hel.isLawfulBelow _) (fun d ↦ d.2.2)
      (isWitness_raise (K := 3) hh hhb) hhb.ne' fun d ↦ min_raise h (e d)
  have hfC3 : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 3) fun d ↦ f d :=
    hf.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩
  -- the lift at the grade `3`, capped at `v`
  obtain ⟨w₃, hw₃, hw₃q, hw₃f⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists _).mp
    (cappedLift_scheme_three (I := I) (x := Fin.last 4) (by simp)) v (hv.mono (by omega))
    (fun d ↦ f d) (fun d ↦ raise h (e d)) hfC3 hq fun d ↦ by
      change min (raise h (e d)) v = min (f d) v
      have hfd := hfe d ⟨d.2.1, d.2.2.trans (by omega)⟩
      by_cases hed : h ≤ e (d : Fin (scheme I).card)
      · rw [show raise h (e d) = ⊤ from ite_eq_left hed, min_top_left]
        have hfh : h ≤ f d := by
          rw [min_eq_right hed] at hfd
          exact min_eq_right_iff.mp hfd
        exact (min_eq_right (hband d d.2 hfh)).symm
      · have hlt := not_le.mp hed
        rw [show raise h (e d) = e d from ite_eq_right hed]
        have hfd' : f d = e d := by
          rw [min_eq_left hlt.le] at hfd
          rcases le_or_gt h (f d) with hle | hgt
          · rw [min_eq_right hle] at hfd; exact absurd hfd hlt.ne'
          · rwa [min_eq_left hgt.le] at hfd
        rw [hfd']
  -- the boundary labelling: `f` below the left coatom, the lift elsewhere
  set w : Fin (scheme I).card → Label.{u} := fun d ↦
    if d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) then f d
    else CellScheme.Rows.extendBot ((univ : Finset (Fin 5)), 3) w₃ d with hw
  have hw3 (d : Fin (scheme I).card)
      (hd : d ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
      w d = w₃ ⟨d, hd⟩ := by
    rw [hw]; dsimp only
    by_cases hdC : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)
    · rw [ite_eq_left hdC]
      exact (hw₃f ⟨d, hdC.1, hd.2⟩).symm
    · rw [ite_eq_right hdC, CellScheme.Rows.extendBot_of_mem w₃ hd]
  have hwU : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d :=
    (CellScheme.Rows.isLawfulBelow_congr fun d hd ↦ ite_eq_left hd).mpr hf
  have hwV : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun d ↦ w d := by
    convert hw₃ using 1
    exact funext fun d ↦ hw3 d d.2
  obtain ⟨g, hg, hgw, hga⟩ := exists_isLawfulBelow_four (x := Fin.last 4)
    (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hwU hwV hel hh
    fun d hd ↦ by
      rcases hd with hd | hd
      · rw [hw]; dsimp only; rw [ite_eq_left hd]; exact hfe d hd
      · rw [hw3 d hd]
        have h1 := hw₃q ⟨d, hd⟩
        change min (w₃ ⟨d, hd⟩) v = min (raise h (e d)) v at h1
        calc min (w₃ ⟨d, hd⟩) h = min (min (w₃ ⟨d, hd⟩) v) h := by
              rw [min_assoc, min_eq_right hfr]
          _ = min (min (raise h (e d)) v) h := by rw [h1]
          _ = min (raise h (e d)) h := by rw [min_assoc, min_eq_right hfr]
          _ = min (e d) h := min_raise h (e d)
  refine ⟨g, hg, fun d hd ↦ (hgw d (.inl hd)).trans (ite_eq_left hd),
    fun d ↦ hga d (mem_below_univ_four d), fun x hx ↦ ?_⟩
  have hx3 : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hX3 x hx⟩
  rw [hgw r (.inl hrC), hgw x (.inr hx3), hw3 x hx3, hw]
  dsimp only
  rw [ite_eq_left hrC]
  have h1 := hw₃q ⟨x, hx3⟩
  change min (w₃ ⟨x, hx3⟩) v = min (raise h (e x)) v at h1
  rw [show raise h (e x) = ⊤ from ite_eq_left (hre.trans (Scheme.le_of_mem_readingMarks he hx)),
    min_top_left] at h1
  exact min_eq_right_iff.mp h1

/-- **The fill at the short caps from the left coatom, when no labelling has a value in the band**:
if every labelling lawful below the left coatom has, at its cells of grade at most `3`, no value in
`[h, f r)` for any positive cap `h ≤ f r`, the fill holds (below the cap at the marker by the fill
of the profile layer, `TowerProfile.reads_of_lt`; at or above it by
`TowerProfile.exists_fillPos_left_of_noBand`). -/
theorem readingFillPos_left_of_noBand (hgr : (scheme I).toCellScheme.grade r = 4)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hX3 : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 3)
    (hnoband : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) →
      ∀ h : Label.{u}, IsSelfVisible 4 h → ⊥ < h → h ≤ f r →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 3), h ≤ f d → f r ≤ f d) :
    ReadingFillPos I r X (Fin.last 4) := by
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset r X he)).1
  by_cases hre : h ≤ e r
  · have hfr : h ≤ f r := by
      have := hfe r hrC
      rw [min_eq_right hre] at this
      exact min_eq_right_iff.mp this
    exact exists_fillPos_left_of_noBand hgr hrC hX3 he hh hhb hf hfe hre
      (hnoband f hf h hh hhb hfr)
  · obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four (x := Fin.last 4)
      (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hf hel hh hfe
    exact ⟨g, hg, hgf, hga, reads_of_lt he (not_le.mp hre) hga⟩

/-! ### The band: servers of the new tops -/

/-- **No fill without a server.**  Let `x ∈ X`, `y` a cell of the left coatom of grade at most that
of `x`, `t` a cell of graded index `(univ, grade x)`, and `f` with `h ≤ f r` and `f y < f r` (the
band).  If every cell `u` of graded index `(univ, grade x)` with `h ≤ e u` reads `x` at most as `y`
(no server), no labelling lawful below `(univ, 4)` extends `f`, agrees with `e` capped at `h`, and
reads `x` at least as `r`: availability at `x` gives a cell `u` at least `x`, hence at least `h`,
and locality at `u` puts `x` at most at `y`. -/
theorem not_exists_fill_of_noServer (hrC : r ∈ (scheme I).toCellScheme.below
      (univ.erase (Fin.last 4), 4)) {e f : Fin (scheme I).card → Label.{u}} {h : Label.{u}}
    {x y t : Fin (scheme I).card} (hyC : y ∈ (scheme I).toCellScheme.below
      (univ.erase (Fin.last 4), 4))
    (hgy : (scheme I).toCellScheme.grade y ≤ (scheme I).toCellScheme.grade x)
    (ht : (scheme I).toCellScheme.gradedIndex t =
      ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x))
    (hfr : h ≤ f r) (hband : f y < f r)
    (hnoserver : ∀ u (hu : (scheme I).toCellScheme.gradedIndex u =
        ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x)), h ≤ e u →
      (scheme I).rows.row u ⟨x, by rw [CellScheme.mem_below, hu]; exact ⟨subset_univ _, le_rfl⟩⟩ ≤
        (scheme I).rows.row u ⟨y, by rw [CellScheme.mem_below, hu]; exact ⟨subset_univ _, hgy⟩⟩) :
    ¬ ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), g d = f d) ∧
      (∀ d, min (g d) h = min (e d) h) ∧ g r ≤ g x := by
  rintro ⟨g, hg, hgf, hga, hgx⟩
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hg
  have htY : t ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 4) :=
    mem_below_univ_four t
  obtain ⟨u, hu, hxu⟩ := havail x t htY
    (by rw [show (scheme I).toCellScheme.scope t = univ from congrArg Prod.fst ht];
        exact subset_univ _)
    (congrArg Prod.snd ht).symm
  have hu' := hu.trans ht
  have hrx : f r ≤ g x := (hgf r hrC).symm.trans_le hgx
  have heu : h ≤ e u := by
    have := hga u
    rw [min_eq_right (hfr.trans (hrx.trans hxu))] at this
    exact min_eq_right_iff.mp this.symm
  have h1 := (hloc u (mem_below_univ_four u)).le_of_le
    (d := ⟨x, by rw [CellScheme.mem_below, hu']; exact ⟨subset_univ _, le_rfl⟩⟩)
    (d' := ⟨y, by rw [CellScheme.mem_below, hu']; exact ⟨subset_univ _, hgy⟩⟩)
    (hnoserver u hu' heu) hgy
  change min (g x) (g u) ≤ min (g y) (g u) at h1
  rw [min_eq_left hxu, hgf y hyC] at h1
  exact absurd ((hrx.trans h1).trans (min_le_left _ _)) (not_le.mpr hband)

/-- **The fill at the short caps from the left coatom fails without a server**: under the
hypotheses of `TowerProfile.not_exists_fill_of_noServer`, with `e` a reading mark, `h` a short
positive cap self-visible at `4`, and `f` lawful below the left coatom agreeing with `e` capped at
`h`, `ReadingFillPos I r X (Fin.last 4)` fails. -/
theorem not_readingFillPos_left_of_noServer (hrC : r ∈ (scheme I).toCellScheme.below
      (univ.erase (Fin.last 4), 4)) {e f : Fin (scheme I).card → Label.{u}}
    (he : e ∈ (scheme I).readingMarks 4 r X) {h : Label.{u}} (hh : IsSelfVisible 4 h)
    (hs : IsShort 4 h) (hhb : ⊥ < h)
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hfe : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      min (f d) h = min (e d) h)
    {x y t : Fin (scheme I).card} (hx : x ∈ X) (hyC : y ∈ (scheme I).toCellScheme.below
      (univ.erase (Fin.last 4), 4))
    (hgy : (scheme I).toCellScheme.grade y ≤ (scheme I).toCellScheme.grade x)
    (ht : (scheme I).toCellScheme.gradedIndex t =
      ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x))
    (hfr : h ≤ f r) (hband : f y < f r)
    (hnoserver : ∀ u (hu : (scheme I).toCellScheme.gradedIndex u =
        ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x)), h ≤ e u →
      (scheme I).rows.row u ⟨x, by rw [CellScheme.mem_below, hu]; exact ⟨subset_univ _, le_rfl⟩⟩ ≤
        (scheme I).rows.row u ⟨y, by rw [CellScheme.mem_below, hu]; exact ⟨subset_univ _, hgy⟩⟩) :
    ¬ ReadingFillPos I r X (Fin.last 4) := fun hfill ↦ by
  obtain ⟨g, hg, hgf, hga, hgr⟩ := hfill e he h hh hs hhb f hf hfe
  exact not_exists_fill_of_noServer hrC hyC hgy ht hfr hband hnoserver
    ⟨g, hg, hgf, hga, hgr x hx⟩

/-- **A mark that reads `y` strictly below `x` has a server**: if `e y < e x` (lawful below
`(univ, 4)`, `y` of grade at most that of `x`, `t` at `(univ, grade x)`), availability at `x` gives
a cell `u` at `(univ, grade x)` with `e x ≤ e u` whose row reads `x` strictly above `y`.  So the
obstruction of `TowerProfile.not_exists_fill_of_noServer` needs a mark with `e x ≤ e y`. -/
theorem exists_server_of_lt {e : Fin (scheme I).card → Label.{u}}
    (he : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ e d) {x y t : Fin (scheme I).card}
    (hgy : (scheme I).toCellScheme.grade y ≤ (scheme I).toCellScheme.grade x)
    (ht : (scheme I).toCellScheme.gradedIndex t =
      ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x)) (hlt : e y < e x) :
    ∃ u, ∃ hu : (scheme I).toCellScheme.gradedIndex u =
        ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x),
      e x ≤ e u ∧ ¬ (scheme I).rows.row u
          ⟨x, by rw [CellScheme.mem_below, hu]; exact ⟨subset_univ _, le_rfl⟩⟩ ≤
        (scheme I).rows.row u
          ⟨y, by rw [CellScheme.mem_below, hu]; exact ⟨subset_univ _, hgy⟩⟩ := by
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp he
  obtain ⟨u, hu, hxu⟩ := havail x t (mem_below_univ_four t)
    (by rw [show (scheme I).toCellScheme.scope t = univ from congrArg Prod.fst ht];
        exact subset_univ _)
    (congrArg Prod.snd ht).symm
  have hu' := hu.trans ht
  refine ⟨u, hu', hxu, fun hrow ↦ ?_⟩
  have h1 := (hloc u (mem_below_univ_four u)).le_of_le
    (d := ⟨x, by rw [CellScheme.mem_below, hu']; exact ⟨subset_univ _, le_rfl⟩⟩)
    (d' := ⟨y, by rw [CellScheme.mem_below, hu']; exact ⟨subset_univ _, hgy⟩⟩) hrow hgy
  change min (e x) (e u) ≤ min (e y) (e u) at h1
  rw [min_eq_left hxu] at h1
  exact absurd (h1.trans (min_le_left _ _)) (not_le.mpr hlt)

/-! ### Gluing the two coatoms at the grade `4` -/

/-- **Gluing at the grade `4`**: a labelling lawful below both coatoms at the grade `4` of the
profile layer extends, unchanged below the coatoms, to a labelling lawful below `(univ, 4)`
(`TowerProfile.exists_extension_bot` at the grade `3`, and
`CellScheme.Rows.IsLawfulBelow.glue₃`). -/
theorem exists_glue_four {w : Fin (scheme I).card → Label.{u}}
    (hwC : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d)
    (hwD : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 4)
      fun d ↦ w d) :
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      ∀ d, d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) ∨
        d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4) →
        g d = w d := by
  classical
  obtain ⟨r₃, hr₃, hr₃w⟩ := exists_extension_bot (w := w)
    (hwC.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩) (hwD.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩)
  obtain ⟨g, hg_def⟩ : ∃ g : Fin (scheme I).card → Label.{u}, g = fun e ↦
      if he : e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) then r₃ ⟨e, he⟩
      else w e := ⟨_, rfl⟩
  have hgw (e : Fin (scheme I).card) (he : (scheme I).toCellScheme.scope e ≠ univ) :
      g e = w e := by
    rw [hg_def]
    beta_reduce
    by_cases h3 : e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)
    · rw [dite_eq_left h3]; exact hr₃w ⟨e, h3⟩ he
    · exact dite_eq_right h3
  have hne {z : Fin 5} {e : Fin (scheme I).card}
      (he : e ∈ (scheme I).toCellScheme.below (univ.erase z, 4)) :
      (scheme I).toCellScheme.scope e ≠ univ := fun hs ↦
    Seed.ne_univ_erase z (univ_subset_iff.mp (hs.ge.trans he.1))
  have hgz (z : Fin 5) (hwz : (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ w d) :
      (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun e ↦ g e :=
    (CellScheme.Rows.isLawfulBelow_congr (R := (scheme I).rows) (X := (univ.erase z, 4)) (w := g)
      (w' := w) fun e he ↦ hgw e (hne he)).mpr hwz
  have hg3 : (scheme I).rows.IsLawfulBelow (univ, 3) fun e ↦ g e := by
    convert hr₃ using 1
    exact funext fun e ↦ by rw [hg_def]; exact dite_eq_left e.2
  refine ⟨g, CellScheme.Rows.IsLawfulBelow.glue₃ (hgz _ hwC) hg3 (hgz _ hwD)
    (mem_below_cover (by simp) (by simp) (by decide)), fun d hd ↦ hgw d ?_⟩
  rcases hd with hd | hd
  exacts [hne hd, hne hd]

/-- **The fill at `⊥` from the left coatom when the marker reads the common face as `⊥`**: at the
marker `⊥`, the fill in the profile layer; otherwise the given labelling is `⊥` on the common face
(`TowerProfile.eq_bot_of_row_eq_bot`) and is glued to a labelling `L` that is `⊥` on the common face
and `⊤` on `X` (`TowerProfile.exists_glue_four`).  No condition on the other readings of the
marker. -/
theorem readingFillBot_left_of_face_bot
    (hgr : (scheme I).toCellScheme.grade r = 4)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hface : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
      y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4) →
        (scheme I).rows.row r ⟨y, hy⟩ = ⊥)
    {L : Fin (scheme I).card → Label.{u}}
    (hL : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 4) fun d ↦ L d)
    (hLface : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4) → L y = ⊥)
    (hXD : ∀ x ∈ X, x ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4))
    (hLX : ∀ x ∈ X, L x = ⊤) : ReadingFillBot I r X (Fin.last 4) := by
  classical
  intro f hf
  by_cases hfr : f r = ⊥
  · obtain ⟨g, hg, hgf, -⟩ := exists_fill_four (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3))
      (by simp) (by simp) (by decide) hf (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot
      (isSelfVisible_bot 4) fun _ _ ↦ by simp
    exact ⟨g, hg, hgf, fun x _ ↦ by rw [hgf r hrC, hfr]; exact bot_le⟩
  have hbelow {y : Fin (scheme I).card}
      (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) :
      y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r) :=
    mem_below_marker hgr hrC hy
  have hfface (y : Fin (scheme I).card)
      (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
      (hyD : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4)) :
      f y = ⊥ :=
    eq_bot_of_row_eq_bot hrC hf hfr (hbelow hy) (hface y (hbelow hy) hyD)
  set w : Fin (scheme I).card → Label.{u} := fun d ↦
    if d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) then f d else L d with hw
  have hwC : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d :=
    (CellScheme.Rows.isLawfulBelow_congr fun d hd ↦ (ite_eq_left hd :)).mpr hf
  have hwD : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 3)), 4)
      fun d ↦ w d := by
    refine (CellScheme.Rows.isLawfulBelow_congr fun d hd ↦ ?_).mpr hL
    by_cases hdC : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)
    · rw [hw]; dsimp only; rw [ite_eq_left hdC, hfface d hdC hd, hLface d hdC hd]
    · rw [hw]; dsimp only; rw [ite_eq_right hdC]
  obtain ⟨g, hg, hgw⟩ := exists_glue_four hwC hwD
  refine ⟨g, hg, fun d hd ↦ (hgw d (.inl hd)).trans (ite_eq_left hd), fun x hx ↦ ?_⟩
  have hxC : x ∉ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := fun hxC ↦ by
    have := hLface x hxC (hXD x hx)
    rw [hLX x hx] at this
    exact top_ne_bot this
  rw [hgw x (.inr (hXD x hx)), hw]
  dsimp only
  rw [ite_eq_right hxC, hLX x hx]
  exact le_top


/-- **The cell of a unique top cell of the left type** in the profile layer: of the grade `4`,
below the left coatom, the only cell there at or above its graded index. -/
theorem leftCell_props {a : Fin I.left.card} (ha : I.left.toCellScheme.gradedIndex a = (univ, 4))
    (hu : ∀ z, I.left.toCellScheme.gradedIndex z = (univ, 4) → z = a) :
    (scheme I).toCellScheme.grade (leftCell I a) = 4 ∧
      leftCell I a ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) ∧
      ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.gradedIndex (leftCell I a) ≤
          (scheme I).toCellScheme.gradedIndex y → y = leftCell I a := by
  have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst ha
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hgi : (scheme I).toCellScheme.gradedIndex (leftCell I a) =
      (univ.erase (Fin.last 4), 4) := by
    rw [gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
  refine ⟨congrArg Prod.snd hgi, by rw [CellScheme.mem_below, hgi], fun y hy hle ↦ ?_⟩
  obtain ⟨z, rfl⟩ := exists_leftCell_eq (I := I) fun h ↦ (notMem_erase _ _) (hy.1 h)
  have heq : (scheme I).toCellScheme.gradedIndex (leftCell I z) =
      (univ.erase (Fin.last 4), 4) := le_antisymm hy (hgi ▸ hle)
  rw [gradedIndex_leftCell, ← univ_map_left_eq] at heq
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
  rw [map_inj] at h1
  exact congrArg (leftCell I) (hu z (Prod.ext h1 h2))

/-! ### A left coatom type labelled `⊥` on the common face -/

/-- The image of the right coatom of `Fin 5`. -/
theorem univ_map_right_eq :
    (univ : Finset (Fin 4)).map (Coatom.right 3) = univ.erase (Fin.castSucc (Fin.last 3)) := by
  decide

/-- **The fill at `⊥` from the left coatom, for a left type labelled `⊥` on the common face**:
let `a` be the only cell of the left type of graded index `(univ, 4)`, whose row reads every cell
labelled `⊥` as `⊥`, the left type labelled `⊥` at every cell off the point `3` (the common face),
and `Z` a set of cells of the right type labelled `⊤`.  Then the fill at `⊥` from the left coatom
holds for the cell of `a` and the cells of `Z` (`TowerProfile.readingFillBot_left_of_face_bot`, with
the glued labelling of the completion). -/
theorem readingFillBot_left_of_left {a : Fin I.left.card}
    (ha : I.left.toCellScheme.gradedIndex a = (univ, 4))
    (hrowbot : ∀ z, I.left.label z = ⊥ → I.left.toScheme.rowAt a z = ⊥)
    (hfaceL : ∀ z, Fin.last 3 ∉ I.left.toCellScheme.scope z → I.left.label z = ⊥)
    (Z : Finset (Fin I.right.card)) (hZ : ∀ z ∈ Z, I.right.label z = ⊤) :
    ReadingFillBot I (leftCell I a)
      (Z.image fun z ↦ embed3 I (StageType.faceCell I.restrictFace_right z)) (Fin.last 4) := by
  have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst ha
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hgi : (scheme I).toCellScheme.gradedIndex (leftCell I a) =
      (univ.erase (Fin.last 4), 4) := by
    rw [gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
  have hgr : (scheme I).toCellScheme.grade (leftCell I a) = 4 := congrArg Prod.snd hgi
  have hrC : leftCell I a ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := by
    rw [CellScheme.mem_below, hgi]
  -- a cell below both coatoms is a cell of the left type off the point `3`, labelled `⊥`
  have hcommon {y : Fin (scheme I).card}
      (hyC : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
      (hyD : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.castSucc (Fin.last 3)), 4)) :
      ∃ z, leftCell I z = y ∧ I.left.label z = ⊥ := by
    obtain ⟨z, rfl⟩ := exists_leftCell_eq (I := I) fun h ↦ (notMem_erase _ _) (hyC.1 h)
    refine ⟨z, rfl, hfaceL z fun h3 ↦ ?_⟩
    have h := hyD.1
    rw [gradedIndex_leftCell] at h
    have := h (mem_map_of_mem _ h3)
    simp at this
  obtain ⟨q, hq, hqe⟩ := exists_isLawful_top (I := I)
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  have hold (d : Fin I.amalgam.card) :
      q (Fin.castAdd _ (embed3 I d)) = I.amalgam.label d := hqe d
  refine readingFillBot_left_of_face_bot hgr hrC (fun y hy hyD ↦ ?_)
    (L := fun d ↦ q (Fin.castAdd _ d)) (hL.isLawfulBelow _) (fun y hyC hyD ↦ ?_)
    (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨z, rfl, hz⟩ := hcommon (hgi ▸ hy) hyD
    rw [← Scheme.rowAt_of_mem, rowAt_leftCell]
    exact hrowbot z hz
  · obtain ⟨z, rfl, hz⟩ := hcommon hyC hyD
    change q (Fin.castAdd _ (embed3 I (StageType.faceCell I.restrictFace_left z))) = ⊥
    rw [hold, StageType.label_faceCell]
    exact hz
  · obtain ⟨z, -, rfl⟩ := mem_image.mp hx
    rw [CellScheme.mem_below, gradedIndex_embed3]
    refine ⟨?_, ?_⟩
    · change I.amalgam.toCellScheme.scope _ ⊆ _
      rw [StageType.scope_faceCell, ← univ_map_right_eq]
      exact map_subset_map.mpr (subset_univ _)
    · change I.amalgam.toCellScheme.grade _ ≤ 4
      rw [StageType.grade_faceCell]
      exact I.right.grade_le z
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [hold, StageType.label_faceCell]
    exact hZ z hz

end TowerProfile

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The label `3`. -/
noncomputable abbrev lab3 : Label.{u} := ((3 : ℕ) : Label.{u})

/-- The cells of `S` off the point `3` are labelled `⊥` by `labelling A F ⊥`. -/
theorem labelling_bot_eq_bot_of_notMem {A F : Label.{u}} (d : Fin 19)
    (hd : (3 : Fin 4) ∉ TwoFaceLiftCounterexample.cellScope d) :
    CaseSplitCounterexample.labelling A F ⊥ d = ⊥ := by
  have key : ∀ d : Fin 19, (3 : Fin 4) ∉ TwoFaceLiftCounterexample.cellScope d →
      CaseSplitCounterexample.live d = false ∨ TwoFaceLiftCounterexample.cellGrade d = 3 := by
    decide
  unfold CaseSplitCounterexample.labelling
  rcases key d hd with h | h
  · simp [h]
  · simp [h]

include hα in
/-- The type `S` labelled `3` at its live cells of grade at most `2` and `⊥` elsewhere: proper
labels off the common face. -/
noncomputable def threeBase : StageType.{u} α 4 where
  toScheme := S
  label := CaseSplitCounterexample.labelling lab3 lab3 ⊥
  isWellFormed := isWellFormed_S
  isCoded := isCoded_S
  isLawful := isLawful_labelling ((isSelfVisible_natCast 3).mpr (by omega))
    ((isSelfVisible_natCast 3).mpr (by omega)) (isSelfVisible_bot 3) bot_le bot_le
  atStage d := by
    have h3 : AtStage α lab3.{u} := (atStage_natCast 3).mpr (Ordinal.natCast_lt_of_isSuccLimit hα 3)
    unfold CaseSplitCounterexample.labelling
    split_ifs <;> first | exact h3 | exact atStage_bot

/-- **The left coatom type with a proper-labelled apex**: `threeBase` with the apex added.  Its
apex row reads the cells labelled `3` at the code of `3`, strictly between `⊥` and the code of
`⊤` at which it reads the apex. -/
noncomputable def threeType : StageType.{u} α 4 :=
  (threeBase hα).addApex isLegalBelowFullGrade_S (by omega)

theorem isLegal_threeType : (threeType hα).IsLegal := StageType.isLegal_addApex _ _

/-- The type `threeType` has the face of `T5`: on the face `{0, 1, 2}` its labels are `⊥`. -/
theorem restrictFace_threeType :
    StageType.restrictFace (Coatom.face 3) (threeType hα) = some (faceT5 α) := by
  have hne : univ.map (Coatom.face 3) ≠ (univ : Finset (Fin 4)) := by decide
  rw [threeType, StageType.restrictFace_addApex (t := threeBase hα) isLegalBelowFullGrade_S
    (by omega) (Coatom.face 3) hne, ← restrictFace_T5, T5,
    StageType.restrictFace_addApex (t := T5₀ α) isLegalBelowFullGrade_S (by omega) (Coatom.face 3)
      hne]
  refine StageType.restrictFace_congr_label rfl fun i j hij hi ↦ ?_
  obtain rfl : i = j := Fin.ext hij
  change CaseSplitCounterexample.labelling lab3 lab3 ⊥ i = ⊥
  refine labelling_bot_eq_bot_of_notMem i fun h3 ↦ ?_
  obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hi (mem_coe.mpr h3)
  exact (Fin.castSucc_lt_last y).ne hy

/-- **The seed of `threeType` and `rightType`.** -/
noncomputable def seedThree : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_threeType hα) (isLegal_rightType α) (restrictFace_threeType hα)
    (restrictFace_rightType α)

/-- **The apex of `threeType` reads a cell strictly between `⊥` and itself**: the cell `{3}`,
labelled `3`. -/
theorem rowAt_threeType_three :
    ⊥ < (threeType hα).toScheme.rowAt (Fin.last _)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ∧
      (threeType hα).toScheme.rowAt (Fin.last _)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) <
      (threeType hα).toScheme.rowAt (Fin.last _) (Fin.last _) := by
  have h3 : (threeType hα).label
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) = lab3 := by
    change CaseSplitCounterexample.labelling lab3 lab3 ⊥ (3 : Fin 19) = lab3
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]
  have e1 := StageType.rowAt_addApex_last (t₀ := threeBase hα) isLegalBelowFullGrade_S
    (by omega) (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
  have e2 := StageType.rowAt_addApex_last (t₀ := threeBase hα) isLegalBelowFullGrade_S
    (by omega) (Fin.last _)
  change ⊥ < ((threeBase hα).addApex isLegalBelowFullGrade_S _).toScheme.rowAt _ _ ∧
    ((threeBase hα).addApex isLegalBelowFullGrade_S _).toScheme.rowAt _ _ <
      ((threeBase hα).addApex isLegalBelowFullGrade_S _).toScheme.rowAt _ _
  rw [e1, e2]
  change ⊥ < blockEncode _ 4 ((threeType hα).label _) ∧
    blockEncode _ 4 ((threeType hα).label _) < blockEncode _ 4 ((threeType hα).label _)
  rw [h3, show (threeType hα).label (Fin.last _) = ⊤ from
    StageType.addApex_label_last (t := threeBase hα) isLegalBelowFullGrade_S (by omega)]
  refine ⟨bot_lt_iff_ne_bot.mpr fun h ↦ natCast_label_ne_bot 3 (blockEncode_eq_bot_iff.mp h),
    blockEncode_lt_blockEncode ?_ ?_⟩
  · rw [← h3]
    exact StageType.label_mem_apexCodes (t := threeBase hα) isLegalBelowFullGrade_S
      (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)
  · exact lt_top_iff_ne_top.mpr fun h ↦ by
      rw [lab3, natCast_label] at h
      exact WithTop.coe_ne_top (WithBot.coe_injective h)

/-- **Three of the four fills at the proper-labelled apex** (the seed of `threeType` and
`rightType`, the marker the apex of `threeType`, `X` the cell `{3}` of `rightType`): the fill at `⊥`
from the left coatom (`TowerProfile.readingFillBot_left_of_left`: the apex reads the common face as
`⊥`), and both fills from the right coatom (`TowerProfile.readingFillBot_right_of_unique`,
`TowerProfile.readingFillPos_right_of_unique`).  The fill at the short positive caps from the left
coatom is not decided here. -/
theorem readingFills_seedThree :
    ReadingFillBot (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
        (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
          Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
            (StageType.faceCell (seedThree hα).restrictFace_right z)) (Fin.last 4) ∧
      ReadingFillBot (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
        (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
          Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
            (StageType.faceCell (seedThree hα).restrictFace_right z)) (Fin.castSucc (Fin.last 3)) ∧
      ReadingFillPos (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
        (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
          Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
            (StageType.faceCell (seedThree hα).restrictFace_right z))
        (Fin.castSucc (Fin.last 3)) := by
  have ha := StageType.addApex_gradedIndex_last (t := threeBase hα) isLegalBelowFullGrade_S
    (by omega)
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := seedThree hα) (a := Fin.last _) ha
    fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := threeBase hα)
      isLegalBelowFullGrade_S (by omega) hz
  have hX3 : ∀ x ∈ (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
      Finset (Fin (seedThree hα).right.card)).image fun z ↦ embed3 (seedThree hα)
        (StageType.faceCell (seedThree hα).restrictFace_right z)),
      (scheme (seedThree hα)).toCellScheme.grade x ≤ 3 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [mem_singleton.mp hz]
    have h2 := congrArg Prod.snd (gradedIndex_embed3 (I := seedThree hα)
      (StageType.faceCell (seedThree hα).restrictFace_right
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))))
    simp only [CellScheme.gradedIndex_snd] at h2
    refine (h2.trans (StageType.grade_faceCell _ _)).trans_le ?_
    change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).grade
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ≤ 3
    rw [Scheme.appendFullCellScheme_grade_castSucc]
    decide
  refine ⟨readingFillBot_left_of_left ha (fun z hz ↦ ?_) (fun z hz ↦ ?_) _ fun z hz ↦ ?_,
    readingFillBot_right_of_unique hgr hrC huniq,
    readingFillPos_right_of_unique hgr hrC huniq hX3⟩
  · exact (StageType.rowAt_addApex_last_eq_bot_iff (t₀ := threeBase hα) isLegalBelowFullGrade_S
      (by omega) z).mpr hz
  · change (threeType hα).label z = ⊥
    change Fin ((threeBase hα).card + 1) at z
    induction z using Fin.lastCases with
    | last =>
      exact absurd (Finset.eq_univ_iff_forall.mp (StageType.addApex_scope_last
        (t := threeBase hα) isLegalBelowFullGrade_S (by omega)) _) hz
    | cast d =>
      refine (StageType.addApex_label_castSucc (t := threeBase hα) isLegalBelowFullGrade_S
        (by omega) d).trans (labelling_bot_eq_bot_of_notMem d fun h3 ↦ hz ?_)
      exact (Scheme.appendFullCellScheme_scope_castSucc (S := CaseSplitCounterexample.S) (j := 4)
        (d := d)).symm ▸ h3
  · rw [mem_singleton.mp hz]
    change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]

end TopReadingApexExample

end VaughtConjecture
