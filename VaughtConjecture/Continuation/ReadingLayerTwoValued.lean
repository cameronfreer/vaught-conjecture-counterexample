/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayer

/-!
# The reading layer at a marker that is not isolated

Roadmap, Layer 3 ((R3) of the table of 3.4).

The test of the four fill conditions of the reading layer (`TowerProfile.ReadingFillBot`,
`TowerProfile.ReadingFillPos`; legality of the layer exactly when they hold,
`TowerProfile.isLegalBelowFullGrade_readingTop_iff`) at a marker that is **not isolated**: its row
reads cells other than itself not as `⊥`.  Outcome: **the fills hold** for every **two-valued**
marker (compiled in this repository (theorem named)), so the restricted design survives this class.

**Two-valued marker.**  A cell `r` of the grade `4` on the left coatom, the only cell at or above
its graded index, whose row reads every cell below it either as `⊥` or at least as `r` itself.
The isolated markers are the case where only `r` is read above `⊥`.

**The mechanism** (`TowerProfile.isLegalBelowFullGrade_readingTop_of_twoValued`).  A labelling `f`
lawful below the left coatom and not `⊥` at `r` is `⊥` at the cells the marker reads as `⊥`
(`TowerProfile.eq_bot_of_row_eq_bot`) and at least `f r` at the others
(`TowerProfile.le_of_row_ne_bot`): capped at `f r` it is determined by the row of the marker.

* Fill at `⊥`, left coatom (`TowerProfile.readingFillBot_left_of_twoValued`): the fill along a
  labelling `L` that is `⊥` where the marker reads `⊥`, `⊤` elsewhere and on `X`, capped at `f r`.
* Fill at the short caps, left coatom (`TowerProfile.readingFillPos_left_of_twoValued`): the mark
  raised to `⊤` above the cap (`Label.raise`) is lawful below the left coatom (below `(univ, 3)` by
  the witness, at the marker by its two-valued row: `transformsTo_of_eq_bot_iff`,
  `CellScheme.Rows.IsLawfulBelow.of_lower_and_cell`), completed on the right coatom, and the given
  labelling is filled along it capped at `f r`.
* Fills from the right coatom (`TowerProfile.readingFillBot_right_of_unique`,
  `TowerProfile.readingFillPos_right_of_unique`), at every marker the only cell at or above its
  graded index: the fill in the profile layer with the marker moved to `⊥` or to the cap (its
  locality is that of the mark capped at the cap, `TransformsTo.min_const`;
  `CellScheme.Rows.IsLawfulBelow.update_of_transformsTo`).

**An instance** (`TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedRR`): the seed of
`rightType` with itself, at the apex of the left copy (a top cap and its own marker,
`TopReadingApexExample.isTopCap_isMarker_rightType`; not isolated,
`TopReadingApexExample.rowAt_rightType_three_ne_bot`) and the new top `{3}` of the right copy.  The
apex row is the code of the labels (`StageType.rowAt_addApex_last`), which are `⊥` or `⊤`
(`TopReadingApexExample.label_rightType_cases`): two-valued.  The general form for a left type
with such an apex is `TowerProfile.isLegalBelowFullGrade_readingTop_of_left_twoValued`.

**Not covered** (prospective): markers whose row reads some cell strictly between `⊥` and the
marker itself (a context with proper labels below the marker), and markers sharing their graded
index with another cell.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Moving one cell, and lawfulness from a lower pair and one cell -/

namespace CellScheme.Rows.IsLawfulBelow

variable {ι κ : Type*} {D : CellScheme ι κ} {R : D.Rows.{u}}

/-- **Moving a cell that no other cell reads.**  Let `r` lie below `X`, the only cell below `X` at
or above its graded index and the only cell below `X` of its grade inside its scope.  The labelling
`w` with `r` sent to `v` (self-visible at the grade of `r`) stays lawful below `X` when the row of
`r` transforms to the new labelling capped at `v`. -/
theorem update_of_transformsTo [DecidableEq ι] {X : Finset κ × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {r : ι} (hrX : r ∈ D.below X)
    (huniq : ∀ y ∈ D.below X, D.gradedIndex r ≤ D.gradedIndex y → y = r)
    (hsame : ∀ y ∈ D.below X, D.grade y = D.grade r → D.scope y ⊆ D.scope r → y = r)
    {v : Label.{u}} (hv : IsSelfVisible (D.grade r) v)
    (hloc : TransformsTo (fun d : D.below (D.gradedIndex r) ↦ D.grade d) (R.row r)
      fun d ↦ min (Function.update w r v d) v) :
    R.IsLawfulBelow X fun d ↦ Function.update w r v d := by
  obtain ⟨hvis, hloc', havail⟩ := isLawfulBelow_iff_forall.mp hw
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hdr : d = r
    · rw [hdr, Function.update_self]; exact hv
    · rw [Function.update_of_ne hdr]; exact hvis d hd
  · by_cases hsr : s = r
    · subst hsr
      simpa only [Function.update_self] using hloc
    · have hrs (d : D.below (D.gradedIndex s)) : (d : ι) ≠ r := fun hdr ↦
        hsr (huniq s hs (hdr ▸ d.2))
      have heq : (fun d : D.below (D.gradedIndex s) ↦
          min (Function.update w r v d) (Function.update w r v s)) =
          fun d : D.below (D.gradedIndex s) ↦ min (w d) (w s) := funext fun d ↦ by
        rw [Function.update_of_ne (hrs d), Function.update_of_ne hsr]
      rw [heq]
      exact hloc' s hs
  · by_cases hsr : s = r
    · rw [hsr] at hst hg ⊢
      have htr : t = r := huniq t ht ⟨hst, hg.le⟩
      exact ⟨r, by rw [htr], le_of_eq (by rw [Function.update_self])⟩
    · obtain ⟨u, hu, hsu⟩ := havail s t ht hst hg
      by_cases hur : u = r
      · have htr : t = r := huniq t ht (by rw [← hu, hur])
        rw [htr] at hst hg ht
        exact absurd (hsame s ⟨hst.trans ht.1, hg.trans_le ht.2⟩ hg hst) hsr
      · exact ⟨u, hu, by rw [Function.update_of_ne hsr, Function.update_of_ne hur]; exact hsu⟩

/-- **Lawfulness from a lower pair and one cell.**  If every cell below `X` other than `r` lies
below `Y`, the only cell below `X` of the grade of `r` inside its scope is `r`, `w` is lawful below
`Y`, self-visible at `r`, and local at `r`, then `w` is lawful below `X`. -/
theorem of_lower_and_cell {X Y : Finset κ × ℕ} {w : ι → Label.{u}}
    (hwY : R.IsLawfulBelow Y fun d ↦ w d) {r : ι}
    (hcov : ∀ d ∈ D.below X, d ≠ r → d ∈ D.below Y)
    (hsame : ∀ y ∈ D.below X, D.grade y = D.grade r → D.scope y ⊆ D.scope r → y = r)
    (hvr : IsSelfVisible (D.grade r) (w r))
    (hloc : TransformsTo (fun d : D.below (D.gradedIndex r) ↦ D.grade d) (R.row r)
      fun d ↦ min (w d) (w r)) :
    R.IsLawfulBelow X fun d ↦ w d := by
  obtain ⟨hvis, hloc', havail⟩ := isLawfulBelow_iff_forall.mp hwY
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hdr : d = r
    · rw [hdr]; exact hvr
    · exact hvis d (hcov d hd hdr)
  · by_cases hsr : s = r
    · rw [hsr]; exact hloc
    · exact hloc' s (hcov s hs hsr)
  · by_cases htr : t = r
    · rw [htr] at hst hg ht
      have hsr : s = r := hsame s ⟨hst.trans ht.1, hg.trans_le ht.2⟩ hg hst
      exact ⟨r, by rw [htr], by rw [hsr]⟩
    · exact havail s t (hcov t ht htr) hst hg

end CellScheme.Rows.IsLawfulBelow

/-! ### The fills at a two-valued marker -/

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {r : Fin (scheme I).card}
  {X : Finset (Fin (scheme I).card)}

/-- The left coatom. -/
private theorem pairL :
    Fin.last 4 ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)) := by
  simp

/-- The right coatom. -/
private theorem pairR :
    Fin.castSucc (Fin.last 3) ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)) := by
  simp

section TwoValued

variable (hgr : (scheme I).toCellScheme.grade r = 4)
  (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
  (huniq : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
    (scheme I).toCellScheme.gradedIndex r ≤ (scheme I).toCellScheme.gradedIndex y → y = r)
  (htwo : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
    (scheme I).rows.row r ⟨y, hy⟩ ≠ ⊥ →
      (scheme I).rows.row r ⟨r, (scheme I).toCellScheme.mem_below_gradedIndex r⟩ ≤
        (scheme I).rows.row r ⟨y, hy⟩)
  (hX3 : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 3)

include hgr hrC in
/-- A cell below the left coatom lies below the marker. -/
theorem mem_below_marker {y : Fin (scheme I).card}
    (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) :
    y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r) := by
  rw [gradedIndex_eq_of_isolated hgr hrC]; exact hy

include hrC in
/-- **Below the marker, a cell read as `⊥` is `⊥`** in every labelling lawful below the left coatom
that is not `⊥` at the marker. -/
theorem eq_bot_of_row_eq_bot {w : Fin (scheme I).card → Label.{u}}
    (hw : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d)
    (hwr : w r ≠ ⊥) {y : Fin (scheme I).card}
    (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hrowy : (scheme I).rows.row r ⟨y, hy⟩ = ⊥) : w y = ⊥ := by
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have h := (hloc r hrC).eq_bot (d := ⟨y, hy⟩) hrowy
  change min (w y) (w r) = ⊥ at h
  exact (min_eq_bot.mp h).resolve_right hwr

include hgr hrC htwo in
/-- **Below a two-valued marker, a cell read above `⊥` is at least the marker** in every labelling
lawful below the left coatom. -/
theorem le_of_row_ne_bot {w : Fin (scheme I).card → Label.{u}}
    (hw : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ w d)
    {y : Fin (scheme I).card}
    (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hrowy : (scheme I).rows.row r ⟨y, hy⟩ ≠ ⊥) : w r ≤ w y := by
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hw
  have hg : (scheme I).toCellScheme.grade y ≤ (scheme I).toCellScheme.grade r := by
    have := hy.2
    rw [gradedIndex_eq_of_isolated hgr hrC] at this
    rw [hgr]; exact this
  have h := (hloc r hrC).le_of_le (d := ⟨r, (scheme I).toCellScheme.mem_below_gradedIndex r⟩)
    (d' := ⟨y, hy⟩) (htwo y hy hrowy) hg
  change min (w r) (w r) ≤ min (w y) (w r) at h
  rw [min_self] at h
  exact h.trans (min_le_left _ _)

include hgr hrC htwo in
/-- **The fill at `⊥` from the left coatom at a two-valued marker**: at the marker `⊥`, the fill in
the profile layer; otherwise the fill along a labelling `L` that is `⊥` at the cells the marker
reads as `⊥`, `⊤` at the others and on `X`, capped at the label of the marker. -/
theorem readingFillBot_left_of_twoValued {L : Fin (scheme I).card → Label.{u}}
    (hL : (scheme I).rows.IsLawful L)
    (hLC : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
      L y = if (scheme I).rows.row r ⟨y, hy⟩ = ⊥ then ⊥ else ⊤)
    (hLX : ∀ x ∈ X, L x = ⊤) : ReadingFillBot I r X (Fin.last 4) := by
  classical
  intro f hf
  by_cases hfr : f r = ⊥
  · obtain ⟨g, hg, hgf, -⟩ := exists_fill_four pairL pairR (by decide) hf
      (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot (isSelfVisible_bot 4)
      fun _ _ ↦ by simp
    exact ⟨g, hg, hgf, fun x _ ↦ by rw [hgf r hrC, hfr]; exact bot_le⟩
  · have hv : IsSelfVisible 4 (f r) := by
      have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hf).1 r hrC
      rwa [hgr] at this
    obtain ⟨g, hg, hgf, hgL⟩ := exists_fill_four pairL pairR (by decide) hf hL hv
      fun y hy ↦ by
        have hy' := mem_below_marker hgr hrC hy
        rw [hLC y hy']
        by_cases hrowy : (scheme I).rows.row r ⟨y, hy'⟩ = ⊥
        · rw [ite_eq_left hrowy, eq_bot_of_row_eq_bot hrC hf hfr hy' hrowy]
        · rw [ite_eq_right hrowy, min_top_left]
          exact min_eq_right (le_of_row_ne_bot hgr hrC htwo hf hy' hrowy)
    refine ⟨g, hg, hgf, fun x hx ↦ ?_⟩
    have h := hgL x
    rw [hLX x hx, min_top_left] at h
    rw [hgf r hrC]
    exact min_eq_right_iff.mp h

include hgr hrC huniq in
/-- **The fill at `⊥` from the right coatom**, at every marker of the grade `4` on the left coatom
that is the only cell at or above its graded index: the fill in the profile layer, with the marker
moved to `⊥`. -/
theorem readingFillBot_right_of_unique : ReadingFillBot I r X (Fin.castSucc (Fin.last 3)) := by
  classical
  intro f hf
  obtain ⟨g, hg, hgf, -⟩ := exists_fill_four pairR pairL (by decide) hf
    (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot (isSelfVisible_bot 4) fun _ _ ↦ by simp
  refine ⟨Function.update g r ⊥, CellScheme.Rows.IsLawfulBelow.update_of_transformsTo hg
      (mem_below_univ_four r) (fun y _ hy ↦ eq_of_le_gradedIndex_of_isolated hgr hrC huniq hy)
      (fun y _ hgy hsy ↦ eq_of_grade_of_isolated hgr hrC huniq hgy hsy) (isSelfVisible_bot _)
      (by simpa only [min_bot_right] using TransformsTo.bot _ _), fun d hd ↦ ?_,
    fun x _ ↦ ?_⟩
  · have hdr : d ≠ r := fun h' ↦ notMem_below_right_of_isolated hgr hrC (h' ▸ hd)
    rw [Function.update_of_ne hdr, hgf d hd]
  · rw [Function.update_self]; exact bot_le

include hgr hrC huniq hX3 in
/-- **The fill at the short positive caps from the right coatom**, at every marker of the grade `4`
on the left coatom that is the only cell at or above its graded index: the fill in the profile
layer along the reading mark; at or above the cap at the marker, the marker moved to the cap (its
locality is that of the mark capped at the cap, `TransformsTo.min_const`). -/
theorem readingFillPos_right_of_unique : ReadingFillPos I r X (Fin.castSucc (Fin.last 3)) := by
  classical
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset r X he)).1
  obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four pairR pairL (by decide) hf hel hh hfe
  by_cases hre : h ≤ e r
  · have hloc := (hel.locality r).min_const (K := 4)
      (fun d ↦ d.2.2.trans hgr.le) hh
    refine ⟨Function.update g r h, CellScheme.Rows.IsLawfulBelow.update_of_transformsTo hg
      (mem_below_univ_four r) (fun y _ hy ↦ eq_of_le_gradedIndex_of_isolated hgr hrC huniq hy)
      (fun y _ hgy hsy ↦ eq_of_grade_of_isolated hgr hrC huniq hgy hsy) (by rw [hgr]; exact hh)
      ?_, fun d hd ↦ ?_, fun d ↦ ?_, fun x hx ↦ ?_⟩
    · convert hloc using 1
      funext d
      by_cases hdr : (d : Fin (scheme I).card) = r
      · rw [hdr, Function.update_self, min_self, min_self, min_eq_right hre]
      · rw [Function.update_of_ne hdr, hga d, min_assoc, min_eq_right hre]
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

include hgr hrC huniq htwo hX3 in
/-- **The fill at the short positive caps from the left coatom at a two-valued marker.**  At or
above the cap at the marker: the reading mark raised to `⊤` above the cap (`Label.raise`) is lawful
below the left coatom (below `(univ, 3)` by the witness, at the marker by its two-valued row) and
below `(univ, 3)`; completed on the right coatom (`TowerProfile.exists_isLawfulBelow_four`), it is
`⊤` on `X`, and the given labelling is filled along it capped at its label at the marker. -/
theorem readingFillPos_left_of_twoValued : ReadingFillPos I r X (Fin.last 4) := by
  classical
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset r X he)).1
  by_cases hre : h ≤ e r
  · have hfr : h ≤ f r := by
      have := hfe r hrC
      rw [min_eq_right hre] at this
      exact min_eq_right_iff.mp this
    have her : e r ≠ ⊥ := (hhb.trans_le hre).ne'
    have hfr0 : f r ≠ ⊥ := (hhb.trans_le hfr).ne'
    have heC := hel.isLawfulBelow (univ.erase (Fin.last 4), 4)
    -- the raised mark on the cells below the marker
    have hraise (y : Fin (scheme I).card)
        (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)) :
        raise h (e y) = if (scheme I).rows.row r ⟨y, hy⟩ = ⊥ then ⊥ else ⊤ := by
      by_cases hrowy : (scheme I).rows.row r ⟨y, hy⟩ = ⊥
      · rw [ite_eq_left hrowy, eq_bot_of_row_eq_bot hrC heC her hy hrowy, raise_bot hhb]
      · rw [ite_eq_right hrowy]
        exact ite_eq_left (hre.trans (le_of_row_ne_bot hgr hrC htwo heC hy hrowy))
    have hr3 : r ∉ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) := fun h' ↦ by
      have := h'.2
      change (scheme I).toCellScheme.grade r ≤ 3 at this
      omega
    have haV : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
        fun d ↦ raise h (e d) :=
      (hel.isLawfulBelow _).map_of_min_eq (hel.isLawfulBelow _) (fun d ↦ d.2.2)
        (isWitness_raise (K := 3) hh hhb) hhb.ne' fun d ↦ min_raise h (e d)
    have haU : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4)
        fun d ↦ raise h (e d) := by
      refine CellScheme.Rows.IsLawfulBelow.of_lower_and_cell (R := (scheme I).rows)
        (X := (univ.erase (Fin.last 4), 4)) (w := fun d ↦ raise h (e d)) haV (r := r)
        (fun d hd hdr ↦ ?_)
        (fun y hy hgy hsy ↦ eq_of_grade_of_isolated hgr hrC huniq hgy hsy)
        (by rw [show raise h (e r) = ⊤ from ite_eq_left hre]; exact isSelfVisible_top _) ?_
      · refine ⟨subset_univ _, ?_⟩
        by_contra h4
        have hd4 : (scheme I).toCellScheme.grade d = 4 := by
          have := hd.2; change (scheme I).toCellScheme.grade d ≤ 4 at this
          change ¬ (scheme I).toCellScheme.grade d ≤ 3 at h4
          omega
        refine hdr (eq_of_grade_of_isolated hgr hrC huniq (hd4.trans hgr.symm) ?_)
        rw [show (scheme I).toCellScheme.scope r = univ.erase (Fin.last 4) from
          congrArg Prod.fst (gradedIndex_eq_of_isolated hgr hrC)]
        exact hd.1
      · refine transformsTo_of_eq_bot_iff _ (K := 4) (fun d ↦ d.2.2.trans hgr.le)
          (isSelfVisible_top 4) _ _ fun d ↦ ?_
        rw [show raise h (e r) = ⊤ from ite_eq_left hre, min_top_right]
        exact hraise d d.2
    obtain ⟨a', ha', ha'w, ha'e⟩ := exists_isLawfulBelow_four pairL pairR (by decide) haU
      haV hel hh fun d _ ↦ min_raise h (e d)
    have hvf : IsSelfVisible 4 (f r) := by
      have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp hf).1 r hrC
      rwa [hgr] at this
    obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four pairL pairR (by decide) hf
      (ha'.isLawful fun d ↦ mem_below_univ_four d) hvf fun y hy ↦ by
        have hy' := mem_below_marker hgr hrC hy
        change min (f y) (f r) = min (a' y) (f r)
        rw [ha'w _ (.inl hy), hraise y hy']
        by_cases hrowy : (scheme I).rows.row r ⟨y, hy'⟩ = ⊥
        · rw [ite_eq_left hrowy, eq_bot_of_row_eq_bot hrC hf hfr0 hy' hrowy]
        · rw [ite_eq_right hrowy, min_top_left]
          exact min_eq_right (le_of_row_ne_bot hgr hrC htwo hf hy' hrowy)
    refine ⟨g, hg, hgf, fun d ↦ ?_, fun x hx ↦ ?_⟩
    · have h1 := hga d
      have h2 := ha'e d (mem_below_univ_four d)
      change min (g d) (f r) = min (a' d) (f r) at h1
      calc min (g d) h = min (min (g d) (f r)) h := by rw [min_assoc, min_eq_right hfr]
        _ = min (min (a' d) (f r)) h := by rw [h1]
        _ = min (a' d) h := by rw [min_assoc, min_eq_right hfr]
        _ = min (e d) h := h2
    · have hx3 : x ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
        ⟨subset_univ _, hX3 x hx⟩
      have h1 := hga x
      change min (g x) (f r) = min (a' x) (f r) at h1
      rw [ha'w _ (.inr hx3), show raise h (e x) = ⊤ from
        ite_eq_left (hre.trans (Scheme.le_of_mem_readingMarks he hx)), min_top_left] at h1
      rw [hgf r hrC]
      exact min_eq_right_iff.mp h1
  · obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four pairL pairR (by decide) hf hel hh hfe
    exact ⟨g, hg, hgf, hga, reads_of_lt he (not_le.mp hre) hga⟩

include hgr hrC huniq htwo hX3 in
/-- **The reading layer at a two-valued marker is legal below the full grade**: a marker of the
grade `4` on the left coatom, the only cell at or above its graded index, whose row reads every
cell below it either as `⊥` or at least as itself, `X` of grade at most
`3`, given a lawful labelling `L` that is `⊥` at the cells the marker reads as `⊥`, `⊤` at the
others and on `X`. -/
theorem isLegalBelowFullGrade_readingTop_of_twoValued {L : Fin (scheme I).card → Label.{u}}
    (hL : (scheme I).rows.IsLawful L)
    (hLC : ∀ y (hy : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r)),
      L y = if (scheme I).rows.row r ⟨y, hy⟩ = ⊥ then ⊥ else ⊤)
    (hLX : ∀ x ∈ X, L x = ⊤) : (readingTop I r X).IsLegalBelowFullGrade := by
  have hpair (z : Fin 5) (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
      z = Fin.last 4 ∨ z = Fin.castSucc (Fin.last 3) := by
    simpa only [mem_insert, mem_singleton] using hz
  refine isLegalBelowFullGrade_readingTop hgr.le (fun x hx ↦ (hX3 x hx).trans (by omega))
    (fun z hz ↦ ?_) fun z hz ↦ ?_
  · rcases hpair z hz with rfl | rfl
    · exact readingFillBot_left_of_twoValued hgr hrC htwo hL hLC hLX
    · exact readingFillBot_right_of_unique hgr hrC huniq
  · rcases hpair z hz with rfl | rfl
    · exact readingFillPos_left_of_twoValued hgr hrC huniq htwo hX3
    · exact readingFillPos_right_of_unique hgr hrC huniq hX3

end TwoValued

/-! ### A left coatom type with a two-valued apex -/

/-- **The reading layer of a two-valued cell of the left type.**  Let `a` be the only cell of the
left coatom type of graded index `(univ, 4)`, the left type labelled `⊥` or `⊤` everywhere, the row
of `a` reading exactly the cells labelled `⊥` as `⊥` and the cells labelled `⊤` as it reads `a`.
For every set `Z` of cells of the right type labelled `⊤` of grade at most `3`, the reading layer of
the cell of `a` and the cells of `Z` is legal below the full grade. -/
theorem isLegalBelowFullGrade_readingTop_of_left_twoValued {a : Fin I.left.card}
    (ha : I.left.toCellScheme.gradedIndex a = (univ, 4))
    (hu : ∀ z, I.left.toCellScheme.gradedIndex z = (univ, 4) → z = a)
    (hlab : ∀ z, I.left.label z = ⊥ ∨ I.left.label z = ⊤)
    (hrowlab : ∀ z, I.left.toScheme.rowAt a z = ⊥ ↔ I.left.label z = ⊥)
    (hrowtop : ∀ z, I.left.label z = ⊤ → I.left.toScheme.rowAt a z = I.left.toScheme.rowAt a a)
    (Z : Finset (Fin I.right.card))
    (hZ : ∀ z ∈ Z, I.right.label z = ⊤ ∧ I.right.toCellScheme.grade z ≤ 3) :
    (readingTop I (leftCell I a)
      (Z.image fun z ↦ embed3 I
        (StageType.faceCell I.restrictFace_right z))).IsLegalBelowFullGrade := by
  have hsa : I.left.toCellScheme.scope a = univ := congrArg Prod.fst ha
  have hga : I.left.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hgi : (scheme I).toCellScheme.gradedIndex (leftCell I a) =
      (univ.erase (Fin.last 4), 4) := by
    rw [gradedIndex_leftCell, hsa, hga, univ_map_left_eq]
  have hleft {y : Fin (scheme I).card}
      (hy : y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4)) :
      ∃ z, leftCell I z = y :=
    exists_leftCell_eq fun h ↦ (notMem_erase _ _) (hy.1 h)
  have hgr : (scheme I).toCellScheme.grade (leftCell I a) = 4 := congrArg Prod.snd hgi
  have hrC : leftCell I a ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := by
    rw [CellScheme.mem_below, hgi]
  have huniq : ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      (scheme I).toCellScheme.gradedIndex (leftCell I a) ≤ (scheme I).toCellScheme.gradedIndex y →
        y = leftCell I a := by
    intro y hy hle
    obtain ⟨z, rfl⟩ := hleft hy
    have heq : (scheme I).toCellScheme.gradedIndex (leftCell I z) =
        (univ.erase (Fin.last 4), 4) := le_antisymm hy (hgi ▸ hle)
    rw [gradedIndex_leftCell, ← univ_map_left_eq] at heq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
    rw [map_inj] at h1
    exact congrArg (leftCell I) (hu z (Prod.ext h1 h2))
  -- the rows of the cell of `a`
  have hrowz (z : Fin I.left.card) (hy : leftCell I z ∈ (scheme I).toCellScheme.below
      ((scheme I).toCellScheme.gradedIndex (leftCell I a))) :
      (scheme I).rows.row (leftCell I a) ⟨leftCell I z, hy⟩ = I.left.toScheme.rowAt a z := by
    rw [← Scheme.rowAt_of_mem, rowAt_leftCell]
  have htwo : ∀ y (hy : y ∈ (scheme I).toCellScheme.below
      ((scheme I).toCellScheme.gradedIndex (leftCell I a))),
      (scheme I).rows.row (leftCell I a) ⟨y, hy⟩ ≠ ⊥ →
        (scheme I).rows.row (leftCell I a)
          ⟨leftCell I a, (scheme I).toCellScheme.mem_below_gradedIndex _⟩ ≤
          (scheme I).rows.row (leftCell I a) ⟨y, hy⟩ := by
    intro y hy hne
    obtain ⟨z, rfl⟩ := hleft (hgi ▸ hy)
    rw [hrowz z hy] at hne ⊢
    rw [hrowz a]
    have hz : I.left.label z = ⊤ :=
      (hlab z).resolve_left fun h ↦ hne ((hrowlab z).mpr h)
    exact (hrowtop z hz).ge
  obtain ⟨q, hq, hqe⟩ := exists_isLawful_top (I := I)
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  have hold (d : Fin I.amalgam.card) :
      q (Fin.castAdd _ (embed3 I d)) = I.amalgam.label d := hqe d
  refine isLegalBelowFullGrade_readingTop_of_twoValued hgr hrC huniq htwo (fun x hx ↦ ?_)
    (L := fun d ↦ q (Fin.castAdd _ d)) hL (fun y hy ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    have h2 := congrArg Prod.snd (gradedIndex_embed3 (I := I)
      (StageType.faceCell I.restrictFace_right z))
    simp only [CellScheme.gradedIndex_snd] at h2
    rw [h2, StageType.grade_faceCell]
    exact (hZ z hz).2
  · obtain ⟨z, rfl⟩ := hleft (hgi ▸ hy)
    change q (Fin.castAdd _ (embed3 I (StageType.faceCell I.restrictFace_left z))) = _
    rw [hold, StageType.label_faceCell, hrowz z hy]
    rcases hlab z with h | h
    · rw [h, ite_eq_left ((hrowlab z).mpr h)]
    · rw [h, ite_eq_right fun h' ↦ absurd ((hrowlab z).mp h') (h ▸ top_ne_bot)]
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [hold, StageType.label_faceCell]
    exact (hZ z hz).1

/-! ### At the seed of the right type with itself -/

end TowerProfile

namespace StageType

variable {α : Ordinal.{u}} {k : ℕ} {t₀ : StageType.{u} α k} (ht₀ : t₀.IsLegalBelowFullGrade)
  (hk : 0 < k)

/-- The apex row reads every cell at the code of its label (in the form of `Scheme.rowAt`). -/
theorem rowAt_addApex_last (z : Fin (t₀.addApex ht₀ hk).card) :
    (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) z =
      blockEncode (apexCodes ht₀) k ((t₀.addApex ht₀ hk).label z) := by
  have hz : z ∈ (t₀.addApex ht₀ hk).toCellScheme.below
      ((t₀.addApex ht₀ hk).toCellScheme.gradedIndex (Fin.last _)) := by
    rw [CellScheme.mem_below, addApex_gradedIndex_last ht₀ hk]
    exact Prod.mk_le_mk.mpr ⟨subset_univ _, (t₀.addApex ht₀ hk).grade_le z⟩
  rw [Scheme.rowAt_of_mem hz]
  exact row_addApex_last_eq ht₀ hk hz

/-- The apex row reads a cell as `⊥` exactly when it is labelled `⊥`. -/
theorem rowAt_addApex_last_eq_bot_iff (z : Fin (t₀.addApex ht₀ hk).card) :
    (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) z = ⊥ ↔ (t₀.addApex ht₀ hk).label z = ⊥ := by
  rw [rowAt_addApex_last, blockEncode_eq_bot_iff]

/-- The apex row reads a cell labelled `⊤` as it reads the apex. -/
theorem rowAt_addApex_last_of_top {z : Fin (t₀.addApex ht₀ hk).card}
    (hz : (t₀.addApex ht₀ hk).label z = ⊤) :
    (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) z =
      (t₀.addApex ht₀ hk).toScheme.rowAt (Fin.last _) (Fin.last _) := by
  rw [rowAt_addApex_last ht₀ hk z, rowAt_addApex_last ht₀ hk (Fin.last _), hz]
  exact congrArg _ (addApex_label_last ht₀ hk).symm

end StageType

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

/-- The seed of the right coatom type `rightType` with itself, over the face of `T5`. -/
noncomputable def seedRR (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (isLegal_rightType α) (isLegal_rightType α) (restrictFace_rightType α)
    (restrictFace_rightType α)

/-- The labels of `rightType` are `⊥` or `⊤`. -/
theorem label_rightType_cases (α : Ordinal.{u}) (z : Fin (rightType α).card) :
    (rightType α).label z = ⊥ ∨ (rightType α).label z = ⊤ := by
  unfold rightType at z ⊢
  change Fin ((rightBase α).card + 1) at z
  induction z using Fin.lastCases with
  | last => exact .inr (StageType.addApex_label_last (t := rightBase α) isLegalBelowFullGrade_S
      (by omega))
  | cast d =>
    rw [StageType.addApex_label_castSucc (t := rightBase α) isLegalBelowFullGrade_S (by omega)]
    change CaseSplitCounterexample.labelling ⊤ ⊤ ⊥ d = ⊥ ∨
      CaseSplitCounterexample.labelling ⊤ ⊤ ⊥ d = ⊤
    unfold CaseSplitCounterexample.labelling
    split_ifs <;> simp

/-- **The apex of `rightType` is not isolated**: its row reads the cell `{3}` (labelled `⊤`) as it
reads the apex, not as `⊥`. -/
theorem rowAt_rightType_three_ne_bot (α : Ordinal.{u}) :
    (rightType α).toScheme.rowAt (Fin.last _)
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ≠ ⊥ := by
  intro h
  have h' := (StageType.rowAt_addApex_last_eq_bot_iff (t₀ := rightBase α) isLegalBelowFullGrade_S
    (by omega) (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))).mp h
  revert h'
  change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) ≠ ⊥
  simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
    TwoFaceLiftCounterexample.cellGrade]

/-- **The apex of `rightType` is a top cap and its own marker** (every cell labelled `⊤` is read by
the apex row as the apex itself). -/
theorem isTopCap_isMarker_rightType (α : Ordinal.{u}) :
    (rightType α).IsTopCap (Fin.last _) ∧ (rightType α).IsMarker (Fin.last _) (Fin.last _) := by
  have hlast : (rightType α).label (Fin.last _) = ⊤ :=
    StageType.addApex_label_last (t := rightBase α) isLegalBelowFullGrade_S (by omega)
  have hg : (rightType α).toCellScheme.grade (Fin.last _) = 4 :=
    congrArg Prod.snd (StageType.addApex_gradedIndex_last (t := rightBase α)
      isLegalBelowFullGrade_S (by omega))
  refine ⟨⟨StageType.addApex_scope_last (t := rightBase α) isLegalBelowFullGrade_S (by omega),
    hlast, fun x _ ↦ by rw [hg]; exact (rightType α).grade_le x⟩,
    hlast, (rightType α).toCellScheme.mem_below_gradedIndex _, fun x hx _ ↦ ?_⟩
  exact (StageType.rowAt_addApex_last_of_top (t₀ := rightBase α) isLegalBelowFullGrade_S
    (by omega) hx).ge

/-- **The reading layer at the seed of `rightType` with itself**, at the apex of the left copy (a
top cap and its own marker, not isolated: `rowAt_rightType_three_ne_bot`) and the cell `{3}` of the
right copy (a new top of grade `1`): legal below the full grade
(`TowerProfile.isLegalBelowFullGrade_readingTop_of_left_twoValued`; the apex row is the code of the
labels, which are `⊥` or `⊤`). -/
theorem isLegalBelowFullGrade_readingTop_seedRR (α : Ordinal.{u}) :
    (readingTop (seedRR α) (leftCell (seedRR α) (Fin.last _))
      (({Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)} :
          Finset (Fin (seedRR α).right.card)).image fun z ↦ embed3 (seedRR α)
        (StageType.faceCell (seedRR α).restrictFace_right z))).IsLegalBelowFullGrade := by
  refine isLegalBelowFullGrade_readingTop_of_left_twoValued
    (StageType.addApex_gradedIndex_last (t := rightBase α) isLegalBelowFullGrade_S (by omega))
    (fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex (t := rightBase α)
      isLegalBelowFullGrade_S (by omega) hz)
    (label_rightType_cases α) (fun z ↦ ?_) (fun z hz ↦ ?_) _ fun z hz ↦ ?_
  · exact StageType.rowAt_addApex_last_eq_bot_iff (t₀ := rightBase α) isLegalBelowFullGrade_S
      (by omega) z
  · exact StageType.rowAt_addApex_last_of_top (t₀ := rightBase α) isLegalBelowFullGrade_S
      (by omega) hz
  · rw [mem_singleton.mp hz]
    refine ⟨?_, ?_⟩
    · change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
      simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
        TwoFaceLiftCounterexample.cellGrade]
    · change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).grade
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ≤ 3
      rw [Scheme.appendFullCellScheme_grade_castSucc]
      decide

end TopReadingApexExample

namespace TowerProfile

end TowerProfile

end VaughtConjecture
