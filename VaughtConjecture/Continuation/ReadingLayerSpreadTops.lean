/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerManyTops

/-!
# The reading layer at spread new tops

Roadmap, Layer 3 ((R3) of the table of 3.4).

* **New tops of grade `1` not below one of them** (`TowerProfile.RightTops`, defined here;
  `TowerProfile.readingFillPos_left_of_rowTie_set`,
  `TowerProfile.isLegalBelowFullGrade_readingTop_of_rightTops`, compiled): one server reads all
  the new tops alike (`TowerProfile.exists_server_of_rightType_set`, the raise at the least of
  them), so the fill from it is `⊤` at all of them; two incomparable new tops of grade `1` need no
  second server.
* **The clause at new tops of grade `1`** (`TowerProfile.exists_coface_of_coatoms`,
  `TowerProfile.exists_coface_of_addApex`, compiled under the hypotheses named): as before, with
  `TowerProfile.RightTops` in place of `TowerProfile.RightNewTops`.
* **Servers refine every fill** (`TowerProfile.exists_refiningServer_of_fill`,
  `TowerProfile.ReadingFillPos.exists_refiningServer`, compiled): the fill at the short positive
  caps from the left coatom needs, at every new top `x`, a cell of graded index `(univ, grade x)`
  at least the cap whose row refines the labelling of the left coatom capped at the marker on the
  cells of grade at most that of `x`.  At a new top of grade `2` this is a server of grade `2`
  refining the band at the grades `1` and `2`; without the tie shape of the left coatom type, a
  server of grade `1` refining a band with several values.  The present raise
  (`Scheme.exists_raise_entry`) gives servers agreeing with an available entry below its value at
  the new top, so neither is constructed here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

open TopReadingApexExample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The fill at the short positive caps from the left coatom at a set of new tops of grade
`1`** (as `TowerProfile.readingFillPos_left_of_rowTie`, the new tops not required to lie below one
of them): the server of the set (`TowerProfile.exists_server_of_rightType_set`) reads all the new
tops alike, so the fill from it is `⊤` at all of them. -/
theorem readingFillPos_left_of_rowTie_set (hraise : I.right.RowsRaiseAt 3)
    {r : Fin (scheme I).card} (hgr : (scheme I).toCellScheme.grade r = 4)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {X : Finset (Fin (scheme I).card)}
    (hX : ∀ x ∈ X, ∃ y, embed3 I y = x ∧ Fin.last 4 ∈ I.amalgam.toCellScheme.scope y ∧
      I.amalgam.toCellScheme.grade y = 1)
    {t₁ t₂ : Fin (scheme I).card}
    (ht₁ : t₁ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hg₁ : (scheme I).toCellScheme.grade t₁ = 1)
    (ht₂ : t₂ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    (hg₂ : (scheme I).toCellScheme.grade t₂ = 2)
    (H1 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 1 → f d ≠ ⊥ → f d = f t₁)
    (H2 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 2 → f d ≠ ⊥ → f d = f t₂)
    (H3 : ∀ f : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) → f r ≠ ⊥ →
      ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade d = 3 → f d = ⊥)
    (hr₁ : t₁ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hr₂ : t₂ ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex r))
    (hrow : (scheme I).rowAt r t₂ ≤ (scheme I).rowAt r t₁) :
    ReadingFillPos I r X (Fin.last 4) := by
  classical
  intro e he h hh _ hhb f hf hfe
  have hel : (scheme I).rows.IsLawful e :=
    (Scheme.mem_catalogue.mp (Scheme.readingMarks_subset _ _ he)).1
  have hgE (y : Fin I.amalgam.card) (hy : I.amalgam.toCellScheme.grade y = 1) :
      (scheme I).toCellScheme.grade (embed3 I y) = 1 := by
    rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd, hy]
  have hX3 : ∀ x ∈ X, (scheme I).toCellScheme.grade x ≤ 3 := fun x hx ↦ by
    obtain ⟨y, rfl, -, hy⟩ := hX x hx
    rw [hgE y hy]
    omega
  rcases X.eq_empty_or_nonempty with hXe | hXne
  · obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four (x := Fin.last 4)
      (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hf hel hh hfe
    exact ⟨g, hg, hgf, hga, fun x hx ↦ absurd (hXe ▸ hx) (Finset.notMem_empty x)⟩
  by_cases hre : h ≤ e r
  swap
  · obtain ⟨g, hg, hgf, hga⟩ := exists_fill_four (x := Fin.last 4)
      (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) hf hel hh hfe
    exact ⟨g, hg, hgf, hga, reads_of_lt he (not_le.mp hre) hga⟩
  have hfr : h ≤ f r := Label.le_of_min_eq_of_le' (hfe _ hrC) hre
  by_cases hband : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 3),
      h ≤ f d → f r ≤ f d
  · exact exists_fillPos_left_of_noBand hgr hrC hX3 he hh hhb hf hfe hre hband
  push Not at hband
  obtain ⟨d₀, hd₀, hhd₀, hd₀r⟩ := hband
  have hfr0 : f r ≠ ⊥ := (hhb.trans_le hfr).ne'
  have hpos (d : Fin (scheme I).card) : 1 ≤ (scheme I).toCellScheme.grade d :=
    isWellFormed_scheme.isWellFormed.grade_pos d
  -- the band: `h ≤ A` and `F ≤ A`
  have hd₀C : d₀ ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) :=
    (CellScheme.mem_below _).mpr (le_trans ((CellScheme.mem_below _).mp hd₀)
      (Prod.mk_le_mk.mpr ⟨subset_rfl, by omega⟩))
  have htie : min (f t₂) (f r) ≤ min (f t₁) (f r) :=
    ((CellScheme.Rows.isLawfulBelow_iff_forall.mp hf).2.1 r hrC).le_of_le
      (d := ⟨t₂, hr₂⟩) (d' := ⟨t₁, hr₁⟩)
      (by rw [← Scheme.rowAt_of_mem, ← Scheme.rowAt_of_mem]; exact hrow) (by rw [hg₁, hg₂]; omega)
  have hd₀3 : (scheme I).toCellScheme.grade d₀ ≤ 3 :=
    ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd₀)).2
  have hd₀0 : f d₀ ≠ ⊥ := (hhb.trans_le hhd₀).ne'
  obtain ⟨hhA, hFA⟩ : h ≤ f t₁ ∧ f t₂ ≤ f t₁ := by
    rcases (show (scheme I).toCellScheme.grade d₀ = 1 ∨ (scheme I).toCellScheme.grade d₀ = 2 ∨
        (scheme I).toCellScheme.grade d₀ = 3 by have := hpos d₀; omega) with h1 | h2 | h3
    · rw [H1 f hf hfr0 d₀ hd₀C h1 hd₀0] at hhd₀ hd₀r
      rw [min_eq_left hd₀r.le] at htie
      refine ⟨hhd₀, ?_⟩
      rcases lt_or_ge (f t₂) (f r) with hlt | hge
      · rwa [min_eq_left hlt.le] at htie
      · rw [min_eq_right hge] at htie
        exact absurd htie (not_le.mpr hd₀r)
    · rw [H2 f hf hfr0 d₀ hd₀C h2 hd₀0] at hhd₀ hd₀r
      rw [min_eq_left hd₀r.le] at htie
      have hF := htie.trans (min_le_left _ _)
      exact ⟨hhd₀.trans hF, hF⟩
    · exact absurd (H3 f hf hfr0 d₀ hd₀C h3) hd₀0
  -- the server
  set Xa : Finset (Fin I.amalgam.card) := (univ : Finset (Fin I.amalgam.card)).filter fun y ↦
    embed3 I y ∈ X ∧ Fin.last 4 ∈ I.amalgam.toCellScheme.scope y ∧
      I.amalgam.toCellScheme.grade y = 1 with hXadef
  have hmemXa {x : Fin (scheme I).card} (hx : x ∈ X) : ∃ y ∈ Xa, embed3 I y = x := by
    obtain ⟨y, rfl, hPy, hgy⟩ := hX x hx
    exact ⟨y, mem_filter.mpr ⟨mem_univ _, hx, hPy, hgy⟩, rfl⟩
  have hXane : Xa.Nonempty := by
    obtain ⟨x, hx⟩ := hXne
    obtain ⟨y, hy, -⟩ := hmemXa hx
    exact ⟨y, hy⟩
  obtain ⟨u, hu, hxu, xa, hxa, hlt, hall, hcode⟩ := exists_server_of_rightType_set
    I.restrictFace_right hraise (hel.isLawfulBelow _) hXane
    (fun y hy ↦ (mem_filter.mp hy).2.2.1) (fun y hy ↦ (mem_filter.mp hy).2.2.2) hhb
    (fun y hy ↦ hre.trans (Scheme.le_of_mem_readingMarks he (mem_filter.mp hy).2.1))
  have hgx := hgE xa (mem_filter.mp hxa).2.2.2
  have hex : h ≤ e (embed3 I xa) := hre.trans (Scheme.le_of_mem_readingMarks he
    (mem_filter.mp hxa).2.1)
  have hvis {d : Fin (scheme I).card} (hd : (scheme I).toCellScheme.grade d = 1) :
      IsSelfVisible 1 ((scheme I).rowAt u d) := by
    have := (CellScheme.Rows.isLawfulBelow_iff_forall.mp (isLawfulBelow_rowAt hu)).1 d
      ⟨subset_univ _, hd.le⟩
    rwa [hd] at this
  have hleft {d : Fin (scheme I).card}
      (hd : d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
      (hg : (scheme I).toCellScheme.grade d = 1) :
      (scheme I).rowAt u d < (scheme I).rowAt u (embed3 I xa) := by
    have hsd := ((scheme I).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hd)).1
    obtain ⟨dam, rfl⟩ := mem_range_embed3 d fun h' ↦ last_notMem_of_subset hsd (h' ▸ mem_univ _)
    refine hlt dam (by rw [← scope_embed3]; exact last_notMem_of_subset hsd) ?_
    rw [← CellScheme.gradedIndex_snd, ← gradedIndex_embed3, CellScheme.gradedIndex_snd, hg]
  have hnex : (scheme I).rowAt u (embed3 I xa) ≠ ⊥ := (bot_le.trans_lt (hleft ht₁ hg₁)).ne'
  obtain ⟨β, hβ⟩ := exists_eq_omega0_mul_add_one hcode (hvis hgx) hnex
  -- the fill from the server
  obtain ⟨hfo, -, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hf
  obtain ⟨g, hg, hgf, hga, hgxtop⟩ := exists_fill_of_server hel hh hhb hf hfe hgx hex hu
    hxu hβ (V := max h (f t₂)) (by have := hfo t₁ ht₁; rwa [hg₁] at this) hhA
    (fun d hd hg h0 ↦ ⟨H1 f hf hfr0 d hd hg h0,
      lt_omega0_mul_of_lt_add_one (hvis hg) (hβ ▸ hleft hd hg)⟩)
    ((hh.mono (by omega)).max (by have := hfo t₂ ht₂; rwa [hg₂] at this))
    (le_max_left _ _) (max_le hhA hFA)
    (fun d hd hg hfd ↦ by
      have h0 : f d ≠ ⊥ := (hhb.trans_le hfd).ne'
      rcases (show (scheme I).toCellScheme.grade d = 1 ∨ (scheme I).toCellScheme.grade d = 2 by
          have := hpos d; omega) with h1 | h2
      · rw [H1 f hf hfr0 d hd h1 h0]
        exact max_le hhA hFA
      · rw [H2 f hf hfr0 d hd h2 h0] at hfd ⊢
        exact max_le hfd le_rfl)
    (fun d hd hg hfd ↦ by
      rw [H2 f hf hfr0 d hd hg (hhb.trans_le hfd).ne']
      exact le_max_right _ _)
    (fun d hd hg ↦ by rw [H3 f hf hfr0 d hd hg]; exact bot_le)
  refine ⟨g, hg, hgf, hga, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hmemXa hx
  rw [hgxtop _ (hgE y (mem_filter.mp hy).2.2.2) (hall y hy).ge]
  exact le_top

/-- **A right coatom type with new tops of grade `1`** `Z`: its rows raise at the point `3`
(`StageType.RowsRaiseAt`), and every cell of `Z` lies through `3`, has grade `1`, and is labelled
`⊤`.  The cells of `Z` need not lie below one of them (as in `TowerProfile.RightNewTops`). -/
structure RightTops (tb : StageType.{u} α 4) (Z : Finset (Fin tb.card)) : Prop where
  rowsRaiseAt : tb.RowsRaiseAt 3
  mem_scope : ∀ z ∈ Z, (3 : Fin 4) ∈ tb.toCellScheme.scope z
  grade_eq : ∀ z ∈ Z, tb.toCellScheme.grade z = 1
  label_eq : ∀ z ∈ Z, tb.label z = ⊤

/-- New tops below one of grade `1` are new tops of grade `1`. -/
theorem RightNewTops.rightTops {tb : StageType.{u} α 4} {Z : Finset (Fin tb.card)}
    {x₀ : Fin tb.card} (hR : RightNewTops tb Z x₀) : RightTops tb Z :=
  ⟨hR.rowsRaiseAt, hR.mem_scope, fun z hz ↦ le_antisymm
    ((Prod.mk_le_mk.mp (hR.le z hz)).2.trans_eq hR.grade_eq)
    (tb.isWellFormed.isWellFormed.grade_pos z), hR.label_eq⟩

theorem grade_le_one_of_rightTops {Z : Finset (Fin I.right.card)} (hR : RightTops I.right Z)
    {x : Fin (scheme I).card} (hx : x ∈ newTopsOf I Z) : (scheme I).toCellScheme.grade x ≤ 1 := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
  rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd,
    StageType.grade_faceCell, hR.grade_eq z hz]

/-- **The fill at the short positive caps from the left coatom at new tops of grade `1`**
(`TowerProfile.readingFillPos_left_of_rowTie_set`). -/
theorem readingFillPos_left_of_rightTops {a z₁ z₂ : Fin I.left.card} {n : ℕ}
    {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {Z : Finset (Fin I.right.card)}
    (hR : RightTops I.right Z) :
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
  refine readingFillPos_left_of_rowTie_set hR.rowsRaiseAt hgr hrC
    (fun x hx ↦ by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      exact ⟨_, rfl, hP z hz, (StageType.grade_faceCell _ _).trans (hR.grade_eq z hz)⟩)
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

/-- **The restricted reading layer at new tops of grade `1` is legal below the full grade** at every
seed on five points whose left coatom type has a tie-keeping marker and whose right coatom type
has a set of new tops of grade `1` through the point `3` (not required to lie below one of them):
the four fill conditions. -/
theorem isLegalBelowFullGrade_readingTop_of_rightTops {a z₁ z₂ : Fin I.left.card}
    {n : ℕ} {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {Z : Finset (Fin I.right.card)}
    (hR : RightTops I.right Z) :
    (readingTop I (leftCell I a) (newTopsOf I Z)).IsLegalBelowFullGrade := by
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hX3 : ∀ x ∈ newTopsOf I Z, (scheme I).toCellScheme.grade x ≤ 3 :=
    fun x hx ↦ (grade_le_one_of_rightTops hR hx).trans (by omega)
  refine (isLegalBelowFullGrade_readingTop_iff hgr fun x hx ↦ (hX3 x hx).trans (by omega)).mpr
    ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillBot_left_of_left hL.gradedIndex_apex hL.rowAt_apex hL.face_bot _
        hR.label_eq
    · rw [mem_singleton.mp hz]
      exact readingFillBot_right_of_unique hgr hrC huniq
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillPos_left_of_rightTops hL hR
    · rw [mem_singleton.mp hz]
      exact readingFillPos_right_of_unique hgr hrC huniq hX3


/-! ### Servers refine every fill -/

/-- **Every fill has a refining server at the grade of each cell at least the cap.**  Let `g` be
lawful below `(univ, 4)` in the profile layer, agreeing with `e` capped at `h`, and `s` a cell
with `h ≤ g s`.  Some cell `u` of graded index `(univ, grade s)` with `h ≤ e u` and `g s ≤ g u`
has a row refining `g` capped at `g s` on the cells of grade at most that of `s`: availability at
`s`, and locality at `u`. -/
theorem exists_refiningServer_of_fill {e g : Fin (scheme I).card → Label.{u}} {h : Label.{u}}
    (hg : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ g d)
    (hga : ∀ d, min (g d) h = min (e d) h) {s t : Fin (scheme I).card}
    (ht : (scheme I).toCellScheme.gradedIndex t =
      ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade s)) (hhs : h ≤ g s) :
    ∃ u, (scheme I).toCellScheme.gradedIndex u =
        ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade s) ∧ h ≤ e u ∧ g s ≤ g u ∧
      ∀ y y', (scheme I).toCellScheme.grade y ≤ (scheme I).toCellScheme.grade s →
        (scheme I).toCellScheme.grade y' ≤ (scheme I).toCellScheme.grade y →
        (scheme I).rowAt u y ≤ (scheme I).rowAt u y' → min (g y) (g s) ≤ min (g y') (g s) := by
  obtain ⟨-, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hg
  obtain ⟨u, hu, hsu⟩ := havail s t (mem_below_univ_four t)
    (by rw [show (scheme I).toCellScheme.scope t = univ from congrArg Prod.fst ht];
        exact subset_univ _)
    (congrArg Prod.snd ht).symm
  have hu' := hu.trans ht
  have heu : h ≤ e u := by
    have := hga u
    rw [min_eq_right (hhs.trans hsu)] at this
    exact min_eq_right_iff.mp this.symm
  refine ⟨u, hu', heu, hsu, fun y y' hy hy' hrow ↦ ?_⟩
  have hyb : y ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex u) := by
    rw [hu']; exact ⟨subset_univ _, hy⟩
  have hyb' : y' ∈ (scheme I).toCellScheme.below ((scheme I).toCellScheme.gradedIndex u) := by
    rw [hu']; exact ⟨subset_univ _, hy'.trans hy⟩
  have h1 := (hloc u (mem_below_univ_four u)).le_of_le (d := ⟨y, hyb⟩) (d' := ⟨y', hyb'⟩)
    (by rw [← Scheme.rowAt_of_mem, ← Scheme.rowAt_of_mem]; exact hrow) hy'
  change min (g y) (g u) ≤ min (g y') (g u) at h1
  calc min (g y) (g s) = min (min (g y) (g u)) (g s) := by
        rw [min_assoc, min_eq_right hsu]
    _ ≤ min (min (g y') (g u)) (g s) := min_le_min_right _ h1
    _ = min (g y') (g s) := by rw [min_assoc, min_eq_right hsu]

/-- **The fill at the short positive caps from the left coatom needs a refining server at every new
top** (`TowerProfile.exists_refiningServer_of_fill` at the new top): if
`ReadingFillPos I r X (Fin.last 4)`, then for every reading mark `e` with `h ≤ e r`, every `f`
lawful below the left coatom agreeing with `e` capped at `h`, and every new top `x` with a cell of
graded index `(univ, grade x)`, some cell `u` of graded index `(univ, grade x)` with `h ≤ e u` has a
row refining `f` capped at `f r` on the cells of the left coatom of grade at most that of `x`.  At
a new top of grade `2` this is a server of grade `2` refining the band of `f` at the grades `1` and
`2`; without the tie shape of the left coatom type, a server of grade `1` refining the band of `f`
at the grade `1`. -/
theorem ReadingFillPos.exists_refiningServer {r : Fin (scheme I).card}
    {X : Finset (Fin (scheme I).card)} (hfill : ReadingFillPos I r X (Fin.last 4))
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4))
    {e f : Fin (scheme I).card → Label.{u}} (he : e ∈ (scheme I).readingMarks 4 r X)
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hs : IsShort 4 h) (hhb : ⊥ < h)
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
    (hfe : ∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
      min (f d) h = min (e d) h) (hre : h ≤ e r)
    {x t : Fin (scheme I).card} (hx : x ∈ X)
    (ht : (scheme I).toCellScheme.gradedIndex t =
      ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x)) :
    ∃ u, (scheme I).toCellScheme.gradedIndex u =
        ((univ : Finset (Fin 5)), (scheme I).toCellScheme.grade x) ∧ h ≤ e u ∧
      ∀ y ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        ∀ y' ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        (scheme I).toCellScheme.grade y ≤ (scheme I).toCellScheme.grade x →
        (scheme I).toCellScheme.grade y' ≤ (scheme I).toCellScheme.grade y →
        (scheme I).rowAt u y ≤ (scheme I).rowAt u y' → min (f y) (f r) ≤ min (f y') (f r) := by
  obtain ⟨g, hg, hgf, hga, hgr⟩ := hfill e he h hh hs hhb f hf hfe
  have hfr : h ≤ f r := Label.le_of_min_eq_of_le' (hfe _ hrC) hre
  have hrx : f r ≤ g x := (hgf r hrC).symm.trans_le (hgr x hx)
  obtain ⟨u, hu, heu, -, href⟩ := exists_refiningServer_of_fill hg hga ht (hfr.trans hrx)
  refine ⟨u, hu, heu, fun y hy y' hy' hgy hgy' hrow ↦ ?_⟩
  have h1 := href y y' hgy hgy' hrow
  rw [hgf y hy, hgf y' hy'] at h1
  calc min (f y) (f r) = min (min (f y) (g x)) (f r) := by rw [min_assoc, min_eq_right hrx]
    _ ≤ min (min (f y') (g x)) (f r) := min_le_min_right _ h1
    _ = min (f y') (f r) := by rw [min_assoc, min_eq_right hrx]

/-! ### The clause at new tops of grade `1` -/

open StageType

variable (hα : Order.IsSuccLimit α)

include hα in
/-- **The clause at a context and a coface** (`TowerProfile.exists_coface_of_legal` at the seed of
the two coatom types): for a legal context `t'` with face `p` along `Fin.castSuccEmb` and a
tie-keeping marker, every coface `tb` of `p` with new tops `Z` of grade `1`
(`TowerProfile.RightTops`), every root of at most two points and
every donor of `tb` whose new tops labelled `⊤` lie in `Z`. -/
theorem exists_coface_of_coatoms {t' tb : StageType.{u} α 4} {p : StageType.{u} α 3}
    (hlt : t'.IsLegal) (hpa : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
    {a z₁ z₂ : Fin t'.card} {m : ℕ} {ι : Fin m ↪ Fin 4} (hL : LeftTie t' ι a z₁ z₂)
    {Z : Finset (Fin tb.card)} (hR : RightTops tb Z)
    {n : ℕ} (g : Fin n ↪ Fin 3) (hn : n ≤ 2) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast g) tb = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d :=
  exists_coface_of_legal (I := Seed.ofCoatoms hlt htb.1 hpa htb.2) hL hR.label_eq
    (isLegalBelowFullGrade_readingTop_of_rightTops hL hR) hα hn hd hcover

/-- The apex type of a type on four points legal below the full grade. -/
noncomputable abbrev apexOf {t₀ : StageType.{u} α 4} (ht₀ : t₀.IsLegalBelowFullGrade) :
    StageType.{u} α 4 :=
  t₀.addApex ht₀ (by omega)

include hα in
/-- **The clause at every acquired apex context of the `StageType.markedCapContextBelow'_addApex`
family** (compiled under the hypotheses named): let `t' = t₀.addApex` be the apex context of a type
`t₀` legal below the full grade, with the conditions of `StageType.markedCapContextBelow'_addApex`
along a root `ι` (root labels never `⊤`, root offsets below `4`), the common face labelled `⊥`
(`hface`), and the tie shape: root cells `z₁`, `z₂` of grades `1`, `2` (`z₂` labelled `⊥` or with
the proper label of `z₁`), one value at the cells of grade `1` not labelled `⊥` (`htie`), one at
those of grade `2` (`htwo`), the cells of grade `3` labelled `⊥` (`hthree`).  Then the clause of
hollow coatom cutoff determination holds at `t'`, every coface `tb` of its face with new tops `Z`
(`TowerProfile.RightTops`), every root `g` of at most two points, and every donor of `tb` along
`extendByLast g` whose new tops labelled `⊤` lie in `Z`.  The apex is the cap and the marker; its
uniqueness at `(univ, 4)`, its grade and the reading of the cells labelled `⊥` as `⊥` are those of
the apex row. -/
theorem exists_coface_of_addApex {t₀ : StageType.{u} α 4} (ht₀ : t₀.IsLegalBelowFullGrade)
    {p : StageType.{u} α 3}
    (hpa : restrictFace Fin.castSuccEmb (apexOf ht₀) = some p)
    {m : ℕ} {ι : Fin m ↪ Fin 4} (hm : m + 1 < 4)
    (hroot : ∀ y ∈ (apexOf ht₀).visibleCells ι,
      (apexOf ht₀).label y ≠ ⊤)
    (hoff : ∀ y ∈ (apexOf ht₀).visibleCells ι, ∀ (μ : Ordinal.{u}) (f : ℕ),
      Order.IsSuccPrelimit μ →
        (apexOf ht₀).label y = ((μ + f : Ordinal.{u}) : Label.{u}) → f < 4)
    (hface : ∀ z, Fin.last 3 ∉ (apexOf ht₀).toCellScheme.scope z →
      (apexOf ht₀).label z = ⊥)
    {z₁ z₂ : Fin (apexOf ht₀).card}
    (hz₁ : z₁ ∈ (apexOf ht₀).visibleCells ι)
    (hz₂ : z₂ ∈ (apexOf ht₀).visibleCells ι)
    (hg₁ : (apexOf ht₀).toCellScheme.grade z₁ = 1)
    (hg₂ : (apexOf ht₀).toCellScheme.grade z₂ = 2)
    (hlab : (apexOf ht₀).label z₂ = ⊥ ∨
      ((apexOf ht₀).label z₂ = (apexOf ht₀).label z₁ ∧
        IsProper ((apexOf ht₀).label z₂)))
    (htie : ∀ q : Fin (apexOf ht₀).card → Label.{u},
      (apexOf ht₀).rows.IsLawful q → ∀ z,
        (apexOf ht₀).toCellScheme.grade z = 1 →
          (apexOf ht₀).label z ≠ ⊥ → q z = q z₁)
    (htwo : ∀ q : Fin (apexOf ht₀).card → Label.{u},
      (apexOf ht₀).rows.IsLawful q → ∀ z,
        (apexOf ht₀).toCellScheme.grade z = 2 →
          (apexOf ht₀).label z ≠ ⊥ → q z = q z₂)
    (hthree : ∀ z, (apexOf ht₀).toCellScheme.grade z = 3 →
      (apexOf ht₀).label z = ⊥)
    {tb : StageType.{u} α 4} (htb : tb ∈ p.cofaces)
    {Z : Finset (Fin tb.card)} (hR : RightTops tb Z)
    {n : ℕ} (g : Fin n ↪ Fin 3) (hn : n ≤ 2) {d : StageType.{u} α (n + 1)}
    (hd : restrictFace (extendByLast g) tb = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    ∃ D' ∈ (apexOf ht₀).cofaces,
      restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) (apexOf ht₀)
          (g.trans Fin.castSuccEmb) d := by
  obtain ⟨c, r, hctx, hoff', hbot⟩ :=
    StageType.markedCapContextBelow'_addApex ht₀ (by omega) hm hroot hoff
  have hg4 : (t₀.addApex ht₀ (by omega)).toCellScheme.grade (Fin.last _) = 4 :=
    congrArg Prod.snd (StageType.addApex_gradedIndex_last ht₀ (by omega))
  have hc : c = Fin.last _ := by
    refine StageType.eq_of_grade_addApex ht₀ (by omega) (le_antisymm
      ((t₀.addApex ht₀ (by omega)).grade_le c) ?_)
    exact hg4.symm.le.trans (hctx.1.2.2 _ (StageType.addApex_label_last ht₀ (by omega)))
  subst hc
  exact exists_coface_of_coatoms hα (StageType.isLegal_addApex _ _) hpa htb
    (leftTie_of_acquired hctx hoff' hbot hg4
      (fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex ht₀ (by omega) hz)
      (fun z _ hz ↦ (StageType.rowAt_addApex_last_eq_bot_iff ht₀ (by omega) z).mpr hz)
      hface hz₁ hz₂ hg₁ hg₂ hlab htie htwo hthree) hR g hn hd hcover

end TowerProfile

end VaughtConjecture
