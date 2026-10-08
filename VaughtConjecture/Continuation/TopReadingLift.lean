/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.FieldLayerForcedTops
import VaughtConjecture.Extension.MarkedCatalogueCompletion

/-!
# A separating lift forces a top reading the marker above a new top

Roadmap, Layer 3 ((R3) of the table of 3.4).

A top-reading carrier (`StageType.IsTopReadingCarrier`) asks every cell of graded index
`(univ, N)` labelled `⊤` to read every new top `x` at least as the marker `r`; the marker is
labelled `⊤` (`StageType.IsMarker`).  This file compiles the mechanism by which a lift of the
carrier's rows defeats that reading, for every scheme, and its instance for every leaf-and-marked
layer (`Scheme.markedLayer`, any marked set, any cap).

* **The forcing lemma** (`CellScheme.Rows.IsLawful.exists_top_row_lt`, compiled in this repository
  (theorem named)).  Let `q` be a lawful section, `u` a cell labelled `⊤` whose row reads `r` at
  most as `x` (the reading holds at `u`), with `r` of the grade of `u`, `x` of grade at most that,
  and `r` labelled `⊤`.  If some labelling `w` lawful below the graded index of `u` agrees with the
  row of `u` capped at its value `τ` at `r` and has `w x < w r`, then some cell `v` of the graded
  index of `u` is labelled `⊤` in `q` and its row reads `x` strictly below `r`.  Availability of
  `w` at `r` gives `v` with `w r ≤ w v`; the cap gives that the row of `u` reads `v` at least as
  `r`, so `v` is a top of `q` (`CellScheme.Rows.IsLawful.eq_top_of_row_le`); locality of `w` at
  `v`, monotone in the source and antitone in the grade, gives the strict reading.
* **In a sheet layer** (`Scheme.exists_top_sheetRow_lt`): the separating `w` is the extension at
  the cap `τ` along the row of a new cell `j` (`Scheme.exists_extension_sheetLayer`) of a fill `p`
  of the old cells that agrees with the entry of `j` capped at `τ` and has `p x < p r`, given a
  template.  So in every lawful section of a sheet layer in which a new cell `j` labelled `⊤`
  reads `r` at most as `x`, and the old cell `r` is labelled `⊤`, the reading fails at some new
  cell labelled `⊤`, as soon as such a fill and its template exist.
* **The instance** (`FieldLayerForcedTops.exists_top_reads_lt_markedLayer`): over the scheme of two
  cells of grade `1` with rows `⊤` (`FieldLayerForcedTops.twoScheme`), for **every** leaf-and-marked
  layer (every marked subset of the catalogue and every cap with values in the field grid that
  respects capped agreement and satisfies marked closure), every lawful section labelling the old
  cell `0` (the marker) with `⊤` has a new cell labelled `⊤` that reads the cell `1` strictly below
  the cell `0`; the label of the cell `1` is not used.  The fill is `(ω * 5 + 1, τ)`.
* **At the completion at `m = 3`** (`TowerProfile.exists_top_reads_lt_markedTop`): the same for the
  marked top of every seed on five points and every marked specification, for old cells `x`, `r`
  of the profile layer with `r` of the grade `4`, given a fill of the profile layer below
  `(univ, 4)` that agrees with the entry of the reading cell capped at `τ` and separates `x` below
  `r`.

* **The fill is a raise in a coatom** (`TowerProfile.exists_top_reads_lt_markedTop_of_raise`): when
  `x` has grade at most `3` (so at every marked-cap context on at most four points, where the donor
  has at most three points) and `r` lies below a coatom, the separating fill is the extension
  (`TowerProfile.exists_isLawfulBelow_four`) of a labelling that equals the entry below `(univ, 3)`
  and is raised at `r` within the coatom at the grade `4`.  A tie blocks the raise
  (`CellScheme.Rows.IsLawful.le_of_row_self_le_below`): if the row of `r` reads `r` at most as a
  cell `y` of grade at most that of `r`, every lawful labelling has `w r ≤ w y`.

**What is refuted.**  A carrier whose cells of graded index `(univ, N)` form a leaf-and-marked
layer (any marked subset, any cap), in which the marker `r` has the grade `N`, labelled through a
cell that reads `r` at most as a new top `x`, and over which a separating fill with its template
exists, is not a top-reading carrier: some cell labelled `⊤` reads `x` below `r`.  More generally
(the forcing lemma) no legal scheme with such a labelling and such a separating lawful labelling
below `(univ, N)` is.  This does not refute `StageType.HasTopReadingCarriers`: the marker may have
a grade below `N` (availability at `(univ, N)` then does not apply to `r`), and for a general legal
carrier the separating labelling below `(univ, N)` comes from a capped lift out of a face, so it
exists only when that face admits the separating fill (argued, not formalized).  The fill at a
concrete seed and marked-cap context with the marker of grade `4` is not built here (prospective);
at the scheme of two cells it is built.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The forcing lemma -/

/-! ### In a sheet layer -/

namespace FieldLayerForcedTops

open Scheme

/-- The value of a catalogue entry at a cell of `twoScheme` lies below `ω * 5 + 1`. -/
private theorem lt_gridPoint_five {e : Fin twoScheme.{u}.card → Label.{u}}
    (he : e ∈ twoScheme.{u}.catalogue 1) (d : Fin 2) : e d < gridPoint 1 5 :=
  (le_gridPoint_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue he d)).trans_lt
    (gridPoint_lt_gridPoint.mpr (by simp))

/-- **Every leaf-and-marked layer over two cells has a top reading `1` below `0`.**  For every
marked subset `Mk` of the catalogue of `twoScheme` at the grade `1` and every cap `κ` with values in
the field grid that respects capped agreement and satisfies marked closure, every lawful section of
the leaf-and-marked layer labelling the old cell `0` with `⊤` labels `⊤` some new cell whose entry
is strictly smaller at the cell `1` than at the cell `0`. -/
theorem exists_top_reads_lt_markedLayer {Mk : Finset (Fin twoScheme.{u}.card → Label.{u})}
    {κ : (Fin twoScheme.{u}.card → Label.{u}) → Label.{u}} (hMk : Mk ⊆ twoScheme.{u}.catalogue 1)
    (hκ : ∀ e, κ e ∈ twoScheme.{u}.fieldGrid 1) (hκr : CapRespects twoScheme.{u} 1 κ)
    (hcl : MarkedClosed twoScheme.{u} 1 Mk κ)
    {q : Fin (twoScheme.{u}.markedLayer 1 Mk κ not_univ_le.{u}).card → Label.{u}}
    (hq : (twoScheme.{u}.markedLayer 1 Mk κ not_univ_le.{u}).rows.IsLawful q)
    (h0 : q (Fin.castAdd _ 0) = ⊤) :
    ∃ j, q (Fin.natAdd twoScheme.{u}.card j) = ⊤ ∧
      twoScheme.{u}.markedEntry 1 Mk j 1 < twoScheme.{u}.markedEntry 1 Mk j 0 := by
  have hε := markedEntry_mem (k := 1) hMk
  -- a new cell labelled `⊤`, by availability at the old cell `0`
  obtain ⟨i₀, -⟩ := exists_catalogueEntry_eq orbitCode_topInput_mem.{u}
  obtain ⟨v, hv, hle⟩ := hq.availability (Fin.castAdd _ 0) (Fin.natAdd _ (Fin.castAdd _ i₀))
    (by rw [appendFullCellsScheme_scope_natAdd]; exact subset_univ _)
    (by rw [appendFullCellsScheme_grade_natAdd, appendFullCellsScheme_grade_castAdd]; rfl)
  obtain ⟨j, rfl⟩ := exists_natAdd_eq_sheetLayer
    (hv.trans (appendFullCellsScheme_gradedIndex_natAdd _ _ _ _))
  have hqj : q (Fin.natAdd _ j) = ⊤ := top_le_iff.mp (h0 ▸ hle)
  set e := twoScheme.markedEntry 1 Mk j
  by_cases hread : e 0 ≤ e 1
  swap
  · exact ⟨j, hqj, not_le.mp hread⟩
  -- the reading holds at `j`; the value at `0` is not bottom, by locality at `j`
  have hτ : ⊥ < e 0 := by
    refine bot_lt_iff_ne_bot.mpr fun h ↦ ?_
    have hmem : Fin.castAdd _ (0 : Fin twoScheme.{u}.card) ∈
        (twoScheme.{u}.markedLayer 1 Mk κ not_univ_le.{u}).toCellScheme.below
          ((twoScheme.{u}.markedLayer 1 Mk κ not_univ_le.{u}).toCellScheme.gradedIndex
            (Fin.natAdd _ j)) := by
      rw [appendFullCellsScheme_gradedIndex_natAdd]
      exact castAdd_mem_below_sheetLayer (hS := not_univ_le) le_rfl
    have hrow : (twoScheme.{u}.markedLayer 1 Mk κ not_univ_le.{u}).rows.row (Fin.natAdd _ j)
        ⟨_, hmem⟩ = ⊥ := by
      rw [sheetLayer_row_natAdd, sheetRow_castAdd]
      exact h
    have := (hq.locality (Fin.natAdd _ j)).eq_bot hrow
    -- locality reads `min (q 0) (q j)` at the old cell `0`
    change min (q (Fin.castAdd _ (0 : Fin twoScheme.{u}.card))) (q (Fin.natAdd _ j)) = ⊥ at this
    rw [h0, hqj, min_self] at this
    exact top_ne_bot this
  have hvis : IsSelfVisible 1 (e 0) := (mem_catalogue.mp (hε j)).1.orderly 0
  have hs : IsShort 1 (e 0) := isShort_of_mem_codeGrid (mem_codeGrid_of_mem_catalogue (hε j) 0)
  -- the fill: `ω * 5 + 1` at `0`, the cap at `1`
  set p : Fin 2 → Label.{u} := ![gridPoint 1 5, e 0]
  have hpv : ∀ d, IsSelfVisible 1 (p d) :=
    Fin.forall_fin_two.mpr ⟨isSelfVisible_gridPoint 1 5, hvis⟩
  have hp : twoScheme.{u}.rows.IsLawful p := isLawful_of_isSelfVisible hpv
  have hag : ∀ d, min (p d) (e 0) = min (e d) (e 0) := Fin.forall_fin_two.mpr
    ⟨by
      change min (gridPoint 1 5) (e 0) = min (e 0) (e 0)
      rw [min_self, min_eq_right (lt_gridPoint_five (hε j) 0).le],
    by
      change min (e 0) (e 0) = min (e 1) (e 0)
      rw [min_self, min_eq_right hread]⟩
  have hlt : p 1 < p 0 := lt_gridPoint_five (hε j) 0
  obtain ⟨j₀, hj₀, hσ⟩ := exists_template_markedLayer hMk hcl hvis hs hτ j
    (hp.isLawfulBelow _) fun d _ ↦ hag d
  obtain ⟨j'', hqj'', hlt''⟩ := exists_top_sheetRow_lt (hS := not_univ_le) hε hκ hκr hq
    (x := 1) (r := 0) rfl le_rfl hqj h0 hread hτ (fun d _ ↦ hag d) hlt hj₀ hσ
  exact ⟨j'', hqj'', hlt''⟩

/-- **When the marked cells read `1` at least as `0`, the forced top is a leaf.**  As
`exists_top_reads_lt_markedLayer`, for a marked subset whose members all have `e 0 ≤ e 1`: the
new cell labelled `⊤` that reads `1` strictly below `0` is a leaf.  So the labellings that label a
leaf `⊤` are not excluded by any choice of marked subset or cap: every lawful section with the
marker `⊤` is one. -/
theorem exists_top_leaf_reads_lt_markedLayer
    {Mk : Finset (Fin twoScheme.{u}.card → Label.{u})}
    {κ : (Fin twoScheme.{u}.card → Label.{u}) → Label.{u}} (hMk : Mk ⊆ twoScheme.{u}.catalogue 1)
    (hκ : ∀ e, κ e ∈ twoScheme.{u}.fieldGrid 1) (hκr : CapRespects twoScheme.{u} 1 κ)
    (hcl : MarkedClosed twoScheme.{u} 1 Mk κ) (hP : ∀ e ∈ Mk, e 0 ≤ e 1)
    {q : Fin (twoScheme.{u}.markedLayer 1 Mk κ not_univ_le.{u}).card → Label.{u}}
    (hq : (twoScheme.{u}.markedLayer 1 Mk κ not_univ_le.{u}).rows.IsLawful q)
    (h0 : q (Fin.castAdd _ 0) = ⊤) :
    ∃ i, q (Fin.natAdd twoScheme.{u}.card (Fin.castAdd Mk.card i)) = ⊤ ∧
      twoScheme.{u}.catalogueEntry 1 i 1 < twoScheme.{u}.catalogueEntry 1 i 0 := by
  obtain ⟨j, hqj, hlt⟩ := exists_top_reads_lt_markedLayer hMk hκ hκr hcl hq h0
  induction j using Fin.addCases with
  | left i =>
    rw [markedEntry_castAdd] at hlt
    exact ⟨i, hqj, hlt⟩
  | right m =>
    rw [markedEntry_natAdd] at hlt
    exact absurd (hP _ (markEntry_mem Mk m)) (not_le.mpr hlt)

end FieldLayerForcedTops

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (D : MarkedSpec I)

/-- **At the marked top, a separating fill forces a top reading `r` above `x`.**  For every marked
specification `D` of a seed on five points, every lawful section `q` of the marked top, every new
cell `j` labelled `⊤` whose entry reads `r` at most as `x` (`r` of the grade `4`, `x` of grade at
most `4`, `r` labelled `⊤`, the value at `r` not `⊥`), and every fill `p` of the profile layer
lawful below `(univ, 4)` that agrees with the entry of `j` capped at its value at `r` and has
`p x < p r`, some new cell labelled `⊤` has an entry reading `x` strictly below `r`. -/
theorem exists_top_reads_lt_markedTop {q : Fin (markedTop I D).card → Label.{u}}
    (hq : (markedTop I D).rows.IsLawful q) {j : Fin (((scheme I).catalogue 4).card + D.marks.card)}
    {x r : Fin (scheme I).card} (hgr : (scheme I).toCellScheme.grade r = 4)
    (hgx : (scheme I).toCellScheme.grade x ≤ 4) (hqj : q (Fin.natAdd _ j) = ⊤)
    (hqr : q (Fin.castAdd _ r) = ⊤)
    (hread : (scheme I).markedEntry 4 D.marks j r ≤ (scheme I).markedEntry 4 D.marks j x)
    (hτ : ⊥ < (scheme I).markedEntry 4 D.marks j r) {p : Fin (scheme I).card → Label.{u}}
    (hp : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ p d)
    (hag : ∀ d ∈ (scheme I).toCellScheme.below (univ, 4),
      min (p d) ((scheme I).markedEntry 4 D.marks j r) =
        min ((scheme I).markedEntry 4 D.marks j d) ((scheme I).markedEntry 4 D.marks j r))
    (hlt : p x < p r) :
    ∃ j'', q (Fin.natAdd _ j'') = ⊤ ∧
      (scheme I).markedEntry 4 D.marks j'' x < (scheme I).markedEntry 4 D.marks j'' r := by
  have hε := markedEntry_mem_spec D
  have hvis : IsSelfVisible 4 ((scheme I).markedEntry 4 D.marks j r) := by
    have h := (Scheme.mem_catalogue.mp (hε j)).1.orderly r
    rwa [hgr] at h
  have hs : IsShort 4 ((scheme I).markedEntry 4 D.marks j r) :=
    isShort_of_mem_codeGrid (Scheme.mem_codeGrid_of_mem_catalogue (hε j) r)
  obtain ⟨j₀, hj₀, hσ⟩ := Scheme.exists_template_markedLayer D.marks_subset D.closed hvis hs hτ j
    hp hag
  exact Scheme.exists_top_sheetRow_lt (hS := not_univ_four_le) hε D.cap_mem D.capRespects hq hgr
    hgx hqj hqr hread hτ (fun d hd ↦ hag d ⟨subset_univ _, hd⟩) hlt hj₀ hσ

/-- **The separating fill from a raise in a coatom.**  As `exists_top_reads_lt_markedTop`, with the
fill replaced by a labelling `w` of the profile layer lawful below the coatom `(univ.erase z₁, 4)`
and below `(univ, 3)`, agreeing with the entry of `j` capped at its value at `r` there, with
`w x < w r`, for `x` of grade at most `3` and `r` below the coatom: the fill is the extension of
`w` below `(univ, 4)` (`TowerProfile.exists_isLawfulBelow_four`), which keeps `w` at `x` (below
`(univ, 3)`) and at `r` (below the coatom).  The premise on `w` is capped agreement with the entry
(at its value at `r`), so the separating fill is a raise of `r` within the coatom relative to that
capped agreement. -/
theorem exists_top_reads_lt_markedTop_of_raise {q : Fin (markedTop I D).card → Label.{u}}
    (hq : (markedTop I D).rows.IsLawful q) {j : Fin (((scheme I).catalogue 4).card + D.marks.card)}
    {x r : Fin (scheme I).card} (hgr : (scheme I).toCellScheme.grade r = 4)
    (hgx : (scheme I).toCellScheme.grade x ≤ 3) (hqj : q (Fin.natAdd _ j) = ⊤)
    (hqr : q (Fin.castAdd _ r) = ⊤)
    (hread : (scheme I).markedEntry 4 D.marks j r ≤ (scheme I).markedEntry 4 D.marks j x)
    (hτ : ⊥ < (scheme I).markedEntry 4 D.marks j r) {z₁ z₂ : Fin 5}
    (hz₁ : z₁ ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hz₂ : z₂ ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hz : z₁ ≠ z₂)
    (hrC : r ∈ (scheme I).toCellScheme.below (univ.erase z₁, 4))
    {w : Fin (scheme I).card → Label.{u}}
    (hwU : (scheme I).rows.IsLawfulBelow (univ.erase z₁, 4) fun d ↦ w d)
    (hwV : (scheme I).rows.IsLawfulBelow (univ, 3) fun d ↦ w d)
    (hag : ∀ d, d ∈ (scheme I).toCellScheme.below (univ.erase z₁, 4) ∨
      d ∈ (scheme I).toCellScheme.below (univ, 3) →
      min (w d) ((scheme I).markedEntry 4 D.marks j r) =
        min ((scheme I).markedEntry 4 D.marks j d) ((scheme I).markedEntry 4 D.marks j r))
    (hlt : w x < w r) :
    ∃ j'', q (Fin.natAdd _ j'') = ⊤ ∧
      (scheme I).markedEntry 4 D.marks j'' x < (scheme I).markedEntry 4 D.marks j'' r := by
  have hε := markedEntry_mem_spec D
  have hvis : IsSelfVisible 4 ((scheme I).markedEntry 4 D.marks j r) := by
    have h := (Scheme.mem_catalogue.mp (hε j)).1.orderly r
    rwa [hgr] at h
  obtain ⟨p, hp, hpw, hpa⟩ := exists_isLawfulBelow_four hz₁ hz₂ hz hwU hwV
    (Scheme.mem_catalogue.mp (hε j)).1 hvis hag
  have hx3 : x ∈ (scheme I).toCellScheme.below (univ, 3) := ⟨subset_univ _, hgx⟩
  refine exists_top_reads_lt_markedTop D hq hgr (hgx.trans (by omega)) hqj hqr hread hτ hp hpa ?_
  rw [hpw x (.inr hx3), hpw r (.inl hrC)]
  exact hlt

end TowerProfile

end VaughtConjecture
