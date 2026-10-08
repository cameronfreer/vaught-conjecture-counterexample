/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerBandFill

/-!
# Legality of the restricted reading layer from conditions on the coatom types

Roadmap, Layer 3 ((R3) of the table of 3.4).

The legality of the restricted reading layer (`TowerProfile.readingTop`) at a seed on five points,
from conditions on its two coatom types.

* **Lawfulness below the left coatom, read on the left coatom type**
  (`TowerProfile.isLawful_left_of_isLawfulBelow`, compiled in this repository (theorem named)).
* **The conditions** (`TowerProfile.LeftTie`, `TowerProfile.RightNewTop`, defined here): on the left
  coatom type, an apex marker reading the cells labelled `⊥` as `⊥`, the face off the point `3`
  labelled `⊥`, the root offsets below the grade `4` of the apex (the acquisition condition), and
  two cells `z₁`, `z₂` of grades `1`, `2` with one proper label, every lawful labelling taking one
  value at the cells of grade `1` not labelled `⊥` and one at those of grade `2`, and the cells of
  grade `3` labelled `⊥`; on the right coatom type, rows raising at the point `3`
  (`StageType.RowsRaiseAt`) and a new top `x₀` of grade `1` through `3` labelled `⊤`.
* **Legality** (`TowerProfile.readingFillPos_left_of_coatoms`,
  `TowerProfile.isLegalBelowFullGrade_readingTop_of_coatoms`, compiled): under these conditions
  the four fill conditions hold, so the reading layer of the marker and the new top is legal below
  the full grade.
* **At `seedThree`** (`TopReadingApexExample.leftTie_threeType`,
  `TopReadingApexExample.rightNewTop_rightType`,
  `TopReadingApexExample.readingFillPos_left_seedThree`,
  `TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedThree`, compiled): `threeType` has a
  tie-keeping marker (its apex, with `z₁`, `z₂` the cells at `(univ, 1)` and `(univ, 2)`, both
  labelled `3`; its only ordinal label is `3`, below the grade `4` of the apex; the cells of grade
  `1` labelled `3` share one value by locality and availability at `z₁`,
  `TopReadingApexExample.tie_one_threeType`), and `rightType` has a new top (its cell `{3}`;
  `TowerProfile.rowsRaiseAt_rightType`).

* **Acquired contexts** (`TowerProfile.isLegalBelowFullGrade_readingTop_of_acquired`,
  `TowerProfile.isLegalBelowFullGrade_readingTop_of_acquired_offRoot`,
  `TowerProfile.arity_le_two_of_isMarkedCapContextAt`, `TowerProfile.arity_eq_two_of_acquired`,
  compiled): when the left coatom type is an acquired marked-cap context along a root `h`
  (`TiedRootCapRelabel.MarkedCapContextBelow'` unpacked), the top cap gives the label `⊤` and the
  full scope of the apex, and the acquisition gives the root offsets and the root bottoms.  The
  residual hypotheses are the top grade `4` of the cap, its uniqueness at `(univ, 4)`, the cells
  off the root labelled `⊥` read as `⊥`, the common face labelled `⊥`, the tied cells with the
  structure of this family, the right coatom condition, and either the tied cells on the root
  (then the root has two points) or the offsets below the grade of the cap at every label.
* **An acquired instance** (`TopReadingApexExample.markedCapContextBelow'_threeType`,
  `TopReadingApexExample.isLegalBelowFullGrade_readingTop_seedThree_of_acquired`, compiled):
  `threeType` is an acquired context along the root `{2, 3}`; the tied cell of grade `2` of this
  family has full scope and is never a root cell
  (`TopReadingApexExample.fifteen_notMem_visibleCells`), so the off-root form gives legality at
  `seedThree`.  `seedThree` is not an acquired context along the identity
  (`TopReadingApexExample.not_isMarkedCapContextAt_threeType`).

The conditions are explicit predicates on the coatom types; the marker condition is the
acquisition condition (root offsets below the grade of the cap), from which the tie of the marker
follows (`StageType.keepsProperRootTies_of_rootOffsetsBelow`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- The cells of the left coatom type lie below the left coatom. -/
theorem leftCell_mem (z : Fin I.left.card) :
    leftCell I z ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4) := by
  rw [CellScheme.mem_below, gradedIndex_leftCell, ← univ_map_left_eq]
  exact Prod.mk_le_mk.mpr ⟨map_subset_map.mpr (subset_univ _), I.left.grade_le z⟩

/-- The grade of the cell of a cell of the left coatom type. -/
theorem grade_leftCell (z : Fin I.left.card) :
    (scheme I).toCellScheme.grade (leftCell I z) = I.left.toCellScheme.grade z := by
  rw [← CellScheme.gradedIndex_snd, gradedIndex_leftCell]

/-- **A labelling lawful below the left coatom, read on the left coatom type, is lawful**: it
extends to a labelling lawful below `(univ, 4)` (the fill at `⊥`, `TowerProfile.exists_fill_four`),
which restricts to the amalgam and to its left face (`StageType.isLawful_comp_faceCell`). -/
theorem isLawful_left_of_isLawfulBelow {f : Fin (scheme I).card → Label.{u}}
    (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d) :
    I.left.rows.IsLawful fun z ↦ f (leftCell I z) := by
  obtain ⟨g, hg, hgf, -⟩ := exists_fill_four (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3))
    (by simp) (by simp) (by decide) hf (a := fun _ ↦ ⊥) CellScheme.Rows.isLawful_const_bot
    (isSelfVisible_bot 4) fun _ _ ↦ by simp
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hg
  have hgl : (scheme I).rows.IsLawful g :=
    ⟨fun d ↦ ho d (mem_below_univ_four d), fun s ↦ hl s (mem_below_univ_four s),
      fun s t hst hgr ↦ ha s t (mem_below_univ_four t) hst hgr⟩
  have hamal : I.amalgam.rows.IsLawful (g ∘ embed3 I) := by
    have := hgl.comap (isLowerEmbedding_embed3 (I := I))
    rwa [comap_rows_embed3] at this
  have hleft := StageType.isLawful_comp_faceCell I.restrictFace_left hamal
  convert hleft using 1
  funext z
  exact (hgf _ (leftCell_mem z)).symm

/-- **A left coatom type with a tie-keeping marker** along a root `ι` (for the restricted reading
layer): an apex `a` (the only cell at `(univ, 4)`, labelled `⊤`), whose row reads the root cells
labelled `⊥` as `⊥` (`StageType.RootBottomRespected`) and the other cells labelled `⊥` as `⊥`; the
face off the point `3` labelled `⊥`; **the root offsets below the grade `4` of the apex** (the
acquisition condition, `StageType.RootOffsetsBelow`); and two root cells `z₁`, `z₂` of grades `1`,
`2` with one proper label such that every lawful labelling takes one value at the cells of grade
`1` not labelled `⊥` (that at `z₁`) and one value at the cells of grade `2` not labelled `⊥`
(that at `z₂`), and the cells of grade `3` are labelled `⊥`. -/
structure LeftTie {n : ℕ} (t' : StageType.{u} α 4) (ι : Fin n ↪ Fin 4)
    (a z₁ z₂ : Fin t'.card) : Prop where
  gradedIndex_apex : t'.toCellScheme.gradedIndex a = (univ, 4)
  eq_apex : ∀ z, t'.toCellScheme.gradedIndex z = (univ, 4) → z = a
  label_apex : t'.label a = ⊤
  rootBottom : t'.RootBottomRespected ι a
  rowAt_apex_off : ∀ z ∉ t'.visibleCells ι, t'.label z = ⊥ → t'.toScheme.rowAt a z = ⊥
  face_bot : ∀ z, Fin.last 3 ∉ t'.toCellScheme.scope z → t'.label z = ⊥
  grade_one : t'.toCellScheme.grade z₁ = 1
  grade_two : t'.toCellScheme.grade z₂ = 2
  row_tie : t'.toScheme.rowAt a z₂ ≤ t'.toScheme.rowAt a z₁
  tie_one : ∀ p : Fin t'.card → Label.{u}, t'.rows.IsLawful p → ∀ z,
    t'.toCellScheme.grade z = 1 → t'.label z ≠ ⊥ → p z = p z₁
  tie_two : ∀ p : Fin t'.card → Label.{u}, t'.rows.IsLawful p → ∀ z,
    t'.toCellScheme.grade z = 2 → t'.label z ≠ ⊥ → p z = p z₂
  label_three : ∀ z, t'.toCellScheme.grade z = 3 → t'.label z = ⊥

/-- The apex of a left coatom type with a tie-keeping marker reads every cell labelled `⊥` as
`⊥`: the root cells by `StageType.RootBottomRespected`, the others by hypothesis. -/
theorem LeftTie.rowAt_apex {n : ℕ} {t' : StageType.{u} α 4} {ι : Fin n ↪ Fin 4}
    {a z₁ z₂ : Fin t'.card} (hL : LeftTie t' ι a z₁ z₂) (z : Fin t'.card) (hz : t'.label z = ⊥) :
    t'.toScheme.rowAt a z = ⊥ := by
  by_cases hv : z ∈ t'.visibleCells ι
  · exact hL.rootBottom z hv hz
  · exact hL.rowAt_apex_off z hv hz

/-- **The tie of the marker from the root offsets**: a cell `a` labelled `⊤`, of full scope and
grade at least the arity of a root `ι`, with the root offsets below its grade, reads two root cells
with one proper label alike (`StageType.keepsProperRootTies_of_rootOffsetsBelow`). -/
theorem rowTie_of_rootOffsetsBelow {n : ℕ} {t' : StageType.{u} α 4} {ι : Fin n ↪ Fin 4}
    {a z₁ z₂ : Fin t'.card} (hc : t'.label a = ⊤) (hcs : t'.toCellScheme.scope a = univ)
    (hn : n ≤ t'.toCellScheme.grade a) (hoff : t'.RootOffsetsBelow ι (t'.toCellScheme.grade a))
    (hv₁ : z₁ ∈ t'.visibleCells ι) (hv₂ : z₂ ∈ t'.visibleCells ι)
    (hlab : t'.label z₂ = t'.label z₁) (hprop : IsProper (t'.label z₂)) :
    t'.toScheme.rowAt a z₂ ≤ t'.toScheme.rowAt a z₁ :=
  StageType.keepsProperRootTies_of_rootOffsetsBelow hc hcs hn hoff z₂ hv₂ z₁ hv₁ hlab.le
    (.inr hprop)

/-- **A right coatom type with a new top** at `x₀`: its rows raise at the point `3`
(`StageType.RowsRaiseAt`), and `x₀` is a cell of grade `1` through `3` labelled `⊤`. -/
structure RightNewTop (tb : StageType.{u} α 4) (x₀ : Fin tb.card) : Prop where
  rowsRaiseAt : tb.RowsRaiseAt 3
  mem_scope : (3 : Fin 4) ∈ tb.toCellScheme.scope x₀
  grade_eq : tb.toCellScheme.grade x₀ = 1
  label_eq : tb.label x₀ = ⊤

/-- The new top of the reading layer: the cell `x₀` of the right coatom type in the profile
layer. -/
noncomputable abbrev newTops (I : Seed.{u} α 3) (x₀ : Fin I.right.card) :
    Finset (Fin (scheme I).card) :=
  ({x₀} : Finset (Fin I.right.card)).image fun z ↦
    embed3 I (StageType.faceCell I.restrictFace_right z)

/-- **The fill at the short positive caps from the left coatom, from the coatom types**
(`TowerProfile.readingFillPos_left_of_tie`, with the conditions on the cells of the profile layer
read on the left coatom type through `TowerProfile.isLawful_left_of_isLawfulBelow`). -/
theorem readingFillPos_left_of_coatoms {a z₁ z₂ : Fin I.left.card} {n : ℕ} {ι : Fin n ↪ Fin 4}
    (hL : LeftTie I.left ι a z₁ z₂)
    {x₀ : Fin I.right.card} (hR : RightNewTop I.right x₀) :
    ReadingFillPos I (leftCell I a) (newTops I x₀) (Fin.last 4) := by
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
  have hPx : Fin.last 4 ∈ I.amalgam.toCellScheme.scope
      (StageType.faceCell I.restrictFace_right x₀) :=
    (last_mem_scope_right I.restrictFace_right x₀).mpr hR.mem_scope
  refine readingFillPos_left_of_rowTie hR.rowsRaiseAt hgr hrC hPx
    ((StageType.grade_faceCell _ _).trans hR.grade_eq)
    (mem_image_of_mem _ (mem_singleton_self _))
    (fun x hx ↦ by obtain ⟨z, hz, rfl⟩ := mem_image.mp hx; rw [mem_singleton.mp hz])
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

/-- **The restricted reading layer is legal below the full grade at every seed on five points
whose left coatom type has a tie-keeping marker and whose right coatom type has a new top**: the
four fill conditions (`TowerProfile.readingFillBot_left_of_left`,
`TowerProfile.readingFillBot_right_of_unique`, `TowerProfile.readingFillPos_right_of_unique`,
`TowerProfile.readingFillPos_left_of_coatoms`), and
`TowerProfile.isLegalBelowFullGrade_readingTop_iff`. -/
theorem isLegalBelowFullGrade_readingTop_of_coatoms {a z₁ z₂ : Fin I.left.card}
    {n : ℕ} {ι : Fin n ↪ Fin 4} (hL : LeftTie I.left ι a z₁ z₂) {x₀ : Fin I.right.card}
    (hR : RightNewTop I.right x₀) :
    (readingTop I (leftCell I a) (newTops I x₀)).IsLegalBelowFullGrade := by
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := I) hL.gradedIndex_apex hL.eq_apex
  have hX3 : ∀ x ∈ newTops I x₀, (scheme I).toCellScheme.grade x ≤ 3 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [mem_singleton.mp hz, ← CellScheme.gradedIndex_snd, gradedIndex_embed3,
      CellScheme.gradedIndex_snd, StageType.grade_faceCell, hR.grade_eq]
    omega
  refine (isLegalBelowFullGrade_readingTop_iff hgr fun x hx ↦ (hX3 x hx).trans (by omega)).mpr
    ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillBot_left_of_left hL.gradedIndex_apex hL.rowAt_apex hL.face_bot _
        fun z hz ↦ by rw [mem_singleton.mp hz]; exact hR.label_eq
    · rw [mem_singleton.mp hz]
      exact readingFillBot_right_of_unique hgr hrC huniq
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillPos_left_of_coatoms hL hR
    · rw [mem_singleton.mp hz]
      exact readingFillPos_right_of_unique hgr hrC huniq hX3

/-! ### Acquired contexts -/

/-- **The root of an acquired context on four points has at most two points**: the top cap of a
marked-cap context has grade above `n + 1` and at most `4`. -/
theorem arity_le_two_of_isMarkedCapContextAt {n : ℕ} {t' : StageType.{u} α 4} {h : Fin n ↪ Fin 4}
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt h c r) : n ≤ 2 := by
  have h1 := hctx.2.2.1
  have h2 := t'.grade_le c
  omega

/-- A cell visible through a root of `n` points has grade at most `n`. -/
theorem grade_le_of_mem_visibleCells {n k : ℕ} {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    {z : Fin t'.card} (hz : z ∈ t'.visibleCells h) : t'.toCellScheme.grade z ≤ n := by
  have hsub : t'.toCellScheme.scope z ⊆ univ.map h := (mem_filter.mp hz).2
  calc t'.toCellScheme.grade z ≤ #(t'.toCellScheme.scope z) :=
        t'.isWellFormed.isWellFormed.grade_le_card z
    _ ≤ #(univ.map h) := card_le_card hsub
    _ = n := by simp

/-- **Legality of the restricted reading layer at an acquired context.**  Let the left coatom type
of a seed on five points be an acquired marked-cap context along a root `h`
(`TiedRootCapRelabel.MarkedCapContextBelow'`, unpacked: top cap `c`, marker `r`, root offsets below
the grade of `c`, root bottoms respected).  These give: `c` labelled `⊤` and of full scope
(`StageType.IsTopCap`), the root offsets and the root bottoms of `TowerProfile.LeftTie`.  The
residual hypotheses are:

* `hN`: the cap has the top grade `4` (so the root has two points, `n + 1 < 4` with a root cell of
  grade `2`) — a shape restriction of seeds on five points;
* `huniq`: the cap is the only cell at `(univ, 4)` — a shape restriction;
* `hbotoff`: the cap reads the cells off the root labelled `⊥` as `⊥` — of the kind of
  `StageType.RootBottomRespected` (an acquisition property, not given by `Realization.IsModel`),
  off the root;
* `hface`: the cells off the point `3` (the common face with the right coatom) are labelled `⊥` —
  a shape restriction;
* `z₁`, `z₂`: root cells of grades `1`, `2`, `z₂` labelled `⊥` (then the cap reads it as `⊥`, by
  the root bottoms) or with the proper label of `z₁` (then the cap reads them alike, by the root
  offsets), with `htie`, `htwo`, `hthree`
  (one value at the cells of grade `1` not labelled `⊥`, one value at those of grade `2`, the
  cells of grade `3` labelled `⊥`) — the shape of this family;
* `hR`: the right coatom type raises at the point `3` and has a new top `x₀`
  (`TowerProfile.RightNewTop`) — a shape restriction on the donor side. -/
theorem isLegalBelowFullGrade_readingTop_of_acquired {n : ℕ} {h : Fin n ↪ Fin 4}
    {c r : Fin I.left.card} (hctx : I.left.IsMarkedCapContextAt h c r)
    (hoff : I.left.RootOffsetsBelow h (I.left.toCellScheme.grade c))
    (hbot : I.left.RootBottomRespected h c)
    (hN : I.left.toCellScheme.grade c = 4)
    (huniq : ∀ z, I.left.toCellScheme.gradedIndex z = (univ, 4) → z = c)
    (hbotoff : ∀ z ∉ I.left.visibleCells h, I.left.label z = ⊥ → I.left.toScheme.rowAt c z = ⊥)
    (hface : ∀ z, Fin.last 3 ∉ I.left.toCellScheme.scope z → I.left.label z = ⊥)
    {z₁ z₂ : Fin I.left.card} (hz₁ : z₁ ∈ I.left.visibleCells h) (hz₂ : z₂ ∈ I.left.visibleCells h)
    (hg₁ : I.left.toCellScheme.grade z₁ = 1) (hg₂ : I.left.toCellScheme.grade z₂ = 2)
    (hlab : I.left.label z₂ = ⊥ ∨
      (I.left.label z₂ = I.left.label z₁ ∧ IsProper (I.left.label z₂)))
    (htie : ∀ p : Fin I.left.card → Label.{u}, I.left.rows.IsLawful p → ∀ z,
      I.left.toCellScheme.grade z = 1 → I.left.label z ≠ ⊥ → p z = p z₁)
    (htwo : ∀ p : Fin I.left.card → Label.{u}, I.left.rows.IsLawful p → ∀ z,
      I.left.toCellScheme.grade z = 2 → I.left.label z ≠ ⊥ → p z = p z₂)
    (hthree : ∀ z, I.left.toCellScheme.grade z = 3 → I.left.label z = ⊥)
    {x₀ : Fin I.right.card} (hR : RightNewTop I.right x₀) :
    (readingTop I (leftCell I c) (newTops I x₀)).IsLegalBelowFullGrade := by
  obtain ⟨⟨hcs, hct, -⟩, -, -, -⟩ := hctx
  refine isLegalBelowFullGrade_readingTop_of_coatoms (ι := h) (z₁ := z₁) (z₂ := z₂) ?_ hR
  exact
    { gradedIndex_apex := Prod.ext hcs hN
      eq_apex := huniq
      label_apex := hct
      rootBottom := hbot
      rowAt_apex_off := hbotoff
      face_bot := hface
      grade_one := hg₁
      grade_two := hg₂
      row_tie := hlab.elim (fun h0 ↦ (le_of_eq (hbot z₂ hz₂ h0)).trans bot_le)
        fun ⟨hl, hp⟩ ↦ rowTie_of_rootOffsetsBelow hct hcs
          (by have := Fintype.card_le_of_embedding h; simp at this; omega) hoff hz₁ hz₂ hl hp
      tie_one := htie
      tie_two := htwo
      label_three := hthree }

/-- **Legality of the restricted reading layer at an acquired context, with the tied cells off the
root.**  As `TowerProfile.isLegalBelowFullGrade_readingTop_of_acquired`, with the tied cells `z₁`,
`z₂` not required to be root cells, and the root offsets strengthened to all the labels of the left
coatom type (`hoffAll`, the root offsets along the identity, which contain those along `h`): the
acquisition condition off the root. -/
theorem isLegalBelowFullGrade_readingTop_of_acquired_offRoot {n : ℕ} {h : Fin n ↪ Fin 4}
    {c r : Fin I.left.card} (hctx : I.left.IsMarkedCapContextAt h c r)
    (hbot : I.left.RootBottomRespected h c)
    (hN : I.left.toCellScheme.grade c = 4)
    (huniq : ∀ z, I.left.toCellScheme.gradedIndex z = (univ, 4) → z = c)
    (hbotoff : ∀ z ∉ I.left.visibleCells h, I.left.label z = ⊥ → I.left.toScheme.rowAt c z = ⊥)
    (hface : ∀ z, Fin.last 3 ∉ I.left.toCellScheme.scope z → I.left.label z = ⊥)
    (hoffAll : I.left.RootOffsetsBelow (Function.Embedding.refl (Fin 4))
      (I.left.toCellScheme.grade c))
    {z₁ z₂ : Fin I.left.card}
    (hg₁ : I.left.toCellScheme.grade z₁ = 1) (hg₂ : I.left.toCellScheme.grade z₂ = 2)
    (hlab : I.left.label z₂ = I.left.label z₁) (hprop : IsProper (I.left.label z₂))
    (htie : ∀ p : Fin I.left.card → Label.{u}, I.left.rows.IsLawful p → ∀ z,
      I.left.toCellScheme.grade z = 1 → I.left.label z ≠ ⊥ → p z = p z₁)
    (htwo : ∀ p : Fin I.left.card → Label.{u}, I.left.rows.IsLawful p → ∀ z,
      I.left.toCellScheme.grade z = 2 → I.left.label z ≠ ⊥ → p z = p z₂)
    (hthree : ∀ z, I.left.toCellScheme.grade z = 3 → I.left.label z = ⊥)
    {x₀ : Fin I.right.card} (hR : RightNewTop I.right x₀) :
    (readingTop I (leftCell I c) (newTops I x₀)).IsLegalBelowFullGrade := by
  obtain ⟨⟨hcs, hct, -⟩, -, -, -⟩ := hctx
  refine isLegalBelowFullGrade_readingTop_of_coatoms (ι := h) (z₁ := z₁) (z₂ := z₂) ?_ hR
  exact
    { gradedIndex_apex := Prod.ext hcs hN
      eq_apex := huniq
      label_apex := hct
      rootBottom := hbot
      rowAt_apex_off := hbotoff
      face_bot := hface
      grade_one := hg₁
      grade_two := hg₂
      row_tie := rowTie_of_rootOffsetsBelow hct hcs (by rw [hN]) hoffAll
        (TopReadingApexExample.mem_visibleCells_refl _ _)
        (TopReadingApexExample.mem_visibleCells_refl _ _) hlab hprop
      tie_one := htie
      tie_two := htwo
      label_three := hthree }

/-- **The root of an acquired context carrying the two tied cells has exactly two points**
(`arity_le_two_of_isMarkedCapContextAt`, and a root cell of grade `2`). -/
theorem arity_eq_two_of_acquired {n : ℕ} {h : Fin n ↪ Fin 4} {c r : Fin I.left.card}
    (hctx : I.left.IsMarkedCapContextAt h c r) {z₂ : Fin I.left.card}
    (hz₂ : z₂ ∈ I.left.visibleCells h) (hg₂ : I.left.toCellScheme.grade z₂ = 2) : n = 2 := by
  have h1 := arity_le_two_of_isMarkedCapContextAt hctx
  have h2 := grade_le_of_mem_visibleCells hz₂
  omega

end TowerProfile

/-! ### The instance `seedThree` -/

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The cells of `threeType`: the apex and the cells of `S`. -/
theorem cases_threeType (z : Fin (threeType hα).card) :
    z = Fin.last _ ∨ ∃ a : Fin CaseSplitCounterexample.S.{u}.card, z = Fin.castSucc a := by
  change Fin ((threeBase hα).card + 1) at z
  induction z using Fin.lastCases with
  | last => exact .inl rfl
  | cast a => exact .inr ⟨a, rfl⟩

/-- The graded index of a cell of `S` in `threeType`. -/
theorem gradedIndex_threeType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (threeType hα).toCellScheme.gradedIndex (Fin.castSucc a) =
      (TwoFaceLiftCounterexample.cellScope a, TwoFaceLiftCounterexample.cellGrade a) :=
  Scheme.appendFullCellScheme_gradedIndex_castSucc CaseSplitCounterexample.S 4 a

/-- The graded index of the apex of `threeType`. -/
theorem gradedIndex_threeType_last :
    (threeType hα).toCellScheme.gradedIndex (Fin.last _) = (univ, 4) :=
  StageType.addApex_gradedIndex_last (t := threeBase hα) isLegalBelowFullGrade_S (by omega)

/-- The labels of `threeType` at the cells of `S`. -/
theorem label_threeType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (threeType hα).label (Fin.castSucc a) = CaseSplitCounterexample.labelling lab3 lab3 ⊥ a :=
  StageType.addApex_label_castSucc (t := threeBase hα) isLegalBelowFullGrade_S (by omega) a

/-- The label of the apex of `threeType`. -/
theorem label_threeType_last : (threeType hα).label (Fin.last _) = ⊤ :=
  StageType.addApex_label_last (t := threeBase hα) isLegalBelowFullGrade_S (by omega)

/-- The grade of a cell of `S` in `threeType`. -/
theorem grade_threeType_castSucc (a : Fin CaseSplitCounterexample.S.{u}.card) :
    (threeType hα).toCellScheme.grade (Fin.castSucc a) = TwoFaceLiftCounterexample.cellGrade a :=
  congrArg Prod.snd (gradedIndex_threeType_castSucc hα a)

/-- The apex of `threeType` has grade `4`. -/
theorem grade_threeType_last : (threeType hα).toCellScheme.grade (Fin.last _) = 4 :=
  congrArg Prod.snd (gradedIndex_threeType_last hα)

/-- **The cells of grade `1` of `threeType` labelled `3` share one value in every lawful
labelling**, that at the cell `9` (at `(univ, 1)`): locality there (it reads them as itself) and
availability (it is the only cell at its graded index). -/
theorem tie_one_threeType {p : Fin (threeType hα).card → Label.{u}}
    (hp : (threeType hα).rows.IsLawful p) (z : Fin (threeType hα).card)
    (hz : (threeType hα).toCellScheme.grade z = 1) (hl : (threeType hα).label z ≠ ⊥) :
    p z = p (Fin.castSucc (⟨9, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) := by
  set n9 : Fin CaseSplitCounterexample.S.{u}.card := ⟨9, by decide⟩ with hn9
  rcases cases_threeType hα z with hzl | ⟨a, hza⟩
  · exact absurd ((grade_threeType_last hα).symm.trans (hzl ▸ hz)) (by decide)
  subst hza
  have ha : TwoFaceLiftCounterexample.cellGrade a = 1 :=
    (grade_threeType_castSucc hα a).symm.trans hz
  have hla : CaseSplitCounterexample.live a = true :=
    live_of_labelling_three_ne_bot ((label_threeType_castSucc hα a).symm.trans_ne hl)
  have h9 : TwoFaceLiftCounterexample.cellGrade n9 = 1 := rfl
  have hl9 : CaseSplitCounterexample.live n9 = true := rfl
  have hs9 : TwoFaceLiftCounterexample.cellScope n9 = univ := rfl
  have hmem : Fin.castSucc a ∈ (threeType hα).toCellScheme.below
      ((threeType hα).toCellScheme.gradedIndex (Fin.castSucc n9)) :=
    (gradedIndex_threeType_castSucc hα a).trans_le
      (le_of_le_of_eq (Prod.mk_le_mk.mpr ⟨hs9 ▸ subset_univ _, ha.trans h9.symm |>.le⟩)
        (gradedIndex_threeType_castSucc hα n9).symm)
  have hrow : (threeType hα).toScheme.rowAt (Fin.castSucc n9) (Fin.castSucc n9) =
      (threeType hα).toScheme.rowAt (Fin.castSucc n9) (Fin.castSucc a) := by
    refine ((rowAt_threeType_castSucc hα n9 n9).trans (rowAt_S_live h9 hl9 h9 subset_rfl)).trans
      (Eq.trans ?_ ((rowAt_threeType_castSucc hα n9 a).trans
        (rowAt_S_live h9 hl9 ha (hs9 ▸ subset_univ _))).symm)
    rw [hl9, hla]
  have h1 := (hp.locality (Fin.castSucc n9)).le_of_le
    (d := ⟨Fin.castSucc n9, (threeType hα).toCellScheme.mem_below_gradedIndex _⟩)
    (d' := ⟨Fin.castSucc a, hmem⟩)
    ((Scheme.rowAt_of_mem _).symm.trans_le (hrow.le.trans_eq (Scheme.rowAt_of_mem hmem)))
    ((grade_threeType_castSucc hα a).trans_le
      ((ha.trans h9.symm).le.trans_eq (grade_threeType_castSucc hα n9).symm))
  change min (p (Fin.castSucc n9)) (p (Fin.castSucc n9)) ≤
    min (p (Fin.castSucc a)) (p (Fin.castSucc n9)) at h1
  rw [min_self] at h1
  obtain ⟨v, hv, hle⟩ := hp.availability (Fin.castSucc a) (Fin.castSucc n9)
    ((threeType hα).toCellScheme.gradedIndex_le_iff.mp ((CellScheme.mem_below _).mp hmem)).1
    ((grade_threeType_castSucc hα a).trans
      ((ha.trans h9.symm).trans (grade_threeType_castSucc hα n9).symm))
  rcases cases_threeType hα v with hvl | ⟨b, hvb⟩
  · exact absurd (congrArg Prod.snd ((gradedIndex_threeType_last hα).symm.trans
      ((hvl ▸ hv).trans (gradedIndex_threeType_castSucc hα n9)))) (by decide)
  subst hvb
  have hb : b = n9 := TwoFaceLiftCounterexample.gradedIndex_injective
    ((gradedIndex_threeType_castSucc hα b).symm.trans
      (hv.trans (gradedIndex_threeType_castSucc hα n9)))
  subst hb
  exact le_antisymm hle (h1.trans (min_le_left _ _))

/-- **The root offsets of `threeType` lie below `4`** along every root: its only ordinal label is
`3`. -/
theorem rootOffsetsBelow_threeType {n : ℕ} (ι : Fin n ↪ Fin 4) :
    (threeType hα).RootOffsetsBelow ι 4 := by
  intro y _ μ f hμ hy
  rcases cases_threeType hα y with rfl | ⟨a, rfl⟩
  · exact absurd ((label_threeType_last hα).symm.trans hy)
      (fun h' ↦ WithTop.coe_ne_top (WithBot.coe_injective h'.symm))
  · have hy' := (label_threeType_castSucc hα a).symm.trans hy
    rcases labelling_three_cases a with h3 | h0
    · have e := h3.symm.trans hy'
      rw [lab3, natCast_label] at e
      have h' : ((0 : Ordinal.{u}) + (3 : ℕ)) = μ + f := by
        rw [zero_add]; exact WithTop.coe_injective (WithBot.coe_injective e)
      have := ((add_natCast_eq_add_natCast_iff Ordinal.isSuccPrelimit_zero hμ).mp h').2
      omega
    · exact absurd (h0.symm.trans hy').symm WithBot.coe_ne_bot

/-- The cells `9` and `15` of `threeType` are both labelled `3`. -/
theorem label_fifteen_eq_nine :
    (threeType hα).label (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) =
      (threeType hα).label
        (Fin.castSucc (⟨9, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) := by
  refine (label_threeType_castSucc hα _).trans (Eq.trans ?_ (label_threeType_castSucc hα _).symm)
  change CaseSplitCounterexample.labelling lab3 lab3 ⊥ (15 : Fin 19) =
    CaseSplitCounterexample.labelling lab3 lab3 ⊥ (9 : Fin 19)
  simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
    TwoFaceLiftCounterexample.cellGrade]

/-- The label of the cell `15` of `threeType` is proper (it is `3`). -/
theorem isProper_label_fifteen :
    IsProper ((threeType hα).label
      (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))) := by
  have e := (label_threeType_castSucc hα
    (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)).trans
    (show CaseSplitCounterexample.labelling lab3 lab3 ⊥ (15 : Fin 19) = (lab3 : Label.{u}) by
      simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
        TwoFaceLiftCounterexample.cellGrade])
  exact ⟨((3 : ℕ) : Ordinal.{u}), (natCast_label 3).symm.trans e.symm⟩

/-- **The apex of `threeType` reads the cells `9` and `15` alike** (the root offsets below `4`
along the identity root, `TowerProfile.rowTie_of_rootOffsetsBelow`). -/
theorem rowTie_threeType :
    (threeType hα).toScheme.rowAt (Fin.last _)
        (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ≤
      (threeType hα).toScheme.rowAt (Fin.last _)
        (Fin.castSucc (⟨9, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) :=
  rowTie_of_rootOffsetsBelow (ι := Function.Embedding.refl (Fin 4)) (label_threeType_last hα)
    (congrArg Prod.fst (gradedIndex_threeType_last hα))
    (le_of_eq (grade_threeType_last hα).symm)
    ((grade_threeType_last hα).symm ▸ rootOffsetsBelow_threeType hα _)
    (mem_visibleCells_refl _ _) (mem_visibleCells_refl _ _) (label_fifteen_eq_nine hα)
    (isProper_label_fifteen hα)

/-- **`threeType` is a left coatom type with a tie-keeping marker** along every root: the apex,
and the cells `9` and `15` (at `(univ, 1)` and `(univ, 2)`, both labelled `3`). -/
theorem leftTie_threeType {n : ℕ} (ι : Fin n ↪ Fin 4) :
    LeftTie (threeType hα) ι (Fin.last _)
      (Fin.castSucc (⟨9, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
      (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) where
  gradedIndex_apex := gradedIndex_threeType_last hα
  eq_apex _ hz := StageType.eq_last_of_gradedIndex_addApex (t := threeBase hα)
    isLegalBelowFullGrade_S (by omega) hz
  label_apex := label_threeType_last hα
  rootBottom z _ hz := (StageType.rowAt_addApex_last_eq_bot_iff (t₀ := threeBase hα)
    isLegalBelowFullGrade_S (by omega) z).mpr hz
  rowAt_apex_off z _ hz := (StageType.rowAt_addApex_last_eq_bot_iff (t₀ := threeBase hα)
    isLegalBelowFullGrade_S (by omega) z).mpr hz
  face_bot z hz := by
    rcases cases_threeType hα z with rfl | ⟨a, rfl⟩
    · exact absurd (Eq.mpr (congrArg (Fin.last 3 ∈ ·)
        (congrArg Prod.fst (gradedIndex_threeType_last hα))) (mem_univ _)) hz
    · refine (label_threeType_castSucc hα a).trans (labelling_bot_eq_bot_of_notMem a fun h3 ↦ hz ?_)
      exact Eq.mpr (congrArg (Fin.last 3 ∈ ·)
        (congrArg Prod.fst (gradedIndex_threeType_castSucc hα a))) h3
  grade_one := (grade_threeType_castSucc hα _).trans rfl
  grade_two := (grade_threeType_castSucc hα _).trans rfl
  row_tie := rowTie_threeType hα
  tie_one p hp z hz hl := tie_one_threeType hα hp z hz hl
  tie_two p _ z hz hl := by
    rcases cases_threeType hα z with rfl | ⟨a, rfl⟩
    · exact absurd ((grade_threeType_last hα).symm.trans hz) (by decide)
    · have ha : TwoFaceLiftCounterexample.cellGrade a = 2 :=
        (grade_threeType_castSucc hα a).symm.trans hz
      have h15 := eq_fifteen_of_live a ha (live_of_labelling_three_ne_bot
        ((label_threeType_castSucc hα a).symm.trans_ne hl))
      rw [show a = (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card) from h15]
      rfl
  label_three z hz := by
    rcases cases_threeType hα z with rfl | ⟨a, rfl⟩
    · exact absurd ((grade_threeType_last hα).symm.trans hz) (by decide)
    · exact (label_threeType_castSucc hα a).trans
        (labelling_three_eq_bot_of_grade ((grade_threeType_castSucc hα a).symm.trans hz))

/-- **`rightType` is a right coatom type with a new top** at its cell `{3}` (labelled `⊤`); its
rows raise at the point `3` (`TowerProfile.rowsRaiseAt_rightType`). -/
theorem rightNewTop_rightType (α : Ordinal.{u}) :
    RightNewTop (rightType α)
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) where
  rowsRaiseAt := rowsRaiseAt_rightType
  mem_scope := by
    change (3 : Fin 4) ∈ (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).scope
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
    rw [Scheme.appendFullCellScheme_scope_castSucc]
    decide
  grade_eq := by
    change (Scheme.appendFullCellScheme CaseSplitCounterexample.S 4).grade
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) = 1
    rw [Scheme.appendFullCellScheme_grade_castSucc]
    rfl
  label_eq := by
    change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]

/-- **The fill at the short positive caps from the left coatom holds at `seedThree`**
(`TowerProfile.readingFillPos_left_of_coatoms`, `leftTie_threeType`, `rightNewTop_rightType`). -/
theorem readingFillPos_left_seedThree :
    ReadingFillPos (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
      (newTops (seedThree hα)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))) (Fin.last 4) :=
  readingFillPos_left_of_coatoms (leftTie_threeType hα (Function.Embedding.refl _))
    (rightNewTop_rightType α)

/-- **The restricted reading layer is legal below the full grade at `seedThree`**, the first
proper-labelled marker that keeps the tie of its root label
(`TowerProfile.isLegalBelowFullGrade_readingTop_of_coatoms`, `leftTie_threeType`,
`rightNewTop_rightType`). -/
theorem isLegalBelowFullGrade_readingTop_seedThree :
    (readingTop (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
      (newTops (seedThree hα)
        (Fin.castSucc (⟨3, by decide⟩ :
          Fin CaseSplitCounterexample.S.{u}.card)))).IsLegalBelowFullGrade :=
  isLegalBelowFullGrade_readingTop_of_coatoms
    (leftTie_threeType hα (Function.Embedding.refl _)) (rightNewTop_rightType α)

/-- **`seedThree` is not an acquired context along the identity**: an acquired context on four
points has a root of at most two points (`TowerProfile.arity_le_two_of_isMarkedCapContextAt`); the
tie at `threeType` is along the identity root. -/
theorem not_isMarkedCapContextAt_threeType (c r : Fin (threeType hα).card) :
    ¬ (threeType hα).IsMarkedCapContextAt (Function.Embedding.refl (Fin 4)) c r := fun h ↦
  absurd (arity_le_two_of_isMarkedCapContextAt h) (by omega)

/-- The root `{2, 3}` of `threeType`. -/
def rootTwoThree : Fin 2 ↪ Fin 4 := ⟨![2, 3], by decide⟩

/-- A cell of `threeType` labelled `⊤` is the apex. -/
theorem eq_last_of_label_top {x : Fin (threeType hα).card} (hx : (threeType hα).label x = ⊤) :
    x = Fin.last _ := by
  rcases cases_threeType hα x with hxl | ⟨a, rfl⟩
  · exact hxl
  · exfalso
    have hl := (label_threeType_castSucc hα a).symm.trans hx
    rcases labelling_three_cases a with h3 | h0
    · rw [h3, lab3, natCast_label] at hl
      exact WithTop.coe_ne_top (WithBot.coe_injective hl)
    · rw [h0] at hl
      exact bot_ne_top hl

/-- **The apex of `threeType` is a marked cap along the root `{2, 3}`** (top cap and its own
marker; the root has no cell labelled `⊤`). -/
theorem isMarkedCapContextAt_threeType :
    (threeType hα).IsMarkedCapContextAt rootTwoThree (Fin.last _) (Fin.last _) := by
  have hcs : (threeType hα).toCellScheme.scope (Fin.last _) = univ :=
    congrArg Prod.fst (gradedIndex_threeType_last hα)
  refine ⟨⟨hcs, label_threeType_last hα, fun x _ ↦
      ((threeType hα).grade_le x).trans (grade_threeType_last hα).ge⟩,
    ⟨label_threeType_last hα, (threeType hα).toCellScheme.mem_below_gradedIndex _,
      fun x hx _ ↦ by rw [eq_last_of_label_top hα hx]⟩,
    by rw [grade_threeType_last]; omega, fun a ha hat ↦ ?_⟩
  exfalso
  obtain rfl := eq_last_of_label_top hα hat
  have h0 : ((0 : Fin 4) : Fin 4) ∈
      ((threeType hα).toCellScheme.scope (Fin.last _) : Set (Fin 4)) := by
    rw [hcs]; exact mem_univ _
  obtain ⟨i, hi⟩ := Scheme.mem_visibleCells.mp ha h0
  fin_cases i <;> simp [rootTwoThree] at hi

/-- **`threeType` is an acquired marked-cap context along the root `{2, 3}`**
(`TiedRootCapRelabel.MarkedCapContextBelow'`): the root offsets lie below the grade `4` of the apex
(its only ordinal label is `3`), and the apex reads the cells labelled `⊥` as `⊥`. -/
theorem markedCapContextBelow'_threeType :
    TiedRootCapRelabel.MarkedCapContextBelow' (threeType hα) rootTwoThree :=
  ⟨Fin.last _, Fin.last _, isMarkedCapContextAt_threeType hα,
    (grade_threeType_last hα).symm ▸ rootOffsetsBelow_threeType hα _,
    (leftTie_threeType hα rootTwoThree).rootBottom⟩

/-- **The tied cell of grade `2` of `threeType` is never a root cell of an acquired context**: the
cell `15` has full scope, so it is visible only through a root of four points, while an acquired
context on four points has a root of at most two
(`TowerProfile.arity_le_two_of_isMarkedCapContextAt`).
So `TowerProfile.isLegalBelowFullGrade_readingTop_of_acquired` (tied cells on the root) has no
instance with this family's tied cells; the off-root form applies. -/
theorem fifteen_notMem_visibleCells {n : ℕ} (h : Fin n ↪ Fin 4) (hn : n ≤ 2) :
    (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card) :
      Fin (threeType hα).card) ∉ (threeType hα).visibleCells h := by
  intro hv
  have hset := Scheme.mem_visibleCells.mp hv
  have hsub : (threeType hα).toCellScheme.scope
      (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) ⊆ univ.map h :=
    fun x hx ↦ by
      obtain ⟨i, rfl⟩ := hset (mem_coe.mpr hx)
      exact mem_map_of_mem _ (mem_univ i)
  have hs : (threeType hα).toCellScheme.scope
      (Fin.castSucc (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)) = univ := by
    have := congrArg Prod.fst (gradedIndex_threeType_castSucc hα
      (⟨15, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))
    exact this.trans (show TwoFaceLiftCounterexample.cellScope (15 : Fin 19) = univ by decide)
  have := card_le_card hsub
  rw [hs] at this
  simp at this
  omega

/-- **An acquired instance of the legality of the restricted reading layer**: at `seedThree`, with
the left coatom type `threeType` an acquired context along the root `{2, 3}`
(`markedCapContextBelow'_threeType`),
`TowerProfile.isLegalBelowFullGrade_readingTop_of_acquired_offRoot` applies (the cell `15` tied
to the cell `9` is off the root, `fifteen_notMem_visibleCells`; the offsets of `threeType` lie
below `4` at every label). -/
theorem isLegalBelowFullGrade_readingTop_seedThree_of_acquired :
    (readingTop (seedThree hα) (leftCell (seedThree hα) (Fin.last _))
      (newTops (seedThree hα)
        (Fin.castSucc (⟨3, by decide⟩ :
          Fin CaseSplitCounterexample.S.{u}.card)))).IsLegalBelowFullGrade := by
  have hL := leftTie_threeType hα rootTwoThree
  exact isLegalBelowFullGrade_readingTop_of_acquired_offRoot (I := seedThree hα)
    (isMarkedCapContextAt_threeType hα) hL.rootBottom (grade_threeType_last hα) hL.eq_apex
    hL.rowAt_apex_off hL.face_bot
    ((grade_threeType_last hα).symm ▸ rootOffsetsBelow_threeType hα _) hL.grade_one hL.grade_two
    (label_fifteen_eq_nine hα) (isProper_label_fifteen hα) hL.tie_one hL.tie_two hL.label_three
    (rightNewTop_rightType α)

end TopReadingApexExample

end VaughtConjecture
