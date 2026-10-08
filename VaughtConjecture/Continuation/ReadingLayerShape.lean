/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefineFill

/-!
# The reading layer without the tie at the grade `1`

Roadmap, Layer 3 ((R3) of the table of 3.4).

* **Legality** (`TowerProfile.isLegalBelowFullGrade_readingTop_of_shape`, compiled): at every seed
  on five points whose left coatom type has the shape `TowerProfile.LeftShape` (an apex reading
  the cells labelled `⊥` as `⊥`, the common face `⊥`, one value at the grade `2` below the values
  at the grade `1`, the grade `3` labelled `⊥`; any labels at the grade `1`) and whose right coatom
  type has new tops of grade `1` (`TowerProfile.RightOneTops`).
* **The clause** (`TowerProfile.exists_coface_of_shape`,
  `TowerProfile.exists_coface_of_addApex_shape`, compiled under the hypotheses named): at every
  apex context of that shape, every coface of its face with new tops of grade `1`, every root of
  at most two points, and every donor whose new tops labelled `⊤` lie in the set.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace TowerProfile

open TopReadingApexExample StageType

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **A left coatom type of the shape of the reading layer**, without a tie at the grade `1`: an
apex cell `a` (`TowerProfile.ApexCell`) reading every cell labelled `⊥` as `⊥`, the face off the
point `3` labelled `⊥`, one value at the cells of grade `2` not labelled `⊥` (that at `z₂`), at
most every value at the cells of grade `1` not labelled `⊥` when `z₂` is not labelled `⊥`, and the
cells of grade `3` labelled `⊥`.  The cells of grade `1` may carry any labels. -/
structure LeftShape {β : Ordinal.{u}} (t' : StageType.{u} β 4) (a z₂ : Fin t'.card) : Prop where
  apex : ApexCell t' a
  rowAt_apex : ∀ z, t'.label z = ⊥ → t'.toScheme.rowAt a z = ⊥
  face_bot : ∀ z, Fin.last 3 ∉ t'.toCellScheme.scope z → t'.label z = ⊥
  grade_two : t'.toCellScheme.grade z₂ = 2
  tie_two : ∀ p : Fin t'.card → Label.{u}, t'.rows.IsLawful p → ∀ z,
    t'.toCellScheme.grade z = 2 → t'.label z ≠ ⊥ → p z = p z₂
  one_two : t'.label z₂ ≠ ⊥ → ∀ p : Fin t'.card → Label.{u}, t'.rows.IsLawful p → ∀ z,
    t'.toCellScheme.grade z = 1 → t'.label z ≠ ⊥ → p z₂ ≤ p z
  label_three : ∀ z, t'.toCellScheme.grade z = 3 → t'.label z = ⊥

/-- **A right coatom type with new tops of grade `1`** `Z`: every cell of `Z` lies through the
point `3`, has grade `1`, and is labelled `⊤`.  No condition on the rows. -/
structure RightOneTops {β : Ordinal.{u}} (tb : StageType.{u} β 4) (Z : Finset (Fin tb.card)) :
    Prop where
  mem_scope : ∀ z ∈ Z, (3 : Fin 4) ∈ tb.toCellScheme.scope z
  grade_eq : ∀ z ∈ Z, tb.toCellScheme.grade z = 1
  label_eq : ∀ z ∈ Z, tb.label z = ⊤

/-- **The fill at the short positive caps from the left coatom at a left coatom type of the
shape** (`TowerProfile.readingFillPos_left_of_refine`). -/
theorem readingFillPos_left_of_shape {a z₂ : Fin I.left.card} (hL : LeftShape I.left a z₂)
    {Z : Finset (Fin I.right.card)} (hR : RightOneTops I.right Z) :
    ReadingFillPos I (leftCell I a) (newTopsOf I Z) (Fin.last 4) := by
  obtain ⟨hgr, hrC, -⟩ := leftCell_props (I := I) hL.apex.gradedIndex_apex hL.apex.eq_apex
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
  have hlab {f : Fin (scheme I).card → Label.{u}}
      (hf : (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) fun d ↦ f d)
      (hfr : f (leftCell I a) ≠ ⊥) {z : Fin I.left.card} (h0 : f (leftCell I z) ≠ ⊥) :
      I.left.label z ≠ ⊥ := fun hz ↦ h0 (hfr0 hf hfr z hz)
  refine readingFillPos_left_of_refine hrC (t₂ := leftCell I z₂)
    (fun x hx ↦ ?_) (leftCell_mem z₂) ((grade_leftCell z₂).trans hL.grade_two)
    (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg h0 ↦ ?_) (fun f hf hfr d hd hg ↦ ?_)
    (fun f hf hfr d hd hd3 ↦ ?_)
  · obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    exact ⟨_, rfl, (last_mem_scope_right I.restrictFace_right z).mpr (hR.mem_scope z hz),
      (StageType.grade_faceCell _ _).trans (hR.grade_eq z hz)⟩
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hL.tie_two _ (isLawful_left_of_isLawfulBelow hf) z ((grade_leftCell z).symm.trans hg)
      (hlab hf hfr h0)
  · obtain ⟨z, rfl⟩ := hcell hd
    by_cases hz₂ : I.left.label z₂ = ⊥
    · rw [hfr0 hf hfr z₂ hz₂]; exact bot_le
    · exact hL.one_two hz₂ _ (isLawful_left_of_isLawfulBelow hf) z
        ((grade_leftCell z).symm.trans hg) (hlab hf hfr h0)
  · obtain ⟨z, rfl⟩ := hcell hd
    exact hfr0 hf hfr z (hL.label_three z ((grade_leftCell z).symm.trans hg))
  · obtain ⟨z, rfl⟩ := hcell hd
    refine hfr0 hf hfr z (hL.face_bot z fun h3 ↦ hd3 ?_)
    rw [← CellScheme.gradedIndex_fst, gradedIndex_leftCell]
    exact mem_map_of_mem _ h3

/-- **The restricted reading layer is legal below the full grade at every seed on five points whose
left coatom type has the shape and whose right coatom type has new tops of grade `1`**: the four
fill conditions, the fill from the left coatom at the short positive caps from a refining server
(`TowerProfile.readingFillPos_left_of_shape`). -/
theorem isLegalBelowFullGrade_readingTop_of_shape {a z₂ : Fin I.left.card}
    (hL : LeftShape I.left a z₂) {Z : Finset (Fin I.right.card)} (hR : RightOneTops I.right Z) :
    (readingTop I (leftCell I a) (newTopsOf I Z)).IsLegalBelowFullGrade := by
  obtain ⟨hgr, hrC, huniq⟩ := leftCell_props (I := I) hL.apex.gradedIndex_apex hL.apex.eq_apex
  have hX3 : ∀ x ∈ newTopsOf I Z, (scheme I).toCellScheme.grade x ≤ 3 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    rw [← CellScheme.gradedIndex_snd, gradedIndex_embed3, CellScheme.gradedIndex_snd,
      StageType.grade_faceCell, hR.grade_eq z hz]
    omega
  refine (isLegalBelowFullGrade_readingTop_iff hgr fun x hx ↦ (hX3 x hx).trans (by omega)).mpr
    ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillBot_left_of_left hL.apex.gradedIndex_apex hL.rowAt_apex hL.face_bot _
        hR.label_eq
    · rw [mem_singleton.mp hz]
      exact readingFillBot_right_of_unique hgr hrC huniq
  · rcases mem_insert.mp hz with rfl | hz
    · exact readingFillPos_left_of_shape hL hR
    · rw [mem_singleton.mp hz]
      exact readingFillPos_right_of_unique hgr hrC huniq hX3

/-! ### The clause without the tie at the grade `1` -/

variable (hα : Order.IsSuccLimit α)

include hα in
/-- **The clause at a context of the shape and a coface with new tops of grade `1`**
(`TowerProfile.exists_coface_of_legal` at the seed of the two coatom types): every root of at
most two points and every donor of the coface whose new tops labelled `⊤` lie in `Z`. -/
theorem exists_coface_of_shape {t' tb : StageType.{u} α 4} {p : StageType.{u} α 3}
    (hlt : t'.IsLegal) (hpa : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
    {a z₂ : Fin t'.card} (hL : LeftShape t' a z₂) {Z : Finset (Fin tb.card)}
    (hR : RightOneTops tb Z) {n : ℕ} (g : Fin n ↪ Fin 3) (hn : n ≤ 2)
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d :=
  exists_coface_of_legal (I := Seed.ofCoatoms hlt htb.1 hpa htb.2) hL.apex hR.label_eq
    (isLegalBelowFullGrade_readingTop_of_shape hL hR) hα hn hd hcover

include hα in
/-- **The clause at every apex context of the shape** (compiled under the hypotheses named): let
`t' = t₀.addApex` be the apex type of `t₀` legal below the full grade, with the common face
labelled `⊥` (`hface`), one value at the cells of grade `2` not labelled `⊥` (`htwo`, at `z₂`), at
most every value at the cells of grade `1` not labelled `⊥` when `z₂` is not labelled `⊥`
(`honetwo`), and the cells of grade `3` labelled `⊥` (`hthree`).  The cells of grade `1` may carry
any labels: no tie at the grade `1`, no root condition, no condition on the rows of the coface.
Then the clause of hollow coatom cutoff determination holds at `t'`, every coface `tb` of its face
with new tops `Z` of grade `1` (`TowerProfile.RightOneTops`), every root of at most two points,
and every donor of `tb` whose new tops labelled `⊤` lie in `Z`.  The apex is the cap and the
marker; its uniqueness, its grade and its reading of the cells labelled `⊥` are those of the apex
row. -/
theorem exists_coface_of_addApex_shape {t₀ : StageType.{u} α 4}
    (ht₀ : t₀.IsLegalBelowFullGrade) {p : StageType.{u} α 3}
    (hpa : restrictFace Fin.castSuccEmb (apexOf ht₀) = some p)
    (hface : ∀ z, Fin.last 3 ∉ (apexOf ht₀).toCellScheme.scope z → (apexOf ht₀).label z = ⊥)
    {z₂ : Fin (apexOf ht₀).card} (hg₂ : (apexOf ht₀).toCellScheme.grade z₂ = 2)
    (htwo : ∀ q : Fin (apexOf ht₀).card → Label.{u}, (apexOf ht₀).rows.IsLawful q → ∀ z,
      (apexOf ht₀).toCellScheme.grade z = 2 → (apexOf ht₀).label z ≠ ⊥ → q z = q z₂)
    (honetwo : (apexOf ht₀).label z₂ ≠ ⊥ → ∀ q : Fin (apexOf ht₀).card → Label.{u},
      (apexOf ht₀).rows.IsLawful q → ∀ z, (apexOf ht₀).toCellScheme.grade z = 1 →
        (apexOf ht₀).label z ≠ ⊥ → q z₂ ≤ q z)
    (hthree : ∀ z, (apexOf ht₀).toCellScheme.grade z = 3 → (apexOf ht₀).label z = ⊥)
    {tb : StageType.{u} α 4} (htb : tb ∈ p.cofaces) {Z : Finset (Fin tb.card)}
    (hR : RightOneTops tb Z) {n : ℕ} (g : Fin n ↪ Fin 3) (hn : n ≤ 2)
    {d : StageType.{u} α (n + 1)} (hd : restrictFace (extendByLast g) tb = some d)
    (hcover : ∀ j, Fin.last n ∈ d.toCellScheme.scope j → d.label j = ⊤ → faceCell hd j ∈ Z) :
    ∃ D' ∈ (apexOf ht₀).cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
      ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
        IsDeterminedWithin (receivingFamily D' δ) (apexOf ht₀) (g.trans Fin.castSuccEmb) d :=
  exists_coface_of_shape hα (StageType.isLegal_addApex _ _) hpa htb
    { apex := ⟨StageType.addApex_gradedIndex_last ht₀ (by omega),
        fun _ hz ↦ StageType.eq_last_of_gradedIndex_addApex ht₀ (by omega) hz,
        StageType.addApex_label_last ht₀ (by omega)⟩
      rowAt_apex := fun z hz ↦ (StageType.rowAt_addApex_last_eq_bot_iff ht₀ (by omega) z).mpr hz
      face_bot := hface
      grade_two := hg₂
      tie_two := htwo
      one_two := honetwo
      label_three := hthree } hR g hn hd hcover

end TowerProfile

end VaughtConjecture
