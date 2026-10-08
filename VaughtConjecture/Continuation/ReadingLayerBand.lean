/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerServers

/-!
# The band at `seedThree`: the strip and a filled band case

Roadmap, Layer 3 ((R3) of the table of 3.4).

The fill at the short caps from the left coatom at `seedThree` reduces to the **band case**
(`TowerProfile.readingFillPos_left_of_noBand`): a labelling `f` lawful below the left coatom,
agreeing with a reading mark `e` capped at `h`, with a left cell `y` in the band
`h ≤ f y < f r`.  In the failure of the two-face lift at grade `2` the band is closed by a
**strip**: a cell of full scope forced to `⊤` (availability, from a right cell prescribed `⊤`),
reading the band cell as its top, so every choice of the right part is blocked.  In the reading
fill the right part is not prescribed: only `x` must be raised to at least `f r`, and the cells
forced above the band at the grade of `x` are the servers of `x`, which exist at `seedThree`
(`TowerProfile.exists_server_of_rightType`).  So the strip does not form there (argued, not
compiled in this file: no lemma states the strip for every choice of the right part).  This file
compiles the escape with `x := ⊤` at one band labelling.

* **Collapsing the proper labels** (`Label.isWitness_bandCollapse`, compiled in this repository
  (theorem named)): for a value `v ≠ ⊥` self-visible at `K`, the map keeping `⊥` and `⊤` and
  sending every other label to `v` is a witness for the step suppressor at `K`; so it preserves
  lawfulness on schemes of grades at most `K` (`CellScheme.Rows.IsLawful.map_of_apply_eq_bot`).
* **A filled band case at every seed** (`TowerProfile.exists_band_fill`, compiled): for cells
  `r`, `x` of the amalgam labelled `⊤` and a cell `y` with a proper label, the glued labelling of
  the completion collapsed to `5` is lawful on the profile layer; with its orbit code as the
  reading mark, the cap `4` and `f` this labelling, `f` is in the band at `y`
  (`4 ≤ f y = 5 < ⊤ = f r`) and is its own fill, with `x` at `⊤`.
* **At `seedThree`** (`TopReadingApexExample.exists_band_fill_seedThree`, compiled): the marker
  the apex of `threeType`, the new top `x` the cell `{3}` of `rightType` (labelled `⊤`), the band
  cell `y` the cell `{3}` of `threeType` (labelled `3`).

**Verdict**: the strip mechanism does not block the band at `seedThree`: a band labelling with
the left cell `y` in the band has a fill with the right part free (`x := ⊤`), compiled as a
**positive instance** (feasibility only: the fill is the band labelling itself, and the mark
reads `y` strictly below `x`).  The fill for **every** band labelling and mark (Step B) is not
done here; it is in the module `VaughtConjecture.Continuation.ReadingLayerBandFill`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Collapsing the proper labels -/

namespace Label

open Classical in
/-- **Collapsing to `v`**: `⊥` and the formal top kept, every other label sent to `v`. -/
noncomputable def bandCollapse (v x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else if x = ⊤ then ⊤ else v

variable {v x : Label.{u}}

theorem bandCollapse_bot : bandCollapse v ⊥ = ⊥ := ite_eq_left rfl

theorem bandCollapse_top : bandCollapse v ⊤ = ⊤ := by simp [bandCollapse]

theorem bandCollapse_of_ne (hb : x ≠ ⊥) (ht : x ≠ ⊤) : bandCollapse v x = v := by
  simp [bandCollapse, hb, ht]

theorem eq_bot_of_bandCollapse_eq_bot (hv : v ≠ ⊥) (h : bandCollapse v x = ⊥) : x = ⊥ := by
  by_contra hb
  by_cases ht : x = ⊤
  · rw [ht, bandCollapse_top] at h
    exact top_ne_bot h
  · exact hv ((bandCollapse_of_ne hb ht).symm.trans h)

/-- **Collapsing to `v` is a witness bounded by the grade `K`** when `v` is self-visible at `K`
and is not `⊥`. -/
theorem isWitness_bandCollapse {K : ℕ} (hv : IsSelfVisible K v) (hvb : v ≠ ⊥) :
    IsWitness (stepSuppressor.{u} K) (bandCollapse v) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := bandCollapse_bot
  monotone a b hab := by
    by_cases ha : a = ⊥
    · rw [ha, bandCollapse_bot]
      exact bot_le
    have hb : b ≠ ⊥ := fun hb ↦ ha (le_bot_iff.mp (hb ▸ hab))
    by_cases hbt : b = ⊤
    · rw [hbt, bandCollapse_top]
      exact le_top
    have hat : a ≠ ⊤ := fun hat ↦ hbt (top_le_iff.mp (hat ▸ hab))
    rw [bandCollapse_of_ne ha hat, bandCollapse_of_ne hb hbt]
  visibilityReplace_comm y k hy i hi := by
    induction y using recBotCoeTop with
    | bot => simp [bandCollapse_bot]
    | top => simp [bandCollapse_top]
    | coe o =>
      have h₁ : (o : Label.{u}) ≠ ⊥ := WithBot.coe_ne_bot
      have h₂ : (o : Label.{u}) ≠ ⊤ := by simp
      rw [bandCollapse_of_ne h₁ h₂] at hy ⊢
      rw [visibilityReplace_coe, bandCollapse_of_ne WithBot.coe_ne_bot (by simp)]
      rcases le_or_gt k K with hk | hk
      · exact ((hv.mono hk).visibilityReplace_eq i).symm
      · rw [stepSuppressor_of_lt hk, le_bot_iff] at hy
        exact absurd hy hvb

end Label

/-! ### A filled band case -/

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **A filled band case at every seed**: let `r`, `x` be cells of the amalgam labelled `⊤` and
`y` a cell with a proper label, the cells of `r` and `y` below the left coatom.  The glued
labelling of the completion with every proper label collapsed to `5` (`Label.bandCollapse`) is a
lawful labelling `g` of the profile layer; with the reading mark `e` its orbit code, the cap `4`
(`gridPoint 4 0`), and `f = g`, the labelling `f` is in the band at `y` (`4 ≤ f y = 5 < ⊤ = f r`)
and `g` is the fill.  Feasibility only: the mark reads `y` strictly below `x`. -/
theorem exists_band_fill {r x y : Fin I.amalgam.card} (hr : I.amalgam.label r = ⊤)
    (hx : I.amalgam.label x = ⊤) (hy0 : I.amalgam.label y ≠ ⊥) (hyt : I.amalgam.label y ≠ ⊤) :
    ∃ e ∈ (scheme I).readingMarks 4 (embed3 I r) {embed3 I x}, ∃ (h : Label.{u})
      (f : Fin (scheme I).card → Label.{u}), IsSelfVisible 4 h ∧ IsShort 4 h ∧ ⊥ < h ∧
      (scheme I).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) ∧
      (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4),
        min (f d) h = min (e d) h) ∧ h ≤ f (embed3 I y) ∧ f (embed3 I y) < f (embed3 I r) ∧
      ∃ g : Fin (scheme I).card → Label.{u},
        (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
        (∀ d ∈ (scheme I).toCellScheme.below (univ.erase (Fin.last 4), 4), g d = f d) ∧
        (∀ d, min (g d) h = min (e d) h) ∧ ∀ x' ∈ ({embed3 I x} : Finset _),
          g (embed3 I r) ≤ g x' := by
  classical
  obtain ⟨q, hq, hqe⟩ := exists_isLawful_top (I := I)
  have hL := hq.comap (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le)
  rw [Scheme.comap_rows_fieldLayer] at hL
  set L₀ : Fin (scheme I).card → Label.{u} := fun d ↦ q (Fin.castAdd _ d) with hL₀
  have hold (d : Fin I.amalgam.card) : L₀ (embed3 I d) = I.amalgam.label d := hqe d
  set v : Label.{u} := gridPoint 5 0 with hvdef
  have hv : IsSelfVisible 4 v := (isSelfVisible_gridPoint 5 0).mono (by omega)
  have hvb : v ≠ ⊥ := gridPoint_ne_bot 5 0
  set g : Fin (scheme I).card → Label.{u} := fun d ↦ bandCollapse v (L₀ d) with hgdef
  have hg : (scheme I).rows.IsLawful g :=
    hL.map_of_apply_eq_bot (K := 4) (fun d ↦ (mem_below_univ_four d).2)
      (isWitness_bandCollapse hv hvb) fun _ h ↦ eq_bot_of_bandCollapse_eq_bot hvb h
  have hg4 : (scheme I).rows.IsLawfulBelow (univ, 4) fun d ↦ g d := hg.isLawfulBelow _
  have hsplice : (scheme I).toCellScheme.splice 4 (fun _ ↦ ⊥) g = g :=
    funext fun d ↦ CellScheme.splice_of_le (mem_below_univ_four d).2
  have hmem := Scheme.orbitCode_splice_bot_mem_catalogue (S := scheme I) (k := 4) hg4
  rw [hsplice] at hmem
  have hgr : g (embed3 I r) = ⊤ := by
    change bandCollapse v (L₀ (embed3 I r)) = ⊤
    rw [hold, hr, bandCollapse_top]
  have hgx : g (embed3 I x) = ⊤ := by
    change bandCollapse v (L₀ (embed3 I x)) = ⊤
    rw [hold, hx, bandCollapse_top]
  have hgy : g (embed3 I y) = v := by
    change bandCollapse v (L₀ (embed3 I y)) = v
    rw [hold, bandCollapse_of_ne hy0 hyt]
  refine ⟨orbitCode 4 g, ?_, gridPoint 4 0, g, isSelfVisible_gridPoint 4 0,
    isShort_gridPoint 4 0, bot_lt_iff_ne_bot.mpr (gridPoint_ne_bot 4 0),
    hg.isLawfulBelow _, fun d _ ↦ (min_orbitCode_gridPoint_zero d).symm, ?_, ?_,
    g, hg4, fun _ _ ↦ rfl, fun d ↦ (min_orbitCode_gridPoint_zero d).symm, fun x' hx' ↦ ?_⟩
  · unfold Scheme.readingMarks
    refine mem_filter.mpr ⟨hmem, fun x' hx' ↦ ?_⟩
    rw [mem_singleton.mp hx', orbitCode_apply, orbitCode_apply, hgr, hgx]
  · rw [hgy]
    exact gridPoint_le_gridPoint_iff_lex.mpr (.inr ⟨rfl, by omega⟩)
  · rw [hgy, hgr]
    exact lt_top_iff_ne_top.mpr (gridPoint_ne_top 5 0)
  · rw [mem_singleton.mp hx', hgr, hgx]

end TowerProfile

namespace TopReadingApexExample

open TwoFaceLiftExistsCounterexample CaseSplitCounterexample TowerProfile

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **A filled band case at `seedThree`**: the marker the apex of `threeType`, the new top the
cell `{3}` of `rightType`, the band cell the cell `{3}` of `threeType` (labelled `3`). -/
theorem exists_band_fill_seedThree :
    ∃ e ∈ (scheme (seedThree hα)).readingMarks 4 (leftCell (seedThree hα) (Fin.last _))
      {embed3 (seedThree hα) (StageType.faceCell (seedThree hα).restrictFace_right
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)))},
    ∃ (h : Label.{u}) (f : Fin (scheme (seedThree hα)).card → Label.{u}),
      IsSelfVisible 4 h ∧ IsShort 4 h ∧ ⊥ < h ∧
      (scheme (seedThree hα)).rows.IsLawfulBelow (univ.erase (Fin.last 4), 4) (fun d ↦ f d) ∧
      (∀ d ∈ (scheme (seedThree hα)).toCellScheme.below (univ.erase (Fin.last 4), 4),
        min (f d) h = min (e d) h) ∧
      h ≤ f (leftCell (seedThree hα)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))) ∧
      f (leftCell (seedThree hα)
        (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))) <
        f (leftCell (seedThree hα) (Fin.last _)) ∧
      ∃ g : Fin (scheme (seedThree hα)).card → Label.{u},
        (scheme (seedThree hα)).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
        (∀ d ∈ (scheme (seedThree hα)).toCellScheme.below (univ.erase (Fin.last 4), 4),
          g d = f d) ∧
        (∀ d, min (g d) h = min (e d) h) ∧
        ∀ x' ∈ ({embed3 (seedThree hα) (StageType.faceCell (seedThree hα).restrictFace_right
          (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card)))} :
            Finset _), g (leftCell (seedThree hα) (Fin.last _)) ≤ g x' := by
  have hr : (seedThree hα).amalgam.label
      (StageType.faceCell (seedThree hα).restrictFace_left (Fin.last _)) = ⊤ :=
    (StageType.label_faceCell _ _).trans
      (StageType.addApex_label_last (t := threeBase hα) isLegalBelowFullGrade_S (by omega))
  have hx : (seedThree hα).amalgam.label (StageType.faceCell (seedThree hα).restrictFace_right
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))) = ⊤ := by
    refine (StageType.label_faceCell _ _).trans ?_
    change CaseSplitCounterexample.labelling (⊤ : Label.{u}) ⊤ ⊥ (3 : Fin 19) = ⊤
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]
  have hy : (seedThree hα).amalgam.label (StageType.faceCell (seedThree hα).restrictFace_left
      (Fin.castSucc (⟨3, by decide⟩ : Fin CaseSplitCounterexample.S.{u}.card))) = lab3 := by
    refine (StageType.label_faceCell _ _).trans ?_
    change CaseSplitCounterexample.labelling lab3 lab3 ⊥ (3 : Fin 19) = lab3
    simp [CaseSplitCounterexample.labelling, CaseSplitCounterexample.live,
      TwoFaceLiftCounterexample.cellGrade]
  exact exists_band_fill hr hx (by rw [hy]; exact natCast_label_ne_bot 3)
    (by rw [hy, lab3, natCast_label]; exact fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h))

end TopReadingApexExample

end VaughtConjecture
