/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefineTwoLawful
import VaughtConjecture.Extension.SectionInterface

/-!
# A frozen state at the seed of the coatom types `TL` and `T5`

Roadmap, Layer 3 ((R3) of the table of 3.4).

Route (b) to `TowerProfile.RefiningServerTwo` (a separating server,
`TowerProfile.SeparatingServersTwo`) is refuted at `seedL`
(`TowerProfile.not_separatingServersTwo_seedL`): the profile `(1, 2, 1, 2, ⊥)` of five parameters
is lawful below both coatoms; its tower section at the layer of grade `1`
(`TowerProfile.isLawfulBelow_towerSection_one_two`) has an orbit code at `2` reading the cell
`({3}, 1)` at `1` and the cell `({0, 1, 2, 3}, 2)` at `2` (`TowerProfile.lowEntryTwo_of_section`,
`TowerProfile.lowEntryTwo_of_TL`).  At the support labelling of its field row and the cap `4`
every server at least `4` is frozen (`TowerProfile.exists_frozen_of_entry`).
`TowerProfile.RefiningServerTwo` is open at `seedL`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme
open scoped Ordinal

namespace TowerProfile

open TopReadingApexExample StageType

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The tower section at the layer of grade `1` is lawful below `(univ, 2)`**, for an amalgam
labelling lawful below both coatoms at `2` (the step at the grade `2` of
`Seed.isLawfulBelow_towerSection`, before the decoded layer). -/
theorem isLawfulBelow_towerSection_one_two (B : ℕ) {x y : Fin 5}
    (hcov : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y)
    {w : Fin I.amalgam.card → Label.{u}}
    (hwx : I.amalgam.rows.IsLawfulBelow (univ.erase x, 2) (fun d ↦ w d))
    (hwy : I.amalgam.rows.IsLawfulBelow (univ.erase y, 2) (fun d ↦ w d)) :
    (I.tower 1).rows.IsLawfulBelow (univ, 2) fun e ↦ I.towerSection B 1 w e := by
  have hr₀ := Seed.isLawfulBelow_towerSection (B := B) hcov 1 (by omega)
    (hwx.mono (X := (univ.erase x, 1)) ⟨subset_rfl, by omega⟩)
    (hwy.mono (X := (univ.erase y, 1)) ⟨subset_rfl, by omega⟩)
  set g := I.towerSection B 1 w with hg_def
  have hgw (d : Fin I.amalgam.card) : g (I.towerEmbed 1 d) = w d :=
    Seed.towerSection_towerEmbed 1 w d
  have hgx : (I.tower 1).rows.IsLawfulBelow (univ.erase x, 2) fun e ↦ g e := by
    rw [I.isLawfulBelow_tower_iff (Seed.ne_univ_erase x)]
    simpa only [hgw] using hwx
  have hgy : (I.tower 1).rows.IsLawfulBelow (univ.erase y, 2) fun e ↦ g e := by
    rw [I.isLawfulBelow_tower_iff (Seed.ne_univ_erase y)]
    simpa only [hgw] using hwy
  refine Rows.IsLawfulBelow.glue₃ hgx hr₀ hgy fun e he ↦ ?_
  by_cases hej : (I.tower 1).toCellScheme.grade e ≤ 1
  · exact .inr (.inl ⟨subset_univ _, hej⟩)
  · obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 1 e ((I.tower_grade_le_or 1 e).resolve_left hej)
    have hd : I.amalgam.toCellScheme.grade d ≤ 2 := (I.grade_towerEmbed 1 d).symm.trans_le he.2
    rcases hcov d with h | h
    · exact .inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
    · exact .inr (.inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))

/-- **A low entry from an amalgam labelling**: an amalgam labelling lawful below both coatoms at
`2`, reading a cell of grade at most `2` in `(⊥, 2)` and a cell of grade `2` not by `⊥`, gives a
low entry (`TowerProfile.LowEntryTwo`): the orbit code at `2` of its tower section at the layer of
grade `1`, which keeps the labelling below `2` (`Label.min_orbitCode_gridPoint_zero`). -/
theorem lowEntryTwo_of_section (B : ℕ) {x y : Fin 5}
    (hcov : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase x ∨
      I.amalgam.toCellScheme.scope d ⊆ univ.erase y)
    {w : Fin I.amalgam.card → Label.{u}}
    (hwx : I.amalgam.rows.IsLawfulBelow (univ.erase x, 2) (fun d ↦ w d))
    (hwy : I.amalgam.rows.IsLawfulBelow (univ.erase y, 2) (fun d ↦ w d))
    {d₁ s : Fin I.amalgam.card} (hd₁ : I.amalgam.toCellScheme.grade d₁ ≤ 2) (hw₁ : w d₁ ≠ ⊥)
    (hw₁2 : w d₁ < (((2 : Ordinal.{u})) : Label.{u}))
    (hs : I.amalgam.toCellScheme.grade s = 2) (hws : w s ≠ ⊥) : LowEntryTwo I := by
  classical
  have hp := isLawfulBelow_towerSection_one_two B hcov hwx hwy
  set p := I.towerSection B 1 w with hpdef
  have hb := Scheme.orbitCode_splice_bot_mem_catalogue (S := I.tower 1) (k := 2) hp
  set b := orbitCode 2 ((I.tower 1).toCellScheme.splice 2 (fun _ ↦ ⊥) p) with hbdef
  set i := ((I.tower 1).catalogue 2).equivFin ⟨b, hb⟩ with hidef
  have hi : (I.tower 1).catalogueEntry 2 i = b := by
    simp [Scheme.catalogueEntry, hidef]
  have hsp (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      (I.tower 1).toCellScheme.splice 2 (fun _ ↦ ⊥) p (I.towerEmbed 1 d) = w d :=
    (CellScheme.splice_of_le ((I.grade_towerEmbed 1 d).trans_le hd)).trans
      (Seed.towerSection_towerEmbed 1 w d)
  have h2 : gridPoint.{u} 2 0 = (((2 : Ordinal.{u})) : Label.{u}) := by simp [gridPoint]
  have hval (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      min (b (I.towerEmbed 1 d)) (((2 : Ordinal.{u})) : Label.{u}) =
        min (w d) (((2 : Ordinal.{u})) : Label.{u}) := by
    have := min_orbitCode_gridPoint_zero (k := 2)
      (w := (I.tower 1).toCellScheme.splice 2 (fun _ ↦ ⊥) p) (I.towerEmbed 1 d)
    rwa [hsp d hd, h2] at this
  have hbot (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 2) :
      b (I.towerEmbed 1 d) = ⊥ ↔ w d = ⊥ := by
    rw [hbdef, orbitCode_eq_bot_iff, hsp d hd]
  refine ⟨i, ⟨I.towerEmbed 1 d₁, (I.grade_towerEmbed 1 d₁).trans_le hd₁, ?_, ?_⟩,
    I.towerEmbed 1 s, (I.grade_towerEmbed 1 s).trans hs, ?_⟩
  · rw [hi]
    exact fun h ↦ hw₁ ((hbot d₁ hd₁).mp h)
  · rw [hi, eq_of_min_eq_of_lt (hval d₁ hd₁).symm hw₁2]
    exact hw₁2
  · rw [hi]
    exact fun h ↦ hws ((hbot s hs.le).mp h)

open TwoFaceLiftExistsCounterexample (TL seedL)
open CaseSplitCounterexample (T5 tripleKind)
open ProfileCatalogue (tripleProfile tripleProfile_apply tripleLabelling_of_kind exists_test_cells)

/-- **A low entry at a seed of the coatom types `TL` and `T5`**: the tower section of the profile
`(1, 2, 1, 2, ⊥)` of five parameters (`SectionInterface.tripleProfile_mem_rankCat`) reads the cell
`({3}, 1)` at `1` and the cell `({0, 1, 2, 3}, 2)` at `2`. -/
theorem lowEntryTwo_of_TL (hIL : I.left = TL α) (hIR : I.right = T5 α) : LowEntryTwo I := by
  have hP := SectionInterface.tripleProfile_mem_rankCat (I := I) hIL hIR (.inl rfl) rfl
    (.inl rfl) rfl
  obtain ⟨⟨hC, hD⟩, -⟩ := RankProfile.mem_rankCat.mp hP
  obtain ⟨d₁, sC, -, -, hd₁, hsC, -, -⟩ := exists_test_cells hIL hIR
  have hk₁ : tripleKind (I.amalgam.toCellScheme.gradedIndex d₁) = 1 := by
    rw [hd₁]; decide
  have hks : tripleKind (I.amalgam.toCellScheme.gradedIndex sC) = 2 := by
    rw [hsC]; decide
  have hv₁ : tripleProfile I (gridPoint 1 0) (gridPoint 2 0) (gridPoint 1 0)
      (gridPoint 2 0) ⊥ d₁ = gridPoint 1 0 := by
    rw [tripleProfile_apply, tripleLabelling_of_kind hk₁]; rfl
  have hvs : tripleProfile I (gridPoint 1 0) (gridPoint 2 0) (gridPoint 1 0)
      (gridPoint 2 0) ⊥ sC = gridPoint 2 0 := by
    rw [tripleProfile_apply, tripleLabelling_of_kind hks]; rfl
  refine lowEntryTwo_of_section 0 (I.scope_subset_or (x := Fin.last 4)
    (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide))
    (hC.mono (X := (OrderedLayer.coatomC, 2)) ⟨subset_rfl, by omega⟩)
    (hD.mono (X := (OrderedLayer.coatomD, 2)) ⟨subset_rfl, by omega⟩)
    (d₁ := d₁) (s := sC) (by rw [← CellScheme.gradedIndex_snd, hd₁]; decide) ?_ ?_
    (by rw [← CellScheme.gradedIndex_snd, hsC]) ?_
  · rw [hv₁]; exact gridPoint_ne_bot 1 0
  · rw [hv₁]; simp [gridPoint]
  · rw [hvs]; exact gridPoint_ne_bot 2 0

/-- A low entry at `seedL` (`TowerProfile.lowEntryTwo_of_TL`). -/
theorem lowEntryTwo_seedL : LowEntryTwo (seedL α) :=
  lowEntryTwo_of_TL rfl rfl

/-- **Route (b) is refuted at `seedL`**: separating servers at the grade `2` fail there, at the
support labelling of the field row of the low entry and the cap `4`
(`TowerProfile.not_separatingServersTwo_of_lowEntry`). -/
theorem not_separatingServersTwo_seedL : ¬ SeparatingServersTwo (seedL α) :=
  not_separatingServersTwo_of_lowEntry lowEntryTwo_seedL

end TowerProfile

end VaughtConjecture
