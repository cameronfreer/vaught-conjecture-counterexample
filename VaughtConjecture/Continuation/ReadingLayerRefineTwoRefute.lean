/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ReadingLayerRefineTwoSeedL

/-!
# The refining server at the grade `2` fails at `seedL`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The statement `TowerProfile.RefiningServerTwo` ("a refining server exists at the grade `2`") is
refuted at `seedL` (`TowerProfile.not_refiningServerTwo_seedL`), and at every seed of the coatom
types `TL` and `T5` (`TowerProfile.not_refiningServerTwo_of_TL`).  The state is that of
`TowerProfile.exists_frozen_of_entry`: `e` the support of the field row of the low entry (the orbit
code of the tower section of `(1, 2, 1, 2, ⊥)`), the cap `4`, `V = 4`.  The target `q` is the
shift by `ω` of the tower section of `(1, 2, 2, 2, ⊥)`.  Availability from the cell
`({0, 1, 2, 3}, 2)` needs a cell of graded index `(univ, 2)` at least `ω + 2`; every such cell
agrees with the low entry capped at `2`, so its entry codes `({3}, 1)` and `({4}, 1)` alike, and
locality there reads them alike, against `q = ω + 1` and `ω + 2` there
(`TowerProfile.not_refiningServerTwo_of_split`; the collision of
`SectionInterface.not_isCapAgreeingAt_of_collision` at the layer of grade `2`).

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

/-- **The refining server at the grade `2` fails at a split low entry.**  Let the entry `i` code
two cells `d₁`, `d₂` of one grade alike, below `2` and not by `⊥`, and let `q`, lawful below
`(univ, 2)` with the `⊥`-pattern of the entry and at least `4` on its support, read `d₁` strictly
below `d₂` and below a cell `s` of grade `2`.  At the support labelling `e` of the field row of
the entry (`TowerProfile.exists_frozen_of_entry`), the cap `4` and `V = 4`, a refining labelling
`w` has a cell of graded index `(univ, 2)` at least `q s` (availability from `s`); it is at least
`4` in `e`, so its entry agrees with `i` capped at `2` and codes `d₁` and `d₂` alike; locality there
reads `d₁` and `d₂` alike capped at it (`Scheme.min_eq_of_catalogueEntry_eq`), against
`q d₁ < q d₂`. -/
theorem not_refiningServerTwo_of_split {i : Fin ((I.tower 1).catalogue 2).card}
    {d₁ d₂ s : Fin (I.tower 1).card} (hd₁ : (I.tower 1).toCellScheme.grade d₁ ≤ 2)
    (hg : (I.tower 1).toCellScheme.grade d₁ = (I.tower 1).toCellScheme.grade d₂)
    (hb₁ : (I.tower 1).catalogueEntry 2 i d₁ ≠ ⊥)
    (hb₁2 : (I.tower 1).catalogueEntry 2 i d₁ < (((2 : Ordinal.{u})) : Label.{u}))
    (hb₁₂ : (I.tower 1).catalogueEntry 2 i d₁ = (I.tower 1).catalogueEntry 2 i d₂)
    (hs : (I.tower 1).toCellScheme.grade s = 2) {q : Fin (I.tower 1).card → Label.{u}}
    (hq : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun d ↦ q d.1)
    (hqb : ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 →
      (q d = ⊥ ↔ (I.tower 1).catalogueEntry 2 i d = ⊥))
    (hq4 : ∀ d, (I.tower 1).toCellScheme.grade d ≤ 2 →
      (I.tower 1).catalogueEntry 2 i d ≠ ⊥ → 4 ≤ q d)
    (hq12 : q d₁ < q d₂) (hqs : q d₁ < q s) : ¬ RefiningServerTwo I := by
  intro hR
  obtain ⟨e, he, heone, hagree, -, -⟩ := exists_frozen_of_entry hd₁ hb₁ hb₁2
  have h4 : IsSelfVisible 4 (4 : Label.{u}) := (isSelfVisible_ofNat 4).mpr le_rfl
  have hbs : (I.tower 1).catalogueEntry 2 i s ≠ ⊥ := fun h ↦ by
    have := (hqb s hs.le).mpr h
    rw [this] at hqs
    exact absurd hqs (not_lt_bot)
  have hqe (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2) :
      min (q d) 4 = min (e (oneCell I d)) 4 := by
    rw [heone]
    by_cases hbd : (I.tower 1).catalogueEntry 2 i d = ⊥
    · rw [hbd, show supportMap (⊥ : Label.{u}) = ⊥ from ite_eq_left rfl, (hqb d hd).mpr hbd]
    · rw [supportMap_of_ne_bot hbd, min_eq_right (hq4 d hd hbd), min_eq_right le_top]
  obtain ⟨w, hw, hwq, hwcap, -⟩ := hR e he 4 h4 (WithBot.bot_lt_coe _) 4 (h4.mono (by decide))
    le_rfl q hq hqe (fun _ _ h ↦ h) ⟨s, hs, by
      rw [heone, supportMap_of_ne_bot hbs]
      exact le_top⟩
  have hw₂ := isLawfulBelow_two_of_scheme hw
  obtain ⟨-, -, havail⟩ :=
    CellScheme.Rows.isLawfulBelow_iff_forall (w := fun y ↦ w (twoCell I y)) |>.mp hw₂
  have hsc : (I.tower 2).toCellScheme.scope (Fin.natAdd _ i) = univ :=
    Scheme.appendFullCellsScheme_scope_natAdd (I.tower 1) 2 _ i
  have hgs : (I.tower 2).toCellScheme.grade (Fin.castAdd _ s) =
      (I.tower 2).toCellScheme.grade (Fin.natAdd _ i) :=
    (Scheme.appendFullCellsScheme_grade_castAdd (I.tower 1) 2 _ s).trans
      (hs.trans (Scheme.appendFullCellsScheme_grade_natAdd (I.tower 1) 2 _ i).symm)
  obtain ⟨u, hu, hsu⟩ := havail (Fin.castAdd _ s) (Fin.natAdd _ i)
    (Scheme.natAdd_mem_below (hS := I.not_univ_succ_le_tower 1) i)
    (by rw [hsc]; exact subset_univ _) hgs
  have hu' : (I.tower 2).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 2) :=
    hu.trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 1) 2 _ i)
  obtain ⟨j, rfl⟩ := Scheme.exists_natAdd_eq (hS := I.not_univ_succ_le_tower 1) hu'
  have hqsW : q s ≤ w (twoCell I (Fin.natAdd _ j)) := (hwq s hs.le).symm.trans_le hsu
  have hmem : twoCell I (Fin.natAdd _ j) ∈
      (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2) := by
    rw [CellScheme.mem_below]
    exact (gradedIndex_twoCell (I := I) (Fin.natAdd _ j)).trans_le
      (Scheme.natAdd_mem_below (hS := I.not_univ_succ_le_tower 1) j)
  have h4W : 4 ≤ w (twoCell I (Fin.natAdd _ j)) :=
    (hq4 d₁ hd₁ hb₁).trans (hqs.le.trans hqsW)
  have he4 : 4 ≤ e (twoCell I (Fin.natAdd _ j)) := by
    have := hwcap _ hmem
    rw [min_eq_right h4W] at this
    exact min_eq_right_iff.mp this.symm
  have hag := hagree j he4
  have hj₁ : (I.tower 1).catalogueEntry 2 j d₁ = (I.tower 1).catalogueEntry 2 i d₁ :=
    eq_of_min_eq_of_lt (hag d₁).symm hb₁2
  have hj₂ : (I.tower 1).catalogueEntry 2 j d₂ = (I.tower 1).catalogueEntry 2 i d₂ :=
    eq_of_min_eq_of_lt (hag d₂).symm (hb₁₂ ▸ hb₁2)
  have hcoll := Scheme.min_eq_of_catalogueEntry_eq (S := I.tower 1) (k := 2)
    (hS := I.not_univ_succ_le_tower 1) (w := fun y ↦ w (twoCell I y)) hw₂ j hd₁ hg
    (hj₁.trans (hb₁₂.trans hj₂.symm))
  have hq₁ : w (twoCell I (Fin.castAdd _ d₁)) = q d₁ := hwq d₁ hd₁
  have hq₂ : w (twoCell I (Fin.castAdd _ d₂)) = q d₂ := hwq d₂ (hg ▸ hd₁)
  change min (w (twoCell I (Fin.castAdd _ d₁))) (w (twoCell I (Fin.natAdd _ j))) =
    min (w (twoCell I (Fin.castAdd _ d₂))) (w (twoCell I (Fin.natAdd _ j))) at hcoll
  rw [hq₁, hq₂, min_eq_left (hqs.le.trans hqsW)] at hcoll
  exact (lt_min hq12 (hqs.trans_le hqsW)).ne hcoll

/-- The shift by `ω` is a witness at `2`. -/
theorem isWitness_shiftL_omega0 : IsWitness (stepSuppressor 2) (shiftL.{u} (ω * 1)) where
  antitone := (IsWitness.id_step 2).antitone
  isSelfVisible := (IsWitness.id_step 2).isSelfVisible
  map_bot := rfl
  monotone := monotone_shiftL _
  visibilityReplace_comm := fun x _ _ _ _ ↦ shiftL_visibilityReplace 1 _ _ x

theorem shiftL_eq_bot_iff {o : Ordinal.{u}} {x : Label.{u}} : shiftL o x = ⊥ ↔ x = ⊥ := by
  induction x using recBotCoeTop with
  | bot => simp
  | top => simp
  | coe a => simp [shiftL_coe]

/-- An agreement height in a grid is `⊥` exactly when the two labellings disagree capped at the
least grid point. -/
theorem agreementHeight_grid_eq_bot_iff {ι : Type*} [Fintype ι] {k B : ℕ}
    {a c : ι → Label.{u}} : agreementHeight (grid k B) a c = ⊥ ↔
      ¬ ∀ d, min (a d) (gridPoint k 0) = min (c d) (gridPoint k 0) := by
  constructor
  · intro h hag
    have := le_agreementHeight (gridPoint_mem_grid (Nat.zero_le B)) hag
    rw [h] at this
    exact gridPoint_ne_bot k 0 (le_bot_iff.mp this)
  · intro hn
    by_contra h0
    obtain ⟨hgG, hgag⟩ := agreementHeight_spec (bot_mem_grid k B) a c
    rcases mem_grid.mp hgG with h | ⟨b, -, hb⟩
    · exact h0 h
    · refine hn fun d ↦ min_eq_min_of_le' (hgag d) ?_
      rw [hb]
      exact (gridPoint_le_gridPoint (k := k)).mpr (Nat.zero_le b)

/-- **The `⊥`-pattern of the tower section at the layer of grade `1`** depends only on the
labelling capped at the least grid point `1`. -/
theorem towerSection_one_eq_bot_iff (B : ℕ) {P Q : Fin I.amalgam.card → Label.{u}}
    (hPQ : ∀ x, min (P x) (gridPoint 1 0) = min (Q x) (gridPoint 1 0))
    (d : Fin (I.tower 1).card) :
    I.towerSection B 1 P d = ⊥ ↔ I.towerSection B 1 Q d = ⊥ := by
  have hb (x : Fin I.amalgam.card) : P x = ⊥ ↔ Q x = ⊥ := by
    have hg := gridPoint_ne_bot.{u} 1 0
    constructor
    · intro h
      have := hPQ x
      rw [h, min_eq_left bot_le] at this
      exact (min_eq_bot.mp this.symm).resolve_right hg
    · intro h
      have := hPQ x
      rw [h, min_eq_left bot_le] at this
      exact (min_eq_bot.mp this).resolve_right hg
  change Fin ((I.tower 0).card + ((I.tower 0).catalogue 1).card) at d
  induction d using Fin.addCases with
  | left x =>
    rw [Seed.towerSection_castAdd, Seed.towerSection_castAdd]
    exact hb x
  | right i =>
    rw [Seed.towerSection_natAdd, Seed.towerSection_natAdd]
    unfold Seed.layerSection
    have hup {w : Fin (I.tower 0).card → Label.{u}} {x : Label.{u}} :
        upperDecoder 1 B w x = ⊥ ↔ x = ⊥ :=
      ⟨eq_bot_of_upperDecoder_eq_bot, fun h ↦ by rw [h]; exact upperDecoder_bot⟩
    rw [hup, hup, agreementHeight_grid_eq_bot_iff, agreementHeight_grid_eq_bot_iff]
    have hA (y : Fin (I.tower 0).card) :
        min (orbitCode 1 (I.layerSplice 0 (I.towerSection B 0 P)) y) (gridPoint 1 0) =
          min (orbitCode 1 (I.layerSplice 0 (I.towerSection B 0 Q)) y) (gridPoint 1 0) := by
      rw [min_orbitCode_gridPoint_zero, min_orbitCode_gridPoint_zero]
      unfold Seed.layerSplice CellScheme.splice
      split_ifs
      · exact hPQ y
      · rfl
    simp only [hA]

open TwoFaceLiftExistsCounterexample (TL seedL)
open CaseSplitCounterexample (T5 tripleKind)
open ProfileCatalogue (tripleProfile tripleProfile_apply tripleLabelling_of_kind exists_test_cells)

/-- **`RefiningServerTwo` fails at every seed of the coatom types `TL` and `T5`.**  The low entry
is the orbit code at `2` of the tower section of `P₁ = (1, 2, 1, 2, ⊥)`; it codes the cells
`({3}, 1)` and `({4}, 1)` both at `1`.  The labelling `q` is the shift by `ω` of the tower section
of `Q₁ = (1, 2, 2, 2, ⊥)`: it has the `⊥`-pattern of the entry (the two profiles agree capped at
`1`, `TowerProfile.towerSection_one_eq_bot_iff`) and reads `({3}, 1)` at `ω + 1` strictly below
`({4}, 1)` and `({0, 1, 2, 3}, 2)` at `ω + 2` (`TowerProfile.not_refiningServerTwo_of_split`). -/
theorem not_refiningServerTwo_of_TL (hIL : I.left = TL α) (hIR : I.right = T5 α) :
    ¬ RefiningServerTwo I := by
  classical
  set g1 := gridPoint.{u} 1 0 with hg1
  set g2 := gridPoint.{u} 2 0 with hg2
  have hP := SectionInterface.tripleProfile_mem_rankCat (I := I) hIL hIR (.inl rfl) rfl
    (.inl rfl) rfl
  have hQ := SectionInterface.tripleProfile_mem_rankCat (I := I) hIL hIR (.inl rfl) rfl
    (.inr rfl) rfl
  set P := tripleProfile I g1 g2 g1 g2 ⊥ with hPdef
  set Q := tripleProfile I g1 g2 g2 g2 ⊥ with hQdef
  obtain ⟨⟨hPC, hPD⟩, -⟩ := RankProfile.mem_rankCat.mp hP
  obtain ⟨⟨hQC, hQD⟩, -⟩ := RankProfile.mem_rankCat.mp hQ
  have hcov := I.scope_subset_or (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp)
    (by simp) (by decide)
  have hp₁ := isLawfulBelow_towerSection_one_two 0 hcov
    (hPC.mono (X := (OrderedLayer.coatomC, 2)) ⟨subset_rfl, by omega⟩)
    (hPD.mono (X := (OrderedLayer.coatomD, 2)) ⟨subset_rfl, by omega⟩)
  have hp₂ := isLawfulBelow_towerSection_one_two 0 hcov
    (hQC.mono (X := (OrderedLayer.coatomC, 2)) ⟨subset_rfl, by omega⟩)
    (hQD.mono (X := (OrderedLayer.coatomD, 2)) ⟨subset_rfl, by omega⟩)
  set p₁ := I.towerSection 0 1 P with hp₁def
  set p₂ := I.towerSection 0 1 Q with hp₂def
  have hb := Scheme.orbitCode_splice_bot_mem_catalogue (S := I.tower 1) (k := 2) hp₁
  set b := orbitCode 2 ((I.tower 1).toCellScheme.splice 2 (fun _ ↦ ⊥) p₁) with hbdef
  set i := ((I.tower 1).catalogue 2).equivFin ⟨b, hb⟩ with hidef
  have hi : (I.tower 1).catalogueEntry 2 i = b := by
    simp [Scheme.catalogueEntry, hidef]
  obtain ⟨d₁, sC, -, d₂, hd₁, hsC, -, hd₂⟩ := exists_test_cells hIL hIR
  have hk₁ : tripleKind (I.amalgam.toCellScheme.gradedIndex d₁) = 1 := by rw [hd₁]; decide
  have hks : tripleKind (I.amalgam.toCellScheme.gradedIndex sC) = 2 := by rw [hsC]; decide
  have hk₂ : tripleKind (I.amalgam.toCellScheme.gradedIndex d₂) = 3 := by rw [hd₂]; decide
  have hP₁ : P d₁ = g1 := by rw [hPdef, tripleProfile_apply, tripleLabelling_of_kind hk₁]; rfl
  have hP₂ : P d₂ = g1 := by rw [hPdef, tripleProfile_apply, tripleLabelling_of_kind hk₂]; rfl
  have hQ₁ : Q d₁ = g1 := by rw [hQdef, tripleProfile_apply, tripleLabelling_of_kind hk₁]; rfl
  have hQ₂ : Q d₂ = g2 := by rw [hQdef, tripleProfile_apply, tripleLabelling_of_kind hk₂]; rfl
  have hQs : Q sC = g2 := by rw [hQdef, tripleProfile_apply, tripleLabelling_of_kind hks]; rfl
  have hg12 : g1 ≤ g2 := by simp [hg1, hg2, gridPoint]
  have hPQ (x : Fin I.amalgam.card) : min (P x) g1 = min (Q x) g1 := by
    rw [hPdef, hQdef, tripleProfile_apply, tripleProfile_apply]
    generalize hc : tripleKind (I.amalgam.toCellScheme.gradedIndex x) = c
    rw [tripleLabelling_of_kind hc, tripleLabelling_of_kind hc]
    fin_cases c <;> simp [min_eq_right hg12]
  have hgr (x : Fin I.amalgam.card) :
      (I.tower 1).toCellScheme.grade (I.towerEmbed 1 x) = I.amalgam.toCellScheme.grade x :=
    I.grade_towerEmbed 1 x
  have hgd₁ : I.amalgam.toCellScheme.grade d₁ = 1 := by
    rw [← CellScheme.gradedIndex_snd, hd₁]
  have hgd₂ : I.amalgam.toCellScheme.grade d₂ = 1 := by
    rw [← CellScheme.gradedIndex_snd, hd₂]
  have hgs : I.amalgam.toCellScheme.grade sC = 2 := by
    rw [← CellScheme.gradedIndex_snd, hsC]
  have hbb (d : Fin (I.tower 1).card) (hd : (I.tower 1).toCellScheme.grade d ≤ 2) :
      b d = ⊥ ↔ p₁ d = ⊥ := by
    rw [hbdef, orbitCode_eq_bot_iff, CellScheme.splice_of_le hd]
  have h2 : gridPoint.{u} 2 0 = (((2 : Ordinal.{u})) : Label.{u}) := by simp [gridPoint]
  have hbv (x : Fin I.amalgam.card) (hx : I.amalgam.toCellScheme.grade x ≤ 2)
      (hlt : P x < (((2 : Ordinal.{u})) : Label.{u})) : b (I.towerEmbed 1 x) = P x := by
    have := min_orbitCode_gridPoint_zero (k := 2)
      (w := (I.tower 1).toCellScheme.splice 2 (fun _ ↦ ⊥) p₁) (I.towerEmbed 1 x)
    rw [CellScheme.splice_of_le ((hgr x).trans_le hx), hp₁def, Seed.towerSection_towerEmbed,
      h2] at this
    exact eq_of_min_eq_of_lt this.symm hlt
  have hg1lt : g1 < (((2 : Ordinal.{u})) : Label.{u}) := by simp [hg1, gridPoint]
  set q : Fin (I.tower 1).card → Label.{u} := fun d ↦ shiftL (ω * 1) (p₂ d) with hqdef
  have hq : (I.tower 1).rows.IsLawfulBelow (univ, 2) fun d ↦ q d.1 :=
    hp₂.map_of_bot_iff hp₂ (fun d ↦ d.2.2) isWitness_shiftL_omega0 fun _ ↦ shiftL_eq_bot_iff
  have hsh : shiftL (ω * 1) g1 < shiftL (ω * 1) g2 := by
    have h12 : ((1 : ℕ) : Ordinal.{u}) < ((2 : ℕ) : Ordinal.{u}) := by exact_mod_cast (by decide)
    rw [hg1, hg2, gridPoint, gridPoint, shiftL_coe, shiftL_coe]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      ((add_lt_add_iff_left _).mpr ((add_lt_add_iff_left _).mpr h12)))
  have h4ω : (4 : Label.{u}) ≤ (((ω * 1 : Ordinal.{u})) : Label.{u}) := by
    have : (4 : Label.{u}) = (((4 : Ordinal.{u})) : Label.{u}) := rfl
    rw [this, WithBot.coe_le_coe, WithTop.coe_le_coe, mul_one]
    exact (Ordinal.natCast_lt_omega0 4).le
  have hq₁ : q (I.towerEmbed 1 d₁) = shiftL (ω * 1) g1 := by
    change shiftL (ω * 1) (I.towerSection 0 1 Q (I.towerEmbed 1 d₁)) = _
    rw [Seed.towerSection_towerEmbed, hQ₁]
  have hq₂ : q (I.towerEmbed 1 d₂) = shiftL (ω * 1) g2 := by
    change shiftL (ω * 1) (I.towerSection 0 1 Q (I.towerEmbed 1 d₂)) = _
    rw [Seed.towerSection_towerEmbed, hQ₂]
  have hqs : q (I.towerEmbed 1 sC) = shiftL (ω * 1) g2 := by
    change shiftL (ω * 1) (I.towerSection 0 1 Q (I.towerEmbed 1 sC)) = _
    rw [Seed.towerSection_towerEmbed, hQs]
  refine not_refiningServerTwo_of_split (i := i) (d₁ := I.towerEmbed 1 d₁)
    (d₂ := I.towerEmbed 1 d₂) (s := I.towerEmbed 1 sC) (q := q)
    ((hgr d₁).trans_le (by omega)) ((hgr d₁).trans (hgd₁.trans (hgd₂.symm.trans (hgr d₂).symm)))
    ?_ ?_ ?_ ((hgr sC).trans hgs) hq ?_ ?_ (by rw [hq₁, hq₂]; exact hsh)
    (by rw [hq₁, hqs]; exact hsh)
  · rw [hi]
    refine fun h ↦ gridPoint_ne_bot 1 0 ?_
    have := (hbb _ ((hgr d₁).trans_le (by omega))).mp h
    rwa [hp₁def, Seed.towerSection_towerEmbed, hP₁] at this
  · rw [hi, hbv d₁ (by omega) (hP₁ ▸ hg1lt), hP₁]
    exact hg1lt
  · rw [hi, hbv d₁ (by omega) (hP₁ ▸ hg1lt), hbv d₂ (by omega) (hP₂ ▸ hg1lt), hP₁, hP₂]
  · intro d hd
    rw [hi, hbb d hd, hqdef]
    exact shiftL_eq_bot_iff.trans (towerSection_one_eq_bot_iff 0 hPQ d).symm
  · intro d hd hbd
    rw [hi] at hbd
    have h1 : p₁ d ≠ ⊥ := fun h ↦ hbd ((hbb d hd).mpr h)
    have h2' : p₂ d ≠ ⊥ := fun h ↦ h1 ((towerSection_one_eq_bot_iff 0 hPQ d).mpr h)
    exact h4ω.trans (coe_le_shiftL _ h2')

/-- **`RefiningServerTwo` fails at `seedL`** (`TowerProfile.not_refiningServerTwo_of_TL`): the
statement "a refining server exists at the grade `2`" is refuted at that seed. -/
theorem not_refiningServerTwo_seedL : ¬ RefiningServerTwo (seedL α) :=
  not_refiningServerTwo_of_TL rfl rfl

end TowerProfile

end VaughtConjecture
