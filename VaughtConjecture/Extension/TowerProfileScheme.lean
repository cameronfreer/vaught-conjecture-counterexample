/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SectionInterface

/-!
# A layer of rank-normalized profiles over the tower at the grade two

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the tower `T 2` with a layer of profiles at the grade `3`, and its capped lifts at the grade `3`;
the first instance of the levels of `VaughtConjecture.Extension.ProfileTower`, kept as a test).

Let `I` be a seed on five points.  The **profile layer over the tower** (`TowerProfile.scheme I`)
is `T 2 = I.tower 2` followed by one cell of full scope and grade `3` for each profile of the
rank-normalized catalogue `RankProfile.rankCat I 3` (`Scheme.appendFullCells`).  The row of the
cell of a profile `P` is its **field labelling** (`TowerProfile.fieldLab`): the tower section
`SectionInterface.towerSectionOp I P` at the cells of `T 2` (so `P` at the old cells), and at the
cell of a profile `P'` the agreement height of `P` and `P'` in `Label.grid 3 (2 N + 2)`.

* **The field labelling of a profile of the catalogue is lawful below `(univ, 3)`**
  (`TowerProfile.isLawfulBelow_fieldLab`): below `(univ, 2)` by the lawfulness of the section,
  below the coatoms at the grade `3` by the lawfulness of the profile, and at a cell of the layer
  by the capped agreement of the sections at the agreement heights in `Label.grid 3`
  (`SectionInterface.towerSectionOp_isCapAgreeingAt`) and the ultrametric inequality.  The
  scheme is consistent, coded and well formed (`TowerProfile.isConsistent_scheme`,
  `TowerProfile.isCoded_scheme`, `TowerProfile.isWellFormed_scheme`); the rows of the cells at
  `(univ, 3)` are short at `3` and never the formal top (`TowerProfile.row_natAdd_props`).
* **Extension from the boundary** (`TowerProfile.exists_extension`,
  `TowerProfile.exists_extension_bot`).  At a cap `h` self-visible and short at `3`, a labelling
  `w` lawful below both coatoms at the grade `3` and agreeing with a profile `P` capped at `h` at
  the old cells extends by the field labelling of the orbit code `Q` of its old labels, read by
  their orbit decoder at `h`.  The decoder reads the values of the section of `Q` literally below
  `h` because they are readable for `Q` (`Label.min_orbitDecoder_eq_of_isReadableAt`,
  `Seed.isReadable_towerSection`); the capped agreement with `P` is that of the sections.  The
  extension depends on the prescription and the cap, as the extension from the boundary allows;
  the rows depend on the profiles only.
* **The lifts** (every seed on five points; compiled in this repository (theorem named)): at the
  grades `j' ≤ 2` from either coatom (`TowerProfile.cappedLift_le_two`), the invariant of the
  tower at the grade `2` from `2FL(1)`, through the source prefix `T 2`
  (`TowerProfile.cappedLift_scheme_iff`); and **at the grade `3` from either coatom**
  (`TowerProfile.cappedLift_three`), by the one-grade lift
  `CellScheme.Rows.cappedLift_of_boundaries_short` with the lift at the grade `2` above, the
  boundary lifts of the amalgam (`TowerProfile.cappedLift_old`) and the serving cells at
  `(univ, 3)`.  The grade-`2` lift is a lift below `(univ, 2)`, where the scheme is `T 2`; the
  compatibility of the profiles with the lower layers enters only through the section operator.
* **`seedL`** (`TowerProfile.cappedLift_three_seedL`): the scheme lifts at the grade `3` from both
  coatoms, while the tower's own layer at the grade `3` does not.

The scheme has no cell at `(univ, 4)`; the canonical field layer at the grade `4` over it, and
the completion below the full grade, are in the module
`VaughtConjecture.Extension.TowerProfileCompletion`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.TowerProfile

open Finset Label CellScheme
open ProfileCatalogue (Profile)
open RankProfile (rankCat mem_rankCat gridBound mem_codeGrid_of_mem_rankCat)
open SectionInterface (towerSectionOp towerSectionOp_isLawful towerSectionOp_isCapAgreeingAt
  towerSectionOp_isLiteral)

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- The number of cells of the layer: the size of the catalogue. -/
noncomputable abbrev mult : ℕ := (rankCat I 3).card

/-- The profile of the cell `i` of the layer. -/
noncomputable def entry (i : Fin (mult I)) : Profile I := ((rankCat I 3).equivFin.symm i).1

/-- The grid of the agreement heights of the layer. -/
noncomputable abbrev cutGrid : Finset Label.{u} := grid 3 (gridBound I)

/-- The **field labelling** of a profile `R`: its tower section at the cells of `T 2`, and at the
cell of a profile `P'` of the layer the agreement height of `R` and `P'`. -/
noncomputable def fieldLab (R : Profile I) : Fin ((I.tower 2).card + mult I) → Label.{u} :=
  Fin.append (towerSectionOp I R) fun j ↦ agreementHeight (cutGrid I) R (entry I j)

/-- **The profile layer over `T 2`**: `T 2` followed by one cell at `(univ, 3)` per profile of the
catalogue, whose row is the field labelling of its profile. -/
noncomputable abbrev scheme : Scheme.{u} 5 :=
  (I.tower 2).appendFullCells 3 (mult I) (fun i ↦ fieldLab I (entry I i))
    (I.not_univ_succ_le_tower 2)

variable {I}

/-- The profile of a cell of the layer is in the catalogue. -/
theorem entry_mem (i : Fin (mult I)) : entry I i ∈ rankCat I 3 :=
  ((rankCat I 3).equivFin.symm i).2

/-- Every profile of the catalogue is the profile of a cell of the layer. -/
theorem exists_entry_eq {R : Profile I} (hR : R ∈ rankCat I 3) : ∃ i, entry I i = R :=
  ⟨(rankCat I 3).equivFin ⟨R, hR⟩, by simp [entry]⟩

/-- The field labelling at a cell of `T 2`. -/
@[simp] theorem fieldLab_castAdd (R : Profile I) (e : Fin (I.tower 2).card) :
    fieldLab I R (Fin.castAdd _ e) = towerSectionOp I R e :=
  Fin.append_left _ _ e

/-- The field labelling at a cell of the layer. -/
@[simp] theorem fieldLab_natAdd (R : Profile I) (j : Fin (mult I)) :
    fieldLab I R (Fin.natAdd _ j) = agreementHeight (cutGrid I) R (entry I j) :=
  Fin.append_right _ _ j

/-- The values of the field labelling of a profile of the catalogue lie in the code grid
`codeGrid 3 (2 N + 2)`. -/
theorem fieldLab_mem_codeGrid {R : Profile I} (hR : R ∈ rankCat I 3)
    (z : Fin ((I.tower 2).card + mult I)) : fieldLab I R z ∈ codeGrid 3 (gridBound I) := by
  induction z using Fin.addCases with
  | left e =>
    rw [fieldLab_castAdd]
    exact Seed.towerSection_mem_codeGrid 2 (by omega) (fun d ↦ mem_codeGrid_of_mem_rankCat hR d) e
  | right j =>
    rw [fieldLab_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid 3 _) _ _).1

/-- The values of the field labelling lie at most at the ceiling `ω * (2 N + 2) + 3`. -/
theorem fieldLab_le_ceiling {R : Profile I} (hR : R ∈ rankCat I 3)
    (z : Fin ((I.tower 2).card + mult I)) : fieldLab I R z ≤ gridPoint 3 (gridBound I) :=
  le_gridPoint_of_mem_codeGrid (fieldLab_mem_codeGrid hR z)

/-- A profile has the ceiling as agreement height with itself. -/
theorem agreementHeight_self_ceiling (R : Profile I) :
    agreementHeight (cutGrid I) R R = gridPoint 3 (gridBound I) :=
  agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx) R

/-- The cells of `T 2` lie above no pair `(univ, 3)`. -/
private theorem not_univ_three_le (e : Fin (I.tower 2).card) :
    ¬ ((univ : Finset (Fin 5)), 3) ≤ (I.tower 2).toCellScheme.gradedIndex e :=
  I.not_univ_succ_le_tower 2 e

/-- **Lawfulness below a pair not above `(univ, 3)`** is lawfulness in `T 2`. -/
theorem isLawfulBelow_scheme_iff {X : Finset (Fin 5) × ℕ} (hX : ¬ ((univ : Finset (Fin 5)), 3) ≤ X)
    {v : Fin ((I.tower 2).card + mult I) → Label.{u}} :
    (scheme I).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      (I.tower 2).rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd _ d)) :=
  Scheme.isLawfulBelow_appendFullCells_iff hX

/-- A cell of `T 2` below `(univ, 3)` lies below `(univ, 2)`, or is an old cell below a coatom at
the grade `3`. -/
private theorem mem_below_cases {e : Fin (I.tower 2).card}
    (he : (I.tower 2).toCellScheme.grade e ≤ 3) :
    e ∈ (I.tower 2).toCellScheme.below ((univ : Finset (Fin 5)), 2) ∨
      e ∈ (I.tower 2).toCellScheme.below (OrderedLayer.coatomC, 3) ∨
      e ∈ (I.tower 2).toCellScheme.below (OrderedLayer.coatomD, 3) := by
  by_cases he2 : (I.tower 2).toCellScheme.grade e ≤ 2
  · exact .inl ⟨subset_univ _, he2⟩
  obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 2 e ((I.tower_grade_le_or 2 e).resolve_left he2)
  have hd : I.amalgam.toCellScheme.grade d ≤ 3 := (I.grade_towerEmbed 2 d).symm.trans_le he
  rcases I.scope_subset_or (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp)
    (by decide) d with h | h
  · exact .inr (.inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))
  · exact .inr (.inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩))

/-- **The field labelling of a profile of the catalogue is lawful below `(univ, 3)`.** -/
theorem isLawfulBelow_fieldLab {R : Profile I} (hR : R ∈ rankCat I 3) :
    (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ fieldLab I R z := by
  classical
  obtain ⟨⟨hC, hD⟩, -⟩ := mem_rankCat.mp hR
  -- The three pairs below which the cells of `T 2` lie.
  have h2 : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 2) fun z ↦ fieldLab I R z := by
    refine (isLawfulBelow_scheme_iff (by rintro ⟨-, h⟩; omega)).mpr ?_
    simpa only [fieldLab_castAdd] using towerSectionOp_isLawful R hR
  have hcoat (X : Finset (Fin 5)) (hX : X ≠ univ)
      (hRX : I.amalgam.rows.IsLawfulBelow (X, 3) fun d ↦ R d) :
      (scheme I).rows.IsLawfulBelow (X, 3) fun z ↦ fieldLab I R z := by
    refine (isLawfulBelow_scheme_iff fun h ↦ hX (univ_subset_iff.mp h.1)).mpr ?_
    simp only [fieldLab_castAdd]
    rw [I.isLawfulBelow_tower_iff hX]
    exact (Rows.isLawfulBelow_congr (w' := fun d ↦ towerSectionOp I R (I.towerEmbed 2 d))
      fun d _ ↦ (towerSectionOp_isLiteral R d).symm).mp hRX
  have h3C := hcoat _ (by decide) hC
  have h3D := hcoat _ (by decide) hD
  obtain ⟨ho2, hl2, ha2⟩ := Rows.isLawfulBelow_iff_forall.mp h2
  obtain ⟨hoC, hlC, haC⟩ := Rows.isLawfulBelow_iff_forall.mp h3C
  obtain ⟨hoD, hlD, haD⟩ := Rows.isLawfulBelow_iff_forall.mp h3D
  -- An old cell below `(univ, 3)` lies below one of the three pairs.
  have hcases {e : Fin (I.tower 2).card}
      (he : Fin.castAdd (mult I) e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
      Fin.castAdd (mult I) e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 2) ∨
        Fin.castAdd (mult I) e ∈ (scheme I).toCellScheme.below (OrderedLayer.coatomC, 3) ∨
        Fin.castAdd (mult I) e ∈ (scheme I).toCellScheme.below (OrderedLayer.coatomD, 3) := by
    have hg : (I.tower 2).toCellScheme.grade e ≤ 3 :=
      (Scheme.appendFullCellsScheme_grade_castAdd (I.tower 2) 3 _ e).symm.trans_le he.2
    simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact mem_below_cases hg
  obtain ⟨i₀, hi₀⟩ := exists_entry_eq hR
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e =>
      rcases hcases hz with h | h | h
      exacts [ho2 _ h, hoC _ h, hoD _ h]
    | right j =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, fieldLab_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid 3 _) _ _).1
  · induction s using Fin.addCases with
    | left e =>
      rcases hcases hs with h | h | h
      exacts [hl2 _ h, hlC _ h, hlD _ h]
    | right j =>
      -- At a cell of the layer: the identity capped at the agreement height.
      set κ := agreementHeight (cutGrid I) R (entry I j) with hκ
      have hκm : κ ∈ cutGrid I := (agreementHeight_spec (bot_mem_grid 3 _) _ _).1
      have hκv : IsSelfVisible 3 κ := isSelfVisible_of_mem_grid hκm
      refine ⟨constStepSuppressor 3 κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : (scheme I).toCellScheme.grade t ≤ 3 := t.2.2.trans_eq
        (congrArg Prod.snd (Scheme.appendFullCellsScheme_gradedIndex_natAdd (I.tower 2) 3 _ j))
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id,
        fieldLab_natAdd]
      obtain ⟨t, -⟩ := t
      -- Beta-reduce the capped target at the cell `t`.
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [fieldLab_castAdd, fieldLab_castAdd]
        exact towerSectionOp_isCapAgreeingAt hκv (isShort_of_mem_grid hκm) R hR (entry I j)
          (entry_mem j) (agreementHeight_spec (bot_mem_grid 3 _) R (entry I j)).2 e
      | right j' =>
        rw [fieldLab_natAdd, fieldLab_natAdd]
        exact agreementHeight_tri (bot_mem_grid 3 _) _ _ _
  · induction t using Fin.addCases with
    | left e =>
      rcases hcases ht with h | h | h
      exacts [ha2 s _ h hst hg, haC s _ h hst hg, haD s _ h hst hg]
    | right j =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [fieldLab_natAdd, hi₀, agreementHeight_self_ceiling]
      exact fieldLab_le_ceiling hR s

/-! ### The cells at `(univ, 3)` and their rows -/

/-- A cell of the scheme of graded index `(univ, 3)` is a cell of the layer. -/
theorem exists_natAdd_eq {u : Fin (scheme I).card}
    (hu : (scheme I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 3)) :
    ∃ i, Fin.natAdd _ i = u := by
  by_cases hlt : (u : ℕ) < (I.tower 2).card
  · refine absurd ?_ (not_univ_three_le ⟨u, hlt⟩)
    rw [← Scheme.appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < (I.tower 2).card + mult I := u.2
    exact ⟨⟨u - (I.tower 2).card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- The row of the cell `i` of the layer, read below `(univ, 3)`, is the field labelling of its
profile. -/
theorem rowBelow_natAdd (i : Fin (mult I))
    (hu : (scheme I).toCellScheme.gradedIndex (Fin.natAdd _ i) = ((univ : Finset (Fin 5)), 3))
    (d : (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
    (scheme I).rows.rowBelow _ hu d = fieldLab I (entry I i) d :=
  Scheme.appendFullCells_row_natAdd i _

omit I in
/-- A row lawful below a pair equal to the graded index of its cell is consistent there. -/
private theorem isLawfulBelow_row_of_rowBelow {n : ℕ} {S : Scheme.{u} n} {u : Fin S.card}
    {Y : Finset (Fin n) × ℕ} (hu : S.toCellScheme.gradedIndex u = Y)
    (h : S.rows.IsLawfulBelow Y (S.rows.rowBelow u hu)) :
    S.rows.IsLawfulBelow (S.toCellScheme.gradedIndex u) (S.rows.row u) := by
  subst hu
  exact h

/-- **The rows of the cells at `(univ, 3)` are consistent, short at `3`, and never the formal
top.** -/
theorem row_natAdd_props (i : Fin (mult I))
    (hu : (scheme I).toCellScheme.gradedIndex (Fin.natAdd _ i) = ((univ : Finset (Fin 5)), 3)) :
    (scheme I).rows.IsLawfulBelow ((scheme I).toCellScheme.gradedIndex (Fin.natAdd _ i))
        ((scheme I).rows.row (Fin.natAdd _ i)) ∧
      (∀ d, IsShort 3 ((scheme I).rows.rowBelow _ hu d)) ∧
      ∀ d, (scheme I).rows.rowBelow _ hu d ≠ ⊤ := by
  refine ⟨?_, fun d ↦ ?_, fun d ↦ ?_⟩
  · have h : (scheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
        ((scheme I).rows.rowBelow _ hu) := by
      convert isLawfulBelow_fieldLab (entry_mem (I := I) i) using 1
      funext d
      exact rowBelow_natAdd i hu d
    exact isLawfulBelow_row_of_rowBelow hu h
  · rw [rowBelow_natAdd]; exact isShort_of_mem_codeGrid (fieldLab_mem_codeGrid (entry_mem i) _)
  · rw [rowBelow_natAdd]; exact ne_top_of_mem_codeGrid (fieldLab_mem_codeGrid (entry_mem i) _)

/-! ### Extension from the boundary -/

/-- The old labels of a labelling of the scheme: its values at the old cells up to the grade `3`,
and those of a profile above. -/
private noncomputable def oldLabels (w : Fin (scheme I).card → Label.{u}) (P : Profile I) :
    Profile I := fun d ↦
  if I.amalgam.toCellScheme.grade d ≤ 3 then w (Fin.castAdd _ (I.towerEmbed 2 d)) else P d

private theorem oldLabels_of_le {w : Fin (scheme I).card → Label.{u}} {P : Profile I}
    {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
    oldLabels w P d = w (Fin.castAdd _ (I.towerEmbed 2 d)) := by
  unfold oldLabels; exact ite_eq_left hd

/-- A labelling lawful below a coatom at the grade `3` in the scheme has old labels lawful below
it in the amalgam. -/
private theorem isLawfulBelow_oldLabels {X : Finset (Fin 5)} (hX : X ≠ univ)
    {w : Fin (scheme I).card → Label.{u}} (P : Profile I)
    (hw : (scheme I).rows.IsLawfulBelow (X, 3) fun z ↦ w z) :
    I.amalgam.rows.IsLawfulBelow (X, 3) fun d ↦ oldLabels w P d := by
  have h1 := (isLawfulBelow_scheme_iff fun h ↦ hX (univ_subset_iff.mp h.1)).mp hw
  have h2 := (I.isLawfulBelow_tower_iff (X := (X, 3)) hX
    (g := fun e ↦ w (Fin.castAdd (mult I) e))).mp h1
  exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (X, 3))
    fun d hd ↦ (oldLabels_of_le hd.2).symm).mp h2

/-- A cell of scope other than the ground set below `(univ, 3)` is an old cell of the amalgam of
grade at most `3`. -/
private theorem exists_old {z : Fin (scheme I).card}
    (hz : z ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3))
    (hne : (scheme I).toCellScheme.scope z ≠ univ) :
    ∃ d, I.amalgam.toCellScheme.grade d ≤ 3 ∧ z = Fin.castAdd _ (I.towerEmbed 2 d) := by
  induction z using Fin.addCases with
  | right j => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j) hne
  | left e =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hne
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 2 e hne
    refine ⟨d, ?_, rfl⟩
    have := hz.2
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, I.gradedIndex_towerEmbed] at this
    exact this

/-- The field labelling of a profile at an old cell is the profile. -/
theorem fieldLab_old (R : Profile I) (d : Fin I.amalgam.card) :
    fieldLab I R (Fin.castAdd _ (I.towerEmbed 2 d)) = R d := by
  rw [fieldLab_castAdd]; exact towerSectionOp_isLiteral R d

/-- **Extension from the boundary along the field labelling of a profile, at a positive cap.**
Let `P` be a profile of the catalogue, `h` a cap self-visible and short at `3` other than `⊥`, and
`w` a labelling of the scheme lawful below the two coatoms at the grade `3` that agrees with `P`
capped at `h` at the old cells of grade at most `3`.  Then some labelling lawful below `(univ, 3)`
equals `w` at the cells of scope other than the ground set and agrees with the field labelling of
`P` capped at `h` at every cell below `(univ, 3)`.  It is the field labelling of the orbit code
`Q` of the old labels of `w`, read by their orbit decoder at `h`: lawful by transport, literal at
the old cells (`Label.orbitDecoder_orbitCode`), and capped at `h` at the other cells because their
values are readable for `Q` (`Label.min_orbitDecoder_eq_of_isReadableAt`,
`Seed.isReadable_towerSection`) and agree with those of `P` capped at `h` (capped agreement of the
sections, relative room of the orbit code). -/
theorem exists_extension {P : Profile I} (hP : P ∈ rankCat I 3) {h : Label.{u}}
    (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) (hb : h ≠ ⊥)
    {w : Fin (scheme I).card → Label.{u}}
    (hwC : (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomC, 3) fun z ↦ w z)
    (hwD : (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomD, 3) fun z ↦ w z)
    (hwP : ∀ d : Fin I.amalgam.card, I.amalgam.toCellScheme.grade d ≤ 3 →
      min (w (Fin.castAdd _ (I.towerEmbed 2 d))) h = min (P d) h) :
    ∃ r : (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 3) r ∧
      (∀ z, (scheme I).toCellScheme.scope z.1 ≠ univ → r z = w z) ∧
      ∀ z, min (r z) h = min (fieldLab I P z) h := by
  classical
  set W := oldLabels w P with hW
  have hWP (d : Fin I.amalgam.card) : min (W d) h = min (P d) h := by
    by_cases hd : I.amalgam.toCellScheme.grade d ≤ 3
    · rw [hW, oldLabels_of_le hd]; exact hwP d hd
    · rw [hW, oldLabels, ite_eq_right hd]
  set Q : Profile I := orbitCode 3 W with hQ
  have hPo := (mem_rankCat.mp hP).2
  have hQP (d : Fin I.amalgam.card) : min (Q d) h = min (P d) h :=
    min_orbitCode_eq hh hs hPo hWP d
  have hQW (d : Fin I.amalgam.card) : min (Q d) h = min (W d) h := (hQP d).trans (hWP d).symm
  have hQ3 : Q ∈ rankCat I 3 := mem_rankCat.mpr
    ⟨⟨(isLawfulBelow_oldLabels (by decide) P hwC).orbitCode fun d ↦ d.2.2,
      (isLawfulBelow_oldLabels (by decide) P hwD).orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩
  have hQB (d : Fin I.amalgam.card) : Q d ∈ codeGrid 3 (gridBound I) :=
    mem_codeGrid_of_mem_rankCat hQ3 d
  -- The capped agreement of the decoded field labelling of `Q` with that of `P`.
  have hag (z : (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)) :
      min (orbitDecoder 3 W h (fieldLab I Q z)) h = min (fieldLab I P z) h := by
    obtain ⟨z, -⟩ := z
    induction z using Fin.addCases with
    | left e =>
      rw [min_orbitDecoder_eq_of_isReadableAt hh hQW (by
          rw [fieldLab_castAdd]
          exact Seed.isReadable_towerSection (B := gridBound I) orbitCode_orbitCode hQB 2 le_rfl e),
        fieldLab_castAdd, fieldLab_castAdd]
      exact towerSectionOp_isCapAgreeingAt hh hs Q hQ3 P hP hQP e
    | right j =>
      rw [fieldLab_natAdd, fieldLab_natAdd,
        min_orbitDecoder_eq (isSelfVisible_of_mem_grid (agreementHeight_spec
          (bot_mem_grid 3 _) _ _).1)]
      exact min_agreementHeight_eq_of_isShort hh hs
        (fun d ↦ ⟨hQB d, mem_codeGrid_of_mem_rankCat hP d⟩) hQP _
  refine ⟨fun z ↦ orbitDecoder 3 W h (fieldLab I Q z),
    (isLawfulBelow_fieldLab hQ3).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder hh hb) (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot hb), fun z hz ↦ ?_,
    hag⟩
  obtain ⟨d, hd, hdz⟩ := exists_old z.2 hz
  -- The decoded field labelling at the old cell `z`.
  change orbitDecoder 3 W h (fieldLab I Q z.1) = w z.1
  rw [hdz, fieldLab_old, orbitDecoder_orbitCode hQW d, hW, oldLabels_of_le hd]

/-- **Extension from the boundary at the cap `⊥`**: every labelling lawful below the two coatoms
at the grade `3` extends, unchanged at the cells of scope other than the ground set, to a labelling
lawful below `(univ, 3)`: the field labelling of the orbit code of its old labels (bottom above
the grade `3`), read by their orbit decoder at the least grid point `3`. -/
theorem exists_extension_bot {w : Fin (scheme I).card → Label.{u}}
    (hwC : (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomC, 3) fun z ↦ w z)
    (hwD : (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomD, 3) fun z ↦ w z) :
    ∃ r : (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 3) r ∧
      ∀ z, (scheme I).toCellScheme.scope z.1 ≠ univ → r z = w z := by
  set W := oldLabels w (fun _ ↦ ⊥) with hW
  set Q : Profile I := orbitCode 3 W with hQ
  have hQ3 : Q ∈ rankCat I 3 := mem_rankCat.mpr ⟨⟨(isLawfulBelow_oldLabels (by decide) _
    hwC).orbitCode fun d ↦ d.2.2, (isLawfulBelow_oldLabels (by decide) _ hwD).orbitCode
    fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩
  have hQW (d : Fin I.amalgam.card) : min (Q d) (gridPoint 3 0) = min (W d) (gridPoint 3 0) :=
    min_orbitCode_gridPoint_zero d
  refine ⟨fun z ↦ orbitDecoder 3 W (gridPoint 3 0) (fieldLab I Q z),
    (isLawfulBelow_fieldLab hQ3).map_of_apply_eq_bot (fun z ↦ z.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint 3 0) (gridPoint_ne_bot 3 0))
      (fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot 3 0)), fun z hz ↦ ?_⟩
  obtain ⟨d, hd, hdz⟩ := exists_old z.2 hz
  -- The decoded field labelling at the old cell `z`.
  change orbitDecoder 3 W (gridPoint 3 0) (fieldLab I Q z.1) = w z.1
  rw [hdz, fieldLab_old, orbitDecoder_orbitCode hQW d, hW, oldLabels_of_le hd]

/-! ### The serving rows extend from the boundary -/

open RankProfile (IsCoatomPair)

/-- The two coatoms, in either order, as `C` and `D`. -/
theorem lawful_of_isCoatomPair {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    {w : Fin (scheme I).card → Label.{u}}
    (hwU : (scheme I).rows.IsLawfulBelow U fun z ↦ w z)
    (hwV : (scheme I).rows.IsLawfulBelow V fun z ↦ w z) :
    (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomC, 3) (fun z ↦ w z) ∧
      (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomD, 3) fun z ↦ w z := by
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [⟨hwU, hwV⟩, ⟨hwV, hwU⟩]

/-- An old cell of grade at most `3` lies below one of the coatoms of a pair. -/
theorem mem_of_isCoatomPair {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
    Fin.castAdd (mult I) (I.towerEmbed 2 d) ∈ (scheme I).toCellScheme.below U ∨
      Fin.castAdd (mult I) (I.towerEmbed 2 d) ∈ (scheme I).toCellScheme.below V := by
  have h : Fin.castAdd (mult I) (I.towerEmbed 2 d) ∈
        (scheme I).toCellScheme.below (OrderedLayer.coatomC, 3) ∨
      Fin.castAdd (mult I) (I.towerEmbed 2 d) ∈
        (scheme I).toCellScheme.below (OrderedLayer.coatomD, 3) := by
    simp only [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    rcases I.scope_subset_or (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp)
      (by simp) (by decide) d with h | h
    · exact .inl (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
    · exact .inr (I.towerEmbed_mem_below_iff.mpr ⟨h, hd⟩)
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [h, h.symm]

/-- The cells on the boundary of a pair have scope other than the ground set. -/
theorem scope_ne_of_isCoatomPair {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    {z : Fin (scheme I).card}
    (hz : z ∈ (scheme I).toCellScheme.below U ∨ z ∈ (scheme I).toCellScheme.below V) :
    (scheme I).toCellScheme.scope z ≠ univ := by
  intro h
  have hsub : ∀ X : Finset (Fin 5) × ℕ, z ∈ (scheme I).toCellScheme.below X →
      (univ : Finset (Fin 5)) ⊆ X.1 := fun X hX ↦ h ▸ hX.1
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hz with hz | hz <;>
    exact absurd (hsub _ hz) (by decide)

/-- **Extension from the boundary along a serving row at `(univ, 3)`**, at every cap self-visible
and short at `3` other than `⊥` (`exists_extension`), for either order of the coatoms. -/
theorem extendsFromBoundary_row {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V)
    (i : Fin (mult I))
    (hu : (scheme I).toCellScheme.gradedIndex (Fin.natAdd _ i) = ((univ : Finset (Fin 5)), 3))
    {h : Label.{u}} (hh : IsSelfVisible 3 h) (hs : IsShort 3 h) (hb : ⊥ < h) :
    (scheme I).rows.ExtendsFromBoundary U V ((univ : Finset (Fin 5)), 3) h
      ((scheme I).rows.rowBelow _ hu) := by
  intro w hwU hwV hwS
  obtain ⟨hwC, hwD⟩ := lawful_of_isCoatomPair hUV hwU hwV
  have hwP (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ 3) :
      min (w (Fin.castAdd _ (I.towerEmbed 2 d))) h = min (entry I i d) h := by
    have hm : Fin.castAdd (mult I) (I.towerEmbed 2 d) ∈
        (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) := by
      rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_castAdd,
        I.gradedIndex_towerEmbed]
      exact ⟨subset_univ _, hd⟩
    have h1 := hwS ⟨_, hm⟩ (mem_of_isCoatomPair hUV d hd)
    rwa [rowBelow_natAdd, fieldLab_old] at h1
  obtain ⟨r, hr, hrw, hrc⟩ := exists_extension (entry_mem i) hh hs hb.ne' hwC hwD hwP
  refine ⟨r, hr, fun d hd ↦ hrw d (scope_ne_of_isCoatomPair hUV hd), fun d ↦ ?_⟩
  rw [rowBelow_natAdd]
  exact hrc d

/-- **Extension from the boundary at the cap `⊥`**, for either order of the coatoms. -/
theorem extendsFromBoundary_bot {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V) :
    (scheme I).rows.ExtendsFromBoundary U V ((univ : Finset (Fin 5)), 3) ⊥ fun _ ↦ ⊥ := by
  intro w hwU hwV _
  obtain ⟨hwC, hwD⟩ := lawful_of_isCoatomPair hUV hwU hwV
  obtain ⟨r, hr, hrw⟩ := exists_extension_bot hwC hwD
  exact ⟨r, hr, fun d hd ↦ hrw d (scope_ne_of_isCoatomPair hUV hd), fun _ ↦ by simp⟩

/-! ### The lifts -/

/-- **`T 2` is a source prefix of the scheme** at every pair not above `(univ, 3)`. -/
theorem isSourcePrefix_scheme {Y : Finset (Fin 5) × ℕ}
    (hY : ¬ ((univ : Finset (Fin 5)), 3) ≤ Y) :
    (I.tower 2).toCellScheme.IsSourcePrefix (scheme I).toCellScheme (Fin.castAdd _) Y :=
  ⟨Scheme.isLowerEmbedding_castAdd (S := I.tower 2) 3 (mult I) _ _,
    Scheme.appendFullCellsScheme_scope_castAdd (I.tower 2) 3 (mult I),
    fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below hY hd⟩, rfl⟩⟩

/-- **Lifts below a pair not above `(univ, 3)`** are those of `T 2`. -/
theorem cappedLift_scheme_iff {X Y : Finset (Fin 5) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin 5)), 3) ≤ Y) :
    (scheme I).rows.CappedLift hXY ↔ (I.tower 2).rows.CappedLift hXY := by
  have h := isSourcePrefix_scheme (I := I) hY
  rw [← h.cappedLift_iff hXY le_rfl]
  exact Iff.of_eq (congrArg (fun R : (I.tower 2).toCellScheme.Rows ↦ R.CappedLift hXY)
    Scheme.comap_rows_castAdd)

/-- **The lifts at the grades `j' ≤ 2`**, from either coatom into `(univ, j')`: the invariant of
the tower at the grade `2`, from `2FL(1)` (`Seed.twoFaceLift_one`, `Seed.towerInvariant_succ`),
for every seed on five points.  No profile enters: no cell of the layer lies below `(univ, 2)`. -/
theorem cappedLift_le_two {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) {j' : ℕ}
    (hj' : j' ≤ 2) :
    (scheme I).rows.CappedLift (X := (univ.erase x, j')) (Y := ((univ : Finset (Fin 5)), j'))
      ⟨erase_subset _ _, le_rfl⟩ :=
  (cappedLift_scheme_iff _ (by rintro ⟨-, h⟩; omega)).mpr
    (I.towerInvariant_succ (j := 1) (by omega) I.towerInvariant_one I.twoFaceLift_one x hx j'
      hj')

/-- **The lift at the grade `2`**, from either coatom into `(univ, 2)`: the invariant of the tower
at the grade `2`, from `2FL(1)` (`Seed.twoFaceLift_one`, `Seed.towerInvariant_succ`), for every
seed on five points.  No profile enters: no cell of the layer lies below `(univ, 2)`. -/
theorem cappedLift_two {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
    (scheme I).rows.CappedLift (X := (univ.erase x, 2)) (Y := ((univ : Finset (Fin 5)), 2))
      ⟨erase_subset _ _, le_rfl⟩ :=
  (cappedLift_scheme_iff _ (by rintro ⟨-, h⟩; omega)).mpr
    (I.towerInvariant_succ (j := 1) (by omega) I.towerInvariant_one I.twoFaceLift_one x hx 2
      le_rfl)

/-- The lifts of the amalgam between graded faces off the ground set are lifts of the scheme. -/
theorem cappedLift_old {X Y : Finset (Fin 5) × ℕ}
    (hX : X ∈ I.amalgam.toCellScheme.gradedFaces) (hY : Y ∈ I.amalgam.toCellScheme.gradedFaces)
    (hY1 : Y.1 ≠ univ) (hXY : X ≤ Y) : (scheme I).rows.CappedLift hXY :=
  (cappedLift_scheme_iff hXY fun h ↦ hY1 (univ_subset_iff.mp h.1)).mpr
    ((I.cappedLift_tower_iff hXY hY1).mpr (I.isBountiful hX hY hXY))

/-- **The capped lift at the grade `3`, from either coatom, for every seed on five points**: the
one-grade lift `CellScheme.Rows.cappedLift_of_boundaries_short`, with the lift at the grade `2`
from `2FL(1)` (`cappedLift_two`), the boundary lifts of the amalgam (`cappedLift_old`), the
extension from the boundary at `⊥` (`extendsFromBoundary_bot`), and the serving cells at
`(univ, 3)` (`row_natAdd_props`, `extendsFromBoundary_row`). -/
theorem cappedLift_three {U V : Finset (Fin 5) × ℕ} (hUV : IsCoatomPair U V) :
    (scheme I).rows.CappedLift (X := U) (Y := ((univ : Finset (Fin 5)), 3))
      ⟨subset_univ _, by rcases hUV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact le_rfl⟩ := by
  classical
  have hO : ((OrderedLayer.coatomC ∩ OrderedLayer.coatomD : Finset (Fin 5)), 3) ∈
      I.amalgam.toCellScheme.gradedFaces := ⟨I.inter_coatoms_mem_faces, by omega, by decide⟩
  have hCf : ((OrderedLayer.coatomC : Finset (Fin 5)), 3) ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨OrderedLayer.coatomC_mem_faces I, by omega, by decide⟩
  have hDf : ((OrderedLayer.coatomD : Finset (Fin 5)), 3) ∈ I.amalgam.toCellScheme.gradedFaces :=
    ⟨OrderedLayer.coatomD_mem_faces I, by omega, by decide⟩
  -- A cell at `(univ, 3)`: the profile constantly `⊥`.
  obtain ⟨i₀, -⟩ := exists_entry_eq (RankProfile.bot_mem_rankCat (I := I) 3)
  have hY : ∃ t, (scheme I).toCellScheme.gradedIndex t = ((univ : Finset (Fin 5)), 3) :=
    ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩
  have hrow : ∀ u (hu : (scheme I).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), 3)),
      (scheme I).rows.IsLawfulBelow ((scheme I).toCellScheme.gradedIndex u)
        ((scheme I).rows.row u) ∧
      (∀ d, IsShort 3 ((scheme I).rows.rowBelow u hu d)) ∧
      (∀ d, (scheme I).rows.rowBelow u hu d ≠ ⊤) ∧
      ∀ h, IsSelfVisible 3 h → IsShort 3 h → ⊥ < h →
        (scheme I).rows.ExtendsFromBoundary U V ((univ : Finset (Fin 5)), 3) h
          ((scheme I).rows.rowBelow u hu) := by
    intro u hu
    obtain ⟨i, rfl⟩ := exists_natAdd_eq hu
    obtain ⟨h1, h2, h3⟩ := row_natAdd_props i hu
    exact ⟨h1, h2, h3, fun h hh hs hb ↦ extendsFromBoundary_row hUV i hu hh hs hb⟩
  rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq_tower 2 hCf (by decide)
    exact Rows.cappedLift_of_boundaries_short (j := 2) (U₀ := (OrderedLayer.coatomC, 3))
      (V₀ := (OrderedLayer.coatomD, 3)) (O₀ := (OrderedLayer.coatomC ∩ OrderedLayer.coatomD, 3))
      (U := (OrderedLayer.coatomC, 3)) (V := (OrderedLayer.coatomD, 3))
      (O := (OrderedLayer.coatomC ∩ OrderedLayer.coatomD, 3)) (subset_univ _)
      ⟨Fin.castAdd _ c, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ c).trans hc⟩
      (cappedLift_two (by simp)) le_rfl ⟨inter_subset_left, le_rfl⟩
      ⟨inter_subset_right, le_rfl⟩ ⟨subset_univ _, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      (fun d h1 h2 ↦ ⟨subset_inter h1.1 h2.1, h1.2⟩) (Rows.cappedLift_refl _)
      (cappedLift_old hO hDf (by decide) _) (extendsFromBoundary_bot (.inl ⟨rfl, rfl⟩)) le_rfl
      ⟨inter_subset_left, le_rfl⟩ ⟨inter_subset_right, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h1.1 h2.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_old hO hDf (by decide) _) hY hrow
  · obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq_tower 2 hDf (by decide)
    exact Rows.cappedLift_of_boundaries_short (j := 2) (U₀ := (OrderedLayer.coatomD, 3))
      (V₀ := (OrderedLayer.coatomC, 3)) (O₀ := (OrderedLayer.coatomC ∩ OrderedLayer.coatomD, 3))
      (U := (OrderedLayer.coatomD, 3)) (V := (OrderedLayer.coatomC, 3))
      (O := (OrderedLayer.coatomC ∩ OrderedLayer.coatomD, 3)) (subset_univ _)
      ⟨Fin.castAdd _ c, (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ c).trans hc⟩
      (cappedLift_two (by simp)) le_rfl ⟨inter_subset_right, le_rfl⟩
      ⟨inter_subset_left, le_rfl⟩ ⟨subset_univ _, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      (fun d h1 h2 ↦ ⟨subset_inter h2.1 h1.1, h1.2⟩) (Rows.cappedLift_refl _)
      (cappedLift_old hO hCf (by decide) _) (extendsFromBoundary_bot (.inr ⟨rfl, rfl⟩)) le_rfl
      ⟨inter_subset_right, le_rfl⟩ ⟨inter_subset_left, le_rfl⟩ ⟨subset_univ _, le_rfl⟩
      ⟨subset_univ _, le_rfl⟩ (fun d h1 h2 ↦ ⟨subset_inter h2.1 h1.1, h1.2⟩)
      (Rows.cappedLift_refl _) (cappedLift_old hO hCf (by decide) _) hY hrow

/-! ### Consistency and coding -/

/-- **The scheme is consistent**: the old rows are those of `T 2`, consistent, and the rows of
the layer are lawful below `(univ, 3)` (`row_natAdd_props`). -/
theorem isConsistent_scheme : (scheme I).rows.IsConsistent := by
  intro s
  induction s using Fin.addCases with
  | right i =>
    exact (row_natAdd_props i (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i)).1
  | left s =>
    have hφ := Scheme.isLowerEmbedding_castAdd (S := I.tower 2) 3 (mult I)
      (fun i ↦ fieldLab I (entry I i)) (I.not_univ_succ_le_tower 2)
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [Scheme.comap_rows_castAdd]
    convert (I.isConsistent_tower 2) s using 1
    funext t
    exact congrArg (fun R : (I.tower 2).toCellScheme.Rows ↦ R.row s t) Scheme.comap_rows_castAdd

/-- **The scheme is coded**: `T 2` is, and the rows of the layer take values in the code grid. -/
theorem isCoded_scheme : (scheme I).IsCoded :=
  Scheme.isCoded_appendFullCells (I.isCoded_tower 2) fun i d ↦
    lt_omega0_sq_of_mem_codeGrid (fieldLab_mem_codeGrid (entry_mem i) d)

/-- **The scheme is well formed**: `T 2` is, and `(univ, 3)` is a graded face. -/
theorem isWellFormed_scheme : (scheme I).IsWellFormed :=
  Scheme.isWellFormed_appendFullCells (I.isWellFormed_tower 2 (by omega)) (by omega) (by omega)

/-! ### `seedL` -/

/-- **The test at `seedL`**: the profile layer over `T 2` lifts capped at the grade `3` from both
coatoms (`cappedLift_three`), while the tower's own layer at the grade `3` does not
(`TwoFaceLiftExistsCounterexample.not_towerInvariant_three_seedL`): the lift is not that of the
refuted step of the tower. -/
theorem cappedLift_three_seedL (α : Ordinal.{u}) :
    (∀ U V (hUV : IsCoatomPair U V),
      (scheme (TwoFaceLiftExistsCounterexample.seedL α)).rows.CappedLift (X := U)
        (Y := ((univ : Finset (Fin 5)), 3))
        ⟨subset_univ _, by rcases hUV with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact le_rfl⟩) ∧
      ¬ (TwoFaceLiftExistsCounterexample.seedL α).TowerInvariant 3 :=
  ⟨fun _ _ hUV ↦ cappedLift_three hUV,
    TwoFaceLiftExistsCounterexample.not_towerInvariant_three_seedL α⟩

end VaughtConjecture.TowerProfile
