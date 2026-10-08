/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.MarkedCatalogue
import VaughtConjecture.Extension.TowerProfileCompletion

/-!
# The leaf-and-marked completion below the full grade at `m = 3`

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`), with
the top layer replaced by a leaf-and-marked layer (`VaughtConjecture.Extension.MarkedCatalogue`).

Let `I` be any seed on five points.  A **marked specification** (`TowerProfile.MarkedSpec I`) is a
subset `marks` of the canonical catalogue of the profile layer at the grade `4`, a cap `cap` with
values in the field grid that respects capped agreement (`Scheme.CapRespects`), and the marked
closure (`Scheme.MarkedClosed`).  **The marked top** (`TowerProfile.markedTop I D`) is the tower
`T 2`, the profile layer at the grade `3`, and the leaf-and-marked layer at the grade `4`: one leaf
for every catalogue entry and one marked cell for every member of `marks`.  Compiled in this
repository (theorem named):

* **legality below the full grade** (`TowerProfile.isLegalBelowFullGrade_markedTop`): well formed,
  coded and consistent (`Scheme.isConsistent_sheetLayer`), complete below the grade `5` (a leaf at
  `(univ, 4)`), and bountiful (`TowerProfile.isBountiful_markedTop`): the lifts at the grades
  `j ≤ 3` are those of `TowerProfile.top`, and at the grade `4` the one-grade lift with the
  extension at `⊥` through the leaves (`TowerProfile.extendsFromBoundary_bot_markedTop`) and, at the
  short caps, the extension along every leaf and every marked cell
  (`TowerProfile.extendsFromBoundary_markedTop`): the template is a leaf along a leaf or at a cap
  at most the cap, and a marked cell by marked closure above the cap
  (`Scheme.exists_template_markedLayer`);
* **the completion** (`TowerProfile.markedCompletion I D`, a `CompletionBelowFullGrade I`), with
  the glued labelling extended through the leaves (`TowerProfile.exists_isLawful_markedTop`);
* **the reading of the marked cells** (`TowerProfile.markedTop_mark_reads`): every marked cell
  reads the old cells of grade at most `4` by its member of `marks`, so a predicate on that reading
  holds at every marked cell when it holds on `marks`.

The empty specification (no marked cell, cap `⊥`) exists (`TowerProfile.MarkedSpec.empty`).  What
the marked cells must read, which members they need, and which cap, is the business of the
instance: the marked closure is the only condition the lifts add.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace TowerProfile

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-- A **marked specification** over the profile layer of `I` at the grade `4`: the members of the
catalogue that get a marked cell, and the cap of the cross readings of leaves and marked cells. -/
structure MarkedSpec where
  /-- The members of the catalogue that get a marked cell. -/
  marks : Finset (Fin (scheme I).card → Label.{u})
  /-- The cap of the cross readings. -/
  cap : (Fin (scheme I).card → Label.{u}) → Label.{u}
  /-- The marked members lie in the catalogue. -/
  marks_subset : marks ⊆ (scheme I).catalogue 4
  /-- The caps lie in the field grid. -/
  cap_mem : ∀ e, cap e ∈ (scheme I).fieldGrid 4
  /-- The cap respects capped agreement. -/
  capRespects : Scheme.CapRespects (scheme I) 4 cap
  /-- Marked closure. -/
  closed : Scheme.MarkedClosed (scheme I) 4 marks cap

/-- **The empty specification**: no marked cell, cap `⊥`. -/
noncomputable def MarkedSpec.empty : MarkedSpec I where
  marks := ∅
  cap _ := ⊥
  marks_subset := empty_subset _
  cap_mem _ := bot_mem_grid _ _
  capRespects := Scheme.capRespects_const ⊥
  closed _ he := absurd he (notMem_empty _)

variable {I} (D : MarkedSpec I)

variable (I) in
/-- **The marked top**: the leaf-and-marked layer at the grade `4` over the profile layer. -/
noncomputable abbrev markedTop (D : MarkedSpec I) : Scheme.{u} 5 :=
  (scheme I).markedLayer 4 D.marks D.cap not_univ_four_le

/-- The entries of the marked top lie in the catalogue. -/
theorem markedEntry_mem_spec (i : Fin (((scheme I).catalogue 4).card + D.marks.card)) :
    (scheme I).markedEntry 4 D.marks i ∈ (scheme I).catalogue 4 :=
  Scheme.markedEntry_mem D.marks_subset i

/-! ### Extension from the boundary through the marked top -/

/-- **Extension from the boundary at the grade `4`, at a short positive cap**, along the row of
every new cell of the marked top: the boundary labelling is completed on the profile layer
(`exists_isLawfulBelow_four`) and extended through the new cells by a template
(`Scheme.exists_template_markedLayer`). -/
theorem extendsFromBoundary_markedTop {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y)
    {u : Fin (markedTop I D).card} (hu : (markedTop I D).toCellScheme.gradedIndex u = (univ, 4))
    {h : Label.{u}} (hh : IsSelfVisible 4 h) (hs : IsShort 4 h) (hbot : ⊥ < h) :
    (markedTop I D).rows.ExtendsFromBoundary (univ.erase x, 4) (univ, 3) (univ, 4) h
      ((markedTop I D).rows.rowBelow u hu) :=
  Scheme.extendsFromBoundary_sheetLayer_of_fill (hS := not_univ_four_le) (markedEntry_mem_spec D)
    D.cap_mem D.capRespects
    (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1)) (fun h ↦ absurd h.2 (by simp))
    le_rfl (by simp) hh hs hbot hu
    (fun _ ha _ hwU hwV hag ↦ exists_isLawfulBelow_four hx hy hxy hwU hwV
      (Scheme.mem_catalogue.mp ha).1 hh hag)
    fun j _ _ hg hga ↦ Scheme.exists_template_markedLayer D.marks_subset D.closed hh hs hbot j hg
      hga

/-- **Extension at the cap `⊥` through the marked top** from the two coatoms at the grade `4`, as
`extendsFromBoundary_bot_top`, with a leaf as template. -/
theorem extendsFromBoundary_bot_markedTop {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y) :
    (markedTop I D).rows.ExtendsFromBoundary (univ.erase x, 4) (univ.erase y, 4) (univ, 4) ⊥
      fun _ ↦ ⊥ := by
  classical
  intro w hwx hwy _
  have hU (z : Fin 5) : ¬ ((univ : Finset (Fin 5)), 4) ≤ (univ.erase z, 4) :=
    fun h ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h.1)
  have hw₁ (z : Fin 5)
      (hwz : (markedTop I D).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ w d) :
      (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4)
      (h := not_univ_four_le) (v := w) (hU z)).mp hwz
  have hwC := hw₁ _ hwx
  have hwD := hw₁ _ hwy
  -- The coatoms at `3` in the two orders of `x` and `y`.
  have hcoat3 : (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomC, 3)
        (fun e ↦ w (Fin.castAdd _ e)) ∧
      (scheme I).rows.IsLawfulBelow (OrderedLayer.coatomD, 3) fun e ↦ w (Fin.castAdd _ e) := by
    rcases Seed.pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hwC.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩,
        hwD.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩⟩
    · exact ⟨hwD.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩,
        hwC.mono (X := (_, 3)) ⟨subset_rfl, by omega⟩⟩
  obtain ⟨r₃, hr₃, hr₃w⟩ := exists_extension_bot (w := fun e ↦ w (Fin.castAdd _ e)) hcoat3.1
    hcoat3.2
  obtain ⟨g, hg_def⟩ : ∃ g : Fin (scheme I).card → Label.{u}, g = fun e ↦
      if he : e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) then r₃ ⟨e, he⟩
      else w (Fin.castAdd _ e) := ⟨_, rfl⟩
  have hgw (e : Fin (scheme I).card) (he : (scheme I).toCellScheme.scope e ≠ univ) :
      g e = w (Fin.castAdd _ e) := by
    rw [hg_def]
    beta_reduce
    by_cases h3 : e ∈ (scheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3)
    · rw [dite_eq_left h3]; exact hr₃w ⟨e, h3⟩ he
    · exact dite_eq_right h3
  have hgz (z : Fin 5) (hwz : (scheme I).rows.IsLawfulBelow (univ.erase z, 4)
      fun e ↦ w (Fin.castAdd _ e)) :
      (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun e ↦ g e :=
    (Rows.isLawfulBelow_congr (R := (scheme I).rows) (X := (univ.erase z, 4)) (w := g)
      (w' := fun e ↦ w (Fin.castAdd _ e)) fun e he ↦ hgw e fun hs ↦
      Seed.ne_univ_erase z (univ_subset_iff.mp (hs.ge.trans he.1))).mpr hwz
  have hg3 : (scheme I).rows.IsLawfulBelow (univ, 3) fun e ↦ g e := by
    convert hr₃ using 1
    exact funext fun e ↦ by rw [hg_def]; exact dite_eq_left e.2
  have hg : (scheme I).rows.IsLawfulBelow (univ, 4) fun e ↦ g e :=
    Rows.IsLawfulBelow.glue₃ (hgz x hwC) hg3 (hgz y hwD) (mem_below_cover hx hy hxy)
  obtain ⟨j₀, hj₀, -⟩ := Scheme.exists_leaf_eq (Mk := D.marks)
    (Scheme.orbitCode_splice_bot_mem_catalogue (S := scheme I) (k := 4) hg)
  obtain ⟨r, hr, hrg, -⟩ := Scheme.exists_isLawfulBelow_sheetLayer (hS := not_univ_four_le)
    (σ := Scheme.markedSheet _ _) (markedEntry_mem_spec D) D.cap_mem D.capRespects hj₀
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he, rfl⟩ := Scheme.exists_castAdd_eq_of_boundary_sheetLayer (S := scheme I) (k := 4)
    (hS := not_univ_four_le) (hU x) (hU y) hd
  rw [hrg e he]
  refine hgw e fun hs ↦ hd.elim (fun h ↦ ?_) fun h ↦ ?_
  · have := h.1
    -- The scope of the old cell `e` in the marked top.
    change (Scheme.appendFullCellsScheme (scheme I) 4 _).scope (Fin.castAdd _ e) ⊆ _ at this
    rw [Scheme.appendFullCellsScheme_scope_castAdd, hs] at this
    exact Seed.ne_univ_erase x (univ_subset_iff.mp this)
  · have := h.1
    -- The scope of the old cell `e` in the marked top.
    change (Scheme.appendFullCellsScheme (scheme I) 4 _).scope (Fin.castAdd _ e) ⊆ _ at this
    rw [Scheme.appendFullCellsScheme_scope_castAdd, hs] at this
    exact Seed.ne_univ_erase y (univ_subset_iff.mp this)

/-! ### The lifts of the marked top -/

/-- The faces of the marked top are those of the amalgam. -/
theorem faces_markedTop : (markedTop I D).toCellScheme.faces = I.amalgam.toCellScheme.faces :=
  I.faces_tower 2

/-- The graded faces of the marked top are those of the amalgam. -/
theorem gradedFaces_markedTop :
    (markedTop I D).toCellScheme.gradedFaces = I.amalgam.toCellScheme.gradedFaces := by
  unfold CellScheme.gradedFaces
  rw [faces_markedTop]

/-- **Lifts below a pair not above `(univ, 4)`** are those of the profile layer. -/
theorem cappedLift_markedTop_iff {X Y : Finset (Fin 5) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin 5)), 4) ≤ Y) :
    (markedTop I D).rows.CappedLift hXY ↔ (scheme I).rows.CappedLift hXY := by
  have h := Scheme.isSourcePrefix_sheetLayer (scheme I) 4 (Scheme.markedEntry (scheme I) 4 D.marks)
    (Scheme.markedSheet _ _) D.cap not_univ_four_le hY
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_castAdd]

/-- **Lifts between graded faces off the ground set** are lifts of the amalgam. -/
theorem cappedLift_markedTop_old {X Y : Finset (Fin 5) × ℕ}
    (hX : X ∈ (markedTop I D).toCellScheme.gradedFaces)
    (hY : Y ∈ (markedTop I D).toCellScheme.gradedFaces) (h : X ≤ Y) (hY1 : Y.1 ≠ univ) :
    (markedTop I D).rows.CappedLift h :=
  (cappedLift_markedTop_iff D h fun h' ↦ hY1 (univ_subset_iff.mp h'.1)).mpr
    ((cappedLift_scheme_old_iff h hY1).mpr
      (I.isBountiful (gradedFaces_markedTop D ▸ hX) (gradedFaces_markedTop D ▸ hY) h))

/-- **The lifts at the grades `j ≤ 3`**, from either coatom into `(univ, j)`: those of the
profile layer (`TowerProfile.cappedLift_top_le_three`). -/
theorem cappedLift_markedTop_le_three {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) {j : ℕ} (hj : j ≤ 3) :
    (markedTop I D).rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin 5)), j))
      ⟨erase_subset _ _, le_rfl⟩ := by
  have hY : ¬ ((univ : Finset (Fin 5)), 4) ≤ ((univ : Finset (Fin 5)), j) :=
    fun h ↦ absurd h.2 (by simp only; omega)
  refine (cappedLift_markedTop_iff D _ hY).mpr ?_
  exact (cappedLift_top_iff (I := I) _ hY).mp (cappedLift_top_le_three hx hj)

/-- The common face of the two coatoms is a face of the amalgam, with three points. -/
private theorem commonFace_props' {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y) :
    univ.erase x ∩ univ.erase y ∈ I.amalgam.toCellScheme.faces ∧
      #(univ.erase x ∩ univ.erase y) = 3 := by
  have h := I.commonFace_mem_faces
  rcases Seed.pair_cases hx hy hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨?_, by decide⟩
    convert h using 1
    ext z
    simp only [mem_inter, mem_erase, mem_univ, and_true]
    exact and_comm
  · refine ⟨?_, by decide⟩
    convert h using 1
    ext z
    simp only [mem_inter, mem_erase, mem_univ, and_true]

/-- **The lift at the grade `4`**, from either coatom into `(univ, 4)`, as
`TowerProfile.cappedLift_top_four`, with the extensions through the marked top. -/
theorem cappedLift_markedTop_four {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
    (markedTop I D).rows.CappedLift (X := (univ.erase x, 4)) (Y := ((univ : Finset (Fin 5)), 4))
      ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := commonFace_props' (I := I) hx hy hxy
  have hcard (z : Fin 5) : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hlift := cappedLift_markedTop_le_three D hx le_rfl
  have hwf := (Scheme.isWellFormed_sheetLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
    (ε := Scheme.markedEntry (scheme I) 4 D.marks) (σ := Scheme.markedSheet _ _) (κ := D.cap)
    isWellFormed_scheme (by omega) (by omega)).isWellFormed
  -- A leaf at `(univ, 4)`.
  obtain ⟨i₀, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
    (S := scheme I) (k := 4) (p := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _))
  -- A cell at `(univ.erase x, 4)`.
  obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq_tower 2 (X := (univ.erase x, 4))
    ⟨I.erase_mem_faces hx, by omega, by rw [hcard]⟩ (Seed.ne_univ_erase x)
  refine Rows.cappedLift_of_boundaries_short (C := univ.erase x) (B := univ) (j := 3)
    (U₀ := (univ.erase x, 4)) (V₀ := (univ.erase y, 4)) (O₀ := (univ.erase x ∩ univ.erase y, 3))
    (U := (univ.erase x, 4)) (V := (univ, 3)) (O := (univ.erase x, 3))
    (erase_subset _ _) ⟨Fin.castAdd _ (Fin.castAdd _ c), ?_⟩ hlift le_rfl
    ⟨inter_subset_left, by omega⟩ ⟨inter_subset_right, by omega⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨erase_subset _ _, le_rfl⟩ (fun d hdU hdV ↦ ⟨subset_inter hdU.1 hdV.1, ?_⟩)
    (Rows.cappedLift_refl _) ?_ (extendsFromBoundary_bot_markedTop D hx hy hxy)
    le_rfl ⟨subset_rfl, by omega⟩ ⟨subset_univ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, by omega⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (Rows.cappedLift_refl _) hlift
    ⟨Fin.natAdd _ (Fin.castAdd _ i₀), Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _⟩
    fun u hu ↦ ?_
  · rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd, hc]
  · -- A cell below both coatoms has grade at most the size of the common face.
    have h1 : (markedTop I D).toCellScheme.grade d ≤ #((markedTop I D).toCellScheme.scope d) :=
      hwf.grade_le_card d
    have h2 : #((markedTop I D).toCellScheme.scope d) ≤ 3 :=
      (card_le_card (subset_inter hdU.1 hdV.1)).trans hOcard.le
    change (markedTop I D).toCellScheme.grade d ≤ 3
    omega
  · exact cappedLift_markedTop_old D ⟨faces_markedTop D ▸ hOf, by omega, by rw [hOcard]⟩
      ⟨faces_markedTop D ▸ I.erase_mem_faces hy, by omega, by rw [hcard]⟩ _
      (Seed.ne_univ_erase y)
  · obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq_sheetLayer (S := scheme I) (k := 4)
      (hS := not_univ_four_le) hu
    exact ⟨Scheme.isConsistent_sheetLayer (hS := not_univ_four_le) isConsistent_scheme
        (markedEntry_mem_spec D) D.cap_mem D.capRespects _,
      fun d ↦ (Scheme.isShort_ne_top_row_sheetLayer (hS := not_univ_four_le)
        (markedEntry_mem_spec D) D.cap_mem i _).1,
      fun d ↦ (Scheme.isShort_ne_top_row_sheetLayer (hS := not_univ_four_le)
        (markedEntry_mem_spec D) D.cap_mem i _).2,
      fun h hh hs hbot ↦ extendsFromBoundary_markedTop D hx hy hxy hu hh hs hbot⟩

/-! ### Legality below the full grade -/

/-- **The marked top is bountiful**, as `TowerProfile.isBountiful_top`. -/
theorem isBountiful_markedTop : (markedTop I D).rows.IsBountiful := by
  have hcard (z : Fin 5) : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hfull {x : Fin 5} (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
      (j : ℕ) (hj : j ≤ #(univ.erase x)) :
      (markedTop I D).rows.CappedLift (X := (univ.erase x, j))
        (Y := ((univ : Finset (Fin 5)), j)) ⟨erase_subset _ _, le_rfl⟩ := by
    rw [hcard] at hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact cappedLift_markedTop_le_three D hx (by omega)
    · exact cappedLift_markedTop_four D hx
  exact Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 4)
    (b := Fin.castSucc (Fin.last 3)) (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ I.subset_or_subset B (faces_markedTop D ▸ hB) hne)
    (faces_markedTop D ▸ I.erase_last_mem_faces)
    (faces_markedTop D ▸ I.erase_castSucc_mem_faces)
    (fun X Y hX hY h hYne ↦ cappedLift_markedTop_old D hX hY h hYne)
    (hfull (by simp)) (hfull (by simp))

/-- Every cell of the marked top has grade below `5`. -/
theorem grade_markedTop_lt (z : Fin (markedTop I D).card) :
    (markedTop I D).toCellScheme.grade z < 5 := by
  induction z using Fin.addCases with
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  | left z =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    induction z using Fin.addCases with
    | right j => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
    | left e =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      exact I.grade_tower_lt (by omega) e

/-- **Completeness below the full grade**, as `TowerProfile.exists_gradedIndex_eq_top`, with a leaf
at `(univ, 4)`. -/
theorem exists_gradedIndex_eq_markedTop (X : Finset (Fin 5) × ℕ)
    (hX : X ∈ (markedTop I D).toCellScheme.gradedFaces) (hX2 : X.2 < 5) :
    ∃ d, (markedTop I D).toCellScheme.gradedIndex d = X := by
  obtain ⟨B, j⟩ := X
  have hgi (e : Fin (I.tower 2).card) :
      (markedTop I D).toCellScheme.gradedIndex (Fin.castAdd _ (Fin.castAdd _ e)) =
        (I.tower 2).toCellScheme.gradedIndex e := by
    rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd]
  by_cases hB : B = univ
  · subst hB
    have hj0 : 0 < j := hX.2.1
    simp only at hX2
    rcases (show j ≤ 2 ∨ j = 3 ∨ j = 4 by omega) with hj | rfl | rfl
    · obtain ⟨t, ht⟩ := I.exists_gradedIndex_eq_univ_tower_of_le hj0 2 hj
      exact ⟨_, (hgi t).trans ht⟩
    · obtain ⟨i₀, -⟩ := exists_entry_eq (RankProfile.bot_mem_rankCat (I := I) 3)
      exact ⟨Fin.castAdd _ (Fin.natAdd _ i₀), by
        rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd]⟩
    · obtain ⟨i₀, -⟩ := Scheme.exists_catalogueEntry_eq
        (Scheme.orbitCode_splice_bot_mem_catalogue (S := scheme I) (k := 4) (p := fun _ ↦ ⊥)
          (Rows.isLawfulBelow_const_bot _))
      exact ⟨Fin.natAdd _ (Fin.castAdd _ i₀),
        Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _⟩
  · obtain ⟨e, he⟩ := I.exists_gradedIndex_eq_tower 2 (gradedFaces_markedTop D ▸ hX) hB
    exact ⟨_, (hgi e).trans he⟩

/-- **The marked top is legal below the full grade.** -/
theorem isLegalBelowFullGrade_markedTop : (markedTop I D).IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_sheetLayer (hS := not_univ_four_le) isWellFormed_scheme
    (by omega) (by omega)
  isCoded := Scheme.isCoded_sheetLayer (hS := not_univ_four_le) isCoded_scheme
    (markedEntry_mem_spec D) D.cap_mem
  isConsistent := Scheme.isConsistent_sheetLayer (hS := not_univ_four_le) isConsistent_scheme
    (markedEntry_mem_spec D) D.cap_mem D.capRespects
  isBountiful := isBountiful_markedTop D
  grade_lt := grade_markedTop_lt D
  exists_gradedIndex_eq := exists_gradedIndex_eq_markedTop D

/-! ### The completion -/

variable (I) in
/-- The old cells of the marked top. -/
noncomputable def markedEmbed (D : MarkedSpec I) : Fin I.amalgam.card ↪o Fin (markedTop I D).card :=
  (embed3 I).trans (Fin.castAddOrderEmb _)

@[simp] theorem markedEmbed_apply (d : Fin I.amalgam.card) :
    markedEmbed I D d = Fin.castAdd _ (embed3 I d) := rfl

/-- The old cells of the marked top form a lower embedding of the amalgam. -/
theorem isLowerEmbedding_markedEmbed :
    I.amalgam.toCellScheme.IsLowerEmbedding (markedTop I D).toCellScheme (markedEmbed I D) :=
  (Scheme.isLowerEmbedding_castAdd 4 _ _ not_univ_four_le).comp isLowerEmbedding_embed3

/-- The rows of the marked top pull back to those of the amalgam. -/
theorem comap_rows_markedEmbed :
    (markedTop I D).rows.comap (isLowerEmbedding_markedEmbed D) = I.amalgam.rows := by
  have h := Rows.comap_comap (markedTop I D).rows
    (Scheme.isLowerEmbedding_castAdd 4 _ _ not_univ_four_le) isLowerEmbedding_embed3
  rw [Scheme.comap_rows_castAdd (h := not_univ_four_le), comap_rows_embed3] at h
  exact h.symm

/-- The old cells of the marked top keep their graded indices. -/
theorem gradedIndex_markedEmbed (d : Fin I.amalgam.card) :
    (markedTop I D).toCellScheme.gradedIndex (markedEmbed I D d) =
      I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (gradedIndex_embed3 d)

/-- Every cell of the marked top of scope other than the ground set is old. -/
theorem mem_range_markedEmbed (z : Fin (markedTop I D).card)
    (hz : (markedTop I D).toCellScheme.scope z ≠ univ) : z ∈ Set.range (markedEmbed I D) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  | left z =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hz
    obtain ⟨d, rfl⟩ := mem_range_embed3 z hz
    exact ⟨d, rfl⟩

/-- **The glued labelling extends to a lawful section of the marked top**, unchanged at the old
cells, through the leaves (`extendsFromBoundary_bot_markedTop`). -/
theorem exists_isLawful_markedTop :
    ∃ q : Fin (markedTop I D).card → Label.{u}, (markedTop I D).rows.IsLawful q ∧
      ∀ d, q (markedEmbed I D d) = I.amalgam.label d := by
  classical
  set w : Fin (markedTop I D).card → Label.{u} :=
    Function.extend (markedEmbed I D) I.amalgam.label fun _ ↦ ⊥ with hw
  have hwe (d : Fin I.amalgam.card) : w (markedEmbed I D d) = I.amalgam.label d :=
    (markedEmbed I D).injective.extend_apply _ _ d
  have hlaw (z : Fin 5) (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
      (markedTop I D).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4)
      (h := not_univ_four_le) (v := w)
      (fun h' ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h'.1))).mpr ?_
    refine (isLawfulBelow_scheme_old_iff (g := fun e ↦ w (Fin.castAdd _ e))
      (Seed.ne_univ_erase z)).mpr ?_
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase z, 4))
      (w := I.amalgam.label) (w' := fun d ↦ w (Fin.castAdd _ (embed3 I d)))
      fun d _ ↦ (hwe d).symm).mp (I.amalgam.isLawful.isLawfulBelow _)
  obtain ⟨r, hr, hrw, -⟩ := extendsFromBoundary_bot_markedTop D (x := Fin.last 4)
    (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) w
    (hlaw _ (by simp)) (hlaw _ (by simp)) fun _ _ ↦ by simp
  have hall (z : Fin (markedTop I D).card) : z ∈ (markedTop I D).toCellScheme.below (univ, 4) :=
    ⟨subset_univ _, by
      have := grade_markedTop_lt D z
      change (markedTop I D).toCellScheme.grade z ≤ 4
      omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_⟩
  rw [← hwe d]
  refine hrw ⟨markedEmbed I D d, hall _⟩ ?_
  rcases I.scope_subset_or (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp)
    (by decide) d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, gradedIndex_markedEmbed]
    exact ⟨h, by have := (hall (markedEmbed I D d)).2; rwa [gradedIndex_markedEmbed] at this⟩
  · refine .inr ?_
    rw [CellScheme.mem_below, gradedIndex_markedEmbed]
    exact ⟨h, by have := (hall (markedEmbed I D d)).2; rwa [gradedIndex_markedEmbed] at this⟩

variable (I) in
/-- **The leaf-and-marked completion below the full grade** of a seed on five points, for a
marked specification `D`. -/
noncomputable def markedCompletion (D : MarkedSpec I) : CompletionBelowFullGrade I where
  scheme := markedTop I D
  embed := markedEmbed I D
  isLowerEmbedding := isLowerEmbedding_markedEmbed D
  scope_embed d := congrArg Prod.fst (gradedIndex_markedEmbed D d)
  comap_rows := comap_rows_markedEmbed D
  mem_range_embed := mem_range_markedEmbed D
  faces_eq := faces_markedTop D
  isLegalBelowFullGrade := isLegalBelowFullGrade_markedTop D
  label := (exists_isLawful_markedTop D).choose
  isLawful := (exists_isLawful_markedTop D).choose_spec.1
  label_embed := (exists_isLawful_markedTop D).choose_spec.2

/-- **The reading of the marked cells**: a predicate on the reading of the old cells by the rows
holds at every marked cell of the marked top when it holds on `marks`. -/
theorem markedTop_mark_reads {P : (Fin (scheme I).card → Label.{u}) → Prop}
    (hP : ∀ e ∈ D.marks, P e) (m : Fin D.marks.card) :
    P fun d ↦ (scheme I).sheetRow 4 ((scheme I).markedEntry 4 D.marks) (Scheme.markedSheet _ _)
      D.cap (Fin.natAdd _ m) (Fin.castAdd _ d) :=
  Scheme.markedLayer_mark_reads hP m

end TowerProfile

/-! ### A marked cell read as `⊥` at every leaf, in the marked top -/

namespace TowerProfile

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} (D : MarkedSpec I)

/-- **No marked gate in the marked top.**  For every marked specification `D` of a seed on five
points and every marked cell `m` whose row is `⊥` at every leaf (for instance a gate reading only
marked cells), some lawful labelling of the marked top extends the glued labelling of the amalgam
and is `⊥` at `m`.  So no marked cell is a gate that is not `⊥` in every lawful labelling with the
face of the first coatom type. -/
theorem exists_isLawful_markedTop_eq_bot (m : Fin D.marks.card)
    (hleaf : ∀ (i : Fin ((scheme I).catalogue 4).card) (t), (markedTop I D).rows.row
      (Fin.natAdd (scheme I).card (Fin.natAdd _ m)) t = ⊥ ∨
        t.1 ≠ Fin.natAdd (scheme I).card (Fin.castAdd D.marks.card i)) :
    ∃ q : Fin (markedTop I D).card → Label.{u}, (markedTop I D).rows.IsLawful q ∧
      (∀ d, q (markedEmbed I D d) = I.amalgam.label d) ∧
      q (Fin.natAdd (scheme I).card (Fin.natAdd _ m)) = ⊥ := by
  have hm := Scheme.markedLayer_cap_eq_bot_of_row_leaf (hS := not_univ_four_le) D.marks_subset
    D.cap_mem m hleaf
  -- a lawful labelling of the profile layer extending the glued labelling
  obtain ⟨q₀, hq₀, hq₀e⟩ := exists_isLawful_markedTop D
  have hp : (scheme I).rows.IsLawful fun d ↦ q₀ (Fin.castAdd _ d) := by
    have h := hq₀.comap (Scheme.isLowerEmbedding_castAdd (S := scheme I) 4 _ _ not_univ_four_le)
    rwa [Scheme.comap_rows_sheetLayer (hS := not_univ_four_le)] at h
  obtain ⟨r, hr, hrp, hrm⟩ := Scheme.exists_isLawfulBelow_markedLayer_eq_bot
    (hS := not_univ_four_le) D.marks_subset D.cap_mem D.capRespects m hm
    (p := fun d ↦ q₀ (Fin.castAdd _ d)) (hp.isLawfulBelow (univ, 4))
  have hall (z : Fin (markedTop I D).card) : z ∈ (markedTop I D).toCellScheme.below (univ, 4) :=
    ⟨subset_univ _, by
      have := grade_markedTop_lt D z
      -- the grade of the pair below is the grade of the cell
      change (markedTop I D).toCellScheme.grade z ≤ 4
      omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_, hrm⟩
  have hd : (scheme I).toCellScheme.grade (embed3 I d) ≤ 4 := by
    have h1 := (isLowerEmbedding_embed3 (I := I)).grade_eq d
    have h2 := I.grade_lt d
    omega
  rw [← hq₀e d]
  exact hrp (embed3 I d) hd

/-- **The marked top has a cell reading `⊥` at the grade `3` and at the grade `4`**: the cell of the
`⊥` profile of the profile layer, and the leaf of the `⊥` entry of the catalogue.  Both read every
old cell of the amalgam as `⊥`. -/
theorem exists_markedTop_row_eq_bot {N : ℕ} (hN : N = 3 ∨ N = 4) :
    ∃ u : Fin (markedTop I D).card,
      (markedTop I D).toCellScheme.gradedIndex u = ((univ : Finset (Fin 5)), N) ∧
      ∀ (d : Fin I.amalgam.card)
        (hd : markedEmbed I D d ∈
          (markedTop I D).toCellScheme.below ((markedTop I D).toCellScheme.gradedIndex u)),
        (markedTop I D).rows.row u ⟨_, hd⟩ = ⊥ := by
  rcases hN with rfl | rfl
  · obtain ⟨u, hu, hrow⟩ := exists_scheme_row_eq_bot (I := I)
    refine ⟨Fin.castAdd _ u, ?_, fun d hd ↦ ?_⟩
    · rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hu]
    · have hd' : embed3 I d ∈ (scheme I).toCellScheme.below
          ((scheme I).toCellScheme.gradedIndex u) := by
        have := hd
        rw [CellScheme.mem_below, markedEmbed_apply,
          Scheme.appendFullCellsScheme_gradedIndex_castAdd,
          Scheme.appendFullCellsScheme_gradedIndex_castAdd] at this
        exact this
      rw [← hrow d hd']
      have key := congrArg (fun R : (scheme I).toCellScheme.Rows ↦ R.row u ⟨embed3 I d, hd'⟩)
        (Scheme.comap_rows_sheetLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
          (ε := (scheme I).markedEntry 4 D.marks) (σ := Scheme.markedSheet _ _) (κ := D.cap))
      exact key
  · obtain ⟨j₀, hj₀, -⟩ := Scheme.exists_leaf_eq (Mk := D.marks) (Scheme.bot_mem_catalogue
      (scheme I) 4)
    refine ⟨Fin.natAdd _ j₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ 4 _ j₀,
      fun d hd ↦ ?_⟩
    rw [Scheme.sheetLayer_row_natAdd (hS := not_univ_four_le)]
    -- the row of a leaf at an old cell is its entry
    change (scheme I).sheetRow 4 ((scheme I).markedEntry 4 D.marks) (Scheme.markedSheet _ _)
      D.cap j₀ (Fin.castAdd _ (embed3 I d)) = ⊥
    rw [Scheme.sheetRow_castAdd, hj₀]

end TowerProfile

end VaughtConjecture
