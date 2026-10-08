/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTower

/-!
# The completion below the full grade at every arity

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade, at every arity
`m`; the case `m = 3` is `VaughtConjecture.Extension.TowerProfileCompletion`).

Let `I` be a seed on `m + 2` points and `N` a good level at the grade `m`
(`ProfileTower.Lvl.Good`, `VaughtConjecture.Extension.ProfileTower`) that extends at `⊥` from the
two coatoms at the grade `m` (`ProfileTower.Lvl.HasBotExtension`).  **The top layer**
(`ProfileTower.Lvl.top`) is the canonical field layer at the grade `m + 1` over `N`
(`Scheme.fieldLayer`); no bottom apex is assumed.  Every field of `CompletionBelowFullGrade` is
proved (`ProfileTower.Lvl.Good.completion`); compiled in this repository (theorem named):

* the old cells: a lower embedding keeping scopes and rows, every cell of proper scope old, the
  faces those of the amalgam (`ProfileTower.Lvl.Good.isLowerEmbedding_top`,
  `ProfileTower.Lvl.Good.comap_rows_top`, `ProfileTower.Lvl.Good.mem_range_topEmbed`);
* **legality below the full grade** (`ProfileTower.Lvl.Good.isLegalBelowFullGrade_top`): well
  formed, coded and consistent, complete below the grade `m + 2`
  (`ProfileTower.Lvl.Good.exists_gradedIndex_eq_top`), and bountiful
  (`ProfileTower.Lvl.Good.isBountiful_top`, `CellScheme.Rows.isBountiful_of_coatoms`): off the
  full face the lifts are those of the amalgam; from either coatom into the full face, at the
  grades `j ≤ m` the lifts of the level, and at the grade `m + 1` the one-grade lift
  (`ProfileTower.Lvl.Good.cappedLift_top_succ`) with the extension at `⊥`
  (`ProfileTower.Lvl.Good.extendsFromBoundary_bot_top`) and, at the caps short at `m + 1`, the
  extension that lifts within the other coatom from the grade `m`, the common face on `m` points
  carrying no cell of the grade `m + 1` (`ProfileTower.Lvl.Good.extendsFromBoundary_top`,
  `Seed.exists_lift_union_of_le`);
* the lawful labelling extending the glued one (`ProfileTower.Lvl.Good.exists_isLawful_top`).

The level at the grade `m ≥ 3` is the next level of the good level at `m - 1`, so it is good and
extends at `⊥` (`ProfileTower.Lvl.Good.next`, `ProfileTower.Lvl.Good.hasBotExtension_next`).
Hence **every seed on `m + 2 ≥ 5` points has a completion below the full grade**
(`ProfileTower.nonempty_completionBelowFullGrade_of_three_le`), and with the completion of the
tower at `m ≤ 2`, **every seed has one** (`Seed.nonempty_completionBelowFullGrade`).  So **the
coatom extension property with apex holds at every stage that is zero or a limit**
(`StageType.hasApexCoatomExtensions`, through
`StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`); compiled in this repository
(theorem named), with the single hypothesis `Order.IsSuccPrelimit α`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The top layer** over a level at the grade `m`: the canonical field layer at the grade
`m + 1`. -/
noncomputable abbrev Lvl.top (N : Lvl I m) : Scheme.{u} (m + 2) := N.S.fieldLayer (m + 1) N.not_le

section Top

variable {N : Lvl I m}

/-- **The boundary labelling at the grade `m + 1`, completed on a good level at the grade `m`.**
Let `C = univ.erase x`, `D = univ.erase y` be the two coatoms, `w` a labelling of the level lawful
below `(C, m + 1)` and `(univ, m)`, and `a` a lawful section of it agreeing with `w` capped at `h`
(self-visible at `m + 1`) on the cells below `(C, m + 1)` or `(univ, m)`.  Some labelling lawful
below `(univ, m + 1)` is `w` on those cells and agrees with `a` capped at `h` below
`(univ, m + 1)`: below `(D, m + 1)` there are only old cells, where the boundary labelling is
lifted within `D` from the grade `m` (`Seed.exists_lift_union_of_le`: the common face carries no
cell of the grade `m + 1`), and the three pieces are glued
(`CellScheme.Rows.IsLawfulBelow.glue₃`, `Lvl.Good.mem_below_cover`). -/
theorem Lvl.Good.exists_isLawfulBelow_top (hN : N.Good) {x y : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hy : y ∈ (Pts : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {w : Fin N.S.card → Label.{u}}
    (hwU : N.S.rows.IsLawfulBelow (univ.erase x, m + 1) fun d ↦ w d)
    (hwV : N.S.rows.IsLawfulBelow (univ, m) fun d ↦ w d)
    {a : Fin N.S.card → Label.{u}} (ha : N.S.rows.IsLawful a) {h : Label.{u}}
    (hh : IsSelfVisible (m + 1) h)
    (hag : ∀ e, e ∈ N.S.toCellScheme.below (univ.erase x, m + 1) ∨
      e ∈ N.S.toCellScheme.below (univ, m) → min (w e) h = min (a e) h) :
    ∃ g : Fin N.S.card → Label.{u},
      N.S.rows.IsLawfulBelow (univ, m + 1) (fun d ↦ g d) ∧
      (∀ e, e ∈ N.S.toCellScheme.below (univ.erase x, m + 1) ∨
        e ∈ N.S.toCellScheme.below (univ, m) → g e = w e) ∧
      ∀ e ∈ N.S.toCellScheme.below (univ, m + 1), min (g e) h = min (a e) h := by
  classical
  have hDne := Seed.ne_univ_erase y
  have hmemD {d : Fin I.amalgam.card} {X : Finset (Fin (m + 2)) × ℕ} :
      N.embed d ∈ N.S.toCellScheme.below X ↔ d ∈ I.amalgam.toCellScheme.below X := by
    rw [CellScheme.mem_below, CellScheme.mem_below, hN.gradedIndex_embed]
  -- The lift within the other coatom, read on the amalgam.
  obtain ⟨v, hv, hvw, hva⟩ := I.exists_lift_union_of_le hx hy hxy (j := m) le_rfl hh
    (a := fun d ↦ a (N.embed d))
    ((hN.isLawfulBelow_old_iff (w := a) hDne).mp (ha.isLawfulBelow _))
    (w := fun d ↦ w (N.embed d))
    ((hN.isLawfulBelow_old_iff (w := w) hDne).mp
      (hwV.mono (X := (univ.erase y, m)) ⟨subset_univ _, le_rfl⟩))
    fun d hd ↦ hag _ (.inr (hmemD.mpr ⟨hd.1.trans (subset_univ _), hd.2⟩))
  -- The lift, carried to the level.
  have P := hN.isSourcePrefix (Y := (univ.erase y, m + 1)) hDne
  obtain ⟨v', hv', hv'v⟩ := P.exists_isLawfulBelow le_rfl (s := v)
    (by rw [hN.comap_rows]; exact hv)
  have hv't (t : I.amalgam.toCellScheme.below (univ.erase y, m + 1)) :
      v' ⟨N.embed t, hmemD.mpr t.2⟩ = v t := hv'v t
  have hold (e : Fin N.S.card) (he : e ∈ N.S.toCellScheme.below (univ.erase y, m + 1)) :
      ∃ t : I.amalgam.toCellScheme.below (univ.erase y, m + 1), N.embed t = e := by
    obtain ⟨t, rfl⟩ := hN.mem_range e fun hsc ↦ hDne (univ_subset_iff.mp (hsc.ge.trans he.1))
    exact ⟨⟨t, hmemD.mp he⟩, rfl⟩
  obtain ⟨g, hgb, hgo⟩ : ∃ g : Fin N.S.card → Label.{u},
      (∀ e, e ∈ N.S.toCellScheme.below (univ.erase x, m + 1) ∨
        e ∈ N.S.toCellScheme.below (univ, m) → g e = w e) ∧
      ∀ e (he : e ∈ N.S.toCellScheme.below (univ.erase y, m + 1)),
        ¬ (e ∈ N.S.toCellScheme.below (univ.erase x, m + 1) ∨
          e ∈ N.S.toCellScheme.below (univ, m)) → g e = v' ⟨e, he⟩ :=
    ⟨fun e ↦ if e ∈ N.S.toCellScheme.below (univ.erase x, m + 1) ∨
        e ∈ N.S.toCellScheme.below (univ, m) then w e
      else Rows.extendBot (univ.erase y, m + 1) v' e,
      fun e hb ↦ ite_eq_left hb, fun e he hb ↦ (ite_eq_right hb).trans
        (Rows.extendBot_of_mem v' he)⟩
  have hgD (e : Fin N.S.card) (he : e ∈ N.S.toCellScheme.below (univ.erase y, m + 1)) :
      g e = v' ⟨e, he⟩ := by
    by_cases hb : e ∈ N.S.toCellScheme.below (univ.erase x, m + 1) ∨
        e ∈ N.S.toCellScheme.below (univ, m)
    · rw [hgb e hb]
      obtain ⟨t, rfl⟩ := hold e he
      rw [hv't t]
      refine (hvw t ?_).symm
      rcases hb with hb | hb
      · exact .inl ⟨subset_inter (hmemD.mp hb).1 t.2.1, t.2.2⟩
      · exact .inr ⟨t.2.1, (hmemD.mp hb).2⟩
    · exact hgo e he hb
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, m + 1)) (V := (univ, m))
    (W := (univ.erase y, m + 1)) ?_ ?_ ?_ (hN.mem_below_cover hx hy hxy), hgb, fun e he ↦ ?_⟩
  · convert hwU using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hwV using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · convert hv' using 1
    exact funext fun e ↦ hgD e e.2
  · rcases hN.mem_below_cover hx hy hxy e he with hb | hb | hb
    · rw [hgb e (.inl hb)]
      exact hag e (.inl hb)
    · rw [hgb e (.inr hb)]
      exact hag e (.inr hb)
    · rw [hgD e hb]
      obtain ⟨t, rfl⟩ := hold e hb
      rw [hv't t]
      exact hva t

/-- **Extension from the boundary at the grade `m + 1`, at a short positive cap**, along the row
of every cell of the top layer: the boundary labelling is completed on the level
(`Lvl.Good.exists_isLawfulBelow_top`) and extended through the new cells
(`Scheme.extendsFromBoundary_fieldLayer_of_fill`). -/
theorem Lvl.Good.extendsFromBoundary_top (hN : N.Good) {x y : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) (hy : y ∈ (Pts : Finset (Fin (m + 2))))
    (hxy : x ≠ y) {u : Fin N.top.card}
    (hu : N.top.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), m + 1))
    {h : Label.{u}} (hh : IsSelfVisible (m + 1) h) (hs : IsShort (m + 1) h) (hbot : ⊥ < h) :
    N.top.rows.ExtendsFromBoundary (univ.erase x, m + 1) (univ, m) (univ, m + 1) h
      (N.top.rows.rowBelow u hu) :=
  Scheme.extendsFromBoundary_fieldLayer_of_fill N.S (m + 1)
    (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1)) (fun h ↦ absurd h.2 (by simp))
    le_rfl (by simp) hh hs hbot
    (fun _ ha _ hwU hwV hag ↦ hN.exists_isLawfulBelow_top hx hy hxy hwU hwV
      (Scheme.mem_catalogue.mp ha).1 hh hag) hu

/-- **Extension at the cap `⊥` through the top layer** from the two coatoms at the grade `m + 1`:
the restriction to the level is extended below `(univ, m)` (`Lvl.HasBotExtension`), glued with
the old cells of the grade `m + 1`, and extended through the top layer
(`Scheme.exists_isLawfulBelow_fieldLayer`). -/
theorem Lvl.Good.extendsFromBoundary_bot_top (hN : N.Good) (hB : N.HasBotExtension)
    {x y : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
    (hy : y ∈ (Pts : Finset (Fin (m + 2)))) (hxy : x ≠ y) :
    N.top.rows.ExtendsFromBoundary (univ.erase x, m + 1) (univ.erase y, m + 1) (univ, m + 1) ⊥
      fun _ ↦ ⊥ := by
  classical
  intro w hwx hwy _
  have hU (z : Fin (m + 2)) : ¬ ((univ : Finset (Fin (m + 2))), m + 1) ≤ (univ.erase z, m + 1) :=
    fun h ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h.1)
  have hw₁ (z : Fin (m + 2))
      (hwz : N.top.rows.IsLawfulBelow (univ.erase z, m + 1) fun d ↦ w d) :
      N.S.rows.IsLawfulBelow (univ.erase z, m + 1) fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := N.S) (k := m + 1)
      (r := fun i ↦ N.S.fieldRow (m + 1) (N.S.catalogueEntry (m + 1) i))
      (h := N.not_le) (v := w) (hU z)).mp hwz
  have hwC := hw₁ _ hwx
  have hwD := hw₁ _ hwy
  have hdown (z : Fin (m + 2))
      (hwz : N.S.rows.IsLawfulBelow (univ.erase z, m + 1) fun e ↦ w (Fin.castAdd _ e)) :
      N.S.rows.IsLawfulBelow (univ.erase z, m) fun e ↦ w (Fin.castAdd _ e) :=
    hwz.mono (X := (univ.erase z, m)) ⟨subset_rfl, by omega⟩
  obtain ⟨hcC, hcD⟩ := lawful_pair (R := N.S.rows) (w := fun e ↦ w (Fin.castAdd _ e)) hx hy hxy
    (hdown _ hwC) (hdown _ hwD)
  obtain ⟨r₃, hr₃, hr₃w⟩ := hB (fun e ↦ w (Fin.castAdd _ e)) hcC hcD
  obtain ⟨g, hg_def⟩ : ∃ g : Fin N.S.card → Label.{u}, g = fun e ↦
      if he : e ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), m) then r₃ ⟨e, he⟩
      else w (Fin.castAdd _ e) := ⟨_, rfl⟩
  have hgw (e : Fin N.S.card) (he : N.S.toCellScheme.scope e ≠ univ) :
      g e = w (Fin.castAdd _ e) := by
    rw [hg_def]
    beta_reduce
    by_cases h3 : e ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), m)
    · rw [dite_eq_left h3]; exact hr₃w ⟨e, h3⟩ he
    · exact dite_eq_right h3
  have hgz (z : Fin (m + 2)) (hwz : N.S.rows.IsLawfulBelow (univ.erase z, m + 1)
      fun e ↦ w (Fin.castAdd _ e)) :
      N.S.rows.IsLawfulBelow (univ.erase z, m + 1) fun e ↦ g e :=
    (Rows.isLawfulBelow_congr (R := N.S.rows) (X := (univ.erase z, m + 1)) (w := g)
      (w' := fun e ↦ w (Fin.castAdd (N.S.catalogue (m + 1)).card e)) fun e he ↦ hgw e fun hs ↦
      Seed.ne_univ_erase z (univ_subset_iff.mp (hs.ge.trans he.1))).mpr hwz
  have hg3 : N.S.rows.IsLawfulBelow (univ, m) fun e ↦ g e := by
    convert hr₃ using 1
    exact funext fun e ↦ by rw [hg_def]; exact dite_eq_left e.2
  have hg : N.S.rows.IsLawfulBelow (univ, m + 1) fun e ↦ g e :=
    Rows.IsLawfulBelow.glue₃ (hgz x hwC) hg3 (hgz y hwD) (hN.mem_below_cover hx hy hxy)
  obtain ⟨r, hr, hrg⟩ := Scheme.exists_isLawfulBelow_fieldLayer (S := N.S) (k := m + 1)
    (hS := N.not_le) (p := g) hg
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he, rfl⟩ := Scheme.exists_castAdd_eq_of_boundary (S := N.S) (k := m + 1)
    (hS := N.not_le) (hU x) (hU y) hd
  rw [hrg e he]
  refine hgw e fun hs ↦ hd.elim (fun h ↦ ?_) fun h ↦ ?_
  · have := h.1
    -- The scope of the old cell `e` in the top layer.
    change (Scheme.appendFullCellsScheme N.S (m + 1) _).scope (Fin.castAdd _ e) ⊆ _ at this
    rw [Scheme.appendFullCellsScheme_scope_castAdd, hs] at this
    exact Seed.ne_univ_erase x (univ_subset_iff.mp this)
  · have := h.1
    -- The scope of the old cell `e` in the top layer.
    change (Scheme.appendFullCellsScheme N.S (m + 1) _).scope (Fin.castAdd _ e) ⊆ _ at this
    rw [Scheme.appendFullCellsScheme_scope_castAdd, hs] at this
    exact Seed.ne_univ_erase y (univ_subset_iff.mp this)

/-! ### The lifts of the top layer -/

/-- **Lifts below a pair not above `(univ, m + 1)`** are those of the level. -/
theorem Lvl.cappedLift_top_iff {X Y : Finset (Fin (m + 2)) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin (m + 2))), m + 1) ≤ Y) :
    N.top.rows.CappedLift hXY ↔ N.S.rows.CappedLift hXY := by
  have h := Scheme.isSourcePrefix_fieldLayer N.S (m + 1) N.not_le hY
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_fieldLayer]

/-- **Lifts between graded faces off the ground set** are lifts of the amalgam. -/
theorem Lvl.Good.cappedLift_top_old (hN : N.Good) {X Y : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ I.amalgam.toCellScheme.gradedFaces) (hY : Y ∈ I.amalgam.toCellScheme.gradedFaces)
    (h : X ≤ Y) (hY1 : Y.1 ≠ univ) : N.top.rows.CappedLift h :=
  (Lvl.cappedLift_top_iff h fun h' ↦ hY1 (univ_subset_iff.mp h'.1)).mpr
    (hN.cappedLift_old hX hY hY1 h)

/-- **The lifts at the grades `j ≤ m`**, from either coatom into `(univ, j)`
(`Lvl.Good.lift`). -/
theorem Lvl.Good.cappedLift_top_le (hN : N.Good) {x : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {j : ℕ} (hj : j ≤ m) :
    N.top.rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨erase_subset _ _, le_rfl⟩ :=
  (Lvl.cappedLift_top_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr (hN.lift x hx j hj)

/-- **The lift at the grade `m + 1`**, from either coatom into `(univ, m + 1)`, by the one-grade
lift with the boundary triples of the top step of the tower: at `⊥`, the two coatoms and their
common face (`Lvl.Good.extendsFromBoundary_bot_top`); at the positive caps,
`U = (C, m + 1)`, `V = (univ, m)`, `O = (C, m)`, with the lift at the grade `m`
(`Lvl.Good.cappedLift_top_le`) and the extension that lifts within the other coatom
(`Lvl.Good.extendsFromBoundary_top`). -/
theorem Lvl.Good.cappedLift_top_succ (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    N.top.rows.CappedLift (X := (univ.erase x, m + 1))
      (Y := ((univ : Finset (Fin (m + 2))), m + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := inter_props (I := I) hx hy hxy
  have hcard (z : Fin (m + 2)) : #(univ.erase z) = m + 1 := Seed.card_erase z
  have hlift := hN.cappedLift_top_le hx le_rfl
  have hwf := (Scheme.isWellFormed_fieldLayer (S := N.S) (k := m + 1) (hS := N.not_le)
    hN.wf (by omega) (by omega)).isWellFormed
  -- A cell at `(univ, m + 1)`.
  obtain ⟨i₀, -⟩ := Scheme.exists_catalogueEntry_eq (Scheme.orbitCode_splice_bot_mem_catalogue
    (S := N.S) (k := m + 1) (p := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _))
  -- A cell at `(univ.erase x, m + 1)`.
  obtain ⟨c, hc⟩ := I.exists_gradedIndex_eq (univ.erase x, m + 1)
    ⟨I.erase_mem_faces hx, by omega, show m + 1 ≤ #(univ.erase x) by rw [hcard]⟩
    (Seed.ne_univ_erase x)
  refine Rows.cappedLift_of_boundaries_short (C := univ.erase x) (B := univ) (j := m)
    (U₀ := (univ.erase x, m + 1)) (V₀ := (univ.erase y, m + 1))
    (O₀ := (univ.erase x ∩ univ.erase y, m))
    (U := (univ.erase x, m + 1)) (V := (univ, m)) (O := (univ.erase x, m))
    (erase_subset _ _) ⟨Fin.castAdd _ (N.embed c), ?_⟩ hlift le_rfl
    ⟨inter_subset_left, by omega⟩ ⟨inter_subset_right, by omega⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨erase_subset _ _, le_rfl⟩ (fun d hdU hdV ↦ ⟨subset_inter hdU.1 hdV.1, ?_⟩)
    (Rows.cappedLift_refl _) ?_ (hN.extendsFromBoundary_bot_top hB hx hy hxy)
    le_rfl ⟨subset_rfl, by omega⟩ ⟨subset_univ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, by omega⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (Rows.cappedLift_refl _) hlift
    ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩ fun u hu ↦ ?_
  · rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd, hN.gradedIndex_embed, hc]
  · -- A cell below both coatoms has grade at most the size of the common face.
    have h1 : N.top.toCellScheme.grade d ≤ #(N.top.toCellScheme.scope d) :=
      hwf.grade_le_card d
    have h2 : #(N.top.toCellScheme.scope d) ≤ m :=
      (card_le_card (subset_inter hdU.1 hdV.1)).trans hOcard.le
    -- The second component of the graded index is the grade.
    change N.top.toCellScheme.grade d ≤ m
    omega
  · exact hN.cappedLift_top_old ⟨hOf, by omega, by rw [hOcard]⟩
      ⟨I.erase_mem_faces hy, by omega, by rw [hcard]⟩ _ (Seed.ne_univ_erase y)
  · obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := N.S) (k := m + 1) (hS := N.not_le) hu
    exact ⟨Scheme.isConsistent_fieldLayer (hS := N.not_le) hN.consistent _,
      fun d ↦ (Scheme.isShort_ne_top_row_fieldLayer (hS := N.not_le) i _).1,
      fun d ↦ (Scheme.isShort_ne_top_row_fieldLayer (hS := N.not_le) i _).2,
      fun h hh hs hbot ↦ hN.extendsFromBoundary_top hx hy hxy hu hh hs hbot⟩

/-! ### Legality below the full grade -/

/-- **The top layer is bountiful** (`CellScheme.Rows.isBountiful_of_coatoms`). -/
theorem Lvl.Good.isBountiful_top (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m) :
    N.top.rows.IsBountiful := by
  have hfull {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2))))
      (j : ℕ) (hj : j ≤ #(univ.erase x)) :
      N.top.rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
        ⟨erase_subset _ _, le_rfl⟩ := by
    rw [Seed.card_erase] at hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact hN.cappedLift_top_le hx (by omega)
    · exact hN.cappedLift_top_succ hB hm hx
  have hfaces : N.top.toCellScheme.faces = I.amalgam.toCellScheme.faces := hN.faces
  have hgf : N.top.toCellScheme.gradedFaces = I.amalgam.toCellScheme.gradedFaces := by
    unfold CellScheme.gradedFaces
    rw [hfaces]
  exact Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last (m + 1))
    (b := Fin.castSucc (Fin.last m)) (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ I.subset_or_subset B (hfaces ▸ hB) hne)
    (hfaces ▸ I.erase_last_mem_faces)
    (hfaces ▸ I.erase_castSucc_mem_faces)
    (fun X Y hX hY h hYne ↦ hN.cappedLift_top_old (hgf ▸ hX) (hgf ▸ hY) h hYne)
    (hfull (by simp)) (hfull (by simp))

/-- Every cell of a good level has grade below `m + 2`. -/
theorem Lvl.Good.grade_lt (hN : N.Good) (z : Fin N.S.card) : N.S.toCellScheme.grade z < m + 2 := by
  rcases N.inv z with h | h
  · omega
  · obtain ⟨d, rfl⟩ := hN.mem_range z h
    rw [hN.lowerEmb.grade_eq]
    exact I.grade_lt d

/-- Every cell of the top layer has grade below `m + 2`. -/
theorem Lvl.Good.grade_top_lt (hN : N.Good) (z : Fin N.top.card) :
    N.top.toCellScheme.grade z < m + 2 := by
  induction z using Fin.addCases with
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  | left z => rw [Scheme.appendFullCellsScheme_grade_castAdd]; exact hN.grade_lt z

/-- **Completeness below the full grade**: every graded face of grade below `m + 2` carries a
cell: an old cell off the ground set, at `(univ, j)` for `j ≤ m` a cell of the level
(`Lvl.Good.complete`), and at `(univ, m + 1)` a cell of the top layer. -/
theorem Lvl.Good.exists_gradedIndex_eq_top (hN : N.Good) (X : Finset (Fin (m + 2)) × ℕ)
    (hX : X ∈ N.top.toCellScheme.gradedFaces) (hX2 : X.2 < m + 2) :
    ∃ d, N.top.toCellScheme.gradedIndex d = X := by
  obtain ⟨B, j⟩ := X
  have hgi (e : Fin N.S.card) :
      N.top.toCellScheme.gradedIndex (Fin.castAdd _ e) = N.S.toCellScheme.gradedIndex e :=
    Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _
  by_cases hB : B = univ
  · subst hB
    have hj0 : 0 < j := hX.2.1
    simp only at hX2
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · obtain ⟨t, ht⟩ := hN.complete j hj0 (by omega)
      exact ⟨_, (hgi t).trans ht⟩
    · obtain rfl : j = m + 1 := by omega
      obtain ⟨i₀, -⟩ := Scheme.exists_catalogueEntry_eq
        (Scheme.orbitCode_splice_bot_mem_catalogue (S := N.S) (k := m + 1) (p := fun _ ↦ ⊥)
          (Rows.isLawfulBelow_const_bot _))
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩
  · have hfaces : N.top.toCellScheme.faces = I.amalgam.toCellScheme.faces := hN.faces
    obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq (B, j) ⟨hfaces ▸ hX.1, hX.2⟩ hB
    exact ⟨Fin.castAdd _ (N.embed d), (hgi _).trans ((hN.gradedIndex_embed d).trans hd)⟩

/-- **The top layer is legal below the full grade.** -/
theorem Lvl.Good.isLegalBelowFullGrade_top (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m) :
    N.top.IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_fieldLayer hN.wf (by omega) (by omega)
  isCoded := Scheme.isCoded_fieldLayer hN.coded
  isConsistent := Scheme.isConsistent_fieldLayer hN.consistent
  isBountiful := hN.isBountiful_top hB hm
  grade_lt := hN.grade_top_lt
  exists_gradedIndex_eq := hN.exists_gradedIndex_eq_top

/-! ### The completion -/

/-- The old cells of the top layer. -/
noncomputable def Lvl.topEmbed (N : Lvl I m) : Fin I.amalgam.card ↪o Fin N.top.card :=
  N.embed.trans (Fin.castAddOrderEmb _)

@[simp] theorem Lvl.topEmbed_apply (d : Fin I.amalgam.card) :
    N.topEmbed d = Fin.castAdd _ (N.embed d) := rfl

/-- The old cells of the top layer form a lower embedding of the amalgam. -/
theorem Lvl.Good.isLowerEmbedding_top (hN : N.Good) :
    I.amalgam.toCellScheme.IsLowerEmbedding N.top.toCellScheme N.topEmbed :=
  (Scheme.isLowerEmbedding_fieldLayer N.S (m + 1) N.not_le).comp hN.lowerEmb

/-- The rows of the top layer pull back to those of the amalgam. -/
theorem Lvl.Good.comap_rows_top (hN : N.Good) :
    N.top.rows.comap hN.isLowerEmbedding_top = I.amalgam.rows := by
  have h := Rows.comap_comap N.top.rows
    (Scheme.isLowerEmbedding_fieldLayer N.S (m + 1) N.not_le) hN.lowerEmb
  rw [Scheme.comap_rows_fieldLayer, hN.comap_rows] at h
  exact h.symm

/-- The old cells of the top layer keep their graded indices. -/
theorem Lvl.Good.gradedIndex_topEmbed (hN : N.Good) (d : Fin I.amalgam.card) :
    N.top.toCellScheme.gradedIndex (N.topEmbed d) = I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (hN.gradedIndex_embed d)

/-- Every cell of the top layer of scope other than the ground set is old. -/
theorem Lvl.Good.mem_range_topEmbed (hN : N.Good) (z : Fin N.top.card)
    (hz : N.top.toCellScheme.scope z ≠ univ) : z ∈ Set.range N.topEmbed := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  | left z =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hz
    obtain ⟨d, rfl⟩ := hN.mem_range z hz
    exact ⟨d, rfl⟩

/-- **The glued labelling extends to a lawful section of the top layer**, unchanged at the old
cells: the extension at `⊥` from the two coatoms at the grade `m + 1`
(`Lvl.Good.extendsFromBoundary_bot_top`) of the glued labelling, every cell lying below
`(univ, m + 1)`. -/
theorem Lvl.Good.exists_isLawful_top (hN : N.Good) (hB : N.HasBotExtension) :
    ∃ q : Fin N.top.card → Label.{u}, N.top.rows.IsLawful q ∧
      ∀ d, q (N.topEmbed d) = I.amalgam.label d := by
  classical
  set w : Fin N.top.card → Label.{u} :=
    Function.extend N.topEmbed I.amalgam.label fun _ ↦ ⊥ with hw
  have hwe (d : Fin I.amalgam.card) : w (N.topEmbed d) = I.amalgam.label d :=
    N.topEmbed.injective.extend_apply _ _ d
  have hlaw (z : Fin (m + 2)) :
      N.top.rows.IsLawfulBelow (univ.erase z, m + 1) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff (S := N.S) (k := m + 1)
      (r := fun i ↦ N.S.fieldRow (m + 1) (N.S.catalogueEntry (m + 1) i))
      (h := N.not_le) (v := w)
      (fun h' ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h'.1))).mpr ?_
    refine (hN.isLawfulBelow_old_iff (w := fun e ↦ w (Fin.castAdd _ e))
      (Seed.ne_univ_erase z)).mpr ?_
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase z, m + 1))
      (w := I.amalgam.label) (w' := fun d ↦ w (Fin.castAdd _ (N.embed d)))
      fun d _ ↦ (hwe d).symm).mp (I.amalgam.isLawful.isLawfulBelow _)
  obtain ⟨r, hr, hrw, -⟩ := hN.extendsFromBoundary_bot_top hB (x := Fin.last (m + 1))
    (y := Fin.castSucc (Fin.last m)) (by simp) (by simp) Seed.last_ne_castSucc w
    (hlaw _) (hlaw _) fun _ _ ↦ by simp
  have hall (z : Fin N.top.card) : z ∈ N.top.toCellScheme.below (univ, m + 1) :=
    ⟨subset_univ _, by
      have := hN.grade_top_lt z
      -- The second component of the graded index is the grade.
      change N.top.toCellScheme.grade z ≤ m + 1
      omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_⟩
  rw [← hwe d]
  refine hrw ⟨N.topEmbed d, hall _⟩ ?_
  rcases I.scope_subset_or (x := Fin.last (m + 1)) (y := Fin.castSucc (Fin.last m)) (by simp)
    (by simp) Seed.last_ne_castSucc d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, hN.gradedIndex_topEmbed]
    exact ⟨h, by have := (hall (N.topEmbed d)).2; rwa [hN.gradedIndex_topEmbed] at this⟩
  · refine .inr ?_
    rw [CellScheme.mem_below, hN.gradedIndex_topEmbed]
    exact ⟨h, by have := (hall (N.topEmbed d)).2; rwa [hN.gradedIndex_topEmbed] at this⟩

/-- **The completion below the full grade over a good level at the grade `m`** that extends at
`⊥`: the level and the canonical field layer at the grade `m + 1`, with the glued labelling
extended (`Lvl.Good.exists_isLawful_top`). -/
noncomputable def Lvl.Good.completion (hN : N.Good) (hB : N.HasBotExtension) (hm : 1 ≤ m) :
    CompletionBelowFullGrade I where
  scheme := N.top
  embed := N.topEmbed
  isLowerEmbedding := hN.isLowerEmbedding_top
  scope_embed d := congrArg Prod.fst (hN.gradedIndex_topEmbed d)
  comap_rows := hN.comap_rows_top
  mem_range_embed := hN.mem_range_topEmbed
  faces_eq := hN.faces
  isLegalBelowFullGrade := hN.isLegalBelowFullGrade_top hB hm
  label := (hN.exists_isLawful_top hB).choose
  isLawful := (hN.exists_isLawful_top hB).choose_spec.1
  label_embed := (hN.exists_isLawful_top hB).choose_spec.2

end Top

/-! ### Every seed has a completion below the full grade -/

/-- **Every seed on `m + 2 ≥ 5` points has a completion below the full grade**: the level at the
grade `m` (`ProfileTower.lvl`, good by `ProfileTower.lvl_good` and `Lvl.Good.next`, extending at
`⊥` by `Lvl.Good.hasBotExtension_next`) and the canonical field layer at the grade `m + 1`
(`Lvl.Good.completion`). -/
theorem nonempty_completionBelowFullGrade_of_three_le (I : Seed.{u} α m) (hm : 3 ≤ m) :
    Nonempty (CompletionBelowFullGrade I) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have hL := lvl_good (I := I) (by omega) j (by omega)
  exact ⟨(hL.next (by omega)).completion hL.hasBotExtension_next (by omega)⟩

end VaughtConjecture.ProfileTower

namespace VaughtConjecture

/-- **Every seed has a completion below the full grade**, at every arity `m`: the completion of
the tower at `m ≤ 2` (`Seed.nonempty_completionBelowFullGrade_of_le_two`), and the levels of
rank-normalized profiles with the top field layer at `m ≥ 3`
(`ProfileTower.nonempty_completionBelowFullGrade_of_three_le`). -/
theorem Seed.nonempty_completionBelowFullGrade {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) :
    Nonempty (CompletionBelowFullGrade I) := by
  rcases le_or_gt m 2 with hm | hm
  · exact I.nonempty_completionBelowFullGrade_of_le_two hm
  · exact ProfileTower.nonempty_completionBelowFullGrade_of_three_le I hm

/-- **The coatom extension property with apex at every stage that is zero or a limit**
(`StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`,
`Seed.nonempty_completionBelowFullGrade`). -/
theorem StageType.hasApexCoatomExtensions {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α) :
    StageType.HasApexCoatomExtensions.{u} α :=
  StageType.HasApexCoatomExtensions.of_completionBelowFullGrade hα
    fun _ _ _ _ _ _ _ _ ↦ Seed.nonempty_completionBelowFullGrade _

end VaughtConjecture
