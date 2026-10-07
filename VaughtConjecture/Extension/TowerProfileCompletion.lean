/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TowerProfileScheme
import VaughtConjecture.Extension.TwoFaceLift

/-!
# The completion below the full grade at `m = 3`, for every seed

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`).

Let `I` be any seed on five points.  **The completion** (`TowerProfile.completion I`) is the scheme
`TowerProfile.top I`: the tower `T 2` (grades `1`, `2`), the layer of rank-normalized profiles at
the grade `3` whose rows read `T 2` through the tower section (`TowerProfile.scheme`,
`SectionInterface.towerSectionOp`), and the canonical field layer at the grade `4` over it
(`Scheme.fieldLayer`), with the glued labelling extended (`TowerProfile.exists_isLawful_top`).
Every field of `CompletionBelowFullGrade` is proved; compiled in this repository (theorem named):

* the old cells (`TowerProfile.embed4`): a lower embedding keeping scopes and rows, every cell of
  proper scope old, the faces those of the amalgam (`TowerProfile.isLowerEmbedding_embed4`,
  `TowerProfile.comap_rows_embed4`, `TowerProfile.mem_range_embed4`, `TowerProfile.faces_top`);
* **legality below the full grade** (`TowerProfile.isLegalBelowFullGrade_top`): well formed, coded
  and consistent (from `T 2` and the profile layer), complete below the grade `5`
  (`TowerProfile.exists_gradedIndex_eq_top`), and bountiful (`TowerProfile.isBountiful_top`,
  `CellScheme.Rows.isBountiful_of_coatoms`): off the full face the lifts are those of the
  amalgam; from either coatom into the full face, at the grades `j ≤ 2` the invariant of the tower
  from `2FL(1)`, at the grade `3` the lift of the profile layer through the section interface
  (`TowerProfile.cappedLift_three`), and at the grade `4` the one-grade lift with the boundary
  triples of the top step of the tower (`TowerProfile.cappedLift_top_four`): the extension at `⊥`
  (`TowerProfile.extendsFromBoundary_bot_top`) and, at the caps short at `4`, the extension that
  lifts within the other coatom from the grade `3`, the common face carrying no cell of the grade
  `4` (`TowerProfile.extendsFromBoundary_top`, `TowerProfile.exists_isLawfulBelow_four`,
  `Seed.exists_lift_union_of_le`, `Scheme.extendsFromBoundary_fieldLayer_of_fill`).  No bottom apex
  is assumed: the top layer is the canonical field layer, as in the step of the tower to the top
  grade;
* the lawful labelling extending the glued one (`TowerProfile.exists_isLawful_top`): the
  extension at `⊥` from the two coatoms at the grade `4`, every cell lying below `(univ, 4)`.

So **every seed on five points has a completion below the full grade**
(`TowerProfile.nonempty_completionBelowFullGrade`), with no hypothesis on the seed or the stage;
`seedL` among them (`TowerProfile.nonempty_completionBelowFullGrade_seedL`).  With the completion
of the tower at the arities `m ≤ 2`, **the coatom extension property with apex holds at the
arities `m ≤ 3`** at every stage that is zero or a limit
(`StageType.hasApexCoatomExtensions_of_le_three`, via
`CompletionBelowFullGrade.exists_coatomExtension`: legal, literal faces along both coatoms, an
apex).  The arities `m ≥ 4` are treated in
`VaughtConjecture.Extension.ProfileTowerCompletion`.

The construction is not presented as an `OrderedLayer.multiLayerScheme` with a
`Seed.MultiLayerStep`: the scheme is built as a sequence of `Scheme.appendFullCells` layers and
given directly the structure `CompletionBelowFullGrade`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### Extension from the boundary through a field layer, from a fill below it -/

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ)
  {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- **Extension from the boundary through a field layer, from a fill below it.**  Let `U` and `V`
be pairs of grade at most `k` not above `(univ, k)`, and `h` self-visible and short at `k` with
`⊥ < h`.  If, along every catalogue entry `a`, every labelling of `S` lawful below `U` and `V`
that agrees with `a` capped at `h` on their cells is, on those cells, some labelling lawful below
`(univ, k)` agreeing with `a` capped at `h` below `(univ, k)`, then the field layer extends from
the boundary of `U` and `V` at `h` along the row of every new cell
(`Scheme.exists_extension_fieldLayer` at the short cap). -/
theorem extendsFromBoundary_fieldLayer_of_fill {U V : Finset (Fin n) × ℕ}
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hUk : U.2 ≤ k) (hVk : V.2 ≤ k)
    {h : Label.{u}} (hh : IsSelfVisible k h) (hs : IsShort k h) (hbot : ⊥ < h)
    (hfill : ∀ a ∈ S.catalogue k, ∀ w : Fin S.card → Label.{u},
      S.rows.IsLawfulBelow U (fun e ↦ w e) → S.rows.IsLawfulBelow V (fun e ↦ w e) →
      (∀ e, e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V →
        min (w e) h = min (a e) h) →
      ∃ g : Fin S.card → Label.{u}, S.rows.IsLawfulBelow (univ, k) (fun e ↦ g e) ∧
        (∀ e, e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V → g e = w e) ∧
        ∀ e ∈ S.toCellScheme.below (univ, k), min (g e) h = min (a e) h)
    {u : Fin (S.fieldLayer k hS).card}
    (hu : (S.fieldLayer k hS).toCellScheme.gradedIndex u = (univ, k)) :
    (S.fieldLayer k hS).rows.ExtendsFromBoundary U V (univ, k) h
      ((S.fieldLayer k hS).rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨i, rfl⟩ := exists_natAdd_eq (S := S) (k := k) (hS := hS) hu
  set a := S.catalogueEntry k i
  have ha := catalogueEntry_mem (S := S) (k := k) i
  have hrowBelow (d : (S.fieldLayer k hS).toCellScheme.below (univ, k)) :
      (S.fieldLayer k hS).rows.rowBelow (Fin.natAdd _ i) hu d = S.fieldRow k a d.1 :=
    fieldLayer_row_natAdd (hS := hS) i _
  have hw₁U : S.rows.IsLawfulBelow U fun e ↦ w (Fin.castAdd _ e) :=
    (isLawfulBelow_appendFullCells_iff (S := S) (k := k) (h := hS) (v := w) hU).mp hwU
  have hw₁V : S.rows.IsLawfulBelow V fun e ↦ w (Fin.castAdd _ e) :=
    (isLawfulBelow_appendFullCells_iff (S := S) (k := k) (h := hS) (v := w) hV).mp hwV
  have hmem {X : Finset (Fin n) × ℕ} (e : Fin S.card) :
      Fin.castAdd (S.catalogue k).card e ∈ (S.fieldLayer k hS).toCellScheme.below X ↔
        e ∈ S.toCellScheme.below X := by
    rw [CellScheme.mem_below, CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd]
  have hag (e : Fin S.card)
      (he : e ∈ S.toCellScheme.below U ∨ e ∈ S.toCellScheme.below V) :
      min (w (Fin.castAdd _ e)) h = min (a e) h := by
    have hle : S.toCellScheme.grade e ≤ k :=
      he.elim (fun h' ↦ h'.2.trans hUk) fun h' ↦ h'.2.trans hVk
    have := hwS ⟨_, castAdd_mem_below (hS := hS) hle⟩ (he.imp (hmem e).mpr (hmem e).mpr)
    rwa [hrowBelow, fieldRow_castAdd] at this
  obtain ⟨g, hg, hgw, hga⟩ := hfill a ha (fun e ↦ w (Fin.castAdd _ e)) hw₁U hw₁V hag
  obtain ⟨r, hr, hrg, hrS⟩ := exists_extension_fieldLayer (S := S) (k := k) (hS := hS) (p := g) hg
    ha hh hbot (.inl hs) fun d hd ↦ hga d ⟨subset_univ _, hd⟩
  refine ⟨r, hr, fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hrS d⟩
  obtain ⟨e, he, rfl⟩ := exists_castAdd_eq_of_boundary (S := S) (k := k) (hS := hS) hU hV hd
  rw [hrg e he]
  exact hgw e (hd.imp (hmem e).mp (hmem e).mp)

end Scheme

namespace TowerProfile

variable {α : Ordinal.{u}} (I : Seed.{u} α 3)

/-! ### The old cells of the profile layer -/

/-- The old cells of the profile layer over `T 2`: the cells of the amalgam, along the tower and
`Fin.castAdd`. -/
noncomputable def embed3 : Fin I.amalgam.card ↪o Fin (scheme I).card :=
  (I.towerEmbed 2).trans (Fin.castAddOrderEmb (mult I))

variable {I}

@[simp] theorem embed3_apply (d : Fin I.amalgam.card) :
    embed3 I d = Fin.castAdd (mult I) (I.towerEmbed 2 d) := rfl

/-- The old cells form a lower embedding of the amalgam. -/
theorem isLowerEmbedding_embed3 :
    I.amalgam.toCellScheme.IsLowerEmbedding (scheme I).toCellScheme (embed3 I) :=
  (Scheme.isLowerEmbedding_castAdd (S := I.tower 2) 3 (mult I) _ _).comp
    (I.isLowerEmbedding_tower 2)

/-- The rows pull back to those of the amalgam. -/
theorem comap_rows_embed3 :
    (scheme I).rows.comap isLowerEmbedding_embed3 = I.amalgam.rows := by
  have h := Rows.comap_comap (scheme I).rows
    (Scheme.isLowerEmbedding_castAdd (S := I.tower 2) 3 (mult I) _ _)
    (I.isLowerEmbedding_tower 2)
  rw [Scheme.comap_rows_castAdd, I.comap_rows_tower 2] at h
  exact h.symm

/-- The old cells keep their scopes. -/
@[simp] theorem scope_embed3 (d : Fin I.amalgam.card) :
    (scheme I).toCellScheme.scope (embed3 I d) = I.amalgam.toCellScheme.scope d :=
  (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _).trans (I.scope_towerEmbed 2 d)

/-- The old cells keep their graded indices. -/
@[simp] theorem gradedIndex_embed3 (d : Fin I.amalgam.card) :
    (scheme I).toCellScheme.gradedIndex (embed3 I d) = I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (I.gradedIndex_towerEmbed 2 d)

/-- Every cell of scope other than the ground set is old. -/
theorem mem_range_embed3 (z : Fin (scheme I).card)
    (hz : (scheme I).toCellScheme.scope z ≠ univ) : z ∈ Set.range (embed3 I) := by
  induction z using Fin.addCases with
  | right j => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ j) hz
  | left e =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hz
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 2 e hz
    exact ⟨d, rfl⟩

/-- The faces of the profile layer are those of the amalgam. -/
theorem faces_scheme : (scheme I).toCellScheme.faces = I.amalgam.toCellScheme.faces :=
  I.faces_tower 2

/-- **The amalgam is a source prefix of the profile layer** at the pairs off the ground set. -/
theorem isSourcePrefix_embed3 {Y : Finset (Fin 5) × ℕ} (hY : Y.1 ≠ univ) :
    I.amalgam.toCellScheme.IsSourcePrefix (scheme I).toCellScheme (embed3 I) Y :=
  ⟨isLowerEmbedding_embed3, scope_embed3, fun z hz ↦ mem_range_embed3 z fun he ↦
    hY (univ_subset_iff.mp (he ▸ (hz.1 : (scheme I).toCellScheme.scope z ⊆ Y.1)))⟩

/-- **Lawfulness below a pair off the ground set** is lawfulness in the amalgam. -/
theorem isLawfulBelow_scheme_old_iff {X : Finset (Fin 5) × ℕ} (hX : X.1 ≠ univ)
    {g : Fin (scheme I).card → Label.{u}} :
    (scheme I).rows.IsLawfulBelow X (fun z ↦ g z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ g (embed3 I d)) := by
  have h := isSourcePrefix_embed3 (I := I) hX
  rw [← h.isLawfulBelow_iff le_rfl, comap_rows_embed3]
  rfl

/-- **Lifts below a pair off the ground set** are lifts of the amalgam. -/
theorem cappedLift_scheme_old_iff {X Y : Finset (Fin 5) × ℕ} (hXY : X ≤ Y) (hY : Y.1 ≠ univ) :
    (scheme I).rows.CappedLift hXY ↔ I.amalgam.rows.CappedLift hXY := by
  have h := isSourcePrefix_embed3 (I := I) hY
  rw [← h.cappedLift_iff hXY le_rfl, comap_rows_embed3]

/-- A cell of the profile layer of grade above `3` is old. -/
theorem mem_range_embed3_of_lt {z : Fin (scheme I).card}
    (hz : 3 < (scheme I).toCellScheme.grade z) : z ∈ Set.range (embed3 I) := by
  induction z using Fin.addCases with
  | right j =>
    rw [Scheme.appendFullCellsScheme_grade_natAdd] at hz
    omega
  | left e =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd] at hz
    obtain ⟨d, rfl⟩ := I.mem_range_towerEmbed 2 e ((I.tower_grade_le_or 2 e).resolve_left
      (by omega))
    exact ⟨d, rfl⟩

/-- The cells of the profile layer lie above no pair `(univ, 4)`. -/
theorem not_univ_four_le (z : Fin (scheme I).card) :
    ¬ ((univ : Finset (Fin 5)), 4) ≤ (scheme I).toCellScheme.gradedIndex z := by
  rintro ⟨hs, hg⟩
  have hg' : 4 ≤ (scheme I).toCellScheme.grade z := hg
  obtain ⟨d, rfl⟩ := mem_range_embed3_of_lt (I := I) (z := z) (by omega)
  rw [gradedIndex_embed3] at hs
  exact I.scope_ne_univ d (univ_subset_iff.mp hs)

/-- **The cover of `(univ, 4)`**: a cell of the profile layer below `(univ, 4)` lies below one of
the coatoms at the grade `4` or below `(univ, 3)`. -/
theorem mem_below_cover {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y)
    (z : Fin (scheme I).card) (hz : z ∈ (scheme I).toCellScheme.below (univ, 4)) :
    z ∈ (scheme I).toCellScheme.below (univ.erase x, 4) ∨
      z ∈ (scheme I).toCellScheme.below (univ, 3) ∨
        z ∈ (scheme I).toCellScheme.below (univ.erase y, 4) := by
  by_cases hz3 : (scheme I).toCellScheme.grade z ≤ 3
  · exact .inr (.inl ⟨subset_univ _, hz3⟩)
  obtain ⟨d, rfl⟩ := mem_range_embed3_of_lt (I := I) (not_le.mp hz3)
  have hd : I.amalgam.toCellScheme.grade d ≤ 4 := by
    have := hz.2
    rwa [gradedIndex_embed3] at this
  rcases I.scope_subset_or hx hy hxy d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, gradedIndex_embed3]; exact ⟨h, hd⟩
  · refine .inr (.inr ?_)
    rw [CellScheme.mem_below, gradedIndex_embed3]; exact ⟨h, hd⟩

/-! ### The top layer -/

variable (I) in
/-- **The top layer**: the canonical field layer at the grade `4` over the profile layer. -/
noncomputable abbrev top : Scheme.{u} 5 := (scheme I).fieldLayer 4 not_univ_four_le

/-- **The boundary labelling at the grade `4`, completed on the profile layer.**  Let
`C = univ.erase x`, `D = univ.erase y` be the two coatoms, `w` a labelling of the profile layer
lawful below `(C, 4)` and `(univ, 3)`, and `a` a lawful section of it agreeing with `w` capped at
`h` (self-visible at `4`) on the cells below `(C, 4)` or `(univ, 3)`.  Some labelling lawful below
`(univ, 4)` is `w` on those cells and agrees with `a` capped at `h` below `(univ, 4)`: below
`(D, 4)` there are only old cells, where the boundary labelling is lifted within `D` from the grade
`3` (`Seed.exists_lift_union_of_le`: the common face carries no cell of the grade `4`), and the
three pieces are glued (`CellScheme.Rows.IsLawfulBelow.glue₃`, `mem_below_cover`). -/
theorem exists_isLawfulBelow_four {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y)
    {w : Fin (scheme I).card → Label.{u}}
    (hwU : (scheme I).rows.IsLawfulBelow (univ.erase x, 4) fun d ↦ w d)
    (hwV : (scheme I).rows.IsLawfulBelow (univ, 3) fun d ↦ w d)
    {a : Fin (scheme I).card → Label.{u}} (ha : (scheme I).rows.IsLawful a) {h : Label.{u}}
    (hh : IsSelfVisible 4 h)
    (hag : ∀ e, e ∈ (scheme I).toCellScheme.below (univ.erase x, 4) ∨
      e ∈ (scheme I).toCellScheme.below (univ, 3) → min (w e) h = min (a e) h) :
    ∃ g : Fin (scheme I).card → Label.{u},
      (scheme I).rows.IsLawfulBelow (univ, 4) (fun d ↦ g d) ∧
      (∀ e, e ∈ (scheme I).toCellScheme.below (univ.erase x, 4) ∨
        e ∈ (scheme I).toCellScheme.below (univ, 3) → g e = w e) ∧
      ∀ e ∈ (scheme I).toCellScheme.below (univ, 4), min (g e) h = min (a e) h := by
  classical
  have hDne := Seed.ne_univ_erase y
  have hmemD {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ} :
      embed3 I d ∈ (scheme I).toCellScheme.below X ↔ d ∈ I.amalgam.toCellScheme.below X := by
    rw [CellScheme.mem_below, CellScheme.mem_below, gradedIndex_embed3]
  -- The lift within the other coatom, read on the amalgam.
  obtain ⟨v, hv, hvw, hva⟩ := I.exists_lift_union_of_le hx hy hxy (j := 3) le_rfl hh
    (a := fun d ↦ a (embed3 I d))
    ((isLawfulBelow_scheme_old_iff (g := a) hDne).mp (ha.isLawfulBelow _))
    (w := fun d ↦ w (embed3 I d))
    ((isLawfulBelow_scheme_old_iff (g := w) hDne).mp
      (hwV.mono (X := (univ.erase y, 3)) ⟨subset_univ _, le_rfl⟩))
    fun d hd ↦ hag _ (.inr (hmemD.mpr ⟨hd.1.trans (subset_univ _), hd.2⟩))
  -- The lift, carried to the profile layer.
  have P := isSourcePrefix_embed3 (I := I) (Y := (univ.erase y, 4)) hDne
  obtain ⟨v', hv', hv'v⟩ := P.exists_isLawfulBelow le_rfl (s := v)
    (by rw [comap_rows_embed3]; exact hv)
  have hv't (t : I.amalgam.toCellScheme.below (univ.erase y, 4)) :
      v' ⟨embed3 I t, hmemD.mpr t.2⟩ = v t := hv'v t
  have hold (e : Fin (scheme I).card)
      (he : e ∈ (scheme I).toCellScheme.below (univ.erase y, 4)) :
      ∃ t : I.amalgam.toCellScheme.below (univ.erase y, 4), embed3 I t = e := by
    obtain ⟨t, rfl⟩ := mem_range_embed3 e fun hsc ↦ hDne (univ_subset_iff.mp (hsc.ge.trans he.1))
    exact ⟨⟨t, hmemD.mp he⟩, rfl⟩
  obtain ⟨g, hgb, hgo⟩ : ∃ g : Fin (scheme I).card → Label.{u},
      (∀ e, e ∈ (scheme I).toCellScheme.below (univ.erase x, 4) ∨
        e ∈ (scheme I).toCellScheme.below (univ, 3) → g e = w e) ∧
      ∀ e (he : e ∈ (scheme I).toCellScheme.below (univ.erase y, 4)),
        ¬ (e ∈ (scheme I).toCellScheme.below (univ.erase x, 4) ∨
          e ∈ (scheme I).toCellScheme.below (univ, 3)) → g e = v' ⟨e, he⟩ :=
    ⟨fun e ↦ if e ∈ (scheme I).toCellScheme.below (univ.erase x, 4) ∨
        e ∈ (scheme I).toCellScheme.below (univ, 3) then w e
      else Rows.extendBot (univ.erase y, 4) v' e,
      fun e hb ↦ ite_eq_left hb, fun e he hb ↦ (ite_eq_right hb).trans
        (Rows.extendBot_of_mem v' he)⟩
  have hgD (e : Fin (scheme I).card)
      (he : e ∈ (scheme I).toCellScheme.below (univ.erase y, 4)) : g e = v' ⟨e, he⟩ := by
    by_cases hb : e ∈ (scheme I).toCellScheme.below (univ.erase x, 4) ∨
        e ∈ (scheme I).toCellScheme.below (univ, 3)
    · rw [hgb e hb]
      obtain ⟨t, rfl⟩ := hold e he
      rw [hv't t]
      refine (hvw t ?_).symm
      rcases hb with hb | hb
      · exact .inl ⟨subset_inter (hmemD.mp hb).1 t.2.1, t.2.2⟩
      · exact .inr ⟨t.2.1, (hmemD.mp hb).2⟩
    · exact hgo e he hb
  refine ⟨g, Rows.IsLawfulBelow.glue₃ (U := (univ.erase x, 4)) (V := (univ, 3))
    (W := (univ.erase y, 4)) ?_ ?_ ?_ (mem_below_cover hx hy hxy), hgb, fun e he ↦ ?_⟩
  · convert hwU using 1
    exact funext fun e ↦ hgb e (.inl e.2)
  · convert hwV using 1
    exact funext fun e ↦ hgb e (.inr e.2)
  · convert hv' using 1
    exact funext fun e ↦ hgD e e.2
  · rcases mem_below_cover hx hy hxy e he with hb | hb | hb
    · rw [hgb e (.inl hb)]
      exact hag e (.inl hb)
    · rw [hgb e (.inr hb)]
      exact hag e (.inr hb)
    · rw [hgD e hb]
      obtain ⟨t, rfl⟩ := hold e hb
      rw [hv't t]
      exact hva t

/-- **Extension from the boundary at the grade `4`, at a short positive cap**, along the row of
every cell of the top layer: the boundary labelling is completed on the profile layer
(`exists_isLawfulBelow_four`) and extended through the new cells
(`Scheme.extendsFromBoundary_fieldLayer_of_fill`). -/
theorem extendsFromBoundary_top {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y)
    {u : Fin (top I).card} (hu : (top I).toCellScheme.gradedIndex u = (univ, 4)) {h : Label.{u}}
    (hh : IsSelfVisible 4 h) (hs : IsShort 4 h) (hbot : ⊥ < h) :
    (top I).rows.ExtendsFromBoundary (univ.erase x, 4) (univ, 3) (univ, 4) h
      ((top I).rows.rowBelow u hu) :=
  Scheme.extendsFromBoundary_fieldLayer_of_fill (scheme I) 4
    (fun h ↦ Seed.ne_univ_erase x (univ_subset_iff.mp h.1)) (fun h ↦ absurd h.2 (by simp))
    le_rfl (by simp) hh hs hbot
    (fun _ ha _ hwU hwV hag ↦ exists_isLawfulBelow_four hx hy hxy hwU hwV
      (Scheme.mem_catalogue.mp ha).1 hh hag) hu

/-- **Extension at the cap `⊥` through the top layer** from the two coatoms at the grade `4`: the
restriction to the profile layer is extended below `(univ, 3)` (`exists_extension_bot`), glued
with the old cells of the grade `4`, and extended through the top layer
(`Scheme.exists_isLawfulBelow_fieldLayer`). -/
theorem extendsFromBoundary_bot_top {x y : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
    (hy : y ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) (hxy : x ≠ y) :
    (top I).rows.ExtendsFromBoundary (univ.erase x, 4) (univ.erase y, 4) (univ, 4) ⊥
      fun _ ↦ ⊥ := by
  classical
  intro w hwx hwy _
  have hU (z : Fin 5) : ¬ ((univ : Finset (Fin 5)), 4) ≤ (univ.erase z, 4) :=
    fun h ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h.1)
  have hw₁ (z : Fin 5)
      (hwz : (top I).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ w d) :
      (scheme I).rows.IsLawfulBelow (univ.erase z, 4) fun e ↦ w (Fin.castAdd _ e) :=
    (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4)
      (r := fun i ↦ (scheme I).fieldRow 4 ((scheme I).catalogueEntry 4 i))
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
      (w' := fun e ↦ w (Fin.castAdd ((scheme I).catalogue 4).card e)) fun e he ↦ hgw e fun hs ↦
      Seed.ne_univ_erase z (univ_subset_iff.mp (hs.ge.trans he.1))).mpr hwz
  have hg3 : (scheme I).rows.IsLawfulBelow (univ, 3) fun e ↦ g e := by
    convert hr₃ using 1
    exact funext fun e ↦ by rw [hg_def]; exact dite_eq_left e.2
  have hg : (scheme I).rows.IsLawfulBelow (univ, 4) fun e ↦ g e :=
    Rows.IsLawfulBelow.glue₃ (hgz x hwC) hg3 (hgz y hwD) (mem_below_cover hx hy hxy)
  obtain ⟨r, hr, hrg⟩ := Scheme.exists_isLawfulBelow_fieldLayer (S := scheme I) (k := 4)
    (hS := not_univ_four_le) (p := g) hg
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he, rfl⟩ := Scheme.exists_castAdd_eq_of_boundary (S := scheme I) (k := 4)
    (hS := not_univ_four_le) (hU x) (hU y) hd
  rw [hrg e he]
  refine hgw e fun hs ↦ hd.elim (fun h ↦ ?_) fun h ↦ ?_
  · have := h.1
    -- The scope of the old cell `e` in the top layer.
    change (Scheme.appendFullCellsScheme (scheme I) 4 _).scope (Fin.castAdd _ e) ⊆ _ at this
    rw [Scheme.appendFullCellsScheme_scope_castAdd, hs] at this
    exact Seed.ne_univ_erase x (univ_subset_iff.mp this)
  · have := h.1
    -- The scope of the old cell `e` in the top layer.
    change (Scheme.appendFullCellsScheme (scheme I) 4 _).scope (Fin.castAdd _ e) ⊆ _ at this
    rw [Scheme.appendFullCellsScheme_scope_castAdd, hs] at this
    exact Seed.ne_univ_erase y (univ_subset_iff.mp this)

/-! ### The lifts of the top layer -/

/-- The faces of the top layer are those of the amalgam. -/
theorem faces_top : (top I).toCellScheme.faces = I.amalgam.toCellScheme.faces := I.faces_tower 2

/-- The graded faces of the top layer are those of the amalgam. -/
theorem gradedFaces_top :
    (top I).toCellScheme.gradedFaces = I.amalgam.toCellScheme.gradedFaces := by
  unfold CellScheme.gradedFaces
  rw [faces_top]

/-- **Lifts below a pair not above `(univ, 4)`** are those of the profile layer. -/
theorem cappedLift_top_iff {X Y : Finset (Fin 5) × ℕ} (hXY : X ≤ Y)
    (hY : ¬ ((univ : Finset (Fin 5)), 4) ≤ Y) :
    (top I).rows.CappedLift hXY ↔ (scheme I).rows.CappedLift hXY := by
  have h := Scheme.isSourcePrefix_fieldLayer (scheme I) 4 not_univ_four_le hY
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_fieldLayer]

/-- **Lifts between graded faces off the ground set** are lifts of the amalgam. -/
theorem cappedLift_top_old {X Y : Finset (Fin 5) × ℕ} (hX : X ∈ (top I).toCellScheme.gradedFaces)
    (hY : Y ∈ (top I).toCellScheme.gradedFaces) (h : X ≤ Y) (hY1 : Y.1 ≠ univ) :
    (top I).rows.CappedLift h :=
  (cappedLift_top_iff h fun h' ↦ hY1 (univ_subset_iff.mp h'.1)).mpr
    ((cappedLift_scheme_old_iff h hY1).mpr
      (I.isBountiful (gradedFaces_top (I := I) ▸ hX) (gradedFaces_top (I := I) ▸ hY) h))

/-- The two points omitted by the coatoms. -/
private theorem mem_pair_cases {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
    x = Fin.last 4 ∨ x = Fin.castSucc (Fin.last 3) := by
  simpa only [mem_insert, mem_singleton] using hx

/-- **The lifts at the grades `j ≤ 3`**, from either coatom into `(univ, j)`
(`cappedLift_le_two`, `cappedLift_three`). -/
theorem cappedLift_top_le_three {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) {j : ℕ} (hj : j ≤ 3) :
    (top I).rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin 5)), j))
      ⟨erase_subset _ _, le_rfl⟩ := by
  refine (cappedLift_top_iff _ fun h ↦ absurd h.2 (by simp only; omega)).mpr ?_
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · exact cappedLift_le_two hx (by omega)
  rcases mem_pair_cases hx with rfl | rfl
  · exact cappedLift_three (.inl ⟨rfl, rfl⟩)
  · exact cappedLift_three (.inr ⟨rfl, rfl⟩)

/-- The common face of the two coatoms is a face of the amalgam, with three points. -/
private theorem commonFace_props {x y : Fin 5}
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

/-- **The lift at the grade `4`**, from either coatom into `(univ, 4)`, by the one-grade lift
with the boundary triples of the top step of the tower: at `⊥`, the two coatoms and their common
face (`extendsFromBoundary_bot_top`); at the positive caps, `U = (C, 4)`, `V = (univ, 3)`,
`O = (C, 3)`, with the lift at the grade `3` (`cappedLift_top_le_three`) and the extension that
lifts within the other coatom (`extendsFromBoundary_top`). -/
theorem cappedLift_top_four {x : Fin 5}
    (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
    (top I).rows.CappedLift (X := (univ.erase x, 4)) (Y := ((univ : Finset (Fin 5)), 4))
      ⟨erase_subset _ _, le_rfl⟩ := by
  obtain ⟨y, hy, hxy⟩ := Seed.exists_other hx
  obtain ⟨hOf, hOcard⟩ := commonFace_props (I := I) hx hy hxy
  have hcard (z : Fin 5) : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hlift := cappedLift_top_le_three (I := I) hx le_rfl
  have hwf := (Scheme.isWellFormed_fieldLayer (S := scheme I) (k := 4) (hS := not_univ_four_le)
    isWellFormed_scheme (by omega) (by omega)).isWellFormed
  -- A cell at `(univ, 4)`.
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
    (Rows.cappedLift_refl _) ?_ (extendsFromBoundary_bot_top hx hy hxy)
    le_rfl ⟨subset_rfl, by omega⟩ ⟨subset_univ _, le_rfl⟩ ⟨erase_subset _ _, le_rfl⟩
    ⟨subset_rfl, by omega⟩ (fun d hdU hdV ↦ ⟨hdU.1, hdV.2⟩) (Rows.cappedLift_refl _) hlift
    ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩ fun u hu ↦ ?_
  · rw [Scheme.appendFullCellsScheme_gradedIndex_castAdd,
      Scheme.appendFullCellsScheme_gradedIndex_castAdd, hc]
  · -- A cell below both coatoms has grade at most the size of the common face.
    have h1 : (top I).toCellScheme.grade d ≤ #((top I).toCellScheme.scope d) :=
      hwf.grade_le_card d
    have h2 : #((top I).toCellScheme.scope d) ≤ 3 :=
      (card_le_card (subset_inter hdU.1 hdV.1)).trans hOcard.le
    change (top I).toCellScheme.grade d ≤ 3
    omega
  · exact cappedLift_top_old ⟨faces_top (I := I) ▸ hOf, by omega, by rw [hOcard]⟩
      ⟨faces_top (I := I) ▸ I.erase_mem_faces hy, by omega, by rw [hcard]⟩ _
      (Seed.ne_univ_erase y)
  · obtain ⟨i, rfl⟩ := Scheme.exists_natAdd_eq (S := scheme I) (k := 4)
      (hS := not_univ_four_le) hu
    exact ⟨Scheme.isConsistent_fieldLayer (hS := not_univ_four_le) isConsistent_scheme _,
      fun d ↦ (Scheme.isShort_ne_top_row_fieldLayer (hS := not_univ_four_le) i _).1,
      fun d ↦ (Scheme.isShort_ne_top_row_fieldLayer (hS := not_univ_four_le) i _).2,
      fun h hh hs hbot ↦ extendsFromBoundary_top hx hy hxy hu hh hs hbot⟩

/-! ### Legality below the full grade -/

/-- **The top layer is bountiful** (`CellScheme.Rows.isBountiful_of_coatoms`): off the full face
the lifts are those of the amalgam (`cappedLift_top_old`), and from each coatom into the full
face at every grade `j ≤ 4` they are `cappedLift_top_le_three` and `cappedLift_top_four`. -/
theorem isBountiful_top : (top I).rows.IsBountiful := by
  have hcard (z : Fin 5) : #(univ.erase z) = 4 := by
    rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
  have hfull {x : Fin 5} (hx : x ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5)))
      (j : ℕ) (hj : j ≤ #(univ.erase x)) :
      (top I).rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin 5)), j))
        ⟨erase_subset _ _, le_rfl⟩ := by
    rw [hcard] at hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact cappedLift_top_le_three hx (by omega)
    · exact cappedLift_top_four hx
  exact Rows.isBountiful_of_coatoms (A := univ) (a := Fin.last 4)
    (b := Fin.castSucc (Fin.last 3)) (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ I.subset_or_subset B (faces_top (I := I) ▸ hB) hne)
    (faces_top (I := I) ▸ I.erase_last_mem_faces)
    (faces_top (I := I) ▸ I.erase_castSucc_mem_faces)
    (fun X Y hX hY h hYne ↦ cappedLift_top_old hX hY h hYne)
    (hfull (by simp)) (hfull (by simp))

/-- Every cell of the top layer has grade below `5`. -/
theorem grade_top_lt (z : Fin (top I).card) : (top I).toCellScheme.grade z < 5 := by
  induction z using Fin.addCases with
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
  | left z =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    induction z using Fin.addCases with
    | right j => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega
    | left e =>
      rw [Scheme.appendFullCellsScheme_grade_castAdd]
      exact I.grade_tower_lt (by omega) e

/-- **Completeness below the full grade**: every graded face of grade below `5` carries a cell —
an old cell off the ground set, and at `(univ, j)` a cell of the tower (`j ≤ 2`), of the profile
layer (`j = 3`) or of the top layer (`j = 4`). -/
theorem exists_gradedIndex_eq_top (X : Finset (Fin 5) × ℕ)
    (hX : X ∈ (top I).toCellScheme.gradedFaces) (hX2 : X.2 < 5) :
    ∃ d, (top I).toCellScheme.gradedIndex d = X := by
  obtain ⟨B, j⟩ := X
  have hgi (e : Fin (I.tower 2).card) :
      (top I).toCellScheme.gradedIndex (Fin.castAdd _ (Fin.castAdd _ e)) =
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
      exact ⟨Fin.natAdd _ i₀, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ i₀⟩
  · obtain ⟨e, he⟩ := I.exists_gradedIndex_eq_tower 2 (gradedFaces_top (I := I) ▸ hX) hB
    exact ⟨_, (hgi e).trans he⟩

/-- **The top layer is legal below the full grade.** -/
theorem isLegalBelowFullGrade_top : (top I).IsLegalBelowFullGrade where
  isWellFormed := Scheme.isWellFormed_fieldLayer isWellFormed_scheme (by omega) (by omega)
  isCoded := Scheme.isCoded_fieldLayer isCoded_scheme
  isConsistent := Scheme.isConsistent_fieldLayer isConsistent_scheme
  isBountiful := isBountiful_top
  grade_lt := grade_top_lt
  exists_gradedIndex_eq := exists_gradedIndex_eq_top

/-! ### The completion -/

variable (I) in
/-- The old cells of the top layer. -/
noncomputable def embed4 : Fin I.amalgam.card ↪o Fin (top I).card :=
  (embed3 I).trans (Fin.castAddOrderEmb _)

@[simp] theorem embed4_apply (d : Fin I.amalgam.card) :
    embed4 I d = Fin.castAdd _ (embed3 I d) := rfl

/-- The old cells of the top layer form a lower embedding of the amalgam. -/
theorem isLowerEmbedding_embed4 :
    I.amalgam.toCellScheme.IsLowerEmbedding (top I).toCellScheme (embed4 I) :=
  (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le).comp isLowerEmbedding_embed3

/-- The rows of the top layer pull back to those of the amalgam. -/
theorem comap_rows_embed4 : (top I).rows.comap isLowerEmbedding_embed4 = I.amalgam.rows := by
  have h := Rows.comap_comap (top I).rows
    (Scheme.isLowerEmbedding_fieldLayer (scheme I) 4 not_univ_four_le) isLowerEmbedding_embed3
  rw [Scheme.comap_rows_fieldLayer, comap_rows_embed3] at h
  exact h.symm

/-- The old cells of the top layer keep their graded indices. -/
theorem gradedIndex_embed4 (d : Fin I.amalgam.card) :
    (top I).toCellScheme.gradedIndex (embed4 I d) = I.amalgam.toCellScheme.gradedIndex d :=
  (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans (gradedIndex_embed3 d)

/-- Every cell of the top layer of scope other than the ground set is old. -/
theorem mem_range_embed4 (z : Fin (top I).card) (hz : (top I).toCellScheme.scope z ≠ univ) :
    z ∈ Set.range (embed4 I) := by
  induction z using Fin.addCases with
  | right i => exact absurd (Scheme.appendFullCellsScheme_scope_natAdd _ _ _ i) hz
  | left z =>
    rw [Scheme.appendFullCellsScheme_scope_castAdd] at hz
    obtain ⟨d, rfl⟩ := mem_range_embed3 z hz
    exact ⟨d, rfl⟩

/-- **The glued labelling extends to a lawful section of the top layer**, unchanged at the old
cells: the extension at `⊥` from the two coatoms at the grade `4` (`extendsFromBoundary_bot_top`)
of the glued labelling, every cell lying below `(univ, 4)`. -/
theorem exists_isLawful_top :
    ∃ q : Fin (top I).card → Label.{u}, (top I).rows.IsLawful q ∧
      ∀ d, q (embed4 I d) = I.amalgam.label d := by
  classical
  set w : Fin (top I).card → Label.{u} :=
    Function.extend (embed4 I) I.amalgam.label fun _ ↦ ⊥ with hw
  have hwe (d : Fin I.amalgam.card) : w (embed4 I d) = I.amalgam.label d :=
    (embed4 I).injective.extend_apply _ _ d
  have hlaw (z : Fin 5) (hz : z ∈ ({Fin.last 4, Fin.castSucc (Fin.last 3)} : Finset (Fin 5))) :
      (top I).rows.IsLawfulBelow (univ.erase z, 4) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff (S := scheme I) (k := 4)
      (r := fun i ↦ (scheme I).fieldRow 4 ((scheme I).catalogueEntry 4 i))
      (h := not_univ_four_le) (v := w)
      (fun h' ↦ Seed.ne_univ_erase z (univ_subset_iff.mp h'.1))).mpr ?_
    refine (isLawfulBelow_scheme_old_iff (g := fun e ↦ w (Fin.castAdd _ e))
      (Seed.ne_univ_erase z)).mpr ?_
    exact (Rows.isLawfulBelow_congr (R := I.amalgam.rows) (X := (univ.erase z, 4))
      (w := I.amalgam.label) (w' := fun d ↦ w (Fin.castAdd _ (embed3 I d)))
      fun d _ ↦ (hwe d).symm).mp (I.amalgam.isLawful.isLawfulBelow _)
  obtain ⟨r, hr, hrw, -⟩ := extendsFromBoundary_bot_top (I := I) (x := Fin.last 4)
    (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp) (by decide) w
    (hlaw _ (by simp)) (hlaw _ (by simp)) fun _ _ ↦ by simp
  have hall (z : Fin (top I).card) : z ∈ (top I).toCellScheme.below (univ, 4) :=
    ⟨subset_univ _, by have := grade_top_lt z; change (top I).toCellScheme.grade z ≤ 4; omega⟩
  refine ⟨fun z ↦ r ⟨z, hall z⟩, hr.isLawful hall, fun d ↦ ?_⟩
  rw [← hwe d]
  refine hrw ⟨embed4 I d, hall _⟩ ?_
  rcases I.scope_subset_or (x := Fin.last 4) (y := Fin.castSucc (Fin.last 3)) (by simp) (by simp)
    (by decide) d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, gradedIndex_embed4]
    exact ⟨h, by have := (hall (embed4 I d)).2; rwa [gradedIndex_embed4] at this⟩
  · refine .inr ?_
    rw [CellScheme.mem_below, gradedIndex_embed4]
    exact ⟨h, by have := (hall (embed4 I d)).2; rwa [gradedIndex_embed4] at this⟩

variable (I) in
/-- **The completion below the full grade of every seed on five points**: the tower `T 2`, the
layer of rank-normalized profiles at the grade `3` read through the tower section
(`SectionInterface.towerSectionOp`), and the canonical field layer at the grade `4`, with the
glued labelling extended (`exists_isLawful_top`). -/
noncomputable def completion : CompletionBelowFullGrade I where
  scheme := top I
  embed := embed4 I
  isLowerEmbedding := isLowerEmbedding_embed4
  scope_embed d := congrArg Prod.fst (gradedIndex_embed4 d)
  comap_rows := comap_rows_embed4
  mem_range_embed := mem_range_embed4
  faces_eq := faces_top
  isLegalBelowFullGrade := isLegalBelowFullGrade_top
  label := exists_isLawful_top.choose
  isLawful := exists_isLawful_top.choose_spec.1
  label_embed := exists_isLawful_top.choose_spec.2

/-- **Every seed on five points has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade : Nonempty (CompletionBelowFullGrade I) :=
  ⟨completion I⟩

/-- **The test at `seedL`**: the asymmetric seed, where the step of the tower fails
(`TwoFaceLiftExistsCounterexample.not_towerInvariant_three_seedL`), has this completion. -/
theorem nonempty_completionBelowFullGrade_seedL (α : Ordinal.{u}) :
    Nonempty (CompletionBelowFullGrade (TwoFaceLiftExistsCounterexample.seedL α)) ∧
      ¬ (TwoFaceLiftExistsCounterexample.seedL α).TowerInvariant 3 :=
  ⟨nonempty_completionBelowFullGrade,
    TwoFaceLiftExistsCounterexample.not_towerInvariant_three_seedL α⟩

end TowerProfile

/-! ### The coatom extension property with apex up to `m = 3` -/

namespace StageType

/-- **The coatom extension property with apex at the arities `m ≤ 3`**, at every stage that is
zero or a limit: any two legal stage types `ta`, `tb` on `m + 1 ≤ 4` points with the same face
along `Fin.castSuccEmb` are the faces, along `Fin.castSuccEmb` and `extendByLast Fin.castSuccEmb`,
of one legal stage type with a cell of full scope and full grade carrying the largest label.  It
is the statement `StageType.HasApexCoatomExtensions α` restricted to `m ≤ 3`: at `m ≤ 2` through
the completion of the tower (`Seed.nonempty_completionBelowFullGrade_of_le_two`), at `m = 3`
through `TowerProfile.completion`, and in both cases
`CompletionBelowFullGrade.exists_coatomExtension`. -/
theorem hasApexCoatomExtensions_of_le_three {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α)
    (m : ℕ) (hm : m ≤ 3) (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m)
    (hla : ta.IsLegal) (hlb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
    (hpb : restrictFace Fin.castSuccEmb tb = some p) :
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧ restrictFace Fin.castSuccEmb t = some ta ∧
      restrictFace (extendByLast Fin.castSuccEmb) t = some tb ∧
      ∃ d, t.toCellScheme.gradedIndex d = (Finset.univ, m + 2) ∧ ∀ e, t.label e ≤ t.label d := by
  rcases Nat.lt_or_eq_of_le hm with hlt | rfl
  · exact ((Seed.ofCoatoms hla hlb hpa hpb).nonempty_completionBelowFullGrade_of_le_two
      (by omega)).some.exists_coatomExtension hα
  · exact (TowerProfile.completion (Seed.ofCoatoms hla hlb hpa hpb)).exists_coatomExtension hα

end StageType

end VaughtConjecture
