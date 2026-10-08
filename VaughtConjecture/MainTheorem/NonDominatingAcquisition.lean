/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.WorkH4
import VaughtConjecture.Extension.ProfileTowerCross

/-!
# Acquiring a context whose caps dominate no live cell, through a completion

Roadmap, Layer 4 (acquisition) and Layer 3 ((R4) of the table of 3.4).

The donor obstruction (`CapRequests.not_botLiftProvisionOf_donor_of_markerCovers`) is excluded by
a clause on the context, `StageType.CapNonDominating`: no cap of full scope dominates a live cell
of the first coatom at its grade.  The clause depends only on the scheme.  This file acquires it
the way the root bottoms were acquired: the context is a one-point extension, realized by the
saturation clause of a model, whose scheme is the completion of the seed of the type of the
occurrence with itself.  Compiled in this repository (theorem named):

* **The clause on a scheme** (`Scheme.CapNonDominatingAt`): at a point `x` and a cell `c`, every
  cell `a` avoiding `x`, of grade at least that of `c`, reading itself other than `⊥`, is read in a
  block strictly above `c` by some cell of every graded index `(univ, grade a)` of the scheme.
* **Completions dominating no live cell** (`CompletionNonDominating`, a named hypothesis on seeds,
  not on models): every seed has a completion below the full grade whose completion (with the apex)
  satisfies the clause at the last point for every cell of full scope.  It holds in the completion
  of the profile tower (`completionNonDominating_of_tower`) given same-layer separation, which is
  proved (`towerLayerSeparating`), and cross-layer non-domination (`TowerCrossLayer`).
* **Cross-layer non-domination from cross separation** (`towerCrossLayer_of_crossSeparating`):
  under `TowerCrossSeparating` (a live profile of the grade of the cell read differs in bottoms
  from each catalogue profile of the cap's grade at a cell of grade at most the cap's), a reader of
  the higher grade reads the cap through the section of the level below at `⊥`; so
  `CompletionNonDominating` holds conditional on `TowerCrossSeparating`
  (`completionNonDominating_of_crossSeparating`).
* **The margin calibration with a non-dominating cap** (`StageType.GradedCapMarginCalibrationND`):
  the margin calibration with a floor, a last point `x` off the root with `univ.erase x` a face,
  and the clause at `x` for every cell of full scope.
* **The calibration with a floor passes to cofaces**
  (`StageType.GradedCapMarginCalibration'.of_restrictFace`).
* **Acquisition** (`Realization.IsModel.acquiresCalibratedContexts_gradedCapMarginND`): a model
  that is not cover-hollow, with top-grade supremum `⊤`, acquires calibrated contexts for the
  calibration with a non-dominating cap, under `CompletionNonDominating`: acquire the margin
  calibration with a floor at an occurrence `w`; extend `w` by one point (high-arity dominance at
  `0`) to an occurrence of type `q₀`; take the completion of the seed of `q₀` with itself given by
  the hypothesis; realize over the extension a coface of `q₀` on its scheme (saturation).  The
  stable type of the realized tuple has face the stable type of `w` along the first points (the
  calibration passes), its last point is new, and its scheme is that of the completion.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n : ℕ}

/-- **The cell `c` dominates no live cell off the point `x`**: for every cell `a` whose scope
avoids `x`, of grade at least that of `c`, reading itself other than `⊥`, and every cell `G` of
full scope and the grade of `a`, some cell of the graded index of `G` reads `c` in a block strictly
below its reading of `a` (`Label.LowerBlock`). -/
def CapNonDominatingAt (S : Scheme.{u} n) (x : Fin n) (c : Fin S.card) : Prop :=
  ∀ a G : Fin S.card, x ∉ S.toCellScheme.scope a → S.toCellScheme.scope G = univ →
    S.toCellScheme.grade a = S.toCellScheme.grade G →
    S.toCellScheme.grade c ≤ S.toCellScheme.grade a → S.rowAt a a ≠ ⊥ →
      ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex G ∧
        Label.LowerBlock (S.rowAt u c) (S.rowAt u a)

end Scheme

/-- `StageType.CapNonDominating` is the clause on the scheme at the last point. -/
theorem StageType.capNonDominating_iff {α : Ordinal.{u}} {m : ℕ} (Tp : StageType.{u} α (m + 1))
    (b : Fin Tp.card) : Tp.CapNonDominating b ↔ Tp.toScheme.CapNonDominatingAt (Fin.last m) b :=
  Iff.rfl

/-- **Completions dominating no live cell** (a named hypothesis on seeds): every seed on `m + 2`
points has a completion below the full grade whose completion, at every limit stage, satisfies
`Scheme.CapNonDominatingAt` at the last point for every cell of full scope and grade
`3 ≤ g ≤ m`. -/
def CompletionNonDominating : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃m : ℕ⦄ (I : Seed.{u} α m), ∃ F : CompletionBelowFullGrade I,
    ∀ (hα : Order.IsSuccPrelimit α) (c : Fin (F.completion hα).card),
      (F.completion hα).toCellScheme.scope c = univ →
      3 ≤ (F.completion hα).toCellScheme.grade c → (F.completion hα).toCellScheme.grade c ≤ m →
        (F.completion hα).toScheme.CapNonDominatingAt (Fin.last (m + 1)) c

/-! ### `CompletionNonDominating` from the completion of the profile tower -/

namespace Scheme

variable {n : ℕ}

/-- **The cross-layer part of the clause**: `Scheme.CapNonDominatingAt` at the cells `a` of grade
strictly above that of `c`. -/
def CapNonDominatingCrossAt (S : Scheme.{u} n) (x : Fin n) (c : Fin S.card) : Prop :=
  ∀ a G : Fin S.card, x ∉ S.toCellScheme.scope a → S.toCellScheme.scope G = univ →
    S.toCellScheme.grade a = S.toCellScheme.grade G →
    S.toCellScheme.grade c < S.toCellScheme.grade a → S.rowAt a a ≠ ⊥ →
      ∃ u, S.toCellScheme.gradedIndex u = S.toCellScheme.gradedIndex G ∧
        Label.LowerBlock (S.rowAt u c) (S.rowAt u a)

end Scheme

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)

/-- The old cells of a completion keep their rows. -/
theorem rowAt_embed (a b : Fin I.amalgam.card) :
    F.scheme.rowAt (F.embed a) (F.embed b) = I.amalgam.toScheme.rowAt a b := by
  by_cases hb : b ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex a)
  · have hb' : F.embed b ∈ F.scheme.toCellScheme.below
        (F.scheme.toCellScheme.gradedIndex (F.embed a)) := by
      rw [CellScheme.mem_below, F.gradedIndex_embed, F.gradedIndex_embed]
      exact hb
    rw [Scheme.rowAt_of_mem hb', Scheme.rowAt_of_mem hb]
    have h := congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row a ⟨b, hb⟩) F.comap_rows
    exact h
  · have hb' : F.embed b ∉ F.scheme.toCellScheme.below
        (F.scheme.toCellScheme.gradedIndex (F.embed a)) := by
      rw [CellScheme.mem_below, F.gradedIndex_embed, F.gradedIndex_embed]
      exact hb
    rw [Scheme.rowAt_of_notMem hb', Scheme.rowAt_of_notMem hb]

/-- **A cell of the completion avoiding the last point is an old cell**, with the scope, grade and
self-reading of its cell of the amalgam. -/
theorem exists_old_completion (hα : Order.IsSuccPrelimit α) {a : Fin (F.completion hα).card}
    (ha : Fin.last (m + 1) ∉ (F.completion hα).toCellScheme.scope a) :
    ∃ a₀ : Fin I.amalgam.card, a = (F.embed a₀).castSucc ∧
      I.amalgam.toCellScheme.scope a₀ = (F.completion hα).toCellScheme.scope a ∧
      I.amalgam.toCellScheme.grade a₀ = (F.completion hα).toCellScheme.grade a ∧
      I.amalgam.toScheme.rowAt a₀ a₀ = (F.completion hα).toScheme.rowAt a a := by
  change Fin (F.scheme.card + 1) at a
  induction a using Fin.lastCases with
  | last =>
    exfalso
    apply ha
    change Fin.last (m + 1) ∈ (F.scheme.appendFullCellScheme (m + 2)).scope (Fin.last _)
    rw [Scheme.appendFullCellScheme_scope_last]
    exact mem_univ _
  | cast a =>
    have hsc : (F.completion hα).toCellScheme.scope a.castSucc = F.scheme.toCellScheme.scope a :=
      Scheme.appendFullCellScheme_scope_castSucc F.scheme (m + 2) a
    have hgr : (F.completion hα).toCellScheme.grade a.castSucc = F.scheme.toCellScheme.grade a :=
      Scheme.appendFullCellScheme_grade_castSucc F.scheme (m + 2) a
    have hne : F.scheme.toCellScheme.scope a ≠ univ := fun h ↦ ha (by
      rw [hsc, h]; exact mem_univ _)
    obtain ⟨a₀, rfl⟩ := F.mem_range_embed a hne
    refine ⟨a₀, rfl, ?_, ?_, ?_⟩
    · rw [hsc, F.scope_embed]
    · rw [hgr]
      exact (congrArg Prod.snd (F.gradedIndex_embed a₀)).symm
    · have h := Scheme.rowAt_appendFullCell_castSucc (S := (F.truncate hα).toScheme)
        (j := m + 2) (r := StageType.apexRow (t := F.truncate hα) F.isLegalBelowFullGrade)
        (h := F.isLegalBelowFullGrade.not_le) (F.embed a₀) (F.embed a₀)
      exact (h.trans (F.rowAt_embed a₀ a₀)).symm

end CompletionBelowFullGrade

/-- **Layer separation at every grade of every seed of the profile tower** (proved:
`towerLayerSeparating`). -/
def TowerLayerSeparating : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃j : ℕ⦄ (I : Seed.{u} α (j + 3)) (g : ℕ), 3 ≤ g → g ≤ j + 3 →
    ProfileTower.LayerSeparating I g

/-- **Cross-layer non-domination in the completion of the profile tower** (a named hypothesis on
seeds): at every cell of full scope and grade `3 ≤ g ≤ m`, the clause at the cells of higher
grade. -/
def TowerCrossLayer : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃j : ℕ⦄ (I : Seed.{u} α (j + 3)) (hα : Order.IsSuccPrelimit α)
    (c : Fin ((ProfileTower.towerCompletion I).completion hα).card),
    ((ProfileTower.towerCompletion I).completion hα).toCellScheme.scope c = univ →
    3 ≤ ((ProfileTower.towerCompletion I).completion hα).toCellScheme.grade c →
    ((ProfileTower.towerCompletion I).completion hα).toCellScheme.grade c ≤ j + 3 →
      ((ProfileTower.towerCompletion I).completion hα).toScheme.CapNonDominatingCrossAt
        (Fin.last (j + 3 + 1)) c

/-- **Completions dominating no live cell from the profile tower**: the same-layer part of the
clause holds in the completion of the profile tower under layer separation
(`ProfileTower.sameLayerReaders_towerCompletion`), and the cross-layer part is
`TowerCrossLayer`; seeds on fewer than five points have no cells of the grades concerned. -/
theorem completionNonDominating_of_tower (hsep : TowerLayerSeparating.{u})
    (hcross : TowerCrossLayer.{u}) : CompletionNonDominating.{u} := by
  intro α m I
  by_cases hm : 3 ≤ m
  swap
  · obtain ⟨F⟩ := I.nonempty_completionBelowFullGrade
    exact ⟨F, fun _ c _ h3 hcm ↦ absurd (h3.trans hcm) hm⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  refine ⟨ProfileTower.towerCompletion I, fun hα c hc h3 hcm a G ha hG hag hca hlive ↦ ?_⟩
  rcases hca.lt_or_eq with hlt | heq
  · exact hcross I hα c hc h3 hcm a G ha hG hag hlt hlive
  obtain ⟨a₀, rfl, hsc, hgr, hrow⟩ :=
    (ProfileTower.towerCompletion I).exists_old_completion hα ha
  obtain ⟨u, hu, hlb⟩ := ProfileTower.sameLayerReaders_towerCompletion I hα c hc h3 hcm
    (hsep I _ h3 hcm) a₀ (hgr.trans heq.symm) (by rw [hrow]; exact hlive)
    (by rw [hsc]; exact ha)
  refine ⟨u, ?_, hlb⟩
  rw [hu]
  have hGs : ((ProfileTower.towerCompletion I).completion hα).toCellScheme.gradedIndex G =
      ((univ : Finset (Fin (j + 3 + 2))),
        ((ProfileTower.towerCompletion I).completion hα).toCellScheme.grade G) := Prod.ext hG rfl
  rw [hGs, ← hag, ← hgr, hgr, heq]

/-- **Layer separation holds at every grade of every seed of the profile tower**
(`ProfileTower.layerSeparating`). -/
theorem towerLayerSeparating : TowerLayerSeparating.{u} := fun _ _ I _ _ hg ↦
  ProfileTower.layerSeparating I (by omega) hg

/-- **Completions dominating no live cell from cross-layer non-domination**: the same-layer part
holds in the completion of the profile tower (`towerLayerSeparating`). -/
theorem completionNonDominating_of_crossLayer (hcross : TowerCrossLayer.{u}) :
    CompletionNonDominating.{u} :=
  completionNonDominating_of_tower towerLayerSeparating hcross

/-- **Cross separation at every pair of grades of every seed of the profile tower** (a named
condition on the catalogues, `ProfileTower.CrossSeparating`). -/
def TowerCrossSeparating : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃j : ℕ⦄ (I : Seed.{u} α (j + 3)) (N k : ℕ), 3 ≤ N → N < k →
    k ≤ j + 3 + 1 → ProfileTower.CrossSeparating I N k

/-- A cell of the completion of the profile tower of grade at most `m` is a cell of the last
level. -/
theorem exists_lvl_cell_towerCompletion {α : Ordinal.{u}} {j : ℕ} (I : Seed.{u} α (j + 3))
    (hα : Order.IsSuccPrelimit α) (c : Fin ((ProfileTower.towerCompletion I).completion hα).card)
    (hc : ((ProfileTower.towerCompletion I).completion hα).toCellScheme.grade c ≤ j + 3) :
    ∃ c₂ : Fin (ProfileTower.lvl I (j + 1)).S.card,
      c = (Fin.castAdd ((ProfileTower.lvl I (j + 1)).S.catalogue (j + 3 + 1)).card
        c₂).castSucc := by
  change Fin (((ProfileTower.towerCompletion I).truncate hα).card + 1) at c
  induction c using Fin.lastCases with
  | last =>
    exfalso
    have h := Scheme.appendFullCellScheme_grade_last
      ((ProfileTower.towerCompletion I).truncate hα).toScheme (j + 3 + 2)
    change ((ProfileTower.towerCompletion I).completion hα).toCellScheme.grade (Fin.last _) =
      j + 3 + 2 at h
    omega
  | cast c₁ =>
    have hg := Scheme.appendFullCellScheme_grade_castSucc
      ((ProfileTower.towerCompletion I).truncate hα).toScheme (j + 3 + 2) c₁
    change ((ProfileTower.towerCompletion I).completion hα).toCellScheme.grade c₁.castSucc =
      (ProfileTower.lvl I (j + 1)).top.toCellScheme.grade c₁ at hg
    rw [hg] at hc
    change Fin ((ProfileTower.lvl I (j + 1)).S.card +
      ((ProfileTower.lvl I (j + 1)).S.catalogue (j + 3 + 1)).card) at c₁
    induction c₁ using Fin.addCases with
    | left c₂ => exact ⟨c₂, rfl⟩
    | right i =>
      exfalso
      have h2 : (ProfileTower.lvl I (j + 1)).top.toCellScheme.grade (Fin.natAdd _ i) =
          j + 3 + 1 := Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i
      omega

/-- **Cross-layer non-domination in the completion of the profile tower from cross separation**:
the readers of the grades up to `m` are those of the levels (`ProfileTower.crossLayerReaders_lvl`),
those of the grade `m + 1` those of the field layer (`ProfileTower.topCrossReaders_lvl`). -/
theorem towerCrossLayer_of_crossSeparating (h : TowerCrossSeparating.{u}) :
    TowerCrossLayer.{u} := by
  intro α j I hα c hc h3 hcm a G ha hG hag hlt hlive
  obtain ⟨a₀, rfl, hsc, hgr, hrow⟩ := (ProfileTower.towerCompletion I).exists_old_completion hα ha
  obtain ⟨c₂, rfl⟩ := exists_lvl_cell_towerCompletion I hα c hcm
  have hgc : ((ProfileTower.towerCompletion I).completion hα).toCellScheme.grade
      (Fin.castAdd ((ProfileTower.lvl I (j + 1)).S.catalogue (j + 3 + 1)).card c₂).castSucc =
      (ProfileTower.lvl I (j + 1)).S.toCellScheme.grade c₂ :=
    (Scheme.appendFullCellScheme_grade_castSucc _ _ _).trans
      (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _)
  have hscc : ((ProfileTower.towerCompletion I).completion hα).toCellScheme.scope
      (Fin.castAdd ((ProfileTower.lvl I (j + 1)).S.catalogue (j + 3 + 1)).card c₂).castSucc =
      (ProfileTower.lvl I (j + 1)).S.toCellScheme.scope c₂ :=
    (Scheme.appendFullCellScheme_scope_castSucc _ _ _).trans
      (Scheme.appendFullCellsScheme_scope_castAdd _ _ _ _)
  rw [hgc] at h3 hcm hlt
  rw [hscc] at hc
  rw [← hgr] at hlt
  have hlive₀ : I.amalgam.toScheme.rowAt a₀ a₀ ≠ ⊥ := by rw [hrow]; exact hlive
  have hlast₀ : Fin.last (j + 3 + 1) ∉ I.amalgam.toCellScheme.scope a₀ := by rw [hsc]; exact ha
  have hGs : ((ProfileTower.towerCompletion I).completion hα).toCellScheme.gradedIndex G =
      ((univ : Finset (Fin (j + 3 + 2))), I.amalgam.toCellScheme.grade a₀) :=
    Prod.ext hG (hag.symm.trans hgr.symm)
  have ha₀m : I.amalgam.toCellScheme.grade a₀ ≤ j + 3 + 1 := by
    have h1 := I.amalgam.isWellFormed.isWellFormed.grade_le_card a₀
    have h2 : #(I.amalgam.toCellScheme.scope a₀) ≤ #((univ : Finset (Fin (j + 3 + 2))).erase
        (Fin.last (j + 3 + 1))) := card_le_card fun y hy ↦
      mem_erase.mpr ⟨fun h ↦ hlast₀ (h ▸ hy), mem_univ _⟩
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
    omega
  have hsep := h I _ _ h3 hlt ha₀m
  -- the rows of the completion at the cells of the top layer
  have hrowc (u x : Fin (ProfileTower.lvl I (j + 1)).top.card) :
      ((ProfileTower.towerCompletion I).completion hα).toScheme.rowAt u.castSucc x.castSucc =
        (ProfileTower.lvl I (j + 1)).top.rowAt u x :=
    Scheme.rowAt_appendFullCell_castSucc
      (S := ((ProfileTower.towerCompletion I).truncate hα).toScheme) (j := j + 3 + 2)
      (r := StageType.apexRow (t := (ProfileTower.towerCompletion I).truncate hα)
        (ProfileTower.towerCompletion I).isLegalBelowFullGrade)
      (h := (ProfileTower.towerCompletion I).isLegalBelowFullGrade.not_le) u x
  have hgiu (u : Fin (ProfileTower.lvl I (j + 1)).top.card) :
      ((ProfileTower.towerCompletion I).completion hα).toCellScheme.gradedIndex u.castSucc =
        (ProfileTower.lvl I (j + 1)).top.toCellScheme.gradedIndex u :=
    Scheme.appendFullCellScheme_gradedIndex_castSucc _ _ _
  rcases Nat.lt_or_ge (I.amalgam.toCellScheme.grade a₀) (j + 3 + 1) with hlt' | hge
  · obtain ⟨u, hu, hlb⟩ := ProfileTower.crossLayerReaders_lvl (I := I) (by omega) (j + 1)
      (by omega) c₂ hc h3 a₀ hlt (by omega) hlive₀ hlast₀ hsep
    set M := ((ProfileTower.lvl I (j + 1)).S.catalogue (j + 3 + 1)).card
    have hgi' : ((ProfileTower.towerCompletion I).completion hα).toCellScheme.gradedIndex
        (Fin.castAdd M u).castSucc =
        ((ProfileTower.towerCompletion I).completion hα).toCellScheme.gradedIndex G :=
      (hgiu (Fin.castAdd M u)).trans
        ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ u).trans (hu.trans hGs.symm))
    have key : LowerBlock
        (((ProfileTower.towerCompletion I).completion hα).toScheme.rowAt
          (Fin.castAdd M u).castSucc (Fin.castAdd M c₂).castSucc)
        (((ProfileTower.towerCompletion I).completion hα).toScheme.rowAt
          (Fin.castAdd M u).castSucc
          (Fin.castAdd M ((ProfileTower.lvl I (j + 1)).embed a₀)).castSucc) := by
      rw [hrowc, hrowc, ProfileTower.Lvl.top_rowAt_castAdd,
        ProfileTower.Lvl.top_rowAt_castAdd]
      exact hlb
    exact ⟨(Fin.castAdd M u).castSucc, hgi', key⟩
  · have ha₀ : I.amalgam.toCellScheme.grade a₀ = j + 3 + 1 := by omega
    rw [ha₀] at hsep
    obtain ⟨u, hu, hlb⟩ := ProfileTower.topCrossReaders_lvl I c₂ hc h3 hcm a₀ ha₀ hlive₀ hlast₀
      hsep
    have hgi' : ((ProfileTower.towerCompletion I).completion hα).toCellScheme.gradedIndex
        u.castSucc = ((ProfileTower.towerCompletion I).completion hα).toCellScheme.gradedIndex G :=
      (hgiu u).trans (hu.trans (by rw [hGs, ha₀]))
    have key : LowerBlock
        (((ProfileTower.towerCompletion I).completion hα).toScheme.rowAt u.castSucc
          (Fin.castAdd ((ProfileTower.lvl I (j + 1)).S.catalogue (j + 3 + 1)).card c₂).castSucc)
        (((ProfileTower.towerCompletion I).completion hα).toScheme.rowAt u.castSucc
          ((ProfileTower.lvl I (j + 1)).topEmbed a₀).castSucc) := by
      rw [hrowc, hrowc]
      exact hlb
    exact ⟨u.castSucc, hgi', key⟩

/-- **Completions dominating no live cell from cross separation.** -/
theorem completionNonDominating_of_crossSeparating (h : TowerCrossSeparating.{u}) :
    CompletionNonDominating.{u} :=
  completionNonDominating_of_tower towerLayerSeparating (towerCrossLayer_of_crossSeparating h)

namespace StageType

variable {ξ : Ordinal.{u}}

variable (ξ) in
/-- **The margin calibration with a non-dominating cap**: the margin calibration with a floor
(`StageType.GradedCapMarginCalibration'`), a last point `x` off the root whose complement is a
face, and no cell of full scope and grade `3 ≤ g ≤ m - 2` dominating a live cell off `x`. -/
def GradedCapMarginCalibrationND ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m)
    (f : Fin k ↪ Fin m) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) :
    Prop :=
  GradedCapMarginCalibration' ξ Tp f D γ ∧
    ∃ x : Fin m, (x : ℕ) + 1 = m ∧ (∀ i, f i ≠ x) ∧ univ.erase x ∈ Tp.toCellScheme.faces ∧
      ∀ c : Fin Tp.card, Tp.toCellScheme.scope c = univ → 3 ≤ Tp.toCellScheme.grade c →
        Tp.toCellScheme.grade c + 2 ≤ m → Tp.toScheme.CapNonDominatingAt x c

/-- **The margin calibration with a floor passes to cofaces**: if `T` has face `W` along `e`, the
calibration of `W` along `f` is that of `T` along `f.trans e` (the cells of `W` are cells of `T`
with their labels and grades, and the cells visible through `f.trans e` are those of `W` visible
through `f`). -/
theorem GradedCapMarginCalibration'.of_restrictFace {m n k : ℕ}
    {T : StageType.{u} (blockStage (ξ + 1)) n} {W : StageType.{u} (blockStage (ξ + 1)) m}
    {e : Fin m ↪ Fin n} (he : restrictFace e T = some W) {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}}
    (h : GradedCapMarginCalibration' ξ W f D γ) :
    GradedCapMarginCalibration' ξ T (f.trans e) D γ := by
  obtain ⟨b, hb, hk, h3, ⟨R, hR, hγ⟩, ⟨a, i, hi, ha, hal⟩, href, hoff⟩ := h
  have hg (z : Fin W.card) := grade_faceCell he z
  have hl (z : Fin W.card) := label_faceCell he z
  refine ⟨faceCell he b, by rw [hg, hl]; exact hb, by rw [hg]; exact hk, by rw [hg]; exact h3,
    ⟨R, by rw [hg]; exact hR, hγ⟩, ⟨faceCell he a, i, by rw [hg]; exact hi,
      by rw [hg, hg]; exact ha, by rw [hl]; exact hal⟩, fun j o ho ↦ ?_, fun y hy μ f' hμ hyl ↦ ?_⟩
  · obtain ⟨μ, n', i', c, hμ, ho', hn, hi', hc, hcl⟩ := href j o ho
    exact ⟨μ, n', i', faceCell he c, hμ, ho', by rw [hg]; exact hn, by rw [hg]; exact hi',
      by rw [hg, hg]; exact hc, by rw [hl]; exact hcl⟩
  · -- a cell visible through `f.trans e` is a cell of `W` visible through `f`
    have hye : y ∈ T.visibleCells e := by
      rw [Scheme.mem_visibleCells] at hy ⊢
      intro z hz
      obtain ⟨w, hw⟩ := hy hz
      exact ⟨f w, hw⟩
    have hfc : ∃ y', faceCell he y' = y :=
      T.toScheme.exists_faceCell_eq (comap_toScheme_of_restrictFace he) hye
    obtain ⟨y', rfl⟩ := hfc
    have hy' : y' ∈ W.visibleCells f := by
      rw [Scheme.mem_visibleCells] at hy ⊢
      intro z hz
      have hz' : e z ∈ (T.toCellScheme.scope (faceCell he y') : Set (Fin n)) := by
        rw [scope_faceCell]
        exact mem_coe.mpr (mem_map_of_mem _ (mem_coe.mp hz))
      obtain ⟨w, hw⟩ := hy hz'
      exact ⟨w, e.injective hw⟩
    rw [hg]
    exact hoff y' hy' μ f' hμ (by rw [← hl]; exact hyl)

end StageType

namespace StageType

variable {ξ : Ordinal.{u}}

/-- **An embedding avoiding the last point factors through the first points.** -/
theorem exists_trans_castSuccEmb {k m : ℕ} (f : Fin k ↪ Fin (m + 1))
    (hf : ∀ i, f i ≠ Fin.last m) : ∃ f' : Fin k ↪ Fin m, f'.trans Fin.castSuccEmb = f :=
  ⟨⟨fun i ↦ (f i).castPred (hf i), fun i j hij ↦ f.injective (by
      have := congrArg Fin.castSucc hij
      simpa using this)⟩, Function.Embedding.ext fun i ↦ Fin.castSucc_castPred (f i) (hf i)⟩

/-- **Cutoff stable recovery for the calibration with a non-dominating cap from first-coatom
completions with a chosen coface**: the root avoids the last point, whose complement is a face, so
the input is an input at the first coatom; no relabelling is needed. -/
theorem HasCutoffFirstCoatomCompletionsEx.hasCutoffStableRecoverySchemes_nd
    (h : HasCutoffFirstCoatomCompletionsEx ξ (GradedCapMarginCalibrationND ξ)) :
    HasCutoffStableRecoverySchemes ξ (GradedCapMarginCalibrationND ξ) := by
  intro m k Tp f P hT hk hP D hD γ hγ hC
  obtain ⟨-, x, hx, hfx, hxf, -⟩ := id hC
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain rfl : x = Fin.last m' := Fin.ext (by simp; omega)
  obtain ⟨f', rfl⟩ := exists_trans_castSuccEmb f hfx
  have hmem : univ.map (Fin.castSuccEmb : Fin m' ↪ Fin (m' + 1)) ∈ Tp.toCellScheme.faces := by
    convert hxf using 1
    ext y
    induction y using Fin.lastCases with
    | last => simp
    | cast y => simp [Fin.castSucc_ne_last]
  have hTp : restrictFace Fin.castSuccEmb Tp = some (Tp.comap Fin.castSuccEmb hmem) :=
    restrictFace_of_mem Tp _ hmem
  have hpP : restrictFace f' (Tp.comap Fin.castSuccEmb hmem) = some P :=
    (restrictFace_trans Tp Fin.castSuccEmb f' hTp).trans hP
  obtain ⟨-, -, -, q, δ, -, hq⟩ := h Tp _ f' P hT hTp hk hpP D hD γ hγ hC
  exact ⟨q, δ, hq⟩

/-- **First-coatom completions with a chosen coface for the calibration with a non-dominating cap,
from the fills** (the statement of `StageType.hasCutoffFirstCoatomCompletionsEx'_of_fills` with the
clause `StageType.CapNonDominating` available to the fills). -/
theorem hasCutoffFirstCoatomCompletionsEx_nd_of_fills
    (h : ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1))
      (p : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
      (P : StageType.{u} (blockStage (ξ + 1)) k) (hT : Tp.IsLegal)
      (hp : restrictFace Fin.castSuccEmb Tp = some p), 0 < k →
      ∀ (hP : restrictFace f p = some P) (D : StageType.{u} (blockStage (ξ + 1)) (k + 1))
        (hD : D ∈ P.cofaces) (γ : Ordinal.{u}), γ < blockStage (ξ + 1) →
      GradedCapMarginCalibrationND ξ Tp (f.trans Fin.castSuccEmb) D γ →
      ∃ (tb : StageType.{u} (blockStage (ξ + 1)) (m + 1)) (htb : tb ∈ p.cofaces)
        (htbD : restrictFace (extendByLast f) tb = some D)
        (c : FloorCapData Tp (f.trans Fin.castSuccEmb) D γ),
        (⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩ : FirstCoatomInput.{u} ξ m k).HasFills
          c.toMarginCapData) :
    HasCutoffFirstCoatomCompletionsEx ξ (GradedCapMarginCalibrationND ξ) := by
  intro m k Tp p f P hT hp hk hP D hD γ hγ hC
  obtain ⟨tb, htb, htbD, c, hc⟩ := h Tp p f P hT hp hk hP D hD γ hγ hC
  let X : FirstCoatomInput.{u} ξ m k := ⟨Tp, p, tb, f, P, D, hT, hp, htb, hP, hD, htbD⟩
  exact ⟨tb, htb, htbD, X.exists_isCutoffStableRecovery' c.toMarginCapData c.three_le
    (fun k' h₁ h₂ ↦ (hc k' h₁ h₂).1) (fun k' h₁ h₂ ↦ (hc k' h₁ h₂).2.1)
    fun k' h₁ h₂ ↦ (hc k' h₁ h₂).2.2⟩

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Acquisition of the margin calibration with a non-dominating cap**, under
`CompletionNonDominating`, for a model `R` at `λ_ξ` that is not cover-hollow and has top-grade
supremum `⊤`. -/
theorem IsModel.acquiresCalibratedContexts_gradedCapMarginND (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    (hND : CompletionNonDominating.{u}) :
    AcquiresCalibratedContexts ξ (StageType.GradedCapMarginCalibrationND ξ) R
      hR.isStablyLawful := by
  intro x hx D hD γ hγ
  have hβ := isSuccLimit_blockStage ξ
  obtain ⟨w, f, hf, hC⟩ := hR.acquiresCalibratedContexts_gradedCapMargin' hnh hgrow x hx D hD γ hγ
  -- one point more, by high-arity dominance at `0`
  obtain ⟨u, hu, q₀, ⟨⟨hq₀l, hq₀f⟩, -⟩, he₀⟩ :=
    (hR.dominance w 0 hβ.bot_lt).inter_cofaces hR.isConsistent hR.isLegal
  set Z₁ : R.Occurrence := ⟨w.arity + 1, u, q₀, he₀⟩
  -- the completion of the seed of `q₀` with itself
  obtain ⟨F, hF⟩ := hND (Seed.ofCoatoms hq₀l hq₀l hq₀f hq₀f)
  set qs := F.completion hβ.isSuccPrelimit
  have hqs : qs ∈ q₀.cofaces :=
    ⟨F.isLegal_completion _, F.restrictFace_left_completion hβ.isSuccPrelimit⟩
  have hne : (Z₁.type.cofaces ∩ StageType.saturationFamily qs.toScheme).Nonempty := ⟨qs, hqs, rfl⟩
  obtain ⟨v, hv, q, ⟨⟨-, hqf⟩, hqS⟩, hev⟩ :=
    (hR.saturation Z₁ qs.toScheme hne).inter_cofaces hR.isConsistent hR.isLegal
  set V : R.Occurrence := ⟨w.arity + 2, v, q, hev⟩
  set g : Fin w.arity ↪ Fin (w.arity + 2) := Fin.castSuccEmb.trans Fin.castSuccEmb
  have hgv : g.trans v = w.tuple := by
    rw [Function.Embedding.trans_assoc, hv]
    exact hu
  -- the stable type of `V` has face the stable type of `w` along the first points
  have hface : StageType.restrictFace g
      (R.stableType hR.isStablyLawful v q hev) =
        some (R.stableType hR.isStablyLawful w.tuple w.type w.eval_tuple) := by
    rw [← isConsistent_stableCandidate hR.isConsistent hR.isCovering v _ g
      (stableCandidate_eval_of_eval hev), hgv]
    exact stableCandidate_eval_of_eval w.eval_tuple
  refine ⟨V, f.trans g, ?_, hC.of_restrictFace hface, Fin.last _, rfl, fun i ↦ ?_, ?_, ?_⟩
  · rw [Function.Embedding.trans_assoc, hgv, hf]
  · simp only [g, Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
    exact Fin.castSucc_ne_last _
  · -- the first points span a face: the face of `q` along the first points is the type of `Z₁`
    have h := ((StageType.restrictFace_eq_some_iff q Fin.castSuccEmb).mp hqf).1
    change univ.erase (Fin.last (w.arity + 1)) ∈ q.toCellScheme.faces
    convert h using 1
    exact (Coatom.univ_map_left (m := w.arity)).symm
  · -- the clause holds on the scheme of the completion
    have key : ∀ S : Scheme.{u} (w.arity + 2), S = qs.toScheme → ∀ c : Fin S.card,
        S.toCellScheme.scope c = univ → 3 ≤ S.toCellScheme.grade c →
        S.toCellScheme.grade c + 2 ≤ w.arity + 2 → S.CapNonDominatingAt (Fin.last _) c := by
      rintro S rfl c hc h3 hcm
      exact hF hβ.isSuccPrelimit c hc h3 (by change qs.toCellScheme.grade c ≤ w.arity; omega)
    exact key _ hqS
end Realization

end VaughtConjecture
