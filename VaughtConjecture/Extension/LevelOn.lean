/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ProfileTowerCompletion

/-!
# Good levels relative to a family of catalogues

Roadmap, Layer 3, 3.1, (R6), the completion below the full grade with restricted catalogues at the
reading grades: the invariant of the levels of the tower of rank-normalized profiles when the
layers at some grades carry only the profiles of a sub-catalogue.

Let `D : ℕ → Finset (Prof I)` be a family of catalogues, `D k` the profiles that carry a cell of
full scope at the grade `k`.  A level `L` at the grade `g` is **good relative to `D`**
(`ProfileTower.Lvl.GoodOn D L`) when it has every property of a good level
(`ProfileTower.Lvl.Good`) except that its section operator need only be lawful below `(univ, g)`
at the profiles lawful on the grade-`g` cut **whose code at `g` lies in `D g`**
(`ProfileTower.Lvl.GoodOn.lawful`).  After a layer on a sub-catalogue, the section of a profile is
the decoded row labelling of its code, which is a lawful section only when the code has a cell.

* A good level is good relative to every family (`ProfileTower.Lvl.Good.toGoodOn`), and a good
  level is exactly a level good relative to the canonical catalogues
  (`ProfileTower.Lvl.good_iff_goodOn_cat`).  The statements relative to a family in these modules
  specialize, at the canonical catalogues `D = cat I ·` and `C = cat I (g + 1)` (where
  `ProfileTower.Lvl.nextSOn` and `ProfileTower.Lvl.ΦOn` are `ProfileTower.Lvl.nextS` and
  `ProfileTower.Lvl.Φ` by definition), to those of `ProfileTower.Lvl.Good` in
  `VaughtConjecture.Extension.ProfileTower`: for example `ProfileTower.Lvl.GoodOn.isLawfulBelow_ΦOn`
  to `ProfileTower.Lvl.Good.isLawfulBelow_Φ`, and the old-cell statements below to the lemmas of
  the same names for good levels.
* The facts about the old cells of a good level that do not use the section operator hold for a
  level good relative to a family (`ProfileTower.Lvl.GoodOn.gradedIndex_embed`,
  `ProfileTower.Lvl.GoodOn.isLawfulBelow_old_iff`, `ProfileTower.Lvl.GoodOn.cappedLift_old`,
  `ProfileTower.Lvl.GoodOn.mem_range_of_lt`, `ProfileTower.Lvl.GoodOn.mem_below_cover`,
  `ProfileTower.Lvl.GoodOn.grade_lt`).
* The code at `k` of a profile of the catalogue at `k + 1` lies in the catalogue at `k`
  (`ProfileTower.code_mem_cat_of_mem_cat`): the canonical catalogues satisfy the downward clause.

## Placement

The completion below the full grade with admitted rows at the reading grades
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The downward clause for the canonical catalogues**: the code at `k` of a profile of the
catalogue at `k + 1` lies in the catalogue at `k`. -/
theorem code_mem_cat_of_mem_cat {k : ℕ} {R : Prof I} (hR : R ∈ cat I (k + 1)) :
    code k R ∈ cat I k := by
  obtain ⟨⟨hC, hD⟩, -⟩ := mem_cat.mp hR
  have hcut : IsCutLawful I k R := ⟨hC.mono (X := (_, k)) ⟨subset_rfl, by omega⟩,
    hD.mono (X := (_, k)) ⟨subset_rfl, by omega⟩⟩
  obtain ⟨hC', hD'⟩ := isCutLawful_hat hcut
  exact mem_cat.mpr ⟨⟨hC'.orbitCode fun d ↦ d.2.2, hD'.orbitCode fun d ↦ d.2.2⟩,
    orbitCode_orbitCode⟩

/-- The code at `k` of a profile lawful on the grade-`k` cut lies in the catalogue at `k`. -/
theorem code_mem_cat_of_isCutLawful {k : ℕ} {P : Prof I} (hP : IsCutLawful I k P) :
    code k P ∈ cat I k := by
  obtain ⟨hC, hD⟩ := isCutLawful_hat hP
  exact mem_cat.mpr ⟨⟨hC.orbitCode fun d ↦ d.2.2, hD.orbitCode fun d ↦ d.2.2⟩,
    orbitCode_orbitCode⟩

/-- **The orbit code of a profile lawful on the cut lies in the catalogue.** -/
theorem orbitCode_mem_cat_of_isCutLawful {k : ℕ} {P : Prof I} (hP : IsCutLawful I k P) :
    orbitCode k P ∈ cat I k :=
  mem_cat.mpr ⟨⟨hP.1.orbitCode fun d ↦ d.2.2, hP.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩

/-- **A level good relative to a family of catalogues `D`** at the grade `g`: the properties of a
good level (`ProfileTower.Lvl.Good`), with the section operator lawful only at the profiles lawful
on the grade-`g` cut whose code at `g` lies in `D g`. -/
structure Lvl.GoodOn {g : ℕ} (D : ℕ → Finset (Prof I)) (L : Lvl I g) : Prop where
  lowerEmb : I.amalgam.toCellScheme.IsLowerEmbedding L.S.toCellScheme L.embed
  scope_embed : ∀ d, L.S.toCellScheme.scope (L.embed d) = I.amalgam.toCellScheme.scope d
  comap_rows : L.S.rows.comap lowerEmb = I.amalgam.rows
  mem_range : ∀ z, L.S.toCellScheme.scope z ≠ univ → z ∈ Set.range L.embed
  faces : L.S.toCellScheme.faces = I.amalgam.toCellScheme.faces
  wf : L.S.IsWellFormed
  coded : L.S.IsCoded
  consistent : L.S.rows.IsConsistent
  lawful : ∀ P, IsCutLawful I g P → code g P ∈ D g →
    L.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), g) fun z ↦ L.σ P z
  mem : ∀ P : Prof I, (∀ d, P d ∈ codeGrid (g + 1) (bound I)) →
    ∀ z, L.σ P z ∈ codeGrid (g + 1) (bound I)
  literal : ∀ P d, L.σ P (L.embed d) = P d
  capAgree : ∀ P P' : Prof I, (∀ d, P d ∈ codeGrid (g + 1) (bound I)) → ∀ h : Label.{u},
    IsSelfVisible (g + 1) h → IsShort (g + 1) h → (∀ d, min (P d) h = min (P' d) h) →
    ∀ z, min (L.σ P z) h = min (L.σ P' z) h
  readable : ∀ Q : Prof I, orbitCode (g + 1) Q = Q → (∀ d, Q d ∈ codeGrid (g + 1) (bound I)) →
    ∀ z, IsReadableAt (g + 1) Q (L.σ Q z)
  lift : ∀ x ∈ (Pts : Finset (Fin (m + 2))), ∀ j ≤ g,
    L.S.rows.CappedLift (X := (univ.erase x, j)) (Y := ((univ : Finset (Fin (m + 2))), j))
      ⟨erase_subset _ _, le_rfl⟩
  complete : ∀ j, 0 < j → j ≤ g →
    ∃ z, L.S.toCellScheme.gradedIndex z = ((univ : Finset (Fin (m + 2))), j)

section GoodOn

variable {g : ℕ} {L : Lvl I g} {D : ℕ → Finset (Prof I)}

/-- **A good level is good relative to every family of catalogues.** -/
theorem Lvl.Good.toGoodOn (hL : L.Good) (D : ℕ → Finset (Prof I)) : L.GoodOn D where
  lowerEmb := hL.lowerEmb
  scope_embed := hL.scope_embed
  comap_rows := hL.comap_rows
  mem_range := hL.mem_range
  faces := hL.faces
  wf := hL.wf
  coded := hL.coded
  consistent := hL.consistent
  lawful P hP _ := hL.lawful P hP
  mem := hL.mem
  literal := hL.literal
  capAgree := hL.capAgree
  readable := hL.readable
  lift := hL.lift
  complete := hL.complete

/-- **A good level is a level good relative to the canonical catalogues**, and conversely: the code
at `g` of a profile lawful on the grade-`g` cut lies in the catalogue at `g`
(`ProfileTower.code_mem_cat_of_isCutLawful`). -/
theorem Lvl.good_iff_goodOn_cat : L.Good ↔ L.GoodOn fun k ↦ cat I k :=
  ⟨fun h ↦ h.toGoodOn _, fun h ↦
    { h with lawful := fun P hP ↦ h.lawful P hP (code_mem_cat_of_isCutLawful hP) }⟩

theorem Lvl.GoodOn.gradedIndex_embed (hL : L.GoodOn D) (d : Fin I.amalgam.card) :
    L.S.toCellScheme.gradedIndex (L.embed d) = I.amalgam.toCellScheme.gradedIndex d :=
  Prod.ext (hL.scope_embed d) (hL.lowerEmb.grade_eq d)

/-- The amalgam is a source prefix of a level good relative to a family, off the ground set. -/
theorem Lvl.GoodOn.isSourcePrefix (hL : L.GoodOn D) {Y : Finset (Fin (m + 2)) × ℕ}
    (hY : Y.1 ≠ univ) : I.amalgam.toCellScheme.IsSourcePrefix L.S.toCellScheme L.embed Y :=
  ⟨hL.lowerEmb, hL.scope_embed, fun z hz ↦ hL.mem_range z fun he ↦
    hY (univ_subset_iff.mp (he ▸ (hz.1 : L.S.toCellScheme.scope z ⊆ Y.1)))⟩

theorem Lvl.GoodOn.isLawfulBelow_old_iff (hL : L.GoodOn D) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X.1 ≠ univ) {w : Fin L.S.card → Label.{u}} :
    L.S.rows.IsLawfulBelow X (fun z ↦ w z) ↔
      I.amalgam.rows.IsLawfulBelow X (fun d ↦ w (L.embed d)) := by
  have h := hL.isSourcePrefix hX
  rw [← h.isLawfulBelow_iff le_rfl, hL.comap_rows]
  rfl

theorem Lvl.GoodOn.cappedLift_old (hL : L.GoodOn D) {X Y : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ I.amalgam.toCellScheme.gradedFaces) (hY : Y ∈ I.amalgam.toCellScheme.gradedFaces)
    (hY1 : Y.1 ≠ univ) (h : X ≤ Y) : L.S.rows.CappedLift h := by
  have hP := hL.isSourcePrefix hY1
  rw [← hP.cappedLift_iff h le_rfl, hL.comap_rows]
  exact I.isBountiful hX hY h

/-- A cell of a level of grade above `g` is old. -/
theorem Lvl.GoodOn.mem_range_of_lt (hL : L.GoodOn D) {z : Fin L.S.card}
    (hz : g < L.S.toCellScheme.grade z) : z ∈ Set.range L.embed :=
  hL.mem_range z ((L.inv z).resolve_left (by omega))

/-- **The cover of `(univ, g + 1)`** for a level good relative to a family. -/
theorem Lvl.GoodOn.mem_below_cover (hL : L.GoodOn D) {x y : Fin (m + 2)}
    (hx : x ∈ (Pts : Finset _)) (hy : y ∈ (Pts : Finset _)) (hxy : x ≠ y) (z : Fin L.S.card)
    (hz : z ∈ L.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), g + 1)) :
    z ∈ L.S.toCellScheme.below (univ.erase x, g + 1) ∨
      z ∈ L.S.toCellScheme.below (univ, g) ∨ z ∈ L.S.toCellScheme.below (univ.erase y, g + 1) := by
  by_cases hzg : L.S.toCellScheme.grade z ≤ g
  · exact .inr (.inl ⟨subset_univ _, hzg⟩)
  obtain ⟨d, rfl⟩ := hL.mem_range_of_lt (_root_.not_le.mp hzg)
  have hd : I.amalgam.toCellScheme.grade d ≤ g + 1 := by
    have := hz.2
    rwa [hL.gradedIndex_embed] at this
  rcases I.scope_subset_or hx hy hxy d with h | h
  · refine .inl ?_
    rw [CellScheme.mem_below, hL.gradedIndex_embed]; exact ⟨h, hd⟩
  · refine .inr (.inr ?_)
    rw [CellScheme.mem_below, hL.gradedIndex_embed]; exact ⟨h, hd⟩

end GoodOn

/-- Every cell of a level at the grade `m` good relative to a family has grade below `m + 2`. -/
theorem Lvl.GoodOn.grade_lt {L : Lvl I m} {D : ℕ → Finset (Prof I)} (hL : L.GoodOn D)
    (z : Fin L.S.card) : L.S.toCellScheme.grade z < m + 2 := by
  rcases L.inv z with h | h
  · omega
  · obtain ⟨d, rfl⟩ := hL.mem_range z h
    rw [hL.lowerEmb.grade_eq]
    exact I.grade_lt d

end VaughtConjecture.ProfileTower
