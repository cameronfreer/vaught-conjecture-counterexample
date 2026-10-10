/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplaySeparator

/-!
# The actual labelling of the completed display

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the reading of the
display); semantic contract, items 3, 4 and 8.

Let `I` be the seed of a LOW family at `K = g + 1 ≤ m`, `L` a good level at `g` whose LOW layer is
a good level, and `N` the level at the grade `m` above it.  When every glued label of grade in
`(K, m]` is `⊥` (no condition when `K = m`), the reading of the completed display holds
(`ProfileTower.lowReading_of_bot`, compiled in this repository), so the converse of
`ProfileTower.LowReading.face_label_eq_bot` holds: for the completed display, the reading holds
exactly when the two faces are `⊥` above `K`.

**The actual labels** (`ProfileTower.actualLabels`).  At the cells of `N` of grade at most `K`,
the upper decoder of the glued labels (`ProfileTower.sepDecoder`) applied to the row of the
controller `u` of the actual profile (`ProfileTower.sepHi`); at the other old cells, the glued
labels; `⊥` elsewhere.  They are lawful (`ProfileTower.isLawful_actualLabels`): below `(univ, K)`
the decoded row of `u` is lawful (consistency, and the decoder is a witness bounded by `K`); with
`⊥` above `K` it is lawful below `(univ, m)` (`CellScheme.Rows.isLawfulBelow_extendAbove`), and it
agrees there with the actual labels by the hypothesis on the glued labels; below the two coatoms
at `m + 1` they are the glued labels, lawful in the amalgam; the three pieces cover the level
(`ProfileTower.Lvl.Good.mem_below_cover`) and glue (`CellScheme.Rows.IsLawfulBelow.glue₃`).  The
decoded row reads the old cells of grade at most `K` as the glued labels (the controller reads
them through the section of `L`, literal, at the code of the glued labels, which the decoder reads
back), the controller `u` as `⊤` (the ceiling of the grid, `ProfileTower.sepDecoder_ceiling`),
and the controller of the partner at the cutoff cut, below the stage
(`ProfileTower.sepDecoder_cutoffCut_lt`).

**The reading** (`ProfileTower.lowReading_of_bot`).  The actual labels extend through the top
layer (`Scheme.exists_isLawful_fieldLayer`) and are reduced to the stage, which keeps the glued
labels, the `⊤` at `u`, and the label of the partner's controller, below the stage.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-! ### The glued labels from the two faces -/

/-- **Every cell of the amalgam is a cell of one of the two faces.** -/
theorem exists_faceCell_left_or_right (d : Fin I.amalgam.card) :
    (∃ x, StageType.faceCell I.restrictFace_left x = d) ∨
      ∃ x, StageType.faceCell I.restrictFace_right x = d := by
  rcases I.scope_subset_or (x := Fin.last (m + 1)) (y := Fin.castSucc (Fin.last m)) (by simp)
    (by simp) Seed.last_ne_castSucc d with h | h
  · refine .inl (I.amalgam.toScheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_left)
      (Scheme.mem_visibleCells.mpr fun y hy ↦ ?_))
    obtain ⟨a, -, rfl⟩ := mem_map.mp (Coatom.univ_map_left.symm ▸ h hy :
      y ∈ univ.map (Coatom.left m))
    exact ⟨a, rfl⟩
  · refine .inr (I.amalgam.toScheme.exists_faceCell_eq
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_right)
      (Scheme.mem_visibleCells.mpr fun y hy ↦ ?_))
    obtain ⟨a, -, rfl⟩ := mem_map.mp (Coatom.univ_map_right.symm ▸ h hy :
      y ∈ univ.map (Coatom.right m))
    exact ⟨a, rfl⟩

/-- **The glued labels are `⊥` in a range of grades when the two faces are.** -/
theorem amalgam_label_eq_bot {K M : ℕ}
    (hl : ∀ x, K < I.left.toCellScheme.grade x → I.left.toCellScheme.grade x ≤ M →
      I.left.label x = ⊥)
    (hr : ∀ x, K < I.right.toCellScheme.grade x → I.right.toCellScheme.grade x ≤ M →
      I.right.label x = ⊥) (d : Fin I.amalgam.card) (hK : K < I.amalgam.toCellScheme.grade d)
    (hM : I.amalgam.toCellScheme.grade d ≤ M) : I.amalgam.label d = ⊥ := by
  rcases exists_faceCell_left_or_right d with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [StageType.grade_faceCell] at hK hM
    rw [StageType.label_faceCell]
    exact hl x hK hM
  · rw [StageType.grade_faceCell] at hK hM
    rw [StageType.label_faceCell]
    exact hr x hK hM

/-! ### The actual labels of the level at `m` -/

section Actual

variable (θ : Label.{u} → Label.{u}) (G : ℕ) (N : Lvl I m) (u : Fin N.S.card)

open Classical in
/-- The **decoded labels** of the level `N` at the grade `m` for a cell `u` of grade `G` and a map
`θ`: the image under `θ` of the row of `u` at the cells of grade at most `G`, the glued labels at
the other old cells, `⊥` elsewhere. -/
noncomputable def decodedLabels : Fin N.S.card → Label.{u} := fun z ↦
  if N.S.toCellScheme.grade z ≤ G then θ (N.S.rowAt u z)
  else Function.extend N.embed I.amalgam.label (fun _ ↦ ⊥) z

variable {θ G N u}

theorem decodedLabels_of_le {z : Fin N.S.card} (hz : N.S.toCellScheme.grade z ≤ G) :
    decodedLabels θ G N u z = θ (N.S.rowAt u z) := ite_eq_left hz

/-- **The decoded labels are the glued labels at the old cells**, when the decoded row reads the
old cells of grade at most `G` as the glued labels. -/
theorem decodedLabels_embed (hN : N.Good)
    (hold : ∀ d, I.amalgam.toCellScheme.grade d ≤ G →
      θ (N.S.rowAt u (N.embed d)) = I.amalgam.label d) (d : Fin I.amalgam.card) :
    decodedLabels θ G N u (N.embed d) = I.amalgam.label d := by
  have hgr := hN.lowerEmb.grade_eq d
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ G
  · rw [decodedLabels_of_le (hgr ▸ hd), hold d hd]
  · rw [decodedLabels, ite_eq_right (by rw [hgr]; exact hd)]
    exact N.embed.injective.extend_apply _ _ d

/-- **The decoded labels are lawful**, for a witness `θ` bounded by `G` reflecting `⊥` and a cell
`u` of graded index `(univ, G)`, when the glued labels of grade in `(G, m]` are `⊥` and the decoded
row reads the old cells of grade at most `G` as the glued labels. -/
theorem isLawful_decodedLabels (hN : N.Good) (hθ : IsWitness (stepSuppressor G) θ)
    (hθb : ∀ x, θ x = ⊥ → x = ⊥)
    (hu : N.S.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), G))
    (hold : ∀ d, I.amalgam.toCellScheme.grade d ≤ G →
      θ (N.S.rowAt u (N.embed d)) = I.amalgam.label d)
    (hbot : ∀ d, G < I.amalgam.toCellScheme.grade d → I.amalgam.toCellScheme.grade d ≤ m →
      I.amalgam.label d = ⊥) :
    N.S.rows.IsLawful (decodedLabels θ G N u) := by
  classical
  -- below `(univ, G)`: the decoded row
  have hK : N.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), G)
      (fun d ↦ θ (N.S.rowAt u d)) :=
    (Scheme.isLawfulBelow_rowAt hN.consistent hu).map_of_apply_eq_bot (fun z ↦ z.2.2) hθ
      fun _ ↦ hθb _
  -- below `(univ, m)`: `⊥` above `G`
  have hm : N.S.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), m)
      (fun d ↦ decodedLabels θ G N u d) := by
    have h1 := Rows.isLawfulBelow_extendAbove (K := m)
      (w := fun d ↦ θ (N.S.rowAt u d)) hK
    refine (Rows.isLawfulBelow_congr (w := fun d ↦ if N.S.toCellScheme.grade d ≤ G then
      θ (N.S.rowAt u d) else ⊥) (w' := decodedLabels θ G N u) fun z hz ↦ ?_).mp h1
    by_cases hzg : N.S.toCellScheme.grade z ≤ G
    · rw [ite_eq_left hzg, decodedLabels_of_le hzg]
    · rw [ite_eq_right hzg, decodedLabels, ite_eq_right hzg]
      by_cases hzr : ∃ d, N.embed d = z
      · obtain ⟨d, rfl⟩ := hzr
        rw [N.embed.injective.extend_apply]
        have hgr := hN.lowerEmb.grade_eq d
        exact (hbot d (by rw [← hgr]; omega) (by rw [← hgr]; exact hz.2)).symm
      · exact (Function.extend_apply' I.amalgam.label (fun _ ↦ ⊥) z hzr).symm
  -- below the two coatoms at `m + 1`: the glued labels
  have hcoat (x : Fin (m + 2)) : N.S.rows.IsLawfulBelow (univ.erase x, m + 1)
      (fun d ↦ decodedLabels θ G N u d) :=
    (hN.isLawfulBelow_old_iff (X := (univ.erase x, m + 1)) (Seed.ne_univ_erase x)).mpr
      ((Rows.isLawfulBelow_congr fun d _ ↦ (decodedLabels_embed hN hold d).symm).mp
        (I.amalgam.isLawful.isLawfulBelow _))
  have hall (z : Fin N.S.card) :
      z ∈ N.S.toCellScheme.below ((univ : Finset (Fin (m + 2))), m + 1) := by
    refine ⟨subset_univ _, ?_⟩
    rcases N.inv z with h | h
    · change N.S.toCellScheme.grade z ≤ m + 1; omega
    · obtain ⟨d, rfl⟩ := hN.mem_range z h
      change N.S.toCellScheme.grade (N.embed d) ≤ m + 1
      rw [hN.lowerEmb.grade_eq]
      exact Nat.lt_succ_iff.mp (I.grade_lt d)
  have hglue := Rows.IsLawfulBelow.glue₃ (hcoat (Fin.last (m + 1))) hm
    (hcoat (Fin.castSucc (Fin.last m))) (Y := ((univ : Finset (Fin (m + 2))), m + 1))
    fun d _ ↦ hN.mem_below_cover (x := Fin.last (m + 1)) (y := Fin.castSucc (Fin.last m))
      (by simp) (by simp) Seed.last_ne_castSucc d (hall d)
  exact hglue.isLawful hall

/-- The **actual labels** of the level `N` at the grade `m` for a cell `u` of grade `g + 1`: the
decoded labels for the upper decoder of the glued labels at `g + 1`. -/
noncomputable abbrev actualLabels (g : ℕ) (N' : Lvl I m) (u' : Fin N'.S.card) :
    Fin N'.S.card → Label.{u} :=
  decodedLabels (sepDecoder I g) (g + 1) N' u'

variable {g : ℕ}

theorem actualLabels_of_le {z : Fin N.S.card} (hz : N.S.toCellScheme.grade z ≤ g + 1) :
    actualLabels g N u z = sepDecoder I g (N.S.rowAt u z) := decodedLabels_of_le hz

theorem actualLabels_embed (hN : N.Good)
    (hold : ∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
      sepDecoder I g (N.S.rowAt u (N.embed d)) = I.amalgam.label d) (d : Fin I.amalgam.card) :
    actualLabels g N u (N.embed d) = I.amalgam.label d :=
  decodedLabels_embed hN hold d

/-- **The actual labels are lawful**, when the glued labels of grade in `(g + 1, m]` are `⊥` and
the decoded row reads the old cells of grade at most `g + 1` as the glued labels. -/
theorem isLawful_actualLabels (hN : N.Good)
    (hu : N.S.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), g + 1))
    (hold : ∀ d, I.amalgam.toCellScheme.grade d ≤ g + 1 →
      sepDecoder I g (N.S.rowAt u (N.embed d)) = I.amalgam.label d)
    (hbot : ∀ d, g + 1 < I.amalgam.toCellScheme.grade d → I.amalgam.toCellScheme.grade d ≤ m →
      I.amalgam.label d = ⊥) :
    N.S.rows.IsLawful (actualLabels g N u) :=
  isLawful_decodedLabels hN isWitness_sepDecoder (fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot) hu
    hold hbot

end Actual

end VaughtConjecture.ProfileTower

/-! ### The reading of the completed display -/

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {g j : ℕ} {I : Seed.{u} α (g + 1 + j)} {o r : Fin I.left.card}
  {L : Lvl I g}

local notation "𝒜" => lowPred (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

/-- **The actual profile and its partner agree up to the cutoff cut**: their agreement height in
the grid at `g + 1` is the cutoff cut. -/
theorem agreementHeight_sepHi_sepLo
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last (g + 1 + j)) o r) :
    agreementHeight (grid (g + 1) (bound I)) (sepHi I g) (sepLo I g) =
      cutoffCut (g + 1) (lowNAll I) (sepHi I g) := by
  have hG : (⊥ : Label.{u}) ∈ grid (g + 1) (bound I) := bot_mem_grid _ _
  have hlt := cutoffCut_sepHi_lt hs
  refine le_antisymm (not_lt.mp fun hgt ↦ ?_) (le_agreementHeight cutoffCut_sepHi_mem fun f ↦ ?_)
  · have h := (agreementHeight_spec hG (sepHi I g) (sepLo I g)).2 (Sum.inr ())
    have h2 : sepLo I g (Sum.inr ()) = cutoffCut (g + 1) (lowNAll I) (sepHi I g) :=
      Function.update_self _ _ _
    rw [h2, min_eq_left hgt.le] at h
    exact (lt_min hlt hgt).ne' h
  · rcases f with d | z
    · rw [sepLo, Function.update_of_ne Sum.inl_ne_inr]
    · cases z
      rw [sepLo, Function.update_self, min_eq_right hlt.le, min_self]

/-- **The reading of the completed display holds when the glued labels above `K` are `⊥`**:
at a stage that is zero or a limit, for the seed of a LOW family at `K = g + 1` (the private
context a source-gap context of grade `K`, the donor of top grade at most `K`), over every good
level at `g` whose LOW layer is a good level, when every glued label of grade in `(K, m]` is `⊥`.
The controllers of the actual profile (`ProfileTower.sepHi`) and its partner
(`ProfileTower.sepLo`) are the separator; the labels are the actual labels
(`ProfileTower.actualLabels`), extended through the top layer and reduced to the stage. -/
theorem lowReading_of_bot (hα : Order.IsSuccPrelimit α)
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last (g + 1 + j)) o r)
    (htb : I.right.topGrade ≤ g + 1) (hL : L.Good) (hN : (L.catNext 𝒜).Good)
    (hbot : ∀ d, g + 1 < I.amalgam.toCellScheme.grade d →
      I.amalgam.toCellScheme.grade d ≤ g + 1 + j → I.amalgam.label d = ⊥) :
    LowReading o r L hL hN := by
  classical
  obtain ⟨ihi, hihi⟩ := exists_equivFin_eq (sepHi_mem (o := o) (r := r) hs htb)
  obtain ⟨ilo, hilo⟩ := exists_equivFin_eq (sepLo_mem (o := o) (r := r) hs htb)
  have hNg : ((L.catNext 𝒜).iter j).Good := hN.iter j le_rfl
  have hP := (L.catNext 𝒜).isGradePrefix_iter j
  have hgr (i) : ((L.catNext 𝒜).iter j).S.toCellScheme.grade
      ((L.catNext 𝒜).iterEmb j (Fin.natAdd L.S.card i)) = g + 1 :=
    (hP.lowerEmb.grade_eq _).trans (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
  have hu : ((L.catNext 𝒜).iter j).S.toCellScheme.gradedIndex
      ((L.catNext 𝒜).iterEmb j (Fin.natAdd L.S.card ihi)) =
        ((univ : Finset (Fin (g + 1 + j + 2))), g + 1) :=
    (hP.gradedIndex_eq _).trans (Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _)
  have hold (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ g + 1) :
      sepDecoder I g (((L.catNext 𝒜).iter j).S.rowAt
        ((L.catNext 𝒜).iterEmb j (Fin.natAdd L.S.card ihi)) (((L.catNext 𝒜).iter j).embed d)) =
        I.amalgam.label d := by
    rw [Lvl.iter_embed, hP.rowAt_eq (Fin.natAdd L.S.card ihi) ((L.catNext 𝒜).embed d)]
    change sepDecoder I g ((L.catS _).rowAt (Fin.natAdd _ ihi) (Fin.castAdd _ (L.embed d))) = _
    rw [rowAt_catS_natAdd_castAdd ihi (by rw [hL.lowerEmb.grade_eq]; exact hd), hL.literal, hihi]
    change upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) I.amalgam.label)
      (orbitCode (g + 1) (hat I (g + 1) I.amalgam.label) d) = _
    rw [upperDecoderAt_orbitCode, hat_of_le hd]
  have hq₀ := isLawful_actualLabels hNg hu hold hbot
  obtain ⟨r₁, hr₁, hr₁q⟩ := Scheme.exists_isLawful_fieldLayer (S := ((L.catNext 𝒜).iter j).S)
    (k := g + 1 + j + 1) (hS := ((L.catNext 𝒜).iter j).not_le) hq₀
  refine ⟨Label.reduce α ∘ r₁, hr₁.reduce hα, fun d ↦ atStage_reduce α _, fun d ↦ ?_, ilo, ihi,
    ?_, ?_, ?_, ?_, ?_⟩
  · change Label.reduce α (r₁ (Fin.castAdd _ (((L.catNext 𝒜).iter j).embed d))) = _
    rw [hr₁q, actualLabels_embed hNg hold, (I.amalgam.atStage d).reduce_eq]
  · rw [hilo, hihi]; rfl
  · rw [hihi]; exact cutoffCut_sepHi_mem
  · rw [hihi]; exact cutoffCut_sepHi_lt hs
  · change Label.reduce α (r₁ (Fin.castAdd _ ((L.catNext 𝒜).iterEmb j (Fin.natAdd _ ilo)))) ≠ ⊤
    rw [hr₁q, actualLabels_of_le (hgr ilo).le,
      hP.rowAt_eq (Fin.natAdd L.S.card ihi) (Fin.natAdd L.S.card ilo),
      show (L.catNext 𝒜).S.rowAt (Fin.natAdd L.S.card ihi) (Fin.natAdd L.S.card ilo) = _ from
        rowAt_catS_natAdd_natAdd (L := L) ihi ilo, hihi, hilo,
      agreementHeight_sepHi_sepLo hs, reduce_of_lt (sepDecoder_cutoffCut_lt hα)]
    exact ne_top_of_lt (sepDecoder_cutoffCut_lt hα)
  · change Label.reduce α (r₁ (Fin.castAdd _ ((L.catNext 𝒜).iterEmb j (Fin.natAdd _ ihi)))) = ⊤
    rw [hr₁q, actualLabels_of_le (hgr ihi).le,
      hP.rowAt_eq (Fin.natAdd L.S.card ihi) (Fin.natAdd L.S.card ihi),
      show (L.catNext 𝒜).S.rowAt (Fin.natAdd L.S.card ihi) (Fin.natAdd L.S.card ihi) = _ from
        rowAt_catS_natAdd_natAdd (L := L) ihi ihi, hihi,
      agreementHeight_self (gridPoint_mem_grid le_rfl) (fun _ hx ↦ le_gridPoint_of_mem_grid hx),
      sepDecoder_ceiling hs, reduce_top]

end VaughtConjecture.ProfileTower
