/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowDisplayReading

/-!
# The separator of the actual profile

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the separator and the
controller of the actual state); semantic contract, items 3, 4 and 8.

Let `I` be the seed of a LOW family at `K = g + 1`: the private context a source-gap context of
grade `K` with owner `o` and lost top `r`, the donor of top grade at most `K`.  Write `W` for the
glued labels of the amalgam and `w` for its splice at `K` (`ProfileTower.hat`).

**The actual profile** (`ProfileTower.sepHi`): the code of `W` at `K` with the cutoff `β`, the
orbit map of `⊤`.  The owner, the lost top and the donor tops are labelled `⊤` and have grade at
most `K`, so all of them are coded by `β`, the largest code: the LOW clause holds whatever the
donor maximum (`ProfileTower.sepHi_mem`).  **Its partner** (`ProfileTower.sepLo`) lowers the
cutoff to the cutoff cut `c` over all proper donor cells; it is LOW (`ProfileTower.sepLo_mem`).

**The cutoff cut** (`ProfileTower.cutoffCut_sepHi_mem`, `ProfileTower.cutoffCut_sepHi_lt`).  The
donor maximum of the actual profile is `⊥` or the code of a proper donor label `W d`, so `c` is
`⊥` or the grid point of the code block of `W d` (`Label.visibilityReplace_orbitMap`): it lies in
the grid, and below `β`, the grid point of the code block of `⊤`, since the key of `W d` is below
that of `⊤` (`Label.codeBlock_lt_codeBlock`).  The agreement height of the actual profile and its
partner in the grid at `K` is `c` (`ProfileTower.agreementHeight_sepHi_sepLo_eq_cutoffCut`).

**The reading of the actual profile** (`ProfileTower.sepDecoder`, the upper decoder of `w` at
`K`, a witness bounded by `K`).  It reads the code of `W` as `W` at the cells of grade at most `K`
(`Label.upperDecoderAt_orbitCode`), the ceiling of the grid as `⊤`
(`ProfileTower.sepDecoder_ceiling`: it is monotone and reads the code `β` of the lost top as
`⊤`), and the cutoff cut below the stage (`ProfileTower.sepDecoder_cutoffCut_lt`: it commutes
with the visibility replacement at `K`, and a replacement of a proper label at a limit stage
stays below the stage).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {g : ℕ} {o r : Fin I.left.card}

local notation "𝒞" => lowCat I (g + 1) (lowN I (g + 1)) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

variable (I g) in
/-- The **upper decoder of the glued labels** at the grade `g + 1`. -/
noncomputable abbrev sepDecoder : Label.{u} → Label.{u} :=
  upperDecoderAt (g + 1) (g + 2) (bound I) (hat I (g + 1) I.amalgam.label)

variable (I g) in
/-- The **actual profile** at the grade `g + 1`: the code of the glued labels, with the cutoff the
orbit map of `⊤`. -/
noncomputable def sepHi : CProf I :=
  withCut (code (g + 1) I.amalgam.label) (orbitMap (g + 1) (hat I (g + 1) I.amalgam.label) ⊤)

variable (I g) in
/-- The **partner of the actual profile**: its cutoff lowered to its cutoff cut over all proper
donor cells. -/
noncomputable def sepLo : CProf I :=
  Function.update (sepHi I g) (Sum.inr ()) (cutoffCut (g + 1) (lowNAll I) (sepHi I g))

theorem isWitness_sepDecoder : IsWitness (stepSuppressor (g + 1)) (sepDecoder I g) :=
  isWitness_upperDecoderAt (by omega)

theorem isCutLawful_label (k : ℕ) : IsCutLawful I k I.amalgam.label :=
  ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩

/-- **The actual profile reads a cell of grade at most `g + 1` labelled `⊤` by its cutoff.** -/
theorem sepHi_of_top {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ g + 1)
    (htop : I.amalgam.label d = ⊤) : sepHi I g (Sum.inl d) = sepHi I g (Sum.inr ()) := by
  change orbitMap (g + 1) _ (hat I (g + 1) I.amalgam.label d) = _
  rw [hat_of_le hd, htop]
  rfl

/-- The owner of the private context, in the amalgam, is labelled `⊤` and has grade `g + 1`. -/
theorem owner_copy (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r) :
    I.amalgam.label (StageType.faceCell I.restrictFace_left o) = ⊤ ∧
      I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_left o) = g + 1 :=
  ⟨(StageType.label_faceCell _ o).trans hs.label_owner,
    (StageType.grade_faceCell _ o).trans hs.grade_owner⟩

/-- The lost top of the private context, in the amalgam, is labelled `⊤` and has grade at most
`g + 1`. -/
theorem lost_copy (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r) :
    I.amalgam.label (StageType.faceCell I.restrictFace_left r) = ⊤ ∧
      I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_left r) ≤ g + 1 :=
  ⟨(StageType.label_faceCell _ r).trans hs.label_lost, (StageType.grade_faceCell _ r).trans_le
    (hs.topGrade_eq ▸ StageType.grade_le_topGrade hs.label_lost)⟩

/-- **The actual profile is LOW**: the owner and the donor tops are coded by the cutoff. -/
theorem isLowAt_sepHi_of (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r)
    (htb : I.right.topGrade ≤ g + 1) {c : Label.{u}} (hc : c ≤ sepHi I g (Sum.inr ())) :
    IsLowAt (g + 1) (lowN I (g + 1)) (lowT I) (Sum.inl (StageType.faceCell I.restrictFace_left o))
      (Sum.inl (StageType.faceCell I.restrictFace_left r)) (Sum.inr ())
      (Function.update (sepHi I g) (Sum.inr ()) c) := by
  intro _ x hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hupd (f : Fin I.amalgam.card) :
      Function.update (sepHi I g) (Sum.inr ()) c (Sum.inl f) = sepHi I g (Sum.inl f) :=
    Function.update_of_ne Sum.inl_ne_inr _ _
  rw [Function.update_self, hupd, sepHi_of_top (by
      rw [StageType.grade_faceCell]; exact StageType.topGrade_le_iff.mp htb t ht)
    (by rw [StageType.label_faceCell]; exact ht)]
  refine max_le hc ((min_le_left _ _).trans ?_)
  rw [hupd, sepHi_of_top (owner_copy hs).2.le (owner_copy hs).1]

/-- **The actual profile lies in the LOW catalogue.** -/
theorem sepHi_mem (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r)
    (htb : I.right.topGrade ≤ g + 1) : sepHi I g ∈ 𝒞 := by
  have h := isLowAt_sepHi_of hs htb (le_refl (sepHi I g (Sum.inr ())))
  rw [Function.update_eq_self] at h
  exact mem_predCat_of (isCutLawful_hat (isCutLawful_label _))
    (orbitMap_mem_codeGrid (by simp only [Fintype.card_fin, bound]; omega) _) h

/-! ### The cutoff cut -/

/-- The cutoff of the actual profile is the grid point of the code block of `⊤`. -/
theorem sepHi_cutoff : sepHi I g (Sum.inr ()) =
    gridPoint (g + 1) (codeBlock (g + 1) (hat I (g + 1) I.amalgam.label) ⊤) :=
  orbitMap_of_not_isOrbitKey top_ne_bot fun h ↦ h.ne_top rfl

/-- **The donor maximum of the actual profile** is `⊥` or the code of a proper donor label of
grade at most `g + 1`. -/
theorem donorMax_sepHi_cases :
    donorMax (lowNAll I) (sepHi I g) = ⊥ ∨ ∃ t : Fin I.right.card, I.right.label t ≠ ⊤ ∧
      I.right.label t ≠ ⊥ ∧ I.right.toCellScheme.grade t ≤ g + 1 ∧
      donorMax (lowNAll I) (sepHi I g) = orbitMap (g + 1) (hat I (g + 1) I.amalgam.label)
        (I.right.label t) := by
  classical
  rcases (lowNAll I).eq_empty_or_nonempty with he | hne
  · left
    rw [donorMax, he, sup_empty]
  obtain ⟨f, hf, hfeq⟩ := exists_mem_eq_sup _ hne (sepHi I g)
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
  have htop := (mem_filter.mp ht).2
  have hval : sepHi I g (Sum.inl (StageType.faceCell I.restrictFace_right t)) =
      orbitMap (g + 1) (hat I (g + 1) I.amalgam.label)
        (hat I (g + 1) I.amalgam.label (StageType.faceCell I.restrictFace_right t)) := rfl
  by_cases hg : I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_right t) ≤ g + 1
  · rw [hat_of_le hg, StageType.label_faceCell] at hval
    by_cases hb : I.right.label t = ⊥
    · left
      rw [donorMax, hfeq, hval, hb, orbitMap_bot]
    · right
      exact ⟨t, htop, hb, by rwa [StageType.grade_faceCell] at hg, by rw [donorMax, hfeq, hval]⟩
  · left
    rw [donorMax, hfeq, hval, hat_of_lt (not_le.mp hg), orbitMap_bot]

/-- **The cutoff cut of the actual profile lies in the grid at `g + 1`.** -/
theorem cutoffCut_sepHi_mem :
    cutoffCut (g + 1) (lowNAll I) (sepHi I g) ∈ grid (g + 1) (bound I) := by
  rcases donorMax_sepHi_cases (I := I) (g := g) with h | ⟨t, -, hb, -, h⟩
  · rw [cutoffCut, h, visibilityReplace_bot]
    exact bot_mem_grid _ _
  · rw [cutoffCut, h, visibilityReplace_orbitMap hb]
    refine gridPoint_mem_grid ((codeBlock_le _ _ _).trans ?_)
    have := keyRank_le_card (g + 1) (hat I (g + 1) I.amalgam.label) (I.right.label t)
    simp only [Fintype.card_fin] at this
    simp only [bound]
    omega

/-- **The cutoff cut of the actual profile lies below its cutoff**, when the lost top is coded. -/
theorem cutoffCut_sepHi_lt
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r) :
    cutoffCut (g + 1) (lowNAll I) (sepHi I g) < sepHi I g (Sum.inr ()) := by
  rcases donorMax_sepHi_cases (I := I) (g := g) with h | ⟨t, hne, hb, -, h⟩
  · rw [cutoffCut, h, visibilityReplace_bot, bot_lt_iff_ne_bot]
    change orbitMap _ _ ⊤ ≠ ⊥
    rw [Ne, orbitMap_eq_bot_iff]
    exact top_ne_bot
  · rw [cutoffCut, h, visibilityReplace_orbitMap hb, sepHi_cutoff]
    have hkey : IsKey (g + 1) (hat I (g + 1) I.amalgam.label) ⊤ :=
      ⟨StageType.faceCell I.restrictFace_left r, by
        rw [hat_of_le (lost_copy hs).2, (lost_copy hs).1]; exact top_ne_bot, by
        rw [hat_of_le (lost_copy hs).2, (lost_copy hs).1]⟩
    have hlt := codeBlock_lt_codeBlock hb hkey (by
      rw [visibilityReplace_top, lt_top_iff_ne_top, Ne, visibilityReplace_eq_top_iff]
      exact hne)
    exact lt_of_le_of_ne (gridPoint_le_gridPoint.mpr hlt.le)
      fun he ↦ absurd (gridPoint_le_gridPoint.mp he.ge) (not_le.mpr hlt)

/-- **The actual profile and its partner agree up to the cutoff cut**, on a seed of any arity: their
agreement height in the grid at `g + 1` is the cutoff cut, which lies in the grid and below the
cutoff (`ProfileTower.cutoffCut_sepHi_mem`, `ProfileTower.cutoffCut_sepHi_lt`). -/
theorem agreementHeight_sepHi_sepLo_eq_cutoffCut
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r) :
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

/-- **The partner of the actual profile lies in the LOW catalogue.** -/
theorem sepLo_mem (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r)
    (htb : I.right.topGrade ≤ g + 1) : sepLo I g ∈ 𝒞 := by
  obtain ⟨hB, hcut, horb, -⟩ := mem_predCat.mp (sepHi_mem hs htb)
  have hcam : camal (sepLo I g) = camal (sepHi I g) :=
    funext fun _ ↦ Function.update_of_ne Sum.inl_ne_inr _ _
  refine mem_predCat.mpr ⟨fun f ↦ ?_, hcam ▸ hcut, by rw [hcam]; exact horb,
    isLowAt_sepHi_of hs htb (cutoffCut_sepHi_lt hs).le⟩
  rcases f with d | z
  · rw [sepLo, Function.update_of_ne Sum.inl_ne_inr]; exact hB _
  · rw [sepLo, Function.update_self]
    exact grid_subset_codeGrid _ _ cutoffCut_sepHi_mem

/-! ### The reading of the actual profile -/

/-- **The decoder reads the ceiling of the grid as `⊤`**: it reads the code of the lost top as
`⊤`, below the ceiling. -/
theorem sepDecoder_ceiling
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last m) o r) :
    sepDecoder I g (gridPoint (g + 1) (bound I)) = ⊤ := by
  have h := upperDecoderAt_orbitCode (k := g + 1) (K := g + 2) (B := bound I)
    (w := hat I (g + 1) I.amalgam.label) (StageType.faceCell I.restrictFace_left r)
  rw [hat_of_le (lost_copy hs).2, (lost_copy hs).1] at h
  refine top_le_iff.mp (h ▸ isWitness_sepDecoder.monotone ?_)
  exact le_gridPoint_of_mem_codeGrid (code_mem_codeGrid _ _ _)

/-- **The decoder reads the cutoff cut below the stage**, at a stage that is zero or a limit. -/
theorem sepDecoder_cutoffCut_lt (hα : Order.IsSuccPrelimit α) :
    sepDecoder I g (cutoffCut (g + 1) (lowNAll I) (sepHi I g)) < α := by
  rcases donorMax_sepHi_cases (I := I) (g := g) with h | ⟨t, hne, -, hg, h⟩
  · rw [cutoffCut, h, visibilityReplace_bot, sepDecoder, upperDecoderAt_bot]
    exact WithBot.bot_lt_coe _
  · have hd : I.amalgam.toCellScheme.grade (StageType.faceCell I.restrictFace_right t) ≤ g + 1 :=
      by rw [StageType.grade_faceCell]; exact hg
    have hcode : orbitMap (g + 1) (hat I (g + 1) I.amalgam.label) (I.right.label t) =
        orbitCode (g + 1) (hat I (g + 1) I.amalgam.label)
          (StageType.faceCell I.restrictFace_right t) := by
      rw [orbitCode_apply, hat_of_le hd, StageType.label_faceCell]
    rw [cutoffCut, h, hcode, isWitness_sepDecoder.visibilityReplace_comm _ (g + 1)
      (by rw [stepSuppressor_of_le le_rfl]; exact le_top) (g + 1) le_rfl, sepDecoder,
      upperDecoderAt_orbitCode, hat_of_le hd, StageType.label_faceCell,
      visibilityReplace_lt_iff hα]
    exact (I.right.atStage t).resolve_right hne

end VaughtConjecture.ProfileTower
