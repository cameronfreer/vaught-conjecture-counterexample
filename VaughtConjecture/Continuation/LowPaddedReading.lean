/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowPaddedTower
import VaughtConjecture.Continuation.LowStateReading

/-!
# The padded tower reads the actual state

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the display above the
controllers when the faces carry labels other than `⊥` above `K`); semantic contract, items 3, 4
and 8.

**LOW layers from a catalogue of states LOW over every grade.**  The LOW layer of a display
(`StageType.IsLowLayer`) asks the LOW clause of every controller over the proper donor cells of
the display, of every grade (`StageType.properDonorFields`).  The entry of a state reads its proper
donor fields literally (`ProfileTower.donorMax_lowFields`), so a state LOW over the proper donor
fields of every grade of the seed (`ProfileTower.lowNAll`) has a LOW entry
(`ProfileTower.isLowAt_lowFields_all`); the LOW layer and the reading from a level reading the
actual state hold for such a catalogue (`ProfileTower.isLowLayer_of_isGradePrefix_all`,
`ProfileTower.ReadsActualOn.exists_isLowLayer_all`, in
`VaughtConjecture.Continuation.LowStateReading`).

**The padded tower reads the actual state** (`ProfileTower.exists_isLowLayer_pTower`, compiled in
this repository).  Let `I` be the seed of a LOW family at `K = g + 1 < m = g + J + 2`, `L` the level
from the grade `0` at `g`, and the padded tower of the LOW clause over the proper donor fields of
every grade.  Its lifts are the steps for states of
`VaughtConjecture.Continuation.LowPaddedStep` (`ProfileTower.stateCatStep_lowAll_seed`), so it is
good up to `m` with no hypothesis; its top level reads the actual state (the glued labels with the
cutoff `⊤`): the cell of the orbit code at `m` of the actual state reads every old cell of grade at
most `m` as its glued label, the controller of the padded bottom code `s` as `⊤`
(`ProfileTower.le_pTower_hi` at the cutoff `⊤`), and the controller of the partner of `s` at most
at the cutoff cut of the glued labels, below the stage (`ProfileTower.pTower_lo_le`).  The actual
state is separated, and so is `s` (`ProfileTower.sepInv_orbitCode`).  So every LOW family with
`K < k` has a legal display with a LOW layer at `K` whose separator is labelled by a proper label
and `⊤`, and the faces keep their labels.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme StageType

variable {α : Ordinal.{u}} {m g : ℕ} {I : Seed.{u} α m} {L : Lvl I g}

/-! ### The padded tower reads the actual state -/

section Actual

variable {J : ℕ} {I : Seed.{u} α (g + J + 2)} {o r : Fin I.left.card}

local notation "𝒜all" => lowPred (g + 1) (lowNAll I) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r)

local notation "𝒦" => sCat I (g + 1) (lowPred (g + 1) (lowNAll I) (lowT I)
  (StageType.faceCell I.restrictFace_left o) (StageType.faceCell I.restrictFace_left r))

/-- **The padded tower of the clause over every grade lifts**, for a LOW family at
`K = g + 1 < m = g + J + 2`: the steps for states at every grade from `K` to `m`
(`ProfileTower.stateCatStep_lowAll_seed`) through `ProfileTower.pTowerLifts_of_amalgam`. -/
theorem pTowerLifts_lowAll
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last (g + J + 2)) o r)
    (htb : I.right.topGrade ≤ g + 1) : PTowerLifts (lvlZero I g) 𝒜all (J + 2) := by
  refine pTowerLifts_of_amalgam (lvlZero_good g (by omega)) (readableS_lvlZero g (by omega))
    (fun W ↦ lowPred_withCut_bot W) (fun j hj P h ↦ lowPred_orbitCode hj h) (J + 2) (by omega) ?_
  intro J' hJ' x hx
  exact stateCatStep_lowAll_seed (by omega) hs htb (by omega) (by omega) hx

/-- **The padded tower of the LOW clause over every grade reads the actual state**, for a LOW
family at `K = g + 1 < m = g + J + 2`, with no hypothesis: the completed display over its top
level is legal, has the private context and the donor as faces, and carries a LOW layer at `K`
whose separator is labelled by a proper label and `⊤`. -/
theorem exists_isLowLayer_pTower (hα : Order.IsSuccPrelimit α)
    (hs : I.left.IsSourceGapContextAt (g + 1) Fin.castSuccEmb (Fin.last (g + J + 2)) o r)
    (htb : I.right.topGrade ≤ g + 1) :
    ∃ (D : StageType.{u} α (g + J + 2 + 2)) (h₁ : restrictFace Fin.castSuccEmb D = some I.left)
      (h₂ : restrictFace (extendByLast Fin.castSuccEmb) D = some I.right)
      (G : Finset Label.{u}) (entry : Fin D.card → LowField D → Label.{u})
      (s : LowField D → Label.{u}) (lo hi : Fin D.card), D.IsLegal ∧ D.label lo ≠ ⊤ ∧
        D.label hi = ⊤ ∧ IsLowLayer (g + 1) h₁ h₂ o r G entry s lo hi := by
  classical
  set L := lvlZero I g with hLdef
  have hL : L.Good := lvlZero_good g (by omega)
  have hF := fieldsLE_low hs htb
  have hA0 : ∀ W : Prof I, 𝒜all (withCut W ⊥) := fun W ↦ lowPred_withCut_bot W
  have hAo : ∀ j, g + 1 ≤ j → ∀ P : CProf I, 𝒜all P → 𝒜all (orbitCode j P) :=
    fun j hj P h ↦ lowPred_orbitCode hj h
  have hlift := pTowerLifts_lowAll hs htb
  have hgood (J' : ℕ) (hJ' : J' ≤ J + 2) : (pTower L 𝒜all J').Good 𝒜all :=
    pTower_good hL hA0 hAo hlift J' hJ' (by omega)
  have hT' : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d ∧ I.amalgam.toCellScheme.grade d ≤ g + 1 :=
    hF.2.1
  have hTi : ∀ f ∈ lowT I, ∃ d, f = Sum.inl d := fun f hf ↦ by
    obtain ⟨d, h, -⟩ := hT' f hf; exact ⟨d, h⟩
  -- the actual state, its code at the top, the padded bottom state
  set P := actState I with hP
  have hPlow : 𝒜all P := isLowAt_of_forall_top fun x hx ↦ by
    obtain ⟨t, ht, rfl⟩ := hx
    exact (StageType.label_faceCell _ t).trans ht
  set Q := orbitCode (g + J + 2) P with hQ
  have hQs : SepInv (lowNAll I) (lowT I) (StageType.faceCell I.restrictFace_left o) Q :=
    sepInv_orbitCode (sepInv_actState hs)
  have hQc : IsCutLawful I (g + J + 2) (camal Q) :=
    ⟨(isCutLawful_label (I := I) (g + J + 2)).1.map_of_apply_eq_bot (fun d ↦ d.2.2)
        (isWitness_orbitMap (g + J + 2) P) fun _ ↦ orbitMap_eq_bot_iff.mp,
      (isCutLawful_label (I := I) (g + J + 2)).2.map_of_apply_eq_bot (fun d ↦ d.2.2)
        (isWitness_orbitMap (g + J + 2) P) fun _ ↦ orbitMap_eq_bot_iff.mp⟩
  have hQ𝒮 : Q ∈ sCat I (g + (J + 1) + 1) 𝒜all :=
    orbitCode_mem_sCat (g := g + (J + 1)) (isCutLawful_label _) (hAo _ (by omega) P hPlow)
  obtain ⟨iu, hiu⟩ := exists_equivFin_eq hQ𝒮
  set S := pBot g J Q with hS
  set s := orbitCode (g + 1) S with hsdef
  have hSs := sepInv_pBot (g := g) J Q hQs
  have hss : SepInv (lowNAll I) (lowT I) (StageType.faceCell I.restrictFace_left o) s :=
    sepInv_orbitCode hSs
  have hSc : IsCutLawful I (g + 1) (camal S) := isCutLawful_pBot J Q (by
    obtain ⟨hC, hD⟩ := hQc
    exact ⟨hC.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩,
      hD.mono (X := (_, g + J + 1)) ⟨subset_rfl, by omega⟩⟩)
  have hsc : IsCutLawful I (g + 1) (camal s) :=
    ⟨hSc.1.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap (g + 1) S)
        fun _ ↦ orbitMap_eq_bot_iff.mp,
      hSc.2.map_of_apply_eq_bot (fun d ↦ d.2.2) (isWitness_orbitMap (g + 1) S)
        fun _ ↦ orbitMap_eq_bot_iff.mp⟩
  set c := cutoffCut (g + 1) (lowNAll I) s with hc
  have hclt : c < s (Sum.inr ()) := cutoffCut_lt_of_sepInv hss
  have hcmem : c ∈ grid (g + 1) (bound I) := cutoffCut_orbitCode_mem_grid _ _ _
  have hsK : s ∈ 𝒦 := by
    refine mem_sCat.mpr ⟨orbitCode_mem_codeGrid _ _, hsc, orbitCode_orbitCode, ?_⟩
    have := lowPred_update_of_sepInv (K := g + 1) (N := lowNAll I)
      (r := StageType.faceCell I.restrictFace_left r) hTi hss le_rfl
    rwa [Function.update_eq_self] at this
  have hpK : Function.update s (Sum.inr ()) c ∈ 𝒦 := by
    refine mem_sCat.mpr ⟨fun f ↦ ?_, ?_,
      orbitCode_update_cutoffCut inr_notMem_lowNAll orbitCode_orbitCode hss.2.1,
      lowPred_update_of_sepInv hTi hss hclt.le⟩
    · rcases f with d | z
      · rw [Function.update_of_ne Sum.inl_ne_inr]; exact orbitCode_mem_codeGrid _ _ _
      · rw [Function.update_self]; exact grid_subset_codeGrid _ _ hcmem
    · have hcam : camal (Function.update s (Sum.inr ()) c) = camal s :=
        funext fun _ ↦ Function.update_of_ne Sum.inl_ne_inr _ _
      rw [hcam]; exact hsc
  obtain ⟨ihi, hihi⟩ := exists_equivFin_eq hsK
  obtain ⟨ilo, hilo⟩ := exists_equivFin_eq hpK
  -- the top state level, its layer below, and the reading
  set N₁ := pTower L 𝒜all (J + 1) with hN₁
  have hN₁ : N₁.Good 𝒜all := hgood (J + 1) (by omega)
  have hN₂ : (pTower L 𝒜all (J + 2)).Good 𝒜all := hgood (J + 2) le_rfl
  set θ := upperDecoderAt (g + J + 2) (g + J + 2 + 1) (bound I) P with hθ
  have hθw : IsWitness (stepSuppressor (g + J + 2)) θ := isWitness_upperDecoderAt (by omega)
  have hgrK (i : Fin (𝒦).card) :
      N₁.S.toCellScheme.grade (pEmb J (Fin.natAdd L.S.card i)) = g + 1 :=
    ((isGradePrefix_pEmb J).lowerEmb.grade_eq _).trans
      (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
  have hrow (i : Fin (𝒦).card) :
      (pTower L 𝒜all (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
        (pEmb (J + 1) (Fin.natAdd L.S.card i)) = N₁.σs Q (pEmb J (Fin.natAdd L.S.card i)) := by
    have h := rowAt_sS_natAdd_castAdd (N := N₁) (C := sCat I (g + (J + 1) + 1) 𝒜all) iu
      (e := pEmb J (Fin.natAdd L.S.card i)) (by rw [hgrK]; omega)
    rw [hiu] at h
    exact h
  refine ReadsActualOn.exists_isLowLayer_all hα hL
    (fun R hR ↦ ⟨(mem_sCat.mp hR).1, (mem_sCat.mp hR).2.2.2⟩)
    (N := (pTower L 𝒜all (J + 2)).forget)
    (hN₂.forget hA0) (hN₁.hasBotExtension_pnext hA0) (by omega) (by omega)
    (ψ := pEmb (J + 1)) (isGradePrefix_pEmb (J + 1)) (fun d ↦ pTower_embed (J + 1) d)
    ⟨Fin.natAdd N₁.S.card iu, θ, ilo, ihi, Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _,
      hθw, fun _ ↦ eq_bot_of_upperDecoderAt_eq_bot, fun d hd ↦ ?_, by rw [hilo, hihi],
      by rw [hihi]; exact hcmem, by rw [hihi]; exact hclt, ?_, ?_⟩
  · -- the old cells
    -- the row of the cell of the actual code at an old cell, through the scheme of the layer
    change θ ((N₁.sS (sCat I (g + (J + 1) + 1) 𝒜all)).rowAt (Fin.natAdd N₁.S.card iu)
      (Fin.castAdd _ (N₁.embed d))) = _
    rw [rowAt_sS_natAdd_castAdd iu (by rw [hN₁.lowerEmb.grade_eq]; omega), hiu, hN₁.literal]
    exact upperDecoderAt_orbitCode _
  · -- the controller of `s` is read as `⊤`
    -- the row of the cell of the actual code at the controller of `s`
    change θ ((pTower L 𝒜all (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
      (pEmb (J + 1) (Fin.natAdd L.S.card ihi))) = ⊤
    rw [hrow]
    have h1 := le_pTower_hi (L := L) (A := 𝒜all) J Q ihi hihi
    have h2 : θ (Q (Sum.inr ())) = ⊤ := upperDecoderAt_orbitCode _
    exact top_le_iff.mp (h2 ▸ hθw.monotone h1)
  · -- the controller of the partner is read below the stage
    -- the row of the cell of the actual code at the controller of the partner of `s`
    change θ ((pTower L 𝒜all (J + 2)).S.rowAt (Fin.natAdd N₁.S.card iu)
      (pEmb (J + 1) (Fin.natAdd L.S.card ilo))) < α
    rw [hrow]
    have h1 := pTower_lo_le (L := L) (A := 𝒜all) (lowNAll I) J Q ilo hilo hclt
    have h2 := upperDecoder_cutoff_orbitCode (K := g + 1) (k := g + J + 2) (by omega)
      (lowNAll I) P
    refine (hθw.monotone h1).trans_lt (h2.trans_lt ?_)
    rw [visibilityReplace_lt_iff hα]
    refine Finset.sup_lt_iff (WithBot.bot_lt_coe _) |>.mpr fun f hf ↦ ?_
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    -- a proper donor field reads the glued label of a donor cell
    change I.amalgam.label _ < α
    rw [StageType.label_faceCell]
    exact (I.right.atStage t).resolve_right (mem_filter.mp ht).2

end Actual

end VaughtConjecture.ProfileTower
