/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CapRequestsPrivateMarker

/-!
# The donor obstruction at a graded index above the cap

Roadmap, Layer 3 ((R4) of the table of 3.4): the donor obstruction with the domination of a live
cell taken at a graded index strictly above the cap.

**The obstruction** (`CapRequests.not_botLiftProvisionOf_donor_of_crossGrade`).  Let `G` be a cell
above the cap, `a` a cell of the grade of `G` with scope inside that of `G`, and suppose the cap
dominates `a` at the graded index of `G` (`CapRequests.CapDominatesAt`) or block-covers it there
(`CapRequests.CapBlockCovers`), and every cell of that graded index reads the marker at an
ordinal `μ + i` and `a` at most `μ + j`.  Then a lift from the donor coatom that is not `⊥` at `a`
and `⊥` at a cell of the request set has no correct code, so the lift provision at `⊥` fails.  In
the lift `W` the cap is not `⊥` (`CapRequests.le_cap_of_capDominatesAt`,
`CapRequests.cap_ne_bot_of_capBlockCovers`), and the marker is not `⊥` either: availability gives
a cell `u` of the graded index of `G` at least `a`, which keeps the block of its reading of the
marker (`CellScheme.Rows.IsLawfulBelow.ne_bot_of_row_le_block`).  Correctness then forces the
marker or the cap to `⊥`.

The cross-grade part of the clause `StageType.CapNonDominating` (the cells `a` of grade above that
of the cap) excludes the domination input of this obstruction
(`StageType.FirstCoatomInput.not_capDominatesAt_of_capNonDominating`,
`StageType.FirstCoatomInput.not_capBlockCovers_of_capNonDominating`); the clause at the grade of
the cap alone does not.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

/-- **The donor lift at `⊥` with a live cell dominated at a graded index above the cap has no
correct code**, when the readers of that graded index read the marker in the block of `a`. -/
theorem not_exists_correct_lift_donor_of_crossGrade
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hmC : r.marker ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex r.cap))
    {a G : Fin I.amalgam.card} (hGk : G ∈ I.amalgam.toCellScheme.below (univ.erase xp, k))
    (hcG : r.cap ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex G))
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope G)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade G)
    (hdom : r.CapDominatesAt a G ∨ r.CapBlockCovers a G)
    (hmk : ∀ u, I.amalgam.toCellScheme.gradedIndex u = I.amalgam.toCellScheme.gradedIndex G →
      ∃ (μ : Ordinal.{u}) (i j : ℕ), Order.IsSuccPrelimit μ ∧
        I.amalgam.toScheme.rowAt u r.marker = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
        I.amalgam.toScheme.rowAt u a ≤ ((μ + j : Ordinal.{u}) : Label.{u}))
    {f : Prof I} (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfa : f a ≠ ⊥)
    {y : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfy : f y = ⊥) :
    ¬ ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k), W d = f d) ∧
        code k W ∈ rowCat r.IsCorrect k := by
  rintro ⟨W, hW, hWf, hc⟩
  have hcorr := (mem_rowCat.mp hc).2
  have hWC := hW.erase hxp
  have hWa : W a ≠ ⊥ := by rw [hWf a ha]; exact hfa
  have hWc : W r.cap ≠ ⊥ := hdom.elim
    (fun h ↦ ne_bot_of_le_ne_bot hWa (le_cap_of_capDominatesAt hWC hGk hcG has hag h))
    (fun h ↦ cap_ne_bot_of_capBlockCovers hWC hGk hcG has hag h hWa)
  -- the marker, through a reader of the graded index of `G` at least `a`
  obtain ⟨-, -, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hWC
  obtain ⟨u, hu, hau⟩ := havail a G hGk has hag
  have huX : u ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := by
    rw [CellScheme.mem_below, hu]; exact hGk
  have hmu : r.marker ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex u) := by
    rw [hu]; exact I.amalgam.toCellScheme.below_mono hcG hmC
  have hau' : a ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex u) := by
    rw [hu]; exact ⟨has, hag.le⟩
  obtain ⟨μ, i, j, hμ, hrm, hra⟩ := hmk u hu
  rw [Scheme.rowAt_of_mem hmu] at hrm
  rw [Scheme.rowAt_of_mem hau'] at hra
  have hWm : W r.marker ≠ ⊥ :=
    Rows.IsLawfulBelow.ne_bot_of_row_le_block hWC huX hmu hau' hμ hrm hra
      (ne_bot_of_le_ne_bot hWa hau) hWa
  have hs {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      hat I k (code k W) d = ⊥ ↔ W d = ⊥ := by
    rw [hat_of_le hd, code, orbitCode_apply, orbitMap_eq_bot_iff, hat_of_le hd]
  have hyN : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hNk
  have hmN : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
  have hsy : hat I k (code k W) y = ⊥ := (hs hyN).mpr (by rw [hWf y hyk]; exact hfy)
  have h := hcorr.markerValue_le y hy
  rw [hsy, min_bot_left, le_bot_iff, markerValue, min_eq_bot, visibilityReplace_eq_bot_iff,
    hs hmN, hs hNk] at h
  rcases h with h | h
  · exact hWm h
  · exact hWc h

/-- **The lift provision at `⊥` from the donor coatom fails** at such a prescription, with the
domination at a graded index above the cap. -/
theorem not_botLiftProvisionOf_donor_of_crossGrade
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    {k : ℕ} (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hmC : r.marker ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex r.cap))
    {a G : Fin I.amalgam.card} (hGk : G ∈ I.amalgam.toCellScheme.below (univ.erase xp, k))
    (hcG : r.cap ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex G))
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope G)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade G)
    (hdom : r.CapDominatesAt a G ∨ r.CapBlockCovers a G)
    (hmk : ∀ u, I.amalgam.toCellScheme.gradedIndex u = I.amalgam.toCellScheme.gradedIndex G →
      ∃ (μ : Ordinal.{u}) (i j : ℕ), Order.IsSuccPrelimit μ ∧
        I.amalgam.toScheme.rowAt u r.marker = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
        I.amalgam.toScheme.rowAt u a ≤ ((μ + j : Ordinal.{u}) : Label.{u}))
    {f : Prof I} (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ f d)
    (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfa : f a ≠ ⊥)
    {y : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfy : f y = ⊥) :
    ¬ BotLiftProvisionOf r.IsCorrect k xd := fun hprov ↦
  not_exists_correct_lift_donor_of_crossGrade hgr hxp hNk hmC hGk hcG has hag hdom hmk ha hfa hy
    hyk hfy (hprov f hf)

end CapRequests

end VaughtConjecture
