/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CapRequestsPrivateMarker
import VaughtConjecture.Continuation.CapRequestsDonorClass

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

**In the class form.**  The input `f y = ⊥` at a cell `y` of `T` lies outside the bottom class as
soon as `T ⊆ B`: such a labelling has a lift whose code is admitted
(`CapRequests.exists_admitted_lift_of_eq_bot`).  The obstruction at a small value with the
domination above the cap does hold in the class form
(`CapRequests.not_botLiftProvisionOf_admits_donor_of_crossGrade`, as
`CapRequests.not_botLiftProvisionOf_admits_donor` at the grade of the cap), and its input refutes
the domination of the tops of the donor (`CapRequests.not_donorTopsDominateAt_of_crossGrade`).

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

/-! ### The class form -/

variable {B : Set (Fin I.amalgam.card)}

/-- **A lift `⊥` at a cell of `B` is admitted**: a labelling lawful below the donor coatom and `⊥`
at a cell of `B` below it has a lift lawful on the cut whose code is admitted in the bottom class
with no prescribed bottoms (the fill of the other coatom; the lift is out of the class).  So the
input `f y = ⊥` at a cell `y` of `T` of `CapRequests.not_botLiftProvisionOf_donor_of_crossGrade`
gives no obstruction in the class form as soon as `T ⊆ B`. -/
theorem exists_admitted_lift_of_eq_bot (hm : 0 < m) {k : ℕ} (hk0 : 0 < k) (hkm : k ≤ m + 1)
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ f d) {y : Fin I.amalgam.card}
    (hyB : y ∈ B) (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfy : f y = ⊥) :
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k), W d = f d) ∧
        code k W ∈ rowCat (r.Admits B ∅) k := by
  obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxd
    (isSelfVisible_bot _) (P := fun _ ↦ ⊥)
    ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf fun _ _ ↦ by simp
  exact ⟨W, hW, hWf, code_mem_rowCat_admits_of_eq_bot hW hyB hyk.2 ((hWf y hyk).trans hfy)⟩

/-- **A small value at a top obstructs the lift at `⊥` in the class form, with the domination at a
graded index above the cap**: as `CapRequests.not_botLiftProvisionOf_admits_donor`, with the cap
dominating `a` at the graded index of a cell `G` above the cap, `a` of the grade of `G` with scope
inside that of `G` (`CapRequests.le_cap_of_capDominatesAt`). -/
theorem not_botLiftProvisionOf_admits_donor_of_crossGrade
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) {a G : Fin I.amalgam.card}
    (hGk : G ∈ I.amalgam.toCellScheme.below (univ.erase xp, k))
    (hcG : r.cap ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex G))
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope G)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade G)
    (hdom : r.CapDominatesAt a G) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ f d)
    (hBD : ∀ d ∈ B, d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hfB : ∀ d ∈ B, f d ≠ ⊥) (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hmk : r.marker ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (haM : f a ≤ visibilityReplace r.N r.R (f r.marker)) {y : Fin I.amalgam.card}
    (hy : y ∈ r.T) (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hy0 : f y ≠ ⊥)
    (hya : visibilityReplace k k (f y) < visibilityReplace k k (f a)) :
    ¬ BotLiftProvisionOf (r.Admits B ∅) k xd := by
  intro hprov
  obtain ⟨W, hW, hWf, hc⟩ := hprov f hf
  set w := hat I k W with hwdef
  have hs (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ k) :
      hat I k (code k W) d = orbitMap k w (W d) := by
    rw [hat_of_le hd, code, orbitCode_apply, hwdef, hat_of_le hd]
  have hcl : InBottomClass B ∅ (hat I k (code k W)) := by
    refine inBottomClass_empty_iff_forall.mpr fun d hdB ↦ ?_
    rw [hs d (hBD d hdB).2, Ne, orbitMap_eq_bot_iff, hWf d (hBD d hdB)]
    exact hfB d hdB
  have hcorr := (mem_rowCat.mp hc).2 hcl
  have hle : W a ≤ W r.cap := le_cap_of_capDominatesAt (hW.erase hxp) hGk hcG has hag hdom
  rw [hWf a ha] at hle
  have hφ := isWitness_orbitMap k w
  have hNk' : r.N ≤ k := hgr.le_grade_cap.trans hNk
  have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hNk
  have hyg : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hNk
  have hmv : orbitMap k w (f a) ≤ r.markerValue (hat I k (code k W)) := by
    unfold markerValue
    rw [hs _ hmg, hs _ hNk, hWf _ hmk, ← hφ.visibilityReplace_comm _ r.N
      (by rw [stepSuppressor_of_le hNk']; exact le_top) r.R r.R_lt_N.le]
    exact le_min (hφ.monotone haM) (hφ.monotone hle)
  have hfa0 : f a ≠ ⊥ := fun h ↦ by
    rw [h, visibilityReplace_bot] at hya
    exact not_lt_bot hya
  have hwa : w a = f a := by rw [hwdef, hat_of_le ha.2, hWf a ha]
  have hkey : IsKey k w (f a) := by
    rw [← hwa]
    exact isKey_apply_iff.mpr (by rw [hwa]; exact hfa0)
  have hlt := orbitMap_lt_orbitMap_of_lt (w := w) hy0 hkey hya
  have h := hcorr.markerValue_le y hy
  rw [hs y hyg, hWf y hyk] at h
  exact absurd ((hmv.trans h).trans (min_le_left _ _)) (not_le.mpr hlt)

/-- **The input of the cross-grade obstruction in the class form refutes the domination of the tops
of the donor** (`CapRequests.DonorTopsDominateAt`), under the hypotheses of
`CapRequests.botLiftProvisionOf_admits_donor`. -/
theorem not_donorTopsDominateAt_of_crossGrade (hm : 0 < m)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hZ : r.Z = ∅) (hF : r.F = ∅)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hBD : ∀ d ∈ B, d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    {a G : Fin I.amalgam.card}
    (hGk : G ∈ I.amalgam.toCellScheme.below (univ.erase xp, k))
    (hcG : r.cap ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex G))
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope G)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade G)
    (hdom : r.CapDominatesAt a G) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ f d)
    (hfB : ∀ d ∈ B, f d ≠ ⊥) (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hmk : r.marker ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (haM : f a ≤ visibilityReplace r.N r.R (f r.marker)) {y : Fin I.amalgam.card}
    (hy : y ∈ r.T) (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hy0 : f y ≠ ⊥)
    (hya : visibilityReplace k k (f y) < visibilityReplace k k (f a)) :
    ¬ DonorTopsDominateAt r B xp xd k := fun hdt ↦
  not_botLiftProvisionOf_admits_donor_of_crossGrade hgr hxp hNk hGk hcG has hag hdom hf hBD hfB
    ha hmk haM hy hyk hy0 hya
    (botLiftProvisionOf_admits_donor hm hgr hcapC hNk hkm hxp hxd hne hZ hF hT hBD hdt)

end CapRequests

end VaughtConjecture
