/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CapRequestsDonorFace

/-!
# The donor lift provisions for the states admitted in a bottom class

Roadmap, Layer 3 ((R3), (R4) of the table of 3.4); the lift provisions from the donor coatom for
the states admitted in the bottom class with no prescribed bottoms (`CapRequests.Admits B ∅`:
correct as soon as no cell of `B` is `⊥`).

Let `I` be a seed on `m + 2` points, `r` cap requests on its amalgam with the cap of scope the
private coatom `Cp = univ.erase xp` and grade `N`, `Dd = univ.erase xd` the donor coatom, and `B` a
set of cells below the donor coatom at the grade `k`.  A labelling `f` lawful below the donor
coatom and `⊥` at a cell of `B` is lifted by any fill: the lift is out of the class.  A labelling
not `⊥` on `B` is lifted by the fill of the private coatom with its cells of grade at least `N`
capped at a label `h`: lawful as soon as the common face carries no value above `h` at the grades
at least `N` (`ProfileTower.IsCutLawful.capAboveLe`, the capping of
`ProfileTower.IsCutLawful.capAbove` without `hface`), and correct as soon as the cells of `T` are at
least `h` (the marker value is at most the capped cap).  Compiled in this repository (theorem
named):

* **The tops of the donor dominate the common face** (`CapRequests.DonorTopsDominateAt`, a named
  condition on the seed and the requests at the grade `k`): every labelling lawful below the donor
  coatom and not `⊥` on `B` has a label `h`, self-visible at `k`, at least its values at the cells
  of the common face of grade at least `N` and at most its values at the cells of `T`.
* **The lift provisions in the class form** (`CapRequests.botLiftProvisionOf_admits_donor`,
  `CapRequests.capLiftProvisionOf_admits_donor`), from the condition, with `Z` and `F` empty and
  the cells of `T` off the private coatom: at the positive caps, a prescribed profile out of the
  class is matched by any fill along it, and one in the class is correct; the cap is capped at the
  larger of the cap of the lift and `h`.

The condition is what the obstruction of `VaughtConjecture.Continuation.CapRequestsDonorFace`
leaves: there a cell of `T` at `⊥` (out of the class here) or below the forced value of the cap
breaks the lift; here the cells of `T` are at least every common-face value above the grade of
the cap.

## Placement

The (R3)/(R4) instances of the engine of the restricted catalogue (`roadmap/README.md`, Layer 3,
3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **Capping the private cells above a grade at a label above the common face keeps a profile
lawful on the cut**: as `ProfileTower.IsCutLawful.capAbove`, without `hface`, when the cells of the
common face of grade at least `N` below the donor coatom carry values at most `h`. -/
theorem IsCutLawful.capAboveLe {xp xd : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {N k : ℕ}
    {W : Prof I} (hW : IsCutLawful I k W) {h : Label.{u}} (hh : IsSelfVisible k h)
    (hle : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k),
      I.amalgam.toCellScheme.scope d ⊆ univ.erase xp → N ≤ I.amalgam.toCellScheme.grade d →
        W d ≤ h) :
    IsCutLawful I k fun d ↦
      if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
      then min (W d) h else W d := by
  classical
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
    then min (W d) h else W d
  have hD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W' d := by
    refine (Rows.isLawfulBelow_congr fun d hd ↦ ?_).mp (hW.erase hxd)
    simp only [W']
    split_ifs with hZ
    · exact (min_eq_left (hle d hd hZ.1 hZ.2)).symm
    · rfl
  have hC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W' d := by
    have hp := Rows.isLawfulBelow_iff.mp (hW.erase hxp)
    have hl := hp.min_const_of_upper
      (fun d : I.amalgam.toCellScheme.below (univ.erase xp, k) ↦
        I.amalgam.toCellScheme.scope d.1 ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d.1)
      (fun d e _ _ ↦ ⟨e.2.1, ?_⟩) (K := k) (fun d ↦ d.2.2) hh
      (fun a b hab hg ha hb ↦ absurd ?_ ha)
    · exact Rows.isLawfulBelow_iff.mpr (by convert hl using 1)
    · rename_i hd hde
      have h' : I.amalgam.toCellScheme.gradedIndex d.1 ≤ I.amalgam.toCellScheme.gradedIndex e.1 :=
        hde
      exact hd.2.trans h'.2
    · change I.amalgam.toCellScheme.scope a.1 ⊆ I.amalgam.toCellScheme.scope b.1 at hab
      change I.amalgam.toCellScheme.grade a.1 = I.amalgam.toCellScheme.grade b.1 at hg
      exact ⟨hab.trans hb.1, hg ▸ hb.2⟩
  exact lawful_pair hxp hxd hne.symm hC hD

end ProfileTower

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {B : Set (Fin I.amalgam.card)} {xp xd : Fin (m + 2)}

/-- The bottom class with no prescribed bottoms: no cell of `B` is `⊥`. -/
theorem inBottomClass_empty_iff_forall {s : Fin I.amalgam.card → Label.{u}} :
    InBottomClass B ∅ s ↔ ∀ d ∈ B, s d ≠ ⊥ := by
  simp [InBottomClass]

variable (r B xp xd) in
/-- **The tops of the donor dominate the common face** at the grade `k`: every labelling lawful
below the donor coatom and not `⊥` on `B` has a label `h`, self-visible at `k`, at least its values
at the cells of the common face of grade at least the grade of the cap, and at most its values at
the cells of `T`. -/
def DonorTopsDominateAt (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ f d) →
    (∀ d ∈ B, f d ≠ ⊥) →
    ∃ h : Label.{u}, IsSelfVisible k h ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k),
        I.amalgam.toCellScheme.scope d ⊆ univ.erase xp →
        I.amalgam.toCellScheme.grade r.cap ≤ I.amalgam.toCellScheme.grade d → f d ≤ h) ∧
      ∀ y ∈ r.T, h ≤ f y

/-- A profile lawful on the cut at `k`, `⊥` at a cell of `B` of grade at most `k`, has its code in
the catalogue of admitted states. -/
theorem code_mem_rowCat_admits_of_eq_bot {k : ℕ} {W : Prof I} (hW : IsCutLawful I k W)
    {d : Fin I.amalgam.card} (hdB : d ∈ B) (hdk : I.amalgam.toCellScheme.grade d ≤ k)
    (hd : W d = ⊥) : code k W ∈ rowCat (r.Admits B ∅) k := by
  have hh := isCutLawful_hat hW
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hh.1.orbitCode fun d ↦ d.2.2,
    hh.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, fun hcl ↦ absurd ?_
      (inBottomClass_empty_iff_forall.mp hcl d hdB)⟩
  rw [hat_of_le hdk, code, orbitCode_apply, orbitMap_eq_bot_iff, hat_of_le hdk, hd]

/-- A profile lawful on the cut at `k`, `⊥` at a cell of `B` of grade at most `k`, has its orbit
code in the catalogue of admitted states. -/
theorem orbitCode_mem_rowCat_admits_of_eq_bot {k : ℕ} {W : Prof I} (hW : IsCutLawful I k W)
    {d : Fin I.amalgam.card} (hdB : d ∈ B) (hdk : I.amalgam.toCellScheme.grade d ≤ k)
    (hd : W d = ⊥) : orbitCode k W ∈ rowCat (r.Admits B ∅) k := by
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hW.1.orbitCode fun d ↦ d.2.2,
    hW.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, fun hcl ↦ absurd ?_
      (inBottomClass_empty_iff_forall.mp hcl d hdB)⟩
  rw [hat_of_le hdk, orbitCode_apply, orbitMap_eq_bot_iff, hd]

/-- The catalogue of correct states lies in the catalogue of admitted states. -/
theorem rowCat_isCorrect_subset_admits {k : ℕ} {R : Prof I} (hR : R ∈ rowCat r.IsCorrect k) :
    R ∈ rowCat (r.Admits B ∅) k :=
  mem_rowCat.mpr ⟨(mem_rowCat.mp hR).1, (mem_rowCat.mp hR).2.admits⟩

/-- **The lift provision at `⊥` from the donor coatom for the admitted states**, at every grade
`k` from the cap, when the tops of the donor dominate the common face. -/
theorem botLiftProvisionOf_admits_donor (hm : 0 < m)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hZ : r.Z = ∅) (hF : r.F = ∅)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hBD : ∀ d ∈ B, d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hdom : DonorTopsDominateAt r B xp xd k) :
    BotLiftProvisionOf (r.Admits B ∅) k xd := fun f hf ↦ by
  classical
  have hk0 : 0 < k := (I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap).trans_le hNk
  obtain ⟨W₀, hW₀, hW₀f, -⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxd
    (isSelfVisible_bot _) (P := fun _ ↦ ⊥)
    ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf fun _ _ ↦ by simp
  by_cases hcl : ∀ d ∈ B, f d ≠ ⊥
  swap
  · push Not at hcl
    obtain ⟨d, hdB, hd⟩ := hcl
    exact ⟨W₀, hW₀, hW₀f, code_mem_rowCat_admits_of_eq_bot hW₀ hdB (hBD d hdB).2
      ((hW₀f d (hBD d hdB)).trans hd)⟩
  obtain ⟨h, hh, hle, hhT⟩ := hdom f hf hcl
  set N := I.amalgam.toCellScheme.grade r.cap
  set W : Prof I := fun d ↦
    if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
    then min (W₀ d) h else W₀ d with hWdef
  have hWcut : IsCutLawful I k W := hW₀.capAboveLe hxp hxd hne hh fun d hd hdC hdN ↦ by
    rw [hW₀f d hd]; exact hle d hd hdC hdN
  have hWD (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) : W d = f d := by
    simp only [hWdef]
    split_ifs with hZ
    · rw [hW₀f d hd]; exact min_eq_left (hle d hd hZ.1 hZ.2)
    · exact hW₀f d hd
  have hWcap : W r.cap ≤ h := by
    simp only [hWdef]
    split_ifs
    · exact min_le_right _ _
    · rename_i hn
      exact absurd ⟨hcapC, le_rfl⟩ hn
  refine ⟨W, hWcut, hWD, rowCat_isCorrect_subset_admits (code_mem_rowCat_of_hat hgr hWcut ?_)⟩
  refine isCorrect_of_forall (fun z hz ↦ by simp [hZ] at hz) (fun f' hf' ↦ by simp [hF] at hf')
    fun y hy ↦ ?_
  rw [hat_of_le ((hgr.grade_le_of_mem_T y hy).trans hNk), hWD y (hT y hy).2]
  refine (min_le_right _ _).trans ?_
  rw [hat_of_le hNk]
  exact hWcap.trans (hhT y hy)

end CapRequests

end VaughtConjecture
