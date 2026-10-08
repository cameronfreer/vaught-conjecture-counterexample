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
  `CapRequests.capLiftProvisionOf_admits_donor`, at every grade from the cap
  `CapRequests.liftProvisionsOf_admits_donor`), from the condition, with `Z` and `F` empty and
  the cells of `T` off the private coatom: at the positive caps, a prescribed profile out of the
  class is matched by any fill along it, and one in the class is correct; the cap is capped at the
  larger of the cap of the lift and `h`.

* **A small value at a top obstructs** (`CapRequests.not_botLiftProvisionOf_admits_donor`, with
  `CapRequests.orbitMap_lt_orbitMap_of_lt`): a common-face cell `a` of the grade of the cap,
  dominated by the cap, with `f a` at most the replaced marker value, and a cell `y` of `T` not `⊥`
  with key below that of `f a`, leave no admitted lift: the lift is in the class, and its code reads
  the marker value at least the code of `f a`, strictly above that of `f y`.  So without a
  condition like `CapRequests.DonorTopsDominateAt` the lift fails also in the class form, at a
  small value rather than at `⊥`.

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

/-- **The lift provision at the positive caps from the donor coatom for the admitted states**, at
every grade `k` from the cap, when the tops of the donor dominate the common face: a prescribed
profile out of the class is matched by the fill along it; one in the class is correct, and the
fill along it is capped at the larger of the cap of the lift and the label of the condition. -/
theorem capLiftProvisionOf_admits_donor (hm : 0 < m)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hZ : r.Z = ∅) (hF : r.F = ∅)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hBD : ∀ d ∈ B, d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k))
    (hdom : DonorTopsDominateAt r B xp xd k) :
    CapLiftProvisionOf (r.Admits B ∅) k xd := fun h₀ hh₀ _ hb P hP f hf hfP ↦ by
  classical
  have hk0 : 0 < k := (I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap).trans_le hNk
  have hPc := mem_cat.mp (mem_rowCat.mp hP).1
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxd hh₀ hPc.1 hf hfP
  by_cases hcl : ∀ d ∈ B, hat I k P d ≠ ⊥
  swap
  · push Not at hcl
    obtain ⟨d, hdB, hd⟩ := hcl
    rw [hat_of_le (hBD d hdB).2] at hd
    have hWd : W d = ⊥ := by
      have e := hWP d
      rw [hd, min_bot_left, min_eq_bot] at e
      exact e.resolve_right hb.ne'
    exact ⟨W, hW, hWf, hWP, orbitCode_mem_rowCat_admits_of_eq_bot hW hdB (hBD d hdB).2 hWd⟩
  have hPcorr : r.IsCorrect (hat I k P) :=
    (mem_rowCat.mp hP).2 (inBottomClass_empty_iff_forall.mpr hcl)
  have hfB : ∀ d ∈ B, f d ≠ ⊥ := fun d hdB hfd ↦ by
    have e := hfP d (hBD d hdB)
    rw [hfd, min_bot_left] at e
    have hPd : P d ≠ ⊥ := by
      have := hcl d hdB
      rwa [hat_of_le (hBD d hdB).2] at this
    exact (min_eq_bot.mp e.symm).elim hPd hb.ne'
  obtain ⟨h, hh, hle, hhT⟩ := hdom f hf hfB
  set h' := max h₀ h with hh'def
  have hh' : IsSelfVisible k h' := hh₀.max hh
  set N := I.amalgam.toCellScheme.grade r.cap
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
    then min (W d) h' else W d with hW'def
  have hW'cut : IsCutLawful I k W' := hW.capAboveLe hxp hxd hne hh' fun d hd hdC hdN ↦ by
    rw [hWf d hd]; exact (hle d hd hdC hdN).trans (le_max_right _ _)
  have hW'D (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) : W' d = f d := by
    simp only [hW'def]
    split_ifs with hZ'
    · rw [hWf d hd]; exact min_eq_left ((hle d hd hZ'.1 hZ'.2).trans (le_max_right _ _))
    · exact hWf d hd
  have hW'h (d : Fin I.amalgam.card) : min (W' d) h₀ = min (W d) h₀ := by
    simp only [hW'def]
    split_ifs
    · rw [min_assoc, min_eq_right (le_max_left h₀ h)]
    · rfl
  have hW'cap : W' r.cap ≤ h' := by
    simp only [hW'def]
    split_ifs
    · exact min_le_right _ _
    · rename_i hn
      exact absurd ⟨hcapC, le_rfl⟩ hn
  have hNN : r.N ≤ N := hgr.le_grade_cap
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := ⟨hcapC, hNk⟩
  have hcorr : r.IsCorrect (hat I k W') := by
    by_cases hc : W' r.cap ≤ h₀
    · -- below the cap of the lift: the state capped at its cap is that of `P`
      have hPsv : IsSelfVisible N (P r.cap) := by
        have := (Rows.isLawfulBelow_iff.mp (hPc.1.erase hxp)).orderly ⟨r.cap, hcb⟩
        change IsSelfVisible (I.amalgam.toCellScheme.grade r.cap) (P r.cap) at this
        exact this
      set s : Prof I := fun d ↦ min (hat I k P d) h₀
      have hs : r.IsCorrect s := hPcorr.cap hgr.off_le (hh₀.mono (hNN.trans hNk))
      have hcap' : W' r.cap = min (P r.cap) h₀ := by
        rw [← min_eq_left hc, hW'h, hWP]
      have hs'cap : hat I k W' r.cap = s r.cap := by
        simp only [s, hat_of_le hNk, hcap']
      have hs'h (d : Fin I.amalgam.card) : min (hat I k W' d) h₀ = min (s d) h₀ := by
        simp only [s]
        rw [min_assoc, min_self]
        exact min_hat_eq (fun e ↦ (hW'h e).trans (hWP e)) d
      refine hs.of_min_eq hs'cap ?_ (fun x ↦ ?_) hgr.off_le
      · simp only [s, hat_of_le hNk]
        exact (hPsv.min (hh₀.mono hNk)).mono hNN
      · have hsc : s r.cap = min (P r.cap) h₀ := by simp only [s, hat_of_le hNk]
        rw [hs'cap, hsc]
        calc min (hat I k W' x) (min (P r.cap) h₀)
            = min (min (hat I k W' x) h₀) (P r.cap) := by
              rw [min_comm (P r.cap) h₀, ← min_assoc]
          _ = min (min (s x) h₀) (P r.cap) := by rw [hs'h]
          _ = min (s x) (min (P r.cap) h₀) := by
              simp only [s]
              rw [min_comm (P r.cap) h₀, ← min_assoc (min (hat I k P x) h₀) h₀ (P r.cap),
                min_assoc (hat I k P x) h₀ h₀, min_self]
    · -- above the cap of the lift: the cap is at most `h`, below the tops
      have hh'h : h' = h := by
        refine max_eq_right ?_
        by_contra hlt
        exact hc (hW'cap.trans_eq (max_eq_left (le_of_lt (not_le.mp hlt))))
      refine isCorrect_of_forall (fun z hz ↦ by simp [hZ] at hz)
        (fun f' hf' ↦ by simp [hF] at hf') fun y hy ↦ ?_
      rw [hat_of_le ((hgr.grade_le_of_mem_T y hy).trans hNk), hW'D y (hT y hy).2]
      refine (min_le_right _ _).trans ?_
      rw [hat_of_le hNk]
      exact (hW'cap.trans_eq hh'h).trans (hhT y hy)
  refine ⟨W', hW'cut, fun d hd ↦ hW'D d hd, fun d ↦ (hW'h d).trans (hWP d),
    rowCat_isCorrect_subset_admits (orbitCode_mem_rowCat hgr (hNN.trans hNk) hW'cut hcorr)⟩

/-- **The lift provisions from the donor coatom for the admitted states at every grade from the
cap** (the shape of the input `hdon` of the class-form engine): from the domination of the common
face by the tops of the donor at every such grade, with `Z` and `F` empty, the cells of `T` on the
donor side off the private coatom, and the cells of `B` on the donor side of grade at most that of
the cap. -/
theorem liftProvisionsOf_admits_donor (hm : 0 < m)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hZ : r.Z = ∅) (hF : r.F = ∅)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      I.amalgam.toCellScheme.scope y ⊆ univ.erase xd)
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.scope d ⊆ univ.erase xd ∧
      I.amalgam.toCellScheme.grade d ≤ I.amalgam.toCellScheme.grade r.cap)
    (hdom : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 →
      DonorTopsDominateAt r B xp xd k) :
    ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 →
      BotLiftProvisionOf (r.Admits B ∅) k xd ∧ CapLiftProvisionOf (r.Admits B ∅) k xd := by
  intro k hNk hkm
  have hT' : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp ∧
      y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) := fun y hy ↦
    ⟨(hT y hy).1, (hT y hy).2, (hgr.grade_le_of_mem_T y hy).trans hNk⟩
  have hBD : ∀ d ∈ B, d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) := fun d hd ↦
    ⟨(hB d hd).1, (hB d hd).2.trans hNk⟩
  exact ⟨botLiftProvisionOf_admits_donor hm hgr hcapC hNk hkm hxp hxd hne hZ hF hT' hBD
      (hdom k hNk hkm),
    capLiftProvisionOf_admits_donor hm hgr hcapC hNk hkm hxp hxd hne hZ hF hT' hBD
      (hdom k hNk hkm)⟩

/-- **The orbit map separates keys**: a label below a key of `w` in the key order goes strictly
below it. -/
theorem orbitMap_lt_orbitMap_of_lt {k : ℕ} {w : Fin I.amalgam.card → Label.{u}}
    {x y : Label.{u}} (hx0 : x ≠ ⊥) (hy : IsKey k w y)
    (hxy : visibilityReplace k k x < visibilityReplace k k y) :
    orbitMap k w x < orbitMap k w y := by
  by_contra hle
  rw [not_lt] at hle
  have h := monotone_visibilityReplace (k := k) le_rfl hle
  rw [visibilityReplace_orbitMap hy.ne_bot, visibilityReplace_orbitMap hx0,
    gridPoint_le_gridPoint] at h
  exact absurd (codeBlock_lt_codeBlock hx0 hy hxy) (not_lt.mpr h)

/-- **A small value at a top obstructs the lift at `⊥` in the class form.**  Let a cell `a` of the
grade of the cap, with scope inside that of the cap, be dominated by the cap, and let `f`, lawful
below the donor coatom and not `⊥` on `B` (below the donor coatom), satisfy `f a ≤ vR N R (f r)` at
the marker `r` (below the donor coatom), and be not `⊥` at a cell `y` of `T` whose key lies below
that of `f a`.  Then no lift is admitted: the lift is in the class, its cap is at least `f a`, so
its code reads the marker value at least the code of `f a`, strictly above the code of `f y`. -/
theorem not_botLiftProvisionOf_admits_donor (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp) {a : Fin I.amalgam.card}
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope r.cap)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade r.cap)
    (hdom : r.CapDominates a) {f : Prof I}
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
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := ⟨hcapC, hNk⟩
  have hle : W a ≤ W r.cap := le_cap_of_capDominates (hW.erase hxp) hcb has hag hdom
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

end CapRequests

end VaughtConjecture
