/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsFill
import VaughtConjecture.Continuation.StableRecoveryAdmittedLift

/-!
# The donor lift with a live common face at the grade of the cap

Roadmap, Layer 3 ((R4) of the table of 3.4); the lift provisions from the donor coatom of
`VaughtConjecture.Extension.CapRequestsGrade` when the common face carries a cell of grade at least
that of the cap (the condition `hface` there fails).

Let `I` be a seed on `m + 2` points, `r` cap requests on the cells of its amalgam with the cap on
the private coatom `Cp = univ.erase xp`, and `Dd = univ.erase xd` the donor coatom.  Compiled in
this repository (theorem named):

* **The cap dominates a cell of its grade read below it** (`CapRequests.le_cap_of_capDominates`):
  if every cell of the graded index of the cap reads the cap at least as a cell `a` of the same
  grade with scope inside that of the cap (`CapRequests.CapDominates`), then every labelling lawful
  below a pair containing the cap has `w a ≤ w cap`: availability from `a` reaches a cell of the
  graded index of the cap at least `w a`, and locality there transfers the reading.
* **Where the donor lift at `⊥` breaks** (`CapRequests.not_botLiftProvisionOf_donor`): if a cell
  `a` of the common face of the grade of the cap is dominated by the cap, and some labelling `f`
  lawful below the donor coatom is not `⊥` at `a` and at the marker (on the common face), but is
  `⊥` at a cell of `T`, then no profile lawful on the cut extending `f` has a correct code: the cap
  is at least `f a`, so not `⊥`, and correctness asks the marker value, not `⊥`, to lie below the
  value `⊥` at the cell of `T`.  So the lift provision at `⊥` from the donor coatom fails.  This is
  the prescription that forces the cap above a common-face value: the capping of the private cells
  above the grade of the cap, which sets the cap to `⊥`, is impossible there, and no other lift is
  correct.
* **A common face dead above the grade of the cap** (`CapRequests.IsDeadAbove`,
  `ProfileTower.IsCutLawful.capAbove'`, `CapRequests.botLiftProvisionOf_donor_le'`,
  `CapRequests.capLiftProvisionOf_donor_le'`): when every cell of the common face of grade at least
  that of the cap reads itself as `⊥`, the capping keeps lawfulness and the lift provisions from
  the donor coatom hold as under `hface`, which is the case of no such cell.

## Placement

The (R4) instance of the engine of the restricted catalogue at the reading grades
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

variable (r) in
/-- **The cap dominates a cell `a`**: every cell of the graded index of the cap reads the cap at
least as it reads `a`. -/
def CapDominates (a : Fin I.amalgam.card) : Prop :=
  ∀ u, I.amalgam.toCellScheme.gradedIndex u = I.amalgam.toCellScheme.gradedIndex r.cap →
    I.amalgam.toScheme.rowAt u a ≤ I.amalgam.toScheme.rowAt u r.cap

/-- **A dominated cell lies below the cap** in every labelling lawful below a pair containing the
cap, for a cell `a` of the grade of the cap with scope inside that of the cap. -/
theorem le_cap_of_capDominates {X : Finset (Fin (m + 2)) × ℕ} {w : Fin I.amalgam.card → Label.{u}}
    (hw : I.amalgam.rows.IsLawfulBelow X fun d ↦ w d)
    (hcapX : r.cap ∈ I.amalgam.toCellScheme.below X) {a : Fin I.amalgam.card}
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope r.cap)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade r.cap)
    (hdom : r.CapDominates a) : w a ≤ w r.cap := by
  have hab : I.amalgam.toCellScheme.gradedIndex a ≤ I.amalgam.toCellScheme.gradedIndex r.cap :=
    ⟨has, hag.le⟩
  refine (Rows.le_of_capped_readers (y₃ := r.cap) (y₄ := r.cap) hw hcapX has hag
    fun u hu _ ↦ ?_).1
  have ha : a ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu]
    exact hab
  have hc : r.cap ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu]
  have hrow := hdom u hu
  rw [Scheme.rowAt_of_mem ha, Scheme.rowAt_of_mem hc] at hrow
  exact ⟨ha, hc, hc, hag.ge, hag.ge, hrow, hrow⟩

/-- **The donor lift at `⊥` with a dominated live common-face cell has no correct code.**  Let the
cap have scope inside the private coatom and grade at most `k`, and let `a` be a cell of the grade
of the cap with scope inside that of the cap, dominated by the cap.  If `f` is lawful below the
donor coatom, not `⊥` at `a` and at the marker, both below the donor coatom, and `⊥` at a cell `y`
of `T` below it, then no profile lawful on the grade-`k` cut agreeing with `f` below the donor
coatom has its code in the catalogue of correct states. -/
theorem not_exists_correct_lift_donor (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp) {a : Fin I.amalgam.card}
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope r.cap)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade r.cap)
    (hdom : r.CapDominates a) {f : Prof I}
    (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfa : f a ≠ ⊥)
    (hmk : r.marker ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfm : f r.marker ≠ ⊥)
    {y : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfy : f y = ⊥) :
    ¬ ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k), W d = f d) ∧
        code k W ∈ rowCat r.IsCorrect k := by
  rintro ⟨W, hW, hWf, hc⟩
  have hcorr := (mem_rowCat.mp hc).2
  -- the cap is at least the value at `a`
  have hle : W a ≤ W r.cap :=
    le_cap_of_capDominates (hW.erase hxp) ⟨hcapC, hNk⟩ has hag hdom
  have hWa : W a ≠ ⊥ := by rw [hWf a ha]; exact hfa
  have hWc : W r.cap ≠ ⊥ := ne_bot_of_le_ne_bot hWa hle
  -- the code at a cell of grade at most `k`
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
  · exact hfm (by rw [← hWf _ hmk]; exact h)
  · exact hWc h

/-- **The lift provision at `⊥` from the donor coatom fails** at such a prescription. -/
theorem not_botLiftProvisionOf_donor (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k)
    (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp) {a : Fin I.amalgam.card}
    (has : I.amalgam.toCellScheme.scope a ⊆ I.amalgam.toCellScheme.scope r.cap)
    (hag : I.amalgam.toCellScheme.grade a = I.amalgam.toCellScheme.grade r.cap)
    (hdom : r.CapDominates a) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ f d)
    (ha : a ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfa : f a ≠ ⊥)
    (hmk : r.marker ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfm : f r.marker ≠ ⊥)
    {y : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyk : y ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) (hfy : f y = ⊥) :
    ¬ BotLiftProvisionOf r.IsCorrect k xd := fun hprov ↦
  not_exists_correct_lift_donor hgr hxp hNk hcapC has hag hdom ha hfa hmk hfm hy hyk hfy
    (hprov f hf)

/-! ### A common face dead above the grade of the cap -/

variable (I xp xd) in
/-- The common face of the coatoms `univ.erase xp` and `univ.erase xd` is **dead above the grade
`N`**: every cell of scope inside it and grade at least `N` reads itself as `⊥`. -/
def IsDeadAbove (N : ℕ) : Prop :=
  ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
    N ≤ I.amalgam.toCellScheme.grade d →
      I.amalgam.rows.row d ⟨d, CellScheme.mem_below_gradedIndex _ d⟩ = ⊥

/-- **A common face with no cell above the grade is dead above it**: the condition `hface` of
`VaughtConjecture.Extension.CapRequestsGrade` gives a common face dead above the grade. -/
theorem isDeadAbove_of_forall_lt {N : ℕ}
    (hface : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
      I.amalgam.toCellScheme.grade d < N) : IsDeadAbove I xp xd N :=
  fun d hd hN ↦ absurd hN (not_le.mpr (hface d hd))

/-- **Capping the private cells above a grade changes nothing below the donor coatom** when the
common face is dead above the grade. -/
theorem capped_eq_of_isDeadAbove {N k : ℕ} (hdead : IsDeadAbove I xp xd N) {W : Prof I}
    (hW : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d) {h : Label.{u}}
    {d : Fin I.amalgam.card} (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) :
    (if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
      then min (W d) h else W d) = W d := by
  split_ifs with hZ
  · rw [eq_bot_of_row_self_eq_bot hW hd (hdead d (subset_inter hZ.1 hd.1) hZ.2), min_bot_left]
  · rfl

end CapRequests

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **Capping the private cells above a grade keeps a profile lawful on the cut** when the common
face is dead above the grade (`ProfileTower.IsCutLawful.capAbove` without `hface`). -/
theorem IsCutLawful.capAbove' {xp xd : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {N k : ℕ}
    (hdead : CapRequests.IsDeadAbove I xp xd N)
    {W : Prof I} (hW : IsCutLawful I k W) {h : Label.{u}} (hh : IsSelfVisible k h) :
    IsCutLawful I k fun d ↦
      if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
      then min (W d) h else W d := by
  classical
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
    then min (W d) h else W d
  have hD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W' d :=
    (Rows.isLawfulBelow_congr fun d hd ↦
      (CapRequests.capped_eq_of_isDeadAbove hdead (hW.erase hxd) hd).symm).mp (hW.erase hxd)
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
  {xp xd : Fin (m + 2)}

/-- **The lift provision at `⊥` from the donor coatom at every grade from the cap, over a common
face dead above the grade of the cap** (`CapRequests.botLiftProvisionOf_donor_le` without
`hface`). -/
theorem botLiftProvisionOf_donor_le' (hm : 0 < m)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hdead : IsDeadAbove I xp xd (I.amalgam.toCellScheme.grade r.cap))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) (hgr : r.IsGraded I.amalgam.toCellScheme.grade) :
    BotLiftProvisionOf r.IsCorrect k xd := fun f hf ↦ by
  classical
  have hk0 : 0 < k := (I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap).trans_le hNk
  obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxd (isSelfVisible_bot _)
    (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
    fun _ _ ↦ by simp
  set N := I.amalgam.toCellScheme.grade r.cap
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
    then min (W d) ⊥ else W d with hW'
  have hW'cut : IsCutLawful I k W' := hW.capAbove' hxp hxd hne hdead (isSelfVisible_bot _)
  have hcap0 : W' r.cap = ⊥ := by
    have hZc : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp ∧
        N ≤ I.amalgam.toCellScheme.grade r.cap := ⟨hcapC.le, le_rfl⟩
    rw [hW']
    exact (ite_eq_left hZc).trans (min_bot_right _)
  refine ⟨W', hW'cut, fun d hd ↦ ?_, code_mem_rowCat_of_hat hgr hW'cut
    (isCorrect_of_cap_eq_bot (by rw [hat_of_le hNk, hcap0]))⟩
  exact (capped_eq_of_isDeadAbove hdead (hW.erase hxd) hd).trans (hWf d hd)

/-- **The lift provision at the positive caps from the donor coatom at every grade from the cap,
over a common face dead above the grade of the cap** (`CapRequests.capLiftProvisionOf_donor_le`
without `hface`). -/
theorem capLiftProvisionOf_donor_le' (hm : 0 < m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hdead : IsDeadAbove I xp xd (I.amalgam.toCellScheme.grade r.cap))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) : CapLiftProvisionOf r.IsCorrect k xd :=
    fun h hh _ _ P hP f hf hfP ↦ by
  classical
  have hk0 : 0 < k := (I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap).trans_le hNk
  have hPc := mem_cat.mp (mem_rowCat.mp hP).1
  have hPcorr : r.IsCorrect (hat I k P) := (mem_rowCat.mp hP).2
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom_le hm hk0 hkm hxd hh hPc.1 hf hfP
  set N := I.amalgam.toCellScheme.grade r.cap
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
    then min (W d) h else W d with hW'
  have hW'cut : IsCutLawful I k W' := hW.capAbove' hxp hxd hne hdead hh
  have hW'h (d : Fin I.amalgam.card) : min (W' d) h = min (W d) h := by
    simp only [hW']
    split_ifs
    · rw [min_assoc, min_self]
    · rfl
  have hW'cap : W' r.cap = min (P r.cap) h := by
    have hZc : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp ∧
        N ≤ I.amalgam.toCellScheme.grade r.cap := ⟨hcapC.le, le_rfl⟩
    rw [hW']
    exact (ite_eq_left hZc).trans (hWP r.cap)
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := ⟨hcapC.le, hNk⟩
  have hPsv : IsSelfVisible N (P r.cap) := by
    have := (Rows.isLawfulBelow_iff.mp (hPc.1.erase hxp)).orderly ⟨r.cap, hcb⟩
    change IsSelfVisible (I.amalgam.toCellScheme.grade r.cap) (P r.cap) at this
    exact this
  have hNN : r.N ≤ N := hgr.le_grade_cap
  set s' := hat I k W'
  set s : Prof I := fun d ↦ min (hat I k P d) h
  have hs : r.IsCorrect s := hPcorr.cap hgr.off_le (hh.mono (hNN.trans hNk))
  have hs'cap : s' r.cap = s r.cap := by
    simp only [s', s, hat_of_le hNk, hW'cap]
  have hs'h (d : Fin I.amalgam.card) : min (s' d) h = min (s d) h := by
    simp only [s', s]
    rw [min_assoc, min_self]
    exact min_hat_eq (fun e ↦ (hW'h e).trans (hWP e)) d
  have hcorr : r.IsCorrect s' := by
    refine hs.of_min_eq hs'cap ?_ (fun x ↦ ?_) hgr.off_le
    · simp only [s, hat_of_le hNk]
      exact (hPsv.min (hh.mono hNk)).mono hNN
    · have hsc : s r.cap = min (P r.cap) h := by simp only [s, hat_of_le hNk]
      rw [hs'cap, hsc]
      calc min (s' x) (min (P r.cap) h) = min (min (s' x) h) (P r.cap) := by
            rw [min_comm (P r.cap) h, ← min_assoc]
        _ = min (min (s x) h) (P r.cap) := by rw [hs'h]
        _ = min (s x) (min (P r.cap) h) := by
            simp only [s]
            rw [min_comm (P r.cap) h, ← min_assoc (min (hat I k P x) h) h (P r.cap)]
  refine ⟨W', hW'cut, fun d hd ↦ ?_, fun d ↦ (hW'h d).trans (hWP d),
    orbitCode_mem_rowCat hgr (hNN.trans hNk) hW'cut hcorr⟩
  exact (capped_eq_of_isDeadAbove hdead (hW.erase hxd) hd).trans (hWf d hd)

end CapRequests

end VaughtConjecture
