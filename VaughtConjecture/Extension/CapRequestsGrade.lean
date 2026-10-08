/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedTower
import VaughtConjecture.Extension.CapRequestsTop

/-!
# Cap requests at every grade from the grade of the cap, and the reading

Roadmap, Layer 3 ((R4) of the table of 3.4, the reading through a proper cap); the catalogue of
correct states at every grade `k` from the grade `N` of the cap to the top grade `m + 1`.

Let `I` be a seed on `m + 2` points, `0 < m`, and `r` cap requests on the cells of its amalgam,
graded by the grades of the amalgam, whose cap has scope the **private coatom** `Cp = univ.erase xp`
and grade `N`; `Dd = univ.erase xd` is the **donor coatom**.

* **The fill at every grade** (`ProfileTower.exists_isCutLawful_of_coatom_le`): the fills of the
  other coatom at the grades `k ≤ m` and at `m + 1`, in one statement.
* **Capping the private cells above a grade** (`ProfileTower.IsCutLawful.capAbove`): capping at `h`
  the cells of scope inside `Cp` and grade at least `N` keeps a profile lawful on the grade-`k` cut,
  provided the **common face carries no cell of grade at least `N`** (`hface`).  Below `Cp` these
  cells form an upper set closed under availability; below `Dd` there are none.
* **The lift provisions from the donor coatom at every grade `N ≤ k ≤ m + 1`**
  (`CapRequests.botLiftProvisionOf_donor_le`, `CapRequests.capLiftProvisionOf_donor_le`), under
  `hface`: the private coatom is filled and its cells of grade at least `N` capped at the cap of the
  lift; correctness of the splice follows as at the top grade (`CapRequests.IsCorrect.of_min_eq`),
  and the orbit code is a plain image under a witness bounded by `k ≥ N`
  (`CapRequests.IsCorrect.comp`).  At the top grade `hface` holds by the size of the common face.
  Without `hface` the cap is forced above the labels of the common face at its grade by
  availability, and correctness is not free from the donor side (argued; not compiled).
* **The fills from the private coatom at a grade** (`CapRequests.CapFillBotAt`,
  `CapRequests.CapFillPosAt`) give the lift provisions from it
  (`CapRequests.botLiftProvisionOf_private_le`, `CapRequests.capLiftProvisionOf_private_le`).
* **The reading** (`CompletionBelowFullGrade.lt_label_of_hasAdmittedRows`,
  `CompletionBelowFullGrade.label_eq_of_hasAdmittedRows`): in a completion whose rows of full scope
  at the grades `≥ N` are correct, every labelling lawful below `(univ, N)` with the marker at
  `λ + i` below a cap at least `λ + R` reads every cell of `T` (of grade at most `N`) above every
  `γ < λ + R`, and every cell of `F` exactly from its reference: availability from the cap gives a
  cell of `(univ, N)` at least the cap, and recognition there gives a correct state
  (`CompletionBelowFullGrade.adm_of_isLawfulBelow`, `CapRequests.IsCorrect.lt_label`,
  `CapRequests.IsCorrect.label_eq`).

## Placement

The (R4) instance of the engine of the restricted catalogue at the reading grades
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The fill of the other coatom at every grade `0 < k ≤ m + 1`**, for `0 < m`. -/
theorem exists_isCutLawful_of_coatom_le (hm : 0 < m) {k : ℕ} (hk : 0 < k) (hkm : k ≤ m + 1)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {h : Label.{u}}
    (hh : IsSelfVisible k h) {P : Prof I} (hP : IsCutLawful I k P) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, k) fun d ↦ f d)
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), min (f d) h = min (P d) h) :
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, k), W d = f d) ∧
      ∀ d, min (W d) h = min (P d) h := by
  rcases Nat.lt_or_eq_of_le hkm with hlt | rfl
  · exact exists_isCutLawful_of_coatom hk (by omega) hx hh hP hf hfP
  · exact exists_isCutLawful_of_coatom_top hm hx hh hP hf hfP

/-- The splice is idempotent. -/
theorem hat_hat (k : ℕ) (R : Prof I) : hat I k (hat I k R) = hat I k R := funext fun d ↦ by
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [hat_of_le hd, hat_of_le hd]
  · rw [hat_of_lt (not_le.mp hd), hat_of_lt (not_le.mp hd)]

/-- **Capping the private cells above a grade keeps a profile lawful on the cut**: capping at `h`
(self-visible at `k`) the cells of scope inside the coatom `univ.erase xp` and grade at least `N`
keeps a profile lawful on the grade-`k` cut, when the common face of the two coatoms carries no
cell of grade at least `N`. -/
theorem IsCutLawful.capAbove {xp xd : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {N k : ℕ}
    (hface : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
      I.amalgam.toCellScheme.grade d < N)
    {W : Prof I} (hW : IsCutLawful I k W) {h : Label.{u}} (hh : IsSelfVisible k h) :
    IsCutLawful I k fun d ↦
      if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
      then min (W d) h else W d := by
  classical
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d
    then min (W d) h else W d
  -- Below the donor coatom no cell is capped.
  have hD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W' d := by
    refine (Rows.isLawfulBelow_congr fun d hd ↦ ?_).mp (hW.erase hxd)
    have hZ : ¬ (I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧
        N ≤ I.amalgam.toCellScheme.grade d) := fun hZ ↦
      absurd hZ.2 (not_le.mpr (hface d (subset_inter hZ.1 hd.1)))
    simp only [W', hZ, ite_false]
  -- Below the private coatom the capped cells form an upper set closed under availability.
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

/-! ### The lift provisions from the donor coatom at every grade from the cap -/

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

/-- The splice at `k` of the orbit code at `k` is the plain image of the splice under the orbit
map. -/
theorem hat_orbitCode (k : ℕ) (W : Prof I) :
    hat I k (orbitCode k W) = orbitMap k W ∘ hat I k W := funext fun d ↦ by
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [hat_of_le hd, Function.comp_apply, hat_of_le hd, orbitCode_apply]
  · rw [hat_of_lt (not_le.mp hd), Function.comp_apply, hat_of_lt (not_le.mp hd), orbitMap_bot]

/-- **A profile with correct splice has its orbit code in the catalogue of correct states**, at a
grade `k` at least the threshold, when lawful on the cut. -/
theorem orbitCode_mem_rowCat (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hNk : r.N ≤ k) {W : Prof I} (hW : IsCutLawful I k W) (hc : r.IsCorrect (hat I k W)) :
    orbitCode k W ∈ rowCat r.IsCorrect k := by
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hW.1.orbitCode fun d ↦ d.2.2,
    hW.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, ?_⟩
  rw [hat_orbitCode]
  exact hc.comp (isWitness_orbitMap k W) hNk hgr.off_le

/-- **A profile with correct splice has its code in the catalogue of correct states.** -/
theorem code_mem_rowCat_of_hat (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    {W : Prof I} (hW : IsCutLawful I k W) (hc : r.IsCorrect (hat I k W)) :
    code k W ∈ rowCat r.IsCorrect k := by
  have hh := isCutLawful_hat hW
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hh.1.orbitCode fun d ↦ d.2.2,
    hh.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, ?_⟩
  have e : code k (hat I k W) = code k W := by
    unfold code
    rw [hat_hat]
  have h := (hc.code hgr k).hat hgr k
  rwa [e] at h

/-- A cell below the donor coatom is not capped, when the common face carries no cell of grade at
least `N`. -/
theorem not_capped_of_mem_below {N k : ℕ}
    (hface : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
      I.amalgam.toCellScheme.grade d < N)
    {d : Fin I.amalgam.card} (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k)) :
    ¬ (I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∧ N ≤ I.amalgam.toCellScheme.grade d) :=
  fun hZ ↦ absurd hZ.2 (not_le.mpr (hface d (subset_inter hZ.1 hd.1)))

/-- **The lift provision at `⊥` from the donor coatom at every grade from the cap**: the private
coatom is filled and its cells of grade at least the grade of the cap capped at `⊥`, so the cap is
`⊥`; the common face carries no cell of grade at least that of the cap. -/
theorem botLiftProvisionOf_donor_le (hm : 0 < m)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hface : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
      I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
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
  have hW'cut : IsCutLawful I k W' := hW.capAbove hxp hxd hne hface (isSelfVisible_bot _)
  have hcap0 : W' r.cap = ⊥ := by
    have hZc : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp ∧
        N ≤ I.amalgam.toCellScheme.grade r.cap := ⟨hcapC.le, le_rfl⟩
    rw [hW']
    exact (ite_eq_left hZc).trans (min_bot_right _)
  refine ⟨W', hW'cut, fun d hd ↦ ?_, code_mem_rowCat_of_hat hgr hW'cut
    (isCorrect_of_cap_eq_bot (by rw [hat_of_le hNk, hcap0]))⟩
  simp only [hW', not_capped_of_mem_below hface hd, ite_false]
  exact hWf d hd

/-- **The lift provision at the positive caps from the donor coatom at every grade from the cap**:
the private coatom is filled at the ambient of the prescribed profile `P` (whose splice is correct)
and its cells of grade at least the grade of the cap capped at `h`; the splice agrees with that of
`P` capped at `h`, its cap is that of `min (hat P) h`, and it is correct because `min (hat P) h`
is; the orbit code is a plain image of the splice under a witness bounded by `k`. -/
theorem capLiftProvisionOf_donor_le (hm : 0 < m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp) {k : ℕ}
    (hNk : I.amalgam.toCellScheme.grade r.cap ≤ k) (hkm : k ≤ m + 1)
    (hface : ∀ d, I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase xd →
      I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
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
  have hW'cut : IsCutLawful I k W' := hW.capAbove hxp hxd hne hface hh
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
  -- The cap of `P` is self-visible at its grade.
  have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) := ⟨hcapC.le, hNk⟩
  have hPsv : IsSelfVisible N (P r.cap) := by
    have := (Rows.isLawfulBelow_iff.mp (hPc.1.erase hxp)).orderly ⟨r.cap, hcb⟩
    change IsSelfVisible (I.amalgam.toCellScheme.grade r.cap) (P r.cap) at this
    exact this
  have hNN : r.N ≤ N := hgr.le_grade_cap
  -- The splices.
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
  simp only [hW', not_capped_of_mem_below hface hd, ite_false]
  exact hWf d hd

/-! ### The lift provisions from the private coatom at a grade -/

variable (r xp) in
/-- **The fill at `⊥` from the private coatom at the grade `k`**: every labelling lawful below the
private coatom at `k` is, below it, a profile lawful on the grade-`k` cut with correct splice. -/
def CapFillBotAt (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), W d = f d) ∧
      r.IsCorrect (hat I k W)

variable (r xp) in
/-- **The fill at the positive caps from the private coatom at the grade `k`**: for every cap `h`
self-visible and short at `k` and every profile `P` lawful on the cut with correct splice, every
labelling lawful below the private coatom agreeing with `P` capped at `h` below it is, below it, a
profile lawful on the cut with correct splice agreeing with `P` capped at `h`. -/
def CapFillPosAt (k : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I k P → r.IsCorrect (hat I k P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), min (f d) h = min (P d) h) →
      ∃ W : Prof I, IsCutLawful I k W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), W d = f d) ∧
        (∀ d, min (W d) h = min (P d) h) ∧ r.IsCorrect (hat I k W)

/-- **The lift provision at `⊥` from the private coatom at `k`**, from the fill. -/
theorem botLiftProvisionOf_private_le (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hfill : CapFillBotAt r xp k) : BotLiftProvisionOf r.IsCorrect k xp := fun f hf ↦ by
  obtain ⟨W, hW, hWf, hWc⟩ := hfill f hf
  exact ⟨W, hW, hWf, code_mem_rowCat_of_hat hgr hW hWc⟩

/-- **The lift provision at the positive caps from the private coatom at `k ≥ N`**, from the
fill. -/
theorem capLiftProvisionOf_private_le (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hNk : r.N ≤ k) (hfill : CapFillPosAt r xp k) : CapLiftProvisionOf r.IsCorrect k xp :=
    fun h hh hs hb P hP f hf hfP ↦ by
  obtain ⟨W, hW, hWf, hWP, hWc⟩ := hfill h hh hs hb P (mem_cat.mp (mem_rowCat.mp hP).1).1
    (mem_rowCat.mp hP).2 f hf hfP
  exact ⟨W, hW, hWf, hWP, orbitCode_mem_rowCat hgr hNk hW hWc⟩

end CapRequests

/-! ### The reading at the grade of the cap -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {F : CompletionBelowFullGrade I}
  {r : CapRequests (Fin I.amalgam.card)}

/-- **Recognition at a cell reached from the cap.**  In a completion whose rows of full scope at
the grades `≥ N` are correct, `N` the grade of the cap, every labelling `q` lawful below
`(univ, N)` has a cell `u` of graded index `(univ, N)` with `q u` at least the label of the cap,
where the splice at `N` of the old part of `q`, capped at `q u`, is correct. -/
theorem exists_isCorrect_of_hasAdmittedRows (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hF : F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) r.IsCorrect)
    {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), I.amalgam.toCellScheme.grade r.cap) fun z ↦ q z) :
    ∃ u, q (F.embed r.cap) ≤ q u ∧ r.IsCorrect fun d ↦
      min (hat I (I.amalgam.toCellScheme.grade r.cap) (fun e ↦ q (F.embed e)) d) (q u) := by
  set N := I.amalgam.toCellScheme.grade r.cap
  obtain ⟨-, -, hav⟩ := Rows.isLawfulBelow_iff_forall.mp hq
  have hk0 : 0 < N := I.amalgam.isWellFormed.isWellFormed.grade_pos r.cap
  have hkm : N < m + 2 := I.grade_lt r.cap
  obtain ⟨t, ht⟩ := F.isLegalBelowFullGrade.exists_gradedIndex_eq
    ((univ : Finset (Fin (m + 2))), N)
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, hk0,
      by simp only [card_univ, Fintype.card_fin]; omega⟩ hkm
  have htb : t ∈ F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), N) := by
    rw [CellScheme.mem_below, ht]
  have hst : F.scheme.toCellScheme.scope (F.embed r.cap) ⊆ F.scheme.toCellScheme.scope t := by
    rw [show F.scheme.toCellScheme.scope t = univ from congrArg Prod.fst ht]
    exact subset_univ _
  have hgt : F.scheme.toCellScheme.grade (F.embed r.cap) = F.scheme.toCellScheme.grade t := by
    rw [F.isLowerEmbedding.grade_eq]
    exact (congrArg Prod.snd ht).symm
  obtain ⟨u, hu, hcu⟩ := hav (F.embed r.cap) t htb hst hgt
  exact ⟨u, hcu, adm_of_isLawfulBelow (fun _ _ _ hs hw ↦ hs.map hgr hw) hF le_rfl hq (hu.trans ht)⟩

/-- **The reading of the tops (R4)**: in a completion whose rows of full scope at the grades at
least the grade `N` of the cap are correct, every labelling `q` lawful below `(univ, N)` with the
marker (of grade at most `N`) at `λ + i`, `i < N`, at most the cap, and the cap at least `λ + R`,
reads every cell of `T` of grade at most `N` above every `γ < λ + R`. -/
theorem lt_label_of_hasAdmittedRows (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hF : F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) r.IsCorrect)
    {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), I.amalgam.toCellScheme.grade r.cap) fun z ↦ q z)
    {y : Fin I.amalgam.card} (hy : y ∈ r.T)
    (hyN : I.amalgam.toCellScheme.grade y ≤ I.amalgam.toCellScheme.grade r.cap)
    {lam : Ordinal.{u}} (hlam : Order.IsSuccPrelimit lam) {i : ℕ} (hi : i < r.N)
    (ha : q (F.embed r.marker) = ((lam + i : Ordinal.{u}) : Label.{u}))
    (hmc : q (F.embed r.marker) ≤ q (F.embed r.cap))
    (hc : ((lam + r.R : Ordinal.{u}) : Label.{u}) ≤ q (F.embed r.cap)) {γ : Label.{u}}
    (hγ : γ < ((lam + r.R : Ordinal.{u}) : Label.{u})) : γ < q (F.embed y) := by
  obtain ⟨u, hcu, hcorr⟩ := exists_isCorrect_of_hasAdmittedRows hgr hF hq
  have hmN := hgr.grade_marker_le
  refine (hcorr.lt_label hy hlam hi ?_ ?_ hγ).trans_le ?_
  · simp only [hat_of_le hmN]
    rw [min_eq_left (hmc.trans hcu), ha]
  · simp only [hat_of_le le_rfl]
    rw [min_eq_left hcu]
    exact hc
  · simp only [hat_of_le hyN]
    exact min_le_left _ _

/-- **The reading of the proper cells (R4)**: under the hypotheses of the reading of the tops, every
cell `f` of `F` of grade at most `N`, with its reference (of grade at most `N`) at `μ + k`, `k < N`,
and `μ + off f` below the cap, is read as `μ + off f`. -/
theorem label_eq_of_hasAdmittedRows (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hF : F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) r.IsCorrect)
    {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow
      ((univ : Finset (Fin (m + 2))), I.amalgam.toCellScheme.grade r.cap) fun z ↦ q z)
    {f : Fin I.amalgam.card} (hf : f ∈ r.F)
    (hfN : I.amalgam.toCellScheme.grade f ≤ I.amalgam.toCellScheme.grade r.cap)
    {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {k : ℕ} (hk : k < r.N)
    (href : q (F.embed (r.ref f)) = ((μ + k : Ordinal.{u}) : Label.{u}))
    (hrefc : q (F.embed (r.ref f)) ≤ q (F.embed r.cap))
    (hlt : ((μ + r.off f : Ordinal.{u}) : Label.{u}) < q (F.embed r.cap)) :
    q (F.embed f) = ((μ + r.off f : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨u, hcu, hcorr⟩ := exists_isCorrect_of_hasAdmittedRows hgr hF hq
  have hrN := hgr.grade_ref_le f hf
  have h := hcorr.label_eq hf hμ hk ?_ ?_
  · simp only [hat_of_le hfN] at h
    have hv := hlt.trans_le hcu
    exact eq_of_min_eq_of_lt ((min_eq_left hv.le).trans h.symm) hv
  · simp only [hat_of_le hrN]
    rw [min_eq_left (hrefc.trans hcu), href]
  · simp only [hat_of_le le_rfl]
    rw [min_eq_left hcu]
    exact hlt

end CompletionBelowFullGrade

end VaughtConjecture

/-! ### The correct completion from the grade of the cap -/

namespace VaughtConjecture

open Finset Label ProfileTower CapRequests

/-- **The correct completion from the grade of the cap, from the lift provisions of the donor
coatom (R4)**: for a seed on `m + 2 ≥ 4` points and cap requests graded by the grades of the
amalgam, with the cap of scope the private coatom `univ.erase xp` and grade `N ≥ 3`, the lift
provisions from the other coatom (`hdon`) and the fills from the private coatom at every grade
`N ≤ k ≤ m + 1`, and the code of the glued labelling at `m + 1` with correct splice, some
completion below the full grade has every row of full scope at the grades `≥ N` correct. -/
theorem Seed.exists_correctCompletion' {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hm : 2 ≤ m)
    {r : CapRequests (Fin I.amalgam.card)} (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {xp : Fin (m + 2)} (hN3 : 3 ≤ I.amalgam.toCellScheme.grade r.cap)
    (hdon : ∀ x ∈ (Pts : Finset (Fin (m + 2))), x ≠ xp → ∀ k,
      I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 →
        BotLiftProvisionOf r.IsCorrect k x ∧ CapLiftProvisionOf r.IsCorrect k x)
    (hbot : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillBotAt r xp k)
    (hpos : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillPosAt r xp k)
    (hlab : r.IsCorrect (hat I (m + 1) (code (m + 1) fun d ↦ I.amalgam.label d))) :
    ∃ F : CompletionBelowFullGrade I,
      F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) r.IsCorrect := by
  have hNN : r.N ≤ I.amalgam.toCellScheme.grade r.cap := hgr.le_grade_cap
  refine I.exists_rowCompletion hm hN3 (fun k hk hkm x hx ↦ ?_) (fun k hk hkm x hx ↦ ?_)
    (fun k _ R hR ↦ code_mem_rowCat_of_mem_rowCat hgr hR) fun _ ↦ hlab
  · by_cases hxe : x = xp
    · subst hxe
      exact botLiftProvisionOf_private_le hgr (hbot k hk hkm)
    · exact (hdon x hx hxe k hk hkm).1
  · by_cases hxe : x = xp
    · subst hxe
      exact capLiftProvisionOf_private_le hgr (hNN.trans hk) (hpos k hk hkm)
    · exact (hdon x hx hxe k hk hkm).2

/-- **The correct completion from the grade of the cap (R4)**: for a seed on `m + 2 ≥ 4` points and
cap requests graded by the grades of the amalgam, with the cap of scope the private coatom
`univ.erase xp` and grade `N ≥ 3`, the common face of the coatoms carrying no cell of grade at
least `N`, the fills from the private coatom at every grade `N ≤ k ≤ m + 1`, and the code of the
glued labelling at `m + 1` with correct splice, some completion below the full grade has every row
of full scope at the grades `≥ N` correct.  The lift provisions from the donor coatom are
`CapRequests.botLiftProvisionOf_donor_le` and `CapRequests.capLiftProvisionOf_donor_le`; the
downward clause is `CapRequests.code_mem_rowCat_of_mem_rowCat`. -/
theorem Seed.exists_correctCompletion {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hm : 2 ≤ m)
    {r : CapRequests (Fin I.amalgam.card)} (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {xp : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp)
    (hN3 : 3 ≤ I.amalgam.toCellScheme.grade r.cap)
    (hface : ∀ x ∈ (Pts : Finset (Fin (m + 2))), x ≠ xp → ∀ d,
      I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase x →
      I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
    (hbot : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillBotAt r xp k)
    (hpos : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillPosAt r xp k)
    (hlab : r.IsCorrect (hat I (m + 1) (code (m + 1) fun d ↦ I.amalgam.label d))) :
    ∃ F : CompletionBelowFullGrade I,
      F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) r.IsCorrect :=
  I.exists_correctCompletion' hm hgr hN3 (fun x hx hxe k hk hkm ↦
    ⟨botLiftProvisionOf_donor_le (by omega) hcapC hk hkm (hface x hx hxe) hxp hx hxe hgr,
      capLiftProvisionOf_donor_le (by omega) hgr hcapC hk hkm (hface x hx hxe) hxp hx hxe⟩)
    hbot hpos hlab

/-- **The reading of the tops from the private fills (R4)**: under the hypotheses of
`Seed.exists_correctCompletion`, some completion below the full grade reads, in every labelling
`q` lawful below `(univ, N)` with the marker at `λ + i` (`i < N`) at most the cap and the cap at
least `λ + R`, every cell of `T` of grade at most `N` above every `γ < λ + R`
(`CompletionBelowFullGrade.lt_label_of_hasAdmittedRows`). -/
theorem Seed.exists_completion_lt_label {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    (hm : 2 ≤ m) {r : CapRequests (Fin I.amalgam.card)}
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {xp : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hcapC : I.amalgam.toCellScheme.scope r.cap = univ.erase xp)
    (hN3 : 3 ≤ I.amalgam.toCellScheme.grade r.cap)
    (hface : ∀ x ∈ (Pts : Finset (Fin (m + 2))), x ≠ xp → ∀ d,
      I.amalgam.toCellScheme.scope d ⊆ univ.erase xp ∩ univ.erase x →
      I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
    (hbot : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillBotAt r xp k)
    (hpos : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillPosAt r xp k)
    (hlab : r.IsCorrect (hat I (m + 1) (code (m + 1) fun d ↦ I.amalgam.label d))) :
    ∃ F : CompletionBelowFullGrade I, ∀ q : Fin F.scheme.card → Label.{u},
      F.scheme.rows.IsLawfulBelow
        ((univ : Finset (Fin (m + 2))), I.amalgam.toCellScheme.grade r.cap) (fun z ↦ q z) →
      ∀ y ∈ r.T, I.amalgam.toCellScheme.grade y ≤ I.amalgam.toCellScheme.grade r.cap →
      ∀ (lam : Ordinal.{u}), Order.IsSuccPrelimit lam → ∀ i < r.N,
        q (F.embed r.marker) = ((lam + i : Ordinal.{u}) : Label.{u}) →
        q (F.embed r.marker) ≤ q (F.embed r.cap) →
        ((lam + r.R : Ordinal.{u}) : Label.{u}) ≤ q (F.embed r.cap) →
        ∀ γ : Label.{u}, γ < ((lam + r.R : Ordinal.{u}) : Label.{u}) → γ < q (F.embed y) := by
  obtain ⟨F, hF⟩ := I.exists_correctCompletion hm hgr hxp hcapC hN3 hface hbot hpos hlab
  exact ⟨F, fun q hq y hy hyN lam hlam i hi ha hmc hc γ hγ ↦
    CompletionBelowFullGrade.lt_label_of_hasAdmittedRows hgr hF hq hy hyN hlam hi ha hmc hc hγ⟩

end VaughtConjecture
