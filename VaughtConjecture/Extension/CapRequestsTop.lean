/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AdmittedCompletion
import VaughtConjecture.Extension.AdmittedClassObstruction
import VaughtConjecture.Extension.CapRequestsCode
import VaughtConjecture.Extension.CapRequestsExamples

/-!
# Cap requests at the top grade: the lift provisions

Roadmap, Layer 3 ((R3) of the table of 3.4, the reading through a top cap); the catalogue of
correct states at the top grade of a completion below the full grade.

Let `I` be a seed on `m + 2` points with `0 < m`, and `r` cap requests on the cells of its amalgam,
graded by the grades of the amalgam (`CapRequests.IsGraded`), whose cap has graded index
`(Cp, m + 1)` for the **private coatom** `Cp = univ.erase xp` (the top cap of a marked-cap context
at the top grade of the coatom type, copied into the amalgam).  The other coatom
`Dd = univ.erase xd` is the **donor coatom**.  The catalogue of correct states at the grade
`m + 1` (`ProfileTower.rowCat r.IsCorrect (m + 1)`) carries the lift provisions:

* **from the donor coatom** (`CapRequests.botLiftProvisionOf_donor`,
  `CapRequests.capLiftProvisionOf_donor`), with no further hypothesis: the private coatom is
  filled (`ProfileTower.exists_isCutLawful_of_coatom_top`) and its cells of graded index
  `(Cp, m + 1)`, the cap among them, are capped at the cap of the lift (`⊥` at the cap `⊥`).  A
  state with cap `⊥` is correct; at a positive cap `h`, the filled state agrees with the prescribed
  correct profile `P` capped at `h`, and with its cap capped at `h` it is correct because
  `min P h` is (`CapRequests.IsCorrect.of_min_eq`, `CapRequests.IsCorrect.cap`).  The code keeps
  correctness (`CapRequests.IsCorrect.code`).
* **from the private coatom** (`CapRequests.botLiftProvisionOf_private`,
  `CapRequests.capLiftProvisionOf_private`), under the **fills** (`CapRequests.CapFillBot`,
  `CapRequests.CapFillPos`): every labelling of the private coatom (agreeing with a correct
  profile capped at `h`, at the positive caps) is, below the private coatom, a state lawful on the
  cut that is correct (and agrees with the profile capped at `h`).  The fills are the raise of the
  donor cells by the prescription of the private coatom; they are the conditions of the reading
  fills of the (R3) lane at the grade `4` when the marker is the cap
  (`CapRequests.isCorrect_iff_of_marker_eq_cap`: correctness is reading `T` at least as the cap).

**The correct completion at the top** (`Seed.exists_correctCompletion_top`): under the fills and the
correctness of the code of the glued labelling, some completion below the full grade has every row
of full scope at the grade `m + 1` correct; and then **the admission of correct states**
(`CapRequests.topAdmission`), with the coatom provision of that completion as its provision, and
**its lift provisions** (`CapRequests.topLiftAdmission`).

**No bottom class.**  The catalogue keeps all correct states: a bottom class on the rows at a cell
read other than `⊥` by the row of the cap admits no bountiful completion
(`CapRequests.not_botLiftProvisionOf_class`, from
`ProfileTower.not_botLiftProvisionOf`: the row of the cap is a labelling of the private coatom
other than `⊥` at the cap and at that cell).

## Placement

The (R3) instance of the engine of the restricted catalogue at the reading grades
(`roadmap/README.md`, Layer 3, 3.1, under "(R6)"), at the top grade.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme ProfileTower

namespace CapRequests

variable {ι : Type*} {r : CapRequests ι} {s s' : ι → Label.{u}}

/-- **Correctness depends only on the state capped at its cap**: if `s` is correct, `s'` has the
same cap, self-visible at `N`, and `s'` and `s` agree capped at their cap, then `s'` is correct. -/
theorem IsCorrect.of_min_eq (hs : r.IsCorrect s) (hc : s' r.cap = s r.cap)
    (hsv : IsSelfVisible r.N (s r.cap))
    (hag : ∀ x, min (s' x) (s' r.cap) = min (s x) (s r.cap))
    (hoff : ∀ f ∈ r.F, r.off f ≤ r.N) : r.IsCorrect s' := by
  -- A replacement capped at the cap reads only the capped state.
  have hrep {i : ℕ} (hi : i ≤ r.N) (x : ι) :
      min (visibilityReplace r.N i (s' x)) (s' r.cap) =
        min (visibilityReplace r.N i (s x)) (s r.cap) := by
    rw [hc, ← visibilityReplace_min_of_isSelfVisible hi hsv,
      ← visibilityReplace_min_of_isSelfVisible hi hsv, ← hc, hag x, hc]
  refine ⟨fun z hz ↦ ?_, fun f hf ↦ ?_, fun y hy ↦ ?_⟩
  · rw [hag z]; exact hs.eq_bot z hz
  · rw [hag f, hs.eq_refValue f hf, refValue, refValue, hrep (hoff f hf)]
  · rw [markerValue, hrep r.R_lt_N.le, hag y]
    exact hs.markerValue_le y hy

end CapRequests

/-! ### The splice at the top grade, and capping the private top -/

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- At the grade `m + 1` the splice of a profile is the profile: every cell of the amalgam has
grade at most `m + 1`. -/
theorem hat_top (P : Prof I) : hat I (m + 1) P = P := funext fun d ↦
  hat_of_le (by have := I.grade_lt d; omega)

/-- The code of a profile at the grade `m + 1` is its orbit code. -/
theorem code_top (P : Prof I) : code (m + 1) P = orbitCode (m + 1) P := by
  rw [code, hat_top]

/-- A cell below one coatom at the grade `m + 1` does not have the other coatom as its scope. -/
theorem gradedIndex_ne_of_mem_below {xp xd : Fin (m + 2)} (hne : xd ≠ xp) {d : Fin I.amalgam.card}
    (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xd, m + 1)) :
    I.amalgam.toCellScheme.gradedIndex d ≠ (univ.erase xp, m + 1) := fun he ↦ by
  have h1 := hd.1
  rw [he] at h1
  exact absurd (h1 (mem_erase.mpr ⟨hne, mem_univ xd⟩)) (by simp)

/-- **Capping the top of a coatom keeps a profile lawful on the cut**: capping at `h` (self-visible
at `m + 1`) the cells of graded index `(univ.erase xp, m + 1)` keeps a profile lawful on the grade
`m + 1` cut.  Below the coatom these cells form an upper set whose grade is the size of the
coatom; below the other coatom there are none. -/
theorem IsCutLawful.capTop {xp : Fin (m + 2)} (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    {W : Prof I} (hW : IsCutLawful I (m + 1) W) {h : Label.{u}} (hh : IsSelfVisible (m + 1) h) :
    IsCutLawful I (m + 1) fun d ↦
      if I.amalgam.toCellScheme.gradedIndex d = (univ.erase xp, m + 1) then min (W d) h
      else W d := by
  classical
  obtain ⟨xd, hxd, hne⟩ := Seed.exists_other hxp
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.gradedIndex d = (univ.erase xp, m + 1) then min (W d) h
    else W d
  -- Below the donor coatom, no cell has graded index `(univ.erase xp, m + 1)`.
  have hD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, m + 1) fun d ↦ W' d := by
    refine (Rows.isLawfulBelow_congr fun d hd ↦ ?_).mp (hW.erase hxd)
    have hgi := gradedIndex_ne_of_mem_below (Ne.symm hne) hd
    simp only [W', hgi, ite_false]
  -- Below the private coatom, the cells of graded index `(univ.erase xp, m + 1)` form an upper
  -- set, and availability carries nothing into it from outside.
  have hC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, m + 1) fun d ↦ W' d := by
    have hp := Rows.isLawfulBelow_iff.mp (hW.erase hxp)
    have hl := hp.min_const_of_upper
      (fun d : I.amalgam.toCellScheme.below (univ.erase xp, m + 1) ↦
        I.amalgam.toCellScheme.gradedIndex d.1 = (univ.erase xp, m + 1))
      (fun d e hd hde ↦ le_antisymm e.2 (by
        have h' : I.amalgam.toCellScheme.gradedIndex d.1 ≤
            I.amalgam.toCellScheme.gradedIndex e.1 := hde
        rwa [hd] at h')) (K := m + 1) (fun d ↦ d.2.2) hh
      (fun a b hab hg ha hb ↦ absurd ?_ ha)
    · exact Rows.isLawfulBelow_iff.mpr (by convert hl using 1)
    · -- a cell of grade `m + 1` inside the coatom has the coatom as its scope
      have hbs : I.amalgam.toCellScheme.scope b.1 = univ.erase xp := congrArg Prod.fst hb
      have hbg : I.amalgam.toCellScheme.grade b.1 = m + 1 := congrArg Prod.snd hb
      change I.amalgam.toCellScheme.scope a.1 ⊆ I.amalgam.toCellScheme.scope b.1 at hab
      change I.amalgam.toCellScheme.grade a.1 = I.amalgam.toCellScheme.grade b.1 at hg
      have hcard : m + 1 ≤ #(I.amalgam.toCellScheme.scope a.1) := by
        have h0 := I.amalgam.isWellFormed.isWellFormed.grade_le_card a.1
        rw [hg, hbg] at h0
        exact h0
      have hsub : I.amalgam.toCellScheme.scope a.1 ⊆ univ.erase xp := by
        rw [hbs] at hab
        exact hab
      have heq : I.amalgam.toCellScheme.scope a.1 = univ.erase xp :=
        eq_of_subset_of_card_le hsub (by rw [Seed.card_erase]; exact hcard)
      exact Prod.ext heq (hg.trans hbg)
  exact lawful_pair hxp hxd hne hC hD

end ProfileTower

/-! ### The downward clause for correct states -/

namespace ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- The splice at `k` of the splice at `k + 1` is the splice at `k`. -/
theorem hat_hat_succ (k : ℕ) (R : Prof I) : hat I k (hat I (k + 1) R) = hat I k R :=
    funext fun d ↦ by
  by_cases hd : I.amalgam.toCellScheme.grade d ≤ k
  · rw [hat_of_le hd, hat_of_le hd, hat_of_le (by omega)]
  · rw [hat_of_lt (_root_.not_le.mp hd), hat_of_lt (_root_.not_le.mp hd)]

end ProfileTower

namespace CapRequests

open ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}

/-- **The downward clause for the catalogues of correct states**: for requests graded by the
grades of the amalgam, the code at `k` of a profile of the catalogue of correct states at `k + 1`
lies in the catalogue of correct states at `k` (the splice and the orbit code keep correctness,
`CapRequests.IsCorrect.code`, `CapRequests.IsCorrect.hat`). -/
theorem code_mem_rowCat_of_mem_rowCat (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    {R : Prof I} (hR : R ∈ rowCat r.IsCorrect (k + 1)) : code k R ∈ rowCat r.IsCorrect k := by
  obtain ⟨hRc, hRr⟩ := mem_rowCat.mp hR
  refine mem_rowCat.mpr ⟨code_mem_cat_of_mem_cat hRc, ?_⟩
  have h := (hRr.code hgr k).hat hgr k
  rwa [code, hat_hat_succ] at h

end CapRequests

/-! ### The lift provisions from the donor coatom -/

namespace CapRequests

open ProfileTower

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp xd : Fin (m + 2)}

/-- A profile of the catalogue of correct states at the grade `m + 1` is correct. -/
theorem isCorrect_of_mem_rowCat {P : Prof I} (hP : P ∈ rowCat r.IsCorrect (m + 1)) :
    r.IsCorrect P := by
  have h := (mem_rowCat.mp hP).2
  rwa [hat_top] at h

/-- **A correct profile lawful on the cut has its code in the catalogue of correct states.** -/
theorem code_mem_rowCat (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {W : Prof I}
    (hW : IsCutLawful I (m + 1) W) (hc : r.IsCorrect W) :
    code (m + 1) W ∈ rowCat r.IsCorrect (m + 1) := by
  have hh := isCutLawful_hat hW
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hh.1.orbitCode fun d ↦ d.2.2,
    hh.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, ?_⟩
  rw [hat_top]
  exact hc.code hgr (m + 1)

/-- **The lift provision at `⊥` from the donor coatom**: the private coatom is filled and its top
capped at `⊥`, so the cap is `⊥` and the state correct. -/
theorem botLiftProvisionOf_donor (hm : 0 < m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcap : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, m + 1))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) : BotLiftProvisionOf r.IsCorrect (m + 1) xd := fun f hf ↦ by
  classical
  obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_top hm hxd (isSelfVisible_bot _)
    (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
    fun _ _ ↦ by simp
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.gradedIndex d = (univ.erase xp, m + 1) then min (W d) ⊥
    else W d with hW'
  have hW'cut : IsCutLawful I (m + 1) W' := hW.capTop hxp (isSelfVisible_bot _)
  refine ⟨W', hW'cut, fun d hd ↦ ?_, code_mem_rowCat hgr hW'cut
    (isCorrect_of_cap_eq_bot (by simp [hW', hcap]))⟩
  have hgi := gradedIndex_ne_of_mem_below hne hd
  simp only [hW', hgi, ite_false]
  exact hWf d hd

/-- **The lift provision at the positive caps from the donor coatom**: the private coatom is filled
at the ambient of the prescribed correct profile `P` and its top capped at the cap `h`; the state
agrees with `P` capped at `h`, its cap is the cap of `min P h`, and it is correct because `min P h`
is. -/
theorem capLiftProvisionOf_donor (hm : 0 < m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcap : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, m + 1))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hxd : xd ∈ (Pts : Finset (Fin (m + 2))))
    (hne : xd ≠ xp) : CapLiftProvisionOf r.IsCorrect (m + 1) xd :=
    fun h hh _ _ P hP f hf hfP ↦ by
  classical
  have hPc := mem_cat.mp (mem_rowCat.mp hP).1
  have hPcorr := isCorrect_of_mem_rowCat hP
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom_top hm hxd hh hPc.1 hf hfP
  set W' : Prof I := fun d ↦
    if I.amalgam.toCellScheme.gradedIndex d = (univ.erase xp, m + 1) then min (W d) h
    else W d with hW'
  have hW'cut : IsCutLawful I (m + 1) W' := hW.capTop hxp hh
  -- `W'` agrees with `W` capped at `h`.
  have hW'h (d : Fin I.amalgam.card) : min (W' d) h = min (W d) h := by
    simp only [hW']
    split_ifs
    · rw [min_assoc, min_self]
    · rfl
  have hW'cap : W' r.cap = min (P r.cap) h := by
    simp only [hW', hcap, ite_true]
    exact hWP r.cap
  -- The cap of `P` is self-visible at the threshold.
  have hPsv : IsSelfVisible (m + 1) (P r.cap) := by
    have hcb : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase xp, m + 1) := by
      rw [CellScheme.mem_below, hcap]
    have := (Rows.isLawfulBelow_iff.mp (hPc.1.erase hxp)).orderly ⟨r.cap, hcb⟩
    change IsSelfVisible (I.amalgam.toCellScheme.grade r.cap) (P r.cap) at this
    rwa [show I.amalgam.toCellScheme.grade r.cap = m + 1 from congrArg Prod.snd hcap] at this
  have hNk : r.N ≤ m + 1 := hgr.le_grade_cap.trans (congrArg Prod.snd hcap).le
  have hPh : r.IsCorrect fun d ↦ min (P d) h := hPcorr.cap hgr.off_le (hh.mono hNk)
  have hW'corr : r.IsCorrect W' := by
    refine hPh.of_min_eq hW'cap ((hPsv.min hh).mono hNk) (fun x ↦ ?_) hgr.off_le
    rw [hW'cap]
    calc min (W' x) (min (P r.cap) h) = min (min (W' x) h) (P r.cap) := by
          rw [min_comm (P r.cap) h, ← min_assoc]
      _ = min (min (P x) h) (P r.cap) := by rw [hW'h, hWP]
      _ = min (min (P x) h) (min (P r.cap) h) := by
          rw [min_comm (P r.cap) h, ← min_assoc, min_assoc (P x) h h, min_self]
  refine ⟨W', hW'cut, fun d hd ↦ ?_, fun d ↦ (hW'h d).trans (hWP d), ?_⟩
  · have hgi := gradedIndex_ne_of_mem_below hne hd
    simp only [hW', hgi, ite_false]
    exact hWf d hd
  · rw [← code_top]
    exact code_mem_rowCat hgr hW'cut hW'corr

/-! ### The lift provisions from the private coatom -/

variable (r xp) in
/-- **The fill at `⊥` from the private coatom**: every labelling lawful below the private coatom is,
below it, a state lawful on the grade `m + 1` cut that is correct. -/
def CapFillBot : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, m + 1) (fun d ↦ f d) →
    ∃ W : Prof I, IsCutLawful I (m + 1) W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, m + 1), W d = f d) ∧ r.IsCorrect W

variable (r xp) in
/-- **The fill at the positive caps from the private coatom**: for every cap `h` self-visible and
short at `m + 1` and every correct profile `P` lawful on the cut, every labelling lawful below the
private coatom agreeing with `P` capped at `h` below it is, below it, a correct state lawful on the
cut agreeing with `P` capped at `h`. -/
def CapFillPos : Prop :=
  ∀ h : Label.{u}, IsSelfVisible (m + 1) h → IsShort (m + 1) h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I (m + 1) P → r.IsCorrect P →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, m + 1) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, m + 1), min (f d) h = min (P d) h) →
      ∃ W : Prof I, IsCutLawful I (m + 1) W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, m + 1), W d = f d) ∧
        (∀ d, min (W d) h = min (P d) h) ∧ r.IsCorrect W

/-- **The lift provision at `⊥` from the private coatom**, from the fill at `⊥`: the code keeps
correctness. -/
theorem botLiftProvisionOf_private (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hfill : CapFillBot r xp) : BotLiftProvisionOf r.IsCorrect (m + 1) xp := fun f hf ↦ by
  obtain ⟨W, hW, hWf, hWc⟩ := hfill f hf
  exact ⟨W, hW, hWf, code_mem_rowCat hgr hW hWc⟩

/-- **The lift provision at the positive caps from the private coatom**, from the fill at the
positive caps. -/
theorem capLiftProvisionOf_private (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hfill : CapFillPos r xp) : CapLiftProvisionOf r.IsCorrect (m + 1) xp :=
    fun h hh hs hb P hP f hf hfP ↦ by
  obtain ⟨W, hW, hWf, hWP, hWc⟩ := hfill h hh hs hb P (mem_cat.mp (mem_rowCat.mp hP).1).1
    (isCorrect_of_mem_rowCat hP) f hf hfP
  refine ⟨W, hW, hWf, hWP, ?_⟩
  rw [← code_top]
  exact code_mem_rowCat hgr hW hWc

/-- **The lift provisions from both coatoms**, for the cap on the private coatom `univ.erase xp`:
from the donor coatom with no further hypothesis, from the private coatom by the fills. -/
theorem liftProvisionOf_of_fills (hm : 0 < m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcap : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, m + 1))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hbot : CapFillBot r xp) (hpos : CapFillPos r xp) :
    ∀ x ∈ (Pts : Finset (Fin (m + 2))),
      BotLiftProvisionOf r.IsCorrect (m + 1) x ∧ CapLiftProvisionOf r.IsCorrect (m + 1) x := by
  intro x hx
  by_cases hxe : x = xp
  · subst hxe
    exact ⟨botLiftProvisionOf_private hgr hbot, capLiftProvisionOf_private hgr hpos⟩
  · exact ⟨botLiftProvisionOf_donor hm hgr hcap hxp hx hxe,
      capLiftProvisionOf_donor hm hgr hcap hxp hx hxe⟩

/-! ### No bottom class on the rows -/

/-- **A bottom class at a cell read by the cap admits no lift provision.**  For the reading rows of
decision (a), states in the bottom class `(B, ZA)` that are correct or have the cap at `⊥`: if a
cell `z ∈ B ∩ ZA` is read other than `⊥` by the row of the cap (itself read other than `⊥` there),
and the cap has graded index `(univ.erase x, k)`, the lift provision at `⊥` from that coatom fails.
The row of the cap is a labelling of the coatom other than `⊥` at the cap and at `z`
(`ProfileTower.not_botLiftProvisionOf`). -/
theorem not_botLiftProvisionOf_class {k : ℕ} {x : Fin (m + 2)} {B ZA : Set (Fin I.amalgam.card)}
    (hcapgi : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase x, k))
    {z : Fin I.amalgam.card} (hzB : z ∈ B) (hzA : z ∈ ZA)
    (hz : I.amalgam.toScheme.rowAt r.cap z ≠ ⊥) (hcc : I.amalgam.toScheme.rowAt r.cap r.cap ≠ ⊥) :
    ¬ BotLiftProvisionOf (fun s ↦ (InBottomClass B ZA s ∧ r.IsCorrect s) ∨ s r.cap = ⊥) k x := by
  have hcC : r.cap ∈ I.amalgam.toCellScheme.below (univ.erase x, k) := by
    rw [CellScheme.mem_below, hcapgi]
  have hzC : z ∈ I.amalgam.toCellScheme.below (univ.erase x, k) := by
    have h := Scheme.mem_below_of_rowAt_ne_bot hz
    rwa [hcapgi] at h
  -- The row of the cap is lawful below the coatom.
  have hf : I.amalgam.rows.IsLawfulBelow (univ.erase x, k)
      fun d ↦ I.amalgam.toScheme.rowAt r.cap d := by
    have key : ∀ X, I.amalgam.toCellScheme.gradedIndex r.cap = X →
        I.amalgam.rows.IsLawfulBelow X fun d ↦ I.amalgam.toScheme.rowAt r.cap d := by
      rintro X rfl
      convert I.isConsistent r.cap using 1
      funext d
      exact Scheme.rowAt_of_mem d.2
    exact key _ hcapgi
  refine not_botLiftProvisionOf hcC hzC (fun R hR ↦ ?_) hf hcc hz
  rcases (mem_rowCat.mp hR).2 with ⟨hcl, -⟩ | h0
  · exact .inl ((hcl z hzB).mpr hzA)
  · exact .inr h0

end CapRequests

/-! ### The correct completion at the top, and the admission of correct states -/

open CapRequests

/-- **The correct completion at the top grade.**  For a seed on `m + 2 ≥ 4` points and cap requests
graded by the grades of the amalgam whose cap has graded index `(univ.erase xp, m + 1)`, under the
fills from the private coatom and the correctness of the glued labelling, some completion below the
full grade has every row of full scope at the grades `≥ m + 1` correct. -/
theorem Seed.exists_correctCompletion_top {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    (hm : 2 ≤ m) {r : CapRequests (Fin I.amalgam.card)}
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {xp : Fin (m + 2)}
    (hcap : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, m + 1))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hbot : CapFillBot r xp) (hpos : CapFillPos r xp)
    (hlab : r.IsCorrect fun d ↦ I.amalgam.label d) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows (m + 1) r.IsCorrect := by
  have hprov := liftProvisionOf_of_fills (by omega) hgr hcap hxp hbot hpos
  have hW : IsCutLawful I (m + 1) fun d ↦ I.amalgam.label d :=
    ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
  have hlab' := code_mem_rowCat hgr hW hlab
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hL := (lvl_good (I := I) hm j le_rfl).toGoodOn fun k ↦ cat I k
  have hdown : ∀ R ∈ rowCat r.IsCorrect (j + 2 + 1), code (j + 2) R ∈ cat I (j + 2) :=
    fun R hR ↦ code_mem_cat_of_mem_cat (rowCat_subset _ _ hR)
  exact ⟨hL.admittedTopCompletion r.IsCorrect hdown (fun x hx ↦ (hprov x hx).1)
    (fun x hx ↦ (hprov x hx).2) hlab', hL.hasAdmittedRows_admittedTopCompletion r.IsCorrect
    hdown (fun x hx ↦ (hprov x hx).1) (fun x hx ↦ (hprov x hx).2) hlab' le_rfl⟩

namespace CapRequests

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {xp : Fin (m + 2)}

/-- **The admission of correct states at the top grade**, from the grade `m + 1`: correct states,
no bottom class, the states with cap `⊥` admitted unconditionally; closed under transformation
images by the grading, under caps by `CapRequests.IsCorrect.cap`; its coatom provision is that of
the correct completion (`CompletionBelowFullGrade.coatomProvision`). -/
noncomputable def topAdmission (hm : 2 ≤ m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcap : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, m + 1))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hbot : CapFillBot r xp) (hpos : CapFillPos r xp)
    (hlab : r.IsCorrect fun d ↦ I.amalgam.label d) : I.Admission where
  N := m + 1
  Adm := r.IsCorrect
  InClass _ := True
  CapBot s := s r.cap = ⊥
  map _ _ _ hs hw := hs.map hgr hw
  cap _ _ _ hk hs hh :=
    hs.cap hgr.off_le (hh.mono ((hgr.le_grade_cap.trans (congrArg Prod.snd hcap).le).trans hk))
  bot := isCorrect_bot r
  adm_of_capBot _ h := isCorrect_of_cap_eq_bot h
  provision :=
    (I.exists_correctCompletion_top hm hgr hcap hxp hbot hpos hlab).choose.coatomProvision
      (fun _ _ _ hs hw ↦ hs.map hgr hw)
      (I.exists_correctCompletion_top hm hgr hcap hxp hbot hpos hlab).choose_spec

/-- The reading rows of the admission of correct states are the correct states. -/
theorem row_topAdmission (hm : 2 ≤ m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcap : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, m + 1))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hbot : CapFillBot r xp) (hpos : CapFillPos r xp)
    (hlab : r.IsCorrect fun d ↦ I.amalgam.label d) :
    (topAdmission hm hgr hcap hxp hbot hpos hlab).Row = r.IsCorrect :=
  funext fun _ ↦ propext ⟨fun h ↦ h.elim (·.2) isCorrect_of_cap_eq_bot,
    fun h ↦ .inl ⟨trivial, h⟩⟩

/-- **The admission of correct states with its lift provisions**, from the grade `m + 1`. -/
noncomputable def topLiftAdmission (hm : 2 ≤ m) (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hcap : I.amalgam.toCellScheme.gradedIndex r.cap = (univ.erase xp, m + 1))
    (hxp : xp ∈ (Pts : Finset (Fin (m + 2)))) (hbot : CapFillBot r xp) (hpos : CapFillPos r xp)
    (hlab : r.IsCorrect fun d ↦ I.amalgam.label d) : I.LiftAdmission where
  toAdmission := topAdmission hm hgr hcap hxp hbot hpos hlab
  botLift k hk hkm x hx := by
    obtain rfl : k = m + 1 := le_antisymm hkm hk
    have h := ((liftProvisionOf_of_fills (by omega) hgr hcap hxp hbot hpos) x hx).1
    rwa [← row_topAdmission hm hgr hcap hxp hbot hpos hlab] at h
  capLift k hk hkm x hx := by
    obtain rfl : k = m + 1 := le_antisymm hkm hk
    have h := ((liftProvisionOf_of_fills (by omega) hgr hcap hxp hbot hpos) x hx).2
    rwa [← row_topAdmission hm hgr hcap hxp hbot hpos hlab] at h

end CapRequests

/-! ### At a seed whose left coatom type is a marked-cap context -/

namespace CapRequests

open StageType

variable {α : Ordinal.{u}} {m : ℕ}

/-- **The requests of a seed at the top cap of its left coatom type**: the cap and the marker are
the cells of the amalgam of the top cap `c` and the marker `r` of the left type, the threshold is
the top grade `m + 1`, the marker offset `R`, `T` the cells of the amalgam containing the last point
(the donor cells off the left coatom) labelled `⊤`, and `Z`, `F` empty. -/
noncomputable def seedTopReq (I : Seed.{u} α m) (c r : Fin I.left.card) (R : ℕ)
    (hR : R < m + 1) : CapRequests (Fin I.amalgam.card) where
  cap := faceCell I.restrictFace_left c
  N := m + 1
  R := R
  R_lt_N := hR
  Z := ∅
  F := ∅
  T := {y | Fin.last (m + 1) ∈ I.amalgam.toCellScheme.scope y ∧ I.amalgam.label y = ⊤}
  ref := id
  off _ := 0
  marker := faceCell I.restrictFace_left r

variable {I : Seed.{u} α m} {c r : Fin I.left.card} {R : ℕ} {hR : R < m + 1}

/-- The cap of the requests of a top cap of full scope at the top grade has graded index
`(univ.erase (Fin.last (m + 1)), m + 1)`, on the private coatom. -/
theorem gradedIndex_seedTopReq_cap (hc : I.left.toCellScheme.scope c = univ)
    (hg : I.left.toCellScheme.grade c = m + 1) :
    I.amalgam.toCellScheme.gradedIndex (seedTopReq I c r R hR).cap =
      (univ.erase (Fin.last (m + 1)), m + 1) := by
  refine Prod.ext ?_ ?_
  · change I.amalgam.toCellScheme.scope (faceCell I.restrictFace_left c) = _
    rw [scope_faceCell, hc, Coatom.univ_map_left]
  · change I.amalgam.toCellScheme.grade (faceCell I.restrictFace_left c) = _
    rw [grade_faceCell, hg]

/-- **The requests of a top cap at the top grade are graded** by the grades of the amalgam. -/
theorem isGraded_seedTopReq (hg : I.left.toCellScheme.grade c = m + 1)
    (hr : I.left.toCellScheme.grade r ≤ m + 1) :
    (seedTopReq I c r R hR).IsGraded I.amalgam.toCellScheme.grade where
  le_grade_cap := by
    change m + 1 ≤ I.amalgam.toCellScheme.grade (faceCell I.restrictFace_left c)
    rw [grade_faceCell, hg]
  off_le _ hf := hf.elim
  grade_le_of_mem_Z _ hz := hz.elim
  grade_le_of_mem_F _ hf := hf.elim
  grade_le_of_mem_T y _ := by
    change I.amalgam.toCellScheme.grade y ≤
      I.amalgam.toCellScheme.grade (faceCell I.restrictFace_left c)
    rw [grade_faceCell, hg]
    have := I.grade_lt y
    omega
  grade_ref_le _ hf := hf.elim
  grade_marker_le := by
    change I.amalgam.toCellScheme.grade (faceCell I.restrictFace_left r) ≤
      I.amalgam.toCellScheme.grade (faceCell I.restrictFace_left c)
    rw [grade_faceCell, grade_faceCell, hg]
    exact hr

/-- **The glued labelling is correct** for the requests of a top cap and a marker labelled `⊤`: the
cells of `T` are labelled `⊤`. -/
theorem isCorrect_seedTopReq_label (hc : I.left.label c = ⊤) (hr : I.left.label r = ⊤) :
    (seedTopReq I c r R hR).IsCorrect fun d ↦ I.amalgam.label d := by
  refine (isCorrect_iff_of_eq_top ?_ ?_).mpr ⟨fun _ hz ↦ hz.elim, fun _ hf ↦ hf.elim,
    fun y hy ↦ hy.2⟩
  · change I.amalgam.label (faceCell I.restrictFace_left c) = ⊤
    rw [label_faceCell, hc]
  · change I.amalgam.label (faceCell I.restrictFace_left r) = ⊤
    rw [label_faceCell, hr]

end CapRequests

/-- **The correct completion at a marked-cap context at the top grade.**  For a seed on `m + 2 ≥ 4`
points whose left coatom type is a marked-cap context along `h : Fin n ↪ Fin (m + 1)` with top cap
`c` at the top grade `m + 1` and marker `r` (the predicate
`CapRequestsExamples.IsMarkedCapContextAt`, copied verbatim), the requests of the seed at `c`,
`r` with marker offset `n + 1` reading the donor cells labelled `⊤`, and the fills from the private
coatom: some completion below the full grade has every row of full scope at the grade `m + 1`
correct. -/
theorem Seed.exists_correctCompletion_markedCap {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)
    (hm : 2 ≤ m) {n : ℕ} {h : Fin n ↪ Fin (m + 1)} {c r : Fin I.left.card}
    (hctx : CapRequestsExamples.IsMarkedCapContextAt I.left h c r)
    (hg : I.left.toCellScheme.grade c = m + 1)
    (hbot : CapFillBot (seedTopReq I c r (n + 1) (hctx.2.2.1.trans_eq hg)) (Fin.last (m + 1)))
    (hpos : CapFillPos (seedTopReq I c r (n + 1) (hctx.2.2.1.trans_eq hg)) (Fin.last (m + 1))) :
    ∃ F : CompletionBelowFullGrade I,
      F.HasAdmittedRows (m + 1) (seedTopReq I c r (n + 1) (hctx.2.2.1.trans_eq hg)).IsCorrect := by
  have hrc : r ∈ I.left.toCellScheme.below (I.left.toCellScheme.gradedIndex c) := hctx.2.1.2.1
  have hrg : I.left.toCellScheme.grade r ≤ m + 1 := by
    have h2 : I.left.toCellScheme.grade r ≤ I.left.toCellScheme.grade c := hrc.2
    omega
  exact I.exists_correctCompletion_top hm (isGraded_seedTopReq hg hrg)
    (gradedIndex_seedTopReq_cap hctx.1.1 hg) (by simp [Pts]) hbot hpos
    (isCorrect_seedTopReq_label hctx.1.2.1 hctx.2.1.1)

end VaughtConjecture
