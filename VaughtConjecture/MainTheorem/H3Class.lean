/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.H3Determination

/-!
# The rows admitted in a bottom class (work file for `h3`)

Work file (placement later).  The completion of `VaughtConjecture.MainTheorem.H3Determination` asks
every row of full scope from the grade of the cap to be correct.  Here the rows are only asked to
be correct when they are not `⊥` on a set `B` of cells (`CapRequests.Admits B ∅`): the bottom class
with no prescribed bottoms.  Compiled in this repository (theorem named):

* **Admission in the class with no prescribed bottoms is closed under every witness**
  (`CapRequests.Admits.map_empty`, `CapRequests.Admits.comp_empty`): a transformation is `⊥` where
  its source is, so a transformed state in the class has its source in the class.
* **The engine** (`Seed.exists_classCompletion`): from the lift provisions of the donor coatom
  for the admitted states, and the fills from the private coatom in the class form
  (`CapRequests.CapFillBotAtIn`, `CapRequests.CapFillPosAtIn`), some completion below the full
  grade has its rows of full scope from the grade of the cap admitted.
* **The fills in the class form** (`CapRequests.capFillBotAtIn_of_raise`,
  `CapRequests.CapFillBotAt.capFillBotAtIn`, `CapRequests.capFillPosAtIn_of_capFillPosAt`): the fill
  at `⊥` needs the donor raise only for the prescriptions not `⊥` on the cells of the class below
  the private coatom; the others are filled by any lift, which is out of the class.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace CapRequests

section Class

variable {ι : Type*} {r : CapRequests ι} {B : Set ι} {s : ι → Label.{u}}

/-- The bottom class with no prescribed bottoms: no cell of `B` is `⊥`. -/
theorem inBottomClass_empty_iff : InBottomClass B ∅ s ↔ ∀ d ∈ B, s d ≠ ⊥ := by
  simp [InBottomClass]

/-- **Transformations keep admission in the class with no prescribed bottoms**, for every witness:
a transformation is `⊥` where its source is. -/
theorem Admits.map_empty (hs : r.Admits B ∅ s) {grade : ι → ℕ} (hgr : r.IsGraded grade)
    {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ) :
    r.Admits B ∅ fun d ↦ min (σ (s d)) (g (grade d)) := fun hcl ↦ by
  refine (hs (inBottomClass_empty_iff.mpr fun d hd h ↦ ?_)).map hgr hw
  exact inBottomClass_empty_iff.mp hcl d hd (by rw [h, hw.map_bot, min_bot_left])

/-- **Plain images keep admission in the class with no prescribed bottoms**, for a witness bounded
by a grade at least the threshold. -/
theorem Admits.comp_empty (hs : r.Admits B ∅ s) {K : ℕ} {σ : Label.{u} → Label.{u}}
    (hw : IsWitness (stepSuppressor K) σ) (hNK : r.N ≤ K) (hoff : ∀ f ∈ r.F, r.off f ≤ r.N) :
    r.Admits B ∅ (σ ∘ s) := fun hcl ↦ by
  refine (hs (inBottomClass_empty_iff.mpr fun d hd h ↦ ?_)).comp hw hNK hoff
  exact inBottomClass_empty_iff.mp hcl d hd (by simp [h, hw.map_bot])

end Class

open ProfileTower CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {r : CapRequests (Fin I.amalgam.card)}
  {B : Set (Fin I.amalgam.card)} {xp xd : Fin (m + 2)}

/-- The splice keeps admission in the class with no prescribed bottoms. -/
theorem Admits.hat_empty {P : Prof I} (hs : r.Admits B ∅ P)
    (hgr : r.IsGraded I.amalgam.toCellScheme.grade) (k : ℕ) : r.Admits B ∅ (hat I k P) := by
  rw [hat_eq_min]
  exact hs.map_empty hgr (IsWitness.id_step k)

/-- Admitted states form a transform-closed predicate on the states of the seed. -/
theorem isTransformClosed_admits (hgr : r.IsGraded I.amalgam.toCellScheme.grade) :
    I.IsTransformClosed (r.Admits B ∅) := fun _ _ _ hs hw ↦ hs.map_empty hgr hw

/-- A profile lawful on the cut with admitted splice has its code in the catalogue of admitted
states, when the cells of the class have grades at most `k`. -/
theorem code_mem_rowCat_admits_of_hat (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k) {W : Prof I} (hW : IsCutLawful I k W)
    (hc : r.Admits B ∅ (hat I k W)) : code k W ∈ rowCat (r.Admits B ∅) k := by
  have hh := isCutLawful_hat hW
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hh.1.orbitCode fun d ↦ d.2.2,
    hh.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, ?_⟩
  have e : code k (hat I k W) = code k W := by
    unfold code
    rw [hat_hat]
  have h := (hc.code hgr hB).hat_empty hgr k
  rwa [e] at h

/-- A profile lawful on the cut with admitted splice has its orbit code in the catalogue of
admitted states, at a grade at least the threshold. -/
theorem orbitCode_mem_rowCat_admits (hgr : r.IsGraded I.amalgam.toCellScheme.grade) {k : ℕ}
    (hNk : r.N ≤ k) {W : Prof I} (hW : IsCutLawful I k W) (hc : r.Admits B ∅ (hat I k W)) :
    orbitCode k W ∈ rowCat (r.Admits B ∅) k := by
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hW.1.orbitCode fun d ↦ d.2.2,
    hW.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, ?_⟩
  rw [hat_orbitCode]
  exact hc.comp_empty (isWitness_orbitMap k W) hNk hgr.off_le

/-- **The downward clause for the catalogues of admitted states**, when the cells of the class
have grades at most `k`. -/
theorem code_mem_rowCat_admits_of_mem_rowCat (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {k : ℕ} (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k) {R : Prof I}
    (hR : R ∈ rowCat (r.Admits B ∅) (k + 1)) : code k R ∈ rowCat (r.Admits B ∅) k := by
  obtain ⟨hRc, hRr⟩ := mem_rowCat.mp hR
  refine mem_rowCat.mpr ⟨code_mem_cat_of_mem_cat hRc, ?_⟩
  have h := (hRr.code hgr hB).hat_empty hgr k
  rwa [code, hat_hat_succ] at h

variable (r B xp) in
/-- **The fill at `⊥` from the private coatom in the class form**: every labelling lawful below
the private coatom is, below it, a profile lawful on the cut with admitted splice. -/
def CapFillBotAtIn (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), W d = f d) ∧
      r.Admits B ∅ (hat I k W)

variable (r B xp) in
/-- **The fill at the positive caps from the private coatom in the class form.** -/
def CapFillPosAtIn (k : ℕ) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible k h → IsShort k h → ⊥ < h → ∀ P : Prof I,
    IsCutLawful I k P → r.Admits B ∅ (hat I k P) →
    ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), min (f d) h = min (P d) h) →
      ∃ W : Prof I, IsCutLawful I k W ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), W d = f d) ∧
        (∀ d, min (W d) h = min (P d) h) ∧ r.Admits B ∅ (hat I k W)

/-- The fill at `⊥` gives the fill at `⊥` in the class form. -/
theorem CapFillBotAt.capFillBotAtIn {k : ℕ} (h : CapFillBotAt r xp k) : CapFillBotAtIn r B xp k :=
  fun f hf ↦ by
    obtain ⟨W, hW, hWf, hWc⟩ := h f hf
    exact ⟨W, hW, hWf, hWc.admits⟩

/-- **The fill at the positive caps in the class form from the fill at the positive caps**: a
profile `P` out of the class is matched by any fill along it at the cap `h ≠ ⊥`, which is out of
the class too (capping at `h` keeps the bottoms). -/
theorem capFillPosAtIn_of_capFillPosAt (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    {k : ℕ} (hk : 0 < k) (hkm : k ≤ m + 1)
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k) (hpos : CapFillPosAt r xp k) :
    CapFillPosAtIn r B xp k := by
  intro h hh hs hb P hP hPc f hf hfP
  by_cases hcl : ∀ d ∈ B, hat I k P d ≠ ⊥
  · obtain ⟨W, hW, hWf, hWP, hWc⟩ :=
      hpos h hh hs hb P hP (hPc (inBottomClass_empty_iff.mpr hcl)) f hf hfP
    exact ⟨W, hW, hWf, hWP, hWc.admits⟩
  push Not at hcl
  obtain ⟨d, hdB, hd⟩ := hcl
  obtain ⟨W, hW, hWf, hWP⟩ := exists_isCutLawful_of_coatom_le hm hk hkm hxp hh hP hf hfP
  refine ⟨W, hW, hWf, hWP, fun hcl ↦ absurd ?_ (inBottomClass_empty_iff.mp hcl d hdB)⟩
  rw [hat_of_le (hB d hdB)] at hd ⊢
  have e := hWP d
  rw [hd, min_bot_left, min_eq_bot] at e
  exact e.resolve_right hb.ne'

/-- **The lift provision at `⊥` from the private coatom for the admitted states**, from the fill
in the class form. -/
theorem botLiftProvisionOf_admits_private (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {k : ℕ} (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k)
    (hfill : CapFillBotAtIn r B xp k) : BotLiftProvisionOf (r.Admits B ∅) k xp := fun f hf ↦ by
  obtain ⟨W, hW, hWf, hWc⟩ := hfill f hf
  exact ⟨W, hW, hWf, code_mem_rowCat_admits_of_hat hgr hB hW hWc⟩

/-- **The lift provision at the positive caps from the private coatom for the admitted states**,
from the fill in the class form. -/
theorem capLiftProvisionOf_admits_private (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {k : ℕ} (hNk : r.N ≤ k) (hfill : CapFillPosAtIn r B xp k) :
    CapLiftProvisionOf (r.Admits B ∅) k xp := fun h hh hs hb P hP f hf hfP ↦ by
  obtain ⟨W, hW, hWf, hWP, hWc⟩ := hfill h hh hs hb P (mem_cat.mp (mem_rowCat.mp hP).1).1
    (mem_rowCat.mp hP).2 f hf hfP
  exact ⟨W, hW, hWf, hWP, orbitCode_mem_rowCat_admits hgr hNk hW hWc⟩

variable (r B xp xd) in
/-- **The donor raise in the class form** at the grade `k`: the donor raise at `⊥` for the
labellings lawful below the private coatom that are not `⊥` at the cells of the class below it. -/
def DonorRaiseBotAtIn (k : ℕ) : Prop :=
  ∀ f : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d) →
    I.amalgam.toCellScheme.grade r.cap ≤ k → f r.cap ≠ ⊥ →
    (∀ d ∈ B, d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) → f d ≠ ⊥) →
    ∃ v : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ v d) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k),
        d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) → v d = f d) ∧
      ∀ y ∈ r.T, r.markerValue f ≤ v y

/-- **The fill at `⊥` of one prescription from its donor raise** (the argument of
`CapRequests.capFillBotAt_of_donorRaiseBotAt` for one labelling). -/
theorem exists_correct_fill_of_raise (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {k : ℕ} (hk : 0 < k)
    (hkm : k ≤ m + 1) (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : r.Z = ∅) (hF : r.F = ∅) {f : Prof I}
    (hf : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) (fun d ↦ f d))
    (hraise : I.amalgam.toCellScheme.grade r.cap ≤ k → f r.cap ≠ ⊥ →
      ∃ v : Prof I, I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) (fun d ↦ v d) ∧
        (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k),
          d ∈ I.amalgam.toCellScheme.below (univ.erase xd, k) → v d = f d) ∧
        ∀ y ∈ r.T, r.markerValue f ≤ v y) :
    ∃ W : Prof I, IsCutLawful I k W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k), W d = f d) ∧
      r.IsCorrect (hat I k W) := by
  classical
  by_cases hck : I.amalgam.toCellScheme.grade r.cap ≤ k ∧ f r.cap ≠ ⊥
  swap
  · obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk hkm hxp (isSelfVisible_bot k)
      (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
      fun _ _ ↦ by simp
    refine ⟨W, hW, hWf, isCorrect_of_cap_eq_bot ?_⟩
    by_cases hg : I.amalgam.toCellScheme.grade r.cap ≤ k
    · rw [hat_of_le hg, hWf _ ⟨hcapC, hg⟩]
      exact not_not.mp fun h ↦ hck ⟨hg, h⟩
    · exact hat_of_lt (not_le.mp hg)
  obtain ⟨hg, hc⟩ := hck
  obtain ⟨v, hv, hvf, hvT⟩ := hraise hg hc
  set W : Prof I := fun d ↦
    if d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) then f d else v d with hW
  have hWf (d) (hd : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)) : W d = f d := by
    rw [hW]; simp only [hd, ite_true]
  have hWC : I.amalgam.rows.IsLawfulBelow (univ.erase xp, k) fun d ↦ W d :=
    (Rows.isLawfulBelow_congr (w := f) (w' := W) fun d hd ↦ (hWf d hd).symm).mp hf
  have hWD : I.amalgam.rows.IsLawfulBelow (univ.erase xd, k) fun d ↦ W d := by
    refine (Rows.isLawfulBelow_congr (w := v) (w' := W) fun d hd ↦ ?_).mp hv
    by_cases hdC : d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k)
    · rw [hWf d hdC]
      exact hvf d hdC hd
    · rw [hW]; simp only [hdC, ite_false]
  have hmg : I.amalgam.toCellScheme.grade r.marker ≤ k := hgr.grade_marker_le.trans hg
  refine ⟨W, lawful_pair hxp hxd hne.symm hWC hWD, hWf, ?_⟩
  refine isCorrect_of_forall (fun z hz ↦ by simp [hZ] at hz) (fun f' hf' ↦ by simp [hF] at hf')
    fun y hy ↦ ?_
  have hyg : I.amalgam.toCellScheme.grade y ≤ k := (hgr.grade_le_of_mem_T y hy).trans hg
  have hmv : r.markerValue (hat I k W) = r.markerValue f := by
    unfold markerValue
    rw [hat_of_le hmg, hat_of_le hg, hWf _ ⟨hmarkC, hmg⟩, hWf _ ⟨hcapC, hg⟩]
  rw [hmv, hat_of_le hyg]
  have hyW : W y = v y := by
    rw [hW]
    exact ite_eq_right fun h ↦ hT y hy h.1
  rw [hyW]
  exact hvT y hy

/-- **The fill at `⊥` in the class form from the donor raise in the class form**: a prescription
`⊥` at a cell of the class below the private coatom is filled by any lift, out of the class; the
others by their raise. -/
theorem capFillBotAtIn_of_donorRaiseBotAtIn (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    (hm : 0 < m) (hxp : xp ∈ (Pts : Finset (Fin (m + 2))))
    (hxd : xd ∈ (Pts : Finset (Fin (m + 2)))) (hne : xd ≠ xp) {k : ℕ} (hk : 0 < k)
    (hkm : k ≤ m + 1) (hcapC : I.amalgam.toCellScheme.scope r.cap ⊆ univ.erase xp)
    (hmarkC : I.amalgam.toCellScheme.scope r.marker ⊆ univ.erase xp)
    (hT : ∀ y ∈ r.T, ¬ I.amalgam.toCellScheme.scope y ⊆ univ.erase xp)
    (hZ : r.Z = ∅) (hF : r.F = ∅) (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k)
    (hraise : DonorRaiseBotAtIn r B xp xd k) : CapFillBotAtIn r B xp k := by
  classical
  intro f hf
  by_cases hcl : ∀ d ∈ B, d ∈ I.amalgam.toCellScheme.below (univ.erase xp, k) → f d ≠ ⊥
  · obtain ⟨W, hW, hWf, hWc⟩ := exists_correct_fill_of_raise hgr hm hxp hxd hne hk hkm hcapC
      hmarkC hT hZ hF hf fun hg hc ↦ hraise f hf hg hc hcl
    exact ⟨W, hW, hWf, hWc.admits⟩
  push Not at hcl
  obtain ⟨d, hdB, hdC, hd⟩ := hcl
  obtain ⟨W, hW, hWf, -⟩ := exists_isCutLawful_of_coatom_le hm hk hkm hxp (isSelfVisible_bot k)
    (P := fun _ ↦ ⊥) ⟨Rows.isLawfulBelow_const_bot _, Rows.isLawfulBelow_const_bot _⟩ hf
    fun _ _ ↦ by simp
  refine ⟨W, hW, hWf, fun hcl' ↦ absurd ?_ (inBottomClass_empty_iff.mp hcl' d hdB)⟩
  rw [hat_of_le (hB d hdB), hWf d hdC, hd]

end CapRequests

open ProfileTower CapRequests in
/-- **The admitted completion from the grade of the cap**: for a seed on `m + 2 ≥ 4` points, cap
requests graded by the grades of the amalgam with the cap of grade `N ≥ 3`, a class `B` of cells of
grades below `N`, the lift provisions of the donor coatoms for the admitted states, the fills from
the private coatom in the class form at every grade `N ≤ k ≤ m + 1`, and the code of the glued
labelling at `m + 1` with correct splice, some completion below the full grade has every row of
full scope at the grades `≥ N` admitted in the class. -/
theorem Seed.exists_classCompletion {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hm : 2 ≤ m)
    {r : CapRequests (Fin I.amalgam.card)} (hgr : r.IsGraded I.amalgam.toCellScheme.grade)
    {B : Set (Fin I.amalgam.card)}
    (hB : ∀ d ∈ B, I.amalgam.toCellScheme.grade d < I.amalgam.toCellScheme.grade r.cap)
    {xp : Fin (m + 2)} (hN3 : 3 ≤ I.amalgam.toCellScheme.grade r.cap)
    (hdon : ∀ x ∈ (Pts : Finset (Fin (m + 2))), x ≠ xp → ∀ k,
      I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 →
        BotLiftProvisionOf (r.Admits B ∅) k x ∧ CapLiftProvisionOf (r.Admits B ∅) k x)
    (hbot : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillBotAtIn r B xp k)
    (hpos : ∀ k, I.amalgam.toCellScheme.grade r.cap ≤ k → k ≤ m + 1 → CapFillPosAtIn r B xp k)
    (hlab : r.IsCorrect (hat I (m + 1) (code (m + 1) fun d ↦ I.amalgam.label d))) :
    ∃ F : CompletionBelowFullGrade I,
      F.HasAdmittedRows (I.amalgam.toCellScheme.grade r.cap) (r.Admits B ∅) := by
  have hNN : r.N ≤ I.amalgam.toCellScheme.grade r.cap := hgr.le_grade_cap
  have hBk {k : ℕ} (hk : I.amalgam.toCellScheme.grade r.cap ≤ k) :
      ∀ d ∈ B, I.amalgam.toCellScheme.grade d ≤ k := fun d hd ↦ ((hB d hd).trans_le hk).le
  refine I.exists_rowCompletion hm hN3 (fun k hk hkm x hx ↦ ?_) (fun k hk hkm x hx ↦ ?_)
    (fun k hk R hR ↦ code_mem_rowCat_admits_of_mem_rowCat hgr (hBk hk) hR) fun _ ↦ hlab.admits
  · by_cases hxe : x = xp
    · subst hxe
      exact botLiftProvisionOf_admits_private hgr (hBk hk) (hbot k hk hkm)
    · exact (hdon x hx hxe k hk hkm).1
  · by_cases hxe : x = xp
    · subst hxe
      exact capLiftProvisionOf_admits_private hgr (hNN.trans hk) (hpos k hk hkm)
    · exact (hdon x hx hxe k hk hkm).2

namespace H3

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

section Class

variable {t' : StageType.{u} α (k + 1)} {p : StageType.{u} α k} {tb : StageType.{u} α (k + 1)}
  (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p) (htb : tb ∈ p.cofaces)
  {g : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)}

/-- **The cells of the class**: the root cells of `t'` not labelled `⊥`, and the new tops of the
donor. -/
def classCells (hd : restrictFace (extendByLast g) tb = some d) :
    Set (Fin (seed ht' hp htb).amalgam.card) :=
  {y | ∃ x ∈ t'.visibleCells (g.trans Fin.castSuccEmb), t'.label x ≠ ⊥ ∧
    y = faceCell (restrictFace_left_seed ht' hp htb) x} ∪
  {y | ∃ j, d.label j = ⊤ ∧ Fin.last n ∈ d.toCellScheme.scope j ∧
    y = faceCell (restrictFace_donor_seed ht' hp htb hd) j}

/-- The cells of the class have grades at most `n + 1`. -/
theorem grade_lt_of_mem_classCells (hd : restrictFace (extendByLast g) tb = some d) {N : ℕ}
    (hN : n + 1 < N) {y : Fin (seed ht' hp htb).amalgam.card}
    (hy : y ∈ classCells ht' hp htb hd) : (seed ht' hp htb).amalgam.toCellScheme.grade y < N := by
  rcases hy with ⟨x, hx, -, rfl⟩ | ⟨j, -, -, rfl⟩
  · rw [grade_faceCell]
    have h1 := t'.isWellFormed.isWellFormed.grade_le_card x
    have h2 : #(t'.toCellScheme.scope x) ≤ n := by
      have hsub : t'.toCellScheme.scope x ⊆ univ.map (g.trans Fin.castSuccEmb) := by
        intro z hz
        obtain ⟨w, hw⟩ := (Scheme.mem_visibleCells.mp hx) hz
        exact mem_map.mpr ⟨w, mem_univ _, hw⟩
      calc #(t'.toCellScheme.scope x) ≤ #(univ.map (g.trans Fin.castSuccEmb)) := card_le_card hsub
        _ = n := by simp
    omega
  · rw [grade_faceCell]
    exact (d.grade_le j).trans_lt hN

/-- **Determination from a completion with rows admitted in the class.**  As
`H3.isDeterminedWithin_of_hasAdmittedRows`: recognition at a cell of graded index `(univ, N)`
labelled `⊤` gives an admitted state, which is in the class since a member literal on `t'` reads
the root cells as `t'` and is at least the cutoff at the new tops; so it is correct. -/
theorem isDeterminedWithin_of_classRows (hα : Order.IsSuccLimit α)
    (hd : restrictFace (extendByLast g) tb = some d) {c r : Fin t'.card}
    (hc : t'.IsTopCap c) (hr : t'.IsMarker c r) (hn : n + 1 < t'.toCellScheme.grade c)
    (F : CompletionBelowFullGrade (seed ht' hp htb))
    (hF : F.HasAdmittedRows (t'.toCellScheme.grade c)
      ((requests ht' hp htb hd c r (by omega)).Admits (classCells ht' hp htb hd) ∅)) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily (F.completion hα.isSuccPrelimit) δ) t'
        (g.trans Fin.castSuccEmb) d := by
  have hα' := hα.isSuccPrelimit
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hr.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hmap : (seed ht' hp htb).IsTransformClosed
      ((requests ht' hp htb hd c r (by omega)).Admits (classCells ht' hp htb hd) ∅) :=
    CapRequests.isTransformClosed_admits hgr
  have h₁ : restrictFace Fin.castSuccEmb (F.completion hα') = some t' :=
    F.restrictFace_left_completion hα'
  have hR : restrictFace (extendByLast Fin.castSuccEmb) (F.completion hα') = some tb :=
    F.restrictFace_right_completion hα'
  have h₂ : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (F.completion hα') =
      some d := by
    rw [← extendByLast_trans, ← restrictFace_trans _ _ _ hR]
    exact hd
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hnk : n ≤ k := by simpa using Fintype.card_le_of_embedding g
  have hf₂ : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ≠ univ := fun he ↦ by
    have := congrArg Finset.card he
    rw [card_map, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at this
    omega
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα (F.completion hα')
  refine ⟨δ, hδ, (isDeterminedWithin_receivingFamily_iff h₂ hδD).mpr ?_⟩
  rintro ⟨S, ℓ, hw, hcod, hl, hat⟩ hq hq₁ i j hij hj
  obtain ⟨hS, hqδ⟩ := hq
  change S = (F.completion hα').toScheme at hS
  subst hS
  obtain rfl : i = faceCell h₂ j := Fin.ext hij
  have hold (z : Fin t'.card) : ℓ (faceCell h₁ z) = t'.label z := label_faceCell hq₁ z
  by_cases hjl : Fin.last n ∈ d.toCellScheme.scope j
  · -- a new top: recognition at a cell of `(univ, N)` labelled `⊤`
    have hcap : ℓ (faceCell h₁ c) = ⊤ := (hold c).trans hc.2.1
    have hmark : ℓ (faceCell h₁ r) = ⊤ := (hold r).trans hr.1
    rw [F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL c] at hcap
    rw [F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL r] at hmark
    have hcg : (F.completion hα').toCellScheme.grade (faceCell h₁ c) = t'.toCellScheme.grade c :=
      grade_faceCell h₁ c
    have hN0 : 0 < t'.toCellScheme.grade c := by omega
    have hNk : t'.toCellScheme.grade c ≤ k + 1 := t'.grade_le c
    obtain ⟨u₀, hu₀⟩ := (F.isLegal_completion hα').isComplete
      ((univ : Finset (Fin (k + 2))), t'.toCellScheme.grade c)
      ⟨(F.completion hα').univ_mem_faces, hN0, by simp; omega⟩
    obtain ⟨u, hu, hcu⟩ := hl.availability (faceCell h₁ c) u₀
      (by rw [show (F.completion hα').toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]
          exact subset_univ _)
      (hcg.trans (congrArg Prod.snd hu₀).symm)
    have hℓu : ℓ u = ⊤ := by
      have h' : ℓ (faceCell h₁ c) ≤ ℓ u := hcu
      rw [hold, hc.2.1] at h'
      exact top_le_iff.mp h'
    obtain ⟨w, rfl, hw'⟩ := F.exists_castSucc_of_gradedIndex_completion hα' (by omega)
      (hu.trans hu₀)
    -- the labelling read on the scheme below the full grade
    have hq' := (F.isLawful_comp_castSucc_completion hα' hl).isLawfulBelow
      ((univ : Finset (Fin (k + 2))), t'.toCellScheme.grade c)
    have hrec := CompletionBelowFullGrade.adm_of_isLawfulBelow hmap hF le_rfl
      (q := fun z ↦ ℓ (Fin.castSucc z)) hq' hw'
    simp only [hℓu, min_top_right] at hrec
    have hcl : ∀ e ∈ classCells ht' hp htb hd, ProfileTower.hat (seed ht' hp htb)
        (t'.toCellScheme.grade c) (fun e ↦ ℓ (Fin.castSucc (F.embed e))) e ≠ ⊥ := by
      intro e he
      rw [ProfileTower.hat_of_le (grade_lt_of_mem_classCells ht' hp htb hd hn he).le]
      rcases he with ⟨x, -, hx, rfl⟩ | ⟨j', hj', -, rfl⟩
      · intro hbot
        apply hx
        rw [← hold x, F.faceCell_completion hα' Coatom.univ_map_left_ne h₁ hL x]
        exact hbot
      · intro hbot
        replace hbot : ℓ (faceCell h₂ j') = ⊥ := by
          rw [F.faceCell_completion hα' hf₂ h₂ hA j']
          exact hbot
        have h' := hqδ ⟨(faceCell h₂ j' : ℕ), (faceCell h₂ j').2⟩ (faceCell h₂ j') rfl
        change min (ℓ (faceCell h₂ j')) δ = _ at h'
        rw [hbot, min_bot_left, label_faceCell h₂ j', hj', min_top_left] at h'
        exact hδ.1.ne h'
    replace hrec := hrec (CapRequests.inBottomClass_empty_iff.mpr hcl)
    have hcapN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) ≤
        t'.toCellScheme.grade c := (grade_faceCell hL c).le
    have hmarkN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL r) ≤
        t'.toCellScheme.grade c := (grade_faceCell hL r).trans_le hrc
    have hyT : faceCell hA j ∈ (requests ht' hp htb hd c r (by omega)).T := ⟨j, hj, hjl, rfl⟩
    have htop := hrec.eq_top_of_mem_T hyT
      (by change ProfileTower.hat (seed ht' hp htb) _ _ (faceCell hL c) = ⊤
          rw [ProfileTower.hat_of_le hcapN]; exact hcap)
      (by change ProfileTower.hat (seed ht' hp htb) _ _ (faceCell hL r) = ⊤
          rw [ProfileTower.hat_of_le hmarkN]; exact hmark)
    have hyN : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hA j) ≤
        t'.toCellScheme.grade c := by
      rw [grade_faceCell]
      exact (d.grade_le j).trans hn.le
    rw [ProfileTower.hat_of_le hyN] at htop
    change ℓ (faceCell h₂ j) = ⊤
    rw [F.faceCell_completion hα' hf₂ h₂ hA j]
    exact htop
  · -- an old cell: visible through the first points, literal on `t'`
    have hvis : faceCell h₂ j ∈ (F.completion hα').visibleCells Fin.castSuccEmb := by
      rw [Scheme.mem_visibleCells]
      intro y hy
      rw [scope_faceCell] at hy
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
      induction x using Fin.lastCases with
      | last => exact absurd hx hjl
      | cast x => exact ⟨Fin.castSucc (g x), by simp⟩
    obtain ⟨z, hz⟩ := exists_faceCell_eq h₁ hvis
    change ℓ (faceCell h₂ j) = ⊤
    rw [← hz, hold]
    have h1 := label_faceCell h₁ z
    have h2 := label_faceCell h₂ j
    rw [hz] at h1
    rw [← h1, h2]
    exact hj


/-- **The completion with rows admitted in the class, from the fills and the donor lift
provisions** (`Seed.exists_classCompletion`): with `k ≥ 2` and the grade `N` of the cap at least
`3`, given the lift provisions from the donor coatom for the admitted states (`hdon`), the donor
raise in the class form (`hraise`) and the band of the fill at the positive caps (`hband`), at
every grade `N ≤ k' ≤ k + 1`. -/
theorem exists_classCompletion_of_fills (hd : restrictFace (extendByLast g) tb = some d)
    {c r : Fin t'.card} (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hk : 2 ≤ k) (hN3 : 3 ≤ t'.toCellScheme.grade c)
    (hdon : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      ProfileTower.BotLiftProvisionOf
          ((requests ht' hp htb hd c r (by omega)).Admits (classCells ht' hp htb hd) ∅) k'
          (Fin.castSucc (Fin.last k)) ∧
        ProfileTower.CapLiftProvisionOf
          ((requests ht' hp htb hd c r (by omega)).Admits (classCells ht' hp htb hd) ∅) k'
          (Fin.castSucc (Fin.last k)))
    (hraise : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.DonorRaiseBotAtIn (requests ht' hp htb hd c r (by omega))
        (classCells ht' hp htb hd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k')
    (hband : ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
      CapRequests.CapFillPosBandAt (requests ht' hp htb hd c r (by omega)) (Fin.last (k + 1))
        k') :
    ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
      F.HasAdmittedRows (t'.toCellScheme.grade c)
        ((requests ht' hp htb hd c r (by omega)).Admits (classCells ht' hp htb hd) ∅) := by
  have hrc : t'.toCellScheme.grade r ≤ t'.toCellScheme.grade c := by
    have h := hctx.2.1.2.1
    rw [CellScheme.mem_below] at h
    exact (Prod.le_def.mp h).2
  have hn := hctx.2.2.1
  have hgr := isGraded_requests ht' hp htb hd (r := r) (by omega) hrc hn
  have hL := restrictFace_left_seed ht' hp htb
  have hA := restrictFace_donor_seed ht' hp htb hd
  have hcapg : (seed ht' hp htb).amalgam.toCellScheme.grade (faceCell hL c) =
      t'.toCellScheme.grade c := grade_faceCell hL c
  have hcapg' : (seed ht' hp htb).amalgam.toCellScheme.grade
      (requests ht' hp htb hd c r (by omega)).cap = t'.toCellScheme.grade c := hcapg
  have hcapC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL c) =
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, hctx.1.1]
    exact Coatom.univ_map_left
  have hmarkC : (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hL r) ⊆
      univ.erase (Fin.last (k + 1)) := by
    rw [scope_faceCell, ← Coatom.univ_map_left]
    exact map_subset_map.mpr (subset_univ _)
  have hTlab (y) (hy : y ∈ (requests ht' hp htb hd c r (by omega)).T) :
      (seed ht' hp htb).amalgam.label y = ⊤ ∧
        ¬ (seed ht' hp htb).amalgam.toCellScheme.scope y ⊆ univ.erase (Fin.last (k + 1)) := by
    obtain ⟨j, hj, hjl, rfl⟩ := hy
    refine ⟨(label_faceCell hA j).trans hj, fun hsub ↦ ?_⟩
    have hmem : Fin.last (k + 1) ∈
        (seed ht' hp htb).amalgam.toCellScheme.scope (faceCell hA j) := by
      rw [scope_faceCell]
      exact mem_map.mpr ⟨Fin.last n, hjl, by simp⟩
    simpa using hsub hmem
  have hglued : (requests ht' hp htb hd c r (by omega)).IsCorrect
      fun e ↦ (seed ht' hp htb).amalgam.label e :=
    CapRequests.isCorrect_of_forall (fun z hz ↦ absurd hz (Set.notMem_empty _))
      (fun f hf ↦ absurd hf (Set.notMem_empty _))
      fun y hy ↦ by rw [(hTlab y hy).1]; exact le_top
  have hlab := (hglued.code hgr (k + 1)).hat hgr (k + 1)
  have hB : ∀ e ∈ classCells ht' hp htb hd, (seed ht' hp htb).amalgam.toCellScheme.grade e <
      (seed ht' hp htb).amalgam.toCellScheme.grade (requests ht' hp htb hd c r (by omega)).cap :=
    fun e he ↦ by rw [hcapg']; exact grade_lt_of_mem_classCells ht' hp htb hd hn he
  have h := (seed ht' hp htb).exists_classCompletion hk hgr hB (xp := Fin.last (k + 1))
    (by rw [hcapg']; exact hN3)
    (fun x hx hxe k' hk' hkm ↦ by
      have hx' : x = Fin.castSucc (Fin.last k) := by
        simp only [ProfileTower.Pts, mem_insert, mem_singleton] at hx
        exact hx.resolve_left hxe
      subst hx'
      exact hdon k' (hcapg' ▸ hk') hkm)
    (fun k' hk' hkm ↦ CapRequests.capFillBotAtIn_of_donorRaiseBotAtIn hgr (by omega) (by simp)
      (by simp) Seed.last_ne_castSucc.symm (by rw [hcapg'] at hk'; omega) hkm hcapC.le hmarkC
      (fun y hy ↦ (hTlab y hy).2) rfl rfl (fun e he ↦ ((hB e he).trans_le hk').le)
      (hraise k' (hcapg' ▸ hk') hkm))
    (fun k' hk' hkm ↦ CapRequests.capFillPosAtIn_of_capFillPosAt (by omega) (by simp)
      (by rw [hcapg'] at hk'; omega) hkm (fun e he ↦ ((hB e he).trans_le hk').le)
      (CapRequests.capFillPosAt_of_band hgr (by omega) (by simp) hcapC hk' hkm
        (hband k' (hcapg' ▸ hk') hkm))) hlab
  rwa [hcapg'] at h

end Class

/-! ### The open inputs (SCAFFOLD) and the assembly -/

set_option warningAsError false in
/-- **SCAFFOLD (`sorry`), (S2): a donor coface with the raise.**  At an acquired context, every
coface `d` of the root face has a coface `tb` of the coatom face `p` with face `d` along
`extendByLast g` such that the donor raise in the class form holds at every grade from the grade
of the cap. -/
theorem exists_raiseCoface (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c) :
    ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      ∀ k', t'.toCellScheme.grade c ≤ k' → k' ≤ k + 1 →
        CapRequests.DonorRaiseBotAtIn
          (requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega))
          (classCells ht' hp htb htbd) (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) k' := by
  sorry

set_option warningAsError false in
/-- **SCAFFOLD (`sorry`)**: at an acquired context, every coface `d` of the root face has a coface
`tb` of `p` with face `d` and a completion of the seed of `t'` and `tb` whose rows of full scope
from the grade of the cap are admitted in the class.  Through `H3.exists_raiseCoface` (S2) and
`H3.exists_classCompletion_of_fills`, with three `sorry`s: (S1) the lift provisions from the donor
coatom for the admitted states, (S4) the band of the fill at the positive caps, and (S5) the small
cases `k ≤ 1` or `N = 2`. -/
theorem exists_coface_classCompletion (hα : Order.IsSuccLimit α) {t' : StageType.{u} α (k + 1)}
    {p : StageType.{u} α k} (ht' : t'.IsLegal) (hp : restrictFace Fin.castSuccEmb t' = some p)
    {g : Fin n ↪ Fin k} {t : StageType.{u} α n}
    (ht : restrictFace (g.trans Fin.castSuccEmb) t' = some t) {d : StageType.{u} α (n + 1)}
    (hd : d ∈ t.cofaces) {c r : Fin t'.card}
    (hctx : t'.IsMarkedCapContextAt (g.trans Fin.castSuccEmb) c r)
    (hoff : t'.RootOffsetsBelow (g.trans Fin.castSuccEmb) (t'.toCellScheme.grade c))
    (hbot : t'.RootBottomRespected (g.trans Fin.castSuccEmb) c) :
    ∃ tb, ∃ htb : tb ∈ p.cofaces, ∃ htbd : restrictFace (extendByLast g) tb = some d,
      ∃ F : CompletionBelowFullGrade (seed ht' hp htb),
        F.HasAdmittedRows (t'.toCellScheme.grade c)
          ((requests ht' hp htb htbd c r (by have := hctx.2.2.1; omega)).Admits
            (classCells ht' hp htb htbd) ∅) := by
  obtain ⟨tb, htb, htbd, hraise⟩ := exists_raiseCoface hα ht' hp ht hd hctx hoff hbot
  refine ⟨tb, htb, htbd, ?_⟩
  by_cases hsmall : 2 ≤ k ∧ 3 ≤ t'.toCellScheme.grade c
  · refine exists_classCompletion_of_fills ht' hp htb htbd hctx hsmall.1 hsmall.2 ?_ hraise ?_
    · -- (S1) the lift provisions from the donor coatom for the admitted states
      sorry
    · -- (S4) the band of the fill at the positive caps
      sorry
  · -- (S5) the small cases: `k ≤ 1` or the cap of grade `2`
    sorry

/-- **The existential coatom form at the contexts respecting the root bottoms** (through the
SCAFFOLD `H3.exists_coface_classCompletion`). -/
theorem hollowCoatomCutoffDeterminationExists :
    Realization.HollowCoatomCutoffDeterminationExists.{u}
      (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) where
  exists_coface α n k t' g p hα ht' hP hp t ht d hd := by
    obtain ⟨c, r, hctx, hoff, hbot⟩ := hP
    obtain ⟨tb, htb, htbd, F, hF⟩ := exists_coface_classCompletion hα ht' hp ht hd hctx hoff hbot
    obtain ⟨δ, hδ, hdet⟩ := isDeterminedWithin_of_classRows ht' hp htb hα htbd hctx.1
      hctx.2.1 hctx.2.2.1 F hF
    exact ⟨tb, htb, htbd, F.completion hα.isSuccPrelimit,
      ⟨F.isLegal_completion _, F.restrictFace_left_completion _⟩,
      F.restrictFace_right_completion _, δ, hδ, hdet⟩

/-- **(R3) for receiving models** through the existential coatom form (SCAFFOLD). -/
theorem receivingHollowReceiving :
    Realization.HollowReceiving.{u, w} Realization.IsReceivingCoverHollowAtBlock :=
  Realization.receivingHollowReceiving_of_markedCapContextBelow'
    (hollowCoatomCutoffDeterminationExists.hollowCutoffDetermination
      (Realization.markedCapContextBelow'_routeInputs.{u, w}).2.1
      (Realization.markedCapContextBelow'_routeInputs.{u, w}).2.2)

end H3

end VaughtConjecture
