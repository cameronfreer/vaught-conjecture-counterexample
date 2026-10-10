/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralEngine
import VaughtConjecture.Extension.RowCompletionZero

/-!
# h2 at every arity: the engine below the full grade

Roadmap, Layer 3 ((R2) of the table of 3.4: coatom cutoff determination at source-gap contexts,
`Realization.CoatomCutoffDetermination`, written **h2** in the names of this family of modules).
Every declaration is proved; the extension above `K` (`H2.ExtAbove`) is a hypothesis.

**The engine below the full grade** (`H2.exists_completion_below`): for a context of top grade
`K ≤ k` on `k + 1` points, an admission of states of the clause between the grade-`K` faces gives
a completion whose rows of full scope at the grades `j ≥ K` read the clause on their part of grade
at most `K` (`H2.trK`), through the completion on the catalogues of a predicate from the grade `K`
(`Seed.exists_rowCompletion₀`, levels from the grade `0`):
* the lift provisions at a grade `j ≥ K` from the first coatom: the context provision of the
  admission on the parts of grade at most `K`, then the extension of the donor face from `(univ, K)`
  to `(univ, j)` keeping the root of the context face above `K` (`H2.ExtAbove`), then the gluing;
  from the second coatom the same with the donor provision;
* the reading at a cell of `(univ, K)` at `⊤` (`H2.adm_of_hasAdmittedRows_below`), the clause
  reading only the cells of grade at most `K` (`H2.ReadsAt`).

**The extension above `K`** (`H2.ExtAbove`) is the residual: a face lawful below `(univ, K)` and a
root prescription lawful below `(univ, j)`, agreeing at the root cells of grade at most `K`, extend
to a face lawful below `(univ, j)` with both, agreeing with a reference capped at `h`.  When the
common face has no cell above `K` (`k ≤ K`) it is bountifulness (`H2.extAbove_of_le`); otherwise
the root cells of grade in `(K, j]` are prescribed as well (the analogue at higher arity of
`H2.GradeTwoExtAtOne`).

**The assembly** (`H2.admittedCompletionsBelowAt_of_ext`,
`H2.coatomCutoffDeterminationLast_of_ext`): the engine below the full grade on `k + 1 ≥ 2` points
from the extension above `K` for `K < k` (`H2.ExtAboveAt`); at `K = k` it needs nothing.  At three
points (`k = 2`) the residual is the extension above the grade `1` (`H2.extAboveAt_two_iff`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission ProfileTower CellScheme

variable {α : Ordinal.{u}}

/-! ### The extension above `K` -/

/-- **The extension above the grade `K`** on a stage type `t` with face `p` along
`Fin.castSuccEmb`: at every grade `K < j ≤ k + 1` and every cap `h` self-visible at `j`, a face `w`
lawful below `(univ, K)` and `⊥` above, a root prescription `y` lawful below `(univ, j)`, agreeing
with `w` at the root cells of grade at most `K`, and a reference `R` lawful below `(univ, j)`
agreeing with `w` and with `y` capped at `h` have an extension lawful below `(univ, j)` equal to `w`
at the grades at most `K`, to `y` at the root cells of grade at most `j`, and agreeing with `R`
capped at `h` at the grades at most `j`. -/
def ExtAbove {k : ℕ} (t : StageType.{u} α (k + 1)) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t = some p) (K : ℕ) : Prop :=
  ∀ ⦃j : ℕ⦄, K < j → j ≤ k + 1 → ∀ ⦃h : Label.{u}⦄, IsSelfVisible j h →
    ∀ ⦃w R : Fin t.card → Label.{u}⦄ ⦃y : Fin p.card → Label.{u}⦄, LawfulAt t K w →
    t.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), j) (fun d ↦ R d) →
    p.rows.IsLawfulBelow ((univ : Finset (Fin k)), j) (fun d ↦ y d) →
    (∀ i, p.toCellScheme.grade i ≤ K → w (StageType.faceCell hp i) = y i) →
    (∀ d, t.toCellScheme.grade d ≤ K → min (w d) h = min (R d) h) →
    (∀ i, p.toCellScheme.grade i ≤ j → min (y i) h = min (R (StageType.faceCell hp i)) h) →
    ∃ W : Fin t.card → Label.{u},
      t.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), j) (fun d ↦ W d) ∧
      (∀ d, t.toCellScheme.grade d ≤ K → W d = w d) ∧
      (∀ i, p.toCellScheme.grade i ≤ j → W (StageType.faceCell hp i) = y i) ∧
      ∀ d, t.toCellScheme.grade d ≤ j → min (W d) h = min (R d) h

/-- **The extension above `K` when the face has no cell above `K`** (`k ≤ K`): bountifulness from
`(univ, K)` to `(univ, j)`. -/
theorem extAbove_of_le {k K : ℕ} {t : StageType.{u} α (k + 1)} (hleg : t.IsLegal)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t = some p) (hK0 : 0 < K)
    (hkK : k ≤ K) : ExtAbove t hp K := by
  classical
  intro j hKj hjk h hh w R y hw hR _ hwy hwR _
  have hXY : (((univ : Finset (Fin (k + 1))), K) : Finset (Fin (k + 1)) × ℕ) ≤
      ((univ : Finset (Fin (k + 1))), j) := ⟨subset_rfl, hKj.le⟩
  obtain ⟨q', hq', hq'R, hq'w⟩ := (CellScheme.Rows.cappedLift_iff_forall_exists hXY).mp
    (hleg.isBountiful ⟨t.univ_mem_faces, hK0, by simp; omega⟩
      ⟨t.univ_mem_faces, by omega, by simp; omega⟩ hXY) h hh (fun d ↦ w d) (fun d ↦ R d)
    hw.1 hR (fun d ↦ (hwR d d.2.2).symm)
  set W : Fin t.card → Label.{u} := CellScheme.Rows.extendBot _ q' with hWdef
  have hW (d : Fin t.card) (hd : d ∈ t.toCellScheme.below ((univ : Finset (Fin (k + 1))), j)) :
      W d = q' ⟨d, hd⟩ := CellScheme.Rows.extendBot_of_mem q' hd
  have hWK (d : Fin t.card) (hd : t.toCellScheme.grade d ≤ K) : W d = w d := by
    rw [hW d ⟨subset_univ _, hd.trans hKj.le⟩]
    exact hq'w ⟨d, subset_univ _, hd⟩
  refine ⟨W, ?_, hWK, fun i _ ↦ ?_, fun d hd ↦ ?_⟩
  · convert hq' using 1
    exact funext fun z ↦ hW z z.2
  · have hg : t.toCellScheme.grade (StageType.faceCell hp i) ≤ K := by
      rw [StageType.grade_faceCell]; exact (p.grade_le i).trans hkK
    rw [hWK _ hg]
    exact hwy i ((StageType.grade_faceCell hp i).symm.trans_le hg)
  · rw [hW d ⟨subset_univ _, hd⟩]
    exact hq'R ⟨d, subset_univ _, hd⟩

/-! ### Truncations -/

/-- Truncating above `j` keeps a labelling lawful below `(univ, j)`. -/
theorem isLawfulBelow_trunc {n j : ℕ} {t : StageType.{u} α n} {f : Fin t.card → Label.{u}}
    (hf : t.rows.IsLawfulBelow ((univ : Finset (Fin n)), j) (fun d ↦ f d)) :
    t.rows.IsLawfulBelow ((univ : Finset (Fin n)), j)
      (fun d ↦ if t.toCellScheme.grade d.1 ≤ j then f d else ⊥) :=
  (CellScheme.Rows.isLawfulBelow_congr (w' := fun d ↦ if t.toCellScheme.grade d ≤ j then f d
    else ⊥) fun _ hd ↦ (ite_eq_left hd.2).symm).mp hf

/-- The face along `Fin.castSuccEmb` of a labelling lawful below `(univ, j)` is lawful below
`(univ, j)`. -/
theorem isLawfulBelow_face {k j : ℕ} {t : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t = some p) {f : Fin t.card → Label.{u}}
    (hf : t.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), j) (fun d ↦ f d)) :
    p.rows.IsLawfulBelow ((univ : Finset (Fin k)), j) (fun i ↦ f (StageType.faceCell hp i)) :=
  (Scheme.isLawfulBelow_faceCell_iff (StageType.comap_toScheme_of_restrictFace hp)
    ((univ : Finset (Fin k)), j) f).mpr
    (hf.mono (X := Prod.map (Finset.map Fin.castSuccEmb) id ((univ : Finset (Fin k)), j))
      ⟨subset_univ _, le_rfl⟩)

/-! ### The clause read at the grades at most `K` -/

section Seed

variable {m : ℕ} {I : Seed.{u} α m}

variable (I) in
/-- The **truncation above `K`** of a state. -/
noncomputable def trK (K : ℕ) (s : I.State) : I.State :=
  fun d ↦ if I.amalgam.toCellScheme.grade d ≤ K then s d else ⊥

theorem trK_ctx (K : ℕ) (s : I.State) (z : Fin I.left.card) :
    trK I K s (ctx I z) = if I.left.toCellScheme.grade z ≤ K then s (ctx I z) else ⊥ := by
  unfold trK
  rw [StageType.grade_faceCell]

theorem trK_don (K : ℕ) (s : I.State) (z : Fin I.right.card) :
    trK I K s (don I z) = if I.right.toCellScheme.grade z ≤ K then s (don I z) else ⊥ := by
  unfold trK
  rw [StageType.grade_faceCell]

variable (I) in
/-- The clause **reads only the cells of grade at most `K`**. -/
def ReadsAt (K : ℕ)
    (Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop) : Prop :=
  ∀ ⦃L L' : Fin I.left.card → Label.{u}⦄ ⦃R R' : Fin I.right.card → Label.{u}⦄,
    (∀ z, I.left.toCellScheme.grade z ≤ K → L z = L' z) →
    (∀ z, I.right.toCellScheme.grade z ≤ K → R z = R' z) → Adm L R → Adm L' R'

variable (I) in
/-- A state **has the clause on its part of grade at most `K`**. -/
def rowAdm (K : ℕ)
    (Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop)
    (s : I.State) : Prop :=
  stateAdm I Adm (trK I K s)

variable {K : ℕ} {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}
  {C : (Fin I.left.card → Label.{u}) → Prop} {D : (Fin I.right.card → Label.{u}) → Prop}

/-- **The clause on the part of grade at most `K` passes to images under witnesses bounded by a
grade at least `K`.** -/
theorem rowAdm_comp (hS : IsStateAdmission (rootLm I) (rootRm I) K C D Adm) {j : ℕ}
    (hKj : K ≤ j) {σ : Label.{u} → Label.{u}} (hσ : IsWitness (stepSuppressor j) σ)
    {s : I.State} (hs : rowAdm I K Adm s) : rowAdm I K Adm fun d ↦ σ (s d) := by
  have e : trK I K (fun d ↦ σ (s d)) = fun d ↦ σ (trK I K s d) := by
    funext d
    unfold trK
    split_ifs
    · rfl
    · exact hσ.map_bot.symm
  unfold rowAdm
  rw [e]
  exact hS.comp hσ.monotone hσ.map_bot (fun x ↦ hσ.visibilityReplace_comm x K
    (by rw [stepSuppressor_of_le hKj]; exact le_top) K le_rfl) hs

/-- The splice at a grade at least `K` keeps the part of grade at most `K`. -/
theorem trK_hat {j : ℕ} (hKj : K ≤ j) (s : I.State) : trK I K (hat I j s) = trK I K s := by
  funext d
  unfold trK
  split_ifs with hd
  · exact hat_of_le (hd.trans hKj)
  · rfl

/-- **The code of a state with the clause has the clause**, at a grade `j ≥ K`. -/
theorem code_mem_rowCat_below (hS : IsStateAdmission (rootLm I) (rootRm I) K C D Adm) {j : ℕ}
    (hKj : K ≤ j) {w : I.State} (hw : IsCutLawful I j w) (ha : rowAdm I K Adm w) :
    code j w ∈ rowCat (rowAdm I K Adm) j := by
  refine mem_rowCat.mpr ⟨code_mem_cat_of_isCutLawful hw, ?_⟩
  have h1 : rowAdm I K Adm (hat I j w) := by
    unfold rowAdm; rw [trK_hat hKj]; exact ha
  have h2 := rowAdm_comp hS hKj (isWitness_orbitMap j (hat I j w)) h1
  unfold rowAdm at h2 ⊢
  rw [trK_hat hKj]
  convert h2 using 3 with d
  change orbitCode j (hat I j w) d = _
  rw [orbitCode_apply]

/-- **The orbit code of a state with the clause has the clause**, at a grade `j ≥ K`. -/
theorem orbitCode_mem_rowCat_below (hS : IsStateAdmission (rootLm I) (rootRm I) K C D Adm)
    {j : ℕ} (hKj : K ≤ j) {w : I.State} (hw : IsCutLawful I j w) (ha : rowAdm I K Adm w) :
    orbitCode j w ∈ rowCat (rowAdm I K Adm) j := by
  refine mem_rowCat.mpr ⟨mem_cat.mpr ⟨⟨hw.1.orbitCode fun d ↦ d.2.2,
    hw.2.orbitCode fun d ↦ d.2.2⟩, orbitCode_orbitCode⟩, ?_⟩
  have h2 := rowAdm_comp hS hKj (isWitness_orbitMap j w) ha
  unfold rowAdm at h2 ⊢
  rw [trK_hat hKj]
  exact h2

/-! ### The lift provisions at a grade `j ≥ K` -/

section Provisions

variable (hS : IsStateAdmission (rootLm I) (rootRm I) K (LawfulAt I.left K) (LawfulAt I.right K)
  Adm)
include hS

/-- **The lift from the first coatom at a grade `j ≥ K`**: the context provision on the parts of
grade at most `K`, the extension of the donor face above `K` keeping the root of the context face,
and the gluing; the result agrees with `P` capped at `h` and has the clause. -/
theorem exists_lift_left (hext : ExtAbove I.right I.restrictFace_face_right K) {j : ℕ}
    (hKj : K ≤ j) (hjm : j ≤ m + 1) {h : Label.{u}} (hh : IsSelfVisible j h) {P : I.State}
    (hP : IsCutLawful I j P) (hPA : rowAdm I K Adm P) {f : I.State}
    (hf : I.amalgam.rows.IsLawfulBelow (coatC, j) fun d ↦ f d)
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (coatC, j), min (f d) h = min (P d) h) :
    ∃ W : I.State, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (coatC, j), W d = f d) ∧
      (∀ d, min (W d) h = min (P d) h) ∧ rowAdm I K Adm W := by
  classical
  -- the context face and its part of grade at most `K`
  set fL : Fin I.left.card → Label.{u} := fun z ↦ f (ctx I z) with hfLdef
  have hfL : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) fun z ↦ fL z :=
    (ctx_isLawfulBelow_iff j f).mpr hf
  set fK : Fin I.left.card → Label.{u} :=
    fun z ↦ if I.left.toCellScheme.grade z ≤ K then fL z else ⊥ with hfKdef
  have hfK : LawfulAt I.left K fK := lawfulAt_trunc hfL hKj
  -- the parts of grade at most `K` of `P`
  have hPc := (isCutLawful_iff j P).mp hP
  set L : Fin I.left.card → Label.{u} :=
    fun z ↦ if I.left.toCellScheme.grade z ≤ K then P (ctx I z) else ⊥ with hLdef
  set R : Fin I.right.card → Label.{u} :=
    fun z ↦ if I.right.toCellScheme.grade z ≤ K then P (don I z) else ⊥ with hRdef
  have hL : LawfulAt I.left K L := lawfulAt_trunc hPc.1 hKj
  have hR : LawfulAt I.right K R := lawfulAt_trunc hPc.2 hKj
  have hgr (x : Fin I.face.card) : I.left.toCellScheme.grade (rootLm I x) =
      I.right.toCellScheme.grade (rootRm I x) :=
    (StageType.grade_faceCell _ x).trans (StageType.grade_faceCell _ x).symm
  have hy (x : Fin I.face.card) : L (rootLm I x) = R (rootRm I x) := by
    simp only [hLdef, hRdef, hgr, ctx_rootLm]
  have hadm : Adm L R := by
    have e1 : (fun z ↦ trK I K P (ctx I z)) = L := funext fun z ↦ trK_ctx K P z
    have e2 : (fun z ↦ trK I K P (don I z)) = R := funext fun z ↦ trK_don K P z
    have := hPA
    unfold rowAdm stateAdm at this
    rwa [e1, e2] at this
  have hfKL (z : Fin I.left.card) : min (fK z) h = min (L z) h := by
    simp only [hfKdef, hLdef]
    split_ifs with hz
    · exact hfP _ (ctx_mem_below z (hz.trans hKj))
    · rfl
  obtain ⟨WK, hWK, hWKr, hWKh, hA⟩ := hS.context (hh.mono hKj) hL hR hy hadm hfK hfKL
  -- the donor face above `K`
  have hdonP : I.right.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j)
      fun z ↦ P (don I z) := hPc.2
  obtain ⟨WR, hWR, hWRK, hWRr, hWRh⟩ : ∃ WR : Fin I.right.card → Label.{u},
      I.right.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) (fun d ↦ WR d) ∧
      (∀ d, I.right.toCellScheme.grade d ≤ K → WR d = WK d) ∧
      (∀ i, I.face.toCellScheme.grade i ≤ j → WR (rootRm I i) = fL (rootLm I i)) ∧
      ∀ d, I.right.toCellScheme.grade d ≤ j → min (WR d) h = min (P (don I d)) h := by
    have hWKroot (i : Fin I.face.card) (hi : I.face.toCellScheme.grade i ≤ K) :
        WK (rootRm I i) = fL (rootLm I i) := by
      rw [hWKr i]
      simp only [hfKdef]
      rw [ite_eq_left (by rw [StageType.grade_faceCell]; exact hi)]
    have hWKP (d : Fin I.right.card) (hd : I.right.toCellScheme.grade d ≤ K) :
        min (WK d) h = min (P (don I d)) h := by
      rw [hWKh d]
      simp only [hRdef]
      rw [ite_eq_left hd]
    rcases Nat.lt_or_eq_of_le hKj with hlt | rfl
    · refine hext hlt hjm hh hWK hdonP (isLawfulBelow_face _ hfL) hWKroot hWKP fun i hi ↦ ?_
      rw [← ctx_rootLm]
      exact hfP _ (ctx_mem_below _ (by rw [StageType.grade_faceCell]; exact hi))
    · refine ⟨WK, hWK.1, fun _ _ ↦ rfl, hWKroot, hWKP⟩
  -- the gluing, below `(univ, j)`
  set sL : Fin I.left.card → Label.{u} :=
    fun z ↦ if I.left.toCellScheme.grade z ≤ j then fL z else ⊥ with hsLdef
  set sR : Fin I.right.card → Label.{u} :=
    fun z ↦ if I.right.toCellScheme.grade z ≤ j then WR z else ⊥ with hsRdef
  have hroot (x : Fin I.face.card) : sL (rootLm I x) = sR (rootRm I x) := by
    simp only [hsLdef, hsRdef]
    rw [← hgr]
    split_ifs with hx
    · exact (hWRr x (by rw [← StageType.grade_faceCell I.restrictFace_face_left]; exact hx)).symm
    · rfl
  obtain ⟨w0, hw0L, hw0R⟩ := exists_glue hroot
  set W : I.State := fun d ↦ if I.amalgam.toCellScheme.grade d ≤ j then w0 d else P d with hWdef
  have hWctx (z : Fin I.left.card) (hz : I.left.toCellScheme.grade z ≤ j) : W (ctx I z) = fL z := by
    simp only [hWdef]
    rw [ite_eq_left (by rw [StageType.grade_faceCell]; exact hz), hw0L]
    simp only [hsLdef]
    rw [ite_eq_left hz]
  have hWdon (z : Fin I.right.card) (hz : I.right.toCellScheme.grade z ≤ j) :
      W (don I z) = WR z := by
    simp only [hWdef]
    rw [ite_eq_left (by rw [StageType.grade_faceCell]; exact hz), hw0R]
    simp only [hsRdef]
    rw [ite_eq_left hz]
  have hcut : IsCutLawful I j W := by
    refine (isCutLawful_iff j W).mpr ⟨?_, ?_⟩
    · exact (CellScheme.Rows.isLawfulBelow_congr (w := fun z ↦ fL z)
        (w' := fun z ↦ W (ctx I z)) fun z
          (hz : z ∈ I.left.toCellScheme.below ((univ : Finset (Fin (m + 1))), j)) ↦
            (hWctx z hz.2).symm).mp hfL
    · exact (CellScheme.Rows.isLawfulBelow_congr (w := fun z ↦ WR z)
        (w' := fun z ↦ W (don I z)) fun z
          (hz : z ∈ I.right.toCellScheme.below ((univ : Finset (Fin (m + 1))), j)) ↦
            (hWdon z hz.2).symm).mp hWR
  refine ⟨W, hcut, fun d hd ↦ ?_, fun d ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := exists_ctx_of_mem_below hd
    have hz : I.left.toCellScheme.grade z ≤ j := by
      have := hd.2
      change I.amalgam.toCellScheme.grade (ctx I z) ≤ j at this
      rwa [StageType.grade_faceCell] at this
    exact hWctx z hz
  · by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
    · rcases ctx_or_don d with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · have hz : I.left.toCellScheme.grade z ≤ j := by rwa [StageType.grade_faceCell] at hd
        rw [hWctx z hz]
        exact hfP _ (ctx_mem_below z hz)
      · have hz : I.right.toCellScheme.grade z ≤ j := by rwa [StageType.grade_faceCell] at hd
        rw [hWdon z hz]
        exact hWRh z hz
    · simp only [hWdef]
      rw [ite_eq_right hd]
  · have e1 : (fun z ↦ trK I K W (ctx I z)) = fK := by
      funext z
      rw [trK_ctx]
      simp only [hfKdef]
      split_ifs with hz
      · exact hWctx z (hz.trans hKj)
      · rfl
    have e2 : (fun z ↦ trK I K W (don I z)) = WK := by
      funext z
      rw [trK_don]
      split_ifs with hz
      · rw [hWdon z (hz.trans hKj), hWRK z hz]
      · exact (hWK.2 z hz).symm
    unfold rowAdm stateAdm
    rw [e1, e2]
    exact hA

/-- **The lift from the second coatom at a grade `j ≥ K`**: the donor provision on the parts of
grade at most `K`, the extension of the context face above `K` keeping the root of the donor face,
and the gluing. -/
theorem exists_lift_right (hext : ExtAbove I.left I.restrictFace_face_left K) {j : ℕ}
    (hKj : K ≤ j) (hjm : j ≤ m + 1) {h : Label.{u}} (hh : IsSelfVisible j h) {P : I.State}
    (hP : IsCutLawful I j P) (hPA : rowAdm I K Adm P) {f : I.State}
    (hf : I.amalgam.rows.IsLawfulBelow (coatD, j) fun d ↦ f d)
    (hfP : ∀ d ∈ I.amalgam.toCellScheme.below (coatD, j), min (f d) h = min (P d) h) :
    ∃ W : I.State, IsCutLawful I j W ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (coatD, j), W d = f d) ∧
      (∀ d, min (W d) h = min (P d) h) ∧ rowAdm I K Adm W := by
  classical
  -- the donor face and its part of grade at most `K`
  set fR : Fin I.right.card → Label.{u} := fun z ↦ f (don I z) with hfRdef
  have hfR : I.right.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) fun z ↦ fR z :=
    (don_isLawfulBelow_iff j f).mpr hf
  set fK : Fin I.right.card → Label.{u} :=
    fun z ↦ if I.right.toCellScheme.grade z ≤ K then fR z else ⊥ with hfKdef
  have hfK : LawfulAt I.right K fK := lawfulAt_trunc hfR hKj
  -- the parts of grade at most `K` of `P`
  have hPc := (isCutLawful_iff j P).mp hP
  set L : Fin I.left.card → Label.{u} :=
    fun z ↦ if I.left.toCellScheme.grade z ≤ K then P (ctx I z) else ⊥ with hLdef
  set R : Fin I.right.card → Label.{u} :=
    fun z ↦ if I.right.toCellScheme.grade z ≤ K then P (don I z) else ⊥ with hRdef
  have hL : LawfulAt I.left K L := lawfulAt_trunc hPc.1 hKj
  have hR : LawfulAt I.right K R := lawfulAt_trunc hPc.2 hKj
  have hgr (x : Fin I.face.card) : I.left.toCellScheme.grade (rootLm I x) =
      I.right.toCellScheme.grade (rootRm I x) :=
    (StageType.grade_faceCell _ x).trans (StageType.grade_faceCell _ x).symm
  have hy (x : Fin I.face.card) : L (rootLm I x) = R (rootRm I x) := by
    simp only [hLdef, hRdef, hgr, ctx_rootLm]
  have hadm : Adm L R := by
    have e1 : (fun z ↦ trK I K P (ctx I z)) = L := funext fun z ↦ trK_ctx K P z
    have e2 : (fun z ↦ trK I K P (don I z)) = R := funext fun z ↦ trK_don K P z
    have := hPA
    unfold rowAdm stateAdm at this
    rwa [e1, e2] at this
  have hfKR (z : Fin I.right.card) : min (fK z) h = min (R z) h := by
    simp only [hfKdef, hRdef]
    split_ifs with hz
    · exact hfP _ (don_mem_below z (hz.trans hKj))
    · rfl
  obtain ⟨WK, hWK, hWKr, hWKh, hA⟩ := hS.donor (hh.mono hKj) hL hR hy hadm hfK hfKR
  -- the context face above `K`
  have hctxP : I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j)
      fun z ↦ P (ctx I z) := hPc.1
  obtain ⟨WL, hWL, hWLK, hWLr, hWLh⟩ : ∃ WL : Fin I.left.card → Label.{u},
      I.left.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))), j) (fun d ↦ WL d) ∧
      (∀ d, I.left.toCellScheme.grade d ≤ K → WL d = WK d) ∧
      (∀ i, I.face.toCellScheme.grade i ≤ j → WL (rootLm I i) = fR (rootRm I i)) ∧
      ∀ d, I.left.toCellScheme.grade d ≤ j → min (WL d) h = min (P (ctx I d)) h := by
    have hWKroot (i : Fin I.face.card) (hi : I.face.toCellScheme.grade i ≤ K) :
        WK (rootLm I i) = fR (rootRm I i) := by
      rw [hWKr i]
      simp only [hfKdef]
      rw [ite_eq_left (by rw [StageType.grade_faceCell]; exact hi)]
    have hWKP (d : Fin I.left.card) (hd : I.left.toCellScheme.grade d ≤ K) :
        min (WK d) h = min (P (ctx I d)) h := by
      rw [hWKh d]
      simp only [hLdef]
      rw [ite_eq_left hd]
    rcases Nat.lt_or_eq_of_le hKj with hlt | rfl
    · refine hext hlt hjm hh hWK hctxP (isLawfulBelow_face _ hfR) hWKroot hWKP fun i hi ↦ ?_
      rw [ctx_rootLm]
      exact hfP _ (don_mem_below _ (by rw [StageType.grade_faceCell]; exact hi))
    · refine ⟨WK, hWK.1, fun _ _ ↦ rfl, hWKroot, hWKP⟩
  -- the gluing, below `(univ, j)`
  set sL : Fin I.left.card → Label.{u} :=
    fun z ↦ if I.left.toCellScheme.grade z ≤ j then WL z else ⊥ with hsLdef
  set sR : Fin I.right.card → Label.{u} :=
    fun z ↦ if I.right.toCellScheme.grade z ≤ j then fR z else ⊥ with hsRdef
  have hroot (x : Fin I.face.card) : sL (rootLm I x) = sR (rootRm I x) := by
    simp only [hsLdef, hsRdef]
    rw [← hgr]
    split_ifs with hx
    · exact hWLr x (by rw [← StageType.grade_faceCell I.restrictFace_face_left]; exact hx)
    · rfl
  obtain ⟨w0, hw0L, hw0R⟩ := exists_glue hroot
  set W : I.State := fun d ↦ if I.amalgam.toCellScheme.grade d ≤ j then w0 d else P d with hWdef
  have hWctx (z : Fin I.left.card) (hz : I.left.toCellScheme.grade z ≤ j) : W (ctx I z) = WL z := by
    simp only [hWdef]
    rw [ite_eq_left (by rw [StageType.grade_faceCell]; exact hz), hw0L]
    simp only [hsLdef]
    rw [ite_eq_left hz]
  have hWdon (z : Fin I.right.card) (hz : I.right.toCellScheme.grade z ≤ j) :
      W (don I z) = fR z := by
    simp only [hWdef]
    rw [ite_eq_left (by rw [StageType.grade_faceCell]; exact hz), hw0R]
    simp only [hsRdef]
    rw [ite_eq_left hz]
  have hcut : IsCutLawful I j W := by
    refine (isCutLawful_iff j W).mpr ⟨?_, ?_⟩
    · exact (CellScheme.Rows.isLawfulBelow_congr (w := fun z ↦ WL z)
        (w' := fun z ↦ W (ctx I z)) fun z
          (hz : z ∈ I.left.toCellScheme.below ((univ : Finset (Fin (m + 1))), j)) ↦
            (hWctx z hz.2).symm).mp hWL
    · exact (CellScheme.Rows.isLawfulBelow_congr (w := fun z ↦ fR z)
        (w' := fun z ↦ W (don I z)) fun z
          (hz : z ∈ I.right.toCellScheme.below ((univ : Finset (Fin (m + 1))), j)) ↦
            (hWdon z hz.2).symm).mp hfR
  refine ⟨W, hcut, fun d hd ↦ ?_, fun d ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := exists_don_of_mem_below hd
    have hz : I.right.toCellScheme.grade z ≤ j := by
      have := hd.2
      change I.amalgam.toCellScheme.grade (don I z) ≤ j at this
      rwa [StageType.grade_faceCell] at this
    exact hWdon z hz
  · by_cases hd : I.amalgam.toCellScheme.grade d ≤ j
    · rcases ctx_or_don d with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · have hz : I.left.toCellScheme.grade z ≤ j := by rwa [StageType.grade_faceCell] at hd
        rw [hWctx z hz]
        exact hWLh z hz
      · have hz : I.right.toCellScheme.grade z ≤ j := by rwa [StageType.grade_faceCell] at hd
        rw [hWdon z hz]
        exact hfP _ (don_mem_below z hz)
    · simp only [hWdef]
      rw [ite_eq_right hd]
  · have e1 : (fun z ↦ trK I K W (ctx I z)) = WK := by
      funext z
      rw [trK_ctx]
      split_ifs with hz
      · rw [hWctx z (hz.trans hKj), hWLK z hz]
      · exact (hWK.2 z hz).symm
    have e2 : (fun z ↦ trK I K W (don I z)) = fK := by
      funext z
      rw [trK_don]
      simp only [hfKdef]
      split_ifs with hz
      · exact hWdon z (hz.trans hKj)
      · rfl
    unfold rowAdm stateAdm
    rw [e1, e2]
    exact hA

/-- The constant `⊥` has the clause. -/
theorem rowAdm_bot : rowAdm I K Adm fun _ ↦ ⊥ := by
  have e : trK I K (fun _ ↦ ⊥) = fun _ ↦ ⊥ := by
    funext d; unfold trK; split_ifs <;> rfl
  unfold rowAdm
  rw [e]
  exact hS.bot

/-- **The lift provisions at a grade `K ≤ j ≤ m + 1` from either coatom**, for the catalogue of the
clause on the parts of grade at most `K`. -/
theorem liftProvisions_below (hextL : ExtAbove I.left I.restrictFace_face_left K)
    (hextR : ExtAbove I.right I.restrictFace_face_right K) {j : ℕ} (hKj : K ≤ j)
    (hjm : j ≤ m + 1) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    BotLiftProvisionOf (rowAdm I K Adm) j x ∧ CapLiftProvisionOf (rowAdm I K Adm) j x := by
  have hbotcut : IsCutLawful I j fun _ ↦ ⊥ :=
    ⟨CellScheme.Rows.isLawfulBelow_const_bot _, CellScheme.Rows.isLawfulBelow_const_bot _⟩
  simp only [Pts, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · refine ⟨fun f hf ↦ ?_, fun h hh _ _ P hP f hf hfP ↦ ?_⟩
    · obtain ⟨W, hcut, hWf, -, hA⟩ := exists_lift_left hS hextR hKj hjm (isSelfVisible_bot j)
        hbotcut (rowAdm_bot hS) hf (fun _ _ ↦ by simp)
      exact ⟨W, hcut, hWf, code_mem_rowCat_below hS hKj hcut hA⟩
    · obtain ⟨hPcat, hPA⟩ := mem_rowCat.mp hP
      have hPA' : rowAdm I K Adm P := by
        unfold rowAdm at hPA ⊢; rwa [trK_hat hKj] at hPA
      obtain ⟨W, hcut, hWf, hWh, hA⟩ := exists_lift_left hS hextR hKj hjm hh
        (mem_cat.mp hPcat).1 hPA' hf hfP
      exact ⟨W, hcut, hWf, hWh, orbitCode_mem_rowCat_below hS hKj hcut hA⟩
  · refine ⟨fun f hf ↦ ?_, fun h hh _ _ P hP f hf hfP ↦ ?_⟩
    · obtain ⟨W, hcut, hWf, -, hA⟩ := exists_lift_right hS hextL hKj hjm (isSelfVisible_bot j)
        hbotcut (rowAdm_bot hS) hf (fun _ _ ↦ by simp)
      exact ⟨W, hcut, hWf, code_mem_rowCat_below hS hKj hcut hA⟩
    · obtain ⟨hPcat, hPA⟩ := mem_rowCat.mp hP
      have hPA' : rowAdm I K Adm P := by
        unfold rowAdm at hPA ⊢; rwa [trK_hat hKj] at hPA
      obtain ⟨W, hcut, hWf, hWh, hA⟩ := exists_lift_right hS hextL hKj hjm hh
        (mem_cat.mp hPcat).1 hPA' hf hfP
      exact ⟨W, hcut, hWf, hWh, orbitCode_mem_rowCat_below hS hKj hcut hA⟩

/-- **The completion with the clause on the rows from the grade `K`**: the completion on the
catalogues of the clause on the parts of grade at most `K` from the grade `K`
(`Seed.exists_rowCompletion₀`). -/
theorem exists_completion_below (hm : 0 < m) (hKm : K ≤ m + 1)
    (hextL : ExtAbove I.left I.restrictFace_face_left K)
    (hextR : ExtAbove I.right I.restrictFace_face_right K) (hreads : ReadsAt I K Adm)
    (hst : Adm I.left.label I.right.label) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows K (rowAdm I K Adm) := by
  refine I.exists_rowCompletion₀ hm (N := K)
    (fun j hj hjm x hx ↦ (liftProvisions_below hS hextL hextR hj hjm hx).1)
    (fun j hj hjm x hx ↦ (liftProvisions_below hS hextL hextR hj hjm hx).2)
    (fun j hj _ R hR ↦ ?_) (fun _ ↦ ?_)
  · obtain ⟨hRcat, hRA⟩ := mem_rowCat.mp hR
    have hRA' : rowAdm I K Adm R := by
      unfold rowAdm at hRA ⊢; rwa [trK_hat (by omega)] at hRA
    have hc := (mem_cat.mp hRcat).1
    exact code_mem_rowCat_below hS hj ⟨hc.1.mono (X := (_, j)) ⟨subset_rfl, by omega⟩,
      hc.2.mono (X := (_, j)) ⟨subset_rfl, by omega⟩⟩ hRA'
  · have hcut : IsCutLawful I (m + 1) fun d ↦ I.amalgam.label d :=
      ⟨I.amalgam.isLawful.isLawfulBelow _, I.amalgam.isLawful.isLawfulBelow _⟩
    have hA : rowAdm I K Adm fun d ↦ I.amalgam.label d := by
      unfold rowAdm stateAdm
      refine hreads (fun z hz ↦ ?_) (fun z hz ↦ ?_) hst
      · rw [trK_ctx, ite_eq_left hz]
        exact (StageType.label_faceCell _ z).symm
      · rw [trK_don, ite_eq_left hz]
        exact (StageType.label_faceCell _ z).symm
    exact (mem_rowCat.mp (code_mem_rowCat_below hS hKm hcut hA)).2

/-- **The reading at the grade `K`**: in a completion whose rows of full scope at the grades `≥ K`
have the clause on their parts of grade at most `K`, every lawful labelling with an old cell of
grade `K` of the first coatom at `⊤` has the clause on its old cells. -/
theorem adm_of_hasAdmittedRows_below (hreads : ReadsAt I K Adm) (hK0 : 0 < K)
    (hKm : K ≤ m + 1) {F : CompletionBelowFullGrade I}
    (hF : F.HasAdmittedRows K (rowAdm I K Adm)) {o : Fin I.left.card}
    (ho : I.left.toCellScheme.grade o = K) {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawful q) (hqo : q (F.embed (ctx I o)) = ⊤) :
    Adm (fun x ↦ q (F.embed (ctx I x))) (fun x ↦ q (F.embed (don I x))) := by
  have hL := F.isLegalBelowFullGrade
  have hY : ((univ : Finset (Fin (m + 2))), K) ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨hL.isWellFormed.univ_mem_faces, hK0, by simp; omega⟩
  obtain ⟨u₀, hu₀⟩ := hL.exists_gradedIndex_eq _ hY (by simp only; omega)
  have hsc : F.scheme.toCellScheme.scope (F.embed (ctx I o)) ⊆
      F.scheme.toCellScheme.scope u₀ := by
    have : F.scheme.toCellScheme.scope u₀ = univ := congrArg Prod.fst hu₀
    rw [this]
    exact subset_univ _
  have hg : F.scheme.toCellScheme.grade (F.embed (ctx I o)) =
      F.scheme.toCellScheme.grade u₀ := by
    rw [F.isLowerEmbedding.grade_eq, StageType.grade_faceCell, ho]
    exact (congrArg Prod.snd hu₀).symm
  obtain ⟨u, hu, hle⟩ := hq.availability _ u₀ hsc hg
  have hu' : F.scheme.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 2))), K) :=
    hu.trans hu₀
  have hqu : q u = ⊤ := top_le_iff.mp (hqo ▸ hle)
  obtain ⟨g, σ, hw, heq⟩ := hq.locality u
  have hgu : F.scheme.toCellScheme.grade u = K := congrArg Prod.snd hu'
  have hgK : g K = ⊤ := by
    have e := heq ⟨u, CellScheme.mem_below_gradedIndex _ u⟩
    change min (q u) (q u) = min (σ _) (g (F.scheme.toCellScheme.grade u)) at e
    rw [hqu, min_self, hgu] at e
    exact (min_eq_top.mp e.symm).2
  have hbelow (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ K) :
      F.embed d ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, F.gradedIndex_embed, hu']
    exact ⟨subset_univ _, hd⟩
  have hval (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤ K) :
      q (F.embed d) = σ (trK I K (F.rowState u) d) := by
    have e := heq ⟨F.embed d, hbelow d hd⟩
    change min (q (F.embed d)) (q u) = min (σ _) (g (F.scheme.toCellScheme.grade (F.embed d)))
      at e
    have hgd : g (F.scheme.toCellScheme.grade (F.embed d)) = ⊤ := by
      refine top_le_iff.mp (hgK ▸ hw.antitone ?_)
      rw [F.isLowerEmbedding.grade_eq]
      exact hd
    rw [hqu, min_top_right, hgd, min_top_right] at e
    unfold trK
    rw [ite_eq_left hd, e, CompletionBelowFullGrade.rowState, Scheme.rowAt_of_mem (hbelow d hd)]
  have hA := hS.comp hw.monotone hw.map_bot (fun x ↦ hw.visibilityReplace_comm x K
    (by rw [hgK]; exact le_top) K le_rfl) (hF hu' le_rfl)
  refine hreads (fun z hz ↦ ?_) (fun z hz ↦ ?_) hA
  · exact (hval _ (by rw [StageType.grade_faceCell]; exact hz)).symm
  · exact (hval _ (by rw [StageType.grade_faceCell]; exact hz)).symm

end Provisions

end Seed

/-! ### The engine below the full grade -/

/-- **The extension above `K` at every legal stage type on `k + 1` points**, for `0 < K < k` (the
residual; at `K = k` it is `H2.extAbove_of_le`). -/
def ExtAboveAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K : ℕ⦄ (t : StageType.{u} α (k + 1)), t.IsLegal →
    ∀ ⦃p : StageType.{u} α k⦄ (hp : restrictFace Fin.castSuccEmb t = some p), 0 < K → K < k →
      ExtAbove t hp K

/-- The clause with the low cells filtered at `K` and the designated tops of grade at most `K`
reads only the cells of grade at most `K`. -/
theorem selfLow_reads {ιC ιD : Type*} {gC : ιC → ℕ} {gD : ιD → ℕ} {K : ℕ} {o r : ιC}
    (ho : gC o ≤ K) (hr : gC r ≤ K) {Lo Tops : Finset ιD} (hTops : ∀ t ∈ Tops, gD t ≤ K)
    {L L' : ιC → Label.{u}} {R R' : ιD → Label.{u}} (hL : ∀ z, gC z ≤ K → L z = L' z)
    (hR : ∀ z, gD z ≤ K → R z = R' z)
    (h : SelfLowG o r K (Lo.filter fun x ↦ gD x ≤ K) Tops L R) :
    SelfLowG o r K (Lo.filter fun x ↦ gD x ≤ K) Tops L' R' := by
  intro t ht hlt
  have hsup : (Lo.filter fun x ↦ gD x ≤ K).sup R = (Lo.filter fun x ↦ gD x ≤ K).sup R' :=
    Finset.sup_congr rfl fun x hx ↦ hR x (mem_filter.mp hx).2
  have hRt := hR t (hTops t ht)
  have hfr : frontierAt o r K L = frontierAt o r K L' := by
    unfold frontierAt; rw [hL o ho, hL r hr]
  rw [← hRt, ← hfr]
  exact h t ht (by rw [hsup, hRt]; exact hlt)

/-- The clause with fewer low cells is stronger. -/
theorem selfLow_of_subset {ιC ιD : Type*} {K : ℕ} {o r : ιC} {Lo Lo' Tops : Finset ιD}
    (hsub : Lo' ⊆ Lo) {L : ιC → Label.{u}} {R : ιD → Label.{u}}
    (h : SelfLowG o r K Lo' Tops L R) : SelfLowG o r K Lo Tops L R := fun t ht hlt ↦
  h t ht ((monotone_visibilityReplace le_rfl (Finset.sup_mono hsub)).trans_lt hlt)

/-- **The engine below the full grade from the extension above `K`**, on `k + 1 ≥ 2` points. -/
theorem admittedCompletionsBelowAt_of_ext {k : ℕ} (hk : 0 < k) (hext : ExtAboveAt.{u} k) :
    AdmittedCompletionsBelowAt.{u} k := by
  intro α K n t' hleg g o r hs hKk p hp tb htbleg htbp Lo Tops _ hTops hS
  set Lo1 : Finset (Fin tb.card) := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K with hLo1
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have hext' {t : StageType.{u} α (k + 1)} (ht : t.IsLegal)
      (htp : restrictFace Fin.castSuccEmb t = some p) : ExtAbove t htp K := by
    rcases Nat.lt_or_eq_of_le hKk with hlt | rfl
    · exact hext t ht htp hK0 hlt
    · exact extAbove_of_le ht htp hK0 le_rfl
  have hr : t'.toCellScheme.grade r ≤ K := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hreads : ReadsAt (Seed.ofCoatoms hleg htbleg hp htbp) K
      (SelfLowG o r K Lo1 Tops) :=
    fun _ _ _ _ hL hR h ↦ selfLow_reads hs.grade_owner.le hr (fun t ht ↦ (hTops t ht).2.1)
      hL hR h
  have hst : SelfLowG o r K Lo1 Tops t'.label tb.label := fun t ht _ ↦ (hTops t ht).1.symm ▸ le_top
  obtain ⟨F, hF⟩ := exists_completion_below (I := Seed.ofCoatoms hleg htbleg hp htbp) hS hk
    (by omega) (hext' hleg hp) (hext' htbleg htbp) hreads hst
  have hsub : Lo1 ⊆ Lo := fun x hx ↦ (mem_filter.mp hx).1
  exact ⟨F, fun q hq hqo ↦ selfLow_of_subset hsub
    (adm_of_hasAdmittedRows_below hS hreads hK0 (by omega) hF hs.grade_owner hq hqo)⟩

/-- **h2 with the lost point last at every arity from the open inputs**: owner lowering below the
designated tops below the full grade, the engine on one point, and the extension above `K`
(`K < k`). -/
theorem coatomCutoffDeterminationLast_of_ext (hOL : ∀ k, OwnerLoweringBelowAt.{u} k)
    (hEN0 : AdmittedCompletionsAt.{u} 0) (hext : ∀ k, 2 ≤ k → ExtAboveAt.{u} k) :
    CoatomCutoffDeterminationLast.{u} :=
  coatomCutoffDeterminationLast_of_open hOL hEN0 fun k hk ↦
    admittedCompletionsBelowAt_of_ext (by omega) (hext k hk)

/-- **At three points** (`k = 2`) the engine below the full grade at `K = 2` needs nothing: the
common face has no cell above `2`. -/
theorem extAboveAt_two_iff : ExtAboveAt.{u} 2 ↔
    ∀ ⦃α : Ordinal.{u}⦄ (t : StageType.{u} α 3), t.IsLegal →
      ∀ ⦃p : StageType.{u} α 2⦄ (hp : restrictFace Fin.castSuccEmb t = some p), ExtAbove t hp 1 :=
  ⟨fun h _ t ht _ hp ↦ h t ht hp one_pos one_lt_two, fun h _ K t ht _ hp hK0 hK2 ↦ by
    obtain rfl : K = 1 := by omega
    exact h t ht hp⟩

end VaughtConjecture.H2
