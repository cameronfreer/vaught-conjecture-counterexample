/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2GeneralZero

/-!
# h2 at every arity: the engine below the full grade with raised extensions (work file)

WORK FILE (branch `research/work-h2`).  No `sorry`.

The extension above `K` (`H2.ExtAbove`) fails on three points (`H2.not_extAboveAt_two`).  The
engine below the full grade needs less of it on each side:
* **the donor side** (`H2.ExtAboveRaised`): the donor face may be raised to `⊤` at cells of grade at
  most `K` where it is at least the cap; the clause is kept under such raises of the donor face
  (`H2.selfLow_raise`: a raised designated top is at least every frontier, and raising a low cell
  only makes the antecedents harder to meet);
* **the context side** (`H2.ExtFrontier`): the context face need not keep its part of grade at most
  `K` at all, only its frontier from above (`H2.selfLow_frontier`: the clause reads the context face
  only through the frontier).

`H2.admittedCompletionsBelowAt_of_raised`: the engine below the full grade from the two raised
extensions (`H2.ExtAboveRaisedAt`, `H2.ExtFrontierAt`); both hold at `K = k` by bountifulness.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission ProfileTower CellScheme

variable {α : Ordinal.{u}}

/-! ### The raised extensions -/

/-- **The extension above `K` with raises** (donor side): as `H2.ExtAbove`, the extension equal to
`w` at the grades at most `K` except that it may be `⊤` where `w` is at least the cap. -/
def ExtAboveRaised {k : ℕ} (t : StageType.{u} α (k + 1)) {p : StageType.{u} α k}
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
      (∀ d, t.toCellScheme.grade d ≤ K → W d = w d ∨ (h ≤ w d ∧ W d = ⊤)) ∧
      (∀ i, p.toCellScheme.grade i ≤ j → W (StageType.faceCell hp i) = y i) ∧
      ∀ d, t.toCellScheme.grade d ≤ j → min (W d) h = min (R d) h

/-- **The extension keeping the frontier** (context side): as `H2.ExtAbove`, with the part of grade
at most `K` replaced by a frontier at most that of `w`. -/
def ExtFrontier {k : ℕ} (t : StageType.{u} α (k + 1)) {p : StageType.{u} α k}
    (hp : restrictFace Fin.castSuccEmb t = some p) (K : ℕ) (o r : Fin t.card) : Prop :=
  ∀ ⦃j : ℕ⦄, K < j → j ≤ k + 1 → ∀ ⦃h : Label.{u}⦄, IsSelfVisible j h →
    ∀ ⦃w R : Fin t.card → Label.{u}⦄ ⦃y : Fin p.card → Label.{u}⦄, LawfulAt t K w →
    t.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), j) (fun d ↦ R d) →
    p.rows.IsLawfulBelow ((univ : Finset (Fin k)), j) (fun d ↦ y d) →
    (∀ i, p.toCellScheme.grade i ≤ K → w (StageType.faceCell hp i) = y i) →
    (∀ d, t.toCellScheme.grade d ≤ K → min (w d) h = min (R d) h) →
    (∀ i, p.toCellScheme.grade i ≤ j → min (y i) h = min (R (StageType.faceCell hp i)) h) →
    ∃ W : Fin t.card → Label.{u},
      t.rows.IsLawfulBelow ((univ : Finset (Fin (k + 1))), j) (fun d ↦ W d) ∧
      frontierAt o r K W ≤ frontierAt o r K w ∧
      (∀ i, p.toCellScheme.grade i ≤ j → W (StageType.faceCell hp i) = y i) ∧
      ∀ d, t.toCellScheme.grade d ≤ j → min (W d) h = min (R d) h

/-- The extension above `K` gives the raised one. -/
theorem ExtAbove.raised {k K : ℕ} {t : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
    {hp : restrictFace Fin.castSuccEmb t = some p} (h : ExtAbove t hp K) :
    ExtAboveRaised t hp K := by
  intro j hj hjk h' hh w R y hw hR hy hwy hwR hyR
  obtain ⟨W, hW, hWK, hWr, hWh⟩ := h hj hjk hh hw hR hy hwy hwR hyR
  exact ⟨W, hW, fun d hd ↦ .inl (hWK d hd), hWr, hWh⟩

/-- The extension above `K` gives the one keeping the frontier, at `o` and `r` of grade at most
`K`. -/
theorem ExtAbove.frontier {k K : ℕ} {t : StageType.{u} α (k + 1)} {p : StageType.{u} α k}
    {hp : restrictFace Fin.castSuccEmb t = some p} (h : ExtAbove t hp K) {o r : Fin t.card}
    (ho : t.toCellScheme.grade o ≤ K) (hr : t.toCellScheme.grade r ≤ K) :
    ExtFrontier t hp K o r := by
  intro j hj hjk h' hh w R y hw hR hy hwy hwR hyR
  obtain ⟨W, hW, hWK, hWr, hWh⟩ := h hj hjk hh hw hR hy hwy hwR hyR
  refine ⟨W, hW, ?_, hWr, hWh⟩
  unfold frontierAt
  rw [hWK o ho, hWK r hr]

/-! ### The clause under raises and lowered frontiers -/

/-- **The clause is kept under raises of the donor face to `⊤`.** -/
theorem selfLow_raise {ιC ιD : Type*} {K : ℕ} {o r : ιC} {Lo Tops : Finset ιD}
    {L : ιC → Label.{u}} {R R' : ιD → Label.{u}} (h : SelfLowG o r K Lo Tops L R)
    (hR : ∀ z, R' z = R z ∨ R' z = ⊤) : SelfLowG o r K Lo Tops L R' := by
  intro t ht hlt
  rcases hR t with e | e
  · have hle : Lo.sup R ≤ Lo.sup R' := Finset.sup_mono_fun fun z _ ↦ by
      rcases hR z with e' | e'
      · exact e'.ge
      · rw [e']; exact le_top
    rw [e] at hlt ⊢
    exact h t ht ((monotone_visibilityReplace le_rfl hle).trans_lt hlt)
  · rw [e]; exact le_top

/-- **The clause is kept under a lower frontier of the context face.** -/
theorem selfLow_frontier {ιC ιD : Type*} {K : ℕ} {o r : ιC} {Lo Tops : Finset ιD}
    {L L' : ιC → Label.{u}} {R : ιD → Label.{u}} (h : SelfLowG o r K Lo Tops L R)
    (hf : frontierAt o r K L' ≤ frontierAt o r K L) : SelfLowG o r K Lo Tops L' R :=
  fun t ht hlt ↦ hf.trans (h t ht hlt)

/-! ### The lifts with the raised extensions -/

section Seed

variable {m : ℕ} {I : Seed.{u} α m}

variable {K : ℕ} {Adm : (Fin I.left.card → Label.{u}) → (Fin I.right.card → Label.{u}) → Prop}

section Provisions

variable (hS : IsStateAdmission (rootLm I) (rootRm I) K (LawfulAt I.left K) (LawfulAt I.right K)
  Adm)
include hS

/-- **The lift from the first coatom at a grade `j ≥ K`, with the raised extension**: as
`H2.exists_lift_left`, the donor face extended above `K` possibly raised to `⊤` at cells of grade at
most `K` at least the cap; the clause is kept under such raises (`hraise`). -/
theorem exists_lift_left_raised (hext : ExtAboveRaised I.right I.restrictFace_face_right K)
    (hraise : ∀ ⦃L R R'⦄, Adm L R → (∀ z, R' z = R z ∨ R' z = ⊤) → Adm L R') {j : ℕ}
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
      (∀ d, I.right.toCellScheme.grade d ≤ K → WR d = WK d ∨ (h ≤ WK d ∧ WR d = ⊤)) ∧
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
    · refine ⟨WK, hWK.1, fun _ _ ↦ .inl rfl, hWKroot, hWKP⟩
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
    have e2 : ∀ z, trK I K W (don I z) = WK z ∨ trK I K W (don I z) = ⊤ := by
      intro z
      rw [trK_don]
      split_ifs with hz
      · rw [hWdon z (hz.trans hKj)]
        exact (hWRK z hz).imp id fun h' ↦ h'.2
      · exact .inl (hWK.2 z hz).symm
    unfold rowAdm stateAdm
    rw [e1]
    exact hraise hA e2

/-- **The lift from the second coatom at a grade `j ≥ K`, keeping the frontier**: as
`H2.exists_lift_right`, the context face extended to the grade `j` with the root of the donor face
and a frontier at most that of the donor provision (`hfront`). -/
theorem exists_lift_right_frontier {o r : Fin I.left.card} (ho : I.left.toCellScheme.grade o ≤ K)
    (hr : I.left.toCellScheme.grade r ≤ K)
    (hext : ExtFrontier I.left I.restrictFace_face_left K o r)
    (hfront : ∀ ⦃L L' R⦄, Adm L R → frontierAt o r K L' ≤ frontierAt o r K L → Adm L' R) {j : ℕ}
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
      frontierAt o r K WL ≤ frontierAt o r K WK ∧
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
    · refine ⟨WK, hWK.1, le_rfl, hWKroot, hWKP⟩
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
  · have e1 : frontierAt o r K (fun z ↦ trK I K W (ctx I z)) ≤ frontierAt o r K WK := by
      have hto : trK I K W (ctx I o) = WL o := by
        rw [trK_ctx, ite_eq_left ho, hWctx o (ho.trans hKj)]
      have htr : trK I K W (ctx I r) = WL r := by
        rw [trK_ctx, ite_eq_left hr, hWctx r (hr.trans hKj)]
      unfold frontierAt at hWLK ⊢
      change min (trK I K W (ctx I o)) (visibilityReplace K K (trK I K W (ctx I r))) ≤ _
      rw [hto, htr]
      exact hWLK
    have e2 : (fun z ↦ trK I K W (don I z)) = fK := by
      funext z
      rw [trK_don]
      simp only [hfKdef]
      split_ifs with hz
      · exact hWdon z (hz.trans hKj)
      · rfl
    unfold rowAdm stateAdm
    rw [e2]
    exact hfront hA e1

/-- **The lift provisions at a grade `K ≤ j ≤ m + 1` from either coatom**, for the catalogue of the
clause on the parts of grade at most `K`. -/
theorem liftProvisions_raised {o r : Fin I.left.card} (ho : I.left.toCellScheme.grade o ≤ K)
    (hr : I.left.toCellScheme.grade r ≤ K)
    (hraise : ∀ ⦃L R R'⦄, Adm L R → (∀ z, R' z = R z ∨ R' z = ⊤) → Adm L R')
    (hfront : ∀ ⦃L L' R⦄, Adm L R → frontierAt o r K L' ≤ frontierAt o r K L → Adm L' R)
    (hextL : ExtFrontier I.left I.restrictFace_face_left K o r)
    (hextR : ExtAboveRaised I.right I.restrictFace_face_right K) {j : ℕ} (hKj : K ≤ j)
    (hjm : j ≤ m + 1) {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) :
    BotLiftProvisionOf (rowAdm I K Adm) j x ∧ CapLiftProvisionOf (rowAdm I K Adm) j x := by
  have hbotcut : IsCutLawful I j fun _ ↦ ⊥ :=
    ⟨CellScheme.Rows.isLawfulBelow_const_bot _, CellScheme.Rows.isLawfulBelow_const_bot _⟩
  simp only [Pts, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · refine ⟨fun f hf ↦ ?_, fun h hh _ _ P hP f hf hfP ↦ ?_⟩
    · obtain ⟨W, hcut, hWf, -, hA⟩ := exists_lift_left_raised hS hextR hraise hKj hjm
        (isSelfVisible_bot j)
        hbotcut (rowAdm_bot hS) hf (fun _ _ ↦ by simp)
      exact ⟨W, hcut, hWf, code_mem_rowCat_below hS hKj hcut hA⟩
    · obtain ⟨hPcat, hPA⟩ := mem_rowCat.mp hP
      have hPA' : rowAdm I K Adm P := by
        unfold rowAdm at hPA ⊢; rwa [trK_hat hKj] at hPA
      obtain ⟨W, hcut, hWf, hWh, hA⟩ := exists_lift_left_raised hS hextR hraise hKj hjm hh
        (mem_cat.mp hPcat).1 hPA' hf hfP
      exact ⟨W, hcut, hWf, hWh, orbitCode_mem_rowCat_below hS hKj hcut hA⟩
  · refine ⟨fun f hf ↦ ?_, fun h hh _ _ P hP f hf hfP ↦ ?_⟩
    · obtain ⟨W, hcut, hWf, -, hA⟩ := exists_lift_right_frontier hS ho hr hextL hfront hKj hjm
        (isSelfVisible_bot j)
        hbotcut (rowAdm_bot hS) hf (fun _ _ ↦ by simp)
      exact ⟨W, hcut, hWf, code_mem_rowCat_below hS hKj hcut hA⟩
    · obtain ⟨hPcat, hPA⟩ := mem_rowCat.mp hP
      have hPA' : rowAdm I K Adm P := by
        unfold rowAdm at hPA ⊢; rwa [trK_hat hKj] at hPA
      obtain ⟨W, hcut, hWf, hWh, hA⟩ := exists_lift_right_frontier hS ho hr hextL hfront hKj hjm hh
        (mem_cat.mp hPcat).1 hPA' hf hfP
      exact ⟨W, hcut, hWf, hWh, orbitCode_mem_rowCat_below hS hKj hcut hA⟩

/-- **The completion with the clause on the rows from the grade `K`, with the raised
extensions**: the completion on the
catalogues of the clause on the parts of grade at most `K` from the grade `K`
(`Seed.exists_rowCompletion₀`). -/
theorem exists_completion_raised (hm : 0 < m) (hKm : K ≤ m + 1) {o r : Fin I.left.card}
    (ho : I.left.toCellScheme.grade o ≤ K) (hr : I.left.toCellScheme.grade r ≤ K)
    (hraise : ∀ ⦃L R R'⦄, Adm L R → (∀ z, R' z = R z ∨ R' z = ⊤) → Adm L R')
    (hfront : ∀ ⦃L L' R⦄, Adm L R → frontierAt o r K L' ≤ frontierAt o r K L → Adm L' R)
    (hextL : ExtFrontier I.left I.restrictFace_face_left K o r)
    (hextR : ExtAboveRaised I.right I.restrictFace_face_right K) (hreads : ReadsAt I K Adm)
    (hst : Adm I.left.label I.right.label) :
    ∃ F : CompletionBelowFullGrade I, F.HasAdmittedRows K (rowAdm I K Adm) := by
  refine I.exists_rowCompletion₀ hm (N := K)
    (fun j hj hjm x hx ↦ (liftProvisions_raised hS ho hr hraise hfront hextL hextR hj hjm hx).1)
    (fun j hj hjm x hx ↦ (liftProvisions_raised hS ho hr hraise hfront hextL hextR hj hjm hx).2)
    (fun j hj R hR ↦ ?_) (fun _ ↦ ?_)
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


end Provisions

end Seed

/-! ### The engine below the full grade from the raised extensions -/

/-- **The raised extension above `K` at every legal stage type on `k + 1` points**, `0 < K < k`
(donor side). -/
def ExtAboveRaisedAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K : ℕ⦄ (t : StageType.{u} α (k + 1)), t.IsLegal →
    ∀ ⦃p : StageType.{u} α k⦄ (hp : restrictFace Fin.castSuccEmb t = some p), 0 < K → K < k →
      ExtAboveRaised t hp K

/-- **The extension keeping the frontier at every legal source-gap context on `k + 1` points with
the lost point last**, `0 < K < k` (context side). -/
def ExtFrontierAt (k : ℕ) : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α (k + 1)), t'.IsLegal →
    ∀ (g : Fin n ↪ Fin k) {o r : Fin t'.card},
    t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) (Fin.last k) o r → K < k →
    ∀ ⦃p : StageType.{u} α k⦄ (hp : restrictFace Fin.castSuccEmb t' = some p),
      ExtFrontier t' hp K o r

/-- **The engine below the full grade from the raised extensions**, on `k + 1 ≥ 2` points. -/
theorem admittedCompletionsBelowAt_of_raised {k : ℕ} (hk : 0 < k)
    (hextR : ExtAboveRaisedAt.{u} k) (hextF : ExtFrontierAt.{u} k) :
    AdmittedCompletionsBelowAt.{u} k := by
  intro α K n t' hleg g o r hs hKk p hp tb htbleg htbp Lo Tops _ hTops hS
  set Lo1 : Finset (Fin tb.card) := Lo.filter fun x ↦ tb.toCellScheme.grade x ≤ K with hLo1
  have hK0 : 0 < K := hs.grade_owner ▸ t'.isWellFormed.isWellFormed.grade_pos o
  have ho : t'.toCellScheme.grade o ≤ K := hs.grade_owner.le
  have hr : t'.toCellScheme.grade r ≤ K := by
    have := grade_le_topGrade hs.label_lost
    rwa [hs.topGrade_eq] at this
  have hraised {t : StageType.{u} α (k + 1)} (ht : t.IsLegal)
      (htp : restrictFace Fin.castSuccEmb t = some p) : ExtAboveRaised t htp K := by
    rcases Nat.lt_or_eq_of_le hKk with hlt | rfl
    · exact hextR t ht htp hK0 hlt
    · exact (extAbove_of_le ht htp hK0 le_rfl).raised
  have hfr : ExtFrontier t' hp K o r := by
    rcases Nat.lt_or_eq_of_le hKk with hlt | rfl
    · exact hextF t' hleg g hs hlt hp
    · exact (extAbove_of_le hleg hp hK0 le_rfl).frontier ho hr
  have hreads : ReadsAt (Seed.ofCoatoms hleg htbleg hp htbp) K (SelfLowG o r K Lo1 Tops) :=
    fun _ _ _ _ hL hR h ↦ selfLow_reads ho hr (fun t ht ↦ (hTops t ht).2.1) hL hR h
  have hst : SelfLowG o r K Lo1 Tops t'.label tb.label := fun t ht _ ↦ (hTops t ht).1.symm ▸ le_top
  obtain ⟨F, hF⟩ := exists_completion_raised (I := Seed.ofCoatoms hleg htbleg hp htbp) hS hk
    (by omega) ho hr (fun _ _ _ h hR ↦ selfLow_raise h hR) (fun _ _ _ h hf ↦ selfLow_frontier h hf)
    hfr (hraised htbleg htbp) hreads hst
  have hsub : Lo1 ⊆ Lo := fun x hx ↦ (mem_filter.mp hx).1
  exact ⟨F, fun q hq hqo ↦ selfLow_of_subset hsub
    (adm_of_hasAdmittedRows_below hS hreads hK0 (by omega) hF hs.grade_owner hq hqo)⟩

end VaughtConjecture.H2
