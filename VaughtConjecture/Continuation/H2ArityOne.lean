/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapAdmittedDetermination
import VaughtConjecture.Continuation.SourceGapFieldFace

/-!
# h2 at two points: coatom cutoff determination for source-gap contexts (work file)

WORK FILE (branch `research/work-h2`).  Every declaration here is proved; the assembly at two
points is `VaughtConjecture.Continuation.H2Two`.

**The clause** (`H2.SelfLowG`): the LOW clause with every designated top as its own field:
`∀ t ∈ Tops, Lo.sup R < R t → frontierAt o r K L ≤ R t`.  At a reader with the context at its
labels the frontier is `⊤`, and every top is at least the cutoff while the cells below the top are
below it, so every top is `⊤`; no field cell is needed.

**The route at two points.**  For a legal source-gap context `t'` on two points with root in the
first point, and a legal coface `tb` of its coatom face `p`:
* a completion below the full grade of the seed `Seed.ofCoatoms` of `t'` and `tb` whose lawful
  labellings with the owner at `⊤` satisfy the clause on their old cells
  (`H2.RecProp`; `H2.exists_completion_recProp`);
* the coface `F.completion` (faces `t'` and `tb`);
* a permitted cutoff above the labels of `tb` other than `⊤` (`H2.exists_cutoff`);
* determination of the donor face from the clause (`H2.key_completion`) and the generic
  passage to `IsDeterminedWithin` (`H2.isDeterminedWithin_addApex`).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

/-! ### The clause -/

/-- **The LOW clause with every designated top its own field.** -/
def SelfLowG {ιC ιD : Type*} (o r : ιC) (K : ℕ) (Lo Tops : Finset ιD) (L : ιC → Label.{u})
    (R : ιD → Label.{u}) : Prop :=
  ∀ t ∈ Tops, visibilityReplace K K (Lo.sup R) < R t → frontierAt o r K L ≤ R t

/-! ### The statement at two points -/

/-- **Coatom cutoff determination for source-gap contexts on two points** (the clause of
`Realization.CoatomCutoffDetermination` at `k = 1`). -/
def CoatomCutoffDeterminationTwo : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃K n : ℕ⦄ (t' : StageType.{u} α 2) (g : Fin n ↪ Fin 1)
    (p : StageType.{u} α 1), Order.IsSuccLimit α → t'.IsLegal →
    t'.IsSourceGapContext K (g.trans Fin.castSuccEmb) →
    restrictFace Fin.castSuccEmb t' = some p → ∀ tb ∈ p.cofaces, ∀ d : StageType.{u} α (n + 1),
      restrictFace (extendByLast g) tb = some d → d.topGrade ≤ K →
        ∃ D' ∈ t'.cofaces, restrictFace (extendByLast Fin.castSuccEmb) D' = some tb ∧
          ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
            IsDeterminedWithin (receivingFamily D' δ) t' (g.trans Fin.castSuccEmb) d

/-! ### The state-level provisions of the clause -/

section StateLevel

variable {ιC ιD ιR : Type*} (rc : ιR → ιC) (rd : ιR → ιD) (K : ℕ)

/-- **An admission of states** (faces sharing a root): it holds at `⊥`, passes to images under
monotone maps fixing `⊥` and commuting with replacement at `K`, and has the lift provisions from
both coatoms at every cap self-visible at `K`. -/
structure IsStateAdmission (C : (ιC → Label.{u}) → Prop) (D : (ιD → Label.{u}) → Prop)
    (Adm : (ιC → Label.{u}) → (ιD → Label.{u}) → Prop) : Prop where
  bot : Adm (fun _ ↦ ⊥) (fun _ ↦ ⊥)
  comp {σ : Label.{u} → Label.{u}} (hσ : Monotone σ) (hσ0 : σ ⊥ = ⊥)
    (hc : ∀ x, σ (visibilityReplace K K x) = visibilityReplace K K (σ x))
    {L : ιC → Label.{u}} {R : ιD → Label.{u}} (h : Adm L R) :
    Adm (fun z ↦ σ (L z)) (fun z ↦ σ (R z))
  context {h : Label.{u}} (hh : IsSelfVisible K h) {L f : ιC → Label.{u}} {R : ιD → Label.{u}}
    (hL : C L) (hR : D R) (hy : ∀ x, L (rc x) = R (rd x)) (hadm : Adm L R) (hf : C f)
    (hfL : ∀ d, min (f d) h = min (L d) h) :
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧
      (∀ d, min (W d) h = min (R d) h) ∧ Adm f W
  donor {h : Label.{u}} (hh : IsSelfVisible K h) {L : ιC → Label.{u}} {R f : ιD → Label.{u}}
    (hL : C L) (hR : D R) (hy : ∀ x, L (rc x) = R (rd x)) (hadm : Adm L R) (hf : D f)
    (hfR : ∀ d, min (f d) h = min (R d) h) :
    ∃ W : ιC → Label.{u}, C W ∧ (∀ x, W (rc x) = f (rd x)) ∧
      (∀ d, min (W d) h = min (L d) h) ∧ Adm W f

variable {rc rd K}

/-- The designated cells below the top of an agreeing face, below a top under the cap, agree. -/
private theorem sup_lt_of_lt_cap {Lo : Finset ιD} {W R : ιD → Label.{u}} {h v : Label.{u}}
    (hWR : ∀ d, min (W d) h = min (R d) h) (hvh : v < h) (hlt : Lo.sup W < v) : Lo.sup R < v := by
  have hv0 : ⊥ < v := bot_le.trans_lt hlt
  refine (Finset.sup_lt_iff hv0).mpr fun d hd ↦ ?_
  have hWd : W d < v := (Finset.sup_lt_iff hv0).mp hlt d hd
  rw [Label.eq_of_min_eq_of_lt (hWR d) (hWd.trans hvh)]
  exact hWd

variable (rc rd K) in
/-- **Donor raising, refined**: as `FieldAdmission.DonorRaising`, except that a designated top
may also end at most the replacement at `K` of the low maximum of the served face (then the clause
asks nothing there). -/
def DonorRaisingV (C : (ιC → Label.{u}) → Prop) (D : (ιD → Label.{u}) → Prop) (A : Set ιR)
    (Lo Tops : Finset ιD) : Prop :=
  ∀ {h c : Label.{u}}, IsSelfVisible K h → IsSelfVisible K c → ∀ {R : ιD → Label.{u}}
    {f : ιC → Label.{u}}, D R → C f → (∀ x, min (f (rc x)) h = min (R (rd x)) h) →
    (∀ a ∈ A, c ≤ f (rc a)) →
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧ (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t ∈ Tops, h ≤ R t → c ≤ W t ∨ W t ≤ visibilityReplace K K (Lo.sup W)

variable (rc rd K) in
/-- **Donor raising with the gap**: as `H2.DonorRaisingV`, given in addition that every designated
top of the served face above the replaced low maximum is at least `min c h` (at a state of the
clause, `c` the frontier cap of the context face, this is the clause itself). -/
def DonorRaisingGap (C : (ιC → Label.{u}) → Prop) (D : (ιD → Label.{u}) → Prop) (A : Set ιR)
    (Lo Tops : Finset ιD) : Prop :=
  ∀ {h c : Label.{u}}, IsSelfVisible K h → IsSelfVisible K c → ∀ {R : ιD → Label.{u}}
    {f : ιC → Label.{u}}, D R → C f → (∀ x, min (f (rc x)) h = min (R (rd x)) h) →
    (∀ a ∈ A, c ≤ f (rc a)) →
    (∀ t ∈ Tops, visibilityReplace K K (Lo.sup R) < R t → min c h ≤ R t) →
    ∃ W : ιD → Label.{u}, D W ∧ (∀ x, W (rd x) = f (rc x)) ∧ (∀ d, min (W d) h = min (R d) h) ∧
      ∀ t ∈ Tops, h ≤ R t → c ≤ W t ∨ W t ≤ visibilityReplace K K (Lo.sup W)

/-- Refined donor raising gives donor raising with the gap. -/
theorem donorRaisingGap_of_V {C : (ιC → Label.{u}) → Prop} {D : (ιD → Label.{u}) → Prop}
    {A : Set ιR} {Lo Tops : Finset ιD} (hDR : DonorRaisingV rc rd K C D A Lo Tops) :
    DonorRaisingGap rc rd K C D A Lo Tops :=
  fun hh hc _ _ hR hf hroot hA _ ↦ hDR hh hc hR hf hroot hA

/-- Donor raising gives the refined donor raising. -/
theorem donorRaisingV_of {C : (ιC → Label.{u}) → Prop} {D : (ιD → Label.{u}) → Prop}
    {A : Set ιR} {Lo Tops : Finset ιD} (hDR : DonorRaising rc rd K C D A Tops) :
    DonorRaisingV rc rd K C D A Lo Tops := fun {_ _} hh hc {_ _} hR hf hroot hA ↦ by
  obtain ⟨W, hW, hWr, hWR, hWt⟩ := hDR hh hc hR hf hroot hA
  exact ⟨W, hW, hWr, hWR, fun t ht hRt ↦ .inl (hWt t ht hRt)⟩

/-- A map fixing `⊥` sends the maximum over `Lo` below the maximum of the images. -/
theorem le_sup_comp {Lo : Finset ιD} {σ : Label.{u} → Label.{u}} (hσ0 : σ ⊥ = ⊥)
    (R : ιD → Label.{u}) : σ (Lo.sup R) ≤ Lo.sup fun z ↦ σ (R z) := by
  rcases Lo.eq_empty_or_nonempty with he | hne
  · subst he
    rw [Finset.sup_empty, hσ0]
    exact bot_le
  · obtain ⟨d, hd, hdeq⟩ := Finset.exists_mem_eq_sup Lo hne R
    rw [hdeq]
    exact Finset.le_sup (f := fun z ↦ σ (R z)) hd

/-- Faces agreeing capped at `h`, with the replaced low maximum of one below a value under `h`,
have the same low maximum. -/
theorem sup_eq_of_lt_cap {Lo : Finset ιD} {W R : ιD → Label.{u}} {h v : Label.{u}}
    (hWR : ∀ d, min (W d) h = min (R d) h) (hvh : v < h)
    (hlt : visibilityReplace K K (Lo.sup W) < v) : Lo.sup R = Lo.sup W := by
  refine Finset.sup_congr rfl fun d hd ↦ ?_
  have hWd : W d < h := (((Finset.le_sup hd).trans (le_visibilityReplace (by omega) _)).trans_lt
    hlt).trans hvh
  exact Label.eq_of_min_eq_of_lt (hWR d) hWd

/-- **The clause is an admission of states** under the order law at the owner, the frontier bound
at the root cells `A`, donor raising with the gap, and owner lowering. -/
theorem selfLow_isStateAdmissionGap {o r : ιC} {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} {Lo Tops : Finset ιD} (A : Set ιR)
    (hCo : ∀ f, C f → IsSelfVisible K (f o))
    (hCF : ∀ f, C f → ∀ a ∈ A, frontierAt o r K f ≤ f (rc a))
    (hDR : DonorRaisingGap rc rd K C D A Lo Tops) (hOL : OwnerLowering rc rd o r K C D) :
    IsStateAdmission rc rd K C D (SelfLowG o r K Lo Tops) where
  bot := fun _ _ h ↦ absurd h (by simp)
  comp := fun {σ} hσ hσ0 hc {L R} h t ht hlt ↦ by
    have hlt' : visibilityReplace K K (Lo.sup R) < R t := by
      by_contra hcon
      refine hlt.not_ge ?_
      have hc' : R t ≤ visibilityReplace K K (Lo.sup R) := not_lt.mp hcon
      calc σ (R t) ≤ σ (visibilityReplace K K (Lo.sup R)) := hσ hc'
        _ = visibilityReplace K K (σ (Lo.sup R)) := hc _
        _ ≤ visibilityReplace K K (Lo.sup fun z ↦ σ (R z)) :=
          monotone_visibilityReplace le_rfl (le_sup_comp hσ0 R)
    have := hσ (h t ht hlt')
    refine le_trans (le_of_eq ?_) this
    rw [frontierAt, frontierAt, hσ.map_min, hc]
  context := fun {h} hh {L f R} hL hR hy hadm hf hfL ↦ by
    have hroot (x : ιR) : min (f (rc x)) h = min (R (rd x)) h := by rw [hfL, hy]
    have hsv : IsSelfVisible K (frontierAt o r K f) :=
      (hCo f hf).min (visibilityReplace_self_visibilityReplace le_rfl (f r))
    have hgap : ∀ t ∈ Tops, visibilityReplace K K (Lo.sup R) < R t →
        min (frontierAt o r K f) h ≤ R t := fun t ht hlt ↦ by
      rw [frontierAt_cap (o := o) (r := r) hh hfL]
      exact (min_le_left _ _).trans (hadm t ht hlt)
    obtain ⟨W, hW, hWr, hWR, hWt⟩ := hDR hh hsv hR hf hroot (hCF f hf) hgap
    refine ⟨W, hW, hWr, hWR, fun t ht hlt ↦ ?_⟩
    by_cases hRt : R t < h
    · have hWt' : W t = R t := Label.eq_of_min_eq_of_lt (hWR t).symm hRt
      rw [hWt'] at hlt ⊢
      have hsup := sup_eq_of_lt_cap (Lo := Lo) hWR hRt hlt
      have horig := hadm t ht (by rw [hsup]; exact hlt)
      have hFF : frontierAt o r K f = frontierAt o r K L :=
        Label.eq_of_min_eq_of_lt (frontierAt_cap (o := o) (r := r) hh hfL).symm (horig.trans_lt hRt)
      rw [hFF]
      exact horig
    · rcases hWt t ht (not_lt.mp hRt) with h1 | h1
      · exact h1
      · exact absurd hlt (not_lt.mpr h1)
  donor := fun {h} hh {L R f} hL hR hy hadm hf hfR ↦ by
    have hroot (x : ιR) : min (f (rd x)) h = min (L (rc x)) h := by rw [hfR, hy]
    obtain ⟨W, hW, hWr, hWL, hWF⟩ := hOL hh hL hf hroot
    refine ⟨W, hW, hWr, hWL, fun t ht hlt ↦ ?_⟩
    by_cases hRt : R t < h
    · have hft : f t = R t := Label.eq_of_min_eq_of_lt (hfR t).symm hRt
      rw [hft] at hlt ⊢
      have hsup := sup_eq_of_lt_cap (Lo := Lo) hfR hRt hlt
      have horig := hadm t ht (by rw [hsup]; exact hlt)
      have hFL : frontierAt o r K L < h := horig.trans_lt hRt
      have hcap := frontierAt_cap (o := o) (r := r) hh hWL
      rw [min_eq_left hWF, min_eq_left hFL.le] at hcap
      rw [hcap]
      exact horig
    · have hft : h ≤ f t := by
        have e := hfR t
        rw [min_eq_right (not_lt.mp hRt)] at e
        exact min_eq_right_iff.mp e
      exact hWF.trans hft

/-- **The clause is an admission of states** under the refined donor raising. -/
theorem selfLow_isStateAdmissionV {o r : ιC} {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} {Lo Tops : Finset ιD} (A : Set ιR)
    (hCo : ∀ f, C f → IsSelfVisible K (f o))
    (hCF : ∀ f, C f → ∀ a ∈ A, frontierAt o r K f ≤ f (rc a))
    (hDR : DonorRaisingV rc rd K C D A Lo Tops) (hOL : OwnerLowering rc rd o r K C D) :
    IsStateAdmission rc rd K C D (SelfLowG o r K Lo Tops) :=
  selfLow_isStateAdmissionGap A hCo hCF (donorRaisingGap_of_V hDR) hOL

/-- **The clause is an admission of states** under donor raising (the unrefined form). -/
theorem selfLow_isStateAdmission {o r : ιC} {C : (ιC → Label.{u}) → Prop}
    {D : (ιD → Label.{u}) → Prop} {Lo Tops : Finset ιD} (A : Set ιR)
    (hCo : ∀ f, C f → IsSelfVisible K (f o))
    (hCF : ∀ f, C f → ∀ a ∈ A, frontierAt o r K f ≤ f (rc a))
    (hDR : DonorRaising rc rd K C D A Tops) (hOL : OwnerLowering rc rd o r K C D) :
    IsStateAdmission rc rd K C D (SelfLowG o r K Lo Tops) :=
  selfLow_isStateAdmissionV A hCo hCF (donorRaisingV_of hDR) hOL

end StateLevel

/-! ### Generic: determination over a stage type with the apex -/

variable {α : Ordinal.{u}}

/-- **Determination from agreement on the donor face**, for any stage type `D`: if every lawful
labelling of its scheme agreeing with it on the context face and capped at `δ` agrees with it on
the donor face, the donor face is determined within the receiving family at `δ`. -/
theorem isDeterminedWithin_of_key {k p : ℕ} {D : StageType.{u} α (k + 1)}
    {t' : StageType.{u} α k} {h : Fin p ↪ Fin k} {d : StageType.{u} α (p + 1)} {δ : Label.{u}}
    (hT : restrictFace Fin.castSuccEmb D = some t')
    (hd : restrictFace (extendByLast h) D = some d)
    (key : ∀ ℓ : Fin D.card → Label.{u}, D.rows.IsLawful ℓ →
      (∀ x ∈ D.toScheme.visibleCells Fin.castSuccEmb, ℓ x = D.label x) →
      (∀ x, min (ℓ x) δ = min (D.label x) δ) →
      ∀ y ∈ D.toScheme.visibleCells (extendByLast h), ℓ y = D.label y) :
    IsDeterminedWithin (receivingFamily D δ) t' h d := by
  obtain ⟨S, ℓ0, hw, hc, hl, ha⟩ := D
  intro Q hQ hQT
  obtain ⟨hs, hlab⟩ := hQ
  obtain ⟨S', ℓ', hw', hc', hl', ha'⟩ := Q
  obtain rfl : S' = S := hs
  have hleft (x) (hx : x ∈ S'.visibleCells Fin.castSuccEmb) : ℓ' x = ℓ0 x :=
    label_eq_of_restrictFace_eq_some hQT hT hx
  rw [← hd]
  exact restrictFace_eq_of_label_eq (key ℓ' hl' hleft fun x ↦ hlab x x rfl)

/-! ### The cutoff -/

/-- **A permitted cutoff above a self-visible bound of the labels other than `⊤`** of a stage type,
at a limit stage. -/
theorem exists_cutoff {n : ℕ} (K : ℕ) (hα : Order.IsSuccLimit α) (t : StageType.{u} α n) :
    ∃ c δ : Label.{u}, IsSelfVisible K c ∧ (∀ x, t.label x ≠ ⊤ → t.label x ≤ c) ∧
      IsPermittedCutoff α δ ∧ c < δ := by
  obtain ⟨c, -, hcα, hcK, hc⟩ := exists_isSelfVisible_bound hα.isSuccPrelimit K
    (WithBot.bot_lt_coe _ : (⊥ : Label.{u}) < α) t.label
  obtain ⟨δ, hδ, hcδ⟩ := MixedSeed.exists_permittedCutoff_gt hα hcα
  exact ⟨c, δ, hcK, fun x hx ↦ hc x ((t.atStage x).resolve_right hx), hδ, hcδ⟩

/-! ### Generic: cells of a stage type with the apex visible through a proper face -/

/-- A cell of a stage type with the apex visible through a face missing a point is an old cell
visible through it. -/
theorem exists_castSucc_of_mem_visibleCells_addApex {k p : ℕ} {t : StageType.{u} α k}
    (ht : t.IsLegalBelowFullGrade) (hn : 0 < k) {f : Fin p ↪ Fin k}
    (hf : ∃ a, a ∉ Set.range f) {y : Fin (t.card + 1)}
    (hy : y ∈ (t.addApex ht hn).toScheme.visibleCells f) :
    ∃ x ∈ t.toScheme.visibleCells f, y = Fin.castSucc x := by
  have hy' := Scheme.mem_visibleCells.mp hy
  induction y using Fin.lastCases with
  | last =>
    obtain ⟨a, ha⟩ := hf
    have hsl : (t.addApex ht hn).toCellScheme.scope (Fin.last t.card) = univ :=
      Scheme.appendFullCellScheme_scope_last _ _
    exact absurd (hy' (show a ∈ (((t.addApex ht hn).toCellScheme.scope (Fin.last t.card)) :
      Set (Fin k)) from mem_coe.mpr (hsl ▸ mem_univ a))) ha
  | cast x =>
    refine ⟨x, Scheme.mem_visibleCells.mpr ?_, rfl⟩
    have hsc : (t.addApex ht hn).toCellScheme.scope (Fin.castSucc x) = t.toCellScheme.scope x :=
      Scheme.appendFullCellScheme_scope_castSucc _ _ x
    exact (congrArg (fun s : Finset (Fin k) ↦ (s : Set (Fin k))) hsc).symm.subset.trans hy'

/-- An old cell visible through a face stays visible after adding the apex. -/
theorem castSucc_mem_visibleCells_addApex {k p : ℕ} {t : StageType.{u} α k}
    (ht : t.IsLegalBelowFullGrade) (hn : 0 < k) {f : Fin p ↪ Fin k} {x : Fin t.card}
    (hx : x ∈ t.toScheme.visibleCells f) :
    (Fin.castSucc x : Fin (t.card + 1)) ∈ (t.addApex ht hn).toScheme.visibleCells f := by
  have hsc : (t.addApex ht hn).toCellScheme.scope (Fin.castSucc x) = t.toCellScheme.scope x :=
    Scheme.appendFullCellScheme_scope_castSucc _ _ x
  exact Scheme.mem_visibleCells.mpr ((congrArg (fun s : Finset (Fin k) ↦ (s : Set (Fin k)))
    hsc).subset.trans (Scheme.mem_visibleCells.mp hx))

/-! ### The cells of the two coatoms in the amalgam -/

section Seed

variable {m : ℕ} {I : Seed.{u} α m}

variable (I) in
/-- The cell of the amalgam over a cell of the context (the first coatom). -/
noncomputable abbrev ctx (x : Fin I.left.card) : Fin I.amalgam.card :=
  StageType.faceCell I.restrictFace_left x

variable (I) in
/-- The cell of the amalgam over a cell of the donor (the second coatom). -/
noncomputable abbrev don (x : Fin I.right.card) : Fin I.amalgam.card :=
  StageType.faceCell I.restrictFace_right x

/-- **The reading property of a completion**: in every lawful labelling with the owner at `⊤`,
the old cells satisfy the clause. -/
def RecProp (F : CompletionBelowFullGrade I) (o r : Fin I.left.card) (K : ℕ)
    (Lo Tops : Finset (Fin I.right.card)) : Prop :=
  ∀ q : Fin F.scheme.card → Label.{u}, F.scheme.rows.IsLawful q → q (F.embed (ctx I o)) = ⊤ →
    SelfLowG o r K Lo Tops (fun x ↦ q (F.embed (ctx I x))) (fun x ↦ q (F.embed (don I x)))

end Seed

/-! ### The key step: the clause determines the donor face -/

/-- A cell **determined by the root**: two lawful labellings agreeing at the root cells (visible
through `Fin.castSuccEmb`) agree at it.  Such a cell is read from the root, literal in the members
of a receiving family, and need not be designated. -/
def RootDet {n : ℕ} (t : StageType.{u} α (n + 1)) (x : Fin t.card) : Prop :=
  ∀ s s' : Fin t.card → Label.{u}, t.rows.IsLawful s → t.rows.IsLawful s' →
    (∀ y ∈ t.toScheme.visibleCells Fin.castSuccEmb, s y = s' y) → s x = s' x


section Key

variable {m : ℕ} {I : Seed.{u} α m}

/-- The last point of the first coatom is not on a face through the second coatom. -/
theorem last_notMem_range {m n : ℕ} (g : Fin n ↪ Fin m) :
    (Fin.last m).castSucc ∉
      Set.range (extendByLast (g.trans (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)))) := by
  rintro ⟨i, hi⟩
  induction i using Fin.lastCases with
  | last =>
    rw [extendByLast_last] at hi
    exact Fin.castSucc_ne_last _ hi.symm
  | cast j =>
    rw [extendByLast_castSucc] at hi
    exact Fin.castSucc_ne_last _ (Fin.castSucc_injective _ hi)

/-- The middle point is not on a face through the second coatom (two points). -/
theorem one_notMem_range {n : ℕ} (g : Fin n ↪ Fin 1) :
    (1 : Fin 3) ∉ Set.range (extendByLast (g.trans (Fin.castSuccEmb : Fin 1 ↪ Fin 2))) :=
  last_notMem_range g

/-- **The key step at two points.**  In the coface `F.completion` of a completion with the reading
property, a lawful labelling agreeing with it on the context face and capped at a cutoff above the
labels of the donor other than `⊤` agrees with it on the donor face along `extendByLast g`. -/
theorem key_completion (F : CompletionBelowFullGrade I) (hα : Order.IsSuccPrelimit α) {K : ℕ}
    {o r : Fin I.left.card} (hlo : I.left.label o = ⊤) (hlr : I.left.label r = ⊤)
    {Lo Tops : Finset (Fin I.right.card)} (hrec : RecProp F o r K Lo Tops) {δ : Label.{u}}
    {c : Label.{u}} (hc : IsSelfVisible K c)
    (hlabc : ∀ x, I.right.label x ≠ ⊤ → I.right.label x ≤ c) (hcδ : c < δ)
    (hLo : ∀ x ∈ Lo, I.right.label x ≠ ⊤) {n : ℕ} {g : Fin n ↪ Fin m}
    (hTops : ∀ x, I.right.label x = ⊤ → x ∈ I.right.toScheme.visibleCells (extendByLast g) →
      x ∉ I.right.toScheme.visibleCells Fin.castSuccEmb → ¬ RootDet I.right x → x ∈ Tops)
    (ℓ : Fin (F.completion hα).card → Label.{u}) (hℓ : (F.completion hα).rows.IsLawful ℓ)
    (hleft : ∀ x ∈ (F.completion hα).toScheme.visibleCells Fin.castSuccEmb,
      ℓ x = (F.completion hα).label x)
    (hcap : ∀ x, min (ℓ x) δ = min ((F.completion hα).label x) δ) :
    ∀ y ∈ (F.completion hα).toScheme.visibleCells
      (extendByLast (g.trans (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)))),
      ℓ y = (F.completion hα).label y := by
  set T := F.truncate hα
  have hδ (x : Fin I.right.card) (hx : I.right.label x ≠ ⊤) : I.right.label x < δ :=
    (hlabc x hx).trans_lt hcδ
  have hn : 0 < m + 2 := by omega
  have hlab (x : Fin F.scheme.card) : (F.completion hα).label (Fin.castSucc x) = T.label x :=
    addApex_label_castSucc (t := T) F.isLegalBelowFullGrade (Nat.succ_pos _) x
  have hTe (e : Fin I.amalgam.card) : T.label (F.embed e) = I.amalgam.label e :=
    F.truncate_label_embed hα e
  have hqL : T.rows.IsLawful fun x ↦ ℓ (Fin.castSucc x) :=
    isLawful_castSucc_addApex (t := T) F.isLegalBelowFullGrade (Nat.succ_pos _) hℓ
  -- the context cells are visible through the first coatom, and carry the labels of `I.left`
  have hctx (x : Fin I.left.card) : ℓ (Fin.castSucc (F.embed (ctx I x))) = I.left.label x := by
    have hv : F.embed (ctx I x) ∈ T.toScheme.visibleCells Fin.castSuccEmb := by
      refine Scheme.mem_visibleCells.mpr ?_
      change ((F.scheme.toCellScheme.scope (F.embed (ctx I x)) : Set (Fin (m + 2))) ⊆ _)
      rw [F.scope_embed, StageType.scope_faceCell]
      intro a ha
      obtain ⟨b, -, rfl⟩ := mem_map.mp (mem_coe.mp ha)
      exact ⟨b, rfl⟩
    rw [hleft _ (castSucc_mem_visibleCells_addApex (t := T) F.isLegalBelowFullGrade
      (Nat.succ_pos _) hv), hlab, hTe, StageType.label_faceCell]
  -- the root cells of the donor are read from the context face
  have hrootcell (z : Fin I.right.card)
      (hroot : z ∈ I.right.toScheme.visibleCells Fin.castSuccEmb) :
      ℓ (Fin.castSucc (F.embed (don I z))) = I.right.label z := by
    have hv : F.embed (don I z) ∈ T.toScheme.visibleCells Fin.castSuccEmb := by
      refine Scheme.mem_visibleCells.mpr ?_
      change ((F.scheme.toCellScheme.scope (F.embed (don I z)) : Set (Fin (m + 2))) ⊆ _)
      rw [F.scope_embed, StageType.scope_faceCell]
      intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_map.mp (mem_coe.mp ha)
      obtain ⟨c, rfl⟩ := Scheme.mem_visibleCells.mp hroot (mem_coe.mpr hb)
      exact ⟨Fin.castSucc c, by simp [Coatom.right, Coatom.face]⟩
    rw [hleft _ (castSucc_mem_visibleCells_addApex (t := T) F.isLegalBelowFullGrade
      (Nat.succ_pos _) hv), hlab, hTe, StageType.label_faceCell]
  -- the donor face of `ℓ` is lawful
  have hdonL : I.right.rows.IsLawful fun z ↦ ℓ (Fin.castSucc (F.embed (don I z))) := by
    have h2 : I.amalgam.rows.IsLawful fun d ↦ ℓ (Fin.castSucc (F.embed d)) := by
      have h1 := (show F.scheme.rows.IsLawful fun x ↦ ℓ (Fin.castSucc x) from hqL).comap
        F.isLowerEmbedding
      rw [F.comap_rows] at h1
      exact h1
    exact StageType.isLawful_comp_faceCell I.restrictFace_right h2
  intro y hy
  obtain ⟨x, hx, rfl⟩ := exists_castSucc_of_mem_visibleCells_addApex (t := T)
    F.isLegalBelowFullGrade (Nat.succ_pos _) ⟨_, last_notMem_range g⟩ hy
  have hx' := Scheme.mem_visibleCells.mp hx
  have hxu : F.scheme.toCellScheme.scope x ≠ univ := by
    intro he
    have h1 : (Fin.last m).castSucc ∈
        ((F.scheme.toCellScheme.scope x : Finset (Fin (m + 2))) : Set (Fin (m + 2))) := by
      rw [he]; exact mem_coe.mpr (mem_univ _)
    exact last_notMem_range g (hx' h1)
  obtain ⟨e, rfl⟩ := F.mem_range_embed x hxu
  have he' : ((I.amalgam.toCellScheme.scope e : Finset (Fin (m + 2))) : Set (Fin (m + 2))) ⊆
      Set.range (extendByLast (g.trans (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)))) := by
    have := hx'
    change ((F.scheme.toCellScheme.scope (F.embed e) : Set (Fin (m + 2))) ⊆ _) at this
    rwa [F.scope_embed] at this
  have hrange : Set.range (extendByLast (g.trans (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)))) =
      (fun i ↦ Coatom.right m i) '' Set.range (extendByLast g) := by
    rw [← extendByLast_trans]
    ext a
    simp [Coatom.right, Coatom.face]
  have hvR : e ∈ I.amalgam.toScheme.visibleCells (Coatom.right m) := by
    refine Scheme.mem_visibleCells.mpr (he'.trans ?_)
    rw [hrange]
    rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  obtain ⟨z, rfl⟩ := Scheme.exists_faceCell_eq
    (StageType.comap_toScheme_of_restrictFace I.restrictFace_right) hvR
  change ℓ (Fin.castSucc (F.embed (don I z))) = (F.completion hα).label
    (Fin.castSucc (F.embed (don I z)))
  rw [hlab, hTe, StageType.label_faceCell]
  by_cases hz : I.right.label z = ⊤
  · by_cases hroot : z ∈ I.right.toScheme.visibleCells Fin.castSuccEmb
    · -- a root cell: visible through the first coatom
      exact hrootcell z hroot
    by_cases hdet : RootDet I.right z
    · -- a cell determined by the root
      exact hdet _ _ hdonL I.right.isLawful fun y hy ↦ hrootcell y hy
    · -- a new top: the clause at the reader
      have hzv : z ∈ I.right.toScheme.visibleCells (extendByLast g) := by
        refine Scheme.mem_visibleCells.mpr fun a ha ↦ ?_
        have hmem : Coatom.right m a ∈ ((I.amalgam.toCellScheme.scope (don I z) :
            Finset (Fin (m + 2))) : Set (Fin (m + 2))) := by
          rw [StageType.scope_faceCell]
          exact mem_coe.mpr (mem_map_of_mem _ (mem_coe.mp ha))
        obtain ⟨b, hb, hba⟩ := (hrange ▸ he' hmem :
          Coatom.right m a ∈ (fun i ↦ Coatom.right m i) '' Set.range (extendByLast g))
        exact (Coatom.right m).injective hba ▸ hb
      have hTz := hTops z hz hzv hroot hdet
      have hqo : (fun x ↦ ℓ (Fin.castSucc x)) (F.embed (ctx I o)) = ⊤ := by
        change ℓ (Fin.castSucc (F.embed (ctx I o))) = ⊤
        rw [hctx, hlo]
      have hcl := hrec _ hqL hqo z hTz
      have hδz : δ ≤ ℓ (Fin.castSucc (F.embed (don I z))) := by
        have := hcap (Fin.castSucc (F.embed (don I z)))
        rw [hlab, hTe, StageType.label_faceCell, hz, min_eq_right le_top] at this
        exact min_eq_right_iff.mp this
      have hsup : visibilityReplace K K
          (Lo.sup (fun x ↦ ℓ (Fin.castSucc (F.embed (don I x))))) < δ := by
        refine (visibilityReplace_le_of_le le_rfl hc (Finset.sup_le fun x hxL ↦ ?_)).trans_lt hcδ
        have hxl := hδ x (hLo x hxL)
        have := hcap (Fin.castSucc (F.embed (don I x)))
        rw [hlab, hTe, StageType.label_faceCell] at this
        exact (Label.eq_of_min_eq_of_lt this.symm hxl).trans_le (hlabc x (hLo x hxL))
      have hfr := hcl (hsup.trans_le hδz)
      change min (ℓ (Fin.castSucc (F.embed (ctx I o))))
        (visibilityReplace K K (ℓ (Fin.castSucc (F.embed (ctx I r))))) ≤ _ at hfr
      rw [hctx, hctx, hlo, hlr, visibilityReplace_top, min_self, top_le_iff] at hfr
      rw [hz]
      exact hfr
  · have hzl := hδ z hz
    have := hcap (Fin.castSucc (F.embed (don I z)))
    rw [hlab, hTe, StageType.label_faceCell] at this
    exact Label.eq_of_min_eq_of_lt this.symm hzl

end Key


end VaughtConjecture.H2
