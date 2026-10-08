/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapAdmittedDetermination
import VaughtConjecture.Continuation.SourceGapFieldFace

/-!
# h2 at two points: coatom cutoff determination for source-gap contexts (work file)

WORK FILE (branch `research/work-h2`): a top-down skeleton.  Statements marked `SCAFFOLD` still
contain `sorry`; everything else is proved.

**The clause** (`H2.SelfLowG`): the LOW clause with every designated top as its own field:
`∀ t ∈ Tops, Lo.sup R < R t → frontierAt o r K L ≤ R t`.  At a reader with the context at its
labels the frontier is `⊤`, and every top is at least the cutoff while the cells below the top are
below it, so every top is `⊤`; no field cell is needed.

**The route at two points.**  For a legal source-gap context `t'` on two points with root in the
first point, and a legal coface `tb` of its coatom face `p`:
* a completion below the full grade of the seed `Seed.ofCoatoms` of `t'` and `tb` whose lawful
  labellings with the owner at `⊤` satisfy the clause on their old cells
  (`H2.RecProp`; SCAFFOLD `H2.exists_completion_recProp`);
* the coface `F.completion` (faces `t'` and `tb`);
* a permitted cutoff above the labels of `tb` other than `⊤` (`H2.exists_cutoff`);
* determination of the donor face from the clause (`H2.key_completion`, SCAFFOLD) and the generic
  passage to `IsDeterminedWithin` (`H2.isDeterminedWithin_addApex`).
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission

/-! ### The clause -/

/-- **The LOW clause with every designated top its own field.** -/
def SelfLowG {ιC ιD : Type*} (o r : ιC) (K : ℕ) (Lo Tops : Finset ιD) (L : ιC → Label.{u})
    (R : ιD → Label.{u}) : Prop :=
  ∀ t ∈ Tops, Lo.sup R < R t → frontierAt o r K L ≤ R t

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

/-- **A permitted cutoff above the labels other than `⊤`** of a stage type, at a limit stage. -/
theorem exists_cutoff {n : ℕ} (hα : Order.IsSuccLimit α) (t : StageType.{u} α n) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧ ∀ x, t.label x ≠ ⊤ → t.label x < δ := by
  obtain ⟨c, -, hcα, -, hc⟩ := exists_isSelfVisible_bound hα.isSuccPrelimit 0
    (WithBot.bot_lt_coe _ : (⊥ : Label.{u}) < α) t.label
  obtain ⟨δ, hδ, hcδ⟩ := MixedSeed.exists_permittedCutoff_gt hα hcα
  refine ⟨δ, hδ, fun x hx ↦ (hc x ?_).trans_lt hcδ⟩
  exact (t.atStage x).resolve_right hx

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

variable {I : Seed.{u} α 1}

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

section Key

variable {I : Seed.{u} α 1}

/-- The middle point is not on a face through the second coatom. -/
theorem one_notMem_range {n : ℕ} (g : Fin n ↪ Fin 1) :
    (1 : Fin 3) ∉ Set.range (extendByLast (g.trans (Fin.castSuccEmb : Fin 1 ↪ Fin 2))) := by
  rintro ⟨i, hi⟩
  induction i using Fin.lastCases with
  | last => rw [extendByLast_last] at hi; exact absurd hi (by decide)
  | cast j =>
    rw [extendByLast_castSucc] at hi
    have : (g j : Fin 1) = 0 := Subsingleton.elim _ _
    simp [this] at hi

/-- **The key step at two points.**  In the coface `F.completion` of a completion with the reading
property, a lawful labelling agreeing with it on the context face and capped at a cutoff above the
labels of the donor other than `⊤` agrees with it on the donor face along `extendByLast g`. -/
theorem key_completion (F : CompletionBelowFullGrade I) (hα : Order.IsSuccPrelimit α) {K : ℕ}
    {o r : Fin I.left.card} (hlo : I.left.label o = ⊤) (hlr : I.left.label r = ⊤)
    {Lo Tops : Finset (Fin I.right.card)} (hrec : RecProp F o r K Lo Tops) {δ : Label.{u}}
    (hδ0 : ⊥ < δ) (hδ : ∀ x, I.right.label x ≠ ⊤ → I.right.label x < δ)
    (hLo : ∀ x ∈ Lo, I.right.label x ≠ ⊤) {n : ℕ} {g : Fin n ↪ Fin 1}
    (hTops : ∀ x, I.right.label x = ⊤ → x ∈ I.right.toScheme.visibleCells (extendByLast g) →
      x ∉ I.right.toScheme.visibleCells Fin.castSuccEmb → x ∈ Tops)
    (ℓ : Fin (F.completion hα).card → Label.{u}) (hℓ : (F.completion hα).rows.IsLawful ℓ)
    (hleft : ∀ x ∈ (F.completion hα).toScheme.visibleCells Fin.castSuccEmb,
      ℓ x = (F.completion hα).label x)
    (hcap : ∀ x, min (ℓ x) δ = min ((F.completion hα).label x) δ) :
    ∀ y ∈ (F.completion hα).toScheme.visibleCells
      (extendByLast (g.trans (Fin.castSuccEmb : Fin 1 ↪ Fin 2))),
      ℓ y = (F.completion hα).label y := by
  set T := F.truncate hα
  have hn : 0 < 1 + 2 := by omega
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
      change ((F.scheme.toCellScheme.scope (F.embed (ctx I x)) : Set (Fin 3)) ⊆ _)
      rw [F.scope_embed, StageType.scope_faceCell]
      intro a ha
      obtain ⟨b, -, rfl⟩ := mem_map.mp (mem_coe.mp ha)
      exact ⟨b, rfl⟩
    rw [hleft _ (castSucc_mem_visibleCells_addApex (t := T) F.isLegalBelowFullGrade
      (Nat.succ_pos _) hv), hlab, hTe, StageType.label_faceCell]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := exists_castSucc_of_mem_visibleCells_addApex (t := T)
    F.isLegalBelowFullGrade (Nat.succ_pos _) ⟨1, one_notMem_range g⟩ hy
  have hx' := Scheme.mem_visibleCells.mp hx
  have hxu : F.scheme.toCellScheme.scope x ≠ univ := by
    intro he
    have h1 : (1 : Fin 3) ∈ ((F.scheme.toCellScheme.scope x : Finset (Fin 3)) : Set (Fin 3)) := by
      rw [he]; exact mem_coe.mpr (mem_univ _)
    exact one_notMem_range g (hx' h1)
  obtain ⟨e, rfl⟩ := F.mem_range_embed x hxu
  have he' : ((I.amalgam.toCellScheme.scope e : Finset (Fin 3)) : Set (Fin 3)) ⊆
      Set.range (extendByLast (g.trans (Fin.castSuccEmb : Fin 1 ↪ Fin 2))) := by
    have := hx'
    change ((F.scheme.toCellScheme.scope (F.embed e) : Set (Fin 3)) ⊆ _) at this
    rwa [F.scope_embed] at this
  have hrange : Set.range (extendByLast (g.trans (Fin.castSuccEmb : Fin 1 ↪ Fin 2))) =
      (fun i ↦ Coatom.right 1 i) '' Set.range (extendByLast g) := by
    rw [← extendByLast_trans]
    ext a
    simp [Coatom.right, Coatom.face]
  have hvR : e ∈ I.amalgam.toScheme.visibleCells (Coatom.right 1) := by
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
      have hv : F.embed (don I z) ∈ T.toScheme.visibleCells Fin.castSuccEmb := by
        refine Scheme.mem_visibleCells.mpr ?_
        change ((F.scheme.toCellScheme.scope (F.embed (don I z)) : Set (Fin 3)) ⊆ _)
        rw [F.scope_embed, StageType.scope_faceCell]
        intro a ha
        obtain ⟨b, hb, rfl⟩ := mem_map.mp (mem_coe.mp ha)
        obtain ⟨c, rfl⟩ := Scheme.mem_visibleCells.mp hroot (mem_coe.mpr hb)
        exact ⟨Fin.castSucc c, by simp [Coatom.right, Coatom.face]⟩
      rw [hleft _ (castSucc_mem_visibleCells_addApex (t := T) F.isLegalBelowFullGrade
        (Nat.succ_pos _) hv), hlab, hTe, StageType.label_faceCell]
    · -- a new top: the clause at the reader
      have hzv : z ∈ I.right.toScheme.visibleCells (extendByLast g) := by
        refine Scheme.mem_visibleCells.mpr fun a ha ↦ ?_
        have hmem : Coatom.right 1 a ∈ ((I.amalgam.toCellScheme.scope (don I z) :
            Finset (Fin 3)) : Set (Fin 3)) := by
          rw [StageType.scope_faceCell]
          exact mem_coe.mpr (mem_map_of_mem _ (mem_coe.mp ha))
        obtain ⟨b, hb, hba⟩ := (hrange ▸ he' hmem :
          Coatom.right 1 a ∈ (fun i ↦ Coatom.right 1 i) '' Set.range (extendByLast g))
        exact (Coatom.right 1).injective hba ▸ hb
      have hTz := hTops z hz hzv hroot
      have hqo : (fun x ↦ ℓ (Fin.castSucc x)) (F.embed (ctx I o)) = ⊤ := by
        change ℓ (Fin.castSucc (F.embed (ctx I o))) = ⊤
        rw [hctx, hlo]
      have hcl := hrec _ hqL hqo z hTz
      have hδz : δ ≤ ℓ (Fin.castSucc (F.embed (don I z))) := by
        have := hcap (Fin.castSucc (F.embed (don I z)))
        rw [hlab, hTe, StageType.label_faceCell, hz, min_eq_right le_top] at this
        exact min_eq_right_iff.mp this
      have hsup : Lo.sup (fun x ↦ ℓ (Fin.castSucc (F.embed (don I x)))) < δ := by
        refine (Finset.sup_lt_iff hδ0).mpr fun x hxL ↦ ?_
        have hxl := hδ x (hLo x hxL)
        have := hcap (Fin.castSucc (F.embed (don I x)))
        rw [hlab, hTe, StageType.label_faceCell] at this
        exact (Label.eq_of_min_eq_of_lt this.symm hxl).trans_lt hxl
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

/-! ### The completion with the reading property (SCAFFOLD) -/

set_option warningAsError false in
/-- **SCAFFOLD (contains `sorry`).**  A completion below the full grade of the seed of a legal
source-gap context on two points and a legal coface of its coatom face, with the reading property
for the designation `Lo` (cells below the top) and `Tops` (new tops of grade at most `K`). -/
theorem exists_completion_recProp {t' : StageType.{u} α 2} (hleg : t'.IsLegal) {K n : ℕ}
    {g : Fin n ↪ Fin 1} {l : Fin 2} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt K (g.trans Fin.castSuccEmb) l o r) {p : StageType.{u} α 1}
    (hp : restrictFace Fin.castSuccEmb t' = some p) {tb : StageType.{u} α 2}
    (htbleg : tb.IsLegal) (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} (hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤)
    (hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb) :
    ∃ F : CompletionBelowFullGrade (Seed.ofCoatoms hleg htbleg hp htbp),
      RecProp F o r K Lo Tops := by
  sorry

/-! ### h2 at two points, from the scaffold -/

/-- **h2 at two points** (modulo `H2.exists_completion_recProp`, SCAFFOLD). -/
theorem coatomCutoffDeterminationTwo : CoatomCutoffDeterminationTwo.{u} := by
  intro α K n t' g p hα hleg ⟨l, o, r, hs⟩ hp tb ⟨htbleg, htbp⟩ d hd hdK
  have hα' := hα.isSuccPrelimit
  set Lo : Finset (Fin tb.card) := univ.filter fun x ↦ tb.label x ≠ ⊤
  set Tops : Finset (Fin tb.card) := ((univ.filter fun x ↦ tb.label x = ⊤) ∩
    tb.toScheme.visibleCells (extendByLast g)) \ tb.toScheme.visibleCells Fin.castSuccEmb
  have hLo : ∀ x ∈ Lo, tb.label x ≠ ⊤ := fun x hx ↦ (mem_filter.mp hx).2
  have hTops : ∀ x ∈ Tops, tb.label x = ⊤ ∧ tb.toCellScheme.grade x ≤ K ∧
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb := by
    intro x hx
    obtain ⟨hx1, hxr⟩ := mem_sdiff.mp hx
    obtain ⟨hx2, hxv⟩ := mem_inter.mp hx1
    have hxt := (mem_filter.mp hx2).2
    refine ⟨hxt, ?_, hxr⟩
    obtain ⟨i, rfl⟩ := Scheme.exists_faceCell_eq (comap_toScheme_of_restrictFace hd) hxv
    have hdi : d.label i = ⊤ := (StageType.label_faceCell hd i).symm.trans hxt
    exact (StageType.grade_faceCell hd i).trans_le ((grade_le_topGrade hdi).trans hdK)
  have hmem : ∀ x, tb.label x = ⊤ → x ∈ tb.toScheme.visibleCells (extendByLast g) →
      x ∉ tb.toScheme.visibleCells Fin.castSuccEmb → x ∈ Tops := by
    intro x hxt hxv hxr
    simp [Tops, hxt, hxv, hxr]
  obtain ⟨F, hF⟩ := exists_completion_recProp hleg hs hp htbleg htbp hLo hTops
  obtain ⟨δ, hδ, hδlab⟩ := exists_cutoff hα tb
  have hR := F.restrictFace_right_completion hα'
  refine ⟨F.completion hα', ⟨F.isLegal_completion hα', F.restrictFace_left_completion hα'⟩, hR,
    δ, hδ, ?_⟩
  have hd' : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) (F.completion hα') = some d := by
    rw [← extendByLast_trans, ← restrictFace_trans _ _ _ hR]
    exact hd
  refine isDeterminedWithin_of_key (F.restrictFace_left_completion hα') hd'
    fun ℓ hℓ hleft hcap ↦ key_completion F hα' hs.label_owner hs.label_lost hF hδ.1 hδlab hLo
      hmem ℓ hℓ hleft hcap

end VaughtConjecture.H2
