/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.LegalSystem

/-!
# Legal templates on arbitrary finite carriers: the second bullet of [AFK26, Proposition 4.30]

Numbering as in the current draft of [AFK26].  The positional statement, for legal templates on
the points `Fin n`, is `proposition430Target`
(`VaughtConjecture.Correspondence.TemplateSystem.LegalSystem`).  This file proves the second bullet
of [AFK26, Proposition 4.30] ("all finite legal templates are isomorphic to renamings of templates
in `L`") for legal templates whose underlying set is an arbitrary finite type of points
(`fintypeCarrierClause_chosenLegalTemplates`), and for underlying sets and cells that are finite
subsets of `ℕ`, the printed collection `T` of [AFK26, Definition 4.11 (a)]
(`finsetNatCarrierClause_chosenLegalTemplates`), and with them the full-carrier forms
`proposition430FintypeTarget` and `proposition430FinsetNatTarget`.

* **Cells below a cell** (`IsIsoRenamingAlong.belowEquiv`): an isomorphism to a renaming
  ([AFK26, Definitions 4.6 and 4.7]) restricts, for every cell `d`, to a bijection between the
  cells below `d` and the cells below its image; it uses only the fields `scope_eq` and `grade_eq`
  (`IsIsoRenamingAlong.gradedIndex_le_iff`).  The rows correspond along it
  (`IsIsoRenamingAlong.row_belowEquiv`).
* **Legality along a point embedding** (`CellScheme.Rows.IsLegalTemplate.comap`): the pullback of
  a legal template along an embedding of points `f : β ↪ α` (the cells are those visible through
  `f`) is legal ([AFK26, Definition 4.29]).  For a bijection of points this is transport of
  legality along the isomorphism; invariance under renaming of cells is
  `CellScheme.Rows.isLegalTemplate_comap_reindex_iff`.
* **Transport of the isomorphism**: along a renaming of the target
  (`IsIsoRenamingAlong.renameCells`), from a pullback along a point embedding
  (`IsIsoRenamingAlong.of_comap`), and for the positional stage type of a template on `Fin n`
  (`isIsoRenamingAlong_toStageType`).

The construction for a legal template on a finite type `P` with `i : P ≃ Fin n`: pull it back
along `i⁻¹` to the points `Fin n` (legal by `IsLegalTemplate.comap`, a plan by
`CellScheme.IsWellFormed.comap`, nonempty by `Geometry.IsTemplatePlan.nonempty`), number its cells
(`CellScheme.Rows.toStageTypeOfLegal`), and take the chosen representative of its class
(T*-3 of [AFK26, Definition 4.11]); the isomorphism composes the three steps.
-/

universe u w

namespace VaughtConjecture

open Finset Ordinal

/-! ### Cells below a cell -/

namespace IsIsoRenamingAlong

variable {ι P : Type*} {α : Ordinal.{u}} {n : ℕ} {j : Fin n ↪ P} {D : CellScheme ι P}
  {R : D.Rows.{u}} {p : ι → Label.{u}} {t : StageType.{u} α n} {e : ι ≃ Fin t.card}

/-- **The cell bijection preserves and reflects the graded order** [AFK26, Definitions 4.2, 4.6
and 4.7].  Uses the fields `scope_eq` and `grade_eq` only. -/
theorem gradedIndex_le_iff (h : IsIsoRenamingAlong j D R p t e) (x d : ι) :
    t.toCellScheme.gradedIndex (e x) ≤ t.toCellScheme.gradedIndex (e d) ↔
      D.gradedIndex x ≤ D.gradedIndex d := by
  simp only [CellScheme.gradedIndex_le_iff, CellScheme.gradedIndex_fst,
    CellScheme.gradedIndex_snd, ← Finset.map_subset_map (f := j), h.scope_eq, h.grade_eq]

/-- **The bijection between the cells below a cell** `D ↓ d` and the cells of `t` below the image
`e d`, restricting `e` (from `gradedIndex_le_iff`; the fields `scope_eq` and `grade_eq`). -/
def belowEquiv (h : IsIsoRenamingAlong j D R p t e) (d : ι) :
    D.below (D.gradedIndex d) ≃ t.toCellScheme.below (t.toCellScheme.gradedIndex (e d)) where
  toFun x := ⟨e x, (h.gradedIndex_le_iff x d).mpr x.2⟩
  invFun y := ⟨e.symm y, (h.gradedIndex_le_iff _ d).mp (by rw [e.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

@[simp] theorem coe_belowEquiv (h : IsIsoRenamingAlong j D R p t e) (d : ι)
    (x : D.below (D.gradedIndex d)) : ((h.belowEquiv d x : Fin t.card)) = e x :=
  rfl

/-- **The rows correspond along the bijection of the cells below a cell.** -/
theorem row_belowEquiv (h : IsIsoRenamingAlong j D R p t e) (d : ι)
    (x : D.below (D.gradedIndex d)) : t.rows.row (e d) (h.belowEquiv d x) = R.row d x :=
  h.row_eq d x _ rfl

/-- **Renaming the target**: an isomorphism to a renaming of `t` is one to a renaming of every
renaming of `t` ([AFK26, Definition 4.6]). -/
theorem renameCells (h : IsIsoRenamingAlong j D R p t e) {k : ℕ} (σ : Fin k ≃ Fin t.card) :
    IsIsoRenamingAlong j D R p (t.renameCells σ) (e.trans σ.symm) where
  ground_eq := h.ground_eq
  faces_eq := h.faces_eq
  scope_eq d := by
    change (t.toCellScheme.scope (σ (σ.symm (e d)))).map j = _
    rw [σ.apply_symm_apply]
    exact h.scope_eq d
  grade_eq d := by
    change t.toCellScheme.grade (σ (σ.symm (e d))) = _
    rw [σ.apply_symm_apply]
    exact h.grade_eq d
  label_eq d := by
    change t.label (σ (σ.symm (e d))) = _
    rw [σ.apply_symm_apply]
    exact h.label_eq d
  row_eq d x y hy := by
    change t.rows.row (σ (σ.symm (e d))) ⟨σ y.1, _⟩ = _
    have hy' : σ y.1 = e x := by
      rw [hy]
      exact σ.apply_symm_apply (e x)
    exact (t.rows.row_congr (σ.apply_symm_apply (e d)) (t' := h.belowEquiv d x) hy').trans
      (h.row_belowEquiv d x)

end IsIsoRenamingAlong

/-! ### Legality along a point embedding -/

/-- **Legal templates pull back along embeddings of points** [AFK26, Definition 4.29]: for finitely
many cells, at a stage `θ ≥ ω ^ 2` that is zero or a limit, the pullback of a legal template along
`f : β ↪ α` (the cells visible through `f`, with their rows and labels) is a legal template.  For
a bijection of points this is the transport of legality along an isomorphism
([AFK26, Definition 4.7]). -/
theorem CellScheme.Rows.IsLegalTemplate.comap {ι α β : Type*} [Finite ι] {D : CellScheme ι α}
    {R : D.Rows.{u}} {θ : Ordinal.{u}} {p : ι → Label.{u}} (hθ : Order.IsSuccPrelimit θ)
    (hθ2 : ω ^ 2 ≤ θ) (hL : R.IsLegalTemplate θ p) (f : β ↪ α) :
    (R.comap (CellScheme.IsLowerEmbedding.comap D f)).IsLegalTemplate θ (p ∘ (↑)) := by
  obtain ⟨hat, hgi, hc, hl, hcons, hb, hs⟩ := (isLegalTemplate_iff hθ hθ2).mp hL
  refine (isLegalTemplate_iff hθ hθ2).mpr ⟨fun d ↦ hat d.1, fun d ↦ ?_, hc.comap f,
    hl.comap _, hcons.comap _, hb.comap f, hs.comap _⟩
  rw [CellScheme.mem_gradedFaces_comap]
  have hd : Prod.map (Finset.map f) id ((D.comap f).gradedIndex d) = D.gradedIndex d.1 :=
    Prod.ext (CellScheme.map_comap_scope D f d) rfl
  rw [hd]
  exact hgi d.1

/-! ### Transport of the isomorphism -/

/-- **The positional stage type of a template is isomorphic to it** along the identity of points
and the numbering of its cells ([AFK26, Definitions 4.6 and 4.7]). -/
theorem isIsoRenamingAlong_toStageType {κ : Type*} {n k : ℕ} {D : CellScheme κ (Fin n)}
    {R : D.Rows.{u}} {p : κ → Label.{u}} {α θ : Ordinal.{u}} (e : Fin k ≃ κ)
    (hground : D.ground = Finset.univ) (hT : R.IsTemplate θ p) (hl : R.IsLawful p)
    (hα : ∀ d, Label.AtStage α (p d)) :
    IsIsoRenamingAlong (Function.Embedding.refl (Fin n)) D R p
      (R.toStageType p e hground hT hl hα) e.symm where
  ground_eq := by rw [hground, Finset.map_refl]
  faces_eq := by
    ext B
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply,
      Finset.map_refl, exists_eq_right]
    exact Iff.rfl
  scope_eq d := by
    change (D.scope (e (e.symm d))).map _ = _
    rw [e.apply_symm_apply, Finset.map_refl]
  grade_eq d := by
    change D.grade (e (e.symm d)) = _
    rw [e.apply_symm_apply]
  label_eq d := by
    change p (e (e.symm d)) = _
    rw [e.apply_symm_apply]
  row_eq d x y hy := by
    change R.row (e (e.symm d)) ⟨e y.1, _⟩ = _
    refine R.row_congr (e.apply_symm_apply d) ?_
    change e y.1 = x.1
    rw [hy]
    exact e.apply_symm_apply x.1

/-- **An isomorphism from a pullback along a point embedding** `g : P ↪ Q` is one from the
template itself, along the composite point map, when every cell is visible through `g` and the
underlying set and the plan lie in the range of `g`. -/
theorem IsIsoRenamingAlong.of_comap {ι P Q : Type*} {α : Ordinal.{u}} {n : ℕ} {j : Fin n ↪ P}
    {g : P ↪ Q} {D : CellScheme ι Q} {R : D.Rows.{u}} {p : ι → Label.{u}} {t : StageType.{u} α n}
    {e : D.visible (Set.range g) ≃ Fin t.card} (hvis : ∀ d, d ∈ D.visible (Set.range g))
    (hground : (D.ground : Set Q) ⊆ Set.range g)
    (hfaces : ∀ B ∈ D.faces, (B : Set Q) ⊆ Set.range g)
    (h : IsIsoRenamingAlong j (D.comap g) (R.comap (CellScheme.IsLowerEmbedding.comap D g))
      (p ∘ (↑)) t e) :
    IsIsoRenamingAlong (j.trans g) D R p t ((Equiv.subtypeUnivEquiv hvis).symm.trans e) where
  ground_eq := by
    rw [← Finset.map_map, ← h.ground_eq, CellScheme.comap_ground,
      Finset.map_preimage_eq_of_subset_range hground]
  faces_eq := by
    ext B
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
    constructor
    · intro hB
      have hB' : B.preimage g g.injective.injOn ∈ (D.comap g).faces := by
        rw [CellScheme.mem_comap_faces, Finset.map_preimage_eq_of_subset_range (hfaces B hB)]
        exact hB
      rw [h.faces_eq, Finset.mem_map] at hB'
      obtain ⟨C, hC, hCB⟩ := hB'
      refine ⟨C, hC, ?_⟩
      rw [← Finset.map_map, ← Finset.map_preimage_eq_of_subset_range (hfaces B hB)]
      exact congrArg (Finset.map g) hCB
    · rintro ⟨C, hC, rfl⟩
      have hC' : C.map j ∈ (D.comap g).faces := by
        rw [h.faces_eq]
        exact Finset.mem_map_of_mem _ hC
      rw [CellScheme.mem_comap_faces, Finset.map_map] at hC'
      exact hC'
  scope_eq d := by
    rw [Equiv.trans_apply, ← Finset.map_map, h.scope_eq]
    exact CellScheme.map_comap_scope D g _
  grade_eq d := h.grade_eq _
  label_eq d := h.label_eq _
  row_eq d x y hy := by
    have hx : (⟨x.1, hvis x.1⟩ : D.visible (Set.range g)) ∈
        (D.comap g).below ((D.comap g).gradedIndex ((Equiv.subtypeUnivEquiv hvis).symm d)) :=
      (CellScheme.gradedIndex_comap_le_iff D g _).mpr (by
        rw [show Prod.map (Finset.map g) id ((D.comap g).gradedIndex
            ((Equiv.subtypeUnivEquiv hvis).symm d)) = D.gradedIndex d from
          Prod.ext (CellScheme.map_comap_scope D g _) rfl]
        exact x.2)
    exact h.row_eq _ ⟨_, hx⟩ y hy

/-! ### Arbitrary finite carriers -/

/-- **The second bullet of [AFK26, Proposition 4.30] on `Fintype` carriers**: every legal template
with finitely many cells on all of a finite type of points `P`, with an explicit `i : P ≃ Fin n`,
is isomorphic along `i` to a renaming of a chosen legal template.  The arity is positive by the
nonemptiness clause of the plan ([AFK26, Definition 4.1]). -/
theorem fintypeCarrierClause_chosenLegalTemplates :
    FintypeCarrierClause.{u, w} chosenLegalTemplates.{u} := by
  intro P _ _ n i ι _ D R p hground hplan hL
  have hω : Order.IsSuccPrelimit ω₁ := (Cardinal.isSuccLimit_omega 1).isSuccPrelimit
  have hω2 : ω ^ 2 ≤ ω₁ := Label.omega0_sq_lt_omega_one.le
  set j : Fin n ↪ P := i.symm.toEmbedding
  have hrange : ∀ s : Set P, s ⊆ Set.range j := fun _ x _ ↦ ⟨i x, i.symm_apply_apply x⟩
  have hvis : ∀ d, d ∈ D.visible (Set.range j) := fun _ ↦ hrange _
  have hPl := (Geometry.isTemplatePlan_iff.mp hplan).1
  have hD : D.IsWellFormed := ⟨inferInstance, hPl, fun d ↦ by
    rw [← hL.range_gradedIndex]
    exact ⟨d, rfl⟩⟩
  have hfg : (D.ground.preimage j j.injective.injOn).map j ∈ D.faces := by
    rw [Finset.map_preimage_eq_of_subset_range (hrange _)]
    exact hPl.ground_mem
  have hground₁ : (D.comap j).ground = Finset.univ := by
    ext x
    simp [hground]
  have hn : 0 < n := by
    obtain ⟨x, -⟩ := hplan.nonempty
    exact (i x).pos
  have hplan₁ : Geometry.IsTemplatePlan (D.comap j).ground (D.comap j).faces :=
    Geometry.isTemplatePlan_iff.mpr ⟨(hD.comap j hfg).isPlan, by
      rw [hground₁]
      exact univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩⟩
  have hL₁ := hL.comap hω hω2 j
  let e₁ := (Finite.equivFin (D.visible (Set.range j))).symm
  let s := CellScheme.Rows.toStageTypeOfLegal hω hω2 e₁ hground₁ hplan₁ hL₁
  have hs : s.IsLegalTemplate ω₁ :=
    CellScheme.Rows.isLegalTemplate_toStageTypeOfLegal hω hω2 e₁ hground₁ hplan₁ hL₁
  have hb : IsIsoRenamingAlong (Function.Embedding.refl _) (D.comap j)
      (R.comap (CellScheme.IsLowerEmbedding.comap D j)) (p ∘ (↑)) s e₁.symm :=
    isIsoRenamingAlong_toStageType e₁ hground₁ _ _ _
  have h₀ := hb.of_comap hvis (hrange _) (fun _ _ ↦ hrange _)
  rw [Function.Embedding.refl_trans] at h₀
  obtain ⟨k, σ, hσ⟩ :=
    StageType.toClass_eq_toClass_iff.mp (toClass_chosenTemplateRepresentative s.toClass).symm
  exact ⟨s.renameCells σ, ⟨hn, ⟨s.toClass,
    (TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate le_rfl s).mpr hs⟩, hσ.symm⟩,
    _, h₀.renameCells σ⟩

/-- **The second bullet of [AFK26, Proposition 4.30] for the printed collection `T`**: every legal
template whose underlying set `A` and cells are finite subsets of `ℕ`, with an explicit
`i : A ≃ Fin n`, is isomorphic along `i` to a renaming of a chosen legal template.  From the
`Fintype` form (`fintypeCarrierClause_chosenLegalTemplates`) for the points of `A`, after pulling
the template back along the inclusion of `A` into `ℕ`. -/
theorem finsetNatCarrierClause_chosenLegalTemplates :
    FinsetNatCarrierClause.{u} chosenLegalTemplates.{u} := by
  intro A C n i D R p hground hplan hL
  have hω : Order.IsSuccPrelimit ω₁ := (Cardinal.isSuccLimit_omega 1).isSuccPrelimit
  have hω2 : ω ^ 2 ≤ ω₁ := Label.omega0_sq_lt_omega_one.le
  set g : A ↪ ℕ := Function.Embedding.subtype _
  have hrange : ∀ s : Finset ℕ, s ⊆ A → (s : Set ℕ) ⊆ Set.range g :=
    fun _ hs x hx ↦ ⟨⟨x, hs hx⟩, rfl⟩
  have hPl := (Geometry.isTemplatePlan_iff.mp hplan).1
  have hfaces : ∀ B ∈ D.faces, B ⊆ A := fun B hB ↦ hground ▸ hPl.subset_of_mem hB
  have hframe : ∀ d, D.gradedIndex d ∈ D.gradedFaces := fun d ↦ by
    rw [← hL.range_gradedIndex]
    exact ⟨d, rfl⟩
  have hvis : ∀ d, d ∈ D.visible (Set.range g) := fun d ↦ hrange _ (hfaces _ (hframe d).1)
  have hD : D.IsWellFormed := ⟨inferInstance, hPl, hframe⟩
  have hfg : (D.ground.preimage g g.injective.injOn).map g ∈ D.faces := by
    rw [Finset.map_preimage_eq_of_subset_range (hrange _ hground.le)]
    exact hPl.ground_mem
  have hground₁ : (D.comap g).ground = Finset.univ := by
    ext x
    simp [hground, g]
  have hplan₁ : Geometry.IsTemplatePlan (D.comap g).ground (D.comap g).faces :=
    Geometry.isTemplatePlan_iff.mpr ⟨(hD.comap g hfg).isPlan, by
      obtain ⟨a, ha⟩ := hplan.nonempty
      rw [hground₁]
      exact ⟨⟨a, hground ▸ ha⟩, mem_univ _⟩⟩
  obtain ⟨t, ht, e, he⟩ := fintypeCarrierClause_chosenLegalTemplates.{u, 0} A n i (D.comap g)
    (R.comap (CellScheme.IsLowerEmbedding.comap D g)) (p ∘ (↑)) hground₁ hplan₁
    (hL.comap hω hω2 g)
  exact ⟨t, ht, _, he.of_comap hvis (hrange _ hground.le) fun B hB ↦ hrange _ (hfaces B hB)⟩

/-! ### The full-carrier forms of Proposition 4.30 -/

/-- **[AFK26, Proposition 4.30], with legal templates on arbitrary finite carriers**: the
positional statement `proposition430Target`, and every legal template on a finite type of points
is isomorphic to a renaming of a chosen legal template. -/
theorem proposition430FintypeTarget : Proposition430FintypeTarget.{u, w} :=
  ⟨proposition430Target, fintypeCarrierClause_chosenLegalTemplates⟩

/-- **[AFK26, Proposition 4.30] for templates on finite subsets of `ℕ`**: the positional statement
`proposition430Target`, and every legal template whose underlying set and cells are finite subsets
of `ℕ` is isomorphic to a renaming of a chosen legal template. -/
theorem proposition430FinsetNatTarget : Proposition430FinsetNatTarget.{u} :=
  ⟨proposition430Target, finsetNatCarrierClause_chosenLegalTemplates⟩

end VaughtConjecture
