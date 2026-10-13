/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Charts.LegalTemplate
import VaughtConjecture.Correspondence.Charts.Plan

/-!
# Templates of [AFK26], cell renaming, and positional stage types

Numbering as in the draft of [AFK26] dated 10 October 2026.

**Templates.**  [AFK26, Definitions 4.1–4.5]: a template `t = (c, Σ, p)` over a plan `(A, P)` is a
frame `c : D → GradedFace[P]`, a row system `Σ = (ℓ_d)_{d ∈ D}` with
`range(ℓ_d) ⊆ {-∞} ∪ ω ^ 2`, and a label `p : D → {-∞} ∪ ω₁ ∪ {∞}`.  Here the cells form an
arbitrary type `ι`; the frame is a cell scheme `D : CellScheme ι α` (ground set `A`, faces `P`,
graded index `c`), the row system is `R : D.Rows` (`ℓ_d = R.row d`, a local label on `D↓d`), and
the label is `p : ι → Label`.  `CellScheme.Rows.IsTemplate θ R p` states the laws, with labels at
stage `θ` ([AFK26] takes `θ = ω₁`); the plan is that of [AFK26, Definition 4.1]
(`Geometry.IsTemplatePlan`).  `CellScheme.Rows.IsLegalTemplate θ R p` states the five clauses of
[AFK26, Definition 4.29] for such data, as `StageType.IsLegalTemplate` does for stage types
(`StageType.isLegalTemplate_iff_rows`).  For finitely many cells, at a stage `θ ≥ ω ^ 2` that is
zero or a limit, the clauses are the native conditions (`CellScheme.Rows.isLegalTemplate_iff`).

**Cell renaming** [AFK26, Definition 4.6].  For a bijection `ι : D₀ → D₁` the renaming of
`(c, Σ, p)` is `(c ∘ ι, (ℓ_{ι(d)} ∘ ι↾(D₀↓d))_{d ∈ D₀}, p ∘ ι)`.  Here the renaming along
`e : κ ≃ ι` is `(D.reindex e, R.comap (IsLowerEmbedding.reindex D e), p ∘ e)`: the frame is
`gradedIndex ∘ e` (`CellScheme.gradedIndex_reindex`), the row of a cell `s` at `t` is the row of
`e s` at `e t` (`CellScheme.Rows.comap_row`), and the label is `p ∘ e`.  The points, the plan, and
the set of graded faces carrying a cell are unchanged.  Being a template and being a legal template
are invariant under renaming (`CellScheme.Rows.isTemplate_comap_reindex_iff`,
`CellScheme.Rows.isLegalTemplate_comap_reindex_iff`), the statement "legality is preserved by cell
renaming" used in the proof of [AFK26, Proposition 4.30].

**Positional stage types.**  A stage type has cells `Fin card`, numbered.  The renaming of its
cells along `σ : Fin k ≃ Fin t.card` is the stage type `StageType.renameCells t σ`, the generic
renaming above; `StageType.IsCellRenaming t t'` (`t'` is a renaming of `t`) is an equivalence
relation (`StageType.cellRenamingSetoid`).  Renaming keeps the points, the plan
(`renameCells_faces`), the graded faces carrying a cell (`range_gradedIndex_renameCells`), the
labels up to the bijection (`renameCells_label`), the rows read through the bijection
(`renameCells_row`), legality, strong coding, and the legal templates
(`isLegal_renameCells_iff`, `isStronglyCoded_renameCells_iff`,
`isLegalTemplate_renameCells_iff`), and it commutes with stage reduction
(`reduce_renameCells`).

**From a template to a positional stage type.**  A template with finitely many cells on the
points `Fin n` (ground set all of `Fin n`), whose label is lawful and at stage `α`, gives for
every numbering `e : Fin k ≃ ι` of its cells the stage type
`CellScheme.Rows.toStageType R p e …`: the renaming of the template along `e`.  It is a legal
template exactly when the template is (`CellScheme.Rows.isLegalTemplate_toStageType_iff`); two
numberings give stage types that are cell renamings of each other
(`CellScheme.Rows.isCellRenaming_toStageType`).  Conversely the data of a stage type on a
nonempty set of points form a template (`StageType.isTemplate`), and numbering its own cells by
the identity gives it back (`StageType.toStageType_refl`).  So a printed template up to cell
renaming is a stage type up to `StageType.IsCellRenaming`; the points are never renamed.

**Not stated here.**  The face maps of renamed stage types (the induced bijection of the cells
of a closed face) and the charts of [AFK26, Definition 4.31].
-/

universe u

namespace VaughtConjecture

open Finset Label Ordinal CellScheme

/-! ### Templates and legal templates over a cell scheme -/

namespace CellScheme.Rows

variable {ι κ α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) {θ : Ordinal.{u}}

/-- **Templates** [AFK26, Definitions 4.1–4.5], with labels at stage `θ`: the faces of `D` form a
plan on its ground set, the graded index of each cell is a graded face (the frame), each row takes
values in `{-∞} ∪ ω ^ 2` (the row system), and the label takes values in `{-∞} ∪ θ ∪ {∞}`. -/
structure IsTemplate [DecidableEq α] (θ : Ordinal.{u}) (p : ι → Label.{u}) : Prop where
  /-- [AFK26, Definition 4.1]: `P` is a plan on `A`. -/
  plan : Geometry.IsTemplatePlan D.ground D.faces
  /-- [AFK26, Definition 4.3]: `c : D → GradedFace[P]`. -/
  frame : ∀ d, D.gradedIndex d ∈ D.gradedFaces
  /-- [AFK26, Definition 4.4]: `range(ℓ_d) ⊆ {-∞} ∪ ω ^ 2` (`⊥` and the ordinals below
  `ω ^ 2`). -/
  rowSystem : ∀ d e, R.row d e < ((ω ^ 2 : Ordinal.{u}) : Label.{u})
  /-- [AFK26, Definition 4.4]: `p : D → {-∞} ∪ θ ∪ {∞}`. -/
  label_atStage : ∀ d, AtStage θ (p d)

/-- **Legal templates** [AFK26, Definition 4.29] for a frame `D`, rows `R` and label `p`, with
labels at stage `θ`: the clauses of `StageType.IsLegalTemplate`. -/
structure IsLegalTemplate (θ : Ordinal.{u}) (p : ι → Label.{u}) : Prop where
  /-- [AFK26, Definition 4.4]: the label takes values in `{-∞} ∪ θ ∪ {∞}`. -/
  label_atStage : ∀ d, AtStage θ (p d)
  /-- Clause 1: `range(c) = GradedFace[P]`. -/
  range_gradedIndex : Set.range D.gradedIndex = D.gradedFaces
  /-- Clause 2: `p` is lawful with respect to `Σ`. -/
  lawful : R.TemplateLawful θ p
  /-- Clause 3: for each `d ∈ D`, `ℓ_d` is lawful. -/
  row_lawful : ∀ d, R.TemplateLawfulLocal θ (D.gradedIndex d) (R.row d)
  /-- Clause 4: the rows are bountiful. -/
  bountiful : R.TemplateBountiful θ
  /-- Clause 5: `range(ℓ_d) ⊆ {-∞} ∪ {ω · n + i : n ∈ ω, i ≤ g(d) + 1}`. -/
  row_range : ∀ d (e : D.below (D.gradedIndex d)), R.row d e = ⊥ ∨
    ∃ m i : ℕ, i ≤ D.grade d + 1 ∧ R.row d e = ((ω * m + i : Ordinal.{u}) : Label.{u})

variable {R}

/-- Strongly coded rows take values at every stage at least `ω ^ 2`. -/
theorem IsStronglyCoded.atStage (h : R.IsStronglyCoded) (hθ2 : ω ^ 2 ≤ θ) (s : ι)
    (t : D.below (D.gradedIndex s)) : AtStage θ (R.row s t) :=
  .inl (((h s).lt_omega0_sq t).trans_le (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hθ2)))

/-- **Legal templates are the native legal data**: for finitely many cells, at a stage
`θ ≥ ω ^ 2` that is zero or a limit, the clauses of [AFK26, Definition 4.29] are: labels at stage
`θ`, every cell on a graded face and every graded face carrying a cell, a lawful label,
consistent, bountiful and strongly coded rows. -/
theorem isLegalTemplate_iff [Finite ι] (hθ : Order.IsSuccPrelimit θ) (hθ2 : ω ^ 2 ≤ θ)
    {p : ι → Label.{u}} :
    R.IsLegalTemplate θ p ↔ (∀ d, AtStage θ (p d)) ∧ (∀ d, D.gradedIndex d ∈ D.gradedFaces) ∧
      D.IsComplete ∧ R.IsLawful p ∧ R.IsConsistent ∧ R.IsBountiful ∧ R.IsStronglyCoded := by
  constructor
  · intro h
    have hs : R.IsStronglyCoded := fun s e ↦ h.row_range s e
    have hR := hs.atStage hθ2
    refine ⟨h.label_atStage, fun d ↦ ?_, fun X hX ↦ ?_,
      (templateLawful_iff hθ hR h.label_atStage).mp h.lawful,
      fun d ↦ (templateLawfulLocal_iff hθ hR (hR d)).mp (h.row_lawful d),
      h.bountiful.isBountiful hθ hθ2 hR, hs⟩
    · rw [← h.range_gradedIndex]
      exact ⟨d, rfl⟩
    · rw [← h.range_gradedIndex] at hX
      exact hX
  · rintro ⟨hθl, hf, hc, hl, hcons, hb, hs⟩
    have hR := hs.atStage hθ2
    exact { label_atStage := hθl
            range_gradedIndex := Set.Subset.antisymm (Set.range_subset_iff.mpr hf) hc
            lawful := (templateLawful_iff hθ hR hθl).mpr hl
            row_lawful := fun d ↦ (templateLawfulLocal_iff hθ hR (hR d)).mpr (hcons d)
            bountiful := hb.templateBountiful hθ hR
            row_range := hs }

/-! ### Renaming of cells -/

section Renaming

variable (e : κ ≃ ι) {p : ι → Label.{u}}

/-- The renamed rows pulled back along the inverse bijection are the original rows. -/
private theorem comap_reindex_symm :
    (R.comap (IsLowerEmbedding.reindex D e)).comap (IsLowerEmbedding.reindex D e).symm = R :=
  comap_comap_symm R _

/-- Renaming does not change the graded faces. -/
private theorem gradedFaces_reindex : (D.reindex e).gradedFaces = D.gradedFaces := rfl

/-- **Templates are invariant under renaming** [AFK26, Definition 4.6]. -/
theorem isTemplate_comap_reindex_iff [DecidableEq α] :
    (R.comap (IsLowerEmbedding.reindex D e)).IsTemplate θ (p ∘ e) ↔ R.IsTemplate θ p := by
  constructor
  · intro h
    have hc : (R.comap (IsLowerEmbedding.reindex D e)).IsCoded := h.rowSystem
    have hc' := hc.comap (IsLowerEmbedding.reindex D e).symm
    rw [comap_reindex_symm] at hc'
    exact ⟨h.plan, fun d ↦ by simpa using h.frame (e.symm d), hc',
      fun d ↦ by simpa using h.label_atStage (e.symm d)⟩
  · intro h
    exact ⟨h.plan, fun d ↦ h.frame (e d),
      (show R.IsCoded from h.rowSystem).comap (IsLowerEmbedding.reindex D e),
      fun d ↦ h.label_atStage (e d)⟩

/-- Completeness is invariant under renaming. -/
theorem isComplete_reindex_iff : (D.reindex e).IsComplete ↔ D.IsComplete :=
  ⟨fun h X hX ↦ let ⟨k, hk⟩ := h X hX; ⟨e k, hk⟩, fun h ↦ h.reindex e.surjective⟩

/-- Consistency is invariant under renaming. -/
theorem isConsistent_comap_reindex_iff :
    (R.comap (IsLowerEmbedding.reindex D e)).IsConsistent ↔ R.IsConsistent := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comap _⟩
  have h' := h.comap (IsLowerEmbedding.reindex D e).symm
  rwa [comap_reindex_symm] at h'

/-- Bountifulness is invariant under renaming. -/
theorem isBountiful_comap_reindex_iff :
    (R.comap (IsLowerEmbedding.reindex D e)).IsBountiful ↔ R.IsBountiful := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reindex e⟩
  have h' := h.comap_of_image_eq (IsLowerEmbedding.reindex D e).symm (g := id)
    (monotone_id.monotoneOn _) (fun _ hX ↦ hX) fun X _ ↦ by
      ext d
      constructor
      · rintro ⟨x, hx, rfl⟩
        change D.gradedIndex (e (e.symm x)) ≤ X
        rw [e.apply_symm_apply]
        exact hx
      · intro hd
        exact ⟨e d, hd, e.symm_apply_apply d⟩
  rwa [comap_reindex_symm] at h'

/-- Strong coding is invariant under renaming. -/
theorem isStronglyCoded_comap_reindex_iff :
    (R.comap (IsLowerEmbedding.reindex D e)).IsStronglyCoded ↔ R.IsStronglyCoded := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comap _⟩
  have h' := h.comap (IsLowerEmbedding.reindex D e).symm
  rwa [comap_reindex_symm] at h'

/-- **Legal templates are invariant under renaming** [AFK26, Definition 4.6]: for finitely many
cells, at a stage `θ ≥ ω ^ 2` that is zero or a limit. -/
theorem isLegalTemplate_comap_reindex_iff [Finite ι] (hθ : Order.IsSuccPrelimit θ)
    (hθ2 : ω ^ 2 ≤ θ) :
    (R.comap (IsLowerEmbedding.reindex D e)).IsLegalTemplate θ (p ∘ e) ↔
      R.IsLegalTemplate θ p := by
  have : Finite κ := Finite.of_equiv _ e.symm
  rw [isLegalTemplate_iff hθ hθ2, isLegalTemplate_iff hθ hθ2, isComplete_reindex_iff,
    isLawful_comap_equiv_iff, isConsistent_comap_reindex_iff, isBountiful_comap_reindex_iff,
    isStronglyCoded_comap_reindex_iff]
  refine and_congr ⟨fun h d ↦ by simpa using h (e.symm d), fun h k ↦ h (e k)⟩
    (and_congr ⟨fun h d ↦ by simpa using h (e.symm d), fun h k ↦ h (e k)⟩ Iff.rfl)

end Renaming

end CellScheme.Rows

/-! ### Renaming the cells of a stage type -/

namespace StageType

open CellScheme.Rows

variable {α θ : Ordinal.{u}} {n k m : ℕ}

/-- The data of a stage type satisfy the clauses of [AFK26, Definition 4.29] exactly when the
stage type does: the two structures have the same fields. -/
theorem isLegalTemplate_iff_rows {t : StageType.{u} α n} :
    t.IsLegalTemplate θ ↔ t.rows.IsLegalTemplate θ t.label :=
  ⟨fun h ↦ ⟨h.label_atStage, h.range_gradedIndex, h.lawful, h.row_lawful, h.bountiful,
      h.row_range⟩,
    fun h ↦ ⟨h.label_atStage, h.range_gradedIndex, h.lawful, h.row_lawful, h.bountiful,
      h.row_range⟩⟩

/-- **The renaming of the cells of a stage type** along `σ : Fin k ≃ Fin t.card`
[AFK26, Definition 4.6]: the cell `i` has the graded index, the row (read through `σ`), and the
label of the cell `σ i`.  The points and the plan are unchanged. -/
def renameCells (t : StageType.{u} α n) (σ : Fin k ≃ Fin t.card) : StageType.{u} α n where
  card := k
  toCellScheme := t.toCellScheme.reindex σ
  rows := t.rows.comap (IsLowerEmbedding.reindex _ σ)
  label := t.label ∘ σ
  isWellFormed := ⟨t.isWellFormed.ground_eq, t.isWellFormed.isWellFormed.reindex σ⟩
  isCoded _ _ := t.isCoded _ _
  isLawful := t.isLawful.comap _
  atStage _ := t.atStage _

variable (t : StageType.{u} α n) (σ : Fin k ≃ Fin t.card)

@[simp] theorem renameCells_card : (t.renameCells σ).card = k := rfl

/-- The graded index of a renamed cell is that of its image. -/
@[simp] theorem renameCells_gradedIndex (i : Fin k) :
    (t.renameCells σ).toCellScheme.gradedIndex i = t.toCellScheme.gradedIndex (σ i) := rfl

/-- The faces (the plan) are unchanged by renaming. -/
@[simp] theorem renameCells_faces : (t.renameCells σ).toCellScheme.faces = t.toCellScheme.faces :=
  rfl

/-- The ground set is unchanged by renaming. -/
@[simp] theorem renameCells_ground :
    (t.renameCells σ).toCellScheme.ground = t.toCellScheme.ground := rfl

/-- The label of a renamed cell is that of its image. -/
@[simp] theorem renameCells_label (i : Fin k) : (t.renameCells σ).label i = t.label (σ i) := rfl

/-- The row of a renamed cell is the row of its image, read through the bijection. -/
@[simp] theorem renameCells_row (s : Fin k)
    (e : (t.renameCells σ).toCellScheme.below ((t.renameCells σ).toCellScheme.gradedIndex s)) :
    (t.renameCells σ).rows.row s e =
      t.rows.row (σ s)
        ⟨σ e.1, (IsLowerEmbedding.reindex t.toCellScheme σ |>.le_iff e.1 s).mpr e.2⟩ :=
  rfl

/-- The graded faces carrying a cell are unchanged by renaming. -/
theorem range_gradedIndex_renameCells :
    Set.range (t.renameCells σ).toCellScheme.gradedIndex =
      Set.range t.toCellScheme.gradedIndex :=
  Set.ext fun _ ↦ ⟨fun ⟨i, hi⟩ ↦ ⟨σ i, hi⟩, fun ⟨d, hd⟩ ↦ ⟨σ.symm d, by
    rw [renameCells_gradedIndex, σ.apply_symm_apply]
    exact hd⟩⟩

/-- The labels that occur are unchanged by renaming. -/
theorem range_label_renameCells : Set.range (t.renameCells σ).label = Set.range t.label :=
  Set.ext fun _ ↦ ⟨fun ⟨i, hi⟩ ↦ ⟨σ i, hi⟩, fun ⟨d, hd⟩ ↦ ⟨σ.symm d, by
    rw [renameCells_label, σ.apply_symm_apply]
    exact hd⟩⟩

/-- Renaming along the identity changes nothing. -/
@[simp] theorem renameCells_refl : t.renameCells (Equiv.refl _) = t := rfl

/-- Two renamings are one renaming. -/
@[simp] theorem renameCells_renameCells (τ : Fin m ≃ Fin k) :
    (t.renameCells σ).renameCells τ = t.renameCells (τ.trans σ) := rfl

/-- Renaming commutes with stage reduction. -/
theorem reduce_renameCells {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) :
    (t.renameCells σ).reduce hβ = (t.reduce hβ).renameCells σ := rfl

/-- Legality is invariant under renaming. -/
theorem isLegal_renameCells_iff : (t.renameCells σ).IsLegal ↔ t.IsLegal := by
  rw [isLegal_iff, isLegal_iff]
  exact and_congr (isConsistent_comap_reindex_iff σ)
    (and_congr (isBountiful_comap_reindex_iff σ) (isComplete_reindex_iff σ))

/-- Strong coding is invariant under renaming. -/
theorem isStronglyCoded_renameCells_iff :
    (t.renameCells σ).rows.IsStronglyCoded ↔ t.rows.IsStronglyCoded :=
  isStronglyCoded_comap_reindex_iff σ

/-- Strongly coded legality is invariant under renaming. -/
theorem isStronglyCodedLegal_renameCells_iff :
    (t.renameCells σ).IsStronglyCodedLegal ↔ t.IsStronglyCodedLegal :=
  and_congr (t.isLegal_renameCells_iff σ) (t.isStronglyCoded_renameCells_iff σ)

/-- **Legal templates are invariant under renaming**: at a stage `θ ≥ ω ^ 2` that is zero or a
limit. -/
theorem isLegalTemplate_renameCells_iff (hθ : Order.IsSuccPrelimit θ) (hθ2 : ω ^ 2 ≤ θ) :
    (t.renameCells σ).IsLegalTemplate θ ↔ t.IsLegalTemplate θ := by
  rw [isLegalTemplate_iff_rows, isLegalTemplate_iff_rows]
  exact isLegalTemplate_comap_reindex_iff σ hθ hθ2

/-- **Cell renaming of stage types** [AFK26, Definition 4.6]: `t'` is a renaming of `t`, along
some bijection of cells. -/
def IsCellRenaming (t t' : StageType.{u} α n) : Prop :=
  ∃ (k : ℕ) (σ : Fin k ≃ Fin t.card), t.renameCells σ = t'

/-- Cell renaming is reflexive. -/
theorem IsCellRenaming.refl (t : StageType.{u} α n) : t.IsCellRenaming t :=
  ⟨_, Equiv.refl _, rfl⟩

/-- Cell renaming is symmetric. -/
theorem IsCellRenaming.symm {t t' : StageType.{u} α n} (h : t.IsCellRenaming t') :
    t'.IsCellRenaming t := by
  obtain ⟨k, σ, rfl⟩ := h
  exact ⟨_, σ.symm, by rw [renameCells_renameCells, Equiv.symm_trans_self, renameCells_refl]⟩

/-- Cell renaming is transitive. -/
theorem IsCellRenaming.trans {t t' t'' : StageType.{u} α n} (h : t.IsCellRenaming t')
    (h' : t'.IsCellRenaming t'') : t.IsCellRenaming t'' := by
  obtain ⟨k, σ, rfl⟩ := h
  obtain ⟨m, τ, rfl⟩ := h'
  exact ⟨m, τ.trans σ, rfl⟩

variable (α n) in
/-- Cell renaming as a setoid on the stage types at stage `α` on `n` points. -/
def cellRenamingSetoid : Setoid (StageType.{u} α n) where
  r := IsCellRenaming
  iseqv := ⟨IsCellRenaming.refl, IsCellRenaming.symm, IsCellRenaming.trans⟩

/-- Renamings have the same number of cells. -/
theorem IsCellRenaming.card_eq {t t' : StageType.{u} α n} (h : t.IsCellRenaming t') :
    t'.card = t.card := by
  obtain ⟨k, σ, rfl⟩ := h
  simpa using Fintype.card_congr σ

end StageType

/-! ### From a template to a positional stage type -/

namespace CellScheme.Rows

variable {ι : Type*} {n k : ℕ} {D : CellScheme ι (Fin n)} (R : D.Rows.{u}) (p : ι → Label.{u})
  {α θ : Ordinal.{u}}

/-- **The positional stage type of a template**, for a numbering `e : Fin k ≃ ι` of its cells: the
renaming of the template along `e` [AFK26, Definition 4.6].  It needs the ground set to be all of
`Fin n`, the template laws, a lawful label, and labels at stage `α`. -/
def toStageType (e : Fin k ≃ ι) (hground : D.ground = Finset.univ) (hT : R.IsTemplate θ p)
    (hl : R.IsLawful p) (hα : ∀ d, AtStage α (p d)) : StageType.{u} α n where
  card := k
  toCellScheme := D.reindex e
  rows := R.comap (IsLowerEmbedding.reindex D e)
  label := p ∘ e
  isWellFormed := ⟨hground, ⟨inferInstance, (Geometry.isTemplatePlan_iff.mp hT.plan).1,
    fun d ↦ hT.frame (e d)⟩⟩
  isCoded _ _ := hT.rowSystem _ _
  isLawful := hl.comap _
  atStage _ := hα _

variable {R p}

/-- **The positional stage type of a template is a legal template exactly when the template is**
[AFK26, Definition 4.29], at a stage `θ ≥ ω ^ 2` that is zero or a limit. -/
theorem isLegalTemplate_toStageType_iff (hθ : Order.IsSuccPrelimit θ) (hθ2 : ω ^ 2 ≤ θ)
    (e : Fin k ≃ ι) (hground : D.ground = Finset.univ) (hT : R.IsTemplate θ p) (hl : R.IsLawful p)
    (hα : ∀ d, AtStage α (p d)) :
    (R.toStageType p e hground hT hl hα).IsLegalTemplate θ ↔ R.IsLegalTemplate θ p := by
  have : Finite ι := Finite.of_equiv _ e
  exact StageType.isLegalTemplate_iff_rows.trans (isLegalTemplate_comap_reindex_iff e hθ hθ2)

/-- **Two numberings of the cells of a template give stage types that are cell renamings of each
other.** -/
theorem isCellRenaming_toStageType (e e' : Fin k ≃ ι) (hground : D.ground = Finset.univ)
    (hT : R.IsTemplate θ p) (hl : R.IsLawful p) (hα : ∀ d, AtStage α (p d)) :
    (R.toStageType p e hground hT hl hα).IsCellRenaming
      (R.toStageType p e' hground hT hl hα) := by
  refine ⟨k, e'.trans e.symm, StageType.ext (Scheme.ext rfl rfl rfl ?_ ?_ ?_) ?_⟩
  · intro i j hij
    obtain rfl := Fin.ext hij
    change D.scope (e (e.symm (e' i))) = D.scope (e' i)
    rw [e.apply_symm_apply]
  · intro i j hij
    obtain rfl := Fin.ext hij
    change D.grade (e (e.symm (e' i))) = D.grade (e' i)
    rw [e.apply_symm_apply]
  · intro s s' t t' hs ht
    obtain rfl := Fin.ext hs
    change R.row (e (e.symm (e' s))) ⟨e (e.symm (e' t.1)), _⟩ = R.row (e' s) ⟨e' t'.1, _⟩
    exact R.row_congr (e.apply_symm_apply _) (by
      change e (e.symm (e' t.1)) = e' t'.1
      rw [e.apply_symm_apply, Fin.ext ht])
  · intro i j hij
    obtain rfl := Fin.ext hij
    change p (e (e.symm (e' i))) = p (e' i)
    rw [e.apply_symm_apply]

end CellScheme.Rows

namespace StageType

open CellScheme.Rows

variable {α θ : Ordinal.{u}} {n : ℕ}

/-- **The data of a stage type form a template** [AFK26, Definitions 4.1–4.5] when it has at
least one point and its labels lie at stage `θ`. -/
theorem isTemplate (t : StageType.{u} α n) (hn : 0 < n) (hθ : ∀ d, AtStage θ (t.label d)) :
    t.rows.IsTemplate θ t.label where
  plan := Geometry.isTemplatePlan_iff.mpr ⟨t.isWellFormed.isWellFormed.isPlan, by
    rw [t.isWellFormed.ground_eq]
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩⟩
  frame := t.isWellFormed.isWellFormed.gradedIndex_mem
  rowSystem := t.isCoded
  label_atStage := hθ

/-- **Numbering the cells of a stage type by the identity gives it back.** -/
theorem toStageType_refl (t : StageType.{u} α n) (hn : 0 < n)
    (hθ : ∀ d, AtStage θ (t.label d)) :
    t.rows.toStageType t.label (Equiv.refl _) t.isWellFormed.ground_eq (t.isTemplate hn hθ)
      t.isLawful t.atStage = t :=
  rfl

end StageType

end VaughtConjecture
