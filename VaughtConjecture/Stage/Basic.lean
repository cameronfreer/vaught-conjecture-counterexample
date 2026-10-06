/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Stage.Scheme

/-!
# Stage types, exact partial face maps, and stage reduction

Roadmap, Library conventions (a stage type owns its scheme and label section; face restriction,
stage reduction, and capped observation are different operations) and Layer 1 (countable stage
types and exact partial face maps, preserving undefined faces; stage-reduction coherence);
semantic contract, items 3–4 (a tuple's partial type is exact under face maps; absence of a face
is mathematical information); the expositions, §1.

A **stage type** `t : StageType α n` at stage `α` on `n` points is a scheme on `n` points
(`Scheme n`) together with a label section `t.label` of its cells, subject to the laws: the scheme
is well formed with coded rows, the section is lawful for the rows (`CellScheme.Rows.IsLawful`),
and every label occurs at stage `α` (`Label.AtStage α`: bottom, an ordinal below `α`, or the
formal top).

**Face maps.**  For an embedding `f : Fin m ↪ Fin n`, the face map
`restrictFace f : StageType α n → Option (StageType α m)` is defined exactly when the image of `f`
is a closed face of the type, and then returns the restriction `t.comap f hf` (the restricted
scheme of `Scheme.comap` with the labels of the visible cells); otherwise it is `none`, and this
`none` is part of the data of the type.  The laws are those of an exact partial chart system:

* `restrictFace_refl`: the identity face is defined and returns the type;
* `restrictFace_trans`: if `restrictFace f t = some u` then
  `restrictFace g u = restrictFace (g.trans f) t`, *including definedness*; nothing is claimed when
  the intermediate face is invisible, and indeed a subface of an invisible face may be visible
  (`VaughtConjecture.Stage.Examples`).
  A composite through an invisible face whose range is that whole face stays undefined
  (`restrictFace_trans_eq_none`).

The faces of a stage type form a plan on all of its points (`isPlan`), and the hull of a set in
a restriction is the preimage of the hull of its image (`hull_comap`).  The grades of the cells of
a stage type on `n` points are at most `n` (`grade_le`).

Reindexing along a bijection `e : Fin m ≃ Fin n` is total (`StageType.reindex`); it is the face
map along `e` (`restrictFace_equiv`) and commutes with all face maps (`restrictFace_reindex`,
`map_reindex_restrictFace`).

A cell of full grade `n` of a stage type on `n` points has full scope: its graded index is
`(univ, n)` (`gradedIndex_eq_univ_of_grade_eq`).

**Stage types on no points.**  A stage type on no points has no cells (`card_eq_zero`) and only
the empty face (`faces_eq_of_zero`), so there is exactly one at each stage (`eq_of_zero`); the
empty face of every stage type is closed (`isSome_restrictFace_of_zero`).  Likewise, the first
point of a stage type on two points spans a closed face, singletons being closed in a plan
(`exists_restrictFace_castSuccEmb_of_two`).

**Stage reduction.**  At a stage `β` that is zero or a limit (`Order.IsSuccPrelimit β`), the
reduction `t.reduce hβ : StageType β n` keeps the scheme and rows and applies `Label.reduce β`
to the section.  The reduced section is lawful (`CellScheme.Rows.IsLawful.reduce`, in
`VaughtConjecture.Scheme.Row`): the order and availability laws need only that reduction
preserves self-visibility and is monotone, while locality uses the reduction rule
`Label.TransformsTo.reduce` [Kni26, §3.1], which holds because stage reduction to a stage that is
zero or a limit commutes with visibility replacement.
At a successor stage `γ + 1` this fails: visibility replacement changes the finite part of an
ordinal label and can move a label below `γ + 1` to one at or above it, so reduction and the
transformation relation do not commute, and the reduction of a lawful section need not be lawful:
the section of a stage type at stage `3` on two points, with labels `1` and `2`, reduces at stage
`2` to a section that is not lawful (`VaughtConjecture.Stage.Examples`).  Stage types are
therefore reduced only to stages that are zero or limits, as in [Kni26, §3.1].  Reductions
compose (`reduce_reduce`), reduction to the stage of the type is the identity (`reduce_self`), and
reduction commutes with face maps (`restrictFace_reduce`) and reindexing (`reindex_reduce`).  In
particular, if `q` restricts along `f` to `p`, a stage type reducing to `q` restricts along `f` to
a stage type reducing to `p` (`exists_restrictFace_reduce_eq`).
Reduction to a stage at least the stage of the type changes no label (`reduce_label_of_le`) and
only relabels the stage: `t.reduce hβ = t.castLE hαβ` (`reduce_eq_castLE`), where `t.castLE hαβ`
reads a stage type at stage `α` as one at the larger stage `β`, with the same scheme and labels;
relabelling is invisible to reduction (`reduce_castLE`).

**Stage types from lawful sections.**  At a stage `α` that is zero or a limit, a well-formed
scheme with coded rows and a lawful section `ρ` give the stage type `ofIsLawful` with the
reduction of `ρ` as labels; if `ρ` extends the labels of `p` along a closed face, its face there
is `p` (`restrictFace_ofIsLawful`).  Stage reduction is `ofIsLawful` applied to the labels of a
type (`reduce_eq_ofIsLawful`).

## References

Stage types are [Kni26, Definition 3.1.1], stage reduction is [Kni26, Definition 3.1.2], and the
face maps are the horizontal restrictions of [Kni26, Definitions 3.1.2 and 3.1.5] (the
restriction to a face of the plan, and its transport along a one-to-one map).
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Stage types -/

/-- A **stage type** at stage `α` on `n` points [Kni26, §3.1]: a scheme on `n` points with a label
section of its cells; the scheme is well formed with coded rows, the section is lawful, and every
label occurs at stage `α`. -/
structure StageType (α : Ordinal.{u}) (n : ℕ) extends Scheme.{u} n where
  /-- The label of each cell. -/
  label : Fin card → Label.{u}
  /-- The scheme is well formed. -/
  isWellFormed : toScheme.IsWellFormed
  /-- The rows are coded. -/
  isCoded : toScheme.IsCoded
  /-- The label section is lawful for the rows. -/
  isLawful : rows.IsLawful label
  /-- Every label occurs at stage `α`. -/
  atStage (d : Fin card) : AtStage α (label d)

namespace StageType

variable {α β γ : Ordinal.{u}} {n m k : ℕ}

/-- **Extensionality** for stage types: equal schemes and equal labels at cells with equal
positions. -/
@[ext (iff := false)] theorem ext {t u : StageType.{u} α n} (h : t.toScheme = u.toScheme)
    (hl : ∀ (i : Fin t.card) (j : Fin u.card), (i : ℕ) = j → t.label i = u.label j) : t = u := by
  obtain ⟨S, p, _, _, _, _⟩ := t
  obtain ⟨S', p', _, _, _, _⟩ := u
  obtain rfl : S = S' := h
  obtain rfl : p = p' := funext fun i ↦ hl i i rfl
  rfl

/-- Equal stage types have equal labels at cells with equal positions. -/
theorem label_congr {t t' : StageType.{u} α n} (h : t = t') {i : Fin t.card} {j : Fin t'.card}
    (hij : (i : ℕ) = j) : t.label i = t'.label j := by
  subst h
  rw [Fin.ext hij]

/-- The whole ground set is a face of a stage type. -/
theorem univ_mem_faces (t : StageType.{u} α n) : (univ : Finset (Fin n)) ∈ t.toCellScheme.faces :=
  t.isWellFormed.univ_mem_faces

/-- The faces of a stage type form a plan on all of its points. -/
theorem isPlan (t : StageType.{u} α n) : Geometry.IsPlan univ t.toCellScheme.faces :=
  t.isWellFormed.isPlan

/-- The grades of the cells of a stage type on `n` points are at most `n`. -/
theorem grade_le (t : StageType.{u} α n) (d : Fin t.card) : t.toCellScheme.grade d ≤ n :=
  (t.isWellFormed.isWellFormed.grade_le_card d).trans ((card_le_univ _).trans_eq
    (Fintype.card_fin n))

/-! ### Restriction to a closed face -/

variable (t : StageType.{u} α n) (f : Fin m ↪ Fin n) (g : Fin k ↪ Fin m)

/-- The **restriction** of a stage type to the closed face spanned by `f`: the restricted scheme
and the labels of the visible cells. -/
noncomputable def comap (hf : univ.map f ∈ t.toCellScheme.faces) : StageType.{u} α m where
  toScheme := t.toScheme.comap f
  label i := t.label (t.cellMap f i)
  isWellFormed := t.isWellFormed.comap f hf
  isCoded := t.isCoded.comap f
  isLawful := t.isLawful.comap (t.isLowerEmbedding_comap f)
  atStage _ := t.atStage _

/-- The scheme of a restriction is the restricted scheme. -/
@[simp] theorem comap_toScheme (hf : univ.map f ∈ t.toCellScheme.faces) :
    (t.comap f hf).toScheme = t.toScheme.comap f := rfl

/-- The labels of a restriction are the labels of the visible cells. -/
@[simp] theorem comap_label (hf : univ.map f ∈ t.toCellScheme.faces)
    (i : Fin (t.comap f hf).card) : (t.comap f hf).label i = t.label (t.cellMap f i) := rfl

/-- Restriction along the identity is the identity. -/
@[simp] theorem comap_refl
    (hf : univ.map (Function.Embedding.refl (Fin n)) ∈ t.toCellScheme.faces) :
    t.comap (Function.Embedding.refl (Fin n)) hf = t := by
  refine ext (t.toScheme.comap_refl) fun i j h ↦ ?_
  simp only [comap_label]
  congr 1
  exact (t.cellMap_eq_of_strictMono _ strictMono_id (fun d ↦ by
    simp [Function.Embedding.coe_refl]) h.symm).symm

/-- A face spanned by `g` is closed in the restriction to the face spanned by `f` exactly when the
face spanned by the composite is closed in the type. -/
theorem map_univ_mem_comap_faces_iff (hf : univ.map f ∈ t.toCellScheme.faces) :
    univ.map g ∈ (t.comap f hf).toCellScheme.faces ↔
      univ.map (g.trans f) ∈ t.toCellScheme.faces := by
  simp [map_map]

/-- Two restrictions compose to the restriction along the composite. -/
@[simp] theorem comap_comap (hf : univ.map f ∈ t.toCellScheme.faces)
    (hg : univ.map g ∈ (t.comap f hf).toCellScheme.faces) :
    (t.comap f hf).comap g hg =
      t.comap (g.trans f) ((t.map_univ_mem_comap_faces_iff f g hf).mp hg) := by
  refine ext (t.toScheme.comap_comap f g) fun i j h ↦ ?_
  simp only [comap_label]
  congr 1
  exact t.cellMap_eq_of_strictMono _
    ((t.cellMap f).strictMono.comp ((t.toScheme.comap f).cellMap g).strictMono)
    (t.mem_range_cellMap_comp_iff f g) h

/-- **Hulls in a restriction.**  The hull of a set of points in the restriction of a stage type to
a closed face is the preimage of the hull of its image (`Geometry.hull_preimage`). -/
theorem hull_comap (hf : univ.map f ∈ t.toCellScheme.faces) (G : Finset (Fin m)) :
    Geometry.hull univ (t.comap f hf).toCellScheme.faces G =
      (Geometry.hull univ t.toCellScheme.faces (G.map f)).preimage f f.injective.injOn := by
  have hfaces : (t.comap f hf).toCellScheme.faces =
      t.toCellScheme.faces.preimage (Finset.map f) (map_injective f).injOn := by
    ext C
    simp
  rw [hfaces, ← Geometry.hull_preimage t.isPlan.infClosed (by rwa [preimage_univ]) (by simp),
    preimage_univ]

/-! ### Exact partial face maps -/

/-- The **face map** along `f : Fin m ↪ Fin n` [Kni26, §3.1]: the restriction of a
stage type to the face spanned by `f` when that face is closed, and `none` when it is not. -/
noncomputable def restrictFace (f : Fin m ↪ Fin n) (t : StageType.{u} α n) :
    Option (StageType.{u} α m) :=
  if hf : univ.map f ∈ t.toCellScheme.faces then some (t.comap f hf) else none

/-- The face map at a closed face is the restriction. -/
theorem restrictFace_of_mem (hf : univ.map f ∈ t.toCellScheme.faces) :
    restrictFace f t = some (t.comap f hf) := by
  simp [restrictFace, hf]

/-- The face map at a face that is not closed is undefined. -/
theorem restrictFace_of_notMem (hf : univ.map f ∉ t.toCellScheme.faces) :
    restrictFace f t = none := by
  simp [restrictFace, hf]

/-- The face map is defined exactly at the closed faces. -/
@[simp] theorem isSome_restrictFace_iff :
    (restrictFace f t).isSome ↔ univ.map f ∈ t.toCellScheme.faces := by
  by_cases hf : univ.map f ∈ t.toCellScheme.faces
  · simp [restrictFace_of_mem t f hf, hf]
  · simp [restrictFace_of_notMem t f hf, hf]

/-- The face map is undefined exactly at the faces that are not closed. -/
@[simp] theorem restrictFace_eq_none_iff :
    restrictFace f t = none ↔ univ.map f ∉ t.toCellScheme.faces := by
  rw [← isSome_restrictFace_iff, Option.not_isSome_iff_eq_none]

/-- The value of the face map, when defined, is the restriction. -/
theorem restrictFace_eq_some_iff {u : StageType.{u} α m} :
    restrictFace f t = some u ↔ ∃ hf : univ.map f ∈ t.toCellScheme.faces, t.comap f hf = u := by
  by_cases hf : univ.map f ∈ t.toCellScheme.faces
  · simp [restrictFace_of_mem t f hf, hf]
  · simp [restrictFace_of_notMem t f hf, hf]

/-- Definedness of the face map depends only on the face. -/
theorem isSome_restrictFace_congr {f' : Fin k ↪ Fin n} (h : univ.map f = univ.map f') :
    (restrictFace f t).isSome ↔ (restrictFace f' t).isSome := by
  simp [h]

/-- **Identity law**: the face map along the identity is defined and returns the type. -/
@[simp] theorem restrictFace_refl : restrictFace (Function.Embedding.refl (Fin n)) t = some t := by
  have hf : univ.map (Function.Embedding.refl (Fin n)) ∈ t.toCellScheme.faces := by
    simpa using t.univ_mem_faces
  rw [restrictFace_of_mem t _ hf, comap_refl]

/-- **Guarded composition law**: if the face map along `f` is defined with value `u`, then the
face map along `g` at `u` is the face map along the composite, including definedness. -/
theorem restrictFace_trans {u : StageType.{u} α m} (hu : restrictFace f t = some u) :
    restrictFace g u = restrictFace (g.trans f) t := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff t f).mp hu
  have hiff := t.map_univ_mem_comap_faces_iff f g hf
  by_cases hgf : univ.map (g.trans f) ∈ t.toCellScheme.faces
  · rw [restrictFace_of_mem _ g (hiff.mpr hgf), restrictFace_of_mem t _ hgf, comap_comap]
  · rw [restrictFace_of_notMem _ g (mt hiff.mp hgf), restrictFace_of_notMem t _ hgf]

/-- The guarded composition law in `Option.bind` form: face maps along `f` and then `g` compose to
the face map along the composite whenever the first is defined, and to `none` otherwise. -/
theorem bind_restrictFace :
    (restrictFace f t).bind (restrictFace g) =
      if univ.map f ∈ t.toCellScheme.faces then restrictFace (g.trans f) t else none := by
  by_cases hf : univ.map f ∈ t.toCellScheme.faces
  · simp only [hf, ↓reduceIte, restrictFace_of_mem t f hf, Option.bind_some]
    exact restrictFace_trans t f g (restrictFace_of_mem t f hf)
  · simp only [hf, ↓reduceIte, restrictFace_of_notMem t f hf, Option.bind_none]

/-- A composite through an undefined face that covers the whole face is undefined. -/
theorem restrictFace_trans_eq_none (hf : restrictFace f t = none)
    (hg : Function.Surjective g) : restrictFace (g.trans f) t = none := by
  have h : univ.map (g.trans f) = univ.map f := by
    rw [← map_map, map_univ_of_surjective hg]
  rw [restrictFace_eq_none_iff, h]
  exact (restrictFace_eq_none_iff t f).mp hf

/-! ### Cells of full grade -/

/-- **Full grade means full scope**: a cell of grade `n` of a stage type on `n` points has graded
index `(univ, n)`, since its grade is at most the size of its scope. -/
theorem gradedIndex_eq_univ_of_grade_eq (t : StageType.{u} α n) {d : Fin t.card}
    (h : t.toCellScheme.grade d = n) : t.toCellScheme.gradedIndex d = (univ, n) := by
  refine Prod.ext (eq_univ_of_card _ (le_antisymm (card_le_univ _) ?_)) h
  rw [Fintype.card_fin]
  exact h.ge.trans (t.isWellFormed.isWellFormed.grade_le_card d)

/-! ### Stage types on no points -/

/-- A stage type on no points has no cells: a cell would have a positive grade at most the size of
its scope, which is empty. -/
theorem card_eq_zero (t : StageType.{u} α 0) : t.card = 0 := by
  by_contra h
  have d : Fin t.card := ⟨0, Nat.pos_of_ne_zero h⟩
  have hle := t.isWellFormed.isWellFormed.grade_le_card d
  have hpos := t.isWellFormed.isWellFormed.grade_pos d
  have hs : t.toCellScheme.scope d = ∅ := eq_empty_of_isEmpty _
  rw [hs, card_empty] at hle
  omega

/-- The faces of a stage type on no points: only the empty face. -/
theorem faces_eq_of_zero (t : StageType.{u} α 0) : t.toCellScheme.faces = {∅} := by
  ext C
  simp only [mem_singleton]
  refine ⟨fun _ ↦ eq_empty_of_isEmpty C, ?_⟩
  rintro rfl
  exact t.isWellFormed.isWellFormed.isPlan.empty_mem

/-- **There is only one stage type on no points** at each stage. -/
theorem eq_of_zero (t t' : StageType.{u} α 0) : t = t' := by
  have hc := t.card_eq_zero
  have hc' := t'.card_eq_zero
  refine ext (Scheme.ext (hc.trans hc'.symm) (by rw [t.isWellFormed.ground_eq,
    t'.isWellFormed.ground_eq]) (by rw [t.faces_eq_of_zero, t'.faces_eq_of_zero])
    (fun i ↦ (hc ▸ i).elim0) (fun i ↦ (hc ▸ i).elim0) (fun s ↦ (hc ▸ s).elim0))
    fun i ↦ (hc ▸ i).elim0

/-- The empty face of a stage type is defined. -/
theorem isSome_restrictFace_of_zero (t : StageType.{u} α n) (e : Fin 0 ↪ Fin n) :
    (restrictFace e t).isSome := by
  rw [isSome_restrictFace_iff, univ_eq_empty, map_empty]
  exact t.isWellFormed.isWellFormed.isPlan.empty_mem

/-- The first point of a two-point type spans a closed face: singletons are closed in a plan. -/
theorem exists_restrictFace_castSuccEmb_of_two (t : StageType.{u} α 2) :
    ∃ p, restrictFace (Fin.castSuccEmb : Fin 1 ↪ Fin 2) t = some p := by
  refine Option.isSome_iff_exists.mp ((isSome_restrictFace_iff _ _).mpr ?_)
  rw [show univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) = {0} by decide]
  exact t.isPlan.singleton_mem (mem_univ 0)

/-! ### Reindexing along bijections -/

/-- **Reindexing** a stage type along a bijection `e : Fin m ≃ Fin n` of points: the face map
along `e`, which is always defined. -/
noncomputable def reindex (e : Fin m ≃ Fin n) : StageType.{u} α m :=
  t.comap e.toEmbedding (by simpa [map_univ_equiv] using t.univ_mem_faces)

/-- The scheme of a reindexed stage type is the restricted scheme. -/
@[simp] theorem reindex_toScheme (e : Fin m ≃ Fin n) :
    (t.reindex e).toScheme = t.toScheme.comap e.toEmbedding := rfl

/-- The labels of a reindexed stage type are the labels of the corresponding cells. -/
@[simp] theorem reindex_label (e : Fin m ≃ Fin n) (i : Fin (t.reindex e).card) :
    (t.reindex e).label i = t.label (t.cellMap e.toEmbedding i) := rfl

/-- The face map along a bijection is reindexing. -/
@[simp] theorem restrictFace_equiv (e : Fin m ≃ Fin n) :
    restrictFace e.toEmbedding t = some (t.reindex e) :=
  restrictFace_of_mem _ _ _

/-- The face map after reindexing is the face map along the composite. -/
theorem restrictFace_reindex (e : Fin m ≃ Fin n) :
    restrictFace g (t.reindex e) = restrictFace (g.trans e.toEmbedding) t :=
  restrictFace_trans t _ g (t.restrictFace_equiv e)

/-- Reindexing after the face map is the face map along the composite. -/
theorem map_reindex_restrictFace (e : Fin k ≃ Fin m) :
    (restrictFace f t).map (reindex · e) = restrictFace (e.toEmbedding.trans f) t := by
  cases hu : restrictFace f t with
  | none =>
    exact (restrictFace_trans_eq_none t f e.toEmbedding hu e.surjective).symm
  | some u =>
    rw [Option.map_some, ← restrictFace_trans t f _ hu, restrictFace_equiv]

/-- Reindexing along the identity is the identity. -/
@[simp] theorem reindex_refl : t.reindex (Equiv.refl (Fin n)) = t :=
  t.comap_refl _

/-- Reindexing twice is reindexing along the composite. -/
@[simp] theorem reindex_reindex (e : Fin m ≃ Fin n) (e' : Fin k ≃ Fin m) :
    (t.reindex e).reindex e' = t.reindex (e'.trans e) := by
  have h := t.restrictFace_reindex e'.toEmbedding e
  rw [restrictFace_equiv, ← Equiv.trans_toEmbedding, restrictFace_equiv] at h
  exact Option.some_injective _ h

/-! ### Stage reduction -/

/-- **Stage reduction** of a stage type to a stage `β` that is zero or a limit [Kni26, §3.1]: the
same scheme and rows, with every label reduced to stage `β`. -/
noncomputable def reduce (hβ : Order.IsSuccPrelimit β) : StageType.{u} β n where
  toScheme := t.toScheme
  label := Label.reduce β ∘ t.label
  isWellFormed := t.isWellFormed
  isCoded := t.isCoded
  isLawful := t.isLawful.reduce hβ
  atStage _ := atStage_reduce β _

/-- Stage reduction keeps the scheme. -/
@[simp] theorem reduce_toScheme (hβ : Order.IsSuccPrelimit β) :
    (t.reduce hβ).toScheme = t.toScheme := rfl

/-- Stage reduction reduces each label. -/
@[simp] theorem reduce_label (hβ : Order.IsSuccPrelimit β) (d : Fin t.card) :
    (t.reduce hβ).label d = Label.reduce β (t.label d) := rfl

/-- **Coherence of stage reduction**: reducing to `β` and then to a lower stage `γ` is reducing
to `γ`. -/
theorem reduce_reduce (hβ : Order.IsSuccPrelimit β) (hγ : Order.IsSuccPrelimit γ) (hγβ : γ ≤ β) :
    (t.reduce hβ).reduce hγ = t.reduce hγ :=
  ext rfl fun i j h ↦ by
    rw [Fin.ext h]
    exact reduce_reduce_of_le hγβ _

/-- Reduction to the stage of the type is the identity. -/
@[simp] theorem reduce_self (hα : Order.IsSuccPrelimit α) : t.reduce hα = t :=
  ext rfl fun i j h ↦ by
    rw [Fin.ext h]
    exact (t.atStage _).reduce_eq

/-- Reduction to a stage at least the stage of the type does not change the labels. -/
theorem reduce_label_of_le (hβ : Order.IsSuccPrelimit β) (hαβ : α ≤ β) (d : Fin t.card) :
    (t.reduce hβ).label d = t.label d :=
  ((t.atStage d).mono hαβ).reduce_eq

/-- A stage type at stage `α` read at a larger stage `β`: the same scheme and labels, each of
which occurs at stage `β`. -/
def castLE (h : α ≤ β) : StageType.{u} β n :=
  { t with atStage := fun d ↦ (t.atStage d).mono h }

/-- Relabelling the stage keeps the scheme. -/
@[simp] theorem castLE_toScheme (h : α ≤ β) : (t.castLE h).toScheme = t.toScheme := rfl

/-- Relabelling the stage keeps the labels. -/
@[simp] theorem castLE_label (h : α ≤ β) (d : Fin t.card) : (t.castLE h).label d = t.label d :=
  rfl

/-- Relabelling to the same stage is the identity. -/
@[simp] theorem castLE_refl : t.castLE le_rfl = t := rfl

/-- Relabelling twice is relabelling once. -/
@[simp] theorem castLE_castLE (h : α ≤ β) (h' : β ≤ γ) :
    (t.castLE h).castLE h' = t.castLE (h.trans h') :=
  rfl

/-- **Reduction to a larger stage only relabels the stage**: for `α ≤ β`, the reduction of a
stage type at stage `α` to `β` is the type itself, read at stage `β`. -/
theorem reduce_eq_castLE (hβ : Order.IsSuccPrelimit β) (h : α ≤ β) :
    t.reduce hβ = t.castLE h :=
  ext rfl fun i j hij ↦ by
    rw [Fin.ext hij]
    exact t.reduce_label_of_le hβ h j

/-- Reduction does not see the stage at which a type is read. -/
@[simp] theorem reduce_castLE (h : α ≤ β) (hγ : Order.IsSuccPrelimit γ) :
    (t.castLE h).reduce hγ = t.reduce hγ :=
  rfl

/-- Stage reduction commutes with restriction to a closed face. -/
theorem comap_reduce (hβ : Order.IsSuccPrelimit β) (hf : univ.map f ∈ t.toCellScheme.faces) :
    (t.reduce hβ).comap f hf = (t.comap f hf).reduce hβ := rfl

/-- **Stage reduction commutes with face maps**, including definedness. -/
theorem restrictFace_reduce (hβ : Order.IsSuccPrelimit β) :
    restrictFace f (t.reduce hβ) = (restrictFace f t).map (reduce · hβ) := by
  by_cases hf : univ.map f ∈ t.toCellScheme.faces
  · rw [restrictFace_of_mem (t.reduce hβ) f hf, restrictFace_of_mem t f hf, Option.map_some,
      comap_reduce]
  · rw [restrictFace_of_notMem (t.reduce hβ) f hf, restrictFace_of_notMem t f hf,
      Option.map_none]

/-- The face along `f` of a stage type at `α` reducing to `q` reduces to the face of `q`: if `q`
restricts to `p` along `f` and `Q` reduces to `q`, then `Q` restricts along `f` to a stage type
reducing to `p`. -/
theorem exists_restrictFace_reduce_eq {α β : Ordinal.{u}} {k m : ℕ} {q : StageType.{u} β m}
    {f : Fin k ↪ Fin m} {p : StageType.{u} β k} {hβ : Order.IsSuccPrelimit β}
    (hfp : restrictFace f q = some p) {Q : StageType.{u} α m}
    (hQ : Q.reduce hβ = q) : ∃ P, restrictFace f Q = some P ∧ P.reduce hβ = p := by
  have h := restrictFace_reduce Q f hβ
  rw [hQ, hfp] at h
  exact Option.map_eq_some_iff.mp h.symm

/-- Stage reduction commutes with reindexing. -/
theorem reindex_reduce (hβ : Order.IsSuccPrelimit β) (e : Fin m ≃ Fin n) :
    (t.reduce hβ).reindex e = (t.reindex e).reduce hβ := rfl

/-! ### Stage types from lawful sections -/

/-- The stage type at a zero-or-limit stage `α` on a well-formed scheme with coded rows, with the
stage reduction of a lawful section `ρ` as labels. -/
noncomputable def ofIsLawful (hα : Order.IsSuccPrelimit α) (S : Scheme.{u} n)
    (hw : S.IsWellFormed) (hc : S.IsCoded) (ρ : Fin S.card → Label.{u})
    (hρ : S.rows.IsLawful ρ) : StageType.{u} α n where
  toScheme := S
  label := Label.reduce α ∘ ρ
  isWellFormed := hw
  isCoded := hc
  isLawful := hρ.reduce hα
  atStage _ := atStage_reduce α _

section OfIsLawful

variable (hα : Order.IsSuccPrelimit α) (S : Scheme.{u} n) (hw : S.IsWellFormed) (hc : S.IsCoded)
  (ρ : Fin S.card → Label.{u}) (hρ : S.rows.IsLawful ρ)

/-- The scheme of `ofIsLawful` is the given scheme. -/
@[simp] theorem ofIsLawful_toScheme : (ofIsLawful hα S hw hc ρ hρ).toScheme = S := rfl

/-- The labels of `ofIsLawful` are the reduced labels of the section. -/
@[simp] theorem ofIsLawful_label (d : Fin S.card) :
    (ofIsLawful hα S hw hc ρ hρ).label d = Label.reduce α (ρ d) := rfl

variable {S hw hc ρ hρ}

/-- A stage type built from a lawful section extending the labels of `p` along a closed face has
the face `p` there. -/
theorem restrictFace_ofIsLawful {f : Fin m ↪ Fin n} (hf : univ.map f ∈ S.toCellScheme.faces)
    {p : StageType.{u} α m} (hp : S.comap f = p.toScheme)
    (hext : ∀ (i : Fin (S.comap f).card) (j : Fin p.card), (i : ℕ) = j →
      ρ (S.cellMap f i) = p.label j) :
    restrictFace f (ofIsLawful hα S hw hc ρ hρ) = some p := by
  rw [restrictFace_of_mem _ f hf]
  refine congrArg some (ext hp fun i j hij ↦ ?_)
  exact (congrArg (Label.reduce α) (hext i j hij)).trans (p.atStage j).reduce_eq

end OfIsLawful

/-- **Stage reduction through `ofIsLawful`**: the stage reduction of a type is `ofIsLawful`
applied to its own labels. -/
theorem reduce_eq_ofIsLawful (hβ : Order.IsSuccPrelimit β) (t : StageType.{u} α n) :
    t.reduce hβ = ofIsLawful hβ t.toScheme t.isWellFormed t.isCoded t.label t.isLawful :=
  rfl

/-! ### Cells visible through a face -/

/-- **Labels of a face type transport to the cells visible through it.** -/
theorem label_of_restrictFace {n m : ℕ} {Am : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {t : StageType.{u} α m} (hf : StageType.restrictFace f Am = some t)
    (P : ℕ → Label.{u} → Prop) (hP : ∀ i, P (t.toCellScheme.grade i) (t.label i))
    {d : Fin Am.card} (hd : (Am.toCellScheme.scope d : Set (Fin n)) ⊆ Set.range f) :
    P (Am.toCellScheme.grade d) (Am.label d) := by
  obtain ⟨hf', rfl⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  obtain ⟨i, rfl⟩ : d ∈ Set.range (Am.cellMap f) := by
    rw [Scheme.range_cellMap]; exact Scheme.mem_visibleCells.mpr hd
  exact hP i

/-- **Rows of a face type transport to the cells visible through it.** -/
theorem row_of_restrictFace {n m : ℕ} {Am : StageType.{u} α n} {f : Fin m ↪ Fin n}
    {t : StageType.{u} α m} (hf : StageType.restrictFace f Am = some t)
    (P : ℕ → ℕ → Label.{u} → Prop)
    (hP : ∀ s (i : t.toCellScheme.below (t.toCellScheme.gradedIndex s)),
      P (t.toCellScheme.grade s) (t.toCellScheme.grade i) (t.rows.row s i))
    {s : Fin Am.card} (hs : (Am.toCellScheme.scope s : Set (Fin n)) ⊆ Set.range f)
    (i : Am.toCellScheme.below (Am.toCellScheme.gradedIndex s)) :
    P (Am.toCellScheme.grade s) (Am.toCellScheme.grade i) (Am.rows.row s i) := by
  obtain ⟨hf', rfl⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  obtain ⟨s', rfl⟩ : s ∈ Set.range (Am.cellMap f) := by
    rw [Scheme.range_cellMap]; exact Scheme.mem_visibleCells.mpr hs
  obtain ⟨i', hi'⟩ : i.1 ∈ Set.range (Am.cellMap f) := by
    rw [Scheme.range_cellMap]
    exact Scheme.mem_visibleCells.mpr ((coe_subset.mpr i.2.1).trans hs)
  have hmem : i' ∈ (Am.toScheme.comap f).toCellScheme.below
      ((Am.toScheme.comap f).toCellScheme.gradedIndex s') := by
    refine ((Am.toScheme.isLowerEmbedding_comap f).le_iff i' s').mp ?_
    rw [hi']; exact i.2
  have h := hP s' ⟨i', hmem⟩
  have hrow : (Am.comap f hf').rows.row s' ⟨i', hmem⟩ = Am.rows.row (Am.cellMap f s') i :=
    Am.rows.row_congr rfl hi'
  have hgr : (Am.comap f hf').toCellScheme.grade i' = Am.toCellScheme.grade i.1 := by
    rw [← hi']; rfl
  rw [hrow, hgr] at h
  exact h

/-- **Cells visible through a face whose type has one cell at each graded index have distinct
graded indices.** -/
theorem eq_of_gradedIndex_eq_of_restrictFace {n m : ℕ} {Am : StageType.{u} α n}
    {f : Fin m ↪ Fin n} {t : StageType.{u} α m} (hf : StageType.restrictFace f Am = some t)
    (ht : Function.Injective t.toCellScheme.gradedIndex) {z z' : Fin Am.card}
    (hz : (Am.toCellScheme.scope z : Set (Fin n)) ⊆ Set.range f)
    (hz' : (Am.toCellScheme.scope z' : Set (Fin n)) ⊆ Set.range f)
    (h : Am.toCellScheme.gradedIndex z = Am.toCellScheme.gradedIndex z') : z = z' := by
  obtain ⟨hf', rfl⟩ := (StageType.restrictFace_eq_some_iff _ _).mp hf
  obtain ⟨i, rfl⟩ : z ∈ Set.range (Am.cellMap f) := by
    rw [Scheme.range_cellMap]; exact Scheme.mem_visibleCells.mpr hz
  obtain ⟨i', rfl⟩ : z' ∈ Set.range (Am.cellMap f) := by
    rw [Scheme.range_cellMap]; exact Scheme.mem_visibleCells.mpr hz'
  rw [← Am.toScheme.map_comap_gradedIndex f i, ← Am.toScheme.map_comap_gradedIndex f i'] at h
  have hinj : Function.Injective (Prod.map (Finset.map f) (id : ℕ → ℕ)) :=
    (Finset.map_injective f).prodMap Function.injective_id
  exact congrArg _ (ht (hinj h))

end StageType

end VaughtConjecture
