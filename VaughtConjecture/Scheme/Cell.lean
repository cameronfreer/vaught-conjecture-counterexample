/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Geometry.Plan

/-!
# Cell schemes: graded cells over a plan

Roadmap, Library conventions (raw finite data separate from their laws; a scheme owns its cells,
scopes, grades, rows, and face geometry) and Layer 1 (graded cells); semantic contract, item 3
(cell scopes and grades); the expositions, §1 (a cell has a closed support and a positive grade
bounded by the size of that support).

A **cell scheme** `D : CellScheme ι α` is raw finite data: a ground set `D.ground`, a family of
closed faces `D.faces`, and for every cell `d : ι` a **scope** `D.scope d` and a **grade**
`D.grade d`.  Cells are the points of the index type `ι`, not scope–grade pairs, so distinct cells
may share a graded index (physical multiplicities are kept).  The laws are separate
(`CellScheme.IsWellFormed`): the faces form a plan on the ground set (`Geometry.IsPlan`), and every
cell's graded index `(scope, grade)` is a *graded face*: its scope is closed and its grade lies in
`[1, |scope|]` (`gradedFaces`).

Graded indices `Finset α × ℕ` carry Mathlib's product order, `(C, i) ≤ (B, j) ↔ C ⊆ B ∧ i ≤ j`;
this is the graded order on scope–grade pairs, not a new relation.

* `D.below X` is the set of cells whose graded index lies below the pair `X`; the semantic row of
  a cell `s` is a labelling of `D.below (D.gradedIndex s)` (`VaughtConjecture.Scheme.Row`).
* `D.visible S` is the set of cells whose scope lies in `S`.
* `D.reindex φ` reads the cells of `D` through a map of index types; `D.restrict B` is the
  restriction to a face `B`, with the faces inside `B` and the cells visible in `B`; and `D.comap f`
  is the pullback along an embedding `f : β ↪ α` of ground types, with the faces whose image is
  closed and the cells visible through `f`, their scopes pulled back.  Restriction to a closed face
  and pullback along an embedding whose range meets the ground set in a closed face preserve
  well-formedness (`IsWellFormed.restrict`, `IsWellFormed.comap`).
* `IsLowerEmbedding E D φ`: the cell map `φ` is injective, preserves grades, preserves and reflects
  the graded order, and its image contains every cell below the image of a cell.  Reindexing along
  an equivalence, restriction, and pullback are lower embeddings, as is the inclusion of a lower
  set `D.below X`; semantic rows and lawful sections transport along lower embeddings.
-/

namespace VaughtConjecture

open Finset

variable {ι κ α β : Type*}

/-! ### Cell schemes -/

/-- A **cell scheme**: the raw data of a ground set, a family of closed faces, and a family of
cells indexed by `ι`, each with a scope and a grade.  The laws are `CellScheme.IsWellFormed`. -/
@[ext]
structure CellScheme (ι α : Type*) where
  /-- The ground set. -/
  ground : Finset α
  /-- The closed faces (the plan). -/
  faces : Finset (Finset α)
  /-- The scope of each cell. -/
  scope : ι → Finset α
  /-- The grade of each cell. -/
  grade : ι → ℕ

namespace CellScheme

variable (D : CellScheme ι α) {E : CellScheme κ β} {X Y : Finset α × ℕ} {d s t : ι}

/-- The graded index of a cell: its scope and grade. -/
def gradedIndex (d : ι) : Finset α × ℕ := (D.scope d, D.grade d)

/-- The first component of a graded index is the scope. -/
@[simp, grind =] theorem gradedIndex_fst : (D.gradedIndex d).1 = D.scope d := rfl

/-- The second component of a graded index is the grade. -/
@[simp, grind =] theorem gradedIndex_snd : (D.gradedIndex d).2 = D.grade d := rfl

/-- A graded index lies below a pair when the scope is contained in the pair's face and the
grade is at most the pair's grade. -/
@[simp] theorem gradedIndex_le_iff : D.gradedIndex d ≤ X ↔ D.scope d ⊆ X.1 ∧ D.grade d ≤ X.2 :=
  Iff.rfl

/-- The *graded faces* of a scheme: the pairs `(B, j)` of a closed face `B` and a grade
`0 < j ≤ |B|`. -/
def gradedFaces : Set (Finset α × ℕ) := {X | X.1 ∈ D.faces ∧ 0 < X.2 ∧ X.2 ≤ #X.1}

/-- Membership in the graded faces. -/
@[simp, grind =] theorem mem_gradedFaces :
    X ∈ D.gradedFaces ↔ X.1 ∈ D.faces ∧ 0 < X.2 ∧ X.2 ≤ #X.1 :=
  Iff.rfl

/-- The laws of a cell scheme: the faces form a plan on the ground set, and the graded index of
every cell is a graded face (its scope is closed and its grade lies in `[1, |scope|]`). -/
structure IsWellFormed [DecidableEq α] : Prop where
  /-- The faces form a recursive visible-face plan on the ground set. -/
  isPlan : Geometry.IsPlan D.ground D.faces
  /-- Every cell has a closed scope and a grade between one and the size of its scope. -/
  gradedIndex_mem (d : ι) : D.gradedIndex d ∈ D.gradedFaces

namespace IsWellFormed

variable [DecidableEq α] {D} (hD : D.IsWellFormed)
include hD

/-- The scope of a cell is a closed face. -/
theorem scope_mem (d : ι) : D.scope d ∈ D.faces := (hD.gradedIndex_mem d).1

/-- The grade of a cell is positive. -/
theorem grade_pos (d : ι) : 0 < D.grade d := (hD.gradedIndex_mem d).2.1

/-- The grade of a cell is at most the size of its scope. -/
theorem grade_le_card (d : ι) : D.grade d ≤ #(D.scope d) := (hD.gradedIndex_mem d).2.2

/-- The scope of a cell lies in the ground set. -/
theorem scope_subset_ground (d : ι) : D.scope d ⊆ D.ground :=
  hD.isPlan.subset_of_mem (hD.scope_mem d)

end IsWellFormed

/-! ### Cells below a pair and visible cells -/

/-- The cells *below* the pair `X`: those whose graded index lies below `X`. -/
def below (X : Finset α × ℕ) : Set ι := {d | D.gradedIndex d ≤ X}

/-- Membership in `below`. -/
@[simp, grind =] theorem mem_below : d ∈ D.below X ↔ D.gradedIndex d ≤ X := Iff.rfl

/-- The cells below a pair increase with the pair. -/
theorem below_mono : Monotone D.below := fun _ _ h _ hd ↦ le_trans hd h

/-- A cell lies below its own graded index. -/
theorem mem_below_gradedIndex (d : ι) : d ∈ D.below (D.gradedIndex d) :=
  (mem_below D).mpr le_rfl

/-- The cells *visible* in `S`: those whose scope lies in `S`. -/
def visible (S : Set α) : Set ι := {d | (D.scope d : Set α) ⊆ S}

/-- Membership in `visible`. -/
@[simp, grind =] theorem mem_visible {S : Set α} : d ∈ D.visible S ↔ (D.scope d : Set α) ⊆ S :=
  Iff.rfl

/-- Every cell below a pair is visible in the pair's face. -/
theorem below_subset_visible (X : Finset α × ℕ) : D.below X ⊆ D.visible (X.1 : Set α) :=
  fun _ hd ↦ coe_subset.mpr hd.1

/-! ### Reindexing, restriction to a face, and pullback -/

/-- The scheme whose cells are read through `φ : κ → ι`: the cell `t` has the scope and grade of
`φ t`; ground and faces are unchanged.  Along an equivalence this is a relabelling of cells;
along the inclusion of `D.below X` it is the scheme `D⟨X⟩` of cells below `X`. -/
def reindex (φ : κ → ι) : CellScheme κ α where
  ground := D.ground
  faces := D.faces
  scope := D.scope ∘ φ
  grade := D.grade ∘ φ

/-- The ground set of a reindexed scheme. -/
@[simp] theorem reindex_ground (φ : κ → ι) : (D.reindex φ).ground = D.ground := rfl

/-- The faces of a reindexed scheme. -/
@[simp] theorem reindex_faces (φ : κ → ι) : (D.reindex φ).faces = D.faces := rfl

/-- The scope of a reindexed cell. -/
@[simp] theorem reindex_scope (φ : κ → ι) (t : κ) : (D.reindex φ).scope t = D.scope (φ t) := rfl

/-- The grade of a reindexed cell. -/
@[simp] theorem reindex_grade (φ : κ → ι) (t : κ) : (D.reindex φ).grade t = D.grade (φ t) := rfl

/-- The graded index of a reindexed cell. -/
@[simp] theorem gradedIndex_reindex (φ : κ → ι) (t : κ) :
    (D.reindex φ).gradedIndex t = D.gradedIndex (φ t) := rfl

/-- Reindexing a well-formed scheme gives a well-formed scheme. -/
theorem IsWellFormed.reindex [DecidableEq α] {D : CellScheme ι α} (hD : D.IsWellFormed)
    (φ : κ → ι) : (D.reindex φ).IsWellFormed :=
  ⟨hD.isPlan, fun t ↦ hD.gradedIndex_mem (φ t)⟩

section Restrict

variable [DecidableEq α]

/-- The **restriction** of a scheme to a face `B`: ground `B`, the faces contained in `B`, and the
cells visible in `B` with their scopes and grades. -/
def restrict (B : Finset α) : CellScheme (D.visible (B : Set α)) α where
  ground := B
  faces := Geometry.restrict D.faces B
  scope d := D.scope d
  grade d := D.grade d

/-- The ground set of a restriction is the face. -/
@[simp] theorem restrict_ground (B : Finset α) : (D.restrict B).ground = B := rfl

/-- The faces of a restriction are the faces contained in the face. -/
@[simp] theorem restrict_faces (B : Finset α) :
    (D.restrict B).faces = Geometry.restrict D.faces B := rfl

/-- A cell of a restriction has its original scope. -/
@[simp] theorem restrict_scope (B : Finset α) (d : D.visible (B : Set α)) :
    (D.restrict B).scope d = D.scope d := rfl

/-- A cell of a restriction has its original grade. -/
@[simp] theorem restrict_grade (B : Finset α) (d : D.visible (B : Set α)) :
    (D.restrict B).grade d = D.grade d := rfl

/-- A cell of a restriction has its original graded index. -/
@[simp] theorem gradedIndex_restrict (B : Finset α) (d : D.visible (B : Set α)) :
    (D.restrict B).gradedIndex d = D.gradedIndex d := rfl

/-- The restriction of a well-formed scheme to a closed face is well formed. -/
theorem IsWellFormed.restrict {D : CellScheme ι α} (hD : D.IsWellFormed) {B : Finset α}
    (hB : B ∈ D.faces) : (D.restrict B).IsWellFormed where
  isPlan := hD.isPlan.restrict hB
  gradedIndex_mem d :=
    ⟨Geometry.mem_restrict.mpr ⟨hD.scope_mem d, coe_subset.mp d.2⟩, hD.grade_pos d,
      hD.grade_le_card d⟩

end Restrict

section Comap

/-- The **pullback** of a scheme along an embedding `f : β ↪ α`: ground set and scopes are pulled
back, the faces are the sets whose image is a face, and the cells are those visible through `f`
(scope inside the range of `f`), with their grades. -/
noncomputable def comap (f : β ↪ α) : CellScheme (D.visible (Set.range f)) β where
  ground := D.ground.preimage f f.injective.injOn
  faces := D.faces.preimage (Finset.map f) (map_injective f).injOn
  scope d := (D.scope d).preimage f f.injective.injOn
  grade d := D.grade d

variable (f : β ↪ α)

/-- The ground set of a pullback is the preimage of the ground set. -/
@[simp] theorem comap_ground : (D.comap f).ground = D.ground.preimage f f.injective.injOn := rfl

/-- A set is a face of the pullback exactly when its image is a face. -/
@[simp, grind =] theorem mem_comap_faces {C : Finset β} :
    C ∈ (D.comap f).faces ↔ C.map f ∈ D.faces := by
  simp [comap]

/-- A cell of a pullback has the preimage of its scope as scope. -/
@[simp] theorem comap_scope (d : D.visible (Set.range f)) :
    (D.comap f).scope d = (D.scope d).preimage f f.injective.injOn := rfl

/-- A cell of a pullback has its original grade. -/
@[simp] theorem comap_grade (d : D.visible (Set.range f)) : (D.comap f).grade d = D.grade d := rfl

/-- The scope of a cell of a pullback maps back onto the original scope. -/
theorem map_comap_scope (d : D.visible (Set.range f)) :
    ((D.comap f).scope d).map f = D.scope d :=
  map_preimage_eq_of_subset_range d.2

/-- The pullback of a well-formed scheme along an embedding whose range meets the ground set in
a closed face is well formed. -/
theorem IsWellFormed.comap [DecidableEq α] [DecidableEq β] {D : CellScheme ι α}
    (hD : D.IsWellFormed)
    (hf : (D.ground.preimage f f.injective.injOn).map f ∈ D.faces) :
    (D.comap f).IsWellFormed where
  isPlan := by
    set B := (D.ground.preimage f f.injective.injOn).map f
    have hBr : (B : Set α) ⊆ Set.range f := by simp [B]
    have h := (hD.isPlan.restrict hf).preimage hBr
    have hB : B.preimage f f.injective.injOn = D.ground.preimage f f.injective.injOn :=
      preimage_map f _
    have hfaces : (Geometry.restrict D.faces B).preimage (Finset.map f) (map_injective f).injOn =
        (D.comap f).faces := by
      ext C
      simp only [mem_preimage, Geometry.mem_restrict, mem_comap_faces, and_iff_left_iff_imp, B,
        map_subset_map]
      exact fun hC ↦ map_subset_iff_subset_preimage.mp (hD.isPlan.subset_of_mem hC)
    rwa [hB, hfaces] at h
  gradedIndex_mem d := by
    refine ⟨(mem_comap_faces D f).mpr ((map_comap_scope D f d).symm ▸ hD.scope_mem d.1),
      hD.grade_pos d.1, ?_⟩
    rw [gradedIndex_fst, ← card_map f, map_comap_scope]
    exact hD.grade_le_card d.1

end Comap

/-! ### Lower embeddings -/

/-- A map of cells `φ : κ → ι` is a **lower embedding** of `E` into `D` if it is injective,
preserves grades, preserves and reflects the graded order, and every cell of `D` below the image
of a cell is itself in the image.  Lower embeddings identify each lower set `E.below
(E.gradedIndex s)` with `D.below (D.gradedIndex (φ s))`. -/
structure IsLowerEmbedding (E : CellScheme κ β) (D : CellScheme ι α) (φ : κ → ι) : Prop where
  /-- The cell map is injective. -/
  injective : Function.Injective φ
  /-- The cell map preserves grades. -/
  grade_eq (t : κ) : D.grade (φ t) = E.grade t
  /-- The cell map preserves and reflects the graded order. -/
  le_iff (s t : κ) : D.gradedIndex (φ s) ≤ D.gradedIndex (φ t) ↔ E.gradedIndex s ≤ E.gradedIndex t
  /-- Every cell below the image of a cell is in the image. -/
  mem_range (t : κ) (d : ι) : D.gradedIndex d ≤ D.gradedIndex (φ t) → d ∈ Set.range φ

namespace IsLowerEmbedding

variable {φ : κ → ι}

/-- A lower embedding preserves and reflects equality of graded indices. -/
theorem gradedIndex_eq_iff {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) (s t : κ) :
    D.gradedIndex (φ s) = D.gradedIndex (φ t) ↔ E.gradedIndex s = E.gradedIndex t := by
  simp only [le_antisymm_iff, hφ.le_iff]

/-- The identity is a lower embedding of a scheme into itself. -/
theorem id (D : CellScheme ι α) : D.IsLowerEmbedding D id :=
  ⟨Function.injective_id, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl, fun _ d _ ↦ ⟨d, rfl⟩⟩

/-- Reindexing along an equivalence is a lower embedding. -/
theorem reindex (D : CellScheme ι α) (e : κ ≃ ι) : (D.reindex e).IsLowerEmbedding D e :=
  ⟨e.injective, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl, fun _ d _ ↦ e.surjective d⟩

/-- The inclusion of the cells below a pair is a lower embedding of `D⟨X⟩` into `D`. -/
theorem subtypeVal_below (D : CellScheme ι α) (X : Finset α × ℕ) :
    (D.reindex ((↑) : D.below X → ι)).IsLowerEmbedding D (↑) :=
  ⟨Subtype.val_injective, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl,
    fun t d hd ↦ ⟨⟨d, le_trans hd t.2⟩, rfl⟩⟩

/-- The inclusion of lower sets `D⟨X⟩ ⊆ D⟨Y⟩` for `X ≤ Y` is a lower embedding. -/
theorem inclusion_below (D : CellScheme ι α) {X Y : Finset α × ℕ} (h : X ≤ Y) :
    (D.reindex ((↑) : D.below X → ι)).IsLowerEmbedding (D.reindex ((↑) : D.below Y → ι))
      (Set.inclusion (D.below_mono h)) :=
  ⟨Set.inclusion_injective _, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl,
    fun t d hd ↦ ⟨⟨d.1, le_trans hd t.2⟩, rfl⟩⟩

/-- The inclusion of the cells visible in a face is a lower embedding of the restriction. -/
theorem restrict [DecidableEq α] (D : CellScheme ι α) (B : Finset α) :
    (D.restrict B).IsLowerEmbedding D (↑) :=
  ⟨Subtype.val_injective, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl,
    fun t d hd ↦ ⟨⟨d, (coe_subset.mpr hd.1).trans t.2⟩, rfl⟩⟩

/-- The inclusion of the cells visible through an embedding is a lower embedding of the
pullback. -/
theorem comap (D : CellScheme ι α) (f : β ↪ α) :
    (D.comap f).IsLowerEmbedding D (↑) := by
  refine ⟨Subtype.val_injective, fun _ ↦ rfl, fun s t ↦ ?_,
    fun t d hd ↦ ⟨⟨d, (coe_subset.mpr hd.1).trans t.2⟩, rfl⟩⟩
  refine and_congr_left' ?_
  change D.scope s ⊆ D.scope t ↔ (D.comap f).scope s ⊆ (D.comap f).scope t
  rw [← map_subset_map (f := f), map_comap_scope, map_comap_scope]

end IsLowerEmbedding

end CellScheme

end VaughtConjecture
