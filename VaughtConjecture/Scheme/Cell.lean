/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.InitialSeg
import VaughtConjecture.Geometry.Plan

/-!
# Cell schemes: graded cells over a plan

Roadmap, Library conventions (raw data separate from their laws; a scheme carries its cells,
scopes, grades, and face geometry) and Layer 1 (graded cells); semantic contract, item 3 (cell
scopes and grades); the expositions, §1 (a cell has a closed support and a positive grade bounded
by the size of that support).  The semantic rows of a scheme are separate data
(`CellScheme.Rows D`, in `VaughtConjecture.Scheme.Row`); the bundle of a scheme with its rows
belongs to the stage types (next tranche).

A **cell scheme** `D : CellScheme ι α` is raw data: a finite ground set `D.ground`, a finite family
of closed faces `D.faces`, and for every cell `d : ι` a **scope** `D.scope d` and a **grade**
`D.grade d`.  Cells are the points of the index type `ι`, not scope–grade pairs, so distinct cells
may share a graded index (physical multiplicities are kept).  The laws are separate
(`CellScheme.IsWellFormed`): there are finitely many cells, the faces form a plan on the ground set
(`Geometry.IsPlan`), and every cell's graded index `(scope, grade)` is a *graded face*: its scope is
closed and its grade lies in `[1, |scope|]` (`gradedFaces`).  A well-formed scheme is therefore
finite data, and no cell lies below a pair of grade `0` or a pair on the empty face
(`IsWellFormed.below_eq_empty`).

Graded indices `Finset α × ℕ` carry Mathlib's product order, `(C, i) ≤ (B, j) ↔ C ⊆ B ∧ i ≤ j`;
this is the graded order on scope–grade pairs, not a new relation.

* `D.below X` is the set of cells whose graded index lies below the pair `X`; the semantic row of
  a cell `s` is a labelling of `D.below (D.gradedIndex s)` (`VaughtConjecture.Scheme.Row`).
* `D.visible S` is the set of cells whose scope lies in `S`.
* `D.reindex φ` reads the cells of `D` through a map of index types; `D.restrict B` is the
  restriction to a face `B`, with the faces inside `B` and the cells visible in `B` (the cells
  below a pair inside `B` are the same there, `image_val_below_restrict`); and `D.comap f` is the
  pullback along an embedding `f : β ↪ α` of ground types, with the faces whose image is
  closed and the cells visible through `f`, their scopes pulled back.  Restriction to a closed face
  and pullback along an embedding whose range meets the ground set in a closed face preserve
  well-formedness (`IsWellFormed.restrict`, `IsWellFormed.comap`), as does reindexing along any
  map from a finite type of cells (`IsWellFormed.reindex`).  The graded faces of `D.comap f` are
  the pairs whose image under `(C, j) ↦ (f '' C, j)` is a graded face of `D`
  (`mem_gradedFaces_comap`), and the cells below a pair in the pullback are the cells below its
  image (`image_val_below_comap`).
* `IsLowerEmbedding E D φ`: the cell map `φ` is injective, preserves grades, preserves and reflects
  the graded order, and its image contains every cell below the image of a cell.  Apart from the
  grades, this says that `φ` is an initial segment (`InitialSeg`) for the graded preorders
  `s ≤ t ↔ gradedIndex s ≤ gradedIndex t` (`IsLowerEmbedding.toInitialSeg`).  Lower embeddings
  compose (`IsLowerEmbedding.comp`); reindexing along an equivalence and its inverse, restriction,
  and pullback are lower embeddings, as are the inclusion of a lower set `D.below X` and the
  induced maps of lower sets (`IsLowerEmbedding.below`).  The inverse of an equivalence of cells
  that is a lower embedding is a lower embedding (`IsLowerEmbedding.symm`), and a lower embedding
  mapping the cells below `X` onto the cells below `Y` induces an equivalence of these lower sets
  (`IsLowerEmbedding.belowEquiv`) that is a lower embedding of the schemes of cells below them
  and commutes with restriction (`IsLowerEmbedding.belowEquiv_inclusion`); semantic rows and
  lawful sections transport along lower embeddings.
-/

namespace VaughtConjecture

open Finset

variable {ι κ α β : Type*}

/-! ### Cell schemes -/

/-- A **cell scheme**: the raw data of a finite ground set, a finite family of closed faces, and a
family of cells indexed by `ι`, each with a scope and a grade.  The laws, including the finiteness
of the family of cells, are `CellScheme.IsWellFormed`. -/
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

/-- The laws of a cell scheme: there are finitely many cells, the faces form a plan on the ground
set, and the graded index of every cell is a graded face (its scope is closed and its grade lies
in `[1, |scope|]`). -/
structure IsWellFormed [DecidableEq α] : Prop where
  /-- There are finitely many cells. -/
  finite : Finite ι
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

/-- In a well-formed scheme, no cell lies below a pair of grade `0` or a pair on the empty face. -/
theorem IsWellFormed.below_eq_empty {D : CellScheme ι α} [DecidableEq α] (hD : D.IsWellFormed)
    {X : Finset α × ℕ} (hX : X.2 = 0 ∨ X.1 = ∅) : D.below X = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun d hd ↦ ?_
  have hpos := hD.grade_pos d
  have hcard := hD.grade_le_card d
  rcases hX with hX | hX
  · have : D.grade d ≤ X.2 := hd.2
    omega
  · have : D.scope d = ∅ := subset_empty.mp (hX ▸ hd.1)
    simp [this] at hcard
    omega

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

/-- Reindexing a well-formed scheme along any map from a finite type of cells gives a well-formed
scheme (cells may be duplicated). -/
theorem IsWellFormed.reindex [DecidableEq α] [Finite κ] {D : CellScheme ι α}
    (hD : D.IsWellFormed) (φ : κ → ι) : (D.reindex φ).IsWellFormed :=
  ⟨inferInstance, hD.isPlan, fun t ↦ hD.gradedIndex_mem (φ t)⟩

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

/-- The cells below a pair whose face lies in `B` are the same in the restriction to `B` and in
the scheme. -/
theorem image_val_below_restrict {B : Finset α} {X : Finset α × ℕ} (hX : X.1 ⊆ B) :
    ((↑) : D.visible (B : Set α) → ι) '' (D.restrict B).below X = D.below X := by
  ext d
  refine ⟨?_, fun hd ↦ ⟨⟨d, coe_subset.mpr (hd.1.trans hX)⟩, hd, rfl⟩⟩
  rintro ⟨d, hd, rfl⟩
  exact hd

/-- The restriction of a well-formed scheme to a closed face is well formed. -/
theorem IsWellFormed.restrict {D : CellScheme ι α} (hD : D.IsWellFormed) {B : Finset α}
    (hB : B ∈ D.faces) : (D.restrict B).IsWellFormed where
  finite := have := hD.finite; Subtype.finite
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

/-- A cell of the pullback lies below a pair exactly when its original cell lies below the image
of the pair. -/
theorem gradedIndex_comap_le_iff (d : D.visible (Set.range f)) {X : Finset β × ℕ} :
    (D.comap f).gradedIndex d ≤ X ↔ D.gradedIndex d ≤ Prod.map (Finset.map f) id X := by
  rw [gradedIndex_le_iff, gradedIndex_le_iff, ← map_subset_map (f := f), map_comap_scope]
  simp

/-- The graded faces of the pullback are the pairs whose image is a graded face. -/
theorem mem_gradedFaces_comap {X : Finset β × ℕ} :
    X ∈ (D.comap f).gradedFaces ↔ Prod.map (Finset.map f) id X ∈ D.gradedFaces := by
  simp

/-- The cells below a pair in the pullback are the cells below the image of the pair. -/
theorem image_val_below_comap (X : Finset β × ℕ) :
    ((↑) : D.visible (Set.range f) → ι) '' (D.comap f).below X =
      D.below (Prod.map (Finset.map f) id X) := by
  ext d
  refine ⟨?_, fun hd ↦ ⟨⟨d, ?_⟩, (gradedIndex_comap_le_iff D f _).mpr hd, rfl⟩⟩
  · rintro ⟨d, hd, rfl⟩
    exact (gradedIndex_comap_le_iff D f d).mp hd
  · exact (coe_subset.mpr hd.1).trans (by simp)

/-- The pullback of a well-formed scheme along an embedding whose range meets the ground set in
a closed face is well formed. -/
theorem IsWellFormed.comap [DecidableEq α] [DecidableEq β] {D : CellScheme ι α}
    (hD : D.IsWellFormed)
    (hf : (D.ground.preimage f f.injective.injOn).map f ∈ D.faces) :
    (D.comap f).IsWellFormed where
  finite := have := hD.finite; Subtype.finite
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
of a cell is itself in the image.  Apart from the grades, this says that `φ` is an initial segment
(`InitialSeg`) for the graded preorders on cells (`IsLowerEmbedding.toInitialSeg`).  Lower
embeddings identify each lower set `E.below (E.gradedIndex s)` with
`D.below (D.gradedIndex (φ s))`. -/
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

variable {μ γ : Type*} {F : CellScheme μ γ} {φ : κ → ι} {ψ : μ → κ}

/-- A lower embedding as an initial segment of the graded preorders on cells,
`s ≤ t ↔ gradedIndex s ≤ gradedIndex t`. -/
def toInitialSeg {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) :
    InitialSeg (fun s t : κ ↦ E.gradedIndex s ≤ E.gradedIndex t)
      (fun s t : ι ↦ D.gradedIndex s ≤ D.gradedIndex t) where
  toFun := φ
  inj' := hφ.injective
  map_rel_iff' {s t} := hφ.le_iff s t
  mem_range_of_rel' t d := hφ.mem_range t d

/-- The initial segment of a lower embedding is the cell map. -/
@[simp] theorem coe_toInitialSeg {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) :
    ⇑hφ.toInitialSeg = φ := rfl

/-- An initial segment of the graded preorders on cells that preserves grades is a lower
embedding. -/
theorem of_initialSeg {D : CellScheme ι α}
    (f : InitialSeg (fun s t : κ ↦ E.gradedIndex s ≤ E.gradedIndex t)
      (fun s t : ι ↦ D.gradedIndex s ≤ D.gradedIndex t))
    (hf : ∀ t, D.grade (f t) = E.grade t) : E.IsLowerEmbedding D f :=
  ⟨f.injective, hf, fun _ _ ↦ f.map_rel_iff, fun _ _ ↦ f.mem_range_of_rel⟩

/-- A lower embedding preserves and reflects equality of graded indices. -/
theorem gradedIndex_eq_iff {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) (s t : κ) :
    D.gradedIndex (φ s) = D.gradedIndex (φ t) ↔ E.gradedIndex s = E.gradedIndex t := by
  simp only [le_antisymm_iff, hφ.le_iff]

/-- The identity is a lower embedding of a scheme into itself. -/
protected theorem id (D : CellScheme ι α) : D.IsLowerEmbedding D id :=
  ⟨Function.injective_id, fun _ ↦ rfl, fun _ _ ↦ Iff.rfl, fun _ d _ ↦ ⟨d, rfl⟩⟩

/-- Lower embeddings compose. -/
theorem comp {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) (hψ : F.IsLowerEmbedding E ψ) :
    F.IsLowerEmbedding D (φ ∘ ψ) :=
  of_initialSeg (hψ.toInitialSeg.trans hφ.toInitialSeg) fun t ↦
    (hφ.grade_eq (ψ t)).trans (hψ.grade_eq t)

/-- An equivalence of cells preserving graded indices is a lower embedding. -/
theorem of_equiv {E : CellScheme κ α} {D : CellScheme ι α} (e : κ ≃ ι)
    (h : ∀ t, D.gradedIndex (e t) = E.gradedIndex t) : E.IsLowerEmbedding D e :=
  ⟨e.injective, fun t ↦ congrArg Prod.snd (h t), fun s t ↦ by rw [h s, h t],
    fun _ d _ ↦ e.surjective d⟩

/-- Reindexing along an equivalence is a lower embedding. -/
theorem reindex (D : CellScheme ι α) (e : κ ≃ ι) : (D.reindex e).IsLowerEmbedding D e :=
  of_equiv e fun _ ↦ rfl

variable {D} in
/-- The inverse of an equivalence of cells that is a lower embedding is a lower embedding. -/
theorem symm {e : κ ≃ ι} (h : E.IsLowerEmbedding D e) : D.IsLowerEmbedding E e.symm where
  injective := e.symm.injective
  grade_eq d := by rw [← h.grade_eq, e.apply_symm_apply]
  le_iff s t := by rw [← h.le_iff, e.apply_symm_apply, e.apply_symm_apply]
  mem_range _ d _ := e.symm.surjective d

/-- The inverse of an equivalence is a lower embedding of a scheme into its reindexing. -/
theorem reindex_symm (D : CellScheme ι α) (e : κ ≃ ι) : D.IsLowerEmbedding (D.reindex e) e.symm :=
  (reindex D e).symm

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

/-- For a lower embedding `φ` and a cell `s`, the induced map from the cells below `s` to the
cells below `φ s` is a lower embedding of the schemes of cells below them. -/
theorem below {D : CellScheme ι α} (hφ : E.IsLowerEmbedding D φ) (s : κ) :
    (E.reindex ((↑) : E.below (E.gradedIndex s) → κ)).IsLowerEmbedding
      (D.reindex ((↑) : D.below (D.gradedIndex (φ s)) → ι))
      (fun t ↦ ⟨φ t, (hφ.le_iff t s).mpr t.2⟩) := by
  refine ⟨fun a b h ↦ Subtype.ext (hφ.injective (congrArg Subtype.val h)),
    fun t ↦ hφ.grade_eq t, fun a b ↦ hφ.le_iff a b, fun t d hd ↦ ?_⟩
  obtain ⟨d', hd'⟩ := hφ.mem_range t d hd
  have hd's : E.gradedIndex d' ≤ E.gradedIndex s :=
    le_trans ((hφ.le_iff d' t).mp (hd' ▸ hd)) t.2
  exact ⟨⟨d', hd's⟩, Subtype.ext hd'⟩

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
  simp only [gradedIndex_le_iff, gradedIndex_fst, gradedIndex_snd, comap_grade]
  rw [← map_subset_map (f := f), map_comap_scope, map_comap_scope]

/-! #### Equivalences of lower sets -/

section BelowEquiv

variable {D}

/-- For a lower embedding `φ` mapping the cells below `X` onto the cells below `Y`, the induced
equivalence of these lower sets. -/
noncomputable def belowEquiv {X : Finset β × ℕ} {Y : Finset α × ℕ} (hφ : E.IsLowerEmbedding D φ)
    (h : φ '' E.below X = D.below Y) : E.below X ≃ D.below Y :=
  Set.BijOn.equiv φ ⟨(Set.image_eq_iff_surjOn_mapsTo.mp h).2, hφ.injective.injOn,
    (Set.image_eq_iff_surjOn_mapsTo.mp h).1⟩

/-- The cell underlying the image of a cell under `belowEquiv` is its image under `φ`. -/
@[simp] theorem coe_belowEquiv {X : Finset β × ℕ} {Y : Finset α × ℕ}
    (hφ : E.IsLowerEmbedding D φ) (h : φ '' E.below X = D.below Y) (t : E.below X) :
    (hφ.belowEquiv h t : ι) = φ t := rfl

/-- The equivalence of lower sets induced by a lower embedding is a lower embedding of the
schemes of cells below them. -/
theorem isLowerEmbedding_belowEquiv {X : Finset β × ℕ} {Y : Finset α × ℕ}
    (hφ : E.IsLowerEmbedding D φ) (h : φ '' E.below X = D.below Y) :
    (E.reindex ((↑) : E.below X → κ)).IsLowerEmbedding (D.reindex ((↑) : D.below Y → ι))
      (hφ.belowEquiv h) :=
  ⟨(hφ.belowEquiv h).injective, fun t ↦ hφ.grade_eq t, fun s t ↦ hφ.le_iff s t,
    fun _ d _ ↦ (hφ.belowEquiv h).surjective d⟩

/-- The equivalences of lower sets induced by a lower embedding commute with restriction. -/
theorem belowEquiv_inclusion {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ)
    {X' Y' : Finset β × ℕ} {X Y : Finset α × ℕ} (h' : X' ≤ Y') (h : X ≤ Y)
    (hX : φ '' E.below X' = D.below X) (hY : φ '' E.below Y' = D.below Y) (d : E.below X') :
    hφ.belowEquiv hY (Set.inclusion (E.below_mono h') d) =
      Set.inclusion (D.below_mono h) (hφ.belowEquiv hX d) :=
  Subtype.ext rfl

end BelowEquiv

end IsLowerEmbedding

/-! ### Cells below a pair inside a face -/

section BelowRestrict

variable [DecidableEq α] {B : Finset α} {Z : Finset α × ℕ}

/-- For a pair `Z` whose face lies in `B`, the cells below `Z` in `D` are the cells below `Z` in
the restriction `D.restrict B`. -/
def belowRestrictEquiv (hZ : Z.1 ⊆ B) : D.below Z ≃ (D.restrict B).below Z where
  toFun d := ⟨⟨d.1, coe_subset.mpr (d.2.1.trans hZ)⟩, d.2⟩
  invFun t := ⟨t.1.1, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cell underlying the image of a cell below `Z` in the restriction. -/
@[simp] theorem belowRestrictEquiv_apply_val_val (hZ : Z.1 ⊆ B) (d : D.below Z) :
    (D.belowRestrictEquiv hZ d).1.1 = d.1 := rfl

/-- The cell underlying the preimage of a cell below `Z` in the restriction. -/
@[simp] theorem belowRestrictEquiv_symm_apply_val (hZ : Z.1 ⊆ B) (t : (D.restrict B).below Z) :
    ((D.belowRestrictEquiv hZ).symm t).1 = t.1.1 := rfl

/-- Reading the cells below `Z` in the restriction is a lower embedding. -/
theorem IsLowerEmbedding.belowRestrictEquiv (hZ : Z.1 ⊆ B) :
    (D.reindex ((↑) : D.below Z → ι)).IsLowerEmbedding
      ((D.restrict B).reindex ((↑) : (D.restrict B).below Z → _)) (D.belowRestrictEquiv hZ) :=
  IsLowerEmbedding.of_equiv _ fun _ ↦ rfl

/-- Reading the cells below `Z` of the restriction in the scheme is a lower embedding. -/
theorem IsLowerEmbedding.belowRestrictEquiv_symm (hZ : Z.1 ⊆ B) :
    ((D.restrict B).reindex ((↑) : (D.restrict B).below Z → _)).IsLowerEmbedding
      (D.reindex ((↑) : D.below Z → ι)) (D.belowRestrictEquiv hZ).symm :=
  (IsLowerEmbedding.belowRestrictEquiv D hZ).symm

end BelowRestrict

end CellScheme

end VaughtConjecture
