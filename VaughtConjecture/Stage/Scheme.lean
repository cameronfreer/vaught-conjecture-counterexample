/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Sort
import VaughtConjecture.Scheme.Row

/-!
# Schemes on `n` points and their face restrictions

Roadmap, Library conventions (a scheme owns its cells, scopes, grades, rows, and face geometry;
raw data separate from their laws) and Layer 1 (countable stage types and exact partial face
maps); semantic contract, items 3–4; the expositions, §1.

A **scheme on `n` points** (`Scheme n`) bundles a cell scheme on the ground type `Fin n` whose
cells are `Fin card`, in their order, with its semantic rows (`CellScheme.Rows`).  It is raw
data.  Its laws are separate: `Scheme.IsWellFormed` (the ground set is all of `Fin n` and the cell
scheme is well formed) and `Scheme.IsCoded` (every row value is bottom or an ordinal
`ω · i + j`, that is, lies below `ω ^ 2`).  Consistency of the rows is the base predicate
`CellScheme.Rows.IsConsistent`, and completeness (`CellScheme.IsComplete`: every graded face is
the graded index of a cell) is defined here.

**Face restriction.**  For an embedding `f : Fin m ↪ Fin n`, `S.comap f : Scheme m` is the
pullback of the cell scheme along `f` (`CellScheme.comap`), whose cells are the cells of `S`
visible through `f` (`S.visibleCells f`), enumerated in increasing order (`S.cellMap f`, an order
embedding into the cells of `S`), with the rows pulled back along the resulting lower embedding
(`S.isLowerEmbedding_comap f`).  The restriction is data and is defined for every embedding; it is
well formed when the range of `f` is a closed face (`IsWellFormed.comap`), and the partial
face maps of stage types (`VaughtConjecture.Stage.Basic`) are defined by that condition.

Because the enumeration is canonical, the restriction is strictly functorial, with no guard:
`S.comap (Function.Embedding.refl _) = S` (`comap_refl`) and
`(S.comap f).comap g = S.comap (g.trans f)` (`comap_comap`).  Both follow from one fact: any
strictly monotone enumeration of the visible cells is the cell map (`cellMap_eq_of_strictMono`).
Graded indices are transported along `f` by `Prod.map (Finset.map f) id`, `(C, j) ↦ (f '' C, j)`,
which identifies the graded faces of the restriction with the graded faces of `S` inside the range
of `f` (`mem_gradedFaces_comap`), and the cell map sends the cells below a pair onto the cells below
its image (`image_cellMap_below`); completeness, codedness, and consistency pass to the restriction.

## References

Schemes with their rows are the domains with their semantics of [Kni26, §2.6], called schemes
here; face restriction is the horizontal restriction of [Kni26, Definition 3.1.2], whose
restriction of a semantics is [Kni26, Lemma 2.5.5]; completeness is [Kni26, Definition 2.5.15]
and the coding of row values follows [Kni26, Lemma 2.5.13], for R. W. Knight, *A counterexample
to Vaught's Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

namespace VaughtConjecture

open Finset

/-! ### Graded indices along an embedding and complete schemes -/

namespace CellScheme

variable {ι κ α β : Type*}

/-- A cell scheme is **complete** [Kni26, §2.5]: every graded face is the graded
index of some cell. -/
def IsComplete (D : CellScheme ι α) : Prop :=
  ∀ X ∈ D.gradedFaces, ∃ d, D.gradedIndex d = X

/-- A scheme is complete after reindexing along a surjective map of cells. -/
theorem IsComplete.reindex {D : CellScheme ι α} (hD : D.IsComplete) {φ : κ → ι}
    (hφ : Function.Surjective φ) : (D.reindex φ).IsComplete := fun X hX ↦ by
  obtain ⟨d, hd⟩ := hD X hX
  obtain ⟨t, rfl⟩ := hφ d
  exact ⟨t, hd⟩

/-- The pullback of a complete scheme along an embedding is complete: the image
`Prod.map (Finset.map f) id X` of a graded face `X` of the pullback is a graded face, whose cell is
visible through the embedding. -/
theorem IsComplete.comap {D : CellScheme ι α} (hD : D.IsComplete) (f : β ↪ α) :
    (D.comap f).IsComplete := by
  intro X hX
  obtain ⟨d, hd⟩ := hD _ ((mem_gradedFaces_comap D f).mp hX)
  have hsc : D.scope d = X.1.map f := congrArg Prod.fst hd
  refine ⟨⟨d, by simp [hsc]⟩, Prod.ext ?_ ?_⟩
  · simp [hsc, preimage_map]
  · simpa using congrArg Prod.snd hd

end CellScheme

/-! ### Schemes on `n` points -/

/-- A **scheme on `n` points**: a cell scheme on the ground type `Fin n` with the cells
`Fin card`, in their order, together with its semantic rows.  This is raw data; the laws are
`Scheme.IsWellFormed` and `Scheme.IsCoded`. -/
structure Scheme (n : ℕ) : Type (u + 1) where
  /-- The number of cells. -/
  card : ℕ
  /-- The cell scheme: ground set, faces, and the scope and grade of each cell. -/
  toCellScheme : CellScheme (Fin card) (Fin n)
  /-- The semantic rows. -/
  rows : toCellScheme.Rows.{u}

namespace Scheme

variable {n m k : ℕ} (S : Scheme.{u} n)

/-- **Extensionality** for schemes: equal numbers of cells, equal ground sets and faces, and equal
scopes, grades, and rows at cells with equal positions. -/
@[ext (iff := false)] theorem ext {S T : Scheme.{u} n} (hcard : S.card = T.card)
    (hground : S.toCellScheme.ground = T.toCellScheme.ground)
    (hfaces : S.toCellScheme.faces = T.toCellScheme.faces)
    (hscope : ∀ (i : Fin S.card) (j : Fin T.card), (i : ℕ) = j →
      S.toCellScheme.scope i = T.toCellScheme.scope j)
    (hgrade : ∀ (i : Fin S.card) (j : Fin T.card), (i : ℕ) = j →
      S.toCellScheme.grade i = T.toCellScheme.grade j)
    (hrow : ∀ (s : Fin S.card) (s' : Fin T.card)
      (t : S.toCellScheme.below (S.toCellScheme.gradedIndex s))
      (t' : T.toCellScheme.below (T.toCellScheme.gradedIndex s')),
      (s : ℕ) = s' → (t.1 : ℕ) = t'.1 → S.rows.row s t = T.rows.row s' t') :
    S = T := by
  obtain ⟨k, D, R⟩ := S
  obtain ⟨k', D', R'⟩ := T
  obtain rfl : k = k' := hcard
  obtain rfl : D = D' := CellScheme.ext hground hfaces (funext fun i ↦ hscope i i rfl)
    (funext fun i ↦ hgrade i i rfl)
  obtain rfl : R = R' := CellScheme.Rows.ext (funext fun s ↦ funext fun t ↦ hrow s s t t rfl rfl)
  rfl

/-! ### Visible cells and the cell map -/

variable (f : Fin m ↪ Fin n) (g : Fin k ↪ Fin m)

/-- The cells of `S` **visible through** `f`: those whose scope lies in the range of `f`. -/
def visibleCells : Finset (Fin S.card) := {d | S.toCellScheme.scope d ⊆ univ.map f}

variable {S f} in
/-- A cell is visible through `f` exactly when its scope lies in the range of `f`. -/
@[simp] theorem mem_visibleCells {d : Fin S.card} :
    d ∈ S.visibleCells f ↔ (S.toCellScheme.scope d : Set (Fin n)) ⊆ Set.range f := by
  simp [visibleCells, ← coe_subset]

/-- The enumeration in increasing order of the cells visible through `f`, as an equivalence onto
the visible cells. -/
noncomputable def cellEquiv : Fin #(S.visibleCells f) ≃ S.toCellScheme.visible (Set.range f) :=
  ((S.visibleCells f).orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight fun _ ↦ mem_visibleCells)

/-! ### Face restriction -/

/-- The **restriction** of a scheme along `f : Fin m ↪ Fin n`: the pullback of the cell scheme
along `f` on the visible cells, enumerated in increasing order, with the rows of those cells. -/
noncomputable def comap : Scheme.{u} m where
  card := #(S.visibleCells f)
  toCellScheme := (S.toCellScheme.comap f).reindex (S.cellEquiv f)
  rows := S.rows.comap ((CellScheme.IsLowerEmbedding.comap _ f).comp
    (CellScheme.IsLowerEmbedding.reindex _ (S.cellEquiv f)))

/-- The number of cells of the restriction is the number of visible cells. -/
theorem comap_card : (S.comap f).card = #(S.visibleCells f) := rfl

/-- The **cell map** of the restriction along `f`: the visible cells of `S` in increasing
order. -/
noncomputable def cellMap : Fin (S.comap f).card ↪o Fin S.card :=
  (S.visibleCells f).orderEmbOfFin rfl

/-- The cell underlying `S.cellEquiv f i` is `S.cellMap f i`. -/
@[simp] theorem coe_cellEquiv (i : Fin #(S.visibleCells f)) :
    (S.cellEquiv f i : Fin S.card) = S.cellMap f i := rfl

/-- The cell map lands in the visible cells. -/
theorem cellMap_mem (i : Fin (S.comap f).card) : S.cellMap f i ∈ S.visibleCells f :=
  orderEmbOfFin_mem _ _ i

/-- The range of the cell map is the set of visible cells. -/
@[simp] theorem range_cellMap : Set.range (S.cellMap f) = S.visibleCells f :=
  range_orderEmbOfFin _ _

/-- The number of cells visible through `f` is the size of any strictly monotone enumeration of
them. -/
theorem card_visibleCells_eq_of_strictMono {e : Fin k → Fin S.card} (he : StrictMono e)
    (hr : ∀ d, d ∈ Set.range e ↔ d ∈ S.visibleCells f) : #(S.visibleCells f) = k := by
  have hV : S.visibleCells f = univ.image e := by
    ext d
    simp [← hr d, Set.mem_range]
  rw [hV, card_image_of_injective _ he.injective, card_univ, Fintype.card_fin]

/-- **Uniqueness of the enumeration**: a strictly monotone map onto the visible cells agrees with
the cell map at equal positions. -/
theorem cellMap_eq_of_strictMono {e : Fin k → Fin S.card} (he : StrictMono e)
    (hr : ∀ d, d ∈ Set.range e ↔ d ∈ S.visibleCells f) {i : Fin k}
    {j : Fin (S.comap f).card} (hij : (i : ℕ) = j) : e i = S.cellMap f j := by
  obtain rfl := S.card_visibleCells_eq_of_strictMono f he hr
  rw [Fin.ext hij, orderEmbOfFin_unique rfl (fun x ↦ (hr _).mp ⟨x, rfl⟩) he]
  rfl

/-- The cell map is a lower embedding of the restriction into the scheme. -/
theorem isLowerEmbedding_comap :
    (S.comap f).toCellScheme.IsLowerEmbedding S.toCellScheme (S.cellMap f) :=
  (CellScheme.IsLowerEmbedding.comap _ f).comp (CellScheme.IsLowerEmbedding.reindex _ _)

/-- The ground set of the restriction is the preimage of the ground set. -/
@[simp] theorem comap_ground :
    (S.comap f).toCellScheme.ground = S.toCellScheme.ground.preimage f f.injective.injOn := rfl

/-- A set is a face of the restriction exactly when its image is a face. -/
@[simp] theorem mem_comap_faces {C : Finset (Fin m)} :
    C ∈ (S.comap f).toCellScheme.faces ↔ C.map f ∈ S.toCellScheme.faces :=
  CellScheme.mem_comap_faces _ f

/-- The scope of a cell of the restriction is the preimage of the scope of its cell. -/
@[simp] theorem comap_scope (i : Fin (S.comap f).card) :
    (S.comap f).toCellScheme.scope i =
      (S.toCellScheme.scope (S.cellMap f i)).preimage f f.injective.injOn := rfl

/-- The grade of a cell of the restriction is the grade of its cell. -/
@[simp] theorem comap_grade (i : Fin (S.comap f).card) :
    (S.comap f).toCellScheme.grade i = S.toCellScheme.grade (S.cellMap f i) := rfl

/-- The row of a cell of the restriction is the row of its cell. -/
@[simp] theorem comap_row (s : Fin (S.comap f).card)
    (t : (S.comap f).toCellScheme.below ((S.comap f).toCellScheme.gradedIndex s)) :
    (S.comap f).rows.row s t = S.rows.row (S.cellMap f s)
      ⟨S.cellMap f t.1, ((S.isLowerEmbedding_comap f).le_iff t s).mpr t.2⟩ := rfl

/-- The scope of a cell of the restriction maps onto the scope of its cell. -/
theorem map_comap_scope (i : Fin (S.comap f).card) :
    ((S.comap f).toCellScheme.scope i).map f = S.toCellScheme.scope (S.cellMap f i) := by
  rw [comap_scope]
  exact map_preimage_eq_of_subset_range (mem_visibleCells.mp (S.cellMap_mem f i))

/-- The graded index of a cell of the restriction maps onto that of its cell. -/
theorem map_comap_gradedIndex (i : Fin (S.comap f).card) :
    Prod.map (Finset.map f) id ((S.comap f).toCellScheme.gradedIndex i) =
      S.toCellScheme.gradedIndex (S.cellMap f i) :=
  Prod.ext (S.map_comap_scope f i) rfl

/-- The cell map of the restriction along `f` maps the cells below a pair onto the cells below its
image. -/
theorem image_cellMap_below (X : Finset (Fin m) × ℕ) :
    S.cellMap f '' (S.comap f).toCellScheme.below X =
      S.toCellScheme.below (Prod.map (Finset.map f) id X) := by
  have h : S.cellMap f '' (S.comap f).toCellScheme.below X =
      Subtype.val '' (S.cellEquiv f '' (S.cellEquiv f ⁻¹' (S.toCellScheme.comap f).below X)) := by
    rw [Set.image_image]
    rfl
  rw [h, Equiv.image_preimage]
  exact CellScheme.image_val_below_comap _ f X

/-- The graded faces of the restriction are those whose image is a graded face. -/
theorem mem_gradedFaces_comap {X : Finset (Fin m) × ℕ} :
    X ∈ (S.comap f).toCellScheme.gradedFaces ↔
      Prod.map (Finset.map f) id X ∈ S.toCellScheme.gradedFaces :=
  CellScheme.mem_gradedFaces_comap _ f

/-! ### Functoriality of restriction -/

/-- Restriction along the identity is the identity. -/
@[simp] theorem comap_refl : S.comap (Function.Embedding.refl (Fin n)) = S := by
  have hr : ∀ d, d ∈ Set.range (id : Fin S.card → Fin S.card) ↔
      d ∈ S.visibleCells (Function.Embedding.refl (Fin n)) := fun d ↦ by
    simp [Function.Embedding.coe_refl]
  have key {i : Fin (S.comap _).card} {j : Fin S.card} (h : (i : ℕ) = j) :
      S.cellMap (Function.Embedding.refl (Fin n)) i = j :=
    (S.cellMap_eq_of_strictMono _ strictMono_id hr h.symm).symm
  refine ext ((S.comap_card _).trans (S.card_visibleCells_eq_of_strictMono _ strictMono_id hr))
    ?_ ?_ ?_ ?_ ?_
  · ext; simp
  · ext; simp
  · intro i j h; ext; simp [key h]
  · intro i j h; simp [key h]
  · intro s s' t t' hs ht
    exact S.rows.row_congr (key hs) (key ht)

/-- The composite of the cell maps of two restrictions enumerates the cells visible through the
composite embedding. -/
theorem mem_range_cellMap_comp_iff (d : Fin S.card) :
    d ∈ Set.range (fun i ↦ S.cellMap f ((S.comap f).cellMap g i)) ↔
      d ∈ S.visibleCells (g.trans f) := by
  rw [Set.mem_range, mem_visibleCells, Function.Embedding.coe_trans, Set.range_comp]
  constructor
  · rintro ⟨i, rfl⟩
    have h := mem_visibleCells.mp ((S.comap f).cellMap_mem g i)
    rw [← map_comap_scope, coe_map]
    exact Set.image_mono h
  · intro hd
    have hdf : d ∈ Set.range (S.cellMap f) := by
      rw [range_cellMap]
      exact mem_visibleCells.mpr (hd.trans (Set.image_subset_range _ _))
    obtain ⟨j, rfl⟩ := hdf
    have hj : j ∈ Set.range ((S.comap f).cellMap g) := by
      rw [range_cellMap, mem_coe, mem_visibleCells, comap_scope, coe_preimage]
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hd hx
      exact f.injective hyx ▸ hy
    obtain ⟨i, rfl⟩ := hj
    exact ⟨i, rfl⟩

/-- **Composition of restrictions**: restricting along `f` and then along `g` is restricting
along the composite `g.trans f`.  No guard is needed at the level of data. -/
@[simp] theorem comap_comap : (S.comap f).comap g = S.comap (g.trans f) := by
  have he : StrictMono fun i ↦ S.cellMap f ((S.comap f).cellMap g i) :=
    (S.cellMap f).strictMono.comp ((S.comap f).cellMap g).strictMono
  have hr := S.mem_range_cellMap_comp_iff f g
  have key {i : Fin ((S.comap f).comap g).card} {j : Fin (S.comap (g.trans f)).card}
      (h : (i : ℕ) = j) : S.cellMap f ((S.comap f).cellMap g i) = S.cellMap (g.trans f) j :=
    S.cellMap_eq_of_strictMono _ he hr h
  refine ext ((S.card_visibleCells_eq_of_strictMono _ he hr).symm.trans (S.comap_card _).symm)
    ?_ ?_ ?_ ?_ ?_
  · ext; simp
  · ext; simp [map_map]
  · intro i j h; ext; simp [← key h]
  · intro i j h; simp [← key h]
  · intro s s' t t' hs ht
    exact S.rows.row_congr (key hs) (key ht)

/-! ### Laws -/

/-- The laws of a scheme on `n` points: the ground set is all of `Fin n`, and the cell scheme is
well formed (its faces form a plan and every cell has a graded face as graded index). -/
structure IsWellFormed : Prop where
  /-- The ground set is all of `Fin n`. -/
  ground_eq : S.toCellScheme.ground = univ
  /-- The cell scheme is well formed. -/
  isWellFormed : S.toCellScheme.IsWellFormed

/-- The rows of a scheme are **coded**: every row value is bottom or an ordinal `ω · i + j`
(`i j : ℕ`), that is, lies below `ω ^ 2` [Kni26, §2.5].  The bound `j ≤ k + 1` at a row
of grade `k` is not part of this law. -/
def IsCoded : Prop :=
  ∀ s t, S.rows.row s t < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})

namespace IsWellFormed

variable {S} (hS : S.IsWellFormed)
include hS

/-- The whole ground set is a face. -/
theorem univ_mem_faces : (univ : Finset (Fin n)) ∈ S.toCellScheme.faces :=
  hS.ground_eq ▸ hS.isWellFormed.isPlan.ground_mem

/-- **Restriction to a closed face** of a well-formed scheme is well formed. -/
theorem comap (hf : univ.map f ∈ S.toCellScheme.faces) : (S.comap f).IsWellFormed where
  ground_eq := by ext; simp [hS.ground_eq]
  isWellFormed := (hS.isWellFormed.comap f (by rwa [hS.ground_eq, preimage_univ])).reindex
    (S.cellEquiv f)

end IsWellFormed

/-- The restriction of a scheme with coded rows has coded rows. -/
theorem IsCoded.comap {S : Scheme.{u} n} (hS : S.IsCoded) : (S.comap f).IsCoded :=
  fun _ _ ↦ hS _ _

/-- The restriction of a scheme with consistent rows has consistent rows. -/
theorem isConsistent_comap {S : Scheme.{u} n} (hS : S.rows.IsConsistent) :
    (S.comap f).rows.IsConsistent :=
  hS.comap (S.isLowerEmbedding_comap f)

/-- The restriction of a complete scheme is complete. -/
theorem isComplete_comap {S : Scheme.{u} n} (hS : S.toCellScheme.IsComplete) :
    (S.comap f).toCellScheme.IsComplete :=
  (hS.comap f).reindex (S.cellEquiv f).surjective

end Scheme

end VaughtConjecture
