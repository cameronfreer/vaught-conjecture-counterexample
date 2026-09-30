/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Basic
import VaughtConjecture.Extension.Gluing
import VaughtConjecture.Extension.Merge
import VaughtConjecture.Scheme.Transport
import VaughtConjecture.Stage.Scheme

/-!
# The amalgamated scheme of two coatom schemes

Roadmap, Layer 3 (the coatom extension construction: its constructed finite object, with the
literal face-map restrictions to the two coatoms, and the bountifulness of the rows it builds);
semantic contract, items 2–4.

Fix `m` and two schemes `Sa` and `Sb` on `m + 1` points, placed on the two coatoms of `Fin (m + 2)`:
`Sa` along `Fin.castSuccEmb`, omitting the last point `a`, and `Sb` along
`extendByLast Fin.castSuccEmb`, omitting the point `b = m`.  Their common face is `Fin m`, embedded
in both by `Fin.castSuccEmb`, and the two schemes are assumed to have literally the same
restriction there (`h : Sa.comap c = Sb.comap c`, where `c = Fin.castSuccEmb`).  This is the
situation of [Kni26, §4.3], with `A = Fin (m + 2)`.

The **amalgamated cell scheme** (`amalgamCellScheme h`, [Kni26, Definition 4.3.1]) has

* the cells of `Sa` and the cells of `Sb` outside the common face, merged in an order retaining
  both orders (`Merge`), a cell of the common face occurring once;
* the scopes and grades of the given cells, the scopes moved to `Fin (m + 2)`;
* the faces `univ` and the images of the faces of `Sa` and of `Sb` (the glued plan of the
  recursive step at `a` and `b`);
* the rows of the given cells (`amalgamRows h`).

The inclusions of `Sa` and `Sb` are lower embeddings (`isLowerEmbedding_left`,
`isLowerEmbedding_right`) along which the rows pull back to the given rows
(`comap_amalgamRows_left`, `comap_amalgamRows_right`).  The amalgam has no cell of full scope, so
it is not complete; this file proves its other laws:

* it is well formed when `Sa` and `Sb` are, and the common face is closed in `Sa`
  (`isWellFormed_amalgamCellScheme`): its faces are the glued plan of the recursive step
  (`isPlan_amalgamFaces`), which restricts to the plans of `Sa` and `Sb` on the two coatoms
  (`map_left_mem_amalgamFaces_iff`, `map_right_mem_amalgamFaces_iff`, by
  `Geometry.IsPlan.mem_step_left` and `Geometry.IsPlan.mem_step_right`);
* its rows are coded, and consistent, when those of `Sa` and `Sb` are (`isCoded_amalgamRows`,
  `isConsistent_amalgamRows`);
* every graded face other than those of full scope is the graded index of a cell, when `Sa` and
  `Sb` are complete (`exists_gradedIndex_eq_amalgam`);
* its rows are **bountiful** when those of `Sa` and `Sb` are (`isBountiful_amalgamRows`): this is
  [Kni26, Lemma 4.3.2], by the boundary lift of `VaughtConjecture.Extension.Gluing`.

The completion of the amalgam by cells of full scope, [Kni26, Definition 4.3.14], is not
constructed here.

## Placement

`Geometry.IsPlan.map` belongs in `VaughtConjecture.Geometry.Plan`, beside `IsPlan.preimage`;
`Scheme.scope_eq_of_eq`, `Scheme.grade_eq_of_eq`, `Scheme.row_eq_of_eq`, and
`Scheme.mem_faces_iff_of_eq` in `VaughtConjecture.Stage.Scheme`; and
`CellScheme.IsLowerEmbedding.image_below_gradedIndex` in `VaughtConjecture.Scheme.Cell`.  They
are stated here so that those files are unchanged.

## References

The amalgam is [Kni26, Definition 4.3.1] and its bountifulness [Kni26, Lemma 4.3.2]; the plan
is the amalgamation plan of [Kni26, Definition 2.1.1], for R. W. Knight, *A counterexample to
Vaught's Conjecture using generalised Stone spaces* (draft, 20 February 2026) [Kni26].
-/

universe u

namespace VaughtConjecture

open Finset

/-! ### Plans pushed forward along an embedding -/

/-- A plan pushed forward along an embedding of ground types is a plan on the image. -/
theorem Geometry.IsPlan.map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    {A : Finset α} {P : Finset (Finset α)} (hP : IsPlan A P) :
    IsPlan (A.map f) (P.map (mapEmbedding f).toEmbedding) := by
  induction hP with
  | empty =>
    simpa using IsPlan.empty
  | singleton a =>
    have : ({∅, {a}} : Finset (Finset α)).map (mapEmbedding f).toEmbedding = {∅, {f a}} := by
      simp
    rw [this, map_singleton]
    exact .singleton (f a)
  | @step A a b Q R ha hb hab hQ hR hface hagree ihQ ihR =>
    have hmap : (insert A (Q ∪ R)).map (mapEmbedding f).toEmbedding =
        insert (A.map f) (Q.map (mapEmbedding f).toEmbedding ∪
          R.map (mapEmbedding f).toEmbedding) := by
      simp [map_insert, map_union]
    rw [hmap]
    have hea : (A.map f).erase (f a) = (A.erase a).map f := (map_erase f A a).symm
    have heb : (A.map f).erase (f b) = (A.erase b).map f := (map_erase f A b).symm
    have heab : ((A.map f).erase (f a)).erase (f b) = ((A.erase a).erase b).map f := by
      rw [hea, ← map_erase]
    refine .step (mem_map_of_mem f ha) (mem_map_of_mem f hb) (f.injective.ne hab)
      (hea ▸ ihQ) (heb ▸ ihR) ?_ fun C hC ↦ ?_
    · rw [heab]
      exact mem_map_of_mem _ hface
    · rw [heab, subset_map_iff] at hC
      obtain ⟨C', hC', rfl⟩ := hC
      simp only [mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply,
        map_inj, exists_eq_right]
      exact hagree C' hC'

/-! ### Equal schemes -/

namespace Scheme

variable {n : ℕ} {S T : Scheme.{u} n}

/-- Equal schemes have equal scopes at corresponding cells. -/
theorem scope_eq_of_eq (h : S = T) (i : Fin S.card) :
    S.toCellScheme.scope i = T.toCellScheme.scope (Fin.cast (congrArg Scheme.card h) i) := by
  subst h
  rfl

/-- Equal schemes have equal grades at corresponding cells. -/
theorem grade_eq_of_eq (h : S = T) (i : Fin S.card) :
    S.toCellScheme.grade i = T.toCellScheme.grade (Fin.cast (congrArg Scheme.card h) i) := by
  subst h
  rfl

/-- Equal schemes have equal rows at corresponding cells. -/
theorem row_eq_of_eq (h : S = T) (s : Fin S.card)
    (t : S.toCellScheme.below (S.toCellScheme.gradedIndex s))
    (ht : T.toCellScheme.gradedIndex (Fin.cast (congrArg Scheme.card h) t.1) ≤
      T.toCellScheme.gradedIndex (Fin.cast (congrArg Scheme.card h) s)) :
    S.rows.row s t = T.rows.row (Fin.cast (congrArg Scheme.card h) s)
      ⟨Fin.cast (congrArg Scheme.card h) t.1, ht⟩ := by
  subst h
  rfl

/-- Equal schemes have the same faces. -/
theorem mem_faces_iff_of_eq (h : S = T) {C : Finset (Fin n)} :
    C ∈ S.toCellScheme.faces ↔ C ∈ T.toCellScheme.faces := by
  subst h
  rfl

end Scheme

/-- The image under a lower embedding of the cells below a cell is the set of cells below its
image. -/
theorem CellScheme.IsLowerEmbedding.image_below_gradedIndex {ι κ α β : Type*}
    {E : CellScheme κ β} {D : CellScheme ι α} {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ)
    (s : κ) : φ '' E.below (E.gradedIndex s) = D.below (D.gradedIndex (φ s)) := by
  ext d
  refine ⟨?_, fun hd ↦ ?_⟩
  · rintro ⟨t, ht, rfl⟩
    exact (hφ.le_iff t s).mpr ht
  · obtain ⟨t, rfl⟩ := hφ.mem_range s d hd
    exact ⟨t, (hφ.le_iff t s).mp hd, rfl⟩

namespace Coatom

/-! ### The two coatoms of `Fin (m + 2)` -/

variable {m : ℕ}

/-- The common face of the two coatoms: `Fin m` in `Fin (m + 1)`. -/
abbrev face (m : ℕ) : Fin m ↪ Fin (m + 1) := Fin.castSuccEmb

/-- The coatom of `Fin (m + 2)` omitting the last point. -/
abbrev left (m : ℕ) : Fin (m + 1) ↪ Fin (m + 2) := Fin.castSuccEmb

/-- The coatom of `Fin (m + 2)` omitting the point `m`. -/
abbrev right (m : ℕ) : Fin (m + 1) ↪ Fin (m + 2) := extendByLast (face m)

/-- The two coatoms agree on the common face. -/
theorem trans_left_eq_trans_right : (face m).trans (left m) = (face m).trans (right m) :=
  (castSuccEmb_trans_extendByLast _).symm

/-- A set of points of `Fin (m + 1)` lies in the common face exactly when it omits the last
point. -/
theorem subset_univ_map_iff {S : Finset (Fin (m + 1))} :
    S ⊆ univ.map (face m) ↔ Fin.last m ∉ S := by
  constructor
  · intro hS hl
    obtain ⟨i, -, hi⟩ := mem_map.mp (hS hl)
    exact (Fin.castSucc_lt_last i).ne hi
  · intro hS x hx
    induction x using Fin.lastCases with
    | last => exact absurd hx hS
    | cast i => exact mem_map_of_mem _ (mem_univ i)

/-- The images of a set under the two coatoms agree when the set lies in the common face. -/
theorem map_left_eq_map_right {S : Finset (Fin (m + 1))} (hS : S ⊆ univ.map (face m)) :
    S.map (left m) = S.map (right m) := by
  obtain ⟨T, -, rfl⟩ := subset_map_iff.mp hS
  rw [map_map, map_map, trans_left_eq_trans_right]

/-- The last point of `Fin (m + 2)` is omitted by the first coatom. -/
theorem last_notMem_univ_map_left : Fin.last (m + 1) ∉ univ.map (left m) := by
  simp only [mem_map, mem_univ, true_and, not_exists]
  exact fun i hi ↦ (Fin.castSucc_lt_last i).ne hi

/-- The image under the first coatom of a set lies in the second coatom exactly when the set lies
in the common face. -/
theorem map_left_subset_univ_map_right_iff {S : Finset (Fin (m + 1))} :
    S.map (left m) ⊆ univ.map (right m) ↔ S ⊆ univ.map (face m) := by
  constructor
  · intro hS
    rw [subset_univ_map_iff]
    intro hl
    have := hS (mem_map_of_mem _ hl)
    rw [univ_map_extendByLast, mem_insert, mem_map] at this
    rcases this with h | ⟨y, hy, hyl⟩
    · exact (Fin.castSucc_lt_last _).ne h
    · obtain ⟨i, -, rfl⟩ := mem_map.mp hy
      simp only [Fin.coe_castSuccEmb, Fin.castSucc_inj] at hyl
      exact (Fin.castSucc_lt_last i).ne hyl
  · intro hS
    rw [map_left_eq_map_right hS]
    exact map_subset_map.mpr (subset_univ _)

/-- The image under the second coatom of a set lies in the first coatom exactly when the set lies
in the common face. -/
theorem map_right_subset_univ_map_left_iff {S : Finset (Fin (m + 1))} :
    S.map (right m) ⊆ univ.map (left m) ↔ S ⊆ univ.map (face m) := by
  constructor
  · intro hS
    rw [subset_univ_map_iff]
    intro hl
    have := hS (mem_map_of_mem _ hl)
    rw [extendByLast_last] at this
    exact last_notMem_univ_map_left this
  · intro hS
    rw [← map_left_eq_map_right hS]
    exact map_subset_map.mpr (subset_univ _)

/-- A set of points of `Fin (m + 2)` in both coatoms lies in the image of the common face. -/
theorem subset_map_of_subset_left_right {S : Finset (Fin (m + 2))} (ha : S ⊆ univ.map (left m))
    (hb : S ⊆ univ.map (right m)) : ∃ T : Finset (Fin m), S = (T.map (face m)).map (left m) := by
  obtain ⟨T', -, rfl⟩ := subset_map_iff.mp ha
  have hT' := map_left_subset_univ_map_right_iff.mp hb
  obtain ⟨T, -, rfl⟩ := subset_map_iff.mp hT'
  exact ⟨T, rfl⟩

/-- The images of the two coatoms are the ground set with one point removed. -/
theorem univ_map_left : univ.map (left m) = univ.erase (Fin.last (m + 1)) := by
  ext x
  induction x using Fin.lastCases with
  | last => simp
  | cast i => simp [(Fin.castSucc_lt_last i).ne]

/-- The second coatom omits exactly the point `m`. -/
theorem univ_map_right : univ.map (right m) = univ.erase (Fin.castSucc (Fin.last m)) := by
  ext x
  rw [univ_map_extendByLast, mem_insert, mem_erase, mem_map]
  induction x using Fin.lastCases with
  | last => simp [(Fin.castSucc_lt_last (Fin.last m)).ne']
  | cast i =>
    simp only [Fin.castSucc_inj, (Fin.castSucc_lt_last i).ne, false_or, mem_univ, and_true,
      mem_map, true_and, Fin.coe_castSuccEmb]
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, hy⟩
      rw [← hy]
      exact (Fin.castSucc_injective _).ne (Fin.castSucc_lt_last k).ne
    · intro hi
      induction i using Fin.lastCases with
      | last => exact absurd rfl hi
      | cast k => exact ⟨k.castSucc, ⟨k, rfl⟩, rfl⟩

/-- The common face is the ground set with the two points removed. -/
theorem map_univ_map_face : (univ.map (face m)).map (left m) =
    (univ.erase (Fin.last (m + 1))).erase (Fin.castSucc (Fin.last m)) := by
  ext x
  rw [map_map, mem_map, mem_erase, mem_erase]
  simp only [mem_univ, true_and, and_true, Function.Embedding.trans_apply, Fin.coe_castSuccEmb]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(Fin.castSucc_injective _).ne (Fin.castSucc_lt_last k).ne,
      (Fin.castSucc_lt_last _).ne⟩
  · rintro ⟨h1, h2⟩
    induction x using Fin.lastCases with
    | last => exact absurd rfl h2
    | cast i =>
      induction i using Fin.lastCases with
      | last => exact absurd rfl h1
      | cast k => exact ⟨k, rfl⟩

/-! ### The common face of two coatom schemes -/

section Overlap

variable {Sa Sb : Scheme.{u} (m + 1)} (h : Sa.comap (face m) = Sb.comap (face m))

/-- The cells of `Sb` on the common face, in the order of the corresponding cells of `Sa`. -/
noncomputable def overlap : Fin (Sa.comap (face m)).card ↪o Fin Sb.card :=
  (Fin.castOrderIso (congrArg Scheme.card h)).toOrderEmbedding.trans (Sb.cellMap (face m))

theorem overlap_apply (t : Fin (Sa.comap (face m)).card) :
    overlap h t = Sb.cellMap (face m) (Fin.cast (congrArg Scheme.card h) t) := rfl

/-- A cell of a scheme on `m + 1` points is a cell of the common face exactly when its scope omits
the last point. -/
theorem mem_range_cellMap_face {S : Scheme.{u} (m + 1)} {i : Fin S.card} :
    i ∈ Set.range (S.cellMap (face m)) ↔ Fin.last m ∉ S.toCellScheme.scope i := by
  rw [Scheme.range_cellMap, mem_coe, Scheme.visibleCells, mem_filter, ← subset_univ_map_iff]
  simp

/-- A cell of `Sb` is a cell of the common face exactly when its scope omits the last point. -/
theorem mem_range_overlap {j : Fin Sb.card} :
    j ∈ Set.range (overlap h) ↔ Fin.last m ∉ Sb.toCellScheme.scope j := by
  rw [← mem_range_cellMap_face]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Fin.cast (congrArg Scheme.card h).symm t, by simp [overlap_apply]⟩

/-- Corresponding cells of the common face have the same scope. -/
theorem scope_overlap (t : Fin (Sa.comap (face m)).card) :
    Sa.toCellScheme.scope (Sa.cellMap (face m) t) = Sb.toCellScheme.scope (overlap h t) := by
  rw [← Scheme.map_comap_scope, Scheme.scope_eq_of_eq h t, Scheme.map_comap_scope]
  rfl

/-- Corresponding cells of the common face have the same grade. -/
theorem grade_overlap (t : Fin (Sa.comap (face m)).card) :
    Sa.toCellScheme.grade (Sa.cellMap (face m) t) = Sb.toCellScheme.grade (overlap h t) :=
  Scheme.grade_eq_of_eq h t

/-- Corresponding cells of the common face have the same rows. -/
theorem row_overlap (t t' : Fin (Sa.comap (face m)).card)
    (ha : Sa.toCellScheme.gradedIndex (Sa.cellMap (face m) t') ≤
      Sa.toCellScheme.gradedIndex (Sa.cellMap (face m) t))
    (hb : Sb.toCellScheme.gradedIndex (overlap h t') ≤ Sb.toCellScheme.gradedIndex (overlap h t)) :
    Sa.rows.row (Sa.cellMap (face m) t) ⟨Sa.cellMap (face m) t', ha⟩ =
      Sb.rows.row (overlap h t) ⟨overlap h t', hb⟩ := by
  have ha' : (Sa.comap (face m)).toCellScheme.gradedIndex t' ≤
      (Sa.comap (face m)).toCellScheme.gradedIndex t :=
    ((Sa.isLowerEmbedding_comap (face m)).le_iff t' t).mp ha
  have hb' : (Sb.comap (face m)).toCellScheme.gradedIndex (Fin.cast (congrArg Scheme.card h) t') ≤
      (Sb.comap (face m)).toCellScheme.gradedIndex (Fin.cast (congrArg Scheme.card h) t) :=
    ((Sb.isLowerEmbedding_comap (face m)).le_iff _ _).mp hb
  have := Scheme.row_eq_of_eq h t ⟨t', ha'⟩ hb'
  rwa [Scheme.comap_row, Scheme.comap_row] at this

include h in
/-- Below the common face, the two schemes have the same faces. -/
theorem mem_faces_iff_of_subset {C : Finset (Fin (m + 1))} (hC : C ⊆ univ.map (face m)) :
    C ∈ Sa.toCellScheme.faces ↔ C ∈ Sb.toCellScheme.faces := by
  obtain ⟨T, -, rfl⟩ := subset_map_iff.mp hC
  rw [← Scheme.mem_comap_faces, ← Scheme.mem_comap_faces]
  exact Scheme.mem_faces_iff_of_eq h

end Overlap

/-! ### The amalgamated cell scheme -/

section Amalgam

variable {Sa Sb : Scheme.{u} (m + 1)} (h : Sa.comap (face m) = Sb.comap (face m))

/-- The cells of the amalgam: the cells of `Sa`, and the cells of `Sb` outside the common face,
merged so that both orders are retained. -/
abbrev AmalgamCell := Merge (Sa.cellMap (face m)) (overlap h)

/-- The scope of a cell of the amalgam: the scope of the given cell, moved to `Fin (m + 2)`. -/
def amalgamScope : AmalgamCell h → Finset (Fin (m + 2))
  | .inl i => (Sa.toCellScheme.scope i).map (left m)
  | .inr j _ => (Sb.toCellScheme.scope j).map (right m)

/-- The grade of a cell of the amalgam: the grade of the given cell. -/
def amalgamGrade : AmalgamCell h → ℕ
  | .inl i => Sa.toCellScheme.grade i
  | .inr j _ => Sb.toCellScheme.grade j

variable (Sa Sb) in
/-- The faces of the amalgam: the ground set, and the faces of `Sa` and of `Sb` moved to
`Fin (m + 2)`. -/
def amalgamFaces : Finset (Finset (Fin (m + 2))) :=
  insert univ (Sa.toCellScheme.faces.map (mapEmbedding (left m)).toEmbedding ∪
    Sb.toCellScheme.faces.map (mapEmbedding (right m)).toEmbedding)

/-- The **amalgamated cell scheme** of two coatom schemes [Kni26, Definition 4.3.1]. -/
def amalgamCellScheme : CellScheme (AmalgamCell h) (Fin (m + 2)) where
  ground := univ
  faces := amalgamFaces Sa Sb
  scope := amalgamScope h
  grade := amalgamGrade h

theorem mem_amalgamFaces {C : Finset (Fin (m + 2))} :
    C ∈ amalgamFaces Sa Sb ↔ C = univ ∨ (∃ C' ∈ Sa.toCellScheme.faces, C'.map (left m) = C) ∨
      ∃ C' ∈ Sb.toCellScheme.faces, C'.map (right m) = C := by
  simp [amalgamFaces]

@[simp] theorem amalgamScope_inl (i : Fin Sa.card) :
    (amalgamCellScheme h).scope (.inl i) = (Sa.toCellScheme.scope i).map (left m) := rfl

@[simp] theorem amalgamScope_inr (j : Fin Sb.card) (hj : j ∉ Set.range (overlap h)) :
    (amalgamCellScheme h).scope (.inr j hj) = (Sb.toCellScheme.scope j).map (right m) := rfl

@[simp] theorem amalgamGrade_inl (i : Fin Sa.card) :
    (amalgamCellScheme h).grade (.inl i) = Sa.toCellScheme.grade i := rfl

@[simp] theorem amalgamGrade_inr (j : Fin Sb.card) (hj : j ∉ Set.range (overlap h)) :
    (amalgamCellScheme h).grade (.inr j hj) = Sb.toCellScheme.grade j := rfl

/-- The scope of a cell of `Sb` in the amalgam. -/
theorem amalgamScope_right (j : Fin Sb.card) :
    (amalgamCellScheme h).scope (Merge.rightFun _ _ j) =
      (Sb.toCellScheme.scope j).map (right m) := by
  by_cases hj : j ∈ Set.range (overlap h)
  · obtain ⟨t, rfl⟩ := hj
    rw [Merge.rightFun_eb, amalgamScope_inl, scope_overlap h t,
      map_left_eq_map_right]
    rw [subset_univ_map_iff, ← scope_overlap h t, ← mem_range_cellMap_face]
    exact ⟨t, rfl⟩
  · rw [Merge.rightFun_of_notMem _ _ hj, amalgamScope_inr]

/-- The grade of a cell of `Sb` in the amalgam. -/
theorem amalgamGrade_right (j : Fin Sb.card) :
    (amalgamCellScheme h).grade (Merge.rightFun _ _ j) = Sb.toCellScheme.grade j := by
  by_cases hj : j ∈ Set.range (overlap h)
  · obtain ⟨t, rfl⟩ := hj
    rw [Merge.rightFun_eb, amalgamGrade_inl, grade_overlap h t]
  · rw [Merge.rightFun_of_notMem _ _ hj, amalgamGrade_inr]

/-- A cell of `Sb` outside the common face contains the last point of `Fin (m + 2)`. -/
theorem last_mem_amalgamScope_inr (j : Fin Sb.card) (hj : j ∉ Set.range (overlap h)) :
    Fin.last (m + 1) ∈ (amalgamCellScheme h).scope (.inr j hj) := by
  rw [amalgamScope_inr, ← extendByLast_last (face m)]
  exact mem_map_of_mem _ (not_not.mp ((mem_range_overlap h).not.mp hj))

/-- A cell whose scope lies in the first coatom is a cell of `Sa`. -/
theorem exists_eq_inl_of_scope_subset {x : AmalgamCell h}
    (hx : (amalgamCellScheme h).scope x ⊆ univ.map (left m)) : ∃ i, x = .inl i := by
  rcases x with i | ⟨j, hj⟩
  · exact ⟨i, rfl⟩
  · exact absurd (hx (last_mem_amalgamScope_inr h j hj)) last_notMem_univ_map_left

/-- A cell whose scope lies in the second coatom is a cell of `Sb`. -/
theorem mem_range_right_of_scope_subset {x : AmalgamCell h}
    (hx : (amalgamCellScheme h).scope x ⊆ univ.map (right m)) :
    x ∈ Set.range (Merge.rightFun _ (overlap h)) := by
  rcases x with i | ⟨j, hj⟩
  · have hi := map_left_subset_univ_map_right_iff.mp hx
    obtain ⟨t, rfl⟩ := mem_range_cellMap_face.mpr (subset_univ_map_iff.mp hi)
    exact ⟨overlap h t, Merge.rightFun_eb _ _ t⟩
  · exact ⟨j, Merge.rightFun_of_notMem _ _ hj⟩

/-- **The cells of `Sa` in the amalgam** form a lower embedding. -/
theorem isLowerEmbedding_left :
    Sa.toCellScheme.IsLowerEmbedding (amalgamCellScheme h) Merge.inl where
  injective := (Merge.left _ (overlap h)).injective
  grade_eq _ := rfl
  le_iff s t := by
    simp only [CellScheme.gradedIndex_le_iff, CellScheme.gradedIndex_fst,
      CellScheme.gradedIndex_snd, amalgamScope_inl, amalgamGrade_inl, map_subset_map]
  mem_range t d hd := by
    obtain ⟨i, rfl⟩ := exists_eq_inl_of_scope_subset h
      (hd.1.trans (map_subset_map.mpr (subset_univ _)))
    exact ⟨i, rfl⟩

/-- **The cells of `Sb` in the amalgam** form a lower embedding. -/
theorem isLowerEmbedding_right :
    Sb.toCellScheme.IsLowerEmbedding (amalgamCellScheme h) (Merge.rightFun _ (overlap h)) where
  injective := (Merge.right _ (overlap h)).injective
  grade_eq j := amalgamGrade_right h j
  le_iff s t := by
    simp only [CellScheme.gradedIndex_le_iff, CellScheme.gradedIndex_fst,
      CellScheme.gradedIndex_snd, amalgamScope_right, amalgamGrade_right, map_subset_map]
  mem_range t d hd := by
    refine mem_range_right_of_scope_subset h (hd.1.trans ?_)
    rw [CellScheme.gradedIndex_fst, amalgamScope_right]
    exact map_subset_map.mpr (subset_univ _)

/-- The cells of the amalgam below a pair on the first coatom are the cells of `Sa` below its
preimage. -/
theorem image_left_below (X : Finset (Fin (m + 1)) × ℕ) :
    Merge.inl '' Sa.toCellScheme.below X =
      (amalgamCellScheme h).below (Prod.map (Finset.map (left m)) id X) := by
  ext d
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨map_subset_map.mpr hi.1, hi.2⟩
  · intro hd
    obtain ⟨i, rfl⟩ := exists_eq_inl_of_scope_subset h
      (hd.1.trans (map_subset_map.mpr (subset_univ _)))
    exact ⟨i, ⟨map_subset_map.mp hd.1, hd.2⟩, rfl⟩

/-- The cells of the amalgam below a pair on the second coatom are the cells of `Sb` below its
preimage. -/
theorem image_right_below (X : Finset (Fin (m + 1)) × ℕ) :
    Merge.rightFun _ (overlap h) '' Sb.toCellScheme.below X =
      (amalgamCellScheme h).below (Prod.map (Finset.map (right m)) id X) := by
  ext d
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, ?_⟩
    · change (amalgamCellScheme h).scope _ ⊆ _
      rw [amalgamScope_right]
      exact map_subset_map.mpr hj.1
    · change (amalgamCellScheme h).grade _ ≤ _
      rw [amalgamGrade_right]
      exact hj.2
  · intro hd
    obtain ⟨j, rfl⟩ := mem_range_right_of_scope_subset h
      (hd.1.trans (map_subset_map.mpr (subset_univ _)))
    have hs := hd.1
    have hg := hd.2
    change (amalgamCellScheme h).scope _ ⊆ _ at hs
    change (amalgamCellScheme h).grade _ ≤ _ at hg
    rw [amalgamScope_right] at hs
    rw [amalgamGrade_right] at hg
    exact ⟨j, ⟨map_subset_map.mp hs, hg⟩, rfl⟩

/-- The cells below a cell of `Sb` outside the common face. -/
theorem image_right_below_inr (j : Fin Sb.card) (hj : j ∉ Set.range (overlap h)) :
    Merge.rightFun _ (overlap h) '' Sb.toCellScheme.below (Sb.toCellScheme.gradedIndex j) =
      (amalgamCellScheme h).below ((amalgamCellScheme h).gradedIndex (.inr j hj)) :=
  image_right_below h _

/-- The **rows of the amalgam**: the rows of the given cells. -/
noncomputable def amalgamRows : (amalgamCellScheme h).Rows.{u} where
  row
    | .inl i => Sa.rows.row i ∘ ((isLowerEmbedding_left h).belowEquiv
        ((isLowerEmbedding_left h).image_below_gradedIndex i)).symm
    | .inr j hj => Sb.rows.row j ∘ ((isLowerEmbedding_right h).belowEquiv
        (image_right_below_inr h j hj)).symm

/-- The row of a cell of `Sa` at a cell of `Sa` is its row in `Sa`. -/
theorem amalgamRows_inl_inl (i i' : Fin Sa.card)
    (q : (Merge.inl i' : AmalgamCell h) ∈
      (amalgamCellScheme h).below ((amalgamCellScheme h).gradedIndex (.inl i))) :
    (amalgamRows h).row (.inl i) ⟨.inl i', q⟩ =
      Sa.rows.row i ⟨i', ((isLowerEmbedding_left h).le_iff i' i).mp q⟩ := by
  change Sa.rows.row i (((isLowerEmbedding_left h).belowEquiv _).symm _) = _
  congr 1
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext rfl

/-- The row of a cell of `Sb` outside the common face at a cell of `Sb` is its row in `Sb`. -/
theorem amalgamRows_inr_right (j : Fin Sb.card) (hj : j ∉ Set.range (overlap h))
    (t : Sb.toCellScheme.below (Sb.toCellScheme.gradedIndex j))
    (q : Merge.rightFun _ (overlap h) t.1 ∈
      (amalgamCellScheme h).below ((amalgamCellScheme h).gradedIndex (.inr j hj))) :
    (amalgamRows h).row (.inr j hj) ⟨Merge.rightFun _ (overlap h) t.1, q⟩ = Sb.rows.row j t := by
  change Sb.rows.row j (((isLowerEmbedding_right h).belowEquiv _).symm _) = _
  congr 1
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext rfl

/-- Corresponding cells of the common face have the same graded index. -/
theorem gradedIndex_overlap (t : Fin (Sa.comap (face m)).card) :
    Sa.toCellScheme.gradedIndex (Sa.cellMap (face m) t) =
      Sb.toCellScheme.gradedIndex (overlap h t) :=
  congrArg₂ Prod.mk (scope_overlap h t) (grade_overlap h t)

/-- The rows of the amalgam pull back to the rows of `Sa`. -/
theorem comap_amalgamRows_left :
    (amalgamRows h).comap (isLowerEmbedding_left h) = Sa.rows := by
  ext s t
  exact amalgamRows_inl_inl h s t.1 _

/-- The rows of the amalgam pull back to the rows of `Sb`. -/
theorem comap_amalgamRows_right :
    (amalgamRows h).comap (isLowerEmbedding_right h) = Sb.rows := by
  ext s t
  rw [CellScheme.Rows.comap_row]
  by_cases hs : s ∈ Set.range (overlap h)
  · obtain ⟨τ, rfl⟩ := hs
    -- The cell `t` lies on the common face as well.
    obtain ⟨τ', hτ'⟩ : t.1 ∈ Set.range (overlap h) :=
      (mem_range_overlap h).mpr fun hl ↦ (mem_range_overlap h).mp ⟨τ, rfl⟩ (t.2.1 hl)
    have hle : Sa.toCellScheme.gradedIndex (Sa.cellMap (face m) τ') ≤
        Sa.toCellScheme.gradedIndex (Sa.cellMap (face m) τ) := by
      rw [gradedIndex_overlap h, gradedIndex_overlap h, hτ']
      exact t.2
    have hl : Merge.rightFun _ (overlap h) t.1 =
        (.inl (Sa.cellMap (face m) τ') : AmalgamCell h) := by
      rw [← hτ', Merge.rightFun_eb]
    rw [CellScheme.Rows.row_congr (amalgamRows h) (Merge.rightFun_eb _ _ τ)
      (t' := ⟨(.inl (Sa.cellMap (face m) τ') : AmalgamCell h),
        (CellScheme.mem_below _).mpr (((isLowerEmbedding_left h).le_iff _ _).mpr hle)⟩) hl,
      amalgamRows_inl_inl, row_overlap h τ τ' _ (by rw [hτ']; exact t.2)]
    exact CellScheme.Rows.row_congr _ rfl hτ'
  · rw [CellScheme.Rows.row_congr (amalgamRows h) (Merge.rightFun_of_notMem _ _ hs)
      (t' := ⟨Merge.rightFun _ _ t.1, by
        rw [← Merge.rightFun_of_notMem _ _ hs]
        exact ((isLowerEmbedding_right h).le_iff _ _).mpr t.2⟩) rfl]
    exact amalgamRows_inr_right h s hs t _

/-! ### The laws of the amalgam -/

include h in
/-- A face of the amalgam inside the first coatom is a face of `Sa`, moved. -/
theorem exists_face_left {C : Finset (Fin (m + 2))} (hC : C ∈ amalgamFaces Sa Sb)
    (hCa : C ⊆ univ.map (left m)) : ∃ C' ∈ Sa.toCellScheme.faces, C'.map (left m) = C := by
  rcases mem_amalgamFaces.mp hC with rfl | hC | ⟨C', hC', rfl⟩
  · exact absurd (hCa (mem_univ _)) last_notMem_univ_map_left
  · exact hC
  · have hsub := map_right_subset_univ_map_left_iff.mp hCa
    exact ⟨C', (mem_faces_iff_of_subset h hsub).mpr hC', map_left_eq_map_right hsub⟩

include h in
/-- A face of the amalgam inside the second coatom is a face of `Sb`, moved. -/
theorem exists_face_right {C : Finset (Fin (m + 2))} (hC : C ∈ amalgamFaces Sa Sb)
    (hCb : C ⊆ univ.map (right m)) : ∃ C' ∈ Sb.toCellScheme.faces, C'.map (right m) = C := by
  rcases mem_amalgamFaces.mp hC with rfl | ⟨C', hC', rfl⟩ | hC
  · refine absurd (hCb (mem_univ (Fin.castSucc (Fin.last m)))) ?_
    rw [univ_map_right]
    exact notMem_erase _ _
  · have hsub := map_left_subset_univ_map_right_iff.mp hCb
    exact ⟨C', (mem_faces_iff_of_subset h hsub).mp hC', (map_left_eq_map_right hsub).symm⟩
  · exact hC

/-- Every face of the amalgam other than the ground set lies in one of the two coatoms. -/
theorem subset_or_subset_of_mem_amalgamFaces {C : Finset (Fin (m + 2))}
    (hC : C ∈ amalgamFaces Sa Sb) (hne : C ≠ univ) :
    C ⊆ univ.map (left m) ∨ C ⊆ univ.map (right m) := by
  rcases mem_amalgamFaces.mp hC with rfl | ⟨C', -, rfl⟩ | ⟨C', -, rfl⟩
  · exact absurd rfl hne
  · exact Or.inl (map_subset_map.mpr (subset_univ _))
  · exact Or.inr (map_subset_map.mpr (subset_univ _))

/-- No cell of the amalgam has the full scope. -/
theorem amalgamScope_ne_univ (x : AmalgamCell h) : (amalgamCellScheme h).scope x ≠ univ := by
  rcases x with i | ⟨j, hj⟩
  · intro he
    have := mem_univ (Fin.last (m + 1))
    rw [← he, amalgamScope_inl] at this
    exact last_notMem_univ_map_left (map_subset_map.mpr (subset_univ _) this)
  · intro he
    have := mem_univ (Fin.castSucc (Fin.last m))
    rw [← he, amalgamScope_inr] at this
    have h' := map_subset_map.mpr (subset_univ (Sb.toCellScheme.scope j)) this
    rw [univ_map_right] at h'
    exact notMem_erase _ _ h'

/-- The faces of `Sa`, moved to the first coatom, form a plan on it. -/
theorem isPlan_map_left (hSa : Sa.IsWellFormed) :
    Geometry.IsPlan (univ.erase (Fin.last (m + 1)))
      (Sa.toCellScheme.faces.map (mapEmbedding (left m)).toEmbedding) := by
  have hP := hSa.isWellFormed.isPlan
  rw [hSa.ground_eq] at hP
  rw [← univ_map_left]
  exact hP.map (left m)

/-- The faces of `Sb`, moved to the second coatom, form a plan on it. -/
theorem isPlan_map_right (hSb : Sb.IsWellFormed) :
    Geometry.IsPlan (univ.erase (Fin.castSucc (Fin.last m)))
      (Sb.toCellScheme.faces.map (mapEmbedding (right m)).toEmbedding) := by
  have hP := hSb.isWellFormed.isPlan
  rw [hSb.ground_eq] at hP
  rw [← univ_map_right]
  exact hP.map (right m)

include h in
/-- Below the common face, the faces of `Sa` moved to the first coatom and the faces of `Sb`
moved to the second coatom are the same. -/
theorem mem_map_left_iff_mem_map_right {C : Finset (Fin (m + 2))}
    (hC : C ⊆ (univ.erase (Fin.last (m + 1))).erase (Fin.castSucc (Fin.last m))) :
    C ∈ Sa.toCellScheme.faces.map (mapEmbedding (left m)).toEmbedding ↔
      C ∈ Sb.toCellScheme.faces.map (mapEmbedding (right m)).toEmbedding := by
  rw [← map_univ_map_face, subset_map_iff] at hC
  obtain ⟨C', hC', rfl⟩ := hC
  have h1 : C'.map (left m) ∈ Sa.toCellScheme.faces.map (mapEmbedding (left m)).toEmbedding ↔
      C' ∈ Sa.toCellScheme.faces :=
    mem_map' (mapEmbedding (left m)).toEmbedding
  have h2 : C'.map (left m) ∈ Sb.toCellScheme.faces.map (mapEmbedding (right m)).toEmbedding ↔
      C' ∈ Sb.toCellScheme.faces := by
    rw [map_left_eq_map_right hC']
    exact mem_map' (mapEmbedding (right m)).toEmbedding
  rw [h1, h2]
  exact mem_faces_iff_of_subset h hC'

include h in
/-- **The faces of the amalgam form a plan**: the glued plan of the recursive step at the last
point and the point `m`, from the plans of `Sa` and `Sb` moved to the two coatoms. -/
theorem isPlan_amalgamFaces (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    (hf : univ.map (face m) ∈ Sa.toCellScheme.faces) :
    Geometry.IsPlan univ (amalgamFaces Sa Sb) := by
  refine Geometry.IsPlan.step (mem_univ _) (mem_univ _) (Fin.castSucc_lt_last _).ne'
    (isPlan_map_left hSa) (isPlan_map_right hSb) ?_ fun C hC ↦ mem_map_left_iff_mem_map_right h hC
  rw [← map_univ_map_face]
  exact mem_map_of_mem _ hf

include h in
/-- A set of points of the first coatom is a face of the amalgam exactly when it is a face of `Sa`,
moved: the glued plan restricts to the plan of `Sa` on the first coatom. -/
theorem map_left_mem_amalgamFaces_iff (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    {C : Finset (Fin (m + 1))} : C.map (left m) ∈ amalgamFaces Sa Sb ↔ C ∈ Sa.toCellScheme.faces :=
  (Geometry.IsPlan.mem_step_left (mem_univ _) (isPlan_map_left hSa) (isPlan_map_right hSb)
    (fun _ ↦ mem_map_left_iff_mem_map_right h)
    (univ_map_left (m := m) ▸ map_subset_map.mpr (subset_univ C))).trans
    (mem_map' (mapEmbedding (left m)).toEmbedding)

include h in
/-- A set of points of the second coatom is a face of the amalgam exactly when it is a face of
`Sb`, moved: the glued plan restricts to the plan of `Sb` on the second coatom. -/
theorem map_right_mem_amalgamFaces_iff (hSa : Sa.IsWellFormed) {C : Finset (Fin (m + 1))} :
    C.map (right m) ∈ amalgamFaces Sa Sb ↔ C ∈ Sb.toCellScheme.faces :=
  (Geometry.IsPlan.mem_step_right (mem_univ _) (isPlan_map_left hSa)
    (fun _ ↦ mem_map_left_iff_mem_map_right h)
    (univ_map_right (m := m) ▸ map_subset_map.mpr (subset_univ C))).trans
    (mem_map' (mapEmbedding (right m)).toEmbedding)

/-- **The amalgam is well formed**: its faces form the glued plan of the recursive step at the
last point and the point `m`, and every cell has a graded face as graded index. -/
theorem isWellFormed_amalgamCellScheme (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    (hf : univ.map (face m) ∈ Sa.toCellScheme.faces) : (amalgamCellScheme h).IsWellFormed where
  finite := inferInstance
  isPlan := isPlan_amalgamFaces h hSa hSb hf
  gradedIndex_mem x := by
    rcases x with i | ⟨j, hj⟩
    · refine ⟨mem_insert_of_mem (mem_union_left _ ?_), hSa.isWellFormed.grade_pos i, ?_⟩
      · exact mem_map_of_mem _ (hSa.isWellFormed.scope_mem i)
      · change Sa.toCellScheme.grade i ≤ #((Sa.toCellScheme.scope i).map (left m))
        rw [card_map]
        exact hSa.isWellFormed.grade_le_card i
    · refine ⟨mem_insert_of_mem (mem_union_right _ ?_), hSb.isWellFormed.grade_pos j, ?_⟩
      · exact mem_map_of_mem _ (hSb.isWellFormed.scope_mem j)
      · change Sb.toCellScheme.grade j ≤ #((Sb.toCellScheme.scope j).map (right m))
        rw [card_map]
        exact hSb.isWellFormed.grade_le_card j

/-- The rows of the amalgam are coded when those of `Sa` and `Sb` are. -/
theorem isCoded_amalgamRows (hSa : Sa.IsCoded) (hSb : Sb.IsCoded) (s : AmalgamCell h)
    (t : (amalgamCellScheme h).below ((amalgamCellScheme h).gradedIndex s)) :
    (amalgamRows h).row s t < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  rcases s with i | ⟨j, hj⟩
  · exact hSa i _
  · exact hSb j _

/-- **The rows of the amalgam are consistent** when those of `Sa` and `Sb` are. -/
theorem isConsistent_amalgamRows (hSa : Sa.rows.IsConsistent) (hSb : Sb.rows.IsConsistent) :
    (amalgamRows h).IsConsistent := by
  rintro (i | ⟨j, hj⟩)
  · refine (CellScheme.Rows.isLawfulBelow_comap_iff (isLowerEmbedding_left h)
      ((isLowerEmbedding_left h).image_below_gradedIndex i)).mp ?_
    rw [comap_amalgamRows_left]
    convert hSa i using 1
    funext t
    change Sa.rows.row i (((isLowerEmbedding_left h).belowEquiv
      ((isLowerEmbedding_left h).image_below_gradedIndex i)).symm
        (((isLowerEmbedding_left h).belowEquiv
          ((isLowerEmbedding_left h).image_below_gradedIndex i)) t)) = _
    rw [Equiv.symm_apply_apply]
  · refine (CellScheme.Rows.isLawfulBelow_comap_iff (isLowerEmbedding_right h)
      (image_right_below_inr h j hj)).mp ?_
    rw [comap_amalgamRows_right]
    convert hSb j using 1
    funext t
    change Sb.rows.row j
      (((isLowerEmbedding_right h).belowEquiv (image_right_below_inr h j hj)).symm
        (((isLowerEmbedding_right h).belowEquiv (image_right_below_inr h j hj)) t)) = _
    rw [Equiv.symm_apply_apply]

/-- The rows of the amalgam lift capped between graded faces inside the first coatom when those of
`Sa` are bountiful. -/
theorem cappedLift_left (hSa : Sa.rows.IsBountiful) {X Y : Finset (Fin (m + 1)) × ℕ}
    (hX : X ∈ Sa.toCellScheme.gradedFaces) (hY : Y ∈ Sa.toCellScheme.gradedFaces) (hXY : X ≤ Y) :
    (amalgamRows h).CappedLift (X := Prod.map (Finset.map (left m)) id X)
      (Y := Prod.map (Finset.map (left m)) id Y) ⟨map_subset_map.mpr hXY.1, hXY.2⟩ := by
  refine CellScheme.Rows.CappedLift.of_comap (isLowerEmbedding_left h) (image_left_below h X)
    (image_left_below h Y) le_rfl (h' := hXY) ?_
  rw [comap_amalgamRows_left]
  exact hSa hX hY hXY

/-- The rows of the amalgam lift capped between graded faces inside the second coatom when those
of `Sb` are bountiful. -/
theorem cappedLift_right (hSb : Sb.rows.IsBountiful) {X Y : Finset (Fin (m + 1)) × ℕ}
    (hX : X ∈ Sb.toCellScheme.gradedFaces) (hY : Y ∈ Sb.toCellScheme.gradedFaces) (hXY : X ≤ Y) :
    (amalgamRows h).CappedLift (X := Prod.map (Finset.map (right m)) id X)
      (Y := Prod.map (Finset.map (right m)) id Y) ⟨map_subset_map.mpr hXY.1, hXY.2⟩ := by
  refine CellScheme.Rows.CappedLift.of_comap (isLowerEmbedding_right h) (image_right_below h X)
    (image_right_below h Y) le_rfl (h' := hXY) ?_
  rw [comap_amalgamRows_right]
  exact hSb hX hY hXY

/-- **The rows of the amalgam are bountiful** when those of `Sa` and `Sb` are
[Kni26, Lemma 4.3.2]: below the proper faces the lifts are those of `Sa` and `Sb`, and the lifts
to the full face are boundary lifts, since no cell has the full scope. -/
theorem isBountiful_amalgamRows (hSa : Sa.IsWellFormed) (hSb : Sb.IsWellFormed)
    (hf : univ.map (face m) ∈ Sa.toCellScheme.faces) (hSaB : Sa.rows.IsBountiful)
    (hSbB : Sb.rows.IsBountiful) : (amalgamRows h).IsBountiful := by
  have hD := isWellFormed_amalgamCellScheme h hSa hSb hf
  have hua : univ.map (left m) ∈ amalgamFaces Sa Sb :=
    mem_insert_of_mem (mem_union_left _ (mem_map_of_mem _ hSa.univ_mem_faces))
  have hub : univ.map (right m) ∈ amalgamFaces Sa Sb :=
    mem_insert_of_mem (mem_union_right _ (mem_map_of_mem _ hSb.univ_mem_faces))
  refine CellScheme.Rows.isBountiful_of_coatoms_of_scope_ne (A := univ)
    (a := Fin.last (m + 1)) (b := Fin.castSucc (Fin.last m)) hD (mem_univ _) (mem_univ _)
    (fun B hB hne ↦ ?_) (univ_map_left ▸ hua) (univ_map_right ▸ hub) ?_ ?_
    (amalgamScope_ne_univ h)
  · rw [← univ_map_left, ← univ_map_right]
    exact subset_or_subset_of_mem_amalgamFaces hB hne
  · rw [← map_univ_map_face]
    exact mem_insert_of_mem (mem_union_left _ (mem_map_of_mem _ hf))
  · intro X Y hX hY hXY hYne
    rcases subset_or_subset_of_mem_amalgamFaces hY.1 hYne with hYa | hYb
    · obtain ⟨Y', hY', hYe⟩ := exists_face_left h hY.1 hYa
      obtain ⟨X', hX', hXe⟩ := exists_face_left h hX.1 (hXY.1.trans hYa)
      obtain ⟨X1, X2⟩ := X
      obtain ⟨Y1, Y2⟩ := Y
      simp only at hYe hXe hXY hX hY
      subst hYe hXe
      have hXY' : (X', X2) ≤ (Y', Y2) := ⟨map_subset_map.mp hXY.1, hXY.2⟩
      exact cappedLift_left h hSaB ⟨hX', hX.2.1, by simpa using hX.2.2⟩
        ⟨hY', hY.2.1, by simpa using hY.2.2⟩ hXY'
    · obtain ⟨Y', hY', hYe⟩ := exists_face_right h hY.1 hYb
      obtain ⟨X', hX', hXe⟩ := exists_face_right h hX.1 (hXY.1.trans hYb)
      obtain ⟨X1, X2⟩ := X
      obtain ⟨Y1, Y2⟩ := Y
      simp only at hYe hXe hXY hX hY
      subst hYe hXe
      have hXY' : (X', X2) ≤ (Y', Y2) := ⟨map_subset_map.mp hXY.1, hXY.2⟩
      exact cappedLift_right h hSbB ⟨hX', hX.2.1, by simpa using hX.2.2⟩
        ⟨hY', hY.2.1, by simpa using hY.2.2⟩ hXY'

/-- **Completeness away from the full face**: when `Sa` and `Sb` are complete, every graded face
of the amalgam whose face is not the ground set is the graded index of a cell. -/
theorem exists_gradedIndex_eq_amalgam (hSaC : Sa.toCellScheme.IsComplete)
    (hSbC : Sb.toCellScheme.IsComplete) {X : Finset (Fin (m + 2)) × ℕ}
    (hX : X ∈ (amalgamCellScheme h).gradedFaces) (hne : X.1 ≠ univ) :
    ∃ d, (amalgamCellScheme h).gradedIndex d = X := by
  obtain ⟨X1, X2⟩ := X
  rcases subset_or_subset_of_mem_amalgamFaces hX.1 hne with hXa | hXb
  · obtain ⟨X', hX', rfl⟩ := exists_face_left h hX.1 hXa
    obtain ⟨i, hi⟩ := hSaC (X', X2) ⟨hX', hX.2.1, by simpa using hX.2.2⟩
    have hs : Sa.toCellScheme.scope i = X' := congrArg Prod.fst hi
    have hg : Sa.toCellScheme.grade i = X2 := congrArg Prod.snd hi
    refine ⟨.inl i, Prod.ext ?_ hg⟩
    change (Sa.toCellScheme.scope i).map (left m) = X'.map (left m)
    rw [hs]
  · obtain ⟨X', hX', rfl⟩ := exists_face_right h hX.1 hXb
    obtain ⟨j, hj⟩ := hSbC (X', X2) ⟨hX', hX.2.1, by simpa using hX.2.2⟩
    have hs : Sb.toCellScheme.scope j = X' := congrArg Prod.fst hj
    have hg : Sb.toCellScheme.grade j = X2 := congrArg Prod.snd hj
    refine ⟨Merge.rightFun _ _ j, Prod.ext ?_ ?_⟩
    · change (amalgamCellScheme h).scope _ = X'.map (right m)
      rw [amalgamScope_right, hs]
    · change (amalgamCellScheme h).grade _ = X2
      rw [amalgamGrade_right, hg]

end Amalgam

end Coatom

end VaughtConjecture
