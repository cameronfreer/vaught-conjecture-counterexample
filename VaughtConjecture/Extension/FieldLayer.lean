/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrbitCode
import VaughtConjecture.Extension.OwnerCappedLift

/-!
# The canonical field layer

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities: one layer of cells of full
scope over the amalgam, with the cap preserved on every auxiliary cell); semantic contract,
item 3.

Let `S` be a scheme on `n` points none of whose cells lies above `(univ, k)`.  The **field layer**
of `S` at grade `k` appends to `S` one cell of scope `univ` and grade `k` for each entry of a
finite catalogue of labellings of the cells of `S`; the row of a new cell reads its catalogue entry
on the old cells and, on the new cells, an agreement height of two catalogue entries.  This file
builds the **canonical field layer** (`Scheme.fieldLayer`), whose catalogue consists of
orbit-canonical labellings, and proves its laws and the extensions through the new cells.  The old
cells may have any grade: those of grade above `k` (not below `(univ, k)`) are kept and not read
by the new rows, and those of grade below `k` are read through the orbit code.  When no old cell
has a grade below `k`, the extensions from the boundary asked by the one-grade lift
(`CellScheme.Rows.cappedLift_of_boundary`) are proved here; with old cells of lower grades, only
the extension through the new cells is proved here, at caps short at `k`, and the extension from
the boundary, for the short-cap form `CellScheme.Rows.cappedLift_of_boundary_short`, is assembled
where the boundary is known (at arity one, in `VaughtConjecture.Extension.SmallArityOne`).  Off
the full grade, `S` is a source prefix of its field layer (`Scheme.isSourcePrefix_fieldLayer`).
The scalar part is in `VaughtConjecture.Extension.CanonicalCode` and
`VaughtConjecture.Extension.OrbitCode`.

**Appending cells of full scope** (`Scheme.appendFullCells S k M r h`, an `abbrev`, for the reason
recorded at `Scheme.appendFullCell`): the cells of `S` along `Fin.castAdd`, then `M` cells of scope
`univ` and grade `k` along `Fin.natAdd`, the `i`-th with row `r i`.  The old cells form a lower
embedding along which the rows pull back to those of `S`; below a pair not above `(univ, k)`
lawfulness is lawfulness in `S`; a labelling is lawful when it is lawful on the old cells and its
locality and availability hold at the new cells; consistency, well-formedness and coding pass to
the appended scheme.

**The canonical field layer** (`Scheme.fieldLayer S k hS`).  The **canonical catalogue**
(`Scheme.catalogue S k`) is the set of lawful labellings of the cells of `S` that are bottom at the
cells of grade above `k` and fixed by the orbit code (`Label.orbitCode`); they take values in the
code grid with block bound `2 N` for `N` cells, so it is finite.  The **splice at `k`** of a
labelling `p` with bottom (`CellScheme.splice`: `p` at the cells of grade at most `k`, bottom
above) is lawful when `p` is lawful below `(univ, k)` (`Scheme.isLawful_splice_bot`), and its orbit
code is an entry (`Scheme.orbitCode_splice_bot_mem_catalogue`).  The row of the new cell of an
entry `a` is its **field row** (`Scheme.fieldRow`): `a` on the old cells, the agreement height of
`a` and `b` in the grid with block bound `2 N + 2` at the cell of `b`, and the ceiling
`ω * (2 N + 2) + k` of the grid at its own cell.

* The field row of every entry is a lawful section of the layer (`Scheme.isLawful_fieldRow`): on
  the old cells it is the entry; at a new cell its locality is the identity capped at the agreement
  height, by the ultrametric inequality; availability holds at its own cell.  So the layer is
  consistent (`Scheme.isConsistent_fieldLayer`); it is well formed, coded, and its new rows are
  short at `k` and never the formal top.
* **Extension at the cap `⊥`** (`Scheme.exists_isLawfulBelow_fieldLayer`,
  `Scheme.exists_isLawful_fieldLayer`): every labelling lawful below `(univ, k)` extends to one
  lawful below `(univ, k)` in the layer, by the field row of the orbit code of its splice, read
  by the orbit decoder at the least grid point, which reads the old cells literally because the
  natural strip is kept; a lawful section of `S` extends to a lawful section of the layer.
* **Extension at a positive cap** (`Scheme.exists_extension_fieldLayer`): a labelling lawful below
  `(univ, k)` that agrees with an entry `a` capped at `h` (self-visible at `k`, `⊥ < h`) on the
  cells of grade at most `k` extends, unchanged there, to a labelling lawful below `(univ, k)` in
  the layer that agrees with the field row of `a` capped at `h` at every cell below `(univ, k)`.
  The extension is the field row of the orbit code `b` of the splice, read by its orbit decoder
  at `h`: relative room gives the agreement of `b` with `a` capped at `h`, the agreement heights
  follow, and the field row of `a` is the lawful companion of the positive-cap transport
  (`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`).  It holds when `h` is **short** at `k` (relative
  room of the orbit code), or at every positive cap when no old cell has a grade below `k` (the
  orbit code is then the canonical code, with relative room at every cap).
* **Extension from the boundary** (`Scheme.extendsFromBoundary_bot_fieldLayer`,
  `Scheme.extendsFromBoundary_fieldLayer`): for pairs `U`, `V` below one of which lies every old
  cell of grade at most `k`, a labelling lawful below `U` and `V` is lawful below `(univ, k)` on
  the old cells (`Scheme.isLawfulBelow_castAdd_of_boundary`), and the two extensions above give the
  extension from the boundary at the cap `⊥`, and at every positive cap along every new row when no
  old cell has a grade below `k`.

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion of [Kni26, Definition 4.3.14] has the same shape (cells of full scope indexed by
patterns of the cells below, rows between them given by meet heights); its catalogue of efficient
stacks is not the canonical catalogue here.  Witnesses are [Kni26, Definition 2.3.9], lawful
sections [Kni26, Definition 2.5.4], and bountifulness [Kni26, Definition 2.5.14].
-/

universe u

/-! ### Appending cells of full scope -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k M : ℕ)

/-- The cell scheme of `S` with `M` more cells, last, of scope `univ` and grade `k`. -/
def appendFullCellsScheme : CellScheme (Fin (S.card + M)) (Fin n) where
  ground := S.toCellScheme.ground
  faces := S.toCellScheme.faces
  scope := Fin.append S.toCellScheme.scope fun _ ↦ univ
  grade := Fin.append S.toCellScheme.grade fun _ ↦ k

/-- An old cell keeps its scope. -/
@[simp] theorem appendFullCellsScheme_scope_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).scope (Fin.castAdd M d) = S.toCellScheme.scope d :=
  Fin.append_left (u := S.toCellScheme.scope) (v := fun _ ↦ univ) d

/-- A new cell has full scope. -/
@[simp] theorem appendFullCellsScheme_scope_natAdd (i : Fin M) :
    (S.appendFullCellsScheme k M).scope (Fin.natAdd S.card i) = univ :=
  Fin.append_right (u := S.toCellScheme.scope) (v := fun _ ↦ univ) i

/-- An old cell keeps its grade. -/
@[simp] theorem appendFullCellsScheme_grade_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).grade (Fin.castAdd M d) = S.toCellScheme.grade d :=
  Fin.append_left (u := S.toCellScheme.grade) (v := fun _ ↦ k) d

/-- A new cell has grade `k`. -/
@[simp] theorem appendFullCellsScheme_grade_natAdd (i : Fin M) :
    (S.appendFullCellsScheme k M).grade (Fin.natAdd S.card i) = k :=
  Fin.append_right (u := S.toCellScheme.grade) (v := fun _ ↦ k) i

/-- An old cell keeps its graded index. -/
@[simp] theorem appendFullCellsScheme_gradedIndex_castAdd (d : Fin S.card) :
    (S.appendFullCellsScheme k M).gradedIndex (Fin.castAdd M d) = S.toCellScheme.gradedIndex d := by
  simp [CellScheme.gradedIndex]

/-- A new cell has graded index `(univ, k)`. -/
@[simp] theorem appendFullCellsScheme_gradedIndex_natAdd (i : Fin M) :
    (S.appendFullCellsScheme k M).gradedIndex (Fin.natAdd S.card i) = (univ, k) := by
  simp [CellScheme.gradedIndex]

variable {S k M}

/-- The graded index of a cell of index below the number of old cells, read in `S`. -/
theorem appendFullCellsScheme_gradedIndex_of_lt {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card) :
    (S.appendFullCellsScheme k M).gradedIndex s = S.toCellScheme.gradedIndex ⟨s, hs⟩ :=
  appendFullCellsScheme_gradedIndex_castAdd S k M ⟨s, hs⟩

/-- Below a pair that is not above `(univ, k)`, every cell is old. -/
theorem lt_card_of_mem_below {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X)
    {d : Fin (S.card + M)} (hd : d ∈ (S.appendFullCellsScheme k M).below X) :
    (d : ℕ) < S.card := by
  by_contra hlt
  have hd' : d = Fin.natAdd S.card ⟨d - S.card, by omega⟩ := Fin.ext (by simp; omega)
  rw [hd', CellScheme.mem_below, appendFullCellsScheme_gradedIndex_natAdd] at hd
  exact hX hd

/-- No new cell lies below an old cell, when no cell of `S` lies above `(univ, k)`. -/
theorem not_le_gradedIndex_of_lt
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d)
    {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card) :
    ¬ ((univ : Finset (Fin n)), k) ≤ (S.appendFullCellsScheme k M).gradedIndex s := by
  rw [appendFullCellsScheme_gradedIndex_of_lt hs]
  exact h _

/-- The cells below an old cell are old, and lie below it in `S`. -/
theorem mem_below_of_lt
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d)
    {s : Fin (S.card + M)} (hs : (s : ℕ) < S.card)
    (t : (S.appendFullCellsScheme k M).below ((S.appendFullCellsScheme k M).gradedIndex s)) :
    (⟨t.1, lt_card_of_mem_below (not_le_gradedIndex_of_lt h hs) t.2⟩ : Fin S.card) ∈
      S.toCellScheme.below (S.toCellScheme.gradedIndex ⟨s, hs⟩) := by
  rw [CellScheme.mem_below, ← appendFullCellsScheme_gradedIndex_of_lt (M := M) (k := k),
    ← appendFullCellsScheme_gradedIndex_of_lt hs]
  exact t.2

variable (S k M) in
/-- **Appending cells of full scope**: the scheme with the cells of `S`, in their order, followed
by `M` cells of scope `univ` and grade `k`, the `i`-th with row `r i` (a labelling of all cells,
read on those below `(univ, k)`).  The hypothesis says that no cell of `S` lies above `(univ, k)`,
so that the old rows, which are those of `S`, see only old cells.

It is an `abbrev`, not a `def`, for the reason recorded at `Scheme.appendFullCell`: its number of
cells must unfold reducibly to `S.card + M`, so that `Fin.castAdd` and `Fin.natAdd` apply to its
cells in rewriting and in `simp`. -/
abbrev appendFullCells (r : Fin M → Fin (S.card + M) → Label.{u})
    (h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n where
  card := S.card + M
  toCellScheme := S.appendFullCellsScheme k M
  rows := ⟨fun s t ↦ if hs : (s : ℕ) < S.card then
      S.rows.row ⟨s, hs⟩ ⟨⟨t.1, lt_card_of_mem_below (not_le_gradedIndex_of_lt h hs) t.2⟩,
        mem_below_of_lt h hs t⟩
    else r ⟨s - S.card, by omega⟩ t.1⟩

variable {r : Fin M → Fin (S.card + M) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- The row of the new cell `i` is `r i`. -/
theorem appendFullCells_row_natAdd (i : Fin M)
    (t : (S.appendFullCellsScheme k M).below
      ((S.appendFullCellsScheme k M).gradedIndex (Fin.natAdd S.card i))) :
    (S.appendFullCells k M r h).rows.row (Fin.natAdd S.card i) t = r i t.1 := by
  refine (dite_eq_right (by simp)).trans (congrArg (r · t.1) (Fin.ext ?_))
  simp

/-- The row of the new cell `i` is `r i`, as a function. -/
theorem appendFullCells_row_natAdd_eq (i : Fin M) :
    (S.appendFullCells k M r h).rows.row (Fin.natAdd S.card i) = fun t ↦ r i t.1 :=
  funext (appendFullCells_row_natAdd i)

variable (k M r h) in
/-- **The old cells form a lower embedding** along `Fin.castAdd`. -/
theorem isLowerEmbedding_castAdd :
    S.toCellScheme.IsLowerEmbedding (S.appendFullCells k M r h).toCellScheme (Fin.castAdd M) where
  injective := Fin.castAdd_injective _ _
  grade_eq d := appendFullCellsScheme_grade_castAdd S k M d
  le_iff s t := by simp only [appendFullCellsScheme_gradedIndex_castAdd]
  mem_range t d hd := ⟨⟨d, lt_card_of_mem_below
    (by rw [appendFullCellsScheme_gradedIndex_castAdd]; exact h t) hd⟩, rfl⟩

/-- **The rows pull back to those of `S`** along the old cells. -/
theorem comap_rows_castAdd :
    (S.appendFullCells k M r h).rows.comap (isLowerEmbedding_castAdd k M r h) = S.rows := by
  ext s t
  rw [CellScheme.Rows.comap_row]
  exact (dite_eq_left s.2).trans (S.rows.row_congr rfl rfl)

/-- The old cells below a pair that is not above `(univ, k)` are all its cells. -/
theorem image_castAdd_below {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X) :
    Fin.castAdd M '' S.toCellScheme.below X = (S.appendFullCells k M r h).toCellScheme.below X := by
  ext d
  constructor
  · rintro ⟨d, hd, rfl⟩
    rwa [CellScheme.mem_below, appendFullCellsScheme_gradedIndex_castAdd]
  · intro hd
    refine ⟨⟨d, lt_card_of_mem_below hX hd⟩, ?_, rfl⟩
    rw [CellScheme.mem_below, ← appendFullCellsScheme_gradedIndex_of_lt]
    exact hd

/-- **Lawfulness below a pair that is not above `(univ, k)`** is lawfulness in `S`. -/
theorem isLawfulBelow_appendFullCells_iff {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X) {v : Fin (S.card + M) → Label.{u}} :
    (S.appendFullCells k M r h).rows.IsLawfulBelow X (fun d ↦ v d) ↔
      S.rows.IsLawfulBelow X (fun d ↦ v (Fin.castAdd M d)) := by
  have := CellScheme.Rows.isLawfulBelow_comap_iff (R := (S.appendFullCells k M r h).rows)
    (isLowerEmbedding_castAdd k M r h) (image_castAdd_below hX) (r := fun d ↦ v d)
  rw [comap_rows_castAdd] at this
  exact this.symm

/-- **Lawful labellings after appending cells.**  A labelling `v` is lawful when it is lawful on
the old cells, its values at the new cells are self-visible at `k`, the row of every new cell
transforms to `v` capped at its value, and every cell of grade `k` has a value at most that of
some new cell. -/
theorem isLawful_appendFullCells {v : Fin (S.card + M) → Label.{u}}
    (hv : S.rows.IsLawful (v ∘ Fin.castAdd M))
    (hvis : ∀ i, IsSelfVisible k (v (Fin.natAdd S.card i)))
    (hloc : ∀ i, TransformsTo (fun t : (S.appendFullCellsScheme k M).below
        ((S.appendFullCellsScheme k M).gradedIndex (Fin.natAdd S.card i)) ↦
          (S.appendFullCellsScheme k M).grade t) (fun t ↦ r i t.1)
        fun t ↦ min (v t) (v (Fin.natAdd S.card i)))
    (havail : ∀ s, (S.appendFullCellsScheme k M).grade s = k →
      ∃ i, v s ≤ v (Fin.natAdd S.card i)) :
    (S.appendFullCells k M r h).rows.IsLawful v where
  orderly d := by
    induction d using Fin.addCases with
    | left d => rw [appendFullCellsScheme_grade_castAdd]; exact hv.orderly d
    | right i => rw [appendFullCellsScheme_grade_natAdd]; exact hvis i
  locality s := by
    induction s using Fin.addCases with
    | right i =>
      rw [appendFullCells_row_natAdd_eq]
      exact hloc i
    | left s =>
      have hX : ¬ ((univ : Finset (Fin n)), k) ≤
          (S.appendFullCellsScheme k M).gradedIndex (Fin.castAdd M s) := by
        rw [appendFullCellsScheme_gradedIndex_castAdd]
        exact h s
      have hb := (isLawfulBelow_appendFullCells_iff (r := r) (h := h) hX).mpr (hv.isLawfulBelow _)
      exact (CellScheme.Rows.isLawfulBelow_iff_forall.mp hb).2.1 _
        (CellScheme.mem_below_gradedIndex _ _)
  availability s t hst hg := by
    induction t using Fin.addCases with
    | right i =>
      obtain ⟨j, hj⟩ := havail s (hg.trans (appendFullCellsScheme_grade_natAdd S k M i))
      exact ⟨Fin.natAdd S.card j, by simp, hj⟩
    | left t =>
      induction s using Fin.addCases with
      | right i =>
        refine absurd ?_ (h t)
        simp only [appendFullCellsScheme_scope_natAdd, appendFullCellsScheme_scope_castAdd,
          appendFullCellsScheme_grade_natAdd, appendFullCellsScheme_grade_castAdd] at hst hg
        exact ⟨hst, hg.le⟩
      | left s =>
        simp only [appendFullCellsScheme_scope_castAdd,
          appendFullCellsScheme_grade_castAdd] at hst hg
        obtain ⟨u, hu, hle⟩ := hv.availability s t hst hg
        exact ⟨Fin.castAdd M u, by simpa using hu, hle⟩

/-- **Consistency after appending cells**: the old rows are those of `S`, and the new rows are
lawful. -/
theorem isConsistent_appendFullCells (hS : S.rows.IsConsistent)
    (hr : ∀ i, (S.appendFullCells k M r h).rows.IsLawful (r i)) :
    (S.appendFullCells k M r h).rows.IsConsistent := by
  intro s
  induction s using Fin.addCases with
  | right i =>
    rw [appendFullCells_row_natAdd_eq]
    exact (hr i).isLawfulBelow _
  | left s =>
    have hφ := isLowerEmbedding_castAdd k M r h
    refine (CellScheme.Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex s)).mp ?_
    rw [comap_rows_castAdd]
    convert hS s using 1
    funext t
    exact congrArg (fun R : S.toCellScheme.Rows ↦ R.row s t) comap_rows_castAdd

/-- **Appending cells keeps well-formedness** when `(univ, k)` is a graded face. -/
theorem isWellFormed_appendFullCells (hS : S.IsWellFormed) (hk : 0 < k) (hkn : k ≤ n) :
    (S.appendFullCells k M r h).IsWellFormed where
  ground_eq := hS.ground_eq
  isWellFormed := by
    refine ⟨inferInstance, hS.isWellFormed.isPlan, fun d ↦ ?_⟩
    induction d using Fin.addCases with
    | right i =>
      rw [appendFullCellsScheme_gradedIndex_natAdd]
      exact ⟨hS.univ_mem_faces, hk, by simpa using hkn⟩
    | left d =>
      rw [appendFullCellsScheme_gradedIndex_castAdd]
      exact hS.isWellFormed.gradedIndex_mem d

/-- **Appending cells keeps coding** when the new rows are coded. -/
theorem isCoded_appendFullCells (hS : S.IsCoded)
    (hr : ∀ i d, r i d < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})) :
    (S.appendFullCells k M r h).IsCoded := by
  intro s t
  induction s using Fin.addCases with
  | right i => exact (appendFullCells_row_natAdd i t).trans_lt (hr i _)
  | left s => exact (dite_eq_left s.2).trans_lt (hS _ _)

end VaughtConjecture.Scheme

/-! ### The canonical field layer -/

namespace VaughtConjecture.Scheme

open Finset Label

variable {n : ℕ} (S : Scheme.{u} n) (k : ℕ)

/-- The grid of the field layer at grade `k`: block bound `2 N + 2` for `N` old cells. -/
noncomputable abbrev fieldGrid : Finset Label.{u} := grid k (2 * S.card + 2)

open Classical in
/-- The **canonical catalogue** at grade `k`: the lawful labellings of the cells of `S` that are
bottom at the cells of grade above `k` and orbit-canonical, fixed by the orbit code.  They take
values in the code grid with block bound `2 N`. -/
noncomputable def catalogue : Finset (Fin S.card → Label.{u}) :=
  {a ∈ Fintype.piFinset fun _ ↦ codeGrid k (2 * S.card) | S.rows.IsLawful a ∧
    (∀ d, k < S.toCellScheme.grade d → a d = ⊥) ∧ orbitCode k a = a}

variable {S k}

/-- Membership in the canonical catalogue: lawful, bottom above `k`, and orbit-canonical. -/
theorem mem_catalogue {a : Fin S.card → Label.{u}} :
    a ∈ S.catalogue k ↔ S.rows.IsLawful a ∧ (∀ d, k < S.toCellScheme.grade d → a d = ⊥) ∧
      orbitCode k a = a := by
  simp only [catalogue, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun d ↦ ?_, h⟩⟩
  rw [← congrFun h.2.2 d]
  exact orbitMap_mem_codeGrid (by simp) _

/-- A catalogue entry takes its values in the code grid with block bound `2 N`. -/
theorem mem_codeGrid_of_mem_catalogue {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k)
    (d : Fin S.card) : a d ∈ codeGrid k (2 * S.card) := by
  simp only [catalogue, Finset.mem_filter, Fintype.mem_piFinset] at ha
  exact ha.1 d

variable (S k) in
/-- The catalogue entry of the new cell `i`. -/
noncomputable def catalogueEntry (i : Fin (S.catalogue k).card) : Fin S.card → Label.{u} :=
  ((S.catalogue k).equivFin.symm i).1

/-- A catalogue entry lies in the catalogue. -/
theorem catalogueEntry_mem (i : Fin (S.catalogue k).card) :
    S.catalogueEntry k i ∈ S.catalogue k :=
  ((S.catalogue k).equivFin.symm i).2

/-- Every member of the catalogue is the entry of some new cell. -/
theorem exists_catalogueEntry_eq {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k) :
    ∃ i, S.catalogueEntry k i = a :=
  ⟨(S.catalogue k).equivFin ⟨a, ha⟩, by simp [catalogueEntry]⟩

/-- **The splice at `k` with bottom is lawful**: a labelling lawful below `(univ, k)`, made bottom
at the cells of grade above `k`, is lawful. -/
theorem isLawful_splice_bot {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, k) fun d ↦ p d) :
    S.rows.IsLawful (S.toCellScheme.splice k (fun _ ↦ ⊥) p) := by
  set J := (univ : Finset (Fin S.card)).sup S.toCellScheme.grade
  have hJ (d : Fin S.card) : S.toCellScheme.grade d ≤ J := le_sup (mem_univ d)
  exact (CellScheme.Rows.IsLawfulBelow.splice (B := univ) (J := J) (M := ⊥)
    (CellScheme.Rows.isLawfulBelow_const_bot _) hp (fun _ _ _ ↦ le_rfl)
    fun _ _ ↦ by simp).isLawful fun d ↦ ⟨subset_univ _, hJ d⟩

/-- **The orbit code of the splice at `k` with bottom is a catalogue entry**, for a labelling
lawful below `(univ, k)`. -/
theorem orbitCode_splice_bot_mem_catalogue {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, k) fun d ↦ p d) :
    orbitCode k (S.toCellScheme.splice k (fun _ ↦ ⊥) p) ∈ S.catalogue k := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p
  have hbot (d : Fin S.card) (hd : k < S.toCellScheme.grade d) : orbitCode k t d = ⊥ := by
    rw [orbitCode_eq_bot_iff]
    exact CellScheme.splice_of_lt hd
  have heq : S.toCellScheme.splice k (fun _ ↦ ⊥) (orbitCode k t) = orbitCode k t := by
    funext d
    by_cases hd : S.toCellScheme.grade d ≤ k
    · exact CellScheme.splice_of_le hd
    · rw [CellScheme.splice_of_lt (not_le.mp hd), hbot d (not_le.mp hd)]
  refine mem_catalogue.mpr ⟨?_, hbot, orbitCode_orbitCode⟩
  rw [← heq]
  exact isLawful_splice_bot (((isLawful_splice_bot hp).isLawfulBelow _).orbitCode fun d ↦ d.2.2)

/-- The canonical code of a lawful section of `S` whose cells all have grade `k` lies in the
catalogue: there it is the orbit code. -/
theorem canonicalCode_mem_catalogue (hk : ∀ d, S.toCellScheme.grade d = k)
    {p : Fin S.card → Label.{u}} (hp : S.rows.IsLawful p) :
    canonicalCode k p ∈ S.catalogue k := by
  have hv (d : Fin S.card) : IsSelfVisible k (p d) := hk d ▸ hp.orderly d
  refine mem_catalogue.mpr ⟨hp.canonicalCode fun d ↦ (hk d).le, fun d hd ↦ absurd (hk d) hd.ne',
    ?_⟩
  rw [← orbitCode_eq_canonicalCode hv, orbitCode_orbitCode]

variable (S k) in
/-- The **field row** of a labelling `a` of the old cells: `a` on the old cells, and on the new
cell `j` the agreement height of `a` with its catalogue entry. -/
noncomputable def fieldRow (a : Fin S.card → Label.{u}) :
    Fin (S.card + (S.catalogue k).card) → Label.{u} :=
  Fin.append a fun j ↦ agreementHeight (S.fieldGrid k) a (S.catalogueEntry k j)

/-- The field row reads the labelling on the old cells. -/
@[simp] theorem fieldRow_castAdd (a : Fin S.card → Label.{u}) (d : Fin S.card) :
    S.fieldRow k a (Fin.castAdd _ d) = a d :=
  Fin.append_left _ _ d

/-- The field row reads an agreement height on the new cells. -/
@[simp] theorem fieldRow_natAdd (a : Fin S.card → Label.{u}) (j : Fin (S.catalogue k).card) :
    S.fieldRow k a (Fin.natAdd _ j) =
      agreementHeight (S.fieldGrid k) a (S.catalogueEntry k j) :=
  Fin.append_right _ _ j

/-- The field row of a catalogue entry takes its values in the code grid with block bound
`2 N + 2`: the entry on the old cells, grid points on the new cells. -/
theorem fieldRow_mem_codeGrid {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k)
    (x : Fin (S.card + (S.catalogue k).card)) :
    S.fieldRow k a x ∈ codeGrid k (2 * S.card + 2) := by
  induction x using Fin.addCases with
  | left d =>
    rw [fieldRow_castAdd]
    exact codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue ha d)
  | right j =>
    rw [fieldRow_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- Two field rows agree capped at the agreement height of their labellings. -/
theorem min_fieldRow_agreementHeight (a b : Fin S.card → Label.{u})
    (x : Fin (S.card + (S.catalogue k).card)) :
    min (S.fieldRow k a x) (agreementHeight (S.fieldGrid k) a b) =
      min (S.fieldRow k b x) (agreementHeight (S.fieldGrid k) a b) := by
  induction x using Fin.addCases with
  | left d =>
    rw [fieldRow_castAdd, fieldRow_castAdd]
    exact (agreementHeight_spec (bot_mem_grid _ _) a b).2 d
  | right j =>
    rw [fieldRow_natAdd, fieldRow_natAdd]
    exact agreementHeight_tri (bot_mem_grid _ _) a b _

variable (S k) in
/-- **The canonical field layer** at grade `k`: the cells of `S`, followed by one cell of scope
`univ` and grade `k` for each entry of the canonical catalogue, whose row is the field row of the
entry. -/
noncomputable abbrev fieldLayer
    (hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n :=
  S.appendFullCells k (S.catalogue k).card (fun i ↦ S.fieldRow k (S.catalogueEntry k i)) hS

variable {hS : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}

/-- The row of a new cell is the field row of its catalogue entry. -/
theorem fieldLayer_row_natAdd (i : Fin (S.catalogue k).card) (t) :
    (S.fieldLayer k hS).rows.row (Fin.natAdd S.card i) t =
      S.fieldRow k (S.catalogueEntry k i) t.1 :=
  appendFullCells_row_natAdd i t

variable (S k hS) in
/-- **The old cells form a lower embedding** of `S` into the field layer, along `Fin.castAdd`. -/
theorem isLowerEmbedding_fieldLayer :
    S.toCellScheme.IsLowerEmbedding (S.fieldLayer k hS).toCellScheme (Fin.castAdd _) :=
  isLowerEmbedding_castAdd _ _ _ _

/-- **The rows of the field layer pull back to those of `S`** along the old cells. -/
theorem comap_rows_fieldLayer :
    (S.fieldLayer k hS).rows.comap (isLowerEmbedding_fieldLayer S k hS) = S.rows :=
  comap_rows_castAdd

/-- Every cell of the field layer has grade `k` when every cell of `S` has. -/
theorem fieldLayer_grade (hk : ∀ d, S.toCellScheme.grade d = k)
    (d : Fin (S.fieldLayer k hS).card) :
    (S.fieldLayer k hS).toCellScheme.grade d = k := by
  induction d using Fin.addCases with
  | left d => exact (appendFullCellsScheme_grade_castAdd S k _ d).trans (hk d)
  | right i => exact appendFullCellsScheme_grade_natAdd S k _ i

/-- **The field row of a catalogue entry is a lawful section of the field layer.**  On the old
cells it is the entry, lawful in `S`; at a new cell its locality is the identity capped at the
agreement height, by the ultrametric inequality; availability at the full face holds at the cell
of the entry itself, whose diagonal entry is the ceiling of the grid. -/
theorem isLawful_fieldRow {a : Fin S.card → Label.{u}} (ha : a ∈ S.catalogue k) :
    (S.fieldLayer k hS).rows.IsLawful (S.fieldRow k a) := by
  refine isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s _ ↦ ?_
  · convert (mem_catalogue.mp ha).1 using 1
    exact funext fun d ↦ fieldRow_castAdd a d
  · rw [fieldRow_natAdd]
    exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · have hc := (isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid k (2 * S.card + 2))
      a (S.catalogueEntry k i)).1)
    convert (TransformsTo.refl (fun t : (S.appendFullCellsScheme k (S.catalogue k).card).below
      ((S.appendFullCellsScheme k (S.catalogue k).card).gradedIndex (Fin.natAdd S.card i)) ↦
        (S.appendFullCellsScheme k (S.catalogue k).card).grade t)
          fun t ↦ S.fieldRow k (S.catalogueEntry k i) t.1)
      |>.min_const (K := k) (fun t ↦ t.2.2.trans (appendFullCellsScheme_grade_natAdd S k _ i).le)
        hc using 1
    funext t
    rw [fieldRow_natAdd]
    exact min_fieldRow_agreementHeight a _ t.1
  · obtain ⟨i, hi⟩ := exists_catalogueEntry_eq ha
    refine ⟨i, ?_⟩
    rw [fieldRow_natAdd, hi, agreementHeight_self (gridPoint_mem_grid le_rfl)
      fun x hx ↦ le_gridPoint_of_mem_grid hx]
    exact le_gridPoint_of_mem_codeGrid (fieldRow_mem_codeGrid ha s)

/-- **The field layer is consistent**: the old rows are those of `S`, and the new rows are field
rows of catalogue entries. -/
theorem isConsistent_fieldLayer (hcons : S.rows.IsConsistent) :
    (S.fieldLayer k hS).rows.IsConsistent :=
  isConsistent_appendFullCells hcons fun i ↦ isLawful_fieldRow (catalogueEntry_mem i)

/-- **The field layer is well formed.** -/
theorem isWellFormed_fieldLayer (hwf : S.IsWellFormed) (hk0 : 0 < k) (hkn : k ≤ n) :
    (S.fieldLayer k hS).IsWellFormed :=
  isWellFormed_appendFullCells hwf hk0 hkn

/-- **The field layer is coded**: the new rows take values in the code grid, below `ω ^ 2`. -/
theorem isCoded_fieldLayer (hc : S.IsCoded) : (S.fieldLayer k hS).IsCoded :=
  isCoded_appendFullCells hc fun i x ↦
    (lt_omega0_sq_of_mem_codeGrid (fieldRow_mem_codeGrid (catalogueEntry_mem i) x))

/-- **The new rows are short at `k` and never the formal top**: their values lie in the code
grid. -/
theorem isShort_ne_top_row_fieldLayer (i : Fin (S.catalogue k).card) (t) :
    IsShort k ((S.fieldLayer k hS).rows.row (Fin.natAdd S.card i) t) ∧
      (S.fieldLayer k hS).rows.row (Fin.natAdd S.card i) t ≠ ⊤ := by
  rw [fieldLayer_row_natAdd]
  exact ⟨isShort_of_mem_codeGrid (fieldRow_mem_codeGrid (catalogueEntry_mem i) t.1),
    ne_top_of_mem_codeGrid (fieldRow_mem_codeGrid (catalogueEntry_mem i) t.1)⟩

/-! ### Extension through the new cells -/

/-- An old cell of grade at most `k` lies below `(univ, k)` in the field layer. -/
theorem castAdd_mem_below {d : Fin S.card} (hd : S.toCellScheme.grade d ≤ k) :
    Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below (univ, k) :=
  ⟨subset_univ _, (appendFullCellsScheme_grade_castAdd S k _ d).trans_le hd⟩

/-- A new cell lies below `(univ, k)` in the field layer. -/
theorem natAdd_mem_below (i : Fin (S.catalogue k).card) :
    Fin.natAdd S.card i ∈ (S.fieldLayer k hS).toCellScheme.below (univ, k) :=
  (appendFullCellsScheme_gradedIndex_natAdd S k _ i).le

variable (S k hS) in
/-- **`S` is a source prefix of its field layer** at every pair that is not above `(univ, k)`: the
cells below such a pair are old. -/
theorem isSourcePrefix_fieldLayer {Y : Finset (Fin n) × ℕ}
    (hY : ¬ ((univ : Finset (Fin n)), k) ≤ Y) :
    S.toCellScheme.IsSourcePrefix (S.fieldLayer k hS).toCellScheme (Fin.castAdd _) Y :=
  ⟨isLowerEmbedding_fieldLayer S k hS, appendFullCellsScheme_scope_castAdd S k _,
    fun d hd ↦ ⟨⟨d, lt_card_of_mem_below hY hd⟩, rfl⟩⟩

/-- A cell of the field layer below a pair that is not above `(univ, k)` is old. -/
theorem exists_castAdd_eq {X : Finset (Fin n) × ℕ} (hX : ¬ ((univ : Finset (Fin n)), k) ≤ X)
    {d : Fin (S.fieldLayer k hS).card} (hd : d ∈ (S.fieldLayer k hS).toCellScheme.below X) :
    ∃ e, Fin.castAdd _ e = d :=
  ⟨⟨d, lt_card_of_mem_below hX hd⟩, rfl⟩

/-- A cell of the field layer of graded index `(univ, k)` is new. -/
theorem exists_natAdd_eq {u : Fin (S.fieldLayer k hS).card}
    (hu : (S.fieldLayer k hS).toCellScheme.gradedIndex u = (univ, k)) :
    ∃ i, Fin.natAdd S.card i = u := by
  by_cases hlt : (u : ℕ) < S.card
  · refine absurd ?_ (hS ⟨u, hlt⟩)
    rw [← appendFullCellsScheme_gradedIndex_of_lt hlt]
    exact hu.ge
  · have hu' : (u : ℕ) < S.card + (S.catalogue k).card := u.2
    exact ⟨⟨u - S.card, by omega⟩, Fin.ext (by simp; omega)⟩

/-- **Extension at the cap `⊥`, below `(univ, k)`**: every labelling lawful below `(univ, k)` in
`S` extends, unchanged at the old cells of grade at most `k`, to a labelling lawful below
`(univ, k)` in the field layer.  It is the field row of the orbit code `b` of its splice, read
by the orbit decoder at the least grid point, which reads `b` literally (the natural strip is
kept) and sends no other label to bottom. -/
theorem exists_isLawfulBelow_fieldLayer {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, k) fun d ↦ p d) :
    ∃ r : (S.fieldLayer k hS).toCellScheme.below (univ, k) → Label.{u},
      (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) r ∧
        ∀ d (hd : S.toCellScheme.grade d ≤ k), r ⟨Fin.castAdd _ d, castAdd_mem_below hd⟩ = p d := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p
  have hb := orbitCode_splice_bot_mem_catalogue hp
  refine ⟨fun x ↦ orbitDecoder k t (gridPoint k 0) (S.fieldRow k (orbitCode k t) x),
    ((isLawful_fieldRow (hS := hS) hb).isLawfulBelow _).map_of_apply_eq_bot (fun x ↦ x.2.2)
      (isWitness_orbitDecoder (isSelfVisible_gridPoint k 0) (gridPoint_ne_bot k 0))
      fun _ ↦ eq_bot_of_orbitDecoder_eq_bot (gridPoint_ne_bot k 0), fun d hd ↦ ?_⟩
  -- The extension at the old cell `d` is the decoder applied to its code.
  change orbitDecoder k t (gridPoint k 0) (S.fieldRow k (orbitCode k t) (Fin.castAdd _ d)) = p d
  rw [fieldRow_castAdd, orbitDecoder_orbitCode (fun e ↦ min_orbitCode_gridPoint_zero e)]
  exact CellScheme.splice_of_le hd

/-- **Extension at the cap `⊥`**: every lawful section `p` of `S` extends to a lawful section of
the field layer: `p` on the old cells, and on the new cells the extension below `(univ, k)`. -/
theorem exists_isLawful_fieldLayer {p : Fin S.card → Label.{u}} (hp : S.rows.IsLawful p) :
    ∃ r, (S.fieldLayer k hS).rows.IsLawful r ∧ ∀ d, r (Fin.castAdd _ d) = p d := by
  obtain ⟨r₀, hr₀, hr₀p⟩ := exists_isLawfulBelow_fieldLayer (hS := hS) (hp.isLawfulBelow (univ, k))
  obtain ⟨i₀, -⟩ := exists_catalogueEntry_eq (orbitCode_splice_bot_mem_catalogue (k := k)
    (hp.isLawfulBelow (univ, k)))
  set r : Fin (S.card + (S.catalogue k).card) → Label.{u} :=
    Fin.append p fun i ↦ r₀ ⟨Fin.natAdd _ i, natAdd_mem_below i⟩ with hr_def
  -- Below `(univ, k)` the labelling `r` is `r₀`.
  have hrr₀ (x : (S.fieldLayer k hS).toCellScheme.below (univ, k)) : r x.1 = r₀ x := by
    obtain ⟨x, hx⟩ := x
    induction x using Fin.addCases with
    | left d =>
      rw [hr_def, Fin.append_left]
      exact (hr₀p d (by simpa using hx.2)).symm
    | right i => rw [hr_def, Fin.append_right]
  have hrb : (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) fun x ↦ r x := by
    convert hr₀ using 1
    exact funext hrr₀
  obtain ⟨hvis, hloc, havail⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hrb
  refine ⟨r, isLawful_appendFullCells ?_ (fun i ↦ ?_) (fun i ↦ ?_) fun s hs ↦ ?_, fun d ↦ ?_⟩
  · convert hp using 1
    exact funext fun d ↦ Fin.append_left _ _ d
  · have hg : (S.fieldLayer k hS).toCellScheme.grade (Fin.natAdd S.card i) = k :=
      appendFullCellsScheme_grade_natAdd S k _ i
    have h := hvis _ (natAdd_mem_below i)
    rwa [hg] at h
  · have h := hloc _ (natAdd_mem_below i)
    rwa [appendFullCells_row_natAdd_eq] at h
  · have hsc : (S.fieldLayer k hS).toCellScheme.scope (Fin.natAdd S.card i₀) = univ :=
      appendFullCellsScheme_scope_natAdd S k _ i₀
    obtain ⟨u, hu, hle⟩ := havail s _ (natAdd_mem_below i₀) (hsc ▸ subset_univ _)
      (hs.trans (appendFullCellsScheme_grade_natAdd S k _ i₀).symm)
    obtain ⟨i, rfl⟩ := exists_natAdd_eq (hS := hS)
      (hu.trans (appendFullCellsScheme_gradedIndex_natAdd S k _ i₀))
    exact ⟨i, hle⟩
  · exact Fin.append_left _ _ d

/-- **Extension through the new cells at a positive cap.**  Let `p` be lawful below `(univ, k)` in
`S`, `a` a catalogue entry, and `h` self-visible at `k` with `⊥ < h`, such that `p` agrees with `a`
capped at `h` at the cells of grade at most `k`.  Suppose that `h` is short at `k`, or that no
cell of `S` has a grade below `k`.  Then some labelling lawful below `(univ, k)` in the field layer
reads `p` at the old cells of grade at most `k` and agrees with the field row of `a` capped at `h`
at every cell below `(univ, k)`.  It is the field row of the orbit code `b` of the splice of
`p`, read by the orbit decoder at `h`: relative room makes `b` agree with `a` capped at `h` (for a
short cap by `Label.min_orbitCode_eq`; without lower grades the orbit code is the canonical code,
`Label.min_canonicalCode_eq`), the agreement heights of `b` then agree with those of `a` capped at
`h`, the decoder reads the old cells literally and keeps the cap at the agreement heights, and the
field row of `a` is a lawful companion of the same bottom pattern. -/
theorem exists_extension_fieldLayer {p : Fin S.card → Label.{u}}
    (hp : S.rows.IsLawfulBelow (univ, k) fun d ↦ p d) {a : Fin S.card → Label.{u}}
    (ha : a ∈ S.catalogue k) {h : Label.{u}} (hh : IsSelfVisible k h) (hbot : ⊥ < h)
    (hcap : IsShort k h ∨ ∀ d, S.toCellScheme.grade d ≤ k → S.toCellScheme.grade d = k)
    (hag : ∀ d, S.toCellScheme.grade d ≤ k → min (p d) h = min (a d) h) :
    ∃ r : (S.fieldLayer k hS).toCellScheme.below (univ, k) → Label.{u},
      (S.fieldLayer k hS).rows.IsLawfulBelow (univ, k) r ∧
        (∀ d (hd : S.toCellScheme.grade d ≤ k), r ⟨Fin.castAdd _ d, castAdd_mem_below hd⟩ = p d) ∧
          ∀ x, min (r x) h = min (S.fieldRow k a x) h := by
  set t := S.toCellScheme.splice k (fun _ ↦ ⊥) p with ht_def
  have htle (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) : t d = p d :=
    CellScheme.splice_of_le hd
  have htgt (d : Fin S.card) (hd : ¬ S.toCellScheme.grade d ≤ k) : t d = ⊥ :=
    CellScheme.splice_of_lt (not_le.mp hd)
  set b := orbitCode k t
  have hb : b ∈ S.catalogue k := orbitCode_splice_bot_mem_catalogue hp
  obtain ⟨-, haup, haa⟩ := mem_catalogue.mp ha
  -- The splice agrees with `a` capped at `h` at every cell.
  have hagt (d : Fin S.card) : min (t d) h = min (a d) h := by
    by_cases hd : S.toCellScheme.grade d ≤ k
    · rw [htle d hd]
      exact hag d hd
    · rw [htgt d hd, haup d (not_le.mp hd)]
  -- Relative room, and its transfer to the agreement heights.
  have hrow : (∀ d, min (b d) h = min (a d) h) ∧ ∀ x : Fin (S.card + (S.catalogue k).card),
      min (S.fieldRow k b x) h = min (S.fieldRow k a x) h := by
    have htransfer (hba : ∀ d, min (b d) h = min (a d) h)
        (hht : ∀ c, min (agreementHeight (S.fieldGrid k) b c) h =
          min (agreementHeight (S.fieldGrid k) a c) h) :
        ∀ x : Fin (S.card + (S.catalogue k).card),
          min (S.fieldRow k b x) h = min (S.fieldRow k a x) h := fun x ↦ by
      induction x using Fin.addCases with
      | left d => rw [fieldRow_castAdd, fieldRow_castAdd]; exact hba d
      | right j => rw [fieldRow_natAdd, fieldRow_natAdd]; exact hht _
    rcases hcap with hs | hk
    · have hba (d : Fin S.card) : min (b d) h = min (a d) h := min_orbitCode_eq hh hs haa hagt d
      refine ⟨hba, htransfer hba fun c ↦ min_agreementHeight_eq_of_isShort hh hs
        (fun d ↦ ⟨codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue hb d),
          codeGrid_mono (by omega) (mem_codeGrid_of_mem_catalogue ha d)⟩) hba c⟩
    · -- Without lower grades, the values are self-visible and the codes canonical.
      have hvt (d : Fin S.card) : IsSelfVisible k (t d) := by
        by_cases hd : S.toCellScheme.grade d ≤ k
        · rw [htle d hd, ← hk d hd]
          exact (CellScheme.Rows.isLawfulBelow_iff.mp hp).orderly ⟨d, subset_univ _, hd⟩
        · rw [htgt d hd]
          exact isSelfVisible_bot k
      have hva (d : Fin S.card) : IsSelfVisible k (a d) := by
        by_cases hd : S.toCellScheme.grade d ≤ k
        · exact hk d hd ▸ (mem_catalogue.mp ha).1.orderly d
        · rw [haup d (not_le.mp hd)]
          exact isSelfVisible_bot k
      have hbt : b = canonicalCode k t := orbitCode_eq_canonicalCode hvt
      have hac : canonicalCode k a = a := by rw [← orbitCode_eq_canonicalCode hva, haa]
      have hba (d : Fin S.card) : min (b d) h = min (a d) h := by
        rw [hbt]
        exact min_canonicalCode_eq hvt hac hagt d
      refine ⟨hba, htransfer hba fun c ↦ min_agreementHeight_eq (bot_mem_grid _ _)
        (fun d ↦ ⟨?_, ?_⟩) hba c⟩
      · rw [hbt]
        exact canonicalMap_mem_grid (by simp; omega) _
      · rw [← hac]
        exact canonicalMap_mem_grid (by simp; omega) _
  obtain ⟨hba, hrowh⟩ := hrow
  -- The decoder reads the old cells literally and keeps the cap at the agreement heights.
  have hread (d : Fin S.card) : orbitDecoder k t h (b d) = t d :=
    orbitDecoder_orbitCode (fun e ↦ (hba e).trans (hagt e).symm) d
  have hcapr (x : Fin (S.card + (S.catalogue k).card)) :
      min (orbitDecoder k t h (S.fieldRow k b x)) h = min (S.fieldRow k a x) h := by
    induction x using Fin.addCases with
    | left d => rw [fieldRow_castAdd, fieldRow_castAdd, hread]; exact hagt d
    | right j =>
      rw [min_orbitDecoder_eq (by
          rw [fieldRow_natAdd]
          exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1)]
      exact hrowh _
  refine ⟨fun x ↦ orbitDecoder k t h (S.fieldRow k b x),
    ((isLawful_fieldRow (hS := hS) hb).isLawfulBelow _).map_of_min_eq
      ((isLawful_fieldRow (hS := hS) ha).isLawfulBelow _) (fun x ↦ x.2.2)
      (isWitness_orbitDecoder hh hbot.ne') hbot.ne' fun x ↦ hcapr x.1, fun d hd ↦ ?_,
    fun x ↦ hcapr x.1⟩
  -- The extension at the old cell `d` is the decoder applied to its code.
  change orbitDecoder k t h (S.fieldRow k b (Fin.castAdd _ d)) = p d
  rw [fieldRow_castAdd, hread, htle d hd]

/-! ### Extension from the boundary -/

variable {U V : Finset (Fin n) × ℕ}

/-- **The boundary labelling is lawful below `(univ, k)` in `S`**: a labelling of the field layer
lawful below two pairs `U` and `V`, neither above `(univ, k)`, below one of which lies every old
cell of grade at most `k`, is lawful below `(univ, k)` on the old cells. -/
theorem isLawfulBelow_castAdd_of_boundary
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.grade d ≤ k →
      S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V)
    {w : Fin (S.fieldLayer k hS).card → Label.{u}}
    (hwU : (S.fieldLayer k hS).rows.IsLawfulBelow U (fun d ↦ w d))
    (hwV : (S.fieldLayer k hS).rows.IsLawfulBelow V (fun d ↦ w d)) :
    S.rows.IsLawfulBelow (univ, k) fun d ↦ w (Fin.castAdd _ d) :=
  CellScheme.Rows.IsLawfulBelow.glue (w := fun e ↦ w (Fin.castAdd _ e))
    ((isLawfulBelow_appendFullCells_iff hU).mp hwU)
    ((isLawfulBelow_appendFullCells_iff hV).mp hwV) fun d hd ↦ hcover d hd.2

/-- A boundary cell below `(univ, k)` is an old cell of grade at most `k`. -/
theorem exists_castAdd_eq_of_boundary (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U)
    (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    {d : (S.fieldLayer k hS).toCellScheme.below (univ, k)}
    (hd : (d : Fin (S.fieldLayer k hS).card) ∈ (S.fieldLayer k hS).toCellScheme.below U ∨
      (d : Fin (S.fieldLayer k hS).card) ∈ (S.fieldLayer k hS).toCellScheme.below V) :
    ∃ e, ∃ he : S.toCellScheme.grade e ≤ k, d = ⟨Fin.castAdd _ e, castAdd_mem_below he⟩ := by
  obtain ⟨e, he⟩ := hd.elim (exists_castAdd_eq hU) (exists_castAdd_eq hV)
  have hge : S.toCellScheme.grade e ≤ k := by
    have := d.2.2
    rw [← he] at this
    exact (appendFullCellsScheme_grade_castAdd S k _ e).symm.trans_le this
  exact ⟨e, hge, Subtype.ext he.symm⟩

/-- **Extension from the boundary at the cap `⊥`**: every labelling lawful below `U` and `V` (the
boundary, here every old cell of grade at most `k`) extends, unchanged there, to a labelling lawful
below `(univ, k)`. -/
theorem extendsFromBoundary_bot_fieldLayer
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.grade d ≤ k →
      S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V) :
    (S.fieldLayer k hS).rows.ExtendsFromBoundary U V (univ, k) ⊥ fun _ ↦ ⊥ := by
  intro w hwU hwV _
  obtain ⟨r, hr, hre⟩ := exists_isLawfulBelow_fieldLayer (hS := hS)
    (p := fun d ↦ w (Fin.castAdd _ d)) (isLawfulBelow_castAdd_of_boundary hU hV hcover hwU hwV)
  refine ⟨r, hr, fun d hd ↦ ?_, fun _ ↦ by simp⟩
  obtain ⟨e, he, rfl⟩ := exists_castAdd_eq_of_boundary hU hV hd
  exact hre e he

/-- **Extension from the boundary at a positive cap, along a new row.**  Suppose that no cell of
`S` has a grade below `k`.  Let `u` be a new cell, of graded index `(univ, k)`, with catalogue
entry `a`, and `h` a cap self-visible at `k` other than bottom.  Every labelling `w` lawful below
`U` and `V` (every old cell of grade at most `k`) that agrees with the row of `u` capped at `h` on
the boundary extends, unchanged there, to a labelling lawful below `(univ, k)` that agrees with the
row of `u` capped at `h` at every cell (`Scheme.exists_extension_fieldLayer`). -/
theorem extendsFromBoundary_fieldLayer
    (hk : ∀ d, S.toCellScheme.grade d ≤ k → S.toCellScheme.grade d = k)
    (hU : ¬ ((univ : Finset (Fin n)), k) ≤ U) (hV : ¬ ((univ : Finset (Fin n)), k) ≤ V)
    (hcover : ∀ d, S.toCellScheme.grade d ≤ k →
      S.toCellScheme.gradedIndex d ≤ U ∨ S.toCellScheme.gradedIndex d ≤ V)
    {u : Fin (S.fieldLayer k hS).card}
    (hu : (S.fieldLayer k hS).toCellScheme.gradedIndex u = (univ, k)) {h : Label.{u}}
    (hh : IsSelfVisible k h) (hbot : ⊥ < h) :
    (S.fieldLayer k hS).rows.ExtendsFromBoundary U V (univ, k) h
      ((S.fieldLayer k hS).rows.rowBelow u hu) := by
  intro w hwU hwV hwS
  obtain ⟨i, rfl⟩ := exists_natAdd_eq hu
  have hrowBelow (d : (S.fieldLayer k hS).toCellScheme.below (univ, k)) :
      (S.fieldLayer k hS).rows.rowBelow (Fin.natAdd S.card i) hu d =
        S.fieldRow k (S.catalogueEntry k i) d :=
    fieldLayer_row_natAdd i _
  have hag (d : Fin S.card) (hd : S.toCellScheme.grade d ≤ k) :
      min (w (Fin.castAdd _ d)) h = min (S.catalogueEntry k i d) h := by
    have hbd : Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below U ∨
        Fin.castAdd (S.catalogue k).card d ∈ (S.fieldLayer k hS).toCellScheme.below V := by
      simpa [CellScheme.mem_below] using hcover d hd
    have := hwS ⟨_, castAdd_mem_below hd⟩ hbd
    rwa [hrowBelow, fieldRow_castAdd] at this
  obtain ⟨r, hr, hrp, hrS⟩ := exists_extension_fieldLayer (hS := hS)
    (p := fun d ↦ w (Fin.castAdd _ d)) (isLawfulBelow_castAdd_of_boundary hU hV hcover hwU hwV)
    (catalogueEntry_mem i) hh hbot
    (.inr hk) hag
  refine ⟨r, hr, fun d hd ↦ ?_, fun d ↦ by rw [hrowBelow]; exact hrS d⟩
  obtain ⟨e, he, rfl⟩ := exists_castAdd_eq_of_boundary hU hV hd
  exact hrp e he

end VaughtConjecture.Scheme
