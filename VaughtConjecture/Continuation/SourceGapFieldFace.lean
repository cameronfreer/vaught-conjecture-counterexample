/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.SourceGapFieldCellObstruction

/-!
# A field cell on a new face: the restrictions to the coatoms are unchanged

Roadmap, Layer 3 ((R2) of the table of 3.4); the way out of
`VaughtConjecture.Continuation.SourceGapFieldCellObstruction`: a field cell of scope `{1, 2}` and
grade `2` (below it only the cells of scope in `{1, 2}`), on the face `{1, 2}` added to the faces.

**Appending a cell on a new face** (`Scheme.appendCell S F k r h`): the cells of `S`, in their
order, followed by one cell of scope `F` and grade `k` with row `r`, and the faces of `S` with `F`
added; the hypothesis `h` says that no cell of `S` lies above `(F, k)`, so the old rows see only
old cells.

**The restrictions are unchanged** (`Scheme.comap_appendCell`): along every `f` whose range does
not contain `F`, the restriction of `S.appendCell F k r h` is that of `S`: the new cell is not
visible, the new face is not the image of a face, and the old cells keep their scopes, grades and
rows.  On three points with `F = {1, 2}`, the two coatoms `Fin.castSuccEmb` and
`extendByLast Fin.castSuccEmb` do not contain `F` (`Scheme.comap_appendCell_pair_left`,
`Scheme.comap_appendCell_pair_right`): a field cell on the face `{1, 2}` leaves both faces of a
coface, the context and the donor, as they are.

**What blocks it in the current framework** (`Scheme.faces_appendCell_ne`,
`Coatom.pair_notMem_amalgamFaces`): the face `{1, 2}` is not a face of the amalgam of two coatom
schemes on two points, so the faces of the scheme with the field cell differ from those of the
amalgam, against the face condition `CompletionBelowFullGrade.faces_eq`.  The completion framework
must allow faces strictly containing those of the amalgam (and the plan laws of the enlarged faces
must be checked); the restrictions themselves are not the obstacle.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset

namespace Scheme

variable {n m : ℕ} (S : Scheme.{u} n) (F : Finset (Fin n)) (k : ℕ)

/-- The cell scheme of `S` with one cell of scope `F` and grade `k` appended, and the face `F`. -/
def appendCellScheme : CellScheme (Fin (S.card + 1)) (Fin n) where
  ground := S.toCellScheme.ground
  faces := insert F S.toCellScheme.faces
  scope := Fin.append S.toCellScheme.scope fun _ ↦ F
  grade := Fin.append S.toCellScheme.grade fun _ ↦ k

@[simp] theorem appendCellScheme_scope_castAdd (d : Fin S.card) :
    (S.appendCellScheme F k).scope (Fin.castAdd 1 d) = S.toCellScheme.scope d :=
  Fin.append_left (u := S.toCellScheme.scope) (v := fun _ ↦ F) d

@[simp] theorem appendCellScheme_scope_natAdd (i : Fin 1) :
    (S.appendCellScheme F k).scope (Fin.natAdd S.card i) = F :=
  Fin.append_right (u := S.toCellScheme.scope) (v := fun _ ↦ F) i

@[simp] theorem appendCellScheme_grade_castAdd (d : Fin S.card) :
    (S.appendCellScheme F k).grade (Fin.castAdd 1 d) = S.toCellScheme.grade d :=
  Fin.append_left (u := S.toCellScheme.grade) (v := fun _ ↦ k) d

@[simp] theorem appendCellScheme_grade_natAdd (i : Fin 1) :
    (S.appendCellScheme F k).grade (Fin.natAdd S.card i) = k :=
  Fin.append_right (u := S.toCellScheme.grade) (v := fun _ ↦ k) i

@[simp] theorem appendCellScheme_gradedIndex_castAdd (d : Fin S.card) :
    (S.appendCellScheme F k).gradedIndex (Fin.castAdd 1 d) = S.toCellScheme.gradedIndex d := by
  simp [CellScheme.gradedIndex]

@[simp] theorem appendCellScheme_gradedIndex_natAdd (i : Fin 1) :
    (S.appendCellScheme F k).gradedIndex (Fin.natAdd S.card i) = (F, k) := by
  simp [CellScheme.gradedIndex]

variable {S F k}

/-- Below a pair not above `(F, k)`, every cell is old. -/
theorem lt_card_of_mem_below_appendCell {X : Finset (Fin n) × ℕ} (hX : ¬ (F, k) ≤ X)
    {d : Fin (S.card + 1)} (hd : d ∈ (S.appendCellScheme F k).below X) : (d : ℕ) < S.card := by
  by_contra hlt
  have hd' : d = Fin.natAdd S.card ⟨d - S.card, by omega⟩ := Fin.ext (by simp; omega)
  rw [hd', CellScheme.mem_below, appendCellScheme_gradedIndex_natAdd] at hd
  exact hX hd

/-- The cells below an old cell are old, and lie below it in `S`. -/
theorem mem_below_of_lt_appendCell (h : ∀ d, ¬ (F, k) ≤ S.toCellScheme.gradedIndex d)
    {s : Fin (S.card + 1)} (hs : (s : ℕ) < S.card)
    (t : (S.appendCellScheme F k).below ((S.appendCellScheme F k).gradedIndex s)) :
    (⟨t.1, lt_card_of_mem_below_appendCell (by
        rw [show s = Fin.castAdd 1 ⟨s, hs⟩ from Fin.ext rfl,
          appendCellScheme_gradedIndex_castAdd]
        exact h _) t.2⟩ : Fin S.card) ∈
      S.toCellScheme.below (S.toCellScheme.gradedIndex ⟨s, hs⟩) := by
  have hgs : (S.appendCellScheme F k).gradedIndex s = S.toCellScheme.gradedIndex ⟨s, hs⟩ :=
    appendCellScheme_gradedIndex_castAdd S F k ⟨s, hs⟩
  have hlt : (t.1 : ℕ) < S.card := lt_card_of_mem_below_appendCell (by rw [hgs]; exact h _) t.2
  have hgt : (S.appendCellScheme F k).gradedIndex t.1 =
      S.toCellScheme.gradedIndex ⟨t.1, hlt⟩ :=
    appendCellScheme_gradedIndex_castAdd S F k ⟨t.1, hlt⟩
  exact (CellScheme.mem_below _).mpr (hgt.symm.le.trans (t.2.trans hgs.le))

variable (S F k) in
/-- **Appending a cell on a new face**: the cells of `S` followed by one cell of scope `F` and
grade `k` with row `r`, and the face `F` added. -/
abbrev appendCell (r : Fin (S.card + 1) → Label.{u})
    (h : ∀ d, ¬ (F, k) ≤ S.toCellScheme.gradedIndex d) : Scheme.{u} n where
  card := S.card + 1
  toCellScheme := S.appendCellScheme F k
  rows := ⟨fun s t ↦ if hs : (s : ℕ) < S.card then
      S.rows.row ⟨s, hs⟩ ⟨_, mem_below_of_lt_appendCell h hs t⟩
    else r t.1⟩

variable {r : Fin (S.card + 1) → Label.{u}} {h : ∀ d, ¬ (F, k) ≤ S.toCellScheme.gradedIndex d}

/-- The row of an old cell is its row in `S`. -/
theorem appendCell_row_castAdd (s : Fin S.card)
    (t : (S.appendCellScheme F k).below ((S.appendCellScheme F k).gradedIndex (Fin.castAdd 1 s))) :
    (S.appendCell F k r h).rows.row (Fin.castAdd 1 s) t =
      S.rows.row s ⟨_, mem_below_of_lt_appendCell h s.isLt t⟩ :=
  dite_eq_left s.isLt

/-- **The restrictions along faces not containing `F` are unchanged.** -/
theorem comap_appendCell (f : Fin m ↪ Fin n) (hF : ¬ F ⊆ univ.map f) :
    (S.appendCell F k r h).comap f = S.comap f := by
  set S' := S.appendCell F k r h
  have he : StrictMono fun i : Fin (S.comap f).card ↦ Fin.castAdd 1 (S.cellMap f i) :=
    fun _ _ hij ↦ Fin.lt_def.mpr (by simpa using Fin.lt_def.mp ((S.cellMap f).strictMono hij))
  have hr (d : Fin S'.card) :
      d ∈ Set.range (fun i : Fin (S.comap f).card ↦ Fin.castAdd 1 (S.cellMap f i)) ↔
        d ∈ S'.visibleCells f := by
    rw [Scheme.mem_visibleCells]
    constructor
    · rintro ⟨i, rfl⟩
      change ((S'.toCellScheme.scope (Fin.castAdd 1 (S.cellMap f i)) : Set (Fin n)) ⊆ _)
      rw [show S'.toCellScheme.scope (Fin.castAdd 1 (S.cellMap f i)) =
        S.toCellScheme.scope (S.cellMap f i) from appendCellScheme_scope_castAdd S F k _]
      exact Scheme.mem_visibleCells.mp (S.cellMap_mem f i)
    · intro hd
      induction d using Fin.addCases with
      | right i =>
        exfalso
        rw [show S'.toCellScheme.scope (Fin.natAdd S.card i) = F from
          appendCellScheme_scope_natAdd S F k i] at hd
        refine hF fun x hx ↦ ?_
        obtain ⟨y, hy⟩ := hd (mem_coe.mpr hx)
        exact mem_map.mpr ⟨y, mem_univ _, hy⟩
      | left x =>
        rw [show S'.toCellScheme.scope (Fin.castAdd 1 x) = S.toCellScheme.scope x from
          appendCellScheme_scope_castAdd S F k x] at hd
        have hx : x ∈ Set.range (S.cellMap f) := by
          rw [Scheme.range_cellMap]
          exact Scheme.mem_visibleCells.mpr hd
        obtain ⟨i, rfl⟩ := hx
        exact ⟨i, rfl⟩
  have hcm {i : Fin (S.comap f).card} {j : Fin (S'.comap f).card} (hij : (i : ℕ) = j) :
      Fin.castAdd 1 (S.cellMap f i) = S'.cellMap f j :=
    S'.cellMap_eq_of_strictMono f he hr hij
  refine Scheme.ext (S'.card_visibleCells_eq_of_strictMono f he hr) rfl ?_
    (fun i j hij ↦ ?_) (fun i j hij ↦ ?_) (fun s s' t t' hs ht ↦ ?_)
  · ext C
    simp only [Scheme.comap, CellScheme.reindex, CellScheme.comap, mem_preimage]
    change Finset.map f C ∈ insert F S.toCellScheme.faces ↔ Finset.map f C ∈ S.toCellScheme.faces
    rw [mem_insert, or_iff_right]
    rintro hC
    exact hF (hC ▸ map_subset_map.mpr (subset_univ C))
  · rw [comap_scope, comap_scope, ← hcm hij.symm]
    exact congrArg (fun B ↦ B.preimage f f.injective.injOn) (appendCellScheme_scope_castAdd S F k _)
  · rw [comap_grade, comap_grade, ← hcm hij.symm]
    exact appendCellScheme_grade_castAdd S F k _
  · rw [comap_row, comap_row]
    have e1 := hcm hs.symm
    have e2 := hcm ht.symm
    refine (S'.rows.row_congr e1.symm (t' := ⟨Fin.castAdd 1 (S.cellMap f t'.1), ?_⟩)
      e2.symm).trans ?_
    · rw [e1, e2]
      exact ((S'.isLowerEmbedding_comap f).le_iff t s).mpr t.2
    · rw [appendCell_row_castAdd]
      exact S.rows.row_congr rfl rfl

/-- On three points, the face `{1, 2}` does not lie in the first coatom `{0, 1}`. -/
theorem pair_not_subset_left :
    ¬ ({1, 2} : Finset (Fin 3)) ⊆ univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) := by
  decide

/-- On three points, the face `{1, 2}` does not lie in the second coatom `{0, 2}`. -/
theorem pair_not_subset_right :
    ¬ ({1, 2} : Finset (Fin 3)) ⊆ univ.map (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)) := by
  decide

/-- **The context face is unchanged** by a field cell on the face `{1, 2}`. -/
theorem comap_appendCell_pair_left {S : Scheme.{u} 3} {k : ℕ} {r : Fin (S.card + 1) → Label.{u}}
    {h : ∀ d, ¬ (({1, 2} : Finset (Fin 3)), k) ≤ S.toCellScheme.gradedIndex d} :
    (S.appendCell {1, 2} k r h).comap Fin.castSuccEmb = S.comap Fin.castSuccEmb :=
  comap_appendCell _ pair_not_subset_left

/-- **The donor face is unchanged** by a field cell on the face `{1, 2}`. -/
theorem comap_appendCell_pair_right {S : Scheme.{u} 3} {k : ℕ}
    {r : Fin (S.card + 1) → Label.{u}}
    {h : ∀ d, ¬ (({1, 2} : Finset (Fin 3)), k) ≤ S.toCellScheme.gradedIndex d} :
    (S.appendCell {1, 2} k r h).comap (extendByLast Fin.castSuccEmb) =
      S.comap (extendByLast Fin.castSuccEmb) :=
  comap_appendCell _ pair_not_subset_right

/-- The faces change when `F` is a new face. -/
theorem faces_appendCell_ne (hF : F ∉ S.toCellScheme.faces) :
    (S.appendCell F k r h).toCellScheme.faces ≠ S.toCellScheme.faces := fun he ↦
  hF (he ▸ mem_insert_self F S.toCellScheme.faces)

end Scheme

namespace Coatom

/-- **The face `{1, 2}` is not a face of the amalgam** of two coatom schemes on two points. -/
theorem pair_notMem_amalgamFaces (Sa Sb : Scheme.{u} 2) :
    ({1, 2} : Finset (Fin 3)) ∉ amalgamFaces Sa Sb := by
  rw [mem_amalgamFaces]
  rintro (h | ⟨C, -, hC⟩ | ⟨C, -, hC⟩)
  · exact absurd (h ▸ mem_univ (0 : Fin 3)) (by decide)
  · have : (2 : Fin 3) ∈ C.map (left 1) := hC ▸ (by decide)
    obtain ⟨i, -, hi⟩ := mem_map.mp this
    revert hi
    revert i
    decide
  · have : (1 : Fin 3) ∈ C.map (right 1) := hC ▸ (by decide)
    obtain ⟨i, -, hi⟩ := mem_map.mp this
    revert hi
    revert i
    decide

end Coatom

end VaughtConjecture
