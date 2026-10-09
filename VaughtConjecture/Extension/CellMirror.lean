/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Gluing

/-!
# Mirrored cells: copies of cells at smaller scopes, reading the rows of their originals

Roadmap, Layer 3 ((R3) and (R4), the replication of the full-scope cells into the mixed faces).

A **mirroring** of a cell scheme `D` (`CellScheme.Mirror`) is a family of cells `κ`, each with an
**original** cell of `D` and its own scope inside the scope of the original, of the grade of the
original, such that a cell below another has its original below the other's original.  The
**mirrored cell scheme** (`CellScheme.Mirror.cells`) has these cells, scopes and grades (and the
ground and faces of `D`); the **mirrored rows** (`CellScheme.Mirror.rows`) read, at every cell, the
row of its original at the originals of the cells below.  So a copy of a cell of full scope at a
smaller face reads the row of its original, and an old cell (its own original, same scope) keeps its
row.

* **Pullback of lawful labellings** (`CellScheme.Mirror.isLawfulBelow_comp`,
  `CellScheme.Mirror.isLawful_comp`): a labelling lawful below `X` for the rows of `D`, read
  through the originals, is lawful below every pair `Y` whose cells have originals below `X`,
  provided the mirroring is **saturated** at the cells below `Y`: for every cell `t` and every cell
  `u₀` of `D` of the graded index of the original of `t`, some cell of the mirroring with original
  `u₀` has the scope of `t` (`CellScheme.Mirror.Saturated`) — a copy of every cell of the same
  graded index at the face of every copy.
* **Consistency** (`CellScheme.Mirror.isConsistent_rows`): mirrored rows of consistent rows are
  consistent, for a saturated mirroring.

## References

Lawful sections and consistency are [Kni26, Definitions 2.5.4 and 2.5.12].
-/

universe u

namespace VaughtConjecture.CellScheme

open Label

variable {ι κ α : Type*} (D : CellScheme ι α)

/-- A **mirroring** of `D` by the cells `κ`: an original cell of `D` for each cell, a scope inside
the scope of the original, such that a cell below another (for the new scopes and the grades of the
originals) has its original below the other's original. -/
structure Mirror (κ : Type*) where
  /-- The original of a cell. -/
  orig : κ → ι
  /-- The scope of a cell. -/
  scope : κ → Finset α
  /-- The scope of a cell lies in that of its original. -/
  scope_subset : ∀ k, scope k ⊆ D.scope (orig k)
  /-- A cell below another has its original below the other's original. -/
  le_orig : ∀ k t, (scope t, D.grade (orig t)) ≤ (scope k, D.grade (orig k)) →
    D.gradedIndex (orig t) ≤ D.gradedIndex (orig k)

namespace Mirror

variable {D} (M : D.Mirror κ)

/-- The **mirrored cell scheme**: the cells of the mirroring with their scopes and the grades of
their originals; the ground and faces of `D`. -/
def cells : CellScheme κ α where
  ground := D.ground
  faces := D.faces
  scope := M.scope
  grade k := D.grade (M.orig k)

@[simp] theorem cells_scope (k : κ) : M.cells.scope k = M.scope k := rfl

@[simp] theorem cells_grade (k : κ) : M.cells.grade k = D.grade (M.orig k) := rfl

theorem cells_gradedIndex (k : κ) : M.cells.gradedIndex k = (M.scope k, D.grade (M.orig k)) :=
  rfl

/-- A cell below a pair has its original below the original of any cell of that graded index. -/
theorem orig_mem_below {k t : κ} (ht : t ∈ M.cells.below (M.cells.gradedIndex k)) :
    M.orig t ∈ D.below (D.gradedIndex (M.orig k)) :=
  M.le_orig k t ht

/-- The **mirrored rows**: every cell reads the row of its original at the originals of the cells
below it. -/
def rows (R : D.Rows.{u}) : M.cells.Rows.{u} where
  row k t := R.row (M.orig k) ⟨M.orig t, M.orig_mem_below t.2⟩

@[simp] theorem rows_row (R : D.Rows.{u}) (k : κ) (t : M.cells.below (M.cells.gradedIndex k)) :
    (M.rows R).row k t = R.row (M.orig k) ⟨M.orig t, M.orig_mem_below t.2⟩ := rfl

/-- The mirroring is **saturated** below `Y`: for every cell `t` below `Y` and every cell `u₀` of
`D` of the graded index of the original of `t`, some cell with original `u₀` has the scope of
`t`. -/
def Saturated (Y : Finset α × ℕ) : Prop :=
  ∀ t ∈ M.cells.below Y, ∀ u₀, D.gradedIndex u₀ = D.gradedIndex (M.orig t) →
    ∃ u, M.orig u = u₀ ∧ M.scope u = M.scope t

/-- **Pullback of a labelling lawful below a pair**: a labelling `w` of the cells of `D` lawful
below `X`, read through the originals, is lawful below `Y`, when every cell below `Y` has its
original below `X` and the mirroring is saturated below `Y`. -/
theorem isLawfulBelow_comp {R : D.Rows.{u}} {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X fun d ↦ w d) {Y : Finset α × ℕ}
    (hXY : ∀ t ∈ M.cells.below Y, M.orig t ∈ D.below X) (hsat : M.Saturated Y) :
    (M.rows R).IsLawfulBelow Y fun t ↦ w (M.orig t) := by
  obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  refine (Rows.isLawfulBelow_iff_forall (w := fun t ↦ w (M.orig t))).mpr
    ⟨?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · intro t ht
    exact ho (M.orig t) (hXY t ht)
  · have h := (hl (M.orig s) (hXY s hs)).reindex
      fun t : M.cells.below (M.cells.gradedIndex s) ↦
        (⟨M.orig t, M.orig_mem_below t.2⟩ : D.below (D.gradedIndex (M.orig s)))
    exact h
  · have hle : D.gradedIndex (M.orig s) ≤ D.gradedIndex (M.orig t) :=
      M.le_orig t s ⟨hst, hg.le⟩
    obtain ⟨u₀, hu₀, hle₀⟩ := ha (M.orig s) (M.orig t) (hXY t ht) hle.1 hg
    obtain ⟨u, rfl, hus⟩ := hsat t ht u₀ hu₀
    refine ⟨u, ?_, hle₀⟩
    have hg' : D.grade (M.orig u) = D.grade (M.orig t) := congrArg Prod.snd hu₀
    rw [cells_gradedIndex, cells_gradedIndex, hus, hg']

/-- **Pullback of a lawful section**: a lawful section of `D`, read through the originals, is a
lawful section of the mirrored rows, for a mirroring saturated everywhere. -/
theorem isLawful_comp {R : D.Rows.{u}} {w : ι → Label.{u}} (hw : R.IsLawful w)
    (hsat : ∀ Y, M.Saturated Y) : (M.rows R).IsLawful fun t ↦ w (M.orig t) where
  orderly t := hw.orderly (M.orig t)
  locality s := (hw.locality (M.orig s)).reindex
    fun t : M.cells.below (M.cells.gradedIndex s) ↦
      (⟨M.orig t, M.orig_mem_below t.2⟩ : D.below (D.gradedIndex (M.orig s)))
  availability s t hst hg := by
    have hle : D.gradedIndex (M.orig s) ≤ D.gradedIndex (M.orig t) :=
      M.le_orig t s ⟨hst, hg.le⟩
    obtain ⟨u₀, hu₀, hle₀⟩ := hw.availability (M.orig s) (M.orig t) hle.1 hg
    obtain ⟨u, rfl, hus⟩ := hsat (M.cells.gradedIndex t) t (M.cells.mem_below_gradedIndex t) u₀ hu₀
    refine ⟨u, ?_, hle₀⟩
    have hg' : D.grade (M.orig u) = D.grade (M.orig t) := congrArg Prod.snd hu₀
    rw [cells_gradedIndex, cells_gradedIndex, hus, hg']

/-- **Mirrored rows of consistent rows are consistent**, for a mirroring saturated everywhere. -/
theorem isConsistent_rows {R : D.Rows.{u}} (hR : R.IsConsistent) (hsat : ∀ Y, M.Saturated Y) :
    (M.rows R).IsConsistent := by
  intro k
  classical
  have hw := hR (M.orig k)
  have hw' : R.IsLawfulBelow (D.gradedIndex (M.orig k))
      (fun d ↦ Rows.extendBot (D.gradedIndex (M.orig k)) (R.row (M.orig k)) d) := by
    rwa [Rows.isLawfulBelow_extendBot]
  have h := M.isLawfulBelow_comp hw' (Y := M.cells.gradedIndex k)
    (fun t ht ↦ M.orig_mem_below ht) (hsat _)
  convert h using 1
  funext t
  rw [Rows.extendBot_of_mem _ (M.orig_mem_below t.2)]
  rfl

end Mirror

end VaughtConjecture.CellScheme
