/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryReading

/-!
# The interior scheme: a legal scheme reading through an interior cap at two faces

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap, the marker and the decoder of (R4)); semantic contract, item 8.

**The question.**  A scheme reading the new cells through the cap
(`StageType.IsStableRecoveryScheme.of_readsThroughCap`) reads them at one cell `s` of the grade
`N` of the cap.  By bountifulness the reading constrains every graded face of grade `N`
containing the cap and the new cells, and these faces must read coherently.  When the scope of
the cap avoids both extreme points of the context (an **interior cap**), there are at least two
such faces in every scheme: the new point is an extreme point of the points of the scheme, the
other extreme point is an extreme point of the context, and the face obtained by deleting it
contains the cap and the new point
(`StageType.IsStableRecoveryScheme.exists_face_ne_univ`, in
`VaughtConjecture.Continuation.StableRecoveryInterior`).  An
interior cap of grade `N ≥ 2` needs a context of at least four points.  This file builds a legal
scheme on five points with an interior cap of grade `2` and two reading cells, one at each of the
two graded faces of grade `2` containing the cap and the new cell; the stage types are in
`VaughtConjecture.Continuation.StableRecoveryInterior`.

**The scheme** (`interiorScheme`).  Five points: `0`, `1`, `2` (private), `3` (the root) and `4`
(the new point); the faces are the intervals of `0 < 1 < 2 < 3 < 4`, so `{0, 1, 2, 3}` (the
context) and `{3, 4}` (the root and the new point) are faces.  There is one cell at each of the
thirty-five graded faces (`interiorCells`), so every graded index carries exactly one cell
(`eq_of_gradedIndex_eq`).  Each cell has a **kind** (`cellKind`), with the rows of the kinds of
the reading scheme of `VaughtConjecture.Continuation.StableRecoveryReading` (`kindRow`):

* **dead** (row `⊥`, so labelled `⊥` in every lawful labelling): every cell not listed below;
* the **reference kind**, reading itself at `1`: the marker `({1, 2}, 1)` and the cells at
  `({0, 1, 2}, 1)`, `({1, 2, 3}, 1)`, `({0, 1, 2, 3}, 1)`;
* the **new kind**, reading itself at `1`: the new cell `({3, 4}, 1)` and the cell at
  `({2, 3, 4}, 1)`;
* the **joint kind**, reading the reference kind at `1` and the new and joint kinds at `ω + 1`: the
  cells at `({1, 2, 3, 4}, 1)` and `(univ, 1)`;
* the **cap kind**, reading the reference kind at `1` and itself at `ω + 2`: the cap
  `({1, 2}, 2)` and the cells at `({0, 1, 2}, 2)`, `({1, 2, 3}, 2)`, `({0, 1, 2, 3}, 2)`;
* the **reading kind**, reading the reference, new and joint kinds at `1` and the cap and reading
  kinds at `ω + 2`: the two **reading cells** at `({1, 2, 3, 4}, 2)` and `(univ, 2)`, the two
  graded faces of grade `2` containing the scope `{1, 2}` of the cap and the new point
  (`eq_of_mem_faces_of_subset`).

**Its lawful labellings** (`isLawful_interiorLabel`, `exists_of_isLawfulBelow`).  Below every pair
they are exactly the labellings `interiorLabel A E B` (`⊥` at the dead cells, `A` at the reference
kind, `E` at the new and joint kinds, `B` at the cap and reading kinds) of the reading triples
(`StableRecoveryReading.IsReadingTriple`).  The cells of one kind copy its first cell: a cell `t`
reading a cell `d` below it of the same grade at the value at which it reads itself has
`p t ≤ p d` (locality), and `p d ≤ p t` (availability, with one cell at each graded index).  The
joint cell `({1, 2, 3, 4}, 1)` gives `A ≤ E`, and the reading cell `({1, 2, 3, 4}, 2)` gives
`min A B = min E B`.  So the scheme has the lawful labellings of the reading scheme of
`StableRecoveryReading`, read at more cells; both reading cells decode the new cell.

**Legality** (`isLegal_interiorScheme`): well formed (the interval plan), coded, consistent (each
row is the labelling of a reading triple), complete, and bountiful (`cappedLift_interiorScheme`):
the parameters prescribed below the smaller pair are those of the marker, the new cell and the cap
below it, since every cell of a live kind lies above the first cell of its kind
(`rep_le_of_kind`), so the lift of parameters of the reading scheme
(`StableRecoveryReading.exists_isReadingTriple_lift`) applies unchanged.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryInterior

open Finset Label StageType ThinCompletion
open StableRecoveryReading (IsReadingTriple exists_isReadingTriple_lift)
open Ordinal hiding univ

/-! ### The scheme -/

/-- The cells of the interior scheme on `Fin 5`, with faces the intervals of `0 < 1 < 2 < 3 < 4`:
one cell at each graded face.  The cells `0`–`14` have grade `1`, at `{0}`, `{1}`, `{2}`, `{3}`,
`{4}`, `{0, 1}`, `{1, 2}`, `{2, 3}`, `{3, 4}`, `{0, 1, 2}`, `{1, 2, 3}`, `{2, 3, 4}`,
`{0, 1, 2, 3}`, `{1, 2, 3, 4}`, `univ`; the cells `15`–`24` grade `2`, at the intervals of at
least two points in the same order; the cells `25`–`30` grade `3`, `31`–`33` grade `4`, and `34`
grade `5`. -/
def interiorCells : CellScheme (Fin 35) (Fin 5) :=
  ⟨univ, Geometry.intervalPlan univ,
    ![{0}, {1}, {2}, {3}, {4}, {0, 1}, {1, 2}, {2, 3}, {3, 4}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4},
      {0, 1, 2, 3}, {1, 2, 3, 4}, univ,
      {0, 1}, {1, 2}, {2, 3}, {3, 4}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {0, 1, 2, 3}, {1, 2, 3, 4},
      univ,
      {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {0, 1, 2, 3}, {1, 2, 3, 4}, univ,
      {0, 1, 2, 3}, {1, 2, 3, 4}, univ, univ],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3,
      4, 4, 4, 5]⟩

/-- The kind of each cell: `0` dead, `1` the reference kind (the marker `6` and the cells `9`,
`10`, `12`), `2` the new kind (the new cell `8` and the cell `11`), `3` the joint kind (the cells
`13`, `14`), `4` the cap kind (the cap `16` and the cells `19`, `20`, `22`), `5` the reading kind
(the reading cells `23`, `24`). -/
def cellKind : Fin 35 → Fin 6 :=
  ![0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 2, 1, 3, 3, 0, 4, 0, 0, 4, 4, 0, 4, 5, 5, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0]

/-- The rows, by the kind of the cell and the kind of the cell read (the rows of the kinds of the
reading scheme): the grid points `1`, `ω + 1`, `ω + 2`, or `⊥`. -/
noncomputable def kindRow : Fin 6 → Fin 6 → Label.{u} :=
  ![fun _ ↦ ⊥,
    ![⊥, gridPoint 1 0, ⊥, ⊥, ⊥, ⊥],
    ![⊥, ⊥, gridPoint 1 0, ⊥, ⊥, ⊥],
    ![⊥, gridPoint 1 0, gridPoint 1 1, gridPoint 1 1, ⊥, ⊥],
    ![⊥, gridPoint 1 0, ⊥, ⊥, gridPoint 2 1, ⊥],
    ![⊥, gridPoint 1 0, gridPoint 1 0, gridPoint 1 0, gridPoint 2 1, gridPoint 2 1]]

/-- The **interior scheme** on five points: the cells `interiorCells` with the rows `kindRow`. -/
noncomputable abbrev interiorScheme : Scheme.{u} 5 :=
  ⟨35, interiorCells, ⟨fun s d ↦ kindRow (cellKind s) (cellKind d.1)⟩⟩

/-- The cells of the interior scheme. -/
@[simp] theorem interiorScheme_toCellScheme : interiorScheme.{u}.toCellScheme = interiorCells :=
  rfl

/-- The row of a cell of the interior scheme, by kinds. -/
theorem interiorScheme_row (s : Fin 35) (d) :
    interiorScheme.{u}.rows.row s d = kindRow (cellKind s) (cellKind d.1) :=
  rfl

/-! ### The labellings -/

/-- The labels of the kinds for the parameters `A` (the reference kind), `E` (the new and joint
kinds) and `B` (the cap and reading kinds). -/
noncomputable def kindValue (A E B : Label.{u}) : Fin 6 → Label.{u} := ![⊥, A, E, E, B, B]

/-- The **interior labelling** of parameters `A`, `E`, `B`. -/
noncomputable def interiorLabel (A E B : Label.{u}) (d : Fin 35) : Label.{u} :=
  kindValue A E B (cellKind d)

/-! ### Facts about kinds, checked cell by cell -/

section Kinds

/-- Every graded index carries exactly one cell. -/
theorem eq_of_gradedIndex_eq : ∀ u t : Fin 35,
    interiorCells.gradedIndex u = interiorCells.gradedIndex t → u = t := by
  decide

/-- The cells below a cell of each live kind, by kinds: dead or of the reference kind below the
reference kind; dead or of the new kind below the new kind; not of the cap or reading kinds below
the joint kind; dead, of the reference kind or of the cap kind below the cap kind. -/
private theorem kind_below : ∀ s d : Fin 35,
    interiorCells.gradedIndex d ≤ interiorCells.gradedIndex s →
      (cellKind s = 1 → cellKind d = 0 ∨ cellKind d = 1) ∧
      (cellKind s = 2 → cellKind d = 0 ∨ cellKind d = 2) ∧
      (cellKind s = 3 → (cellKind d : ℕ) ≤ 3) ∧
      (cellKind s = 4 → cellKind d = 0 ∨ cellKind d = 1 ∨ cellKind d = 4) := by
  decide

/-- The cells of the reference, new and joint kinds have grade `1`; the cells of the cap and
reading kinds have grade `2`. -/
private theorem grade_of_kind : ∀ s : Fin 35,
    ((cellKind s : ℕ) ∈ ({1, 2, 3} : Finset ℕ) → interiorCells.grade s = 1) ∧
      ((cellKind s : ℕ) ∈ ({4, 5} : Finset ℕ) → interiorCells.grade s = 2) := by
  decide

/-- Availability, by kinds: a cell whose scope lies in that of `t`, of the same grade, is dead if
`t` is; dead or of the reference kind if `t` is of the reference kind; dead or of the new kind if
`t` is of the new kind; not of the cap or reading kinds if `t` is of the joint kind; and dead or
of the cap or reading kinds if `t` is of the cap or reading kinds. -/
private theorem kind_availability : ∀ s t : Fin 35,
    interiorCells.scope s ⊆ interiorCells.scope t →
    interiorCells.grade s = interiorCells.grade t →
      (cellKind t = 0 → cellKind s = 0) ∧ (cellKind t = 1 → cellKind s = 0 ∨ cellKind s = 1) ∧
      (cellKind t = 2 → cellKind s = 0 ∨ cellKind s = 2) ∧
      (cellKind t = 3 → (cellKind s : ℕ) ≤ 3) ∧
      (4 ≤ (cellKind t : ℕ) → cellKind s = 0 ∨ 4 ≤ (cellKind s : ℕ)) := by
  decide

/-- The first cell of each live kind lies below the cells of that kind: the marker `6` below the
reference, joint and reading kinds, the new cell `8` below the new, joint and reading kinds, the
cap `16` below the cap and reading kinds. -/
theorem rep_le_of_kind : ∀ d : Fin 35,
    (cellKind d = 1 → interiorCells.gradedIndex 6 ≤ interiorCells.gradedIndex d) ∧
      ((cellKind d = 2 ∨ cellKind d = 3) →
        interiorCells.gradedIndex 8 ≤ interiorCells.gradedIndex d) ∧
      ((cellKind d = 4 ∨ cellKind d = 5) →
        interiorCells.gradedIndex 16 ≤ interiorCells.gradedIndex d) := by
  decide

end Kinds

/-! ### Witnesses -/

section Witness

variable {a b : Label.{u}}

private theorem blockConst_gridPoint_zero (k : ℕ) : blockConst a b (gridPoint.{u} k 0) = a := by
  rw [gridPoint, blockConst_block]
  simp

private theorem blockConst_gridPoint_one (k : ℕ) : blockConst a b (gridPoint.{u} k 1) = b := by
  rw [gridPoint, blockConst_block]
  simp

private theorem blockConst_bot : blockConst a b ⊥ = ⊥ := by
  unfold blockConst
  simp

private theorem twoStrip_gridPoint_one_zero {f : Label.{u}} :
    twoStrip a b f (gridPoint.{u} 1 0) = visibilityReplace 2 1 a := by
  rw [gridPoint, twoStrip_block]
  simp

private theorem twoStrip_gridPoint_two_one {f : Label.{u}} :
    twoStrip a b f (gridPoint.{u} 2 1) = visibilityReplace 2 2 b := by
  rw [gridPoint, twoStrip_block]
  simp

end Witness

/-! ### Lawful labellings -/

/-- Locality at `s` from a witness with the suppressor constant at `v` up to `K`, checked by the
kinds of the cells below `s`. -/
private theorem transformsTo_of_kinds {s : Fin 35} {A E B v : Label.{u}} {K : ℕ}
    {σ : Label.{u} → Label.{u}} (hv : interiorLabel A E B s = v)
    (hw : IsWitness (constStepSuppressor K v) σ) (hK : interiorCells.grade s ≤ K)
    (h : ∀ d : Fin 35, interiorCells.gradedIndex d ≤ interiorCells.gradedIndex s →
      min (kindValue A E B (cellKind d)) v = min (σ (kindRow (cellKind s) (cellKind d))) v) :
    TransformsTo (fun d : interiorCells.below (interiorCells.gradedIndex s) ↦ interiorCells.grade d)
      (interiorScheme.{u}.rows.row s)
      (fun d ↦ min (interiorLabel A E B d) (interiorLabel A E B s)) :=
  ⟨_, σ, hw, fun d ↦ by
    -- the labelling of locality at `s`, and the suppressor at the grade of `d`
    change min (interiorLabel A E B d.1) (interiorLabel A E B s) =
      min (σ (kindRow (cellKind s) (cellKind d.1)))
        (if interiorCells.grade d.1 ≤ K then v else ⊥)
    rw [ite_eq_left (show interiorCells.grade d.1 ≤ K from d.2.2.trans hK), hv]
    exact h d.1 d.2⟩

/-- **The interior labellings of reading triples are lawful.**  The shifter is constant at `A` at
the reference kind and at `E` at the new kind; `A` on the natural numbers and `E` above at the
joint kind (`ThinCompletion.isWitness_blockConst`); and the two-strip shifter of `min A B` and `B`
at the cap and reading kinds (`ThinCompletion.isWitness_twoStrip`).  Availability holds by kinds
(`A ≤ E` where a reference cell lies below a joint cell). -/
theorem isLawful_interiorLabel {A E B : Label.{u}} (h : IsReadingTriple A E B) :
    interiorScheme.{u}.rows.IsLawful (interiorLabel A E B) := by
  have hA := h.isSelfVisible_ref
  have hE := h.isSelfVisible_new
  have hB := h.isSelfVisible_cap
  refine ⟨fun d ↦ ?_, fun s ↦ ?_, fun s t hst hg ↦ ?_⟩
  · -- the order law, by kinds
    obtain ⟨g1, g2⟩ := grade_of_kind d
    simp only [interiorLabel]
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    rw [hk] at g1 g2 ⊢
    fin_cases k
    · exact isSelfVisible_bot _
    · rw [g1 (by decide)]; exact hA
    · rw [g1 (by decide)]; exact hE
    · rw [g1 (by decide)]; exact hE
    · rw [g2 (by decide)]; exact hB
    · rw [g2 (by decide)]; exact hB
  · -- locality, by the kind of `s`
    have hx1 : IsSelfVisible 1 (min A B) := hA.min (hB.mono (by omega))
    have hvr : visibilityReplace 2 1 (min A B) = min A B :=
      visibilityReplace_two_one_of_isSelfVisible hx1
    have hBB : visibilityReplace 2 2 B = B := hB
    have hEB : min E B = min A B := h.min_cap_eq.symm
    have hw2 : IsWitness (constStepSuppressor 2 B) (twoStrip (min A B) B B) :=
      isWitness_twoStrip hB
        (by rw [hB.visibilityReplace_eq 0]
            exact visibilityReplace_le_of_le le_rfl hB (min_le_right A B))
        hBB.le
    obtain ⟨k, hk⟩ : ∃ k, cellKind s = k := ⟨_, rfl⟩
    have hg := grade_of_kind s
    rw [hk] at hg
    have hv : interiorLabel A E B s = kindValue A E B k := by rw [interiorLabel, hk]
    fin_cases k
    · -- dead: the label is `⊥`
      convert TransformsTo.bot _ (interiorScheme.{u}.rows.row s) using 1
      funext d
      rw [hv]
      simp [kindValue]
    · -- the reference kind: the constant shifter `A`
      refine transformsTo_of_kinds hv (isWitness_blockConst hA hA le_rfl)
        (by simp at hg; omega) fun d hd ↦ ?_
      rcases (kind_below s d hd).1 hk with h0 | h0 <;>
        simp [hk, h0, kindValue, kindRow, blockConst_bot, blockConst_gridPoint_zero]
    · -- the new kind: the constant shifter `E`
      refine transformsTo_of_kinds hv (isWitness_blockConst hE hE le_rfl)
        (by simp at hg; omega) fun d hd ↦ ?_
      rcases (kind_below s d hd).2.1 hk with h0 | h0 <;>
        simp [hk, h0, kindValue, kindRow, blockConst_bot, blockConst_gridPoint_zero]
    · -- the joint kind: `A` on the natural numbers and `E` above
      refine transformsTo_of_kinds hv (isWitness_blockConst hA hE h.ref_le_new)
        (by simp at hg; omega) fun d hd ↦ ?_
      have hd3 := (kind_below s d hd).2.2.1 hk
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj] at hd3 ⊢
      fin_cases j <;> simp at hd3 <;> simp [hk, kindValue, kindRow, blockConst_bot,
        blockConst_gridPoint_zero, blockConst_gridPoint_one]
    · -- the cap kind: the two-strip shifter
      refine transformsTo_of_kinds hv hw2 (by simp at hg; omega) fun d hd ↦ ?_
      rcases (kind_below s d hd).2.2.2 hk with h0 | h0 | h0 <;>
        simp [hk, h0, kindValue, kindRow, twoStrip_bot, twoStrip_gridPoint_one_zero,
          twoStrip_gridPoint_two_one, hvr, hBB]
    · -- the reading kind: the two-strip shifter, with `min E B = min A B`
      refine transformsTo_of_kinds hv hw2 (by simp at hg; omega) fun d hd ↦ ?_
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj]
      fin_cases j <;> simp [hk, kindValue, kindRow, twoStrip_bot, twoStrip_gridPoint_one_zero,
          twoStrip_gridPoint_two_one, hvr, hBB, hEB]
  · -- availability, by the kind of `t`: the cell `t` itself
    obtain ⟨h0, h1, h2, h3, h45⟩ := kind_availability s t hst hg
    refine ⟨t, rfl, ?_⟩
    -- the interior labelling, by kinds
    change kindValue A E B (cellKind s) ≤ kindValue A E B (cellKind t)
    generalize cellKind s = j at h0 h1 h2 h3 h45 ⊢
    obtain ⟨k, hk⟩ : ∃ k, cellKind t = k := ⟨_, rfl⟩
    rw [hk] at h0 h1 h2 h3 h45 ⊢
    have hAE := h.ref_le_new
    fin_cases k
    · simp [h0 rfl, kindValue]
    · rcases h1 rfl with rfl | rfl <;> simp [kindValue]
    · rcases h2 rfl with rfl | rfl <;> simp [kindValue]
    · have := h3 rfl
      fin_cases j <;> simp_all [kindValue]
    · have := h45 (by simp)
      fin_cases j <;> simp_all [kindValue]
    · have := h45 (by simp)
      fin_cases j <;> simp_all [kindValue]

/-! ### Lawful labellings below a pair -/

section Below

variable {X : Finset (Fin 5) × ℕ}

private theorem mem_below_of_le {d e : Fin 35} (hd : d ∈ interiorCells.below X)
    (h : interiorCells.gradedIndex e ≤ interiorCells.gradedIndex d) :
    e ∈ interiorCells.below X :=
  le_trans h hd

/-- A pair above the marker and the new cell is above the joint cell `13` at `({1, 2, 3, 4}, 1)`;
with the cap, it is above the reading cell `23` at `({1, 2, 3, 4}, 2)`. -/
private theorem mem_joint (h6 : (6 : Fin 35) ∈ interiorCells.below X)
    (h8 : (8 : Fin 35) ∈ interiorCells.below X) :
    (13 : Fin 35) ∈ interiorCells.below X ∧
      ((16 : Fin 35) ∈ interiorCells.below X → (23 : Fin 35) ∈ interiorCells.below X) := by
  obtain ⟨C, j⟩ := X
  have key : ∀ C : Finset (Fin 5), ({1, 2} : Finset (Fin 5)) ⊆ C →
      ({3, 4} : Finset (Fin 5)) ⊆ C → ({1, 2, 3, 4} : Finset (Fin 5)) ⊆ C := by decide
  exact ⟨⟨key C h6.1 h8.1, h6.2⟩, fun h16 ↦ ⟨key C h16.1 h8.1, h16.2⟩⟩

/-- **Every labelling lawful below a pair is an interior labelling** of a reading triple, whose
third parameter is `⊥` when the cap is not below the pair: for `r` lawful below `X` there are `A`,
`E`, `B` with `IsReadingTriple A E B`, `r d = interiorLabel A E B d` at every cell `d` below `X`,
and `B = ⊥` unless the cap `16` is below `X`.  The cells of each kind copy the first cell of the
kind (locality and availability), the joint cell `13` gives `A ≤ E`, and the reading cell `23`
gives `min A B = min E B`. -/
theorem exists_of_isLawfulBelow {r : interiorCells.below X → Label.{u}}
    (hr : interiorScheme.{u}.rows.IsLawfulBelow X r) :
    ∃ A E B, IsReadingTriple A E B ∧ (∀ d, r d = interiorLabel A E B d.1) ∧
      ((16 : Fin 35) ∉ interiorCells.below X → B = ⊥) := by
  classical
  -- `w`: `r` extended by `⊥` to all cells, lawful below `X`
  set w := CellScheme.Rows.extendBot X r with hw
  have hlaw : interiorScheme.{u}.rows.IsLawfulBelow X (fun d ↦ w d) := by
    rw [hw, CellScheme.Rows.restrict_extendBot]
    exact hr
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hlaw
  have hout : ∀ d, d ∉ interiorCells.below X → w d = ⊥ := fun d hd ↦ dite_eq_right hd
  have hsv : ∀ d, IsSelfVisible (interiorCells.grade d) (w d) := fun d ↦ by
    by_cases hd : d ∈ interiorCells.below X
    · exact ho d hd
    · rw [hout d hd]
      exact isSelfVisible_bot _
  have self : ∀ d : Fin 35, d ∈ interiorCells.below (interiorCells.gradedIndex d) :=
    interiorCells.mem_below_gradedIndex
  have hdead : ∀ d, cellKind d = 0 → w d = ⊥ := fun d h0 ↦ by
    by_cases hd : d ∈ interiorCells.below X
    · have := (hl d hd).eq_bot (d := ⟨d, self d⟩) (by rw [interiorScheme_row]; simp [h0, kindRow])
      simpa using this
    · exact hout d hd
  -- locality between two cells read by `s`, and availability into the one cell of a graded index
  have hloc : ∀ s ∈ interiorCells.below X, ∀ a b : Fin 35,
      ∀ (ha : interiorCells.gradedIndex a ≤ interiorCells.gradedIndex s)
        (hb : interiorCells.gradedIndex b ≤ interiorCells.gradedIndex s),
      kindRow (cellKind s) (cellKind a) ≤ kindRow (cellKind s) (cellKind b) →
      interiorCells.grade b ≤ interiorCells.grade a → min (w a) (w s) ≤ min (w b) (w s) :=
    fun s hs a b ha hb hab hg ↦ (hl s hs).le_of_le (d := ⟨a, ha⟩) (d' := ⟨b, hb⟩) hab hg
  have hav : ∀ s t : Fin 35, t ∈ interiorCells.below X →
      interiorCells.gradedIndex s ≤ interiorCells.gradedIndex t →
      interiorCells.grade s = interiorCells.grade t → w s ≤ w t := fun s t ht hst hg ↦ by
    obtain ⟨u, hu, hle⟩ := ha s t ht hst.1 hg
    rwa [eq_of_gradedIndex_eq u t hu] at hle
  -- a cell reading a cell below it of the same grade as it reads itself copies it
  have hcopy : ∀ d t : Fin 35, t ∈ interiorCells.below X →
      interiorCells.gradedIndex d ≤ interiorCells.gradedIndex t →
      interiorCells.grade d = interiorCells.grade t →
      kindRow (cellKind t) (cellKind d) = kindRow (cellKind t) (cellKind t) → w t = w d :=
    fun d t ht hdt hg hrow ↦ by
      have h1 := hloc t ht t d (self t) hdt hrow.symm.le hg.le
      rw [min_self] at h1
      exact le_antisymm (h1.trans (min_le_left _ _)) (hav d t ht hdt hg)
  -- the joint cell `13`: `w 6 ≤ w 8`
  have h13 : (13 : Fin 35) ∈ interiorCells.below X → w 6 ≤ w 8 := fun h13 ↦ by
    have e13 := hcopy 8 13 h13 (by decide) rfl rfl
    exact (hav 6 13 h13 (by decide) rfl).trans e13.le
  -- the reading cell `23`: `w 23 = w 16`, and `w 6`, `w 8` agree below the cap
  have h23 : (23 : Fin 35) ∈ interiorCells.below X →
      w 23 = w 16 ∧ min (w 6) (w 16) = min (w 8) (w 16) := fun h23 ↦ by
    have e23 := hcopy 16 23 h23 (by decide) rfl rfl
    have a1 := hloc 23 h23 6 8 (by decide) (by decide) le_rfl le_rfl
    have a2 := hloc 23 h23 8 6 (by decide) (by decide) le_rfl le_rfl
    rw [e23] at a1 a2
    exact ⟨e23, le_antisymm a1 a2⟩
  have h616 : (16 : Fin 35) ∈ interiorCells.below X → (6 : Fin 35) ∈ interiorCells.below X :=
    fun h16 ↦ mem_below_of_le h16 (by decide)
  refine ⟨if (6 : Fin 35) ∈ interiorCells.below X then w 6 else w 8,
    if (8 : Fin 35) ∈ interiorCells.below X then w 8 else w 6, w 16, ⟨?_, ?_, hsv 16, ?_, ?_⟩,
    fun d ↦ ?_, fun h16 ↦ hout 16 h16⟩
  -- the clauses of `IsReadingTriple`: self-visibility, `A ≤ E`, `min A B = min E B`
  · split_ifs
    exacts [hsv 6, hsv 8]
  · split_ifs
    exacts [hsv 8, hsv 6]
  · by_cases h6 : (6 : Fin 35) ∈ interiorCells.below X <;>
      by_cases h8 : (8 : Fin 35) ∈ interiorCells.below X <;> simp only [h6, h8, ↓reduceIte]
    · exact h13 (mem_joint h6 h8).1
    · exact le_rfl
    · exact le_rfl
    · rw [hout 8 h8, hout 6 h6]
  · by_cases h16 : (16 : Fin 35) ∈ interiorCells.below X
    · have h6 := h616 h16
      by_cases h8 : (8 : Fin 35) ∈ interiorCells.below X
      · simp only [h6, h8, ↓reduceIte]
        exact (h23 ((mem_joint h6 h8).2 h16)).2
      · simp only [h6, h8, ↓reduceIte]
    · rw [hout 16 h16, min_bot_right, min_bot_right]
  · -- the labelling, cell by cell, by kinds
    obtain ⟨d, hd⟩ := d
    rw [← CellScheme.Rows.extendBot_of_mem r hd]
    -- the left side is `w d`, the extension of `r` by `⊥` at a cell below `X`
    change w d = kindValue _ _ _ (cellKind d)
    obtain ⟨r1, r23, r45⟩ := rep_le_of_kind d
    obtain ⟨g1, g2⟩ := grade_of_kind d
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    rw [hk] at r1 r23 r45 g1 g2 ⊢
    fin_cases k
    · rw [hdead d hk]
      rfl
    · have h6 := mem_below_of_le hd (r1 rfl)
      -- the first parameter
      change w d = if (6 : Fin 35) ∈ interiorCells.below X then w 6 else w 8
      rw [ite_eq_left h6]
      exact hcopy 6 d hd (r1 rfl) (by rw [g1 (by decide)]; rfl) (by rw [hk]; rfl)
    · have h8 := mem_below_of_le hd (r23 (.inl rfl))
      -- the second parameter
      change w d = if (8 : Fin 35) ∈ interiorCells.below X then w 8 else w 6
      rw [ite_eq_left h8]
      exact hcopy 8 d hd (r23 (.inl rfl)) (by rw [g1 (by decide)]; rfl) (by rw [hk]; rfl)
    · have h8 := mem_below_of_le hd (r23 (.inr rfl))
      -- the second parameter
      change w d = if (8 : Fin 35) ∈ interiorCells.below X then w 8 else w 6
      rw [ite_eq_left h8]
      exact hcopy 8 d hd (r23 (.inr rfl)) (by rw [g1 (by decide)]; rfl) (by rw [hk]; rfl)
    · exact hcopy 16 d hd (r45 (.inl rfl)) (by rw [g2 (by decide)]; rfl) (by rw [hk]; rfl)
    · exact hcopy 16 d hd (r45 (.inr rfl)) (by rw [g2 (by decide)]; rfl) (by rw [hk]; rfl)

end Below

/-! ### Legality -/

/-- **Every pair lifts capped**: the parameters prescribed below the smaller pair (those of the
marker, the new cell and the cap below it) are kept, the others lifted by
`StableRecoveryReading.exists_isReadingTriple_lift`, and the interior labelling of the lifted
parameters is lawful. -/
theorem cappedLift_interiorScheme {X Y : Finset (Fin 5) × ℕ} (h : X ≤ Y) :
    interiorScheme.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨pA, pE, pB, hpT, hpX, -⟩ := exists_of_isLawfulBelow hp
  obtain ⟨qA, qE, qB, hqT, hqY, hq16⟩ := exists_of_isLawfulBelow hq
  have hagree {d : Fin 35} (hd : d ∈ interiorCells.below X) :
      min (interiorLabel pA pE pB d) c = min (interiorLabel qA qE qB d) c := by
    have := hpq ⟨d, hd⟩
    rw [hpX, hqY] at this
    exact this.symm
  have hc2 : IsSelfVisible 2 c ∨ qB = ⊥ := by
    by_cases h16 : (16 : Fin 35) ∈ interiorCells.below Y
    · exact .inl (hc.mono h16.2)
    · exact .inr (hq16 h16)
  obtain ⟨rA, rE, rB, hrT, hrA, hrE, hrB, hcA, hcE, hcB⟩ :=
    exists_isReadingTriple_lift (xa := (6 : Fin 35) ∈ interiorCells.below X)
      (xe := (8 : Fin 35) ∈ interiorCells.below X) (xb := (16 : Fin 35) ∈ interiorCells.below X)
      hpT hqT hc2 (fun h16 ↦ mem_below_of_le h16 (by decide)) hagree hagree hagree
  refine ⟨fun d ↦ interiorLabel rA rE rB d.1,
    (isLawful_interiorLabel hrT).isLawfulBelow Y, fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hqY]
    obtain ⟨d, hd⟩ := d
    -- the restriction to `Y` at the cell `d`
    change min (kindValue rA rE rB (cellKind d)) c = min (kindValue qA qE qB (cellKind d)) c
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    rw [hk]
    fin_cases k
    exacts [rfl, hcA, hcE, hcE, hcB, hcB]
  · obtain ⟨d, hd⟩ := d
    rw [hpX]
    -- the restriction to `X` at the cell `d`
    change kindValue rA rE rB (cellKind d) = kindValue pA pE pB (cellKind d)
    obtain ⟨r1, r23, r45⟩ := rep_le_of_kind d
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    rw [hk] at r1 r23 r45 ⊢
    fin_cases k
    · rfl
    · exact hrA (le_trans (r1 rfl) hd)
    · exact hrE (le_trans (r23 (.inl rfl)) hd)
    · exact hrE (le_trans (r23 (.inr rfl)) hd)
    · exact hrB (le_trans (r45 (.inl rfl)) hd)
    · exact hrB (le_trans (r45 (.inr rfl)) hd)

/-- **The interior scheme is legal.** -/
theorem isLegal_interiorScheme : interiorScheme.{u}.IsLegal where
  -- well formed: the interval plan, each scope a face, each grade at most the size of the scope
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 35, interiorCells.scope d ∈ interiorCells.faces ∧
        0 < interiorCells.grade d ∧ interiorCells.grade d ≤ #(interiorCells.scope d) := by decide
    exact key d⟩⟩
  -- coded: each row entry is `⊥` or a grid point below `ω ^ 2`
  isCoded s t := by
    have key : ∀ s d : Fin 6, kindRow.{u} s d = ⊥ ∨ kindRow.{u} s d = gridPoint 1 0 ∨
        kindRow.{u} s d = gridPoint 1 1 ∨ kindRow.{u} s d = gridPoint 2 1 := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [kindRow]
    rw [interiorScheme_row]
    rcases key (cellKind s) (cellKind t.1) with h | h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    all_goals exact gridPoint_lt_omega0_sq _ _
  -- consistent: each row is the interior labelling of a reading triple, by the kind of the cell
  isConsistent s := by
    have hrow {A E B : Label.{u}} (hT : IsReadingTriple A E B)
        (h : ∀ d : Fin 35, interiorCells.gradedIndex d ≤ interiorCells.gradedIndex s →
          kindRow (cellKind s) (cellKind d) = kindValue A E B (cellKind d)) :
        interiorScheme.{u}.rows.IsLawfulBelow (interiorCells.gradedIndex s)
          (interiorScheme.{u}.rows.row s) := by
      have : interiorScheme.{u}.rows.row s = fun d ↦ interiorLabel A E B d.1 :=
        funext fun d ↦ h d.1 d.2
      rw [this]
      exact (isLawful_interiorLabel hT).isLawfulBelow _
    have g10 := isSelfVisible_gridPoint.{u} 1 0
    have g11 := isSelfVisible_gridPoint.{u} 1 1
    have g21 := isSelfVisible_gridPoint.{u} 2 1
    have hb {k : ℕ} : IsSelfVisible k (⊥ : Label.{u}) := isSelfVisible_bot _
    have h0 : IsReadingTriple.{u} ⊥ ⊥ ⊥ := ⟨hb, hb, hb, le_rfl, rfl⟩
    have h1 : IsReadingTriple.{u} (gridPoint 1 0) (gridPoint 1 0) ⊥ := ⟨g10, g10, hb, le_rfl, rfl⟩
    have h2 : IsReadingTriple.{u} ⊥ (gridPoint 1 0) ⊥ :=
      ⟨hb, g10, hb, bot_le, by rw [min_bot_right, min_bot_right]⟩
    have h3 : IsReadingTriple.{u} (gridPoint 1 0) (gridPoint 1 1) ⊥ :=
      ⟨g10, g11, hb, gridPoint_le_gridPoint.mpr (by omega), by rw [min_bot_right, min_bot_right]⟩
    have h4 : IsReadingTriple.{u} (gridPoint 1 0) (gridPoint 1 0) (gridPoint 2 1) :=
      ⟨g10, g10, g21, le_rfl, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, cellKind s = k := ⟨_, rfl⟩
    fin_cases k
    · refine hrow h0 fun d _ ↦ ?_
      rw [hk]
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj]; fin_cases j <;> rfl
    · refine hrow h1 fun d hd ↦ ?_
      rcases (kind_below s d hd).1 hk with h0 | h0 <;> rw [hk, h0] <;> rfl
    · refine hrow h2 fun d hd ↦ ?_
      rcases (kind_below s d hd).2.1 hk with h0 | h0 <;> rw [hk, h0] <;> rfl
    · refine hrow h3 fun d _ ↦ ?_
      rw [hk]
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj]; fin_cases j <;> rfl
    · refine hrow h4 fun d hd ↦ ?_
      rcases (kind_below s d hd).2.2.2 hk with h0 | h0 | h0 <;> rw [hk, h0] <;> rfl
    · refine hrow h4 fun d _ ↦ ?_
      rw [hk]
      obtain ⟨j, hj⟩ : ∃ j, cellKind d = j := ⟨_, rfl⟩
      rw [hj]; fin_cases j <;> rfl
  isBountiful _ _ _ _ h := cappedLift_interiorScheme h
  -- complete: one cell at each graded face
  isComplete X hX := by
    obtain ⟨S, j⟩ := X
    obtain ⟨hS, hj0, hjS⟩ := hX
    have hj5 : j ≤ 5 := hjS.trans (by simpa using card_le_univ S)
    have key : ∀ S : Finset (Fin 5), S ∈ interiorCells.faces → ∀ j : Fin 6, 0 < (j : ℕ) →
        (j : ℕ) ≤ #S → ∃ d : Fin 35, interiorCells.gradedIndex d = (S, (j : ℕ)) := by decide
    exact key S hS ⟨j, by omega⟩ hj0 hjS

/-! ### The graded faces of grade `2` containing the cap and the new cell -/

/-- **Two graded faces of grade `2` contain the cap and the new cell**: a face of the interior
scheme containing the scope `{1, 2}` of the cap and the new point `4` is `{1, 2, 3, 4}` or the
ground set, and the cells at these faces of grade `2` are the reading cells `23` and `24`, the
cells of the reading kind. -/
theorem eq_of_mem_faces_of_subset : ∀ S ∈ interiorCells.faces, ({1, 2, 4} : Finset (Fin 5)) ⊆ S →
    S = {1, 2, 3, 4} ∨ S = univ := by
  decide

/-- The cells of the reading kind are the cells `23` at `({1, 2, 3, 4}, 2)` and `24` at
`(univ, 2)`. -/
theorem cellKind_eq_five_iff : ∀ s : Fin 35, cellKind s = 5 ↔ s = 23 ∨ s = 24 := by
  decide

end VaughtConjecture.Continuation.StableRecoveryInterior
