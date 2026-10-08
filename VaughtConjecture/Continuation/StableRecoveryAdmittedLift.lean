/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryCapCorrectness

/-!
# Admitted states at `P`: gluing on the amalgam, and the raise forced on lifts

Roadmap, Layer 3, 3.1 (a completion whose catalogue at the reading grade is restricted) and 3.3;
the capped correctness at the private type `P` of
`VaughtConjecture.Continuation.StableRecoveryCapCorrectness`.

**Gluing** (`Seed.exists_isLawful_glue`).  For a seed whose two coatom types are equal (`T`), two
lawful labellings `sL`, `sR` of `T` agreeing at the cells of `T` avoiding the last point glue to a
lawful labelling of the amalgam, `sL` on the copies along the first coatom and `sR` on the copies
along the second: lawful below each coatom pair through the faces
(`Scheme.isLawfulBelow_faceCell_iff`), and every cell of the amalgam lies on a coatom
(`CellScheme.Rows.IsLawfulBelow.glue`).  At `P`
(`GatedExtensionCounterexample.exists_isLawful_glue_reader_P`): the admitted reader state
`(⊥, ⊥, ⊥, 3, 2 | ⊥, ⊥, ⊥, 3, 3)` is a lawful labelling of the amalgam of the seed of `P` with
itself.

**Recognition at an admitted reader** (`CellScheme.Rows.le_of_row_le_of_locality`,
`GatedExtensionCounterexample.le_of_isAdmittedP_reader`).  If a cell `u` reads `c` at most as it
reads `y` (equal grades), every labelling satisfying locality at `u` with `q c ≤ q u` has
`q c ≤ q y`.  At `P`, with the cap `3` and the marker at the cap: a cell whose row on the old cells
is an admitted state in the bottom class reads the donor's high cells at least as the private cap,
so every lawful labelling that availability lifts above the private cap at that cell has the
donor's high cells at least the private cap.

**The raise forced on the private-coatom lift** (`CellScheme.Rows.le_of_capped_readers`, compiled
for any rows).  If every cell of graded index `(univ, 2)` lifted above the private cap reads the
donor's high cells at least as the cap (admission in the bottom class, marker at the cap), then
every labelling lawful below `(univ, 2)` has the donor's high cells at least the private cap.  So
in a layer of admitted states every lift of `P`'s lawful `(3, 2)` from the private coatom has the
donor's high cells at least `3`: the symmetric fill
`(3, 2 | 3, 2)` that the doubling uses for this lift is excluded
(`GatedExtensionCounterexample.not_isAdmittedP_rowAt_self`), and the lift must raise the donor side,
for instance to `(3, 3)`, which is an admitted, lawful glued state.  Whether a layer of admitted
states is bountiful (the lifts from both coatoms at every cap, with the cross rows of a sheet
layer) is not decided here: the compiled sheet-layer extensions
(`Scheme.extendsFromBoundary_bot_sheetLayer`) take every catalogue entry as a template, which an
admitted layer does not have.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

/-! ### Lawfulness through a face -/

namespace Scheme

variable {n m : ℕ} {S : Scheme.{u} n} {f : Fin m ↪ Fin n} {T : Scheme.{u} m}

/-- **Lawfulness through a face**: a labelling of `S` read on the cells of a face `T` along `f` is
lawful below `X` in `T` exactly when it is lawful below the image of `X` in `S`. -/
theorem isLawfulBelow_faceCell_iff (he : S.comap f = T) (X : Finset (Fin m) × ℕ)
    (x : Fin S.card → Label.{u}) :
    T.rows.IsLawfulBelow X (fun i ↦ x (S.faceCell f he i)) ↔
      S.rows.IsLawfulBelow (Prod.map (Finset.map f) id X) (fun d ↦ x d) := by
  subst he
  exact S.isLawfulBelow_comap_cellMap_iff f X x

end Scheme

/-! ### Gluing two labellings on the amalgam of a type with itself -/

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m) (hLR : I.left = I.right)

/-- A copy along the second coatom that also lies on the first is a cell of `T` avoiding the last
point. -/
theorem last_notMem_of_faceCell_right_mem {z : Fin I.left.card}
    (hz : StageType.faceCell (I.restrictFace_right_left hLR) z ∈
      I.amalgam.toScheme.visibleCells (Coatom.left m)) :
    Fin.last m ∉ I.left.toCellScheme.scope z := by
  intro hm
  have h := I.faceCell_left_doublingCell hLR hz
  rw [I.doublingCell_faceCell_right hLR] at h
  have hs := congrArg (fun d ↦ I.amalgam.toCellScheme.scope d) h
  simp only [StageType.scope_faceCell] at hs
  have hl : Coatom.right m (Fin.last m) ∈ (I.left.toCellScheme.scope z).map (Coatom.left m) :=
    hs ▸ mem_map_of_mem _ hm
  obtain ⟨y, -, hy⟩ := mem_map.mp hl
  rw [Coatom.right, extendByLast_last] at hy
  exact (Fin.castSucc_lt_last y).ne hy

open Classical in
/-- **Gluing on the amalgam**: two lawful labellings of `T` agreeing at the cells avoiding the last
point glue to a lawful labelling of the amalgam of `T` with itself, the first on the copies along
the first coatom and the second on the copies along the second. -/
theorem exists_isLawful_glue {sL sR : Fin I.left.card → Label.{u}}
    (hL : I.left.rows.IsLawful sL) (hR : I.left.rows.IsLawful sR)
    (hagree : ∀ z, Fin.last m ∉ I.left.toCellScheme.scope z → sL z = sR z) :
    ∃ w : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawful w ∧
      (∀ z, w (StageType.faceCell I.restrictFace_left z) = sL z) ∧
      ∀ z, w (StageType.faceCell (I.restrictFace_right_left hLR) z) = sR z := by
  set w : Fin I.amalgam.card → Label.{u} := fun d ↦
    if d ∈ I.amalgam.toScheme.visibleCells (Coatom.left m) then sL (I.doublingCell hLR d)
    else sR (I.doublingCell hLR d)
  have hwL (z : Fin I.left.card) : w (StageType.faceCell I.restrictFace_left z) = sL z := by
    have h : StageType.faceCell I.restrictFace_left z ∈
        I.amalgam.toScheme.visibleCells (Coatom.left m) :=
      I.amalgam.toScheme.faceCell_mem_visibleCells _ z
    simp only [w, h, ↓reduceIte, I.doublingCell_faceCell_left hLR]
  have hwR (z : Fin I.left.card) :
      w (StageType.faceCell (I.restrictFace_right_left hLR) z) = sR z := by
    by_cases h : StageType.faceCell (I.restrictFace_right_left hLR) z ∈
        I.amalgam.toScheme.visibleCells (Coatom.left m)
    · simp only [w, h, ↓reduceIte, I.doublingCell_faceCell_right hLR]
      exact hagree z (I.last_notMem_of_faceCell_right_mem hLR h)
    · simp only [w, h, ↓reduceIte, I.doublingCell_faceCell_right hLR]
  have hU : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))).map (Coatom.left m),
      m + 1) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_faceCell_iff
      (StageType.comap_toScheme_of_restrictFace I.restrictFace_left) (univ, m + 1) w).mp ?_
    convert hL.isLawfulBelow ((univ : Finset (Fin (m + 1))), m + 1) using 1
    funext i
    exact hwL i
  have hV : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 1))).map (Coatom.right m),
      m + 1) fun d ↦ w d := by
    refine (Scheme.isLawfulBelow_faceCell_iff
      (StageType.comap_toScheme_of_restrictFace (I.restrictFace_right_left hLR)) (univ, m + 1)
        w).mp ?_
    convert hR.isLawfulBelow ((univ : Finset (Fin (m + 1))), m + 1) using 1
    funext i
    exact hwR i
  have hgrade (d : Fin I.amalgam.card) : I.amalgam.toCellScheme.grade d ≤ m + 1 :=
    Nat.lt_succ_iff.mp (I.grade_lt d)
  have hY : I.amalgam.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), m + 1)
      fun d ↦ w d := by
    refine CellScheme.Rows.IsLawfulBelow.glue hU hV fun d _ ↦ ?_
    rcases I.mem_visibleCells_or d with hd | hd
    · refine Or.inl ⟨fun x hx ↦ ?_, hgrade d⟩
      obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hd hx
      exact mem_map.mpr ⟨y, mem_univ _, hy⟩
    · refine Or.inr ⟨fun x hx ↦ ?_, hgrade d⟩
      obtain ⟨y, hy⟩ := Scheme.mem_visibleCells.mp hd hx
      exact mem_map.mpr ⟨y, mem_univ _, hy⟩
  exact ⟨w, hY.isLawful fun d ↦ ⟨subset_univ _, hgrade d⟩, hwL, hwR⟩

end Seed

/-! ### Recognition at a reader -/

namespace CellScheme.Rows

variable {ι α : Type*} [Finite ι] {D : CellScheme ι α} {R : D.Rows.{u}} {q : ι → Label.{u}}

omit [Finite ι] in
/-- **Recognition at a reader**: if `u` reads `c` at most as it reads `y`, and `y` has grade at
most that of `c`, then every labelling satisfying locality at `u` with `q c ≤ q u` has
`q c ≤ q y`. -/
theorem le_of_row_le_of_locality {u : ι}
    (hloc : TransformsTo (fun d : D.below (D.gradedIndex u) ↦ D.grade d) (R.row u)
      fun d ↦ min (q d) (q u))
    {c y : D.below (D.gradedIndex u)} (hg : D.grade y ≤ D.grade c) (hrow : R.row u c ≤ R.row u y)
    (hcu : q c ≤ q u) : q c ≤ q y := by
  have h := hloc.le_of_le hrow hg
  rw [min_eq_left hcu] at h
  exact h.trans (min_le_left _ _)

omit [Finite ι] in
/-- **The raise is forced in a layer of capped readers.**  Let `w` be lawful below `Y`, with a cell
`G` of graded index `Y` below `Y`, and a cell `c` (the private cap) with scope in that of `G` and
the grade of `G`.  Suppose every cell `u` of graded index `Y` with `w c ≤ w u` reads the cells
`y₃`, `y₄` (of grade at most that of `c`) at least as it reads `c` (the capped reading, which is
admission in the bottom class with the marker at the cap,
`GatedExtensionCounterexample.isCapCorrectP_self_iff`).  Then `w c ≤ w y₃` and `w c ≤ w y₄`:
availability against `G` reaches such a cell, and locality there transfers the reading. -/
theorem le_of_capped_readers {Y : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow Y fun d ↦ w d) {G : ι} (hG : G ∈ D.below Y)
    {c y₃ y₄ : ι} (hcs : D.scope c ⊆ D.scope G) (hcg : D.grade c = D.grade G)
    (hread : ∀ u, D.gradedIndex u = D.gradedIndex G → w c ≤ w u →
      ∃ (hc : c ∈ D.below (D.gradedIndex u)) (h₃ : y₃ ∈ D.below (D.gradedIndex u))
        (h₄ : y₄ ∈ D.below (D.gradedIndex u)), D.grade y₃ ≤ D.grade c ∧
          D.grade y₄ ≤ D.grade c ∧ R.row u ⟨c, hc⟩ ≤ R.row u ⟨y₃, h₃⟩ ∧
            R.row u ⟨c, hc⟩ ≤ R.row u ⟨y₄, h₄⟩) :
    w c ≤ w y₃ ∧ w c ≤ w y₄ := by
  obtain ⟨-, hloc, havail⟩ := isLawfulBelow_iff_forall.mp hw
  obtain ⟨u, hu, hcu⟩ := havail c G hG hcs hcg
  have huY : u ∈ D.below Y := by
    rw [CellScheme.mem_below, hu]
    exact hG
  obtain ⟨hc, h₃, h₄, hg₃, hg₄, hr₃, hr₄⟩ := hread u hu hcu
  exact ⟨le_of_row_le_of_locality (q := w) (c := ⟨c, hc⟩) (y := ⟨y₃, h₃⟩) (hloc u huY) hg₃
      hr₃ hcu,
    le_of_row_le_of_locality (q := w) (c := ⟨c, hc⟩) (y := ⟨y₄, h₄⟩) (hloc u huY) hg₄ hr₄ hcu⟩

end CellScheme.Rows

namespace GatedExtensionCounterexample

/-- **The admitted reader state is a lawful labelling of the amalgam** of the seed of `P` with
itself: `(⊥, ⊥, ⊥, 3, 2)` on the private copy and `(⊥, ⊥, ⊥, 3, 3)` on the donor copy. -/
theorem exists_isLawful_glue_reader_P (β : Ordinal.{u}) :
    ∃ w : Fin (seedP β).amalgam.card → Label.{u}, (seedP β).amalgam.rows.IsLawful w ∧
      (∀ z, w (StageType.faceCell (seedP β).restrictFace_left z) =
        labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) z) ∧
      ∀ z, w (StageType.faceCell ((seedP β).restrictFace_right_left rfl) z) =
        labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) z := by
  obtain ⟨sL, sR, hL, hR, -, -, -, -, -, -, -⟩ := exists_admitted_reader_P.{u}
  have hR' : rows.{u}.IsLawful (labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u})) := by
    have h := isLawful_labelling_top_top.{u}.min_const_of_isSelfVisible (K := 2)
      (c := ((3 : ℕ) : Label.{u})) (fun d ↦ by fin_cases d <;> decide) (by simp)
    convert h using 1
    funext d
    fin_cases d <;> simp [labelling]
  refine (seedP β).exists_isLawful_glue rfl isLawful_labelling_three_two hR' ?_
  change ∀ z : Fin 5, Fin.last 1 ∉ cellScope z →
    labelling ((3 : ℕ) : Label.{u}) ((2 : ℕ) : Label.{u}) z =
      labelling ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) z
  intro z hz
  fin_cases z
  · rfl
  all_goals exact absurd (by decide) hz

/-- **Recognition at an admitted reader of `P`** (cap `3`, marker at the cap).  Let a cell `u` read
the private cap `c₃` and the donor's high cells `y₃`, `y₄` (all of grade `2`) as an admitted state
`(sL, sR)` in the bottom class, with `sL 3` self-visible at `2`.  Every labelling satisfying
locality at `u` with `q c₃ ≤ q u` has the donor's high cells at least the private cap. -/
theorem le_of_isAdmittedP_reader {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}
    {q : ι → Label.{u}} {u : ι}
    (hloc : TransformsTo (fun d : D.below (D.gradedIndex u) ↦ D.grade d) (R.row u)
      fun d ↦ min (q d) (q u))
    {c₃ y₃ y₄ : D.below (D.gradedIndex u)} (hg₃ : D.grade y₃ ≤ D.grade c₃)
    (hg₄ : D.grade y₄ ≤ D.grade c₃) {sL sR : Fin 5 → Label.{u}} {R' : ℕ}
    (hc : R.row u c₃ = sL 3) (hy₃ : R.row u y₃ = sR 3) (hy₄ : R.row u y₄ = sR 4)
    (hadm : IsAdmittedP 3 3 R' sL sR) (hclass : InBottomClassP sL)
    (hvis : IsSelfVisible 2 (sL 3)) (hcu : q c₃ ≤ q u) :
    q c₃ ≤ q y₃ ∧ q c₃ ≤ q y₄ := by
  have hT := ((isCapCorrectP_self_iff hvis).mp (hadm hclass)).2
  exact ⟨CellScheme.Rows.le_of_row_le_of_locality hloc hg₃
      (by rw [hc, hy₃]; exact hT 3 (by simp [selfT])) hcu,
    CellScheme.Rows.le_of_row_le_of_locality hloc hg₄
      (by rw [hc, hy₄]; exact hT 4 (by simp [selfT])) hcu⟩

end GatedExtensionCounterexample

end VaughtConjecture
