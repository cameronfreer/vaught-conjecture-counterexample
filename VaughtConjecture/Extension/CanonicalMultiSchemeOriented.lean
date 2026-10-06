/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CanonicalMultiScheme

/-!
# Oriented copy rows: the canonical multi-layer scheme over an ordered-layer step

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: copy
rows for the canonical multi-layer scheme that restrict the pairs of coatom labellings, and the
step of the family under them); semantic contract, items 2–4.

Let `I` be a seed on five points, with coatoms `C = {0, 1, 2, 3}`, `D = {0, 1, 2, 4}`.  The
canonical multi-layer scheme `canonicalMultiScheme I R`
(`VaughtConjecture.Extension.CanonicalMultiScheme`) puts at each `(univ, k)` two copies, of the
cells at `(C, k)` and `(D, k)`, each reading every cell through its base by its copy row.  The
family is defined for every seed, and its uniform clauses are compiled there.  Its product clause
(`Seed.CanonicalProduct`: the lawful labellings are all pairs of coatom labellings agreeing on the
common face) is a sufficient hypothesis for its step, refuted at the grades `2`, `3`, `4` of the
five seeds `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` and at the grade `4` of `seedHG`
(`VaughtConjecture.Extension.CanonicalMultiSchemeCounterexample`).  This module gives one choice
of copy rows that restricts the pairs instead, and determines exactly when it gives the step.

**Oriented layer rows** (`OrderedLayer.IsOriented ρ b`, a condition on layer rows `ρ` and a copy
index `b` that does not involve the seed).  The layer rows of the ordered-layer step
(`VaughtConjecture.Extension.OrderedLayerStep`) read graded indices.  They *orient the two coatoms
toward `b`* when the row at `(univ, k)` reads the full graded face `(univ, j)`, `j ≤ k`, as it
reads the graded face `(copyCoatom b, j)` of the coatom `b` (`IsOriented.read`), and reads the
full graded face `(copyCoatom i, k)` of either coatom at most as it reads that of the coatom `b`
(`IsOriented.le`).  At the compiled seeds the coatom `b` is `D` (the rows read the parameter of
grade `1` of `C` below that of `D`, in an earlier block, or at the same value), or `C` for the
mirror seed `seedLM`.

**The oriented rows** (`OrderedLayer.orientedRows I ρ`): both copies of grade `k + 1` read every
cell of the amalgam by `ρ (k + 1)`, through its graded index.  So both copies read with the one
orientation of the layer rows: the copy of the coatom `b` reads its own coatom's parameters at
least as high as the other coatom's, and the other copy reads them in the same order.  This is one
choice of the copy rows; the choice under which each copy reads its own coatom above the other
(opposite orientations for the two copies of a grade) is not the one made here (it is
`OrderedLayer.ownSideRows`, `VaughtConjecture.Extension.CanonicalMultiSchemeOwnSide`, which fails
at `seedHG`, `seedL` and `seedLM`).

**The lawful labellings** (compiled, for every seed and all oriented layer rows).  The *layer
base* of a cell of the layer scheme (`OrderedLayer.layerBase`) is the cell itself for an old
cell, and the original of the copy `b` of grade `k` for the new cell at `(univ, k)`.

* *From the layer scheme* (`OrderedLayer.isLawfulBelow_oriented_of_layer`): a labelling lawful
  below `(univ, j)` in the layer scheme, read through the bases, is lawful below `(univ, j)` in
  the canonical multi-layer scheme.  Locality at a copy is locality at the new cell of its grade
  capped at the label of the original (`Label.TransformsTo.min_const`), read along the bases;
  availability into a copy goes through the new cell, whose label is that of the original of the
  copy `b` (`OrderedLayer.newCell_bounds_of_isLawfulBelow`,
  `OrderedLayer.eq_layerBase_of_isLawfulBelow`): the new cell reads itself and that original at
  one value.
* *To the layer scheme* (`OrderedLayer.isLawfulBelow_layer_of_oriented`): a labelling lawful below
  `(univ, j)` in the canonical multi-layer scheme, read through the layer bases, is lawful below
  `(univ, j)` in the layer scheme.  Locality at the new cell of grade `k` is locality at the copy
  `b` of grade `k`, read along the layer bases; availability into the new cell uses that the
  original of the other copy is at most that of the copy `b` (the orientation `IsOriented.le`,
  read by the locality of the other copy).
* *The classification* (`OrderedLayer.isLawfulBelow_oriented_iff`): the lawful labellings below
  `(univ, j)` are read through the bases, and on the old cells they are exactly the lawful
  labellings of the layer scheme.  These form a subset of the pairs of coatom labellings agreeing
  on the common face (a *restriction of the pairs*, not the fibre product): at `seedL`, for
  example, the new cells of the layer scheme impose `A_C ≤ A_D` and `F_C = F_D`
  (`ThinCompletion.IsThinLawfulBelow`).

**The step** (compiled).  For layer rows oriented toward `b`, the canonical multi-layer scheme of
the oriented rows has the multi-layer step exactly when the layer scheme has the ordered-layer step
(`Seed.canonicalMultiStep_oriented_iff`):

* `Seed.canonicalMultiStep_of_orderedLayerStep`: the coding and consistency of the copy rows and
  the lawful extension of the glued labelling come from the layer scheme; a capped lift from a
  coatom into `(univ, k)` is the lift of the layer scheme, with the ambient read through the layer
  bases and the lift read back through the bases (`OrderedLayer.cappedLift_oriented`);
* `Seed.orderedLayerStep_of_canonicalMultiStep_oriented`: the converse, symmetrically
  (`OrderedLayer.cappedLift_layer_of_oriented`).

This iff is an exact reformulation of the ordered-layer step: both copies of a grade read alike,
so under oriented rows the family adds nothing to the layer scheme.  The clause for these rows is
the ordered-layer step itself, with oriented rows (`Seed.HasOrientedLayerStep`); it gives a step
of the canonical multi-layer scheme (`Seed.HasOrientedLayerStep.hasCanonicalMultiStep`) and a
completion below the full grade (`Seed.nonempty_completionBelowFullGrade_of_orderedLayerStep`),
and oriented rows give a step exactly at the seeds whose ordered-layer step has oriented rows.

**Status** (`VaughtConjecture.Extension.CanonicalMultiSchemeOrientedExamples`).  The five seeds
`seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` have ordered-layer steps with oriented rows; those
steps already complete them (`Seed.orderedLayerStep_seed4`, `…_seed5`, `…_seedL`, `…_seedLM`,
`…_seedLL`), and what is new is only that the canonical multi-layer scheme itself has a step at
them.  Oriented rows give `seedHG` no step, since it has no ordered-layer step; so they give no
completion of `seedHG` by the canonical multi-layer scheme, whose step with given rows is exactly
the content of such a completion (`Seed.multiLayerStep_iff`).  The family has a step at `seedHG`
with the rows of the product clause below the top grade (`Seed.canonicalMultiStep_of_TH_TG`).
No oriented layer rows serve both `seedL` and `seedLM`.  So the canonical multi-layer scheme has a
step at every compiled seed (`Seed.hasCanonicalMultiStep_seed4_seed5_seedL_seedLM_seedLL_seedHG`),
and no seed refutes it; the fibre product was refuted at those seeds and grades; oriented rows are
one choice of the copy rows, and they are not uniform in the seed.  Whether some choice of copy
rows gives the step for every seed on five points (`Seed.HasCanonicalMultiStep` for every seed) is
open; oriented rows are not such a choice, since they fail at `seedHG`.  The rows of `seedHG` in
the family (`CanonicalHG.rowsHG`) read the two copies of the grade `1` in opposite orientations,
each its own coatom's parameter above the other's; at the grades `2` and `3` they read both copies
alike, toward `C` and toward `D`, as every step of the family at `seedHG` must
(`Seed.copyRows_lt_two_of_TH_TG`, `Seed.copyRows_lt_three_of_TH_TG`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion has the shape of [Kni26, Definition 4.3.14] (the old cells kept, the new cells of
full scope, several at one graded face); its rows are not those of that definition, and neither
printed proof of [Kni26, Lemma 4.3.16] or [Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture

namespace Label

variable {D D' : Type*} {grade : D → ℕ} {p q : D → Label.{u}}

/-- **A transformation read along a map**: if `p` transforms to `q`, then `p'` transforms to `q'`
whenever the grades, sources and targets of `p'` and `q'` are those of `p` and `q` along a map.
The pointwise form of `Label.TransformsTo.reindex`. -/
theorem TransformsTo.of_comp (h : TransformsTo grade p q) {grade' : D' → ℕ}
    {p' q' : D' → Label.{u}} (φ : D' → D) (hg : ∀ d, grade' d = grade (φ d))
    (hp : ∀ d, p' d = p (φ d)) (hq : ∀ d, q' d = q (φ d)) : TransformsTo grade' p' q' := by
  rw [show grade' = grade ∘ φ from funext hg, show p' = p ∘ φ from funext hp,
    show q' = q ∘ φ from funext hq]
  exact h.reindex φ

end Label

namespace OrderedLayer

open Finset Label CellScheme

/-! ### Oriented layer rows -/

/-- **Layer rows oriented toward the coatom `copyCoatom b`**: the row at `(univ, k)` reads the full
graded face `(univ, j)`, `j ≤ k`, as it reads the graded face `(copyCoatom b, j)`, and reads the
full graded face of either coatom at the grade `k` at most as that of `copyCoatom b`. -/
structure IsOriented (ρ : LayerRows.{u}) (b : Fin 2) : Prop where
  /-- The row at `(univ, k)` reads `(univ, j)` as `(copyCoatom b, j)`, for `1 ≤ j ≤ k ≤ 4`. -/
  read : ∀ k j : ℕ, 1 ≤ j → j ≤ k → k ≤ 4 →
    ρ k ((univ : Finset (Fin 5)), j) = ρ k (copyCoatom b, j)
  /-- The row at `(univ, k)` reads `(copyCoatom i, k)` at most as `(copyCoatom b, k)`. -/
  le : ∀ (k : ℕ) (i : Fin 2), 1 ≤ k → k ≤ 4 → ρ k (copyCoatom i, k) ≤ ρ k (copyCoatom b, k)

variable {α : Ordinal.{u}} (I : Seed.{u} α 3) (ρ : LayerRows.{u})

/-- **The oriented rows** of layer rows `ρ`: both copies of grade `k + 1` read every cell of the
amalgam by `ρ (k + 1)`, through its graded index. -/
noncomputable def orientedRows : CopyRows I :=
  fun k _ d ↦ ρ ((k : ℕ) + 1) (I.amalgam.toCellScheme.gradedIndex d)

/-- The oriented rows read the graded index. -/
theorem orientedRows_apply (k : Fin 4) (i : Fin 2) (d : Fin I.amalgam.card) :
    orientedRows I ρ k i d = ρ ((k : ℕ) + 1) (I.amalgam.toCellScheme.gradedIndex d) := rfl

/-- **The layer base** of a cell of the layer scheme, for the copy `b`: an old cell is its own
layer base, and the new cell at `(univ, k + 1)` has layer base the original `copyOrig I k b`. -/
noncomputable def layerBase (b : Fin 2) (z : Fin (layerScheme I ρ).card) : Fin I.amalgam.card :=
  Fin.lastCases (motive := fun _ ↦ Fin I.amalgam.card) (copyOrig I 3 b)
    (Fin.lastCases (motive := fun _ ↦ Fin I.amalgam.card) (copyOrig I 2 b)
      (Fin.lastCases (motive := fun _ ↦ Fin I.amalgam.card) (copyOrig I 1 b)
        (Fin.lastCases (motive := fun _ ↦ Fin I.amalgam.card) (copyOrig I 0 b) id)))
    (show Fin (I.amalgam.card + 1 + 1 + 1 + 1) from z)

variable {I ρ}

/-- An old cell is its own layer base. -/
@[simp] theorem layerBase_oldCell (b : Fin 2) (d : Fin I.amalgam.card) :
    layerBase I ρ b (oldCell I ρ d) = d := by
  simp [layerBase, oldCell]

/-- The new cell at `(univ, k + 1)` has layer base the original of the copy `b` of grade
`k + 1`. -/
@[simp] theorem layerBase_newCell (b : Fin 2) (k : Fin 4) :
    layerBase I ρ b (newCell I ρ ((k : ℕ) + 1)) = copyOrig I k b := by
  fin_cases k <;> simp [layerBase, newCell]

/-- A cell and its layer base have one grade. -/
theorem grade_layerBase (b : Fin 2) (z : Fin (layerScheme I ρ).card) :
    I.amalgam.toCellScheme.grade (layerBase I ρ b z) = (layerScheme I ρ).toCellScheme.grade z := by
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [layerBase_oldCell, grade_oldCell]
  · rw [show layerBase I ρ b (newCell I ρ 1) = copyOrig I 0 b from layerBase_newCell b 0,
      grade_copyOrig, grade_newCell le_rfl (by omega)]; rfl
  · rw [show layerBase I ρ b (newCell I ρ 2) = copyOrig I 1 b from layerBase_newCell b 1,
      grade_copyOrig, grade_newCell (by omega) (by omega)]; rfl
  · rw [show layerBase I ρ b (newCell I ρ 3) = copyOrig I 2 b from layerBase_newCell b 2,
      grade_copyOrig, grade_newCell (by omega) (by omega)]; rfl
  · rw [show layerBase I ρ b (newCell I ρ 4) = copyOrig I 3 b from layerBase_newCell b 3,
      grade_copyOrig, grade_newCell (by omega) le_rfl]; rfl

/-- **Oriented rows read the layer base**: under an orientation toward `b`, the row at
`(univ, k)` reads the layer base of a cell of grade at most `k` as it reads the cell. -/
theorem row_layerBase {b : Fin 2} (hρ : IsOriented ρ b) {k : ℕ} (hk4 : k ≤ 4)
    {z : Fin (layerScheme I ρ).card} (hz : (layerScheme I ρ).toCellScheme.grade z ≤ k) :
    ρ k (I.amalgam.toCellScheme.gradedIndex (layerBase I ρ b z)) =
      ρ k ((layerScheme I ρ).toCellScheme.gradedIndex z) := by
  have new (k' : Fin 4) (hz' : (k' : ℕ) + 1 ≤ k) :
      ρ k (I.amalgam.toCellScheme.gradedIndex (layerBase I ρ b (newCell I ρ ((k' : ℕ) + 1)))) =
        ρ k ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ ((k' : ℕ) + 1))) := by
    rw [layerBase_newCell, gradedIndex_copyOrig, gradedIndex_newCell (by omega) (by omega)]
    exact (hρ.read k _ (by omega) hz' hk4).symm
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [layerBase_oldCell, gradedIndex_oldCell]
  · exact new 0 (by rw [grade_newCell le_rfl (by omega)] at hz; simpa using hz)
  · exact new 1 (by rw [grade_newCell (by omega) (by omega)] at hz; simpa using hz)
  · exact new 2 (by rw [grade_newCell (by omega) (by omega)] at hz; simpa using hz)
  · exact new 3 (by rw [grade_newCell (by omega) le_rfl] at hz; simpa using hz)

/-! ### The lawful labellings -/

variable {R : CopyRows I}

/-- An old cell lies below a pair in the canonical multi-layer scheme exactly when it does in the
amalgam. -/
private theorem multiOldCell_mem_below_iff {d : Fin I.amalgam.card}
    {X : Finset (Fin 5) × ℕ} :
    multiOldCell I canonicalMult d ∈ (canonicalMultiScheme I R).toCellScheme.below X ↔
      d ∈ I.amalgam.toCellScheme.below X := by
  rw [CellScheme.mem_below, gradedIndex_multiOldCell]; rfl

/-- An old cell lies below a pair in the layer scheme exactly when it does in the amalgam. -/
private theorem oldCell_mem_below_iff {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ} :
    oldCell I ρ d ∈ (layerScheme I ρ).toCellScheme.below X ↔
      d ∈ I.amalgam.toCellScheme.below X := by
  rw [CellScheme.mem_below, gradedIndex_oldCell]; rfl

/-- **The new cells of a lawful labelling of the layer scheme**, for layer rows oriented toward
`b`: below `(univ, j)`, the new cell at `(univ, k + 1)`, `k + 1 ≤ j`, is at least every old cell of
grade `k + 1` (availability) and at most the original of the copy `b` of grade `k + 1` (it reads
itself and that original at one value). -/
theorem newCell_bounds_of_isLawfulBelow {b : Fin 2} (hρ : IsOriented ρ b) {j : ℕ}
    {W : Fin (layerScheme I ρ).card → Label.{u}}
    (hW : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j) fun z ↦ W z)
    (k : Fin 4) (hkj : (k : ℕ) + 1 ≤ j) :
    newCell I ρ ((k : ℕ) + 1) ∈ (layerScheme I ρ).toCellScheme.below
      ((univ : Finset (Fin 5)), j) ∧
    (∀ d : Fin I.amalgam.card, I.amalgam.toCellScheme.grade d = (k : ℕ) + 1 →
      W (oldCell I ρ d) ≤ W (newCell I ρ ((k : ℕ) + 1))) ∧
    W (newCell I ρ ((k : ℕ) + 1)) ≤ W (oldCell I ρ (copyOrig I k b)) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  have hN1 : 1 ≤ (k : ℕ) + 1 := by omega
  have hN4 : (k : ℕ) + 1 ≤ 4 := by omega
  have hN := newCell_mem_below (I := I) (ρ := ρ) hN1 hN4 hkj
  refine ⟨hN, fun d hd ↦ ?_, ?_⟩
  · obtain ⟨u, hu, hle⟩ := ha (oldCell I ρ d) _ hN
      (by rw [scope_newCell hN1 hN4]; exact subset_univ _)
      (by rw [grade_oldCell, grade_newCell hN1 hN4, hd])
    rw [gradedIndex_newCell hN1 hN4] at hu
    rwa [eq_newCell hN1 hN4 hu] at hle
  · -- The new cell reads itself and the original of the copy `b` at one value.
    have hL := hl _ hN
    have hself := (layerScheme I ρ).toCellScheme.mem_below_gradedIndex (newCell I ρ ((k : ℕ) + 1))
    have hob : oldCell I ρ (copyOrig I k b) ∈ (layerScheme I ρ).toCellScheme.below
        ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ ((k : ℕ) + 1))) := by
      rw [gradedIndex_newCell hN1 hN4]
      exact oldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_copyOrig I k b).le⟩
    have := hL.le_of_le (d := ⟨_, hself⟩) (d' := ⟨_, hob⟩) (by
      rw [row_newCell hN1 hN4, row_newCell hN1 hN4, gradedIndex_oldCell, gradedIndex_copyOrig,
        gradedIndex_newCell hN1 hN4, hρ.read _ _ hN1 le_rfl hN4]) (by
      -- The grades of the two cells, as cells of the layer scheme: the goal reads them through
      -- `Subtype.val` of anonymous constructors, which `rw [grade_oldCell]` does not match.
      change (layerScheme I ρ).toCellScheme.grade (oldCell I ρ (copyOrig I k b)) ≤
        (layerScheme I ρ).toCellScheme.grade (newCell I ρ ((k : ℕ) + 1))
      rw [grade_oldCell, grade_copyOrig, grade_newCell hN1 hN4])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)

/-- **Lawful labellings of the layer scheme are read through the layer bases**, for layer rows
oriented toward `b`: below `(univ, j)`, the new cell at `(univ, k)` carries the label of the
original of the copy `b` of grade `k`. -/
theorem eq_layerBase_of_isLawfulBelow {b : Fin 2} (hρ : IsOriented ρ b) {j : ℕ}
    {W : Fin (layerScheme I ρ).card → Label.{u}}
    (hW : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j) fun z ↦ W z)
    {z : Fin (layerScheme I ρ).card}
    (hz : z ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), j)) :
    W z = W (oldCell I ρ (layerBase I ρ b z)) := by
  have new (k : Fin 4) (hz : newCell I ρ ((k : ℕ) + 1) ∈ (layerScheme I ρ).toCellScheme.below
      ((univ : Finset (Fin 5)), j)) :
      W (newCell I ρ ((k : ℕ) + 1)) =
        W (oldCell I ρ (layerBase I ρ b (newCell I ρ ((k : ℕ) + 1)))) := by
    have hkj : (k : ℕ) + 1 ≤ j := (congrArg Prod.snd (gradedIndex_newCell (I := I) (ρ := ρ)
      (k := (k : ℕ) + 1) (by omega) (by omega))).symm.trans_le hz.2
    obtain ⟨-, hle, hNb⟩ := newCell_bounds_of_isLawfulBelow hρ hW k hkj
    rw [layerBase_newCell]
    exact le_antisymm hNb (hle _ (grade_copyOrig I k b))
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [layerBase_oldCell]
  · exact new 0 hz
  · exact new 1 hz
  · exact new 2 hz
  · exact new 3 hz

/-- **From the layer scheme to the canonical multi-layer scheme.**  For layer rows oriented toward
`b`, a labelling lawful below `(univ, j)` in the layer scheme, read through the bases, is lawful
below `(univ, j)` in the canonical multi-layer scheme of the oriented rows. -/
theorem isLawfulBelow_oriented_of_layer {b : Fin 2} (hρ : IsOriented ρ b) {j : ℕ}
    {W : Fin (layerScheme I ρ).card → Label.{u}}
    (hW : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j) fun z ↦ W z) :
    (canonicalMultiScheme I (orientedRows I ρ)).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
      fun z ↦ W (oldCell I ρ (copyBase I z)) := by
  obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hW
  -- Below each coatom the labelling is that of the amalgam.
  have hB {B : Finset (Fin 5)} (hBu : B ≠ univ) :
      (canonicalMultiScheme I (orientedRows I ρ)).rows.IsLawfulBelow (B, j)
        fun z ↦ W (oldCell I ρ (copyBase I z)) := by
    have h1 := (isLawfulBelow_oldCell_iff (X := (B, j)) hBu).mp
      (hW.mono (X := (B, j)) ⟨subset_univ _, le_rfl⟩)
    refine (isLawfulBelow_multiOldCell_iff (X := (B, j))
      (w := fun z ↦ W (oldCell I ρ (copyBase I z))) hBu).mpr ?_
    simpa only [copyBase_multiOldCell] using h1
  have hBC := Rows.isLawfulBelow_iff_forall (w := fun z ↦ W (oldCell I ρ (copyBase I z))) |>.mp
    (hB (B := coatomC) (by decide))
  have hBD := Rows.isLawfulBelow_iff_forall (w := fun z ↦ W (oldCell I ρ (copyBase I z))) |>.mp
    (hB (B := coatomD) (by decide))
  -- The base of a cell below `(univ, j)`, as an old cell of the layer scheme.
  have hmem {z : Fin (canonicalMultiScheme I (orientedRows I ρ)).card} {j' : ℕ}
      (hz : (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.grade z ≤ j') :
      oldCell I ρ (copyBase I z) ∈ (layerScheme I ρ).toCellScheme.below
        ((univ : Finset (Fin 5)), j') :=
    oldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_copyBase _ z).trans_le hz⟩
  have newCell_facts := newCell_bounds_of_isLawfulBelow hρ hW
  refine (Rows.isLawfulBelow_iff_forall
    (w := fun z ↦ W (oldCell I ρ (copyBase I z)))).mpr
    ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · have := ho _ (hmem hz.2)
    rwa [grade_oldCell, grade_copyBase] at this
  · rcases multiCell_cases (r := canonicalRows I (orientedRows I ρ)) s with ⟨a, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi hs (scope_multiOldCell_ne a) with h | h
      exacts [hBC.2.1 _ h, hBD.2.1 _ h]
    · have hkj : (k : ℕ) + 1 ≤ j := by
        have := hs.2
        rwa [gradedIndex_multiNewCell] at this
      have hN1 : 1 ≤ (k : ℕ) + 1 := by omega
      have hN4 : (k : ℕ) + 1 ≤ 4 := by omega
      obtain ⟨hN, hle, -⟩ := newCell_facts k hkj
      have hLN := hl _ hN
      have hK (t : (layerScheme I ρ).toCellScheme.below
          ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ ((k : ℕ) + 1)))) :
          (layerScheme I ρ).toCellScheme.grade t ≤ (k : ℕ) + 1 := by
        have := t.2.2.trans_eq (congrArg Prod.snd (gradedIndex_newCell hN1 hN4))
        exact this
      have hvis : IsSelfVisible ((k : ℕ) + 1) (W (oldCell I ρ (copyOrig I k i))) := by
        have := ho _
          (oldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_copyOrig I k i).trans_le hkj⟩)
        rwa [grade_oldCell, grade_copyOrig] at this
      have hoN := hle _ (grade_copyOrig I k i)
      refine (hLN.min_const hK hvis).of_comp (fun t ↦ ⟨oldCell I ρ (copyBase I t.1), ?_⟩)
        (fun t ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)
      · rw [gradedIndex_newCell hN1 hN4]
        refine hmem ?_
        have := t.2.2.trans_eq (congrArg Prod.snd
          (gradedIndex_multiNewCell (r := canonicalRows I (orientedRows I ρ)) k i))
        exact this
      · -- The grades of a cell and of its base: the right side is `Subtype.val` of an anonymous
        -- constructor, which `rw [grade_oldCell]` does not match.
        change _ = (layerScheme I ρ).toCellScheme.grade (oldCell I ρ (copyBase I t.1))
        rw [grade_oldCell, grade_copyBase]
      · rw [row_canonical, row_newCell hN1 hN4, gradedIndex_oldCell]
        rfl
      · simp only [copyBase_multiNewCell]
        rw [min_assoc, min_eq_right hoN]
  · rcases multiCell_cases (r := canonicalRows I (orientedRows I ρ)) t with ⟨e, rfl⟩ | ⟨k, i, rfl⟩
    · rcases mem_below_coatom_of_ne_multi ht (scope_multiOldCell_ne e) with h | h
      exacts [hBC.2.2 s _ h hst hg, hBD.2.2 s _ h hst hg]
    · have hkj : (k : ℕ) + 1 ≤ j := by
        have := ht.2
        rwa [gradedIndex_multiNewCell] at this
      obtain ⟨-, hle, hNb⟩ := newCell_facts k hkj
      refine ⟨multiNewCell I canonicalMult k b, by rw [gradedIndex_multiNewCell,
        gradedIndex_multiNewCell], ?_⟩
      simp only [copyBase_multiNewCell]
      refine (hle _ ?_).trans hNb
      rw [grade_copyBase, hg, grade_multiNewCell]

/-- **From the canonical multi-layer scheme to the layer scheme.**  For layer rows oriented toward
`b`, a labelling lawful below `(univ, j)` in the canonical multi-layer scheme of the oriented rows,
read through the layer bases, is lawful below `(univ, j)` in the layer scheme. -/
theorem isLawfulBelow_layer_of_oriented {b : Fin 2} (hρ : IsOriented ρ b) {j : ℕ}
    {w : Fin (canonicalMultiScheme I (orientedRows I ρ)).card → Label.{u}}
    (hw : (canonicalMultiScheme I (orientedRows I ρ)).rows.IsLawfulBelow
      ((univ : Finset (Fin 5)), j) fun z ↦ w z) :
    (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
      fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z)) := by
  obtain ⟨ho, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  -- Below each coatom the labelling is that of the amalgam.
  have hB {B : Finset (Fin 5)} (hBu : B ≠ univ) :
      (layerScheme I ρ).rows.IsLawfulBelow (B, j)
        fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z)) := by
    have h1 := (isLawfulBelow_multiOldCell_iff (X := (B, j)) hBu).mp
      (hw.mono (X := (B, j)) ⟨subset_univ _, le_rfl⟩)
    refine (isLawfulBelow_oldCell_iff (X := (B, j))
      (w := fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z))) hBu).mpr ?_
    simpa only [layerBase_oldCell] using h1
  have hBC := Rows.isLawfulBelow_iff_forall
    (w := fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z))) |>.mp
    (hB (B := coatomC) (by decide))
  have hBD := Rows.isLawfulBelow_iff_forall
    (w := fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z))) |>.mp
    (hB (B := coatomD) (by decide))
  -- The layer base of a cell below `(univ, j')`, as an old cell of the canonical scheme.
  have hmem {z : Fin (layerScheme I ρ).card} {j' : ℕ}
      (hz : (layerScheme I ρ).toCellScheme.grade z ≤ j') :
      multiOldCell I canonicalMult (layerBase I ρ b z) ∈
        (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.below
          ((univ : Finset (Fin 5)), j') :=
    multiOldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_layerBase b z).trans_le hz⟩
  -- Locality and availability at the new cell of grade `k + 1`.
  have newCell_facts (k : Fin 4) (hkj : (k : ℕ) + 1 ≤ j) :
      TransformsTo (fun d : (layerScheme I ρ).toCellScheme.below
          ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ ((k : ℕ) + 1))) ↦
          (layerScheme I ρ).toCellScheme.grade d)
        ((layerScheme I ρ).rows.row (newCell I ρ ((k : ℕ) + 1)))
        (fun d ↦ min (w (multiOldCell I canonicalMult (layerBase I ρ b d)))
          (w (multiOldCell I canonicalMult (layerBase I ρ b (newCell I ρ ((k : ℕ) + 1)))))) ∧
      ∀ s, (layerScheme I ρ).toCellScheme.grade s = (k : ℕ) + 1 →
        w (multiOldCell I canonicalMult (layerBase I ρ b s)) ≤
          w (multiOldCell I canonicalMult (layerBase I ρ b (newCell I ρ ((k : ℕ) + 1)))) := by
    have hN1 : 1 ≤ (k : ℕ) + 1 := by omega
    have hN4 : (k : ℕ) + 1 ≤ 4 := by omega
    have hκ (i : Fin 2) := multiNewCell_mem_below (r := canonicalRows I (orientedRows I ρ)) i hkj
    have hforce (i : Fin 2) := eq_copyOrig_of_isLawfulBelow (orientedRows I ρ) hw hkj i
    have hob (i i' : Fin 2) : multiOldCell I canonicalMult (copyOrig I k i') ∈
        (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.below
          ((canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.gradedIndex
            (multiNewCell I canonicalMult k i)) := by
      rw [gradedIndex_multiNewCell]
      exact multiOldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_copyOrig I k i').le⟩
    -- The orientation: the original of a copy is at most the original of the copy `b`.
    have horient (i : Fin 2) : w (multiOldCell I canonicalMult (copyOrig I k i)) ≤
        w (multiOldCell I canonicalMult (copyOrig I k b)) := by
      have := (hl _ (hκ i)).le_of_le (d := ⟨_, hob i i⟩) (d' := ⟨_, hob i b⟩) (by
        rw [row_canonical, row_canonical, copyBase_multiOldCell, copyBase_multiOldCell,
          orientedRows_apply, orientedRows_apply, gradedIndex_copyOrig, gradedIndex_copyOrig]
        exact hρ.le _ i hN1 hN4) (by
        -- The grades of the two originals, as cells of the canonical scheme: the goal reads them
        -- through `Subtype.val` of anonymous constructors, which `rw` does not match.
        change (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.grade
            (multiOldCell I canonicalMult (copyOrig I k b)) ≤
          (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.grade
            (multiOldCell I canonicalMult (copyOrig I k i))
        rw [grade_multiOldCell, grade_multiOldCell, grade_copyOrig, grade_copyOrig])
      simp only [hforce i, min_self] at this
      exact this.trans (min_le_left _ _)
    refine ⟨?_, fun s hs ↦ ?_⟩
    · refine (hl _ (hκ b)).of_comp
        (fun t ↦ ⟨multiOldCell I canonicalMult (layerBase I ρ b t.1), ?_⟩)
        (fun t ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)
      · rw [gradedIndex_multiNewCell]
        refine hmem ?_
        have := t.2.2.trans_eq (congrArg Prod.snd (gradedIndex_newCell hN1 hN4))
        exact this
      · -- The grades of a cell and of its layer base: the right side is `Subtype.val` of an
        -- anonymous constructor, which `rw [grade_multiOldCell]` does not match.
        change _ = (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.grade
          (multiOldCell I canonicalMult (layerBase I ρ b t.1))
        rw [grade_multiOldCell, grade_layerBase]
      · rw [row_newCell hN1 hN4, row_canonical, copyBase_multiOldCell, orientedRows_apply,
          row_layerBase hρ hN4]
        have := t.2.2.trans_eq (congrArg Prod.snd (gradedIndex_newCell hN1 hN4))
        exact this
      · simp only [layerBase_newCell, hforce b]
    · obtain ⟨u, hu, hle⟩ := ha (multiOldCell I canonicalMult (layerBase I ρ b s))
        (multiNewCell I canonicalMult k 0) (hκ 0)
        (by rw [scope_multiNewCell]; exact subset_univ _)
        (by rw [grade_multiOldCell, grade_layerBase, hs, grade_multiNewCell])
      rw [gradedIndex_multiNewCell] at hu
      obtain ⟨k', i', hk', rfl⟩ := exists_eq_multiNewCell hu
      obtain rfl : k' = k := Fin.ext (by omega)
      rw [layerBase_newCell]
      exact hle.trans ((hforce i').le.trans (horient i'))
  -- The new cells, case by case.
  have newMem {s : Fin (layerScheme I ρ).card} {k : Fin 4}
      (hs : s = newCell I ρ ((k : ℕ) + 1))
      (h : s ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), j)) :
      (k : ℕ) + 1 ≤ j := by
    have := h.2
    rwa [hs, gradedIndex_newCell (by omega) (by omega)] at this
  refine (Rows.isLawfulBelow_iff_forall
    (w := fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z)))).mpr
    ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · have := ho _ (hmem hz.2)
    rwa [grade_multiOldCell, grade_layerBase] at this
  · rcases cell_cases s with ⟨a, rfl⟩ | rfl | rfl | rfl | rfl
    · rcases mem_below_coatom_of_ne hs (scope_oldCell_ne a) with h | h
      exacts [hBC.2.1 _ h, hBD.2.1 _ h]
    · exact (newCell_facts 0 (newMem (k := 0) rfl hs)).1
    · exact (newCell_facts 1 (newMem (k := 1) rfl hs)).1
    · exact (newCell_facts 2 (newMem (k := 2) rfl hs)).1
    · exact (newCell_facts 3 (newMem (k := 3) rfl hs)).1
  · have avail (k : Fin 4) (ht : t = newCell I ρ ((k : ℕ) + 1)) :
        ∃ u, (layerScheme I ρ).toCellScheme.gradedIndex u =
          (layerScheme I ρ).toCellScheme.gradedIndex t ∧
          w (multiOldCell I canonicalMult (layerBase I ρ b s)) ≤
            w (multiOldCell I canonicalMult (layerBase I ρ b u)) := by
      subst ht
      refine ⟨_, rfl, (newCell_facts k (newMem rfl ht)).2 s ?_⟩
      rw [hg, grade_newCell (by omega) (by omega)]
    rcases cell_cases t with ⟨e, rfl⟩ | rfl | rfl | rfl | rfl
    · rcases mem_below_coatom_of_ne ht (scope_oldCell_ne e) with h | h
      exacts [hBC.2.2 s _ h hst hg, hBD.2.2 s _ h hst hg]
    · exact avail 0 rfl
    · exact avail 1 rfl
    · exact avail 2 rfl
    · exact avail 3 rfl

/-- **The classification of the lawful labellings under oriented rows.**  For layer rows oriented
toward `b`, a labelling is lawful below `(univ, j)` in the canonical multi-layer scheme of the
oriented rows exactly when it is read through the bases below `(univ, j)` and, read through the
layer bases, it is lawful below `(univ, j)` in the layer scheme.  So the lawful labellings are,
on the old cells, those of the layer scheme: a restriction of the pairs of coatom labellings
agreeing on the common face. -/
theorem isLawfulBelow_oriented_iff {b : Fin 2} (hρ : IsOriented ρ b) {j : ℕ}
    {w : Fin (canonicalMultiScheme I (orientedRows I ρ)).card → Label.{u}} :
    (canonicalMultiScheme I (orientedRows I ρ)).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
        (fun z ↦ w z) ↔
      (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), j)
        (fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z))) ∧
      ∀ z ∈ (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.below
        ((univ : Finset (Fin 5)), j), w z = w (multiOldCell I canonicalMult (copyBase I z)) := by
  refine ⟨fun hw ↦ ⟨isLawfulBelow_layer_of_oriented hρ hw,
    fun z hz ↦ eq_copyBase_of_isLawfulBelow _ hw hz⟩, fun ⟨hW, he⟩ ↦ ?_⟩
  refine (Rows.isLawfulBelow_congr he).mpr ?_
  simpa only [layerBase_oldCell] using isLawfulBelow_oriented_of_layer hρ
    (W := fun z ↦ w (multiOldCell I canonicalMult (layerBase I ρ b z))) hW

/-! ### The capped lifts -/

/-- **The capped lift from a coatom under oriented rows**: for layer rows oriented toward `b`,
the capped lift of the layer scheme from `(B, k)` into `(univ, k)` gives that of the canonical
multi-layer scheme of the oriented rows.  The ambient is read through the layer bases, lifted in the
layer scheme, and read back through the bases; the ambient is read through the bases
(forcedness), so the cap agreement holds at the copies. -/
theorem cappedLift_oriented {b : Fin 2} (hρ : IsOriented ρ b) {B : Finset (Fin 5)} (hBu : B ≠ univ)
    {k : ℕ} (hL : (layerScheme I ρ).rows.CappedLift (X := (B, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩) :
    (canonicalMultiScheme I (orientedRows I ρ)).rows.CappedLift (X := (B, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩ := by
  classical
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  set P := Rows.extendBot (D := (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme)
    (B, k) p with hPdef
  set Q := Rows.extendBot (D := (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme)
    ((univ : Finset (Fin 5)), k) q with hQdef
  have hQ : (canonicalMultiScheme I (orientedRows I ρ)).rows.IsLawfulBelow
      ((univ : Finset (Fin 5)), k) fun z ↦ Q z := Rows.isLawfulBelow_extendBot.mpr hq
  -- The prescription and the ambient, read through the layer bases.
  have hPl : (layerScheme I ρ).rows.IsLawfulBelow (B, k)
      fun z ↦ P (multiOldCell I canonicalMult (layerBase I ρ b z)) := by
    have h1 := (isLawfulBelow_multiOldCell_iff hBu).mp (Rows.isLawfulBelow_extendBot.mpr hp)
    refine (isLawfulBelow_oldCell_iff (X := (B, k))
      (w := fun z ↦ P (multiOldCell I canonicalMult (layerBase I ρ b z))) hBu).mpr ?_
    simpa only [layerBase_oldCell] using h1
  have hQl := isLawfulBelow_layer_of_oriented hρ hQ
  obtain ⟨r, hr, hrc, hrp⟩ := (Rows.cappedLift_iff_forall_exists _).mp hL c hc _ _ hPl hQl
    fun d ↦ by
      obtain ⟨e, he⟩ := exists_eq_oldCell (I := I) (ρ := ρ) (z := d.1)
        fun hU ↦ hBu (univ_subset_iff.mp (hU ▸ d.2.1))
      have hd := d.2
      rw [he] at hd
      have heB := multiOldCell_mem_below_iff (R := orientedRows I ρ) |>.mpr
        (oldCell_mem_below_iff.mp hd)
      have heU := multiOldCell_mem_below_iff (R := orientedRows I ρ) (X := (univ, k)) |>.mpr
        ⟨subset_univ _, (oldCell_mem_below_iff.mp hd).2⟩
      -- The two labellings at the old cell `e`, through the inclusion of the cells below `B`:
      -- the value of `Set.inclusion _ d` is `d.1` only by unfolding, so `rw [he]` needs `d.1`.
      change min (Q (multiOldCell I canonicalMult (layerBase I ρ b d.1))) c =
        min (P (multiOldCell I canonicalMult (layerBase I ρ b d.1))) c
      rw [he, layerBase_oldCell, hQdef, hPdef, Rows.extendBot_of_mem q heU,
        Rows.extendBot_of_mem p heB]
      exact hpq ⟨_, heB⟩
  -- The lift, read back through the bases.
  have hR := isLawfulBelow_oriented_of_layer hρ (W := Rows.extendBot ((univ : Finset (Fin 5)), k) r)
    (Rows.isLawfulBelow_extendBot.mpr hr)
  refine ⟨fun z ↦ Rows.extendBot ((univ : Finset (Fin 5)), k) r (oldCell I ρ (copyBase I z.1)),
    hR, fun z ↦ ?_, fun d ↦ ?_⟩
  · have hz : oldCell I ρ (copyBase I z.1) ∈ (layerScheme I ρ).toCellScheme.below
        ((univ : Finset (Fin 5)), k) :=
      oldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_copyBase _ z.1).trans_le z.2.2⟩
    -- The ambient is read through the bases.
    have hqz : q z = Q (multiOldCell I canonicalMult (copyBase I z.1)) := by
      rw [← eq_copyBase_of_isLawfulBelow _ hQ z.2, hQdef, Rows.extendBot_of_mem q z.2]
    dsimp only
    rw [Rows.extendBot_of_mem r hz, hrc ⟨_, hz⟩, hqz, layerBase_oldCell]
  · obtain ⟨e, he⟩ := exists_eq_multiOldCell (r := canonicalRows I (orientedRows I ρ)) (z := d.1)
      fun hU ↦ hBu (univ_subset_iff.mp (hU ▸ d.2.1))
    have hd := d.2
    rw [he] at hd
    have heB : oldCell I ρ e ∈ (layerScheme I ρ).toCellScheme.below (B, k) :=
      oldCell_mem_below_iff.mpr (multiOldCell_mem_below_iff.mp hd)
    have heU : oldCell I ρ e ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), k) :=
      oldCell_mem_below_iff.mpr ⟨subset_univ _, (multiOldCell_mem_below_iff.mp hd).2⟩
    -- The lift at the old cell `e`, through the inclusion of the cells below `B`: the goal is an
    -- unreduced application to `Set.inclusion _ d`, whose value is `d.1` only by unfolding.
    change Rows.extendBot ((univ : Finset (Fin 5)), k) r (oldCell I ρ (copyBase I d.1)) = p d
    rw [he, copyBase_multiOldCell, Rows.extendBot_of_mem r heU, hrp ⟨_, heB⟩]
    dsimp only
    rw [layerBase_oldCell, hPdef, ← he, Rows.extendBot_of_mem p d.2]

/-- **The capped lift of the layer scheme from that of the canonical multi-layer scheme**, for
layer rows oriented toward `b`: the converse of `OrderedLayer.cappedLift_oriented`.  The ambient is
read through the bases, lifted in the canonical multi-layer scheme, and read back through the
layer bases; the ambient is read through the layer bases (`eq_layerBase_of_isLawfulBelow`), so the
cap agreement holds at the new cells. -/
theorem cappedLift_layer_of_oriented {b : Fin 2} (hρ : IsOriented ρ b) {B : Finset (Fin 5)}
    (hBu : B ≠ univ) {k : ℕ}
    (hL : (canonicalMultiScheme I (orientedRows I ρ)).rows.CappedLift (X := (B, k))
      (Y := ((univ : Finset (Fin 5)), k)) ⟨subset_univ _, le_rfl⟩) :
    (layerScheme I ρ).rows.CappedLift (X := (B, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ := by
  classical
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  set P := Rows.extendBot (D := (layerScheme I ρ).toCellScheme) (B, k) p with hPdef
  set Q := Rows.extendBot (D := (layerScheme I ρ).toCellScheme) ((univ : Finset (Fin 5)), k) q
    with hQdef
  have hQ : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k) fun z ↦ Q z :=
    Rows.isLawfulBelow_extendBot.mpr hq
  -- The prescription and the ambient, read through the bases.
  have hPc : (canonicalMultiScheme I (orientedRows I ρ)).rows.IsLawfulBelow (B, k)
      fun z ↦ P (oldCell I ρ (copyBase I z)) := by
    have h1 := (isLawfulBelow_oldCell_iff (X := (B, k)) hBu).mp
      (Rows.isLawfulBelow_extendBot.mpr hp)
    refine (isLawfulBelow_multiOldCell_iff (X := (B, k))
      (w := fun z ↦ P (oldCell I ρ (copyBase I z))) hBu).mpr ?_
    simpa only [copyBase_multiOldCell] using h1
  have hQc := isLawfulBelow_oriented_of_layer hρ (W := fun z ↦ Q z) hQ
  obtain ⟨r, hr, hrc, hrp⟩ := (Rows.cappedLift_iff_forall_exists _).mp hL c hc _ _ hPc hQc
    fun d ↦ by
      obtain ⟨e, he⟩ := exists_eq_multiOldCell (r := canonicalRows I (orientedRows I ρ))
        (z := d.1) fun hU ↦ hBu (univ_subset_iff.mp (hU ▸ d.2.1))
      have hd := d.2
      rw [he] at hd
      have heB : oldCell I ρ e ∈ (layerScheme I ρ).toCellScheme.below (B, k) :=
        oldCell_mem_below_iff.mpr (multiOldCell_mem_below_iff.mp hd)
      have heU : oldCell I ρ e ∈ (layerScheme I ρ).toCellScheme.below
          ((univ : Finset (Fin 5)), k) :=
        oldCell_mem_below_iff.mpr ⟨subset_univ _, (multiOldCell_mem_below_iff.mp hd).2⟩
      -- The two labellings at the old cell `e`, through the inclusion of the cells below `B`:
      -- the value of `Set.inclusion _ d` is `d.1` only by unfolding, so `rw [he]` needs `d.1`.
      change min (Q (oldCell I ρ (copyBase I d.1))) c = min (P (oldCell I ρ (copyBase I d.1))) c
      rw [he, copyBase_multiOldCell, hQdef, hPdef, Rows.extendBot_of_mem q heU,
        Rows.extendBot_of_mem p heB]
      exact hpq ⟨_, heB⟩
  -- The lift, read back through the layer bases.
  have hR := isLawfulBelow_layer_of_oriented hρ
    (w := Rows.extendBot ((univ : Finset (Fin 5)), k) r) (Rows.isLawfulBelow_extendBot.mpr hr)
  refine ⟨fun z ↦ Rows.extendBot ((univ : Finset (Fin 5)), k) r
    (multiOldCell I canonicalMult (layerBase I ρ b z.1)), hR, fun z ↦ ?_, fun d ↦ ?_⟩
  · have hz : multiOldCell I canonicalMult (layerBase I ρ b z.1) ∈
        (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.below
          ((univ : Finset (Fin 5)), k) :=
      multiOldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_layerBase b z.1).trans_le z.2.2⟩
    -- The ambient is read through the layer bases.
    have hqz : q z = Q (oldCell I ρ (layerBase I ρ b z.1)) := by
      rw [← eq_layerBase_of_isLawfulBelow hρ hQ z.2, hQdef, Rows.extendBot_of_mem q z.2]
    dsimp only
    rw [Rows.extendBot_of_mem r hz, hrc ⟨_, hz⟩, hqz, copyBase_multiOldCell]
  · obtain ⟨e, he⟩ := exists_eq_oldCell (I := I) (ρ := ρ) (z := d.1)
      fun hU ↦ hBu (univ_subset_iff.mp (hU ▸ d.2.1))
    have hd := d.2
    rw [he] at hd
    have heB : multiOldCell I canonicalMult e ∈
        (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.below (B, k) :=
      multiOldCell_mem_below_iff.mpr (oldCell_mem_below_iff.mp hd)
    have heU : multiOldCell I canonicalMult e ∈
        (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.below
          ((univ : Finset (Fin 5)), k) :=
      multiOldCell_mem_below_iff.mpr ⟨subset_univ _, (oldCell_mem_below_iff.mp hd).2⟩
    -- The lift at the old cell `e`, through the inclusion of the cells below `B`: the goal is an
    -- unreduced application to `Set.inclusion _ d`, whose value is `d.1` only by unfolding.
    change Rows.extendBot ((univ : Finset (Fin 5)), k) r
      (multiOldCell I canonicalMult (layerBase I ρ b d.1)) = p d
    rw [he, layerBase_oldCell, Rows.extendBot_of_mem r heU, hrp ⟨_, heB⟩]
    dsimp only
    rw [copyBase_multiOldCell, hPdef, ← he, Rows.extendBot_of_mem p d.2]

end OrderedLayer

namespace Seed

open Finset Label CellScheme OrderedLayer

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {ρ : LayerRows.{u}} {b : Fin 2}

/-- **The multi-layer step from the ordered-layer step with oriented rows.**  For a seed with an
ordered-layer step whose layer rows `ρ` are oriented toward `b`, the canonical multi-layer scheme
of the oriented rows has the multi-layer step: the copy rows are coded and consistent as the layer
rows are (`OrderedLayer.isLawfulBelow_oriented_of_layer`), the capped lifts are those of the layer
scheme (`OrderedLayer.cappedLift_oriented`), and the lawful extension of the glued labelling is
that of the layer scheme read through the bases. -/
theorem canonicalMultiStep_of_orderedLayerStep (h : I.OrderedLayerStep ρ) (hρ : IsOriented ρ b) :
    I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I ρ)) where
  pos _ := two_pos
  row_lt k i z hz := by
    rw [canonicalRows_apply, orientedRows_apply]
    have hm : oldCell I ρ (copyBase I z) ∈ (layerScheme I ρ).toCellScheme.below
        ((univ : Finset (Fin 5)), (k : ℕ) + 1) :=
      oldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_copyBase _ z).trans_le hz.2⟩
    have := h.row_lt ((k : ℕ) + 1) (by omega) (by omega) _ hm
    rwa [gradedIndex_oldCell] at this
  isLawfulBelow_row k i := by
    have := isLawfulBelow_oriented_of_layer hρ
      (W := fun z ↦ ρ ((k : ℕ) + 1) ((layerScheme I ρ).toCellScheme.gradedIndex z))
      (h.isLawfulBelow_row ((k : ℕ) + 1) (by omega)
      (by omega))
    refine (Rows.isLawfulBelow_congr (w := fun z ↦ ρ ((k : ℕ) + 1)
      ((layerScheme I ρ).toCellScheme.gradedIndex (oldCell I ρ (copyBase I z))))
      (w' := fun z ↦ canonicalRows I (orientedRows I ρ) k i z) fun z _ ↦ ?_).mp this
    rw [canonicalRows_apply, orientedRows_apply, gradedIndex_oldCell]
  cappedLift_left k hk1 hk4 := cappedLift_oriented hρ (by decide) (h.cappedLift_left k hk1 hk4)
  cappedLift_right k hk1 hk4 := cappedLift_oriented hρ (by decide) (h.cappedLift_right k hk1 hk4)
  exists_isLawful := by
    obtain ⟨W, hW, hWl⟩ := h.exists_isLawful
    have := isLawfulBelow_oriented_of_layer hρ (j := 4) (hW.isLawfulBelow _)
    exact ⟨_, this.isLawful mem_below_univ_four_multi, fun d ↦ by
      simp only [copyBase_multiOldCell, hWl]⟩

/-- **The completion from the ordered-layer step with oriented rows**: a seed on five points with
an ordered-layer step whose layer rows are oriented has a completion below the full grade, the
canonical multi-layer scheme of the oriented rows. -/
theorem nonempty_completionBelowFullGrade_of_orderedLayerStep (h : I.OrderedLayerStep ρ)
    (hρ : IsOriented ρ b) : Nonempty (CompletionBelowFullGrade I) :=
  (canonicalMultiStep_of_orderedLayerStep h hρ).nonempty_completionBelowFullGrade

/-- **The ordered-layer step from the multi-layer step with oriented rows**: the converse of
`Seed.canonicalMultiStep_of_orderedLayerStep`.  The layer rows are coded and consistent as the
copy rows of the copy `b` are (`OrderedLayer.isLawfulBelow_layer_of_oriented`), the capped lifts
are those of the canonical multi-layer scheme (`OrderedLayer.cappedLift_layer_of_oriented`), and the
lawful extension of the glued labelling is that of the canonical multi-layer scheme read through
the layer bases. -/
theorem orderedLayerStep_of_canonicalMultiStep_oriented (hρ : IsOriented ρ b)
    (h : I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I ρ))) :
    I.OrderedLayerStep ρ where
  row_lt k hk1 hk4 z hz := by
    obtain ⟨k', rfl⟩ : ∃ k' : Fin 4, k = (k' : ℕ) + 1 :=
      ⟨⟨k - 1, by omega⟩, by simp only; omega⟩
    have hm : multiOldCell I canonicalMult (layerBase I ρ b z) ∈
        (canonicalMultiScheme I (orientedRows I ρ)).toCellScheme.below
          ((univ : Finset (Fin 5)), (k' : ℕ) + 1) :=
      multiOldCell_mem_below_iff.mpr ⟨subset_univ _, (grade_layerBase b z).trans_le hz.2⟩
    have := h.row_lt k' b _ hm
    rwa [canonicalRows_apply, copyBase_multiOldCell, orientedRows_apply,
      row_layerBase hρ hk4 hz.2] at this
  isLawfulBelow_row k hk1 hk4 := by
    obtain ⟨k', rfl⟩ : ∃ k' : Fin 4, k = (k' : ℕ) + 1 :=
      ⟨⟨k - 1, by omega⟩, by simp only; omega⟩
    have := isLawfulBelow_layer_of_oriented hρ
      (w := fun z ↦ canonicalRows I (orientedRows I ρ) k' b z) (h.isLawfulBelow_row k' b)
    refine (Rows.isLawfulBelow_congr (w := fun z ↦ canonicalRows I (orientedRows I ρ) k' b
      (multiOldCell I canonicalMult (layerBase I ρ b z)))
      (w' := fun z ↦ ρ ((k' : ℕ) + 1) ((layerScheme I ρ).toCellScheme.gradedIndex z))
      fun z hz ↦ ?_).mp this
    rw [canonicalRows_apply, copyBase_multiOldCell, orientedRows_apply,
      row_layerBase hρ hk4 hz.2]
  cappedLift_left k hk1 hk4 :=
    cappedLift_layer_of_oriented hρ (by decide) (h.cappedLift_left k hk1 hk4)
  cappedLift_right k hk1 hk4 :=
    cappedLift_layer_of_oriented hρ (by decide) (h.cappedLift_right k hk1 hk4)
  exists_isLawful := by
    obtain ⟨w, hw, hwl⟩ := h.exists_isLawful
    have := isLawfulBelow_layer_of_oriented hρ (j := 4) (w := w) (hw.isLawfulBelow _)
    exact ⟨_, this.isLawful mem_below_univ_four, fun d ↦ by
      simp only [layerBase_oldCell, hwl]⟩

/-- **Under oriented rows, the step of the canonical multi-layer scheme is the ordered-layer
step**: for layer rows oriented toward `b`, the canonical multi-layer scheme of the oriented rows
has the multi-layer step exactly when the layer scheme has the ordered-layer step.  This is an
exact reformulation: both copies of a grade read alike, so the family adds nothing to the layer
scheme under these rows. -/
theorem canonicalMultiStep_oriented_iff (hρ : IsOriented ρ b) :
    I.MultiLayerStep canonicalMult (canonicalRows I (orientedRows I ρ)) ↔ I.OrderedLayerStep ρ :=
  ⟨orderedLayerStep_of_canonicalMultiStep_oriented hρ,
    fun h ↦ canonicalMultiStep_of_orderedLayerStep h hρ⟩

variable (I) in
/-- A seed on five points **has an oriented ordered-layer step** when it has an ordered-layer step
whose layer rows are oriented toward one of the two coatoms.  Under the oriented rows the step of
the canonical multi-layer scheme is exactly this ordered-layer step
(`Seed.canonicalMultiStep_oriented_iff`, an exact reformulation), so this is the ordered-layer step
itself, with oriented rows, and not a new clause. -/
def HasOrientedLayerStep : Prop :=
  ∃ (ρ : LayerRows.{u}) (b : Fin 2), I.OrderedLayerStep ρ ∧ IsOriented ρ b

/-- **An oriented ordered-layer step gives a step of the canonical multi-layer scheme**, with the
oriented rows. -/
theorem HasOrientedLayerStep.hasCanonicalMultiStep (h : I.HasOrientedLayerStep) :
    I.HasCanonicalMultiStep :=
  let ⟨_, _, hs, hρ⟩ := h
  ⟨_, canonicalMultiStep_of_orderedLayerStep hs hρ⟩

end Seed

end VaughtConjecture
