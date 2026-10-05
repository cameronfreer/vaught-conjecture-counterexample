/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Bountiful
import VaughtConjecture.Correspondence.Current.Transform

/-!
# Correspondence with the legal templates of [AFK26]: lawful local labellings

Roadmap, "Manuscript concordance", row 43.  [AFK26, Definition 4.26] (first part) calls a local
labelling `r : D↓U → L` at a graded face `U` of a template `t = (c, Σ)`, `Σ = (ℓ_d)_{d ∈ D}`,
*lawful* with respect to `Σ` when it satisfies Orderliness, Locality, and Availability.  The
clauses are compared with `CellScheme.Rows.IsLawfulBelow`, lawfulness below a pair.

## The setting

A template is a frame `c : D → GradedFace[P]` with a row system [AFK26, Definitions 4.4–4.6]: here
a cell scheme `D` (the frame, with the faces of the scheme as the plan), its scope and grade
functions `s = CellScheme.scope`, `g = CellScheme.grade`, `c = CellScheme.gradedIndex`, and rows
`R : D.Rows`, the row `R.row d` being the local label `ℓ_d : D↓d → L`.  The cells `D↓U` below `U`
[AFK26, Definition 4.4] are `D.below U`, the order of graded faces [AFK26, Definition 4.2] being
the product order on pairs.  The printed graded faces `(B, j)` have `B ∈ P` and `j ≤ |B|`
(`CellScheme.printedGradedFaces`); the graded faces of this development have `0 < j`
(`CellScheme.gradedFaces`), and the two differ by the faces of grade `0`
(`CellScheme.mem_printedGradedFaces_iff`).  Lawfulness at `U` is stated here for every pair `U`.

As in rows 3 and 4, the printed labels are those at stage `ω₁`; the definition is stated at a
stage `θ`, and the identification holds at every stage that is zero or a limit for rows and
labellings with values at that stage; at `ω₁` it is
`CellScheme.Rows.printedLawfulLocal_omega_one_iff`.

| Printed clause | `PrintedLawfulLocal` | `IsLawful` below `U` |
| --- | --- | --- |
| (Orderliness) `r(d)` self-visible at `g(d)` | `orderliness` | `orderly` |
| (Locality) `ℓ_d ⇒ min (r↾D↓d, r(d))` | `locality` | `locality` |
| (Availability) `s(d) ⊆ s(e)`, `g(d) = g(e)` give `e'` (below) | `availability` | `availability` |

In (Availability) the cell `e' ∈ D` has `c(e) = c(e')` and `r(d) ≤ r(e')`.

The identification is `CellScheme.Rows.printedLawfulLocal_iff`: at a stage `θ` that is zero or a
limit, for rows and a labelling with values at stage `θ`, `r` is lawful at `U` as printed exactly
when it is lawful below `U`.

**Departures**, each proved harmless:
1. *Self-visibility* in Orderliness is that of [AFK26, Definition 4.24], with the corrected
   visibility map of row 41 (`Label.CorrectedVisibilityMap.apply_eq_self_iff`).
2. *The relation* `⇒` in Locality is the corrected relation of row 42, the relation of
   [Kni26, Definition 2.3.9] at stage `θ`; it is `Label.TransformsTo` for the labellings in
   question by `Label.printedTransformsTo_iff` (row 3).
3. *The cell `e'` of Availability* ranges over `D`, while `r(e')` is defined only on `D↓U`: here
   `e'` is a cell of `D` lying in `D↓U`, and every cell with the graded index of a cell below `U`
   lies below `U` (`CellScheme.mem_below_of_gradedIndex_eq`).
4. *The cells below `d`*: `D↓d` is computed in `D`; it lies in `D↓U` for `d ∈ D↓U`, and `r↾D↓d`
   is `r` along that inclusion.  The law of `IsLawful` computes the cells below `d` inside the
   scheme of cells below `U`; the two index types are in bijection, and the transformation
   relation is transported along it (in the proof of `CellScheme.Rows.printedLawfulLocal_iff`).
5. *The range of the labels*: as in rows 3 and 4.

**The two printed definitions.**  [Kni26, Definition 2.5.4] (`CellScheme.Rows.PrintedRespects`,
row 4) presupposes orderliness, caps with the partial operation of [Kni26, Definition 2.3.7], and
quantifies availability over graded faces `⟨C, i⟩ ∈ P̂`, `B ⊇ C`, with `D_{B,i} ≠ ∅`; the printed
definition of [AFK26] caps with the minimum and quantifies availability over pairs of cells.  For
cells with graded index in the graded plan, at a stage that is zero or a limit, both are
lawfulness below `U` (`CellScheme.Rows.printedLawfulLocal_iff_printedRespects`).

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace CellScheme

variable {ι α : Type*} {D : CellScheme ι α}

/-- **The graded faces of [AFK26, Definition 4.2]**: the pairs `(B, j)` with `B` a face and
`j ≤ |B|`, the grade `0` included. -/
def printedGradedFaces (D : CellScheme ι α) : Set (Finset α × ℕ) :=
  {X | X.1 ∈ D.faces ∧ X.2 ≤ #X.1}

/-- A printed graded face is a graded face of this development or a face with grade `0`. -/
theorem mem_printedGradedFaces_iff {X : Finset α × ℕ} :
    X ∈ D.printedGradedFaces ↔ X ∈ D.gradedFaces ∨ (X.1 ∈ D.faces ∧ X.2 = 0) := by
  rcases Nat.eq_zero_or_pos X.2 with h | h
  · simp [printedGradedFaces, h]
  · simp [printedGradedFaces, h, h.ne']

/-- Every graded face of this development is a printed graded face. -/
theorem gradedFaces_subset_printedGradedFaces : D.gradedFaces ⊆ D.printedGradedFaces :=
  fun _ hX ↦ mem_printedGradedFaces_iff.mpr (.inl hX)

/-- A cell with the graded index of a cell below `U` lies below `U`. -/
theorem mem_below_of_gradedIndex_eq {U : Finset α × ℕ} {e e' : ι} (he : e ∈ D.below U)
    (h : D.gradedIndex e' = D.gradedIndex e) : e' ∈ D.below U :=
  (mem_below D).mpr (h ▸ he)

namespace Rows

variable (R : D.Rows.{u}) {θ : Ordinal.{u}} {U : Finset α × ℕ}

/-- **Lawful local labellings** [AFK26, Definition 4.26], at stage `θ`: a labelling `r` of the
cells below `U` satisfying Orderliness, Locality, and Availability with respect to the rows `R`,
the relation of Locality being the corrected relation of [AFK26, Definition 4.25], that of
[Kni26, Definition 2.3.9] at stage `θ`. -/
structure PrintedLawfulLocal (θ : Ordinal.{u}) (U : Finset α × ℕ) (r : D.below U → Label.{u}) :
    Prop where
  /-- (Orderliness) of [AFK26, Definition 4.26]: `r(d)` is self-visible at `g(d)`. -/
  orderliness : ∀ d : D.below U, IsSelfVisible (D.grade d) (r d)
  /-- (Locality) of [AFK26, Definition 4.26]: `ℓ_d ⇒ min (r↾D↓d, r(d))` over the grades of the
  cells below `d`. -/
  locality : ∀ d : D.below U,
    PrintedTransformsTo θ (fun e : D.below (D.gradedIndex d) ↦ D.grade e) (R.row d)
      (fun e ↦ min (r (Set.inclusion (D.below_mono d.2) e)) (r d))
  /-- (Availability) of [AFK26, Definition 4.26]: if `s(d) ⊆ s(e)` and `g(d) = g(e)`, then some
  cell `e'` of `D` (lying in `D↓U`) has `c(e) = c(e')` and `r(d) ≤ r(e')`. -/
  availability : ∀ d e : D.below U, D.scope d ⊆ D.scope e → D.grade d = D.grade e →
    ∃ e' : ι, D.gradedIndex e' = D.gradedIndex e ∧ ∃ he' : e' ∈ D.below U, r d ≤ r ⟨e', he'⟩

variable {R} {r : D.below U → Label.{u}}

/-- **Lawful local labellings are the labellings lawful below `U`** [AFK26, Definition 4.26]: at
a stage `θ` that is zero or a limit, for rows and a labelling with values at stage `θ`, `r` is
lawful at `U` as printed exactly when it is lawful below `U`. -/
theorem printedLawfulLocal_iff (hθ : Order.IsSuccPrelimit θ) (hR : ∀ s t, AtStage θ (R.row s t))
    (hr : ∀ d, AtStage θ (r d)) : R.PrintedLawfulLocal θ U r ↔ R.IsLawfulBelow U r := by
  -- The cells below `d` in `D` and in the scheme of cells below `U`.
  let φ (d : D.below U) (e : D.below (D.gradedIndex d.1)) :
      (D.reindex ((↑) : D.below U → ι)).below
        ((D.reindex ((↑) : D.below U → ι)).gradedIndex d) :=
    ⟨⟨e.1, D.below_mono d.2 e.2⟩, e.2⟩
  let ψ (d : D.below U) (t : (D.reindex ((↑) : D.below U → ι)).below
      ((D.reindex ((↑) : D.below U → ι)).gradedIndex d)) : D.below (D.gradedIndex d.1) :=
    ⟨t.1.1, t.2⟩
  have htr (d : D.below U) := printedTransformsTo_iff
    (a := fun e : D.below (D.gradedIndex d.1) ↦ D.grade e) hθ (hR d)
    (q := fun e ↦ min (r (Set.inclusion (D.below_mono d.2) e)) (r d)) fun e ↦ (hr _).min (hr d)
  refine ⟨fun h ↦ isLawfulBelow_iff.mpr ⟨h.orderliness, fun d ↦ ?_, fun d e hde hg ↦ ?_⟩,
    fun h ↦ ⟨(isLawfulBelow_iff.mp h).orderly, fun d ↦ ?_, fun d e hde hg ↦ ?_⟩⟩
  · exact ((htr d).mp (h.locality d)).reindex (ψ d)
  · obtain ⟨e', he, he', hle⟩ := h.availability d e hde hg
    exact ⟨⟨e', he'⟩, he, hle⟩
  · exact (htr d).mpr (((isLawfulBelow_iff.mp h).locality d).reindex (φ d))
  · obtain ⟨e', he, hle⟩ := (isLawfulBelow_iff.mp h).availability d e hde hg
    exact ⟨e'.1, he, e'.2, hle⟩

/-- **Lawful local labellings** [AFK26, Definition 4.26] on the printed labels
`{-∞} ∪ ω₁ ∪ {∞}`: for rows and a labelling with values at stage `ω₁`, `r` is lawful at `U` as
printed exactly when it is lawful below `U`. -/
theorem printedLawfulLocal_omega_one_iff (hR : ∀ s t, AtStage (Ordinal.omega 1) (R.row s t))
    (hr : ∀ d, AtStage (Ordinal.omega 1) (r d)) :
    R.PrintedLawfulLocal (Ordinal.omega 1) U r ↔ R.IsLawfulBelow U r :=
  printedLawfulLocal_iff (Cardinal.isSuccLimit_omega 1).isSuccPrelimit hR hr

/-- **The two printed definitions of lawfulness**: for cells with graded index in the graded plan,
at a stage `θ` that is zero or a limit, for rows and a labelling with values at stage `θ`, `r` is
lawful at `U` in the sense of [AFK26, Definition 4.26] exactly when it respects the rows below `U`
in the sense of [Kni26, Definition 2.5.4]. -/
theorem printedLawfulLocal_iff_printedRespects (hθ : Order.IsSuccPrelimit θ)
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hR : ∀ s t, AtStage θ (R.row s t))
    (hr : ∀ d, AtStage θ (r d)) :
    R.PrintedLawfulLocal θ U r ↔
      (R.comap (IsLowerEmbedding.subtypeVal_below D U)).PrintedRespects θ r :=
  (printedLawfulLocal_iff hθ hR hr).trans (printedRespects_below_iff hθ hD hR hr).symm

/-- A labelling lawful at `U` restricts to a labelling lawful at every `V ≤ U`, at a stage that is
zero or a limit, for rows and a labelling with values at that stage. -/
theorem PrintedLawfulLocal.restrict (hθ : Order.IsSuccPrelimit θ)
    (hR : ∀ s t, AtStage θ (R.row s t)) (hr : ∀ d, AtStage θ (r d))
    (h : R.PrintedLawfulLocal θ U r) {V : Finset α × ℕ} (hVU : V ≤ U) :
    R.PrintedLawfulLocal θ V (r ∘ Set.inclusion (D.below_mono hVU)) :=
  (printedLawfulLocal_iff hθ hR fun _ ↦ hr _).mpr
    (((printedLawfulLocal_iff hθ hR hr).mp h).mono hVU)

end Rows

end CellScheme

end VaughtConjecture
