/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Witness
import VaughtConjecture.Scheme.Row

/-!
# Correspondence: orderly and lawful labellings, and capping

Roadmap, "Manuscript concordance", rows 4 and 5.  The printed definitions of orderly labellings
[Kni26, Definition 2.3.4], of the cap `p ∧ γ` [Kni26, Definition 2.3.7], and of the labellings
respecting a semantics [Kni26, Definition 2.5.4] are compared clause by clause with the laws of
`CellScheme.Rows.IsLawful`; the printed form of [Kni26, Lemma 2.5.8] is then a corollary of
`CellScheme.Rows.IsLawful.min_const`.

## The setting

The printed domain is a union `D = ⋃ {D_{B,j} : ⟨B, j⟩ ∈ P̂}` of disjoint finite sets over the
graded plan `P̂` of a plan `P` [Kni26, Definition 2.1.8], with arity `a(Σ) = j` on `D_{B,j}`
[Kni26, Definition 2.5.3].  Here it is a cell scheme `D : CellScheme ι α`: the cells with graded
index `⟨B, j⟩` form `D_{B,j}`, the arity is the grade, and `P̂` is `D.gradedFaces`, whose
membership `CellScheme.mem_gradedFaces` is the printed condition `B ∈ P`, `0 < j ≤ |B|`.  That
every cell lies in some `D_{B,j}` with `⟨B, j⟩ ∈ P̂` is the hypothesis
`∀ d, D.gradedIndex d ∈ D.gradedFaces` (a law of `CellScheme.IsWellFormed`).  The restriction
`D↾⟨B, j⟩` of [Kni26, Definition 2.5.2] is `D.below (B, j)`
(`CellScheme.mem_below_iff_exists_mem_gradedFaces`), and a semantics `E` [Kni26, Definition 2.5.3]
is a family of rows `R : D.Rows`, the row `R.row s` being `E(Σ)` for the cell `s = Σ`.  The
printed semantics also requires each `E(Σ)` to be orderly (`CellScheme.Rows.IsOrderly`), and the
printed `D` is finite; neither is assumed (departures 6 and 7 below).

No clause of Definition 2.5.4 uses the plan property of `P`: the identifications below take no
`Geometry.IsPlan` hypothesis and hold for every family of faces, in particular for plans.  The
domains of [Kni26, Definition 2.6.1] (row 7) are not used by Definition 2.5.4 at all.  So neither
the correspondence of `Geometry.IsPlan` with [Kni26, Definition 2.1.1] (no concordance row) nor
row 7 is a prerequisite.  The notions the clauses do use are identified here: `P̂` by
`CellScheme.mem_gradedFaces`, `D↾⟨B, j⟩` by `CellScheme.mem_below_iff_exists_mem_gradedFaces`,
the arity by `CellScheme.grade`, and `⇒` by row 3.

As in row 3, the printed labels are those at stage `ω₁`; the definitions are stated at a stage
`θ`, and the identifications hold at every stage that is zero or a limit for labellings and rows
with values at that stage; at `ω₁` the identification of Definition 2.5.4 is
`CellScheme.Rows.printedRespects_omega_one_iff`.

## Orderly labellings, [Kni26, Definition 2.3.4]

`Label.PrintedOrderly a p`: `p d = p d ⌊+⌋_{a(d)} a(d)` for every `d`.  It is the order law of
`IsLawful` up to the orientation of the equation (`Label.printedOrderly_iff`).

## The cap `p ∧ γ`, [Kni26, Definition 2.3.7]

The printed cap is a partial operation: `p ∧ γ` is defined, as `d ↦ min (p d) γ`, when `p` is
orderly and `γ = γ ⌊+⌋_k k` for every `k` such that some `d` has `a(d) ≥ k` and `p(d) ≥ γ`
(`Label.PrintedCapDefined a p γ`, one field each).  Here the cap is always `d ↦ min (p d) γ`;
`Label.printedCapDefined_iff` restates the condition as self-visibility of `γ` at the arity of
every `d` with `p d ≥ γ`, which holds for the caps of the locality law
(`CellScheme.Rows.printedCapDefined_below`).

## Respecting a semantics, [Kni26, Definition 2.5.4]

| Printed clause | Field of `PrintedRespects` | Law of `IsLawful` |
| --- | --- | --- |
| `p` is orderly (presupposed) | `orderly` | `orderly` |
| 1. `E(Σ) ⇒ p↾D_{⟨B,j⟩} ∧ p(Σ)` for `Σ ∈ D_{B,j}` | `locality` | `locality` |
| 2. `C ⊆ B`, `Σ ∈ D_{C,i}`, `D_{B,i} ≠ ∅`: `p Ξ ≥ p Σ`, `Ξ ∈ D_{B,i}` | `availability` | the same |

The identification is `CellScheme.Rows.printedRespects_iff`: for a scheme whose cells have graded
indices in `D.gradedFaces`, at a stage `θ` that is zero or a limit, for rows and a labelling with
values at stage `θ`, `p` is orderly and respects the semantics as printed exactly when it is a
lawful section.

**Departures**, each proved harmless:
1. *Orientation* of the orderly equation: `Label.printedOrderly_iff`.
2. *The cap* in clause 1 is printed as the partial operation of Definition 2.3.7; it is defined for
   every orderly `p` (`CellScheme.Rows.printedCapDefined_below`), and then it is the minimum.
3. *The relation* `⇒` in clause 1 is the printed one at stage `θ`; it agrees with `TransformsTo`
   for the labellings in question by `Label.printedTransformsTo_iff` (row 3).
4. *Quantification*: clause 1 ranges over `⟨B, j⟩ ∈ P̂` and `Σ ∈ D_{B,j}`, the locality law over
   all cells; clause 2 ranges over `⟨C, i⟩ ∈ P̂`, `B ⊇ C`, `Σ ∈ D_{C,i}` with `D_{B,i} ≠ ∅`, the
   availability law over pairs of cells `s`, `t` with `scope s ⊆ scope t` and equal grades.  They
   agree when every cell has its graded index in `P̂`.
5. *The range of the labels*: as in row 3.
6. *Orderliness of the semantics*: the printed semantics requires each `E(Σ)` to be orderly.
   Harmless: `CellScheme.Rows.printedRespects_iff` holds without it.
7. *Finiteness of the domain*: the printed `D` is finite.  Harmless:
   `CellScheme.Rows.printedRespects_iff` holds for every type of cells.

## Capping, [Kni26, Lemma 2.5.8]

`CellScheme.Rows.PrintedRespects.min_const` is the printed statement: if `p` respects the
semantics and `γ = γ ⌊+⌋_k k` for every `k` that is the arity of some `Σ` with `p(Σ) ≥ γ`, then
`p ∧ γ` is defined and respects the semantics.  It is `CellScheme.Rows.IsLawful.min_const`
transported along `printedRespects_iff`.  The printed `γ` is an ordinal; here it is any label at
the stage.  Restricting `γ` to the stage is the printed typing: an ordinal `γ ≥ ω₁` would make
`p ∧ γ` leave `{-∞} ∪ ω₁ ∪ {∞}` whenever some `p(Σ) = ∞`, and would otherwise give `p ∧ γ = p`.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Label

namespace Label

variable {D : Type*} {a : D → ℕ} {p : D → Label.{u}} {γ : Label.{u}}

/-- **Orderly labellings** [Kni26, Definition 2.3.4]: `p d = p d ⌊+⌋_{a(d)} a(d)` for every `d`,
over the arities `a`. -/
def PrintedOrderly (a : D → ℕ) (p : D → Label.{u}) : Prop :=
  ∀ d, p d = visibilityReplace (a d) (a d) (p d)

/-- A labelling is orderly as printed exactly when every label is self-visible at its arity. -/
theorem printedOrderly_iff : PrintedOrderly a p ↔ ∀ d, IsSelfVisible (a d) (p d) :=
  forall_congr' fun _ ↦ eq_comm

/-- **The conditions under which the cap `p ∧ γ` is defined** [Kni26, Definition 2.3.7]. -/
structure PrintedCapDefined (a : D → ℕ) (p : D → Label.{u}) (γ : Label.{u}) : Prop where
  /-- First condition of [Kni26, Definition 2.3.7]: `p` is orderly with respect to `a`. -/
  orderly : PrintedOrderly a p
  /-- Second condition of [Kni26, Definition 2.3.7]: `γ = γ ⌊+⌋_k k` for every `k` such that some
  `d` has `a(d) ≥ k` and `p(d) ≥ γ`. -/
  visibility : ∀ k : ℕ, (∃ d, k ≤ a d ∧ γ ≤ p d) → γ = visibilityReplace k k γ

/-- The cap `p ∧ γ` is defined exactly when `p` is orderly and `γ` is self-visible at the arity of
every `d` with `γ ≤ p d`. -/
theorem printedCapDefined_iff :
    PrintedCapDefined a p γ ↔
      (∀ d, IsSelfVisible (a d) (p d)) ∧ ∀ d, γ ≤ p d → IsSelfVisible (a d) γ := by
  refine ⟨fun h ↦ ⟨printedOrderly_iff.mp h.orderly, fun d hd ↦
    (h.visibility (a d) ⟨d, le_rfl, hd⟩).symm⟩, fun ⟨hp, hγ⟩ ↦ ⟨printedOrderly_iff.mpr hp, ?_⟩⟩
  rintro k ⟨d, hk, hd⟩
  exact ((hγ d hd).mono hk).symm

/-- The cap of an orderly labelling at a label self-visible at a bound `K` on the arities is
defined [Kni26, Definition 2.3.7]. -/
theorem printedCapDefined_of_isSelfVisible (hp : PrintedOrderly a p) {K : ℕ}
    (hK : ∀ d, a d ≤ K) (hγ : IsSelfVisible K γ) : PrintedCapDefined a p γ :=
  printedCapDefined_iff.mpr ⟨printedOrderly_iff.mp hp, fun d _ ↦ hγ.mono (hK d)⟩

end Label

namespace CellScheme

variable {ι α : Type*} {D : CellScheme ι α}

/-- **The restriction `D↾⟨B, j⟩`** [Kni26, Definition 2.5.2]: when every cell has its graded index
in the graded plan, the cells below `X` are the union of the cells with graded index a graded face
below `X`. -/
theorem mem_below_iff_exists_mem_gradedFaces (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces)
    {X : Finset α × ℕ} {d : ι} :
    d ∈ D.below X ↔ ∃ Y ∈ D.gradedFaces, Y ≤ X ∧ D.gradedIndex d = Y :=
  ⟨fun hd ↦ ⟨_, hD d, hd, rfl⟩, fun ⟨_, _, hYX, hY⟩ ↦ by rw [mem_below, hY]; exact hYX⟩

namespace Rows

variable (R : D.Rows.{u}) {θ : Ordinal.{u}} {p : ι → Label.{u}}

/-- **Labellings respecting a semantics** [Kni26, Definition 2.5.4], at stage `θ`: an orderly
labelling `p` satisfying the two printed clauses, the cap in clause 1 being the partial operation
of [Kni26, Definition 2.3.7] and the relation that of [Kni26, Definition 2.3.9] at stage `θ`. -/
structure PrintedRespects (θ : Ordinal.{u}) (p : ι → Label.{u}) : Prop where
  /-- The presupposition of [Kni26, Definition 2.5.4]: `p` is orderly
  ([Kni26, Definition 2.3.4]). -/
  orderly : PrintedOrderly D.grade p
  /-- Clause 1 of [Kni26, Definition 2.5.4]: for `⟨B, j⟩ ∈ P̂` and `Σ ∈ D_{B,j}`, the cap
  `p↾D_{⟨B,j⟩} ∧ p(Σ)` is defined and `E(Σ) ⇒ p↾D_{⟨B,j⟩} ∧ p(Σ)`. -/
  locality : ∀ s, D.gradedIndex s ∈ D.gradedFaces →
    PrintedCapDefined (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (fun d ↦ p d) (p s) ∧
      PrintedTransformsTo θ (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
        (fun d ↦ min (p d) (p s))
  /-- Clause 2 of [Kni26, Definition 2.5.4]: if `C ⊆ B` and `⟨C, i⟩ ∈ P̂`, then for every
  `Σ ∈ D_{C,i}`, if `D_{B,i} ≠ ∅`, some `Ξ ∈ D_{B,i}` has `p(Ξ) ≥ p(Σ)`. -/
  availability : ∀ (C B : Finset α) (i : ℕ), C ⊆ B → (C, i) ∈ D.gradedFaces →
    ∀ s, D.gradedIndex s = (C, i) → (∃ t, D.gradedIndex t = (B, i)) →
      ∃ u, D.gradedIndex u = (B, i) ∧ p s ≤ p u

/-- **The cap of the locality law is defined** [Kni26, Definition 2.3.7]: for an orderly
labelling, the cap of its restriction below a cell `s` at the label of `s` is defined. -/
theorem printedCapDefined_below (hp : ∀ d, IsSelfVisible (D.grade d) (p d)) (s : ι) :
    PrintedCapDefined (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (fun d ↦ p d) (p s) :=
  printedCapDefined_iff.mpr ⟨fun d ↦ hp d, fun d _ ↦ (hp s).mono d.2.2⟩

/-- **Lawful sections are the orderly labellings respecting the semantics**
[Kni26, Definitions 2.3.4 and 2.5.4]: for a scheme whose cells have their graded indices in the
graded plan, at a stage `θ` that is zero or a limit, and for rows and a labelling with values at
stage `θ`, `p` respects the rows as printed exactly when it is a lawful section. -/
theorem printedRespects_iff (hθ : Order.IsSuccPrelimit θ)
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hR : ∀ s t, AtStage θ (R.row s t))
    (hp : ∀ d, AtStage θ (p d)) : R.PrintedRespects θ p ↔ R.IsLawful p := by
  have htr (s : ι) := printedTransformsTo_iff (a := fun d : D.below (D.gradedIndex s) ↦ D.grade d)
    hθ (hR s) (q := fun d ↦ min (p d) (p s)) fun d ↦ (hp d).min (hp s)
  refine ⟨fun h ↦ ⟨printedOrderly_iff.mp h.orderly, fun s ↦ (htr s).mp (h.locality s (hD s)).2,
    fun s t hst hg ↦ ?_⟩, fun h ↦ ⟨printedOrderly_iff.mpr h.orderly,
    fun s _ ↦ ⟨printedCapDefined_below h.orderly s, (htr s).mpr (h.locality s)⟩, ?_⟩⟩
  · obtain ⟨u, hu, hpu⟩ := h.availability (D.scope s) (D.scope t) (D.grade s) hst (hD s) s rfl
      ⟨t, by rw [hg]; rfl⟩
    exact ⟨u, by rw [hu, hg]; rfl, hpu⟩
  · rintro C B i hCB - s hs ⟨t, ht⟩
    have hs₁ : D.scope s = C := congrArg Prod.fst hs
    have hs₂ : D.grade s = i := congrArg Prod.snd hs
    have ht₁ : D.scope t = B := congrArg Prod.fst ht
    have ht₂ : D.grade t = i := congrArg Prod.snd ht
    obtain ⟨u, hu, hpu⟩ := h.availability s t (by rw [hs₁, ht₁]; exact hCB) (hs₂.trans ht₂.symm)
    exact ⟨u, hu.trans ht, hpu⟩

/-- **Lawful sections are the orderly labellings respecting the semantics**
[Kni26, Definitions 2.3.4 and 2.5.4], on the printed labels `{-∞} ∪ ω₁ ∪ {∞}`: for a scheme whose
cells have their graded indices in the graded plan, and for rows and a labelling with values at
stage `ω₁`, `p` respects the rows as printed exactly when it is a lawful section. -/
theorem printedRespects_omega_one_iff (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces)
    (hR : ∀ s t, AtStage (Ordinal.omega 1) (R.row s t))
    (hp : ∀ d, AtStage (Ordinal.omega 1) (p d)) :
    R.PrintedRespects (Ordinal.omega 1) p ↔ R.IsLawful p :=
  R.printedRespects_iff (Cardinal.isSuccLimit_omega 1).isSuccPrelimit hD hR hp

/-- **Capping a labelling respecting a semantics** [Kni26, Lemma 2.5.8], in the printed form: if
`p` respects the rows and `γ = γ ⌊+⌋_k k` for every `k` that is the arity of a cell `d` with
`γ ≤ p d`, then the cap `p ∧ γ` is defined and respects the rows.  The hypotheses are those of
`printedRespects_iff`, with `γ` at stage `θ`. -/
theorem PrintedRespects.min_const (hθ : Order.IsSuccPrelimit θ)
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hR : ∀ s t, AtStage θ (R.row s t))
    (hp : ∀ d, AtStage θ (p d)) (h : R.PrintedRespects θ p) {γ : Label.{u}}
    (hγ : AtStage θ γ) (hγv : ∀ k, (∃ d, D.grade d = k ∧ γ ≤ p d) → γ = visibilityReplace k k γ) :
    PrintedCapDefined D.grade p γ ∧ R.PrintedRespects θ (fun d ↦ min (p d) γ) := by
  have hc (d : ι) (hd : γ ≤ p d) : IsSelfVisible (D.grade d) γ := (hγv _ ⟨d, rfl, hd⟩).symm
  have hl := (R.printedRespects_iff hθ hD hR hp).mp h
  exact ⟨printedCapDefined_iff.mpr ⟨hl.orderly, hc⟩,
    (R.printedRespects_iff hθ hD hR fun d ↦ (hp d).min hγ).mpr (hl.min_const hc)⟩

end Rows

end CellScheme

end VaughtConjecture
