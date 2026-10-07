/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Bountiful
import VaughtConjecture.Geometry.IntervalPlan
import VaughtConjecture.Label.OmegaOne
import VaughtConjecture.Stage.Legal

/-!
# Correspondence: domains and legal schemes

Roadmap, "Manuscript concordance", row 7.  The printed definition of a domain with its semantics
[Kni26, Definition 2.6.1] is compiled clause by clause (`CellScheme.Rows.PrintedDomain`) and
compared with the legality of a scheme (`Scheme.IsLegal`).  The comparison shows that legality is
a corrected form of the printed definition: it adds the coding clause `Scheme.IsCoded`, a bound on
the range of the rows, which the printed clauses compared here (the fields of `PrintedDomain`) do
not imply, and it requires bountifulness at every stage; its cells are positions, and the codes
of the printed cells are forgotten (departure 1).  The status of the row is C, with
bountifulness at `ω₁` still to be proved (row 6, S).

## The setting

As in `VaughtConjecture.Correspondence.Lawful`, the printed domain `D` over the graded plan `P̂` of
a plan `P` on a finite set `A` is a cell scheme `D : CellScheme ι α` whose cells with graded index
`⟨B, j⟩` form `D_{B,j}`, and the semantics `E` is a family of rows `R : D.Rows`.  The printed
labels are those at stage `ω₁`; the definition is stated at a stage `θ`
(`CellScheme.Rows.PrintedDomain R θ`).  A semantics for `D` [Kni26, Definition 2.5.3] is the
union clause, the range of the rows, and orderliness; it is complete
[Kni26, Definition 2.5.15] when it is bountiful [Kni26, Definition 2.5.14], hence consistent
[Kni26, Definition 2.5.12], and every `D_{B,j}` with `⟨B, j⟩ ∈ P̂` is nonempty.

## Consistency, [Kni26, Definition 2.5.12]

`CellScheme.Rows.PrintedConsistent R θ`: for `⟨B, j⟩ ∈ P̂` and `Σ ∈ D_{B,j}`, `E(Σ)` respects the
semantics `E_{⟨B,j⟩}` (row 4).  At a stage `θ` that is zero or a limit and carries the values of
the rows, it is `CellScheme.Rows.IsConsistent` (`CellScheme.Rows.printedConsistent_iff`).

## Domains, [Kni26, Definition 2.6.1]

In the third column, `IsWellFormed`, `IsComplete`, and `Rows` are in the namespace `CellScheme`.

| Printed clause | Field of `PrintedDomain` | Here |
| --- | --- | --- |
| `P` is a plan on `A` (the setting) | `isPlan` | `IsWellFormed.isPlan` |
| `D` is a finite set | `finite` | `IsWellFormed.finite` |
| `D = ⋃ {D_{B,j} : ⟨B,j⟩ ∈ P̂}` (2.5.3) | `gradedIndex_mem` | `IsWellFormed.gradedIndex_mem` |
| `E(Σ)` has values in `{-∞} ∪ θ ∪ {∞}` (after 2.5.2; 2.5.4) | `row_atStage` | (the stage) |
| `E(Σ)` is orderly (2.5.3) | `orderly` | `Rows.IsConsistent.isOrderly` |
| `E` is consistent (2.5.12, presupposed in 2.5.14) | `consistent` | `Rows.IsConsistent` |
| `E` is bountiful (2.5.14) | `bountiful` | `Rows.IsBountiful` (row 6) |
| `D_{B,j} ≠ ∅` for `⟨B,j⟩ ∈ P̂` (2.5.15) | `complete` | `IsComplete` |
| `⟨B,j⟩`, `P↾B`, `D↾⟨B,j⟩`, `E↾⟨B,j⟩` recoverable from `Ξ` | none | departure 1 |
| the code `⌜⌜Ξ⌝⌝ ∈ D̃_{B,j}` of `Ξ` (after 2.6.2) | none | departure 1 |

**Identification.**  At a stage `θ` that is zero or a limit, the printed definition is
well-formedness, consistency, the printed bountifulness at `θ`, and completeness, for rows with
values at `θ` (`CellScheme.Rows.printedDomain_iff`).  A legal scheme is a domain as printed at
every such stage carrying the values of its rows (`Scheme.IsLegal.printedDomain`), in particular
at `ω₁` (`Scheme.IsLegal.printedDomain_omega_one`).  Conversely, a scheme is legal exactly when
its ground set is all of its points, its rows are coded, and it is a domain as printed at every
stage that is zero or a limit and carries the values of its rows
(`Scheme.isLegal_iff_forall_printedDomain`).

**Departures.**  The row is a corrected definition (C), for the reasons 1 and 2; the comparison
at a single stage is also incomplete, by 3, so its status is C with bountifulness at `ω₁` still to
be proved (row 6, S).
1. *The recoverability clause and the codes of the cells* (no field).  The printed elements of `D`
   are sets chosen so that `⟨B,j⟩`, `P↾B`, `D↾⟨B,j⟩`, and `E↾⟨B,j⟩` can be read off each
   `Ξ ∈ D_{B,j}` by a standard coding.  Here a cell is a position in a scheme whose graded index,
   faces, cells below, and rows are fields of the scheme, so these are recovered by projection; the
   clause, a condition on the objects chosen as cells, has no counterpart and is not compared.  The
   coding described after [Kni26, Definition 2.6.2] also gives each `Ξ ∈ D_{B,j}` a code
   `⌜⌜Ξ⌝⌝`, a natural number in a finite set `D̃_{B,j}`, one-to-one, and the map `Df` of
   [Kni26, Proposition 2.6.3, clause 5] keeps it.  The cells here are the positions `Fin card` and
   carry no code (`Scheme` has no code accessor): a printed domain corresponds to a scheme through
   a numbering of its cells by positions, and the codes are forgotten, so printed domains that
   differ only in their codes correspond to the same scheme.  Forgetting the codes is part of the
   correction of this row; the face maps (row 8) are compared under it.
2. *The range of the rows* (the correction).  `Scheme.IsLegal` requires the rows to be coded, with
   every value bottom or below `ω ^ 2` (`Scheme.IsCoded`).  The printed definition bounds no value.
   The coding described after [Kni26, Definition 2.6.2] stores each `E(Σ)` in `{-∞} ∪ ω ^ 2` by the
   first clause of [Kni26, Lemma 2.5.13], which replaces `E(Σ)` by a function equivalent under `⇔`
   when only the functions respecting `E` matter; that clause is not compiled, the printed text does
   not state the effect of the replacement on consistency, bountifulness, and completeness, and the
   offset bound of the same lemma is not correct as stated (the roadmap, Layer 1) and is not used.
   The printed clauses compared here, the fields of `PrintedDomain`, which omit the recoverability
   clause 1, do not imply the range bound `Scheme.IsCoded`: the scheme on one point with a single
   cell whose row is the formal top satisfies them at every stage that is zero or a limit and is
   not coded (`Scheme.exists_printedDomain_not_isCoded`).
3. *Bountifulness at a single stage* (row 6, S).  `Scheme.IsLegal` requires `IsBountiful`, the
   printed definition at every stage that is zero or a limit and carries the values of the rows;
   at `ω₁` only the implication from `IsBountiful` is proved.  This is neither a recorded
   correction nor proved equivalent, so the declarations whose clauses use domains (rows 8 and 11)
   identify the printed definitions over legal schemes only: a coded scheme that is a domain as
   printed at `ω₁` but not at some other stage that is zero or a limit would not be legal, and
   whether one exists is row 6.
4. *The points.*  The printed `A` is a finite set; a scheme on `n` points has the points `Fin n`,
   and legality asks its ground set to be all of them (`Scheme.IsWellFormed.ground_eq`), as for
   the type spaces `S^α n` of [Kni26, Definition 3.2.1].

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace CellScheme

variable {ι α : Type*} {D : CellScheme ι α}

namespace Rows

variable (R : D.Rows.{u}) {θ : Ordinal.{u}}

/-- **Consistent semantics** [Kni26, Definition 2.5.12], at stage `θ`: for every `⟨B, j⟩ ∈ P̂` and
every `Σ ∈ D_{B,j}`, `E(Σ)` respects the semantics `E_{⟨B,j⟩}` of `D_{⟨B,j⟩}`. -/
def PrintedConsistent (θ : Ordinal.{u}) : Prop :=
  ∀ s, D.gradedIndex s ∈ D.gradedFaces →
    (R.comap (IsLowerEmbedding.subtypeVal_below D (D.gradedIndex s))).PrintedRespects θ (R.row s)

variable {R}

/-- **Consistency is the printed definition** [Kni26, Definition 2.5.12]: for a scheme whose cells
have their graded indices in the graded plan, at a stage `θ` that is zero or a limit, for rows with
values at stage `θ`, the rows are consistent as printed exactly when they are consistent. -/
theorem printedConsistent_iff (hθ : Order.IsSuccPrelimit θ)
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hR : ∀ s t, AtStage θ (R.row s t)) :
    R.PrintedConsistent θ ↔ R.IsConsistent :=
  ⟨fun h s ↦ (printedRespects_below_iff hθ hD hR (hR s)).mp (h s (hD s)),
    fun h s _ ↦ (printedRespects_below_iff hθ hD hR (hR s)).mpr (h s)⟩

variable (R) [DecidableEq α]

/-- **Domains with their semantics** [Kni26, Definition 2.6.1], at stage `θ`: the cells form a
finite set, the union over the graded plan of a plan, and the rows are a complete semantics for
them: a semantics [Kni26, Definition 2.5.3] that is consistent [Kni26, Definition 2.5.12],
bountiful [Kni26, Definition 2.5.14], and has a cell at every graded face
[Kni26, Definition 2.5.15].  The recoverability clause of [Kni26, Definition 2.6.1] has no field
(departure 1 of the module documentation). -/
structure PrintedDomain (θ : Ordinal.{u}) : Prop where
  /-- The setting of [Kni26, Definition 2.6.1]: `P` is a plan on `A`. -/
  isPlan : Geometry.IsPlan D.ground D.faces
  /-- [Kni26, Definition 2.6.1]: `D` is a finite set. -/
  finite : Finite ι
  /-- [Kni26, Definition 2.5.3], a semantics for `D`: `D` is the union of the `D_{B,j}` for
  `⟨B, j⟩ ∈ P̂`. -/
  gradedIndex_mem : ∀ d, D.gradedIndex d ∈ D.gradedFaces
  /-- [Kni26, Definition 2.5.3], a semantics for `D`: each `E(Σ)` takes values in
  `{-∞} ∪ θ ∪ {∞}`, the range stated in the text after [Kni26, Definition 2.5.2] and in
  [Kni26, Definition 2.5.4] (`p : D → {-∞} ∪ ω₁ ∪ {∞}`). -/
  row_atStage : ∀ s t, AtStage θ (R.row s t)
  /-- [Kni26, Definition 2.5.3], a semantics for `D`: each `E(Σ)` is orderly with respect to the
  arity. -/
  orderly : ∀ s, PrintedOrderly (fun t : D.below (D.gradedIndex s) ↦ D.grade t) (R.row s)
  /-- [Kni26, Definition 2.5.12], presupposed by [Kni26, Definition 2.5.14]: `E` is
  consistent. -/
  consistent : R.PrintedConsistent θ
  /-- [Kni26, Definition 2.5.14], required by [Kni26, Definition 2.5.15]: `E` is bountiful. -/
  bountiful : R.PrintedBountiful θ
  /-- [Kni26, Definition 2.5.15]: `E` is complete, `D_{B,j} ≠ ∅` for every `⟨B, j⟩ ∈ P̂`. -/
  complete : ∀ X ∈ D.gradedFaces, ∃ d, D.gradedIndex d = X

variable {R}

/-- **Domains as printed** [Kni26, Definition 2.6.1]: at a stage `θ` that is zero or a limit, the
rows are a domain as printed exactly when they take values at stage `θ`, the cell scheme is well
formed, and the rows are consistent, bountiful as printed at `θ`, and complete. -/
theorem printedDomain_iff (hθ : Order.IsSuccPrelimit θ) :
    R.PrintedDomain θ ↔ (∀ s t, AtStage θ (R.row s t)) ∧ D.IsWellFormed ∧ R.IsConsistent ∧
      R.PrintedBountiful θ ∧ D.IsComplete := by
  refine ⟨fun h ↦ ⟨h.row_atStage, ⟨h.finite, h.isPlan, h.gradedIndex_mem⟩,
    (printedConsistent_iff hθ h.gradedIndex_mem h.row_atStage).mp h.consistent, h.bountiful,
    h.complete⟩, fun ⟨hR, hD, hc, hb, hC⟩ ↦ ⟨hD.isPlan, hD.finite, hD.gradedIndex_mem, hR,
    fun s ↦ printedOrderly_iff.mpr (hc.isOrderly s), ?_, hb, hC⟩⟩
  exact (printedConsistent_iff hθ hD.gradedIndex_mem hR).mpr hc

end Rows

end CellScheme

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {θ : Ordinal.{u}}

/-- Coded rows take values at every stage at least `ω ^ 2`. -/
theorem IsCoded.atStage (hS : S.IsCoded) (hθ : Ordinal.omega0 ^ 2 ≤ θ) (s : Fin S.card)
    (t : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) : AtStage θ (S.rows.row s t) :=
  .inl ((hS s t).trans_le (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hθ)))

/-- Coded rows take values at stage `ω₁`. -/
theorem IsCoded.atStage_omega_one (hS : S.IsCoded) (s : Fin S.card)
    (t : S.toCellScheme.below (S.toCellScheme.gradedIndex s)) :
    AtStage (Ordinal.omega.{u} 1) (S.rows.row s t) :=
  hS.atStage omega0_sq_lt_omega_one.le s t

/-- **Legal schemes are domains as printed** [Kni26, Definition 2.6.1], at every stage `θ` that is
zero or a limit and carries the values of the rows. -/
theorem IsLegal.printedDomain (hS : S.IsLegal) (hθ : Order.IsSuccPrelimit θ)
    (hR : ∀ s t, AtStage θ (S.rows.row s t)) : S.rows.PrintedDomain θ :=
  (CellScheme.Rows.printedDomain_iff hθ).mpr ⟨hR, hS.isWellFormed.isWellFormed, hS.isConsistent,
    hS.isBountiful.printedBountiful hθ hS.isWellFormed.isWellFormed.gradedIndex_mem hR,
    hS.isComplete⟩

/-- **Legal schemes are domains as printed** [Kni26, Definition 2.6.1], on the printed labels
`{-∞} ∪ ω₁ ∪ {∞}`. -/
theorem IsLegal.printedDomain_omega_one (hS : S.IsLegal) :
    S.rows.PrintedDomain (Ordinal.omega.{u} 1) :=
  hS.printedDomain (Cardinal.isSuccLimit_omega 1).isSuccPrelimit hS.isCoded.atStage_omega_one

/-- **Legality is the printed definition at every stage, with the coding clause**
[Kni26, Definition 2.6.1]: a scheme is legal exactly when its ground set is all of its points,
its rows are coded, and it is a domain as printed at every stage that is zero or a limit and
carries the values of its rows. -/
theorem isLegal_iff_forall_printedDomain :
    S.IsLegal ↔ S.toCellScheme.ground = univ ∧ S.IsCoded ∧
      ∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → (∀ s t, AtStage θ (S.rows.row s t)) →
        S.rows.PrintedDomain θ := by
  refine ⟨fun h ↦ ⟨h.isWellFormed.ground_eq, h.isCoded, fun _ hθ hR ↦ h.printedDomain hθ hR⟩,
    fun ⟨hg, hc, h⟩ ↦ ?_⟩
  have hθ := (Cardinal.isSuccLimit_omega.{u} 1).isSuccPrelimit
  obtain ⟨-, hD, hcons, -, hC⟩ :=
    (CellScheme.Rows.printedDomain_iff hθ).mp (h _ hθ hc.atStage_omega_one)
  have := hD.finite
  refine ⟨⟨hg, hD⟩, hc, hcons, ?_, hC⟩
  exact (CellScheme.Rows.isBountiful_iff_forall_printedBountiful hD.gradedIndex_mem).mpr
    fun θ hθ hR ↦ (h θ hθ hR).bountiful

/-! ### The range bound is not implied by the compared clauses -/

/-- The scheme on one point with a single cell of scope `{0}` and grade `1`, the faces `∅` and
`{0}`, and the row of the cell the formal top. -/
private def topPoint : Scheme.{0} 1 where
  card := 1
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, fun _ ↦ univ, fun _ ↦ 1⟩
  rows := ⟨fun _ _ ↦ ⊤⟩

private theorem isWellFormed_topPoint : topPoint.toCellScheme.IsWellFormed :=
  ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun _ ↦ by
    simp [CellScheme.gradedIndex, topPoint]⟩

/-- The only graded face of `topPoint` is `({0}, 1)`. -/
private theorem eq_of_mem_gradedFaces_topPoint {X : Finset (Fin 1) × ℕ}
    (hX : X ∈ topPoint.toCellScheme.gradedFaces) : X = (univ, 1) := by
  obtain ⟨C, j⟩ := X
  obtain ⟨-, hpos, hle⟩ := hX
  have hC : #C ≤ 1 := card_le_univ C
  simp only at hpos hle
  have hC' : C = univ := (card_eq_iff_eq_univ C).mp (by simp; omega)
  simp only [hC', Prod.mk.injEq, true_and]
  omega

private theorem isConsistent_topPoint : topPoint.rows.IsConsistent := fun _ ↦
  { orderly := fun _ ↦ isSelfVisible_top _
    locality := fun _ ↦ by
      -- By the definition of `topPoint`, the row of the cell and its label are the formal top.
      change TransformsTo _ (fun _ ↦ (⊤ : Label.{0})) (fun _ ↦ min ⊤ ⊤)
      simpa only [min_self] using TransformsTo.refl _ _
    availability := fun _ t _ _ ↦ ⟨t, rfl, le_rfl⟩ }

private theorem isBountiful_topPoint : topPoint.rows.IsBountiful := by
  intro X Y hX hY h
  obtain rfl := eq_of_mem_gradedFaces_topPoint hX
  obtain rfl := eq_of_mem_gradedFaces_topPoint hY
  exact CellScheme.Rows.cappedLift_refl (R := topPoint.rows) (univ, 1)

private theorem isComplete_topPoint : topPoint.toCellScheme.IsComplete := fun _ hX ↦
  ⟨⟨0, zero_lt_one⟩, (eq_of_mem_gradedFaces_topPoint hX).symm ▸ rfl⟩

/-- **The compared clauses do not imply the range bound** [Kni26, Definition 2.6.1]: some scheme on
one point, with ground set its point, satisfies the fields of `PrintedDomain` (the printed clauses
other than recoverability) at every stage that is zero or a limit and is not coded
(`Scheme.IsCoded`).  It is the scheme with a single cell whose row is the formal top. -/
theorem exists_printedDomain_not_isCoded :
    ∃ S : Scheme.{0} 1, S.toCellScheme.ground = univ ∧
      (∀ θ : Ordinal.{0}, Order.IsSuccPrelimit θ → S.rows.PrintedDomain θ) ∧ ¬ S.IsCoded := by
  refine ⟨topPoint, rfl, fun θ hθ ↦ ?_, fun h ↦ ?_⟩
  · have hR : ∀ s t, AtStage θ (topPoint.rows.row s t) := fun _ _ ↦ atStage_top
    exact (CellScheme.Rows.printedDomain_iff hθ).mpr ⟨hR, isWellFormed_topPoint,
      isConsistent_topPoint,
      isBountiful_topPoint.printedBountiful hθ isWellFormed_topPoint.gradedIndex_mem hR,
      isComplete_topPoint⟩
  · have s : Fin topPoint.card := ⟨0, zero_lt_one⟩
    exact (h s ⟨s, CellScheme.mem_below_gradedIndex _ s⟩).ne_top rfl

end Scheme

end VaughtConjecture
