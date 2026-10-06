/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Lawful
import VaughtConjecture.Scheme.Bountiful

/-!
# Correspondence: bountiful rows

Roadmap, "Manuscript concordance", row 6.  The printed definition of a bountiful semantics
[Kni26, Definition 2.5.14] is compared clause by clause with `CellScheme.Rows.IsBountiful`, in its
extension form `CellScheme.Rows.isBountiful_iff_forall_exists`.

The setting is that of `VaughtConjecture.Correspondence.Lawful`: cells of a scheme `D` for the
printed domain, rows `R` for the semantics `E`, and the semantics `E_{⟨C,i⟩}` restricted to
`D_{⟨C,i⟩}` [Kni26, Definition 2.5.6] for the rows pulled back to the cells below `(C, i)`
(`R.comap (IsLowerEmbedding.subtypeVal_below D (C, i))`), so that "`p` respects `E_{⟨C,i⟩}`" is
`PrintedRespects` for these rows (row 4).  The printed labels are those at stage `ω₁`; the
definition is stated at a stage `θ` (`CellScheme.Rows.PrintedBountiful R θ`).  Its hypotheses
and its conclusion are two structures, one field per printed clause:

| Printed clause | Field | Extension form of `IsBountiful` |
| --- | --- | --- |
| 1. `⟨C,i⟩, ⟨B,j⟩ ∈ P̂`, `⟨C,i⟩ ≺ ⟨B,j⟩` | `mem_left`, `mem_right`, `le` | `X ≤ Y` graded faces |
| 2. `p : D_{⟨C,i⟩} → {-∞} ∪ θ ∪ {∞}` | `left_atStage` | `p : D.below X → Label` |
| 3. `q : D_{⟨B,j⟩} → {-∞} ∪ θ ∪ {∞}` | `right_atStage` | `q : D.below Y → Label` |
| 4. `γ ∈ {-∞} ∪ θ ∪ {∞}` | `cap_atStage` | `c : Label` |
| 5. `p` respects `E_{⟨C,i⟩}` | `left_respects` | `R.IsLawfulBelow X p` |
| 6. `q` respects `E_{⟨B,j⟩}` | `right_respects` | `R.IsLawfulBelow Y q` |
| 7. `γ = γ ⌊+⌋_j j` | `visibility` | `IsSelfVisible Y.2 c` |
| 8. `(q ∧ γ)↾D_{⟨C,i⟩} = p ∧ γ` | `cap_eq` | the capped observations agree |
| conclusion: `q'` on `D_{⟨B,j⟩}` | `atStage` | `q' : D.below Y → Label` |
| conclusion 1. `q'` respects `E_{⟨B,j⟩}` | `respects` | `R.IsLawfulBelow Y q'` |
| conclusion 2. `q' ∧ γ = q ∧ γ` | `cap_eq` | the capped observations agree |
| conclusion 3. `q'↾D_{⟨C,i⟩} = p` | `restrict_eq` | `q'` restricts to `p` |

**Identification.**  For a scheme with finitely many cells, all with graded index in the graded
plan, the rows are bountiful exactly when they are bountiful as printed at every stage that is
zero or a limit and carries their values
(`CellScheme.Rows.isBountiful_iff_forall_printedBountiful`).  Bountiful rows are bountiful as
printed at each such stage (`CellScheme.Rows.IsBountiful.printedBountiful`), in particular at `ω₁`
(`CellScheme.Rows.IsBountiful.printedBountiful_omega_one`).  No theorem here identifies
`IsBountiful` with the printed definition at a single stage, in particular at `ω₁`: the row is
still to be proved (departure 4).

**Departures.**
1. *The order of clause 1.*  The relation `⪯` of [Kni26, Definition 2.5.1] is the product order
   on pairs.  Clause 1 prints `≺`; read strictly, it omits the case `⟨C,i⟩ = ⟨B,j⟩`, in which the
   conclusion holds for every semantics
   (`CellScheme.Rows.PrintedLiftHypotheses.exists_printedLiftConclusion_of_eq`), so both readings
   give the same definition (`CellScheme.Rows.printedBountiful_iff_forall_lt`).
2. *The caps* `q ∧ γ`, `p ∧ γ`, `q' ∧ γ` are the partial operation of
   [Kni26, Definition 2.3.7]; under clause 7 they are defined
   (`CellScheme.Rows.PrintedLiftHypotheses.printedCapDefined`,
   `CellScheme.Rows.PrintedLiftConclusion.printedCapDefined`), and they are then the minima.
3. *Consistency.*  The printed definition presupposes that `E` is consistent
   [Kni26, Definition 2.5.12] (`CellScheme.Rows.IsConsistent`); `IsBountiful` is defined for all
   rows.  Harmless: `CellScheme.Rows.isBountiful_iff_forall_printedBountiful` and
   `CellScheme.Rows.IsBountiful.printedBountiful` hold without it.
4. *The range of the labels* (not proved harmless at a single stage).  `IsBountiful` quantifies
   over labellings and caps among all labels, the printed definition over those at stage `θ`.  The
   two agree when the printed definition is required at every stage that is zero or a limit (the
   identification above); at a single stage, in particular at the stage `ω₁` of [Kni26], only the
   implication from `IsBountiful` is proved.  What is missing is the transfer of the printed
   definition from `ω₁` up to larger stages that are limits, which would need a collapse of labels
   preserving lawfulness in the style of [Kni26, Lemmas 2.3.3 and 2.5.13]; it is prospective.
   The downward transfer, from a larger stage that is a limit to a smaller one such as `ω₁`,
   follows by the argument of `CellScheme.Rows.IsBountiful.printedBountiful` but is not a named
   theorem either.
   Restricting the universe does not remove the gap: `Label.{0}` already contains uncountable
   ordinals, such as `Ordinal.omega.{0} 1`, and `IsBountiful` quantifies over all of `Label.{u}`.

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Label

namespace CellScheme

variable {ι α : Type*} {D : CellScheme ι α}

/-- The cells below a pair have their graded indices in the graded plan when the cells of the
scheme do. -/
theorem gradedIndex_mem_gradedFaces_below (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces)
    (X : Finset α × ℕ) (d : D.below X) :
    (D.reindex ((↑) : D.below X → ι)).gradedIndex d ∈
      (D.reindex ((↑) : D.below X → ι)).gradedFaces :=
  hD d

namespace Rows

variable (R : D.Rows.{u}) {θ : Ordinal.{u}} {X Y : Finset α × ℕ}

/-- **The hypotheses of [Kni26, Definition 2.5.14]**, clauses 1–8, for pairs `X = ⟨C, i⟩` and
`Y = ⟨B, j⟩`, labellings `p` below `X` and `q` below `Y`, and a cap `γ`, at stage `θ`. -/
structure PrintedLiftHypotheses (θ : Ordinal.{u}) (X Y : Finset α × ℕ) (p : D.below X → Label.{u})
    (q : D.below Y → Label.{u}) (γ : Label.{u}) : Prop where
  /-- Clause 1 of [Kni26, Definition 2.5.14]: `⟨C, i⟩ ∈ P̂`. -/
  mem_left : X ∈ D.gradedFaces
  /-- Clause 1 of [Kni26, Definition 2.5.14]: `⟨B, j⟩ ∈ P̂`. -/
  mem_right : Y ∈ D.gradedFaces
  /-- Clause 1 of [Kni26, Definition 2.5.14]: `⟨C, i⟩ ⪯ ⟨B, j⟩`, the order of
  [Kni26, Definition 2.5.1]. -/
  le : X ≤ Y
  /-- Clause 2 of [Kni26, Definition 2.5.14]: `p` takes values in `{-∞} ∪ θ ∪ {∞}`. -/
  left_atStage : ∀ d, AtStage θ (p d)
  /-- Clause 3 of [Kni26, Definition 2.5.14]: `q` takes values in `{-∞} ∪ θ ∪ {∞}`. -/
  right_atStage : ∀ d, AtStage θ (q d)
  /-- Clause 4 of [Kni26, Definition 2.5.14]: `γ ∈ {-∞} ∪ θ ∪ {∞}`. -/
  cap_atStage : AtStage θ γ
  /-- Clause 5 of [Kni26, Definition 2.5.14]: `p` respects `E_{⟨C,i⟩}`. -/
  left_respects : (R.comap (IsLowerEmbedding.subtypeVal_below D X)).PrintedRespects θ p
  /-- Clause 6 of [Kni26, Definition 2.5.14]: `q` respects `E_{⟨B,j⟩}`. -/
  right_respects : (R.comap (IsLowerEmbedding.subtypeVal_below D Y)).PrintedRespects θ q
  /-- Clause 7 of [Kni26, Definition 2.5.14]: `γ = γ ⌊+⌋_j j`. -/
  visibility : γ = visibilityReplace Y.2 Y.2 γ
  /-- Clause 8 of [Kni26, Definition 2.5.14]: `(q ∧ γ)↾D_{⟨C,i⟩} = p ∧ γ`. -/
  cap_eq : ∀ d : D.below X, min (q (Set.inclusion (D.below_mono le) d)) γ = min (p d) γ

/-- **The conclusion of [Kni26, Definition 2.5.14]**, clauses 1–3, for a labelling `q'` below
`Y`. -/
structure PrintedLiftConclusion (θ : Ordinal.{u}) (h : X ≤ Y) (p : D.below X → Label.{u})
    (q : D.below Y → Label.{u}) (γ : Label.{u}) (q' : D.below Y → Label.{u}) : Prop where
  /-- The typing of the conclusion of [Kni26, Definition 2.5.14]: `q'` has domain `D_{⟨B,j⟩}` and
  values in `{-∞} ∪ θ ∪ {∞}`. -/
  atStage : ∀ d, AtStage θ (q' d)
  /-- Clause 1 of the conclusion of [Kni26, Definition 2.5.14]: `q'` respects `E_{⟨B,j⟩}`. -/
  respects : (R.comap (IsLowerEmbedding.subtypeVal_below D Y)).PrintedRespects θ q'
  /-- Clause 2 of the conclusion of [Kni26, Definition 2.5.14]: `q' ∧ γ = q ∧ γ`. -/
  cap_eq : ∀ d, min (q' d) γ = min (q d) γ
  /-- Clause 3 of the conclusion of [Kni26, Definition 2.5.14]: `q'↾D_{⟨C,i⟩} = p`. -/
  restrict_eq : ∀ d : D.below X, q' (Set.inclusion (D.below_mono h) d) = p d

/-- **Bountiful semantics** [Kni26, Definition 2.5.14], at stage `θ`: whenever clauses 1–8 hold,
some `q'` satisfies the three clauses of the conclusion. -/
def PrintedBountiful (θ : Ordinal.{u}) : Prop :=
  ∀ (X Y : Finset α × ℕ) (p : D.below X → Label.{u}) (q : D.below Y → Label.{u})
    (γ : Label.{u}) (h : R.PrintedLiftHypotheses θ X Y p q γ),
    ∃ q', R.PrintedLiftConclusion θ h.le p q γ q'

variable {R} {p : D.below X → Label.{u}} {q : D.below Y → Label.{u}} {γ : Label.{u}}

/-- **The caps of clause 8 are defined** [Kni26, Definition 2.3.7]: under clauses 5–7, the caps
`q ∧ γ` and `p ∧ γ` are defined. -/
theorem PrintedLiftHypotheses.printedCapDefined (h : R.PrintedLiftHypotheses θ X Y p q γ) :
    PrintedCapDefined (fun d : D.below Y ↦ D.grade d) q γ ∧
      PrintedCapDefined (fun d : D.below X ↦ D.grade d) p γ :=
  ⟨printedCapDefined_of_isSelfVisible h.right_respects.orderly (fun d ↦ d.2.2)
      h.visibility.symm,
    printedCapDefined_of_isSelfVisible h.left_respects.orderly (fun d ↦ d.2.2.trans h.le.2)
      h.visibility.symm⟩

/-- **The cap of conclusion 2 is defined** [Kni26, Definition 2.3.7]: under clause 7, the cap
`q' ∧ γ` is defined. -/
theorem PrintedLiftConclusion.printedCapDefined {hXY : X ≤ Y} {q' : D.below Y → Label.{u}}
    (h : R.PrintedLiftConclusion θ hXY p q γ q') (hγ : γ = visibilityReplace Y.2 Y.2 γ) :
    PrintedCapDefined (fun d : D.below Y ↦ D.grade d) q' γ :=
  printedCapDefined_of_isSelfVisible h.respects.orderly (fun d ↦ d.2.2) hγ.symm

/-- **The reflexive case of [Kni26, Definition 2.5.14]**: when `⟨C, i⟩ = ⟨B, j⟩`, the conclusion
holds for every semantics, with `q' = p`.  Reading `≺` in clause 1 strictly therefore gives the
same definition. -/
theorem PrintedLiftHypotheses.exists_printedLiftConclusion_of_eq
    (h : R.PrintedLiftHypotheses θ X Y p q γ) (hXY : X = Y) :
    ∃ q', R.PrintedLiftConclusion θ h.le p q γ q' := by
  subst hXY
  exact ⟨p, h.left_atStage, h.left_respects, fun d ↦ (h.cap_eq d).symm, fun _ ↦ rfl⟩

/-- **The strict reading of clause 1 of [Kni26, Definition 2.5.14]**: the rows are bountiful as
printed at stage `θ` exactly when the conclusion holds for every instance of clauses 1–8 with
`⟨C, i⟩ ≺ ⟨B, j⟩` strict. -/
theorem printedBountiful_iff_forall_lt :
    R.PrintedBountiful θ ↔
      ∀ (X Y : Finset α × ℕ) (p : D.below X → Label.{u}) (q : D.below Y → Label.{u})
        (γ : Label.{u}) (h : R.PrintedLiftHypotheses θ X Y p q γ), X < Y →
        ∃ q', R.PrintedLiftConclusion θ h.le p q γ q' := by
  refine ⟨fun hb X Y p q γ h _ ↦ hb X Y p q γ h, fun hb X Y p q γ h ↦ ?_⟩
  rcases h.le.lt_or_eq with hlt | heq
  · exact hb X Y p q γ h hlt
  · exact h.exists_printedLiftConclusion_of_eq heq

/-- Lawfulness below a pair is the printed respect of the rows restricted below it, for rows and
labellings with values at a stage that is zero or a limit. -/
theorem printedRespects_below_iff (hθ : Order.IsSuccPrelimit θ)
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hR : ∀ s t, AtStage θ (R.row s t))
    {r : D.below X → Label.{u}} (hr : ∀ d, AtStage θ (r d)) :
    (R.comap (IsLowerEmbedding.subtypeVal_below D X)).PrintedRespects θ r ↔
      R.IsLawfulBelow X r :=
  printedRespects_iff _ hθ (gradedIndex_mem_gradedFaces_below hD X) (fun _ _ ↦ hR _ _) hr

/-- **Bountiful rows are bountiful as printed** [Kni26, Definition 2.5.14], at every stage `θ`
that is zero or a limit and carries the values of the rows: the lift given by `IsBountiful`,
reduced to stage `θ`, satisfies the printed conclusion. -/
theorem IsBountiful.printedBountiful (hθ : Order.IsSuccPrelimit θ)
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hR : ∀ s t, AtStage θ (R.row s t))
    (hb : R.IsBountiful) : R.PrintedBountiful θ := by
  intro X Y p q γ h
  obtain ⟨q', hl, hc, hr⟩ := ((isBountiful_iff_forall_exists R).mp hb) h.mem_left h.mem_right h.le γ
    h.visibility.symm p q ((printedRespects_below_iff hθ hD hR h.left_atStage).mp h.left_respects)
    ((printedRespects_below_iff hθ hD hR h.right_atStage).mp h.right_respects) h.cap_eq
  have hγ : Label.reduce θ γ = γ := h.cap_atStage.reduce_eq
  refine ⟨Label.reduce θ ∘ q', fun d ↦ atStage_reduce θ _,
    (printedRespects_below_iff hθ hD hR fun d ↦ atStage_reduce θ _).mpr (hl.reduce hθ),
    fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [Function.comp_apply, ← hγ, ← (monotone_reduce θ).map_min, hc d,
      (monotone_reduce θ).map_min, hγ, (h.right_atStage d).reduce_eq]
  · rw [Function.comp_apply, hr d, (h.left_atStage d).reduce_eq]

/-- **Bountiful rows are bountiful as printed in [Kni26, Definition 2.5.14]**, on the printed
labels `{-∞} ∪ ω₁ ∪ {∞}`, when the rows take values among them. -/
theorem IsBountiful.printedBountiful_omega_one (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces)
    (hR : ∀ s t, AtStage (Ordinal.omega 1) (R.row s t)) (hb : R.IsBountiful) :
    R.PrintedBountiful (Ordinal.omega 1) :=
  hb.printedBountiful (Cardinal.isSuccLimit_omega 1).isSuccPrelimit hD hR

/-- **Bountifulness is the printed definition at every stage** [Kni26, Definition 2.5.14]: for a
scheme with finitely many cells, all with graded index in the graded plan, the rows are bountiful
exactly when they are bountiful as printed at every stage that is zero or a limit and carries the
values of the rows. -/
theorem isBountiful_iff_forall_printedBountiful [Finite ι]
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) :
    R.IsBountiful ↔ ∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ →
      (∀ s t, AtStage θ (R.row s t)) → R.PrintedBountiful θ := by
  refine ⟨fun hb θ hθ hR ↦ hb.printedBountiful hθ hD hR, fun h ↦ ?_⟩
  rw [isBountiful_iff_forall_exists]
  intro X Y hX hY hXY c hc p q hp hq hpq
  have hS : (Set.range p ∪ Set.range q ∪ {c} ∪ ⋃ s, Set.range (R.row s)).Finite :=
    (((Set.finite_range p).union (Set.finite_range q)).union (Set.finite_singleton c)).union
      (Set.finite_iUnion fun _ ↦ Set.finite_range _)
  obtain ⟨θ, hθ, hall⟩ := exists_isSuccPrelimit_forall_atStage hS
  have hR (s : ι) (t : D.below (D.gradedIndex s)) : AtStage θ (R.row s t) :=
    hall _ (Or.inr (Set.mem_iUnion.mpr ⟨s, t, rfl⟩))
  have hpθ (d : D.below X) : AtStage θ (p d) := hall _ (Or.inl (Or.inl (Or.inl ⟨d, rfl⟩)))
  have hqθ (d : D.below Y) : AtStage θ (q d) := hall _ (Or.inl (Or.inl (Or.inr ⟨d, rfl⟩)))
  obtain ⟨q', hq'⟩ := h θ hθ hR X Y p q c
    ⟨hX, hY, hXY, hpθ, hqθ, hall _ (Or.inl (Or.inr rfl)),
      (printedRespects_below_iff hθ hD hR hpθ).mpr hp,
      (printedRespects_below_iff hθ hD hR hqθ).mpr hq, hc.symm, hpq⟩
  exact ⟨q', (printedRespects_below_iff hθ hD hR hq'.atStage).mp hq'.respects, hq'.cap_eq,
    hq'.restrict_eq⟩

end Rows

end CellScheme

end VaughtConjecture
