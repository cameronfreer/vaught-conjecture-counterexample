/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Current.LocalLabelling

/-!
# Correspondence with the legal templates of [AFK26]: the balls `B_γ(q)` and bountiful rows

Roadmap, "Manuscript concordance", row 44.  [AFK26, Definition 4.26] (second part) sets, for
`γ ∈ ω₁` and a lawful local labelling `q` at `U`,
`B_γ(q) = {r : r is lawful and min (r, γ) = min (q, γ)}`, and calls the rows of `Σ` *bountiful*
if for every graded face `U`, lawful local labelling `q` with domain `D↓U`, `γ ∈ ω₁` self-visible
at `g(U)`, and graded face `V ≤ U`, `{r↾D↓V : r ∈ B_γ(q)} = B_γ(q↾D↓V)`.  The clauses are compared
with `CellScheme.Rows.IsBountiful`, in its form `CellScheme.Rows.isBountiful_iff_image_eq`
(restriction maps the cap ball `R.capBall U c q` onto the cap ball of the restriction).

The setting is that of `VaughtConjecture.Correspondence.Current.LocalLabelling` (row 43).  As in
row 6, the printed labels are those at stage `ω₁`; the definition is stated at a stage `θ`
(`CellScheme.Rows.printedBall`, `CellScheme.Rows.PrintedBountifulRows`), the hypotheses being the
fields of one structure:

| Printed clause | Field of `PrintedBallHypotheses` | `IsBountiful` (image form) |
| --- | --- | --- |
| `U` a graded face | `mem_left` | `Y ∈ D.gradedFaces` |
| `q` a local labelling, `dom(q) = D↓U` | `atStage` | `q : D.below Y → Label` |
| `q` lawful | `lawful` | `R.IsLawfulBelow Y q` |
| `γ ∈ ω₁` | `lt` (an ordinal `γ < θ`) | `c : Label` |
| `γ` self-visible at `g(U)` | `isSelfVisible` | `IsSelfVisible Y.2 c` |
| `V` a graded face, `V ≤ U` | `mem_right`, `le` | `X ∈ D.gradedFaces`, `X ≤ Y` |
| `B_γ(q)`: `r` lawful, `min (r, γ) = min (q, γ)` | `printedBall` | `R.capBall Y c q` |
| `{r↾D↓V : r ∈ B_γ(q)} = B_γ(q↾D↓V)` | `PrintedBountifulRows` | the image equation |

**Identification, and what is not identified** (status S).  For a scheme with finitely many cells,
all with graded index in the graded plan, the rows are bountiful exactly when they are bountiful
as printed at every stage that is zero or a limit and carries their values, **and** every labelling
lawful below a graded face `X` extends to one lawful below every graded face `Y ≥ X`
(`CellScheme.Rows.isBountiful_iff_forall_printedBountifulRows`).  Bountiful rows are bountiful as
printed at each such stage (`CellScheme.Rows.IsBountiful.printedBountifulRows`), in particular at
`ω₁` (`CellScheme.Rows.IsBountiful.printedBountifulRows_omega_one`).  No theorem here gives the
converse at a single stage, or without the extension of lawful labellings (departures 3 and 4).

**Departures.**
1. *Graded faces of grade `0`* ([AFK26, Definition 4.2] allows `j = 0`): harmless.  No cell lies
   below a pair of grade `0` when all cells have positive grade, and the printed equation then
   holds for every lawful `q`; the definition is the same with `U` and `V` among the graded faces
   of positive grade (`CellScheme.Rows.printedBountifulRows_iff_gradedFaces`).
2. *The cap `∞`*: the printed `γ` is an ordinal, `IsBountiful` also takes the cap `⊤`.  Harmless:
   at the cap `⊤` the cap balls are singletons and the equation always holds (in the proof of
   `CellScheme.Rows.isBountiful_iff_forall_printedBountifulRows`).
3. *The cap `-∞`* (not proved harmless).  `IsBountiful` also takes the cap `⊥`, at which the cap
   ball is the set of all lawful labellings: every labelling lawful below `X` extends to one
   lawful below `Y`.  The printed definition does not state it, and no theorem here derives it
   from the printed definition; it is the second conjunct of
   `CellScheme.Rows.isBountiful_iff_forall_printedBountifulRows`.  [Kni26, Definition 2.5.14]
   includes it (clause 4, `γ ∈ {-∞} ∪ θ ∪ {∞}`).
4. *The range of the labels* (not proved harmless at a single stage): as in row 6, the printed
   definition at the single stage `ω₁` is implied by `IsBountiful`, and the converse would need the
   transfer of the printed definition from `ω₁` up to larger limit stages.

**The two printed definitions.**  [Kni26, Definition 2.5.14] (`CellScheme.Rows.PrintedBountiful`,
row 6) is an extension form over pairs `⟨C, i⟩ ⪯ ⟨B, j⟩` with caps in `{-∞} ∪ θ ∪ {∞}`; the printed
definition of [AFK26] is an image form with ordinal caps.  Required at every stage that is zero or
a limit and carries the rows, the definition of [Kni26] is that of [AFK26] together with the
extension of lawful labellings (the cap `-∞`)
(`CellScheme.Rows.forall_printedBountiful_iff_forall_printedBountifulRows`).

## Placement

The concordance and its notes are in `roadmap/IMPLEMENTATION.md`, "Manuscript concordance".
-/

universe u

namespace VaughtConjecture

open Label

namespace CellScheme.Rows

variable {ι α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) {θ : Ordinal.{u}}

/-- **The ball `B_γ(q)`** of [AFK26, Definition 4.26], at stage `θ`: the lawful local labellings
`r` at `U`, with values at stage `θ`, such that `min (r, γ) = min (q, γ)`. -/
def printedBall (θ : Ordinal.{u}) (U : Finset α × ℕ) (γ : Ordinal.{u})
    (q : D.below U → Label.{u}) : Set (D.below U → Label.{u}) :=
  {r | (∀ d, AtStage θ (r d)) ∧ R.PrintedLawfulLocal θ U r ∧ ∀ d, min (r d) γ = min (q d) γ}

/-- **The hypotheses of the bountiful equation** of [AFK26, Definition 4.26], at stage `θ`: a
graded face `U`, a lawful local labelling `q` at `U`, an ordinal `γ < θ` self-visible at the grade
of `U`, and a graded face `V ≤ U`. -/
structure PrintedBallHypotheses (θ : Ordinal.{u}) (U V : Finset α × ℕ)
    (q : D.below U → Label.{u}) (γ : Ordinal.{u}) : Prop where
  /-- [AFK26, Definition 4.26]: `U` is a graded face. -/
  mem_left : U ∈ D.printedGradedFaces
  /-- [AFK26, Definition 4.26]: `q` is a local labelling with domain `D↓U`, with values at stage
  `θ`. -/
  atStage : ∀ d, AtStage θ (q d)
  /-- [AFK26, Definition 4.26]: `q` is lawful. -/
  lawful : R.PrintedLawfulLocal θ U q
  /-- [AFK26, Definition 4.26]: `γ ∈ θ` (printed `γ ∈ ω₁`). -/
  lt : γ < θ
  /-- [AFK26, Definition 4.26]: `γ` is self-visible at `g(U)`. -/
  isSelfVisible : IsSelfVisible U.2 γ
  /-- [AFK26, Definition 4.26]: `V` is a graded face. -/
  mem_right : V ∈ D.printedGradedFaces
  /-- [AFK26, Definition 4.26]: `V ≤ U`. -/
  le : V ≤ U

/-- **Bountiful rows** [AFK26, Definition 4.26], at stage `θ`: under the hypotheses,
`{r↾D↓V : r ∈ B_γ(q)} = B_γ(q↾D↓V)`. -/
def PrintedBountifulRows (θ : Ordinal.{u}) : Prop :=
  ∀ (U V : Finset α × ℕ) (q : D.below U → Label.{u}) (γ : Ordinal.{u})
    (h : R.PrintedBallHypotheses θ U V q γ),
    (fun r ↦ r ∘ Set.inclusion (D.below_mono h.le)) '' R.printedBall θ U γ q =
      R.printedBall θ V γ (q ∘ Set.inclusion (D.below_mono h.le))

variable {R}

/-- Restriction maps each ball `B_γ(q)` into the ball of the restriction, at a stage that is zero
or a limit carrying the rows. -/
theorem mapsTo_printedBall (hθ : Order.IsSuccPrelimit θ) (hR : ∀ s t, AtStage θ (R.row s t))
    {U V : Finset α × ℕ} (hVU : V ≤ U) (γ : Ordinal.{u}) (q : D.below U → Label.{u}) :
    Set.MapsTo (fun r ↦ r ∘ Set.inclusion (D.below_mono hVU)) (R.printedBall θ U γ q)
      (R.printedBall θ V γ (q ∘ Set.inclusion (D.below_mono hVU))) :=
  fun _ ⟨hθr, hl, hc⟩ ↦ ⟨fun _ ↦ hθr _, hl.restrict hθ hR hθr hVU, fun _ ↦ hc _⟩

/-- **Graded faces of grade `0`** [AFK26, Definition 4.2]: when every cell has its graded index in
the graded plan, the rows are bountiful as printed exactly when the bountiful equation holds for
the graded faces `U` and `V` of positive grade. -/
theorem printedBountifulRows_iff_gradedFaces (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) :
    R.PrintedBountifulRows θ ↔
      ∀ (U V : Finset α × ℕ) (q : D.below U → Label.{u}) (γ : Ordinal.{u})
        (h : R.PrintedBallHypotheses θ U V q γ), U ∈ D.gradedFaces → V ∈ D.gradedFaces →
        (fun r ↦ r ∘ Set.inclusion (D.below_mono h.le)) '' R.printedBall θ U γ q =
          R.printedBall θ V γ (q ∘ Set.inclusion (D.below_mono h.le)) := by
  refine ⟨fun hb U V q γ h _ _ ↦ hb U V q γ h, fun hb U V q γ h ↦ ?_⟩
  by_cases hV : V ∈ D.gradedFaces
  · refine hb U V q γ h ?_ hV
    rcases mem_printedGradedFaces_iff.mp h.mem_left with hU | ⟨-, hU⟩
    · exact hU
    · exact absurd (hU ▸ h.le.2) (not_le.mpr hV.2.1)
  · have hV0 : V.2 = 0 := by
      rcases mem_printedGradedFaces_iff.mp h.mem_right with hV' | ⟨-, hV'⟩
      · exact absurd hV' hV
      · exact hV'
    have : IsEmpty (D.below V) := ⟨fun d ↦ by
      have h₁ : D.grade d ≤ V.2 := d.2.2
      have h₂ := (hD d).2.1
      simp only [gradedIndex_snd] at h₂
      omega⟩
    ext r'
    refine ⟨fun _ ↦ ⟨fun d ↦ isEmptyElim d, ⟨fun d ↦ isEmptyElim d, fun d ↦ isEmptyElim d,
      fun d ↦ isEmptyElim d⟩, fun d ↦ isEmptyElim d⟩, fun _ ↦ ⟨q, ⟨h.atStage, h.lawful,
      fun _ ↦ rfl⟩, funext fun d ↦ isEmptyElim d⟩⟩

/-- **Bountiful rows are bountiful as printed** [AFK26, Definition 4.26], at every stage `θ` that
is zero or a limit and carries the values of the rows: the lift given by `IsBountiful`, reduced to
stage `θ`, lies in the ball and restricts to the given labelling. -/
theorem IsBountiful.printedBountifulRows (hθ : Order.IsSuccPrelimit θ)
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) (hR : ∀ s t, AtStage θ (R.row s t))
    (hb : R.IsBountiful) : R.PrintedBountifulRows θ := by
  refine (printedBountifulRows_iff_gradedFaces hD).mpr fun U V q γ h hU hV ↦ ?_
  refine Set.Subset.antisymm (Set.image_subset_iff.mpr (mapsTo_printedBall hθ hR h.le γ q)) ?_
  rintro r' ⟨hθr', hl', hc'⟩
  have hq := (printedLawfulLocal_iff hθ hR h.atStage).mp h.lawful
  have hp := (printedLawfulLocal_iff hθ hR hθr').mp hl'
  obtain ⟨q', hl, hc, hr⟩ := (isBountiful_iff_forall_exists R).mp hb hV hU h.le γ
    h.isSelfVisible r' q hp hq fun d ↦ (hc' d).symm
  have hγ : Label.reduce θ (γ : Label.{u}) = γ := (atStage_coe.mpr h.lt).reduce_eq
  refine ⟨Label.reduce θ ∘ q', ⟨fun d ↦ atStage_reduce θ _,
    (printedLawfulLocal_iff hθ hR fun d ↦ atStage_reduce θ _).mpr (hl.reduce hθ), fun d ↦ ?_⟩,
    funext fun d ↦ ?_⟩
  · rw [Function.comp_apply, ← hγ, ← (monotone_reduce θ).map_min, hc d,
      (monotone_reduce θ).map_min, hγ, (h.atStage d).reduce_eq]
  · simp only [Function.comp_apply]
    rw [hr d, (hθr' d).reduce_eq]

/-- **Bountiful rows are bountiful as printed in [AFK26, Definition 4.26]**, on the printed labels
`{-∞} ∪ ω₁ ∪ {∞}`, when the rows take values among them. -/
theorem IsBountiful.printedBountifulRows_omega_one (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces)
    (hR : ∀ s t, AtStage (Ordinal.omega 1) (R.row s t)) (hb : R.IsBountiful) :
    R.PrintedBountifulRows (Ordinal.omega 1) :=
  hb.printedBountifulRows (Cardinal.isSuccLimit_omega 1).isSuccPrelimit hD hR

/-- **Bountifulness from the printed definition and the extension of lawful labellings**: for a
scheme with finitely many cells, if the rows are bountiful as printed at every stage `θ ≥ b` that
is zero or a limit and carries their values, and every labelling lawful below a graded face
extends to one lawful below every larger graded face, the rows are bountiful. -/
theorem isBountiful_of_forall_printedBountifulRows [Finite ι] (b : Ordinal.{u})
    (h : ∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → b ≤ θ → (∀ s t, AtStage θ (R.row s t)) →
      R.PrintedBountifulRows θ)
    (hbot : ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces → ∀ hXY : X ≤ Y,
      Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono hXY)) {q | R.IsLawfulBelow Y q}
        {p | R.IsLawfulBelow X p}) :
    R.IsBountiful := by
  rw [isBountiful_iff_forall_exists]
  intro X Y hX hY hXY c hc p q hp hq hpq
  induction c using recBotCoeTop with
  | bot =>
    obtain ⟨q', hq', hr⟩ := hbot hX hY hXY hp
    exact ⟨q', hq', fun d ↦ by simp, fun d ↦ congrFun hr d⟩
  | top =>
    exact ⟨q, hq, fun _ ↦ rfl, fun d ↦ by simpa using hpq d⟩
  | coe o =>
    have hS : (Set.range p ∪ Set.range q ∪ {(o : Label.{u}), (b : Label.{u})} ∪
        ⋃ s, Set.range (R.row s)).Finite :=
      (((Set.finite_range p).union (Set.finite_range q)).union (Set.toFinite _)).union
        (Set.finite_iUnion fun _ ↦ Set.finite_range _)
    obtain ⟨θ, hθ, hall⟩ := exists_isSuccPrelimit_forall_atStage hS
    have hR (s : ι) (t : D.below (D.gradedIndex s)) : AtStage θ (R.row s t) :=
      hall _ (Or.inr (Set.mem_iUnion.mpr ⟨s, t, rfl⟩))
    have hpθ (d : D.below X) : AtStage θ (p d) := hall _ (Or.inl (Or.inl (Or.inl ⟨d, rfl⟩)))
    have hqθ (d : D.below Y) : AtStage θ (q d) := hall _ (Or.inl (Or.inl (Or.inr ⟨d, rfl⟩)))
    have hoθ : o < θ := atStage_coe.mp (hall _ (Or.inl (Or.inr (Or.inl rfl))))
    have hbθ : b < θ := atStage_coe.mp (hall _ (Or.inl (Or.inr (Or.inr rfl))))
    have heq := h θ hθ hbθ.le hR Y X q o ⟨gradedFaces_subset_printedGradedFaces hY, hqθ,
      (printedLawfulLocal_iff hθ hR hqθ).mpr hq, hoθ, hc, gradedFaces_subset_printedGradedFaces hX,
      hXY⟩
    have hpb : p ∈ R.printedBall θ X o (q ∘ Set.inclusion (D.below_mono hXY)) :=
      ⟨hpθ, (printedLawfulLocal_iff hθ hR hpθ).mpr hp, fun d ↦ (hpq d).symm⟩
    rw [← heq] at hpb
    obtain ⟨r, ⟨hrθ, hrl, hrc⟩, hr⟩ := hpb
    exact ⟨r, (printedLawfulLocal_iff hθ hR hrθ).mp hrl, hrc, fun d ↦ congrFun hr d⟩

/-- **Bountifulness is the printed definition at every stage with the extension of lawful
labellings** [AFK26, Definition 4.26]: for a scheme with finitely many cells, all with graded index
in the graded plan, the rows are bountiful exactly when they are bountiful as printed at every
stage that is zero or a limit and carries their values, and every labelling lawful below a graded
face `X` extends to one lawful below every graded face `Y ≥ X` (the cap `-∞`). -/
theorem isBountiful_iff_forall_printedBountifulRows [Finite ι]
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) :
    R.IsBountiful ↔
      (∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → (∀ s t, AtStage θ (R.row s t)) →
        R.PrintedBountifulRows θ) ∧
      ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces → ∀ hXY : X ≤ Y,
        Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono hXY)) {q | R.IsLawfulBelow Y q}
          {p | R.IsLawfulBelow X p} :=
  ⟨fun hb ↦ ⟨fun _ hθ hR ↦ hb.printedBountifulRows hθ hD hR,
    fun _ _ hX hY hXY ↦ IsBountiful.surjOn_isLawfulBelow R hb hX hY hXY⟩,
    fun ⟨h, hbot⟩ ↦ isBountiful_of_forall_printedBountifulRows 0
      (fun θ hθ _ hR ↦ h θ hθ hR) hbot⟩

/-- **The two printed definitions of bountiful rows**: for a scheme with finitely many cells, all
with graded index in the graded plan, the rows are bountiful in the sense of
[Kni26, Definition 2.5.14] at every stage that is zero or a limit and carries their values exactly
when they are bountiful in the sense of [AFK26, Definition 4.26] at every such stage and every
labelling lawful below a graded face extends to one lawful below every larger graded face. -/
theorem forall_printedBountiful_iff_forall_printedBountifulRows [Finite ι]
    (hD : ∀ d, D.gradedIndex d ∈ D.gradedFaces) :
    (∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → (∀ s t, AtStage θ (R.row s t)) →
        R.PrintedBountiful θ) ↔
      (∀ θ : Ordinal.{u}, Order.IsSuccPrelimit θ → (∀ s t, AtStage θ (R.row s t)) →
        R.PrintedBountifulRows θ) ∧
      ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces → ∀ hXY : X ≤ Y,
        Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono hXY)) {q | R.IsLawfulBelow Y q}
          {p | R.IsLawfulBelow X p} :=
  (isBountiful_iff_forall_printedBountiful hD).symm.trans
    (isBountiful_iff_forall_printedBountifulRows hD)

end CellScheme.Rows

end VaughtConjecture
