/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ThinScheme

/-!
# A thin completion outside the tower route

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the recursion on the grade; here a completion below
the full grade of the asymmetric seed `seedL`, for which the tower of the step fails); semantic
contract, items 2–4.

**The theorem** (`nonempty_completionBelowFullGrade_seedL`): the asymmetric seed `seedL` of
`VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample` has a completion below the full grade.
It is a completion *outside the tower route*: the tower of the step is refuted for `seedL`
(`not_twoFaceLiftExists_two_seedL`, `not_towerInvariant_top_seedL`), and this completion is not
built as a tower.  It is the **thin completion** (`thinCompletion`): the amalgam with one new cell
at each graded face `(univ, k)` of full scope, `k = 1, 2, 3, 4`, whose rows are the ordered rows of
`VaughtConjecture.Extension.OrderedRow` (the scheme is `thinScheme`,
`VaughtConjecture.Extension.ThinScheme`), with the label `⊤` at the cells of grade `4` (the two
apexes and the new cell at `(univ, 4)`) and `⊥` elsewhere.  It is proved for every seed whose coatom
types are `TL` and `T5` (`nonempty_completionBelowFullGrade_of`) and specialized to `seedL` by
`rfl`.

**Legality below the full grade** (`isLegalBelowFullGrade_thinScheme`).

* Well formed and coded: each new cell has a graded face as its graded index, and every value of
  the row of a new cell is `⊥` or a grid point below `ω²`.
* Consistent (`isConsistent_thinScheme`): the old rows are those of the amalgam; the row of the new
  cell at `(univ, k)` is the thin labelling of the parameters `isThinLawfulBelow_row_one`,
  `isThinLawfulBelow_row_two`, `isThinLawfulBelow_row_three` for `k ≤ 3`, and the labelling of
  `Ω = ω + 4` alone for `k = 4`.
* Complete below the full grade: one new cell at each `(univ, k)`, `k < 5`.
* Bountiful (`isBountiful_thinScheme`): it is enough to lift between pairs of the same grade
  (`Rows.isBountiful_iff_forall_cappedLift_fst`).  Below a coatom the lifts are those of the
  amalgam (`cappedLift_old`).  A lift from `(B, k)` into `(univ, k)` goes first, within the amalgam,
  to the coatom containing `B`, and then to the full scope: at the grades `k ≤ 3` by the lift of
  parameters (`exists_lift_left`, `exists_lift_right`, from `exists_thinLift`) with the
  prescription and the ambient extended by `⊥` above the grade `k` (`cappedLift_of_exists_lift`);
  at the grade `4` from the lift at the grade `3` (`cappedLift_four`): if the prescription is `⊥`
  at its apex, lift its restriction below the grade `3` and extend by `⊥`; otherwise it is `⊥`
  below its apex, and the lift is the labelling of its apex label alone.

**The grade `4`.**  The row of the new cell at `(univ, 4)` reads only the cells of grade `4`, so a
lawful labelling is constant on them (`eq_newCell_four`) and, if not `⊥` there, is `⊥` below the
grade `4` (`eq_bot_of_newCell_four`); the labelling of a label `Ω` self-visible at `4` alone is
lawful (`isLawfulBelow_omega`), through the rows of the apexes of `TL` and `T5`, `⊥` below the
grade `4` (`amalgam_row_apex`).  The labels of the amalgam are `⊤` at the apexes and `⊥` elsewhere
(`amalgam_label`), and the amalgam has one cell at each graded index
(`amalgam_gradedIndex_injective`).

**What the thin completion imposes.**  Its lawful labellings below `(univ, 3)` impose `A_C ≤ A_D`
and `F_C = F_D` and exclude collisions: they are not all the labellings of the amalgam lawful
below both coatoms (`ThinCompletionExamples.exists_not_restriction`).  The orientation `C` before
`D` of its ordered rows is forced at `(univ, 1)`, `(univ, 2)` and `(univ, 3)`: every completion of
a seed whose coatom types are `TL` and `T5` has, at each `(univ, k)`, `1 ≤ k ≤ 3`, a cell whose row
reads `({3}, 1)` strictly below `({4}, 1)` (`exists_separating_cell_of_completion_of_le_three`; at
`(univ, 2)`, `exists_separating_cell_of_completion`), and the thin completion has only one cell
there.  At `(univ, 4)` no separating cell is forced: the only cell of the thin completion there
(`eq_newCell`) reads `({3}, 1)` and `({4}, 1)` both at `⊥` (`row_newCell_four_eq_bot_iff`).

**Consequences.**  The identified obstruction of the tower (step 3 of
`not_twoFaceLiftExists_two_of`: a new cell at `(univ, 2)` where the catalogue entry reaches the cap
reads `({3}, 1)` and `({4}, 1)` at one value) does not apply to the thin completion: its only cell
at `(univ, 2)` separates (`ThinCompletionExamples.row_newCell_two_lt`).
`StageType.HasApexCoatomExtensions` is not refuted by `seedL`: `seedL` has the coatom extension
property with apex at `m = 3` (`ThinCompletionExamples.exists_coatomExtension_seedL`, at every stage
since the labels `⊥` and `⊤` lie at every stage; at the stages that are zero or a limit, this is
also `CompletionBelowFullGrade.exists_coatomExtension` applied to the thin completion).  In general
it is compiled by another construction (`StageType.hasApexCoatomExtensions`).

**Special cases.**  The thin pattern also completes the seeds of `T4` and of `T5` with themselves,
which the tower already completes
(`TwoFaceLiftCounterexample.nonempty_completionBelowFullGrade_seed4`,
`CaseSplitCounterexample.nonempty_completionBelowFullGrade_seed5`): both have the ordered-layer step
of `VaughtConjecture.Extension.OrderedLayerStep` (`Seed.orderedLayerStep_of_T4`,
`Seed.orderedLayerStep_of_T5`, module `VaughtConjecture.Extension.OrderedLayerExamples`):

* `seed4` (`T4` with itself): there is no live cell of grade `3`, and the new cell at `(univ, 3)`
  reads `⊥` everywhere (`OrderedLayer.Seed4.layerRows4`);
* `seed5` (`T5` with itself): the row at `(univ, 3)` reads every live kind at `ω + 3`
  (`OrderedLayer.Seed5.rows5`).  The row at `(univ, 3)` of this module, which reads `A_C` at `1`,
  is not consistent there (argued, not formalized): `T5` on `C` couples `G ≤ A_C`, and that row as
  a labelling has `A_C = 1 < ω + 3 = G`.  The lift keeps `G ≤ A_C`.

**The ordered-layer step.**  The thin completion is the instance for `seedL` of the ordered-layer
step (`Seed.orderedLayerStep_thinRows`): one new cell at each graded face of full scope, with rows
read off graded indices, stated for an arbitrary seed on five points as a named hypothesis
(`Seed.OrderedLayerStep`) from which the completion follows (`Seed.OrderedLayerStep.completion`).
For the seeds with bottom apexes its top grade is automatic
(`Seed.OrderedLayerStepBelowTop.orderedLayerStep`, `VaughtConjecture.Extension.OrderedLayerTop`).
Every ordered-layer step of `seedL` reads `({3}, 1)` strictly below `({4}, 1)` at the grades `1`,
`2`, `3` (`Seed.OrderedLayerStep.thinRow_lt_of_TL_T5`), and a seed with two opposite forced
separations at one grade has no ordered-layer step (`Seed.not_hasOrderedLayerStep_of_forcesTop`,
`VaughtConjecture.Extension.OrderedLayerObstruction`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion has the shape of [Kni26, Definition 4.3.14] (the old cells kept, the new cells of
full scope), with one new cell per graded face of full scope; its rows are not those of that
definition, and neither printed proof of [Kni26, Lemma 4.3.16] or [Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture.ThinCompletion

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftExistsCounterexample

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

variable (hIL : I.left = TL α) (hIR : I.right = CaseSplitCounterexample.T5 α)

/-! ### The labels and the apex rows of the amalgam -/

include hIL hIR in
/-- **The labels of the amalgam**: `⊤` at the two apexes, the cells of grade `4`, and `⊥`
elsewhere. -/
theorem amalgam_label (d : Fin I.amalgam.card) :
    I.amalgam.label d = if I.amalgam.toCellScheme.grade d = 4 then ⊤ else ⊥ := by
  have hP := fun (t₀ : StageType.{u} α 4) (ht : t₀.IsLegalBelowFullGrade)
    (hbot : ∀ d, t₀.label d = ⊥) (i : Fin (t₀.addApex ht (by omega)).card) ↦
    StageType.label_addApex ht (by omega) hbot i
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
    (I.scope_ne_univ d) with h | h
  · exact StageType.label_of_restrictFace (hIL ▸ I.restrictFace_left)
      (fun a l ↦ l = if a = 4 then ⊤ else ⊥) (hP _ isLegalBelowFullGrade_SL fun _ ↦ rfl)
      ((coe_subset.mpr (Coatom.univ_map_left ▸ h)).trans (coe_map_subset_range _ _))
  · exact StageType.label_of_restrictFace (hIR ▸ I.restrictFace_right)
      (fun a l ↦ l = if a = 4 then ⊤ else ⊥)
      (hP _ CaseSplitCounterexample.isLegalBelowFullGrade_S fun _ ↦ rfl)
      ((coe_subset.mpr (Coatom.univ_map_right ▸ h)).trans (coe_map_subset_range _ _))

include hIL hIR in
/-- **The rows of the apexes of the amalgam**: the row of a cell of grade `4` is `⊥` exactly at
the cells of grade below `4`. -/
theorem amalgam_row_apex {s : Fin I.amalgam.card} (hs : I.amalgam.toCellScheme.grade s = 4)
    (i : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    I.amalgam.rows.row s i = ⊥ ↔ I.amalgam.toCellScheme.grade i ≠ 4 := by
  have hP := fun (t₀ : StageType.{u} α 4) (ht : t₀.IsLegalBelowFullGrade)
    (hbot : ∀ d, t₀.label d = ⊥) (s : Fin (t₀.addApex ht (by omega)).card)
    (i : (t₀.addApex ht (by omega)).toCellScheme.below
      ((t₀.addApex ht (by omega)).toCellScheme.gradedIndex s))
    (hs : (t₀.addApex ht (by omega)).toCellScheme.grade s = 4) ↦
    StageType.row_addApex ht (by omega) hbot s hs i
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem s)
    (I.scope_ne_univ s) with h | h
  · exact StageType.row_of_restrictFace (hIL ▸ I.restrictFace_left)
      (fun a b r ↦ a = 4 → (r = ⊥ ↔ b ≠ 4))
      (fun s i hs ↦ hP _ isLegalBelowFullGrade_SL (fun _ ↦ rfl) s i hs)
      ((coe_subset.mpr (Coatom.univ_map_left ▸ h)).trans (coe_map_subset_range _ _)) i hs
  · exact StageType.row_of_restrictFace (hIR ▸ I.restrictFace_right)
      (fun a b r ↦ a = 4 → (r = ⊥ ↔ b ≠ 4))
      (fun s i hs ↦ hP _ CaseSplitCounterexample.isLegalBelowFullGrade_S (fun _ ↦ rfl) s i hs)
      ((coe_subset.mpr (Coatom.univ_map_right ▸ h)).trans (coe_map_subset_range _ _)) i hs

/-! ### The grade `4` -/

/-- The rows of the old cells are those of the amalgam. -/
theorem row_oldCell (s d : Fin I.amalgam.card)
    (h : oldCell I d ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (oldCell I s)))
    (h' : d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    (thinScheme I).rows.row (oldCell I s) ⟨oldCell I d, h⟩ = I.amalgam.rows.row s ⟨d, h'⟩ :=
  congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row s ⟨d, h'⟩) (comap_rows_oldCell (I := I))

/-- A cell below an old cell is old. -/
theorem exists_oldCell_of_mem_below {s : Fin I.amalgam.card} {z : Fin (thinScheme I).card}
    (hz : z ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (oldCell I s))) :
    ∃ d, z = oldCell I d ∧ d ∈ I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)
    := by
  obtain ⟨d, rfl⟩ := (isLowerEmbedding_oldCell I).mem_range s z hz
  exact ⟨d, rfl, ((isLowerEmbedding_oldCell I).le_iff d s).mp hz⟩

/-- Every cell has grade at most `4`. -/
theorem grade_le_four (z : Fin (thinScheme I).card) : (thinScheme I).toCellScheme.grade z ≤ 4 := by
  rcases cell_cases z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [grade_oldCell]; exact Nat.lt_succ_iff.mp (I.grade_lt d)
  all_goals rw [grade_newCell (by omega) (by omega)]
  all_goals omega

/-- Every cell is below `(univ, 4)`. -/
theorem mem_below_univ_four (z : Fin (thinScheme I).card) :
    z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 4) :=
  ⟨subset_univ _, grade_le_four z⟩

/-- A graded index of grade `4` has the kind `Ω`. -/
theorem thinKind_of_snd_eq_four {X : Finset (Fin 5) × ℕ} (h : X.2 = 4) : thinKind X = 5 := by
  unfold thinKind; simp [h]

/-- The kind `Ω` is exactly the grade `4`. -/
theorem thinKind_eq_five_iff {X : Finset (Fin 5) × ℕ} : thinKind X = 5 ↔ X.2 = 4 :=
  ⟨fun h ↦ (snd_eq_kindGrade (by rw [h]; decide)).trans (by rw [h]; rfl),
    thinKind_of_snd_eq_four⟩

/-- The row at `(univ, 4)` is `⊥` exactly at the kinds other than `Ω`. -/
theorem thinRow_four_eq_bot_iff {c : Fin 6} : thinRow.{u} 4 c = ⊥ ↔ c ≠ 5 := by
  fin_cases c <;> simp [thinRow, kindLabel, gridPoint_ne_bot]

/-- The thin labelling of `Ω` alone: `Ω` at the cells of grade `4` and `⊥` elsewhere. -/
theorem thinLabelling_omega (Ω : Label.{u}) (z : Fin (thinScheme I).card) :
    thinLabelling I ⊥ ⊥ ⊥ ⊥ Ω z = if (thinScheme I).toCellScheme.grade z = 4 then Ω else ⊥ := by
  unfold thinLabelling thinLabel
  split_ifs with h
  · rw [thinKind_of_snd_eq_four h]; rfl
  · have : thinKind ((thinScheme I).toCellScheme.gradedIndex z) ≠ 5 :=
      fun h5 ↦ h (thinKind_eq_five_iff.mp h5)
    generalize thinKind ((thinScheme I).toCellScheme.gradedIndex z) = c at this
    fin_cases c <;> first | rfl | exact (this rfl).elim

/-- The row of the new cell at `(univ, 4)` is `⊥` exactly below the grade `4`. -/
theorem row_newCell_four_eq_bot_iff
    (d : (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I 4))) :
    (thinScheme I).rows.row (newCell I 4) d = ⊥ ↔ (thinScheme I).toCellScheme.grade d.1 ≠ 4 := by
  rw [row_newCell (by omega) le_rfl, thinRow_four_eq_bot_iff, Ne, thinKind_eq_five_iff]
  rfl

/-- **At the grade `4`, a lawful labelling is constant on the cells of grade `4`**: locality and
availability at the new cell at `(univ, 4)`, whose row reads the cells of grade `4` at one value. -/
theorem eq_newCell_four {w : Fin (thinScheme I).card → Label.{u}}
    (hw : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) fun z ↦ w z)
    {z : Fin (thinScheme I).card} (hz : (thinScheme I).toCellScheme.grade z = 4) :
    w z = w (newCell I 4) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hz' : z ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I 4)) := by
    rw [gradedIndex_newCell (by omega) le_rfl]; exact mem_below_univ_four z
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu, hle⟩ := ha z (newCell I 4) (mem_below_univ_four _)
      (by rw [scope_newCell (by omega) le_rfl]; exact subset_univ _)
      (by rw [hz, grade_newCell (by omega) le_rfl])
    rwa [eq_newCell (by omega) le_rfl (hu.trans (gradedIndex_newCell (by omega) le_rfl))] at hle
  · have hr : (thinScheme I).rows.row (newCell I 4) ⟨newCell I 4, newCell_mem_below_self⟩ ≤
        (thinScheme I).rows.row (newCell I 4) ⟨z, hz'⟩ := by
      rw [row_newCell (by omega) le_rfl, row_newCell (by omega) le_rfl]
      -- Read the graded indices of the two cells off the subtype.
      change thinRow 4 (thinKind ((thinScheme I).toCellScheme.gradedIndex (newCell I 4))) ≤
        thinRow 4 (thinKind ((thinScheme I).toCellScheme.gradedIndex z))
      rw [gradedIndex_newCell (by omega) le_rfl, thinKind_univ_four,
        thinKind_of_snd_eq_four hz]
    have := (hl _ (mem_below_univ_four (newCell I 4))).le_of_le hr
      (show (thinScheme I).toCellScheme.grade z ≤
          (thinScheme I).toCellScheme.grade (newCell I 4) by
        rw [hz, grade_newCell (by omega) le_rfl])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)

/-- **At the grade `4`, a lawful labelling that is not `⊥` at the new cell at `(univ, 4)` is `⊥`
below the grade `4`**: the row of that cell is `⊥` there. -/
theorem eq_bot_of_newCell_four {w : Fin (thinScheme I).card → Label.{u}}
    (hw : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) fun z ↦ w z)
    (hΩ : w (newCell I 4) ≠ ⊥) {z : Fin (thinScheme I).card}
    (hz : (thinScheme I).toCellScheme.grade z ≠ 4) : w z = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hz' : z ∈ (thinScheme I).toCellScheme.below
      ((thinScheme I).toCellScheme.gradedIndex (newCell I 4)) := by
    rw [gradedIndex_newCell (by omega) le_rfl]; exact mem_below_univ_four z
  have := (hl _ (mem_below_univ_four (newCell I 4))).eq_bot (d := ⟨z, hz'⟩)
    ((row_newCell_four_eq_bot_iff ⟨z, hz'⟩).mpr hz)
  exact (min_eq_bot.mp this).resolve_right hΩ

include hIL hIR in
/-- The row of a cell of grade `4` is `⊥` exactly below the grade `4`. -/
theorem row_eq_bot_iff_of_grade_four {s : Fin (thinScheme I).card}
    (hs : (thinScheme I).toCellScheme.grade s = 4)
    (d : (thinScheme I).toCellScheme.below ((thinScheme I).toCellScheme.gradedIndex s)) :
    (thinScheme I).rows.row s d = ⊥ ↔ (thinScheme I).toCellScheme.grade d.1 ≠ 4 := by
  by_cases hne : (thinScheme I).toCellScheme.scope s = univ
  · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
    obtain rfl : j = 4 := (grade_newCell hj1 hj4).symm.trans hs
    exact row_newCell_four_eq_bot_iff d
  · obtain ⟨a, rfl⟩ := exists_eq_oldCell hne
    rw [grade_oldCell] at hs
    obtain ⟨e, he, hea⟩ := exists_oldCell_of_mem_below d.2
    have hrow : (thinScheme I).rows.row (oldCell I a) d = I.amalgam.rows.row a ⟨e, hea⟩ := by
      rw [← row_oldCell a e (he ▸ d.2) hea]
      exact (thinScheme I).rows.row_congr rfl he
    rw [hrow, amalgam_row_apex hIL hIR hs, he, grade_oldCell]

include hIL hIR in
/-- **The labelling of `Ω` alone is lawful**, for `Ω` self-visible at `4`: at the new cell at
`(univ, 4)` and at the two apexes, whose rows are `⊥` exactly below the grade `4`, the top shifter
is a witness. -/
theorem isLawfulBelow_omega {Ω : Label.{u}} (hΩ : IsSelfVisible 4 Ω) :
    (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4)
      fun z ↦ thinLabelling I ⊥ ⊥ ⊥ ⊥ Ω z := by
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d _ ↦ ?_, fun s _ ↦ ?_, fun s t _ hst hg ↦ ?_⟩
  · rw [thinLabelling_omega]
    split_ifs with h
    · rw [h]; exact hΩ
    · exact isSelfVisible_bot _
  · by_cases hs : (thinScheme I).toCellScheme.grade s = 4
    · have hws : thinLabelling I ⊥ ⊥ ⊥ ⊥ Ω s = Ω := by rw [thinLabelling_omega, ite_eq_left hs]
      refine transformsTo_topShifter _
        (fun d : (thinScheme I).toCellScheme.below
          ((thinScheme I).toCellScheme.gradedIndex s) ↦ grade_le_four d.1) hΩ _ _ fun d ↦ ?_
      have key := row_eq_bot_iff_of_grade_four hIL hIR hs d
      rw [hws, thinLabelling_omega]
      by_cases hd4 : (thinScheme I).toCellScheme.grade d.1 = 4
      · rw [ite_eq_left hd4, min_self, ite_eq_right (fun h ↦ (key.mp h) hd4)]
      · rw [ite_eq_right hd4, min_bot_left, ite_eq_left (key.mpr hd4)]
    · have hws : thinLabelling I ⊥ ⊥ ⊥ ⊥ Ω s = ⊥ := by rw [thinLabelling_omega, ite_eq_right hs]
      rw [hws]
      simp only [min_bot_right]
      exact TransformsTo.bot _ _
  · refine ⟨t, rfl, ?_⟩
    rw [thinLabelling_omega, thinLabelling_omega, hg]

/-! ### The lifts from the coatoms at the grade `3` -/

/-- A property of `a` holds at every member of `some a`. -/
private theorem forall_mem_some {β : Type*} {a : β} {P : β → Prop} (h : P a) : ∀ b ∈ some a, P b :=
  fun _ hb ↦ (Option.some_inj.mp hb) ▸ h

/-- Every property holds at every member of `none`. -/
private theorem forall_mem_none {β : Type*} {P : β → Prop} : ∀ b ∈ (none : Option β), P b :=
  fun _ hb ↦ by cases hb

/-- Two thin labellings whose parameters agree capped at `c` agree capped at `c` (with `Ω = ⊥`). -/
theorem min_thinLabel_eq {c AC AD F G AC' AD' F' G' : Label.{u}}
    (hAC : min AC c = min AC' c) (hAD : min AD c = min AD' c) (hF : min F c = min F' c)
    (hG : min G c = min G' c) (X : Finset (Fin 5) × ℕ) :
    min (thinLabel AC AD F G ⊥ X) c = min (thinLabel AC' AD' F' G' ⊥ X) c := by
  unfold thinLabel
  generalize thinKind X = k
  fin_cases k
  exacts [rfl, hAC, hAD, hF, hG, rfl]

include hIL hIR in
/-- **The lift from `(C, 3)` to `(univ, 3)`**, for a cap `c` self-visible at `1`, and at `2` unless
the prescription is `⊥` at the grade `2`.  The parameters of the prescription (`TL`) and of the
ambient (`IsThinLawfulBelow`) are lifted by `exists_thinLift`, with `A_D` unprescribed. -/
theorem exists_lift_left {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {p q : Fin (thinScheme I).card → Label.{u}}
    (hp : (thinScheme I).rows.IsLawfulBelow (coatomC, 3) fun z ↦ p z)
    (hq : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (thinScheme I).toCellScheme.below (coatomC, 3), min (q z) c = min (p z) c)
    (hc2 : IsSelfVisible 2 c ∨ ∀ z ∈ (thinScheme I).toCellScheme.below (coatomC, 3),
      (thinScheme I).toCellScheme.grade z = 2 → p z = ⊥) :
    ∃ x : Fin (thinScheme I).card → Label.{u},
      (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (thinScheme I).toCellScheme.below (coatomC, 3), x z = p z := by
  -- Step 1: read the parameters `(A, F, G)` of the prescription (a labelling of `TL`) and the
  -- parameters of the ambient (`IsThinLawfulBelow`).
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGFp, hcp, hp'⟩ := exists_of_isLawfulBelow_left hIL hp
  obtain ⟨qAC, qAD, qF, qG, hq', hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
  -- Step 2: the cells `({3}, 1)`, `(C, 2)` and `(E, 3)`, one of each live kind on `C`.
  obtain ⟨d₁, hd₁⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sC, hsC⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := exists_oldCell_left hIL 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₁ : oldCell I d₁ ∈ (thinScheme I).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hd₁]; decide)
  have hs : oldCell I sC ∈ (thinScheme I).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hsC]; decide)
  have hg : oldCell I gE ∈ (thinScheme I).toCellScheme.below (coatomC, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (thinScheme I).toCellScheme.below (coatomC, 3)) :
      z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  -- Step 3: at those cells, the prescribed parameters agree with the ambient capped at `c`.
  have hAq : min Ap c = min qAC c := by
    have := hpq _ h₁
    rw [hp' _ h₁, hqz _ (hmem h₁), thinLabelling, gradedIndex_oldCell, hd₁] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), thinLabelling, gradedIndex_oldCell, hsC] at this
    exact this.symm
  have hGq : min Gp c = min qG c := by
    have := hpq _ hg
    rw [hp' _ hg, hqz _ (hmem hg), thinLabelling, gradedIndex_oldCell, hgE] at this
    exact this.symm
  -- Step 4: the parameter-level lift, with `A_D` unprescribed; its thin labelling is the lift.
  have hc2' : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    refine hc2.imp_right fun h ↦ ?_
    have := h _ hs (by rw [grade_oldCell]; exact congrArg Prod.snd hsC)
    rw [hp' _ hs, gradedIndex_oldCell, hsC] at this
    exact congrArg some this
  obtain ⟨xAC, xAD, xF, xG, hx, hxAC, hxAD, hxF, hxG, hpAC, -, hpF, hpG⟩ :=
    exists_thinLift hc1 (PAC := some Ap) (PAD := none) (PF := some Fp) (PG := some Gp) hc2'
      (.inr rfl) hq' (forall_mem_some hAp) forall_mem_none (forall_mem_some hFp)
      (forall_mem_some hGp) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some hGFp)) (forall_mem_some forall_mem_none)
      (forall_mem_some (forall_mem_some hcp)) (forall_mem_some forall_mem_none)
      (forall_mem_some hAq) forall_mem_none (forall_mem_some hFq) (forall_mem_some hGq)
  refine ⟨thinLabelling I xAC xAD xF xG ⊥, isLawfulBelow_thinLabel hIL hIR hx,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_thinLabel_eq hxAC hxAD hxF hxG _
  · rw [hp' z hz, thinLabelling, hpAC Ap rfl, hpF Fp rfl, hpG Gp rfl]
    exact thinLabel_congr_two (thinKind_ne_two (four_notMem_of_mem_below hz)) _ _ _ _ _ _

include hIL hIR in
/-- **The lift from `(D, 3)` to `(univ, 3)`**, for a cap `c` self-visible at `1`, and at `2` unless
the prescription is `⊥` at the grade `2`.  The parameters of the prescription (`T5`) and of the
ambient (`IsThinLawfulBelow`) are lifted by `exists_thinLift`, with `A_C` unprescribed. -/
theorem exists_lift_right {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {p q : Fin (thinScheme I).card → Label.{u}}
    (hp : (thinScheme I).rows.IsLawfulBelow (coatomD, 3) fun z ↦ p z)
    (hq : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hpq : ∀ z ∈ (thinScheme I).toCellScheme.below (coatomD, 3), min (q z) c = min (p z) c)
    (hc2 : IsSelfVisible 2 c ∨ ∀ z ∈ (thinScheme I).toCellScheme.below (coatomD, 3),
      (thinScheme I).toCellScheme.grade z = 2 → p z = ⊥) :
    ∃ x : Fin (thinScheme I).card → Label.{u},
      (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
      (∀ z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3),
        min (x z) c = min (q z) c) ∧
      ∀ z ∈ (thinScheme I).toCellScheme.below (coatomD, 3), x z = p z := by
  -- Step 1: read the parameters `(A, F, G)` of the prescription (a labelling of `T5`) and the
  -- parameters of the ambient (`IsThinLawfulBelow`).
  obtain ⟨Ap, Fp, Gp, hAp, hFp, hGp, hGAp, hGFp, hp'⟩ := exists_of_isLawfulBelow_right hIR hp
  obtain ⟨qAC, qAD, qF, qG, hq', hqz⟩ := exists_of_isLawfulBelow_three hIL hIR hq
  -- Step 2: the cells `({4}, 1)`, `(D, 2)` and `(E, 3)`, one of each live kind on `D`.
  obtain ⟨d₂, hd₂⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨sD, hsD⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := exists_oldCell_right hIR 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have h₂ : oldCell I d₂ ∈ (thinScheme I).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hd₂]; decide)
  have hs : oldCell I sD ∈ (thinScheme I).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hsD]; decide)
  have hg : oldCell I gE ∈ (thinScheme I).toCellScheme.below (coatomD, 3) :=
    oldCell_mem_below (by rw [hgE]; decide)
  have hmem {z} (hz : z ∈ (thinScheme I).toCellScheme.below (coatomD, 3)) :
      z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
    ⟨subset_univ _, hz.2⟩
  -- Step 3: at those cells, the prescribed parameters agree with the ambient capped at `c`.
  have hAq : min Ap c = min qAD c := by
    have := hpq _ h₂
    rw [hp' _ h₂, hqz _ (hmem h₂), thinLabelling, gradedIndex_oldCell, hd₂] at this
    exact this.symm
  have hFq : min Fp c = min qF c := by
    have := hpq _ hs
    rw [hp' _ hs, hqz _ (hmem hs), thinLabelling, gradedIndex_oldCell, hsD] at this
    exact this.symm
  have hGq : min Gp c = min qG c := by
    have := hpq _ hg
    rw [hp' _ hg, hqz _ (hmem hg), thinLabelling, gradedIndex_oldCell, hgE] at this
    exact this.symm
  -- Step 4: the parameter-level lift, with `A_C` unprescribed; its thin labelling is the lift.
  have hc2' : IsSelfVisible 2 c ∨ some Fp = some ⊥ := by
    refine hc2.imp_right fun h ↦ ?_
    have := h _ hs (by rw [grade_oldCell]; exact congrArg Prod.snd hsD)
    rw [hp' _ hs, gradedIndex_oldCell, hsD] at this
    exact congrArg some this
  obtain ⟨xAC, xAD, xF, xG, hx, hxAC, hxAD, hxF, hxG, -, hpAD, hpF, hpG⟩ :=
    exists_thinLift hc1 (PAC := none) (PAD := some Ap) (PF := some Fp) (PG := some Gp) hc2'
      (.inr rfl) hq' forall_mem_none (forall_mem_some hAp) (forall_mem_some hFp)
      (forall_mem_some hGp) forall_mem_none
      (forall_mem_some (forall_mem_some hGFp)) (forall_mem_some (forall_mem_some hGAp))
      forall_mem_none forall_mem_none
      forall_mem_none (forall_mem_some hAq) (forall_mem_some hFq) (forall_mem_some hGq)
  refine ⟨thinLabelling I xAC xAD xF xG ⊥, isLawfulBelow_thinLabel hIL hIR hx,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hqz z hz]
    exact min_thinLabel_eq hxAC hxAD hxF hxG _
  · rw [hp' z hz, thinLabelling, hpAD Ap rfl, hpF Fp rfl, hpG Gp rfl]
    exact thinLabel_congr_one (thinKind_ne_one (three_notMem_of_mem_below hz)) _ _ _ _ _ _

/-! ### One old cell at each graded index -/

include hIL hIR in
/-- **The amalgam has one cell at each graded index.** -/
theorem amalgam_gradedIndex_injective : Function.Injective I.amalgam.toCellScheme.gradedIndex := by
  intro z z' h
  have hs : I.amalgam.toCellScheme.scope z = I.amalgam.toCellScheme.scope z' := congrArg Prod.fst h
  rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem z)
    (I.scope_ne_univ z) with hC | hD
  · exact StageType.eq_of_gradedIndex_eq_of_restrictFace (hIL ▸ I.restrictFace_left)
      gradedIndex_injective_TL
      ((coe_subset.mpr (Coatom.univ_map_left ▸ hC)).trans (coe_map_subset_range _ _))
      ((coe_subset.mpr (Coatom.univ_map_left ▸ hs ▸ hC)).trans (coe_map_subset_range _ _)) h
  · exact StageType.eq_of_gradedIndex_eq_of_restrictFace (hIR ▸ I.restrictFace_right)
      CaseSplitCounterexample.gradedIndex_injective_T5
      ((coe_subset.mpr (Coatom.univ_map_right ▸ hD)).trans (coe_map_subset_range _ _))
      ((coe_subset.mpr (Coatom.univ_map_right ▸ hs ▸ hD)).trans (coe_map_subset_range _ _)) h

/-! ### Capped lifts from the coatoms to the full scope -/

/-- **From lifts at the grade `3` to capped lifts at the grades `k ≤ 3`.**  A prescription below
`(B, k)` and an ambient below `(univ, k)` are extended by `⊥` above the grade `k`; the lift at the
grade `3` of the extensions, restricted below `(univ, k)`, is the capped lift. -/
private theorem cappedLift_of_exists_lift {B : Finset (Fin 5)} {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (H : ∀ c : Label.{u}, IsSelfVisible 1 c → ∀ p q : Fin (thinScheme I).card → Label.{u},
      (thinScheme I).rows.IsLawfulBelow (B, 3) (fun z ↦ p z) →
      (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ q z) →
      (∀ z ∈ (thinScheme I).toCellScheme.below (B, 3), min (q z) c = min (p z) c) →
      (IsSelfVisible 2 c ∨ ∀ z ∈ (thinScheme I).toCellScheme.below (B, 3),
        (thinScheme I).toCellScheme.grade z = 2 → p z = ⊥) →
      ∃ x : Fin (thinScheme I).card → Label.{u},
        (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ x z) ∧
        (∀ z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3),
          min (x z) c = min (q z) c) ∧
        ∀ z ∈ (thinScheme I).toCellScheme.below (B, 3), x z = p z) :
    (thinScheme I).rows.CappedLift (X := (B, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ := by
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  let p' : Fin (thinScheme I).card → Label.{u} := fun z ↦
    if (thinScheme I).toCellScheme.grade z ≤ k then Rows.extendBot (B, k) p z else ⊥
  let q' : Fin (thinScheme I).card → Label.{u} := fun z ↦
    if (thinScheme I).toCellScheme.grade z ≤ k then
      Rows.extendBot ((univ : Finset (Fin 5)), k) q z else ⊥
  have hp' (z) : p' z = if (thinScheme I).toCellScheme.grade z ≤ k then
      Rows.extendBot (B, k) p z else ⊥ := rfl
  have hq' (z) : q' z = if (thinScheme I).toCellScheme.grade z ≤ k then
      Rows.extendBot ((univ : Finset (Fin 5)), k) q z else ⊥ := rfl
  have hpl : (thinScheme I).rows.IsLawfulBelow (B, 3) (fun z ↦ p' z) :=
    Rows.isLawfulBelow_extendAbove (Rows.isLawfulBelow_extendBot.mpr hp)
  have hql : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ q' z) :=
    Rows.isLawfulBelow_extendAbove (Rows.isLawfulBelow_extendBot.mpr hq)
  have hpq' : ∀ z ∈ (thinScheme I).toCellScheme.below (B, 3), min (q' z) c = min (p' z) c := by
    intro z hz
    rw [hp', hq']
    split_ifs with h
    · rw [Rows.extendBot_of_mem p (⟨hz.1, h⟩ : z ∈ (thinScheme I).toCellScheme.below (B, k)),
        Rows.extendBot_of_mem q (⟨subset_univ _, h⟩ :
          z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), k))]
      exact hpq ⟨z, ⟨hz.1, h⟩⟩
    · rfl
  have hc2 : IsSelfVisible 2 c ∨ ∀ z ∈ (thinScheme I).toCellScheme.below (B, 3),
      (thinScheme I).toCellScheme.grade z = 2 → p' z = ⊥ := by
    rcases (show 2 ≤ k ∨ k = 1 by omega) with h2 | rfl
    · exact .inl (hc.mono h2)
    · exact .inr fun z _ hz2 ↦ by rw [hp', ite_eq_right (by omega)]
  obtain ⟨x, hx, hxq, hxp⟩ := H c (hc.mono hk1) p' q' hpl hql hpq' hc2
  refine ⟨fun z ↦ x z, hx.mono (X := ((univ : Finset (Fin 5)), k)) ⟨subset_rfl, hk3⟩,
    fun z ↦ ?_, fun z ↦ ?_⟩
  · have hz : (thinScheme I).toCellScheme.grade z.1 ≤ k := z.2.2
    rw [hxq z.1 ⟨subset_univ _, hz.trans hk3⟩, hq', ite_eq_left hz,
      Rows.extendBot_of_mem q z.2]
  · have hz : (thinScheme I).toCellScheme.grade z.1 ≤ k := z.2.2
    -- The restriction of `x` below `(univ, k)`, at `z`.
    change x z.1 = p z
    rw [hxp z.1 ⟨z.2.1, hz.trans hk3⟩, hp', ite_eq_left hz, Rows.extendBot_of_mem p z.2]

include hIL hIR in
/-- **The capped lift from `(C, k)` to `(univ, k)`**, `k ≤ 3`. -/
theorem cappedLift_left {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (thinScheme I).rows.CappedLift (X := (coatomC, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_exists_lift hk1 hk3 fun _ hc _ _ hp hq hpq hc2 ↦
    exists_lift_left hIL hIR hc hp hq hpq hc2

include hIL hIR in
/-- **The capped lift from `(D, k)` to `(univ, k)`**, `k ≤ 3`. -/
theorem cappedLift_right {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    (thinScheme I).rows.CappedLift (X := (coatomD, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ :=
  cappedLift_of_exists_lift hk1 hk3 fun _ hc _ _ hp hq hpq hc2 ↦
    exists_lift_right hIL hIR hc hp hq hpq hc2

include hIL hIR in
/-- **The capped lift from a coatom at the grade `4` to `(univ, 4)`**, from the capped lift at the
grade `3`.  If the prescription is `⊥` at the apex, lift its restriction below the grade `3` (with
the ambient, or with `⊥` when the ambient is not `⊥` at the grade `4`, where the cap is then `⊥`)
and extend by `⊥`; otherwise the prescription is `⊥` below its apex, and the lift is the labelling
of its apex label alone. -/
theorem cappedLift_four {B : Finset (Fin 5)} (hB : B = coatomC ∨ B = coatomD)
    (h3 : (thinScheme I).rows.CappedLift (X := (B, 3)) (Y := ((univ : Finset (Fin 5)), 3))
      ⟨subset_univ _, le_rfl⟩) :
    (thinScheme I).rows.CappedLift (X := (B, 4)) (Y := ((univ : Finset (Fin 5)), 4))
      ⟨subset_univ _, le_rfl⟩ := by
  -- Step 1: the apex `a` at `(B, 4)` is the only cell of grade `4` below `(B, 4)`.
  have hBne : B ≠ univ := by rcases hB with rfl | rfl <;> decide
  have hBcard : #B = 4 := by rcases hB with rfl | rfl <;> decide
  -- The apex at `(B, 4)`.
  obtain ⟨a, ha⟩ : ∃ a : Fin I.amalgam.card, I.amalgam.toCellScheme.gradedIndex a = (B, 4) := by
    refine I.exists_gradedIndex_eq _ ⟨?_, by omega, by rw [hBcard]⟩ hBne
    rcases hB with rfl | rfl
    · exact coatomC_eq ▸ ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
    · exact coatomD_eq ▸ ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1
  have hag : I.amalgam.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hag' : (thinScheme I).toCellScheme.grade (oldCell I a) = 4 := by rw [grade_oldCell, hag]
  have haB : oldCell I a ∈ (thinScheme I).toCellScheme.below (B, 4) := oldCell_mem_below ha.le
  -- The apex is the only cell of grade `4` below `(B, 4)`.
  have huniq : ∀ z ∈ (thinScheme I).toCellScheme.below (B, 4),
      (thinScheme I).toCellScheme.grade z = 4 → z = oldCell I a := by
    intro z hz hz4
    obtain ⟨d, rfl⟩ := exists_eq_oldCell (z := z) fun h ↦ hBne (univ_subset_iff.mp (h ▸ hz.1))
    refine congrArg (oldCell I) (amalgam_gradedIndex_injective hIL hIR ?_)
    have hs : I.amalgam.toCellScheme.scope d ⊆ B := by rw [← scope_oldCell]; exact hz.1
    have hg : I.amalgam.toCellScheme.grade d = 4 := by rw [← grade_oldCell]; exact hz4
    have hcard : 4 ≤ #(I.amalgam.toCellScheme.scope d) :=
      hg ▸ I.amalgam.isWellFormed.isWellFormed.grade_le_card d
    rw [ha]
    exact Prod.ext (eq_of_subset_of_card_le hs (by rw [hBcard]; exact hcard)) hg
  have hbelow : ∀ z ∈ (thinScheme I).toCellScheme.below (B, 4),
      z ∈ (thinScheme I).toCellScheme.below
        ((thinScheme I).toCellScheme.gradedIndex (oldCell I a)) := fun z hz ↦ by
    rw [gradedIndex_oldCell, ha]; exact hz
  -- Step 2: extend the prescription `p` and the ambient `q` by `⊥` to all cells (`p'`, `q'`); it
  -- is enough to lift `p'` against `q'`.  The ambient is constant at the grade `4`.
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  let p' := Rows.extendBot (B, 4) p
  let q' := Rows.extendBot ((univ : Finset (Fin 5)), 4) q
  have hpl : (thinScheme I).rows.IsLawfulBelow (B, 4) (fun z ↦ p' z) :=
    Rows.isLawfulBelow_extendBot.mpr hp
  have hql : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) (fun z ↦ q' z) :=
    Rows.isLawfulBelow_extendBot.mpr hq
  have hp'z : ∀ z (hz : z ∈ (thinScheme I).toCellScheme.below (B, 4)), p' z = p ⟨z, hz⟩ :=
    fun _ hz ↦ Rows.extendBot_of_mem p hz
  have hq'z : ∀ z, q' z = q ⟨z, mem_below_univ_four z⟩ :=
    fun z ↦ Rows.extendBot_of_mem q (mem_below_univ_four z)
  have hpq' : ∀ z ∈ (thinScheme I).toCellScheme.below (B, 4), min (q' z) c = min (p' z) c :=
    fun z hz ↦ by
      rw [hp'z z hz, hq'z z]
      exact hpq ⟨z, hz⟩
  have hqa : q' (oldCell I a) = q' (newCell I 4) := eq_newCell_four hql hag'
  suffices h : ∃ x : Fin (thinScheme I).card → Label.{u},
      (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) (fun z ↦ x z) ∧
      (∀ z, min (x z) c = min (q' z) c) ∧
      ∀ z ∈ (thinScheme I).toCellScheme.below (B, 4), x z = p' z by
    obtain ⟨x, hx, hxq, hxp⟩ := h
    refine ⟨fun z ↦ x z, hx, fun z ↦ ?_, fun z ↦ ?_⟩
    · rw [hxq, hq'z z.1]
    · -- The restriction of `x` below `(univ, 4)`, at `z`.
      change x z.1 = p z
      rw [hxp z.1 z.2, hp'z z.1 z.2]
  by_cases hω : p' (oldCell I a) = ⊥
  · -- Step 3: the prescription is `⊥` at the apex.  If the ambient is not `⊥` at the grade `4`,
    -- the cap is `⊥`; replace the ambient by `⊥` (`q₃`), lift below the grade `3` by `h3`, and
    -- extend by `⊥` above the grade `3`.
    have hc0 : q' (newCell I 4) ≠ ⊥ → c = ⊥ := fun h ↦ by
      have := hpq' _ haB
      rw [hω, min_bot_left, hqa] at this
      exact (min_eq_bot.mp this).resolve_left h
    let q₃ : Fin (thinScheme I).card → Label.{u} := fun z ↦
      if q' (newCell I 4) = ⊥ then q' z else ⊥
    have hq₃ : (thinScheme I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) (fun z ↦ q₃ z) := by
      by_cases h : q' (newCell I 4) = ⊥
      · have he : (fun z : (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) ↦ q₃ z)
            = fun z : (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) ↦ q' z :=
          funext fun z ↦ ite_eq_left h
        rw [he]
        exact hql.mono (X := ((univ : Finset (Fin 5)), 3)) ⟨subset_rfl, by omega⟩
      · have he : (fun z : (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) ↦ q₃ z)
            = fun _ ↦ ⊥ := funext fun z ↦ ite_eq_right h
        rw [he]
        exact Rows.isLawfulBelow_const_bot _
    have hq₃c : ∀ z, min (q₃ z) c = min (q' z) c := fun z ↦ by
      by_cases h : q' (newCell I 4) = ⊥
      · exact congrArg (min · c) (ite_eq_left h)
      · rw [hc0 h, min_bot_right, min_bot_right]
    obtain ⟨x₃, hx₃, hx₃q, hx₃p⟩ := (Rows.cappedLift_iff_forall_exists _).mp h3 c
      (hc.mono (by omega)) (fun z ↦ p' z) (fun z ↦ q₃ z)
      (hpl.mono (X := (B, 3)) ⟨subset_rfl, by omega⟩) hq₃
      (fun z ↦ (hq₃c z.1).trans (hpq' z.1 ⟨z.2.1, z.2.2.trans (by omega)⟩))
    refine ⟨fun z ↦ if (thinScheme I).toCellScheme.grade z ≤ 3 then
      Rows.extendBot ((univ : Finset (Fin 5)), 3) x₃ z else ⊥,
      Rows.isLawfulBelow_extendAbove (Rows.isLawfulBelow_extendBot.mpr hx₃), fun z ↦ ?_,
      fun z hz ↦ ?_⟩
    · dsimp only
      by_cases hz3 : (thinScheme I).toCellScheme.grade z ≤ 3
      · have hzm : z ∈ (thinScheme I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
          ⟨subset_univ _, hz3⟩
        rw [ite_eq_left hz3, Rows.extendBot_of_mem x₃ hzm, hx₃q ⟨z, hzm⟩]
        exact hq₃c z
      · have hz4 : (thinScheme I).toCellScheme.grade z = 4 := by
          have := grade_le_four z; omega
        rw [ite_eq_right hz3, eq_newCell_four hql hz4]
        by_cases h : q' (newCell I 4) = ⊥
        · rw [h]
        · rw [hc0 h, min_bot_right, min_bot_right]
    · dsimp only
      by_cases hz3 : (thinScheme I).toCellScheme.grade z ≤ 3
      · rw [ite_eq_left hz3, Rows.extendBot_of_mem x₃ ⟨subset_univ _, hz3⟩]
        exact hx₃p ⟨z, ⟨hz.1, hz3⟩⟩
      · have hz4 : (thinScheme I).toCellScheme.grade z = 4 := by
          have := grade_le_four z; omega
        rw [ite_eq_right hz3, huniq z hz hz4, hω]
  · -- Step 4: the prescription is not `⊥` at the apex, hence `⊥` below the grade `4` (the row of
    -- the apex); the lift is the labelling of its apex label `Ω` alone.  If `c ≠ ⊥`, the ambient
    -- is not `⊥` at the grade `4`, hence `⊥` below it, and agrees with `Ω` capped at `c` there.
    obtain ⟨ho, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hpl
    have hωsv : IsSelfVisible 4 (p' (oldCell I a)) := hag' ▸ ho _ haB
    refine ⟨thinLabelling I ⊥ ⊥ ⊥ ⊥ (p' (oldCell I a)), isLawfulBelow_omega hIL hIR hωsv,
      fun z ↦ ?_, fun z hz ↦ ?_⟩
    · by_cases hc0 : c = ⊥
      · rw [hc0, min_bot_right, min_bot_right]
      have hΩq : q' (newCell I 4) ≠ ⊥ := by
        intro h
        have := hpq' _ haB
        rw [hqa, h, min_bot_left] at this
        exact (min_eq_bot.mp this.symm).elim hω hc0
      rw [thinLabelling_omega]
      split_ifs with hz4
      · rw [eq_newCell_four hql hz4, ← hqa]
        exact (hpq' _ haB).symm
      · rw [eq_bot_of_newCell_four hql hΩq hz4]
    · rw [thinLabelling_omega]
      split_ifs with hz4
      · rw [huniq z hz hz4]
      · have := (hl _ haB).eq_bot (d := ⟨z, hbelow z hz⟩)
          ((row_eq_bot_iff_of_grade_four hIL hIR hag' ⟨z, hbelow z hz⟩).mpr hz4)
        exact ((min_eq_bot.mp this).resolve_right hω).symm

/-! ### Legality below the full grade -/

/-- The faces of the thin scheme are those of the amalgam. -/
theorem faces_thinScheme : (thinScheme I).toCellScheme.faces = I.amalgam.toCellScheme.faces := rfl

/-- **Pairs below a coatom**: the capped lifts of the amalgam, transported along the old
cells. -/
theorem cappedLift_old {X Y : Finset (Fin 5) × ℕ}
    (hX : X ∈ (thinScheme I).toCellScheme.gradedFaces)
    (hY : Y ∈ (thinScheme I).toCellScheme.gradedFaces) (hY1 : Y.1 ≠ univ) (h : X ≤ Y) :
    (thinScheme I).rows.CappedLift h := by
  have hX1 : X.1 ≠ univ := fun hX ↦ hY1 (univ_subset_iff.mp (hX ▸ h.1))
  refine Rows.CappedLift.of_comap (isLowerEmbedding_oldCell I) (image_oldCell_below hX1)
    (image_oldCell_below hY1) le_rfl (h' := h) ?_
  rw [comap_rows_oldCell]
  exact I.isBountiful hX hY h

include hIL hIR in
/-- **The thin scheme is bountiful.**  By `Rows.isBountiful_iff_forall_cappedLift_fst`, it is
enough to lift from `X` to the pair on the face of `Y` at the grade of `X`.  Below a coatom the
lifts are those of the amalgam; to the full scope, a lift from `(B, k)` goes first within the
amalgam to the coatom containing `B`, and then by `cappedLift_left`, `cappedLift_right` (at the
grades `k ≤ 3`) or `cappedLift_four`. -/
theorem isBountiful_thinScheme : (thinScheme I).rows.IsBountiful := by
  refine Rows.isBountiful_iff_forall_cappedLift_fst.mpr fun X Y hX hY h ↦ ?_
  by_cases hY1 : Y.1 = univ
  · obtain ⟨Y1, k⟩ := Y
    simp only at hY1
    subst hY1
    obtain ⟨X1, j⟩ := X
    by_cases hX1 : X1 = univ
    · subst hX1; exact Rows.cappedLift_refl _
    have hj1 : 1 ≤ j := hX.2.1
    have hside : X1 ⊆ coatomC ∨ X1 ⊆ coatomD :=
      I.subset_or_subset X1 hX.1 hX1
    have hj4 : j ≤ 4 := hX.2.2.trans (by
      rcases hside with hs | hs
      · exact (card_le_card hs).trans (by decide)
      · exact (card_le_card hs).trans (by decide))
    rcases hside with hs | hs
    · have hB : (coatomC, j) ∈ (thinScheme I).toCellScheme.gradedFaces :=
        ⟨coatomC_eq ▸ ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1, hj1,
          hj4.trans (show (4 : ℕ) ≤ #coatomC by decide)⟩
      have h1 := cappedLift_old hX hB (show coatomC ≠ univ by decide) (X := (X1, j))
        ⟨hs, le_rfl⟩
      have h2 : (thinScheme I).rows.CappedLift (X := (coatomC, j))
          (Y := ((univ : Finset (Fin 5)), j)) ⟨subset_univ _, le_rfl⟩ := by
        rcases (show j ≤ 3 ∨ j = 4 by omega) with hj3 | rfl
        · exact cappedLift_left hIL hIR hj1 hj3
        · exact cappedLift_four hIL hIR (.inl rfl) (cappedLift_left hIL hIR (by omega) le_rfl)
      exact h1.trans h2
    · have hB : (coatomD, j) ∈ (thinScheme I).toCellScheme.gradedFaces :=
        ⟨coatomD_eq ▸ ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1, hj1,
          hj4.trans (show (4 : ℕ) ≤ #coatomD by decide)⟩
      have h1 := cappedLift_old hX hB (show coatomD ≠ univ by decide) (X := (X1, j))
        ⟨hs, le_rfl⟩
      have h2 : (thinScheme I).rows.CappedLift (X := (coatomD, j))
          (Y := ((univ : Finset (Fin 5)), j)) ⟨subset_univ _, le_rfl⟩ := by
        rcases (show j ≤ 3 ∨ j = 4 by omega) with hj3 | rfl
        · exact cappedLift_right hIL hIR hj1 hj3
        · exact cappedLift_four hIL hIR (.inr rfl) (cappedLift_right hIL hIR (by omega) le_rfl)
      exact h1.trans h2
  · exact cappedLift_old (Y := (Y.1, X.2)) hX
      ⟨hY.1, hX.2.1, hX.2.2.trans (card_le_card h.1)⟩ hY1 _

/-- Adding a new cell keeps well-formedness. -/
theorem isWellFormed_addThinCell {S : Scheme.{u} 5} {j : ℕ} {h : NoneAbove S j}
    (hS : S.IsWellFormed) (hj : 0 < j) (hj5 : j ≤ 5) : (addThinCell S j h).IsWellFormed :=
  Scheme.isWellFormed_appendFullCell hS hj hj5

/-- Adding a new cell keeps coding: the rows of the new cells are coded. -/
theorem isCoded_addThinCell {S : Scheme.{u} 5} {j : ℕ} {h : NoneAbove S j} (hS : S.IsCoded) :
    (addThinCell S j h).IsCoded :=
  Scheme.isCoded_appendFullCell hS fun _ ↦ thinRow_lt _ _

/-- **The thin scheme is well formed.** -/
theorem isWellFormed_thinScheme : (thinScheme I).IsWellFormed :=
  isWellFormed_addThinCell (isWellFormed_addThinCell (isWellFormed_addThinCell
    (isWellFormed_addThinCell I.amalgam.isWellFormed (by omega) (by omega)) (by omega) (by omega))
    (by omega) (by omega)) (by omega) (by omega)

/-- **The rows of the thin scheme are coded.** -/
theorem isCoded_thinScheme : (thinScheme I).IsCoded :=
  isCoded_addThinCell (isCoded_addThinCell (isCoded_addThinCell
    (isCoded_addThinCell I.amalgam.isCoded)))

include hIL hIR in
/-- **The rows of the thin scheme are consistent.**  The old rows are those of the amalgam; the row
of the new cell at `(univ, k)` is the thin labelling of the parameters `isThinLawfulBelow_row_one`,
`isThinLawfulBelow_row_two`, `isThinLawfulBelow_row_three` for `k ≤ 3`, and the labelling of
`Ω = ω + 4` alone for `k = 4`. -/
theorem isConsistent_thinScheme : (thinScheme I).rows.IsConsistent := by
  intro s
  rcases cell_cases s with ⟨a, rfl⟩ | rfl | rfl | rfl | rfl
  · have hφ := isLowerEmbedding_oldCell I
    refine (Rows.isLawfulBelow_comap_iff hφ (hφ.image_below_gradedIndex a)).mp ?_
    rw [comap_rows_oldCell]
    convert I.isConsistent a using 1
    funext t
    exact congrArg (fun R : I.amalgam.toCellScheme.Rows ↦ R.row a t) comap_rows_oldCell
  all_goals
    rw [row_newCell_eq (by omega) (by omega)]
  · exact (isLawfulBelow_thinLabel hIL hIR (Ω := ⊥) isThinLawfulBelow_row_one).mono
      (by rw [gradedIndex_newCell (by omega) (by omega)]; exact ⟨subset_rfl, by omega⟩)
  · exact (isLawfulBelow_thinLabel hIL hIR (Ω := ⊥) isThinLawfulBelow_row_two).mono
      (by rw [gradedIndex_newCell (by omega) (by omega)]; exact ⟨subset_rfl, by omega⟩)
  · exact (isLawfulBelow_thinLabel hIL hIR (Ω := ⊥) isThinLawfulBelow_row_three).mono
      (by rw [gradedIndex_newCell (by omega) (by omega)])
  · exact (isLawfulBelow_omega hIL hIR (isSelfVisible_gridPoint 4 1)).mono
      (by rw [gradedIndex_newCell (by omega) (by omega)])

/-- **The thin scheme is complete below the full grade.** -/
theorem exists_gradedIndex_eq_thinScheme {X : Finset (Fin 5) × ℕ}
    (hX : X ∈ (thinScheme I).toCellScheme.gradedFaces) (hX5 : X.2 < 5) :
    ∃ z, (thinScheme I).toCellScheme.gradedIndex z = X := by
  by_cases hX1 : X.1 = univ
  · obtain ⟨X1, k⟩ := X
    simp only at hX1 hX5
    subst hX1
    exact ⟨newCell I k, gradedIndex_newCell hX.2.1 (by omega)⟩
  · obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq X hX hX1
    exact ⟨oldCell I d, (gradedIndex_oldCell d).trans hd⟩

include hIL hIR in
/-- **The thin scheme is legal below the full grade.** -/
theorem isLegalBelowFullGrade_thinScheme : (thinScheme I).IsLegalBelowFullGrade where
  isWellFormed := isWellFormed_thinScheme
  isCoded := isCoded_thinScheme
  isConsistent := isConsistent_thinScheme hIL hIR
  isBountiful := isBountiful_thinScheme hIL hIR
  grade_lt z := Nat.lt_succ_of_le (grade_le_four z)
  exists_gradedIndex_eq _ hX hX5 := exists_gradedIndex_eq_thinScheme hX hX5

/-! ### The thin completion -/

/-- The old cells, in their order. -/
noncomputable def embedOld : Fin I.amalgam.card ↪o Fin (thinScheme I).card :=
  OrderEmbedding.ofStrictMono (oldCell I) fun _ _ h ↦ by
    unfold oldCell; simpa [Fin.castSucc_lt_castSucc_iff] using h

include hIL hIR in
/-- **The thin completion** of a seed whose coatom types are `TL` and `T5`: the thin scheme, with
the labelling `⊤` at the cells of grade `4` (the two apexes and the new cell at `(univ, 4)`) and
`⊥` elsewhere. -/
noncomputable def thinCompletion : CompletionBelowFullGrade I where
  scheme := thinScheme I
  embed := embedOld
  isLowerEmbedding := isLowerEmbedding_oldCell I
  scope_embed := scope_oldCell
  comap_rows := comap_rows_oldCell
  mem_range_embed z hz := by
    obtain ⟨d, rfl⟩ := exists_eq_oldCell hz
    exact ⟨d, rfl⟩
  faces_eq := faces_thinScheme
  isLegalBelowFullGrade := isLegalBelowFullGrade_thinScheme hIL hIR
  label := thinLabelling I ⊥ ⊥ ⊥ ⊥ ⊤
  isLawful := (isLawfulBelow_omega hIL hIR (isSelfVisible_top 4)).isLawful mem_below_univ_four
  label_embed d := by
    -- `embedOld` is `oldCell` and the label is the thin labelling of `Ω = ⊤` alone.
    change thinLabelling I ⊥ ⊥ ⊥ ⊥ ⊤ (oldCell I d) = _
    rw [thinLabelling_omega, grade_oldCell, amalgam_label hIL hIR]

include hIL hIR in
/-- **A seed whose coatom types are `TL` and `T5` has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_of : Nonempty (CompletionBelowFullGrade I) :=
  ⟨thinCompletion hIL hIR⟩

/-- **The asymmetric seed has a completion below the full grade**: the thin completion, outside
the tower route (the tower fails for `seedL`, `not_towerInvariant_top_seedL`). -/
theorem nonempty_completionBelowFullGrade_seedL :
    Nonempty (CompletionBelowFullGrade (seedL α)) :=
  nonempty_completionBelowFullGrade_of rfl rfl

end VaughtConjecture.ThinCompletion
