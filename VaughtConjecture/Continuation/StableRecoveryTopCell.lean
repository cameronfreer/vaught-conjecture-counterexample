/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryReading

/-!
# A stable recovery scheme for a donor with a new cell at the formal top, under a proper cap

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap, the marker and the decoder of (R4)); semantic contract, item 8.

**The question.**  (R4) follows from stable recovery schemes for the graded cap calibration at
every `ξ < ω₁` (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`), a finite statement
that is open.  The instances compiled so far (`Continuation.StableRecoveryReading`,
`Continuation.StableRecoveryTwin`) have a cap labelled the formal top and donors without a cell
labelled the formal top, so the clause on `γ` of `StageType.IsStableRecoveryScheme` and the branch
at the formal top of `StageType.ReadsThroughCap` were not used.  In (R4) the cap is a stable label
of the context, a proper ordinal `λ_ξ + M` with `M` at least its grade.  This file tests both:
a context whose cap is labelled exactly `λ_ξ + 2 = λ_ξ + N` (a proper ordinal, the least label the
calibration allows at grade `N = 2`), `γ = λ_ξ + 1` (the largest `γ` the calibration allows), and
a donor with a new cell labelled the formal top.  The result is positive
(`exists_isStableRecoveryScheme_topCell`): the hypotheses of
`StageType.IsStableRecoveryScheme.of_readsThroughCap` hold, so the conclusion of
`StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds at this input.

**The scheme** (`topScheme`).  The cells of the reading scheme
(`StableRecoveryReading.readingCells`: points `0` private, `1` the root, `2` the new point; faces
the intervals of `0 < 1 < 2`; one cell at each graded face), with the dead cell `6` at `({1, 2}, 2)`
made live as a **new cap**: its row reads the new cell `4` at `1` and itself at `ω + 2`, as the cap
`5` reads the reference cell `3`; and the reading cell `8` reads the cell `6` exactly as it reads
the cap.  The other rows are those of the reading scheme.

**Its lawful labellings** (`isLawful_topLabel`, `exists_of_isLawfulBelow`).  Below every pair they
are exactly the labellings `topLabel A E B` (`⊥` at the dead cells, `A` at the reference cell, `E`
at the new cell and the cell `(univ, 1)`, `B` at the cap, the new cap and the reading cell) of the
reading triples (`StableRecoveryReading.IsReadingTriple`).  The new cap equals the reading cell:
the reading cell reads it as it reads itself (locality) and lies above it at the same grade
(availability).  The lift of parameters (`exists_isReadingTriple_lift_top`) has one case more than
`StableRecoveryReading.exists_isReadingTriple_lift`: below `({1, 2}, 2)` the third parameter is
prescribed (by the new cap) without the first.

**The input.**  The context `T⁺` (`contextType`) is the face along `{0, 1}` of the labelled scheme
with the parameters `(λ_ξ + 1, λ_ξ + 1, λ_ξ + 2)` (`capType`): the marker `λ_ξ + 1` at the
reference cell and the cap `λ_ξ + 2` at grade `2`.  The donor `D` (`donorType`) is the face along
`{1, 2}` of the labelled scheme with the parameters `(λ_ξ + 1, λ_ξ + 1, ⊤)` (`sourceType`): `⊥` at
`({2}, 1)`, `λ_ξ + 1` at `({1, 2}, 1)`, and the formal top at `({1, 2}, 2)`.  Both labelled
schemes have the same face along the root `{1}`, one dead cell (`rootType`), so `D` is a coface of
the root of `T⁺`.  The graded cap calibration holds with `γ = λ_ξ + 1`
(`gradedCapCalibration_contextType`).

**What it exercises** (`isStableRecoveryScheme_topScheme`, by `of_readsThroughCap` at the reading
cell).  The cap's label enters only through the hypotheses of `of_readsThroughCap` on the cap (`λ_ξ
+ N ≤ T⁺ b`, `γ < λ_ξ + N`), not through `StageType.ReadsThroughCap`; the decoder
`CellScheme.Rows.IsLawful.label_eq_of_reading` needs only the reference value and the decoded value
strictly below the cap, which holds for a proper cap since their finite parts are below `N`.  The
new cell labelled the formal top is read as the cap (the branch at the formal top of
`ReadsThroughCap`), and the clause on `γ` is met through
`CellScheme.Rows.IsLawful.le_label_of_reading`: the recovered label is at least the cap, above `γ`.
The recovered label is exactly the cap's proper value `λ_ξ + 2` in every stage type on the scheme
with face `T⁺` (`label_newCap_eq`): the formal top of `D` is recovered as a proper ordinal above
`γ`, not as the formal top, which is all that (R4) asks there.

**What stays degenerate.**  Recovery at the ordinal new cell still copies the marker (`n = i = 1`);
the root is one dead cell; `N = k + 1`; the reference is in the block `λ_ξ`; and `(univ, 2)` is
the only graded face of grade `2` containing the cap and the new cells.

## Implementation notes

The two labelled schemes `sourceType` and `capType` differ only in the label of the caps and the
reading cell, `⊤` against `λ_ξ + 2`.  Their faces along the root are compared in
`restrictFace_sourceType_root` with the scheme equality stated as
`show topScheme.comap g = topScheme.comap g from rfl` and the labels compared through the dead cell
`1` (`cellMap_root_eq`), never through the two labellings.  Closing the same goal by
`StageType.ext rfl` makes the kernel unfold the ordinal labels of both labellings and hits a
deterministic timeout.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryTopCell

open Finset Label StageType ThinCompletion StableRecoveryReading
open Ordinal hiding univ

/-! ### The scheme -/

/-- The kind of each cell of `StableRecoveryReading.readingCells`: `0` dead, `1` the reference
cell, `2` the new cell, `3` the cell at `(univ, 1)`, `4` the cap, `5` the reading cell, `6` the
new cap at `({1, 2}, 2)`. -/
def cellKind : Fin 10 → Fin 7 := ![0, 0, 0, 1, 2, 4, 6, 3, 5, 0]

/-- The rows, by the kind of the cell and the kind of the cell read: those of the reading scheme,
and the new cap reading the new cell at `1` and itself at `ω + 2`, read by the reading cell at
`ω + 2`. -/
noncomputable def kindRow : Fin 7 → Fin 7 → Label.{u} :=
  ![fun _ ↦ ⊥,
    ![⊥, gridPoint 1 0, ⊥, ⊥, ⊥, ⊥, ⊥],
    ![⊥, ⊥, gridPoint 1 0, ⊥, ⊥, ⊥, ⊥],
    ![⊥, gridPoint 1 0, gridPoint 1 1, gridPoint 1 1, ⊥, ⊥, ⊥],
    ![⊥, gridPoint 1 0, ⊥, ⊥, gridPoint 2 1, ⊥, ⊥],
    ![⊥, gridPoint 1 0, gridPoint 1 0, gridPoint 1 0, gridPoint 2 1, gridPoint 2 1, gridPoint 2 1],
    ![⊥, ⊥, gridPoint 1 0, ⊥, ⊥, ⊥, gridPoint 2 1]]

/-- The **scheme with a new cap** on three points: the cells `readingCells` with the rows
`kindRow`. -/
noncomputable abbrev topScheme : Scheme.{u} 3 :=
  ⟨10, readingCells, ⟨fun s d ↦ kindRow (cellKind s) (cellKind d.1)⟩⟩

/-- The row of a cell of the scheme, by kinds. -/
theorem topScheme_row (s : Fin 10) (d) :
    topScheme.{u}.rows.row s d = kindRow (cellKind s) (cellKind d.1) :=
  rfl

/-! ### The labellings -/

/-- The labels of the kinds for the parameters `A` (the reference cell), `E` (the new cell and the
cell `(univ, 1)`) and `B` (the cap, the reading cell and the new cap). -/
noncomputable def kindValue (A E B : Label.{u}) : Fin 7 → Label.{u} := ![⊥, A, E, E, B, B, B]

/-- The **labelling with a new cap** of parameters `A`, `E`, `B`. -/
noncomputable def topLabel (A E B : Label.{u}) (d : Fin 10) : Label.{u} :=
  kindValue A E B (cellKind d)

/-! ### Lawful labellings -/

/-- Locality at `s` from one witness checked at every cell below `s`. -/
private theorem transformsTo_of_witness {s : Fin 10} {p : Fin 10 → Label.{u}} {g : ℕ → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    (h : ∀ d : Fin 10, readingCells.gradedIndex d ≤ readingCells.gradedIndex s →
      min (p d) (p s) = min (σ (kindRow (cellKind s) (cellKind d))) (g (readingCells.grade d))) :
    TransformsTo (fun d : readingCells.below (readingCells.gradedIndex s) ↦ readingCells.grade d)
      (topScheme.{u}.rows.row s) (fun d ↦ min (p d) (p s)) :=
  ⟨g, σ, hw, fun d ↦ h d.1 d.2⟩

/-- Locality at a dead cell: its row and its label are `⊥`. -/
private theorem transformsTo_dead {s : Fin 10} (hs : cellKind s = 0) {A E B : Label.{u}} :
    TransformsTo (fun d : readingCells.below (readingCells.gradedIndex s) ↦ readingCells.grade d)
      (topScheme.{u}.rows.row s)
      (fun d ↦ min (topLabel A E B d) (topLabel A E B s)) := by
  convert TransformsTo.bot _ (topScheme.{u}.rows.row s) using 1
  funext d
  simp [topLabel, hs, kindValue]

/-- **The labellings of reading triples are lawful** on the scheme with a new cap.  The witnesses
are those of `StableRecoveryReading.isLawful_readingLabel`, and at the new cap the two-strip
shifter of `min E B` and `B`; availability holds since the only cells below another of the same
grade are the reference cell and the new cell below the cell `(univ, 1)`, and the cap and the new
cap below the reading cell. -/
theorem isLawful_topLabel {A E B : Label.{u}} (h : IsReadingTriple A E B) :
    topScheme.{u}.rows.IsLawful (topLabel A E B) where
  -- the order law: each label is `⊥` or a parameter, self-visible at the grade of its cell
  orderly d := by
    fin_cases d <;> simp [topLabel, kindValue, cellKind, readingCells, isSelfVisible_bot,
      h.isSelfVisible_ref, h.isSelfVisible_new, h.isSelfVisible_cap]
  -- locality: the witnesses, then the ten cells in order, `⊥` at the dead cells
  locality s := by
    have hx1 : IsSelfVisible 1 (min A B) :=
      h.isSelfVisible_ref.min (h.isSelfVisible_cap.mono (by omega))
    have hy1 : IsSelfVisible 1 (min E B) :=
      h.isSelfVisible_new.min (h.isSelfVisible_cap.mono (by omega))
    have hvr : visibilityReplace 2 1 (min A B) = min A B :=
      visibilityReplace_two_one_of_isSelfVisible hx1
    have hvr' : visibilityReplace 2 1 (min E B) = min E B :=
      visibilityReplace_two_one_of_isSelfVisible hy1
    have hBB : visibilityReplace 2 2 B = B := h.isSelfVisible_cap
    have hEB : min E B = min A B := h.min_cap_eq.symm
    have hAE : min A E = A := min_eq_left h.ref_le_new
    have hw2 : IsWitness (constStepSuppressor 2 B) (twoStrip (min A B) B B) :=
      isWitness_twoStrip h.isSelfVisible_cap
        (by rw [h.isSelfVisible_cap.visibilityReplace_eq 0]
            exact visibilityReplace_le_of_le le_rfl h.isSelfVisible_cap (min_le_right A B))
        hBB.le
    have hw2' : IsWitness (constStepSuppressor 2 B) (twoStrip (min E B) B B) :=
      isWitness_twoStrip h.isSelfVisible_cap
        (by rw [h.isSelfVisible_cap.visibilityReplace_eq 0]
            exact visibilityReplace_le_of_le le_rfl h.isSelfVisible_cap (min_le_right E B))
        hBB.le
    fin_cases s
    · exact transformsTo_dead rfl
    · exact transformsTo_dead rfl
    · exact transformsTo_dead rfl
    · -- the reference cell `3`: the constant shifter `A`
      refine transformsTo_of_witness
        (isWitness_blockConst h.isSelfVisible_ref h.isSelfVisible_ref le_rfl) fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [topLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          blockConst_gridPoint_zero, blockConst_bot]
    · -- the new cell `4`: the constant shifter `E`
      refine transformsTo_of_witness
        (isWitness_blockConst h.isSelfVisible_new h.isSelfVisible_new le_rfl) fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [topLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          blockConst_gridPoint_zero, blockConst_bot]
    · -- the cap `5`: the two-strip shifter of `min A B`
      refine transformsTo_of_witness hw2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [topLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          twoStrip_gridPoint_one_zero, twoStrip_gridPoint_two_one, twoStrip_bot, hvr, hBB]
    · -- the new cap `6`: the two-strip shifter of `min E B`
      refine transformsTo_of_witness hw2' fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [topLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          twoStrip_gridPoint_one_zero, twoStrip_gridPoint_two_one, twoStrip_bot, hvr', hBB]
    · -- the cell `7`: `A` on the natural numbers and `E` above
      refine transformsTo_of_witness
        (isWitness_blockConst h.isSelfVisible_ref h.isSelfVisible_new h.ref_le_new) fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [topLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          blockConst_gridPoint_zero, blockConst_gridPoint_one, blockConst_bot, hAE]
    · -- the reading cell `8`: the two-strip shifter, with `min E B = min A B`
      refine transformsTo_of_witness hw2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [topLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          twoStrip_gridPoint_one_zero, twoStrip_gridPoint_two_one, twoStrip_bot, hvr, hBB, hEB]
    · exact transformsTo_dead rfl
  -- availability: a cell below another of the same grade is itself, `3` or `4` below `7`, `5` or
  -- `6` below `8`, or dead; each is at most the other
  availability s t hst hg := by
    have key : ∀ s t : Fin 10, readingCells.scope s ⊆ readingCells.scope t →
        readingCells.grade s = readingCells.grade t →
          s = t ∨ (s = 3 ∧ t = 7) ∨ (s = 4 ∧ t = 7) ∨ (s = 5 ∧ t = 8) ∨ (s = 6 ∧ t = 8) ∨
            cellKind s = 0 := by
      decide
    refine ⟨t, rfl, ?_⟩
    rcases key s t hst hg with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h0
    · exact le_rfl
    · exact h.ref_le_new
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · simp [topLabel, h0, kindValue]

/-! ### The lift of parameters -/

/-- **The lift of parameters with the third prescribed without the first.**  For reading triples
`p` and `q` and a cap `c`, self-visible at `2` unless the third parameter of `q` is `⊥`, if the
second and third parameters of `p` agree with those of `q` capped at `c`, some first parameter
completes them to a reading triple agreeing with `q` capped at `c`. -/
theorem exists_isReadingTriple_lift_of_new {pA pE pB qA qE qB c : Label.{u}}
    (hp : IsReadingTriple pA pE pB) (hq : IsReadingTriple qA qE qB)
    (hE : min pE c = min qE c) (hB : min pB c = min qB c) :
    ∃ rA, IsReadingTriple rA pE pB ∧ min rA c = min qA c := by
  obtain ⟨-, pe1, pb2, -, -⟩ := hp
  obtain ⟨qa1, -, -, qle, qmin⟩ := hq
  by_cases hEB : pE < pB
  · -- the first parameter is the second
    refine ⟨pE, ⟨pe1, pe1, pb2, le_rfl, rfl⟩, ?_⟩
    by_cases hqEB : qE < qB
    · rw [Label.eq_of_min_eq_of_lt qmin.symm hqEB]
      exact hE
    · have hqBE : qB ≤ qE := not_lt.mp hqEB
      have hqBA : qB ≤ qA := by
        have := qmin
        rw [min_eq_right hqBE] at this
        exact min_eq_right_iff.mp this
      by_cases hcB : c ≤ qB
      · rw [hE, min_eq_right (hcB.trans hqBE), min_eq_right (hcB.trans hqBA)]
      · -- `qB < c` forces `pB = qB` and then `qE = pE < qB`, which is impossible
        have hlt : qB < c := not_le.mp hcB
        have hpB : pB = qB := Label.eq_of_min_eq_of_lt hB.symm hlt
        have hpc : pE < c := (hEB.trans_eq hpB).trans hlt
        have hqE : qE = pE := Label.eq_of_min_eq_of_lt hE hpc
        exact absurd (hqBE.trans_eq hqE) (not_le.mpr (hEB.trans_eq hpB))
  · -- the first parameter is `max (min pE qA) pB`
    have hBE : pB ≤ pE := not_lt.mp hEB
    refine ⟨max (min pE qA) pB, ⟨(pe1.min qa1).max (pb2.mono (by omega)), pe1, pb2,
      max_le (min_le_left _ _) hBE, ?_⟩, ?_⟩
    · rw [min_eq_right (le_max_right _ _), min_eq_right hBE]
    · have h1 : min (min pE qA) c = min qA c := by
        rw [min_comm pE qA, min_assoc, hE, ← min_assoc, min_eq_left qle]
      rw [min_max_distrib_right, h1]
      refine max_eq_left ?_
      by_cases hqBA : qB ≤ qA
      · rw [hB]
        exact min_le_min_right c hqBA
      · have hqE : qE = qA := Label.eq_of_min_eq_of_lt qmin (not_le.mp hqBA)
        calc min pB c ≤ min pE c := min_le_min_right c hBE
          _ = min qA c := by rw [hE, hqE]

/-- **The lift of parameters on the scheme with a new cap.**  As
`StableRecoveryReading.exists_isReadingTriple_lift`, with the third parameter prescribed whenever
the first or the second is (the cap lies above the reference cell, the new cap above the new
cell). -/
theorem exists_isReadingTriple_lift_top {pA pE pB qA qE qB c : Label.{u}}
    (hp : IsReadingTriple pA pE pB) (hq : IsReadingTriple qA qE qB)
    (hc2 : IsSelfVisible 2 c ∨ qB = ⊥) {xa xe xb : Prop} (hba : xb → xa ∨ xe)
    (hA : xa → min pA c = min qA c) (hE : xe → min pE c = min qE c)
    (hB : xb → min pB c = min qB c) :
    ∃ rA rE rB, IsReadingTriple rA rE rB ∧ (xa → rA = pA) ∧ (xe → rE = pE) ∧ (xb → rB = pB) ∧
      min rA c = min qA c ∧ min rE c = min qE c ∧ min rB c = min qB c := by
  by_cases ha : xa
  · exact exists_isReadingTriple_lift hp hq hc2 (fun _ ↦ ha) hA hE hB
  by_cases hb : xb
  swap
  · exact exists_isReadingTriple_lift hp hq hc2 (fun h ↦ absurd h hb) hA hE hB
  have he : xe := (hba hb).resolve_left ha
  obtain ⟨rA, hrT, hrA⟩ := exists_isReadingTriple_lift_of_new hp hq (hE he) (hB hb)
  exact ⟨rA, pE, pB, hrT, fun h ↦ absurd h ha, fun _ ↦ rfl, fun _ ↦ rfl, hrA, hE he, hB hb⟩

/-! ### Lawful labellings below a pair -/

/-- Every cell is dead or one of the six live cells. -/
private theorem cellKind_cases (d : Fin 10) :
    cellKind d = 0 ∨ d = 3 ∨ d = 4 ∨ d = 7 ∨ d = 5 ∨ d = 6 ∨ d = 8 := by
  revert d
  decide

/-- A dead cell is labelled `⊥`. -/
private theorem topLabel_of_kind_zero {A E B : Label.{u}} {d : Fin 10} (h : cellKind d = 0) :
    topLabel A E B d = ⊥ := by
  simp [topLabel, h, kindValue]

section Below

variable {X : Finset (Fin 3) × ℕ}

/-- A pair above the reference cell and the new cap is above the cap. -/
private theorem mem_five (h3 : (3 : Fin 10) ∈ readingCells.below X)
    (h6 : (6 : Fin 10) ∈ readingCells.below X) : (5 : Fin 10) ∈ readingCells.below X :=
  ⟨h3.1, h6.2⟩

/-- **Every labelling lawful below a pair is a labelling of a reading triple** on the scheme with
a new cap, whose third parameter is `⊥` when neither the cap nor the new cap is below the pair:
for `r` lawful below `X` there are `A`, `E`, `B` with `IsReadingTriple A E B`,
`r d = topLabel A E B d` at every cell `d` below `X`, and `B = ⊥` unless the cap `5` or the new
cap `6` is below `X`. -/
theorem exists_of_isLawfulBelow {r : readingCells.below X → Label.{u}}
    (hr : topScheme.{u}.rows.IsLawfulBelow X r) :
    ∃ A E B, IsReadingTriple A E B ∧ (∀ d, r d = topLabel A E B d.1) ∧
      ((5 : Fin 10) ∉ readingCells.below X → (6 : Fin 10) ∉ readingCells.below X → B = ⊥) := by
  classical
  -- `w`: `r` extended by `⊥` to all cells, lawful below `X`; first its values at the dead
  -- cells, then locality and availability at the cells `7` and `8`; then the triple `(A, E, B)`
  -- and the labelling cell by cell
  set w := CellScheme.Rows.extendBot X r with hw
  have hlaw : topScheme.{u}.rows.IsLawfulBelow X (fun d ↦ w d) := by
    rw [hw, CellScheme.Rows.restrict_extendBot]
    exact hr
  obtain ⟨ho, hl, ha⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hlaw
  have hout : ∀ d, d ∉ readingCells.below X → w d = ⊥ := fun d hd ↦ dite_eq_right hd
  have hsv : ∀ d, IsSelfVisible (readingCells.grade d) (w d) := fun d ↦ by
    by_cases hd : d ∈ readingCells.below X
    · exact ho d hd
    · rw [hout d hd]
      exact isSelfVisible_bot _
  have self : ∀ d : Fin 10, d ∈ readingCells.below (readingCells.gradedIndex d) :=
    readingCells.mem_below_gradedIndex
  have hdead : ∀ d, cellKind d = 0 → w d = ⊥ := fun d h0 ↦ by
    by_cases hd : d ∈ readingCells.below X
    · have := (hl d hd).eq_bot (d := ⟨d, self d⟩) (by rw [topScheme_row]; simp [h0, kindRow])
      simpa using this
    · exact hout d hd
  -- availability into the cells `7` and `8`, the only cells of their graded indices
  have hav : ∀ s t : Fin 10, t ∈ readingCells.below X →
      readingCells.scope s ⊆ readingCells.scope t → readingCells.grade s = readingCells.grade t →
      (∀ u : Fin 10, readingCells.gradedIndex u = readingCells.gradedIndex t → u = t) →
      w s ≤ w t := fun s t ht hst hg huniq ↦ by
    obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
    rwa [huniq u hu] at hle
  -- locality and availability at the cell `7`: `w 7 = w 4` and `w 3 ≤ w 4`
  have h7 : (7 : Fin 10) ∈ readingCells.below X → w 7 = w 4 ∧ w 3 ≤ w 4 := fun h7 ↦ by
    have hT := hl 7 h7
    have m3 : (3 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 7) :=
      show readingCells.gradedIndex 3 ≤ readingCells.gradedIndex 7 by decide
    have m4 : (4 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 7) :=
      show readingCells.gradedIndex 4 ≤ readingCells.gradedIndex 7 by decide
    have huniq : ∀ u : Fin 10, readingCells.gradedIndex u = readingCells.gradedIndex 7 → u = 7 := by
      decide
    have h74 := hT.le_of_le (d := ⟨7, self 7⟩) (d' := ⟨4, m4⟩) le_rfl le_rfl
    have h34 := hT.le_of_le (d := ⟨3, m3⟩) (d' := ⟨4, m4⟩)
      (show gridPoint.{u} 1 0 ≤ gridPoint 1 1 from gridPoint_le_gridPoint.mpr (by omega)) le_rfl
    have h47 := hav 4 7 h7 (by decide) rfl huniq
    have h37 := hav 3 7 h7 (by decide) rfl huniq
    simp only [min_self] at h74
    have h74' : w 7 ≤ w 4 := h74.trans (min_le_left _ _)
    refine ⟨le_antisymm h74' h47, ?_⟩
    have h34' : min (w 3) (w 7) ≤ min (w 4) (w 7) := h34
    rw [min_eq_left h37] at h34'
    exact h34'.trans (min_le_left _ _)
  -- locality and availability at the reading cell `8`: `w 8 = w 5 = w 6`, and `w 3`, `w 4`
  -- agree below the cap
  have h8 : (8 : Fin 10) ∈ readingCells.below X →
      w 8 = w 5 ∧ w 6 = w 5 ∧ min (w 3) (w 5) = min (w 4) (w 5) := fun h8 ↦ by
    have hT := hl 8 h8
    have m3 : (3 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 8) :=
      show readingCells.gradedIndex 3 ≤ readingCells.gradedIndex 8 by decide
    have m4 : (4 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 8) :=
      show readingCells.gradedIndex 4 ≤ readingCells.gradedIndex 8 by decide
    have m5 : (5 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 8) :=
      show readingCells.gradedIndex 5 ≤ readingCells.gradedIndex 8 by decide
    have m6 : (6 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 8) :=
      show readingCells.gradedIndex 6 ≤ readingCells.gradedIndex 8 by decide
    have huniq : ∀ u : Fin 10, readingCells.gradedIndex u = readingCells.gradedIndex 8 → u = 8 := by
      decide
    have h85 := hT.le_of_le (d := ⟨8, self 8⟩) (d' := ⟨5, m5⟩) le_rfl le_rfl
    have h86 := hT.le_of_le (d := ⟨8, self 8⟩) (d' := ⟨6, m6⟩) le_rfl le_rfl
    have h58 := hav 5 8 h8 (by decide) rfl huniq
    have h68 := hav 6 8 h8 (by decide) rfl huniq
    simp only [min_self] at h85 h86
    have hw85 : w 8 = w 5 := le_antisymm (h85.trans (min_le_left _ _)) h58
    have hw86 : w 8 = w 6 := le_antisymm (h86.trans (min_le_left _ _)) h68
    have h34 := hT.le_of_le (d := ⟨3, m3⟩) (d' := ⟨4, m4⟩) le_rfl le_rfl
    have h43 := hT.le_of_le (d := ⟨4, m4⟩) (d' := ⟨3, m3⟩) le_rfl le_rfl
    have heq : min (w 3) (w 8) = min (w 4) (w 8) := le_antisymm h34 h43
    rw [hw85] at heq
    exact ⟨hw85, hw86.symm.trans hw85, heq⟩
  have h35 : (5 : Fin 10) ∈ readingCells.below X → (3 : Fin 10) ∈ readingCells.below X :=
    fun h5 ↦ mem_below_of_le h5 (by decide)
  have h46 : (6 : Fin 10) ∈ readingCells.below X → (4 : Fin 10) ∈ readingCells.below X :=
    fun h6 ↦ mem_below_of_le h6 (by decide)
  refine ⟨if (3 : Fin 10) ∈ readingCells.below X then w 3 else w 4,
    if (4 : Fin 10) ∈ readingCells.below X then w 4 else w 3,
    if (5 : Fin 10) ∈ readingCells.below X then w 5 else w 6, ⟨?_, ?_, ?_, ?_, ?_⟩,
    fun d ↦ ?_, fun h5 h6 ↦ ?_⟩
  -- the clauses of `IsReadingTriple`: self-visibility, `A ≤ E`, `min A B = min E B`
  · split_ifs
    exacts [hsv 3, hsv 4]
  · split_ifs
    exacts [hsv 4, hsv 3]
  · split_ifs
    exacts [hsv 5, hsv 6]
  · by_cases h3 : (3 : Fin 10) ∈ readingCells.below X <;>
      by_cases h4 : (4 : Fin 10) ∈ readingCells.below X <;> simp only [h3, h4, ↓reduceIte]
    · exact (h7 (mem_seven h3 h4)).2
    · exact le_rfl
    · exact le_rfl
    · rw [hout 4 h4, hout 3 h3]
  · by_cases h5 : (5 : Fin 10) ∈ readingCells.below X
    · have h3 := h35 h5
      by_cases h4 : (4 : Fin 10) ∈ readingCells.below X
      · simp only [h3, h4, h5, ↓reduceIte]
        exact (h8 (mem_eight h4 h5)).2.2
      · simp only [h3, h4, h5, ↓reduceIte]
    · by_cases h6 : (6 : Fin 10) ∈ readingCells.below X
      · -- the new cap without the cap: the reference cell is absent, so `A = E`
        have h3 : (3 : Fin 10) ∉ readingCells.below X := fun h3 ↦ h5 (mem_five h3 h6)
        simp only [h3, h46 h6, h5, ↓reduceIte]
      · simp only [h5, ↓reduceIte]
        rw [hout 6 h6, min_bot_right, min_bot_right]
  · -- the labelling, cell by cell
    obtain ⟨d, hd⟩ := d
    rw [← CellScheme.Rows.extendBot_of_mem r hd]
    -- the left side is `w d`, the extension of `r` by `⊥` at a cell below `X`
    change w d = _
    rcases cellKind_cases d with h0 | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hdead d h0, topLabel_of_kind_zero h0]
    · -- `topLabel` at the reference cell is the first parameter
      change _ = if (3 : Fin 10) ∈ readingCells.below X then w 3 else w 4
      rw [ite_eq_left hd]
    · -- `topLabel` at the new cell is the second parameter
      change _ = if (4 : Fin 10) ∈ readingCells.below X then w 4 else w 3
      rw [ite_eq_left hd]
    · -- `topLabel` at the cell `7` is the second parameter
      change _ = if (4 : Fin 10) ∈ readingCells.below X then w 4 else w 3
      rw [ite_eq_left (mem_below_of_le hd (by decide)), (h7 hd).1]
    · -- `topLabel` at the cap is the third parameter
      change _ = if (5 : Fin 10) ∈ readingCells.below X then w 5 else w 6
      rw [ite_eq_left hd]
    · -- `topLabel` at the new cap is the third parameter
      change _ = if (5 : Fin 10) ∈ readingCells.below X then w 5 else w 6
      by_cases h5 : (5 : Fin 10) ∈ readingCells.below X
      · rw [ite_eq_left h5]
        exact (h8 (mem_eight (h46 hd) h5)).2.1
      · simp only [h5, ↓reduceIte]
    · -- `topLabel` at the reading cell is the third parameter
      change _ = if (5 : Fin 10) ∈ readingCells.below X then w 5 else w 6
      rw [ite_eq_left (mem_below_of_le hd (by decide)), (h8 hd).1]
  · -- neither the cap nor the new cap below `X`
    simp only [h5, ↓reduceIte]
    exact hout 6 h6

end Below

/-! ### Legality -/

/-- **Every pair lifts capped**: prescribed parameters are kept, the others lifted by
`exists_isReadingTriple_lift_top`, and the labelling of the lifted parameters is lawful. -/
theorem cappedLift_topScheme {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y) :
    topScheme.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨pA, pE, pB, hpT, hpX, -⟩ := exists_of_isLawfulBelow hp
  obtain ⟨qA, qE, qB, hqT, hqY, hq5⟩ := exists_of_isLawfulBelow hq
  have hagree {d : Fin 10} (hd : d ∈ readingCells.below X) :
      min (topLabel pA pE pB d) c = min (topLabel qA qE qB d) c := by
    have := hpq ⟨d, hd⟩
    rw [hpX, hqY] at this
    exact this.symm
  have hc2 : IsSelfVisible 2 c ∨ qB = ⊥ := by
    by_cases h5 : (5 : Fin 10) ∈ readingCells.below Y
    · exact .inl (hc.mono h5.2)
    by_cases h6 : (6 : Fin 10) ∈ readingCells.below Y
    · exact .inl (hc.mono h6.2)
    exact .inr (hq5 h5 h6)
  obtain ⟨rA, rE, rB, hrT, hrA, hrE, hrB, hcA, hcE, hcB⟩ :=
    exists_isReadingTriple_lift_top (xa := (3 : Fin 10) ∈ readingCells.below X)
      (xe := (4 : Fin 10) ∈ readingCells.below X)
      (xb := (5 : Fin 10) ∈ readingCells.below X ∨ (6 : Fin 10) ∈ readingCells.below X)
      hpT hqT hc2
      (fun h56 ↦ h56.elim (fun h5 ↦ .inl (mem_below_of_le h5 (by decide)))
        fun h6 ↦ .inr (mem_below_of_le h6 (by decide)))
      hagree hagree (fun h56 ↦ h56.elim hagree hagree)
  refine ⟨fun d ↦ topLabel rA rE rB d.1,
    (isLawful_topLabel hrT).isLawfulBelow Y, fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hqY]
    obtain ⟨d, hd⟩ := d
    -- the restriction to `Y` at the cell `d`
    change min (topLabel rA rE rB d) c = min (topLabel qA qE qB d) c
    rcases cellKind_cases d with h0 | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [topLabel_of_kind_zero h0, topLabel_of_kind_zero h0]
    exacts [hcA, hcE, hcE, hcB, hcB, hcB]
  · obtain ⟨d, hd⟩ := d
    rw [hpX]
    -- the restriction to `X` at the cell `d`
    change topLabel rA rE rB d = topLabel pA pE pB d
    rcases cellKind_cases d with h0 | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [topLabel_of_kind_zero h0, topLabel_of_kind_zero h0]
    · exact hrA hd
    · exact hrE hd
    · exact hrE (mem_below_of_le hd (by decide))
    · exact hrB (.inl hd)
    · exact hrB (.inr hd)
    · exact hrB (.inl (mem_below_of_le hd (by decide)))

/-- **The scheme with a new cap is legal.** -/
theorem isLegal_topScheme : topScheme.{u}.IsLegal where
  -- well formed: the interval plan, each scope a face, each grade at most the size of the scope
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 10, readingCells.scope d ∈ readingCells.faces ∧
        0 < readingCells.grade d ∧ readingCells.grade d ≤ #(readingCells.scope d) := by decide
    exact key d⟩⟩
  -- coded: each row entry is `⊥` or a grid point below `ω ^ 2`
  isCoded s t := by
    have key : ∀ s d : Fin 7, kindRow.{u} s d = ⊥ ∨ kindRow.{u} s d = gridPoint 1 0 ∨
        kindRow.{u} s d = gridPoint 1 1 ∨ kindRow.{u} s d = gridPoint 2 1 := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [kindRow]
    rw [topScheme_row]
    rcases key (cellKind s) (cellKind t.1) with h | h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    all_goals exact gridPoint_lt_omega0_sq _ _
  -- consistent: each row is the labelling of one of four reading triples, `h0` at the dead
  -- cells, `h1` at the reference cell and the new cell, `h2` at the caps and the reading cell,
  -- `h3` at the cell `7`
  isConsistent s := by
    have hrow {A E B : Label.{u}} (hT : IsReadingTriple A E B)
        (h : ∀ d : Fin 10, readingCells.gradedIndex d ≤ readingCells.gradedIndex s →
          kindRow (cellKind s) (cellKind d) = topLabel A E B d) :
        topScheme.{u}.rows.IsLawfulBelow (readingCells.gradedIndex s)
          (topScheme.{u}.rows.row s) := by
      have : topScheme.{u}.rows.row s = fun d ↦ topLabel A E B d.1 :=
        funext fun d ↦ h d.1 d.2
      rw [this]
      exact (isLawful_topLabel hT).isLawfulBelow _
    have h0 : IsReadingTriple.{u} ⊥ ⊥ ⊥ :=
      ⟨isSelfVisible_bot _, isSelfVisible_bot _, isSelfVisible_bot _, le_rfl, rfl⟩
    have h1 : IsReadingTriple.{u} (gridPoint 1 0) (gridPoint 1 0) ⊥ :=
      ⟨isSelfVisible_gridPoint 1 0, isSelfVisible_gridPoint 1 0, isSelfVisible_bot _, le_rfl, rfl⟩
    have h2 : IsReadingTriple.{u} (gridPoint 1 0) (gridPoint 1 0) (gridPoint 2 1) :=
      ⟨isSelfVisible_gridPoint 1 0, isSelfVisible_gridPoint 1 0, isSelfVisible_gridPoint 2 1,
        le_rfl, rfl⟩
    have h3 : IsReadingTriple.{u} (gridPoint 1 0) (gridPoint 1 1) ⊥ :=
      ⟨isSelfVisible_gridPoint 1 0, isSelfVisible_gridPoint 1 1, isSelfVisible_bot _,
        gridPoint_le_gridPoint.mpr (by omega), by rw [min_bot_right, min_bot_right]⟩
    fin_cases s
    · refine hrow h0 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h0 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h0 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h1 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h1 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h3 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h0 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
  isBountiful _ _ _ _ h := cappedLift_topScheme h
  -- complete: one cell at each graded face
  isComplete X hX := by
    obtain ⟨B, j⟩ := X
    obtain ⟨hB, hj0, hjB⟩ := hX
    have hj3 : j ≤ 3 := hjB.trans (by simpa using card_le_univ B)
    have key : ∀ B : Finset (Fin 3), B ∈ readingCells.faces → ∀ j : Fin 4, 0 < (j : ℕ) →
        (j : ℕ) ≤ #B → ∃ d : Fin 10, readingCells.gradedIndex d = (B, (j : ℕ)) := by decide
    exact key B hB ⟨j, by omega⟩ hj0 hjB

/-! ### The labelled schemes -/

variable (ξ : Ordinal.{u})

/-- The cap label `λ_ξ + 2`, a proper ordinal. -/
noncomputable abbrev capLabel : Label.{u} :=
  ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

/-- The cap label is self-visible at `2`. -/
theorem isSelfVisible_capLabel : IsSelfVisible 2 (capLabel ξ) :=
  isSelfVisible_coe_add (isSuccPrelimit_blockStage ξ) le_rfl

/-- The cap label occurs at `λ_{ξ+1}`. -/
theorem capLabel_lt : capLabel ξ < ((blockStage (ξ + 1) : Ordinal.{u}) : Label.{u}) := by
  rw [blockStage_add_one]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    (add_lt_add_right (natCast_lt_omega0 2) _))

/-- The parameters of the context: the marker at the reference cell and the new cell, the cap
label `λ_ξ + 2` at the caps. -/
theorem isReadingTriple_capLabel : IsReadingTriple (markerLabel ξ) (markerLabel ξ) (capLabel ξ) :=
  ⟨isSelfVisible_markerLabel ξ, isSelfVisible_markerLabel ξ, isSelfVisible_capLabel ξ, le_rfl, rfl⟩

/-- The **labelled scheme** with parameters `A`, `E`, `B` occurring at `λ_{ξ+1}`. -/
noncomputable def topType {A E B : Label.{u}} (hT : IsReadingTriple A E B)
    (hA : AtStage (blockStage (ξ + 1)) A) (hE : AtStage (blockStage (ξ + 1)) E)
    (hB : AtStage (blockStage (ξ + 1)) B) : StageType.{u} (blockStage (ξ + 1)) 3 where
  toScheme := topScheme
  label := topLabel A E B
  isWellFormed := isLegal_topScheme.isWellFormed
  isCoded := isLegal_topScheme.isCoded
  isLawful := isLawful_topLabel hT
  atStage d := by
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    simp only [topLabel, hk]
    fin_cases k
    exacts [atStage_bot, hA, hE, hE, hB, hB, hB]

/-- The marker occurs at `λ_{ξ+1}`. -/
private theorem atStage_markerLabel : AtStage (blockStage (ξ + 1)) (markerLabel ξ) :=
  .inl (markerLabel_lt ξ)

/-- The **labelled scheme of the context**: the marker `λ_ξ + 1` at the reference cell, the new
cell and the cell `(univ, 1)`, and the proper cap label `λ_ξ + 2` at the caps and the reading
cell. -/
noncomputable def capType : StageType.{u} (blockStage (ξ + 1)) 3 :=
  topType ξ (isReadingTriple_capLabel ξ) (atStage_markerLabel ξ) (atStage_markerLabel ξ)
    (.inl (capLabel_lt ξ))

/-- The **labelled scheme of the donor**: the marker `λ_ξ + 1` at the reference cell, the new cell
and the cell `(univ, 1)`, and the formal top at the caps and the reading cell. -/
noncomputable def sourceType : StageType.{u} (blockStage (ξ + 1)) 3 :=
  topType ξ (isReadingTriple_marker ξ) (atStage_markerLabel ξ) (atStage_markerLabel ξ) atStage_top

/-! ### The context, the donor, and the root -/

/-- The first two points span a closed face, the context. -/
theorem map_castSuccEmb_mem_faces :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ readingCells.faces := by
  decide

/-- The root followed by the new point spans `{1, 2}`. -/
theorem map_extendByLast_eq :
    univ.map (extendByLast rootEmb) = ({1, 2} : Finset (Fin 3)) := by
  decide

/-- The root and the new point span a closed face, the face of the donor. -/
theorem map_extendByLast_mem_faces : univ.map (extendByLast rootEmb) ∈ readingCells.faces := by
  rw [map_extendByLast_eq]
  decide

/-- The root, as a point of the scheme, spans a closed face. -/
theorem map_rootEmb_mem_faces :
    univ.map (rootEmb.trans (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) ∈ readingCells.faces := by
  decide

/-- The **context type** `T⁺` on two points: the face of `capType` along the first two points. -/
noncomputable def contextType : StageType.{u} (blockStage (ξ + 1)) 2 :=
  (capType ξ).comap Fin.castSuccEmb map_castSuccEmb_mem_faces

/-- The **donor** on two points: the face of `sourceType` along the root followed by the new
point. -/
noncomputable def donorType : StageType.{u} (blockStage (ξ + 1)) 2 :=
  (sourceType ξ).comap (extendByLast rootEmb) map_extendByLast_mem_faces

/-- The **root** on one point: the face of the context type along the root embedding. -/
noncomputable def rootType : StageType.{u} (blockStage (ξ + 1)) 1 :=
  (contextType ξ).comap rootEmb
    (((capType ξ).map_univ_mem_comap_faces_iff _ _ _).mpr map_rootEmb_mem_faces)

/-- The context type is the face of `capType` along the first two points. -/
theorem restrictFace_contextType :
    restrictFace Fin.castSuccEmb (capType ξ) = some (contextType ξ) :=
  restrictFace_of_mem _ _ _

/-- The root is the face of the context type along the root embedding. -/
theorem restrictFace_rootType : restrictFace rootEmb (contextType ξ) = some (rootType ξ) :=
  restrictFace_of_mem _ _ _

/-- The context type is legal. -/
theorem isLegal_contextType : (contextType ξ).IsLegal :=
  isLegal_topScheme.comap _ map_castSuccEmb_mem_faces

/-- The only cell visible through the root is the dead cell `({1}, 1)`. -/
private theorem cellMap_root_eq {i} :
    topScheme.{u}.cellMap (rootEmb.trans (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) i = 1 := by
  have hvis := topScheme.{u}.cellMap_mem (rootEmb.trans (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) i
  generalize topScheme.{u}.cellMap (rootEmb.trans (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) i = d at hvis
  have hu : univ.map (rootEmb.trans (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) = ({1} : Finset (Fin 3)) :=
    by decide
  rw [Scheme.visibleCells, Finset.mem_filter, hu] at hvis
  have key : ∀ d : Fin 10, readingCells.scope d ⊆ ({1} : Finset (Fin 3)) → d = 1 := by decide
  exact key d hvis.2

/-- The label of the dead cell `({1}, 1)`. -/
private theorem topLabel_one (A E B : Label.{u}) : topLabel A E B 1 = ⊥ :=
  rfl

/-- **The two labelled schemes have the same root**: their faces along the root are the one dead
cell `({1}, 1)`.  (The comparison goes through the cell `1`, never through the two labellings,
whose ordinal labels differ.) -/
theorem restrictFace_sourceType_root :
    restrictFace (rootEmb.trans Fin.castSuccEmb) (sourceType ξ) =
      restrictFace (rootEmb.trans Fin.castSuccEmb) (capType ξ) := by
  rw [restrictFace_of_mem _ _ map_rootEmb_mem_faces, restrictFace_of_mem _ _ map_rootEmb_mem_faces]
  have key : ∀ i j : Fin (topScheme.{u}.comap (rootEmb.trans Fin.castSuccEmb)).card,
      topLabel (markerLabel ξ) (markerLabel ξ) ⊤
          (topScheme.{u}.cellMap (rootEmb.trans Fin.castSuccEmb) i) =
        topLabel (markerLabel ξ) (markerLabel ξ) (capLabel ξ)
          (topScheme.{u}.cellMap (rootEmb.trans Fin.castSuccEmb) j) := fun i j ↦ by
    rw [cellMap_root_eq, cellMap_root_eq, topLabel_one, topLabel_one]
  refine congrArg some (StageType.ext ?_ fun i j _ ↦ key i j)
  -- both faces are on the face of `topScheme` along the root
  exact (show topScheme.{u}.comap (rootEmb.trans Fin.castSuccEmb) =
    topScheme.{u}.comap (rootEmb.trans Fin.castSuccEmb) from rfl)

/-- The donor is a coface of the root. -/
theorem donorType_mem_cofaces : donorType ξ ∈ (rootType ξ).cofaces := by
  refine ⟨isLegal_topScheme.comap _ map_extendByLast_mem_faces, ?_⟩
  unfold donorType
  rw [restrictFace_trans _ _ _ (restrictFace_of_mem (sourceType ξ) _ map_extendByLast_mem_faces),
    castSuccEmb_trans_extendByLast, restrictFace_sourceType_root,
    ← restrictFace_trans _ _ _ (restrictFace_contextType ξ), restrictFace_rootType]

/-- The cells of the context type are the cells of the scheme visible through the first two
points. -/
private theorem exists_cellMap_castSuccEmb {d : Fin 10}
    (hd : d ∈ topScheme.{u}.visibleCells Fin.castSuccEmb) :
    ∃ b, topScheme.{u}.cellMap Fin.castSuccEmb b = d := by
  have : d ∈ Set.range (topScheme.{u}.cellMap Fin.castSuccEmb) := by
    rw [Scheme.range_cellMap]
    exact hd
  exact this

/-- The cap: the cell of the context type at the cell `5` of the scheme, of grade `2`, labelled
`λ_ξ + 2`. -/
theorem exists_cap : ∃ b : Fin (contextType ξ).card,
    topScheme.{u}.cellMap Fin.castSuccEmb b = 5 ∧
      (contextType ξ).toCellScheme.grade b = 2 ∧ (contextType ξ).label b = capLabel ξ := by
  obtain ⟨b, hb⟩ := exists_cellMap_castSuccEmb.{u} (d := 5) (by decide)
  refine ⟨b, hb, ?_, ?_⟩
  · -- the grade of a cell of the face is the grade of its image
    change readingCells.grade (topScheme.{u}.cellMap Fin.castSuccEmb b) = 2
    rw [hb]
    rfl
  · -- the label of a cell of the face is the label of its image
    change topLabel (markerLabel ξ) (markerLabel ξ) (capLabel ξ)
      (topScheme.{u}.cellMap Fin.castSuccEmb b) = capLabel ξ
    rw [hb]
    rfl

/-- The reference cell (the marker): the cell of the context type at the cell `3` of the scheme,
of grade `1`, labelled `λ_ξ + 1`. -/
theorem exists_marker : ∃ a : Fin (contextType ξ).card,
    topScheme.{u}.cellMap Fin.castSuccEmb a = 3 ∧
      (contextType ξ).toCellScheme.grade a = 1 ∧ (contextType ξ).label a = markerLabel ξ := by
  obtain ⟨a, ha⟩ := exists_cellMap_castSuccEmb.{u} (d := 3) (by decide)
  refine ⟨a, ha, ?_, ?_⟩
  · -- the grade of a cell of the face is the grade of its image
    change readingCells.grade (topScheme.{u}.cellMap Fin.castSuccEmb a) = 1
    rw [ha]
    rfl
  · -- the label of a cell of the face is the label of its image
    change topLabel (markerLabel ξ) (markerLabel ξ) (capLabel ξ)
      (topScheme.{u}.cellMap Fin.castSuccEmb a) = markerLabel ξ
    rw [ha]
    rfl

/-- The labels of the donor's labelled scheme are `⊥`, the marker, or the formal top. -/
private theorem topLabel_marker_cases (d : Fin 10) :
    topLabel (markerLabel ξ) (markerLabel ξ) ⊤ d = ⊥ ∨
      topLabel (markerLabel ξ) (markerLabel ξ) ⊤ d = markerLabel ξ ∨
      topLabel (markerLabel ξ) (markerLabel ξ) ⊤ d = ⊤ := by
  fin_cases d <;> simp [topLabel, kindValue, cellKind]

/-- `γ = λ_ξ + 1` lies below `λ_ξ + 2`. -/
private theorem one_lt_two_add :
    blockStage ξ + ((1 : ℕ) : Ordinal.{u}) < blockStage ξ + ((2 : ℕ) : Ordinal.{u}) :=
  add_lt_add_right (Nat.cast_lt.mpr (by omega)) _

/-- **The context type satisfies the graded cap calibration** for the root embedding, the donor
and `γ = λ_ξ + 1`: the cap has grade `2 > 1` and the proper label `λ_ξ + 2`, and
`λ_ξ + 1 < λ_ξ + 2`; the only ordinal label of the donor is `λ_ξ + 1`, with the marker as its
reference cell. -/
theorem gradedCapCalibration_contextType :
    GradedCapCalibration ξ (contextType ξ) rootEmb (donorType ξ)
      (blockStage ξ + ((1 : ℕ) : Ordinal.{u})) := by
  obtain ⟨b, -, hbg, hbl⟩ := exists_cap ξ
  obtain ⟨a, -, hag, hal⟩ := exists_marker ξ
  refine ⟨b, by rw [hbl, hbg], by rw [hbg]; omega, ?_, fun j o ho ↦ ?_⟩
  · rw [hbg]
    exact one_lt_two_add ξ
  · have hj : (donorType ξ).label j = topLabel (markerLabel ξ) (markerLabel ξ) ⊤
        (topScheme.{u}.cellMap (extendByLast rootEmb) j) := rfl
    rcases topLabel_marker_cases ξ (topScheme.{u}.cellMap (extendByLast rootEmb) j)
      with h | h | h <;> rw [← hj, ho] at h
    · exact absurd h WithBot.coe_ne_bot
    · obtain rfl : o = blockStage ξ + ((1 : ℕ) : Ordinal.{u}) :=
        WithTop.coe_injective (WithBot.coe_injective h)
      refine ⟨blockStage ξ, 1, 1, a, isSuccPrelimit_blockStage ξ, rfl, ?_, ?_, ?_, hal⟩
      · rw [hbg]; omega
      · rw [hbg]; omega
      · rw [hag, hbg]; omega
    · exact absurd h (by simp)

/-- The new cell of the donor labelled the formal top: the cell at the new cap `6` of the scheme,
whose scope contains the new point. -/
theorem exists_topCell : ∃ j : Fin (donorType ξ).card,
    Fin.last 1 ∈ (donorType ξ).toCellScheme.scope j ∧ (donorType ξ).label j = ⊤ := by
  have : (6 : Fin 10) ∈ Set.range (topScheme.{u}.cellMap (extendByLast rootEmb)) := by
    rw [Scheme.range_cellMap, Finset.mem_coe, Scheme.visibleCells, Finset.mem_filter,
      map_extendByLast_eq]
    decide
  obtain ⟨j, hj⟩ := this
  refine ⟨j, ?_, ?_⟩
  · -- the scope of a cell of the face is the preimage of the scope of its image
    change Fin.last 1 ∈ (readingCells.scope
      (topScheme.{u}.cellMap (extendByLast rootEmb) j)).preimage (extendByLast rootEmb)
      (extendByLast rootEmb).injective.injOn
    rw [hj, Finset.mem_preimage, extendByLast_last]
    decide
  · -- the label of a cell of the face is the label of its image
    change topLabel (markerLabel ξ) (markerLabel ξ) ⊤
      (topScheme.{u}.cellMap (extendByLast rootEmb) j) = ⊤
    rw [hj]
    rfl

/-- The new cells of the donor: a cell of the scheme visible through the root and the new point
whose scope contains the new point is one of the cells `2`, `4`, `6`. -/
private theorem eq_of_mem_newCells {d : Fin 10}
    (hd : d ∈ topScheme.{u}.visibleCells (extendByLast rootEmb))
    (h2 : (2 : Fin 3) ∈ readingCells.scope d) : d = 2 ∨ d = 4 ∨ d = 6 := by
  rw [Scheme.visibleCells, Finset.mem_filter, map_extendByLast_eq] at hd
  have key : ∀ d : Fin 10, readingCells.scope d ⊆ ({1, 2} : Finset (Fin 3)) →
      (2 : Fin 3) ∈ readingCells.scope d → d = 2 ∨ d = 4 ∨ d = 6 := by decide
  exact key d hd.2 h2

/-! ### The recovery -/

/-- **The scheme with a new cap is a stable recovery scheme** for the context type (cap `λ_ξ + 2`),
the root embedding, the donor (with a new cell labelled the formal top) and `γ = λ_ξ + 1`, by
`StageType.IsStableRecoveryScheme.of_readsThroughCap` at the reading cell `8`, the only cell of
`(univ, 2)`: it reads the new cell `2` (labelled `⊥`) as `⊥`, the new cell `4` (labelled
`λ_ξ + 1`) at `1`, where it reads the marker, and the new cap `6` (labelled the formal top) as it
reads the cap. -/
theorem isStableRecoveryScheme_topScheme :
    (contextType ξ).IsStableRecoveryScheme rootEmb (donorType ξ)
      (blockStage ξ + ((1 : ℕ) : Ordinal.{u})) topScheme := by
  obtain ⟨b, hb, hbg, hbl⟩ := exists_cap ξ
  obtain ⟨a, ha, -, hal⟩ := exists_marker ξ
  refine IsStableRecoveryScheme.of_readsThroughCap (restrictFace_rootType ξ)
    (donorType_mem_cofaces ξ)
    ⟨(capType ξ).reduce (isSuccPrelimit_blockStage ξ), ⟨isLegal_topScheme, ?_⟩, rfl⟩
    map_extendByLast_mem_faces rfl (b := b) (b₀ := b) rfl ?_ ?_ (s := 8) ?_ ?_ ?_
  · rw [restrictFace_reduce, restrictFace_contextType]
    rfl
  · rw [hb, hbl]
    exact le_rfl
  · rw [hb]
    exact one_lt_two_add ξ
  · rw [hb]
    exact show readingCells.gradedIndex 5 ≤ readingCells.gradedIndex 8 by decide
  · rw [hb]
    rfl
  intro i j hij hj
  obtain rfl : i = j := Fin.ext hij
  have h2 : (2 : Fin 3) ∈ readingCells.scope (topScheme.{u}.cellMap (extendByLast rootEmb) i) := by
    have : Fin.last 1 ∈ (readingCells.scope
        (topScheme.{u}.cellMap (extendByLast rootEmb) i)).preimage (extendByLast rootEmb)
        (extendByLast rootEmb).injective.injOn := hj
    rw [Finset.mem_preimage, extendByLast_last] at this
    exact this
  -- the label of the new cell `i` of `D` is the label of its image in `sourceType`
  change _ ∧ ∀ u, _ → (contextType ξ).ReadsThroughCap topScheme b u _
    (topLabel (markerLabel ξ) (markerLabel ξ) ⊤ (topScheme.{u}.cellMap (extendByLast rootEmb) i))
  have hvis := topScheme.{u}.cellMap_mem (extendByLast rootEmb) i
  generalize topScheme.{u}.cellMap (extendByLast rootEmb) i = d at h2 hvis ⊢
  have huniq : ∀ u : Fin 10, readingCells.gradedIndex u = readingCells.gradedIndex 8 → u = 8 := by
    decide
  rcases eq_of_mem_newCells hvis h2 with rfl | rfl | rfl
  · -- the new cell `2`, labelled `⊥`, read as `⊥`
    refine ⟨show readingCells.gradedIndex 2 ≤ readingCells.gradedIndex 8 by decide,
      fun u hu ↦ ?_⟩
    obtain rfl := huniq u hu
    exact fun _ _ ↦ ⟨fun _ ↦ rfl, fun h ↦ absurd h bot_ne_top,
      fun μ n _ h ↦ absurd h WithBot.bot_ne_coe⟩
  · -- the new cell `4`, labelled `λ_ξ + 1`, read at `1` with the marker
    refine ⟨show readingCells.gradedIndex 4 ≤ readingCells.gradedIndex 8 by decide,
      fun u hu ↦ ?_⟩
    obtain rfl := huniq u hu
    refine fun _ _ ↦ ⟨fun h ↦ absurd h WithBot.coe_ne_bot,
      fun h ↦ absurd (WithBot.coe_injective (h : markerLabel ξ = ⊤)) WithTop.coe_ne_top,
      fun μ n hμ h ↦ ?_⟩
    obtain rfl := eq_one_of_markerLabel_eq ξ hμ h
    have ha8 : topScheme.{u}.cellMap Fin.castSuccEmb a ∈
        readingCells.below (readingCells.gradedIndex 8) := by
      rw [ha]
      exact show readingCells.gradedIndex 3 ≤ readingCells.gradedIndex 8 by decide
    refine ⟨by rw [hb]; decide, a, a, 1, ((0 : ℕ) : Ordinal.{u}), rfl, hal.trans h,
      by rw [hb]; decide, ha8, ?_, rfl⟩
    -- the row of the reading cell, by kinds
    change kindRow (cellKind 8) (cellKind (topScheme.{u}.cellMap Fin.castSuccEmb a)) = _
    rw [ha]
    rfl
  · -- the new cap `6`, labelled the formal top, read as the cap
    refine ⟨show readingCells.gradedIndex 6 ≤ readingCells.gradedIndex 8 by decide,
      fun u hu ↦ ?_⟩
    obtain rfl := huniq u hu
    refine fun _ hb' ↦ ⟨fun h ↦ absurd h top_ne_bot, fun _ ↦ ?_,
      fun μ n _ h ↦ absurd (WithBot.coe_injective
        (show ((⊤ : WithTop Ordinal.{u}) : Label.{u}) = _ from h)) WithTop.top_ne_coe⟩
    -- the row of the reading cell, by kinds
    change kindRow (cellKind 8) (cellKind 6) =
      kindRow (cellKind 8) (cellKind (topScheme.{u}.cellMap Fin.castSuccEmb b))
    rw [hb]
    rfl

/-- **The formal top of the donor is recovered as the proper cap value**: in every stage type at
`λ_{ξ+1}` on the scheme with face `T⁺` along the first two points, the new cap `6` (labelled the
formal top in the donor) is labelled exactly `λ_ξ + 2`, the label of the cap of `T⁺`.  So the
clause on `γ` is met by a proper ordinal above `γ = λ_ξ + 1`, not by the formal top. -/
theorem label_newCap_eq (Q' : StageType.{u} (blockStage (ξ + 1)) 3)
    (hS : Q'.toScheme = topScheme) (hf : restrictFace Fin.castSuccEmb Q' = some (contextType ξ))
    (i : Fin Q'.card) (hi : (i : ℕ) = 6) : Q'.label i = capLabel ξ := by
  obtain ⟨S, ℓ, hwf, hcd, hlaw, hat⟩ := Q'
  obtain rfl : S = topScheme := hS
  obtain rfl : i = 6 := Fin.ext hi
  obtain ⟨b, hb, -, hbl⟩ := exists_cap ξ
  obtain ⟨_, hcT⟩ := (restrictFace_eq_some_iff _ _).mp hf
  -- the label at the cap `5` is the label of the cap of `T⁺`
  have h5 : ℓ 5 = capLabel ξ := by
    have := label_congr hcT (i := b) (j := b) rfl
    rw [hbl] at this
    rw [← hb]
    exact this
  -- the labelling is a labelling of a reading triple, where the cells `5` and `6` agree
  obtain ⟨A, E, B, -, hr, -⟩ := exists_of_isLawfulBelow (hlaw.isLawfulBelow (univ, 3))
  have h6 := hr ⟨6, show readingCells.gradedIndex 6 ≤ (univ, 3) by decide⟩
  have h5' := hr ⟨5, show readingCells.gradedIndex 5 ≤ (univ, 3) by decide⟩
  change ℓ 6 = B at h6
  change ℓ 5 = B at h5'
  exact h6.trans (h5'.symm.trans h5)

/-- **A stable recovery scheme for a donor with a new cell at the formal top, under a proper cap,
at every `ξ`**: a legal context type `T⁺` on two points with a cap of grade `2` labelled the proper
ordinal `λ_ξ + 2`, the embedding of a root on one point, a coface `D` of the root with a new cell
labelled the formal top, and `γ = λ_ξ + 1 < λ_{ξ+1}`, satisfying the graded cap calibration, with
a stable recovery scheme.  So the conclusion of
`StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds at this input, and
the hypotheses of `StageType.IsStableRecoveryScheme.of_readsThroughCap` are met there with the
clause at the formal top used. -/
theorem exists_isStableRecoveryScheme_topCell :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 2) (f : Fin 1 ↪ Fin 2)
      (P : StageType.{u} (blockStage (ξ + 1)) 1) (D : StageType.{u} (blockStage (ξ + 1)) 2)
      (γ : Ordinal.{u}), Tp.IsLegal ∧ restrictFace f Tp = some P ∧ D ∈ P.cofaces ∧
        γ < blockStage (ξ + 1) ∧ GradedCapCalibration ξ Tp f D γ ∧
        (∃ b : Fin Tp.card, Tp.label b = capLabel ξ ∧ Tp.toCellScheme.grade b = 2) ∧
        (∃ j : Fin D.card, Fin.last 1 ∈ D.toCellScheme.scope j ∧ D.label j = ⊤) ∧
        ∃ E : Scheme.{u} 3, Tp.IsStableRecoveryScheme f D γ E := by
  obtain ⟨b, -, hbg, hbl⟩ := exists_cap ξ
  refine ⟨contextType ξ, rootEmb, rootType ξ, donorType ξ, blockStage ξ + ((1 : ℕ) : Ordinal.{u}),
    isLegal_contextType ξ, restrictFace_rootType ξ, donorType_mem_cofaces ξ, ?_,
    gradedCapCalibration_contextType ξ, ⟨b, hbl, hbg⟩, exists_topCell ξ, topScheme,
    isStableRecoveryScheme_topScheme ξ⟩
  rw [blockStage_add_one]
  exact add_lt_add_right (natCast_lt_omega0 1) _

/-- The input lies in the binders of `StageType.HasStableRecoverySchemes`. -/
example (h : HasStableRecoverySchemes ξ (GradedCapCalibration ξ)) :
    ∃ E, (contextType ξ).IsStableRecoveryScheme rootEmb (donorType ξ)
      (blockStage ξ + ((1 : ℕ) : Ordinal.{u})) E :=
  h (contextType ξ) rootEmb (rootType ξ) (isLegal_contextType ξ) one_pos
    (restrictFace_rootType ξ) _ (donorType_mem_cofaces ξ) _
    (by rw [blockStage_add_one]; exact add_lt_add_right (natCast_lt_omega0 1) _)
    (gradedCapCalibration_contextType ξ)

end VaughtConjecture.Continuation.StableRecoveryTopCell
