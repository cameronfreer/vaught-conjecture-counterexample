/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecovery
import VaughtConjecture.Extension.OrderedRow

/-!
# A stable recovery scheme reading through the cap

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap, the marker and the decoder of (R4)); semantic contract, item 8.

**The question.**  (R4) follows from stable recovery schemes for the graded cap calibration at
every `ξ < ω₁` (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`, in
`VaughtConjecture.Continuation.StableRecovery`), a finite statement that is open, and a scheme
with a cell `s` of the grade `N` of a cap, every cell of whose graded index reads the new cells of
the donor through the cap and reference cells, is a stable recovery scheme
(`StageType.IsStableRecoveryScheme.of_readsThroughCap`).  This file compiles an instance of the
hypotheses of that theorem, at every `ξ`, with the smallest sizes the calibration allows: a root
of one point (`k = 1`), a context `T⁺` of two points, a cap of grade `N = 2`, and a donor with a new
cell labelled `λ_ξ + 1`.  So the sufficient condition is satisfiable with a proper new label, and
the conclusion of `StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds
at this input (`exists_isStableRecoveryScheme_gradedCap`).  The finite statement at every input is
not proved, and (R4) is not proved.

**The scheme** (`readingScheme`).  Three points: `0` (the private point), `1` (the root) and `2`
(the new point); the faces are the intervals of `0 < 1 < 2`, so `{0, 1}` (the context) and
`{1, 2}` (the root and the new point) are faces.  There is one cell at each graded face, ten in
all.  Five are **dead** (row `⊥`, so labelled `⊥` in every lawful labelling): `({0}, 1)`,
`({1}, 1)`, `({2}, 1)`, `({1, 2}, 2)` and `(univ, 3)`.  The others, with their rows (values `1`,
`ω + 1`, `ω + 2`, coded):

* the **reference cell** `3` at `({0, 1}, 1)`, reading itself at `1`;
* the **new cell** `4` at `({1, 2}, 1)`, reading itself at `1`;
* the **cap** `5` at `({0, 1}, 2)`, reading the reference cell at `1` and itself at `ω + 2`;
* the cell `7` at `(univ, 1)`, reading the reference cell at `1`, the new cell and itself at
  `ω + 1`;
* the **reading cell** `8` at `(univ, 2)`, reading the reference cell, the new cell and the cell
  `7` at `1`, and the cap and itself at `ω + 2`.

**Its lawful labellings** (`isLawful_readingLabel`, `exists_of_isLawfulBelow`).  Below every pair
they are exactly the labellings `readingLabel A E B` (`⊥` at the dead cells, `A` at the reference
cell, `E` at the new cell and the cell `7`, `B` at the cap and the reading cell) of the **reading
triples** (`IsReadingTriple`): `A` and `E` self-visible at `1`, `B` at `2`, `A ≤ E` (locality and
availability at the cell `7`), and `min A B = min E B` (locality at the reading cell, which reads
the reference cell and the new cell at one value).  Below a pair without the cap, `B` may be taken
`⊥`.  The witnesses are the shifters of the ordered rows of the thin completion
(`ThinCompletion.blockConst`, `ThinCompletion.twoStrip`).

**The cap decodes the new cell** (`IsReadingTriple.eq_of_lt`, `isReadingTriple_of_le`): a cap
above the reference cell forces `E = A`, and a cap at most the reference cell leaves `E` free
above `A` (for `A` and `E` self-visible at `1` and the cap self-visible at `2`, every `E ≥ A`
gives a reading triple).  So the new cell is recovered through the cap, as in the decoder at one
reading cell (`CellScheme.Rows.IsLawful.label_eq_of_reading`), not from the face of the context
alone.

**Legality** (`isLegal_readingScheme`): well formed (the interval plan), coded, consistent (each
row is the reading labelling of a reading triple), complete (one cell at each graded face), and
bountiful: every pair lifts capped (`cappedLift_readingScheme`), since the parameters of the
prescribed labelling below the smaller pair are kept and the others lifted, agreeing with the
ambient labelling capped at the cap (`exists_isReadingTriple_lift`, a case analysis on which of
the reference cell, the new cell and the cap lie below the smaller pair).

**The input** (`contextType`, `rootEmb`, `rootType`, `donorType`, `γ = λ_ξ`).  The reading type
(`readingType`) labels the reading triple `(λ_ξ + 1, λ_ξ + 1, ⊤)` at `λ_{ξ+1}`.  The context type
`T⁺` is its face along `{0, 1}`: `⊥, ⊥` at the dead cells, the marker `λ_ξ + 1` at the reference
cell (grade `1`), and the formal top at the cap (grade `2`).  The root is the face along `{1}`, one
dead cell, and the donor `D` the face along `{1, 2}`: `⊥` at its new cells `({2}, 1)` and
`({1, 2}, 2)`, and `λ_ξ + 1` at the new cell `({1, 2}, 1)`.  The graded cap calibration holds
(`gradedCapCalibration_contextType`): `N = 2 > k = 1`, the cap is labelled the formal top, at least
`λ_ξ + 2`, `γ = λ_ξ < λ_ξ + 2`, and the only ordinal label `λ_ξ + 1` of `D` has finite part
`1 < 2`, with the marker as reference cell.  The reading scheme is a stable recovery scheme for
these data (`isStableRecoveryScheme_readingScheme`), by `of_readsThroughCap` at the reading cell,
the only cell of `(univ, 2)`; the coface of `T⁺↓λ_ξ` is the reduction of the reading type to
`λ_ξ`.

**What this does not show.**  `StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration
ξ)` asks for a stable recovery scheme at every legal `T⁺`, embedding, coface `D` and `γ` with the
calibration; it is proved here at one input only, and stays open.  (Informal; not compiled: by
bountifulness and completeness the reading constrains every graded face of grade `N` containing
the cap, a reference cell and a new cell; here the reading constrains no other graded face, since
`(univ, 2)` is the only graded face of grade `2` containing both the cap and the new cell; and the
new cells read as `⊥` are dead, so no lawful labelling of the donor's face raises them.)

The input is degenerate, so it shows that reading through the cap is feasible, with a legal
(bountiful) scheme, at the smallest sizes only:

* recovery copies the marker: in every lawful labelling with the marker at the reference cell `3`
  and the formal top at the cap, the new cell equals the marker (`IsReadingTriple.eq_of_lt`), so
  the new label is the reference label (`n = i = 1`, `c = 0` in `StageType.ReadsThroughCap`) and
  the reading cell reads both at the same value `1`;
* no label of `D` is the formal top, so the clause on `γ` of `StageType.IsStableRecoveryScheme`
  and the branch at the formal top of `StageType.ReadsThroughCap` are not used;
* the root is one cell, labelled `⊥`, so recovery at the old cells is immediate;
* `N = k + 1`.

The next test is the twin donor of `Continuation.StableRecoveryCounterexample` (finite parts `1`
and `2`, so `N ≥ 3`; `E` on at least four points; several graded faces of grade `N` containing the
cap and the new cells) (informal; not compiled).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryReading

open Finset Label StageType ThinCompletion
open Ordinal hiding univ

/-! ### The scheme -/

/-- The cells of the reading scheme on `Fin 3`, with faces the intervals of `0 < 1 < 2`: one cell at
each graded face, the cells `0`–`9` at `({0}, 1)`, `({1}, 1)`, `({2}, 1)`, `({0, 1}, 1)`,
`({1, 2}, 1)`, `({0, 1}, 2)`, `({1, 2}, 2)`, `(univ, 1)`, `(univ, 2)`, `(univ, 3)`. -/
def readingCells : CellScheme (Fin 10) (Fin 3) :=
  ⟨univ, Geometry.intervalPlan univ,
    ![{0}, {1}, {2}, {0, 1}, {1, 2}, {0, 1}, {1, 2}, univ, univ, univ],
    ![1, 1, 1, 1, 1, 2, 2, 1, 2, 3]⟩

/-- The kind of each cell: `0` dead, `1` the reference cell, `2` the new cell, `3` the cell at
`(univ, 1)`, `4` the cap, `5` the reading cell. -/
private def cellKind : Fin 10 → Fin 6 := ![0, 0, 0, 1, 2, 4, 0, 3, 5, 0]

/-- The rows, by the kind of the cell and the kind of the cell read: the grid points `1`, `ω + 1`,
`ω + 2`, or `⊥`. -/
private noncomputable def kindRow : Fin 6 → Fin 6 → Label.{u} :=
  ![fun _ ↦ ⊥,
    ![⊥, gridPoint 1 0, ⊥, ⊥, ⊥, ⊥],
    ![⊥, ⊥, gridPoint 1 0, ⊥, ⊥, ⊥],
    ![⊥, gridPoint 1 0, gridPoint 1 1, gridPoint 1 1, ⊥, ⊥],
    ![⊥, gridPoint 1 0, ⊥, ⊥, gridPoint 2 1, ⊥],
    ![⊥, gridPoint 1 0, gridPoint 1 0, gridPoint 1 0, gridPoint 2 1, gridPoint 2 1]]

/-- The **reading scheme** on three points: the cells `readingCells` with the rows `kindRow`. -/
noncomputable abbrev readingScheme : Scheme.{u} 3 :=
  ⟨10, readingCells, ⟨fun s d ↦ kindRow (cellKind s) (cellKind d.1)⟩⟩

/-- The row of a cell of the reading scheme, by kinds. -/
private theorem readingScheme_row (s : Fin 10) (d) :
    readingScheme.{u}.rows.row s d = kindRow (cellKind s) (cellKind d.1) :=
  rfl

/-! ### The labellings -/

/-- The labels of the kinds for the parameters `A` (the reference cell), `E` (the new cell and the
cell `(univ, 1)`) and `B` (the cap and the reading cell). -/
private noncomputable def kindValue (A E B : Label.{u}) : Fin 6 → Label.{u} := ![⊥, A, E, E, B, B]

/-- The **reading labelling** of parameters `A`, `E`, `B`. -/
noncomputable def readingLabel (A E B : Label.{u}) (d : Fin 10) : Label.{u} :=
  kindValue A E B (cellKind d)

/-- A **reading triple**: the parameters of a lawful reading labelling. -/
structure IsReadingTriple (A E B : Label.{u}) : Prop where
  /-- The reference parameter is self-visible at `1`. -/
  isSelfVisible_ref : IsSelfVisible 1 A
  /-- The new parameter is self-visible at `1`. -/
  isSelfVisible_new : IsSelfVisible 1 E
  /-- The cap parameter is self-visible at `2`. -/
  isSelfVisible_cap : IsSelfVisible 2 B
  /-- The reference parameter is at most the new parameter (the cell `(univ, 1)`). -/
  ref_le_new : A ≤ E
  /-- The reference and new parameters agree below the cap (the reading cell). -/
  min_cap_eq : min A B = min E B

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

/-- Locality at `s` from one witness checked at every cell below `s`. -/
private theorem transformsTo_of_witness {s : Fin 10} {p : Fin 10 → Label.{u}} {g : ℕ → Label.{u}}
    {σ : Label.{u} → Label.{u}} (hw : IsWitness g σ)
    (h : ∀ d : Fin 10, readingCells.gradedIndex d ≤ readingCells.gradedIndex s →
      min (p d) (p s) = min (σ (kindRow (cellKind s) (cellKind d))) (g (readingCells.grade d))) :
    TransformsTo (fun d : readingCells.below (readingCells.gradedIndex s) ↦ readingCells.grade d)
      (readingScheme.{u}.rows.row s) (fun d ↦ min (p d) (p s)) :=
  ⟨g, σ, hw, fun d ↦ h d.1 d.2⟩

/-- Locality at a dead cell: its row and its label are `⊥`. -/
private theorem transformsTo_dead {s : Fin 10} (hs : cellKind s = 0) {A E B : Label.{u}} :
    TransformsTo (fun d : readingCells.below (readingCells.gradedIndex s) ↦ readingCells.grade d)
      (readingScheme.{u}.rows.row s)
      (fun d ↦ min (readingLabel A E B d) (readingLabel A E B s)) := by
  convert TransformsTo.bot _ (readingScheme.{u}.rows.row s) using 1
  funext d
  simp [readingLabel, hs, kindValue]

/-- **The reading labellings of reading triples are lawful.**  At the reference cell and the new
cell the shifter is constant on the natural numbers, at the cell `(univ, 1)` it is `A` on the
natural numbers and `E` above (`ThinCompletion.isWitness_blockConst`), and at the cap and the
reading cell it is the two-strip shifter of `min A B` and `B` (`ThinCompletion.isWitness_twoStrip`);
availability holds since the only cells below another of the same grade are the reference cell
and the new cell below the cell `(univ, 1)`, and the cap below the reading cell. -/
theorem isLawful_readingLabel {A E B : Label.{u}} (h : IsReadingTriple A E B) :
    readingScheme.{u}.rows.IsLawful (readingLabel A E B) where
  -- the order law: each label is `⊥` or a parameter, self-visible at the grade of its cell
  orderly d := by
    fin_cases d <;> simp [readingLabel, kindValue, cellKind, readingCells, isSelfVisible_bot,
      h.isSelfVisible_ref, h.isSelfVisible_new, h.isSelfVisible_cap]
  -- locality: the witnesses, then the ten cells in order, `⊥` at the dead cells
  locality s := by
    have hx1 : IsSelfVisible 1 (min A B) :=
      h.isSelfVisible_ref.min (h.isSelfVisible_cap.mono (by omega))
    have hvr : visibilityReplace 2 1 (min A B) = min A B :=
      visibilityReplace_two_one_of_isSelfVisible hx1
    have hBB : visibilityReplace 2 2 B = B := h.isSelfVisible_cap
    have hEB : min E B = min A B := h.min_cap_eq.symm
    have hAE : min A E = A := min_eq_left h.ref_le_new
    have hw2 : IsWitness (constStepSuppressor 2 B) (twoStrip (min A B) B B) :=
      isWitness_twoStrip h.isSelfVisible_cap
        (by rw [h.isSelfVisible_cap.visibilityReplace_eq 0]
            exact visibilityReplace_le_of_le le_rfl h.isSelfVisible_cap (min_le_right A B))
        hBB.le
    fin_cases s
    · exact transformsTo_dead rfl
    · exact transformsTo_dead rfl
    · exact transformsTo_dead rfl
    · -- the reference cell `3`: the constant shifter `A`
      refine transformsTo_of_witness
        (isWitness_blockConst h.isSelfVisible_ref h.isSelfVisible_ref le_rfl) fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [readingLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          blockConst_gridPoint_zero, blockConst_bot]
    · -- the new cell `4`: the constant shifter `E`
      refine transformsTo_of_witness
        (isWitness_blockConst h.isSelfVisible_new h.isSelfVisible_new le_rfl) fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [readingLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          blockConst_gridPoint_zero, blockConst_bot]
    · -- the cap `5`: the two-strip shifter
      refine transformsTo_of_witness hw2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [readingLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          twoStrip_gridPoint_one_zero, twoStrip_gridPoint_two_one, twoStrip_bot, hvr, hBB]
    · exact transformsTo_dead rfl
    · -- the cell `7`: `A` on the natural numbers and `E` above
      refine transformsTo_of_witness
        (isWitness_blockConst h.isSelfVisible_ref h.isSelfVisible_new h.ref_le_new) fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [readingLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          blockConst_gridPoint_zero, blockConst_gridPoint_one, blockConst_bot, hAE]
    · -- the reading cell `8`: the two-strip shifter, with `min E B = min A B`
      refine transformsTo_of_witness hw2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) |
        simp [readingLabel, kindValue, cellKind, kindRow, readingCells, constStepSuppressor,
          twoStrip_gridPoint_one_zero, twoStrip_gridPoint_two_one, twoStrip_bot, hvr, hBB, hEB]
    · exact transformsTo_dead rfl
  -- availability: a cell below another of the same grade is itself, `3` or `4` below `7`, `5`
  -- below `8`, or dead; each is at most the other
  availability s t hst hg := by
    have key : ∀ s t : Fin 10, readingCells.scope s ⊆ readingCells.scope t →
        readingCells.grade s = readingCells.grade t →
          s = t ∨ (s = 3 ∧ t = 7) ∨ (s = 4 ∧ t = 7) ∨ (s = 5 ∧ t = 8) ∨ cellKind s = 0 := by
      decide
    refine ⟨t, rfl, ?_⟩
    rcases key s t hst hg with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h0
    · exact le_rfl
    · exact h.ref_le_new
    · exact le_rfl
    · exact le_rfl
    · simp [readingLabel, h0, kindValue]

/-! ### The lift of parameters -/

/-- Two different labels with one capped observation are both at least the cap. -/
private theorem le_of_min_eq_min_of_lt {a b c : Label.{u}} (h : min a c = min b c) (hab : a < b) :
    c ≤ a := by
  by_contra hca
  exact hab.ne' (Label.eq_of_min_eq_of_lt h (not_le.mp hca))

/-- **The lift of parameters.**  Let `p` and `q` be reading triples and `c` a cap, self-visible at
`2` unless the third parameter of `q` is `⊥`.  For the parameters prescribed by `p` (`xa`, `xe`,
`xb`; the third only with the first), agreeing with `q` capped at `c`, some reading triple keeps
the prescribed parameters and agrees with `q` capped at `c` at all three. -/
theorem exists_isReadingTriple_lift {pA pE pB qA qE qB c : Label.{u}}
    (hp : IsReadingTriple pA pE pB) (hq : IsReadingTriple qA qE qB)
    (hc2 : IsSelfVisible 2 c ∨ qB = ⊥) {xa xe xb : Prop} (hba : xb → xa)
    (hA : xa → min pA c = min qA c) (hE : xe → min pE c = min qE c)
    (hB : xb → min pB c = min qB c) :
    ∃ rA rE rB, IsReadingTriple rA rE rB ∧ (xa → rA = pA) ∧ (xe → rE = pE) ∧ (xb → rB = pB) ∧
      min rA c = min qA c ∧ min rE c = min qE c ∧ min rB c = min qB c := by
  have hp' := hp
  have hq' := hq
  obtain ⟨pa1, pe1, pb2, ple, pmin⟩ := hp
  obtain ⟨qa1, qe1, qb2, qle, qmin⟩ := hq
  -- eight cases by which of `xa`, `xe`, `xb` hold; the two with `xb` but not `xa` are impossible
  by_cases ha : xa <;> by_cases he : xe <;> by_cases hb : xb
  · -- everything prescribed: `p` itself
    exact ⟨pA, pE, pB, hp', fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, hA ha, hE he, hB hb⟩
  · -- `A` and `E` prescribed: lower `B` to the cap when the cap is at most `A`
    have hA' := hA ha
    have hE' := hE he
    by_cases hcA : c ≤ pA
    · have hsv : IsSelfVisible 2 (min qB c) := by
        rcases hc2 with hc | hc
        · exact qb2.min hc
        · rw [hc, min_eq_left bot_le]
          exact isSelfVisible_bot _
      refine ⟨pA, pE, min qB c, ⟨pa1, pe1, hsv, ple, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl,
        fun h ↦ absurd h hb, hA', hE', by rw [min_assoc, min_self]⟩
      rw [min_eq_right ((min_le_right _ _).trans hcA),
        min_eq_right ((min_le_right _ _).trans (hcA.trans ple))]
    · have hlt : pA < c := not_le.mp hcA
      have hqA : qA = pA := Label.eq_of_min_eq_of_lt hA' hlt
      refine ⟨pA, pE, qB, ⟨pa1, pe1, qb2, ple, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl,
        fun h ↦ absurd h hb, hA', hE', rfl⟩
      rcases ple.lt_or_eq with hpE | hpE
      · -- `qB ≤ pA`: otherwise `qE = qA = pA` and then `pE = pA`
        have hqB : qB ≤ pA := by
          by_contra hqB
          have hqE : qE = qA := Label.eq_of_min_eq_of_lt qmin (hqA ▸ not_le.mp hqB)
          have : pE = pA := by
            have h1 : min pE c = min pA c := by rw [hE', hqE, hqA]
            exact Label.eq_of_min_eq_of_lt h1.symm hlt
          exact hpE.ne this.symm
        rw [min_eq_right hqB, min_eq_right (hqB.trans ple)]
      · rw [hpE]
  · -- `A` and `B` prescribed: `E` equal to `A` below `B`, at least `A` and `qE` above
    have hA' := hA ha
    have hB' := hB hb
    by_cases hAB : pA < pB
    · refine ⟨pA, pA, pB, ⟨pa1, pa1, pb2, le_rfl, rfl⟩, fun _ ↦ rfl,
        fun h ↦ absurd h he, fun _ ↦ rfl, hA', ?_, hB'⟩
      by_cases hqAB : qA < qB
      · rw [Label.eq_of_min_eq_of_lt qmin hqAB]
        exact hA'
      · -- the cap is at most `pA`
        have hcA : c ≤ pA := by
          by_contra hcA
          have hlt : pA < c := not_le.mp hcA
          have hqA : qA = pA := Label.eq_of_min_eq_of_lt hA' hlt
          have h1 : min pB c ≤ pA := by
            rw [hB']
            exact (min_le_left _ _).trans (hqA ▸ not_lt.mp hqAB)
          exact (lt_min hAB hlt).not_ge h1
        have hcqA : c ≤ qA := by
          rw [min_eq_right hcA] at hA'
          exact min_eq_right_iff.mp hA'.symm
        rw [min_eq_right hcA, min_eq_right (hcqA.trans qle)]
    · have hBA : pB ≤ pA := not_lt.mp hAB
      refine ⟨pA, max pA qE, pB, ⟨pa1, pa1.max qe1, pb2, le_max_left _ _, ?_⟩,
        fun _ ↦ rfl, fun h ↦ absurd h he, fun _ ↦ rfl, hA', ?_, hB'⟩
      · rw [min_eq_right hBA, min_eq_right (hBA.trans (le_max_left _ _))]
      · rw [min_max_distrib_right, hA', max_eq_right (min_le_min_right c qle)]
  · -- only `A` prescribed: as above, with `qB` in place of `pB`
    have hA' := hA ha
    by_cases hAB : pA < qB
    · refine ⟨pA, pA, qB, ⟨pa1, pa1, qb2, le_rfl, rfl⟩, fun _ ↦ rfl,
        fun h ↦ absurd h he, fun h ↦ absurd h hb, hA', ?_, rfl⟩
      by_cases hqAB : qA < qB
      · rw [Label.eq_of_min_eq_of_lt qmin hqAB]
        exact hA'
      · have hpq : pA < qA := hAB.trans_le (not_lt.mp hqAB)
        have hcA : c ≤ pA := by
          by_contra hcA
          have hqA : qA = pA := Label.eq_of_min_eq_of_lt hA' (not_le.mp hcA)
          exact hpq.ne' hqA
        rw [min_eq_right hcA, min_eq_right (hcA.trans (hpq.le.trans qle))]
    · have hBA : qB ≤ pA := not_lt.mp hAB
      refine ⟨pA, max pA qE, qB, ⟨pa1, pa1.max qe1, qb2, le_max_left _ _, ?_⟩,
        fun _ ↦ rfl, fun h ↦ absurd h he, fun h ↦ absurd h hb, hA', ?_, rfl⟩
      · rw [min_eq_right hBA, min_eq_right (hBA.trans (le_max_left _ _))]
      · rw [min_max_distrib_right, hA', max_eq_right (min_le_min_right c qle)]
  · -- `B` and `E` prescribed without `A`: impossible
    exact absurd (hba hb) ha
  · -- only `E` prescribed: `A` equal to `E` below `qB`, between `qB` and `E` above
    have hE' := hE he
    by_cases hEB : pE < qB
    · refine ⟨pE, pE, qB, ⟨pe1, pe1, qb2, le_rfl, rfl⟩, fun h ↦ absurd h ha,
        fun _ ↦ rfl, fun h ↦ absurd h hb, ?_, hE', rfl⟩
      by_cases hqEB : qE < qB
      · rw [Label.eq_of_min_eq_of_lt qmin.symm hqEB]
        exact hE'
      · have hqBE : qB ≤ qE := not_lt.mp hqEB
        have hpq : pE < qE := hEB.trans_le hqBE
        have hcE : c ≤ pE := le_of_min_eq_min_of_lt hE' hpq
        have hqBA : qB ≤ qA := by
          have := qmin
          rw [min_eq_right hqBE] at this
          exact min_eq_right_iff.mp this
        rw [min_eq_right hcE, min_eq_right (hcE.trans (hEB.le.trans hqBA))]
    · have hBE : qB ≤ pE := not_lt.mp hEB
      refine ⟨max (min pE qA) qB, pE, qB, ⟨(pe1.min qa1).max (qb2.mono (by omega)),
        pe1, qb2, max_le (min_le_left _ _) hBE, ?_⟩, fun h ↦ absurd h ha, fun _ ↦ rfl,
        fun h ↦ absurd h hb, ?_, hE', rfl⟩
      · rw [min_eq_right (le_max_right _ _), min_eq_right hBE]
      · have h1 : min (min pE qA) c = min qA c := by
          rw [min_comm pE qA, min_assoc, hE', ← min_assoc, min_eq_left qle]
        rw [min_max_distrib_right, h1]
        refine max_eq_left ?_
        by_cases hqBA : qB ≤ qA
        · exact min_le_min_right c hqBA
        · have hqE : qE = qA := Label.eq_of_min_eq_of_lt qmin (not_le.mp hqBA)
          have hcE : c ≤ qE := le_of_min_eq_min_of_lt hE'.symm
            (hqE ▸ (not_le.mp hqBA).trans_le hBE)
          have hcA : c ≤ qA := hqE ▸ hcE
          rw [min_eq_right hcA]
          exact min_le_right _ _
  · -- `B` prescribed without `A`: impossible
    exact absurd (hba hb) ha
  · -- nothing prescribed: `q` itself
    exact ⟨qA, qE, qB, hq', fun h ↦ absurd h ha, fun h ↦ absurd h he, fun h ↦ absurd h hb, rfl,
      rfl, rfl⟩

/-! ### Lawful labellings below a pair -/

/-- Every cell is dead or one of the five live cells. -/
private theorem cellKind_cases (d : Fin 10) :
    cellKind d = 0 ∨ d = 3 ∨ d = 4 ∨ d = 7 ∨ d = 5 ∨ d = 8 := by
  revert d
  decide

/-- A dead cell is labelled `⊥`. -/
private theorem readingLabel_of_kind_zero {A E B : Label.{u}} {d : Fin 10} (h : cellKind d = 0) :
    readingLabel A E B d = ⊥ := by
  simp [readingLabel, h, kindValue]

section Below

variable {X : Finset (Fin 3) × ℕ}

private theorem mem_below_of_le {d e : Fin 10} (hd : d ∈ readingCells.below X)
    (h : readingCells.gradedIndex e ≤ readingCells.gradedIndex d) : e ∈ readingCells.below X :=
  le_trans h hd

/-- A pair above the reference cell and the new cell is above the cell `(univ, 1)`. -/
private theorem mem_seven (h3 : (3 : Fin 10) ∈ readingCells.below X)
    (h4 : (4 : Fin 10) ∈ readingCells.below X) : (7 : Fin 10) ∈ readingCells.below X := by
  obtain ⟨C, j⟩ := X
  have key : ∀ C : Finset (Fin 3), ({0, 1} : Finset (Fin 3)) ⊆ C →
      ({1, 2} : Finset (Fin 3)) ⊆ C → (univ : Finset (Fin 3)) ⊆ C := by decide
  exact ⟨key C h3.1 h4.1, h3.2⟩

/-- A pair above the new cell and the cap is above the reading cell. -/
private theorem mem_eight (h4 : (4 : Fin 10) ∈ readingCells.below X)
    (h5 : (5 : Fin 10) ∈ readingCells.below X) : (8 : Fin 10) ∈ readingCells.below X := by
  obtain ⟨C, j⟩ := X
  have key : ∀ C : Finset (Fin 3), ({0, 1} : Finset (Fin 3)) ⊆ C →
      ({1, 2} : Finset (Fin 3)) ⊆ C → (univ : Finset (Fin 3)) ⊆ C := by decide
  exact ⟨key C h5.1 h4.1, h5.2⟩

/-- **Every labelling lawful below a pair is a reading labelling** of a reading triple, whose
third parameter is `⊥` when the cap is not below the pair: for `r` lawful below `X` there are `A`,
`E`, `B` with `IsReadingTriple A E B`, `r d = readingLabel A E B d` at every cell `d` below `X`, and
`B = ⊥` unless the cap `5` is below `X`. -/
theorem exists_of_isLawfulBelow {r : readingCells.below X → Label.{u}}
    (hr : readingScheme.{u}.rows.IsLawfulBelow X r) :
    ∃ A E B, IsReadingTriple A E B ∧ (∀ d, r d = readingLabel A E B d.1) ∧
      ((5 : Fin 10) ∉ readingCells.below X → B = ⊥) := by
  classical
  -- `w`: `r` extended by `⊥` to all cells, lawful below `X`; first its values at the dead
  -- cells, then locality and availability at the cells `7` and `8`; then the triple `(A, E, B)`,
  -- with `A` and `E` read at `3` and `4` (each replaced by the other off `X`), and the labelling
  -- cell by cell
  set w := CellScheme.Rows.extendBot X r with hw
  have hlaw : readingScheme.{u}.rows.IsLawfulBelow X (fun d ↦ w d) := by
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
    · have := (hl d hd).eq_bot (d := ⟨d, self d⟩) (by rw [readingScheme_row]; simp [h0, kindRow])
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
  -- locality and availability at the reading cell `8`: `w 8 = w 5`, and `w 3`, `w 4` agree below
  -- the cap
  have h8 : (8 : Fin 10) ∈ readingCells.below X →
      w 8 = w 5 ∧ min (w 3) (w 5) = min (w 4) (w 5) := fun h8 ↦ by
    have hT := hl 8 h8
    have m3 : (3 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 8) :=
      show readingCells.gradedIndex 3 ≤ readingCells.gradedIndex 8 by decide
    have m4 : (4 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 8) :=
      show readingCells.gradedIndex 4 ≤ readingCells.gradedIndex 8 by decide
    have m5 : (5 : Fin 10) ∈ readingCells.below (readingCells.gradedIndex 8) :=
      show readingCells.gradedIndex 5 ≤ readingCells.gradedIndex 8 by decide
    have huniq : ∀ u : Fin 10, readingCells.gradedIndex u = readingCells.gradedIndex 8 → u = 8 := by
      decide
    have h85 := hT.le_of_le (d := ⟨8, self 8⟩) (d' := ⟨5, m5⟩) le_rfl le_rfl
    have h58 := hav 5 8 h8 (by decide) rfl huniq
    simp only [min_self] at h85
    have hw85 : w 8 = w 5 := le_antisymm (h85.trans (min_le_left _ _)) h58
    have h34 := hT.le_of_le (d := ⟨3, m3⟩) (d' := ⟨4, m4⟩) le_rfl le_rfl
    have h43 := hT.le_of_le (d := ⟨4, m4⟩) (d' := ⟨3, m3⟩) le_rfl le_rfl
    have heq : min (w 3) (w 8) = min (w 4) (w 8) := le_antisymm h34 h43
    rw [hw85] at heq
    exact ⟨hw85, heq⟩
  have h35 : (5 : Fin 10) ∈ readingCells.below X → (3 : Fin 10) ∈ readingCells.below X :=
    fun h5 ↦ mem_below_of_le h5 (by decide)
  refine ⟨if (3 : Fin 10) ∈ readingCells.below X then w 3 else w 4,
    if (4 : Fin 10) ∈ readingCells.below X then w 4 else w 3, w 5, ⟨?_, ?_, hsv 5, ?_, ?_⟩,
    fun d ↦ ?_, fun h5 ↦ hout 5 h5⟩
  -- the clauses of `IsReadingTriple`: self-visibility, `A ≤ E`, `min A B = min E B`
  · split_ifs
    exacts [hsv 3, hsv 4]
  · split_ifs
    exacts [hsv 4, hsv 3]
  · by_cases h3 : (3 : Fin 10) ∈ readingCells.below X <;>
      by_cases h4 : (4 : Fin 10) ∈ readingCells.below X <;> simp only [h3, h4, ↓reduceIte]
    · exact (h7 (mem_seven h3 h4)).2
    · exact le_rfl
    · exact le_rfl
    · rw [hout 4 h4, hout 3 h3]
  · by_cases h5 : (5 : Fin 10) ∈ readingCells.below X
    · have h3 := h35 h5
      by_cases h4 : (4 : Fin 10) ∈ readingCells.below X
      · simp only [h3, h4, ↓reduceIte]
        exact (h8 (mem_eight h4 h5)).2
      · simp only [h3, h4, ↓reduceIte]
    · rw [hout 5 h5, min_bot_right, min_bot_right]
  · -- the labelling, cell by cell
    obtain ⟨d, hd⟩ := d
    rw [← CellScheme.Rows.extendBot_of_mem r hd]
    -- the left side is `w d`, the extension of `r` by `⊥` at a cell below `X`
    change w d = _
    rcases cellKind_cases d with h0 | rfl | rfl | rfl | rfl | rfl
    · rw [hdead d h0, readingLabel_of_kind_zero h0]
    · -- `readingLabel` at the reference cell is the first parameter
      change _ = if (3 : Fin 10) ∈ readingCells.below X then w 3 else w 4
      rw [ite_eq_left hd]
    · -- `readingLabel` at the new cell is the second parameter
      change _ = if (4 : Fin 10) ∈ readingCells.below X then w 4 else w 3
      rw [ite_eq_left hd]
    · -- `readingLabel` at the cell `7` is the second parameter
      change _ = if (4 : Fin 10) ∈ readingCells.below X then w 4 else w 3
      rw [ite_eq_left (mem_below_of_le hd (by decide)), (h7 hd).1]
    · rfl
    · exact (h8 hd).1

end Below

/-! ### Legality -/

/-- **Every pair lifts capped**: prescribed parameters are kept, the others lifted by
`exists_isReadingTriple_lift`, and the reading labelling of the lifted parameters is lawful. -/
theorem cappedLift_readingScheme {X Y : Finset (Fin 3) × ℕ} (h : X ≤ Y) :
    readingScheme.{u}.rows.CappedLift h := by
  classical
  refine (CellScheme.Rows.cappedLift_iff_forall_exists h).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨pA, pE, pB, hpT, hpX, -⟩ := exists_of_isLawfulBelow hp
  obtain ⟨qA, qE, qB, hqT, hqY, hq5⟩ := exists_of_isLawfulBelow hq
  have hagree {d : Fin 10} (hd : d ∈ readingCells.below X) :
      min (readingLabel pA pE pB d) c = min (readingLabel qA qE qB d) c := by
    have := hpq ⟨d, hd⟩
    rw [hpX, hqY] at this
    exact this.symm
  have hc2 : IsSelfVisible 2 c ∨ qB = ⊥ := by
    by_cases h5 : (5 : Fin 10) ∈ readingCells.below Y
    · exact .inl (hc.mono h5.2)
    · exact .inr (hq5 h5)
  obtain ⟨rA, rE, rB, hrT, hrA, hrE, hrB, hcA, hcE, hcB⟩ :=
    exists_isReadingTriple_lift (xa := (3 : Fin 10) ∈ readingCells.below X)
      (xe := (4 : Fin 10) ∈ readingCells.below X) (xb := (5 : Fin 10) ∈ readingCells.below X)
      hpT hqT hc2 (fun h5 ↦ mem_below_of_le h5 (by decide)) hagree hagree hagree
  refine ⟨fun d ↦ readingLabel rA rE rB d.1,
    (isLawful_readingLabel hrT).isLawfulBelow Y, fun d ↦ ?_, fun d ↦ ?_⟩
  · rw [hqY]
    obtain ⟨d, hd⟩ := d
    -- the restriction to `Y` at the cell `d`
    change min (readingLabel rA rE rB d) c = min (readingLabel qA qE qB d) c
    rcases cellKind_cases d with h0 | rfl | rfl | rfl | rfl | rfl
    · rw [readingLabel_of_kind_zero h0, readingLabel_of_kind_zero h0]
    exacts [hcA, hcE, hcE, hcB, hcB]
  · obtain ⟨d, hd⟩ := d
    rw [hpX]
    -- the restriction to `X` at the cell `d`
    change readingLabel rA rE rB d = readingLabel pA pE pB d
    rcases cellKind_cases d with h0 | rfl | rfl | rfl | rfl | rfl
    · rw [readingLabel_of_kind_zero h0, readingLabel_of_kind_zero h0]
    · exact hrA hd
    · exact hrE hd
    · exact hrE (mem_below_of_le hd (by decide))
    · exact hrB hd
    · exact hrB (mem_below_of_le hd (by decide))

/-- **The reading scheme is legal.** -/
theorem isLegal_readingScheme : readingScheme.{u}.IsLegal where
  -- well formed: the interval plan, each scope a face, each grade at most the size of the scope
  isWellFormed := ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    have key : ∀ d : Fin 10, readingCells.scope d ∈ readingCells.faces ∧
        0 < readingCells.grade d ∧ readingCells.grade d ≤ #(readingCells.scope d) := by decide
    exact key d⟩⟩
  -- coded: each row entry is `⊥` or a grid point below `ω ^ 2`
  isCoded s t := by
    have key : ∀ s d : Fin 6, kindRow.{u} s d = ⊥ ∨ kindRow.{u} s d = gridPoint 1 0 ∨
        kindRow.{u} s d = gridPoint 1 1 ∨ kindRow.{u} s d = gridPoint 2 1 := by
      intro s d
      fin_cases s <;> fin_cases d <;> simp [kindRow]
    rw [readingScheme_row]
    rcases key (cellKind s) (cellKind t.1) with h | h | h | h <;> rw [h]
    · exact WithBot.bot_lt_coe _
    all_goals exact gridPoint_lt_omega0_sq _ _
  -- consistent: each row is the reading labelling of one of four reading triples, `h0` at the
  -- dead cells, `h1` at the reference cell and the new cell, `h2` at the cap and the reading cell,
  -- `h3` at the cell `7`
  isConsistent s := by
    have hrow {A E B : Label.{u}} (hT : IsReadingTriple A E B)
        (h : ∀ d : Fin 10, readingCells.gradedIndex d ≤ readingCells.gradedIndex s →
          kindRow (cellKind s) (cellKind d) = readingLabel A E B d) :
        readingScheme.{u}.rows.IsLawfulBelow (readingCells.gradedIndex s)
          (readingScheme.{u}.rows.row s) := by
      have : readingScheme.{u}.rows.row s = fun d ↦ readingLabel A E B d.1 :=
        funext fun d ↦ h d.1 d.2
      rw [this]
      exact (isLawful_readingLabel hT).isLawfulBelow _
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
    · refine hrow h0 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h3 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h2 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
    · refine hrow h0 fun d hd ↦ ?_
      fin_cases d <;> first | exact absurd hd (by decide) | rfl
  isBountiful _ _ _ _ h := cappedLift_readingScheme h
  -- complete: one cell at each graded face
  isComplete X hX := by
    obtain ⟨B, j⟩ := X
    obtain ⟨hB, hj0, hjB⟩ := hX
    have hj3 : j ≤ 3 := hjB.trans (by simpa using card_le_univ B)
    have key : ∀ B : Finset (Fin 3), B ∈ readingCells.faces → ∀ j : Fin 4, 0 < (j : ℕ) →
        (j : ℕ) ≤ #B → ∃ d : Fin 10, readingCells.gradedIndex d = (B, (j : ℕ)) := by decide
    exact key B hB ⟨j, by omega⟩ hj0 hjB

/-! ### The decoding of the new cell by the cap -/

/-- **The cap decodes the new cell**: in a reading triple, a third parameter (the cap) above the
first (the reference cell) forces the second (the new cell) to equal the first. -/
theorem IsReadingTriple.eq_of_lt {A E B : Label.{u}} (h : IsReadingTriple A E B) (hAB : A < B) :
    E = A :=
  Label.eq_of_min_eq_of_lt h.min_cap_eq hAB

/-- **Below the reference cell the cap decodes nothing**: a cap at most the first parameter
leaves the second free above the first; with the first and second parameters self-visible at `1`
and the cap self-visible at `2`, every second parameter at least the first gives a reading
triple. -/
theorem isReadingTriple_of_le {A E B : Label.{u}} (hA : IsSelfVisible 1 A) (hE : IsSelfVisible 1 E)
    (hB : IsSelfVisible 2 B) (hAE : A ≤ E) (hBA : B ≤ A) : IsReadingTriple A E B :=
  ⟨hA, hE, hB, hAE, by rw [min_eq_right hBA, min_eq_right (hBA.trans hAE)]⟩

/-! ### The context, the donor, and the root -/

variable (ξ : Ordinal.{u})

/-- The marker label `λ_ξ + 1`. -/
noncomputable abbrev markerLabel : Label.{u} :=
  ((blockStage ξ + ((1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

/-- The marker label is self-visible at `1`. -/
theorem isSelfVisible_markerLabel : IsSelfVisible 1 (markerLabel ξ) :=
  isSelfVisible_coe_add (isSuccPrelimit_blockStage ξ) le_rfl

/-- The finite part of the marker label is `1`. -/
theorem eq_one_of_markerLabel_eq {μ : Ordinal.{u}} {n : ℕ} (hμ : Order.IsSuccPrelimit μ)
    (h : markerLabel ξ = ((μ + n : Ordinal.{u}) : Label.{u})) : n = 1 := by
  have h1 : IsSelfVisible 1 (markerLabel ξ) := isSelfVisible_markerLabel ξ
  have h2 : ¬ IsSelfVisible 2 (markerLabel ξ) :=
    not_isSelfVisible_coe_add_natCast (isSuccPrelimit_blockStage ξ) (by omega)
  rw [h] at h1 h2
  by_contra hn
  rcases Nat.lt_or_gt_of_ne hn with hn | hn
  · exact not_isSelfVisible_coe_add_natCast hμ hn h1
  · exact h2 (isSelfVisible_coe_add hμ hn)

/-- The parameters of the reading type: the marker at the reference cell and the new cell, the
formal top at the cap. -/
theorem isReadingTriple_marker : IsReadingTriple (markerLabel ξ) (markerLabel ξ) ⊤ :=
  ⟨isSelfVisible_markerLabel ξ, isSelfVisible_markerLabel ξ, isSelfVisible_top _, le_rfl, rfl⟩

/-- The labels of the marker triple are `⊥`, the marker, or the formal top. -/
theorem readingLabel_marker_cases (d : Fin 10) :
    readingLabel (markerLabel ξ) (markerLabel ξ) ⊤ d = ⊥ ∨
      readingLabel (markerLabel ξ) (markerLabel ξ) ⊤ d = markerLabel ξ ∨
      readingLabel (markerLabel ξ) (markerLabel ξ) ⊤ d = ⊤ := by
  fin_cases d <;> simp [readingLabel, kindValue, cellKind]

/-- The marker label occurs at `λ_{ξ+1}`. -/
theorem markerLabel_lt : markerLabel ξ < ((blockStage (ξ + 1) : Ordinal.{u}) : Label.{u}) := by
  rw [blockStage_add_one]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    (add_lt_add_right (natCast_lt_omega0 1) _))

/-- The **reading type** at `λ_{ξ+1}`: the reading scheme labelled `λ_ξ + 1` at the reference
cell, the new cell and the cell `(univ, 1)`, and the formal top at the cap and the reading cell. -/
noncomputable def readingType : StageType.{u} (blockStage (ξ + 1)) 3 where
  toScheme := readingScheme
  label := readingLabel (markerLabel ξ) (markerLabel ξ) ⊤
  isWellFormed := isLegal_readingScheme.isWellFormed
  isCoded := isLegal_readingScheme.isCoded
  isLawful := isLawful_readingLabel (isReadingTriple_marker ξ)
  atStage d := by
    rcases readingLabel_marker_cases ξ d with h | h | h <;> rw [h]
    · exact atStage_bot
    · exact .inl (markerLabel_lt ξ)
    · exact atStage_top

/-- The **root embedding**: the point of the root is the point `1` of the context. -/
def rootEmb : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 1, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The first two points span a closed face, the context. -/
private theorem map_castSuccEmb_mem_faces :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ readingCells.faces := by
  decide

/-- The root followed by the new point spans `{1, 2}`. -/
private theorem map_extendByLast_eq :
    univ.map (extendByLast rootEmb) = ({1, 2} : Finset (Fin 3)) := by
  decide

/-- The root and the new point span a closed face, the face of the donor. -/
private theorem map_extendByLast_mem_faces :
    univ.map (extendByLast rootEmb) ∈ readingCells.faces := by
  rw [map_extendByLast_eq]
  decide

/-- The root spans a closed face. -/
private theorem map_rootEmb_mem_faces :
    univ.map (rootEmb.trans (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) ∈ readingCells.faces := by
  decide

/-- The **context type** `T⁺` on two points: the face of the reading type along the first two
points. -/
noncomputable def contextType : StageType.{u} (blockStage (ξ + 1)) 2 :=
  (readingType ξ).comap Fin.castSuccEmb map_castSuccEmb_mem_faces

/-- The **donor** on two points: the face of the reading type along the root followed by the
new point. -/
noncomputable def donorType : StageType.{u} (blockStage (ξ + 1)) 2 :=
  (readingType ξ).comap (extendByLast rootEmb) map_extendByLast_mem_faces

/-- The **root** on one point: the face of the context type along the root embedding. -/
noncomputable def rootType : StageType.{u} (blockStage (ξ + 1)) 1 :=
  (contextType ξ).comap rootEmb
    (((readingType ξ).map_univ_mem_comap_faces_iff _ _ _).mpr map_rootEmb_mem_faces)

/-- The context type is the face of the reading type along the first two points. -/
theorem restrictFace_contextType :
    restrictFace Fin.castSuccEmb (readingType ξ) = some (contextType ξ) :=
  restrictFace_of_mem _ _ _

/-- The root is the face of the context type along the root embedding. -/
theorem restrictFace_rootType : restrictFace rootEmb (contextType ξ) = some (rootType ξ) :=
  restrictFace_of_mem _ _ _

/-- The context type is legal. -/
theorem isLegal_contextType : (contextType ξ).IsLegal :=
  isLegal_readingScheme.comap _ map_castSuccEmb_mem_faces

/-- The donor is a coface of the root. -/
theorem donorType_mem_cofaces : donorType ξ ∈ (rootType ξ).cofaces := by
  refine ⟨isLegal_readingScheme.comap _ map_extendByLast_mem_faces, ?_⟩
  unfold donorType
  rw [restrictFace_trans _ _ _ (restrictFace_of_mem (readingType ξ) _ map_extendByLast_mem_faces),
    castSuccEmb_trans_extendByLast, ← restrictFace_trans _ _ _ (restrictFace_contextType ξ),
    restrictFace_rootType]

/-- The cells of the context type are the cells of the reading scheme visible through the first
two points. -/
private theorem exists_cellMap_castSuccEmb {d : Fin 10}
    (hd : d ∈ readingScheme.{u}.visibleCells Fin.castSuccEmb) :
    ∃ b, readingScheme.{u}.cellMap Fin.castSuccEmb b = d := by
  have : d ∈ Set.range (readingScheme.{u}.cellMap Fin.castSuccEmb) := by
    rw [Scheme.range_cellMap]
    exact hd
  exact this

/-- The cap: the cell of the context type at the cell `5` of the reading scheme, of grade `2`,
labelled the formal top. -/
theorem exists_cap : ∃ b : Fin (contextType ξ).card,
    readingScheme.{u}.cellMap Fin.castSuccEmb b = 5 ∧
      (contextType ξ).toCellScheme.grade b = 2 ∧ (contextType ξ).label b = ⊤ := by
  obtain ⟨b, hb⟩ := exists_cellMap_castSuccEmb.{u} (d := 5) (by decide)
  refine ⟨b, hb, ?_, ?_⟩
  · -- the grade of a cell of the face is the grade of its image
    change readingCells.grade (readingScheme.{u}.cellMap Fin.castSuccEmb b) = 2
    rw [hb]
    rfl
  · -- the label of a cell of the face is the label of its image
    change readingLabel (markerLabel ξ) (markerLabel ξ) ⊤
      (readingScheme.{u}.cellMap Fin.castSuccEmb b) = ⊤
    rw [hb]
    rfl

/-- The reference cell (the marker): the cell of the context type at the cell `3` of the reading
scheme, of grade `1`, labelled `λ_ξ + 1`. -/
theorem exists_marker : ∃ a : Fin (contextType ξ).card,
    readingScheme.{u}.cellMap Fin.castSuccEmb a = 3 ∧
      (contextType ξ).toCellScheme.grade a = 1 ∧ (contextType ξ).label a = markerLabel ξ := by
  obtain ⟨a, ha⟩ := exists_cellMap_castSuccEmb.{u} (d := 3) (by decide)
  refine ⟨a, ha, ?_, ?_⟩
  · -- the grade of a cell of the face is the grade of its image
    change readingCells.grade (readingScheme.{u}.cellMap Fin.castSuccEmb a) = 1
    rw [ha]
    rfl
  · -- the label of a cell of the face is the label of its image
    change readingLabel (markerLabel ξ) (markerLabel ξ) ⊤
      (readingScheme.{u}.cellMap Fin.castSuccEmb a) = markerLabel ξ
    rw [ha]
    rfl

/-- **The context type satisfies the graded cap calibration** for the root embedding, the donor
and `γ = λ_ξ`: the cap has grade `2 > 1`, is labelled the formal top, and `λ_ξ < λ_ξ + 2`; the
only ordinal label of the donor is `λ_ξ + 1`, with the marker as its reference cell. -/
theorem gradedCapCalibration_contextType :
    GradedCapCalibration ξ (contextType ξ) rootEmb (donorType ξ) (blockStage ξ) := by
  obtain ⟨b, -, hbg, hbl⟩ := exists_cap ξ
  obtain ⟨a, -, hag, hal⟩ := exists_marker ξ
  refine ⟨b, by rw [hbl]; exact le_top, by rw [hbg]; omega, ?_, fun j o ho ↦ ?_⟩
  · rw [hbg]
    exact lt_add_of_pos_right _ (by simp)
  · have hj : (donorType ξ).label j = readingLabel (markerLabel ξ) (markerLabel ξ) ⊤
        (readingScheme.{u}.cellMap (extendByLast rootEmb) j) := rfl
    rcases readingLabel_marker_cases ξ (readingScheme.{u}.cellMap (extendByLast rootEmb) j)
      with h | h | h <;> rw [← hj, ho] at h
    · exact absurd h WithBot.coe_ne_bot
    · obtain rfl : o = blockStage ξ + ((1 : ℕ) : Ordinal.{u}) :=
        WithTop.coe_injective (WithBot.coe_injective h)
      refine ⟨blockStage ξ, 1, 1, a, isSuccPrelimit_blockStage ξ, rfl, ?_, ?_, ?_, hal⟩
      · rw [hbg]; omega
      · rw [hbg]; omega
      · rw [hag, hbg]; omega
    · exact absurd h (by simp)

/-- The new cell of the donor: the cell at the cell `4` of the reading scheme, whose scope contains
the new point, labelled `λ_ξ + 1`. -/
theorem exists_newCell : ∃ j : Fin (donorType ξ).card,
    Fin.last 1 ∈ (donorType ξ).toCellScheme.scope j ∧ (donorType ξ).label j = markerLabel ξ := by
  have : (4 : Fin 10) ∈ Set.range (readingScheme.{u}.cellMap (extendByLast rootEmb)) := by
    rw [Scheme.range_cellMap, Finset.mem_coe, Scheme.visibleCells, Finset.mem_filter,
      map_extendByLast_eq]
    decide
  obtain ⟨j, hj⟩ := this
  refine ⟨j, ?_, ?_⟩
  · -- the scope of a cell of the face is the preimage of the scope of its image
    change Fin.last 1 ∈ (readingCells.scope
      (readingScheme.{u}.cellMap (extendByLast rootEmb) j)).preimage (extendByLast rootEmb)
      (extendByLast rootEmb).injective.injOn
    rw [hj, Finset.mem_preimage, extendByLast_last]
    decide
  · -- the label of a cell of the face is the label of its image
    change readingLabel (markerLabel ξ) (markerLabel ξ) ⊤
      (readingScheme.{u}.cellMap (extendByLast rootEmb) j) = markerLabel ξ
    rw [hj]
    rfl

/-- The new cells of the donor: a cell of the reading scheme visible through the root and the new
point whose scope contains the new point is one of the cells `2`, `4`, `6`. -/
theorem eq_of_mem_newCells {d : Fin 10}
    (hd : d ∈ readingScheme.{u}.visibleCells (extendByLast rootEmb))
    (h2 : (2 : Fin 3) ∈ readingCells.scope d) : d = 2 ∨ d = 4 ∨ d = 6 := by
  rw [Scheme.visibleCells, Finset.mem_filter, map_extendByLast_eq] at hd
  have key : ∀ d : Fin 10, readingCells.scope d ⊆ ({1, 2} : Finset (Fin 3)) →
      (2 : Fin 3) ∈ readingCells.scope d → d = 2 ∨ d = 4 ∨ d = 6 := by decide
  exact key d hd.2 h2

/-- **The reading scheme is a stable recovery scheme** for the context type, the root embedding,
the donor and `γ = λ_ξ`, by `StageType.IsStableRecoveryScheme.of_readsThroughCap` at the cell `8`
(the reading cell, the only cell of the graded index `(univ, 2)`): it reads the new cells `2` and
`6`, labelled `⊥` in the donor, as `⊥`, and the new cell `4`, labelled `λ_ξ + 1`, at `1`, where it
reads the marker. -/
theorem isStableRecoveryScheme_readingScheme :
    (contextType ξ).IsStableRecoveryScheme rootEmb (donorType ξ) (blockStage ξ) readingScheme := by
  obtain ⟨b, hb, hbg, hbl⟩ := exists_cap ξ
  obtain ⟨a, ha, -, hal⟩ := exists_marker ξ
  have hγ : blockStage ξ < blockStage ξ + ((2 : ℕ) : Ordinal.{u}) :=
    lt_add_of_pos_right _ (by simp)
  refine IsStableRecoveryScheme.of_readsThroughCap (restrictFace_rootType ξ)
    (donorType_mem_cofaces ξ)
    ⟨(readingType ξ).reduce (isSuccPrelimit_blockStage ξ), ⟨isLegal_readingScheme, ?_⟩, rfl⟩
    map_extendByLast_mem_faces rfl (b := b) (b₀ := b) rfl ?_ ?_ (s := 8) ?_ ?_ ?_
  · rw [restrictFace_reduce, restrictFace_contextType]
    rfl
  · rw [hbl]
    exact le_top
  · rw [hb]
    exact hγ
  · rw [hb]
    exact show readingCells.gradedIndex 5 ≤ readingCells.gradedIndex 8 by decide
  · rw [hb]
    rfl
  intro i j hij hj
  obtain rfl : i = j := Fin.ext hij
  have h2 : (2 : Fin 3) ∈
      readingCells.scope (readingScheme.{u}.cellMap (extendByLast rootEmb) i) := by
    have : Fin.last 1 ∈ (readingCells.scope
        (readingScheme.{u}.cellMap (extendByLast rootEmb) i)).preimage (extendByLast rootEmb)
        (extendByLast rootEmb).injective.injOn := hj
    rw [Finset.mem_preimage, extendByLast_last] at this
    exact this
  -- the label of the new cell `i` of `D` is the label of its image in the reading type
  change _ ∧ ∀ u, _ → (contextType ξ).ReadsThroughCap readingScheme b u _
    (readingLabel (markerLabel ξ) (markerLabel ξ) ⊤
      (readingScheme.{u}.cellMap (extendByLast rootEmb) i))
  have hvis := readingScheme.{u}.cellMap_mem (extendByLast rootEmb) i
  generalize readingScheme.{u}.cellMap (extendByLast rootEmb) i = d at h2 hvis ⊢
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
    have ha8 : readingScheme.{u}.cellMap Fin.castSuccEmb a ∈
        readingCells.below (readingCells.gradedIndex 8) := by
      rw [ha]
      exact show readingCells.gradedIndex 3 ≤ readingCells.gradedIndex 8 by decide
    refine ⟨by rw [hb]; decide, a, a, 1, ((0 : ℕ) : Ordinal.{u}), rfl, hal.trans h,
      by rw [hb]; decide, ha8, ?_, rfl⟩
    -- the row of the reading cell, by kinds
    change kindRow (cellKind 8) (cellKind (readingScheme.{u}.cellMap Fin.castSuccEmb a)) = _
    rw [ha]
    rfl
  · -- the new cell `6`, labelled `⊥`, read as `⊥`
    refine ⟨show readingCells.gradedIndex 6 ≤ readingCells.gradedIndex 8 by decide,
      fun u hu ↦ ?_⟩
    obtain rfl := huniq u hu
    exact fun _ _ ↦ ⟨fun _ ↦ rfl, fun h ↦ absurd h bot_ne_top,
      fun μ n _ h ↦ absurd h WithBot.bot_ne_coe⟩

/-- **Stable recovery schemes for the graded cap calibration exist at one input, at every `ξ`**:
a legal context type `T⁺` on two points, the embedding of a root on one point, a coface `D` of the
root with a new cell labelled `λ_ξ + 1`, and `γ = λ_ξ < λ_{ξ+1}`, satisfying the graded cap
calibration, with a stable recovery scheme.  So the conclusion of
`StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds at this input,
and the hypotheses of `StageType.IsStableRecoveryScheme.of_readsThroughCap` are met there.  This
is one input; the statement for every input is not proved. -/
theorem exists_isStableRecoveryScheme_gradedCap :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 2) (f : Fin 1 ↪ Fin 2)
      (P : StageType.{u} (blockStage (ξ + 1)) 1) (D : StageType.{u} (blockStage (ξ + 1)) 2)
      (γ : Ordinal.{u}), Tp.IsLegal ∧ restrictFace f Tp = some P ∧ D ∈ P.cofaces ∧
        γ < blockStage (ξ + 1) ∧ GradedCapCalibration ξ Tp f D γ ∧
        (∃ j : Fin D.card, Fin.last 1 ∈ D.toCellScheme.scope j ∧
          D.label j = ((blockStage ξ + ((1 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u})) ∧
        ∃ E : Scheme.{u} 3, Tp.IsStableRecoveryScheme f D γ E :=
  ⟨contextType ξ, rootEmb, rootType ξ, donorType ξ, blockStage ξ, isLegal_contextType ξ,
    restrictFace_rootType ξ, donorType_mem_cofaces ξ, blockStage_lt_blockStage_add_one ξ,
    gradedCapCalibration_contextType ξ, exists_newCell ξ, readingScheme,
    isStableRecoveryScheme_readingScheme ξ⟩

end VaughtConjecture.Continuation.StableRecoveryReading
