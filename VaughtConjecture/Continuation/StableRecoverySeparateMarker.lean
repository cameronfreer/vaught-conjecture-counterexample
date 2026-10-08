/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryAdmittedMarker

/-!
# The admitted completion for self-seeds at the arity one with a separate marker

Roadmap, Layer 3, 3.1, (R6) and 3.3 (the (R4) cap); the generalization of
`VaughtConjecture.Continuation.StableRecoveryAdmittedMarker` from the coupled-gate type to every
legal self-seed at the arity one.

## The requests

Let `I` be a seed on three points whose two coatom types are equal to a legal stage type `T` on two
points.  **Marked-cap data** on `T` (`StageType.MarkedCap`) are a cap `b`, a marker `m`, an offset
`R < 2`, and three sets of cells of `T` to be read as `⊥`, exactly, and from below, and a set of
cells of `T` forming the bottom class.  The (R4) cap requests on the doubled lower layer
(`Seed.requestsOf`): the cap and the marker are the private copies of `b` and `m` (`N = 2`); the
requested cells are the donor copies; the reference of a cell is the private copy of the cell of
`T` under it, at the offset `1`.  The admission (`Seed.admOf`) is capped correctness in the bottom
class of the private copies.  The marker at the cap (`m = b`) is the degenerate case.

## The hypotheses

* `hI : T.IsLegal`;
* `hb`: the cap has grade `2`;
* `hZ`: the cells read as `⊥` have grade `1` and read themselves at `⊥`;
* `hF`: the cells read exactly have grade `1`;
* `hfull`: every cell of grade `2` is read from below;
* `hlow`: a cell of grade `1` read from below is the marker;
* `hraise : T.HasFullRaise b`: every lawful labelling `s` of `T` has a lawful labelling equal to it
  at the cells of grade `1` and at least `s b` at every cell of grade `2`.

`hraise` holds when the cap is the only cell of grade `2` (`StageType.hasFullRaise_of_unique`) and
when the cells of grade `1` are dead and those of grade `2` labelled `⊤`
(`StageType.hasFullRaise_of_dead_top`).

## Results

* `Seed.isLegalBelowFullGrade_markedLayer`: under the hypotheses, **the admitted layer at the grade
  `2` over the doubled lower layer is legal below the full grade**.  The fills: at the cap `⊥`, the
  raise of the prescription (private coatom) and the prescription with the cells of grade `2` capped
  at `⊥` (donor coatom); at a positive cap `h`, the raise when the prescription is in the bottom
  class with its marker value above `h`, else the lift of `T` from `(univ, 1)` to `(univ, 2)`
  (private coatom), and that lift with the cells of grade `2` capped at `h` (donor coatom).
* `Seed.not_forall_privS_le_donS`: the hypothesis `hA` of the obstruction
  `Seed.not_isBountiful_admittedDoubledLower` fails for every lawful `s` and cell `y` of grade `1`
  with `s y < s b`.
* `Seed.not_isBountiful_markedLayer_of_marker_eq_cap`: `hlow` cannot be dropped: with the marker at
  the cap and a cell `y` of grade `1` read from below with `s y < s b` for a lawful `s` whose `⊥`
  cells are the bottom class and dead, the layer is not bountiful (the coupled-gate type is an
  instance, `CoupledGatedExtensionCounterexample.not_isBountiful_markedLayer_capCP`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open Ordinal hiding univ

namespace StageType

variable {α : Ordinal.{u}}

/-- **Marked-cap data** on a stage type on two points: the cap, the marker, the marker offset, the
cells read as `⊥`, exactly, and from below, and the bottom class. -/
structure MarkedCap (T : StageType.{u} α 2) where
  /-- The cap. -/
  cap : Fin T.card
  /-- The marker. -/
  marker : Fin T.card
  /-- The marker offset. -/
  R : ℕ
  /-- The marker offset is below `2`. -/
  R_lt_two : R < 2
  /-- The cells read as `⊥`. -/
  zeroCells : Set (Fin T.card)
  /-- The cells read exactly, through themselves at the offset `1`. -/
  exactCells : Set (Fin T.card)
  /-- The cells read from below, through the marker. -/
  readCells : Set (Fin T.card)
  /-- The bottom class: the cells that are `⊥`. -/
  botCells : Set (Fin T.card)

variable {T : StageType.{u} α 2}

namespace MarkedCap

variable (c : T.MarkedCap)

/-- The **marker value** of a labelling of `T`: the replaced marker capped at the cap. -/
noncomputable def value (s : Fin T.card → Label.{u}) : Label.{u} :=
  min (visibilityReplace 2 c.R (s c.marker)) (s c.cap)

/-- A labelling of `T` is **in the bottom class** when it is `⊥` exactly at the bottom cells. -/
def InClass (s : Fin T.card → Label.{u}) : Prop := ∀ z, s z = ⊥ ↔ z ∈ c.botCells

variable {c}

/-- The marker value is at most the cap. -/
theorem value_le_cap (s : Fin T.card → Label.{u}) : c.value s ≤ s c.cap := min_le_right _ _

/-- The marker values of two labellings agreeing under `h` self-visible at `2` agree under `h`. -/
theorem min_value_eq {h : Label.{u}} (hh : IsSelfVisible 2 h) {s t : Fin T.card → Label.{u}}
    (hst : ∀ z, min (s z) h = min (t z) h) : min (c.value s) h = min (c.value t) h := by
  unfold value
  rw [inf_inf_distrib_right, inf_inf_distrib_right (visibilityReplace 2 c.R (t c.marker)),
    Label.min_visibilityReplace_two_eq hh (by have := c.R_lt_two; omega) (hst c.marker),
    hst c.cap]

/-- The bottom class passes along an agreement capped at a positive cap. -/
theorem InClass.of_min_eq {s t : Fin T.card → Label.{u}} {h : Label.{u}} (hh : ⊥ < h)
    (hst : ∀ z, min (s z) h = min (t z) h) (hs : c.InClass s) : c.InClass t := by
  intro z
  rw [← hs z]
  have e := hst z
  constructor
  · intro ht
    rw [ht, min_bot_left] at e
    rcases min_eq_bot.mp e with h' | h'
    · exact h'
    · exact absurd h' hh.ne'
  · intro hs'
    rw [hs', min_bot_left] at e
    rcases min_eq_bot.mp e.symm with h' | h'
    · exact h'
    · exact absurd h' hh.ne'

end MarkedCap

/-- The cells of a stage type on two points have grade `1` or `2`. -/
theorem grade_one_or_two' (z : Fin T.card) :
    T.toCellScheme.grade z = 1 ∨ T.toCellScheme.grade z = 2 := by
  have h0 : 0 < T.toCellScheme.grade z := (T.isWellFormed.isWellFormed.gradedIndex_mem z).2.1
  have h2 := T.grade_le z
  omega

/-- **The raise at a cap `b`**: every lawful labelling `s` has a lawful labelling equal to it at
the cells of grade `1` and at least `s b` at every cell of grade `2`. -/
def HasFullRaise (T : StageType.{u} α 2) (b : Fin T.card) : Prop :=
  ∀ s : Fin T.card → Label.{u}, T.rows.IsLawful s → ∃ D : Fin T.card → Label.{u},
    T.rows.IsLawful D ∧ (∀ z, T.toCellScheme.grade z = 1 → D z = s z) ∧
      ∀ z, T.toCellScheme.grade z = 2 → s b ≤ D z

/-- The raise holds when the cap is the only cell of grade `2`: the labelling itself. -/
theorem hasFullRaise_of_unique {b : Fin T.card} (hu : ∀ z, T.toCellScheme.grade z = 2 → z = b) :
    T.HasFullRaise b :=
  fun s hs ↦ ⟨s, hs, fun _ _ ↦ rfl, fun z hz ↦ (hu z hz) ▸ le_rfl⟩

/-- The raise holds when the cells of grade `1` are dead and those of grade `2` are labelled `⊤`:
the labels capped at `s b`. -/
theorem hasFullRaise_of_dead_top (hd : T.HasDeadLowCells) (ht : T.HasTopFullCells)
    {b : Fin T.card} (hb : T.toCellScheme.grade b = 2) : T.HasFullRaise b := by
  intro s hs
  have hvs : IsSelfVisible 2 (s b) := hb ▸ hs.orderly b
  refine ⟨fun z ↦ min (T.label z) (s b),
    T.isLawful.min_const_of_isSelfVisible (K := 2) (fun d ↦ T.grade_le d) hvs, fun z hz ↦ ?_,
    fun z hz ↦ by simp only [ht z hz, min_top_left, le_refl]⟩
  simp only
  rw [hd.eq_bot T.isLawful hz, min_bot_left, hd.eq_bot hs hz]

/-- Capping the cells of grade `2` of a lawful labelling at `h` self-visible at `2`. -/
theorem isLawful_capTwo {s : Fin T.card → Label.{u}} (hs : T.rows.IsLawful s) {h : Label.{u}}
    (hh : IsSelfVisible 2 h) :
    T.rows.IsLawful fun z ↦ if T.toCellScheme.grade z = 2 then min (s z) h else s z :=
  hs.capTopGrade (fun d ↦ T.grade_le d) hh

end StageType

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 1} {hLR : I.left = I.right}

variable (I hLR) in
/-- The private copy of a cell of `T` in the doubled lower layer. -/
noncomputable abbrev leftCell (z : Fin I.left.card) : Fin (I.doubledLower hLR).card :=
  Fin.castAdd _ (StageType.faceCell I.restrictFace_left z)

variable (I hLR) in
/-- The donor copy of a cell of `T` in the doubled lower layer. -/
noncomputable abbrev rightCell (z : Fin I.left.card) : Fin (I.doubledLower hLR).card :=
  Fin.castAdd _ (StageType.faceCell (I.restrictFace_right_left hLR) z)

theorem grade_leftCell (z : Fin I.left.card) :
    (I.doubledLower hLR).toCellScheme.grade (I.leftCell hLR z) = I.left.toCellScheme.grade z :=
  (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
    (StageType.grade_faceCell I.restrictFace_left z)

theorem grade_rightCell (z : Fin I.left.card) :
    (I.doubledLower hLR).toCellScheme.grade (I.rightCell hLR z) = I.left.toCellScheme.grade z :=
  (Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
    (StageType.grade_faceCell (I.restrictFace_right_left hLR) z)

/-- **Symmetry at the grade `1`**: a lawful labelling of the doubled lower layer agrees at the two
copies of a cell of grade `1`. -/
theorem eq_of_grade_one (hI : I.left.IsLegal) {e : Fin (I.doubledLower hLR).card → Label.{u}}
    (he : (I.doubledLower hLR).rows.IsLawful e) {z : Fin I.left.card}
    (hz : I.left.toCellScheme.grade z = 1) : I.donS hLR e z = I.privS hLR e z :=
  eq_of_isLawfulBelow_lower hI (he.isLawfulBelow _) ((grade_rightCell z).trans hz)
    ((grade_leftCell z).trans hz) ((lowerCell_right z).trans (lowerCell_left z).symm)

/-- A lawful labelling of the doubled lower layer is self-visible at `1` at the private copy of a
cell of grade `1`. -/
theorem isSelfVisible_privS {e : Fin (I.doubledLower hLR).card → Label.{u}}
    (he : (I.doubledLower hLR).rows.IsLawful e) {z : Fin I.left.card}
    (hz : I.left.toCellScheme.grade z = 1) : IsSelfVisible 1 (I.privS hLR e z) :=
  ((grade_leftCell z).trans hz) ▸ he.orderly (I.leftCell hLR z)

/-- A lawful labelling of the doubled lower layer is self-visible at `2` at the private copy of a
cell of grade `2`. -/
theorem isSelfVisible_privS_two {e : Fin (I.doubledLower hLR).card → Label.{u}}
    (he : (I.doubledLower hLR).rows.IsLawful e) {z : Fin I.left.card}
    (hz : I.left.toCellScheme.grade z = 2) : IsSelfVisible 2 (I.privS hLR e z) :=
  ((grade_leftCell z).trans hz) ▸ he.orderly (I.leftCell hLR z)

/-! ### The requests -/

variable (I hLR) in
/-- **The (R4) cap requests of marked-cap data** on the doubled lower layer. -/
noncomputable def requestsOf (c : I.left.MarkedCap) :
    CapRequests (Fin (I.doubledLower hLR).card) where
  cap := I.leftCell hLR c.cap
  N := 2
  R := c.R
  R_lt_N := c.R_lt_two
  Z := I.rightCell hLR '' c.zeroCells
  F := I.rightCell hLR '' c.exactCells
  T := I.rightCell hLR '' c.readCells
  ref d := I.leftCell hLR (I.lowerCell hLR d)
  off _ := 1
  marker := I.leftCell hLR c.marker

variable (I hLR) in
/-- **The admission of marked-cap data**: capped correctness in the bottom class of the private
copies. -/
def admOf (c : I.left.MarkedCap) (e : Fin (I.doubledLower hLR).card → Label.{u}) : Prop :=
  (I.requestsOf hLR c).Admits (Set.range (I.leftCell hLR)) (I.leftCell hLR '' c.botCells) e

variable (I hLR) in
/-- **The admitted layer of marked-cap data** at the grade `2` over the doubled lower layer. -/
noncomputable abbrev markedLayer (c : I.left.MarkedCap) : Scheme.{u} 3 :=
  (I.doubledLower hLR).admittedFieldLayer 2 (I.admOf hLR c) (I.not_univ_two_le_doubledLower hLR)

variable {c : I.left.MarkedCap}

/-- The bottom class of a state is that of its private copy. -/
theorem inBottomClass_iff {e : Fin (I.doubledLower hLR).card → Label.{u}} :
    InBottomClass (Set.range (I.leftCell hLR)) (I.leftCell hLR '' c.botCells) e ↔
      c.InClass (I.privS hLR e) := by
  have hinj (z z' : Fin I.left.card) (h : I.leftCell hLR z = I.leftCell hLR z') : z = z' := by
    have := congrArg (I.lowerCell hLR) h
    rwa [lowerCell_left, lowerCell_left] at this
  have key (z : Fin I.left.card) : I.leftCell hLR z ∈ I.leftCell hLR '' c.botCells ↔
      z ∈ c.botCells :=
    ⟨fun ⟨z', hz', he⟩ ↦ hinj _ _ he ▸ hz', fun hz ↦ ⟨z, hz, rfl⟩⟩
  constructor
  · intro hcl z
    exact (hcl _ ⟨z, rfl⟩).trans (key z)
  · rintro hcl _ ⟨z, rfl⟩
    exact (hcl z).trans (key z).symm

/-- **Correctness**: a lawful state whose donor copy reads every cell of grade `2` at least as the
marker value of its private copy is correct. -/
theorem isCorrect_requestsOf (hI : I.left.IsLegal)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    {e : Fin (I.doubledLower hLR).card → Label.{u}} (he : (I.doubledLower hLR).rows.IsLawful e)
    (h4 : ∀ y, I.left.toCellScheme.grade y = 2 → c.value (I.privS hLR e) ≤ I.donS hLR e y) :
    (I.requestsOf hLR c).IsCorrect e where
  eq_bot := by
    rintro _ ⟨z, hz, rfl⟩
    change min (I.donS hLR e z) (I.privS hLR e c.cap) = ⊥
    rw [eq_of_grade_one hI he (hZ z hz).1, I.eq_bot_privS_of_row_self hLR (hZ z hz).2 he,
      min_bot_left]
  eq_refValue := by
    rintro _ ⟨f, hf, rfl⟩
    change min (I.donS hLR e f) (I.privS hLR e c.cap) =
      min (visibilityReplace 2 1 (e (I.leftCell hLR (I.lowerCell hLR (I.rightCell hLR f)))))
        (I.privS hLR e c.cap)
    rw [lowerCell_right]
    change min (I.donS hLR e f) _ = min (visibilityReplace 2 1 (I.privS hLR e f)) _
    rw [eq_of_grade_one hI he (hF f hf),
      Label.visibilityReplace_two_one (isSelfVisible_privS he (hF f hf))]
  markerValue_le := by
    rintro _ ⟨y, hy, rfl⟩
    change c.value (I.privS hLR e) ≤ min (I.donS hLR e y) (I.privS hLR e c.cap)
    rcases grade_one_or_two' y with h1 | h2
    · have hym := hlow y hy h1
      subst hym
      rw [eq_of_grade_one hI he h1]
      exact min_le_min (Label.visibilityReplace_two_le (isSelfVisible_privS he h1)
        (by have := c.R_lt_two; omega)) le_rfl
    · exact le_min (h4 y h2) (MarkedCap.value_le_cap _)

/-- Correctness gives the reading of every cell read from below. -/
theorem le_of_isCorrect_requestsOf {e : Fin (I.doubledLower hLR).card → Label.{u}}
    (hc : (I.requestsOf hLR c).IsCorrect e) {y : Fin I.left.card} (hy : y ∈ c.readCells) :
    c.value (I.privS hLR e) ≤ I.donS hLR e y :=
  (hc.markerValue_le _ ⟨y, hy, rfl⟩).trans (min_le_left _ _)

/-- The reading of the cells of grade `2` by an admitted state in the bottom class. -/
theorem le_of_admOf (hfull : ∀ z, I.left.toCellScheme.grade z = 2 → z ∈ c.readCells)
    {e : Fin (I.doubledLower hLR).card → Label.{u}} (hA : I.admOf hLR c e)
    (hc : c.InClass (I.privS hLR e)) (y : Fin I.left.card)
    (hy : I.left.toCellScheme.grade y = 2) : c.value (I.privS hLR e) ≤ I.donS hLR e y :=
  le_of_isCorrect_requestsOf (hA (inBottomClass_iff.mpr hc)) (hfull y hy)

private theorem grade_le_two_doubled (d : Fin (I.doubledLower hLR).card) :
    (I.doubledLower hLR).toCellScheme.grade d ≤ 2 := by
  induction d using Fin.addCases with
  | left a =>
    rw [Scheme.appendFullCellsScheme_grade_castAdd]
    exact Nat.lt_succ_iff.mp (I.grade_lt a)
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; omega

/-- **The orbit code of an admitted state is admitted.** -/
theorem admOf_orbitCode {W : Fin (I.doubledLower hLR).card → Label.{u}} (hadm : I.admOf hLR c W) :
    I.admOf hLR c
      (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsp : (I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W = W :=
    funext fun d ↦ CellScheme.splice_of_le (grade_le_two_doubled d)
  rw [hsp]
  have hcode : orbitCode 2 W = orbitMap 2 W ∘ W := funext fun d ↦ orbitCode_apply d
  intro hcl
  have hcl' : InBottomClass (Set.range (I.leftCell hLR)) (I.leftCell hLR '' c.botCells) W := by
    intro d hd
    rw [← hcl d hd, hcode, Function.comp_apply, orbitMap_eq_bot_iff]
  rw [hcode]
  exact (hadm hcl').comp (isWitness_orbitMap 2 W) le_rfl fun _ _ ↦ by
    change 1 ≤ 2
    omega

/-- A state outside the bottom class is admitted. -/
theorem admOf_of_not {W : Fin (I.doubledLower hLR).card → Label.{u}}
    (hn : ¬ c.InClass (I.privS hLR W)) : I.admOf hLR c W :=
  fun hcl ↦ absurd (inBottomClass_iff.mp hcl) hn

/-- A lawful state agrees with its private copy at the copies of full scope. -/
theorem natAdd_eq_privS (hI : I.left.IsLegal) {e : Fin (I.doubledLower hLR).card → Label.{u}}
    (he : (I.doubledLower hLR).rows.IsLawful e) (i : Fin (I.nFull 1)) :
    e (Fin.natAdd _ i) = I.privS hLR e (I.left.toScheme.fullCell 1 i) := by
  have hg1 : I.left.toCellScheme.grade (I.left.toScheme.fullCell 1 i) = 1 :=
    congrArg Prod.snd (Scheme.gradedIndex_fullCell 1 i)
  exact eq_of_isLawfulBelow_lower hI (he.isLawfulBelow _)
    (Scheme.appendFullCellsScheme_grade_natAdd _ _ _ i)
    ((Scheme.appendFullCellsScheme_grade_castAdd _ _ _ _).trans
      ((StageType.grade_faceCell _ _).trans hg1))
    ((lowerCell_natAdd i).trans (lowerCell_left _).symm)

/-- **The capped agreement of a glued state**: a state with private copy `sL` and donor copy `D`,
reading its copies of full scope through `sL`, agrees under `h` with a lawful `a` whose copies
agree with `sL` and `D` under `h`. -/
theorem min_eq_of_copies (hI : I.left.IsLegal) {h : Label.{u}}
    {a g : Fin (I.doubledLower hLR).card → Label.{u}} (ha : (I.doubledLower hLR).rows.IsLawful a)
    (hgN : ∀ i, g (Fin.natAdd _ i) = I.privS hLR g (I.left.toScheme.fullCell 1 i))
    (hL : ∀ z, min (I.privS hLR g z) h = min (I.privS hLR a z) h)
    (hR : ∀ z, min (I.donS hLR g z) h = min (I.donS hLR a z) h) (d) :
    min (g d) h = min (a d) h := by
  induction d using Fin.addCases with
  | right i =>
    rw [hgN, natAdd_eq_privS hI ha i]
    exact hL _
  | left e =>
    rcases I.eq_faceCell_or hLR e with he | he
    · rw [← he]
      exact hL _
    · rw [← he]
      exact hR _

/-- **Admission of a glued state** from the reading of the cells of grade `2` by its donor copy. -/
theorem admOf_orbitCode_of_le (hI : I.left.IsLegal)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    {g : Fin (I.doubledLower hLR).card → Label.{u}} (hg : (I.doubledLower hLR).rows.IsLawful g)
    (h4 : c.InClass (I.privS hLR g) →
      ∀ y, I.left.toCellScheme.grade y = 2 → c.value (I.privS hLR g) ≤ I.donS hLR g y) :
    I.admOf hLR c (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) g)) := by
  by_cases hcl : c.InClass (I.privS hLR g)
  · exact admOf_orbitCode (isCorrect_requestsOf hI hZ hF hlow hg (h4 hcl)).admits
  · exact admOf_orbitCode (admOf_of_not hcl)

/-! ### The fills -/

/-- **The donor copy of the fill at a positive cap.** -/
theorem exists_donorFill (hI : I.left.IsLegal) (hraise : I.left.HasFullRaise c.cap)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {sL eL eR : Fin I.left.card → Label.{u}} (hsL : I.left.rows.IsLawful sL)
    (heR : I.left.rows.IsLawful eR) (hagL : ∀ z, min (sL z) h = min (eL z) h)
    (hsym : ∀ z, I.left.toCellScheme.grade z = 1 → eR z = eL z)
    (hA : c.InClass eL → ∀ y, I.left.toCellScheme.grade y = 2 → c.value eL ≤ eR y) :
    ∃ D : Fin I.left.card → Label.{u}, I.left.rows.IsLawful D ∧
      (∀ z, I.left.toCellScheme.grade z = 1 → D z = sL z) ∧ (∀ z, min (D z) h = min (eR z) h) ∧
      (c.InClass sL → ∀ y, I.left.toCellScheme.grade y = 2 → c.value sL ≤ D y) := by
  have hm := MarkedCap.min_value_eq (c := c) hh hagL
  obtain ⟨r, hr, hrsL, hreR⟩ := StageType.exists_lift_one_two hI hsL heR hh
    fun z hz ↦ (hagL z).trans (by rw [hsym z hz])
  by_cases hc : c.InClass sL ∧ h < c.value sL
  · have hma : h ≤ c.value eL := by
      have e1 := hm
      rw [min_eq_right hc.2.le] at e1
      exact min_eq_right_iff.mp e1.symm
    have hcl := hc.1.of_min_eq hbh hagL
    obtain ⟨D, hD, hD1, hD2⟩ := hraise sL hsL
    refine ⟨D, hD, hD1, fun z ↦ ?_,
      fun _ y hy ↦ (MarkedCap.value_le_cap _).trans (hD2 y hy)⟩
    rcases grade_one_or_two' z with hz | hz
    · rw [hD1 z hz, hagL z, hsym z hz]
    · rw [min_eq_right (hc.2.le.trans ((MarkedCap.value_le_cap _).trans (hD2 z hz))),
        min_eq_right (hma.trans (hA hcl z hz))]
  · refine ⟨r, hr, hrsL, hreR, fun hcl y hy ↦ ?_⟩
    have hle : c.value sL ≤ h := not_lt.mp fun hlt ↦ hc ⟨hcl, hlt⟩
    calc c.value sL = min (c.value sL) h := (min_eq_left hle).symm
      _ = min (c.value eL) h := hm
      _ ≤ min (eR y) h := min_le_min_right _ (hA (hcl.of_min_eq hbh hagL) y hy)
      _ = min (r y) h := (hreR y).symm
      _ ≤ r y := min_le_left _ _

/-- **The private copy of the fill at a positive cap**: the lift of `T` from `(univ, 1)` to
`(univ, 2)` of the prescription against the private copy of the entry, capped at `h` at the cells
of grade `2`. -/
theorem exists_privateFill (hI : I.left.IsLegal) (hb : I.left.toCellScheme.grade c.cap = 2)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {fR eL eR : Fin I.left.card → Label.{u}} (hfR : I.left.rows.IsLawful fR)
    (heL : I.left.rows.IsLawful eL) (hagR : ∀ z, min (fR z) h = min (eR z) h)
    (hsym : ∀ z, I.left.toCellScheme.grade z = 1 → eR z = eL z)
    (hA : c.InClass eL → ∀ y, I.left.toCellScheme.grade y = 2 → c.value eL ≤ eR y) :
    ∃ L : Fin I.left.card → Label.{u}, I.left.rows.IsLawful L ∧
      (∀ z, I.left.toCellScheme.grade z = 1 → fR z = L z) ∧ (∀ z, min (L z) h = min (eL z) h) ∧
      (c.InClass L → ∀ y, I.left.toCellScheme.grade y = 2 → c.value L ≤ fR y) := by
  obtain ⟨r, hr, hrfR, hreL⟩ := StageType.exists_lift_one_two hI hfR heL hh
    fun z hz ↦ (hagR z).trans (by rw [hsym z hz])
  have hLa (z : Fin I.left.card) :
      min (if I.left.toCellScheme.grade z = 2 then min (r z) h else r z) h = min (eL z) h := by
    split_ifs
    · rw [min_assoc, min_self, hreL]
    · exact hreL z
  refine ⟨_, StageType.isLawful_capTwo hr hh, fun z hz ↦ ?_, hLa, fun hcl y hy ↦ ?_⟩
  · simp only [show I.left.toCellScheme.grade z ≠ 2 by omega, ↓reduceIte]
    exact (hrfR z hz).symm
  · have hle : c.value (fun z ↦ if I.left.toCellScheme.grade z = 2 then min (r z) h else r z) ≤
        h := by
      refine (MarkedCap.value_le_cap _).trans ?_
      simp only [hb, ↓reduceIte]
      exact min_le_right _ _
    calc _ = min (c.value (fun z ↦ if I.left.toCellScheme.grade z = 2 then min (r z) h
            else r z)) h := (min_eq_left hle).symm
      _ = min (c.value eL) h := MarkedCap.min_value_eq hh hLa
      _ ≤ min (eR y) h := min_le_min_right _ (hA (hcl.of_min_eq hbh hLa) y hy)
      _ = min (fR y) h := (hagR y).symm
      _ ≤ fR y := min_le_left _ _

/-! ### The provisions -/

/-- **The lift provision at the cap `⊥` from the private coatom**: the private copy of the
prescription glued to its raise. -/
theorem botProvision_left (hI : I.left.IsLegal) (hraise : I.left.HasFullRaise c.cap)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d)) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      I.admOf hLR c (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsL := isLawful_privS hf
  obtain ⟨D, hD, hD1, hD2⟩ := hraise _ hsL
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glueSym hI hsL hD hD1
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_,
    admOf_orbitCode_of_le hI hZ hF hlow hg fun _ y hy ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_belowS hd
    exact congrFun hgL z
  · rw [hgL, hgR]
    exact (MarkedCap.value_le_cap _).trans (hD2 y hy)

/-- **The lift provision at the cap `⊥` from the donor coatom**: the donor copy of the
prescription, glued to it with the cells of grade `2` capped at `⊥`. -/
theorem botProvision_right (hI : I.left.IsLegal) (hb : I.left.toCellScheme.grade c.cap = 2)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d)) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2), W d = f d) ∧
      I.admOf hLR c (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hfR := isLawful_donS hf
  have hL := StageType.isLawful_capTwo hfR (isSelfVisible_bot 2)
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glueSym hI hL hfR fun z hz ↦ by
    simp only [show I.left.toCellScheme.grade z ≠ 2 by omega, ↓reduceIte]
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_,
    admOf_orbitCode_of_le hI hZ hF hlow hg fun _ y _ ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_belowS hd
    exact congrFun hgR z
  · rw [hgL, hgR]
    refine (MarkedCap.value_le_cap _).trans ?_
    simp only [hb, ↓reduceIte, min_bot_right, bot_le]

/-- **The lift provision at a positive cap from the private coatom**: the private copy of the
prescription glued to `exists_donorFill`. -/
theorem capProvision_left (hI : I.left.IsLegal) (hraise : I.left.HasFullRaise c.cap)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hfull : ∀ z, I.left.toCellScheme.grade z = 2 → z ∈ c.readCells)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin (I.doubledLower hLR).card → Label.{u}} (ha : (I.doubledLower hLR).rows.IsLawful a)
    (hA : I.admOf hLR c a) {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.last 2), 2) (fun d ↦ f d))
    (hfa : ∀ d ∈ (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2),
      min (f d) h = min (a d) h) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below (univ.erase (Fin.last 2), 2), W d = f d) ∧
      (∀ d, (I.doubledLower hLR).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admOf hLR c (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hsL := isLawful_privS hf
  have heR := isLawful_donS (ha.isLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2))
  have hagL (z : Fin I.left.card) : min (I.privS hLR f z) h = min (I.privS hLR a z) h :=
    hfa _ (left_mem_belowS z)
  obtain ⟨D, hD, hD1, hDa, hDT⟩ := exists_donorFill hI hraise hh hbh hsL heR hagL
    (fun z hz ↦ eq_of_grade_one hI ha hz) (le_of_admOf hfull hA)
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glueSym hI hsL hD hD1
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_,
    fun d _ ↦ min_eq_of_copies hI ha (fun i ↦ (hgN i).trans (congrFun hgL _).symm)
      (fun z ↦ by rw [hgL]; exact hagL z)
      (fun z ↦ by rw [hgR]; exact hDa z) d,
    admOf_orbitCode_of_le hI hZ hF hlow hg fun hcl ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_left_of_mem_belowS hd
    exact congrFun hgL z
  · rw [hgL, hgR] at *
    exact hDT hcl

/-- **The lift provision at a positive cap from the donor coatom**: `exists_privateFill` glued to
the donor copy of the prescription. -/
theorem capProvision_right (hI : I.left.IsLegal) (hb : I.left.toCellScheme.grade c.cap = 2)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hfull : ∀ z, I.left.toCellScheme.grade z = 2 → z ∈ c.readCells)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    {h : Label.{u}} (hh : IsSelfVisible 2 h) (hbh : ⊥ < h)
    {a : Fin (I.doubledLower hLR).card → Label.{u}} (ha : (I.doubledLower hLR).rows.IsLawful a)
    (hA : I.admOf hLR c a) {f : Fin (I.doubledLower hLR).card → Label.{u}}
    (hf : (I.doubledLower hLR).rows.IsLawfulBelow (univ.erase (Fin.castSucc (Fin.last 1)), 2)
      (fun d ↦ f d))
    (hfa : ∀ d ∈ (I.doubledLower hLR).toCellScheme.below
      (univ.erase (Fin.castSucc (Fin.last 1)), 2), min (f d) h = min (a d) h) :
    ∃ W : Fin (I.doubledLower hLR).card → Label.{u},
      (I.doubledLower hLR).rows.IsLawfulBelow ((univ : Finset (Fin 3)), 2) (fun d ↦ W d) ∧
      (∀ d ∈ (I.doubledLower hLR).toCellScheme.below
        (univ.erase (Fin.castSucc (Fin.last 1)), 2), W d = f d) ∧
      (∀ d, (I.doubledLower hLR).toCellScheme.grade d ≤ 2 → min (W d) h = min (a d) h) ∧
      I.admOf hLR c (orbitCode 2 ((I.doubledLower hLR).toCellScheme.splice 2 (fun _ ↦ ⊥) W)) := by
  have hfR := isLawful_donS hf
  have heL := isLawful_privS (ha.isLawfulBelow (univ.erase (Fin.last 2), 2))
  have hagR (z : Fin I.left.card) : min (I.donS hLR f z) h = min (I.donS hLR a z) h :=
    hfa _ (right_mem_belowS z)
  obtain ⟨L, hL, hL1, hLa, hLT⟩ := exists_privateFill hI hb hh hbh hfR heL hagR
    (fun z hz ↦ eq_of_grade_one hI ha hz) (le_of_admOf hfull hA)
  obtain ⟨g, hg, hgL, hgR, hgN⟩ := exists_glueSym hI hL hfR hL1
  refine ⟨g, hg.isLawfulBelow _, fun d hd ↦ ?_,
    fun d _ ↦ min_eq_of_copies hI ha (fun i ↦ (hgN i).trans (congrFun hgL _).symm)
      (fun z ↦ by rw [hgL]; exact hLa z)
      (fun z ↦ by rw [hgR]; exact hagR z) d,
    admOf_orbitCode_of_le hI hZ hF hlow hg fun hcl ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := exists_right_of_mem_belowS hd
    exact congrFun hgR z
  · rw [hgL, hgR] at *
    exact hLT hcl

/-! ### Legality -/

private theorem erase_ne_univ' (x : Fin 3) : univ.erase x ≠ univ :=
  fun he ↦ Finset.notMem_erase x univ (he.symm ▸ mem_univ x)

/-- **The lift from the private coatom into the admitted layer.** -/
theorem cappedLift_markedLayer_left (hI : I.left.IsLegal) (hraise : I.left.HasFullRaise c.cap)
    (hb : I.left.toCellScheme.grade c.cap = 2)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hfull : ∀ z, I.left.toCellScheme.grade z = 2 → z ∈ c.readCells)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker) :
    (I.markedLayer hLR c).rows.CappedLift (X := (univ.erase (Fin.last 2), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_doubledLower hLR)
    (I.isConsistent_doubledLower hLR hI) (CapRequests.admits_bot _ _ _) (erase_ne_univ' _)
    ⟨_, gradedIndex_left_cap hb⟩ (cappedLift_doubledLower_left hI)
    (fun _ hf ↦ botProvision_left hI hraise hZ hF hlow hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦
      capProvision_left hI hraise hZ hF hfull hlow hh hbh ha hA hf hfa)

/-- **The lift from the donor coatom into the admitted layer.** -/
theorem cappedLift_markedLayer_right (hI : I.left.IsLegal)
    (hb : I.left.toCellScheme.grade c.cap = 2)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hfull : ∀ z, I.left.toCellScheme.grade z = 2 → z ∈ c.readCells)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker) :
    (I.markedLayer hLR c).rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last 1)), 2))
      (Y := ((univ : Finset (Fin 3)), 2)) ⟨erase_subset _ _, le_rfl⟩ :=
  Scheme.cappedLift_admittedFieldLayer (j := 1) (hS := I.not_univ_two_le_doubledLower hLR)
    (I.isConsistent_doubledLower hLR hI) (CapRequests.admits_bot _ _ _) (erase_ne_univ' _)
    ⟨_, gradedIndex_right_cap hb⟩ (cappedLift_doubledLower_right hI)
    (fun _ hf ↦ botProvision_right hI hb hZ hF hlow hf)
    (fun _ hh _ hbh _ ha hA _ hf hfa ↦
      capProvision_right hI hb hZ hF hfull hlow hh hbh ha hA hf hfa)

/-- **The admitted completion for self-seeds at the arity one with marked-cap data.**  For a seed
whose two coatom types equal a legal stage type `T` on two points, and marked-cap data on `T` with
the cap of grade `2`, the cells read as `⊥` dead of grade `1`, the cells read exactly of grade `1`,
every cell of grade `2` read from below, the marker the only cell of grade `1` read from below, and
the raise of `T` at the cap, the admitted layer at the grade `2` over the doubled lower layer is
legal below the full grade. -/
theorem isLegalBelowFullGrade_markedLayer (hI : I.left.IsLegal)
    (hb : I.left.toCellScheme.grade c.cap = 2)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hfull : ∀ z, I.left.toCellScheme.grade z = 2 → z ∈ c.readCells)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    (hraise : I.left.HasFullRaise c.cap) :
    (I.markedLayer hLR c).IsLegalBelowFullGrade :=
  I.isLegalBelowFullGrade_admittedDoubledLower hLR hI (CapRequests.admits_bot _ _ _)
    (I.isBountiful_admittedDoubledLower hLR (cappedLift_doubledLower_left hI)
      (cappedLift_doubledLower_right hI)
      (cappedLift_markedLayer_left hI hraise hb hZ hF hfull hlow)
      (cappedLift_markedLayer_right hI hb hZ hF hfull hlow))

/-! ### The obstruction -/

/-- **The hypothesis of the obstruction fails** (`Seed.not_isBountiful_admittedDoubledLower`, its
`hA`): for a lawful `s` and a cell `y` of grade `1` with `s y < s b`, the private copy `s` glued to
its raise is admitted, has private copy `s`, and reads the donor copy of `y` below the private
cap. -/
theorem not_forall_privS_le_donS (hI : I.left.IsLegal) (hraise : I.left.HasFullRaise c.cap)
    (hZ : ∀ z ∈ c.zeroCells, I.left.toCellScheme.grade z = 1 ∧
      I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hF : ∀ f ∈ c.exactCells, I.left.toCellScheme.grade f = 1)
    (hlow : ∀ y ∈ c.readCells, I.left.toCellScheme.grade y = 1 → y = c.marker)
    {s : Fin I.left.card → Label.{u}} (hs : I.left.rows.IsLawful s) {y : Fin I.left.card}
    (hy : I.left.toCellScheme.grade y = 1) (hlt : s y < s c.cap) :
    ¬ ∀ e, (I.doubledLower hLR).rows.IsLawful e → I.admOf hLR c e →
      (∀ z, s z ≠ ⊥ → I.privS hLR e z ≠ ⊥) → I.privS hLR e c.cap ≤ I.donS hLR e y := by
  intro hA
  obtain ⟨D, hD, hD1, hD2⟩ := hraise s hs
  obtain ⟨g, hg, hgL, hgR, -⟩ := exists_glueSym hI hs hD hD1
  have hadm : I.admOf hLR c g := (isCorrect_requestsOf hI hZ hF hlow hg fun y' hy' ↦ by
    rw [hgL, hgR]; exact (MarkedCap.value_le_cap _).trans (hD2 y' hy')).admits
  have key := hA g hg hadm fun z hz ↦ by rw [hgL]; exact hz
  rw [hgL, hgR, hD1 y hy] at key
  exact absurd key (not_le.mpr hlt)

/-- **The marker at the cap with a cell of grade `1` read from below** (`hlow` dropped): for a
lawful `s` whose `⊥` cells are the bottom class, all dead, and a cell `y` of grade `1` read from
below with `s y < s b`, the admitted layer is not bountiful. -/
theorem not_isBountiful_markedLayer_of_marker_eq_cap
    (hb : I.left.toCellScheme.grade c.cap = 2) (hm : c.marker = c.cap)
    {y : Fin I.left.card} (hyT : y ∈ c.readCells) (hy : I.left.toCellScheme.grade y = 1)
    {s : Fin I.left.card → Label.{u}} (hs : I.left.rows.IsLawful s) (hlt : s y < s c.cap)
    (hc1 : ∃ x, I.left.toCellScheme.gradedIndex x = ((univ : Finset (Fin 2)), 1))
    (hdead : ∀ z ∈ c.botCells, I.left.rows.row z ⟨z, CellScheme.mem_below_gradedIndex _ z⟩ = ⊥)
    (hbot : ∀ z ∉ c.botCells, s z ≠ ⊥) :
    ¬ (I.markedLayer hLR c).rows.IsBountiful :=
  I.not_isBountiful_admittedDoubledLower hLR (CapRequests.admits_bot _ _ _) hs hb hy hlt hc1
    fun e he hadm hne ↦ by
      have hcl : c.InClass (I.privS hLR e) := fun z ↦ by
        by_cases hz : z ∈ c.botCells
        · exact ⟨fun _ ↦ hz, fun _ ↦ I.eq_bot_privS_of_row_self hLR (hdead z hz) he⟩
        · exact ⟨fun h ↦ absurd h (hne z (hbot z hz)), fun h ↦ absurd h hz⟩
      have h3 := le_of_isCorrect_requestsOf (hadm (inBottomClass_iff.mpr hcl)) hyT
      unfold MarkedCap.value at h3
      rwa [hm, (isSelfVisible_privS_two he hb).visibilityReplace_eq, min_self] at h3

end Seed

/-! ### Instances -/

namespace CoupledGatedExtensionCounterexample

variable (α : Ordinal.{u}) (hα : 1 < α)

/-- **The separate marker at the coupled-gate type**: cap `C = 4`, marker `z₂ = 3`, offset `R`;
`⊥` at `1`, exactly at `z₁ = 2`, from below at `3` and `4`; bottom class `{0, 1}`. -/
def capSepCP (R : ℕ) (hR : R < 2) : (seedCP α hα).left.MarkedCap where
  cap := ((4 : Fin 5) : Fin (P α hα).card)
  marker := ((3 : Fin 5) : Fin (P α hα).card)
  R := R
  R_lt_two := hR
  zeroCells := ({1} : Set (Fin 5))
  exactCells := ({2} : Set (Fin 5))
  readCells := ({3, 4} : Set (Fin 5))
  botCells := ({0, 1} : Set (Fin 5))

/-- **The marker at the cap at the coupled-gate type** (the requests of `requestsCP`): cap and
marker `C = 4`; the rest as `capSepCP`. -/
def capCP : (seedCP α hα).left.MarkedCap where
  cap := ((4 : Fin 5) : Fin (P α hα).card)
  marker := ((4 : Fin 5) : Fin (P α hα).card)
  R := 0
  R_lt_two := two_pos
  zeroCells := ({1} : Set (Fin 5))
  exactCells := ({2} : Set (Fin 5))
  readCells := ({3, 4} : Set (Fin 5))
  botCells := ({0, 1} : Set (Fin 5))

/-- **The separate marker at the coupled-gate type is an instance**: legal below the full grade. -/
theorem isLegalBelowFullGrade_markedLayer_capSepCP (R : ℕ) (hR : R < 2) :
    ((seedCP α hα).markedLayer rfl (capSepCP α hα R hR)).IsLegalBelowFullGrade :=
  Seed.isLegalBelowFullGrade_markedLayer (isLegal_P α hα) rfl
    (by rintro z rfl; exact ⟨rfl, rfl⟩) (by rintro z rfl; rfl)
    (by
      change ∀ z : Fin 5, cellGrade z = 2 → z = 3 ∨ z = 4
      decide)
    (by
      change ∀ y : Fin 5, y = 3 ∨ y = 4 → cellGrade y = 1 → y = 3
      decide)
    (StageType.hasFullRaise_of_unique (by
      change ∀ z : Fin 5, cellGrade z = 2 → z = 4
      decide))

private theorem omegaAdd_one_lt_two'' : omegaAdd.{u} 1 < omegaAdd 2 := by
  unfold omegaAdd
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_iff_left _).mpr
      ((Nat.cast_lt (α := Ordinal.{u})).mpr (by norm_num : (1 : ℕ) < 2))))

/-- **`hlow` cannot be dropped**: with the marker at the cap and the cell `z₂` of grade `1` read
from below, the admitted layer at the coupled-gate type is not bountiful (prescription: the row of
the full cell, `⊥, ⊥, 1, ω + 1, ω + 2`). -/
theorem not_isBountiful_markedLayer_capCP :
    ¬ ((seedCP α hα).markedLayer rfl (capCP α hα)).rows.IsBountiful := by
  have hg4 : (P α hα).toCellScheme.gradedIndex (4 : Fin 5) = ((univ : Finset (Fin 2)), 2) := rfl
  have hs := Scheme.isLawful_rowAt (isLegal_P α hα).isConsistent hg4
  have hrow (z : Fin 5) : (P α hα).rowAt (4 : Fin 5) z = code z := by
    rw [Scheme.rowAt_of_mem (show z ∈ (P α hα).toCellScheme.below
      ((P α hα).toCellScheme.gradedIndex (4 : Fin 5)) by
        rw [hg4]; exact ⟨subset_univ _, (P α hα).grade_le z⟩)]
    fin_cases z <;> rfl
  refine Seed.not_isBountiful_markedLayer_of_marker_eq_cap rfl rfl
    (y := ((3 : Fin 5) : Fin (P α hα).card)) (Or.inl rfl) rfl hs ?_ ⟨(2 : Fin 5), rfl⟩
    (by rintro z (rfl | rfl) <;> rfl) ?_
  · change (P α hα).rowAt (4 : Fin 5) (3 : Fin 5) < (P α hα).rowAt (4 : Fin 5) (4 : Fin 5)
    rw [hrow, hrow]
    exact omegaAdd_one_lt_two''
  · change ∀ z : Fin 5, ¬ (z = 0 ∨ z = 1) → (P α hα).rowAt (4 : Fin 5) z ≠ ⊥
    intro z hz
    rw [hrow]
    fin_cases z
    · exact absurd (Or.inl rfl) hz
    · exact absurd (Or.inr rfl) hz
    all_goals exact WithBot.coe_ne_bot

end CoupledGatedExtensionCounterexample

namespace GatedExtensionCounterexample

variable (α : Ordinal.{u})

/-- **The marker at the cap at the private type `P`** (the degenerate case): cap and marker the
full cell `4`, offset `R`; nothing read as `⊥` or exactly; both full cells read from below; bottom
class the dead cells `{0, 1, 2}`. -/
def capP (R : ℕ) (hR : R < 2) : (seedP α).left.MarkedCap where
  cap := ((4 : Fin 5) : Fin (P α).card)
  marker := ((4 : Fin 5) : Fin (P α).card)
  R := R
  R_lt_two := hR
  zeroCells := ∅
  exactCells := ∅
  readCells := ({3, 4} : Set (Fin 5))
  botCells := ({0, 1, 2} : Set (Fin 5))

/-- **The marker at the cap at `P` is an instance**: legal below the full grade (the raise from the
dead cells of grade `1` and the full cells labelled `⊤`). -/
theorem isLegalBelowFullGrade_markedLayer_capP (R : ℕ) (hR : R < 2) :
    ((seedP α).markedLayer rfl (capP α R hR)).IsLegalBelowFullGrade :=
  Seed.isLegalBelowFullGrade_markedLayer (isLegal_P α) rfl (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    (by
      change ∀ z : Fin 5, cellGrade z = 2 → z = 3 ∨ z = 4
      decide)
    (by
      change ∀ y : Fin 5, y = 3 ∨ y = 4 → cellGrade y = 1 → y = 4
      decide)
    (StageType.hasFullRaise_of_dead_top (hasDeadLowCells_P α) (hasTopFullCells_P α) rfl)

end GatedExtensionCounterexample

end VaughtConjecture
