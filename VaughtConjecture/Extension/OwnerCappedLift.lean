/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AlignedEncoding

/-!
# Owner-capped lifts

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.4 (the alignment of owners; each lift preserves its cap
on every coordinate); Layer 1 (bountifulness, cap by cap); semantic contract, item 3.

Fix `C ⊆ B`, a grade `j`, the pairs `X = (C, j + 1) ≤ Y = (B, j + 1)`, and a cap `c` self-visible
at `j + 1`.  The one-grade lift (`CellScheme.Rows.cappedLift_of_ownerCappedLift`) needs
owner-capped lifts at every such cap (`CellScheme.Rows.HasOwnerCappedLifts`): for a prescription
`p` below `X`, an ambient `q` below `Y` with the same observation at `c` below `X`, and an owner
`o` of `p` with `c < p o`, a labelling lawful below `Y` that reads `min p (p o)` below `X` and has
the observation of `q` at `c` at every cell below `Y`.  This file constructs them from explicit
properties of the rows.

**A positive cap, from a source** (`CellScheme.Rows.hasOwnerCappedLifts_of_source`).  Suppose
that every ambient `q` that reaches `c` at a cell of grade `j + 1` below `Y` has a **source**: a
labelling `S` lawful below `Y`, short at `j + 1` and never the formal top, with a witness `τ`
bounded by grade `j + 1`, `τ ≤ c`, and `τ ∘ S = min q c`, such that the rows **lift capped at the
ambient `S`** from `X` to `Y` at the positive caps (`CellScheme.Rows.CappedLiftAt`: the special
case of `CellScheme.Rows.CappedLift` in which the ambient is `S`, the cap is positive, and the
prescription is never the formal top).  Then the rows have owner-capped lifts at `c > ⊥`.  The
restriction of `S` to `X` is a source of the owner-local alignment, since `q` and `p` agree at
`c` below `X`; the aligned encoding (`CellScheme.Rows.IsLawfulBelow.exists_alignedEncoding`) gives
a labelling `f` of codes below `X`, agreeing with `S` capped at the source cap `h`, and a decoder
`ρ`.  Its codes are the values of `S` capped at `h` and tail codes, which are translations of
strongly coded codes and need not be strongly coded themselves
(`VaughtConjecture.Extension.AlignedEncoding`).  The lift at the ambient `S` extends `f` to a
labelling `r` lawful below `Y` agreeing with `S` capped at `h`; and `ρ ∘ r` is the owner-capped
lift.  It is lawful by positive-cap transport with the ambient as lawful companion
(`CellScheme.Rows.IsLawfulBelow.map_of_min_eq`): at every cell
below `Y`, the new cells and the cells of the other coatom included, `r` agrees with the short
label `S d` capped at `h`, so `ρ` reads it as `τ (S d) = min (q d) c` capped at `c`; below `X`, `ρ`
reads `f` literally as `min p (p o)`.

**The serving cell** (`CellScheme.Rows.exists_isWitness_rowBelow`,
`CellScheme.Rows.hasOwnerCappedLifts_of_rows`).  When some cell has graded index `Y`, an ambient
`q` reaching `c` at a cell of grade `j + 1` below `Y` reaches it at a cell `u` of graded index `Y`
(availability); `u` is the cell that **serves** the lift.  Its row, read on the cells below `Y`
(`CellScheme.Rows.rowBelow`), is a source of `q` at `c` when it is lawful below `Y` (the
consistency of the rows at `u`), short at `j + 1`, and never the formal top: the capped witness of
the locality of `q` at `u`, capped again at `c`, decodes it.

**The boundary** (`CellScheme.Rows.exists_lift_of_boundary`).  Let `U, V ≤ Y` be pairs whose cells
below both lie below a pair `O`, with capped lifts from `X ≤ U` to `U` and from `O` to `V`.  The
*boundary* below `Y` is the set of cells below `Y` that lie below `U` or `V`; in the one-grade
step, `U` and `V` are the two coatoms at grade `j + 1`, the boundary is the set of cells of the
amalgam below `Y`, and the cells off the boundary are the new cells of full scope.  The rows
**extend from the boundary** at a cap `h` along a labelling `S` below `Y`
(`CellScheme.Rows.ExtendsFromBoundary`) when every labelling lawful below `U` and `V` that agrees
with `S` capped at `h` on the boundary extends, unchanged there, to one lawful below `Y` that
agrees with `S` capped at `h` everywhere.  A labelling lawful below `X` that agrees with `S` capped
at `h` is lifted in `U`, its trace on `O` is lifted in `V` (the extension across the other
coatom), the two are glued, and the result is extended from the boundary.  This gives:

* the lift at the ambient `S` (`CellScheme.Rows.cappedLiftAt_of_boundary`), when the rows extend
  from the boundary along `S` at every positive cap;
* the owner-capped lifts at the cap `⊥` (`CellScheme.Rows.hasOwnerCappedLifts_bot_of_boundary`),
  when the rows extend from the boundary at the cap `⊥`: the prescription capped at the owner
  label is lifted across the boundary and then through the new cells, and no ambient condition
  remains.

**The one-grade lift** (`CellScheme.Rows.hasOwnerCappedLifts_of_boundary`,
`CellScheme.Rows.cappedLift_of_boundary`).  Under the hypotheses that the one-grade step of the
recursion on the grade supplies, the rows have owner-capped lifts at every cap self-visible at
`j + 1`, and lift capped from `(C, j + 1)` to `(B, j + 1)`:

* the lift at the lower grade, from `(C, j)` to `(B, j)` (the scheme reached after the grade `j`);
* the boundary lifts, from `(C, j + 1)` to the coatom `U` containing it and from the common face `O`
  to the other coatom `V` (lifts of the amalgam);
* a cell of graded index `(B, j + 1)`, and, at every cell `u` of graded index `(B, j + 1)`, a row
  lawful below `(B, j + 1)`, short at `j + 1` and never the formal top, along which the rows
  extend from the boundary at every positive cap.  That the new rows of full scope and grade at
  least `2` are short by their support is to be proved with their construction (checkpoints 2.5
  and 2.6); at `j = 0` the new rows of grade `1` need not be short, their locality being the
  mapped locality of `VaughtConjecture.Extension.InheritedLocality`, so at `j = 0` this
  hypothesis is to be checked on the actual rows, or the lift proved directly.  Never the formal
  top is used only at the owner cell, where it bounds the source cap and leaves room for the tail
  codes;
* the extension from the boundary at the cap `⊥`.

Bountifulness enters only through the boundary lifts, which are instances of the bountifulness of
the amalgam; no consistency of the other rows is assumed, and no lift from `(C, j + 1)` to
`(B, j + 1)` at an ambient other than the rows of the serving cells.  The prescription may
contain the formal top and its lower labels may exceed the cap; the lift at every cap keeps the
ambient observation at every cell below `Y`.

## Placement

Checkpoint 2.4 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

Bountifulness is [Kni26, Definition 2.5.14]; lawful sections are [Kni26, Definition 2.5.4], with
availability its second clause.
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {X Y I U V O : Finset α × ℕ}
  {B C : Finset α} {j : ℕ}

/-! ### The row of a cell, read below its graded index -/

/-- The row of a cell `u` of graded index `Y`, read as a labelling of the cells below `Y`.  In the
one-grade step, the row of the cell that serves a lift is the source of the ambient. -/
def rowBelow (R : D.Rows.{u}) (u : ι) (hu : D.gradedIndex u = Y) : D.below Y → Label.{u} :=
  fun d ↦ R.row u ⟨d.1, show d.1 ∈ D.below (D.gradedIndex u) from le_trans d.2 hu.ge⟩

/-- The row of a cell, read below its graded index, is lawful there when the rows are consistent at
the cell. -/
theorem isLawfulBelow_rowBelow {u : ι} (hu : D.gradedIndex u = Y)
    (h : R.IsLawfulBelow (D.gradedIndex u) (R.row u)) : R.IsLawfulBelow Y (R.rowBelow u hu) := by
  subst hu
  exact h

/-- **The serving cell decodes its row to the ambient.**  Let `u` be a cell of graded index `Y`,
`q` lawful below `Y`, and `c` self-visible at the grade of `Y` with `c ≤ q u`.  Some witness `τ`
bounded by the grade of `Y`, with values at most `c`, sends the row of `u` to the ambient capped
at `c`: `τ (row u d) = min (q d) c` at every cell below `Y`.  It makes the row of the serving cell
a source of the ambient (`CellScheme.Rows.hasOwnerCappedLifts_of_rows`). -/
theorem exists_isWitness_rowBelow {u : ι} (hu : D.gradedIndex u = Y) {q : D.below Y → Label.{u}}
    (hq : R.IsLawfulBelow Y q) {c : Label.{u}} (hc : IsSelfVisible Y.2 c)
    (hcu : c ≤ q ⟨u, hu.le⟩) :
    ∃ τ, IsWitness (stepSuppressor.{u} Y.2) τ ∧ (∀ x, τ x ≤ c) ∧
      ∀ d, τ (R.rowBelow u hu d) = min (q d) c := by
  have hgrade : D.grade u = Y.2 := congrArg Prod.snd hu
  have hext (d : D.below (D.gradedIndex u)) : extendBot Y q d = q ⟨d.1, le_trans d.2 hu.le⟩ :=
    extendBot_of_mem q _
  have hloc := (isLawfulBelow_iff_forall.mp (isLawfulBelow_extendBot.mpr hq)).2.1 u hu.le
  have hvis : IsSelfVisible (D.grade u) (extendBot Y q u) := by
    rw [extendBot_of_mem q hu.le]
    exact (isLawfulBelow_iff.mp hq).orderly ⟨u, hu.le⟩
  obtain ⟨τ', hτ', -, hτ'read⟩ := TransformsTo.exists_isWitness_capped
    (grade := fun d : D.below (D.gradedIndex u) ↦ D.grade d) (E := R.row u)
    (p := fun d ↦ extendBot Y q d) (c := ⟨u, D.mem_below_gradedIndex u⟩) (fun d ↦ d.2.2) hvis
    hloc
  refine ⟨fun x ↦ min (τ' x) c, (hgrade ▸ hτ').min_const hc, fun _ ↦ min_le_right _ _,
    fun d ↦ ?_⟩
  have h' := hτ'read ⟨d.1, show d.1 ∈ D.below (D.gradedIndex u) from le_trans d.2 hu.ge⟩
  simp only [extendBot_of_mem q d.2, extendBot_of_mem q hu.le] at h'
  change min (τ' (R.row u _)) c = min (q d) c
  rw [h', min_assoc, min_eq_right hcu]

/-! ### Lifts at a given ambient -/

/-- The rows **lift capped at the ambient `S`** from `X` to `Y ≥ X`, at the positive caps: for
every cap `h` self-visible at the grade of `Y` with `⊥ < h`, every labelling `f` lawful below `X`,
never the formal top, with the observation of `S` at `h` below `X`, extends to a labelling lawful
below `Y`, equal to `f` below `X`, with the observation of `S` at `h` at every cell below `Y`.  It
is the special case of `CellScheme.Rows.CappedLift` at the ambient `S`
(`CellScheme.Rows.CappedLift.cappedLiftAt`); in the one-grade step `S` is the row of a serving
cell. -/
def CappedLiftAt (R : D.Rows.{u}) (hXY : X ≤ Y) (S : D.below Y → Label.{u}) : Prop :=
  ∀ h : Label.{u}, IsSelfVisible Y.2 h → ⊥ < h → ∀ f : D.below X → Label.{u},
    R.IsLawfulBelow X f → (∀ e, f e ≠ ⊤) →
    (∀ e, min (f e) h = min (S (Set.inclusion (D.below_mono hXY) e)) h) →
    ∃ r : D.below Y → Label.{u}, R.IsLawfulBelow Y r ∧
      (∀ e, r (Set.inclusion (D.below_mono hXY) e) = f e) ∧ ∀ d, min (r d) h = min (S d) h

/-- A capped lift from `X` to `Y` lifts capped at every ambient lawful below `Y`. -/
theorem CappedLift.cappedLiftAt {hXY : X ≤ Y} (hl : R.CappedLift hXY) {S : D.below Y → Label.{u}}
    (hS : R.IsLawfulBelow Y S) : R.CappedLiftAt hXY S := fun h hh _ f hf _ hfS ↦ by
  obtain ⟨r, hr, hrS, hrf⟩ :=
    (cappedLift_iff_forall_exists hXY).mp hl h hh f S hf hS fun e ↦ (hfS e).symm
  exact ⟨r, hr, hrf, hrS⟩

/-! ### Owner-capped lifts at a positive cap -/

/-- **Owner-capped lifts at a positive cap, from a source.**  Let `C ⊆ B`, with finitely many cells
below `(C, j + 1)`, and let `c` be self-visible at `j + 1` with `⊥ < c`.  Suppose that every `q`
lawful below `(B, j + 1)` that is at least `c` at some cell of grade `j + 1` below `(B, j + 1)` has
a source `S`: lawful below `(B, j + 1)`, short at `j + 1`, never the formal top, decoded to `q`
capped at `c` by a witness `τ` bounded by grade `j + 1` with values at most `c`, and with capped
lifts at the ambient `S` from `(C, j + 1)` to `(B, j + 1)`.  Then the rows have owner-capped lifts
from `(C, j + 1)` to `(B, j + 1)` at `c`.  It is the positive-cap case of the one-grade step
(`CellScheme.Rows.hasOwnerCappedLifts_of_rows`). -/
theorem hasOwnerCappedLifts_of_source [Finite (D.below (C, j + 1))] (hCB : C ⊆ B)
    {c : Label.{u}} (hcbot : ⊥ < c) (hc : IsSelfVisible (j + 1) c)
    (hsrc : ∀ q : D.below (B, j + 1) → Label.{u}, R.IsLawfulBelow (B, j + 1) q →
      (∃ d : D.below (B, j + 1), D.grade d = j + 1 ∧ c ≤ q d) →
      ∃ (S : D.below (B, j + 1) → Label.{u}) (τ : Label.{u} → Label.{u}),
        R.IsLawfulBelow (B, j + 1) S ∧ (∀ d, IsShort (j + 1) (S d)) ∧ (∀ d, S d ≠ ⊤) ∧
        IsWitness (stepSuppressor (j + 1)) τ ∧ (∀ x, τ x ≤ c) ∧ (∀ d, τ (S d) = min (q d) c) ∧
        R.CappedLiftAt (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩) S) :
    R.HasOwnerCappedLifts hCB j c := by
  intro p q hp hq hag o ho hop hco
  set incl := Set.inclusion (D.below_mono
    (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)) with hincl
  have hqo : c ≤ q (incl o) := by
    have h' := hag o
    rw [min_eq_right hco.le] at h'
    exact min_eq_right_iff.mp h'
  obtain ⟨S, τ, hS, hSshort, hStop, hτ, hτc, hτS, hSlift⟩ :=
    hsrc q hq ⟨incl o, congrArg Prod.snd ho, hqo⟩
  have hs : R.IsLawfulBelow (C, j + 1) (S ∘ incl) := hS.mono (X := (C, j + 1)) ⟨hCB, le_rfl⟩
  obtain ⟨h, ρ, f, hhbot, hhvis, -, hρ, hf, hftop, hfcap, hfread, hρcap⟩ :=
    hs.exists_alignedEncoding hp ho (fun _ ↦ hSshort _) (hStop _) hτ hτc
      (fun e ↦ (hτS _).trans (hag e)) hc hcbot hco
  obtain ⟨r, hr, hrf, hrS⟩ := hSlift h hhvis hhbot f hf hftop hfcap
  have hamb (d : D.below (B, j + 1)) : min (ρ (r d)) c = min (q d) c := by
    rw [hρcap (r d) (S d) (hSshort d) (hrS d), hτS d, min_assoc, min_self]
  refine ⟨ρ ∘ r, hr.map_of_min_eq hq (fun d ↦ d.2.2) hρ hcbot.ne' hamb, fun e ↦ ?_, hamb⟩
  rw [Function.comp_apply, hrf e, hfread e]

/-- **Owner-capped lifts at a positive cap, from the serving cells.**  Let `C ⊆ B`, with finitely
many cells below `(C, j + 1)` and some cell of graded index `(B, j + 1)`, and let `c` be
self-visible at `j + 1` with `⊥ < c`.  Suppose that the row of every cell `u` of graded index
`(B, j + 1)` is lawful below `(B, j + 1)` (the consistency of the rows at `u`), short at `j + 1`,
and never the formal top, and that the rows lift capped at the ambient given by that row from
`(C, j + 1)` to `(B, j + 1)`.  Then the rows have owner-capped lifts from `(C, j + 1)` to
`(B, j + 1)` at `c`.  The cell serving an ambient `q` is a cell of graded index `(B, j + 1)` where
`q` is at least `c`, chosen by availability.  Of the hypothesis that the rows are never the formal
top, only the value at the owner cell is used. -/
theorem hasOwnerCappedLifts_of_rows [Finite (D.below (C, j + 1))] (hCB : C ⊆ B)
    {c : Label.{u}} (hcbot : ⊥ < c) (hc : IsSelfVisible (j + 1) c)
    (hY : ∃ t, D.gradedIndex t = (B, j + 1))
    (hrow : ∀ u (hu : D.gradedIndex u = (B, j + 1)),
      R.IsLawfulBelow (D.gradedIndex u) (R.row u) ∧ (∀ d, IsShort (j + 1) (R.rowBelow u hu d)) ∧
      (∀ d, R.rowBelow u hu d ≠ ⊤) ∧
      R.CappedLiftAt (show ((C, j + 1) : Finset α × ℕ) ≤ (B, j + 1) from ⟨hCB, le_rfl⟩)
        (R.rowBelow u hu)) :
    R.HasOwnerCappedLifts hCB j c := by
  refine hasOwnerCappedLifts_of_source hCB hcbot hc fun q hq ⟨d, hd, hcd⟩ ↦ ?_
  obtain ⟨t, ht⟩ := hY
  -- The serving cell: a cell of graded index `(B, j + 1)` where `q` is at least `c`.
  obtain ⟨u, hu, hle⟩ := (isLawfulBelow_iff_forall.mp (isLawfulBelow_extendBot.mpr hq)).2.2 d.1 t
    ht.le (d.2.1.trans (congrArg Prod.fst ht).ge) (hd.trans (congrArg Prod.snd ht).symm)
  have hu' : D.gradedIndex u = (B, j + 1) := hu.trans ht
  rw [extendBot_of_mem q d.2, extendBot_of_mem q hu'.le] at hle
  obtain ⟨hcons, hshort, htop, hlift⟩ := hrow u hu'
  obtain ⟨τ, hτ, hτc, hτS⟩ := exists_isWitness_rowBelow hu' hq hc (hcd.trans hle)
  exact ⟨R.rowBelow u hu', τ, isLawfulBelow_rowBelow hu' hcons, hshort, htop, hτ, hτc, hτS, hlift⟩

/-! ### The boundary -/

/-- The rows **extend from the boundary** below `Y` at the cap `h` along `S`, for pairs `U` and
`V`: every labelling of the cells lawful below `U` and below `V` that agrees with `S` capped at `h`
at the cells below `Y` and below `U` or `V` (the boundary) extends, unchanged on the boundary, to a
labelling lawful below `Y` that agrees with `S` capped at `h` at every cell below `Y`.  In the
one-grade step the cells off the boundary are the new cells of full scope, and this is the
extension through them; at the cap `⊥` the condition on `S` is empty. -/
def ExtendsFromBoundary (R : D.Rows.{u}) (U V Y : Finset α × ℕ) (h : Label.{u})
    (S : D.below Y → Label.{u}) : Prop :=
  ∀ w : ι → Label.{u}, R.IsLawfulBelow U (fun d ↦ w d) → R.IsLawfulBelow V (fun d ↦ w d) →
    (∀ d : D.below Y, (d : ι) ∈ D.below U ∨ (d : ι) ∈ D.below V →
      min (w d) h = min (S d) h) →
    ∃ r : D.below Y → Label.{u}, R.IsLawfulBelow Y r ∧
      (∀ d : D.below Y, (d : ι) ∈ D.below U ∨ (d : ι) ∈ D.below V → r d = w d) ∧
      ∀ d, min (r d) h = min (S d) h

/-- **The one-face case.**  When `U = V = Y`, every cell below `Y` lies on the boundary, and the
rows extend from the boundary at every cap along every labelling. -/
theorem extendsFromBoundary_self (Y : Finset α × ℕ) (h : Label.{u}) (S : D.below Y → Label.{u}) :
    R.ExtendsFromBoundary Y Y Y h S := fun w hw _ hwS ↦
  ⟨fun d ↦ w d, hw, fun _ _ ↦ rfl, fun d ↦ hwS d (.inl d.2)⟩

/-- **Lifting across the boundary.**  Let `I ≤ U` and `O ≤ U, V` with `U, V ≤ Y`, the cells below
both `U` and `V` lying below `O`, and capped lifts from `I` to `U` and from `O` to `V`.  Let `h` be
self-visible at the grade of `Y`, `S` lawful below `Y`, and suppose the rows extend from the
boundary at `h` along `S`.  Every `f` lawful below `I` that agrees with `S` capped at `h` extends to
a labelling lawful below `Y`, equal to `f` below `I`, that agrees with `S` capped at `h` at every
cell below `Y`: lift `f` in `U`, lift its trace on `O` in `V` (the extension across the other
coatom), glue, and extend from the boundary.  It gives the lifts at the ambient of a serving cell
(`CellScheme.Rows.cappedLiftAt_of_boundary`) and the owner-capped lifts at the cap `⊥`
(`CellScheme.Rows.hasOwnerCappedLifts_bot_of_boundary`). -/
theorem exists_lift_of_boundary (hIU : I ≤ U) (hOU : O ≤ U) (hOV : O ≤ V) (hUY : U ≤ Y)
    (hVY : V ≤ Y) (hinter : ∀ d ∈ D.below U, d ∈ D.below V → d ∈ D.below O)
    (hleft : R.CappedLift hIU) (hright : R.CappedLift hOV) {h : Label.{u}}
    (hh : IsSelfVisible Y.2 h) {S : D.below Y → Label.{u}} (hS : R.IsLawfulBelow Y S)
    (hext : R.ExtendsFromBoundary U V Y h S) {f : D.below I → Label.{u}}
    (hf : R.IsLawfulBelow I f)
    (hfS : ∀ e, min (f e) h = min (S (Set.inclusion (D.below_mono (hIU.trans hUY)) e)) h) :
    ∃ r : D.below Y → Label.{u}, R.IsLawfulBelow Y r ∧
      (∀ e, r (Set.inclusion (D.below_mono (hIU.trans hUY)) e) = f e) ∧
      ∀ d, min (r d) h = min (S d) h := by
  classical
  -- Lift `f` within `U`.
  obtain ⟨u, hu, hucap, hup⟩ := (cappedLift_iff_forall_exists hIU).mp hleft h (hh.mono hUY.2) f
    (S ∘ Set.inclusion (D.below_mono hUY)) hf (hS.mono hUY) fun e ↦ (hfS e).symm
  -- Lift the trace of that lift on `O` within `V`.
  obtain ⟨v, hv, hvcap, hvo⟩ := (cappedLift_iff_forall_exists hOV).mp hright h (hh.mono hVY.2)
    (u ∘ Set.inclusion (D.below_mono hOU)) (S ∘ Set.inclusion (D.below_mono hVY))
    (hu.mono hOU) (hS.mono hVY) fun d ↦ (hucap (Set.inclusion (D.below_mono hOU) d)).symm
  -- Glue: below `U` read `u`, elsewhere read `v`.
  let w : ι → Label.{u} := fun d ↦ if hd : d ∈ D.below U then u ⟨d, hd⟩ else extendBot V v d
  have hwU (d : ι) (hd : d ∈ D.below U) : w d = u ⟨d, hd⟩ := dite_eq_left hd
  have hwV (d : ι) (hd : d ∈ D.below V) : w d = v ⟨d, hd⟩ := by
    by_cases hdU : d ∈ D.below U
    · rw [hwU d hdU]
      exact (hvo ⟨d, hinter d hdU hd⟩).symm
    · simp only [w, dite_eq_right hdU, extendBot_of_mem v hd]
  have hlU : R.IsLawfulBelow U (fun d ↦ w d) := by
    convert hu using 1
    exact funext fun d ↦ hwU d d.2
  have hlV : R.IsLawfulBelow V (fun d ↦ w d) := by
    convert hv using 1
    exact funext fun d ↦ hwV d d.2
  obtain ⟨r, hr, hrw, hrS⟩ := hext w hlU hlV fun d hd ↦ by
    rcases hd with hd | hd
    · exact (congrArg (min · h) (hwU d hd)).trans (hucap ⟨d, hd⟩)
    · exact (congrArg (min · h) (hwV d hd)).trans (hvcap ⟨d, hd⟩)
  refine ⟨r, hr, fun e ↦ ?_, hrS⟩
  have heU : (e : ι) ∈ D.below U := D.below_mono hIU e.2
  rw [hrw _ (.inl heU), hwU _ heU]
  exact hup e

/-- **Lifts at the ambient of a serving cell, across the boundary.**  Under the hypotheses of
`CellScheme.Rows.exists_lift_of_boundary`, if the rows extend from the boundary along `S` at
every positive cap self-visible at the grade of `Y`, they lift capped at the ambient `S` from `I`
to `Y`.  In the one-grade step, `S` is the row of a serving cell and the lifts from `I` to `U` and
from `O` to `V` are lifts of the amalgam: the extension across the other coatom. -/
theorem cappedLiftAt_of_boundary (hIU : I ≤ U) (hOU : O ≤ U) (hOV : O ≤ V) (hUY : U ≤ Y)
    (hVY : V ≤ Y) (hinter : ∀ d ∈ D.below U, d ∈ D.below V → d ∈ D.below O)
    (hleft : R.CappedLift hIU) (hright : R.CappedLift hOV) {S : D.below Y → Label.{u}}
    (hS : R.IsLawfulBelow Y S)
    (hext : ∀ h, IsSelfVisible Y.2 h → ⊥ < h → R.ExtendsFromBoundary U V Y h S) :
    R.CappedLiftAt (hIU.trans hUY) S := fun h hh hhb _ hf _ hfS ↦
  exists_lift_of_boundary hIU hOU hOV hUY hVY hinter hleft hright hh hS (hext h hh hhb) hf hfS

/-! ### Owner-capped lifts at the cap `⊥` -/

/-- **Owner-capped lifts at the cap `⊥`.**  Let `C ⊆ B`, and let `(C, j + 1) ≤ U`, `O ≤ U, V`,
`U, V ≤ (B, j + 1)`, with the cells below both `U` and `V` lying below `O`, and capped lifts from
`(C, j + 1)` to `U` and from `O` to `V`.  If the rows extend from the boundary at the cap `⊥`, they
have owner-capped lifts from `(C, j + 1)` to `(B, j + 1)` at the cap `⊥`: the prescription capped
at the owner label (which may contain the formal top) is lifted across the boundary and then
through the cells off it.  It is the cap `⊥` of the one-grade step
(`CellScheme.Rows.hasOwnerCappedLifts_of_boundary`). -/
theorem hasOwnerCappedLifts_bot_of_boundary (hCB : C ⊆ B)
    (hCU : ((C, j + 1) : Finset α × ℕ) ≤ U) (hOU : O ≤ U) (hOV : O ≤ V)
    (hUY : U ≤ (B, j + 1)) (hVY : V ≤ (B, j + 1))
    (hinter : ∀ d ∈ D.below U, d ∈ D.below V → d ∈ D.below O)
    (hleft : R.CappedLift hCU) (hright : R.CappedLift hOV)
    (hext : R.ExtendsFromBoundary U V (B, j + 1) ⊥ fun _ ↦ ⊥) :
    R.HasOwnerCappedLifts hCB j ⊥ := by
  intro p q hp _ _ o ho _ _
  obtain ⟨r, hr, hrp, -⟩ := exists_lift_of_boundary hCU hOU hOV hUY hVY hinter hleft hright
    (isSelfVisible_bot _) (isLawfulBelow_const_bot _) hext
    (hp.min_const_of_isSelfVisible (hp.isSelfVisible_of_gradedIndex_eq ho)) fun _ ↦ by simp
  exact ⟨r, hr, hrp, fun _ ↦ by simp⟩

/-! ### The one-grade lift -/

/-- **Owner-capped lifts at every cap, from the boundary and the serving cells.**  Let `C ⊆ B`,
with finitely many cells below `(C, j + 1)`, and let `(C, j + 1) ≤ U`, `O ≤ U, V`,
`U, V ≤ (B, j + 1)`, with the cells below both `U` and `V` lying below `O`.  Suppose:

* the boundary lifts: the rows lift capped from `(C, j + 1)` to `U` and from `O` to `V`;
* the rows extend from the boundary at the cap `⊥`;
* some cell has graded index `(B, j + 1)`, and at every cell `u` of graded index `(B, j + 1)` the
  row is lawful below `(B, j + 1)`, short at `j + 1`, never the formal top, and the rows extend
  from the boundary along it at every positive cap self-visible at `j + 1`.

Then the rows have owner-capped lifts from `(C, j + 1)` to `(B, j + 1)` at every cap `c`
self-visible at `j + 1`: at `⊥` by `CellScheme.Rows.hasOwnerCappedLifts_bot_of_boundary`, and at
a positive cap by the alignment, the aligned encoding, and the decoding of
`CellScheme.Rows.hasOwnerCappedLifts_of_rows`. -/
theorem hasOwnerCappedLifts_of_boundary [Finite (D.below (C, j + 1))] (hCB : C ⊆ B)
    (hCU : ((C, j + 1) : Finset α × ℕ) ≤ U) (hOU : O ≤ U) (hOV : O ≤ V)
    (hUY : U ≤ (B, j + 1)) (hVY : V ≤ (B, j + 1))
    (hinter : ∀ d ∈ D.below U, d ∈ D.below V → d ∈ D.below O)
    (hleft : R.CappedLift hCU) (hright : R.CappedLift hOV)
    (hbot : R.ExtendsFromBoundary U V (B, j + 1) ⊥ fun _ ↦ ⊥)
    (hY : ∃ t, D.gradedIndex t = (B, j + 1))
    (hrow : ∀ u (hu : D.gradedIndex u = (B, j + 1)),
      R.IsLawfulBelow (D.gradedIndex u) (R.row u) ∧ (∀ d, IsShort (j + 1) (R.rowBelow u hu d)) ∧
      (∀ d, R.rowBelow u hu d ≠ ⊤) ∧
      ∀ h, IsSelfVisible (j + 1) h → ⊥ < h → R.ExtendsFromBoundary U V (B, j + 1) h
        (R.rowBelow u hu))
    (c : Label.{u}) (hc : IsSelfVisible (j + 1) c) : R.HasOwnerCappedLifts hCB j c := by
  rcases eq_bot_or_bot_lt c with rfl | hcbot
  · exact hasOwnerCappedLifts_bot_of_boundary hCB hCU hOU hOV hUY hVY hinter hleft hright hbot
  refine hasOwnerCappedLifts_of_rows hCB hcbot hc hY fun u hu ↦ ?_
  obtain ⟨hcons, hshort, htop, hext⟩ := hrow u hu
  exact ⟨hcons, hshort, htop, cappedLiftAt_of_boundary hCU hOU hOV hUY hVY hinter hleft hright
    (isLawfulBelow_rowBelow hu hcons) hext⟩

/-- **The one-grade lift from the boundary and the serving cells.**  Under the hypotheses of
`CellScheme.Rows.hasOwnerCappedLifts_of_boundary`, together with some cell of graded index
`(C, j + 1)` and the lift at the lower grade (the capped lift from `(C, j)` to `(B, j)`), the rows
lift capped from `(C, j + 1)` to `(B, j + 1)` (`CellScheme.Rows.cappedLift_of_ownerCappedLift`).
In the recursion on the grade, `U` and `V` are the coatoms at grade `j + 1`, `O` their common face,
the boundary lifts are lifts of the amalgam, and the remaining hypotheses are properties of the new
rows of full scope. -/
theorem cappedLift_of_boundary [Finite (D.below (C, j + 1))] (hCB : C ⊆ B)
    (hX : ∃ c, D.gradedIndex c = (C, j + 1))
    (hlift : R.CappedLift (X := (C, j)) (Y := (B, j)) ⟨hCB, le_rfl⟩)
    (hCU : ((C, j + 1) : Finset α × ℕ) ≤ U) (hOU : O ≤ U) (hOV : O ≤ V)
    (hUY : U ≤ (B, j + 1)) (hVY : V ≤ (B, j + 1))
    (hinter : ∀ d ∈ D.below U, d ∈ D.below V → d ∈ D.below O)
    (hleft : R.CappedLift hCU) (hright : R.CappedLift hOV)
    (hbot : R.ExtendsFromBoundary U V (B, j + 1) ⊥ fun _ ↦ ⊥)
    (hY : ∃ t, D.gradedIndex t = (B, j + 1))
    (hrow : ∀ u (hu : D.gradedIndex u = (B, j + 1)),
      R.IsLawfulBelow (D.gradedIndex u) (R.row u) ∧ (∀ d, IsShort (j + 1) (R.rowBelow u hu d)) ∧
      (∀ d, R.rowBelow u hu d ≠ ⊤) ∧
      ∀ h, IsSelfVisible (j + 1) h → ⊥ < h → R.ExtendsFromBoundary U V (B, j + 1) h
        (R.rowBelow u hu)) :
    R.CappedLift (X := (C, j + 1)) (Y := (B, j + 1)) ⟨hCB, le_rfl⟩ :=
  cappedLift_of_ownerCappedLift hCB hX hlift fun c hc ↦
    hasOwnerCappedLifts_of_boundary hCB hCU hOU hOV hUY hVY hinter hleft hright hbot hY hrow c hc

end VaughtConjecture.CellScheme.Rows
