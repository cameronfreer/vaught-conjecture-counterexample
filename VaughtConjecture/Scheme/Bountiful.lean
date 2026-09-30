/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Row

/-!
# Capped observation, cap balls, and bountiful rows

Roadmap, Library conventions (observations `obs_c(q)`, not a lawful cap endomorphism) and Layer 1
(bountifulness); semantic contract, item 3 (capped vectors need not be lawful); the expositions,
§2.

The capped observation of a labelling `q` at a cap `c` is the labelling `d ↦ min (q d) c`; no new
operation is introduced, and the observation need not be lawful.  For semantic rows `R` of a
scheme `D`, a pair `X`, a cap `c`, and a labelling `q` of the cells below `X`, the **cap ball**
`R.capBall X c q` is the set of labellings lawful below `X` with the same capped observation as
`q` at **every** cell below `X`:
`B_c(q) = {q' lawful : min (q' d) c = min (q d) c for every cell d}`.

For `X ≤ Y`, write `r` for the restriction `q ↦ q ∘ Set.inclusion _` of labellings from the cells
below `Y` to those below `X`.  Restriction maps each cap ball into the cap ball of the restriction
(`mapsTo_capBall`).  The rows **lift capped** from `X` to `Y` (`Rows.CappedLift R h`, for
`h : X ≤ Y`) when, for every cap `c` self-visible at the grade of `Y`
(`Label.IsSelfVisible Y.2 c`) and every `q` lawful below `Y`, the restriction is surjective from
the cap ball of `q` onto the cap ball of `r q` (`Set.SurjOn`).  Equivalently, every `p` lawful
below `X` with the capped observation of `r q` extends to a labelling lawful below `Y` that
restricts to `p` exactly and has the capped observation of `q` at every cell below `Y`
(`cappedLift_iff_forall_exists`).  Every pair lifts to itself (`cappedLift_refl`), lifts compose
(`CappedLift.trans`), and a pair with no cells below it lifts to every larger pair
(`cappedLift_of_below_eq_empty`).

The rows are **bountiful** (`Rows.IsBountiful`) when they lift capped between any two graded faces
`X ≤ Y`; this is the definition, unfolded by `isBountiful_iff_cappedLift` and applied by
`IsBountiful.cappedLift`.  Equivalently:

* `r '' B_c(q) = B_c(r q)` (`isBountiful_iff_image_eq`, by `Set.image_eq_iff_surjOn_mapsTo`);
* the extension form at every pair of graded faces (`isBountiful_iff_forall_exists`).

These equivalences of the `Set.SurjOn`, image-equation, and explicit-extension forms are the
specialization to cap balls of semantic rows; the general capped-extension statement of the
roadmap's Layer 0 is not formalized here.

**The caps.**  The caps at which bountifulness is required are the labels self-visible at the
target grade.  This is a different set from the stage-permitted cutoffs `Label.IsPermittedCutoff`:
for example, the ordinal `0` is a permitted cutoff at every positive stage but is not self-visible
at any grade `≥ 1`, while `⊥` and `⊤` are self-visible at every grade but are never permitted
cutoffs.  How model-level cutoffs are matched with scheme-level caps is settled with the stage
types (next tranche).

Bountifulness is a statement about each cap separately.  Cap balls shrink as the cap grows
(`capBall_anti`); at the cap `⊤` the ball of a lawful labelling is a singleton (`capBall_top`), and
at the cap `⊥` it is the set of all lawful labellings (`capBall_bot`), so bountiful rows extend
every lawful labelling below `X` to one below `Y` (`IsBountiful.surjOn_isLawfulBelow`).  The mute
rows are bountiful (`isBountiful_mute`): every cap ball is the singleton of the bottom labelling.
Capped lifts and bountifulness transport along lower embeddings, in particular to restrictions,
pullbacks, and reindexings (`VaughtConjecture.Scheme.Transport`).

**The bottom end.**  Capped lifting is stated for arbitrary pairs, not only graded faces.  In a
well-formed scheme no cell lies below a pair of grade `0` or a pair on the empty face
(`IsWellFormed.below_eq_empty`), so any rows lift capped from such a pair to every larger pair
(`IsWellFormed.cappedLift`).  Such pairs, among them the root `(∅, 0)` of a scheme on no points,
are not graded faces, so bountifulness says nothing about them.

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) {X Y : Finset α × ℕ}
  {c c' : Label.{u}} {q q' : D.below X → Label.{u}}

/-- The **cap ball** of `q` at the cap `c`: the labellings lawful below `X` whose capped
observation at `c` agrees with that of `q` at every cell below `X`. -/
def capBall (X : Finset α × ℕ) (c : Label.{u}) (q : D.below X → Label.{u}) :
    Set (D.below X → Label.{u}) :=
  {q' | R.IsLawfulBelow X q' ∧ ∀ d, min (q' d) c = min (q d) c}

/-- Membership in a cap ball: lawfulness below `X` and pointwise agreement after capping. -/
@[simp, grind =] theorem mem_capBall :
    q' ∈ R.capBall X c q ↔ R.IsLawfulBelow X q' ∧ ∀ d, min (q' d) c = min (q d) c :=
  Iff.rfl

/-- Membership in a cap ball, with the capped observations compared as functions. -/
theorem mem_capBall_iff_comp :
    q' ∈ R.capBall X c q ↔ R.IsLawfulBelow X q' ∧ (min · c) ∘ q' = (min · c) ∘ q := by
  simp [funext_iff]

/-- A lawful labelling lies in each of its cap balls. -/
theorem self_mem_capBall (hq : R.IsLawfulBelow X q) (c : Label.{u}) : q ∈ R.capBall X c q :=
  ⟨hq, fun _ ↦ rfl⟩

/-- Cap balls shrink as the cap grows: agreement capped at `c'` implies agreement capped at every
`c ≤ c'`. -/
theorem capBall_anti (h : c ≤ c') : R.capBall X c' q ⊆ R.capBall X c q := fun q' ⟨hl, he⟩ ↦
  ⟨hl, fun d ↦ by rw [← min_eq_right h, ← min_assoc, he d, min_assoc]⟩

/-- At the cap `⊤`, the cap ball of a lawful labelling is the singleton of that labelling. -/
@[simp] theorem capBall_top (hq : R.IsLawfulBelow X q) : R.capBall X ⊤ q = {q} := by
  ext q'
  simp only [mem_capBall, min_top_right, Set.mem_singleton_iff]
  refine ⟨fun h ↦ funext h.2, ?_⟩
  rintro rfl
  exact ⟨hq, fun _ ↦ rfl⟩

/-- At the cap `⊥`, the cap ball is the set of all lawful labellings. -/
@[simp] theorem capBall_bot : R.capBall X ⊥ q = {q' | R.IsLawfulBelow X q'} := by
  ext q'
  simp

/-- Restriction maps each cap ball into the cap ball of the restriction. -/
theorem mapsTo_capBall (h : X ≤ Y) (c : Label.{u}) (q : D.below Y → Label.{u}) :
    Set.MapsTo (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) (R.capBall Y c q)
      (R.capBall X c (q ∘ Set.inclusion (D.below_mono h))) :=
  fun _ ⟨hl, he⟩ ↦ ⟨hl.mono h, fun _ ↦ he _⟩

/-! ### Capped lifting between two pairs -/

/-- The rows **lift capped** from `X` to `Y ≥ X`: for every cap `c` self-visible at the grade of
`Y` and every `q` lawful below `Y`, restriction from the cells below `Y` to those below `X` maps
the cap ball of `q` at `c` onto the cap ball of the restriction of `q`. -/
def CappedLift (h : X ≤ Y) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible Y.2 c → ∀ q : D.below Y → Label.{u}, R.IsLawfulBelow Y q →
    Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) (R.capBall Y c q)
      (R.capBall X c (q ∘ Set.inclusion (D.below_mono h)))

/-- The rows are **bountiful** [Kni26, §2.5]: they lift capped between any two graded faces
`X ≤ Y`, that is, for every cap `c` self-visible at the grade of `Y` and every `q` lawful below
`Y`, restriction from the cells below `Y` to those below `X` maps the cap ball of `q` at `c` onto
the cap ball of the restriction of `q`.

The caps at which bountifulness is required are the labels self-visible at the target grade.  This
is a different set from the stage-permitted cutoffs `Label.IsPermittedCutoff` (e.g. the ordinal
`0` is a permitted cutoff at every positive stage but is not self-visible at any grade `≥ 1`); how
model-level cutoffs are matched with scheme-level caps is settled with the stage types. -/
def IsBountiful : Prop :=
  ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces → ∀ h : X ≤ Y, R.CappedLift h

section CappedLift

variable {R} {Z : Finset α × ℕ}

/-- Bountifulness is capped lifting at every pair of graded faces. -/
theorem isBountiful_iff_cappedLift :
    R.IsBountiful ↔ ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ h : X ≤ Y, R.CappedLift h :=
  Iff.rfl

/-- Bountiful rows lift capped between any two graded faces. -/
theorem IsBountiful.cappedLift (hR : R.IsBountiful) (hX : X ∈ D.gradedFaces)
    (hY : Y ∈ D.gradedFaces) (h : X ≤ Y) : R.CappedLift h :=
  hR hX hY h

/-- Capped lifting as extension: a labelling `p` lawful below `X` whose capped observation agrees
with that of `q` below `X` extends to a labelling lawful below `Y`, equal to `p` below `X`, with
the capped observation of `q` at every cell below `Y`. -/
theorem cappedLift_iff_forall_exists (h : X ≤ Y) :
    R.CappedLift h ↔ ∀ c : Label.{u}, IsSelfVisible Y.2 c →
      ∀ (p : D.below X → Label.{u}) (q : D.below Y → Label.{u}),
        R.IsLawfulBelow X p → R.IsLawfulBelow Y q →
        (∀ d, min (q (Set.inclusion (D.below_mono h) d)) c = min (p d) c) →
        ∃ q' : D.below Y → Label.{u}, R.IsLawfulBelow Y q' ∧
          (∀ d, min (q' d) c = min (q d) c) ∧
          ∀ d, q' (Set.inclusion (D.below_mono h) d) = p d := by
  refine ⟨fun hR c hc p q hp hq hpq ↦ ?_, fun hR c hc q hq p hp ↦ ?_⟩
  · obtain ⟨q', ⟨hl, he⟩, rfl⟩ := hR c hc q hq ⟨hp, fun d ↦ (hpq d).symm⟩
    exact ⟨q', hl, he, fun _ ↦ rfl⟩
  · obtain ⟨q', hl, he, hr⟩ := hR c hc p q hp.1 hq fun d ↦ (hp.2 d).symm
    exact ⟨q', ⟨hl, he⟩, funext hr⟩

/-- Every pair lifts capped to itself. -/
@[simp]
theorem cappedLift_refl (X : Finset α × ℕ) : R.CappedLift (le_refl X) :=
  fun _ _ _ _ p hp ↦ ⟨p, hp, rfl⟩

/-- A pair with no cells below it lifts capped to every larger pair. -/
theorem cappedLift_of_below_eq_empty (hX : D.below X = ∅) (h : X ≤ Y) : R.CappedLift h := by
  intro c _ q hq p _
  have : IsEmpty (D.below X) := Set.isEmpty_coe_sort.mpr hX
  exact ⟨q, R.self_mem_capBall hq c, funext isEmptyElim⟩

/-- **Composition of lifts**: capped lifts from `X` to `Y` and from `Y` to `Z` compose to a capped
lift from `X` to `Z`. -/
theorem CappedLift.trans {hXY : X ≤ Y} {hYZ : Y ≤ Z} (hl : R.CappedLift hXY)
    (hr : R.CappedLift hYZ) : R.CappedLift (hXY.trans hYZ) := by
  intro c hc q hq p hp
  obtain ⟨u, hu, rfl⟩ := hl c (hc.mono hYZ.2) _ (hq.mono hYZ) hp
  obtain ⟨r, hr', rfl⟩ := hr c hc q hq hu
  exact ⟨r, hr', rfl⟩

end CappedLift

/-- Bountifulness as equality of cap balls: `r '' B_c(q) = B_c(r q)`. -/
theorem isBountiful_iff_image_eq :
    R.IsBountiful ↔ ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ (h : X ≤ Y) (c : Label.{u}), IsSelfVisible Y.2 c →
        ∀ q : D.below Y → Label.{u}, R.IsLawfulBelow Y q →
          (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) '' R.capBall Y c q =
            R.capBall X c (q ∘ Set.inclusion (D.below_mono h)) := by
  refine ⟨fun hR X Y hX hY h c hc q hq ↦ Set.image_eq_iff_surjOn_mapsTo.mpr
    ⟨hR hX hY h c hc q hq, R.mapsTo_capBall h c q⟩, fun hR X Y hX hY h c hc q hq ↦ ?_⟩
  exact (Set.image_eq_iff_surjOn_mapsTo.mp (hR hX hY h c hc q hq)).1

/-- Bountifulness as extension: a labelling `p` lawful below `X` whose capped observation agrees
with that of `q` below `X` extends to a labelling lawful below `Y`, equal to `p` below `X`, with
the capped observation of `q` at every cell below `Y`. -/
theorem isBountiful_iff_forall_exists :
    R.IsBountiful ↔ ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ (h : X ≤ Y) (c : Label.{u}), IsSelfVisible Y.2 c →
        ∀ (p : D.below X → Label.{u}) (q : D.below Y → Label.{u}),
          R.IsLawfulBelow X p → R.IsLawfulBelow Y q →
          (∀ d, min (q (Set.inclusion (D.below_mono h) d)) c = min (p d) c) →
          ∃ q' : D.below Y → Label.{u}, R.IsLawfulBelow Y q' ∧
            (∀ d, min (q' d) c = min (q d) c) ∧
            ∀ d, q' (Set.inclusion (D.below_mono h) d) = p d := by
  simp only [isBountiful_iff_cappedLift, cappedLift_iff_forall_exists]

/-- **The bottom cap.**  For bountiful rows, every labelling lawful below a graded face `X`
extends to one lawful below every graded face `Y ≥ X`. -/
theorem IsBountiful.surjOn_isLawfulBelow (hR : R.IsBountiful) (hX : X ∈ D.gradedFaces)
    (hY : Y ∈ D.gradedFaces) (h : X ≤ Y) :
    Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) {q | R.IsLawfulBelow Y q}
      {p | R.IsLawfulBelow X p} := by
  have := hR hX hY h ⊥ (isSelfVisible_bot _) (fun _ ↦ ⊥) (isLawfulBelow_bot Y)
  rwa [capBall_bot, capBall_bot] at this

/-- Mute rows are bountiful. -/
theorem isBountiful_mute : (mute D : D.Rows.{u}).IsBountiful := by
  intro X Y _ _ h c _ q hq p ⟨hp, _⟩
  rw [isLawfulBelow_mute_iff] at hq hp
  subst hq hp
  exact ⟨fun _ ↦ ⊥, self_mem_capBall _ (isLawfulBelow_bot Y) c, rfl⟩

end Rows

/-! ### Pairs with no cells below them -/

/-- **The bottom end.**  In a well-formed scheme, any rows lift capped from a pair of grade `0`,
or a pair on the empty face, to every larger pair.  Such pairs are not graded faces, so this is
not an instance of bountifulness. -/
theorem IsWellFormed.cappedLift {ι α : Type*} {D : CellScheme ι α} [DecidableEq α]
    (hD : D.IsWellFormed) {X Y : Finset α × ℕ} (R : D.Rows.{u}) (hX : X.2 = 0 ∨ X.1 = ∅)
    (h : X ≤ Y) : R.CappedLift h :=
  Rows.cappedLift_of_below_eq_empty (hD.below_eq_empty hX) h

end VaughtConjecture.CellScheme
