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
(`mapsTo_capBall`).  The rows are **bountiful** (`Rows.IsBountiful`) when, for all graded faces
`X ≤ Y`, every cap `c` that is self-visible at the grade of `Y` (`Label.IsSelfVisible Y.2 c`), and
every `q` lawful below `Y`, the restriction is surjective from the cap ball of `q` onto the cap
ball of `r q` (`Set.SurjOn`).  Equivalently:

* `r '' B_c(q) = B_c(r q)` (`isBountiful_iff_image_eq`, by `Set.image_eq_iff_surjOn_mapsTo`);
* every labelling `p` lawful below `X` whose capped observation agrees with that of `r q` extends
  to a labelling lawful below `Y` that restricts to `p` exactly and has the capped observation of
  `q` at every cell below `Y` (`isBountiful_iff_forall_exists`).

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
every lawful labelling below `X` to one below `Y` (`IsBountiful.surjOn_isLawfulBelow`).
Bountifulness passes to the restriction to a face (`IsBountiful.restrict`), and the mute rows are
bountiful (`isBountiful_mute`): every cap ball is the singleton of the bottom labelling.

## References

Bountifulness is Definition 2.5.14 of R. W. Knight, *A counterexample to Vaught's Conjecture
using generalised Stone spaces* (draft, 20 February 2026) [Kni26].
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

/-- The rows are **bountiful** [Kni26, §2.5]: for all graded faces `X ≤ Y`, every cap `c`
self-visible at the grade of `Y`, and every `q` lawful below `Y`, restriction from the cells below
`Y` to those below `X` maps the cap ball of `q` at `c` onto the cap ball of the restriction of `q`.

The caps at which bountifulness is required are the labels self-visible at the target grade.  This
is a different set from the stage-permitted cutoffs `Label.IsPermittedCutoff` (e.g. the ordinal
`0` is a permitted cutoff at every positive stage but is not self-visible at any grade `≥ 1`); how
model-level cutoffs are matched with scheme-level caps is settled with the stage types. -/
def IsBountiful : Prop :=
  ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces → ∀ (h : X ≤ Y) (c : Label.{u}),
    IsSelfVisible Y.2 c → ∀ q : D.below Y → Label.{u}, R.IsLawfulBelow Y q →
      Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) (R.capBall Y c q)
        (R.capBall X c (q ∘ Set.inclusion (D.below_mono h)))

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
  refine ⟨fun hR X Y hX hY h c hc p q hp hq hpq ↦ ?_, fun hR X Y hX hY h c hc q hq p hp ↦ ?_⟩
  · obtain ⟨q', ⟨hl, he⟩, rfl⟩ := hR hX hY h c hc q hq ⟨hp, fun d ↦ (hpq d).symm⟩
    exact ⟨q', hl, he, fun _ ↦ rfl⟩
  · obtain ⟨q', hl, he, hr⟩ := hR hX hY h c hc p q hp.1 hq fun d ↦ (hp.2 d).symm
    exact ⟨q', ⟨hl, he⟩, funext hr⟩

/-- **The bottom cap.**  For bountiful rows, every labelling lawful below a graded face `X`
extends to one lawful below every graded face `Y ≥ X`. -/
theorem IsBountiful.surjOn_isLawfulBelow (hR : R.IsBountiful) (hX : X ∈ D.gradedFaces)
    (hY : Y ∈ D.gradedFaces) (h : X ≤ Y) :
    Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) {q | R.IsLawfulBelow Y q}
      {p | R.IsLawfulBelow X p} := by
  have := hR hX hY h ⊥ (isSelfVisible_bot _) (fun _ ↦ ⊥) (isLawfulBelow_bot Y)
  rwa [capBall_bot, capBall_bot] at this

/-- **Restriction to a face.**  The restriction of bountiful rows to a face is bountiful. -/
theorem IsBountiful.restrict [DecidableEq α] (hR : R.IsBountiful) (B : Finset α) :
    (R.restrict B).IsBountiful := by
  intro X Y hX hY h c hc q hq p hp
  have hYB : Y.1 ⊆ B := (Geometry.mem_restrict.mp hY.1).2
  have hXB : X.1 ⊆ B := h.1.trans hYB
  have hXD : X ∈ D.gradedFaces := ⟨(Geometry.mem_restrict.mp hX.1).1, hX.2⟩
  have hYD : Y ∈ D.gradedFaces := ⟨(Geometry.mem_restrict.mp hY.1).1, hY.2⟩
  obtain ⟨q', ⟨hl, he⟩, hr⟩ := hR hXD hYD h c hc _
    ((isLawfulBelow_iff.mp hq).comap (IsLowerEmbedding.belowRestrictEquiv D hYB))
    ⟨(isLawfulBelow_iff.mp hp.1).comap (IsLowerEmbedding.belowRestrictEquiv D hXB),
      fun d ↦ hp.2 (D.belowRestrictEquiv hXB d)⟩
  exact ⟨q' ∘ (D.belowRestrictEquiv hYB).symm,
    ⟨(isLawfulBelow_iff.mp hl).comap (IsLowerEmbedding.belowRestrictEquiv_symm D hYB),
      fun t ↦ he ((D.belowRestrictEquiv hYB).symm t)⟩,
    funext fun t ↦ congrFun hr ((D.belowRestrictEquiv hXB).symm t)⟩

/-- Mute rows are bountiful. -/
theorem isBountiful_mute : (mute D : D.Rows.{u}).IsBountiful := by
  intro X Y _ _ h c _ q hq p ⟨hp, _⟩
  rw [isLawfulBelow_mute_iff] at hq hp
  subst hq hp
  exact ⟨fun _ ↦ ⊥, self_mem_capBall _ (isLawfulBelow_bot Y) c, rfl⟩

end VaughtConjecture.CellScheme.Rows
