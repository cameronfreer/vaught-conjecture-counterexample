/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Transport

/-!
# Capped lifting between two pairs

Roadmap, Layer 1 (bountifulness; restriction, transport, and pullback; the bottom cases);
semantic contract, item 3 (bountifulness is a statement about cap balls of lawful labellings, cap
by cap); the expositions, §2.

Bountifulness (`CellScheme.Rows.IsBountiful`) is a family of lifting properties, one for each
pair of graded faces `X ≤ Y`.  This file isolates the single property at one pair: the rows `R`
**lift capped** from `X` to `Y` (`Rows.CappedLift R h`, for `h : X ≤ Y`) when, for every cap `c`
self-visible at the grade of `Y` and every `q` lawful below `Y`, restriction from the cells below
`Y` to those below `X` maps the cap ball of `q` at `c` onto the cap ball of the restriction of `q`
(`Set.SurjOn`, exactly as in `IsBountiful`).  Equivalently, every `p` lawful below `X` with the
capped observation of `q` extends to a labelling lawful below `Y`, equal to `p` below `X`, with
the capped observation of `q` at every cell below `Y` (`cappedLift_iff_forall_exists`).

The relation is stated for arbitrary pairs, not only graded faces, and so also covers the bottom
end that bountifulness leaves out:

* bountifulness is capped lifting at every pair of graded faces (`isBountiful_iff_cappedLift`,
  `IsBountiful.cappedLift`);
* every pair lifts to itself (`cappedLift_refl`), and lifts compose (`CappedLift.trans`);
* a pair with no cells below it lifts to every larger pair (`cappedLift_of_below_eq_empty`).  In a
  well-formed scheme this holds for every pair of grade `0` and every pair on the empty face
  (`IsWellFormed.below_eq_empty`, `IsWellFormed.cappedLift`); such pairs, among them the root
  `(∅, 0)` of a scheme on no points, are not graded faces, so bountifulness says nothing about
  them;
* lifts transport along equivalences of the lower sets that commute with restriction, preserve
  lawfulness, and do not raise the target grade (`CappedLift.of_equiv`), in particular in both
  directions along a lower embedding mapping the cells below the two pairs onto the cells below
  their images (`CappedLift.comap`, `CappedLift.of_comap`, `cappedLift_comap_iff`).

No bountifulness of the ambient rows is assumed anywhere: a lift at one pair is a property of that
pair alone.  The transfer across a face restriction (`Scheme.cappedLift_comap_iff` in
`VaughtConjecture.Stage.Legal`) assumes no bountifulness at all, and the lift across a defined
face (`StageType.cappedLift_of_restrictFace`, same file) needs only bountifulness on the face.

## Placement

`Rows.CappedLift`, `cappedLift_iff_forall_exists`, `cappedLift_refl`, `CappedLift.trans`, and
`cappedLift_of_below_eq_empty` belong in `VaughtConjecture.Scheme.Bountiful`, with
`Rows.IsBountiful` then *defined* as capped lifting at every pair of graded faces, so that
`isBountiful_iff_cappedLift` becomes the definitional unfolding; after the move the base
`isBountiful_iff_forall_exists` is kept as the corollary
`simp only [isBountiful_iff_cappedLift, cappedLift_iff_forall_exists]`, and `IsBountiful.cappedLift`
is the direct application; `IsWellFormed.below_eq_empty` is a fact about well-formed cell schemes
for `VaughtConjecture.Scheme.Cell`.  `CappedLift.of_equiv`,
`CappedLift.comap`, `CappedLift.of_comap`, and `cappedLift_comap_iff` belong in
`VaughtConjecture.Scheme.Transport` (where `IsBountiful.comap_of_image_eq` follows from
`CappedLift.comap` applied at every pair of graded faces), and
`IsLowerEmbedding.belowEquiv_inclusion` in its `IsLowerEmbedding` namespace, beside
`IsLowerEmbedding.belowEquiv`.  They are stated here so that those files are unchanged.

## References

Bountifulness is [Kni26, Definition 2.5.14], and the restriction of a semantics to a face of the
plan is [Kni26, Lemma 2.5.5], for R. W. Knight, *A counterexample to Vaught's Conjecture using
generalised Stone spaces* (draft, 20 February 2026).
-/

universe u

namespace VaughtConjecture.CellScheme

open Finset Label

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β}

/-- The equivalences of lower sets induced by a lower embedding commute with restriction. -/
theorem IsLowerEmbedding.belowEquiv_inclusion {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ)
    {X' Y' : Finset β × ℕ} {X Y : Finset α × ℕ} (h' : X' ≤ Y') (h : X ≤ Y)
    (hX : φ '' E.below X' = D.below X) (hY : φ '' E.below Y' = D.below Y) (d : E.below X') :
    hφ.belowEquiv hY (Set.inclusion (E.below_mono h') d) =
      Set.inclusion (D.below_mono h) (hφ.belowEquiv hX d) :=
  Subtype.ext rfl

namespace Rows

variable (R : D.Rows.{u}) {X Y Z : Finset α × ℕ}

/-- The rows **lift capped** from `X` to `Y ≥ X`: for every cap `c` self-visible at the grade of
`Y` and every `q` lawful below `Y`, restriction from the cells below `Y` to those below `X` maps
the cap ball of `q` at `c` onto the cap ball of the restriction of `q`. -/
def CappedLift (h : X ≤ Y) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible Y.2 c → ∀ q : D.below Y → Label.{u}, R.IsLawfulBelow Y q →
    Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) (R.capBall Y c q)
      (R.capBall X c (q ∘ Set.inclusion (D.below_mono h)))

variable {R}

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

/-- Bountifulness is capped lifting at every pair of graded faces. -/
theorem isBountiful_iff_cappedLift :
    R.IsBountiful ↔ ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces →
      ∀ h : X ≤ Y, R.CappedLift h :=
  Iff.rfl

/-- Bountiful rows lift capped between any two graded faces. -/
theorem IsBountiful.cappedLift (hR : R.IsBountiful) (hX : X ∈ D.gradedFaces)
    (hY : Y ∈ D.gradedFaces) (h : X ≤ Y) : R.CappedLift h :=
  hR hX hY h

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

/-- **Transport of lifts along equivalences of lower sets.**  Let `R'` be rows of a scheme `E`
and `X' ≤ Y'` pairs of `E`, with equivalences from the cells below `X'` and `Y'` to the cells
below `X` and `Y` that commute with restriction, carry labellings lawful below `X` to labellings
lawful below `X'`, and identify the labellings lawful below `Y` and `Y'`.  If the grade of `Y'` is
at most that of `Y`, a capped lift from `X'` to `Y'` gives one from `X` to `Y`. -/
theorem CappedLift.of_equiv {R' : E.Rows.{u}} {X' Y' : Finset β × ℕ} {h' : X' ≤ Y'} {h : X ≤ Y}
    (eX : E.below X' ≃ D.below X) (eY : E.below Y' ≃ D.below Y)
    (hsq : ∀ d, eY (Set.inclusion (E.below_mono h') d) = Set.inclusion (D.below_mono h) (eX d))
    (hgrade : Y'.2 ≤ Y.2) (hX : ∀ p, R.IsLawfulBelow X p → R'.IsLawfulBelow X' (p ∘ eX))
    (hY : ∀ q, R.IsLawfulBelow Y q ↔ R'.IsLawfulBelow Y' (q ∘ eY)) (hl : R'.CappedLift h') :
    R.CappedLift h := by
  intro c hc q hq p ⟨hp, hpq⟩
  obtain ⟨r, ⟨hr, hrc⟩, hrp⟩ := hl c (hc.mono hgrade) (q ∘ eY) ((hY q).mp hq)
    ⟨hX p hp, fun d ↦ by simpa [hsq] using hpq (eX d)⟩
  refine ⟨r ∘ eY.symm, ⟨(hY _).mpr (by simpa [Function.comp_assoc] using hr),
    fun d ↦ by simpa using hrc (eY.symm d)⟩, funext fun d ↦ ?_⟩
  have he : eY.symm (Set.inclusion (D.below_mono h) d) =
      Set.inclusion (E.below_mono h') (eX.symm d) :=
    eY.symm_apply_eq.mpr (by rw [hsq, eX.apply_symm_apply])
  simpa [he] using congrFun hrp (eX.symm d)

section LowerEmbedding

variable {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ) {X' Y' : Finset β × ℕ} {h' : X' ≤ Y'}
  {h : X ≤ Y} (hX : φ '' E.below X' = D.below X) (hY : φ '' E.below Y' = D.below Y)
include hX hY

/-- **Pullback of lifts along a lower embedding.**  If `φ` maps the cells below `X'` and `Y'`
onto the cells below `X` and `Y`, and the grade of `Y` is at most that of `Y'`, a capped lift of
`R` from `X` to `Y` pulls back to a capped lift of the pulled-back rows from `X'` to `Y'`. -/
theorem CappedLift.comap (hgrade : Y.2 ≤ Y'.2) (hl : R.CappedLift h) :
    (R.comap hφ).CappedLift h' := by
  refine hl.of_equiv (hφ.belowEquiv hX).symm (hφ.belowEquiv hY).symm (fun d ↦ ?_) hgrade
    (fun p hp ↦ (isLawfulBelow_comap_iff hφ hX).mp (by simpa [Function.comp_assoc] using hp))
    fun q ↦ ?_
  · rw [Equiv.symm_apply_eq, hφ.belowEquiv_inclusion h' h hX hY, Equiv.apply_symm_apply]
  · rw [← isLawfulBelow_comap_iff hφ hY]
    simp [Function.comp_assoc]

/-- **Pushforward of lifts along a lower embedding.**  If `φ` maps the cells below `X'` and `Y'`
onto the cells below `X` and `Y`, and the grade of `Y'` is at most that of `Y`, a capped lift of
the pulled-back rows from `X'` to `Y'` gives a capped lift of `R` from `X` to `Y`. -/
theorem CappedLift.of_comap (hgrade : Y'.2 ≤ Y.2) (hl : (R.comap hφ).CappedLift h') :
    R.CappedLift h :=
  hl.of_equiv (hφ.belowEquiv hX) (hφ.belowEquiv hY) (hφ.belowEquiv_inclusion h' h hX hY) hgrade
    (fun _ hp ↦ (isLawfulBelow_comap_iff hφ hX).mpr hp)
    fun _ ↦ (isLawfulBelow_comap_iff hφ hY).symm

/-- Along a lower embedding mapping the cells below `X'` and `Y'` onto the cells below `X` and
`Y`, with `Y` and `Y'` of the same grade, the pulled-back rows lift capped from `X'` to `Y'`
exactly when the rows lift capped from `X` to `Y`. -/
theorem cappedLift_comap_iff (hgrade : Y'.2 = Y.2) :
    (R.comap hφ).CappedLift h' ↔ R.CappedLift h :=
  ⟨CappedLift.of_comap hφ hX hY hgrade.le, CappedLift.comap hφ hX hY hgrade.ge⟩

end LowerEmbedding

end Rows

/-! ### Pairs with no cells below them -/

namespace IsWellFormed

variable [DecidableEq α] (hD : D.IsWellFormed) {X Y : Finset α × ℕ}
include hD

/-- In a well-formed scheme, no cell lies below a pair of grade `0` or a pair on the empty face. -/
theorem below_eq_empty (hX : X.2 = 0 ∨ X.1 = ∅) : D.below X = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun d hd ↦ ?_
  have hpos := hD.grade_pos d
  have hcard := hD.grade_le_card d
  rcases hX with hX | hX
  · have : D.grade d ≤ X.2 := hd.2
    omega
  · have : D.scope d = ∅ := subset_empty.mp (hX ▸ hd.1)
    simp [this] at hcard
    omega

/-- **The bottom end.**  In a well-formed scheme, any rows lift capped from a pair of grade `0`,
or a pair on the empty face, to every larger pair.  Such pairs are not graded faces, so this is
not an instance of bountifulness. -/
theorem cappedLift (R : D.Rows.{u}) (hX : X.2 = 0 ∨ X.1 = ∅) (h : X ≤ Y) : R.CappedLift h :=
  Rows.cappedLift_of_below_eq_empty (hD.below_eq_empty hX) h

end IsWellFormed

end VaughtConjecture.CellScheme
