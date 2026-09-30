/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Scheme.Row

/-!
# Capped observation, cap balls, and bountiful rows

Roadmap, Library conventions (observations `obs_c(q)`, not a lawful cap endomorphism; the
permitted-cap test) and Layer 0 ("capped extension") and Layer 1 (all-permitted-cap
bountifulness); semantic contract, item 3 (a cap is an observation satisfying its permitted-cap
condition; capped vectors need not be lawful); the expositions, §2.

The capped observation of a labelling `q` at a cap `c` is the labelling `d ↦ min (q d) c`; no new
operation is introduced, and the observation need not be lawful.  For semantic rows `R` of a
scheme `D`, a pair `X`, a cap `c`, and a labelling `q` of the cells below `X`, the **cap ball**
`R.capBall X c q` is the set of labellings lawful below `X` with the same capped observation as
`q` at **every** cell below `X`:
`B_c(q) = {q' lawful : min (q' d) c = min (q d) c for every cell d}`.

For `X ≤ Y`, write `r` for the restriction `q ↦ q ∘ Set.inclusion _` of labellings from the cells
below `Y` to those below `X`.  Restriction maps each cap ball into the cap ball of the restriction
(`mapsTo_capBall`).  The rows are **bountiful** (`Rows.IsBountiful`) when, for all graded faces
`X ≤ Y`, every cap `c` that is self-visible at the grade of `Y` (the permitted-cap condition), and
every `q` lawful below `Y`, the restriction is surjective from the cap ball of `q` onto the cap
ball of `r q` (`Set.SurjOn`).  Equivalently:

* `r '' B_c(q) = B_c(r q)` (`isBountiful_iff_image_eq`, by `Set.image_eq_iff_surjOn_mapsTo`);
* every labelling `p` lawful below `X` whose capped observation agrees with that of `r q` extends
  to a labelling lawful below `Y` that restricts to `p` exactly and has the capped observation of
  `q` at every cell below `Y` (`isBountiful_iff_forall_exists`).

Bountifulness is a statement about each permitted cap separately.  Cap balls shrink as the cap
grows (`capBall_anti`); at the cap `⊤` the ball of a lawful labelling is a singleton
(`capBall_top`), and at the cap `⊥` it is the set of all lawful labellings (`capBall_bot`), so
bountiful rows extend every lawful labelling below `X` to one below `Y`
(`IsBountiful.surjOn_isLawfulBelow`).  Bountifulness passes to the restriction to a face
(`IsBountiful.restrict`).
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
theorem capBall_top (hq : R.IsLawfulBelow X q) : R.capBall X ⊤ q = {q} := by
  ext q'
  simp only [mem_capBall, min_top_right, Set.mem_singleton_iff]
  refine ⟨fun h ↦ funext h.2, ?_⟩
  rintro rfl
  exact ⟨hq, fun _ ↦ rfl⟩

/-- At the cap `⊥`, the cap ball is the set of all lawful labellings. -/
theorem capBall_bot : R.capBall X ⊥ q = {q' | R.IsLawfulBelow X q'} := by
  ext q'
  simp

/-- Restriction maps each cap ball into the cap ball of the restriction. -/
theorem mapsTo_capBall (h : X ≤ Y) (c : Label.{u}) (q : D.below Y → Label.{u}) :
    Set.MapsTo (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) (R.capBall Y c q)
      (R.capBall X c (q ∘ Set.inclusion (D.below_mono h))) :=
  fun _ ⟨hl, he⟩ ↦ ⟨hl.mono h, fun _ ↦ he _⟩

/-- The rows are **bountiful**: for all graded faces `X ≤ Y`, every cap `c` self-visible at the
grade of `Y`, and every `q` lawful below `Y`, restriction from the cells below `Y` to those below
`X` maps the cap ball of `q` at `c` onto the cap ball of the restriction of `q`. -/
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

/-- **Restriction to a face.**  The restriction of bountiful rows to a face is bountiful: below a
graded face of the restriction, the cells of the restriction are exactly the cells of the scheme,
so lawfulness, cap balls, and extensions transfer. -/
theorem IsBountiful.restrict [DecidableEq α] (hR : R.IsBountiful) (B : Finset α) :
    (R.restrict B).IsBountiful := by
  intro X Y hX hY h c hc q hq p hp
  have hYB : Y.1 ⊆ B := (Geometry.mem_restrict.mp hY.1).2
  have hXB : X.1 ⊆ B := h.1.trans hYB
  -- The cells below a pair inside `B`, read in the scheme and in its restriction.
  let toE (Z : Finset α × ℕ) (hZ : Z.1 ⊆ B) (d : D.below Z) : (D.restrict B).below Z :=
    ⟨⟨d.1, Finset.coe_subset.mpr (d.2.1.trans hZ)⟩, d.2⟩
  let toD (Z : Finset α × ℕ) (t : (D.restrict B).below Z) : D.below Z := ⟨t.1.1, t.2⟩
  have hE (Z : Finset α × ℕ) (hZ : Z.1 ⊆ B) :
      (D.reindex ((↑) : D.below Z → ι)).IsLowerEmbedding
        ((D.restrict B).reindex ((↑) : (D.restrict B).below Z → _)) (toE Z hZ) :=
    ⟨fun a b hab ↦ Subtype.ext (congrArg (fun t ↦ t.1.1) hab), fun _ ↦ rfl, fun _ _ ↦ Iff.rfl,
      fun _ t _ ↦ ⟨toD Z t, rfl⟩⟩
  have hD (Z : Finset α × ℕ) (hZ : Z.1 ⊆ B) :
      ((D.restrict B).reindex ((↑) : (D.restrict B).below Z → _)).IsLowerEmbedding
        (D.reindex ((↑) : D.below Z → ι)) (toD Z) :=
    ⟨fun a b hab ↦ Subtype.ext (Subtype.ext (congrArg (fun d : D.below Z ↦ d.1) hab)),
      fun _ ↦ rfl,
      fun _ _ ↦ Iff.rfl, fun _ d _ ↦ ⟨toE Z hZ d, rfl⟩⟩
  have hXD : X ∈ D.gradedFaces := ⟨(Geometry.mem_restrict.mp hX.1).1, hX.2⟩
  have hYD : Y ∈ D.gradedFaces := ⟨(Geometry.mem_restrict.mp hY.1).1, hY.2⟩
  obtain ⟨q', ⟨hl, he⟩, hr⟩ := hR hXD hYD h c hc _ (IsLawful.comap hq (hE Y hYB))
    ⟨IsLawful.comap hp.1 (hE X hXB), fun d ↦ hp.2 (toE X hXB d)⟩
  exact ⟨q' ∘ toD Y, ⟨IsLawful.comap hl (hD Y hYB), fun t ↦ he (toD Y t)⟩,
    funext fun t ↦ congrFun hr (toD X t)⟩

end VaughtConjecture.CellScheme.Rows
