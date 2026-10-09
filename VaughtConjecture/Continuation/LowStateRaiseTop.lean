/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.LowStateRaiseAbove

/-!
# Raising one donor top at the cap

Roadmap, Layer 3 ((R2) of the table of 3.4, the LOW construction of 3.3: the step for states above
the controllers); semantic contract, items 3 and 8.

In the failure mode of the step for states at a grade `j` (`ProfileTower.LowStateRaise`) the
raise above the cap (`ProfileTower.lowStateFail_raise`) leaves the donor tops of `W₀` labelled
exactly at the cap `h`: a witness fixes `h`.  Such a top is raised alone.

**Raising one cell** (`CellScheme.Rows.isLawfulBelow_update`, compiled in this repository).  Let
`w` be lawful below `X`, `x` a cell below `X`, and `v ≥ w x` self-visible at the grade of `x`.  The
labelling `w` with `x` relabelled `v` is lawful below `X` when:
* **(readers)** every other cell below `X` reading `x` (with `x` below its graded index) is
  labelled at most `w x`: locality at such a cell `s` caps the label of `x` at `w s ≤ w x`, so the
  raise is invisible there;
* **(the cell itself)** the row of `x` transforms to the new labelling capped at `v` (locality at
  `x`);
* **(availability)** every graded index of the grade of `x` with scope containing that of `x`
  carries a cell labelled at least `v` in the new labelling.
Order is the self-visibility of `v`; locality at a cell not reading `x` is unchanged; availability
from another cell only grows.

**One donor top at the cap** (`ProfileTower.lowStateFail_raise_top`, compiled in this repository).
For a donor top `x` of `W₀` off the private coatom, raising it to `c' = R_j(c)` keeps `W₀` below the
private coatom, keeps capped agreement at `h` (both labels are at least `h`), keeps the frontier
(the owner and the lost top are private), and reads `x` at least at the frontier; lawfulness on the
cut is lawfulness below the donor coatom, given the three conditions there.

**The residual of case (β), exactly.**  The reader condition fails when a donor cell reading the top
`x` (a cell of the donor face of grade above that of `x`, or of the same graded index) carries a
label above `h`: such a cell must then read the raised top, and its row codes `x` at the value it
coded `h`: the obstruction (1) of the lower-top lane.  The condition at `x` itself asks the row of
`x` to read the cells below `x` capped at the new value; it holds when every other cell below `x`
is labelled at most `h` and the row of `x` reads `x` strictly above every other cell (a separating
raise of the witness), and is otherwise a statement about the row of the top.  Availability asks a
cell at least `c'` at every graded index of the grade of `x` above `x` in the donor face; when `x`
has the full scope of the donor face this is `x` itself.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.CellScheme.Rows

open Finset Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}}

/-- **Raising one cell keeps lawfulness** when every other reader of the cell is labelled at most
its old label, the row of the cell transforms to the new labelling capped at the new label, and the
new label is available at every graded index of its grade above it. -/
theorem isLawfulBelow_update [DecidableEq ι] {X : Finset α × ℕ} {w : ι → Label.{u}}
    (hw : R.IsLawfulBelow X (fun d : D.below X ↦ w d)) {x : ι} {v : Label.{u}} (hxv : w x ≤ v)
    (hv : IsSelfVisible (D.grade x) v)
    (hread : ∀ s ∈ D.below X, s ≠ x → x ∈ D.below (D.gradedIndex s) → w s ≤ w x)
    (hloc : TransformsTo (fun d : D.below (D.gradedIndex x) ↦ D.grade d) (R.row x)
      (fun d ↦ min (Function.update w x v d) v))
    (havail : ∀ t ∈ D.below X, D.scope x ⊆ D.scope t → D.grade x = D.grade t →
      ∃ u, D.gradedIndex u = D.gradedIndex t ∧ v ≤ Function.update w x v u) :
    R.IsLawfulBelow X (fun d : D.below X ↦ Function.update w x v d) := by
  obtain ⟨ho, hl, ha⟩ := isLawfulBelow_iff_forall.mp hw
  have hge (u : ι) : w u ≤ Function.update w x v u := by
    by_cases hu : u = x
    · subst hu; rw [Function.update_self]; exact hxv
    · rw [Function.update_of_ne hu]
  refine isLawfulBelow_iff_forall.mpr ⟨fun d hd ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · by_cases hdx : d = x
    · subst hdx; rw [Function.update_self]; exact hv
    · rw [Function.update_of_ne hdx]; exact ho d hd
  · by_cases hsx : s = x
    · subst hsx
      rw [Function.update_self]
      exact hloc
    · obtain ⟨g, σ, hσ, heq⟩ := hl s hs
      refine ⟨g, σ, hσ, fun d ↦ ?_⟩
      rw [Function.update_of_ne hsx, ← heq d]
      dsimp only
      by_cases hdx : d.1 = x
      · have hd := d.2
        rw [hdx] at hd ⊢
        have hsle := hread s hs hsx hd
        rw [Function.update_self, min_eq_right (hsle.trans hxv), min_eq_right hsle]
      · rw [Function.update_of_ne hdx]
  · by_cases hsx : s = x
    · subst hsx
      rw [Function.update_self]
      exact havail t ht hst hg
    · obtain ⟨u, hu, hle⟩ := ha s t ht hst hg
      exact ⟨u, hu, by rw [Function.update_of_ne hsx]; exact hle.trans (hge u)⟩

end VaughtConjecture.CellScheme.Rows

namespace VaughtConjecture.ProfileTower

open Finset Label CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} {K j : ℕ}
  {T : Set (Fin I.amalgam.card ⊕ Unit)} {o r : Fin I.amalgam.card}

/-- **One donor top at the cap, raised alone.**  For a cut-lawful `W₀` agreeing with `P` capped at
`h`, a donor top `x` of `W₀` at least `h`, off the private coatom (not below `(coatC, j)`), distinct
from the owner and the lost top, and `v ≥ W₀ x`: if the relabelled profile is lawful below the donor
coatom (by `CellScheme.Rows.isLawfulBelow_update` under its three conditions there), it is lawful on
the cut, equal to `W₀` below the private coatom, agrees with `P` capped at `h`, has the frontier of
`W₀`, and reads `x` at `v`. -/
theorem lowStateFail_raise_top {P : CProf I} {h : Label.{u}} {W₀ : Prof I}
    (hW₀ : IsCutLawful I j W₀) (hW₀P : ∀ d, min (W₀ d) h = min (P (Sum.inl d)) h)
    {x : Fin I.amalgam.card} (hxh : h ≤ W₀ x)
    (hxC : x ∉ I.amalgam.toCellScheme.below (coatC, j)) (hxo : x ≠ o) (hxr : x ≠ r)
    {v : Label.{u}} (hxv : W₀ x ≤ v)
    (hD : I.amalgam.rows.IsLawfulBelow (coatD, j)
      (fun d : I.amalgam.toCellScheme.below (coatD, j) ↦ Function.update W₀ x v d)) :
    IsCutLawful I j (Function.update W₀ x v) ∧
      (∀ d ∈ I.amalgam.toCellScheme.below (coatC, j), Function.update W₀ x v d = W₀ d) ∧
      (∀ d, min (Function.update W₀ x v d) h = min (P (Sum.inl d)) h) ∧
      Label.frontier K (Sum.inl o) (Sum.inl r) (withCut (Function.update W₀ x v) ⊥) =
        Label.frontier K (Sum.inl o) (Sum.inl r) (withCut W₀ ⊥) ∧
      withCut (Function.update W₀ x v) ⊥ (Sum.inl x) = v := by
  have hC (d : Fin I.amalgam.card) (hd : d ∈ I.amalgam.toCellScheme.below (coatC, j)) :
      Function.update W₀ x v d = W₀ d :=
    Function.update_of_ne (fun h' : d = x ↦ hxC (h' ▸ hd)) _ _
  refine ⟨⟨(Rows.isLawfulBelow_congr fun d hd ↦ (hC d hd).symm).mp hW₀.1, hD⟩, hC,
    fun d ↦ ?_, ?_, Function.update_self _ _ _⟩
  · by_cases hdx : d = x
    · subst hdx
      rw [Function.update_self, min_eq_right (hxh.trans hxv), ← hW₀P, min_eq_right hxh]
    · rw [Function.update_of_ne hdx]; exact hW₀P d
  · unfold Label.frontier
    change min (Function.update W₀ x v o) (visibilityReplace K K (Function.update W₀ x v r)) =
      min (W₀ o) (visibilityReplace K K (W₀ r))
    rw [Function.update_of_ne hxo.symm, Function.update_of_ne hxr.symm]

end VaughtConjecture.ProfileTower
