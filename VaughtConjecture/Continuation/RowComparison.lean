/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Candidate

/-!
# The row comparison at a cell of high grade, from the lawful stable section

Roadmap, Layer 4 (cover-hollowness and the anchor definition of hollowness; output 1, the lawful
stable section); semantic contract, item 8.  A research file: one comparison of rows toward the
converse of `Realization.IsRowAnchor.isTopAnchor` (in
`VaughtConjecture.Continuation.ActualCoverTransport`); the converse itself is not assembled here.

**The comparison for a lawful labelling** (`StageType.rowAt_lt_visibilityReplace_of_isLawful`).
Let `β` be zero or a limit, `q` a stage type at `β`, `ℓ` a lawful section of the rows of `q`, `θ`
a cell, `σ` and `e` cells below `θ`, and `N` at most the grade of `θ`.  If
`ℓ e < β + N ≤ ℓ θ` and `β ≤ ℓ σ`, then `q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ)`.
Only locality of `ℓ` at `θ` is used, with a witness `(g, s)`: the row of `θ`, read at a cell `d`
below `θ`, satisfies `min (ℓ d) (ℓ θ) = min (s (row d)) (g (grade d))`.

* At `θ` itself: `ℓ θ ≤ g (grade θ)`, so the suppressor is at least `β + N` at every grade at most
  the grade of `θ` (it is antitone), in particular at the grade of `e` and at `N`.
* At `e`: `min (ℓ e) (ℓ θ) = ℓ e < β + N` while the suppressor at the grade of `e` is at least
  `β + N`, so the shifter reads the row at `e` below `β + N`.
* At `σ`: `min (ℓ σ) (ℓ θ) ≥ β`, so the shifter reads the row at `σ` at least `β`.
* The shifter at `visibilityReplace N N` of the row at `σ` is at least `β + N`, under two
  conditions on the witness, taken separately.  When the shifter at the row of `σ` is at most the
  suppressor at `N` (the condition of the commutation clause of `Label.IsWitness`), the shifter
  commutes with `visibilityReplace N N`, and a label at least `β` replaced at `(N, N)` is at least
  `β + N` (it is self-visible at `N`, `Label.coe_add_le_of_isSelfVisible`).  Otherwise the shifter
  at the row of `σ` already exceeds the suppressor at `N`, which is at least `β + N`, and
  `visibilityReplace N N` does not lower a label (`Label.le_visibilityReplace`).
* The shifter is monotone, so the row at `e` is strictly below `visibilityReplace N N` of the row
  at `σ`.

The strict inequality holds whenever the hypotheses do; the weak inequality is its consequence
(`StageType.rowAt_le_visibilityReplace_of_isLawful`).  No legality, coding, top cap or marker is
used.

**At a typed tuple, through the stable section**
(`Realization.rowAt_lt_visibilityReplace_of_stableOffset_lt`).  Let `R` at `λ_ξ` be stably
lawful (`Realization.IsStablyLawful`; every model is, `Realization.IsModel.isStablyLawful`, from
exact consistency, covering and legal types; the stable candidate is not assumed to be a model),
`u` a tuple of type `q`, `θ`, `σ`, `e` cells of
`q` labelled `⊤` with `σ` and `e` below `θ`, and `N` at most the grade of `θ`.  If the stable
offset of `e` at `u` is below `N`, then `q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ)`.  The
premises of the comparison are read off the stable section (`Realization.stableSection`): at `e`
it is `λ_ξ + i` with `i` below `N`; at `θ` the stable offset is at least the grade of `θ`
(`Realization.grade_le_stableOffset`), so the section is at least `λ_ξ + N`; at `σ` it is at
least `λ_ξ`.

**Use.**  The converse of `Realization.IsRowAnchor.isTopAnchor` at models, at the same bound,
is assembled from this comparison in `VaughtConjecture.Continuation.ActualCoverConverse`
(`Realization.IsTopAnchor.isRowAnchor`).  No equivalence of the two readings of an anchor, of
cover-hollowness with the absence of a row anchor, or any modelhood statement is stated here.

## Placement

This file belongs to Layer 4 of `roadmap/README.md` (research).

## References

The transformation relation and its witnesses are [Kni26, Definition 2.3.9]; the row reading of
an anchor is a reading of [Kni26, Definition 5.4.2].
-/

universe u v

namespace VaughtConjecture

open Order Label
open scoped Ordinal

namespace StageType

variable {β : Ordinal.{u}} {m : ℕ} {q : StageType.{u} β m} {ℓ : Fin q.card → Label.{u}}
  {θ σ e : Fin q.card} {N : ℕ}

/-- **The row comparison at a cell of high grade, strict form.**  Let `β` be zero or a limit, `ℓ`
a lawful section of the rows of `q`, `σ` and `e` cells below `θ`, and `N` at most the grade of
`θ`.  If `ℓ e < β + N ≤ ℓ θ` and `β ≤ ℓ σ`, then
`q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ)`.  Only locality of `ℓ` at `θ` is used. -/
theorem rowAt_lt_visibilityReplace_of_isLawful (hβ : IsSuccPrelimit β)
    (hℓ : q.rows.IsLawful ℓ)
    (hσθ : σ ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (heθ : e ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (hNθ : N ≤ q.toCellScheme.grade θ) (he : ℓ e < ((β + N : Ordinal.{u}) : Label.{u}))
    (hθ : ((β + N : Ordinal.{u}) : Label.{u}) ≤ ℓ θ) (hσ : (β : Label.{u}) ≤ ℓ σ) :
    q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ) := by
  obtain ⟨g, s, hw, hq⟩ := hℓ.locality θ
  set B : Label.{u} := ((β + N : Ordinal.{u}) : Label.{u})
  have hβB : (β : Label.{u}) ≤ B := coe_le_coe_add β N
  -- locality at `θ` itself: the suppressor at the grade of `θ` is at least `ℓ θ`
  have hgθ : ℓ θ ≤ g (q.toCellScheme.grade θ) := by
    have h : min (ℓ θ) (ℓ θ) = min (s (q.rows.row θ ⟨θ, q.toCellScheme.mem_below_gradedIndex θ⟩))
        (g (q.toCellScheme.grade θ)) := hq ⟨θ, q.toCellScheme.mem_below_gradedIndex θ⟩
    rw [min_self] at h
    exact h.trans_le (min_le_right _ _)
  have hgN : B ≤ g N := hθ.trans (hgθ.trans (hw.antitone hNθ))
  -- at `e`: the shifter reads the row below `β + N`
  have hse : s (q.rows.row θ ⟨e, heθ⟩) < B := by
    have h : min (ℓ e) (ℓ θ) = min (s (q.rows.row θ ⟨e, heθ⟩)) (g (q.toCellScheme.grade e)) :=
      hq ⟨e, heθ⟩
    have hge : B ≤ g (q.toCellScheme.grade e) :=
      hθ.trans (hgθ.trans (hw.antitone heθ.2))
    rw [min_eq_left (he.le.trans hθ)] at h
    rcases min_choice (s (q.rows.row θ ⟨e, heθ⟩)) (g (q.toCellScheme.grade e)) with hm | hm
    · rw [← hm, ← h]
      exact he
    · rw [hm] at h
      exact absurd (h ▸ hge) (not_le.mpr he)
  -- at `σ`: the shifter reads the row at least `β`
  have hsσ : (β : Label.{u}) ≤ s (q.rows.row θ ⟨σ, hσθ⟩) := by
    have h : min (ℓ σ) (ℓ θ) = min (s (q.rows.row θ ⟨σ, hσθ⟩)) (g (q.toCellScheme.grade σ)) :=
      hq ⟨σ, hσθ⟩
    exact (le_min hσ (hβB.trans hθ)).trans (h.trans_le (min_le_left _ _))
  -- the shifter at the replaced row of `σ` is at least `β + N`, under either condition
  set x := q.rows.row θ ⟨σ, hσθ⟩
  have hsx : B ≤ s (visibilityReplace N N x) := by
    by_cases hc : s x ≤ g N
    · rw [hw.visibilityReplace_comm x N hc N le_rfl]
      exact coe_add_le_of_isSelfVisible hβ
        (hsσ.trans (le_visibilityReplace (Nat.le_succ N) (s x)))
        (visibilityReplace_self_visibilityReplace le_rfl (s x))
    · exact hgN.trans ((not_le.mp hc).le.trans
        (hw.monotone (le_visibilityReplace (Nat.le_succ N) x)))
  rw [Scheme.rowAt_of_mem heθ, Scheme.rowAt_of_mem hσθ]
  by_contra hle
  exact (hse.trans_le hsx).not_ge (hw.monotone (not_lt.mp hle))

/-- **The row comparison at a cell of high grade, weak form**: under the hypotheses of
`StageType.rowAt_lt_visibilityReplace_of_isLawful`,
`q.rowAt θ e ≤ visibilityReplace N N (q.rowAt θ σ)`. -/
theorem rowAt_le_visibilityReplace_of_isLawful (hβ : IsSuccPrelimit β)
    (hℓ : q.rows.IsLawful ℓ)
    (hσθ : σ ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (heθ : e ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (hNθ : N ≤ q.toCellScheme.grade θ) (he : ℓ e < ((β + N : Ordinal.{u}) : Label.{u}))
    (hθ : ((β + N : Ordinal.{u}) : Label.{u}) ≤ ℓ θ) (hσ : (β : Label.{u}) ≤ ℓ σ) :
    q.rowAt θ e ≤ visibilityReplace N N (q.rowAt θ σ) :=
  (rowAt_lt_visibilityReplace_of_isLawful hβ hℓ hσθ heθ hNθ he hθ hσ).le

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M} {m : ℕ}
  {u : Fin m ↪ M} {q : StageType.{u} (blockStage ξ) m} {θ σ e : Fin q.card} {N : ℕ}

/-- **The row comparison at a typed tuple, through the stable section.**  Let `R` at `λ_ξ` be
stably lawful, `u` a tuple of type `q`, `θ`, `σ`, `e` cells of `q` labelled `⊤` with `σ` and `e`
below `θ`, and `N` at most the grade of `θ`.  If the stable offset of `e` at `u` is below `N`,
then `q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ)`. -/
theorem rowAt_lt_visibilityReplace_of_stableOffset_lt (hlaw : R.IsStablyLawful)
    (hu : R.eval u = some q) (hθ : q.label θ = ⊤) (hσ : q.label σ = ⊤) (he : q.label e = ⊤)
    (hσθ : σ ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (heθ : e ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (hNθ : N ≤ q.toCellScheme.grade θ)
    (hoff : R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u q e < N) :
    q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ) := by
  refine StageType.rowAt_lt_visibilityReplace_of_isLawful (isSuccPrelimit_blockStage ξ)
    (hlaw u q hu) hσθ heθ hNθ ?_ ?_ ?_
  · rw [stableSection_of_eq_top he, stableLabel, lt_iff_not_ge, coe_add_le_ofOffset_iff]
    exact not_le.mpr hoff
  · rw [stableSection_of_eq_top hθ, stableLabel, coe_add_le_ofOffset_iff]
    exact (Nat.cast_le.mpr hNθ).trans (grade_le_stableOffset hu hθ)
  · rw [stableSection_of_eq_top hσ, stableLabel]
    exact le_ofOffset

/-- **The row comparison at a typed tuple of a model**: the form of
`Realization.rowAt_lt_visibilityReplace_of_stableOffset_lt` for a model at `λ_ξ`, which is stably
lawful (`Realization.IsModel.isStablyLawful`). -/
theorem IsModel.rowAt_lt_visibilityReplace_of_stableOffset_lt (hR : R.IsModel)
    (hu : R.eval u = some q) (hθ : q.label θ = ⊤) (hσ : q.label σ = ⊤) (he : q.label e = ⊤)
    (hσθ : σ ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (heθ : e ∈ q.toCellScheme.below (q.toCellScheme.gradedIndex θ))
    (hNθ : N ≤ q.toCellScheme.grade θ)
    (hoff : R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u q e < N) :
    q.rowAt θ e < visibilityReplace N N (q.rowAt θ σ) :=
  Realization.rowAt_lt_visibilityReplace_of_stableOffset_lt hR.isStablyLawful hu hθ hσ he hσθ heθ
    hNθ hoff

end Realization

end VaughtConjecture
