/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceivingExamples
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Extension.GatedExtensionCounterexample
import VaughtConjecture.Stage.Cap
import VaughtConjecture.Stage.MarkedCap

/-!
# Marked caps at cover-hollow realizations

Roadmap, Layer 4 (cover-hollowness) and Layer 3 ((R3) of the table of 3.4); the marked-cap context
of `VaughtConjecture.Stage.MarkedCap` read with the top grade, at a cover-hollow realization, and
against the refuted determination statements.

**Top caps and the top grade.**  The grade of a top cap is the top grade
(`StageType.IsTopCap.grade_eq_topGrade`), and a top cap is a cell of graded index
`(univ, t'.topGrade)` labelled `⊤` (`StageType.isTopCap_iff`).  So a stage type `t'` is a marked-cap
context along `h : Fin n ↪ Fin k` exactly when `n + 1 < N` for its top grade `N` and some cell `c`
of graded index `(univ, N)` labelled `⊤` has a marker `r` with
`visibilityReplace N (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a` at every cell `a` of the root labelled
`⊤` (`StageType.isMarkedCapContext_iff`).  With reference cells for the proper labels of a donor
`d`, read below the top cap (`StageType.IsAnchored`), it is an **anchored marked-cap context**
(`StageType.IsAnchoredMarkedCapContext`, defined in this repository).

**Forcing is read by the rows at a cover-hollow realization**
(`Realization.IsCoverHollow.exists_forcesThreshold_rowAt`, compiled in this repository (theorem
named)).  Let `R` be cover-hollow at `λ_ξ` with legal types (a model has legal types,
`Realization.IsModel.hasLegalTypes`), `x` an occurrence, `a` a cell of its type labelled `⊤` (its
stable label is `⊤`, `Realization.isCoverHollow_iff_forall_stableLabel_eq_top`), and `L : ℕ`.
Cover-hollowness gives a rooted cover `(q, f)` compatible with `x` that forces `L` at `a`; `q` is
legal, it has a top cap with a marker, `L` is at most its top grade `N`, and for every top cap `c`
and every marker `r` of `c`, at the cell `e` of `q` transported from `a`,
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`.  No hypothesis beyond legality is used: no
exact consistency, covering, receiving, growth, or forcing donors.  The cover depends on `L`; a
single cover of large top grade forcing `n + 1` at every top of a root at once (the synchronization
step of an acquisition) is prospective.

**The determination counterexamples are excluded**, each by an instance of a general exclusion
of `VaughtConjecture.Stage.MarkedCap` or of this file.

* The predicate always true (`ExactReceivingExamples`): the context is the empty root of the apex
  point, along the identity.  It is top-free, so it is not a marked-cap context
  (`MarkedCapExclusions.not_isMarkedCapContext_root_apexPoint`, compiled in this repository
  (theorem named)).
* The anchored predicate (the refuting instance is not in this library): its context is the legal
  two-point type `GatedExtensionCounterexample.P α` capped at an ordinal `c < α` self-visible at
  `2`.  The data are in this library; the capped type is top-free, so it is a marked-cap context
  along no embedding (`MarkedCapExclusions.not_isMarkedCapContext_cap_P`, compiled in this
  repository (theorem named)).
* The anchored predicate with a top (the refuting instance is not in this library): its context,
  on three points over a root on one point, has its cells of grade at least `2` capped at an
  ordinal, so its top grade is at most `1` (argued here); a context of top grade at most `1` is
  not a marked-cap context over a root on one point
  (`MarkedCapExclusions.not_isMarkedCapContext_of_topGrade_le_one`, compiled in this repository
  (theorem named)): the clause `n + 1 < N` fails.

**An instance.**  The legal two-point type `GatedExtensionCounterexample.P α`, uncapped, is a
marked-cap context over the empty root (`MarkedCapExclusions.isMarkedCapContext_P`, compiled in
this repository (theorem named)): its cell of graded index `(univ, 2)` labelled `⊤` is a top cap of
grade `2`, and over the empty root the row inequality is vacuous
(`StageType.isMarkedCapContext_of_isTopCap_of_zero`).

Acquisition and determination for the marked-cap context are open; nothing here proves or reduces
(R3) (`Realization.HollowReceiving`).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label
open scoped Ordinal

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ} {t' : StageType.{u} α k} {c : Fin t'.card}

/-! ### Top caps and the top grade -/

/-- **The grade of a top cap is the top grade.** -/
theorem IsTopCap.grade_eq_topGrade (hc : t'.IsTopCap c) :
    t'.toCellScheme.grade c = t'.topGrade :=
  le_antisymm (grade_le_topGrade hc.2.1) (topGrade_le_iff.mpr hc.2.2)

/-- A top cap is exactly a cell of graded index `(univ, t'.topGrade)` labelled `⊤`. -/
theorem isTopCap_iff :
    t'.IsTopCap c ↔ t'.toCellScheme.gradedIndex c = (univ, t'.topGrade) ∧ t'.label c = ⊤ := by
  refine ⟨fun hc ↦ ⟨Prod.ext hc.1 hc.grade_eq_topGrade, hc.2.1⟩, fun ⟨hi, ht⟩ ↦
    ⟨congrArg Prod.fst hi, ht, fun x hx ↦ ?_⟩⟩
  rw [show t'.toCellScheme.grade c = t'.topGrade from congrArg Prod.snd hi]
  exact grade_le_topGrade hx

/-- **The marked-cap context in terms of the top grade**: a stage type `t'` is a marked-cap context
along `h : Fin n ↪ Fin k` exactly when `n + 1 < N` for its top grade `N`, and it has a cell `c` of
graded index `(univ, N)` labelled `⊤` with a marker `r` such that
`visibilityReplace N (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a` at every cell `a` of the root labelled
`⊤`. -/
theorem isMarkedCapContext_iff {h : Fin n ↪ Fin k} :
    t'.IsMarkedCapContext h ↔ n + 1 < t'.topGrade ∧
      ∃ c r, t'.toCellScheme.gradedIndex c = (univ, t'.topGrade) ∧ t'.label c = ⊤ ∧
        t'.IsMarker c r ∧ ∀ a ∈ t'.visibleCells h, t'.label a = ⊤ →
          visibilityReplace t'.topGrade (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a := by
  refine ⟨fun ⟨c, r, hc, hr, hn, ha⟩ ↦ ?_, fun ⟨hn, c, r, hi, ht, hr, ha⟩ ↦ ?_⟩
  · rw [hc.grade_eq_topGrade] at hn ha
    exact ⟨hn, c, r, (isTopCap_iff.mp hc).1, hc.2.1, hr, ha⟩
  · have hc : t'.IsTopCap c := isTopCap_iff.mpr ⟨hi, ht⟩
    refine ⟨c, r, hc, hr, ?_, ?_⟩
    · rwa [hc.grade_eq_topGrade]
    · rwa [hc.grade_eq_topGrade]

/-- A marked-cap context along an embedding of `n` points has top grade above `n + 1`. -/
theorem IsMarkedCapContext.lt_topGrade {h : Fin n ↪ Fin k} (ht : t'.IsMarkedCapContext h) :
    n + 1 < t'.topGrade :=
  (isMarkedCapContext_iff.mp ht).1

/-- **A stage type of top grade at most `n + 1` is a marked-cap context along no embedding of `n`
points.** -/
theorem not_isMarkedCapContext_of_topGrade_le (ht : t'.topGrade ≤ n + 1) (h : Fin n ↪ Fin k) :
    ¬ t'.IsMarkedCapContext h :=
  fun hm ↦ hm.lt_topGrade.not_ge ht

/-! ### Reference cells -/

/-- A stage type `t'` on `k` points is an **anchored marked-cap context** along `h` for a
one-point type `d` on `n + 1` points when it is a marked-cap context along `h` whose top cap `c`
anchors `d` (`StageType.IsAnchored`): every label of a new cell of `d` other than `⊥` and `⊤` is a
visibility replacement at the threshold `k` of the label of a cell of `t'`, a reference cell. -/
def IsAnchoredMarkedCapContext (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
    (d : StageType.{u} α (n + 1)) : Prop :=
  ∃ c r, t'.IsTopCap c ∧ t'.IsMarker c r ∧ n + 1 < t'.toCellScheme.grade c ∧
    (∀ a ∈ t'.visibleCells h, t'.label a = ⊤ →
      visibilityReplace (t'.toCellScheme.grade c) (n + 1) (t'.rowAt c r) ≤ t'.rowAt c a) ∧
    t'.IsAnchored c d

/-- An anchored marked-cap context is a marked-cap context. -/
theorem IsAnchoredMarkedCapContext.isMarkedCapContext {h : Fin n ↪ Fin k}
    {d : StageType.{u} α (n + 1)} (ht : t'.IsAnchoredMarkedCapContext h d) :
    t'.IsMarkedCapContext h :=
  let ⟨c, r, hc, hr, hn, ha, _⟩ := ht
  ⟨c, r, hc, hr, hn, ha⟩

end StageType

/-! ### Forcing is read by the rows at a cover-hollow realization -/

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Forcing is read by the rows at a cover-hollow realization**: the stable value `⊤` of a cell
labelled `⊤` is read by the rows.  Let `R` be cover-hollow at `λ_ξ` with legal types, `x` an
occurrence, `a` a cell of its type labelled `⊤`, and `L : ℕ`.  Some rooted cover `(q, f)`
compatible with `x` forces the threshold `L` at `a` (cover-hollowness); `q` is legal, `L` is at
most the top grade `N` of `q`, `q` has a top cap with a marker, and for every top cap `c` of `q`
and every marker `r` of `c`, at the cell `e` of `q` transported from `a`,
`visibilityReplace N L (q.rowAt c r) ≤ q.rowAt c e`. -/
theorem IsCoverHollow.exists_forcesThreshold_rowAt (hR : R.IsCoverHollow)
    (hl : R.HasLegalTypes) (x : R.Occurrence) {a : Fin x.type.card} (ha : x.type.label a = ⊤)
    (L : ℕ) :
    ∃ y : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin x.arity ↪ Fin m),
      R.ExtendsToCover x.tuple y ∧
      StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) y.2.1 y.2.2
        x.type a L ∧
      y.2.1.IsLegal ∧ L ≤ y.2.1.topGrade ∧ (∃ c r, y.2.1.IsTopCap c ∧ y.2.1.IsMarker c r) ∧
      ∀ c r, y.2.1.IsTopCap c → y.2.1.IsMarker c r →
        ∀ i : Fin (y.2.1.toScheme.comap y.2.2).card, (i : ℕ) = a →
          visibilityReplace y.2.1.topGrade L (y.2.1.rowAt c r) ≤
            y.2.1.rowAt c (y.2.1.cellMap y.2.2 i) := by
  have hno : ¬ R.IsTopAnchor x a L := fun h ↦ hR ⟨x, a, L, h⟩
  simp only [IsTopAnchor, not_and, not_forall, not_not] at hno
  obtain ⟨y, hy, hforce⟩ := hno ha
  obtain ⟨m, q, f⟩ := y
  have hq : q.IsLegal := by
    obtain ⟨s, -, hs⟩ := hy
    exact hl ⟨s, hs.injective⟩ q hs.eval_eq
  have hβ := isSuccLimit_blockStage ξ
  have hα : blockStage ξ + ω ≤ blockStage (ξ + 1) := (blockStage_add_one ξ).ge
  obtain ⟨hf, hqp⟩ := (StageType.restrictFace_eq_some_iff q f).mp hforce.1
  have hcard : (q.comap f hf).card = x.type.card :=
    congrArg (fun s : StageType.{u} (blockStage ξ) x.arity ↦ s.card) hqp
  set i₀ : Fin (q.comap f hf).card := ⟨a, lt_of_lt_of_eq a.2 hcard.symm⟩
  have hnt : ¬ q.IsTopFree :=
    fun h ↦ h _ (StageType.label_cellMap_eq_top hforce.1 ha i₀ rfl)
  obtain ⟨c, hc⟩ := StageType.exists_isTopCap hq hnt
  obtain ⟨r, hr⟩ := StageType.exists_isMarker hc.2.1
  have hF := StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc hr
    hforce ha (e := q.cellMap f i₀) fun i hi ↦ congrArg (q.cellMap f) (Fin.ext hi)
  refine ⟨⟨m, q, f⟩, hy, hforce, hq, hc.grade_eq_topGrade ▸ hF.1, ⟨c, r, hc, hr⟩,
    fun c' r' hc' hr' i hi ↦ ?_⟩
  rw [← hc'.grade_eq_topGrade]
  exact (StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le hβ hα hq hc' hr'
    hforce ha fun i' hi' ↦ congrArg (q.cellMap f) (Fin.ext (hi'.trans hi.symm))).2

end Realization

/-! ### The three determination counterexamples are excluded -/

namespace MarkedCapExclusions

open StageType

variable {k n : ℕ}

/-- **The empty root of the apex point is not a marked-cap context**: in the refutation of
determination with the predicate always true (`ExactReceivingExamples`), the context is the root
of `ExactReceivingExamples.apexPoint`, a stage type at `ω` on no points
(`ExactReceivingExamples.exists_root_apexPoint`), along the identity.  It is the instance on no
points of `StageType.not_isMarkedCapContext_of_zero`, stated for every stage type at `ω` on no
points. -/
theorem not_isMarkedCapContext_root_apexPoint (t : StageType.{0} ω 0) :
    ¬ t.IsMarkedCapContext (Function.Embedding.refl _) :=
  not_isMarkedCapContext_of_zero t _

/-- **The capped context of the anchored predicate is not a marked-cap context**: the legal
two-point type `GatedExtensionCounterexample.P α` capped at an ordinal `c < α` self-visible at `2`
is top-free (`StageType.isTopFree_cap`), so it is a marked-cap context along no embedding; an
instance of `StageType.not_isMarkedCapContext_of_isTopFree`. -/
theorem not_isMarkedCapContext_cap_P {α c : Ordinal.{u}} (hc : IsSelfVisible 2 (c : Label.{u}))
    (hcα : c < α) (h : Fin n ↪ Fin 2) :
    ¬ ((GatedExtensionCounterexample.P α).cap c hc hcα).IsMarkedCapContext h :=
  not_isMarkedCapContext_of_isTopFree isTopFree_cap h

/-- **A context of top grade at most `1` is not a marked-cap context over a one-point root**: the
clause `n + 1 < N` fails for `n = 1`; an instance of
`StageType.not_isMarkedCapContext_of_topGrade_le`. -/
theorem not_isMarkedCapContext_of_topGrade_le_one {α : Ordinal.{u}} {t' : StageType.{u} α k}
    (ht : t'.topGrade ≤ 1) (h : Fin 1 ↪ Fin k) : ¬ t'.IsMarkedCapContext h :=
  not_isMarkedCapContext_of_topGrade_le (ht.trans (by omega)) h

/-- **The uncapped two-point type is a marked-cap context over the empty root**: its cell `3`,
of graded index `(univ, 2)`, is labelled `⊤` and every grade is at most `2`, so it is a top cap of
grade `2 > 1` (`StageType.isMarkedCapContext_of_isTopCap_of_zero`).  So the predicate has an
instance on a legal stage type. -/
theorem isMarkedCapContext_P (α : Ordinal.{u}) (h : Fin 0 ↪ Fin 2) :
    (GatedExtensionCounterexample.P α).IsMarkedCapContext h := by
  have hc : (GatedExtensionCounterexample.P α).IsTopCap (3 : Fin 5) :=
    ⟨rfl, rfl, fun x _ ↦ (GatedExtensionCounterexample.P α).grade_le x⟩
  -- the grade of cell `3` is `GatedExtensionCounterexample.cellGrade 3 = 2`
  have hg : (GatedExtensionCounterexample.P α).toCellScheme.grade (3 : Fin 5) = 2 := rfl
  exact isMarkedCapContext_of_isTopCap_of_zero hc (by rw [hg]; omega) h

end MarkedCapExclusions

end VaughtConjecture
