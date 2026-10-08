/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCap

/-!
# The grade of the marker is not below the grade of the cap in general

Roadmap, Layer 3 ((R3) of the table of 3.4).

The forcing lemma of `VaughtConjecture.Continuation.TopReadingLift`
(`CellScheme.Rows.IsLawful.exists_top_row_lt`) applies when the marker `r` has the grade `N` of the
reading cells at `(univ, N)`: availability at `(univ, N)` is used at `r`.  A marked-cap context
whose marker has a grade below `N` escapes it.  This file records that the marked-cap context does
not provide such a marker in general, and that the cap cannot be moved one grade higher.

* **No cap above the top cap** (`StageType.IsTopCap.label_ne_top_of_grade_lt`, compiled in this
  repository (theorem named)): every cell of grade above a top cap has a label other than `⊤`, so
  no cell of grade `N + 1` is a top cap, and the reading cell at `(univ, N + 1)` given by
  availability from a cap of that grade is not labelled `⊤`.
* **A legal marked-cap context whose markers have the grade of the cap**
  (`MarkedCapExclusions.exists_isMarkedCapContext_grade_marker_eq`, compiled in this repository
  (theorem named)): the legal two-point type `GatedExtensionCounterexample.P α` is a marked-cap
  context over the empty root (`MarkedCapExclusions.isMarkedCapContext_P`), and its cells labelled
  `⊤` are the two cells of graded index `(univ, 2)`, so every marker of every top cap has the grade
  `2` of the cap (`MarkedCapExclusions.grade_marker_eq_P`).

So a marker of grade below `N` is not available from the marked-cap context alone; whether the
acquisition from a cover-hollow model (`Realization.hollowAcquisition_isMarkedCapContext`) can be
steered to one is not settled here (prospective).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {β : Ordinal.{u}} {m : ℕ} {q : StageType.{u} β m} {c : Fin q.card}

/-- **No cell above a top cap is labelled `⊤`.** -/
theorem IsTopCap.label_ne_top_of_grade_lt (hc : q.IsTopCap c) {x : Fin q.card}
    (hx : q.toCellScheme.grade c < q.toCellScheme.grade x) : q.label x ≠ ⊤ :=
  fun h ↦ (hc.2.2 x h).not_gt hx

/-- **No cell of grade above a top cap is a top cap.** -/
theorem IsTopCap.not_isTopCap_of_grade_lt (hc : q.IsTopCap c) {x : Fin q.card}
    (hx : q.toCellScheme.grade c < q.toCellScheme.grade x) : ¬ q.IsTopCap x :=
  fun hx' ↦ hc.label_ne_top_of_grade_lt hx hx'.2.1

end StageType

namespace MarkedCapExclusions

/-- The cells of the two-point type labelled `⊤` have the grade `2`. -/
theorem grade_eq_two_of_label_eq_top_P {α : Ordinal.{u}} {x : Fin 5}
    (hx : (GatedExtensionCounterexample.P α).label x = ⊤) :
    (GatedExtensionCounterexample.P α).toCellScheme.grade x = 2 := by
  -- the labels are `labelling ⊤ ⊤ = (⊥, ⊥, ⊥, ⊤, ⊤)` and the grades `(1, 1, 1, 2, 2)`
  change GatedExtensionCounterexample.labelling ⊤ ⊤ x = ⊤ at hx
  change GatedExtensionCounterexample.cellGrade x = 2
  fin_cases x <;> simp_all [GatedExtensionCounterexample.labelling,
    GatedExtensionCounterexample.cellGrade]

/-- **Every marker of the two-point type has the grade of its top cap.** -/
theorem grade_marker_eq_P {α : Ordinal.{u}} {c r : Fin 5}
    (hc : (GatedExtensionCounterexample.P α).IsTopCap c)
    (hr : (GatedExtensionCounterexample.P α).IsMarker c r) :
    (GatedExtensionCounterexample.P α).toCellScheme.grade r =
      (GatedExtensionCounterexample.P α).toCellScheme.grade c := by
  rw [grade_eq_two_of_label_eq_top_P hr.1, grade_eq_two_of_label_eq_top_P hc.2.1]

/-- **A legal marked-cap context whose markers all have the grade of their cap**: the two-point
type over the empty root. -/
theorem exists_isMarkedCapContext_grade_marker_eq (α : Ordinal.{u}) (h : Fin 0 ↪ Fin 2) :
    ∃ t' : StageType.{u} α 2, t'.IsLegal ∧ t'.IsMarkedCapContext h ∧
      ∀ c r, t'.IsTopCap c → t'.IsMarker c r →
        t'.toCellScheme.grade r = t'.toCellScheme.grade c :=
  ⟨_, GatedExtensionCounterexample.isLegal_P α, isMarkedCapContext_P α h,
    fun _ _ hc hr ↦ grade_marker_eq_P hc hr⟩

end MarkedCapExclusions

end VaughtConjecture
