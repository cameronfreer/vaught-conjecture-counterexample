/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Label.Visibility

/-!
# The request data at the private type `P` of the gated extension counterexample

Roadmap, Layer 3, 3.3 (the private cap and the decoder of (R4)).

The private type `P` of `GatedExtensionCounterexample` lives on two points (cells `0`, `1`, `2`
dead, of grade `1`; cells `3`, `4` of full scope and grade `2`).  A state with the self-donor is a
pair `(sL, sR)` of functions on the cells of `P`, on the private copy and on the donor copy.

* The donor cells requested `⊥` (`GatedExtensionCounterexample.selfZ`, the dead cells `1`, `2` on
  the new point) and requested high (`GatedExtensionCounterexample.selfT`, the cells `3`, `4`).
* The bottom class of the private side (`GatedExtensionCounterexample.InBottomClassP`), capped
  correctness (`GatedExtensionCounterexample.IsCapCorrectP`) and admission
  (`GatedExtensionCounterexample.IsAdmittedP`).
* With the marker at the cap, correctness is the capped reading of the high cells
  (`GatedExtensionCounterexample.isCapCorrectP_self_iff`); the capped reading gives correctness
  with every marker (`GatedExtensionCounterexample.isCapCorrectP_of_le`).

These are the one definition of the request data at `P`, read as `CapRequests` in
`VaughtConjecture.Extension.CapRequestsExamples` and used by the capped-correctness results of
`VaughtConjecture.Continuation.StableRecoveryCapCorrectness`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.GatedExtensionCounterexample

open Finset Label

/-- The donor cells requested `⊥`: the dead cells on the new point. -/
def selfZ : Finset (Fin 5) := {1, 2}

/-- The donor cells requested high: the two cells of full scope. -/
def selfT : Finset (Fin 5) := {3, 4}

/-- **The bottom class** of the private side: `⊥` exactly at the dead cells. -/
def InBottomClassP (sL : Fin 5 → Label.{u}) : Prop :=
  ∀ d, sL d = ⊥ ↔ d ∈ ({0, 1, 2} : Finset (Fin 5))

/-- **Capped correctness** of a state (`sL` on the private copy, `sR` on the donor copy) for the
cap `C`, the marker `a` and the marker offset `R`, at the threshold `N = 2`: the requested-`⊥` cells
are `⊥` below the cap, and the high cells lie at least at the replaced marker, below the cap. -/
def IsCapCorrectP (C a : Fin 5) (R : ℕ) (sL sR : Fin 5 → Label.{u}) : Prop :=
  (∀ z ∈ selfZ, min (sR z) (sL C) = ⊥) ∧
    ∀ y ∈ selfT, min (visibilityReplace 2 R (sL a)) (sL C) ≤ min (sR y) (sL C)

/-- **Admission**: a state is admitted when it is correct as soon as its private side is in the
bottom class. -/
def IsAdmittedP (C a : Fin 5) (R : ℕ) (sL sR : Fin 5 → Label.{u}) : Prop :=
  InBottomClassP sL → IsCapCorrectP C a R sL sR

variable {C a : Fin 5} {R : ℕ} {sL sR : Fin 5 → Label.{u}}

/-- **With the marker at the cap, correctness is the capped reading** of the high cells, when the
cap's value is self-visible at `N = 2`. -/
theorem isCapCorrectP_self_iff (hC : IsSelfVisible 2 (sL C)) :
    IsCapCorrectP C C R sL sR ↔
      (∀ z ∈ selfZ, min (sR z) (sL C) = ⊥) ∧ ∀ y ∈ selfT, sL C ≤ sR y := by
  rw [IsCapCorrectP, hC.visibilityReplace_eq, min_self]
  refine and_congr Iff.rfl (forall₂_congr fun y _ ↦ ?_)
  exact ⟨fun h ↦ (h.trans (min_le_left _ _)), fun h ↦ le_min h le_rfl⟩

/-- **The capped reading gives correctness** with every marker and offset. -/
theorem isCapCorrectP_of_le (hZ : ∀ z ∈ selfZ, min (sR z) (sL C) = ⊥)
    (hT : ∀ y ∈ selfT, sL C ≤ sR y) : IsCapCorrectP C a R sL sR :=
  ⟨hZ, fun y hy ↦ (min_le_right _ _).trans (le_min (hT y hy) le_rfl)⟩

end VaughtConjecture.GatedExtensionCounterexample
