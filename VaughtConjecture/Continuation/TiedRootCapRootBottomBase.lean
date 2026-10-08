/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.Continuation.Hollow
import VaughtConjecture.Continuation.MarkedCap
import VaughtConjecture.Extension.BotKeeping

/-!
# Marked-cap contexts respecting the root bottoms (definitions)

Roadmap, Layer 3 ((R3) of the table of 3.4).

The definitions and lemmas used by the acquisition of marked-cap contexts respecting the root
bottoms: root offsets below a grade and their bound (`StageType.RootOffsetsBelow`,
`StageType.exists_offset_bound`), root bottoms respected (`StageType.RootBottomRespected`) and the
predicate `TiedRootCapRelabel.MarkedCapContextBelow'`, and the named acquisition statement
`Realization.RootBottomAcquisition`.  Compiled in this repository (theorem named).  The marked-cap
context at a given cap and marker (`StageType.IsMarkedCapContextAt`) and the marker inequality
from forcing (`StageType.IsMarker.visibilityReplace_le_of_forcesThreshold`) are in
`VaughtConjecture.Stage.MarkedCap`; visible cells as cells of a face
(`StageType.exists_faceCell_eq`) are in `VaughtConjecture.Stage.Basic`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- The **root offsets lie below `N`** along `h`: every label of a cell visible through `h` that
is an ordinal `μ + f` (`μ` zero or a limit) has `f < N`. -/
def RootOffsetsBelow (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (N : ℕ) : Prop :=
  ∀ y ∈ t'.visibleCells h, ∀ (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
    t'.label y = ((μ + f : Ordinal.{u}) : Label.{u}) → f < N

/-- **A bound on the offsets of finitely many labels**: some `K` exceeds the offset `f` of every
label `μ + f` (`μ` zero or a limit) among the labels of a stage type. -/
theorem exists_offset_bound (t : StageType.{u} α n) :
    ∃ K : ℕ, ∀ d (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
      t.label d = ((μ + f : Ordinal.{u}) : Label.{u}) → f ≤ K := by
  classical
  have hd (d : Fin t.card) : ∃ K : ℕ, ∀ (μ : Ordinal.{u}) (f : ℕ), Order.IsSuccPrelimit μ →
      t.label d = ((μ + f : Ordinal.{u}) : Label.{u}) → f ≤ K := by
    by_cases hx : ∃ o : Ordinal.{u}, t.label d = o
    · obtain ⟨o, ho⟩ := hx
      obtain ⟨μ₀, hμ₀, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
      refine ⟨j, fun μ f hμ hf ↦ ?_⟩
      have h := ho.symm.trans hf
      exact ((add_natCast_eq_add_natCast_iff hμ₀ hμ).mp
        (WithTop.coe_injective (WithBot.coe_injective h))).2.ge
    · exact ⟨0, fun μ f _ hf ↦ absurd ⟨_, hf⟩ hx⟩
  choose K hK using hd
  exact ⟨univ.sup K, fun d μ f hμ hf ↦ (hK d μ f hμ hf).trans (le_sup (mem_univ d))⟩

/-- The row of `c` **respects the root bottoms** along `h`: it reads every cell visible through
`h` and labelled `⊥` as `⊥`. -/
def RootBottomRespected (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (c : Fin t'.card) : Prop :=
  ∀ y ∈ t'.visibleCells h, t'.label y = ⊥ → t'.rowAt c y = ⊥

end StageType

namespace TiedRootCapRelabel

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **Acquired marked-cap contexts respecting the root bottoms**: a marked-cap context along `h`
whose root offsets lie below the grade of its cap and whose cap reads the root cells labelled `⊥`
as `⊥`. -/
def MarkedCapContextBelow' (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) : Prop :=
  ∃ c r, t'.IsMarkedCapContextAt h c r ∧ t'.RootOffsetsBelow h (t'.toCellScheme.grade c) ∧
    t'.RootBottomRespected h c

end TiedRootCapRelabel

namespace Realization

/-- **Acquisition of marked-cap contexts respecting the root bottoms**: hollow acquisition of the
marked-cap contexts with root offsets below the grade of the cap whose cap reads every root cell
labelled `⊥` as `⊥`. -/
def RootBottomAcquisition : Prop :=
  HollowAcquisition.{u, w} IsCoverHollowAtBlock fun t' h ↦
    TiedRootCapRelabel.MarkedCapContextBelow' t' h

end Realization

end VaughtConjecture
