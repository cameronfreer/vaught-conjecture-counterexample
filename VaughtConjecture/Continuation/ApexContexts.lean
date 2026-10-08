/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRootBottomBase

/-!
# Apex types as contexts respecting the root bottoms

Roadmap, Layer 3 ((R3) of the table of 3.4).

The simplest stage types in `TiedRootCapRelabel.MarkedCapContextBelow'`: an apex added to a type
legal below the full grade (`StageType.addApex`), along a root of `n` points with `n + 1 < k`
whose labels are never `⊤` and have offsets below `k`
(`StageType.markedCapContextBelow'_addApex`, compiled in this repository (theorem named)).  The
apex is the top cap and its own marker (it reads every cell labelled `⊤` at the code of `⊤`); the
row inequality at the root tops is vacuous; the apex reads the cells labelled `⊥` as `⊥` (its row
is the code of the labels, `StageType.rowAt_addApex_last_eq_bot_iff`).  Root labels in proper
blocks (ordinals `μ + f` with `f < k`) are allowed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

/-- **An apex type is a context respecting the root bottoms** along every root of `n` points with
`n + 1 < k`, root labels never `⊤`, and root offsets below `k`. -/
theorem markedCapContextBelow'_addApex {t₀ : StageType.{u} α k}
    (ht₀ : t₀.IsLegalBelowFullGrade) (hk : 0 < k) {h : Fin n ↪ Fin k} (hnk : n + 1 < k)
    (hroot : ∀ y ∈ (t₀.addApex ht₀ hk).visibleCells h, (t₀.addApex ht₀ hk).label y ≠ ⊤)
    (hoff : ∀ y ∈ (t₀.addApex ht₀ hk).visibleCells h, ∀ (μ : Ordinal.{u}) (f : ℕ),
      Order.IsSuccPrelimit μ → (t₀.addApex ht₀ hk).label y = ((μ + f : Ordinal.{u}) : Label.{u}) →
        f < k) :
    TiedRootCapRelabel.MarkedCapContextBelow' (t₀.addApex ht₀ hk) h := by
  have hg : (t₀.addApex ht₀ hk).toCellScheme.grade (Fin.last _) = k :=
    congrArg Prod.snd (addApex_gradedIndex_last ht₀ hk)
  refine ⟨Fin.last _, Fin.last _, ⟨⟨addApex_scope_last ht₀ hk, addApex_label_last ht₀ hk,
    fun x _ ↦ by rw [hg]; exact (t₀.addApex ht₀ hk).grade_le x⟩,
    ⟨addApex_label_last ht₀ hk, (t₀.addApex ht₀ hk).toCellScheme.mem_below_gradedIndex _,
      fun x hx _ ↦ le_of_eq ((rowAt_addApex_last ht₀ hk _).trans
        ((congrArg (blockEncode (apexCodes ht₀) k) ((addApex_label_last ht₀ hk).trans
          hx.symm)).trans (rowAt_addApex_last ht₀ hk x).symm))⟩,
    by rw [hg]; exact hnk, fun a ha hat ↦ absurd hat (hroot a ha)⟩,
    fun y hy μ f hμ hf ↦ by rw [hg]; exact hoff y hy μ f hμ hf,
    fun y _ hyb ↦ (rowAt_addApex_last_eq_bot_iff ht₀ hk y).mpr hyb⟩

end StageType

end VaughtConjecture
