/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRootBottom

/-!
# Cutoff determination at contexts respecting the root bottoms

Roadmap, Layer 3 ((R3) of the table of 3.4).

The predicate `TiedRootCapRelabel.MarkedCapContextBelow'` (marked-cap contexts whose root offsets
lie below the grade of the cap and whose cap reads the root cells labelled `⊥` as `⊥`) is acquired
with no hypothesis (`Realization.rootBottomAcquisition`).  This file states cutoff determination and
gives the route inputs for this predicate; the composition with the receiving route is in
`VaughtConjecture.MainTheorem.RootBottomRoute`.

* **The route inputs for the predicate** (compiled): the roots are never onto
  (`TiedRootCapRelabel.MarkedCapContextBelow'.not_surjective`), the predicate is invariant under
  relabelling (`TiedRootCapRelabel.MarkedCapContextBelow'.reindex`, with
  `StageType.rowAt_reindex` and `StageType.mem_below_reindex_iff`), and it is
  acquired (`Realization.rootBottomAcquisition`); together
  `Realization.markedCapContextBelow'_routeInputs`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

/-! ### Relabelling the acquired predicate -/

namespace TiedRootCapRelabel

open StageType

variable {α : Ordinal.{u}} {n k : ℕ}

/-- **The root of an acquired context is not onto**: its top cap has grade above `n + 1`, at most
the number `k` of points. -/
theorem MarkedCapContextBelow'.not_surjective {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow' t' h) : ¬ Function.Surjective h := by
  obtain ⟨c, -, ⟨-, -, hn, -⟩, -⟩ := ht
  intro hs
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_surjective h hs
  have := t'.grade_le c
  omega

/-- **Invariance under relabelling**: the top cap, the marker and the root correspond through the
cell map of `σ`, with their labels and rows. -/
theorem MarkedCapContextBelow'.reindex {t' : StageType.{u} α k} {h : Fin n ↪ Fin k}
    (ht : MarkedCapContextBelow' t' h) (σ : Equiv.Perm (Fin k)) :
    MarkedCapContextBelow' (t'.reindex σ) (h.trans σ.symm.toEmbedding) := by
  obtain ⟨c, r, hctx, hoff, hbot⟩ := ht
  have hsurj := t'.toScheme.surjective_cellMap_equiv σ
  obtain ⟨c', rfl⟩ := hsurj c
  obtain ⟨r', rfl⟩ := hsurj r
  have hvis (a : Fin (t'.reindex σ).card)
      (ha : a ∈ (t'.reindex σ).visibleCells (h.trans σ.symm.toEmbedding)) :
      t'.toScheme.cellMap σ.toEmbedding a ∈ t'.visibleCells h := by
    rw [Scheme.mem_visibleCells] at ha ⊢
    intro y hy
    have hy' : σ.symm y ∈ ((t'.reindex σ).toCellScheme.scope a : Set (Fin k)) := by
      change σ.symm y ∈ (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding a)).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn
      simpa using hy
    obtain ⟨i, hi⟩ := ha hy'
    exact ⟨i, by simpa using congrArg σ hi⟩
  refine ⟨c', r', ?_, ?_, fun a ha hab ↦ ?_⟩
  · obtain ⟨⟨hcs, hcl, hcg⟩, ⟨hrl, hrb, hrm⟩, hn, hroot⟩ := hctx
    refine ⟨⟨?_, hcl, fun x hx ↦ hcg _ hx⟩, ⟨hrl, (mem_below_reindex_iff t' σ c' r').mpr hrb,
      fun x hx hxb ↦ ?_⟩, hn, fun a ha hat ↦ ?_⟩
    · change (t'.toCellScheme.scope (t'.toScheme.cellMap σ.toEmbedding c')).preimage
        σ.toEmbedding σ.toEmbedding.injective.injOn = univ
      rw [hcs]
      exact Finset.preimage_univ _
    · exact (rowAt_reindex t' σ c' r').trans_le
        ((hrm _ hx ((mem_below_reindex_iff t' σ c' x).mp hxb)).trans_eq
          (rowAt_reindex t' σ c' x).symm)
    · exact (congrArg (visibilityReplace _ (n + 1)) (rowAt_reindex t' σ c' r')).trans_le
        ((hroot _ (hvis a ha) hat).trans_eq (rowAt_reindex t' σ c' a).symm)
  · exact fun a ha μ f hμ hf ↦ hoff _ (hvis a ha) μ f hμ hf
  · exact (rowAt_reindex t' σ c' a).trans (hbot _ (hvis a ha) hab)

end TiedRootCapRelabel

/-! ### Hollow cutoff determination and its coatom form -/

namespace Realization

open StageType

/-! ### (R3) from acquisition and cutoff determination -/

/-! ### The acquired predicate -/

/-- **The route inputs for the acquired predicate**: its hollow acquisition (with no hypothesis),
roots never onto, and invariance under relabelling. -/
theorem markedCapContextBelow'_routeInputs :
    HollowAcquisition.{u, w} IsCoverHollowAtBlock
        (fun t' h ↦ TiedRootCapRelabel.MarkedCapContextBelow' t' h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k),
        TiedRootCapRelabel.MarkedCapContextBelow' t' h → ¬ Function.Surjective h) ∧
      (∀ ⦃α : Ordinal.{u}⦄ ⦃n k : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k)
        (σ : Equiv.Perm (Fin k)), TiedRootCapRelabel.MarkedCapContextBelow' t' h →
          TiedRootCapRelabel.MarkedCapContextBelow' (t'.reindex σ)
            (h.trans σ.symm.toEmbedding)) :=
  ⟨rootBottomAcquisition, fun _ _ _ _ _ ht ↦ ht.not_surjective, fun _ _ _ _ _ σ ht ↦ ht.reindex σ⟩

end Realization

end VaughtConjecture
