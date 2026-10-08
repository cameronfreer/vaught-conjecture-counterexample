/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCarrierAcquisition

/-!
# Top-reading carriers: the reading asked only at the cells labelled `⊤`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The cutoff form of determination
(`StageType.isDeterminedWithin_receivingFamily_of_isPrescribedExtension`) keeps every label of the
carrier other than `⊤`, so the reading of the new tops is needed only at the cells of graded index
`(univ, N)` that are labelled `⊤` in the carrier.  A **top-reading carrier**
(`StageType.IsTopReadingCarrier`, defined in `Continuation/MarkedCarrier.lean`) asks exactly that; a
prescribed extension for the top-marked prescription is one
(`StageType.IsPrescribedExtension.isTopReadingCarrier`).  It determines the donor at a cutoff
(`StageType.isDeterminedWithin_receivingFamily_of_isTopReadingCarrier`, compiled in
`Continuation/MarkedCarrier.lean`), and (R3) for cover-hollow models with finite-cut receiving
follows from **top-reading carriers** at every block stage (`StageType.HasTopReadingCarriers`,
implied by `StageType.HasTopMarkedCarriers`;
`Realization.hollowReceiving_withReceiving_of_hasTopReadingCarriers`).
`StageType.HasTopReadingCarriers` is assumed by that theorem at every arity; it is proved at no
arity here.  Contexts on at most four points are proposed test cases (prospective).  The route
through the canonical completion is closed: there a new cell labelled `⊤` is forced at entries
with different values where the input is `⊤` (`Continuation/FieldLayerForcedTops.lean`).

The cells of graded index `(univ, N)` with a label other than `⊤` are free: they may serve the
availability of the lawful labellings that a reading cell cannot.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {k n : ℕ}

variable (α) in
/-- **Top-reading carriers** at the stage `α`: over every legal marked-cap context `t'` along `h`
with top cap `c` and marker `r`, and every legal donor `d` that is a one-point coface of the face
of `t'` along `h`, there is a top-reading carrier.

It is assumed at every arity by
`Realization.hollowReceiving_withReceiving_of_hasTopReadingCarriers` and proved at no arity here;
contexts on at most four points are proposed test cases (prospective).  The canonical completion
does not prove it: there the new cells labelled `⊤` include entries with different values at two
cells where the input is `⊤` (`FieldLayerForcedTops.exists_forced_top`,
`FieldLayerForcedTops.orbitDecoder_fieldRow_eq_top`). -/
def HasTopReadingCarriers : Prop :=
  ∀ ⦃k n : ℕ⦄ (t' : StageType.{u} α k) (h : Fin n ↪ Fin k) (t : StageType.{u} α n)
    (_ : restrictFace h t' = some t) (d : StageType.{u} α (n + 1))
    (_ : restrictFace Fin.castSuccEmb d = some t) (c r : Fin t'.card), t'.IsLegal → d.IsLegal →
    t'.IsMarkedCapContextAt h c r → ∃ D, t'.IsTopReadingCarrier h d c r D

/-- **Top-marked carriers give top-reading carriers.** -/
theorem HasTopMarkedCarriers.hasTopReadingCarriers (hcar : HasTopMarkedCarriers.{u} α) :
    HasTopReadingCarriers.{u} α := fun _ _ t' h t ht d hd c r ht' hd' hctx ↦
  let ⟨D, hD⟩ := hcar t' h t ht d hd c r ht' hd' hctx
  ⟨D, hD.isTopReadingCarrier⟩

end StageType

namespace Realization

/-- **(R3) for cover-hollow models with finite-cut receiving, from top-reading carriers**: as
`Realization.hollowReceiving_withReceiving_of_hasTopMarkedCarriers`, with
`StageType.HasTopReadingCarriers` (which `StageType.HasTopMarkedCarriers` implies). -/
theorem hollowReceiving_withReceiving_of_hasTopReadingCarriers
    (hcar : ∀ ξ : Ordinal.{u}, StageType.HasTopReadingCarriers.{u} (blockStage ξ)) :
    HollowReceiving.{u, w} IsCoverHollowWithReceivingAtBlock where
  exists_covers α M R hα hR hH htop n t c hc d hd := by
    obtain ⟨hH, hrec⟩ := hH
    obtain ⟨k, t', c', h, hc', hcc', ctx, r, hctx⟩ :=
      hollowAcquisition_isMarkedCapContext.exists_context hα hR hH htop t c hc
    obtain ⟨ξ, rfl, -⟩ := hH
    have ht : StageType.restrictFace h t' = some t := by
      rw [← hR.isConsistent ⟨c', hc'.injective⟩ t' h hc'.eval_eq, ← hc.eval_eq]
      congr 1
      ext i
      exact congrFun hcc' i
    obtain ⟨D, hD⟩ := hcar ξ t' h t ht d hd.2 ctx r (hR.isLegal _ _ hc'.eval_eq) hd.1 hctx
    obtain ⟨δ, hδα, hδ⟩ := D.exists_lt_forall_label_lt hα
    have hδc : IsPermittedCutoff (blockStage ξ) (δ : Label.{u}) := isPermittedCutoff_coe.mpr hδα
    have hdet := StageType.isDeterminedWithin_receivingFamily_of_isTopReadingCarrier ht hd.2
      hctx.1 hctx.2.1.1 hctx.2.2.1.le hD hδ
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      (hrec.realizesOver_receivingFamily hc' ⟨hD.isLegal, hD.restrictFace_castSucc⟩ hδc) hdet

end Realization

end VaughtConjecture
