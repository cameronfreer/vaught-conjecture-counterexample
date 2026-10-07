/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.AnchoredDetermination
import VaughtConjecture.Continuation.ExactReceivingExamples
import VaughtConjecture.Extension.GatedExtensionCounterexample

/-!
# Determination over anchored contexts fails

Roadmap, Layer 3 ((R2) and (R3) of the table of 3.4); the refuting instance for the anchored
context of `VaughtConjecture.Continuation.AnchoredDetermination`.

**The instance**, at every limit stage `α`:

* the **root** is the stage type on no points (the empty root);
* the **donor** (`AnchoredDeterminationCounterexample.donor α`) is the stage type on one point
  whose only cell is an apex of grade `1` labelled `⊤`, the apex added to the one-point scheme
  with no cells (`StageType.addApex`, `StageType.cellless`).  It is legal, a coface of the empty
  root, and not top-free, so the empty root is not a rigid core of it
  (`StageType.isRigidCoreIn_empty_iff_isTopFree`);
* the **context** (`AnchoredDeterminationCounterexample.context α`) is the legal two-point type
  `GatedExtensionCounterexample.P α`, whose cells `3` and `4` have graded index `(univ, 2)` and
  are labelled `⊤`, capped at an ordinal `c < α` self-visible at `2` (`StageType.cap`).  It is
  legal and top-free, and cell `3`, labelled `c`, is a private cap.  The donor's only label is `⊤`
  (`AnchoredDeterminationCounterexample.donor_label_eq_top`), so the label bound and the anchoring
  (`StageType.isAnchored_of_forall_label_eq_bot_or_top`) hold vacuously, and the context is an
  anchored context for the donor (`StageType.IsAnchoredContext`).  The instance uses only the
  clauses `n + 1 < k` and the existence of a cell of graded index `(univ, k)`.

Over this context, along the empty face, the donor is determined neither within the receiving
family of any coface at any permitted cutoff nor within the stage types on the scheme of any
coface (`AnchoredDeterminationCounterexample.exists_not_isDeterminedWithin`): the context is
top-free, so no private top is available to a new cell
(`StageType.not_hasAvailablePrivateTop_of_isTopFree`), and capping the new cells lowers the apex to
an ordinal (`StageType.not_isDeterminedWithin_receivingFamily_of_not_hasAvailablePrivateTop`).  So
cutoff determination with a donor fails for the anchored context
(`AnchoredDeterminationCounterexample.not_cutoffDonorDetermination`), while donor acquisition holds
for it in every model (`Realization.donorAcquisition_isAnchoredContext`).

The refuted statement is determination for this predicate; nothing here refutes (R2) or (R3).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.AnchoredDeterminationCounterexample

open Finset StageType Realization Label

variable (α : Ordinal.{u})

/-- The stage type on one point with no cells. -/
def celllessType : StageType.{u} α 1 :=
  ExactReceivingExamples.celllessTypeAt α

/-- **The donor**: the stage type on one point whose only cell is an apex of grade `1`, labelled
`⊤`. -/
noncomputable def donor : StageType.{u} α 1 :=
  ExactReceivingExamples.apexPointAt α

/-- The donor is legal. -/
theorem isLegal_donor : (donor α).IsLegal :=
  ExactReceivingExamples.isLegal_apexPointAt α

/-- The donor is not top-free: its apex is labelled `⊤`. -/
theorem not_isTopFree_donor : ¬ (donor α).IsTopFree :=
  ExactReceivingExamples.not_isTopFree_apexPointAt α

/-- The donor has exactly one cell, the apex, so its only label is `⊤`. -/
theorem donor_label_eq_top (j : Fin (donor α).card) : (donor α).label j = ⊤ := by
  obtain rfl : j = Fin.last _ := Subsingleton.elim (α := Fin 1) _ _
  exact addApex_label_last _ one_pos

/-- **The empty root is not a rigid core of the donor**, at a limit stage. -/
theorem not_isRigidCoreIn_donor (hα : Order.IsSuccLimit α) :
    ¬ (donor α).IsRigidCoreIn Fin.castSuccEmb :=
  fun h ↦ not_isTopFree_donor α
    ((isRigidCoreIn_empty_iff_isTopFree hα (isLegal_donor α) Fin.castSuccEmb).mp h)

/-- **The context**: the legal two-point type `GatedExtensionCounterexample.P α`, whose two cells of
graded index `(univ, 2)` are labelled `⊤`, capped at an ordinal `c < α` self-visible at `2`. -/
noncomputable def context {c : Ordinal.{u}} (hc : IsSelfVisible 2 (c : Label.{u})) (hcα : c < α) :
    StageType.{u} α 2 :=
  (GatedExtensionCounterexample.P α).cap c hc hcα

variable {α} {c : Ordinal.{u}} (hc : IsSelfVisible 2 (c : Label.{u})) (hcα : c < α)

/-- The context is legal. -/
theorem isLegal_context : (context α hc hcα).IsLegal :=
  isLegal_cap.mpr (GatedExtensionCounterexample.isLegal_P α)

/-- The context is top-free. -/
theorem isTopFree_context : (context α hc hcα).IsTopFree :=
  isTopFree_cap

/-- **The context is an anchored context for the donor**: its cell `3` has graded index
`(univ, 2)` (and is labelled `c`, by the cap).  The donor's only label is `⊤`
(`donor_label_eq_top`), so the label bound and the anchoring hold vacuously. -/
theorem isAnchoredContext_context : (context α hc hcα).IsAnchoredContext (donor α) :=
  -- the context has five cells (`GatedExtensionCounterexample.P`); cell `3` has graded index
  -- `(univ, 2)`
  ⟨by omega, ⟨3, by change 3 < 5; omega⟩, rfl, fun j hj ↦ absurd (donor_label_eq_top α j) hj,
    isAnchored_of_forall_label_eq_bot_or_top _ _ fun j _ ↦ .inr (donor_label_eq_top α j)⟩

/-- **The refuting instance**: at a limit stage, the context is a legal anchored context for the
donor whose face along the empty embedding is a stage type `t` on no points, the donor is a coface
of `t` in which the root is not a rigid core, and over the context along the empty face the donor
is determined neither within the receiving family of any coface at any permitted cutoff nor within
the stage types on the scheme of any coface. -/
theorem exists_not_isDeterminedWithin (hα : Order.IsSuccLimit α) :
    ∃ (t' : StageType.{u} α 2) (h : Fin 0 ↪ Fin 2) (t : StageType.{u} α 0),
      t'.IsLegal ∧ t'.IsAnchoredContext (donor α) ∧ restrictFace h t' = some t ∧
        donor α ∈ t.cofaces ∧ ¬ (donor α).IsRigidCoreIn Fin.castSuccEmb ∧
        ∀ D' : StageType.{u} α 3, restrictFace Fin.castSuccEmb D' = some t' →
          (∀ δ, IsPermittedCutoff α δ →
            ¬ IsDeterminedWithin (receivingFamily D' δ) t' h (donor α)) ∧
          ¬ IsDeterminedWithin (saturationFamily D'.toScheme) t' h (donor α) := by
  obtain ⟨c, -, hcα, hc⟩ := exists_lt_lt_isSelfVisible hα.isSuccPrelimit hα.bot_lt 2
  let h : Fin 0 ↪ Fin 2 := Function.Embedding.ofIsEmpty
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((context α hc hcα).isSome_restrictFace_of_zero h)
  have hnr := not_isRigidCoreIn_donor α hα
  refine ⟨context α hc hcα, h, t, isLegal_context hc hcα, isAnchoredContext_context hc hcα, ht,
    mem_cofaces_of_zero (isLegal_donor α), hnr, fun D' hD' ↦ ?_⟩
  have hav := not_hasAvailablePrivateTop_of_isTopFree hD' (isTopFree_context hc hcα)
  have htop := exists_new_top_of_not_isRigidCoreIn hnr
  exact ⟨fun _ hδ ↦ not_isDeterminedWithin_receivingFamily_of_not_hasAvailablePrivateTop hα hD'
    hav htop hδ, not_isDeterminedWithin_saturationFamily_of_not_hasAvailablePrivateTop hα hD' hav
    htop⟩

/-- **Cutoff determination with a donor fails for the anchored context**, already at `ω`, while
donor acquisition holds for it in every model (`Realization.donorAcquisition_isAnchoredContext`).
This refutes determination for this predicate only. -/
theorem not_cutoffDonorDetermination :
    ¬ CutoffDonorDetermination.{u} fun t' _ d ↦ t'.IsAnchoredContext d := by
  intro hdet
  obtain ⟨t', h, t, ht', hP, ht, hd, hnr, hno⟩ :=
    exists_not_isDeterminedWithin Ordinal.isSuccLimit_omega0.{u}
  obtain ⟨D', hD', δ, hδ, hdet'⟩ :=
    hdet.exists_coface t' h _ Ordinal.isSuccLimit_omega0 ht' hP t ht hd hnr
  exact (hno D' hD'.2).1 δ hδ hdet'

end VaughtConjecture.AnchoredDeterminationCounterexample
