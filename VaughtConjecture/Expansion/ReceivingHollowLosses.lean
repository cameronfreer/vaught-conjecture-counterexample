/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.MarkedCarrierAcquisition
import VaughtConjecture.Expansion.Losses

/-!
# Countable losses with (R3) for cover-hollow models with finite-cut receiving

Roadmap, Layer 5 (condition 2 of the reduction, countable losses); the form of
`VaughtConjecture.Expansion.Losses` in which the hollow comparison uses (R3) for the predicate
`Realization.IsCoverHollowWithReceivingAtBlock` (cover-hollow at a block stage, with finite-cut
receiving).  The models of the count are at `λ_ξ` with `ξ < ω₁` in universe `0`, where (R1)
(`Expansion.FiniteCutReceiving`, item 2) gives them finite-cut receiving, so (R3) is needed only
for that predicate:

* `ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_receivingHollow`: two model expansions
  sharing a terminal property have isomorphic base structures;
* `Expansion.subsingleton_classes_of_property_of_receivingHollow`: at most one class per terminal
  property;
* `Expansion.expansionDomain_loss_countable_of_receivingHollow`: the successor losses are
  countable.

Each is conditional on (R1), the continuation criterion (for the last), (R2), and (R3) for the
predicate, each still to be proved; the last is implied by top-marked carriers at every block
stage (`Realization.hollowReceiving_withReceiving_of_hasTopMarkedCarriers`).

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

/-- **Two model expansions sharing a terminal property have isomorphic base structures**, for
countable carriers at `λ_ξ` with `ξ < ω₁`, conditional on (R1) (`hrec`), (R2) (`hres`) and (R3)
for cover-hollowness with finite-cut receiving at a block stage (`hhol`), each still to be proved.
(R1) is used for the rigid-core property and gives the hollow models finite-cut receiving. -/
theorem ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_receivingHollow {M N : Type w}
    [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N] [Countable M] [Countable N]
    (hrec : Expansion.FiniteCutReceiving.{w}) (hres : Realization.ResidualReceiving.{0, w})
    (hhol : Realization.HollowReceiving.{0, w} Realization.IsCoverHollowWithReceivingAtBlock)
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    {P : TerminalProperty ξ} (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion N (blockStage ξ)) (h : e.1.HasTerminalProperty P)
    (h' : e'.1.HasTerminalProperty P) : Nonempty (M ≃[baseLanguage.{0}] N) := by
  have hα := isSuccLimit_blockStage ξ
  have hω := blockStage_lt_omega_one hξ
  have hr {K : Type w} (R : Realization.{0, w} (blockStage ξ) K) :=
    hrec.finiteExtensionReceiving.receive hα hω R
  rcases P with ⟨_, p⟩ | K | ⟨⟩
  · obtain ⟨x, hx, hcx⟩ := h
    obtain ⟨y, hy, hcy⟩ := h'
    exact Realization.nonempty_equiv_of_isGloballyRigidCore hα e.2 e'.2 (hr _ e.2.isModel)
      (hr _ e'.2.isModel) hx hy hcx hcy
  · exact Realization.nonempty_equiv_of_residual hres hα e.2 e'.2 h.1 h'.1 h.2 h'.2
  · exact Realization.nonempty_equiv_of_hollow hhol hα e.2 e'.2
      ⟨⟨ξ, rfl, h.1⟩, hrec.receive hα hω _ e.2.isModel⟩
      ⟨⟨ξ, rfl, h'.1⟩, hrec.receive hα hω _ e'.2.isModel⟩ h.2 h'.2

namespace Expansion

open Realization

/-- **At most one class per terminal property**, with (R3) for cover-hollowness with finite-cut
receiving: for `ξ < ω₁`, the classes with a code having a model expansion to `λ_ξ` with the
terminal property `P` form a subsingleton, conditional on (R1) (`hrec`), (R2) (`hres`) and (R3)
for that predicate (`hhol`), each still to be proved. -/
theorem subsingleton_classes_of_property_of_receivingHollow (hrec : FiniteCutReceiving.{0})
    (hres : ResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsCoverHollowWithReceivingAtBlock)
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁) (P : TerminalProperty ξ) :
    {q : Quotient (isoSetoid densitySentence.{0}) | ∃ (c : ModelsOf densitySentence.{0})
      (e : @ModelExpansion ℕ c.1.toStructure (blockStage ξ)),
        Quotient.mk _ c = q ∧ e.1.HasTerminalProperty P}.Subsingleton := by
  rintro _ ⟨c, e, rfl, h⟩ _ ⟨c', e', rfl, h'⟩
  obtain ⟨i⟩ := @ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_receivingHollow ℕ ℕ
    c.1.toStructure c'.1.toStructure _ _ hrec hres hhol ξ hξ P e e' h h'
  exact Quotient.sound (isoSetoid_r_iff.mpr ⟨i⟩)

/-- **The successor losses of the expansion domains are countable, with (R3) for cover-hollowness
with finite-cut receiving**, conditional on (R1) (`hrec`), the continuation criterion (`hcont`),
(R2) (`hres`) and (R3) for that predicate (`hhol`), each still to be proved.  The loss at `ξ` is
covered by the countably many subsingletons of classes with a given terminal property. -/
theorem expansionDomain_loss_countable_of_receivingHollow (hrec : FiniteCutReceiving.{0})
    (hcont : ContinuationCriterion.{0}) (hres : ResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsCoverHollowWithReceivingAtBlock) :
    ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable := by
  intro ξ hξ
  have := countable_terminalProperty hξ
  refine Counting.countable_of_subsingleton_cover _
    (subsingleton_classes_of_property_of_receivingHollow hrec hres hhol hξ) fun q hq ↦ ?_
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e⟩ := (mem_expansionDomain_iff c).mp hq.1
  obtain ⟨P, hP⟩ :=
    e.1.exists_hasTerminalProperty hcont hξ e.2.isModel (e.isTerminalAt_of_mem_loss hq)
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, hP⟩

end Expansion

end VaughtConjecture
