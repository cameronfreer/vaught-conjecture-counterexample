/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Continuation
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.MainTheorem.Assembly

/-!
# The cap-to-model theorem at `ω` from the coatom extension property with apex

Roadmap, Layer 3, 3.4 (the cap-to-model theorem); the main theorem's hypothesis `CapToModel`.

The hypothesis `CapToModel.{w}` of the main theorem (a realization at stage `ω`, on a carrier in
`Type w`, with a nonempty carrier, legal types, exact consistency, covering, and finite-cut
receiving, is a model) follows from the coatom extension property with apex at `ω`
(`CapToModel.of_hasApexCoatomExtensions`): it is the cap-to-model theorem at the nonzero limit
stage `ω` (`Realization.isModel_of_hasFiniteCutReceiving`), whose two nonemptiness hypotheses hold
at every legal type, uniformity under the plain coatom extension property
(`StageType.nonempty_cofaces_inter_uniformityFamily`) and dominance under the form with apex
(`StageType.nonempty_cofaces_inter_dominanceFamily`).  The coatom extension property with apex at
`ω` is not proved.

**Output 3 and the continuation criterion.**  At every stage that is zero or a limit, the coatom
extension property with apex gives the three coface instances used by the cap-to-model theorem and
by the empty-root case of receiving
(`StageType.HasNonemptyCofaceInstances.of_hasApexCoatomExtensions`, in
`VaughtConjecture.Extension.FamilyCofaces`).  At the block stages `λ_{ξ+1}` this gives output 3
of higher-stage reconstruction for every model at `λ_ξ`, `ξ < ω₁`, that is not cover-hollow and
has top-grade supremum `⊤` (`Realization.isModel_stableCandidate_of_hasApexCoatomExtensions`),
conditional on (R4) (`StableCappedReceiving`) and the coatom extension property with apex at
`λ_{ξ+1}` only, neither of which is proved; the stable candidate is defined because every model is
stably lawful (`Realization.IsModel.isStablyLawful`).  It also gives the continuation criterion
(`ContinuationCriterion.of_hasApexCoatomExtensions`), conditional on (R4) and the coatom extension
property with apex at every `λ_{ξ+1}` with `ξ < ω₁`.

## Placement

This file belongs to the main theorem of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.MainTheorem

open StageType
open scoped Ordinal

/-- **The cap-to-model theorem at `ω`** from the coatom extension property with apex at `ω`, for
the realizations on the carriers of every universe `w`. -/
theorem CapToModel.of_hasApexCoatomExtensions (hext : HasApexCoatomExtensions.{0} ω) :
    CapToModel.{w} :=
  ⟨fun _ hne hl hc hcov hr ↦ Realization.isModel_of_hasFiniteCutReceiving
    Ordinal.isSuccLimit_omega0 hne hl hc hcov hr
    (fun x _ _ hγ ↦ nonempty_cofaces_inter_uniformityFamily hext.hasCoatomExtensions
      Ordinal.isSuccLimit_omega0.isSuccPrelimit (hl _ _ x.eval_tuple) hγ)
    (fun x _ hγ ↦ nonempty_cofaces_inter_dominanceFamily hext
      Ordinal.isSuccLimit_omega0.isSuccPrelimit (hl _ _ x.eval_tuple) hγ)⟩

end VaughtConjecture.MainTheorem

namespace VaughtConjecture

universe u

open Ordinal StageType

/-- **Output 3 under the coatom extension property with apex at the next block**: the stable
candidate of a model at `λ_ξ`, `ξ < ω₁`, that is not cover-hollow and has top-grade supremum `⊤` is
a model at `λ_{ξ+1}`, conditional on (R4) (`hR4`) and the coatom extension property with apex at
`λ_{ξ+1}` (`hapex`), neither of which is proved. -/
theorem Realization.isModel_stableCandidate_of_hasApexCoatomExtensions {ξ : Ordinal.{0}}
    {M : Type w} {R : Realization.{0, w} (blockStage ξ) M} (hξ : ξ < ω₁) (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) (hR4 : StableCappedReceiving.{w})
    (hapex : HasApexCoatomExtensions.{0} (blockStage (ξ + 1))) :
    (R.stableCandidate hR.isStablyLawful).IsModel :=
  isModel_stableCandidate hξ hR hnh hgrow hR4
    (.of_hasApexCoatomExtensions hapex (isSuccLimit_blockStage (ξ + 1)).isSuccPrelimit)

/-- **The continuation criterion under the coatom extension property with apex at every next
block**, conditional on (R4) (`hR4`) and the coatom extension property with apex at every
`λ_{ξ+1}` with `ξ < ω₁` (`hext`), neither of which is proved. -/
theorem ContinuationCriterion.of_hasApexCoatomExtensions (hR4 : StableCappedReceiving.{w})
    (hext : ∀ ξ < ω₁, HasApexCoatomExtensions.{0} (blockStage (ξ + 1))) :
    ContinuationCriterion.{w} :=
  .of_stableCappedReceiving hR4 fun ξ hξ ↦ .of_hasApexCoatomExtensions (hext ξ hξ)
    (isSuccLimit_blockStage (ξ + 1)).isSuccPrelimit

end VaughtConjecture
