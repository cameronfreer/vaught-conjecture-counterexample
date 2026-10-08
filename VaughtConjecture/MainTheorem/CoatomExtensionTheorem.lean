/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ForcingDonorsCoatom
import VaughtConjecture.Extension.PrescribedFullRows
import VaughtConjecture.Extension.ProfileTowerCompletion
import VaughtConjecture.MainTheorem.AllCarriers
import VaughtConjecture.MainTheorem.LowerBound
import VaughtConjecture.MainTheorem.SameLevelMaximal

/-!
# Consequences of the coatom extension theorem

Roadmap, Layer 3, 3.1, (R6), 2.7 and the table of Layer 3; Layer 6 ("Status: the hypotheses of
the main theorem").

**The coatom extension property with apex** holds at every stage that is zero or a limit
(`StageType.hasApexCoatomExtensions`, `VaughtConjecture.Extension.ProfileTowerCompletion`): every
seed has a completion below the full grade.  So the statements formerly derived from it as a
hypothesis (hypothesis 8 of the roadmap) hold with that hypothesis discharged; each is compiled in
this repository (theorem named), with the hypotheses listed:

* at every block stage `λ_η = ω + ω · η`, the coatom extension property with apex
  (`StageType.hasApexCoatomExtensions_blockStage`), and at every stage that is zero or a limit the
  plain coatom extension property (`StageType.hasCoatomExtensions`) and the exact pinned extension
  (`StageType.exists_pinned_extension_of_isSuccPrelimit`; row 6 of the table of Layer 3, 3.4),
  and the compatibility of the empty prescription (`StageType.hasCompatibleEmptyPrescription`);
  no hypothesis besides the stage;
* forcing donors at every block index (`forcingDonors_blockStage`); no hypothesis;
* the cap-to-model theorem at `ω`, for the realizations on the carriers of every universe
  (`MainTheorem.capToModel`), and the absence of finite models of the density sentence
  (`MainTheorem.infinite_of_realize_densitySentence`); no hypothesis;
* nonempty losses of the expansion domains of the density sentence (condition 4), from next-block
  uniqueness alone (`MainTheorem.hasNonemptyLosses_of_nextBlockUniqueness`);
* acceptance lemma 1, the same-level maximal realization at every countable block index
  (`exists_sameLevelMaximal_covers'`); no hypothesis besides `β < ω₁`;
* the continuation criterion, and output 3 of higher-stage reconstruction, from (R4) alone
  (`ContinuationCriterion.of_stableCappedReceiving'`,
  `Realization.isModel_stableCandidate_of_stableCappedReceiving`).

Next-block uniqueness, (R1), (R2), (R3), (R4) and the continuation criterion are not derived here;
each is still to be proved.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Ordinal StageType

/-- **The coatom extension property with apex at every block stage** `λ_η = ω + ω · η`. -/
theorem StageType.hasApexCoatomExtensions_blockStage (η : Ordinal.{u}) :
    HasApexCoatomExtensions.{u} (blockStage η) :=
  hasApexCoatomExtensions (isSuccPrelimit_blockStage η)

/-- **The coatom extension property at every stage that is zero or a limit**: forget the apex. -/
theorem StageType.hasCoatomExtensions {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α) :
    HasCoatomExtensions.{u} α :=
  (hasApexCoatomExtensions hα).hasCoatomExtensions

/-- **The exact pinned extension at every stage that is zero or a limit** (row 6 of the table of
Layer 3, 3.4): for a legal stage type `P`, a closed face `f` of `P` with restriction `p`, and a
legal one-point coface `d` of `p`, some legal one-point extension `Q` of `P` has the face `d`
along `extendByLast f` (`StageType.exists_pinned_extension`). -/
theorem StageType.exists_pinned_extension_of_isSuccPrelimit {α : Ordinal.{u}} {n m : ℕ}
    (hα : Order.IsSuccPrelimit α) {P : StageType.{u} α n} (hP : P.IsLegal) {f : Fin m ↪ Fin n}
    {p : StageType.{u} α m} {d : StageType.{u} α (m + 1)} (hPf : restrictFace f P = some p)
    (hd : d.IsLegal) (hdp : restrictFace Fin.castSuccEmb d = some p) :
    ∃ Q : StageType.{u} α (n + 1), Q.IsLegal ∧ restrictFace Fin.castSuccEmb Q = some P ∧
      restrictFace (extendByLast f) Q = some d :=
  exists_pinned_extension (hasCoatomExtensions hα) hP hPf hd hdp

/-- **The empty prescription is compatible at every stage that is zero or a limit**
(`StageType.HasCoatomExtensions.hasCompatibleEmptyPrescription`). -/
theorem StageType.hasCompatibleEmptyPrescription {α : Ordinal.{u}} (hα : Order.IsSuccPrelimit α) :
    HasCompatibleEmptyPrescription.{u} α :=
  (hasCoatomExtensions hα).hasCompatibleEmptyPrescription

/-- **Forcing donors at every block index** (`forcingDonors_of_hasApexCoatomExtensions`, at the
next block stage). -/
theorem forcingDonors_blockStage (η : Ordinal.{u}) : ForcingDonors.{u} η :=
  forcingDonors_of_hasApexCoatomExtensions (StageType.hasApexCoatomExtensions_blockStage (η + 1))

/-- **The continuation criterion from (R4) alone**
(`ContinuationCriterion.of_hasApexCoatomExtensions`, with the coatom extension property with apex
at every next block stage).  (R4) (`hR4`) is not proved. -/
theorem ContinuationCriterion.of_stableCappedReceiving' (hR4 : StableCappedReceiving.{w}) :
    ContinuationCriterion.{w} :=
  .of_hasApexCoatomExtensions hR4 fun ξ _ ↦ StageType.hasApexCoatomExtensions_blockStage (ξ + 1)

/-- **Output 3 from (R4) alone**: the stable candidate of a model at `λ_ξ`, `ξ < ω₁`, that is not
cover-hollow and has top-grade supremum `⊤` is a model at `λ_{ξ+1}`
(`Realization.isModel_stableCandidate_of_hasApexCoatomExtensions`).  (R4) (`hR4`) is not
proved. -/
theorem Realization.isModel_stableCandidate_of_stableCappedReceiving {ξ : Ordinal.{0}}
    {M : Type w} {R : Realization.{0, w} (blockStage ξ) M} (hξ : ξ < ω₁) (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) (hR4 : StableCappedReceiving.{w}) :
    (R.stableCandidate hR.isStablyLawful).IsModel :=
  isModel_stableCandidate_of_hasApexCoatomExtensions hξ hR hnh hgrow hR4
    (StageType.hasApexCoatomExtensions_blockStage (ξ + 1))

/-- **Acceptance lemma 1, the same-level maximal realization**, at every countable block index `β`
(`exists_sameLevelMaximal_covers`, with the coatom extension property with apex at `λ_β` and
forcing donors at `β` compiled): on every countably infinite carrier, every legal stage type at
`λ_β` is covered at any prescribed tuple by a model at `λ_β` that covers every legal stage type,
receives exactly the legal types, and is cover-hollow and terminal at `β`. -/
theorem exists_sameLevelMaximal_covers' {β : Ordinal.{0}} (hβ : β < ω₁)
    (X : Type) [Countable X] [Infinite X] {n : ℕ} {p : StageType.{0} (blockStage β) n}
    (hp : p.IsLegal) (a : Fin n ↪ X) :
    ∃ H : Realization.{0, 0} (blockStage β) X, H.IsModel ∧ H.Covers p a ∧
      (∀ ⦃n : ℕ⦄ (p : StageType.{0} (blockStage β) n), p.IsLegal → ∃ c : Fin n → X, H.Covers p c) ∧
      H.ExactReceivingWithin (fun m ↦ {D : StageType.{0} (blockStage β) m | D.IsLegal}) ∧
      H.IsCoverHollow ∧ H.IsTerminalAt β :=
  exists_sameLevelMaximal_covers hβ (StageType.hasApexCoatomExtensions_blockStage β)
    (forcingDonors_blockStage β) X hp a

namespace MainTheorem

open Expansion

/-- **The cap-to-model theorem at `ω`**, for the realizations on the carriers of every universe
`w` (`MainTheorem.CapToModel.of_hasApexCoatomExtensions`); no hypothesis. -/
theorem capToModel : CapToModel.{w} :=
  CapToModel.of_hasApexCoatomExtensions
    (hasApexCoatomExtensions Ordinal.isSuccLimit_omega0.isSuccPrelimit)

/-- **The density sentence has no finite models**, on the carriers of every universe
(`MainTheorem.infinite_of_realize_densitySentence_of_hasCoatomExtensions`, with the coatom extension
property at `ω` compiled); no hypothesis. -/
theorem infinite_of_realize_densitySentence {M : Type w} [baseLanguage.{u}.Structure M]
    (h : baseLanguage.densitySentence.Realize M) : Infinite M :=
  infinite_of_realize_densitySentence_of_hasCoatomExtensions
    (StageType.hasCoatomExtensions Ordinal.isSuccLimit_omega0.isSuccPrelimit) h

/-- **Nonempty losses of the expansion domains of the density sentence** (condition 4 of the
reduction), from next-block uniqueness of models (`hnext`) alone
(`MainTheorem.hasNonemptyLosses_of_hasApexCoatomExtensions`).  Next-block uniqueness is not proved
here. -/
theorem hasNonemptyLosses_of_nextBlockUniqueness (hnext : NextBlockUniqueness.{0}) :
    (modelExpansionDomains capToModel hnext).HasNonemptyLosses :=
  hasNonemptyLosses_of_hasApexCoatomExtensions capToModel hnext
    fun η _ ↦ StageType.hasApexCoatomExtensions_blockStage η

end MainTheorem

end VaughtConjecture
