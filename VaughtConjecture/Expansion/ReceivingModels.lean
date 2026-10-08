/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Continuation
import VaughtConjecture.Expansion.UniquenessOfForcing
import VaughtConjecture.Realization.ReceivingLimit

/-!
# Uniqueness and continuation for receiving models

Roadmap, Layer 5 (coherent countable-limit expansions) and Layer 4, outputs 3 and 4 of
higher-stage reconstruction, for the auxiliary class `𝒞_α` of receiving models
(`Realization.IsReceivingModel`: models with the finite-cut receiving property); semantic
contract, items 5, 9 and 12.

In the class of receiving models, finite-cut receiving is a clause of the class, so the per-model
theorems that take receiving of the given models as an explicit hypothesis apply by
instantiation, without (R1) of the table of Layer 3.  The interfaces below are new statements
about receiving models, not renamings of the statements about all models: each is compared with
its form for models.

**Next-block uniqueness** (`Expansion.ReceivingNextBlockUniqueness`): two receiving models at
`λ_{ξ+1}`, `ξ < ω₁`, with equal reductions to `λ_ξ` are equal.  It follows from forcing donors
alone (`Expansion.ReceivingNextBlockUniqueness.of_forcingDonors`, by instantiation of
`Realization.eq_of_reduce_eq_of_forcingDonors`, which takes receiving of the two given
realizations); (R1) is not used.  Next-block uniqueness of models gives it
(`Expansion.NextBlockUniqueness.receivingNextBlockUniqueness`); conversely it gives next-block
uniqueness of models given (R1) (`Expansion.ReceivingNextBlockUniqueness.nextBlockUniqueness`).

**Uniqueness of receiving models** (`Realization.IsReceivingModel.eq_of_reduce_zero_eq`,
`ModelExpansion.eq_of_hasFiniteCutReceiving`): given next-block uniqueness of receiving models,
two receiving models at `λ_ξ`, `ξ < ω₁`, with the same reduction to `λ_0 = ω` are equal; so a base
structure has at most one model expansion with finite-cut receiving to each countable block
stage.  The induction is that of `ModelExpansion.subsingleton`, inside the class: the reductions
of a receiving model are receiving models (`Realization.IsReceivingModel.reduce`), so the
successor step stays in the class, and the limit step is separation of realizations.

**Continuation** (`Expansion.ReceivingContinuationCriterion`): a receiving model at `λ_ξ`,
`ξ < ω₁`, not cover-hollow and with top-grade supremum `⊤`, is the reduction of a receiving model
at `λ_{ξ+1}`.  The conclusion is receiving **and** modelhood of the successor; the continuation
criterion for models (`ContinuationCriterion`) concludes modelhood only.  It follows from the
receiving form of (R4) (`Expansion.ReceivingStableCappedReceiving`, (R4) asked only of receiving
models) and the coface instances at the next block stages
(`Expansion.ReceivingContinuationCriterion.of_receivingStableCappedReceiving`): the candidate
receives by the argument of `Realization.hasFiniteCutReceiving_stableCandidate`, and is a model by
the cap-to-model theorem.  (R4) gives its receiving form
(`Expansion.StableCappedReceiving.receivingStableCappedReceiving`); the converse is not claimed.

**Terminality** (`Realization.IsReceivingTerminalAt`): no receiving model at the next block stage
reduces to the realization.  A terminal realization is receiving-terminal
(`Realization.IsTerminalAt.isReceivingTerminalAt`); the converse holds when every model successor
receives (`Realization.isReceivingTerminalAt_iff_isTerminalAt`), in particular under (R1)
(`Realization.isReceivingTerminalAt_iff_isTerminalAt_of_finiteCutReceiving`), and is not claimed
otherwise: "no receiving successor" is not shown to give "no model successor".  Under the receiving
continuation criterion, a receiving-terminal receiving model with top-grade supremum `⊤` is
cover-hollow (`Realization.IsReceivingTerminalAt.isCoverHollow`).

**Status.**  Proved: the statements above, each from the explicit hypotheses named.  Forcing
donors, the receiving form of (R4), and the coface instances remain hypotheses.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Ordinal Label StageType

/-! ### Next-block determination of receiving models -/

namespace Realization

section Determination

variable {η : Ordinal.{u}} {M : Type v} {R R' : Realization.{u, v} (blockStage (η + 1)) M}

/-- **Determination of receiving models by their reduction**, conditional on forcing donors at
`η`: two receiving models at `λ_{η+1}` with equal reductions to `λ_η` are equal.  Receiving of the
two models is a clause of the class; (R1) is not used. -/
theorem IsReceivingModel.eq_of_reduce_eq_of_forcingDonors (hF : ForcingDonors.{u} η)
    (hR : R.IsReceivingModel) (hR' : R'.IsReceivingModel)
    (h : R.reduce (isSuccPrelimit_blockStage η) = R'.reduce (isSuccPrelimit_blockStage η)) :
    R = R' :=
  have hα := isSuccPrelimit_blockStage (η + 1)
  Realization.eq_of_reduce_eq_of_forcingDonors hF hR.1.isConsistent hR'.1.isConsistent
    hR.1.hasLegalTypes hR'.1.hasLegalTypes (hR.2.hasFiniteExtensionReceiving hR.1.isConsistent hα)
    (hR'.2.hasFiniteExtensionReceiving hR'.1.isConsistent hα) h

end Determination

end Realization

namespace Expansion

/-- **Next-block uniqueness of receiving models** on the carriers in the universe `w`: two
receiving models at `λ_{ξ+1}`, `ξ < ω₁`, on one carrier, with the same stage reduction to `λ_ξ`,
are equal. -/
structure ReceivingNextBlockUniqueness : Prop where
  /-- Receiving models at `λ_{ξ+1}` with equal reductions to `λ_ξ` are equal. -/
  eq_of_reduce_eq : ∀ {ξ : Ordinal.{0}} {M : Type w}, ξ < ω₁ →
    ∀ R R' : Realization.{0, w} (blockStage (ξ + 1)) M, R.IsReceivingModel →
      R'.IsReceivingModel →
        R.reduce (isSuccPrelimit_blockStage ξ) = R'.reduce (isSuccPrelimit_blockStage ξ) → R = R'

/-- Next-block uniqueness of models gives it for receiving models. -/
theorem NextBlockUniqueness.receivingNextBlockUniqueness (h : NextBlockUniqueness.{w}) :
    ReceivingNextBlockUniqueness.{w} :=
  ⟨fun hξ R R' hR hR' ↦ h.eq_of_reduce_eq hξ R R' hR.1 hR'.1⟩

/-- **Next-block uniqueness of receiving models from forcing donors**: forcing donors at every
countable block index give next-block uniqueness of receiving models.  (R1) is not used. -/
theorem ReceivingNextBlockUniqueness.of_forcingDonors (hF : ∀ ξ < ω₁, ForcingDonors.{0} ξ) :
    ReceivingNextBlockUniqueness.{w} :=
  ⟨fun hξ _ _ hR hR' ↦ hR.eq_of_reduce_eq_of_forcingDonors (hF _ hξ) hR'⟩

/-- **Back to models under (R1)**: next-block uniqueness of receiving models and (R1) give
next-block uniqueness of models, since under (R1) every model at `λ_{ξ+1}` receives. -/
theorem ReceivingNextBlockUniqueness.nextBlockUniqueness (hu : ReceivingNextBlockUniqueness.{w})
    (hrec : FiniteCutReceiving.{w}) : NextBlockUniqueness.{w} :=
  ⟨fun hξ R R' hR hR' ↦
    have hα := isSuccLimit_blockStage (_ + 1)
    have hαω := blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hξ)
    hu.eq_of_reduce_eq hξ R R' ⟨hR, hrec.receive hα hαω R hR⟩ ⟨hR', hrec.receive hα hαω R' hR'⟩⟩

end Expansion

/-! ### Uniqueness of receiving models -/

namespace Realization

/-- **Uniqueness of receiving models**, given next-block uniqueness of receiving models: two
receiving models at `λ_ξ`, `ξ < ω₁`, on one carrier, with the same reduction to `λ_0` are equal.
By induction on `ξ`: at `0` the reduction to `λ_0` is the identity; at a successor the reductions
to `λ_ξ` are receiving models (`IsReceivingModel.reduce`), equal by the induction hypothesis; at a
limit the reductions to the earlier block stages are equal, and separation applies
(`eq_of_forall_reduce_eq`). -/
theorem IsReceivingModel.eq_of_reduce_zero_eq (hu : Expansion.ReceivingNextBlockUniqueness.{w})
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁) {M : Type w} {R R' : Realization.{0, w} (blockStage ξ) M}
    (hR : R.IsReceivingModel) (hR' : R'.IsReceivingModel)
    (h : R.reduce (isSuccPrelimit_blockStage 0) = R'.reduce (isSuccPrelimit_blockStage 0)) :
    R = R' := by
  induction ξ using Ordinal.limitRecOn with
  | zero => rwa [reduce_self, reduce_self] at h
  | add_one ξ ih =>
    have hξ' : ξ < ω₁ := (Order.lt_add_one_iff.mpr le_rfl).trans hξ
    have hle : blockStage ξ ≤ blockStage (ξ + 1) := blockStage_mono (Order.le_succ ξ)
    have h0 : blockStage 0 ≤ blockStage ξ := blockStage_mono zero_le
    refine hu.eq_of_reduce_eq hξ' R R' hR hR' (ih hξ'
      (hR.reduce (isSuccPrelimit_blockStage _) (isSuccLimit_blockStage ξ) hle)
      (hR'.reduce (isSuccPrelimit_blockStage _) (isSuccLimit_blockStage ξ) hle) ?_)
    rwa [reduce_reduce _ _ _ h0, reduce_reduce _ _ _ h0]
  | limit δ hδ ih =>
    refine eq_of_forall_reduce_eq hδ fun ζ hζ ↦ ?_
    have hle : blockStage ζ ≤ blockStage δ := blockStage_mono hζ.le
    have h0 : blockStage 0 ≤ blockStage ζ := blockStage_mono zero_le
    refine ih ζ hζ (hζ.trans hξ)
      (hR.reduce (isSuccPrelimit_blockStage _) (isSuccLimit_blockStage ζ) hle)
      (hR'.reduce (isSuccPrelimit_blockStage _) (isSuccLimit_blockStage ζ) hle) ?_
    rwa [reduce_reduce _ _ _ h0, reduce_reduce _ _ _ h0]

end Realization

section ModelExpansion

variable {M : Type w} [baseLanguage.{0}.Structure M]

/-- **Uniqueness of receiving model expansions**, given next-block uniqueness of receiving
models: two model expansions of `M` to `λ_ξ`, `ξ < ω₁`, with the finite-cut receiving property
are equal.  Their reductions to `λ_0 = ω` are expansions there, hence equal
(`ModelExpansion.instSubsingletonOmega`). -/
theorem ModelExpansion.eq_of_hasFiniteCutReceiving
    (hu : Expansion.ReceivingNextBlockUniqueness.{w}) {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    {e e' : ModelExpansion M (blockStage ξ)} (he : e.1.HasFiniteCutReceiving)
    (he' : e'.1.HasFiniteCutReceiving) : e = e' := by
  have : Subsingleton (ModelExpansion M (blockStage 0)) := by
    rw [blockStage_zero]
    infer_instance
  have h := congrArg Subtype.val
    (Subsingleton.elim (e.reduceBlock (zero_le : 0 ≤ ξ)) (e'.reduceBlock zero_le))
  rw [ModelExpansion.reduceBlock_val, ModelExpansion.reduceBlock_val] at h
  exact Subtype.ext (Realization.IsReceivingModel.eq_of_reduce_zero_eq hu hξ ⟨e.2.isModel, he⟩
    ⟨e'.2.isModel, he'⟩ h)

end ModelExpansion

/-! ### Continuation of receiving models -/

namespace Expansion

/-- **The continuation criterion for receiving models** on the carriers in the universe `w`: a
receiving model at `λ_ξ`, `ξ < ω₁`, that is not cover-hollow and has top-grade supremum `⊤` is the
stage reduction of a receiving model at `λ_{ξ+1}`.  The successor is required to receive, as well
as to be a model. -/
structure ReceivingContinuationCriterion : Prop where
  /-- A receiving model that is not cover-hollow and has unbounded top-grade growth is the
  reduction of a receiving model at the next block stage. -/
  exists_receivingModel ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) :
    ξ < ω₁ → R.IsReceivingModel → ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∃ R' : Realization.{0, w} (blockStage (ξ + 1)) M, R'.IsReceivingModel ∧
        R'.reduce (isSuccPrelimit_blockStage ξ) = R

/-- **(R4) for receiving models**: the statement of `StableCappedReceiving`, asked only of models
`R` that have the finite-cut receiving property. -/
structure ReceivingStableCappedReceiving : Prop where
  /-- Receiving of the stable candidate of a receiving model over positive roots, capped at every
  `γ < λ_{ξ+1}`. -/
  receive ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) :
    ξ < ω₁ → ∀ hR : R.IsModel, R.HasFiniteCutReceiving → ¬ R.IsCoverHollow →
      R.topGradeSup = ⊤ → ∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, 0 < x.arity →
        ∀ D ∈ x.type.cofaces, ∀ γ : Ordinal.{0}, γ < blockStage (ξ + 1) →
          ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
            ∃ Q, (R.stableCandidate hR.isStablyLawful).eval u = some Q ∧
              Q.toScheme = D.toScheme ∧ ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
                (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
                  (D.label j = ⊤ → (γ : Label.{0}) < Q.label i)

/-- (R4) gives its form for receiving models. -/
theorem StableCappedReceiving.receivingStableCappedReceiving (h : StableCappedReceiving.{w}) :
    ReceivingStableCappedReceiving.{w} :=
  ⟨fun _ _ R hξ hR _ ↦ h.receive R hξ hR⟩

end Expansion

namespace Realization

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **Finite-cut receiving of the candidate of a receiving model**, conditional on the receiving
form of (R4): over positive roots by that form at the cutoff `γ`, and over the empty root by the
amalgam over the empty face at `λ_{ξ+1}` (the argument of `hasFiniteCutReceiving_stableCandidate`,
with (R4) asked only of `R`). -/
theorem IsReceivingModel.hasFiniteCutReceiving_stableCandidate (hξ : ξ < ω₁)
    (hR : R.IsReceivingModel) (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    (hR4 : Expansion.ReceivingStableCappedReceiving.{w})
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    (R.stableCandidate hR.1.isStablyLawful).HasFiniteCutReceiving := by
  refine hasFiniteCutReceiving_of_pos hR.1.nonempty
    (hasLegalTypes_stableCandidate hR.1.hasLegalTypes)
    (isConsistent_stableCandidate hR.1.isConsistent hR.1.isCovering)
    (isCovering_stableCandidate hR.1.isCovering) hinst.exists_amalgam_empty
    fun x hx D hD c hc ↦ ?_
  induction c using Label.recBotCoeTop with
  | bot => exact absurd hc not_isPermittedCutoff_bot
  | top => exact absurd hc not_isPermittedCutoff_top
  | coe γ =>
    obtain ⟨u, hu, Q, hQ, hS, hl⟩ :=
      hR4.receive R hξ hR.1 hR.2 hnh hgrow x hx D hD γ (isPermittedCutoff_coe.mp hc)
    exact ⟨u, hu, Q, mem_receivingFamily_of_capped hS hl, hQ⟩

/-- **The candidate of a receiving model is a receiving model**, conditional on the receiving form
of (R4) and the coface instances at `λ_{ξ+1}`. -/
theorem IsReceivingModel.isReceivingModel_stableCandidate (hξ : ξ < ω₁)
    (hR : R.IsReceivingModel) (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    (hR4 : Expansion.ReceivingStableCappedReceiving.{w})
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    (R.stableCandidate hR.1.isStablyLawful).IsReceivingModel :=
  have hrec := hR.hasFiniteCutReceiving_stableCandidate hξ hnh hgrow hR4 hinst
  ⟨isModel_stableCandidate_of_hasFiniteCutReceiving hR.1 hinst hrec, hrec⟩

end Realization

namespace Expansion

/-- **The continuation criterion for receiving models from the receiving form of (R4)** and the
coface instances at every `λ_{ξ+1}` with `ξ < ω₁`: the successor is the stable candidate, a
receiving model reducing to the given one. -/
theorem ReceivingContinuationCriterion.of_receivingStableCappedReceiving
    (hR4 : ReceivingStableCappedReceiving.{w})
    (hinst : ∀ ξ < ω₁, StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    ReceivingContinuationCriterion.{w} :=
  ⟨fun _ _ _ hξ hR hnh hgrow ↦
    ⟨_, hR.isReceivingModel_stableCandidate hξ hnh hgrow hR4 (hinst _ hξ),
      Realization.stableCandidate_reduce⟩⟩

/-- **From the criterion for models, under (R1)**: the continuation criterion for models and (R1)
give the criterion for receiving models, since under (R1) the model successor receives. -/
theorem ReceivingContinuationCriterion.of_continuationCriterion
    (hcont : ContinuationCriterion.{w}) (hrec : FiniteCutReceiving.{w}) :
    ReceivingContinuationCriterion.{w} :=
  ⟨fun _ _ R hξ hR hnh hgrow ↦
    let ⟨R', hR', hred⟩ := hcont.exists_model R hξ hR.1 hnh hgrow
    ⟨R', ⟨hR', hrec.receive (isSuccLimit_blockStage _)
      (blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hξ)) R' hR'⟩, hred⟩⟩

end Expansion

/-! ### Terminality for receiving models -/

namespace Realization

section Terminal

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

variable (ξ R) in
/-- A realization `R` at `λ_ξ` is **receiving-terminal at `ξ`** when no receiving model at the
next block stage on the same carrier has `R` as its stage reduction to `λ_ξ`. -/
def IsReceivingTerminalAt : Prop :=
  ∀ R' : Realization.{u, v} (blockStage (ξ + 1)) M, R'.IsReceivingModel →
    R'.reduce (isSuccPrelimit_blockStage ξ) ≠ R

/-- A terminal realization is receiving-terminal: a receiving successor is a model successor. -/
theorem IsTerminalAt.isReceivingTerminalAt (h : R.IsTerminalAt ξ) : R.IsReceivingTerminalAt ξ :=
  fun R' hR' ↦ h R' hR'.1

/-- **Receiving-terminal is terminal when the model successors receive**: if every model at
`λ_{ξ+1}` reducing to `R` has the finite-cut receiving property, then `R` is receiving-terminal
exactly when it is terminal. -/
theorem isReceivingTerminalAt_iff_isTerminalAt
    (hfid : ∀ R' : Realization.{u, v} (blockStage (ξ + 1)) M, R'.IsModel →
      R'.reduce (isSuccPrelimit_blockStage ξ) = R → R'.HasFiniteCutReceiving) :
    R.IsReceivingTerminalAt ξ ↔ R.IsTerminalAt ξ :=
  ⟨fun h R' hR' hred ↦ h R' ⟨hR', hfid R' hR' hred⟩ hred, IsTerminalAt.isReceivingTerminalAt⟩

end Terminal

/-- Under (R1), receiving-terminal at a countable index is terminal. -/
theorem isReceivingTerminalAt_iff_isTerminalAt_of_finiteCutReceiving
    (hrec : Expansion.FiniteCutReceiving.{w}) {ξ : Ordinal.{0}} (hξ : ξ < ω₁) {M : Type w}
    {R : Realization.{0, w} (blockStage ξ) M} : R.IsReceivingTerminalAt ξ ↔ R.IsTerminalAt ξ :=
  isReceivingTerminalAt_iff_isTerminalAt fun R' hR' _ ↦ hrec.receive (isSuccLimit_blockStage _)
    (blockStage_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hξ)) R' hR'

/-- **Receiving-terminal receiving models with unbounded growth are cover-hollow**, under the
continuation criterion for receiving models: otherwise the criterion gives a receiving successor.
-/
theorem IsReceivingTerminalAt.isCoverHollow (hcont : Expansion.ReceivingContinuationCriterion.{w})
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁) {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}
    (ht : R.IsReceivingTerminalAt ξ) (hR : R.IsReceivingModel) (hgrow : R.topGradeSup = ⊤) :
    R.IsCoverHollow :=
  not_not.mp fun hnh ↦
    let ⟨R', hR', hred⟩ := hcont.exists_receivingModel R hξ hR hnh hgrow
    ht R' hR' hred

end Realization

end VaughtConjecture
