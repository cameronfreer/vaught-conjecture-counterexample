/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.ScottAnalysis
import VaughtConjecture.Continuation.Normalization
import VaughtConjecture.Expansion.ReceivingModels

/-!
# A receiving successor at `ω₁` separates two points after `ω₁`

Companion programme over the density sentence: the process rank `R(M) = sup_a orbitRank(a)` of a
base structure `M` with a receiving model expansion at the block stage `λ_{ω₁ + 1} = λ_{ω₁} + ω`
(a **receiving successor** of its reduction to `λ_{ω₁}`) exceeds `ω₁`.  Every statement here is
a given-model statement; all are proved, in
`VaughtConjecture.ProcessRank.SuccessorPair` (steps 1–3),
`VaughtConjecture.ProcessRank.SuccessorDetection`
(step 4) and `VaughtConjecture.ProcessRank.SuccessorRank` (steps 5–6).

Throughout, `Ω = ω₁` and `λ_Ω = blockStage ω₁`, an ordinal equal to `ω₁` (`blockStage_omegaOne`,
used in the proofs of step 4).  The hypothesis "receiving successor at `Ω + ω`" is written with the
repository's names in two equivalent forms:

* a model expansion `e : ModelExpansion M (blockStage (ω₁ + 1))` with
  `e.1.HasFiniteCutReceiving` (so `e.1.IsReceivingModel`);
* a model expansion `R : ModelExpansion M (blockStage ω₁)` with
  `¬ R.1.IsReceivingTerminalAt ω₁`: some receiving model at `λ_{ω₁ + 1}` reduces to `R.1`.

**The argument.**

1. *The pair* (`SuccessorOnePointPairTarget`).  At every block index `ξ`, in a receiving model at
   `λ_{ξ+1}`, the one-point apex type capped at `λ_ξ + i` and at `λ_ξ + j`, `0 < i < j`, are legal
   top-free one-point types with one scheme and equal reductions to `λ_ξ`; exact receiving of the
   legal top-free types over the empty tuple realizes both
   (`Realization.IsReceivingModel.exists_covers_onePoint`, `onePointPairTarget`).
2. *Agreement through `Ω`* (`SuccessorPairAgreementTarget`).  Covers in `e` of two types with
   equal reductions to `λ_Ω` cover one type in every countable reduction `e↓λ_η`, a receiving model
   expansion, so they are back-and-forth equivalent at every `η < ω₁`
   (`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`), hence at the limit `ω₁`.
3. *A rooted-cover distinction at `λ_ξ`* (`SuccessorThresholdSeparationTarget`).  By the threshold
   lemma `Realization.le_label_iff_exists_forcesThreshold` (finite-extension receiving from
   receiving; forcing donors at every block index), if the label of a cell of `t₁` at `c₁` is below
   `λ_ξ + n` and the label of the same cell of `t₂` at `c₂` is at least `λ_ξ + n`, then some rooted
   cover forcing `n` at the common root extends `c₂` in `R↓λ_ξ`, and none extends `c₁`.  The
   distinction is a property of the **reduction** `R↓λ_ξ`, not of the successor expansion.
4. *Stage-`Ω` charts in the base language* (`StageOmegaOneCoversDefinableTarget`,
   `StageOmegaOneCoversBFEquivTarget`, `StageOmegaOneExtendsToCoverBFEquivTarget`).  In a receiving
   model expansion at `λ_Ω`, a tuple covers a stage type exactly when, at every `η < ω₁`, it
   satisfies the block formula of the forcing thresholds of its reduction to `λ_η` (the
   conjunction over `η < ω₁` is an `L_{∞,ω}` formula of the base language; it is used here only
   through its semantics).  Each block formula has rank at most `ω · η < ω₁`, so covers at `λ_Ω`
   are preserved by back-and-forth equivalence at level `ω₁`, and extension to a rooted cover on
   `m` points by back-and-forth equivalence at level `ω₁ + m`.  No formula constructor of
   countable rank is applied at the stage `ω₁` itself.
5. *Separation after `Ω`* (`SuccessorSeparatedPairTarget`).  With `ξ = ω₁`, `i = 1`, `j = 2`, the
   points of step 1 agree at `ω₁` (step 2); a rooted cover forcing `2` extends the second point at
   `λ_Ω` and none extends the first (step 3); equivalence at `ω₁ + m`, `m` the size of that rooted
   cover, would carry it to the first point (step 4).  So the pair is separated at `ω₁ + m` in the
   base language.
6. *The ranks* (`SuccessorOrbitRankGtTarget`, `ReceivingNotTerminalOrbitRankGtTarget`,
   `SuccessorProcessRankGtTarget`).  The orbit rank of the first point exceeds `ω₁`, so
   `R(M) > ω₁`, and the semantic Scott process of `M` has no rank `β ≤ ω₁`
   (`InfinitaryLogic.ScottProcess.Semantic.isRank_iff_lift_eq_iSup_orbitRank`).

## References

Receiving models and the stable labels are those of [Kni26, §4]; the stage reduction and the
block stages are those of [AFK26].
-/

universe u v w

namespace VaughtConjecture.ProcessRank

open Ordinal Order FirstOrder Language InfinitaryLogic.ScottProcess.Semantic

/-! ### Step 1: the pair -/

/-- **Target: a one-point pair in the next block.**  In a receiving model at `λ_{ξ+1}`, for
`0 < i < j`, two legal top-free stage types on one point with one scheme, labelled `λ_ξ + i` and
`λ_ξ + j`, with equal reductions to `λ_ξ`, are the types of points `a₁` and `a₂`.  No bound on
`ξ`.  Given-model statement.  Proved (`successorOnePointPairTarget`). -/
def SuccessorOnePointPairTarget : Prop :=
  ∀ ⦃ξ : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} (blockStage (ξ + 1)) M),
    R.IsReceivingModel → ∀ ⦃i j : ℕ⦄, 0 < i → i < j →
      ∃ d₁ d₂ : StageType.{u} (blockStage (ξ + 1)) 1, d₁.IsLegal ∧ d₂.IsLegal ∧
        d₁.IsTopFree ∧ d₂.IsTopFree ∧ d₁.toScheme = d₂.toScheme ∧
        (∀ x, d₁.label x = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})) ∧
        (∀ x, d₂.label x = ((blockStage ξ + j : Ordinal.{u}) : Label.{u})) ∧
        d₁.reduce (isSuccPrelimit_blockStage ξ) = d₂.reduce (isSuccPrelimit_blockStage ξ) ∧
        ∃ a₁ a₂ : M, R.Covers d₁ ![a₁] ∧ R.Covers d₂ ![a₂]

/-! ### Step 2: agreement through `ω₁` -/

/-- **Target: agreement through `ω₁`.**  In a receiving model expansion `e` at `λ_{ω₁ + 1}`,
covers `c₁` and `c₂` of two stage types with equal reductions to `λ_{ω₁}` are back-and-forth
equivalent at level `ω₁` in the base language.  Given-model statement.
Proved (`successorPairAgreementTarget`). -/
def SuccessorPairAgreementTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (e : ModelExpansion M (blockStage (ω₁ + 1))),
    e.1.HasFiniteCutReceiving → ∀ ⦃k : ℕ⦄ ⦃t₁ t₂ : StageType.{0} (blockStage (ω₁ + 1)) k⦄
      ⦃c₁ c₂ : Fin k → M⦄,
      t₁.reduce (isSuccPrelimit_blockStage ω₁) = t₂.reduce (isSuccPrelimit_blockStage ω₁) →
        e.1.Covers t₁ c₁ → e.1.Covers t₂ c₂ →
          BFEquiv (L := baseLanguage.{0}) (ω₁ : Ordinal.{0}) k c₁ c₂

/-! ### Step 3: a rooted-cover distinction at `λ_ξ` -/

/-- **Target: the threshold lemma separates two covers at the reduction.**  In a receiving model
`R` at `λ_{ξ+1}`, let `c₁` and `c₂` cover `t₁` and `t₂`, with equal reductions to `λ_ξ`, and let
`d₁`, `d₂` be cells at one position, `d₁` reducing to the formal top.  If the label at `d₁` is
below `λ_ξ + n` and the label at `d₂` is at least `λ_ξ + n`, then some rooted cover forcing `n`
at `d₁` over the common root `t₁↓λ_ξ` extends `c₂` in `R↓λ_ξ`, and none extends `c₁`.  The
predicate separating `c₂` from `c₁` reads `R` only through `R↓λ_ξ`.  No bound on `ξ`.
Given-model statement.  Proved (`successorThresholdSeparationTarget`). -/
def SuccessorThresholdSeparationTarget : Prop :=
  ∀ ⦃ξ : Ordinal.{u}⦄ ⦃M : Type v⦄ (R : Realization.{u, v} (blockStage (ξ + 1)) M),
    R.IsReceivingModel → ∀ ⦃k : ℕ⦄ ⦃t₁ t₂ : StageType.{u} (blockStage (ξ + 1)) k⦄
      ⦃c₁ c₂ : Fin k → M⦄, R.Covers t₁ c₁ → R.Covers t₂ c₂ →
      t₁.reduce (isSuccPrelimit_blockStage ξ) = t₂.reduce (isSuccPrelimit_blockStage ξ) →
      ∀ (d₁ : Fin t₁.card) (d₂ : Fin t₂.card), (d₁ : ℕ) = d₂ →
        (t₁.reduce (isSuccPrelimit_blockStage ξ)).label d₁ = ⊤ → ∀ n : ℕ,
          t₁.label d₁ < ((blockStage ξ + n : Ordinal.{u}) : Label.{u}) →
          ((blockStage ξ + n : Ordinal.{u}) : Label.{u}) ≤ t₂.label d₂ →
            (∃ x : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin k ↪ Fin m),
              StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ)
                x.2.1 x.2.2 (t₁.reduce (isSuccPrelimit_blockStage ξ)) d₁ n ∧
              (R.reduce (isSuccPrelimit_blockStage ξ)).ExtendsToCover c₂ x) ∧
            ¬ ∃ x : Σ m : ℕ, StageType.{u} (blockStage ξ) m × (Fin k ↪ Fin m),
              StageType.ForcesThreshold (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ)
                x.2.1 x.2.2 (t₁.reduce (isSuccPrelimit_blockStage ξ)) d₁ n ∧
              (R.reduce (isSuccPrelimit_blockStage ξ)).ExtendsToCover c₁ x

/-! ### Step 4: stage-`ω₁` charts in the base language -/

/-- **Target: the charts at `λ_{ω₁}` are the conjunctions of the countable block formulas.**  In a
receiving model expansion `R` at `λ_{ω₁}`, a tuple `c` covers a stage type `t` exactly when, at
every `η < ω₁`, it satisfies the block formula of the forcing thresholds of the reduction of `t`
to `λ_η`.  Given-model statement.  Proved (`stageOmegaOneCoversDefinableTarget`). -/
def StageOmegaOneCoversDefinableTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage ω₁)),
    R.1.IsReceivingModel → ∀ ⦃k : ℕ⦄ (t : StageType.{0} (blockStage ω₁) k) (c : Fin k → M),
      R.1.Covers t c ↔ ∀ η (hη : η < ω₁),
        (blockFormula forcingThresholds η hη (t.reduce (isSuccPrelimit_blockStage η))).Realize c

/-- **Target: covers at `λ_{ω₁}` are invariant under equivalence at `ω₁`.**  In a receiving model
expansion `R` at `λ_{ω₁}`, a tuple back-and-forth equivalent at level `ω₁` in the base language to
a cover of `t` covers `t`.  Given-model statement.  Proved (`stageOmegaOneCoversBFEquivTarget`). -/
def StageOmegaOneCoversBFEquivTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage ω₁)),
    R.1.IsReceivingModel → ∀ ⦃k : ℕ⦄ (t : StageType.{0} (blockStage ω₁) k) (c c' : Fin k → M),
      BFEquiv (L := baseLanguage.{0}) (ω₁ : Ordinal.{0}) k c c' → R.1.Covers t c → R.1.Covers t c'

/-- **Target: rooted covers at `λ_{ω₁}` are invariant under equivalence at `ω₁ + m`.**  In a
receiving model expansion `R` at `λ_{ω₁}`, if `c` extends to a cover of a triple `(m, q, f)` and
`c'` is back-and-forth equivalent to `c` at level `ω₁ + m` in the base language, then `c'`
extends to a cover of the same triple.  Given-model statement.
Proved (`stageOmegaOneExtendsToCoverBFEquivTarget`). -/
def StageOmegaOneExtendsToCoverBFEquivTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage ω₁)),
    R.1.IsReceivingModel → ∀ ⦃k : ℕ⦄
      (x : Σ m : ℕ, StageType.{0} (blockStage ω₁) m × (Fin k ↪ Fin m)) (c c' : Fin k → M),
      BFEquiv (L := baseLanguage.{0}) ((ω₁ : Ordinal.{0}) + x.1) k c c' →
        R.1.ExtendsToCover c x → R.1.ExtendsToCover c' x

/-! ### Steps 5 and 6: separation after `ω₁`, and the ranks -/

/-- **Target: a receiving successor at `ω₁` separates two points after `ω₁`.**  If the base
structure `M` has a receiving model expansion `e` at `λ_{ω₁ + 1}`, some two points of `M` are
back-and-forth equivalent at level `ω₁` and not at some level `ω₁ + m`, `m : ℕ`, both in the base
language.  Given-model statement.  Proved (`successorSeparatedPairTarget`). -/
def SuccessorSeparatedPairTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (e : ModelExpansion M (blockStage (ω₁ + 1))),
    e.1.HasFiniteCutReceiving → ∃ a₁ a₂ : M,
      BFEquiv (L := baseLanguage.{0}) (ω₁ : Ordinal.{0}) 1 ![a₁] ![a₂] ∧
        ∃ m : ℕ, ¬ BFEquiv (L := baseLanguage.{0}) ((ω₁ : Ordinal.{0}) + m) 1 ![a₁] ![a₂]

/-- **Target: a receiving successor at `ω₁` gives an orbit rank above `ω₁`.**  If `M` has a
receiving model expansion at `λ_{ω₁ + 1}`, some tuple of `M` has orbit rank above `ω₁`, lifted
to the carrier universe.  Given-model statement.  Proved (`successorOrbitRankGtTarget`). -/
def SuccessorOrbitRankGtTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (e : ModelExpansion M (blockStage (ω₁ + 1))),
    e.1.HasFiniteCutReceiving → ∃ (n : ℕ) (a : Fin n → M),
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) < orbitRank (L := baseLanguage.{0}) a

/-- **Target: a model expansion at `λ_{ω₁}` that is not receiving-terminal gives an orbit rank
above `ω₁`.**  For a model expansion `R` of `M` at `λ_{ω₁}` such that some receiving model at
`λ_{ω₁ + 1}` reduces to `R.1` (`¬ R.1.IsReceivingTerminalAt ω₁`), some tuple of `M` has orbit
rank above `ω₁`.  Given-model statement.  Proved (`receivingNotTerminalOrbitRankGtTarget`). -/
def ReceivingNotTerminalOrbitRankGtTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M (blockStage ω₁)),
    ¬ R.1.IsReceivingTerminalAt ω₁ → ∃ (n : ℕ) (a : Fin n → M),
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) < orbitRank (L := baseLanguage.{0}) a

/-- **Target: a receiving successor at `ω₁` gives process rank above `ω₁`.**  If an infinite `M`
has a receiving model expansion at `λ_{ω₁ + 1}`, no initial segment of the semantic Scott process
of `M` has rank at most `ω₁` (the rank, lifted, is `sup_a orbitRank(a)` when it exists).
Given-model statement.  Proved (`successorProcessRankGtTarget`). -/
def SuccessorProcessRankGtTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] [Infinite M]
    (e : ModelExpansion M (blockStage (ω₁ + 1))), e.1.HasFiniteCutReceiving →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ) ⦃β : Ordinal.{0}⦄, β ≤ ω₁ →
        ¬ (scottProcessOf baseLanguage.{0} M δ hδ).IsRank β

end VaughtConjecture.ProcessRank
