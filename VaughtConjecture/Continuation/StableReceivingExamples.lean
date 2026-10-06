/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableReceiving

/-!
# Examples: (R4) at one occurrence

Special cases of `VaughtConjecture.Continuation.StableReceiving`, each conditional only where
stated:

* **The first block** `ξ = 0`: (R4) at an occurrence of the candidate of a realization at
  `λ_0 = ω` is exact receiving in `R` of the reduction of the donor to `ω` together with the
  calibration of the stable labels, read at the requested ordinal `ω + K`.
* **Donors below the block**: a coface of the type of `x` all of whose labels lie below `λ_ξ` has
  no cell reducing to the top, so finite-cut receiving of `R` receives it exactly in the candidate.
* **Donors whose top cells are old**: (R4) holds at every `γ`, from finite-cut receiving of `R`.
* **Models with a model expansion**: (R4) at every occurrence, from finite-cut receiving of the
  expansion and forcing donors at `0`; non-hollowness and unbounded growth are not used.
* **Cover-hollowness and bounded stable labels**: (R4) fails at one donor with a label in the new
  block, and at one donor with a top cell at `γ = λ_ξ + K`.
* **The evaluation step**: a stable recovery scheme over an occurrence containing `x` gives (R4)
  at `x`.
* **The marker and cap calibration**: acquired in every model that is not cover-hollow and has
  top-grade supremum `⊤`; with stable recovery schemes for it (false at every `ξ`) it gives (R4) at
  every occurrence of positive arity.
-/

namespace VaughtConjecture.Continuation.StableReceivingExamples

open Ordinal Realization StageType

variable {M : Type} {ξ : Ordinal.{0}} {R : Realization.{0, 0} (blockStage ξ) M}
  {hlaw : R.IsStablyLawful} {x : (R.stableCandidate hlaw).Occurrence}
  {D : StageType.{0} (blockStage (ξ + 1)) (x.arity + 1)}

/-! ### The first block -/

/-- At the first block, (R4) at `γ = ω + K` is exact receiving in `R` of the reduction of the
donor to `ω` and the calibration of the stable labels at the cells where that reduction is the
formal top. -/
example {R : Realization.{0, 0} (blockStage 0) M} {hlaw : R.IsStablyLawful}
    {x : (R.stableCandidate hlaw).Occurrence} {D : StageType.{0} (blockStage (0 + 1)) (x.arity + 1)}
    (K : ℕ) :
    R.StablyReceivesAt hlaw x D (blockStage 0 + K) ↔
      ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
        R.eval u = some (D.reduce (isSuccPrelimit_blockStage 0)) ∧
        ∀ d : Fin D.card, (D.reduce (isSuccPrelimit_blockStage 0)).label d = ⊤ →
          (D.label d ≠ ⊤ → R.stableLabel (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) u
              (D.reduce (isSuccPrelimit_blockStage 0)) d = D.label d) ∧
          (D.label d = ⊤ → ((blockStage 0 + K : Ordinal.{0}) : Label.{0}) <
            R.stableLabel (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) u
              (D.reduce (isSuccPrelimit_blockStage 0)) d) :=
  stablyReceivesAt_iff le_self_add

/-- (R4) at every `γ` below the next block stage is (R4) at every `λ_ξ + K`. -/
example : (∀ γ < blockStage (ξ + 1), R.StablyReceivesAt hlaw x D γ) ↔
    ∀ K : ℕ, R.StablyReceivesAt hlaw x D (blockStage ξ + K) :=
  forall_lt_stablyReceivesAt_iff

/-! ### Donors below the block and donors whose top cells are old -/

/-- **Donors below the block**: in an exactly consistent covering realization with finite-cut
receiving, a coface of the type of `x` all of whose labels lie below `λ_ξ` is received exactly in
the candidate. -/
example (hR : R.IsConsistent) (hc : R.IsCovering) (hrec : R.HasFiniteCutReceiving)
    (hD : D ∈ x.type.cofaces) (hlt : ∀ d, D.label d < (blockStage ξ : Label.{0})) :
    ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
      (R.stableCandidate hlaw).eval u = some D :=
  exists_stableCandidate_eval_eq_of_hasFiniteCutReceiving hR hc hrec hD fun d hd ↦ absurd hd
    (by rw [reduce_label, Label.reduce_of_lt (hlt d)]; exact (hlt d).ne_top)

/-- **Donors whose top cells are old**: (R4) holds at every `γ`, conditional on finite-cut
receiving of `R`. -/
example (hR : R.IsConsistent) (hc : R.IsCovering) (hrec : R.HasFiniteCutReceiving)
    (hD : D ∈ x.type.cofaces)
    (hnew : ∀ d : Fin D.card, (D.reduce (isSuccPrelimit_blockStage ξ)).label d = ⊤ →
      d ∈ D.toScheme.visibleCells Fin.castSuccEmb) (γ : Ordinal.{0}) :
    R.StablyReceivesAt hlaw x D γ := by
  obtain ⟨u, hu, hQ⟩ := exists_stableCandidate_eval_eq_of_hasFiniteCutReceiving hR hc hrec hD hnew
  refine ⟨u, hu, D, hQ, rfl, fun i j hij ↦ ?_⟩
  obtain rfl : i = j := Fin.ext hij
  exact ⟨fun _ ↦ rfl, fun h ↦ h ▸ WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top γ)⟩

/-! ### Models with a model expansion -/

/-- **(R4) at a model with a model expansion**, at the first block, conditional on forcing donors
at `0`: if `R` is the reduction of an exactly consistent realization at `ω + ω` with legal types
and finite-cut receiving, (R4) holds at every occurrence of the candidate, every coface and every
`γ < ω + ω`. -/
example (hF : ForcingDonors.{0} 0) {R : Realization.{0, 0} (blockStage 0) M}
    {hlaw : R.IsStablyLawful} {R' : Realization.{0, 0} (blockStage (0 + 1)) M}
    (hR' : R'.IsConsistent) (hl' : R'.HasLegalTypes) (hrec' : R'.HasFiniteCutReceiving)
    (h : R'.reduce (isSuccPrelimit_blockStage 0) = R) (x : (R.stableCandidate hlaw).Occurrence)
    (D : StageType.{0} (blockStage (0 + 1)) (x.arity + 1)) (hD : D ∈ x.type.cofaces)
    (γ : Ordinal.{0}) (hγ : γ < ω + ω) : R.StablyReceivesAt hlaw x D γ :=
  stablyReceivesAt_of_reduce_eq hF hR' hl' hrec' h hD
    (by rwa [blockStage_add_one, blockStage_zero])

/-! ### Where non-hollowness and unbounded growth are used -/

/-- **Cover-hollow realizations**: (R4) fails at every donor with a label `λ_ξ + i`. -/
example (hh : R.IsCoverHollow) {j : Fin D.card} {i : ℕ}
    (hj : D.label j = ((blockStage ξ + i : Ordinal.{0}) : Label.{0})) (γ : Ordinal.{0}) :
    ¬ R.StablyReceivesAt hlaw x D γ :=
  not_stablyReceivesAt_of_isCoverHollow hh hj γ

/-- **Bounded stable labels**: (R4) fails at `γ = λ_ξ + K` at every donor with a top cell. -/
example {K : ℕ}
    (hK : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{0} (blockStage ξ) n), R.eval u = some t →
      ∀ d, t.label d = ⊤ → R.stableLabel (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t d ≤
        ((blockStage ξ + K : Ordinal.{0}) : Label.{0}))
    {j : Fin D.card} (hj : D.label j = ⊤) : ¬ R.StablyReceivesAt hlaw x D (blockStage ξ + K) :=
  not_stablyReceivesAt_of_stableLabel_le hK hj

/-! ### The evaluation step -/

/-- **The evaluation step**: in a model, a stable recovery scheme for the stable type of an
occurrence `w` containing `x` gives (R4) at `x`. -/
example (hR : R.IsModel) (w : R.Occurrence) {f : Fin x.arity ↪ Fin w.arity}
    (hf : f.trans w.tuple = x.tuple) {γ : Ordinal.{0}} {E : Scheme.{0} (w.arity + 1)}
    (hE : (R.stableType hlaw w.tuple w.type w.eval_tuple).IsStableRecoveryScheme f D γ E) :
    R.StablyReceivesAt hlaw x D γ :=
  stablyReceivesAt_of_isStableRecoveryScheme hR w hf hE

/-! ### The marker and cap calibration -/

/-- In a model that is not cover-hollow and has unbounded growth, over every occurrence of the
candidate of positive arity, an occurrence containing it has a stable type with a cell labelled
`λ_ξ + i` and a cell labelled at least `λ_ξ` and above any requested `γ < λ_{ξ+1}`. -/
example (hR : R.IsModel) (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) :
    AcquiresCalibratedContexts ξ (MarkerCapCalibration ξ) R hR.isStablyLawful :=
  hR.acquiresCalibratedContexts_markerCap hnh hgrow

/-- With stable recovery schemes for the marker and cap calibration at `ξ` (a hypothesis that is
false, `Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`), (R4)
holds at every occurrence of positive arity of the candidate of such a model. -/
example (hR : R.IsModel) (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤)
    (hS : HasStableRecoverySchemes ξ (MarkerCapCalibration ξ))
    (x : (R.stableCandidate hR.isStablyLawful).Occurrence) (hx : 0 < x.arity)
    (D : StageType.{0} (blockStage (ξ + 1)) (x.arity + 1)) (hD : D ∈ x.type.cofaces)
    (γ : Ordinal.{0}) (hγ : γ < blockStage (ξ + 1)) :
    R.StablyReceivesAt hR.isStablyLawful x D γ :=
  stablyReceivesAt_of_acquiresCalibratedContexts hR hS
    (hR.acquiresCalibratedContexts_markerCap hnh hgrow) x hx D hD γ hγ

end VaughtConjecture.Continuation.StableReceivingExamples
