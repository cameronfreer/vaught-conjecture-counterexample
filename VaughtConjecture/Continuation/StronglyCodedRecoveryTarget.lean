/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.CutoffStableRecovery
import VaughtConjecture.Realization.ReceivingInClass

/-!
# Strongly coded cutoff stable recovery, and its evaluation without modelhood

Roadmap, Layer 3 ((R4), the evaluation step) and Layer 4 (higher-stage reconstruction);
Correspondence, item 1 (the strongly coded legal stage types).  All results here are native
constructions of this repository.

The evaluation step of (R4) through stable recovery schemes
(`Realization.stablyReceivesAt_of_isStableRecoveryScheme`) realizes the recovery scheme by
generalized saturation (`hR.saturation`), with no restriction on the scheme.  Its cutoff form
(`Realization.stablyReceivesAt_of_isCutoffStableRecovery`) realizes the carrier `q` of cutoff stable
recovery by finite-cut receiving instead, still for every coface.  Receiving restricted to the
strongly coded stage types (`Realization.HasFiniteCutReceivingIn`, with
`fun t ↦ t.rows.IsStronglyCoded`) can replace that call only for a strongly coded carrier `q`.

**The finite target** (`StageType.HasStronglyCodedCutoffStableRecovery ξ`, a named statement;
**open**).  For a strongly coded legal context `T⁺` at `λ_{ξ+1}`, an embedding `f` of `k > 0`
points with face `P`, a strongly coded coface `D` of `P`, `γ < λ_{ξ+1}` and the margin calibration
(`StageType.GradedCapMarginCalibration`), it asks for a **strongly coded** carrier `(q, δ)` of
cutoff stable recovery (`StageType.IsCutoffStableRecovery`, unchanged: literal faces, and recovery
for every stage type whose reduction lies in the receiving family of `q` at `δ`).  The binders are
those of `StageType.HasCutoffStableRecoverySchemes` for the margin calibration, with strong coding
added to `T⁺`, `D` and `q`.

**The existing construction does not give it.**  The compiled carrier for the margin calibration is
the ladder carrier (`StageType.HasLadderGrowthCarriersStable.hasStableGrowthCarriers`, from
`StageType.hasLadderGrowthCarriersStableAtSeed_levels`), and its carrier `q` lies on the carrier
scheme (`GrowthCarrier.isStableRecoveryScheme`).  Its first construction that is not strongly coded
is the padded grade-one base (`Scheme.LadderBaseData.not_isStronglyCoded_ladderBase`, in
`VaughtConjecture.MainTheorem.LevelCarrierCoding`): at the height of the seed choice the second
rung is present, and its diagonal `ω + 3` exceeds the grade-one bound `2`.

**Evaluation without modelhood**
(`Realization.stablyReceivesAt_of_isCutoffStableRecovery_of_isStronglyCoded`,
`Realization.stablyReceivesAt_of_hasStronglyCodedCutoffStableRecovery`).  From exact consistency,
covering, stable lawfulness (`Realization.isStablyLawful_of_hasLegalTypes`) and finite-cut receiving
for the strongly coded cofaces, a strongly coded carrier of cutoff stable recovery at a context
containing `x` gives (R4) at `(x, D, γ)`.  The second form takes the finite target as a hypothesis;
it is an assumption, not evidence that the finite construction is solved.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label StageType
open Ordinal hiding univ

namespace StageType

variable (ξ : Ordinal.{u})

/-- **Strongly coded cutoff stable recovery for the margin calibration** (a named statement;
open).  For every strongly coded legal `T⁺` at `λ_{ξ+1}` on `m` points, embedding `f` of `k > 0`
points with face `P`, coface `D` of `P` with strongly coded rows, and `γ < λ_{ξ+1}` with the margin
calibration `StageType.GradedCapMarginCalibration ξ T⁺ f D γ`, there is a carrier `(q, δ)` of cutoff
stable recovery (`StageType.IsCutoffStableRecovery`) with `q` strongly coded.  The recovery
contract is unchanged: literal faces, and recovery for every stage type whose reduction lies in the
receiving family of `q` at `δ`.  The existing ladder carrier does not give it
(`Scheme.LadderBaseData.not_isStronglyCoded_ladderBase`). -/
def HasStronglyCodedCutoffStableRecovery : Prop :=
  ∀ ⦃m k : ℕ⦄ (Tp : StageType.{u} (blockStage (ξ + 1)) m) (f : Fin k ↪ Fin m)
    (P : StageType.{u} (blockStage (ξ + 1)) k), Tp.IsStronglyCodedLegal → 0 < k →
    restrictFace f Tp = some P → ∀ D ∈ P.cofaces, D.rows.IsStronglyCoded →
      ∀ γ : Ordinal.{u}, γ < blockStage (ξ + 1) → GradedCapMarginCalibration ξ Tp f D γ →
        ∃ (q : StageType.{u} (blockStage ξ) (m + 1)) (δ : Label.{u}),
          q.rows.IsStronglyCoded ∧ Tp.IsCutoffStableRecovery f D γ q δ

end StageType

namespace Realization

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-! ### Evaluation without modelhood -/

/-- **Evaluation without modelhood at a strongly coded carrier** (native construction): for an
exactly consistent covering realization `R` with finite-cut receiving for the strongly coded
cofaces, if an occurrence `w` of `R` contains the tuple of `x` along `f` and `(q, δ)` carries cutoff
stable recovery for the stable type of `w`, `f`, `D` and `γ` **with `q` strongly coded**, then (R4)
holds at `(x, D, γ)`.  As `Realization.stablyReceivesAt_of_isCutoffStableRecovery`, with modelhood
replaced by consistency and covering and the receiving restricted to the strongly coded class.  The
strongly coded carrier is a hypothesis (`hqs`, `hq`). -/
theorem stablyReceivesAt_of_isCutoffStableRecovery_of_isStronglyCoded {hlaw : R.IsStablyLawful}
    {x : (R.stableCandidate hlaw).Occurrence} {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)}
    {γ : Ordinal.{u}} (hR : R.IsConsistent) (hc : R.IsCovering)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded) (w : R.Occurrence)
    {f : Fin x.arity ↪ Fin w.arity} (hf : f.trans w.tuple = x.tuple)
    {q : StageType.{u} (blockStage ξ) (w.arity + 1)} {δ : Label.{u}} (hqs : q.rows.IsStronglyCoded)
    (hq : (R.stableType hlaw w.tuple w.type w.eval_tuple).IsCutoffStableRecovery f D γ q δ) :
    R.StablyReceivesAt hlaw x D γ := by
  obtain ⟨hqc, hδ, hrecov⟩ := hq
  rw [reduce_stableType] at hqc
  obtain ⟨v, hv, q', hq', hvq⟩ := hrec w q hqc hqs δ hδ
  have hcons := isConsistent_stableCandidate (hlaw := hlaw) hR hc
  have hQ'v := stableCandidate_eval_of_eval (hlaw := hlaw) hvq
  have hface : restrictFace Fin.castSuccEmb (R.stableType hlaw v q' hvq) =
      some (R.stableType hlaw w.tuple w.type w.eval_tuple) := by
    rw [← hcons v _ Fin.castSuccEmb hQ'v, hv]
    exact stableCandidate_eval_of_eval w.eval_tuple
  obtain ⟨Q, hQ, hS, hl⟩ := hrecov (R.stableType hlaw v q' hvq)
    (by rw [reduce_stableType]; exact hq') hface
  refine ⟨(extendByLast f).trans v, ?_, Q, ?_, hS, hl⟩
  · rw [← hf, ← hv, ← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
      Function.Embedding.trans_assoc]
  · rw [hcons v _ _ hQ'v, hQ]

/-- **Evaluation without modelhood from the strongly coded finite target** (native construction;
the target is **assumed**).  Let `R` be exactly consistent and covering, with legal types (so
stably lawful, `Realization.isStablyLawful_of_hasLegalTypes`), with strongly coded types (`hsc`),
and with finite-cut receiving for the strongly coded cofaces (`hrec`).  Let `x` be an occurrence of
the candidate of positive arity, `D` a strongly coded coface of its type, `γ < λ_{ξ+1}`, and `w` an
occurrence of `R` containing the tuple of `x` along `f` whose stable type satisfies the margin
calibration for `f`, `D` and `γ`.  Then **assuming** the finite target
`StageType.HasStronglyCodedCutoffStableRecovery ξ` (`hS`), (R4) holds at `(x, D, γ)`.  The target is
a hypothesis here, not evidence that the finite construction is solved: it is open, and the
existing ladder carrier does not give it (`Scheme.LadderBaseData.not_isStronglyCoded_ladderBase`).
The calibrated context `w` is also a hypothesis: its acquisition in this class is not addressed. -/
theorem stablyReceivesAt_of_hasStronglyCodedCutoffStableRecovery (hR : R.IsConsistent)
    (hc : R.IsCovering) (hl : R.HasLegalTypes)
    (hsc : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage ξ) n), R.eval t = some p →
      p.rows.IsStronglyCoded)
    (hrec : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded)
    (hS : StageType.HasStronglyCodedCutoffStableRecovery ξ)
    {x : (R.stableCandidate (isStablyLawful_of_hasLegalTypes hR hc hl)).Occurrence}
    (hx : 0 < x.arity) {D : StageType.{u} (blockStage (ξ + 1)) (x.arity + 1)}
    (hD : D ∈ x.type.cofaces) (hDs : D.rows.IsStronglyCoded) {γ : Ordinal.{u}}
    (hγ : γ < blockStage (ξ + 1)) (w : R.Occurrence) {f : Fin x.arity ↪ Fin w.arity}
    (hf : f.trans w.tuple = x.tuple)
    (hC : GradedCapMarginCalibration ξ
      (R.stableType (isStablyLawful_of_hasLegalTypes hR hc hl) w.tuple w.type w.eval_tuple) f D γ) :
    R.StablyReceivesAt (isStablyLawful_of_hasLegalTypes hR hc hl) x D γ := by
  have hlaw := isStablyLawful_of_hasLegalTypes hR hc hl
  have hface : restrictFace f (R.stableType hlaw w.tuple w.type w.eval_tuple) = some x.type := by
    rw [← isConsistent_stableCandidate hR hc w.tuple _ f
      (stableCandidate_eval_of_eval w.eval_tuple), hf]
    exact x.eval_tuple
  obtain ⟨q, δ, hqs, hq⟩ := hS _ f x.type
    ⟨hl w.tuple w.type w.eval_tuple, hsc w.tuple w.type w.eval_tuple⟩ hx hface D hD hDs γ hγ hC
  exact stablyReceivesAt_of_isCutoffStableRecovery_of_isStronglyCoded hR hc hrec w hf hqs hq

end Realization

end VaughtConjecture
