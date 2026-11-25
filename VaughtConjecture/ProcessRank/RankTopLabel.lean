/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.ScottAnalysis
import VaughtConjecture.Stage.Cap

/-!
# A tuple covering a chart with a top cell has orbit rank at least `ω₁`

Companion programme over the density sentence, process rank `ω₁`.  Conventions as in
`VaughtConjecture.ProcessRank.RankConventions`: `r(a) = orbitRank a`.  Every statement here is a
**given-model statement** about one receiving model expansion `R` at stage `ω₁`
(`ModelExpansion M ω₁` with `R.1.IsReceivingModel`); none asserts the existence of a model.

**The obstruction.**  Let `a` cover a stage type `p` at `ω₁` that is not top-free.  For every
countable `η`, capping `p` above the block stage `λ_η` gives a legal top-free stage type `q` with
the same reduction to `λ_η` (`ExistsTopFreeReduceEqTarget`, finite).  A cover `b` of `q` occurs
in the same model, by exact receiving of the legal top-free types over the empty root
(`Realization.exactReceivingWithin_isTopFree`).  Then `a` and `b` are back-and-forth equivalent
at `η` (the comparison from a common chart at `λ_η`,
`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`), and not at the countable rank
of the chart selection formula of `q` (`chartSelectionFormula`): that formula holds of `b`, and
would make `a` a cover of the top-free `q ≠ p`.  The approximating tuple `b` depends on `η`
(`ExistsCappedApproximationTarget`).  Hence `r(a) ≥ ω₁` (`OrbitRankGeOmegaOneOfCoversTarget`),
the implication being `orbitRankGeOmegaOneOfCoversTarget_of_approximation`.

**Results.**

* `ExistsTopFreeReduceEqTarget` (proved, `existsTopFreeReduceEqTarget`).
* `ExistsCappedApproximationTarget` (proved, `existsCappedApproximationTarget`).
* `OrbitRankGeOmegaOneOfCoversTarget` (proved, `orbitRankGeOmegaOneOfCoversTarget`), through
  `orbitRankGeOmegaOneOfCoversTarget_of_approximation` (the approximation gives the bound).
-/

universe w

namespace VaughtConjecture.ProcessRank

open Ordinal _root_.Order FirstOrder Language

/-- **Target: a legal stage type at `ω₁` has a legal top-free stage type with the same reduction
to any countable block stage.**  For a legal stage type `p` at `ω₁` and a countable index `η`,
some legal top-free stage type `q` at `ω₁` on the same points has the same reduction to `λ_η` as
`p`.  Route: `q = p.cap c` for an ordinal `c < ω₁` self-visible at the arity with `λ_η ≤ c`
(`Label.exists_lt_lt_isSelfVisible`); labels below `λ_η` are unchanged by the cap, and labels at
or above `λ_η`, `⊤` included, stay at or above `λ_η`, so both reduce to `⊤`.  Finite statement.
Proved (`existsTopFreeReduceEqTarget`). -/
def ExistsTopFreeReduceEqTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω₁ n), p.IsLegal → ∀ ⦃η : Ordinal.{0}⦄, η < ω₁ →
    ∃ q : StageType.{0} ω₁ n, q.IsLegal ∧ q.IsTopFree ∧
      q.reduce (isSuccPrelimit_blockStage η) = p.reduce (isSuccPrelimit_blockStage η)

/-- **Target: capped approximations of a tuple covering a chart with a top cell.**  In a
receiving model expansion `R` to `ω₁`, if `a` covers a stage type `p` that is not top-free, then
for every countable `η` some tuple `b` of the same model is back-and-forth equivalent to `a` at
`η` in the base language and not at some countable level.  The tuple `b` depends on `η`.
Given-model statement.  Proved (`existsCappedApproximationTarget`). -/
def ExistsCappedApproximationTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω₁ n) (a : Fin n → M), R.1.Covers p a → ¬ p.IsTopFree →
      ∀ ⦃η : Ordinal.{0}⦄, η < ω₁ → ∃ b : Fin n → M,
        BFEquiv (L := baseLanguage.{0}) η n a b ∧
          ∃ γ < (ω₁ : Ordinal.{0}), ¬ BFEquiv (L := baseLanguage.{0}) γ n a b

/-- **Target: a tuple covering a chart with a top cell has orbit rank at least `ω₁`.**  In a
receiving model expansion `R` to `ω₁`, a tuple `a` covering a stage type `p` that is not
top-free has `r(a) = orbitRank a` at least the lift of `ω₁` to the carrier universe.
Given-model statement.  Proved (`orbitRankGeOmegaOneOfCoversTarget`). -/
def OrbitRankGeOmegaOneOfCoversTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃n : ℕ⦄ (p : StageType.{0} ω₁ n) (a : Fin n → M), R.1.Covers p a → ¬ p.IsTopFree →
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤ orbitRank (L := baseLanguage.{0}) a

/-- **The approximations give the bound**: if `r(a)` were below the lift of `ω₁`, it would be the
lift of a countable `η`; the approximation `b` at `η` would be equivalent to `a` at `r(a)`, hence
at every level (`bfEquiv_all_of_bfEquiv_orbitRank`), against the separating countable level. -/
theorem orbitRankGeOmegaOneOfCoversTarget_of_approximation
    (h : ExistsCappedApproximationTarget.{w}) : OrbitRankGeOmegaOneOfCoversTarget.{w} := by
  intro M _ R hR n p a hp htop
  refine le_of_not_gt fun hlt ↦ ?_
  obtain ⟨η, hη, hηa⟩ := Ordinal.lt_lift_iff.1 hlt
  obtain ⟨b, hab, γ, -, hγ⟩ := h R hR p a hp htop hη
  exact hγ (BFEquiv.toOrdinalLift
    (bfEquiv_all_of_bfEquiv_orbitRank (hηa ▸ hab.ofOrdinalLift) (Ordinal.lift.{w} γ)))

/-! ### Proofs -/

/-- **A legal top-free stage type with the same reduction**, the target form: the cap of `p` at an
ordinal `c` with `λ_η < c < ω₁`, self-visible at the arity (`Label.exists_lt_lt_isSelfVisible`).
A label below `λ_η` is below `c`, so the cap keeps it; a label at or above `λ_η` stays at or above
`λ_η` under the cap, so both reduce to `⊤`. -/
theorem existsTopFreeReduceEqTarget : ExistsTopFreeReduceEqTarget := by
  intro n p hp η hη
  obtain ⟨c, hηc, hcω, hc⟩ := Label.exists_lt_lt_isSelfVisible
    (Cardinal.isSuccLimit_omega 1).isSuccPrelimit (blockStage_lt_omega_one hη) n
  refine ⟨p.cap c hc hcω, StageType.isLegal_cap.2 hp, StageType.isTopFree_cap,
    StageType.ext rfl fun i j h ↦ ?_⟩
  change Label.reduce _ (min (p.label i) c) = Label.reduce _ (p.label j)
  obtain rfl : (i : Fin p.card) = j := Fin.ext h
  have hβc : ((blockStage η : Ordinal.{0}) : Label.{0}) ≤ (c : Label.{0}) :=
    WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hηc.le)
  rcases lt_or_ge (p.label i) ((blockStage η : Ordinal.{0}) : Label.{0}) with hl | hl
  · rw [min_eq_left (hl.le.trans hβc)]
  · rw [Label.reduce_of_le hl, Label.reduce_of_le (le_min hl hβc)]

/-- **Capped approximations**, the target form.  The top-free `q` with the reduction of `p` to
`λ_η` (`existsTopFreeReduceEqTarget`) is covered by some `b` in the same model, by exact receiving
of the legal top-free types over the empty cover (`Realization.exactReceivingWithin_isTopFree`).
The tuples `a` and `b` cover one stage type in the reduction to `λ_η`, so they are equivalent at
`η` (`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`).  At the countable rank of
the chart selection formula of `q` along the identity (`chartSelectionFormula`, at a block stage
where the reduction of `q` is top-free), equivalence would carry that formula from `b` to `a`
(`BFEquiv_implies_agreeQR`), making `a` a cover of `q`, so `p = q`, against `p` having a top
cell. -/
theorem existsCappedApproximationTarget : ExistsCappedApproximationTarget.{w} := by
  intro M _ R hR n p a hpa htop η hη
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have hp : p.IsLegal := hR.1.hasLegalTypes _ p hpa.eval_eq
  obtain ⟨q, hql, hqt, hqr⟩ := existsTopFreeReduceEqTarget p hp hη
  -- a cover of `q`, received over the empty cover
  obtain ⟨p₀, hp₀⟩ := hR.1.exists_covers_zero
  obtain ⟨q₀, hq₀⟩ := Option.isSome_iff_exists.mp
    (q.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  rw [StageType.eq_of_zero q₀ p₀] at hq₀
  obtain ⟨b, hb, -⟩ := Realization.exactReceivingWithin_isTopFree hR.1.isConsistent hω
    (hR.2.hasFiniteExtensionReceiving hR.1.isConsistent hω.isSuccPrelimit) p₀ ![] hp₀ q
    Function.Embedding.ofIsEmpty ⟨hql, hqt⟩ hq₀
  refine ⟨b, ?_, ?_⟩
  · -- equivalence at `η`, from a common chart at `λ_η`
    let e := R.reduce hω.isSuccPrelimit (isSuccLimit_blockStage η) (omega0_le_blockStage η)
      (blockStage_lt_omega_one hη).le
    have he : e.1.HasFiniteCutReceiving :=
      (hR.reduce hω.isSuccPrelimit (isSuccLimit_blockStage η) (blockStage_lt_omega_one hη).le).2
    have hb' : e.1.Covers (p.reduce (isSuccPrelimit_blockStage η)) b := by
      rw [← hqr]
      exact hb.reduce _
    exact ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving hη e e he he
      (hpa.reduce (isSuccPrelimit_blockStage η)) hb' id
  · -- separation at the rank of the chart selection formula of `q`
    obtain ⟨η', hη', hqη'⟩ := existsIsTopFreeReduceBlockStageTarget q hqt
    refine ⟨_, qrank_chartSelectionFormula_lt hη' q id, fun hab ↦ htop ?_⟩
    have hφb : (chartSelectionFormula hη' q id).Realize b :=
      (realize_chartSelectionFormula_iff hη' hqη' id R hR b).2 ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hca⟩ := (realize_chartSelectionFormula_iff hη' hqη' id R hR a).1
      ((BFEquiv_implies_agreeQR _ a b hab _ le_rfl).2 hφb)
    have hca' : c = a := hca
    subst hca'
    obtain rfl : p = q := Option.some_injective _ (hpa.eval_eq.symm.trans hc.eval_eq)
    exact hqt

/-- **A tuple covering a chart with a top cell has orbit rank at least `ω₁`**, the target form:
`orbitRankGeOmegaOneOfCoversTarget_of_approximation` with `existsCappedApproximationTarget`. -/
theorem orbitRankGeOmegaOneOfCoversTarget : OrbitRankGeOmegaOneOfCoversTarget.{w} :=
  orbitRankGeOmegaOneOfCoversTarget_of_approximation existsCappedApproximationTarget

end VaughtConjecture.ProcessRank
