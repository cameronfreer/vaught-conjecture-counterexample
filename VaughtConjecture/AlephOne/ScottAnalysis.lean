/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ScottProcess.RankComparison
import VaughtConjecture.AlephOne.ChartDefinability
import VaughtConjecture.AlephOne.OnePointPair
import VaughtConjecture.Comparison.ScottProcess
import VaughtConjecture.Continuation.Comparison
import VaughtConjecture.Expansion.ReceivingAgreement
import VaughtConjecture.Language.Density

/-!
# Scott analysis of receiving models at `ω₁`

Companion programme over the density sentence: Scott ranks of the receiving model expansions at
stage `ω₁` all of whose types are top-free.  Every statement here except the last is a
**given-model statement**: it is about every model expansion (or realization) in the class, and
asserts the existence of no model.  The exception is the combined target
`ExistsAlephOneModelScottRankOmegaOneTarget`, an existence statement.  The class is
`IsReceivingModel` together with top-freeness of every type of the realization, written inline
as `∀ ⦃n⦄ (t : Fin n ↪ M) p, R.eval t = some p → p.IsTopFree`.

**Back-and-forth types, not orbits.**  Chart definability together with the comparison
theorem determines the back-and-forth type of a tuple (its class under back-and-forth
equivalence at every level).  Nothing here identifies such a class with an automorphism orbit,
and nothing needs it: InfinitaryLogic's `orbitRank` and `internalScottRank`
(`Scott/OrbitRank.lean`) are defined through back-and-forth equivalence at every level, for
structures of any cardinality, and the comparison of the semantic Scott process with them
(`ScottProcess/RankComparison.lean`) is stated in the same terms.  The name `orbitRank` is
InfinitaryLogic's; for countable structures that library proves the orbit reading, which is not
used here.

**The comparison within the class.**  Two model expansions in the class, on carriers in any two
universes, are related by a potential isomorphism of their base structures whose family contains
every pair of selections, along one selector, of covers of one stage type
(`ReceivingModelsPotentialIsoTarget`): the rooted back-and-forth family of the exact-age
comparison (`Realization.rootedPotentialIso`) at the empty cores, with the age of the legal
top-free types and exact receiving within it (`Realization.exactReceivingWithin_isTopFree`).

**Step 1: back-and-forth types are determined below `ω₁`.**  Every tuple `a` of a model in the
class is a selection along some `f` of a cover of a top-free type `p`.  The selections along `f`
of covers of `p` are defined, in every model in the class, by one formula of rank `ξ < ω₁`
(`chartSelectionFormula`).  If a tuple `b` of a model in the class is back-and-forth equivalent
to `a` at `ξ`, it satisfies that formula (Karp), so it is the selection along `f` of a cover of
`p`, and the comparison makes `a` and `b` back-and-forth equivalent at every level
(`BFEquivAllOfBFEquivLtOmegaOneTarget`).  Within one model this bounds every orbit rank below
`ω₁` (`OrbitRankLtOmegaOneTarget`).

**Step 2: unbounded stabilization below `ω₁`.**  Above every countable block stage `λ_ξ`, a model
in the class has two points whose one-point types are distinct with equal reductions to `λ_ξ`
(`onePointPairOccursTarget`).  The two points are back-and-forth equivalent at `ξ` (the
comparison from a common chart at `λ_ξ`,
`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`), and not at the rank of the
chart formula of either type (`ExistsBFEquivNotBFEquivTarget`); so some orbit rank exceeds `ξ`
(`ExistsOrbitRankGtTarget`).  Top-freeness of the model is not used in this step.

**Step 3: the ranks.**  Steps 1 and 2 give internal Scott rank exactly `ω₁`
(`InternalScottRankEqOmegaOneTarget`); since `ω₁` is a limit, the semantic Scott process of every
length beyond `ω₁ + 1` has rank `ω₁` (`ScottProcessIsRankOmegaOneTarget`, through
`isRank_iff_lift_eq_internalScottRank_of_isSuccLimit`).  The comparison and the generic
`Comparison.scottProcessOf_eq_of_potentialIso` give one Scott process for all models in the
class (`ReceivingModelsScottProcessEqTarget`).

**Results.**

* `ReceivingModelsPotentialIsoTarget` (proved).
* `chartSelectionFormula`, with `qrank_chartSelectionFormula_lt` and
  `realize_chartSelectionFormula_iff` (proved): the formula of `ChartSelectionFormulaTarget`,
  named, so that one formula serves models on carriers in different universes.
* `BFEquivAllOfBFEquivLtOmegaOneTarget` (proved).
* `ReceivingModelsScottProcessEqTarget` (proved), with the form
  `ReceivingModelsScottProcessEqOfModelTarget` (proved) that derives the `Infinite` instances
  from the models.
* `OrbitRankLtOmegaOneTarget` (proved).
* `ExistsBFEquivNotBFEquivTarget`, `ExistsOrbitRankGtTarget` (proved).
* `InternalScottRankEqOmegaOneTarget`, `ScottProcessIsRankOmegaOneTarget` (proved), with
  `ScottProcessIsRankOmegaOneOfModelTarget` (proved).
* For a realization with its own base structure: `RealizationScottRankOmegaOneTarget` and
  `RealizationsScottProcessEqTarget` (proved), with `RealizationScottRankOmegaOneOfModelTarget`
  and `RealizationsScottProcessEqOfModelTarget` (proved).
* `lift_omega_one_eq` (proved): in the rank statements, `Ordinal.lift.{w} ω₁` elaborates as the
  lift of `ω₁ : Ordinal.{w}` to its own universe, which is the lift of `ω₁ : Ordinal.{0}`.
* `ExistsAlephOneModelScottRankOmegaOneTarget` (stated): the combined shape, an existence
  statement, to be assembled from an existence theorem for the class and the given-model
  statements here.
-/

universe u w w'

namespace VaughtConjecture

open Ordinal Order FirstOrder Language InfinitaryLogic.ScottProcess.Semantic

/-- **The two readings of `Ordinal.lift.{w} ω₁`.**  In the rank statements below, the expected
type `Ordinal.{w}` makes `Ordinal.lift.{w} ω₁` elaborate as the lift of `ω₁ : Ordinal.{w}` to its
own universe; it is the lift of `ω₁ : Ordinal.{0}` (`Ordinal.lift_id`, `Ordinal.lift_omega`). -/
theorem lift_omega_one_eq :
    Ordinal.lift.{w, w} (ω₁ : Ordinal.{w}) = Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0}) := by
  rw [Ordinal.lift_id, Ordinal.lift_omega, Ordinal.lift_one]

/-! ### The comparison within the class -/

/-- **Target: a potential isomorphism between any two models in the class.**  For model
expansions `R` of `M` and `S` of `N` to `ω₁`, on carriers in any two universes, both receiving
models all of whose types are top-free, some potential isomorphism of the base structures
contains every pair `(x ∘ s, y ∘ s)` of selections along one selector `s` of covers `x` in `R` and
`y` in `S` of one stage type.  Given-model statement.  Proved
(`receivingModelsPotentialIsoTarget`). -/
def ReceivingModelsPotentialIsoTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁), R.1.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) → S.1.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ N) p, S.1.eval t = some p → p.IsTopFree) →
      ∃ P : PotentialIso baseLanguage.{0} M N, ∀ ⦃k : ℕ⦄ (p : StageType.{0} ω₁ k) (x : Fin k → M)
        (y : Fin k → N), R.1.Covers p x → S.1.Covers p y → ∀ ⦃n : ℕ⦄ (s : Fin n → Fin k),
          (⟨n, x ∘ s, y ∘ s⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family

/-- A potential isomorphism between any two models in the class: the rooted back-and-forth family
(`Realization.rootedPotentialIso`) at the empty cores, which cover the stage type on no points
(`Realization.IsModel.exists_covers_zero`, `StageType.eq_of_zero`), for the age of the legal
top-free types.  Age inclusion is legality and top-freeness of the types of each model; exact
receiving within the age is `Realization.exactReceivingWithin_isTopFree`, from finite-extension
receiving at the limit stage `ω₁`.  Selections of covers of one type are matched through covers
(`Realization.CoverMatch`). -/
theorem receivingModelsPotentialIsoTarget : ReceivingModelsPotentialIsoTarget.{w, w'} := by
  intro M N _ _ R S hR htR hS htS
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  obtain ⟨p₀, hp₀⟩ := hR.1.exists_covers_zero
  obtain ⟨q₀, hq₀⟩ := hS.1.exists_covers_zero
  rw [StageType.eq_of_zero q₀ p₀] at hq₀
  have hr := (Realization.exactReceivingWithin_isTopFree hR.1.isConsistent hω
    (hR.2.hasFiniteExtensionReceiving hR.1.isConsistent hω.isSuccPrelimit)).exactReceivingWithinAt
      (![] : Fin 0 → M)
  have hr' := (Realization.exactReceivingWithin_isTopFree hS.1.isConsistent hω
    (hS.2.hasFiniteExtensionReceiving hS.1.isConsistent hω.isSuccPrelimit)).exactReceivingWithinAt
      (![] : Fin 0 → N)
  refine ⟨Realization.rootedPotentialIso (A := fun _ _ ↦ {D | D.IsLegal ∧ D.IsTopFree}) R.2 S.2
    (fun _ s _ D hD _ ↦ ⟨hR.1.hasLegalTypes s D hD, htR s D hD⟩)
    (fun _ s _ D hD _ ↦ ⟨hS.1.hasLegalTypes s D hD, htS s D hD⟩) hr hr' hp₀ hq₀,
    fun k p x y hx hy n s ↦ ?_⟩
  exact ⟨k, p, x, y, Function.Embedding.ofIsEmpty, s, hx, hy, funext fun i ↦ i.elim0,
    funext fun i ↦ i.elim0, rfl, rfl⟩

/-! ### Chart selection formulas, uniformly in the carrier universe -/

/-- **The chart selection formula** of a stage type `p` at `ω₁` along a selector `f`, read at a
countable block index `η`: the extension formula along `f` of the formula of the forcing
thresholds of the reduction of `p` to `λ_η`.  It is the formula of `ChartSelectionFormulaTarget`;
it does not depend on a carrier universe. -/
noncomputable def chartSelectionFormula {η : Ordinal.{0}} (hη : η < ω₁) {m : ℕ}
    (p : StageType.{0} ω₁ m) {n : ℕ} (f : Fin n → Fin m) : baseLanguage.{0}.Formulaω (Fin n) :=
  extendFormula (blockFormula forcingThresholds η hη (p.reduce (isSuccPrelimit_blockStage η))) f

/-- The chart selection formula has rank below `ω₁`: at most `ω · η + m`. -/
theorem qrank_chartSelectionFormula_lt {η : Ordinal.{0}} (hη : η < ω₁) {m : ℕ}
    (p : StageType.{0} ω₁ m) {n : ℕ} (f : Fin n → Fin m) :
    (chartSelectionFormula hη p f).qrank < ω₁ := by
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  rw [chartSelectionFormula, qrank_extendFormula]
  refine (add_le_add (qrank_blockFormula_le _ hη _) le_rfl).trans_lt ?_
  exact hω.isSuccPrelimit.add_natCast_lt
    ((le_add_self : ω * η ≤ ω + ω * η).trans_lt (blockStage_lt_omega_one hη)) m

/-- **The chart selection formula defines the selections**: if the reduction of `p` to `λ_η` is
top-free, the chart selection formula holds of `b`, in a receiving model expansion at `ω₁` on a
carrier in any universe, exactly when `b` is the selection along `f` of a cover of `p`.  The
argument of `chartSelectionFormulaTarget`. -/
theorem realize_chartSelectionFormula_iff {η : Ordinal.{0}} (hη : η < ω₁) {m : ℕ}
    {p : StageType.{0} ω₁ m} (hpη : (p.reduce (isSuccPrelimit_blockStage η)).IsTopFree) {n : ℕ}
    (f : Fin n → Fin m) {M : Type w} [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁)
    (hR : R.1.IsReceivingModel) (b : Fin n → M) :
    (chartSelectionFormula hη p f).Realize b ↔ ∃ a : Fin m → M, R.1.Covers p a ∧ a ∘ f = b := by
  rw [chartSelectionFormula, realize_extendFormula]
  refine exists_congr fun a ↦ ?_
  rw [realizeBlockFormulaOfIsReceivingModelTarget R hR hη, and_comm]
  refine and_congr_left fun _ ↦ ⟨fun ⟨ha, he⟩ ↦ ?_, fun h ↦ h.reduce _⟩
  rw [Realization.reduce_eval, Option.map_eq_some_iff] at he
  obtain ⟨q, hq, hqp⟩ := he
  exact ⟨ha, hq.trans (congrArg some (StageType.eq_of_reduce_eq_of_isTopFree _ hqp hpη))⟩

/-! ### Step 1: back-and-forth types are determined below `ω₁` -/

/-- **Target: the back-and-forth type of a tuple is determined below `ω₁`.**  For a model
expansion `R` to `ω₁` in the class and a tuple `a`, some countable level `ξ < ω₁` has the
following property: every tuple `b` of a model expansion `S` to `ω₁` in the class, on a carrier
in any universe, back-and-forth equivalent to `a` at `ξ` in the base language, is back-and-forth
equivalent to `a` at every level.  The level is chosen before `S`.  With `S = R` this is the
statement within one model.  Given-model statement.  Proved
(`bfEquivAllOfBFEquivLtOmegaOneTarget`). -/
def BFEquivAllOfBFEquivLtOmegaOneTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) →
    ∀ ⦃n : ℕ⦄ (a : Fin n → M), ∃ ξ < (ω₁ : Ordinal.{0}),
      ∀ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure N] (S : ModelExpansion N ω₁),
        S.1.IsReceivingModel → (∀ ⦃k : ℕ⦄ (t : Fin k ↪ N) p, S.1.eval t = some p → p.IsTopFree) →
          ∀ b : Fin n → N, BFEquiv (L := baseLanguage.{0}) ξ n a b →
            ∀ γ : Ordinal.{u}, BFEquiv (L := baseLanguage.{0}) γ n a b

/-- The back-and-forth type of a tuple is determined below `ω₁`.  The tuple `a` is a selection
along some `f` of a cover `x` of a top-free type `p` (covering); `ξ` is the rank of the chart
selection formula of `p` along `f`.  A tuple `b` equivalent to `a` at `ξ` satisfies it
(`BFEquiv_implies_agreeQR`), so it is the selection along `f` of a cover `y` of `p`
(`realize_chartSelectionFormula_iff`), and the pair is in the potential isomorphism of the class
(`receivingModelsPotentialIsoTarget`), hence equivalent at every level
(`PotentialIso.family_bfEquiv`). -/
theorem bfEquivAllOfBFEquivLtOmegaOneTarget : BFEquivAllOfBFEquivLtOmegaOneTarget.{u, w, w'} := by
  intro M _ R hR htR n a
  classical
  obtain ⟨x, hx⟩ := hR.1.isCovering.exists_subset_support (Finset.univ.image a)
  have hf (i : Fin n) : ∃ j, x.tuple j = a i :=
    (Realization.Occurrence.mem_support x).1 (hx (Finset.mem_image_of_mem a (Finset.mem_univ i)))
  choose f hf using hf
  have hxf : ⇑x.tuple ∘ f = a := funext hf
  obtain ⟨η, hη, hpη⟩ :=
    existsIsTopFreeReduceBlockStageTarget x.type (htR x.tuple x.type x.eval_tuple)
  refine ⟨_, qrank_chartSelectionFormula_lt hη x.type f, fun N _ S hS htS b hab γ ↦ ?_⟩
  have hφa : (chartSelectionFormula hη x.type f).Realize a :=
    (realize_chartSelectionFormula_iff hη hpη f R hR a).2
      ⟨x.tuple, Realization.covers_of_eval _ x.eval_tuple, hxf⟩
  have hφb : (chartSelectionFormula hη x.type f).Realize b :=
    (BFEquiv_implies_agreeQR _ a b hab (chartSelectionFormula hη x.type f) le_rfl).1 hφa
  obtain ⟨y, hy, rfl⟩ := (realize_chartSelectionFormula_iff hη hpη f S hS b).1 hφb
  obtain ⟨P, hP⟩ := receivingModelsPotentialIsoTarget R S hR htR hS htS
  rw [← hxf]
  exact P.family_bfEquiv γ (hP x.type _ y (Realization.covers_of_eval _ x.eval_tuple) hy f)

/-- **Target: every orbit rank is below `ω₁`.**  In a model expansion `R` to `ω₁` in the class,
every tuple has orbit rank (InfinitaryLogic's `orbitRank`: the least level at which equivalence
with the tuple is equivalence at every level) below `ω₁`, lifted to the carrier universe.  The
statement of step 1 within one model, in InfinitaryLogic's vocabulary.  Given-model statement.
Proved (`orbitRankLtOmegaOneTarget`). -/
def OrbitRankLtOmegaOneTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) →
      ∀ ⦃n : ℕ⦄ (a : Fin n → M), orbitRank (L := baseLanguage.{0}) a < Ordinal.lift.{w} ω₁

/-- Every orbit rank is below `ω₁`: step 1 with `S = R` makes the lift of the countable level `ξ`
of `a` a level at which equivalence with `a` is equivalence at every level (`orbitStable`), with
`BFEquiv.toOrdinalLift` from the lifted level to `ξ`. -/
theorem orbitRankLtOmegaOneTarget : OrbitRankLtOmegaOneTarget.{w} := by
  intro M _ R hR htR n a
  obtain ⟨ξ, hξ, h⟩ := bfEquivAllOfBFEquivLtOmegaOneTarget.{w, w, w} R hR htR a
  refine (orbitRank_le_of_mem (α := Ordinal.lift.{w} ξ) fun b hb γ ↦
    h R hR htR b hb.toOrdinalLift γ).trans_lt ?_
  rw [lift_omega_one_eq.{w}]
  exact Ordinal.lift_lt.2 hξ

/-! ### Step 2: unbounded stabilization below `ω₁` -/

/-- **Target: pairs equivalent at `ξ` and not at every level.**  In a receiving model expansion
`R` to `ω₁`, for every countable `ξ`, some two points are back-and-forth equivalent at `ξ` in the
base language and not back-and-forth equivalent at some countable level.  Top-freeness of the
types of `R` is not assumed.  Given-model statement.  Proved
(`existsBFEquivNotBFEquivTarget`). -/
def ExistsBFEquivNotBFEquivTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃ξ : Ordinal.{0}⦄, ξ < ω₁ → ∃ a₁ a₂ : M, BFEquiv (L := baseLanguage.{0}) ξ 1 ![a₁] ![a₂] ∧
      ∃ γ < (ω₁ : Ordinal.{0}), ¬ BFEquiv (L := baseLanguage.{0}) γ 1 ![a₁] ![a₂]

/-- Pairs equivalent at `ξ` and not at every level: the two points `a₁` and `a₂` of a one-point
pair above `λ_ξ` (`onePointPairOccursTarget`), with types `d₁ ≠ d₂` of equal reductions to `λ_ξ`.
They cover one stage type in the reduction of `R` to `λ_ξ`, a receiving model expansion, so they
are equivalent at `ξ` (`ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving`).  At the
rank `γ < ω₁` of the chart selection formula of `d₁`, equivalence would carry that formula from
`![a₁]` to `![a₂]` (`BFEquiv_implies_agreeQR`), making `![a₂]` a cover of `d₁`
(`realize_chartSelectionFormula_iff`), against `d₁ ≠ d₂`. -/
theorem existsBFEquivNotBFEquivTarget : ExistsBFEquivNotBFEquivTarget.{w} := by
  intro M _ R hR ξ hξ
  have hω : IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  obtain ⟨d₁, d₂, -, -, ht₁, -, -, hne, hr, a₁, a₂, h₁, h₂⟩ := onePointPairOccursTarget R.1 hR hξ
  let e := R.reduce hω.isSuccPrelimit (isSuccLimit_blockStage ξ) (omega0_le_blockStage ξ)
    (blockStage_lt_omega_one hξ).le
  have he : e.1.HasFiniteCutReceiving :=
    (hR.reduce hω.isSuccPrelimit (isSuccLimit_blockStage ξ) (blockStage_lt_omega_one hξ).le).2
  have h₂' : e.1.Covers (d₁.reduce (isSuccPrelimit_blockStage ξ)) ![a₂] := by
    rw [hr]
    exact h₂.reduce _
  have hbf := ModelExpansion.bfEquiv_comp_of_covers_of_hasFiniteCutReceiving hξ e e he he
    (h₁.reduce (isSuccPrelimit_blockStage ξ)) h₂' id
  obtain ⟨η, hη, hpη⟩ := existsIsTopFreeReduceBlockStageTarget d₁ ht₁
  refine ⟨a₁, a₂, hbf, _, qrank_chartSelectionFormula_lt hη d₁ id, fun hb ↦ hne ?_⟩
  have hφ₁ : (chartSelectionFormula hη d₁ id).Realize ![a₁] :=
    (realize_chartSelectionFormula_iff hη hpη id R hR _).2 ⟨_, h₁, rfl⟩
  obtain ⟨c, hc, hcb⟩ := (realize_chartSelectionFormula_iff hη hpη id R hR _).1
    ((BFEquiv_implies_agreeQR _ _ _ hb _ le_rfl).1 hφ₁)
  have hc₂ : c = ![a₂] := hcb
  subst hc₂
  exact Option.some_injective _ (hc.eval_eq.symm.trans h₂.eval_eq)

/-- **Target: orbit ranks are unbounded below `ω₁`.**  In a receiving model expansion `R` to
`ω₁`, for every countable `ξ`, some tuple has orbit rank above `ξ`, lifted to the carrier
universe.  Given-model statement.  Proved
(`existsOrbitRankGtTarget`). -/
def ExistsOrbitRankGtTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃ξ : Ordinal.{0}⦄, ξ < ω₁ →
      ∃ (n : ℕ) (a : Fin n → M), Ordinal.lift.{w} ξ < orbitRank (L := baseLanguage.{0}) a

/-- Orbit ranks are unbounded below `ω₁`: for the pair of `existsBFEquivNotBFEquivTarget`, an
orbit rank of `![a₁]` at most the lift of `ξ` would make `![a₁]` and `![a₂]` equivalent at every
level (`bfEquiv_all_of_bfEquiv_orbitRank`), in particular at the separating level. -/
theorem existsOrbitRankGtTarget : ExistsOrbitRankGtTarget.{w} := by
  intro M _ R hR ξ hξ
  obtain ⟨a₁, a₂, hbf, γ, -, hγ⟩ := existsBFEquivNotBFEquivTarget R hR hξ
  refine ⟨1, ![a₁], lt_of_not_ge fun hle ↦ hγ ?_⟩
  exact BFEquiv.toOrdinalLift
    (bfEquiv_all_of_bfEquiv_orbitRank (BFEquiv.monotone hle hbf.ofOrdinalLift) _)

/-! ### Step 3: the ranks and the common process -/

/-- **Target: internal Scott rank `ω₁`.**  A model expansion to `ω₁` in the class has internal
Scott rank (InfinitaryLogic's `internalScottRank`, the supremum of `orbitRank a + 1`) equal to
`ω₁`, lifted to the carrier universe.  Given-model statement.  Proved
(`internalScottRankEqOmegaOneTarget`). -/
def InternalScottRankEqOmegaOneTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) →
      internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w} ω₁

/-- Internal Scott rank `ω₁`, by InfinitaryLogic's exact-rank criterion
(`internalScottRank_eq_iff`): every `orbitRank a + 1` is below the limit `ω₁`
(`orbitRankLtOmegaOneTarget`), and every level below `ω₁` is exceeded by an orbit rank
(`existsOrbitRankGtTarget`). -/
theorem internalScottRankEqOmegaOneTarget : InternalScottRankEqOmegaOneTarget.{w} := by
  intro M _ R hR htR
  rw [lift_omega_one_eq.{w}]
  have hω : IsSuccLimit (Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0})) :=
    Ordinal.isSuccLimit_lift.2 (Cardinal.isSuccLimit_omega 1)
  refine internalScottRank_eq_iff.2 ⟨fun n a ↦ ?_, fun γ hγ ↦ ?_⟩
  · have h := orbitRankLtOmegaOneTarget R hR htR a
    rw [lift_omega_one_eq.{w}] at h
    rw [← Order.succ_eq_add_one]
    exact (hω.succ_lt h).le
  · obtain ⟨ξ, hξ, rfl⟩ := Ordinal.lt_lift_iff.1 hγ
    obtain ⟨n, a, ha⟩ := existsOrbitRankGtTarget R hR hξ
    exact ⟨n, a, ha.trans (lt_add_one _)⟩

/-- **Target: the semantic Scott process has rank `ω₁`.**  For a model expansion to `ω₁` in the
class, the semantic Scott process of the base structure (InfinitaryLogic's `scottProcessOf`) of
every length `δ > ω₁ + 1` has rank `ω₁` (`ScottProcess.IsRank`: the least level at which it
stabilizes).  The carrier is infinite for every model in the class (`Realization.IsModel.infinite`);
the instance is a binder because the process needs it.  Given-model statement.  Proved
(`scottProcessIsRankOmegaOneTarget`). -/
def ScottProcessIsRankOmegaOneTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] [Infinite M] (R : ModelExpansion M ω₁),
    R.1.IsReceivingModel → (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
        (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-- The semantic Scott process has rank `ω₁`: the internal Scott rank is the limit `ω₁`
(`internalScottRankEqOmegaOneTarget`), so InfinitaryLogic's comparison
`isRank_iff_lift_eq_internalScottRank_of_isSuccLimit` reads the rank off it, given
`ω₁ + 1 < δ`. -/
theorem scottProcessIsRankOmegaOneTarget : ScottProcessIsRankOmegaOneTarget.{w} := by
  intro M _ _ R hR htR δ hδ
  have hS := internalScottRankEqOmegaOneTarget R hR htR
  rw [lift_omega_one_eq.{w}] at hS
  have hlim : IsSuccLimit (internalScottRank (L := baseLanguage.{0}) M) :=
    hS ▸ Ordinal.isSuccLimit_lift.2 (Cardinal.isSuccLimit_omega 1)
  exact (isRank_iff_lift_eq_internalScottRank_of_isSuccLimit hlim).2 ⟨hδ, hS.symm⟩

/-- **Target: the semantic Scott process has rank `ω₁`, with the carrier's infinitude from the
model.**  `ScottProcessIsRankOmegaOneTarget` without the `Infinite` binder: the carrier of a model
expansion at the nonzero stage `ω₁` is infinite (`Realization.IsModel.infinite`).  Given-model
statement.  Proved (`scottProcessIsRankOmegaOneOfModelTarget`). -/
def ScottProcessIsRankOmegaOneOfModelTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁),
    R.1.IsReceivingModel → (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
        letI : Infinite M := R.2.isModel.infinite (Ordinal.omega_pos 1)
        (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-- The semantic Scott process has rank `ω₁`, with the carrier's infinitude from the model. -/
theorem scottProcessIsRankOmegaOneOfModelTarget : ScottProcessIsRankOmegaOneOfModelTarget.{w} := by
  intro M _ R hR htR δ hδ
  let : Infinite M := R.2.isModel.infinite (Ordinal.omega_pos 1)
  exact scottProcessIsRankOmegaOneTarget R hR htR hδ

/-- **Target: one Scott process for the class.**  Any two model expansions to `ω₁` in the class,
on carriers in any two universes, have the same semantic Scott process of every positive length.
No countability, cardinality or rank hypothesis.  Given-model statement.  Proved
(`receivingModelsScottProcessEqTarget`). -/
def ReceivingModelsScottProcessEqTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    [Infinite M] [Infinite N] (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁),
    R.1.IsReceivingModel → (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) →
    S.1.IsReceivingModel → (∀ ⦃n : ℕ⦄ (t : Fin n ↪ N) p, S.1.eval t = some p → p.IsTopFree) →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
        scottProcessOf baseLanguage.{0} M δ hδ = scottProcessOf baseLanguage.{0} N δ hδ

/-- One Scott process for the class: the potential isomorphism of the class
(`receivingModelsPotentialIsoTarget`) and `Comparison.scottProcessOf_eq_of_potentialIso`. -/
theorem receivingModelsScottProcessEqTarget : ReceivingModelsScottProcessEqTarget.{w, w'} := by
  intro M N _ _ _ _ R S hR htR hS htS δ hδ
  obtain ⟨P, -⟩ := receivingModelsPotentialIsoTarget R S hR htR hS htS
  exact Comparison.scottProcessOf_eq_of_potentialIso P hδ

/-- **Target: one Scott process for the class, with the carriers' infinitude from the models.**
`ReceivingModelsScottProcessEqTarget` without the `Infinite` binders: the carriers of model
expansions at the nonzero stage `ω₁` are infinite (`Realization.IsModel.infinite`).  Given-model
statement.  Proved (`receivingModelsScottProcessEqOfModelTarget`). -/
def ReceivingModelsScottProcessEqOfModelTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁),
    R.1.IsReceivingModel → (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.1.eval t = some p → p.IsTopFree) →
    S.1.IsReceivingModel → (∀ ⦃n : ℕ⦄ (t : Fin n ↪ N) p, S.1.eval t = some p → p.IsTopFree) →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
        letI : Infinite M := R.2.isModel.infinite (Ordinal.omega_pos 1)
        letI : Infinite N := S.2.isModel.infinite (Ordinal.omega_pos 1)
        scottProcessOf baseLanguage.{0} M δ hδ = scottProcessOf baseLanguage.{0} N δ hδ

/-- One Scott process for the class, with the carriers' infinitude from the models. -/
theorem receivingModelsScottProcessEqOfModelTarget :
    ReceivingModelsScottProcessEqOfModelTarget.{w, w'} := by
  intro M N _ _ R S hR htR hS htS δ hδ
  let : Infinite M := R.2.isModel.infinite (Ordinal.omega_pos 1)
  let : Infinite N := S.2.isModel.infinite (Ordinal.omega_pos 1)
  exact receivingModelsScottProcessEqTarget R S hR htR hS htS hδ

/-! ### Realizations with their own base structure -/

/-- **Target: the ranks, for a realization with its own base structure.**  For a realization `R`
at `ω₁` on an infinite carrier, a receiving model all of whose types are top-free, the base
structure (the structure of the reduction of `R` to `ω`) has internal Scott rank `ω₁`, and its
semantic Scott process of every length `δ > ω₁ + 1` has rank `ω₁`.  Given-model statement.
Proved
(`realizationScottRankOmegaOneTarget`). -/
def RealizationScottRankOmegaOneTarget : Prop :=
  ∀ ⦃M : Type w⦄ [Infinite M] (R : Realization.{0, w} ω₁ M), R.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.eval t = some p → p.IsTopFree) →
      letI := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w} ω₁ ∧
        ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
          (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-- The ranks, for a realization with its own base structure: the model expansion
`⟨R, hR.1, rfl⟩` of the base structure. -/
theorem realizationScottRankOmegaOneTarget : RealizationScottRankOmegaOneTarget.{w} := by
  intro M _ R hR htR
  let := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  exact ⟨internalScottRankEqOmegaOneTarget ⟨R, hR.1, rfl⟩ hR htR,
    fun _ hδ ↦ scottProcessIsRankOmegaOneTarget ⟨R, hR.1, rfl⟩ hR htR hδ⟩

/-- **Target: the ranks, for a realization, with the carrier's infinitude from the model.**
`RealizationScottRankOmegaOneTarget` without the `Infinite` binder
(`Realization.IsModel.infinite` at the nonzero stage `ω₁`).  Given-model statement.  Proved
(`realizationScottRankOmegaOneOfModelTarget`). -/
def RealizationScottRankOmegaOneOfModelTarget : Prop :=
  ∀ ⦃M : Type w⦄ (R : Realization.{0, w} ω₁ M) (hR : R.IsReceivingModel),
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.eval t = some p → p.IsTopFree) →
      letI := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      letI : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
      internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w} ω₁ ∧
        ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
          (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-- The ranks, for a realization, with the carrier's infinitude from the model. -/
theorem realizationScottRankOmegaOneOfModelTarget :
    RealizationScottRankOmegaOneOfModelTarget.{w} := by
  intro M R hR htR
  let : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
  exact realizationScottRankOmegaOneTarget R hR htR

/-- **Target: one Scott process, for realizations with their own base structures.**  Two
realizations at `ω₁` on infinite carriers in any two universes, both receiving models all of
whose types are top-free, have base structures with the same semantic Scott process of every
positive length.  Given-model statement.  Proved (`realizationsScottProcessEqTarget`). -/
def RealizationsScottProcessEqTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [Infinite M] [Infinite N] (R : Realization.{0, w} ω₁ M)
    (S : Realization.{0, w'} ω₁ N), R.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.eval t = some p → p.IsTopFree) → S.IsReceivingModel →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ N) p, S.eval t = some p → p.IsTopFree) →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
        letI := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
        letI := (S.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
        scottProcessOf baseLanguage.{0} M δ hδ = scottProcessOf baseLanguage.{0} N δ hδ

/-- One Scott process, for realizations with their own base structures: the model expansions
`⟨R, hR.1, rfl⟩` and `⟨S, hS.1, rfl⟩` of the base structures. -/
theorem realizationsScottProcessEqTarget : RealizationsScottProcessEqTarget.{w, w'} := by
  intro M N _ _ R S hR htR hS htS δ hδ
  let := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  let := (S.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  exact receivingModelsScottProcessEqTarget ⟨R, hR.1, rfl⟩ ⟨S, hS.1, rfl⟩ hR htR hS htS hδ

/-- **Target: one Scott process, for realizations, with the carriers' infinitude from the
models.**  `RealizationsScottProcessEqTarget` without the `Infinite` binders
(`Realization.IsModel.infinite` at the nonzero stage `ω₁`).  Given-model statement.  Proved
(`realizationsScottProcessEqOfModelTarget`). -/
def RealizationsScottProcessEqOfModelTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ (R : Realization.{0, w} ω₁ M) (S : Realization.{0, w'} ω₁ N)
    (hR : R.IsReceivingModel), (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) p, R.eval t = some p → p.IsTopFree) →
    ∀ (hS : S.IsReceivingModel), (∀ ⦃n : ℕ⦄ (t : Fin n ↪ N) p, S.eval t = some p → p.IsTopFree) →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
        letI := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
        letI := (S.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
        letI : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
        letI : Infinite N := hS.1.infinite (Ordinal.omega_pos 1)
        scottProcessOf baseLanguage.{0} M δ hδ = scottProcessOf baseLanguage.{0} N δ hδ

/-- One Scott process, for realizations, with the carriers' infinitude from the models. -/
theorem realizationsScottProcessEqOfModelTarget :
    RealizationsScottProcessEqOfModelTarget.{w, w'} := by
  intro M N R S hR htR hS htS δ hδ
  let : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
  let : Infinite N := hS.1.infinite (Ordinal.omega_pos 1)
  exact realizationsScottProcessEqTarget R S hR htR hS htS hδ

/-! ### The combined shape -/

/-- **Target: a model of the density sentence of cardinality `ℵ₁` and Scott rank `ω₁`.**  Some
structure of the base language on a carrier in `Type` satisfies the density sentence, has
cardinality `ℵ₁` and internal Scott rank `ω₁`, and its semantic Scott process of every length
beyond `ω₁ + 1` has rank `ω₁`.  Existence statement, to be assembled from an existence theorem
for the class and the given-model statements of this file.  Stated. -/
def ExistsAlephOneModelScottRankOmegaOneTarget : Prop :=
  ∃ (M : Type) (_ : baseLanguage.{0}.Structure M) (_ : Infinite M),
    Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧ Cardinal.mk M = Cardinal.aleph 1 ∧
      internalScottRank (L := baseLanguage.{0}) M = (ω₁ : Ordinal.{0}) ∧
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
        (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

end VaughtConjecture
