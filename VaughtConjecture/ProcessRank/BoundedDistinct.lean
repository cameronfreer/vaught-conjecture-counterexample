/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Count
import VaughtConjecture.AlephOne.ScottAnalysis
import VaughtConjecture.ProcessRank.BoundedConstruction

/-!
# Distinct Scott classes of the bounded receiving models: the statements

For each bound `K`, the receiving model `M_K` of `VaughtConjecture.ProcessRank.BoundedConstruction`
realizes exactly the bounded age `A_K` (the legal stage types at `ω₁` of top grade at most `K`).
This file states that the models `M_K` lie in pairwise distinct Scott classes (classes up to
potential isomorphism of the base structures, equivalently up to `L_{∞ω}`-equivalence; not
isomorphism classes), and that their process rank is `ω₁`, conditionally on a named hypothesis
for the upper bound on orbit ranks.

**The realized age is an invariant of the base structure** (`RealizedAgeInvariantTarget`,
stated, given-model).  For receiving model expansions `R` of `M` and `S` of `N` to `ω₁`, a
potential isomorphism of the base structures `M` and `N` gives equal realized ages.  It concerns
the base structures, not the expansions: two receiving expansions of one base structure have the
same realized age (the identity potential isomorphism).  The intended proof: a cover `y` of `D`
in `S` is matched by the back steps of the potential isomorphism with a tuple `x` of `M`
back-and-forth equivalent to it at every level (`PotentialIso.family_bfEquiv`); at every countable
block stage `λ_η`, `y` covers the reduction of `D` in the reduction of `S`, so it satisfies the
block formula of that reduction, a formula of countable rank
(`Realization.IsReceivingModel.realize_blockFormula_iff`, valid for every stage type, top-bearing
included), and so does `x`; so the type `p` of `x` in `R` has the reductions of `D` at every
countable block stage, and `p = D` (`StageType.eq_of_forall_reduce_eq_of_isSuccLimit`).  No
formula of uncountable rank is built: the back-and-forth equivalence at every countable level of
the two covers suffices.

**What gives infinitely many classes.**  Three inputs:
1. witnesses: for every `n ≥ 1` a legal stage type `t_n` of top grade exactly `n`
   (`ProcessRank.Bounded.topGradeWitnessTarget`, proved; `t_1` is the one-point apex type,
   `ProcessRank.Bounded.topGrade_onePointApex`);
2. detection: a receiving model with top grades at most `K` and exact receiving within `A_K`
   covers `t_n` exactly when `n ≤ K` (`covers_iff_le_of_topGrade_eq`, proved);
3. invariance: detection depends only on the Scott class of the base structure, not on the
   receiving expansion (`WitnessDetectionTarget`, proved from `RealizedAgeInvariantTarget`,
   `witnessDetectionTarget_of`).
So `K ↦` the Scott class of `M_K` is injective (`BoundedNotPotentiallyIsoTarget`, proved from the
invariance and the witnesses, `boundedNotPotentiallyIsoTarget_of`): for `K < L`, the witness
`t_L` lies in `A_L` and not in `A_K`.

**The case `K = 1`** (first milestone).  The one-point apex type (top grade `1`) lies in `A_1`
and in no top-free age, so `M_1` is not potentially isomorphic to any top-free receiving model
(`BoundedOneNotTopFreeTarget`, proved from the invariance alone,
`boundedOneNotTopFreeTarget_of`).

**Ranks** (conditional; the hypotheses are named premises).

* `OrbitRankLeOmegaOneHypothesis` (a hypothesis, stated, not proved here): in a receiving model
  expansion to `ω₁` with exact receiving within its own realized age, every orbit rank is at most
  `ω₁`.  This is the upper half of the rank lemma of the programme; the lower half, unbounded
  orbit ranks below `ω₁`, is proved for every receiving model (`AlephOne.existsOrbitRankGtTarget`).
* `TopOrbitRankGeOmegaOneHypothesis` (a hypothesis, stated, not proved here): in a receiving model
  expansion to `ω₁`, a cover of a type with a cell labelled `⊤` has orbit rank at least `ω₁`.
* `BoundedProcessRankTarget`: under the first hypothesis, the process rank of `M_K` is `ω₁`.
* `BoundedInternalScottRankTarget`: under both hypotheses, for `K ≥ 1` the internal Scott rank is
  `ω₁ + 1` (some orbit rank is exactly `ω₁`; InfinitaryLogic's
  `isRank_iff_lift_add_one_eq_internalScottRank_of_not_isSuccLimit`).
* `BoundedOneRankTarget`: the case `K = 1` of both.

**Existence** (stated).

* `ExistsBoundedOneModelTarget`: a receiving model `M_1` on the carrier, realizing the one-point
  apex type, whose base structure is not potentially isomorphic to the base structure of any
  top-free receiving model, on a carrier in any universe.
* `BoundedOneMilestoneTarget` (conditional on both hypotheses): the same model, satisfying the
  density sentence, of process rank `ω₁` and internal Scott rank `ω₁ + 1`.
* `ExistsBoundedFamilyTarget`: receiving models `M_K` on the carrier for all `K`, each realizing a
  legal witness of top grade exactly `K`, with pairwise not potentially isomorphic base
  structures.
* `InfinitelyManyRankOmegaOneScottClassesTarget` (conditional on the first hypothesis): countably
  infinitely many pairwise not potentially isomorphic models of the density sentence on the
  carrier, each of process rank `ω₁`.
* `InfinitelyManyInternalRankOmegaOneAddOneScottClassesTarget` (conditional on both hypotheses):
  the same with internal Scott rank `ω₁ + 1`.

## Placement

The bounded top-grade part of the process-rank companion programme (the files
`VaughtConjecture/ProcessRank/Bounded*.lean`).
-/

universe w w'

namespace VaughtConjecture.ProcessRank.Bounded

open Ordinal FirstOrder Language InfinitaryLogic.ScottProcess.Semantic AlephOne

/-- The **base structure** of a realization at `ω₁`: the structure of its reduction to `ω`. -/
noncomputable abbrev baseStructure {M : Type w} (R : Realization.{0, w} (ω₁ : Ordinal.{0}) M) :
    baseLanguage.{0}.Structure M :=
  (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure

/-! ### The realized age is an invariant of the base structure -/

/-- **Target: potentially isomorphic base structures have receiving expansions with equal realized
ages** (given-model statement).  For receiving model expansions `R` of `M` and `S` of `N` to
`ω₁`, on carriers in any two universes, a potential isomorphism of the base structures gives
equal realized ages at every arity.  Stated. -/
def RealizedAgeInvariantTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁), R.1.IsReceivingModel →
      S.1.IsReceivingModel → Nonempty (PotentialIso baseLanguage.{0} M N) →
        ∀ m : ℕ, realizedAge R.1 m = realizedAge S.1 m

/-! ### Detection of the witnesses -/

/-- **A bounded model realizes a witness of top grade `n` exactly when `n ≤ K`** (given-model
statement): a model with top grades at most `K` and exact receiving within `A_K` covers a legal
stage type of top grade `n` exactly when `n ≤ K`; its realized age is `A_K`
(`ProcessRank.Bounded.realizedAge_eq_boundedAge`). -/
theorem covers_iff_le_of_topGrade_eq {α : Ordinal.{0}} {M : Type w}
    {R : Realization.{0, w} α M} (hR : R.IsModel) {K : ℕ} (hK : HasTopGradeLe R K)
    (hrec : R.ExactReceivingWithin (boundedAge K)) {n m : ℕ} {t : StageType.{0} α m}
    (ht : t.IsLegal) (htn : t.topGrade = n) : (∃ u, R.Covers t u) ↔ n ≤ K := by
  change t ∈ realizedAge R m ↔ _
  rw [realizedAge_eq_boundedAge hR hK hrec, mem_boundedAge_iff_of_topGrade_eq ht htn]

/-- **Target: detection of the witnesses is invariant under potential isomorphism of the base
structures** (given-model statement).  Let `R` be a receiving model expansion of `M` to `ω₁` with
top grades at most `K` and exact receiving within `A_K`, and `t` a legal stage type of top grade
`n`.  For every structure `N` whose base structure is potentially isomorphic to `M` and every
receiving model expansion `S` of `N` to `ω₁`, `S` covers `t` exactly when `n ≤ K`.  So whether
`n ≤ K` is read off the Scott class of the base structure of `R`, whatever its receiving
expansion.  Proved from the invariance of the realized age
(`witnessDetectionTarget_of`). -/
def WitnessDetectionTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁) ⦃K n m : ℕ⦄
    (t : StageType.{0} (ω₁ : Ordinal.{0}) m), t.IsLegal → t.topGrade = n →
      R.1.IsReceivingModel → HasTopGradeLe R.1 K → R.1.ExactReceivingWithin (boundedAge K) →
      S.1.IsReceivingModel → Nonempty (PotentialIso baseLanguage.{0} M N) →
        ((∃ v, S.1.Covers t v) ↔ n ≤ K)

/-- **Detection of the witnesses is invariant under potential isomorphism of the base
structures**, from the invariance of the realized age and
`ProcessRank.Bounded.covers_iff_le_of_topGrade_eq`. -/
theorem witnessDetectionTarget_of (hinv : RealizedAgeInvariantTarget.{w, w'}) :
    WitnessDetectionTarget.{w, w'} := by
  intro M N _ _ R S K n m t ht htn hR hRK hRrec hS hP
  rw [← covers_iff_le_of_topGrade_eq hR.1 hRK hRrec ht htn]
  exact (Set.ext_iff.mp (hinv R S hR hS hP m) t).symm

/-! ### Distinctness -/

/-- **Target: distinct bounds give distinct Scott classes** (given-model statement).  For receiving
model expansions `R` of `M` and `S` of `N` to `ω₁` with top grades at most `K` and `L` and exact
receiving within `A_K` and `A_L`, and `K ≠ L`, the base structures are not potentially
isomorphic.  Proved from the invariance of the realized age, with the witnesses
(`boundedNotPotentiallyIsoTarget_of`). -/
def BoundedNotPotentiallyIsoTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁) ⦃K L : ℕ⦄, K ≠ L →
      R.1.IsReceivingModel → HasTopGradeLe R.1 K → R.1.ExactReceivingWithin (boundedAge K) →
      S.1.IsReceivingModel → HasTopGradeLe S.1 L → S.1.ExactReceivingWithin (boundedAge L) →
        IsEmpty (PotentialIso baseLanguage.{0} M N)

/-- A witness of top grade `L` above `K` is realized in a model with realized age `A_L` and not
in one with realized age `A_K`, so the realized ages differ. -/
theorem realizedAge_ne_of_lt {α : Ordinal.{0}} {M : Type w} {N : Type w'}
    {R : Realization.{0, w} α M} {S : Realization.{0, w'} α N} {K L : ℕ} (hKL : K < L)
    (hR : ∀ m, realizedAge R m = boundedAge K m) (hS : ∀ m, realizedAge S m = boundedAge L m)
    (hwit : TopGradeWitnessTarget α) : ∃ m, realizedAge R m ≠ realizedAge S m := by
  obtain ⟨t, ht, htL⟩ := hwit L (Nat.zero_le K |>.trans_lt hKL)
  refine ⟨L, fun h ↦ ?_⟩
  have hmem : t ∈ realizedAge R L := by
    rw [h, hS]
    exact (mem_boundedAge_iff_of_topGrade_eq ht htL).mpr le_rfl
  rw [hR, mem_boundedAge_iff_of_topGrade_eq ht htL] at hmem
  omega

/-- **Distinct bounds give distinct Scott classes**, from the invariance of the realized age and
the witnesses of every top grade: the realized ages are `A_K` and `A_L`
(`ProcessRank.Bounded.realizedAge_eq_boundedAge`), which differ at a witness of top grade
`max K L`. -/
theorem boundedNotPotentiallyIsoTarget_of (hinv : RealizedAgeInvariantTarget.{w, w'}) :
    BoundedNotPotentiallyIsoTarget.{w, w'} := by
  intro M N _ _ R S K L hKL hR hRK hRrec hS hSL hSrec
  have hwit := topGradeWitnessTarget (Cardinal.isSuccLimit_omega 1).isSuccPrelimit
  refine ⟨fun P ↦ ?_⟩
  have heq := hinv R S hR hS ⟨P⟩
  have hRa := realizedAge_eq_boundedAge hR.1 hRK hRrec
  have hSa := realizedAge_eq_boundedAge hS.1 hSL hSrec
  rcases lt_or_gt_of_ne hKL with h | h
  · obtain ⟨m, hm⟩ := realizedAge_ne_of_lt h hRa hSa hwit
    exact hm (heq m)
  · obtain ⟨m, hm⟩ := realizedAge_ne_of_lt h hSa hRa hwit
    exact hm (heq m).symm

/-- **Target: the model of top grades at most `1` is outside the top-free Scott class**
(given-model statement).  For a receiving model expansion `R` of `M` to `ω₁` with top grades at
most `1` and exact receiving within `A_1`, and a receiving model expansion `S` of `N` to `ω₁` all
of whose types are top-free, the base structures are not potentially isomorphic.  Proved from the
invariance (`boundedOneNotTopFreeTarget_of`). -/
def BoundedOneNotTopFreeTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁),
      R.1.IsReceivingModel → HasTopGradeLe R.1 1 → R.1.ExactReceivingWithin (boundedAge 1) →
      S.1.IsReceivingModel → S.1.HasTopFreeTypes →
        IsEmpty (PotentialIso baseLanguage.{0} M N)

/-- **The model of top grades at most `1` is outside the top-free Scott class**, from the
invariance: the one-point apex type is realized in `R` (it lies in `A_1`,
`ProcessRank.Bounded.onePointApex_mem_boundedAge_iff`), hence in `S`, whose types are
top-free. -/
theorem boundedOneNotTopFreeTarget_of (hinv : RealizedAgeInvariantTarget.{w, w'}) :
    BoundedOneNotTopFreeTarget.{w, w'} := by
  intro M N _ _ R S hR hRK hRrec hS hSt
  refine ⟨fun P ↦ ?_⟩
  have hmem : StageType.onePointApex ∈ realizedAge R.1 1 := by
    rw [realizedAge_eq_boundedAge hR.1 hRK hRrec]
    exact onePointApex_mem_boundedAge_iff.mpr le_rfl
  rw [hinv R S hR hS ⟨P⟩ 1] at hmem
  obtain ⟨u, hinj, hu⟩ := hmem
  have h0 : 0 < (StageType.onePointApex (α := (ω₁ : Ordinal.{0}))).card := by simp
  exact hSt _ _ hu ⟨0, h0⟩ (StageType.onePointApex_label _)

/-! ### Ranks -/

/-- **Hypothesis: orbit ranks at most `ω₁`.**  In a receiving model expansion `R` of `M` to `ω₁`
with exact receiving within its own realized age, every tuple has orbit rank at most `ω₁`, lifted
to the carrier universe.  A named hypothesis of the rank results below; stated, not proved
here. -/
def OrbitRankLeOmegaOneHypothesis : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    R.1.ExactReceivingWithin (realizedAge R.1) → ∀ ⦃n : ℕ⦄ (a : Fin n → M),
      orbitRank (L := baseLanguage.{0}) a ≤ Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0})

/-- **Hypothesis: covers of top-bearing types have orbit rank at least `ω₁`.**  In a receiving model
expansion `R` of `M` to `ω₁`, a cover of a stage type with a cell labelled `⊤` has orbit rank at
least `ω₁`, lifted to the carrier universe.  A named hypothesis of the internal-rank results
below; stated, not proved here. -/
def TopOrbitRankGeOmegaOneHypothesis : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃k : ℕ⦄ (p : StageType.{0} (ω₁ : Ordinal.{0}) k) (x : Fin k → M), R.1.Covers p x →
      ¬ p.IsTopFree → Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0}) ≤ orbitRank (L := baseLanguage.{0}) x

/-- **Target: process rank `ω₁` for the bounded receiving models, under the orbit-rank
hypothesis** (given-model statement).  Given `OrbitRankLeOmegaOneHypothesis`, for a receiving
model expansion `R` of `M` to `ω₁` with top grades at most `K` and exact receiving within `A_K`,
the semantic Scott process of the base structure of every length `δ > ω₁ + 1` has rank `ω₁`.
Stated. -/
def BoundedProcessRankTarget : Prop :=
  OrbitRankLeOmegaOneHypothesis.{w} →
    ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁) ⦃K : ℕ⦄
      (hR : R.1.IsReceivingModel), HasTopGradeLe R.1 K → R.1.ExactReceivingWithin (boundedAge K) →
        ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
          letI : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
          (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-- **Target: internal Scott rank `ω₁ + 1` for the bounded receiving models with a top, under both
hypotheses** (given-model statement).  Given `OrbitRankLeOmegaOneHypothesis` and
`TopOrbitRankGeOmegaOneHypothesis`, for `K ≥ 1` and a receiving model expansion `R` of `M` to
`ω₁` with top grades at most `K` and exact receiving within `A_K`, the internal Scott rank of the
base structure is `ω₁ + 1`, lifted to the carrier universe: the one-point apex type is realized,
and its covers have orbit rank exactly `ω₁`.  Stated. -/
def BoundedInternalScottRankTarget : Prop :=
  OrbitRankLeOmegaOneHypothesis.{w} → TopOrbitRankGeOmegaOneHypothesis.{w} →
    ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁) ⦃K : ℕ⦄, 1 ≤ K →
      R.1.IsReceivingModel → HasTopGradeLe R.1 K → R.1.ExactReceivingWithin (boundedAge K) →
        internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0}) + 1

/-- **Target: the ranks of the model of top grades at most `1`, under both hypotheses**
(given-model statement): process rank `ω₁` and internal Scott rank `ω₁ + 1`.  The case `K = 1`
of `BoundedProcessRankTarget` and `BoundedInternalScottRankTarget`.  Stated. -/
def BoundedOneRankTarget : Prop :=
  OrbitRankLeOmegaOneHypothesis.{w} → TopOrbitRankGeOmegaOneHypothesis.{w} →
    ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁)
      (hR : R.1.IsReceivingModel), HasTopGradeLe R.1 1 → R.1.ExactReceivingWithin (boundedAge 1) →
        internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0}) + 1 ∧
        ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
          letI : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
          (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-! ### Existence -/

/-- **Target: one model outside the top-free Scott class.**  Some receiving model `R` at `ω₁` on
the carrier `ω₁.ToType`, with top grades at most `1` and exact receiving within `A_1`, realizes
the one-point apex type, and its base structure is not potentially isomorphic to the base
structure of any receiving model expansion to `ω₁` all of whose types are top-free, on a carrier
in any universe.  Existence statement.  Stated. -/
def ExistsBoundedOneModelTarget : Prop :=
  ∃ R : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier, R.IsReceivingModel ∧ HasTopGradeLe R 1 ∧
    R.ExactReceivingWithin (boundedAge 1) ∧ (∃ u, R.Covers StageType.onePointApex u) ∧
    ∀ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure N] (S : ModelExpansion N ω₁),
      S.1.IsReceivingModel → S.1.HasTopFreeTypes →
        IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier N (baseStructure R) _)

/-- **Target: the first milestone, the bounded model of top grades at most `1`, under both
hypotheses.**  Given `OrbitRankLeOmegaOneHypothesis` and `TopOrbitRankGeOmegaOneHypothesis`, some
receiving model `R` at `ω₁` on the carrier `ω₁.ToType`, with top grades at most `1` and exact
receiving within `A_1`, realizes the one-point apex type (a chart with a cell labelled `⊤`), and
its base structure satisfies the density sentence, has process rank `ω₁` (the semantic Scott
process of every length beyond `ω₁ + 1` has rank `ω₁`; `R(M) = sup_a orbitRank a`) and internal
Scott rank `ω₁ + 1` (`S(M) = sup_a (orbitRank a + 1)`), and is not potentially isomorphic to the
base structure of any receiving model expansion to `ω₁` all of whose types are top-free (in
particular, to the top-free model of `AlephOne.existsReceivingModelTarget`).  Existence
statement, conditional.  Stated. -/
def BoundedOneMilestoneTarget : Prop :=
  OrbitRankLeOmegaOneHypothesis.{0} → TopOrbitRankGeOmegaOneHypothesis.{0} →
    ∃ R : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier, R.IsReceivingModel ∧
      HasTopGradeLe R 1 ∧ R.ExactReceivingWithin (boundedAge 1) ∧
      (∃ u, R.Covers StageType.onePointApex u) ∧
      (letI := baseStructure R;
        Sentenceω.Realize baseLanguage.densitySentence.{0} Carrier ∧
          internalScottRank (L := baseLanguage.{0}) Carrier = (ω₁ : Ordinal.{0}) + 1 ∧
          ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
            (scottProcessOf baseLanguage.{0} Carrier δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
      ∀ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure N] (S : ModelExpansion N ω₁),
        S.1.IsReceivingModel → S.1.HasTopFreeTypes →
          IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier N (baseStructure R) _)

/-- **Target: the family of bounded receiving models.**  Some receiving models `R K` at `ω₁` on
the carrier `ω₁.ToType`, for all `K`, have top grades at most `K`, exact receiving within `A_K`,
and realize a legal stage type of top grade exactly `K`; their base structures are pairwise not
potentially isomorphic.  Existence statement.  Stated. -/
def ExistsBoundedFamilyTarget : Prop :=
  ∃ R : ℕ → Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier,
    (∀ K, (R K).IsReceivingModel ∧ HasTopGradeLe (R K) K ∧
      (R K).ExactReceivingWithin (boundedAge K) ∧
      ∃ t : StageType.{0} (ω₁ : Ordinal.{0}) K, t.IsLegal ∧ t.topGrade = K ∧
        ∃ u, (R K).Covers t u) ∧
    ∀ K L, K ≠ L →
      IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier Carrier (baseStructure (R K))
        (baseStructure (R L)))

/-- **Target: countably infinitely many Scott classes of process rank `ω₁`, under the orbit-rank
hypothesis.**  Given `OrbitRankLeOmegaOneHypothesis`, some structures `S K` of the base language
on the carrier `ω₁.ToType`, for all `K`, satisfy the density sentence, have semantic Scott process
of rank `ω₁` at every length beyond `ω₁ + 1`, and are pairwise not potentially isomorphic.
Existence statement, conditional.  Stated. -/
def InfinitelyManyRankOmegaOneScottClassesTarget : Prop :=
  OrbitRankLeOmegaOneHypothesis.{0} →
    ∃ S : ℕ → baseLanguage.{0}.Structure Carrier,
      (∀ K, letI := S K;
        Sentenceω.Realize baseLanguage.densitySentence.{0} Carrier ∧
          ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
            (scottProcessOf baseLanguage.{0} Carrier δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
      ∀ K L, K ≠ L → IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier Carrier (S K) (S L))

/-- **Target: countably infinitely many Scott classes of internal Scott rank `ω₁ + 1`, under both
hypotheses.**  Given `OrbitRankLeOmegaOneHypothesis` and `TopOrbitRankGeOmegaOneHypothesis`, some
structures `S K` of the base language on the carrier `ω₁.ToType`, for all `K`, satisfy the
density sentence, have semantic Scott process of rank `ω₁` at every length beyond `ω₁ + 1` and
internal Scott rank `ω₁ + 1`, and are pairwise not potentially isomorphic.  Existence statement,
conditional.  Stated. -/
def InfinitelyManyInternalRankOmegaOneAddOneScottClassesTarget : Prop :=
  OrbitRankLeOmegaOneHypothesis.{0} → TopOrbitRankGeOmegaOneHypothesis.{0} →
    ∃ S : ℕ → baseLanguage.{0}.Structure Carrier,
      (∀ K, letI := S K;
        Sentenceω.Realize baseLanguage.densitySentence.{0} Carrier ∧
          internalScottRank (L := baseLanguage.{0}) Carrier = (ω₁ : Ordinal.{0}) + 1 ∧
          ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
            (scottProcessOf baseLanguage.{0} Carrier δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
      ∀ K L, K ≠ L → IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier Carrier (S K) (S L))

end VaughtConjecture.ProcessRank.Bounded
