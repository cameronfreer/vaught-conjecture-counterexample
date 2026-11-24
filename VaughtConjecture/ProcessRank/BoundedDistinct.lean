/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Count
import VaughtConjecture.AlephOne.ScottAnalysis
import VaughtConjecture.ProcessRank.BoundedExistence
import VaughtConjecture.ProcessRank.CoverTransfer
import VaughtConjecture.ProcessRank.RankConventions
import VaughtConjecture.ProcessRank.RankTopLabel

/-!
# Distinct Scott classes of the bounded receiving models: the statements

For each bound `K`, the receiving model `M_K` of `VaughtConjecture.ProcessRank.BoundedConstruction`
realizes exactly the bounded age `A_K` (the legal stage types at `ω₁` of top grade at most `K`).
This file states that the models `M_K` lie in pairwise distinct Scott classes (classes up to
potential isomorphism of the base structures, equivalently up to `L_{∞ω}`-equivalence; not
isomorphism classes), and that their process rank is `ω₁`, conditionally on a named premise for
the upper bound on orbit ranks.

**The realized age is an invariant of the base structure** (`RealizedAgeInvariantTarget`, proved,
`realizedAgeInvariantTarget`, given-model).  For receiving model expansions `R` of `M` and `S` of
`N` to `ω₁`, a potential isomorphism of the base structures `M` and `N` gives equal realized
ages.  It concerns the base structures, not the expansions: two receiving expansions of one base
structure have the same realized age (the identity potential isomorphism).  The proof
(`ProcessRank.exists_covers_iff_of_potentialIso`, in
`VaughtConjecture.ProcessRank.CoverTransfer`): a cover `y` of `D` in `S` is matched by the back
steps of the potential isomorphism with a tuple `x` of `M` back-and-forth equivalent to it at
every level (`PotentialIso.family_bfEquiv`); at every countable block stage `λ_η`, `y` covers the
reduction of `D` in the reduction of `S`, so it satisfies the block formula of that reduction, a
formula of countable rank (`Realization.IsReceivingModel.realize_blockFormula_iff`, valid for
every stage type, top-bearing included), and so does `x`; so the type `p` of `x` in `R` has the
reductions of `D` at every countable block stage, and `p = D`
(`StageType.eq_of_forall_reduce_blockStage_eq_omega_one`).  No formula of uncountable rank is
built: the back-and-forth equivalence at every countable level of the two covers suffices.

**What gives infinitely many classes.**  Three inputs:
1. witnesses: for every `n ≥ 1` a legal stage type `t_n` of top grade exactly `n`
   (`ProcessRank.Bounded.topGradeWitnessTarget`, proved; `t_1` is the one-point apex type,
   `ProcessRank.Bounded.topGrade_onePointApex`);
2. detection: a receiving model with top grades at most `K` and exact receiving within `A_K`
   covers `t_n` exactly when `n ≤ K` (`covers_iff_le_of_topGrade_eq`, proved);
3. invariance: detection depends only on the Scott class of the base structure, not on the
   receiving expansion (`WitnessDetectionTarget`, proved, `witnessDetectionTarget`, from
   `realizedAgeInvariantTarget`).
So `K ↦` the Scott class of `M_K` is injective (`BoundedNotPotentiallyIsoTarget`, proved,
`boundedNotPotentiallyIsoTarget`): for `K < L`, the witness
`t_L` lies in `A_L` and not in `A_K`.

**The case `K = 1`** (first milestone).  The one-point apex type (top grade `1`) lies in `A_1`
and in no top-free age, so `M_1` is not potentially isomorphic to any top-free receiving model
(`BoundedOneNotTopFreeTarget`, proved, `boundedOneNotTopFreeTarget`).

**Ranks** (conditional on one named premise).

* The upper bound on orbit ranks is the premise
  `ProcessRank.OrbitRankLeOmegaOneOfExactReceivingTarget` (in
  `VaughtConjecture.ProcessRank.RankUpper`, open): in a receiving model expansion to `ω₁` with
  exact receiving within its own realized age, every orbit rank is at most `ω₁`.  The lower bound,
  unbounded orbit ranks below `ω₁`, holds in every receiving model
  (`ProcessRank.lift_omegaOne_le_iSup_orbitRank`).  A cover of a type with a cell labelled `⊤` has
  orbit rank at least `ω₁` (`ProcessRank.orbitRankGeOmegaOneOfCoversTarget`, proved).
* `BoundedProcessRankTarget` (proved, conditional): the process rank of `M_K` is `ω₁`.
* `BoundedInternalScottRankTarget` (proved, conditional): for `K ≥ 1` the internal Scott rank is
  `ω₁ + 1`.
* `BoundedOneRankTarget` (proved, conditional): the case `K = 1` of both.

**Existence** (proved, with the construction of `VaughtConjecture.ProcessRank.BoundedExistence`).

* `ExistsBoundedOneModelTarget` (unconditional): a receiving model `M_1` on the carrier, realizing
  the one-point apex type, whose base structure is not potentially isomorphic to the base
  structure of any top-free receiving model, on a carrier in any universe.
* `BoundedOneMilestoneTarget` (conditional on the upper bound): the same model, satisfying the
  density sentence, of process rank `ω₁` and internal Scott rank `ω₁ + 1`.
* `ExistsBoundedFamilyTarget` (unconditional): receiving models `M_K` on the carrier for all `K`,
  each realizing a legal type of top grade exactly `K`, with pairwise not potentially isomorphic
  base structures.
* `InfinitelyManyRankOmegaOneScottClassesTarget` (conditional on the upper bound): countably
  infinitely many pairwise not potentially isomorphic models of the density sentence on the
  carrier, each of process rank `ω₁`.
* `InfinitelyManyInternalRankOmegaOneAddOneScottClassesTarget` (conditional on the upper bound):
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
equal realized ages at every arity.  Proved (`realizedAgeInvariantTarget`). -/
def RealizedAgeInvariantTarget : Prop :=
  ∀ ⦃M : Type w⦄ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N]
    (R : ModelExpansion M ω₁) (S : ModelExpansion N ω₁), R.1.IsReceivingModel →
      S.1.IsReceivingModel → Nonempty (PotentialIso baseLanguage.{0} M N) →
        ∀ m : ℕ, realizedAge R.1 m = realizedAge S.1 m

/-- **Potentially isomorphic base structures have receiving expansions with equal realized
ages**: `ProcessRank.exists_covers_iff_of_potentialIso`. -/
theorem realizedAgeInvariantTarget : RealizedAgeInvariantTarget.{w, w'} := by
  intro M N _ _ R S hR hS ⟨P⟩ m
  ext D
  rw [mem_realizedAge_iff, mem_realizedAge_iff]
  exact exists_covers_iff_of_potentialIso P hR hS D

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
(`witnessDetectionTarget_of`, `witnessDetectionTarget`). -/
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
(`boundedNotPotentiallyIsoTarget_of`, `boundedNotPotentiallyIsoTarget`). -/
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
invariance (`boundedOneNotTopFreeTarget_of`, `boundedOneNotTopFreeTarget`). -/
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

/-- **Detection of the witnesses is invariant under potential isomorphism of the base
structures** (`witnessDetectionTarget_of`, `realizedAgeInvariantTarget`). -/
theorem witnessDetectionTarget : WitnessDetectionTarget.{w, w'} :=
  witnessDetectionTarget_of realizedAgeInvariantTarget

/-- **Distinct bounds give distinct Scott classes** (`boundedNotPotentiallyIsoTarget_of`,
`realizedAgeInvariantTarget`). -/
theorem boundedNotPotentiallyIsoTarget : BoundedNotPotentiallyIsoTarget.{w, w'} :=
  boundedNotPotentiallyIsoTarget_of realizedAgeInvariantTarget

/-- **The model of top grades at most `1` is outside the top-free Scott class**
(`boundedOneNotTopFreeTarget_of`, `realizedAgeInvariantTarget`). -/
theorem boundedOneNotTopFreeTarget : BoundedOneNotTopFreeTarget.{w, w'} :=
  boundedOneNotTopFreeTarget_of realizedAgeInvariantTarget

/-! ### Ranks -/

/-- **Exact receiving within the realized age**: a model with top grades at most `K` and exact
receiving within `A_K` has realized age `A_K` (`ProcessRank.Bounded.realizedAge_eq_boundedAge`). -/
theorem exactReceivingWithin_realizedAge {M : Type w} {R : Realization.{0, w} ω₁ M}
    (hR : R.IsModel) {K : ℕ} (hK : HasTopGradeLe R K)
    (hrec : R.ExactReceivingWithin (boundedAge K)) : R.ExactReceivingWithin (realizedAge R) := by
  rwa [show realizedAge R = boundedAge K from funext (realizedAge_eq_boundedAge hR hK hrec)]

/-- **Target: process rank `ω₁` for the bounded receiving models, under the orbit-rank
hypothesis** (given-model statement).  Given `OrbitRankLeOmegaOneOfExactReceivingTarget`, for a
receiving model expansion `R` of `M` to `ω₁` with top grades at most `K` and exact receiving
within `A_K`, the semantic Scott process of the base structure of every length `δ > ω₁ + 1` has
rank `ω₁` (`R(M) = sup_a orbitRank a = ω₁`).  Proved (`boundedProcessRankTarget`). -/
def BoundedProcessRankTarget : Prop :=
  OrbitRankLeOmegaOneOfExactReceivingTarget.{w} →
    ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁) ⦃K : ℕ⦄
      (hR : R.1.IsReceivingModel), HasTopGradeLe R.1 K → R.1.ExactReceivingWithin (boundedAge K) →
        ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
          letI : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
          (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-- **Process rank `ω₁` for the bounded receiving models**, under the orbit-rank hypothesis: the
realized age is `A_K`, so the hypothesis applies, and the supremum of the orbit ranks is `ω₁`
(`ProcessRank.iSup_orbitRank_eq_omegaOne_of_exactReceiving`, `ProcessRank.isRank_omegaOne_iff`). -/
theorem boundedProcessRankTarget : BoundedProcessRankTarget.{w} := by
  intro hup M _ R K hR hK hrec δ hδ
  let : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
  exact (isRank_omegaOne_iff hδ).2 (iSup_orbitRank_eq_omegaOne_of_exactReceiving hup R hR
    (exactReceivingWithin_realizedAge hR.1 hK hrec))

/-- **Target: internal Scott rank `ω₁ + 1` for the bounded receiving models with a top, under the
orbit-rank hypothesis** (given-model statement).  Given
`OrbitRankLeOmegaOneOfExactReceivingTarget`, for `K ≥ 1` and a receiving model expansion `R` of
`M` to `ω₁` with top grades at most `K` and exact receiving within `A_K`, the internal Scott rank
of the base structure is `ω₁ + 1` (`S(M) = sup_a (orbitRank a + 1)`), lifted to the carrier
universe: the one-point apex type is realized, and its covers have orbit rank exactly `ω₁` (at
least `ω₁` by `ProcessRank.orbitRankGeOmegaOneOfCoversTarget`).  Proved
(`boundedInternalScottRankTarget`). -/
def BoundedInternalScottRankTarget : Prop :=
  OrbitRankLeOmegaOneOfExactReceivingTarget.{w} →
    ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁) ⦃K : ℕ⦄, 1 ≤ K →
      R.1.IsReceivingModel → HasTopGradeLe R.1 K → R.1.ExactReceivingWithin (boundedAge K) →
        internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0}) + 1

/-- **Internal Scott rank `ω₁ + 1` for the bounded receiving models with a top**, under the
orbit-rank hypothesis: the supremum of the orbit ranks is `ω₁`, and a cover of the one-point apex
type (realized since `1 ≤ K`) has orbit rank exactly `ω₁`
(`ProcessRank.internalScottRank_eq_add_one_iff_of_isSuccLimit`). -/
theorem boundedInternalScottRankTarget : BoundedInternalScottRankTarget.{w} := by
  intro hup M _ R K hK1 hR hK hrec
  have hex := exactReceivingWithin_realizedAge hR.1 hK hrec
  have hlim : Order.IsSuccLimit (Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0})) :=
    Ordinal.isSuccLimit_lift.2 (Cardinal.isSuccLimit_omega 1)
  obtain ⟨a, ha⟩ : ∃ a : Fin 1 → M, R.1.Covers StageType.onePointApex a := by
    rw [← mem_realizedAge_iff, realizedAge_eq_boundedAge hR.1 hK hrec]
    exact onePointApex_mem_boundedAge_iff.mpr hK1
  have h0 : 0 < (StageType.onePointApex (α := (ω₁ : Ordinal.{0}))).card := by simp
  have hnt : ¬ (StageType.onePointApex (α := (ω₁ : Ordinal.{0}))).IsTopFree :=
    fun h ↦ h ⟨0, h0⟩ (StageType.onePointApex_label _)
  refine (internalScottRank_eq_add_one_iff_of_isSuccLimit hlim).2
    ⟨iSup_orbitRank_eq_omegaOne_of_exactReceiving hup R hR hex, 1, a,
      le_antisymm (hup R hR hex a) (orbitRankGeOmegaOneOfCoversTarget R hR _ a ha hnt)⟩

/-- **Target: the ranks of the model of top grades at most `1`, under the orbit-rank
hypothesis** (given-model statement): process rank `ω₁` and internal Scott rank `ω₁ + 1`.  The
case `K = 1` of `BoundedProcessRankTarget` and `BoundedInternalScottRankTarget`.  Proved
(`boundedOneRankTarget`). -/
def BoundedOneRankTarget : Prop :=
  OrbitRankLeOmegaOneOfExactReceivingTarget.{w} →
    ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁)
      (hR : R.1.IsReceivingModel), HasTopGradeLe R.1 1 → R.1.ExactReceivingWithin (boundedAge 1) →
        internalScottRank (L := baseLanguage.{0}) M = Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0}) + 1 ∧
        ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
          letI : Infinite M := hR.1.infinite (Ordinal.omega_pos 1)
          (scottProcessOf baseLanguage.{0} M δ (zero_le.trans_lt hδ)).IsRank ω₁

/-- **The ranks of the model of top grades at most `1`**, under the orbit-rank hypothesis. -/
theorem boundedOneRankTarget : BoundedOneRankTarget.{w} := fun hup _ _ R hR hK hrec ↦
  ⟨boundedInternalScottRankTarget hup R le_rfl hR hK hrec,
    boundedProcessRankTarget hup R hR hK hrec⟩

/-! ### Existence -/

/-- The receiving model on the carrier as a model expansion of its own base structure. -/
abbrev toModelExpansion (R : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier)
    (hR : R.IsReceivingModel) :
    @ModelExpansion Carrier (baseStructure R) (ω₁ : Ordinal.{0}) :=
  letI := baseStructure R
  ⟨R, hR.1, rfl⟩

/-- **Target: one model outside the top-free Scott class.**  Some receiving model `R` at `ω₁` on
the carrier `ω₁.ToType`, with top grades at most `1` and exact receiving within `A_1`, realizes
the one-point apex type, and its base structure is not potentially isomorphic to the base
structure of any receiving model expansion to `ω₁` all of whose types are top-free, on a carrier
in any universe.  Existence statement.  Proved (`existsBoundedOneModelTarget`). -/
def ExistsBoundedOneModelTarget : Prop :=
  ∃ R : Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier, R.IsReceivingModel ∧ HasTopGradeLe R 1 ∧
    R.ExactReceivingWithin (boundedAge 1) ∧ (∃ u, R.Covers StageType.onePointApex u) ∧
    ∀ ⦃N : Type w'⦄ [baseLanguage.{0}.Structure N] (S : ModelExpansion N ω₁),
      S.1.IsReceivingModel → S.1.HasTopFreeTypes →
        IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier N (baseStructure R) _)

/-- **One model outside the top-free Scott class**: the receiving model of
`existsBoundedReceivingModelTarget` at `K = 1` realizes the one-point apex type (it lies in
`A_1`), and `boundedOneNotTopFreeTarget` separates it from every top-free receiving model. -/
theorem existsBoundedOneModelTarget : ExistsBoundedOneModelTarget.{w'} := by
  obtain ⟨R, hR, hK, hrec⟩ := existsBoundedReceivingModelTarget 1
  refine ⟨R, hR, hK, hrec, ?_, fun N _ S hS hSt ↦ ?_⟩
  · rw [← mem_realizedAge_iff, realizedAge_eq_boundedAge hR.1 hK hrec]
    exact onePointApex_mem_boundedAge_iff.mpr le_rfl
  · let := baseStructure R
    exact boundedOneNotTopFreeTarget (toModelExpansion R hR) S hR hK hrec hS hSt

/-- **Target: the first milestone, the bounded model of top grades at most `1`, under the
orbit-rank hypothesis.**  Given `OrbitRankLeOmegaOneOfExactReceivingTarget`, some receiving model
`R` at `ω₁` on the carrier `ω₁.ToType`, with top grades at most `1` and exact receiving within
`A_1`, realizes the one-point apex type (a chart with a cell labelled `⊤`), and its base structure
satisfies the density sentence, has process rank `ω₁` (the semantic Scott process of every
length beyond `ω₁ + 1` has rank `ω₁`; `R(M) = sup_a orbitRank a`) and internal Scott rank
`ω₁ + 1` (`S(M) = sup_a (orbitRank a + 1)`), and is not potentially isomorphic to the base
structure of any receiving model expansion to `ω₁` all of whose types are top-free (in particular,
to the top-free model of `AlephOne.existsReceivingModelTarget`).  Existence statement,
conditional.  Proved (`boundedOneMilestoneTarget`). -/
def BoundedOneMilestoneTarget : Prop :=
  OrbitRankLeOmegaOneOfExactReceivingTarget.{0} →
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

/-- **The first milestone**, under the orbit-rank hypothesis: the model of
`existsBoundedOneModelTarget`, with the density sentence (`AlephOne.realizeDensitySentenceTarget`)
and the ranks (`boundedOneRankTarget`). -/
theorem boundedOneMilestoneTarget : BoundedOneMilestoneTarget.{w'} := by
  intro hup
  obtain ⟨R, hR, hK, hrec, hcov, hsep⟩ := existsBoundedOneModelTarget.{w'}
  let := baseStructure R
  obtain ⟨hint, hproc⟩ := boundedOneRankTarget hup (toModelExpansion R hR) hR hK hrec
  refine ⟨R, hR, hK, hrec, hcov, ⟨realizeDensitySentenceTarget R hR, ?_, fun δ hδ ↦ ?_⟩, hsep⟩
  · simpa using hint
  · exact hproc hδ

/-- **Target: the family of bounded receiving models.**  Some receiving models `R K` at `ω₁` on
the carrier `ω₁.ToType`, for all `K`, have top grades at most `K`, exact receiving within `A_K`,
and realize a legal stage type of top grade exactly `K`; their base structures are pairwise not
potentially isomorphic.  Existence statement.  Proved (`existsBoundedFamilyTarget`). -/
def ExistsBoundedFamilyTarget : Prop :=
  ∃ R : ℕ → Realization.{0, 0} (ω₁ : Ordinal.{0}) Carrier,
    (∀ K, (R K).IsReceivingModel ∧ HasTopGradeLe (R K) K ∧
      (R K).ExactReceivingWithin (boundedAge K) ∧
      ∃ t : StageType.{0} (ω₁ : Ordinal.{0}) K, t.IsLegal ∧ t.topGrade = K ∧
        ∃ u, (R K).Covers t u) ∧
    ∀ K L, K ≠ L →
      IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier Carrier (baseStructure (R K))
        (baseStructure (R L)))

/-- **A legal stage type of top grade exactly `K`**, for every `K`: the stage type on no points
for `K = 0`, the witness of `topGradeWitnessTarget` otherwise. -/
theorem exists_isLegal_topGrade_eq (K : ℕ) :
    ∃ t : StageType.{0} (ω₁ : Ordinal.{0}) K, t.IsLegal ∧ t.topGrade = K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact ⟨Condition.emptyType, Condition.isLegal_emptyType,
      StageType.topGrade_eq_zero_iff.mpr (StageType.isTopFree_of_zero _)⟩
  · exact topGradeWitnessTarget (Cardinal.isSuccLimit_omega 1).isSuccPrelimit K hK

/-- **The family of bounded receiving models**: for each `K` the receiving model of
`existsBoundedReceivingModelTarget`; it realizes a legal type of top grade `K`, which lies in
`A_K`; distinct bounds are separated by `boundedNotPotentiallyIsoTarget`. -/
theorem existsBoundedFamilyTarget : ExistsBoundedFamilyTarget := by
  choose R hR hK hrec using existsBoundedReceivingModelTarget
  refine ⟨R, fun K ↦ ⟨hR K, hK K, hrec K, ?_⟩, fun K L hKL ↦ ?_⟩
  · obtain ⟨t, ht, htK⟩ := exists_isLegal_topGrade_eq K
    refine ⟨t, ht, htK, ?_⟩
    rw [← mem_realizedAge_iff, realizedAge_eq_boundedAge (hR K).1 (hK K) (hrec K)]
    exact (mem_boundedAge_iff_of_topGrade_eq ht htK).mpr le_rfl
  · let := baseStructure (R K)
    exact @boundedNotPotentiallyIsoTarget Carrier Carrier (baseStructure (R K))
      (baseStructure (R L)) (toModelExpansion (R K) (hR K)) (toModelExpansion (R L) (hR L)) K L
      hKL (hR K) (hK K) (hrec K) (hR L) (hK L) (hrec L)

/-- **Target: countably infinitely many Scott classes of process rank `ω₁`, under the orbit-rank
hypothesis.**  Given `OrbitRankLeOmegaOneOfExactReceivingTarget`, some structures `S K` of the
base language on the carrier `ω₁.ToType`, for all `K`, satisfy the density sentence, have
semantic Scott process of rank `ω₁` at every length beyond `ω₁ + 1`, and are pairwise not
potentially isomorphic.  Existence statement, conditional.  Proved
(`infinitelyManyRankOmegaOneScottClassesTarget`). -/
def InfinitelyManyRankOmegaOneScottClassesTarget : Prop :=
  OrbitRankLeOmegaOneOfExactReceivingTarget.{0} →
    ∃ S : ℕ → baseLanguage.{0}.Structure Carrier,
      (∀ K, letI := S K;
        Sentenceω.Realize baseLanguage.densitySentence.{0} Carrier ∧
          ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
            (scottProcessOf baseLanguage.{0} Carrier δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
      ∀ K L, K ≠ L → IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier Carrier (S K) (S L))

/-- **Countably infinitely many Scott classes of process rank `ω₁`**, under the orbit-rank
hypothesis: the base structures of the family of `existsBoundedFamilyTarget`. -/
theorem infinitelyManyRankOmegaOneScottClassesTarget :
    InfinitelyManyRankOmegaOneScottClassesTarget := by
  intro hup
  obtain ⟨R, hR, hsep⟩ := existsBoundedFamilyTarget
  refine ⟨fun K ↦ baseStructure (R K), fun K ↦ ?_, hsep⟩
  let := baseStructure (R K)
  obtain ⟨hRK, hK, hrec, -⟩ := hR K
  exact ⟨realizeDensitySentenceTarget (R K) hRK, fun δ hδ ↦
    boundedProcessRankTarget hup (toModelExpansion (R K) hRK) hRK hK hrec hδ⟩

/-- **Target: countably infinitely many Scott classes of internal Scott rank `ω₁ + 1`, under the
orbit-rank hypothesis.**  Given `OrbitRankLeOmegaOneOfExactReceivingTarget`, some structures
`S K` of the base language on the carrier `ω₁.ToType`, for all `K`, satisfy the density sentence,
have semantic Scott process of rank `ω₁` at every length beyond `ω₁ + 1` and internal Scott rank
`ω₁ + 1`, and are pairwise not potentially isomorphic.  Existence statement, conditional.  Proved
(`infinitelyManyInternalRankOmegaOneAddOneScottClassesTarget`). -/
def InfinitelyManyInternalRankOmegaOneAddOneScottClassesTarget : Prop :=
  OrbitRankLeOmegaOneOfExactReceivingTarget.{0} →
    ∃ S : ℕ → baseLanguage.{0}.Structure Carrier,
      (∀ K, letI := S K;
        Sentenceω.Realize baseLanguage.densitySentence.{0} Carrier ∧
          internalScottRank (L := baseLanguage.{0}) Carrier = (ω₁ : Ordinal.{0}) + 1 ∧
          ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
            (scottProcessOf baseLanguage.{0} Carrier δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
      ∀ K L, K ≠ L → IsEmpty (@PotentialIso baseLanguage.{0} _ Carrier Carrier (S K) (S L))

/-- **Countably infinitely many Scott classes of internal Scott rank `ω₁ + 1`**, under the
orbit-rank hypothesis: the base structures of the members `K + 1` of the family of
`existsBoundedFamilyTarget`. -/
theorem infinitelyManyInternalRankOmegaOneAddOneScottClassesTarget :
    InfinitelyManyInternalRankOmegaOneAddOneScottClassesTarget := by
  intro hup
  obtain ⟨R, hR, hsep⟩ := existsBoundedFamilyTarget
  refine ⟨fun K ↦ baseStructure (R (K + 1)), fun K ↦ ?_,
    fun K L hKL ↦ hsep (K + 1) (L + 1) (by omega)⟩
  let := baseStructure (R (K + 1))
  obtain ⟨hRK, hK, hrec, -⟩ := hR (K + 1)
  refine ⟨realizeDensitySentenceTarget (R (K + 1)) hRK, ?_, fun δ hδ ↦
    boundedProcessRankTarget hup (toModelExpansion (R (K + 1)) hRK) hRK hK hrec hδ⟩
  simpa using boundedInternalScottRankTarget hup (toModelExpansion (R (K + 1)) hRK)
    (Nat.le_add_left 1 K) hRK hK hrec

end VaughtConjecture.ProcessRank.Bounded
