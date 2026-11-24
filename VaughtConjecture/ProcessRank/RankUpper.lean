/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.ScottAnalysis

/-!
# Process rank `ω₁` from exact receiving within the realized age

Companion programme over the density sentence, process rank `ω₁`.  Conventions as in
`VaughtConjecture.ProcessRank.RankConventions`: `r(a) = orbitRank a`,
`R(M) = sup_a (r(a))`.  Every statement here is a **given-model statement** about one receiving
model expansion `R` at stage `ω₁`.

**Lower bound, in every receiving model** (`lift_omegaOne_le_iSup_orbitRank`, proved).  For every
countable `ξ` some tuple has `r(a) > ξ` (`AlephOne.existsOrbitRankGtTarget`, the one-point pair
of `AlephOne.onePointPairOccursTarget`); top-freeness of the model is not used there.  So
`R(M)` is at least the lift of `ω₁` in every receiving model expansion at `ω₁`, top-bearing ones
included.

**Upper bound, from exact receiving within the realized age.**  The **realized age** of `R` is
the family of the stage types of its covers.  Two steps.

1. Matching hulls (`ExistsCoverMatchOfBFEquivOmegaOneTarget`, stated; every receiving model): if
   tuples `a`, `b` of `M` are back-and-forth equivalent at `ω₁`, they are selections along one
   selector of covers of one stage type at `ω₁`.  Route: enumerate the finite hull of `a` by a
   cover of `p`; at each countable block stage the formula saying that a tuple is the selection of
   a cover of the reduction of `p` has countable rank, so `b` satisfies it; the matching covers
   enumerate the finite hull of `b`; one of finitely many enumerations serves for unboundedly many
   `η`, and its type is `p`, since stage types are separated by their countable reductions.
2. Exact-age comparison within `M` (`orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch`,
   proved from step 1): matched tuples are equivalent at every level by the rooted back-and-forth
   family (`Realization.CoverMatch.bfEquiv`) for the realized age at the empty cores.

So, with exact receiving within the realized age, `r(a) ≤ ω₁` for every `a`
(`OrbitRankLeOmegaOneOfExactReceivingTarget`) and `R(M)` is the lift of `ω₁`
(`iSup_orbitRank_eq_omegaOne_of_exactReceiving`, proved from the bound).

**Results.**

* `lift_omegaOne_le_iSup_orbitRank` (proved).
* `ExistsCoverMatchOfBFEquivOmegaOneTarget` (stated).
* `OrbitRankLeOmegaOneOfExactReceivingTarget` (stated), with
  `orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch` (proved from step 1).
* `iSup_orbitRank_eq_omegaOne_of_exactReceiving` (proved from
  `OrbitRankLeOmegaOneOfExactReceivingTarget`).
-/

universe w

namespace VaughtConjecture.ProcessRank

open Ordinal _root_.Order FirstOrder Language

/-- The **realized age** of a realization: at each number `m` of points, the stage types of its
covers on `m` points. -/
def realizedAge {α : Ordinal.{0}} {M : Type w} (R : Realization.{0, w} α M) (m : ℕ) :
    Set (StageType.{0} α m) :=
  {D | ∃ s : Fin m ↪ M, R.eval s = some D}

/-- **`R(M)` is at least `ω₁` in every receiving model expansion at `ω₁`**: every countable `ξ`
is exceeded by some `r(a)` (`AlephOne.existsOrbitRankGtTarget`). -/
theorem lift_omegaOne_le_iSup_orbitRank {M : Type w} [baseLanguage.{0}.Structure M]
    (R : ModelExpansion M ω₁) (hR : R.1.IsReceivingModel) :
    Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤
      ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2 := by
  refine le_of_forall_lt fun γ hγ ↦ ?_
  obtain ⟨ξ, hξ, rfl⟩ := Ordinal.lt_lift_iff.1 hγ
  obtain ⟨n, a, ha⟩ := AlephOne.existsOrbitRankGtTarget R hR hξ
  exact ha.trans_le (orbitRank_le_iSup_orbitRank a)

/-- **Target: tuples equivalent at `ω₁` are matched through one chart.**  In a receiving model
expansion `R` to `ω₁`, two tuples `a`, `b` of `M` back-and-forth equivalent at `ω₁` in the base
language are the selections `x ∘ s`, `y ∘ s` along one selector `s` of covers `x`, `y` of one
stage type at `ω₁`.  Given-model statement.  Stated. -/
def ExistsCoverMatchOfBFEquivOmegaOneTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    ∀ ⦃n : ℕ⦄ (a b : Fin n → M), BFEquiv (L := baseLanguage.{0}) (ω₁ : Ordinal.{0}) n a b →
      ∃ (k : ℕ) (p : StageType.{0} ω₁ k) (x y : Fin k → M) (s : Fin n → Fin k),
        R.1.Covers p x ∧ R.1.Covers p y ∧ x ∘ s = a ∧ y ∘ s = b

/-- **Target: orbit ranks at most `ω₁` under exact receiving within the realized age.**  In a
receiving model expansion `R` to `ω₁` with exact receiving within its realized age, every tuple
has `r(a)` at most the lift of `ω₁`.  Given-model statement.  Stated. -/
def OrbitRankLeOmegaOneOfExactReceivingTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁), R.1.IsReceivingModel →
    R.1.ExactReceivingWithin (realizedAge R.1) →
      ∀ ⦃n : ℕ⦄ (a : Fin n → M),
        orbitRank (L := baseLanguage.{0}) a ≤ Ordinal.lift.{w} (ω₁ : Ordinal.{0})

/-- **Step 2: the exact-age comparison within the model.**  Matched tuples
(`ExistsCoverMatchOfBFEquivOmegaOneTarget`) are pairs of the rooted back-and-forth family of `R`
with itself for the realized age at the empty cores, hence equivalent at every level
(`Realization.CoverMatch.bfEquiv`). -/
theorem orbitRankLeOmegaOneOfExactReceivingTarget_of_coverMatch
    (h : ExistsCoverMatchOfBFEquivOmegaOneTarget.{w}) :
    OrbitRankLeOmegaOneOfExactReceivingTarget.{w} := by
  intro M _ R hR hex n a
  refine orbitRank_le_of_mem fun b hb γ ↦ ?_
  obtain ⟨k, p, x, y, s, hx, hy, rfl, rfl⟩ := h R hR a b hb.toOrdinalLift
  obtain ⟨p₀, hp₀⟩ := hR.1.exists_covers_zero
  have hage : ∀ ⦃m : ℕ⦄ (t : Fin m ↪ M) (ι : Fin 0 ↪ Fin m) (D : StageType.{0} ω₁ m),
      R.1.eval t = some D → ⇑t ∘ ι = ![] → D ∈ realizedAge R.1 m :=
    fun _ t _ D hD _ ↦ ⟨t, hD⟩
  have hr := hex.exactReceivingWithinAt (![] : Fin 0 → M)
  exact Realization.CoverMatch.bfEquiv R.2 R.2 hage hage hr hr hp₀ hp₀
    ⟨k, p, x, y, Function.Embedding.ofIsEmpty, s, hx, hy, funext fun i ↦ i.elim0,
      funext fun i ↦ i.elim0, rfl, rfl⟩ γ

/-- **`R(M)` is `ω₁` under exact receiving within the realized age**, given the upper bound
`OrbitRankLeOmegaOneOfExactReceivingTarget`; the lower bound is
`lift_omegaOne_le_iSup_orbitRank`. -/
theorem iSup_orbitRank_eq_omegaOne_of_exactReceiving
    (h : OrbitRankLeOmegaOneOfExactReceivingTarget.{w}) {M : Type w}
    [baseLanguage.{0}.Structure M] (R : ModelExpansion M ω₁) (hR : R.1.IsReceivingModel)
    (hex : R.1.ExactReceivingWithin (realizedAge R.1)) :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2) =
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) :=
  le_antisymm (iSup_orbitRank_le_iff.2 fun _ a ↦ h R hR hex a)
    (lift_omegaOne_le_iSup_orbitRank R hR)

end VaughtConjecture.ProcessRank
