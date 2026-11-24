/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Height.CanonicalSentence
import InfinitaryLogic.Scott.OrbitRank
import VaughtConjecture.MainTheorem.GrowthLevelRoute
import VaughtConjecture.MainTheorem.ReceivingDomains
import VaughtConjecture.MainTheorem.ReceivingRoute

/-!
# Receiving expansions at `ω₁` of the models of uncountable process rank

Companion programme over the density sentence, process rank `ω₁`.  Conventions as in
`VaughtConjecture.ProcessRank.RankConventions`: `r(a) = orbitRank a`,
`R(M) = sup_a (r(a))`.  The goal (`ExistsReceivingExpansionOfProcessRankTarget`, stated): every
model `M` of the density sentence, on a carrier in any universe, with `R(M)` at least the lift of
`ω₁`, has a model expansion to `ω₁` that is a receiving model.

**The hypothesis.**  `R(M) ≥ ω₁` is the same as uncountable process rank: an ordinal of
`Ordinal.{w}` below the lift of `ω₁` is the lift of a countable ordinal.  It holds whenever
`S(M) = internalScottRank M` is `ω₁` or `ω₁ + 1`
(`ProcessRank.iSup_orbitRank_eq_iff_of_isSuccLimit`).  Finite-cut receiving of every model, (R1),
is refuted in the repository and is not used.

**Route.**

1. The receiving expansion domains have countable complements below `ω₁`
   (`receivingExpansionDomain_compl_countable`, proved from compiled inputs): all but countably
   many isomorphism classes of models coded on `ℕ` have a receiving expansion to each countable
   block stage `λ_η`.
2. Countable exceptions (`ProcessRankLtOfCountableExceptionsTarget`, stated): if a sentence of
   `L_{ω₁,ω}` fails in only countably many classes of countable models of the density sentence,
   it holds in every model of uncountable process rank.  The input is that a model satisfying the
   Scott sentence of a countable model is potentially isomorphic to it
   (`PotentialIsoOfRealizeCanonicalScottSentenceTarget`, stated; InfinitaryLogic's
   `canonicalScottSentence_iff_potentialIso` assumes the second structure countable), and that
   potential isomorphism keeps `R(M)` (`ProcessRank.RanksLiftEqOfPotentialIsoTarget`).
3. At each countable `η` (`ExistsReceivingBlockExpansionOfProcessRankTarget`, stated): a model
   of uncountable process rank has a receiving expansion to `λ_η`.  Either through one sentence of
   `L_{ω₁,ω}` asserting that the chart readings of the block formulas form a receiving model at
   `λ_η`, or through countable substructures elementary for a countable fragment containing the
   density sentence, the chart formulas at `λ_η` and the Scott sentences of the exceptional
   countable models: such a substructure containing given parameters omits the exceptions, so has
   a receiving expansion to `λ_η`, and its chart readings agree with those of the ambient formulas.
4. Gluing at the stage `ω₁` itself
   (`ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt_of_le`, proved; the limit
   existence lemma of `VaughtConjecture.MainTheorem.ReceivingDomains` with `δ ≤ ω₁` in place of
   `δ < ω₁`), with next-block uniqueness of receiving models from forcing
   donors (compiled), and `λ_{ω₁} = ω₁` (`blockStage_omegaOne`, proved).  Step 3 gives the goal
   (`existsReceivingExpansionOfProcessRankTarget_of_block`, proved).

**Results.**

* `blockStage_omegaOne`, `ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt_of_le`,
  `exists_isReceivingModel_of_forall_blockStage`, `receivingExpansionDomain_compl_countable`
  (proved).
* `PotentialIsoOfRealizeCanonicalScottSentenceTarget`, `ProcessRankLtOfCountableExceptionsTarget`,
  `ExistsReceivingBlockExpansionOfProcessRankTarget`, `ExistsReceivingExpansionOfProcessRankTarget`
  (stated), with `existsReceivingExpansionOfProcessRankTarget_of_block` (proved from step 3).
-/

universe u v w w'

namespace VaughtConjecture.ProcessRank

open Ordinal _root_.Order FirstOrder Language Expansion

/-! ### Gluing at `ω₁` itself -/

/-- The block stage of index `ω₁` is `ω₁`: `ω` and `ω₁` are below `ω₁`, which is closed under
ordinal multiplication and addition. -/
theorem blockStage_omegaOne : blockStage (ω₁ : Ordinal.{u}) = ω₁ := by
  have hω : ω < (ω₁ : Ordinal.{u}) := omega0_lt_omega_one
  rw [blockStage, isPrincipal_mul_iff_mul_left_eq.1 (isPrincipal_mul_omega 1) ω omega0_pos hω,
    isPrincipal_add_iff_add_left_eq_self.1 (isPrincipal_add_omega 1) ω hω]

variable {M : Type w} [baseLanguage.{0}.Structure M]

/-- **Limit existence for receiving expansions, up to `ω₁` inclusive**, given next-block
uniqueness of receiving models: for a nonzero limit `δ ≤ ω₁`, a base structure with a receiving
model expansion to every `λ_ξ`, `ξ < δ`, has one to `λ_δ`.  The proof of
`ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt` uses `δ < ω₁` only to see that the
earlier indices are countable. -/
theorem ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt_of_le
    (hu : ReceivingNextBlockUniqueness.{w}) {δ : Ordinal.{0}} (hδ : IsSuccLimit δ)
    (hδω : δ ≤ ω₁)
    (h : ∀ ξ < δ, ∃ e : ModelExpansion M (blockStage ξ), e.1.HasFiniteCutReceiving) :
    ∃ e : ModelExpansion M (blockStage δ), e.1.HasFiniteCutReceiving := by
  choose e he using h
  have hcoh : ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ) (h : ζ ≤ ξ), (e ξ hξ).reduceBlock h = e ζ hζ :=
    fun ζ hζ ξ hξ h ↦ ModelExpansion.eq_of_hasFiniteCutReceiving hu (hζ.trans_le hδω)
      (ModelExpansion.hasFiniteCutReceiving_reduceBlock (he ξ hξ) h) (he ζ hζ)
  refine ⟨ModelExpansion.glue hδ e hcoh,
    Realization.hasFiniteCutReceiving_of_forall_reduce_blockStage hδ fun ξ hξ ↦ ?_⟩
  have h1 := congrArg Subtype.val (ModelExpansion.glue_reduceBlock (hδ := hδ) hcoh hξ)
  rw [ModelExpansion.reduceBlock_val] at h1
  rw [h1]
  exact he ξ hξ

/-- **A receiving expansion at `ω₁` from receiving expansions at the countable block stages**:
the gluing at `δ = ω₁`, with next-block uniqueness of receiving models from forcing donors
(`Expansion.ReceivingNextBlockUniqueness.of_forcingDonors`, `forcingDonors_blockStage`), and
`λ_{ω₁} = ω₁`. -/
theorem exists_isReceivingModel_of_forall_blockStage
    (h : ∀ η < (ω₁ : Ordinal.{0}), ∃ e : ModelExpansion M (blockStage η),
      e.1.HasFiniteCutReceiving) :
    ∃ R : ModelExpansion M ω₁, R.1.IsReceivingModel := by
  have hu : ReceivingNextBlockUniqueness.{w} :=
    ReceivingNextBlockUniqueness.of_forcingDonors fun ξ _ ↦ forcingDonors_blockStage ξ
  obtain ⟨e, he⟩ := ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt_of_le hu
    (Cardinal.isSuccLimit_omega 1) le_rfl h
  have key : ∀ {α : Ordinal.{0}} (_ : α = ω₁) (e : ModelExpansion M α),
      e.1.HasFiniteCutReceiving → ∃ R : ModelExpansion M ω₁, R.1.IsReceivingModel := by
    rintro _ rfl e he
    exact ⟨e, e.2.isModel, he⟩
  exact key blockStage_omegaOne e he

/-! ### Countable exceptions -/

/-- **The receiving expansion domains have countable complements below `ω₁`**: countable losses
of the receiving expansion domains (`MainTheorem.receivingExpansionDomains_hasCountableLosses`)
with its compiled inputs (the cap-to-model theorem, forcing donors, the coface instances, and
(R2), (R3), (R4) for receiving models), and `MainTheorem.ExpansionDomains.compl_countable`. -/
theorem receivingExpansionDomain_compl_countable {η : Ordinal.{0}} (hη : η < ω₁) :
    (receivingExpansionDomain η)ᶜ.Countable := by
  have hu : ReceivingNextBlockUniqueness.{0} :=
    ReceivingNextBlockUniqueness.of_forcingDonors fun ξ _ ↦ forcingDonors_blockStage ξ
  exact (MainTheorem.receivingExpansionDomains MainTheorem.capToModel hu).compl_countable
    (MainTheorem.receivingExpansionDomains_hasCountableLosses MainTheorem.capToModel hu
      (fun ξ _ ↦ MainTheorem.hasNonemptyCofaceInstances_blockStage_add_one ξ)
      Expansion.receivingStableCappedReceiving_levels
      Realization.receivingResidualReceiving_of_padded Realization.hollowReceiving_levels) hη

/-- **Target: a structure satisfying the canonical Scott sentence of a countable structure is
potentially isomorphic to it.**  For a relational language with countably many relation symbols,
a countable structure `C` and a structure `N` of any cardinality, on carriers in any two
universes: if `N` satisfies the canonical Scott sentence of `C`, there is a potential isomorphism
between `C` and `N`.  InfinitaryLogic's `canonicalScottSentence_iff_potentialIso` assumes `N`
countable; the route for arbitrary `N` passes to countable substructures of `N` elementary for a
countable fragment containing the Scott formulas of the tuples of `C`.  Stated. -/
def PotentialIsoOfRealizeCanonicalScottSentenceTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] [Countable (Σ l, L.Relations l)] ⦃C : Type w⦄
    [L.Structure C] [Countable C] ⦃N : Type w'⦄ [L.Structure N],
    (canonicalScottSentence (L := L) C).realize_as_sentence N → Nonempty (PotentialIso L C N)

/-- **Target: countable exceptions.**  If a sentence `ψ` of `L_{ω₁,ω}` in the base language fails
in only countably many isomorphism classes of models of the density sentence coded on `ℕ`, then
`ψ` holds in every model of the density sentence, on a carrier in any universe, with
`R(M) = sup_a (r(a))` at least the lift of `ω₁`.  Route: a model failing `ψ` has a countable
substructure, elementary for a countable fragment containing the density sentence, `ψ` and the
Scott sentences of the exceptional classes, which is isomorphic to an exceptional model; so the
model satisfies the Scott sentence of a countable model, is potentially isomorphic to it
(`PotentialIsoOfRealizeCanonicalScottSentenceTarget`), and has countable process rank.
Given-model statement.  Stated. -/
def ProcessRankLtOfCountableExceptionsTarget : Prop :=
  ∀ ψ : baseLanguage.{0}.Sentenceω,
    (Quotient.mk (isoSetoid baseLanguage.densitySentence.{0}) ''
      {c | c.1 ∉ ModelsOf ψ}).Countable →
    ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M],
      Sentenceω.Realize baseLanguage.densitySentence.{0} M →
      Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤
        (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2) →
      Sentenceω.Realize ψ M

/-! ### The reconstruction -/

/-- **Target: receiving expansions to the countable block stages.**  A model of the density
sentence, on a carrier in any universe, with `R(M) = sup_a (r(a))` at least the lift of `ω₁`,
has, at every countable block index `η`, a model expansion to `λ_η` with the finite-cut receiving
property.  Given-model statement.  Stated. -/
def ExistsReceivingBlockExpansionOfProcessRankTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M],
    Sentenceω.Realize baseLanguage.densitySentence.{0} M →
    Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤
      (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2) →
    ∀ ⦃η : Ordinal.{0}⦄, η < ω₁ →
      ∃ e : ModelExpansion M (blockStage η), e.1.HasFiniteCutReceiving

/-- **Target: the reconstruction.**  A model of the density sentence, on a carrier in any
universe, with `R(M) = sup_a (r(a))` at least the lift of `ω₁`, has a model expansion to `ω₁`
that is a receiving model.  Given-model statement.  Stated. -/
def ExistsReceivingExpansionOfProcessRankTarget : Prop :=
  ∀ ⦃M : Type w⦄ [baseLanguage.{0}.Structure M],
    Sentenceω.Realize baseLanguage.densitySentence.{0} M →
    Ordinal.lift.{w} (ω₁ : Ordinal.{0}) ≤
      (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := baseLanguage.{0}) x.2) →
    ∃ R : ModelExpansion M ω₁, R.1.IsReceivingModel

/-- **The reconstruction from the countable block stages**: the receiving expansions to the
countable block stages glue to one at `ω₁` (`exists_isReceivingModel_of_forall_blockStage`). -/
theorem existsReceivingExpansionOfProcessRankTarget_of_block
    (h : ExistsReceivingBlockExpansionOfProcessRankTarget.{w}) :
    ExistsReceivingExpansionOfProcessRankTarget.{w} :=
  fun _ _ hΦ hR ↦ exists_isReceivingModel_of_forall_blockStage fun _ hη ↦ h hΦ hR hη

end VaughtConjecture.ProcessRank
