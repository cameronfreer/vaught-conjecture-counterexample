/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Losses
import VaughtConjecture.Expansion.ReceivingAgreement
import VaughtConjecture.Expansion.ReceivingModels
import VaughtConjecture.MainTheorem.Assembly

/-!
# The receiving expansion domains of the density sentence

Roadmap, the reduction of the main theorem to expansion domains (conditions 1–3), Layers 4–5, for
the auxiliary class `𝒞_α` of receiving models (`Realization.IsReceivingModel`); semantic contract,
items 5, 8, 9 and 12.

**The receiving expansion domains.**  The **receiving expansion domain** at `η`
(`Expansion.receivingExpansionDomain`) is the set of classes of models of the density sentence
coded on `ℕ` with a code whose structure has a model expansion to `λ_η` with the finite-cut
receiving property.  It is contained in the expansion domain at `η`
(`Expansion.receivingExpansionDomain_subset`).  The clauses of `ExpansionDomains`:
* `zero`, conditional on the cap-to-model theorem at `ω` on `ℕ`
  (`Expansion.receivingExpansionDomain_zero`): the model expansion to `λ_0 = ω` is the realization
  of the base structure, which receives because the density sentence says so
  (`ModelExpansion.hasFiniteCutReceiving_blockStage_zero`);
* `antitone`, unconditional: receiving descends along reduction
  (`ModelExpansion.hasFiniteCutReceiving_reduceBlock`);
* `limit`, conditional on next-block uniqueness of receiving models
  (`Expansion.biInter_receivingExpansionDomain_subset`): the receiving expansions below a limit
  are coherent by uniqueness of receiving expansions, glue to a model expansion, and the glued
  expansion receives by the receiving-limit lemma
  (`ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt`);
* emptiness at and above `ω₁`, unconditional.
These form `MainTheorem.receivingExpansionDomains hcap hu`.

**Logical agreement** (`MainTheorem.receivingExpansionDomains_hasLogicalAgreement`), with no
hypothesis beyond those of the domains: the receiving expansion-match data
(`Expansion.realize_iff_of_receivingModelExpansions`).

**Countable losses** (`Expansion.receivingExpansionDomain_loss_countable`).  Every receiving
expansion of a class in the loss at `ξ` is receiving-terminal at `ξ`
(`ModelExpansion.isReceivingTerminalAt_of_mem_receivingLoss`).  Under the continuation criterion
for receiving models, a receiving-terminal receiving model has a terminal property
(`Realization.exists_hasTerminalProperty_of_isReceivingTerminalAt`): with unbounded growth it is
cover-hollow (`Realization.IsReceivingTerminalAt.isCoverHollow`), and otherwise it has a globally
rigid core or is residual, as for models.  Two receiving expansions sharing a terminal property
have isomorphic base structures
(`ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_hasFiniteCutReceiving`):
* the rigid-core comparison takes finite-extension receiving of the two given expansions, which
  they have; (R1) is not used;
* the residual comparison takes **(R2) for receiving models**
  (`Realization.ReceivingResidualReceiving`, the statement of `Realization.ResidualReceiving`
  asked only of models with finite-cut receiving);
* the hollow comparison takes **(R3) for receiving models**: `Realization.HollowReceiving` for the
  predicate `Realization.IsReceivingCoverHollowAtBlock` (cover-hollow at a block stage, with
  finite-cut receiving), an instance of the existing parametrized statement.
(R2) and (R3) give their receiving forms (`Realization.ResidualReceiving.receiving`,
`Realization.HollowReceiving.receiving`); the converses are not claimed.

**Receiving-terminal classes** (`MainTheorem.receivingTerminalClasses`): the classes with a
receiving expansion to `λ_β` that is receiving-terminal at `β`; countable at every countable `β`
under the same hypotheses (`MainTheorem.countable_receivingTerminalClasses`).

**Status.**  Proved from the explicit hypotheses named: the cap-to-model theorem at `ω` (first
domain), next-block uniqueness of receiving models (limit clause), the continuation criterion for
receiving models, (R2) and (R3) for receiving models (countable losses).  (R1) is not used.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage Expansion

/-! ### Receiving model expansions -/

section ModelExpansion

variable {M : Type w} [baseLanguage.{0}.Structure M]

/-- Transport along an isomorphism of base structures keeps finite-cut receiving. -/
theorem ModelExpansion.hasFiniteCutReceiving_map_iff {N : Type w}
    [baseLanguage.{0}.Structure N] {α : Ordinal.{0}} (f : ModelExpansion M α)
    (e : M ≃[baseLanguage.{0}] N) :
    (f.map e).1.HasFiniteCutReceiving ↔ f.1.HasFiniteCutReceiving := by
  rw [ModelExpansion.map_val]
  exact Realization.hasFiniteCutReceiving_map_iff _

/-- **Receiving at `λ_0`**: every model expansion to `λ_0 = ω` of a model of the density sentence
has finite-cut receiving.  It is the realization of its base structure
(`ModelExpansion.val_eq_toRealization`), which receives by the density sentence
(`realize_densitySentence_iff`). -/
theorem ModelExpansion.hasFiniteCutReceiving_blockStage_zero
    (hM : densitySentence.{0}.Realize M) (e : ModelExpansion M (blockStage 0)) :
    e.1.HasFiniteCutReceiving := by
  have key : ∀ {α : Ordinal.{0}} (_ : α = ω) (e : ModelExpansion M α),
      e.1.HasFiniteCutReceiving := by
    rintro _ rfl e
    rw [e.val_eq_toRealization]
    exact ((realize_densitySentence_iff M).mp hM).2.2.2.2
  exact key blockStage_zero e

/-- **Limit existence for receiving expansions**, given next-block uniqueness of receiving models:
for a nonzero limit `δ < ω₁`, a base structure with a receiving model expansion to every `λ_ξ`,
`ξ < δ`, has one to `λ_δ`.  The chosen expansions are coherent by uniqueness of receiving
expansions (`ModelExpansion.eq_of_hasFiniteCutReceiving`); they glue to a model expansion
(`ModelExpansion.glue`), which receives by the receiving-limit lemma
(`Realization.hasFiniteCutReceiving_of_forall_reduce_blockStage`). -/
theorem ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt
    (hu : ReceivingNextBlockUniqueness.{w}) {δ : Ordinal.{0}} (hδ : Order.IsSuccLimit δ)
    (hδω : δ < ω₁)
    (h : ∀ ξ < δ, ∃ e : ModelExpansion M (blockStage ξ), e.1.HasFiniteCutReceiving) :
    ∃ e : ModelExpansion M (blockStage δ), e.1.HasFiniteCutReceiving := by
  choose e he using h
  have hcoh : ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ) (h : ζ ≤ ξ), (e ξ hξ).reduceBlock h = e ζ hζ :=
    fun ζ hζ ξ hξ h ↦ ModelExpansion.eq_of_hasFiniteCutReceiving hu (hζ.trans hδω)
      (ModelExpansion.hasFiniteCutReceiving_reduceBlock (he ξ hξ) h) (he ζ hζ)
  refine ⟨ModelExpansion.glue hδ e hcoh,
    Realization.hasFiniteCutReceiving_of_forall_reduce_blockStage hδ fun ξ hξ ↦ ?_⟩
  have h1 := congrArg Subtype.val (ModelExpansion.glue_reduceBlock (hδ := hδ) hcoh hξ)
  rw [ModelExpansion.reduceBlock_val] at h1
  rw [h1]
  exact he ξ hξ

end ModelExpansion

/-! ### The receiving expansion domains -/

namespace Expansion

/-- The **receiving expansion domain** at `η`: the classes of models of the density sentence coded
on `ℕ` with a coded representative whose structure has a model expansion to `λ_η` with the
finite-cut receiving property. -/
def receivingExpansionDomain (η : Ordinal.{0}) : Set (Quotient (isoSetoid densitySentence.{0})) :=
  {q | ∃ c : ModelsOf densitySentence.{0}, Quotient.mk _ c = q ∧
    ∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage η), e.1.HasFiniteCutReceiving}

/-- **Membership up to isomorphism**: a class is in the receiving expansion domain at `η` exactly
when the structure of a given code of it has a receiving model expansion to `λ_η`. -/
theorem mem_receivingExpansionDomain_iff {η : Ordinal.{0}} (c : ModelsOf densitySentence.{0}) :
    Quotient.mk _ c ∈ receivingExpansionDomain η ↔
      ∃ e : @ModelExpansion ℕ c.1.toStructure (blockStage η), e.1.HasFiniteCutReceiving := by
  refine ⟨fun ⟨c', hc', e, he⟩ ↦ ?_, fun h ↦ ⟨c, rfl, h⟩⟩
  obtain ⟨i⟩ := (isoSetoid_r_iff (c₁ := c') (c₂ := c)).mp (Quotient.exact hc')
  exact ⟨@ModelExpansion.map ℕ c'.1.toStructure _ ℕ c.1.toStructure e i,
    (@ModelExpansion.hasFiniteCutReceiving_map_iff ℕ c'.1.toStructure ℕ c.1.toStructure _ e i).mpr
      he⟩

/-- The receiving expansion domain is contained in the expansion domain. -/
theorem receivingExpansionDomain_subset (η : Ordinal.{0}) :
    receivingExpansionDomain η ⊆ expansionDomain η :=
  fun _ ⟨c, hc, e, _⟩ ↦ ⟨c, hc, ⟨e⟩⟩

/-- **The receiving expansion domains decrease**: a receiving expansion reduces to a receiving
expansion (`ModelExpansion.hasFiniteCutReceiving_reduceBlock`). -/
theorem receivingExpansionDomain_antitone : Antitone receivingExpansionDomain := by
  rintro _ _ h _ ⟨c, hc, e, he⟩
  let := c.1.toStructure
  exact ⟨c, hc, e.reduceBlock h, ModelExpansion.hasFiniteCutReceiving_reduceBlock he h⟩

/-- The receiving expansion domains are empty at and above `ω₁`. -/
theorem receivingExpansionDomain_eq_empty {η : Ordinal.{0}} (h : ω₁ ≤ η) :
    receivingExpansionDomain η = ∅ :=
  Set.subset_eq_empty (receivingExpansionDomain_subset η) (expansionDomain_eq_empty h)

/-- **The receiving domain at `0` is every class**, conditional on the cap-to-model theorem at
`ω` on `ℕ` (`hcap`, unbundled as in `expansionDomain_zero`): the expansion to `λ_0` receives by
the density sentence. -/
theorem receivingExpansionDomain_zero
    (hcap : ∀ R : Realization.{0, 0} ω ℕ, Nonempty ℕ → R.HasLegalTypes → R.IsConsistent →
      R.IsCovering → R.HasFiniteCutReceiving → R.IsModel) :
    receivingExpansionDomain 0 = Set.univ :=
  Set.eq_univ_of_forall fun q ↦ Quotient.inductionOn q fun c ↦ by
    let := c.1.toStructure
    obtain ⟨e⟩ := (mem_expansionDomain_iff c).mp
      ((expansionDomain_zero hcap).symm ▸ Set.mem_univ (Quotient.mk _ c))
    exact (mem_receivingExpansionDomain_iff c).mpr
      ⟨e, e.hasFiniteCutReceiving_blockStage_zero c.2⟩

/-- **The limit clause of the receiving expansion domains**, given next-block uniqueness of
receiving models: at a nonzero limit `l < ω₁`, the receiving domain at `l` contains the
intersection of the earlier ones (`ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt`). -/
theorem biInter_receivingExpansionDomain_subset (hu : ReceivingNextBlockUniqueness.{0})
    {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hlω : l < ω₁) :
    (⋂ ξ < l, receivingExpansionDomain ξ) ⊆ receivingExpansionDomain l := by
  intro q hq
  induction q using Quotient.inductionOn with
  | h c =>
    simp only [Set.mem_iInter] at hq
    let := c.1.toStructure
    exact (mem_receivingExpansionDomain_iff c).mpr
      (ModelExpansion.exists_hasFiniteCutReceiving_of_forall_lt hu hl hlω
        fun ξ hξ ↦ (mem_receivingExpansionDomain_iff c).mp (hq ξ hξ))

end Expansion

/-! ### Terminal properties of receiving-terminal receiving models -/

namespace Realization

section Terminal

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **The cover of the receiving-terminal receiving models**: under the continuation criterion for
receiving models, every receiving model at `λ_ξ`, `ξ < ω₁`, that is receiving-terminal at `ξ` has
some terminal property.  With unbounded growth it is cover-hollow
(`IsReceivingTerminalAt.isCoverHollow`); with top-grade supremum `K` it has a globally rigid core
or is residual, as in `exists_hasTerminalProperty`. -/
theorem exists_hasTerminalProperty_of_isReceivingTerminalAt
    (hcont : ReceivingContinuationCriterion.{w}) (hξ : ξ < ω₁) (hR : R.IsReceivingModel)
    (ht : R.IsReceivingTerminalAt ξ) : ∃ P, R.HasTerminalProperty P := by
  by_cases htop : R.topGradeSup = ⊤
  · exact ⟨.inr (.inr ()), ht.isCoverHollow hcont hξ hR htop, htop⟩
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp htop
  by_cases hcore : ∃ (k : ℕ) (p : StageType.{0} (blockStage ξ) k) (c : Fin k → M),
      R.Covers p c ∧ R.IsGloballyRigidCore c
  · obtain ⟨k, p, hp⟩ := hcore
    exact ⟨.inl ⟨k, p⟩, hp⟩
  · exact ⟨.inr (.inl K), hcore, hK.symm⟩

end Terminal

/-! ### (R2) and (R3) for receiving models -/

/-- **Exact residual receiving for receiving models**: the statement of `ResidualReceiving`, (R2)
of the table of Layer 3, asked only of models with the finite-cut receiving property. -/
structure ReceivingResidualReceiving : Prop where
  /-- Over every cover, every one-point coface of top grade at most `K` is received exactly. -/
  exists_covers ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄ ⦃K : ℕ⦄ :
    Order.IsSuccLimit α → R.IsModel → R.HasFiniteCutReceiving →
      (¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
        R.IsGloballyRigidCore c) →
      R.topGradeSup = K → ∀ ⦃n : ℕ⦄ (t : StageType.{u} α n) (c : Fin n → M), R.Covers t c →
        ∀ D ∈ t.cofaces, D.topGrade ≤ K → ∃ y : M, R.Covers D (Fin.snoc c y)

/-- (R2) gives its form for receiving models. -/
theorem ResidualReceiving.receiving (h : ResidualReceiving.{u, w}) :
    ReceivingResidualReceiving.{u, w} :=
  ⟨fun _ _ _ _ hα hR _ ↦ h.exists_covers hα hR⟩

/-- **Cover-hollow receiving realizations at a block stage**: cover-hollowness at a block stage
together with the finite-cut receiving property.  (R3) for receiving models is `HollowReceiving`
for this predicate. -/
def IsReceivingCoverHollowAtBlock {α : Ordinal.{u}} {M : Type w} (R : Realization.{u, w} α M) :
    Prop :=
  R.IsCoverHollowAtBlock ∧ R.HasFiniteCutReceiving

/-- (R3) for cover-hollowness at a block stage gives (R3) for receiving models. -/
theorem HollowReceiving.receiving (h : HollowReceiving.{u, w} IsCoverHollowAtBlock) :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  ⟨fun _ _ _ hα hR hH ↦ h.exists_covers hα hR hH.1⟩

section Comparison

variable {α : Ordinal.{u}} {M N : Type w} [baseLanguage.{u}.Structure M]
  [baseLanguage.{u}.Structure N] [Countable M] [Countable N] {R : Realization.{u, w} α M}
  {R' : Realization.{u, w} α N}

/-- **The residual comparison for receiving expansions**, under (R2) for receiving models: two
expansions of countable base structures at a limit stage, with finite-cut receiving, no cover
that is a globally rigid core, and the same top-grade supremum `K`, have isomorphic base
structures.  The argument is that of `nonempty_equiv_of_residual`: one-point exact receiving
within the legal types of top grade at most `K`, from the empty covers. -/
theorem nonempty_equiv_of_receivingResidual (hres : ReceivingResidualReceiving.{u, w})
    (hα : Order.IsSuccLimit α) (he : R.IsExpansionOf) (he' : R'.IsExpansionOf)
    (hr : R.HasFiniteCutReceiving) (hr' : R'.HasFiniteCutReceiving)
    (hcore : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M), R.Covers p c ∧
      R.IsGloballyRigidCore c)
    (hcore' : ¬ ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → N), R'.Covers p c ∧
      R'.IsGloballyRigidCore c)
    {K : ℕ} (hK : R.topGradeSup = K) (hK' : R'.topGradeSup = K) :
    Nonempty (M ≃[baseLanguage.{u}] N) := by
  have hA : ∀ ⦃m k : ℕ⦄ (D : StageType.{u} α m) (f : Fin k ↪ Fin m) (p : StageType.{u} α k),
      D ∈ {D : StageType.{u} α m | D.IsLegal ∧ D.topGrade ≤ K} →
        StageType.restrictFace f D = some p → p ∈ {p : StageType.{u} α k | p.IsLegal ∧
          p.topGrade ≤ K} :=
    fun _ _ _ _ _ hD hf ↦ StageType.isLegal_and_topGrade_le_of_restrictFace hD hf
  obtain ⟨p, hp⟩ := he.isModel.exists_covers_zero
  obtain ⟨p', hp'⟩ := he'.isModel.exists_covers_zero
  refine nonempty_equiv_of_exactReceivingWithin (A := fun _ ↦ {D | D.IsLegal ∧ D.topGrade ≤ K})
    he he' (fun _ _ _ hs ↦ he.isModel.isLegal_and_topGrade_le hK hs)
    (fun _ _ _ hs ↦ he'.isModel.isLegal_and_topGrade_le hK' hs)
    (.of_one_point he.isModel.isConsistent hA fun _ t c hc D hD hDt ↦ ?_)
    (.of_one_point he'.isModel.isConsistent hA fun _ t c hc D hD hDt ↦ ?_) hp
    (StageType.eq_of_zero p' p ▸ hp')
  · obtain ⟨y, hy⟩ := hres.exists_covers hα he.isModel hr hcore hK t c hc D ⟨hD.1, hDt⟩ hD.2
    exact ⟨Fin.snoc c y, hy, Fin.snoc_comp_castSucc⟩
  · obtain ⟨y, hy⟩ := hres.exists_covers hα he'.isModel hr' hcore' hK' t c hc D ⟨hD.1, hDt⟩ hD.2
    exact ⟨Fin.snoc c y, hy, Fin.snoc_comp_castSucc⟩

end Comparison

end Realization

/-! ### Comparison of receiving expansions sharing a terminal property -/

open Realization in
/-- **Two receiving model expansions sharing a terminal property have isomorphic base
structures**, for countable carriers at `λ_ξ`, `ξ < ω₁`: the rigid-core comparison with the
receiving of the two expansions (no (R1)), the residual comparison under (R2) for receiving models
(`hres`), and the hollow comparison under (R3) for receiving models (`hhol`). -/
theorem ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_hasFiniteCutReceiving
    {M N : Type w} [baseLanguage.{0}.Structure M] [baseLanguage.{0}.Structure N] [Countable M]
    [Countable N] (hres : ReceivingResidualReceiving.{0, w})
    (hhol : HollowReceiving.{0, w} IsReceivingCoverHollowAtBlock) {ξ : Ordinal.{0}}
    {P : TerminalProperty ξ} (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion N (blockStage ξ)) (he : e.1.HasFiniteCutReceiving)
    (he' : e'.1.HasFiniteCutReceiving) (h : e.1.HasTerminalProperty P)
    (h' : e'.1.HasTerminalProperty P) : Nonempty (M ≃[baseLanguage.{0}] N) := by
  have hα := isSuccLimit_blockStage ξ
  rcases P with ⟨_, p⟩ | K | ⟨⟩
  · obtain ⟨x, hx, hcx⟩ := h
    obtain ⟨y, hy, hcy⟩ := h'
    exact nonempty_equiv_of_isGloballyRigidCore hα e.2 e'.2
      (ModelExpansion.hasFiniteExtensionReceiving_of_hasFiniteCutReceiving he)
      (ModelExpansion.hasFiniteExtensionReceiving_of_hasFiniteCutReceiving he') hx hy hcx hcy
  · exact nonempty_equiv_of_receivingResidual hres hα e.2 e'.2 he he' h.1 h'.1 h.2 h'.2
  · exact nonempty_equiv_of_hollow hhol hα e.2 e'.2 ⟨⟨ξ, rfl, h.1⟩, he⟩ ⟨⟨ξ, rfl, h'.1⟩, he'⟩
      h.2 h'.2

/-- **Receiving expansions of a class in the receiving loss are receiving-terminal**: every
receiving model expansion to `λ_ξ` of a code whose class lies in the receiving loss at `ξ` is
receiving-terminal at `ξ`.  A receiving model at `λ_{ξ+1}` reducing to it would be a receiving
model expansion of the same code.  Unconditional. -/
theorem ModelExpansion.isReceivingTerminalAt_of_mem_receivingLoss {ξ : Ordinal.{0}}
    {c : ModelsOf densitySentence.{0}}
    (hq : Quotient.mk _ c ∈ receivingExpansionDomain ξ \ receivingExpansionDomain (ξ + 1))
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage ξ)) : e.1.IsReceivingTerminalAt ξ := by
  let := c.1.toStructure
  intro R' hR' heq
  refine hq.2 ((mem_receivingExpansionDomain_iff c).mpr ⟨⟨R', hR'.1, ?_⟩, hR'.2⟩)
  rw [← R'.reduce_reduce (isSuccPrelimit_blockStage ξ) Ordinal.isSuccLimit_omega0.isSuccPrelimit
    (omega0_le_blockStage ξ), heq]
  exact e.2.toStructure_reduce

namespace Expansion

open Realization

/-- **At most one class per terminal property among receiving expansions**: for `ξ < ω₁`, the
classes with a code having a receiving model expansion to `λ_ξ` with the terminal property `P`
form a subsingleton, under (R2) and (R3) for receiving models. -/
theorem subsingleton_receivingClasses_of_property (hres : ReceivingResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsReceivingCoverHollowAtBlock) {ξ : Ordinal.{0}}
    (P : TerminalProperty ξ) :
    {q : Quotient (isoSetoid densitySentence.{0}) | ∃ (c : ModelsOf densitySentence.{0})
      (e : @ModelExpansion ℕ c.1.toStructure (blockStage ξ)),
        Quotient.mk _ c = q ∧ e.1.HasFiniteCutReceiving ∧
          e.1.HasTerminalProperty P}.Subsingleton := by
  rintro _ ⟨c, e, rfl, he, h⟩ _ ⟨c', e', rfl, he', h'⟩
  obtain ⟨i⟩ := @ModelExpansion.nonempty_equiv_of_hasTerminalProperty_of_hasFiniteCutReceiving ℕ ℕ
    c.1.toStructure c'.1.toStructure _ _ hres hhol ξ P e e' he he' h h'
  exact Quotient.sound (isoSetoid_r_iff.mpr ⟨i⟩)

/-- **The successor losses of the receiving expansion domains are countable**, under the
continuation criterion for receiving models (`hcont`) and (R2) (`hres`) and (R3) (`hhol`) for
receiving models.  (R1) is not used. -/
theorem receivingExpansionDomain_loss_countable (hcont : ReceivingContinuationCriterion.{0})
    (hres : ReceivingResidualReceiving.{0, 0})
    (hhol : HollowReceiving.{0, 0} IsReceivingCoverHollowAtBlock) :
    ∀ ξ < ω₁, (receivingExpansionDomain ξ \ receivingExpansionDomain (ξ + 1)).Countable := by
  intro ξ hξ
  have := countable_terminalProperty hξ
  refine Counting.countable_of_subsingleton_cover _
    (subsingleton_receivingClasses_of_property (ξ := ξ) hres hhol) fun q hq ↦ ?_
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e, he⟩ := (mem_receivingExpansionDomain_iff c).mp hq.1
  obtain ⟨P, hP⟩ := exists_hasTerminalProperty_of_isReceivingTerminalAt hcont hξ ⟨e.2.isModel, he⟩
    (e.isReceivingTerminalAt_of_mem_receivingLoss hq)
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, he, hP⟩

end Expansion

/-! ### The receiving expansion domains as expansion domains -/

namespace MainTheorem

/-- **The receiving expansion domains of the density sentence**: the domain at `η` is
`Expansion.receivingExpansionDomain η`.  The first domain is every class conditional on the
cap-to-model theorem (`hcap`), and the limit clause is conditional on next-block uniqueness of
receiving models (`hu`; from forcing donors alone,
`Expansion.ReceivingNextBlockUniqueness.of_forcingDonors`). -/
def receivingExpansionDomains (hcap : CapToModel.{0}) (hu : ReceivingNextBlockUniqueness.{0}) :
    ExpansionDomains DensityClass where
  domain := receivingExpansionDomain
  zero := receivingExpansionDomain_zero fun R ↦ hcap.isModel R
  antitone := receivingExpansionDomain_antitone
  limit _ hl hlω := biInter_receivingExpansionDomain_subset hu hl hlω
  domain_eq_empty_of_omega_one_le _ h := receivingExpansionDomain_eq_empty h

/-- The domains of `receivingExpansionDomains` are the receiving expansion domains. -/
@[simp] theorem receivingExpansionDomains_domain (hcap : CapToModel.{0})
    (hu : ReceivingNextBlockUniqueness.{0}) :
    (receivingExpansionDomains hcap hu).domain = receivingExpansionDomain :=
  rfl

/-- **Logical agreement of the receiving expansion domains**: classes in the receiving domain at
`η` agree on the sentences of quantifier rank at most `η`
(`Expansion.realize_iff_of_receivingModelExpansions`).  (R1) is not used. -/
theorem receivingExpansionDomains_hasLogicalAgreement (hcap : CapToModel.{0})
    (hu : ReceivingNextBlockUniqueness.{0}) :
    (receivingExpansionDomains hcap hu).HasLogicalAgreement densityTruth :=
  ExpansionDomains.HasLogicalAgreement.of_qrank_le fun η hη p hp q hq θ hθ ↦ by
    obtain ⟨c₁, rfl, h₁⟩ := hp
    obtain ⟨c₂, rfl, h₂⟩ := hq
    rw [densityTruth, classTruth_mk, classTruth_mk]
    -- membership in `ModelsOf θ` is the realization of `θ` in the structure of the code
    exact @realize_iff_of_receivingModelExpansions ℕ ℕ c₁.1.toStructure c₂.1.toStructure η hη h₁
      h₂ θ hθ

/-- The **receiving-terminal classes at `β`**: the classes with a code whose structure has a
receiving model expansion to `λ_β` that is receiving-terminal at `β`. -/
def receivingTerminalClasses (β : Ordinal.{0}) : Set DensityClass :=
  {q | ∃ (c : ModelsOf densitySentence.{0})
    (e : @ModelExpansion ℕ c.1.toStructure (blockStage β)),
      Quotient.mk _ c = q ∧ e.1.HasFiniteCutReceiving ∧ e.1.IsReceivingTerminalAt β}

/-- **Receiving losses are receiving-terminal classes.**  Unconditional. -/
theorem receivingLoss_subset_receivingTerminalClasses (ξ : Ordinal.{0}) :
    receivingExpansionDomain ξ \ receivingExpansionDomain (ξ + 1) ⊆ receivingTerminalClasses ξ := by
  intro q hq
  obtain ⟨c, rfl⟩ := Quotient.mk_surjective q
  let := c.1.toStructure
  obtain ⟨e, he⟩ := (mem_receivingExpansionDomain_iff c).mp hq.1
  exact ⟨c, e, rfl, he, e.isReceivingTerminalAt_of_mem_receivingLoss hq⟩

/-- **Countably many receiving-terminal classes at each level**, for `β < ω₁`, under the
continuation criterion for receiving models (`hcont`) and (R2) (`hres`) and (R3) (`hhol`) for
receiving models. -/
theorem countable_receivingTerminalClasses (hcont : ReceivingContinuationCriterion.{0})
    (hres : Realization.ReceivingResidualReceiving.{0, 0})
    (hhol : Realization.HollowReceiving.{0, 0} Realization.IsReceivingCoverHollowAtBlock)
    {β : Ordinal.{0}} (hβ : β < ω₁) : (receivingTerminalClasses β).Countable := by
  have := countable_terminalProperty hβ
  refine Counting.countable_of_subsingleton_cover _
    (subsingleton_receivingClasses_of_property (ξ := β) hres hhol) ?_
  rintro _ ⟨c, e, rfl, he, ht⟩
  let := c.1.toStructure
  obtain ⟨P, hP⟩ := Realization.exists_hasTerminalProperty_of_isReceivingTerminalAt hcont hβ
    ⟨e.2.isModel, he⟩ ht
  exact Set.mem_iUnion.mpr ⟨P, c, e, rfl, he, hP⟩

end MainTheorem

end VaughtConjecture
