/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.Modelhood
import VaughtConjecture.MainTheorem.CapToModel
import VaughtConjecture.MainTheorem.ModelExpansionDomains

/-!
# The lower bound, conditionally: the class of the top-free witness lies in the loss at its block

Roadmap, the section on the top-free witnesses (step 7, the placement of the witness in the loss),
the reduction of the main theorem to expansion domains (condition 4) and Layer 6 (the lower
bound); semantic contract, items 5 and 9.

Fix a block index `η` and a countable structure `M` of the hull language at the block stage
`λ_η = ω + ω · η` whose age is the age of top-free charts and which is ultrahomogeneous, for
instance a Fraïssé limit of that age.  Write `R = reconstruct λ_η M` for its reconstructed
realization and `B` for the structure of the base language on `M` read from the reduction of `R`
to `ω` (the base reduct).  The **top-free witness** at `η` is `R` when it is a model; the suffix
`_of_topFreeWitness` of the names below refers to it, not to the witnesses of encoders
(`IsWitness`).

**The code** (`exists_code_of_topFreeWitness`).  `B` satisfies the density sentence
(`realize_densitySentence_reconstruct_reduce`), and `M` is infinite when `R` is a model
(`Realization.IsModel.infinite`), so `B` is isomorphic to the structure of a code on `ℕ` of a model
of the density sentence (`exists_mem_modelsOf_equiv`, the reduction to `ℕ`).

**Membership** (`mem_expansionDomain_of_topFreeWitness`).  If `R` is a model, it is a model
expansion of `B` to `λ_η` whose base reduct is `B` by definition, and it transports along the
isomorphism to the code (`ModelExpansion.map`), so the class of the code lies in the expansion
domain at `η`, and in every lower one (`expansionDomain_antitone`).  No uniqueness and no chain of
expansions is used.

**Non-membership** (`notMem_expansionDomain_succ_of_topFreeWitness`).  An expansion of the code to
`λ_{η+1}` transports back to a model expansion `S` of `B` to `λ_{η+1}`, whose reduction to `λ_η`
is a model expansion of `B` to `λ_η`.  Given **uniqueness of the model expansions of `B` at
`λ_η`** (the hypothesis `huniq`: every one of them is `R`), that reduction is `R`; but `R` is not
the reduction of a model at a higher stage (`reduce_ne_reconstruct`, terminality).  This is the
only use of uniqueness, at the single stage `λ_η`.  It holds:
* at `η = 0` unconditionally, without modelhood of `R` (`eq_reconstruct_of_blockStage_zero`): a
  model expansion to `λ_0 = ω` is the realization of its base structure
  (`ModelExpansion.val_eq_toRealization`), and so is `R`, which has legal types;
* at every countable `η` given next-block uniqueness of models
  (`eq_reconstruct_of_nextBlockUniqueness`, through `ModelExpansion.subsingleton`), which is used
  at the successor blocks `ξ + 1 ≤ η` only.

**The lower bound** (`hasNonemptyLosses_of_hasApexCoatomExtensions`).  Under the coatom
extension property with apex at a countable block stage `λ_η`, the age of top-free charts has a
countable Fraïssé limit (`exists_isFraisseLimit_topFreeAge`), whose reconstructed realization is a
model (`isModel_reconstruct_of_hasApexCoatomExtensions`); its class lies in the loss at `η` given
uniqueness of model expansions at `λ_η` on countable carriers
(`nonempty_loss_of_hasApexCoatomExtensions`, the hypothesis `hsub`), and at
`η = 0` with no uniqueness hypothesis (`nonempty_loss_zero_of_hasApexCoatomExtensions`).  With
next-block uniqueness at every block this is condition 4 of the reduction for the expansion
domains of the density sentence.

**The composition** (`densitySentence_hasThinAlephOneSpectrum_of_hasApexCoatomExtensions`).  The
thin `ℵ₁` spectrum of the density sentence, with the nonempty losses derived from the coatom
extension property with apex and next-block uniqueness, conditional on the hypotheses that
remain: the coatom extension property with apex at every countable block stage, next-block
uniqueness of models, finite-cut receiving of models ((R1)), and countable losses (condition 2).
It is conditional; the main theorem of the roadmap has none of these hypotheses.

Not assumed anywhere in this file: global termination or eventual departure, any cardinality
conclusion, uniqueness of model expansions beyond the named hypotheses `huniq` (at `λ_η`, for
one base reduct), `hsub` (at `λ_η`, on countable carriers) and next-block uniqueness `hnext`,
finite-cut receiving of every model ((R1)) for the witness, and uniqueness of the Fraïssé limit.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure baseLanguage Expansion Realization StageType Ordinal

/-! ### The class of the witness -/

section Witness

variable {η : Ordinal.{0}} {M : Type} [(hullLanguage.{0} (blockStage η)).Structure M]

/-- **The code of the witness**: if the reconstructed realization at the block stage `λ_η` of a
countable structure whose age is the age of top-free charts and which is ultrahomogeneous is a
model, its base reduct is isomorphic to the structure of a code on `ℕ` of a model of the density
sentence. -/
theorem exists_code_of_topFreeWitness [Countable M]
    (hage : (hullLanguage.{0} (blockStage η)).age M = topFreeAge (blockStage η))
    (hu : (hullLanguage.{0} (blockStage η)).IsUltrahomogeneous M)
    (hmod : (reconstruct (blockStage η) M).IsModel) :
    ∃ c : ModelsOf densitySentence.{0}, Nonempty (@Language.Equiv baseLanguage.{0} M ℕ
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      c.1.toStructure) := by
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  have := hmod.infinite (omega0_pos.trans_le (omega0_le_blockStage η))
  obtain ⟨c, hc, he⟩ := exists_mem_modelsOf_equiv
    (realize_densitySentence_reconstruct_reduce hage hu (isSuccPrelimit_blockStage η)
      (omega0_le_blockStage η))
  exact ⟨⟨c, hc⟩, he⟩

/-- **Membership of the class of the witness** in the expansion domain at its block: if the
reconstructed realization `R` at `λ_η` is a model, it is a model expansion of its base reduct, and
it transports to every code isomorphic to the base reduct.  No uniqueness is used. -/
theorem mem_expansionDomain_of_topFreeWitness (hmod : (reconstruct (blockStage η) M).IsModel)
    (c : ModelsOf densitySentence.{0}) (e : @Language.Equiv baseLanguage.{0} M ℕ
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      c.1.toStructure) :
    Quotient.mk _ c ∈ expansionDomain η :=
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  let := c.1.toStructure
  (mem_expansionDomain_iff c).mpr ⟨ModelExpansion.map ⟨_, hmod, rfl⟩ e⟩

/-- **Non-membership of the class of the witness** in the expansion domain at the next block,
given uniqueness of the model expansions of its base reduct at `λ_η` (`huniq`): the reduction to
`λ_η` of a model expansion of the base reduct to `λ_{η+1}` would be the reconstructed
realization, which is not the reduction of a model at a higher stage (`reduce_ne_reconstruct`).
Modelhood of the reconstructed realization is not used. -/
theorem notMem_expansionDomain_succ_of_topFreeWitness
    (hage : (hullLanguage.{0} (blockStage η)).age M ⊆ topFreeAge (blockStage η))
    (huniq : ∀ e : @ModelExpansion M
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage η), e.1 = reconstruct (blockStage η) M)
    (c : ModelsOf densitySentence.{0}) (e : @Language.Equiv baseLanguage.{0} M ℕ
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      c.1.toStructure) :
    Quotient.mk _ c ∉ expansionDomain (η + 1) := by
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  let := c.1.toStructure
  intro hc
  obtain ⟨f⟩ := (mem_expansionDomain_iff c).mp hc
  let S : ModelExpansion M (blockStage (η + 1)) := f.map e.symm
  exact reduce_ne_reconstruct hage (isSuccPrelimit_blockStage η)
    (blockStage_lt_blockStage_add_one η) S.2.isModel (huniq (S.reduceBlock (Order.le_succ η)))

/-- **The class of the witness lies in the loss at its block**, given uniqueness of the model
expansions of its base reduct at `λ_η` (`huniq`): the loss `D_η \ D_{η+1}` is nonempty. -/
theorem nonempty_loss_of_topFreeWitness [Countable M]
    (hage : (hullLanguage.{0} (blockStage η)).age M = topFreeAge (blockStage η))
    (hu : (hullLanguage.{0} (blockStage η)).IsUltrahomogeneous M)
    (hmod : (reconstruct (blockStage η) M).IsModel)
    (huniq : ∀ e : @ModelExpansion M
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage η), e.1 = reconstruct (blockStage η) M) :
    (expansionDomain η \ expansionDomain (η + 1)).Nonempty :=
  let ⟨c, ⟨e⟩⟩ := exists_code_of_topFreeWitness hage hu hmod
  ⟨_, mem_expansionDomain_of_topFreeWitness hmod c e,
    notMem_expansionDomain_succ_of_topFreeWitness hage.subset huniq c e⟩

/-! ### Uniqueness of the expansions of the base reduct -/

/-- **Uniqueness at `λ_η` from a subsingleton**: if the base reduct has at most one model
expansion to `λ_η` and the reconstructed realization is a model, every model expansion of the
base reduct to `λ_η` is the reconstructed realization. -/
theorem eq_reconstruct_of_subsingleton (hsub : Subsingleton (@ModelExpansion M
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage η)))
    (hmod : (reconstruct (blockStage η) M).IsModel) :
    ∀ e : @ModelExpansion M
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage η), e.1 = reconstruct (blockStage η) M :=
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  fun e ↦ congrArg Subtype.val (hsub.elim e ⟨_, hmod, rfl⟩)

/-- **Uniqueness at `λ_η` from next-block uniqueness**: for `η < ω₁`, every model expansion of
the base reduct to `λ_η` is the reconstructed realization, if that is a model
(`ModelExpansion.subsingleton`; next-block uniqueness is used at the blocks `ξ + 1 ≤ η`). -/
theorem eq_reconstruct_of_nextBlockUniqueness (hnext : NextBlockUniqueness.{0}) (hη : η < ω₁)
    (hmod : (reconstruct (blockStage η) M).IsModel) :
    ∀ e : @ModelExpansion M
      ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage η), e.1 = reconstruct (blockStage η) M :=
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  eq_reconstruct_of_subsingleton (ModelExpansion.subsingleton hnext hη) hmod

end Witness

/-- At the first block stage, a base structure has at most one model expansion
(`ModelExpansion.instSubsingletonOmega`, since `λ_0 = ω`). -/
private theorem subsingleton_blockStage_zero (N : Type) [baseLanguage.{0}.Structure N] :
    Subsingleton (ModelExpansion N (blockStage 0)) := by
  rw [blockStage_zero]
  infer_instance

/-- At the stage `ω`, every model expansion of the base reduct is the reconstructed realization:
both are the realization of the base reduct. -/
private theorem eq_reconstruct_of_eq_omega {α : Ordinal.{0}} (hα : α = ω) {M : Type}
    [(hullLanguage.{0} α).Structure M] :
    ∀ e : @ModelExpansion M
      ((reconstruct α M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure α,
      e.1 = reconstruct α M := by
  subst hα
  let := ((reconstruct ω M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  intro e
  rw [e.val_eq_toRealization]
  have h : (reconstruct ω M).reduce isSuccLimit_omega0.isSuccPrelimit = reconstruct ω M :=
    Realization.reduce_self _ _
  exact (congrArg (fun R : Realization.{0, 0} ω M ↦ @toRealization M R.toStructure) h).trans
    (toRealization_toStructure hasLegalTypes_reconstruct)

/-- **Uniqueness at `λ_0`, unconditionally**: every model expansion of the base reduct to
`λ_0 = ω` is the reconstructed realization; modelhood of the reconstructed realization is not
needed. -/
theorem eq_reconstruct_of_blockStage_zero {M : Type}
    [(hullLanguage.{0} (blockStage 0)).Structure M] :
    ∀ e : @ModelExpansion M
      ((reconstruct (blockStage 0) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
      (blockStage 0), e.1 = reconstruct (blockStage 0) M :=
  eq_reconstruct_of_eq_omega blockStage_zero

/-! ### The lower bound -/

/-- **The loss at a countable block is nonempty**, under the coatom extension property with apex
at its block stage `λ_η` (`hext`) and uniqueness of model expansions at `λ_η` on countable
carriers (`hsub`): the
reconstructed realization of a countable Fraïssé limit of the age of top-free charts at `λ_η` is a
model, and its class lies in the loss. -/
theorem nonempty_loss_of_hasApexCoatomExtensions {η : Ordinal.{0}} (hη : η < ω₁)
    (hext : HasApexCoatomExtensions.{0} (blockStage η))
    (hsub : ∀ (N : Type) [baseLanguage.{0}.Structure N] [Countable N],
      Subsingleton (ModelExpansion N (blockStage η))) :
    (expansionDomain η \ expansionDomain (η + 1)).Nonempty := by
  have hcount := Cardinal.countable_Iio_of_lt_omega_one (blockStage_lt_omega_one hη)
  let := hullLanguage.countable_functions hcount
  obtain ⟨M, _, hM⟩ := exists_isFraisseLimit_topFreeAge hext.hasCoatomExtensions
    (isSuccPrelimit_blockStage η) (omega0_pos.trans_le (omega0_le_blockStage η)) hcount
  have hmod := isModel_reconstruct_of_hasApexCoatomExtensions hext hM.age hM.ultrahomogeneous
    (isSuccLimit_blockStage η)
  let := ((reconstruct (blockStage η) M).reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  exact nonempty_loss_of_topFreeWitness hM.age hM.ultrahomogeneous hmod
    (eq_reconstruct_of_subsingleton (hsub M) hmod)

/-- **The loss at `0` is nonempty** under the coatom extension property with apex at `ω` alone,
with no uniqueness hypothesis: uniqueness of model expansions at `λ_0 = ω` is unconditional. -/
theorem nonempty_loss_zero_of_hasApexCoatomExtensions (hext : HasApexCoatomExtensions.{0} ω) :
    (expansionDomain 0 \ expansionDomain 1).Nonempty :=
  zero_add (1 : Ordinal) ▸
    nonempty_loss_of_hasApexCoatomExtensions (omega0_pos.trans omega0_lt_omega_one)
      (blockStage_zero.{0} ▸ hext) fun N _ _ ↦ subsingleton_blockStage_zero N

/-- **Nonempty losses of the expansion domains of the density sentence** (condition 4 of the
reduction; the lower bound), under the coatom extension property with apex at every countable
block stage (`hext`) and next-block uniqueness of models (`hnext`), both still to be proved. -/
theorem hasNonemptyLosses_of_hasApexCoatomExtensions (hcap : CapToModel.{0})
    (hnext : NextBlockUniqueness.{0})
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η)) :
    (modelExpansionDomains hcap hnext).HasNonemptyLosses :=
  ⟨fun η hη ↦ nonempty_loss_of_hasApexCoatomExtensions hη (hext η hη)
    fun _ _ _ ↦ ModelExpansion.subsingleton hnext hη⟩

/-- **The thin `ℵ₁` spectrum of the density sentence, with the nonempty losses derived from the
coatom extension property with apex and next-block uniqueness**, conditional on the following
hypotheses, each still to be proved:
* the coatom extension property with apex at every countable block stage (`hext`; Layer 3, 3.1,
  the open part of (R6)), which also gives the cap-to-model theorem at `ω`
  (`CapToModel.of_hasApexCoatomExtensions`);
* next-block uniqueness of models (`hnext`; Layer 4, output 2);
* finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3);
* countable losses of the expansion domains (`hc`; condition 2 of the reduction, Layers 4–5).
Nonempty losses (condition 4) are derived from `hext` and `hnext`
(`hasNonemptyLosses_of_hasApexCoatomExtensions`).  This is not the main theorem of the roadmap,
which has none of these hypotheses. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_hasApexCoatomExtensions
    (hext : ∀ η < ω₁, HasApexCoatomExtensions.{0} (blockStage η))
    (hnext : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0})
    (hc : ∀ ξ < ω₁, (expansionDomain ξ \ expansionDomain (ξ + 1)).Countable) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  have hcap : CapToModel.{0} := CapToModel.of_hasApexCoatomExtensions
    (blockStage_zero.{0} ▸ hext 0 (omega0_pos.trans omega0_lt_omega_one))
  densitySentence_hasThinAlephOneSpectrum_of_modelExpansions hcap hnext hrec hc
    (hasNonemptyLosses_of_hasApexCoatomExtensions hcap hnext hext).nonempty_loss

end VaughtConjecture.MainTheorem
