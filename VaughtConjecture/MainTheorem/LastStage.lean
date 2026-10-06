/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LowerBound

/-!
# Eventual departure and the last stage of a class, for expansion domains

Roadmap, the reduction of the main theorem to expansion domains (conditions 1, 3 and 4) and "The
persistent core"; `COMPANIONS.md`, "Further companion results", terminal refinement, items 1 and
2.

Let `D` be expansion domains on a type `X` of classes (`ExpansionDomains`, in
`VaughtConjecture.MainTheorem.Assembly`): `D 0` is every class, the domains decrease, and at a
nonzero limit below `ω₁` the domain contains the intersection of the earlier ones (condition 1);
the domains at and above `ω₁` are empty.  Observations `truth s` on the classes are given.  A class
`q` is **isolated** by the observation `s` when `truth s p ↔ p = q` for every class `p`.

**Eventual departure** (terminal refinement, item 1).  If `D_ξ` has two members, every
observation constant on `D_ξ` and isolating `q` excludes `q` from `D_ξ`
(`ExpansionDomains.notMem_of_isolating`): a class of `D_ξ` agrees with `q` on it, so equals `q`.
Nonempty losses at `ξ` and `ξ + 1` give the two members (`HasNonemptyLosses.nontrivial_domain`).
So, under logical agreement (`HasLogicalAgreement`: each observation is constant on some domain
below `ω₁`) and nonempty losses (condition 4), or only cofinally many nonempty losses, a class
isolated by some observation leaves the domains at a countable stage
(`exists_notMem_of_isolating`, `exists_notMem_of_isolating_of_cofinal`), and if every class is
isolated, the persistent core `⋂ ξ < ω₁, D_ξ` is empty (`core_eq_empty`).  This strengthens
`ExpansionDomains.core_subsingleton`, which uses separation instead of isolation; separation does
not suffice for departure (`VaughtConjecture.MainTheorem.LastStageExamples`).

With the sentences of a language as observations and condition 3 in its sharp form,
`HasRankAgreement` (the classes in `D_η` agree on the sentences of quantifier rank at most `η`, at
the same index `η`, with no offset), a sentence of quantifier rank `δ < ω₁` isolating `q` excludes
`q` from `D_δ` under nonempty losses (`notMem_of_isolating_of_qrank_le`).

**The last stage** (terminal refinement, item 2).  The **last stage** of a class `q` is
`lastStage D q = sSup {β | q ∈ D_β}`, defined for every class with no hypothesis; it is at most
`ω₁` (`lastStage_le_omega_one`), and it bounds every stage at which `q` lies
(`le_lastStage`).  Membership in the domains is downward closed and continuous at the nonzero
countable limits, and holds at `0`, so once `q ∉ D_ξ` for some `ξ < ω₁` the set of stages at
which `q` lies has a greatest element, the last stage, below `ξ` (`isGreatest_lastStage`, through
the attained greatest index `exists_isGreatest_of_closed`): the least stage missing `q` is the
successor of the last stage.  Then `q ∈ D_β ↔ β ≤ lastStage D q` for every ordinal `β`, `β ≥ ω₁`
included.  Under isolation, logical agreement and nonempty losses:
* `exists_lastStage`: a countable `ρ` with `q ∈ D_β ↔ β ≤ ρ` for every `β`;
* `mem_domain_iff_le_lastStage`, `lastStage_lt_omega_one`;
* `mem_loss_iff_lastStage_eq`: the loss `D_β \ D_{β+1}` is the fibre of the last stage at `β`
  (`loss_eq_preimage_lastStage`), and the domains are the tails of the last stage
  (`domain_eq_setOf_le_lastStage`);
* `lastStage_lt_qrank`, under the sharp agreement: the last stage of `q` is below the quantifier
  rank of every sentence isolating `q`.
The rank is that of a *chosen* isolating sentence; it is not identified with any Scott rank, and
the last stage is not a Scott rank.  No global termination is used or proved: departure is a
consequence of conditions 1, 3 and 4 with isolation, not a hypothesis, and no expansion of a model
to its last stage is constructed here (terminal refinement, item 3, is not addressed).

**The classes of coded models.**  For the classes `Quotient (isoSetoid φ)` of the models coded on
`ℕ` of a sentence `φ` of a countable relational language, every class is isolated by a sentence
(Scott isolation, `exists_classTruth_iff_eq`, in `VaughtConjecture.MainTheorem.Spectrum`), so
logical agreement for `classTruth φ` and nonempty losses give departure and the last stage with
no further hypothesis (`core_eq_empty_of_classTruth`, `mem_domain_iff_le_lastStage_of_classTruth`,
`mem_loss_iff_lastStage_eq_of_classTruth`, `lastStage_lt_omega_one_of_classTruth`).

**The expansion domains of the density sentence**, `modelExpansionDomains hcap hnext`, satisfy
the sharp agreement under finite-cut receiving of models (`modelExpansionDomains_hasRankAgreement`,
through `Expansion.mem_modelsOf_iff_of_modelExpansions`), and nonempty losses under the coatom
extension property with apex at every countable block stage
(`hasNonemptyLosses_of_hasApexCoatomExtensions`).  So departure and the last stage hold for them
(`expansionDomain_core_eq_empty`, `mem_expansionDomain_iff_le_lastStage`,
`mem_expansionDomain_loss_iff_lastStage_eq`, `lastStage_modelExpansionDomains_lt_qrank`)
conditional on the following hypotheses, each still to be proved:
* the cap-to-model theorem at `ω` on `ℕ` (`hcap`; Layer 3, 3.4): the first domain is every class
  (it follows from `hext` at `0`, `CapToModel.of_hasApexCoatomExtensions`);
* next-block uniqueness of models (`hnext`; Layer 4, output 2): the limit clause, and the
  placement of the top-free witness in the loss (it follows from (R1) and forcing donors,
  `Expansion.NextBlockUniqueness.of_forcingDonors`);
* finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3): the agreement;
* the coatom extension property with apex at every countable block stage (`hext`; Layer 3, 3.1,
  the open part of (R6)): the nonempty losses.
Countable losses (condition 2) are not used.

**The attained greatest index.**  `exists_isGreatest_of_closed` uses Mathlib only.  The same
statement, with the same name, is proposed for a module `VaughtConjecture.Label.GreatestIndex`;
one copy is kept when both are present.  It follows from the greatest-stage statements of
InfinitaryLogic (`OrdinalUtil`), available upstream, not at the pin `e460cb6`, but it is not the
same statement as any of them.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe u v x y

open Order Ordinal

namespace VaughtConjecture

/-- **An attained greatest index**: a predicate on ordinals that holds at `β`, is closed
downward, is closed at the nonzero countable limits, and holds only below a countable ordinal `δ`
has a greatest element `ρ`, with `β ≤ ρ < δ`.  Mathlib only.  The greatest element is the
supremum of the ordinals at which the predicate holds: if the predicate failed there, it would
hold everywhere below, so the supremum would be neither zero, nor a successor, nor a limit.  It
follows from the greatest-stage statements of InfinitaryLogic, available upstream, not at the pin
`e460cb6`, whose hypotheses and conclusions differ.  The same statement is proposed for
`VaughtConjecture.Label.GreatestIndex`; one copy is kept when both are present. -/
theorem exists_isGreatest_of_closed {P : Ordinal.{u} → Prop} {β δ : Ordinal.{u}} (hβ : P β)
    (hdown : ∀ ⦃a b⦄, a ≤ b → P b → P a)
    (hlim : ∀ l, IsSuccLimit l → l < ω₁ → (∀ a < l, P a) → P l)
    (hbound : ∀ a, P a → a < δ) (hδ : δ < ω₁) :
    ∃ ρ, IsGreatest {a | P a} ρ ∧ β ≤ ρ ∧ ρ < δ := by
  have hbdd : BddAbove {a | P a} := ⟨δ, fun a ha ↦ (hbound a ha).le⟩
  set ρ := sSup {a | P a}
  have hle : ∀ a, P a → a ≤ ρ := fun a ha ↦ le_csSup hbdd ha
  suffices hρ : P ρ from ⟨ρ, ⟨hρ, hle⟩, hle β hβ, hbound ρ hρ⟩
  by_contra hρ
  -- below the supremum, `P` holds everywhere
  have hbelow : ∀ a < ρ, P a := fun a ha ↦
    let ⟨b, hb, hab⟩ := exists_lt_of_lt_csSup ⟨β, hβ⟩ ha
    hdown hab.le hb
  rcases zero_or_succ_or_isSuccLimit ρ with h0 | ⟨a, ha⟩ | hl
  · exact hρ (hdown (h0.le.trans (zero_le (a := β))) hβ)
  · -- every element is below `a + 1`, so the supremum is at most `a`
    have hsup : ρ ≤ a := csSup_le ⟨β, hβ⟩ fun b hb ↦
      lt_succ_iff.mp (ha ▸ (hle b hb).lt_of_ne fun h ↦ hρ (h ▸ hb))
    exact (lt_succ a).not_ge (ha ▸ hsup)
  · exact hρ (hlim ρ hl ((csSup_le ⟨β, hβ⟩ fun b hb ↦ (hbound b hb).le).trans_lt hδ) hbelow)

end VaughtConjecture

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure Cardinal Set Counting baseLanguage Expansion
open scoped Ordinal

namespace ExpansionDomains

variable {X : Type u} (D : ExpansionDomains X)

/-! ### The sharp agreement -/

/-- **The sharp agreement** (condition 3 of the reduction of the main theorem to expansion
domains, in sentence form), for a truth predicate `truth θ` of the sentences `θ` of a language `L`
on the classes: the classes in each domain `D η` below `ω₁` agree on every sentence of quantifier
rank at most `η`.  The convention is rank `≤ η` at stage `η`, with no offset.  It gives logical
agreement (`HasRankAgreement.hasLogicalAgreement`).  For the expansion domains of the density
sentence it holds under finite-cut receiving of models (`modelExpansionDomains_hasRankAgreement`).
-/
structure HasRankAgreement {L : Language.{x, y}} (truth : L.Sentenceω → X → Prop) : Prop where
  /-- The classes in `D η` agree on the sentences of quantifier rank at most `η`. -/
  agree : ∀ η, η < ω₁ → ∀ p ∈ D.domain η, ∀ q ∈ D.domain η, ∀ θ : L.Sentenceω,
    θ.qrank ≤ η → (truth θ p ↔ truth θ q)

variable {D}

/-- The sharp agreement gives logical agreement: each sentence is constant on the domain at its
quantifier rank (`HasLogicalAgreement.of_qrank_le`). -/
theorem HasRankAgreement.hasLogicalAgreement {L : Language.{x, y}}
    {truth : L.Sentenceω → X → Prop} (h : D.HasRankAgreement truth) :
    D.HasLogicalAgreement truth :=
  .of_qrank_le h.agree

/-! ### Eventual departure -/

/-- A class lying in a domain lies in it below `ω₁`: the domains at and above `ω₁` are empty. -/
theorem lt_omega_one_of_mem {q : X} {β : Ordinal.{0}} (hq : q ∈ D.domain β) : β < ω₁ :=
  not_le.1 fun h ↦ by simp [D.domain_eq_empty_of_omega_one_le β h] at hq

/-- **Two members in every countable domain**: under nonempty losses (condition 4), `D_ξ`
contains a class of the loss at `ξ` and a class of the loss at `ξ + 1`, which lies in
`D_{ξ+1} ⊆ D_ξ`. -/
theorem HasNonemptyLosses.nontrivial_domain (hn : D.HasNonemptyLosses) {ξ : Ordinal.{0}}
    (hξ : ξ < ω₁) : (D.domain ξ).Nontrivial := by
  obtain ⟨p, hp, hp'⟩ := hn.nonempty_loss ξ hξ
  obtain ⟨p', hp₁, -⟩ := hn.nonempty_loss (ξ + 1) ((isSuccLimit_omega 1).succ_lt hξ)
  exact ⟨p, hp, p', D.antitone (Order.le_succ ξ) hp₁, fun h ↦ hp' (h ▸ hp₁)⟩

/-- **An isolated class is not in a domain with two members on which its observation is
constant**: if `truth s` holds exactly at `q` and is constant on `D_ξ`, and `D_ξ` has two members,
then `q ∉ D_ξ`; otherwise every member of `D_ξ` would agree with `q` on `s`, hence equal `q`. -/
theorem notMem_of_isolating {S : Type v} {truth : S → X → Prop} {s : S} {q : X}
    {ξ : Ordinal.{0}} (hξ : ∀ p ∈ D.domain ξ, ∀ p' ∈ D.domain ξ, (truth s p ↔ truth s p'))
    (hiso : ∀ p, truth s p ↔ p = q) (hnt : (D.domain ξ).Nontrivial) : q ∉ D.domain ξ := by
  intro hq
  have heq : ∀ p ∈ D.domain ξ, p = q := fun p hp ↦
    (hiso p).1 ((hξ p hp q hq).2 ((hiso q).2 rfl))
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  exact hab ((heq a ha).trans (heq b hb).symm)

/-- **A class isolated by a sentence of quantifier rank `δ` is not in `D_δ`**, under the sharp
agreement (`hr`, condition 3, rank `≤ δ` at stage `δ`) and nonempty losses (`hn`, condition 4, at
`δ` and `δ + 1`, for the two members of `D_δ`). -/
theorem notMem_of_isolating_of_qrank_le {L : Language.{x, y}} {truth : L.Sentenceω → X → Prop}
    (hr : D.HasRankAgreement truth) (hn : D.HasNonemptyLosses) {σ : L.Sentenceω} {q : X}
    (hiso : ∀ p, truth σ p ↔ p = q) {δ : Ordinal.{0}} (hδ : δ < ω₁) (hqr : σ.qrank ≤ δ) :
    q ∉ D.domain δ :=
  notMem_of_isolating (fun p hp p' hp' ↦ hr.agree δ hδ p hp p' hp' σ hqr) hiso
    (hn.nontrivial_domain hδ)

/-- **Eventual departure of an isolated class, from cofinally nonempty losses**: under logical
agreement (`ha`) and nonempty losses at cofinally many stages below `ω₁` (`hcof`), a class
isolated by some observation (`hiso`) is not in some domain below `ω₁`.  If `q ∈ D_ξ`, with `ξ`
the stage at which the observation is constant, a class of a nonempty loss at `β ≥ ξ` lies in
`D_ξ`, so equals `q`, and `q ∉ D_{β+1}`. -/
theorem exists_notMem_of_isolating_of_cofinal {S : Type v} {truth : S → X → Prop}
    (ha : D.HasLogicalAgreement truth)
    (hcof : ∀ γ, γ < ω₁ → ∃ β, γ ≤ β ∧ β < ω₁ ∧ (D.domain β \ D.domain (β + 1)).Nonempty)
    {q : X} (hiso : ∃ s, ∀ p, truth s p ↔ p = q) : ∃ ξ, ξ < ω₁ ∧ q ∉ D.domain ξ := by
  obtain ⟨s, hs⟩ := hiso
  obtain ⟨ξ, hξ, hconst⟩ := ha.uniform s
  by_cases hq : q ∈ D.domain ξ
  · obtain ⟨β, hξβ, hβ, p, hp, hp'⟩ := hcof ξ hξ
    have hpq : p = q := (hs p).1 ((hconst p (D.antitone hξβ hp) q hq).2 ((hs q).2 rfl))
    exact ⟨β + 1, (isSuccLimit_omega 1).succ_lt hβ, hpq ▸ hp'⟩
  · exact ⟨ξ, hξ, hq⟩

/-- **Eventual departure of an isolated class** (terminal refinement, item 1): under logical
agreement (`ha`) and nonempty losses (`hn`, condition 4), a class isolated by some observation
(`hiso`) is not in some domain below `ω₁`. -/
theorem exists_notMem_of_isolating {S : Type v} {truth : S → X → Prop}
    (ha : D.HasLogicalAgreement truth) (hn : D.HasNonemptyLosses) {q : X}
    (hiso : ∃ s, ∀ p, truth s p ↔ p = q) : ∃ ξ, ξ < ω₁ ∧ q ∉ D.domain ξ :=
  exists_notMem_of_isolating_of_cofinal ha
    (fun γ hγ ↦ ⟨γ, le_rfl, hγ, hn.nonempty_loss γ hγ⟩) hiso

/-- **The persistent core is empty** (terminal refinement, item 1, corollary): under logical
agreement (`ha`) and nonempty losses (`hn`), if every class is isolated by some observation
(`hiso`), no class lies in every domain below `ω₁`.  This strengthens `core_subsingleton`, whose
separation hypothesis does not suffice for it. -/
theorem core_eq_empty {S : Type v} {truth : S → X → Prop} (ha : D.HasLogicalAgreement truth)
    (hn : D.HasNonemptyLosses) (hiso : ∀ q, ∃ s, ∀ p, truth s p ↔ p = q) :
    (⋂ ξ < ω₁, D.domain ξ) = ∅ :=
  eq_empty_of_forall_notMem fun q hq ↦
    let ⟨ξ, hξ, hq'⟩ := exists_notMem_of_isolating ha hn (hiso q)
    hq' (mem_iInter₂.1 hq ξ hξ)

/-! ### The last stage -/

variable (D)

/-- The **last stage** of a class `q`: the supremum of the stages `β` with `q ∈ D_β`.  It is
defined for every class; it is the greatest such stage once `q` leaves the domains below `ω₁`
(`isGreatest_lastStage`), and it is `ω₁` for a class in every domain below `ω₁`.  It is not a
Scott rank. -/
noncomputable def lastStage (q : X) : Ordinal.{0} :=
  sSup {β | q ∈ D.domain β}

variable {D}

/-- The stages at which a class lies are bounded by `ω₁`. -/
theorem bddAbove_setOf_mem (q : X) : BddAbove {β | q ∈ D.domain β} :=
  ⟨ω₁, fun _ hβ ↦ (lt_omega_one_of_mem hβ).le⟩

/-- The last stage bounds every stage at which the class lies. -/
theorem le_lastStage {q : X} {β : Ordinal.{0}} (hq : q ∈ D.domain β) : β ≤ D.lastStage q :=
  le_csSup (bddAbove_setOf_mem q) hq

/-- The last stage is at most `ω₁`. -/
theorem lastStage_le_omega_one (q : X) : D.lastStage q ≤ ω₁ :=
  csSup_le ⟨0, by simp [D.zero]⟩ fun _ hβ ↦ (lt_omega_one_of_mem hβ).le

/-- **The last stage is attained once the class leaves** (terminal refinement, item 2): if
`q ∉ D_ξ` for some `ξ < ω₁`, the stages at which `q` lies have a greatest element, the last stage
of `q`, and it is below `ξ`.  It uses only condition 1 (`zero`, `antitone`, `limit`), through
`exists_isGreatest_of_closed`. -/
theorem isGreatest_lastStage {q : X} {ξ : Ordinal.{0}} (hξ : ξ < ω₁) (hq : q ∉ D.domain ξ) :
    IsGreatest {β | q ∈ D.domain β} (D.lastStage q) ∧ D.lastStage q < ξ := by
  obtain ⟨ρ, hρ, -, hρξ⟩ := exists_isGreatest_of_closed (P := (q ∈ D.domain ·)) (β := 0)
    (by simp [D.zero]) (fun _ _ hab hb ↦ D.antitone hab hb)
    (fun l hl hlω h ↦ D.limit l hl hlω (mem_iInter₂.2 h))
    (fun _ ha ↦ not_le.1 fun h ↦ hq (D.antitone h ha)) hξ
  rw [lastStage, hρ.csSup_eq]
  exact ⟨hρ, hρξ⟩

/-- **The domains of a departing class are the stages up to its last stage**: if `q ∉ D_ξ` for
some `ξ < ω₁`, then `q ∈ D_β ↔ β ≤ lastStage D q` for every ordinal `β`. -/
theorem mem_domain_iff_le_lastStage_of_notMem {q : X} {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    (hq : q ∉ D.domain ξ) {β : Ordinal.{0}} : q ∈ D.domain β ↔ β ≤ D.lastStage q :=
  ⟨le_lastStage, fun h ↦ D.antitone h (isGreatest_lastStage hξ hq).1.1⟩

/-- **A departing class lies in the loss at its last stage, and only there**: if `q ∉ D_ξ` for
some `ξ < ω₁`, then `q ∈ D_β \ D_{β+1} ↔ lastStage D q = β`. -/
theorem mem_loss_iff_lastStage_eq_of_notMem {q : X} {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    (hq : q ∉ D.domain ξ) {β : Ordinal.{0}} :
    q ∈ D.domain β \ D.domain (β + 1) ↔ D.lastStage q = β := by
  rw [mem_sdiff, mem_domain_iff_le_lastStage_of_notMem hξ hq,
    mem_domain_iff_le_lastStage_of_notMem hξ hq, not_le, ← Order.succ_eq_add_one,
    Order.lt_succ_iff, le_antisymm_iff, and_comm]

/-- **The last stage of a class not in `D_1` is `0`.** -/
theorem lastStage_eq_zero {q : X} (hq : q ∉ D.domain 1) : D.lastStage q = 0 :=
  Order.lt_one_iff.1 (isGreatest_lastStage (one_lt_omega0.trans omega0_lt_omega_one) hq).2

section Isolation

variable {S : Type v} {truth : S → X → Prop} {q : X}

/-- **The last stage of an isolated class** (terminal refinement, items 1–2): under logical
agreement (`ha`) and nonempty losses (`hn`), a class isolated by some observation (`hiso`) has a
countable `ρ` with `q ∈ D_β ↔ β ≤ ρ` for every ordinal `β`. -/
theorem exists_lastStage (ha : D.HasLogicalAgreement truth) (hn : D.HasNonemptyLosses)
    (hiso : ∃ s, ∀ p, truth s p ↔ p = q) :
    ∃ ρ, ρ < ω₁ ∧ ∀ β, q ∈ D.domain β ↔ β ≤ ρ :=
  let ⟨_, hξ, hq⟩ := exists_notMem_of_isolating ha hn hiso
  ⟨D.lastStage q, (isGreatest_lastStage hξ hq).2.trans hξ,
    fun _ ↦ mem_domain_iff_le_lastStage_of_notMem hξ hq⟩

/-- **The last stage of an isolated class is countable**, under logical agreement (`ha`) and
nonempty losses (`hn`). -/
theorem lastStage_lt_omega_one (ha : D.HasLogicalAgreement truth) (hn : D.HasNonemptyLosses)
    (hiso : ∃ s, ∀ p, truth s p ↔ p = q) : D.lastStage q < ω₁ :=
  let ⟨_, hξ, hq⟩ := exists_notMem_of_isolating ha hn hiso
  (isGreatest_lastStage hξ hq).2.trans hξ

/-- **An isolated class lies exactly in the domains up to its last stage**, under logical
agreement (`ha`) and nonempty losses (`hn`). -/
theorem mem_domain_iff_le_lastStage (ha : D.HasLogicalAgreement truth)
    (hn : D.HasNonemptyLosses) (hiso : ∃ s, ∀ p, truth s p ↔ p = q) {β : Ordinal.{0}} :
    q ∈ D.domain β ↔ β ≤ D.lastStage q :=
  let ⟨_, hξ, hq⟩ := exists_notMem_of_isolating ha hn hiso
  mem_domain_iff_le_lastStage_of_notMem hξ hq

/-- **An isolated class lies in the loss at its last stage, and only there**, under logical
agreement (`ha`) and nonempty losses (`hn`). -/
theorem mem_loss_iff_lastStage_eq (ha : D.HasLogicalAgreement truth) (hn : D.HasNonemptyLosses)
    (hiso : ∃ s, ∀ p, truth s p ↔ p = q) {β : Ordinal.{0}} :
    q ∈ D.domain β \ D.domain (β + 1) ↔ D.lastStage q = β :=
  let ⟨_, hξ, hq⟩ := exists_notMem_of_isolating ha hn hiso
  mem_loss_iff_lastStage_eq_of_notMem hξ hq

/-- **The losses are the fibres of the last stage**, when every class is isolated, under logical
agreement (`ha`) and nonempty losses (`hn`). -/
theorem loss_eq_preimage_lastStage (ha : D.HasLogicalAgreement truth) (hn : D.HasNonemptyLosses)
    (hiso : ∀ q, ∃ s, ∀ p, truth s p ↔ p = q) (β : Ordinal.{0}) :
    D.domain β \ D.domain (β + 1) = D.lastStage ⁻¹' {β} :=
  Set.ext fun q ↦ mem_loss_iff_lastStage_eq ha hn (hiso q)

/-- **The domains are the tails of the last stage**, when every class is isolated, under logical
agreement (`ha`) and nonempty losses (`hn`). -/
theorem domain_eq_setOf_le_lastStage (ha : D.HasLogicalAgreement truth)
    (hn : D.HasNonemptyLosses) (hiso : ∀ q, ∃ s, ∀ p, truth s p ↔ p = q) (β : Ordinal.{0}) :
    D.domain β = {q | β ≤ D.lastStage q} :=
  Set.ext fun q ↦ mem_domain_iff_le_lastStage ha hn (hiso q)

end Isolation

/-- **The last stage is below the quantifier rank of every isolating sentence**, under the sharp
agreement (`hr`, condition 3) and nonempty losses (`hn`, condition 4).  The rank is that of the
chosen sentence `σ`, not a Scott rank. -/
theorem lastStage_lt_qrank {L : Language.{x, y}} {truth : L.Sentenceω → X → Prop}
    (hr : D.HasRankAgreement truth) (hn : D.HasNonemptyLosses) {σ : L.Sentenceω} {q : X}
    (hiso : ∀ p, truth σ p ↔ p = q) : D.lastStage q < σ.qrank :=
  (isGreatest_lastStage (qrank_lt_omega_one σ)
    (notMem_of_isolating_of_qrank_le hr hn hiso (qrank_lt_omega_one σ) le_rfl)).2

/-! ### The classes of coded models -/

section ClassTruth

variable {L : Language.{x, y}} [L.IsRelational] [Countable (Σ n, L.Relations n)]
  {φ : L.Sentenceω} {D : ExpansionDomains (Quotient (isoSetoid φ))}

/-- **The persistent core of domains of coded classes is empty**, under logical agreement for
the truth of sentences (`ha`) and nonempty losses (`hn`): every class is isolated by a sentence
(Scott isolation, `exists_classTruth_iff_eq`). -/
theorem core_eq_empty_of_classTruth (ha : D.HasLogicalAgreement (classTruth φ))
    (hn : D.HasNonemptyLosses) : (⋂ ξ < ω₁, D.domain ξ) = ∅ :=
  core_eq_empty ha hn exists_classTruth_iff_eq

/-- **The last stage of a coded class is countable**, under logical agreement for the truth of
sentences (`ha`) and nonempty losses (`hn`). -/
theorem lastStage_lt_omega_one_of_classTruth (ha : D.HasLogicalAgreement (classTruth φ))
    (hn : D.HasNonemptyLosses) (q : Quotient (isoSetoid φ)) : D.lastStage q < ω₁ :=
  lastStage_lt_omega_one ha hn (exists_classTruth_iff_eq q)

/-- **A coded class lies exactly in the domains up to its last stage**, under logical agreement
for the truth of sentences (`ha`) and nonempty losses (`hn`). -/
theorem mem_domain_iff_le_lastStage_of_classTruth (ha : D.HasLogicalAgreement (classTruth φ))
    (hn : D.HasNonemptyLosses) {q : Quotient (isoSetoid φ)} {β : Ordinal.{0}} :
    q ∈ D.domain β ↔ β ≤ D.lastStage q :=
  mem_domain_iff_le_lastStage ha hn (exists_classTruth_iff_eq q)

/-- **A coded class lies in the loss at its last stage, and only there**, under logical agreement
for the truth of sentences (`ha`) and nonempty losses (`hn`). -/
theorem mem_loss_iff_lastStage_eq_of_classTruth (ha : D.HasLogicalAgreement (classTruth φ))
    (hn : D.HasNonemptyLosses) {q : Quotient (isoSetoid φ)} {β : Ordinal.{0}} :
    q ∈ D.domain β \ D.domain (β + 1) ↔ D.lastStage q = β :=
  mem_loss_iff_lastStage_eq ha hn (exists_classTruth_iff_eq q)

end ClassTruth

end ExpansionDomains

/-! ### The expansion domains of the density sentence -/

/-- **The sharp agreement of the expansion domains of the density sentence**, conditional on
finite-cut receiving of models (`hrec`; (R1) of the table of Layer 3, still to be proved): two
classes with model expansions of coded representatives to the block stage `λ_η` agree on the
sentences of quantifier rank at most `η` (`Expansion.mem_modelsOf_iff_of_modelExpansions`). -/
theorem modelExpansionDomains_hasRankAgreement (hcap : CapToModel.{0})
    (hnext : NextBlockUniqueness.{0}) (hrec : FiniteCutReceiving.{0}) :
    (modelExpansionDomains hcap hnext).HasRankAgreement densityTruth :=
  ⟨fun η hη p hp q hq θ hθ ↦ by
    obtain ⟨c₁, rfl, h₁⟩ := hp
    obtain ⟨c₂, rfl, h₂⟩ := hq
    rw [densityTruth, classTruth_mk, classTruth_mk]
    exact mem_modelsOf_iff_of_modelExpansions hrec.finiteExtensionReceiving hη c₁.1 c₂.1 h₁ h₂ θ
      hθ⟩

section Density

variable (hcap : CapToModel.{0}) (hnext : NextBlockUniqueness.{0})
  (hrec : FiniteCutReceiving.{0})
  (hext : ∀ η < ω₁, StageType.HasApexCoatomExtensions.{0} (blockStage η))

include hcap hnext hrec hext

/-- **Eventual departure for the expansion domains of the density sentence**: no class has a
model expansion of a coded representative to every countable block stage, conditional on the
cap-to-model theorem (`hcap`), next-block uniqueness of models (`hnext`), finite-cut receiving of
models (`hrec`) and the coatom extension property with apex at every countable block stage
(`hext`), each still to be proved. -/
theorem expansionDomain_core_eq_empty : (⋂ ξ < ω₁, expansionDomain ξ) = ∅ :=
  ExpansionDomains.core_eq_empty_of_classTruth (D := modelExpansionDomains hcap hnext)
    (modelExpansionDomains_hasRankAgreement hcap hnext hrec).hasLogicalAgreement
    (hasNonemptyLosses_of_hasApexCoatomExtensions hcap hnext hext)

/-- **The expansion domains of the density sentence are the tails of the last stage**: a class
lies in `expansionDomain β` exactly when `β` is at most its last stage, conditional on `hcap`,
`hnext`, `hrec` and `hext`, each still to be proved. -/
theorem mem_expansionDomain_iff_le_lastStage {q : DensityClass} {β : Ordinal.{0}} :
    q ∈ expansionDomain β ↔ β ≤ (modelExpansionDomains hcap hnext).lastStage q :=
  ExpansionDomains.mem_domain_iff_le_lastStage_of_classTruth
    (modelExpansionDomains_hasRankAgreement hcap hnext hrec).hasLogicalAgreement
    (hasNonemptyLosses_of_hasApexCoatomExtensions hcap hnext hext)

/-- **The losses of the expansion domains of the density sentence are the fibres of the last
stage**, conditional on `hcap`, `hnext`, `hrec` and `hext`, each still to be proved. -/
theorem mem_expansionDomain_loss_iff_lastStage_eq {q : DensityClass} {β : Ordinal.{0}} :
    q ∈ expansionDomain β \ expansionDomain (β + 1) ↔
      (modelExpansionDomains hcap hnext).lastStage q = β :=
  ExpansionDomains.mem_loss_iff_lastStage_eq_of_classTruth
    (modelExpansionDomains_hasRankAgreement hcap hnext hrec).hasLogicalAgreement
    (hasNonemptyLosses_of_hasApexCoatomExtensions hcap hnext hext)

/-- **The last stage of a class of the density sentence is below the quantifier rank of every
sentence isolating it**, conditional on `hcap`, `hnext`, `hrec` and `hext`, each still to be
proved.  The rank is that of the chosen sentence `σ`, not a Scott rank. -/
theorem lastStage_modelExpansionDomains_lt_qrank {σ : baseLanguage.{0}.Sentenceω}
    {q : DensityClass} (hσ : ∀ p, densityTruth σ p ↔ p = q) :
    (modelExpansionDomains hcap hnext).lastStage q < σ.qrank :=
  ExpansionDomains.lastStage_lt_qrank (modelExpansionDomains_hasRankAgreement hcap hnext hrec)
    (hasNonemptyLosses_of_hasApexCoatomExtensions hcap hnext hext) hσ

end Density

end VaughtConjecture.MainTheorem
