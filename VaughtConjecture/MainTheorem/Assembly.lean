/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.Spectrum

/-!
# The main theorem as a conditional composition

Roadmap, the reduction of the main theorem to expansion domains, Layer 5 (expansion domains and
logical agreement) and Layer 6 (the upper and lower bounds); `IMPLEMENTATION.md`, checkpoints 5
and 6; semantic contract, items 1, 8 and 9.

This file states, as named hypotheses, the statements of Layers 3–6 of the roadmap that the main
theorem needs, and proves that they suffice.  **None of these hypotheses is proved here, and
nothing here constructs the objects they describe**: they are statements still to be proved by the
finite extension constructions of Layer 3, the terminal comparisons and counting of Layer 4, the
expansion domains and logical agreement of Layer 5, and the lower bound of Layer 6.  An instance
of any of these structures is not a substitute for those constructions (semantic contract, closing
paragraph; roadmap, Summit 6).  The main theorem of the roadmap has no such hypotheses; the
theorems here are conditional.

## The hypotheses

The classes are `DensityClass`, the countable models of the density sentence coded on `ℕ`, up to
isomorphism (the infinitary-logic library's `Quotient (isoSetoid densitySentence)`).  The
hypotheses are those of the reduction of the main theorem to expansion domains in the roadmap,
for a family `D ξ` of sets of classes indexed by the ordinals `ξ < ω₁`, where `D ξ` is to be the
set of classes admitting a model expansion to the stage `ω + ω · ξ`:

* `ExpansionDomains` (reduction item 1; Layer 5): `D 0` is every class, the domains decrease, and
  at a nonzero limit below `ω₁` the domain contains the intersection of the earlier ones.  Layer 5
  is to prove this for the actual expansion domains, the limit clause by the coherent
  countable-limit expansions (checkpoint 5, unique limit expansions).
* `ExpansionDomains.HasCountableLosses` (reduction item 2; **terminal countability**): each
  successor loss `D ξ \ D (ξ + 1)` below `ω₁` is countable.  Layer 5 is to map each loss into the
  terminal classes at a fixed stage, and Layer 4 to count those by the countable family of
  singleton conditions, through the rigid-core, residual, and hollow comparisons (the first uses
  of rows 2 and 3 of the table of Layer 3; checkpoint 5; semantic contract, item 8).
* `ExpansionDomains.HasLogicalAgreement` (**increasing logical agreement**, the consequence of
  reduction item 3 used here): the truth of every sentence is constant on some domain below `ω₁`,
  the form of `SentenceAgreementDomains` in the roadmap sketch `SuggestedInterfaces.lean`.  Layer 5
  is to prove reduction item 3 itself, the sharp comparison that the classes in `D η` agree on
  every sentence of quantifier rank at most `η`, by the one-sided finite-donor transfer (the first
  use of row 1 of the table of Layer 3); `ExpansionDomains.HasLogicalAgreement.of_qrank_le`
  derives the hypothesis from it.
* `ExpansionDomains.HasNonemptyLosses` (reduction item 4; **the lower bound**): each successor
  loss below `ω₁` is nonempty.  Layer 6 is to construct a top-free terminal model at every
  countable block (the top-free chain construction, with the top-free pinned extension, row 5 of
  the table of Layer 3; checkpoint 3) and place its base class in the loss by expansion
  uniqueness (Layer 5).
* `HasModelOnNat` (**existence**): the density sentence has a model on `ℕ`, which general model
  existence is to provide (the exact-family chain construction, with the exact pinned extension,
  row 6 of the table of Layer 3; checkpoint 3).  It is not a premise of the composition: it follows
  from the lower bound (`ExpansionDomains.HasNonemptyLosses.hasModelOnNat`).
* `CapToModel` (the **cap-to-model theorem** of Layer 3, item 3.4; checkpoint 4): a realization at
  stage `ω` with legal types on a nonempty carrier that is exactly consistent, covering, and has
  the finite-cut receiving property is a model.  It is used only for the absence of finite models
  of the density sentence, hence for the reduction of every countable model to a code.

Scott separation and descriptive separation are not hypotheses: they are proved in
`VaughtConjecture.MainTheorem.Spectrum` (`classTruth_separates`,
`isThinOnNatModels_of_countable_truth_sides`) as instantiations of theorems of the
infinitary-logic library.
The persistent core `⋂ ξ < ω₁, D ξ` is proved to be a subsingleton from Scott separation and
logical agreement (`ExpansionDomains.core_subsingleton`); it need not be empty, and no eventual
departure of every class is assumed.

## The conditional theorems

* `densitySentence_isThinOnNatModels_of_expansionDomains`: expansion domains with countable
  losses and logical agreement give thinness (no lower bound is used);
* `ExpansionDomains.aleph_one_le_mk`: nonempty losses give at least `ℵ₁` classes (neither
  countability of losses nor logical agreement is used);
* `densitySentence_hasThinAlephOneSpectrum_of_expansionDomains`: all four give the thin `ℵ₁`
  spectrum of the density sentence, through the filtration `ExpansionDomains.toFiltration` and
  `hasThinAlephOneSpectrum_of_filtration` (`Filtration.mk_eq_aleph_one_of_separation` and
  descriptive separation);
* `exists_mem_modelsOf_densitySentence_equiv_of_capToModel`: under the cap-to-model theorem, every
  countable model of the density sentence, on a carrier in any universe, is isomorphic to a coded
  model on `ℕ`;
* `vaughtCounterexample_of_expansionDomains`: under all these hypotheses, a countable relational
  language and a sentence of `L_{ω₁,ω}` whose models coded on `ℕ` have exactly `ℵ₁` isomorphism
  classes with no perfect set of pairwise nonisomorphic ones, and every countable model of which,
  on a carrier in any universe, is isomorphic to a coded one.  A spectrum statement counting the
  isomorphism classes of the models on all countable carriers at once is not made here.

The hypothesis structures on the domains are stated for an arbitrary type of classes, so that
their composition can be checked on examples (`VaughtConjecture.MainTheorem.Examples`).

## References

The main theorem is [Kni26, Theorem 1.0.1], for R. W. Knight, *A counterexample to Vaught's
Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u v w x y

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure Cardinal Set Counting baseLanguage
open scoped Ordinal

/-! ### Expansion domains and their hypotheses -/

/-- **Expansion domains** on a type `X` of classes (reduction item 1 of the roadmap; Layer 5): a
family of sets of classes indexed by the ordinals, of which only the stages below `ω₁` are used,
with `D 0` every class, decreasing, and continuous at the nonzero limits below `ω₁`.  For the
density sentence, the domain at `ξ` is to be the set of classes admitting a model expansion to
the stage `ω + ω · ξ`; that it has these properties is a statement of Layer 5, not proved here. -/
structure ExpansionDomains (X : Type u) where
  /-- The domain at stage `ξ`. -/
  domain : Ordinal.{0} → Set X
  /-- The first domain is every class. -/
  zero : domain 0 = Set.univ
  /-- The domains decrease. -/
  antitone : Antitone domain
  /-- At a nonzero limit below `ω₁`, the domain contains the intersection of the earlier ones
  (for the actual expansion domains: the coherent countable-limit expansions of Layer 5). -/
  limit : ∀ l, Order.IsSuccLimit l → l < ω₁ → (⋂ ξ < l, domain ξ) ⊆ domain l

namespace ExpansionDomains

variable {X : Type u} (D : ExpansionDomains X)

/-- **Terminal countability** (reduction item 2 of the roadmap): every successor loss below `ω₁`
is countable.  For the density sentence this is a statement of Layers 4–5 (the losses mapped
into the terminal classes at a fixed stage, counted through the three terminal comparisons),
not proved here. -/
structure HasCountableLosses : Prop where
  /-- Each successor loss below `ω₁` is countable. -/
  countable_loss : ∀ ξ, ξ < ω₁ → (D.domain ξ \ D.domain (ξ + 1)).Countable

/-- **The lower bound** (reduction item 4 of the roadmap): every successor loss below `ω₁` is
nonempty.  For the density sentence this is a statement of Layer 6 (a top-free terminal model at
every countable block, placed in the loss by expansion uniqueness), not proved here. -/
structure HasNonemptyLosses : Prop where
  /-- Each successor loss below `ω₁` is nonempty. -/
  nonempty_loss : ∀ ξ, ξ < ω₁ → (D.domain ξ \ D.domain (ξ + 1)).Nonempty

/-- **Increasing logical agreement** (the consequence of reduction item 3 of the roadmap used
here; see `of_qrank_le`), for observations `truth s` on the classes: each observation is constant
on some domain below `ω₁`.  For the density sentence, with the sentences as observations, this is
a statement of Layer 5, not proved here. -/
structure HasLogicalAgreement {S : Type v} (truth : S → X → Prop) : Prop where
  /-- Each observation is constant on some domain below `ω₁`. -/
  uniform : ∀ s, ∃ ξ, ξ < ω₁ ∧ ∀ p ∈ D.domain ξ, ∀ q ∈ D.domain ξ, (truth s p ↔ truth s q)

variable {D}

/-- **Logical agreement from the sharp comparison**: if the classes in each domain `D η` below
`ω₁` agree on every sentence of quantifier rank at most `η`, then every sentence is constant on
some domain below `ω₁` (its quantifier rank is countable). -/
theorem HasLogicalAgreement.of_qrank_le {L : Language.{x, y}} {truth : L.Sentenceω → X → Prop}
    (h : ∀ η, η < ω₁ → ∀ p ∈ D.domain η, ∀ q ∈ D.domain η, ∀ θ : L.Sentenceω,
      θ.qrank ≤ η → (truth θ p ↔ truth θ q)) :
    D.HasLogicalAgreement truth :=
  ⟨fun θ ↦ ⟨θ.qrank, qrank_lt_omega_one θ, fun p hp q hq ↦
    h _ (qrank_lt_omega_one θ) p hp q hq θ le_rfl⟩⟩

/-- Countable losses and continuity give countable complements below `ω₁` (the infinitary-logic
library's `compl_countable_of_loss`). -/
theorem compl_countable (hc : D.HasCountableLosses) {β : Ordinal.{0}} (hβ : β < ω₁) :
    (D.domain β)ᶜ.Countable :=
  InfinitaryLogic.compl_countable_of_loss D.domain D.zero hc.countable_loss D.limit β hβ

/-- **Countable truth sides**: with countable losses, an observation constant on some domain below
`ω₁` holds at only countably many classes or fails at only countably many classes.  The lower
bound is not used. -/
theorem countable_truth_side (hc : D.HasCountableLosses) {S : Type v} {truth : S → X → Prop}
    (ha : D.HasLogicalAgreement truth) (s : S) :
    {x | truth s x}.Countable ∨ {x | ¬ truth s x}.Countable :=
  have ⟨_, hξ, h⟩ := ha.uniform s
  countable_split_of_uniform_domain (truth s) (D.compl_countable hc hξ) h

/-- **The persistent core is a subsingleton**: if the observations separate distinct classes and
each is constant on some domain below `ω₁`, then at most one class lies in every domain below
`ω₁`.  The core need not be empty, so the upper bound assumes no eventual departure of every
class (no global eventual-departure theorem occurs in the reduction). -/
theorem core_subsingleton {S : Type v} {truth : S → X → Prop} (ha : D.HasLogicalAgreement truth)
    (hsep : ∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q)) :
    (⋂ ξ < ω₁, D.domain ξ).Subsingleton :=
  persistent_subsingleton_of_separation D.domain truth hsep ha.uniform

/-- **The lower bound**: nonempty successor losses give at least `ℵ₁` classes.  Neither
countability of the losses nor logical agreement is used, so the lower bound does not rest on the
upper bound, and it uses no cardinality conclusion or eventual departure. -/
theorem aleph_one_le_mk (hn : D.HasNonemptyLosses) : ℵ₁ ≤ #X :=
  aleph_one_le_mk_of_cofinal D.antitone fun β hβ ↦ ⟨β, le_rfl, hβ, hn.nonempty_loss β hβ⟩

variable (D)

/-- The **filtration** of expansion domains with countable and nonempty losses: the domains
below `ω₁`, and the empty set at and above `ω₁`. -/
def toFiltration (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses) : Filtration X where
  domain ξ := {x | ξ < ω₁ ∧ x ∈ D.domain ξ}
  zero := eq_univ_of_forall fun x ↦ ⟨Ordinal.omega_pos 1, D.zero ▸ mem_univ x⟩
  antitone _ _ h _ hx := ⟨h.trans_lt hx.1, D.antitone h hx.2⟩
  limit l hl hlt _ hx :=
    ⟨hlt, D.limit l hl hlt (mem_iInter₂.2 fun ξ hξ ↦ (mem_iInter₂.1 hx ξ hξ).2)⟩
  loss_countable ξ hξ := by
    refine Set.Countable.mono ?_ (hc.countable_loss ξ hξ)
    rintro x ⟨⟨-, hx⟩, hx'⟩
    exact ⟨hx, fun h ↦ hx' ⟨(isSuccLimit_omega 1).succ_lt hξ, h⟩⟩
  cofinal_losses β hβ := by
    obtain ⟨x, hx, hx'⟩ := hn.nonempty_loss β hβ
    exact ⟨β, le_rfl, hβ, x, ⟨hβ, hx⟩, fun h ↦ hx' h.2⟩
  domain_eq_empty_of_omega_one_le _ h := eq_empty_of_forall_notMem fun _ hx ↦ h.not_gt hx.1

variable {D}

/-- **Logical agreement on the filtration**: an observation constant on some expansion domain
below `ω₁` is constant on the domain of the filtration at the same stage. -/
theorem HasLogicalAgreement.uniform_toFiltration {S : Type v} {truth : S → X → Prop}
    (ha : D.HasLogicalAgreement truth) (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses)
    (s : S) : ∃ ξ, ξ < ω₁ ∧ ∀ p ∈ (D.toFiltration hc hn).domain ξ,
      ∀ q ∈ (D.toFiltration hc hn).domain ξ, (truth s p ↔ truth s q) :=
  have ⟨ξ, hξ, h⟩ := ha.uniform s
  ⟨ξ, hξ, fun p hp q hq ↦ h p hp.2 q hq.2⟩

/-- **Exactly `ℵ₁` classes** from expansion domains with countable and nonempty losses and
logical agreement for observations separating distinct classes, through
`Filtration.mk_eq_aleph_one_of_separation`. -/
theorem mk_eq_aleph_one (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses) {S : Type v}
    {truth : S → X → Prop} (ha : D.HasLogicalAgreement truth)
    (hsep : ∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q)) : #X = ℵ₁ :=
  (D.toFiltration hc hn).mk_eq_aleph_one_of_separation truth hsep (ha.uniform_toFiltration hc hn)

end ExpansionDomains

/-! ### The density sentence -/

/-- The **classes of the density sentence**: its models coded on `ℕ`, up to isomorphism. -/
abbrev DensityClass : Type 1 :=
  Quotient (isoSetoid (densitySentence.{0}))

/-- The truth of a sentence of the base language on a class of models of the density sentence. -/
abbrev densityTruth (θ : baseLanguage.{0}.Sentenceω) : DensityClass → Prop :=
  classTruth densitySentence θ

/-- **Existence** of a model of the density sentence on `ℕ`.  General model existence (the
exact-family chain construction, with the exact pinned extension, row 6 of the table of Layer 3
of the roadmap) is to provide it; it is not proved here.  It is not a premise of the
composition, being implied by the lower bound (`ExpansionDomains.HasNonemptyLosses.hasModelOnNat`).
-/
structure HasModelOnNat : Prop where
  /-- Some code on `ℕ` satisfies the density sentence. -/
  exists_mem_modelsOf : ∃ c : StructureSpace baseLanguage.{0}, c ∈ ModelsOf densitySentence.{0}

/-- The density sentence has a model on `ℕ` exactly when it has a class. -/
theorem hasModelOnNat_iff : HasModelOnNat ↔ Nonempty DensityClass :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨Quotient.mk _ ⟨c, hc⟩⟩, fun ⟨q⟩ ↦ q.inductionOn fun c ↦ ⟨c.1, c.2⟩⟩

/-- The lower bound gives a model on `ℕ`: a nonempty loss contains a class. -/
theorem ExpansionDomains.HasNonemptyLosses.hasModelOnNat {D : ExpansionDomains DensityClass}
    (hn : D.HasNonemptyLosses) : HasModelOnNat :=
  hasModelOnNat_iff.mpr ((hn.nonempty_loss 0 (Ordinal.omega_pos 1)).to_subtype.map Subtype.val)

/-- **The cap-to-model theorem** (Layer 3 of the roadmap, item 3.4), for the realizations at stage
`ω` on the carriers in the universe `w`: a realization with legal types on a nonempty carrier that
is exactly consistent, covering, and has the finite-cut receiving property is a model.  It is a
statement of Layer 3, not proved here. -/
structure CapToModel : Prop where
  /-- The realizations with the structural clauses and finite-cut receiving are models. -/
  isModel : ∀ {M : Type w} (R : Realization.{0, w} ω M), Nonempty M → R.HasLegalTypes →
    R.IsConsistent → R.IsCovering → R.HasFiniteCutReceiving → R.IsModel

/-- **No finite models, given the cap-to-model theorem**: a model of the density sentence is
infinite. -/
theorem CapToModel.infinite (hcap : CapToModel.{w}) {M : Type w}
    [baseLanguage.{0}.Structure M] (h : densitySentence.Realize M) : Infinite M :=
  infinite_of_realize_densitySentence_of_capToModel (fun R ↦ hcap.isModel R) h

/-- **All countable carriers, given the cap-to-model theorem**: every countable model of the
density sentence, on a carrier in the universe `w`, is isomorphic to a coded model on `ℕ`. -/
theorem exists_mem_modelsOf_densitySentence_equiv_of_capToModel (hcap : CapToModel.{w})
    {M : Type w} [baseLanguage.{0}.Structure M] [Countable M] (h : densitySentence.Realize M) :
    ∃ c : StructureSpace baseLanguage.{0}, c ∈ ModelsOf densitySentence.{0} ∧
      Nonempty (@Language.Equiv baseLanguage.{0} M ℕ _ c.toStructure) :=
  have := hcap.infinite h
  exists_mem_modelsOf_equiv h

/-- **Thinness, conditionally**: expansion domains of the classes of the density sentence with
countable losses (terminal countability) and logical agreement give no perfect set of pairwise
nonisomorphic coded models.  The lower bound is not used.  The hypotheses are statements of
Layers 3–5 of the roadmap, not proved here. -/
theorem densitySentence_isThinOnNatModels_of_expansionDomains (D : ExpansionDomains DensityClass)
    (ha : D.HasLogicalAgreement densityTruth) (hc : D.HasCountableLosses) :
    densitySentence.{0}.IsThinOnNatModels :=
  isThinOnNatModels_of_countable_truth_sides (D.countable_truth_side hc ha)

/-- **The main theorem, conditionally**: expansion domains of the classes of the density sentence
with logical agreement (Layer 5), countable losses (terminal countability, Layers 4–5), and
nonempty losses (the lower bound, Layer 6) give exactly `ℵ₁` classes of models coded on `ℕ` and
no perfect set of pairwise nonisomorphic ones.  The hypotheses are statements of Layers 3–6 of
the roadmap, not proved here. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_expansionDomains
    (D : ExpansionDomains DensityClass) (ha : D.HasLogicalAgreement densityTruth)
    (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  hasThinAlephOneSpectrum_of_filtration (D.toFiltration hc hn) (ha.uniform_toFiltration hc hn)

/-- **A thin uncountable infinitary class, conditionally**: under the hypotheses of the main
theorem and the cap-to-model theorem, there are a countable relational language and a sentence
of `L_{ω₁,ω}` whose models coded on `ℕ` have exactly `ℵ₁` isomorphism classes with no perfect
set of pairwise nonisomorphic ones, and every countable model of which, on a carrier in the
universe `w`, is isomorphic to a coded one.  The hypotheses are statements of Layers 3–6 of the
roadmap, not proved here. -/
theorem vaughtCounterexample_of_expansionDomains (D : ExpansionDomains DensityClass)
    (ha : D.HasLogicalAgreement densityTruth) (hc : D.HasCountableLosses)
    (hn : D.HasNonemptyLosses) (hcap : CapToModel.{w}) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) :=
  ⟨baseLanguage.{0}, inferInstance, inferInstance, densitySentence,
    densitySentence_hasThinAlephOneSpectrum_of_expansionDomains D ha hc hn,
    fun _ _ _ h ↦ exists_mem_modelsOf_densitySentence_equiv_of_capToModel hcap h⟩

end VaughtConjecture.MainTheorem
