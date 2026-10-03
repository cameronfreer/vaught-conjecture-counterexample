/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.Scatteredness
import VaughtConjecture.MainTheorem.Spectrum

/-!
# The main theorem as a conditional composition

Roadmap, the reduction of the main theorem to expansion domains, Layer 5 (expansion domains and
logical agreement) and Layer 6 (the upper and lower bounds); `IMPLEMENTATION.md`, checkpoints 5
and 6; semantic contract, items 1, 8 and 9.  The second route: roadmap, "Reduction to full
presentations", and `IMPLEMENTATION.md`, "The full-presentation route".

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
  countable-limit expansions (checkpoint 5, unique limit expansions).  As for a `Filtration`, the
  domains at and above `ω₁` are empty, so expansion domains are determined by their stages below
  `ω₁` (`ExpansionDomains.ext`).
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
  on a carrier in any universe, is isomorphic to a coded one.  The spectrum statement counting the
  isomorphism classes of the countable models on the carriers of a universe `w` is not made here:
  it is `HasThinAlephOneSpectrumOnCountableCarriers` in `VaughtConjecture.MainTheorem.AllCarriers`
  (`vaughtCounterexample_allCarriers_of_expansionDomains`), by the reduction to `ℕ`.  The
  conclusion states a counterexample to Vaught's Conjecture by the number of classes and
  thinness: it gives the negation, for this sentence, of Vaught's Conjecture in the form of the
  introduction to [Mon, Chapter XII] (the models of a sentence of `L_{ω₁,ω}` are countably many
  up to isomorphism or contain a perfect set of nonisomorphic presentations on `ℕ`).  Cf. the
  scattered, unbounded sentences of [Mon, §XII.1], recalled in the module docstring of
  `VaughtConjecture.MainTheorem.Spectrum`.

The hypothesis structures on the domains are stated for an arbitrary type of classes, so that
their composition can be checked on examples (`VaughtConjecture.MainTheorem.Examples`).

## The full-presentation route

A second conditional composition reaches the same conclusion from different hypotheses (roadmap,
"Reduction to full presentations"), in addition to the composition through expansion domains
above, which it leaves unchanged.  A countable structure is **full** for a class of finite closed
diagrams (a prescribed age) when its finite closed diagrams are exactly that class, every finite
subset lies in one of them, and every embedding into the structure of a diagram of the class
extends along every embedding of that diagram into a larger diagram of the class; a **full
presentation** of a class at level `α < ω₁` is a countable structure full for one of the
prescribed ages at level `α` whose base reduct lies in the class.  The hypotheses, none of them
proved here, are:

* `FullPresentations` (**full presentations at countable levels**): sets `presentedAt α` of
  classes, for the levels `α < ω₁`, each countable, together containing every class, and empty
  at the levels `α ≥ ω₁`.  For the density sentence, `presentedAt α` is to be the set of classes
  with a full presentation at level `α`; its countability is to come from the isomorphism of two
  countable structures full for the same prescribed age, together with the countability of the
  prescribed ages at each level, which is folded into the countability of `presentedAt α` here.
  That **every** class has a full presentation, including any class admitting model expansions
  to every countable stage, is part of this hypothesis.
* `FullPresentations.HasBoundedComparison` (**bounded comparison**, in sentence form): the
  classes in the tail `FullPresentations.tail η`, those with no full presentation below level
  `η`, agree on every sentence of quantifier rank at most `η`.  This is the sharp comparison of
  `ExpansionDomains.HasLogicalAgreement.of_qrank_le`, taken on the least-level tails in place of
  the expansion domains.
* `FullPresentations.HasScatteredTails` (**scattered tails**, the scatteredness form): for each
  `η < ω₁`, the codes of the models whose classes lie in the tail at `η` fall into countably many
  classes of `bfEquivSetoid densitySentence η`.
* `UncountablyManyClasses` (**noncollapse**): there are at least `ℵ₁` classes.  The existence of
  full presentations cannot give it: `FullPresentations` and `HasBoundedComparison` hold for a
  single class (`VaughtConjecture.MainTheorem.Examples`).
* `CapToModel`, as above, for the reduction of every countable model to a code.

Bounded comparison is stated in its **minimality form**: on the least-level tails, all classes
of the tail at `η` agree up to quantifier rank `η`.  Its proof by back-and-forth is to start from
a common observation of presentations at high levels (such as the common empty chart).  With it,
thinness follows from countable truth sides through `isThinOnNatModels_of_countable_truth_sides`.
The weaker **scatteredness form**, `FullPresentations.HasScatteredTails` (weaker in mathematics,
through formulas of quantifier rank `η` defining back-and-forth classes; that implication is not
proved here), says that the codes of the models whose classes lie in the tail at each `η < ω₁`
fall into only countably many classes of back-and-forth equivalence at `η` (the library's
`CodeBFEquiv η`, restricted to the codes of models of the density sentence:
`bfEquivSetoid densitySentence η`); it counts classes of that relation, not codes.  It also gives
thinness, but not through countable truth sides: the tail at `η` has countable complement, so all
the codes of models fall into countably many classes at `η`
(`FullPresentations.HasScatteredTails.countable_quotient`), and
`isThinOnNatModels_of_countable_bfClasses` (`VaughtConjecture.MainTheorem.Scatteredness`)
excludes a nonempty perfect set of pairwise nonisomorphic coded models by the library's uniform
back-and-forth separation of analytic sets of nonisomorphic pairs (`exists_uniform_bfSeparation`,
the boundedness of analytic families of well-founded trees).  Neither sentence separation (Scott
or descriptive) nor López–Escobar nor bounded comparison is used in this composition.

The **least presentation level** of a class, the least `α < ω₁` with the class in
`presentedAt α`, is a rank into the countable ordinals with countable fibres, and its tails form
the filtration `FullPresentations.toFiltration` (`Counting.Filtration.ofCountableCover`, through
`Counting.Filtration.ofRank`) on an uncountable type of classes.  What the count of this route
uses and does not use:

* the bound `#X ≤ ℵ₁` uses only `FullPresentations`: the classes are covered by `ℵ₁` countable
  sets (`FullPresentations.mk_le_aleph_one`); the lower bound is `UncountablyManyClasses`, and
  bounded comparison is used only for thinness;
* the count uses neither expansion uniqueness nor same-carrier transport.  Departure is not
  removed from the assumptions: the least presentation level is a total rank below `ω₁`, so
  every class leaves the tail just above its least presentation level, which is part of
  `FullPresentations`.  What this route does not need is a separate termination theorem for
  expansion domains;
* Scott separation on the persistent core (the step of `Filtration.mk_eq_aleph_one_of_separation`
  that bounds the core by one class) is not used: the core of the least-level filtration is empty
  (`FullPresentations.core_toFiltration`), so the count is `Filtration.mk_eq_aleph_one` with an
  empty core.  Descriptive separation (separation of invariant analytic sets by a sentence, the
  library's `sentence_separates_analytic_classes` behind
  `SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits`) is still used for thinness in
  the minimality-form composition, through `isThinOnNatModels_of_filtration`, the thinness half of
  `hasThinAlephOneSpectrum_of_filtration`.  That composition applies to the same filtration; its
  two halves are taken separately here so that the count does not pass through Scott separation.
  The scatteredness-form composition uses no sentence separation;
* `ExpansionDomains.HasNonemptyLosses` is replaced by uncountability: the losses of the
  least-level filtration are nonempty only cofinally often, not at every successor, and
  cofinally many nonempty losses are equivalent to uncountability
  (InfinitaryLogic's `InfinitaryLogic.rankTail_cofinal_losses_iff`).

The conditional theorems of this route:

* `densitySentence_isThinOnNatModels_of_presentations`: full presentations and bounded
  comparison give thinness (no lower bound is used);
* `densitySentence_hasThinAlephOneSpectrum_of_presentations`: with uncountability, the thin
  `ℵ₁` spectrum of the density sentence;
* `densitySentence_isThinOnNatModels_of_scatteredTails`: full presentations with scattered tails
  give thinness (neither bounded comparison nor the lower bound is used);
* `densitySentence_hasThinAlephOneSpectrum_of_scatteredTails`: with uncountability, the thin
  `ℵ₁` spectrum of the density sentence, the count as in
  `densitySentence_hasThinAlephOneSpectrum_of_presentations`, thinness from scattered tails;
* `vaughtCounterexample_of_presentations`: with the cap-to-model theorem, the counterpart of
  `vaughtCounterexample_of_expansionDomains`;
* `vaughtCounterexample_of_scatteredTails`: with the cap-to-model theorem, the counterpart of
  `vaughtCounterexample_of_presentations` with scattered tails in place of bounded comparison.

## References

The cardinality statement of the main theorem, exactly `ℵ₁` countable models up to isomorphism,
is [Kni26, Theorem 11.1.9], and the failure of Vaught's Conjecture in `L_{ω₁,ω}` is
[Kni26, Theorem 11.1.10], immediate from it, for R. W. Knight, *A counterexample to Vaught's
Conjecture using generalised Stone spaces* (draft, 20 February 2026).

Vaught's Conjecture in the form that a sentence of `L_{ω₁,ω}` has countably many models up to
isomorphism or a perfect set of nonisomorphic presentations on `ℕ` is stated in the
introduction to [Mon, Chapter XII], and a counterexample to
Vaught's Conjecture is, in [Mon, §XII.1], a scattered sentence of `L_{ω₁,ω}` that is unbounded
in the sense of [Mon, Definition XII.1], for A. Montalbán, *Computable Structure Theory: Beyond
the arithmetic* (draft, 22 April 2025).
-/

universe u v w x y

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure Cardinal Set Counting baseLanguage
open scoped Ordinal

/-! ### Expansion domains and their hypotheses -/

/-- **Expansion domains** on a type `X` of classes (reduction item 1 of the roadmap; Layer 5): a
family of sets of classes indexed by the stages below `ω₁`, with `D 0` every class, decreasing,
and continuous at the nonzero limits below `ω₁`.  As in `Counting.Filtration`, the index is
`Ordinal.{0}` and the domains at stages `ξ ≥ ω₁` are empty, so expansion domains are determined
by their stages below `ω₁` (`ExpansionDomains.ext`).  For the density sentence, the domain at
`ξ < ω₁` is to be the set of classes admitting a model expansion to the stage `ω + ω · ξ`; that
it has these properties is a statement of Layer 5, not proved here. -/
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
  /-- No data is carried at or above `ω₁`: the domains there are empty. -/
  domain_eq_empty_of_omega_one_le : ∀ ξ, ω₁ ≤ ξ → domain ξ = ∅

namespace ExpansionDomains

variable {X : Type u} (D : ExpansionDomains X)

/-- Expansion domains agreeing below `ω₁` are equal: at and above `ω₁` both domains are empty. -/
@[ext]
theorem ext {D E : ExpansionDomains X} (h : ∀ ξ, ξ < ω₁ → D.domain ξ = E.domain ξ) : D = E := by
  obtain ⟨D, _, _, _, hD⟩ := D
  obtain ⟨E, _, _, _, hE⟩ := E
  congr
  funext ξ
  rcases lt_or_ge ξ ω₁ with hξ | hξ
  · exact h ξ hξ
  · rw [hD ξ hξ, hE ξ hξ]

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

/-- The **filtration** of expansion domains with countable and nonempty losses: the same
domains. -/
def toFiltration (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses) : Filtration X where
  domain := D.domain
  zero := D.zero
  antitone := D.antitone
  limit := D.limit
  loss_countable := hc.countable_loss
  cofinal_losses β hβ := ⟨β, le_rfl, hβ, hn.nonempty_loss β hβ⟩
  domain_eq_empty_of_omega_one_le := D.domain_eq_empty_of_omega_one_le

variable {D}

/-- **Logical agreement on the filtration**: an observation constant on some expansion domain
below `ω₁` is constant on the domain of the filtration at the same stage. -/
theorem HasLogicalAgreement.uniform_toFiltration {S : Type v} {truth : S → X → Prop}
    (ha : D.HasLogicalAgreement truth) (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses)
    (s : S) : ∃ ξ, ξ < ω₁ ∧ ∀ p ∈ (D.toFiltration hc hn).domain ξ,
      ∀ q ∈ (D.toFiltration hc hn).domain ξ, (truth s p ↔ truth s q) :=
  ha.uniform s

/-- **Exactly `ℵ₁` classes** from expansion domains with countable and nonempty losses and
logical agreement for observations separating distinct classes, through
`Filtration.mk_eq_aleph_one_of_separation`. -/
theorem mk_eq_aleph_one (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses) {S : Type v}
    {truth : S → X → Prop} (ha : D.HasLogicalAgreement truth)
    (hsep : ∀ p q, p ≠ q → ∃ s, ¬ (truth s p ↔ truth s q)) : #X = ℵ₁ :=
  (D.toFiltration hc hn).mk_eq_aleph_one_of_separation truth hsep (ha.uniform_toFiltration hc hn)

end ExpansionDomains

/-! ### Full presentations and bounded comparison -/

/-- **Full presentations at countable levels** on a type `X` of classes: sets `presentedAt α` of
classes for the levels `α < ω₁`, each countable, together containing every class; the sets at the
levels `α ≥ ω₁` are empty, so full presentations are determined by their levels below `ω₁`
(`FullPresentations.ext`).  For the density sentence, `presentedAt α` is to be the set of classes
with a full presentation at level `α` (a countable structure full for one of the countably many
prescribed ages at level `α`, whose base reduct lies in the class); that every class has one, and
that only countably many classes have one at each level, are statements of the full-presentation
route (roadmap, "Reduction to full presentations"), not proved here. -/
structure FullPresentations (X : Type u) where
  /-- The classes with a full presentation at level `α`. -/
  presentedAt : Ordinal.{0} → Set X
  /-- Only countably many classes have a full presentation at a given level below `ω₁`. -/
  countable_presentedAt : ∀ α, α < ω₁ → (presentedAt α).Countable
  /-- Every class has a full presentation at some level below `ω₁`. -/
  exists_mem_presentedAt : ∀ x, ∃ α, α < ω₁ ∧ x ∈ presentedAt α
  /-- No data is carried at or above `ω₁`: no class is presented at a level `α ≥ ω₁`. -/
  presentedAt_eq_empty_of_omega_one_le : ∀ α, ω₁ ≤ α → presentedAt α = ∅

namespace FullPresentations

variable {X : Type u} (P : FullPresentations X)

/-- Full presentations agreeing below `ω₁` are equal: at and above `ω₁` both are empty. -/
@[ext]
theorem ext {P₁ P₂ : FullPresentations X}
    (h : ∀ α, α < ω₁ → P₁.presentedAt α = P₂.presentedAt α) : P₁ = P₂ := by
  obtain ⟨Q₁, _, _, h₁⟩ := P₁
  obtain ⟨Q₂, _, _, h₂⟩ := P₂
  congr
  funext α
  rcases lt_or_ge α ω₁ with hα | hα
  · exact h α hα
  · rw [h₁ α hα, h₂ α hα]

/-- The **tail** at `η`: the classes with no full presentation at a level below `η`. -/
def tail (η : Ordinal.{0}) : Set X :=
  (⋃ α < η, P.presentedAt α)ᶜ

/-- The tail at a countable stage has countable complement: the classes presented at the
countably many levels below it. -/
theorem countable_compl_tail {η : Ordinal.{0}} (hη : η < ω₁) : (P.tail η)ᶜ.Countable := by
  rw [tail, compl_compl]
  exact (InfinitaryLogic.setCountable_Iio_of_lt_omega1 η hη).biUnion fun α hα ↦
    P.countable_presentedAt α (lt_trans hα hη)

include P in
/-- **At most `ℵ₁` classes**: the classes are covered by the `ℵ₁` countable sets `presentedAt α`
(`Counting.mk_le_aleph_one_of_countable_cover`). -/
theorem mk_le_aleph_one : #X ≤ ℵ₁ :=
  mk_le_aleph_one_of_countable_cover P.countable_presentedAt P.exists_mem_presentedAt

/-- The **least-level filtration** of an uncountable type of classes with full presentations: the
domain at `η` is the tail at `η` (`domain_toFiltration`). -/
noncomputable def toFiltration (hX : ¬ Countable X) : Filtration X :=
  .ofCountableCover P.presentedAt P.countable_presentedAt P.exists_mem_presentedAt hX

/-- The domain of the least-level filtration at `η` is the tail at `η`. -/
theorem domain_toFiltration (hX : ¬ Countable X) (η : Ordinal.{0}) :
    (P.toFiltration hX).domain η = P.tail η :=
  Filtration.domain_ofCountableCover η

/-- **The persistent core of the least-level filtration is empty**: every class leaves the tail just
above its least presentation level. -/
@[simp]
theorem core_toFiltration (hX : ¬ Countable X) : (P.toFiltration hX).core = ∅ :=
  iInter_setOf_le_rank_eq_empty _ fun x ↦ (leastLevel_lt_and_mem P.exists_mem_presentedAt x).1

/-- **Bounded comparison** (in sentence form), for a truth predicate `truth θ` of the sentences `θ`
of a language `L` on the classes: the classes in the tail at each `η < ω₁` agree on every sentence
of quantifier rank at most `η`.  This is the minimality form of bounded comparison: the sharp
comparison of `ExpansionDomains.HasLogicalAgreement.of_qrank_le`, taken on the least-level tails.
The weaker scatteredness form, for the density sentence, is `FullPresentations.HasScatteredTails`.
For the density sentence, with the truth of sentences on its classes, bounded comparison is a
statement of the full-presentation route (the projections of full presentations at levels `≥ η`
are back-and-forth equivalent at `η`; roadmap, "Reduction to full presentations"), not proved
here. -/
structure HasBoundedComparison {L : Language.{x, y}} (truth : L.Sentenceω → X → Prop) :
    Prop where
  /-- The classes in the tail at `η` agree on the sentences of quantifier rank at most `η`. -/
  agree : ∀ η, η < ω₁ → ∀ p ∈ P.tail η, ∀ q ∈ P.tail η, ∀ θ : L.Sentenceω,
    θ.qrank ≤ η → (truth θ p ↔ truth θ q)

variable {P}

/-- **Countable truth sides from bounded comparison**: each sentence is constant on the tail at
its quantifier rank, whose complement is countable, so it holds at only countably many classes or
fails at only countably many classes.  No lower bound is used. -/
theorem HasBoundedComparison.countable_truth_side {L : Language.{x, y}}
    {truth : L.Sentenceω → X → Prop} (hb : P.HasBoundedComparison truth) (θ : L.Sentenceω) :
    {x | truth θ x}.Countable ∨ {x | ¬ truth θ x}.Countable :=
  countable_split_of_uniform_domain (truth θ) (P.countable_compl_tail (qrank_lt_omega_one θ))
    fun p hp q hq ↦ hb.agree _ (qrank_lt_omega_one θ) p hp q hq θ le_rfl

end FullPresentations

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
roadmap, not proved here.  The conclusion states a counterexample to Vaught's Conjecture by the
number of classes and thinness, the negation of the form of the conjecture in the introduction
to [Mon, Chapter XII] (cf. also [Mon, §XII.1]). -/
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

/-! ### The full-presentation route -/

/-- **Noncollapse**: the density sentence has at least `ℵ₁` classes of models coded on `ℕ`.  For the
full-presentation route (roadmap, "Reduction to full presentations") this is a separate statement
(full presentations alone do not give it), not proved here. -/
structure UncountablyManyClasses : Prop where
  /-- There are at least `ℵ₁` classes. -/
  aleph_one_le_mk : ℵ₁ ≤ #DensityClass

/-- Uncountably many classes: the type of classes is not countable. -/
theorem UncountablyManyClasses.not_countable (hu : UncountablyManyClasses) :
    ¬ Countable DensityClass := by
  rw [← mk_le_aleph0_iff, not_le]
  exact aleph0_lt_aleph_one.trans_le hu.aleph_one_le_mk

/-- Noncollapse gives a model on `ℕ`. -/
theorem UncountablyManyClasses.hasModelOnNat (hu : UncountablyManyClasses) : HasModelOnNat :=
  hasModelOnNat_iff.mpr (mk_ne_zero_iff.1 ((aleph_pos 1).trans_le hu.aleph_one_le_mk).ne')

/-- **Uniformity on the least-level filtration**: bounded comparison for the classes of the
density sentence makes every sentence uniform on the least-level filtration
(`IsUniformOnFiltration.of_qrank_le`). -/
theorem FullPresentations.HasBoundedComparison.isUniformOnFiltration
    {P : FullPresentations DensityClass} (hb : P.HasBoundedComparison densityTruth)
    (hX : ¬ Countable DensityClass) :
    IsUniformOnFiltration densitySentence (P.toFiltration hX) :=
  .of_qrank_le fun η hη p hp q hq ↦ by
    rw [P.domain_toFiltration] at hp hq
    exact hb.agree η hη p hp q hq

/-- **Thinness, conditionally, by full presentations**: full presentations of the classes of the
density sentence at countable levels with bounded comparison give no perfect set of pairwise
nonisomorphic coded models.  The lower bound is not used.  The hypotheses are statements of the
full-presentation route (roadmap, "Reduction to full presentations"), not proved here. -/
theorem densitySentence_isThinOnNatModels_of_presentations (P : FullPresentations DensityClass)
    (hb : P.HasBoundedComparison densityTruth) : densitySentence.{0}.IsThinOnNatModels :=
  isThinOnNatModels_of_countable_truth_sides hb.countable_truth_side

/-- **The main theorem, conditionally, by full presentations**: full presentations of the classes of
the density sentence at countable levels, bounded comparison, and noncollapse give exactly `ℵ₁`
classes of models coded on `ℕ` and no perfect set of pairwise nonisomorphic ones.  The count is
`Filtration.mk_eq_aleph_one` on the least-level filtration, whose persistent core is empty; thinness
is `isThinOnNatModels_of_filtration` with the uniformity of `IsUniformOnFiltration.of_qrank_le`.
The hypotheses are statements of the full-presentation route (roadmap, "Reduction to full
presentations"), not proved here. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_presentations
    (P : FullPresentations DensityClass) (hb : P.HasBoundedComparison densityTruth)
    (hu : UncountablyManyClasses) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  ⟨(P.toFiltration hu.not_countable).mk_eq_aleph_one (by simp),
    isThinOnNatModels_of_filtration _ (hb.isUniformOnFiltration hu.not_countable)⟩

/-- **A thin uncountable infinitary class, conditionally, by full presentations**: under full
presentations at countable levels, bounded comparison, noncollapse, and the cap-to-model theorem,
there are a countable relational language and a sentence of `L_{ω₁,ω}` whose models coded on `ℕ`
have exactly `ℵ₁` isomorphism classes with no perfect set of pairwise nonisomorphic ones, and every
countable model of which, on a carrier in the universe `w`, is isomorphic to a coded one.  The
hypotheses are statements of the full-presentation route (roadmap, "Reduction to full
presentations") and of Layer 3 of the roadmap, not proved here. -/
theorem vaughtCounterexample_of_presentations (P : FullPresentations DensityClass)
    (hb : P.HasBoundedComparison densityTruth) (hu : UncountablyManyClasses)
    (hcap : CapToModel.{w}) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) :=
  ⟨baseLanguage.{0}, inferInstance, inferInstance, densitySentence,
    densitySentence_hasThinAlephOneSpectrum_of_presentations P hb hu,
    fun _ _ _ h ↦ exists_mem_modelsOf_densitySentence_equiv_of_capToModel hcap h⟩

/-! ### The full-presentation route in scatteredness form -/

/-- **Scattered tails** (the scatteredness form of bounded comparison, weaker in mathematics;
that implication is not proved here): for every `η < ω₁`, the codes of the models of the density
sentence whose classes lie in the tail at `η` (the classes with no full presentation below level
`η`) fall into only countably many classes of back-and-forth equivalence at `η` (the library's
`bfEquivSetoid densitySentence η`, the restriction of `CodeBFEquiv η` to the codes of models).  It
counts classes of that relation, not codes.  Since the tail has countable complement, this is
equivalent, for every `P`, to countably many classes of `bfEquivSetoid densitySentence η` among
all the codes of models, for every `η < ω₁` (`HasScatteredTails.countable_quotient` and
`HasScatteredTails.of_countable_quotient`).  It is a statement of the full-presentation route
(roadmap, "Reduction to full presentations": countably many observed types at every level), not
proved here. -/
structure FullPresentations.HasScatteredTails (P : FullPresentations DensityClass) : Prop where
  /-- The codes of the models in the tail at `η` meet countably many classes at `η`. -/
  countable_bfClasses : ∀ η, η < ω₁ →
    (Quotient.mk (bfEquivSetoid densitySentence.{0} η) ''
      {c | Quotient.mk (isoSetoid densitySentence.{0}) c ∈ P.tail η}).Countable

/-- **Countably many back-and-forth classes at every level from scattered tails**: the tail at
`η` has countable complement, and isomorphic codes are back-and-forth equivalent, so all the
codes of models of the density sentence fall into countably many classes at `η`. -/
theorem FullPresentations.HasScatteredTails.countable_quotient
    {P : FullPresentations DensityClass} (hs : P.HasScatteredTails) {η : Ordinal.{0}}
    (hη : η < ω₁) : Countable (Quotient (bfEquivSetoid densitySentence.{0} η)) := by
  let g : DensityClass → Quotient (bfEquivSetoid densitySentence.{0} η) :=
    Quotient.lift (Quotient.mk _) fun _ _ h ↦
      Quotient.sound (isoSetoid_refines_bfEquivSetoid _ η h)
  refine countable_univ_iff.mp
    (((hs.countable_bfClasses η hη).union ((P.countable_compl_tail hη).image g)).mono ?_)
  rintro q -
  induction q using Quotient.inductionOn with
  | h c =>
    by_cases hc : Quotient.mk (isoSetoid densitySentence.{0}) c ∈ P.tail η
    · exact Or.inl ⟨c, hc, rfl⟩
    · exact Or.inr ⟨_, hc, rfl⟩

/-- **Scattered tails from countably many back-and-forth classes at every level**: the converse of
`FullPresentations.HasScatteredTails.countable_quotient`, for any full presentations. -/
theorem FullPresentations.HasScatteredTails.of_countable_quotient
    {P : FullPresentations DensityClass}
    (h : ∀ η, η < ω₁ → Countable (Quotient (bfEquivSetoid densitySentence.{0} η))) :
    P.HasScatteredTails :=
  ⟨fun η hη ↦ have := h η hη; Set.to_countable _⟩

/-- **Thinness, conditionally, by full presentations with scattered tails**: full presentations
of the classes of the density sentence at countable levels with scattered tails give no perfect
set of pairwise nonisomorphic coded models (`isThinOnNatModels_of_countable_bfClasses`, by the
library's uniform back-and-forth separation).  Neither bounded comparison nor the lower bound is
used.  The hypotheses are statements of the full-presentation route (roadmap, "Reduction to full
presentations"), not proved here. -/
theorem densitySentence_isThinOnNatModels_of_scatteredTails (P : FullPresentations DensityClass)
    (hs : P.HasScatteredTails) : densitySentence.{0}.IsThinOnNatModels :=
  isThinOnNatModels_of_countable_bfClasses fun _ hη ↦ hs.countable_quotient hη

/-- **The main theorem, conditionally, by full presentations with scattered tails**: full
presentations of the classes of the density sentence at countable levels, scattered tails, and
noncollapse give exactly `ℵ₁` classes of models coded on `ℕ` and no perfect set of pairwise
nonisomorphic ones.  The count is that of `densitySentence_hasThinAlephOneSpectrum_of_presentations`
(`Filtration.mk_eq_aleph_one` on the least-level filtration, whose persistent core is empty);
thinness is `densitySentence_isThinOnNatModels_of_scatteredTails`.  The hypotheses are statements
of the full-presentation route (roadmap, "Reduction to full presentations"), not proved here. -/
theorem densitySentence_hasThinAlephOneSpectrum_of_scatteredTails
    (P : FullPresentations DensityClass) (hs : P.HasScatteredTails)
    (hu : UncountablyManyClasses) :
    HasThinAlephOneSpectrum densitySentence.{0} :=
  ⟨(P.toFiltration hu.not_countable).mk_eq_aleph_one (by simp),
    densitySentence_isThinOnNatModels_of_scatteredTails P hs⟩

/-- **A thin uncountable infinitary class, conditionally, by full presentations with scattered
tails**: under full presentations at countable levels, scattered tails, noncollapse, and the
cap-to-model theorem, there are a countable relational language and a sentence of `L_{ω₁,ω}` whose
models coded on `ℕ` have exactly `ℵ₁` isomorphism classes with no perfect set of pairwise
nonisomorphic ones, and every countable model of which, on a carrier in the universe `w`, is
isomorphic to a coded one.  The hypotheses are statements of the full-presentation route (roadmap,
"Reduction to full presentations") and of Layer 3 of the roadmap, not proved here. -/
theorem vaughtCounterexample_of_scatteredTails (P : FullPresentations DensityClass)
    (hs : P.HasScatteredTails) (hu : UncountablyManyClasses) (hcap : CapToModel.{w}) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) :=
  ⟨baseLanguage.{0}, inferInstance, inferInstance, densitySentence,
    densitySentence_hasThinAlephOneSpectrum_of_scatteredTails P hs hu,
    fun _ _ _ h ↦ exists_mem_modelsOf_densitySentence_equiv_of_capToModel hcap h⟩

end VaughtConjecture.MainTheorem
