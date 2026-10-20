/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.KnightSystem.Conditions
import VaughtConjecture.MainTheorem.Spectrum

/-!
# The spectrum of `σ[L]`: the statement of [AFK26, Theorem 4.36]

Numbering as in the current draft of [AFK26].  [AFK26, Theorem 4.36]: the sentence `σ[L]` has
`ℵ₁` countable models up to isomorphism and no perfect set of non-isomorphic countable models.
The printed proof: `K[L]` is a weak Knight system whose base is the class of models of `σ[L]`
([AFK26, Theorem 4.23]); it satisfies [AFK26, Definition 2.23] (a)–(d)
(`VaughtConjecture.Correspondence.KnightSystem.Conditions`); so the abstract theorem
[AFK26, Theorem 2.25] applies.

This file **states** the conclusion for `templateSentence` (`σ[L]`) itself, as
`Theorem436Target`, in the repository's notion of a thin `ℵ₁` spectrum,
`MainTheorem.HasThinAlephOneSpectrum`: the models of the sentence coded on `ℕ` (InfinitaryLogic's
`ModelsOf`, satisfaction `Sentenceω.Realize` of a code's structure) have exactly `ℵ₁` classes
under isomorphism in the language of the sentence (`isoSetoid`), and there is no perfect set of
pairwise nonisomorphic coded models (`Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels`).
Nothing here is proved about the spectrum.

## What is not done here

* `σ[L]` is **not** identified with the repository's public sentence
  `baseLanguage.densitySentence`, and no spectrum result is transferred from it or to it.  The two
  sentences are in different languages (`baseTemplateLanguage` and `baseLanguage`).
* No dependency pin is changed.  The statements use this repository's definitions and
  InfinitaryLogic's coded-model notions at the current pins; no declaration of
  ComputableModelTheory appears in them, so its revision does not bear on them.

## Applicability of the existing counting infrastructure

* **Language.**  `templateSentence.{0}` is a sentence of `baseTemplateLanguage.{0}`, a relational
  language in `Language.{0, 1}`, the universes of `HasThinAlephOneSpectrum`.
  Its countability, `Countable (Σ n, baseTemplateLanguage.{0}.Relations n)`, is not yet a theorem
  (`BaseLanguageCountableTarget`, a new lemma: `L_c[L]` has the symbols `P_n` and `R_c` with
  `τ₀(c) = c`, countably many in each arity by `TemplateSymbol.countable_setOf_not_isInvariant`).
  `Theorem436Target` therefore takes the countability instance as its premise; it is a
  proposition, so the statement does not depend on the proof supplied.
* **Coded models and isomorphism.**  `isoSetoid` and `ModelsOf` do not use countability of the
  language.  The coded models live on `ℕ`, a nonempty carrier, so the model on the empty carrier
  (`realize_templateSentence_of_isEmpty`) is not among them.  The variant on all countable
  carriers, `MainTheorem.HasThinAlephOneSpectrumOnCountableCarriers`, is **not** stated: its
  comparison with the coded statement (`hasThinAlephOneSpectrumOnCountableCarriers_iff`) assumes no
  finite models, which fails for `σ[L]` at the empty carrier (nonempty finite carriers carry no
  model: a model on a nonempty carrier has a lift in `K_0[L]`, whose carriers are infinite by
  `infinitudeTarget`).
* **Counting.**  `Counting.mk_eq_aleph_one_of_rank` (exactly `ℵ₁` elements from a rank into the
  countable ordinals with countable fibres on an uncountable type) applies to
  `Quotient (isoSetoid templateSentence.{0})`, with the rank the **maximal stage**, below.
  `MainTheorem.hasThinAlephOneSpectrum_of_filtration` needs uniformity of every sentence on a
  filtration, a different input, and is not the route here.
* **Thinness.**  `MainTheorem.isThinOnNatModels_of_countable_bfClasses` (no perfect set of pairwise
  nonisomorphic coded models from countably many classes of `bfEquivSetoid φ η` for every
  `η < ω₁`) applies to any sentence of a countable relational language, `templateSentence.{0}`
  included, given the countability of the language.

## The proof plan for `Theorem436Target`

Write `X = Quotient (isoSetoid templateSentence.{0})`, the classes of models of `σ[L]` coded on
`ℕ`.  Every such model `B` has a unique maximal lift `(γ_B, H_B)` on `ℕ`
(`sentenceMaximalLiftTarget`, `ℕ` countable and nonempty).

1. **The maximal stage is a rank on `X`.**  `γ_B` depends only on the class of `B`
   (`MaximalStageInvariantTarget`: a base isomorphism carries the maximal lift, by transport,
   `maximalTransportTarget`, and uniqueness, `maximalLiftUniqueTarget`).  Write `r : X → Ordinal`.
   `r < ω₁`.
2. **Countable fibres.**  The classes with `r = γ` are classes of base reducts of structures
   maximal at `γ` on `ℕ`; by (b) (`uniformMaximalRepresentativesTarget`) each such structure is
   isomorphic in the full language to a member of the countable set `S γ`, and a full isomorphism
   restricts to an isomorphism of base reducts.  So the fibre over `γ` is countable.
3. **Unbounded, hence uncountable.**  For every `β < ω₁` there is a structure maximal at some
   `γ ≥ β` on `ℕ` (`unboundedMaximalStagesTarget`, proved here: Lemma 4.33 makes `K_β[L]` nonempty
   on `ℕ`, and the maximal completion of a member is at a level `γ ≥ β`); its base reduct is a
   coded model of `σ[L]` (`templateBaseModelsTarget`) of rank `γ`.  A rank into `ω₁` with unbounded
   values is not countable.  This replaces the printed use of (d) and [AFK26, Lemma 2.22] for the
   lower bound; (d) is not used in this plan.
4. **Exactly `ℵ₁`.**  `Counting.mk_eq_aleph_one_of_rank` with 1–3.
5. **Thinness.**  For `η < ω₁`, the classes of rank `< η` are countably many (2 at each level
   below `η`); a class of rank `≥ η` has the lift `τ_η(H_B) ∈ K_η[L]` (`projectionTarget`), and two
   members of `K_η[L]` realizing a common invariant have back-and-forth equivalent base reducts at
   level `η` ([AFK26, Proposition 2.18] for `K[L]`, a new lemma, with the comparison of its levels
   with InfinitaryLogic's `BFEquiv`); a member of `K_η[L]` realizes some invariant fixed by `τ_η`,
   and these are countably many.  So `bfEquivSetoid templateSentence.{0} η` has countably many
   classes, and `MainTheorem.isThinOnNatModels_of_countable_bfClasses` gives thinness.  This is the
   argument of [AFK26, Theorem 2.19 and Theorem 2.25 (b)].

## The remaining inputs, with their status

Each entry: the input, its name, its status, and its carrier convention.

* Weak Knight clauses [AFK26, Theorem 4.23]: `projectionTarget`,
  `mem_templateStageClass_transportStructure_iff`, the clauses of `templateStageClass`.  Proved.
  Carriers of `K_β[L]` are nonempty by definition.
* The base is the class of models of `σ[L]` [AFK26, Theorem 4.23]: `templateBaseModelsTarget`.
  Proved (composition).  Countable carrier, premise `Nonempty M`.
* (a) maximal coverage: `maximalCoverageTarget`, `maximalCoverageBaseTarget`.  Proved
  (composition).  Countable carrier; nonemptiness automatic.
* (b) uniform countable maximal representatives: `uniformMaximalRepresentativesTarget`.  Proved
  (composition, with a choice in `β`).  Representatives on `ℕ`; sources countable carriers in
  `Type v`; nonemptiness automatic.
* (c) attained eventual determination: `attainedEventualDeterminationTarget`,
  `eventualDeterminationOfBaseTarget`.  Proved (composition).  Countable carrier; nonemptiness
  automatic.
* (d) invariant occurrence: `InvariantOccurrenceTarget`.  Stated, open; from the two new lemmas
  `LegalClassFixingStageTarget` (no carrier) and `UniversalModelOccurrenceTarget` (countable
  through `K_β[L]`) by `invariantOccurrenceTarget_of`.  Countably infinite carrier.  Not used in
  the plan above.
* The universal chart model [AFK26, Lemma 4.33]: `universalChartModelTarget`.  Proved.  Countably
  infinite carrier.
* Countability of `L_c[L]`: `BaseLanguageCountableTarget`.  New lemma.  No carrier.
* The maximal stage is an isomorphism invariant: `MaximalStageInvariantTarget`.  Stated; a
  composition of proved results, not yet written.  Countable carriers `M`, `N`.
* Unbounded maximal stages on `ℕ`: `unboundedMaximalStagesTarget`.  Proved (composition).  `ℕ`.
* A full isomorphism restricts to an isomorphism of base reducts.  New lemma (not yet named).
  Any carriers.
* Exactly `ℵ₁` classes, steps 1–4.  New lemma (assembly).  Models coded on `ℕ`.
* [AFK26, Proposition 2.18] for `K[L]`, with its levels compared with InfinitaryLogic's
  `BFEquiv`.  New lemma (a back-and-forth system; not yet named).  Countable carriers.
* Thinness, step 5.  New lemma (assembly).  Models coded on `ℕ`.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The statement -/

/-- **Target: `L_c[L]` is countable**: countably many relation symbols of `baseTemplateLanguage`
in all arities.  A new lemma: in each arity the symbols `P_n` and `R_c` (`τ₀(c) = c`) inject into
the symbols of `L_b[L] ∪ L_c[L]` that are not invariants (`BaseSymbol.toTemplateSymbol`), a
countable set (`TemplateSymbol.countable_setOf_not_isInvariant`).  Stated; not proved.
Correspondence with the printed definitions. -/
def BaseLanguageCountableTarget : Prop :=
  Countable (Σ n, baseTemplateLanguage.{u}.Relations n)

/-- **Target: [AFK26, Theorem 4.36]** for `σ[L]` itself (`templateSentence`, at universe `0`):
the models of `σ[L]` coded on `ℕ` have exactly `ℵ₁` isomorphism classes, and there is no perfect
set of pairwise nonisomorphic coded models (`MainTheorem.HasThinAlephOneSpectrum`).  The premise is
the countability of the language, part of the binders of `HasThinAlephOneSpectrum`; it is
`BaseLanguageCountableTarget` at universe `0`, a new lemma.  Not identified with any statement
about `baseLanguage.densitySentence`.  Stated; open; the proof plan is in the module docstring.
Correspondence with the printed definitions. -/
def Theorem436Target : Prop :=
  ∀ hL : Countable (Σ n, baseTemplateLanguage.{0}.Relations n),
    @MainTheorem.HasThinAlephOneSpectrum baseTemplateLanguage.{0} _ hL templateSentence.{0}

/-! ### Inputs of the count -/

/-- **Target: the maximal stage is an isomorphism invariant**: on countable carriers `M` and `N`,
if `H` is maximal at `γ < ω₁` on `M`, `H'` is maximal at `γ' < ω₁` on `N`, and their base reducts
are isomorphic, then `γ = γ'` and `H ≅ H'` in the full language.  Route (composition of proved
results): transport `H'` to `M` along the base isomorphism (`maximalTransportTarget`,
`baseReduct_transportStructure`, `FirstOrder.Language.Equiv.inducedStructure_eq`), then
`maximalLiftUniqueTarget` on `M` and `equivOfTransportStructureEq`.  Stated; not proved.
Correspondence with the printed definitions. -/
def MaximalStageInvariantTarget (M : Type v) (N : Type v) : Prop :=
  Countable M → Countable N → ∀ (γ γ' : Ordinal.{u}) (H : templateLanguage.{u}.Structure M)
    (H' : templateLanguage.{u}.Structure N), γ < ω₁ → γ' < ω₁ → IsMaximalAt γ H →
    IsMaximalAt γ' H' →
    Nonempty (@Language.Equiv baseTemplateLanguage.{u} M N (baseReduct H) (baseReduct H')) →
      γ = γ' ∧ Nonempty (@Language.Equiv templateLanguage.{u} M N H H')

/-- **Target: the maximal stages on `ℕ` are unbounded below `ω₁`**: for every `β < ω₁` there is a
structure on `ℕ` maximal at a level `γ` with `β ≤ γ < ω₁`.  Proved; route:
`universalChartModelTarget` (a member of `K_β[L]` on `ℕ`, [AFK26, Lemma 4.33]) and
`maximalCompletionTarget`.  Correspondence with the printed definitions. -/
def UnboundedMaximalStagesTarget : Prop :=
  ∀ β : Ordinal.{u}, β < ω₁ →
    ∃ γ, β ≤ γ ∧ γ < ω₁ ∧ ∃ H : templateLanguage.{u}.Structure ℕ, IsMaximalAt γ H

/-- **The maximal stages on `ℕ` are unbounded** (`UnboundedMaximalStagesTarget`): the universal
chart model at `β` on `ℕ` (`universalChartModelTarget`) and its maximal completion
(`maximalCompletionTarget`).  Correspondence with the printed definitions. -/
theorem unboundedMaximalStagesTarget : UnboundedMaximalStagesTarget.{u} := by
  intro β hβ
  obtain ⟨G, hG, -⟩ := universalChartModelTarget.{u, 0, 0} β ℕ hβ inferInstance inferInstance
  obtain ⟨γ, H, ⟨hβγ, hγ, -, -, hH⟩, -⟩ := maximalCompletionTarget β ℕ inferInstance hβ G hG
  exact ⟨γ, hβγ, hγ, H, hH⟩

end VaughtConjecture
