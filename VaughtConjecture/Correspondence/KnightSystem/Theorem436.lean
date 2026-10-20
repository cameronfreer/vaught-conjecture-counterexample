/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.KnightSystem.WeakSystem
import VaughtConjecture.MainTheorem.Spectrum

/-!
# The spectrum of `σ[L]`: the statement of [AFK26, Theorem 4.36]

Numbering as in the current draft of [AFK26].  [AFK26, Theorem 4.36]: the sentence `σ[L]` has
`ℵ₁` countable models up to isomorphism and no perfect set of non-isomorphic countable models.
The printed proof: `K[L]` is a weak system whose base is the class of models of `σ[L]`
([AFK26, Theorem 4.23]; `VaughtConjecture.Correspondence.KnightSystem.WeakSystem`); it satisfies
[AFK26, Definition 2.23] (a)–(d) (`knightSystemTarget`,
`VaughtConjecture.Correspondence.KnightSystem.Conditions`); so the abstract theorem
[AFK26, Theorem 2.25] applies.

This file **states** the conclusion for `templateSentence` (`σ[L]`) itself, as
`Theorem436Target`, in the repository's notion of a thin `ℵ₁` spectrum,
`MainTheorem.HasThinAlephOneSpectrum`: the models of the sentence coded on `ℕ` (InfinitaryLogic's
`ModelsOf`, satisfaction `Sentenceω.Realize` of a code's structure) have exactly `ℵ₁` classes
under isomorphism in the language of the sentence (`isoSetoid`), and there is no perfect set of
pairwise nonisomorphic coded models (`Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels`).
Nothing here is proved about the spectrum.  The file also proves some inputs of the count (the
countability of the language, the restriction of an isomorphism to the base reducts, the
invariance of the maximal stage, unbounded maximal stages) and states, as a named requirement, the
passage from the models coded on `ℕ` to the models on all countable nonempty carriers.

## What is not done here

* `σ[L]` is **not** identified with the repository's public sentence
  `baseLanguage.densitySentence`, and no spectrum result is transferred from it or to it.  The two
  sentences are in different languages (`baseTemplateLanguage` and `baseLanguage`).
* No dependency pin is changed.  The statements use this repository's definitions and
  InfinitaryLogic's coded-model notions at the current pins; no declaration of
  ComputableModelTheory appears in them, so its revision does not bear on them.
* Neither the count of `ℵ₁` classes nor thinness is attempted.

## Applicability of the existing counting infrastructure

* **Language.**  `templateSentence.{0}` is a sentence of `baseTemplateLanguage.{0}`, a relational
  language in `Language.{0, 1}`, the universes of `HasThinAlephOneSpectrum`.  Its countability,
  `Countable (Σ n, baseTemplateLanguage.{u}.Relations n)`, is proved
  (`baseLanguageCountableTarget`) and is an instance here, so `Theorem436Target` has no premise.
* **Coded models and isomorphism.**  The coded models live on `ℕ`, a nonempty carrier, so the
  model on the empty carrier (`realize_templateSentence_of_isEmpty`) is not among them.  The
  variant on all countable carriers, `MainTheorem.HasThinAlephOneSpectrumOnCountableCarriers`, is
  **not** stated: its comparison with the coded statement
  (`hasThinAlephOneSpectrumOnCountableCarriers_iff`) assumes no finite models, which fails for
  `σ[L]` at the empty carrier.  The passage to all countable **nonempty** carriers is the named
  requirement `NonemptyCarrierPassageTarget`, with its infinitude part
  `TemplateModelInfiniteTarget` (from the level-zero correspondence
  `realize_templateSentence_iff_exists_lift` and `infinitudeTarget` at `β = 0`).
* **Counting.**  `Counting.mk_eq_aleph_one_of_rank` (exactly `ℵ₁` elements from a rank into the
  countable ordinals with countable fibres on an uncountable type) applies to
  `Quotient (isoSetoid templateSentence.{0})`, with the rank the **maximal stage**, below.
  `MainTheorem.hasThinAlephOneSpectrum_of_filtration` needs uniformity of every sentence on a
  filtration, a different input, and is not the route here.
* **Thinness.**  `MainTheorem.isThinOnNatModels_of_countable_bfClasses` (no perfect set of pairwise
  nonisomorphic coded models from countably many classes of `bfEquivSetoid φ η` for every
  `η < ω₁`) applies to any sentence of a countable relational language, `templateSentence.{0}`
  included.

## The proof plan for `Theorem436Target`

Write `X = Quotient (isoSetoid templateSentence.{0})`, the classes of models of `σ[L]` coded on
`ℕ`.  Every such model `B` has a unique maximal lift `(γ_B, H_B)` on `ℕ`
(`sentenceMaximalLiftTarget`, `ℕ` countable and nonempty).

1. **The maximal stage is a rank on `X`.**  `γ_B` depends only on the class of `B`
   (`maximalStageInvariantTarget`).  Write `r : X → Ordinal`; `r < ω₁`.
2. **Countable fibres.**  The classes with `r = γ` are classes of base reducts of structures
   maximal at `γ` on `ℕ`; by (b) (`uniformMaximalRepresentativesTarget`) each such structure is
   isomorphic in the full language to a member of the countable set `S γ`, and a full isomorphism
   restricts to an isomorphism of base reducts (`baseReductEquiv`).  So the fibre over `γ` is
   countable.
3. **Unbounded, hence uncountable.**  For every `β < ω₁` there is a structure maximal at some
   `γ ≥ β` on `ℕ` (`unboundedMaximalStagesTarget`); its base reduct is a coded model of `σ[L]`
   (`templateBaseModelsTarget`) of rank `γ`.  A rank into `ω₁` with unbounded values is not
   countable.  This replaces the printed use of (d) and [AFK26, Lemma 2.22] for the lower bound.
4. **Exactly `ℵ₁`.**  `Counting.mk_eq_aleph_one_of_rank` with 1–3.
5. **Thinness.**  For `η < ω₁`, the classes of rank `< η` are countably many (2 at each level
   below `η`); a class of rank `≥ η` has the lift `τ_η(H_B) ∈ K_η[L]` (`projectionTarget`), and two
   members of `K_η[L]` realizing a common invariant have back-and-forth equivalent base reducts at
   level `η` ([AFK26, Proposition 2.18] for `K[L]`, from `WeakSystemClausesTarget` and
   `TemplateInvariantSystemTarget`, with the comparison of its levels with InfinitaryLogic's
   `BFEquiv`); a member of `K_η[L]` realizes some invariant fixed by `τ_η`, and these are countably
   many.  So `bfEquivSetoid templateSentence.{0} η` has countably many classes, and
   `MainTheorem.isThinOnNatModels_of_countable_bfClasses` gives thinness.  This is the argument of
   [AFK26, Theorem 2.19 and Theorem 2.25 (b)].

## The remaining inputs, with their status

Each entry: the input, its name, its status, and its carrier convention.

* The four conditions [AFK26, Definition 2.23]: `knightSystemTarget`.  Proved.  Countable
  carriers, countably infinite for (d); nonemptiness automatic for members of `K[L]`.
* The base is the class of models of `σ[L]` [AFK26, Theorem 4.23]: `templateBaseModelsTarget`.
  Proved.  Countable carrier, premise `Nonempty M`.
* The weak-system clauses for `ID[L]` [AFK26, Definition 2.17]: `WeakSystemClausesTarget`.
  Stated.  Countable carrier.
* The invariant system of the legal classes [AFK26, Definitions 2.6 and 2.8, Lemma 4.19]:
  `TemplateInvariantSystemTarget`.  Stated.  No carrier.
* Countability of `L_c[L]`: `baseLanguageCountableTarget`.  Proved.  No carrier.
* A full isomorphism restricts to the base reducts: `baseReductEquiv`,
  `baseReductEquivTarget`.  Proved.  Any carriers.
* The maximal stage is an isomorphism invariant: `maximalStageInvariantTarget`.  Proved.
  Countable carriers `M`, `N`.
* Unbounded maximal stages on `ℕ`: `unboundedMaximalStagesTarget`.  Proved.  `ℕ`.
* Infinitude of the countable nonempty models of `σ[L]`: `TemplateModelInfiniteTarget`.  Stated
  (a named requirement).  Countable nonempty carriers.
* The passage from the models coded on `ℕ` to all countable nonempty carriers:
  `NonemptyCarrierPassageTarget`.  Stated (a named requirement).  Countable nonempty carriers.
* Exactly `ℵ₁` classes, steps 1–4.  Open (assembly).  Models coded on `ℕ`.
* [AFK26, Proposition 2.18] for `K[L]`, with its levels compared with InfinitaryLogic's
  `BFEquiv`.  Open (a back-and-forth system; not yet named).  Countable carriers.
* Thinness, step 5.  Open (assembly).  Models coded on `ℕ`.
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The countability of `L_c[L]` -/

/-- **Target: `L_c[L]` is countable**: countably many relation symbols of `baseTemplateLanguage`
in all arities.  Proved (`baseLanguageCountableTarget`).  Correspondence with the printed
definitions. -/
def BaseLanguageCountableTarget : Prop :=
  Countable (Σ n, baseTemplateLanguage.{u}.Relations n)

/-- **`L_c[L]` is countable** (`BaseLanguageCountableTarget`): in each arity the symbols `P_n` and
`R_c` (`τ₀(c) = c`) inject (`baseInclusion_injective`) into the symbols of `L_b[L] ∪ L_c[L]` that
are not invariants (`not_isInvariant_toTemplateSymbol`), a countable set
(`TemplateSymbol.countable_setOf_not_isInvariant`); a sigma type over `ℕ` of countable types is
countable.  Correspondence with the printed definitions. -/
theorem baseLanguageCountableTarget : BaseLanguageCountableTarget.{u} := by
  have h (n : ℕ) : Countable (baseTemplateLanguage.{u}.Relations n) := by
    have := (TemplateSymbol.countable_setOf_not_isInvariant.{u} n).to_subtype
    exact Function.Injective.countable
      (f := fun r : BaseSymbol.{u} n ↦ (⟨r.toTemplateSymbol, not_isInvariant_toTemplateSymbol r⟩ :
        {r : TemplateSymbol.{u} n | ¬ r.IsInvariant}))
      fun a b hab ↦ baseInclusion_injective.onRelation (congrArg Subtype.val hab)
  exact (inferInstance : Countable (Σ n, baseTemplateLanguage.{u}.Relations n))

instance : Countable (Σ n, baseTemplateLanguage.{u}.Relations n) :=
  baseLanguageCountableTarget

/-! ### The statement -/

/-- **Target: [AFK26, Theorem 4.36]** for `σ[L]` itself (`templateSentence`, at universe `0`):
the models of `σ[L]` coded on `ℕ` have exactly `ℵ₁` isomorphism classes, and there is no perfect
set of pairwise nonisomorphic coded models (`MainTheorem.HasThinAlephOneSpectrum`).  The
countability of the language is the instance from `baseLanguageCountableTarget`.  Not identified
with any statement about `baseLanguage.densitySentence`.  Stated; open; the proof plan is in the
module docstring.  Correspondence with the printed definitions. -/
def Theorem436Target : Prop :=
  MainTheorem.HasThinAlephOneSpectrum templateSentence.{0}

/-! ### The passage to countable nonempty carriers -/

/-- **Target (a named requirement): the countable nonempty models of `σ[L]` are infinite**: on a
countable nonempty carrier, a model of `σ[L]` has a lift in `K_0[L]`
(`realize_templateSentence_iff_exists_lift`), whose carrier is infinite (`infinitudeTarget` at
`β = 0`).  The structure on the empty carrier is a model (`realize_templateSentence_of_isEmpty`), so
`Nonempty M` is needed.  Stated; not proved.  Correspondence with the printed definitions. -/
def TemplateModelInfiniteTarget (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    @Sentenceω.Realize _ templateSentence.{u} M B → Infinite M

/-- **Target (a named requirement): the passage from the models coded on `ℕ` to all countable
nonempty carriers**: every model of `σ[L]` on a countable nonempty carrier in the universe `w` is
infinite and isomorphic, in `L_c[L]`, to the structure of a coded model of `σ[L]` on `ℕ`.  Route:
`TemplateModelInfiniteTarget`, then the reduction to `ℕ`
(`MainTheorem.exists_mem_modelsOf_equiv`).  With it, the classes of models of `σ[L]` on countable
nonempty carriers of `w` correspond to the coded classes of `Theorem436Target`; on all countable
carriers there is exactly one further class, the empty model.  Stated; not proved.
Correspondence with the printed definitions. -/
def NonemptyCarrierPassageTarget : Prop :=
  ∀ (M : Type w) [Countable M] [Nonempty M] (B : baseTemplateLanguage.{0}.Structure M),
    @Sentenceω.Realize _ templateSentence.{0} M B →
      Infinite M ∧ ∃ c : StructureSpace baseTemplateLanguage.{0},
        c ∈ ModelsOf templateSentence.{0} ∧
          Nonempty (@Language.Equiv baseTemplateLanguage.{0} M ℕ B c.toStructure)

/-! ### Inputs of the count -/

section Inputs

variable {M : Type v} {N : Type w}

/-- **A full isomorphism restricts to the base reducts**: an isomorphism `G ≃ H` in
`L_b[L] ∪ L_c[L]` is, by the same bijection, an isomorphism `G↾L_c[L] ≃ H↾L_c[L]` (each base
symbol is read as its image, `relMap_baseReduct`).  Correspondence with the printed
definitions. -/
def baseReductEquiv {G : templateLanguage.{u}.Structure M} {H : templateLanguage.{u}.Structure N}
    (g : @Language.Equiv templateLanguage.{u} M N G H) :
    @Language.Equiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H) :=
  @Language.Equiv.mk baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H)
    (@Language.Equiv.toEquiv templateLanguage.{u} M N G H g) (fun f ↦ Empty.elim f)
    (fun r xs ↦
      @Language.Equiv.map_rel' templateLanguage.{u} M N G H g _ (BaseSymbol.toTemplateSymbol r) xs)

/-- The restriction to the base reducts has the same bijection.  Correspondence with the printed
definitions. -/
@[simp] theorem toEquiv_baseReductEquiv {G : templateLanguage.{u}.Structure M}
    {H : templateLanguage.{u}.Structure N} (g : @Language.Equiv templateLanguage.{u} M N G H) :
    @Language.Equiv.toEquiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H)
      (baseReductEquiv g) = @Language.Equiv.toEquiv templateLanguage.{u} M N G H g :=
  rfl

variable (M N) in
/-- **Target: a full isomorphism restricts to an isomorphism of base reducts**: structures of
`L_b[L] ∪ L_c[L]` isomorphic in the full language have isomorphic base reducts.  Proved
(`baseReductEquivTarget`, by `baseReductEquiv`).  Correspondence with the printed definitions. -/
def BaseReductEquivTarget : Prop :=
  ∀ (G : templateLanguage.{u}.Structure M) (H : templateLanguage.{u}.Structure N),
    Nonempty (@Language.Equiv templateLanguage.{u} M N G H) →
      Nonempty (@Language.Equiv baseTemplateLanguage.{u} M N (baseReduct G) (baseReduct H))

variable (M N) in
/-- **A full isomorphism restricts to an isomorphism of base reducts** (`BaseReductEquivTarget M N`
for every `M`, `N`).  Correspondence with the printed definitions. -/
theorem baseReductEquivTarget : BaseReductEquivTarget.{u} M N :=
  fun _ _ ⟨g⟩ ↦ ⟨baseReductEquiv g⟩

end Inputs

/-- **Target: the maximal stage is an isomorphism invariant**: on countable carriers `M` and `N`,
if `H` is maximal at `γ < ω₁` on `M`, `H'` is maximal at `γ' < ω₁` on `N`, and their base reducts
are isomorphic, then `γ = γ'` and `H ≅ H'` in the full language.  Proved
(`maximalStageInvariantTarget`).  Correspondence with the printed definitions. -/
def MaximalStageInvariantTarget (M : Type v) (N : Type v) : Prop :=
  Countable M → Countable N → ∀ (γ γ' : Ordinal.{u}) (H : templateLanguage.{u}.Structure M)
    (H' : templateLanguage.{u}.Structure N), γ < ω₁ → γ' < ω₁ → IsMaximalAt γ H →
    IsMaximalAt γ' H' →
    Nonempty (@Language.Equiv baseTemplateLanguage.{u} M N (baseReduct H) (baseReduct H')) →
      γ = γ' ∧ Nonempty (@Language.Equiv templateLanguage.{u} M N H H')

/-- **The maximal stage is an isomorphism invariant** (`MaximalStageInvariantTarget M N` for every
`M`, `N`).  Transport `H'` to `M` along the inverse of the base isomorphism `e`: it is maximal at
`γ'` (`IsMaximalAt.transportStructure`) with the base reduct of `H`
(`baseReduct_transportStructure`, `FirstOrder.Language.Equiv.inducedStructure_eq`), so `γ = γ'` by
uniqueness of the maximal lift on `M` (`maximalLiftUniqueTarget`); then `e` is a full isomorphism by
Reconstruction at `γ` (`nonempty_equiv_of_baseReduct_equiv`).  Countability of `N` is not used.
Correspondence with the printed definitions. -/
theorem maximalStageInvariantTarget (M : Type v) (N : Type v) :
    MaximalStageInvariantTarget.{u} M N := by
  rintro hc - γ γ' H H' hγ hγ' hH hH' ⟨e⟩
  set e₀ := @Language.Equiv.toEquiv baseTemplateLanguage.{u} M N (baseReduct H) (baseReduct H') e
  have hbase : baseReduct (transportStructure e₀.symm H') = baseReduct H := by
    rw [baseReduct_transportStructure]
    exact @Language.Equiv.inducedStructure_eq baseTemplateLanguage.{u} N M (baseReduct H')
      (baseReduct H)
      (@Language.Equiv.symm baseTemplateLanguage.{u} M N (baseReduct H) (baseReduct H') e)
  obtain ⟨rfl, -⟩ := maximalLiftUniqueTarget M hc γ γ' H _ hγ hγ' hH
    (hH'.transportStructure e₀.symm) hbase.symm
  have := hc
  obtain ⟨g, -⟩ := nonempty_equiv_of_baseReduct_equiv hγ hH.1 hH'.1 e
  exact ⟨rfl, ⟨g⟩⟩

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
