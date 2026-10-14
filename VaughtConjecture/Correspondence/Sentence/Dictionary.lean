/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.ClassRealization
import VaughtConjecture.Correspondence.Sentence.Targets

/-!
# The dictionary targets of B.T16: inventory

Numbering as in the current draft of [AFK26].  Two different passages between vocabularies are
kept apart here.

* **The chosen vocabulary** (a renaming of symbols).  The printed `σ[L]` names its symbols `R_t`
  by the templates `t` that the template system `L` chooses, one in each renaming class
  ([AFK26, Definition 4.11]).  `templateSentence` names `R_t` by the class of `t`.  For every
  choice of representatives, `t ↦ [t]` is a bijection from the printed symbols onto `cR[L]`
  (`ChosenVocabularyTarget`, proved), extended by `P_n ↦ P_n`; it is one-to-one and changes no
  formula's meaning.
* **The class-disjunction interpretation** (`classStructure`, a genuine interpretation, not a
  renaming).  A structure of the positional base language (`baseLanguage`, one symbol for each
  legal stage type at `ω`) is read as a structure of `L_c[L]` on the same carrier: `R_t` as the
  disjunction of the positional symbols in the renaming class of `t` (the class reading
  `classSymbolReading`), and `P_n` as "typed", the disjunction of all positional symbols of arity
  `n`.  The symbol map is many-to-one, and `P_n` has no positional counterpart.

**Inventory of D1–D9** (statuses as of this file; "the `L`-instance" means the statement for the
template system `L` of legal templates, whose `L_c[L]` is `baseTemplateLanguage`):

* **D1**, a syntactic translation `tr` with `(tr φ).Realize B ↔ φ.Realize (classStructure B)`:
  the `L`-instance is stated (`TranslationTarget`); **new**.
* **D2**, a base isomorphism gives an isomorphism of class structures with the same point map:
  the `L`-instance is stated (`ClassStructureEquivTarget`); **new**.
* **D3**, literal fibres: tuplewise cell renaming gives equal class structures, and conversely.
  The forward `L`-instance is stated (`ClassStructureFibreTarget`); it is a **direct
  specialization** of `Realization.classReading_eq_classReading_iff` with
  `StageType.globalClass_eq_iff` (not yet written).  The converse is **new**, and false for the
  `L`-instance in general: `R_t` sees only strongly coded classes.
* **D4**, isomorphism reflection on countable carriers: **new**; for `L` it needs the strongly
  coded restriction of the converse of D3.  Not stated.
* **D5**, `densitySentence.Realize B → σ[L°].Realize (classStructure B)`: **new**.  Not stated:
  `L°` (the legal templates without clause (5)) has no language here, since
  `baseTemplateLanguage` is fixed to `L`.
* **D6**, `σ[L°].Realize (classStructure B) ↔ densitySentenceRen.Realize B`: **new**.  Not
  stated (`σ[L°]` and `densitySentenceRen` are not defined).
* **D7**, on countable carriers, every model of `σ[L°]` is the class structure of a model of
  `densitySentence` on the same carrier: **new**.  Not stated (`σ[L°]` is not defined).
* **D8**, `densitySentence.Realize B → ¬ σ[L].Realize (classStructure B)`: stated
  (`ClassStructureSeparationTarget`).  A **direct composition** (not yet written) of the compiled
  `baseLanguage.not_singletons_and_typing_of_realize_densitySentence` with B.T18
  (`singletonsProjectionTarget`, `typingProjectionTarget`) and B.T19 (`classReadingTarget`), all
  proved.  Restricted to this reading.
* **D9**, D1–D7 for `σ[L]` through the chosen vocabulary, against a strongly coded density
  sentence: the chosen vocabulary is `ChosenVocabularyTarget`, **proved**.  The rest is **new**
  and not stated (no strongly coded density sentence is defined).

Nothing here compares `σ[L]` with the density sentence beyond D8, which is a separation for the
class reading only; no spectrum transfer and no correspondence of model classes is claimed.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### The chosen vocabulary -/

/-- **The printed symbols `R_t` of `cR[L]^n`** for a choice `ch` of one representative in each
renaming class: the chosen templates `t = ch c` that are legal templates of
[AFK26, Definition 4.29] (labels in `{-∞} ∪ ω₁ ∪ {∞}`) and are fixed by `τ₀`.
Correspondence with the printed definitions. -/
def PrintedClassSymbol (ch : ∀ ⦃n : ℕ⦄, TemplateClass.{u} ω₁ n → StageType.{u} ω₁ n) (n : ℕ) :
    Type (u + 1) :=
  {t : StageType.{u} ω₁ n // (∃ c, ch c = t) ∧ t.IsLegalTemplate ω₁ ∧
    t.toClass.project (isSuccPrelimit_blockStage 0) = t.toClass}

/-- The class of a printed symbol.  Correspondence with the printed definitions. -/
def PrintedClassSymbol.toClassSymbol {ch : ∀ ⦃n : ℕ⦄, TemplateClass.{u} ω₁ n → StageType.{u} ω₁ n}
    {n : ℕ} (t : PrintedClassSymbol ch n) : ClassSymbol.{u} n :=
  ⟨⟨t.1.toClass, (TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate le_rfl t.1).mpr
    t.2.2.1⟩, t.2.2.2⟩

/-- **Target: the chosen vocabulary is the class vocabulary.**  For every choice `ch` of one
representative in each renaming class (`(ch c).toClass = c`, the last two clauses of
[AFK26, Definition 4.11]), `t ↦ [t]` is a bijection from the printed symbols `R_t` of
`cR[L]^n` onto `ClassSymbol n`.  A renaming of symbols, distinct from the class-disjunction
interpretation `classStructure`.  Correspondence with the printed definitions. -/
def ChosenVocabularyTarget : Prop :=
  ∀ (ch : ∀ ⦃n : ℕ⦄, TemplateClass.{u} ω₁ n → StageType.{u} ω₁ n),
    (∀ ⦃n : ℕ⦄ (c : TemplateClass.{u} ω₁ n), (ch c).toClass = c) →
      ∀ n : ℕ, Function.Bijective (PrintedClassSymbol.toClassSymbol (ch := ch) (n := n))

/-- **The chosen vocabulary is the class vocabulary, proved.**
Correspondence with the printed definitions. -/
theorem chosenVocabularyTarget : ChosenVocabularyTarget.{u} := by
  intro ch hch n
  refine ⟨fun t t' h ↦ ?_, fun s ↦ ?_⟩
  · obtain ⟨⟨c, hc⟩, -⟩ := t.2
    obtain ⟨⟨c', hc'⟩, -⟩ := t'.2
    have h' : t.1.toClass = t'.1.toClass := congrArg (fun s : ClassSymbol.{u} n ↦ s.1.1) h
    refine Subtype.ext ?_
    rw [← hc, ← hc'] at h' ⊢
    rw [hch, hch] at h'
    rw [h']
  · have hs : (ch s.1.1).toClass = s.1.1 := hch _
    have h1 : (ch s.1.1).toClass.IsStronglyCodedLegal := by
      rw [hs]
      exact s.1.2
    have h2 : (ch s.1.1).toClass.project (isSuccPrelimit_blockStage 0) = (ch s.1.1).toClass := by
      rw [hs]
      exact s.2
    exact ⟨⟨ch s.1.1, ⟨_, rfl⟩,
      (TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate le_rfl _).mp h1, h2⟩,
      Subtype.ext (Subtype.ext hs)⟩

/-! ### The class-disjunction interpretation -/

/-- The relations of `classStructure`: `P_n` as "typed", `R_t` by the class reading. -/
def classRelMap (M : Type v) [baseLanguage.{u}.Structure M] :
    ∀ {k : ℕ}, BaseSymbol.{u} k → (Fin k → M) → Prop
  | _, .closed _, xs => ∃ p : baseLanguage.{u}.Relations _, RelMap p xs
  | _, .base c h0 _, xs => (classSymbolReading M).holds (⟨c, h0⟩ : ClassSymbol.{u} _) xs

/-- **The class-disjunction interpretation** of a structure of the positional base language as a
structure of `L_c[L]` on the same carrier: `P_n` holds of a tuple when some positional symbol
holds of it ("typed"), and `R_t` when some positional symbol in the renaming class of `t` holds of
it (`classSymbolReading`).  Many-to-one on symbols; not a renaming.
Correspondence with the printed definitions. -/
@[instance_reducible] def classStructure (M : Type v) [baseLanguage.{u}.Structure M] :
    baseTemplateLanguage.{u}.Structure M where
  funMap f := Empty.elim f
  RelMap r xs := classRelMap M r xs

section ClassStructure

variable {M : Type v} [baseLanguage.{u}.Structure M]

@[simp] theorem relMap_classStructure_closed {k : ℕ} (hk : 0 < k) (xs : Fin k → M) :
    RelMap (L := baseTemplateLanguage.{u}) (self := classStructure M) (BaseSymbol.closed hk) xs ↔
      ∃ p : baseLanguage.{u}.Relations k, RelMap p xs :=
  Iff.rfl

@[simp] theorem relMap_classStructure_base {k : ℕ} (t : ClassSymbol.{u} k) (hk : 0 < k)
    (xs : Fin k → M) :
    RelMap (L := baseTemplateLanguage.{u}) (self := classStructure M) (t.toBaseSymbol hk) xs ↔
      (classSymbolReading M).holds t xs :=
  Iff.rfl

end ClassStructure

/-! ### The inventory targets -/

/-- **D1, the `L`-instance (new)**: a syntactic translation of the formulas of `L_c[L]` into the
positional base language, uniform in the structure, with `(tr φ).Realize B ↔
φ.Realize (classStructure B)`.  Correspondence with the printed definitions. -/
def TranslationTarget : Prop :=
  ∃ tr : ∀ ⦃n : ℕ⦄, baseTemplateLanguage.{u}.BoundedFormulaω Empty n →
      baseLanguage.{u}.BoundedFormulaω Empty n,
    ∀ (M : Type v) [baseLanguage.{u}.Structure M] (n : ℕ)
      (φ : baseTemplateLanguage.{u}.BoundedFormulaω Empty n) (xs : Fin n → M),
      ((tr φ).Realize (Empty.elim : Empty → M) xs ↔
        letI := classStructure M
        φ.Realize (Empty.elim : Empty → M) xs)

/-- **D2, the `L`-instance (new)**: an isomorphism of structures of the positional base language
is an isomorphism of their class structures, with the same point map.
Correspondence with the printed definitions. -/
def ClassStructureEquivTarget : Prop :=
  ∀ (M M' : Type v) [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure M']
    (e : M ≃[baseLanguage.{u}] M'),
    ∃ e' : @Language.Equiv baseTemplateLanguage.{u} M M' (classStructure M) (classStructure M'),
      ∀ x, e' x = e x

/-- **D3, forward, the `L`-instance (a direct specialization, not yet written)**: two type
assignments on one carrier whose types are cell renamings of each other, tuple by tuple, have the
same class structure.  The converse is not stated: `R_t` sees only strongly coded classes.
Correspondence with the printed definitions. -/
def ClassStructureFibreTarget : Prop :=
  ∀ (M : Type v) (B B' : baseLanguage.{u}.Structure M),
    @baseLanguage.IsTypeAssignment M B → @baseLanguage.IsTypeAssignment M B' →
      (@baseLanguage.toRealization M B).IsCellRenamingOf (@baseLanguage.toRealization M B') →
        @classStructure M B = @classStructure M B'

/-- **D8 (stated; a direct composition, not yet written)**: a structure of the positional base
language satisfying the density sentence has a class structure that does not satisfy `σ[L]`.
Restricted to the class-disjunction interpretation: the compiled core
`baseLanguage.not_singletons_and_typing_of_realize_densitySentence` with B.T18 and B.T19.
Correspondence with the printed definitions. -/
def ClassStructureSeparationTarget : Prop :=
  ∀ (M : Type v) [baseLanguage.{u}.Structure M], baseLanguage.densitySentence.{u}.Realize M →
    ¬ @Sentenceω.Realize _ templateSentence.{u} M (classStructure M)

end

end VaughtConjecture
