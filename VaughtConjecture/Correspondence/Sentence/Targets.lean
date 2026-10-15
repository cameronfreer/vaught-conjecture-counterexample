/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Sentence.TemplateSentence
import VaughtConjecture.Correspondence.StronglyCodedOccurrence

/-!
# Targets for the sentence `σ[L]`: B.T12, B.T18 and B.T19

Numbering as in the current draft of [AFK26].  `σ[L]` is `templateSentence`
(`VaughtConjecture.Correspondence.Sentence.TemplateSentence`), `K_β[L]` is
`templateStageClass M β`, and `N↾L_c[L]` is `baseReduct N`.

* **B.T12, the sentence and the lifts at level zero** (`SentenceCorrespondenceTarget M`, proved
  as `sentenceCorrespondenceTarget` in
  `VaughtConjecture.Correspondence.Sentence.Correspondence`, where `Countable M` is not used): on
  a countable nonempty carrier, a structure `B` of `L_c[L]` satisfies `σ[L]`
  exactly when some `G ∈ K₀[L]` on the same carrier has `G↾L_c[L] = B` ([AFK26, Theorem 4.23],
  the base of `K[L]` at level zero).  **Level zero is the label stage `blockStage 0 = ω`**, not
  the literal stage `0`: `templateStageClass M 0` asks for `τ₀(G) = G`, the projection to
  `ω + ω · 0 = ω` (`blockStage_zero`), and for `D[α]` for every `α < blockStage 0 = ω`, the
  finite cutoffs `k ∈ ω` of clause (d).
* **The empty carrier** (proved): every clause of `σ[L]` is a conjunction of universal closures
  over at least one variable, so the structure on an empty carrier satisfies `σ[L]`
  (`realize_templateSentence_of_isEmpty`), while `K_β[L]` has nonempty carriers by the convention
  of [AFK26, §1] (`templateStageClass_eq_empty_of_isEmpty`).  So B.T12 fails on an empty carrier
  (`realize_templateSentence_and_not_exists_lift_of_isEmpty`), and the target assumes
  `Nonempty M`, the printed convention, rather than adding a clause to the printed sentence.
* **B.T18, the projections** (proved; immediate from the conjunction): `σ[L]` gives (Singletons)
  `∀ x, P_1(x)` (`singletonsProjectionTarget`) and the first sentence of clause (b) at arity `1`,
  `∀ x, P_1(x) ↔ ⋁_{t ∈ cR[L]^1} R_t(x)` (`typingProjectionTarget`), in every structure of
  `L_c[L]`.
* **B.T19, clause (5) and the class reading** (proved; a composition of existing theorems).  The
  class reading `classSymbolReading M` of a structure of the positional base language reads
  `R_t` as the disjunction of the positional symbols in the renaming class of `t`
  (`SymbolReading.ofClasses`).
  - Clause (5) for the chosen templates (`chosenTemplateTarget`): every representative of a class
    `t ∈ cR[L]` is a legal template of [AFK26, Definition 4.29] with labels in
    `{-∞} ∪ ω₁ ∪ {∞}`, by `TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate`; its
    rows are strongly coded, which is clause (5).
  - Every positional member of the class of `t` is a cell renaming of the scheme of the chosen
    representative `Quotient.out t` (`positionalMemberTarget`).
  - Hence the class reading presents strongly coded templates (`classReadingTarget`), by
    `SymbolReading.presentsStronglyCoded_ofClasses_of_isCellRenaming` with
    `Scheme.IsCellRenaming.isStronglyCoded_iff`.

These are what the compiled incompatibility
`baseLanguage.not_singletons_and_typing_of_realize_densitySentence` asks of a reading; their
composition with it is D8, proved in `VaughtConjecture.Correspondence.Sentence.Dictionary` for the
class reading only.  Nothing here identifies `σ[L]` with
the density sentence, and no correspondence of model classes beyond the targets stated is claimed.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal BoundedFormulaω TemplateSentence

/-! ### B.T12 -/

/-- **Target B.T12, the sentence `σ[L]` and the lifts at level zero**: on a countable nonempty
carrier `M`, a structure `B` of `L_c[L]` satisfies `σ[L]` exactly when there is `G ∈ K₀[L]` on
`M` with `G↾L_c[L] = B` (literal reduct, same carrier).  Level zero is the label stage
`blockStage 0 = ω`.  `Nonempty M` is the printed convention of [AFK26, §1]; without it the
statement fails (`realize_templateSentence_and_not_exists_lift_of_isEmpty`).  Proved as
`sentenceCorrespondenceTarget`.  Correspondence with the printed definitions. -/
def SentenceCorrespondenceTarget (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    (@Sentenceω.Realize _ templateSentence.{u} M B ↔
      ∃ G ∈ templateStageClass M (0 : Ordinal.{u}), baseReduct G = B)

section Empty

variable {M : Type v} [IsEmpty M]

/-- On an empty carrier, a universal closure over at least one variable holds.
Native construction. -/
private theorem realize_alls_of_isEmpty [baseTemplateLanguage.{u}.Structure M] {n : ℕ}
    (φ : baseTemplateLanguage.{u}.BoundedFormulaω Empty n) (hn : 0 < n) :
    BoundedFormulaω.Realize φ.alls (Empty.elim : Empty → M) Fin.elim0 :=
  (realize_alls φ).mpr fun ys ↦ isEmptyElim (ys ⟨0, hn⟩)

/-- **`σ[L]` holds on an empty carrier**: every clause is a conjunction of universal closures over
at least one variable.  Correspondence with the printed definitions. -/
theorem realize_templateSentence_of_isEmpty [baseTemplateLanguage.{u}.Structure M] :
    templateSentence.{u}.Realize M := by
  simp only [templateSentence, planClause, structureClause, geometryDistinctClause,
    geometryPermClause, geometryExtensionClause, geometryIntersectionClause, singletonsClause,
    convexityClause, extremePointsClause, extremePointsExclusionClause, typingClause,
    exclusivityClause, determinationClause, diagramClause, densityClause, Sentenceω.realize_def,
    realize_inf, realize_ciInf]
  and_intros
  all_goals intros
  all_goals (try and_intros)
  all_goals intros
  all_goals exact realize_alls_of_isEmpty _ (by omega)

/-- **`K_β[L]` is empty on an empty carrier**: its structures have nonempty carriers, the
convention of [AFK26, §1].  Correspondence with the printed definitions. -/
theorem templateStageClass_eq_empty_of_isEmpty (β : Ordinal.{u}) :
    templateStageClass M β = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hG ↦ isEmptyElim (nonempty_of_mem_templateStageClass hG).some

/-- **B.T12 fails on an empty carrier**: the structure satisfies `σ[L]` and has no lift in
`K₀[L]`.  This is why `SentenceCorrespondenceTarget` assumes `Nonempty M`.
Correspondence with the printed definitions. -/
theorem realize_templateSentence_and_not_exists_lift_of_isEmpty
    (B : baseTemplateLanguage.{u}.Structure M) :
    @Sentenceω.Realize _ templateSentence.{u} M B ∧
      ¬ ∃ G ∈ templateStageClass M (0 : Ordinal.{u}), baseReduct G = B := by
  refine ⟨realize_templateSentence_of_isEmpty, ?_⟩
  rintro ⟨G, hG, -⟩
  rw [templateStageClass_eq_empty_of_isEmpty] at hG
  exact hG

end Empty

/-! ### B.T18 -/

/-- **Target B.T18, (Singletons)**: in every structure of `L_c[L]` satisfying `σ[L]`,
`∀ x, P_1(x)` ([AFK26, Definition 4.13], through clause (a) of Definition 4.22).
Correspondence with the printed definitions. -/
def SingletonsProjectionTarget : Prop :=
  ∀ (M : Type v) (C : baseTemplateLanguage.{u}.Structure M),
    @Sentenceω.Realize _ templateSentence.{u} M C →
      ∀ x : M, RelMap (L := baseTemplateLanguage.{u}) (self := C) (BaseSymbol.closed Nat.one_pos)
        ![x]

/-- **Target B.T18, typing at arity `1`**: in every structure of `L_c[L]` satisfying `σ[L]`,
`∀ x, P_1(x) ↔ ⋁_{t ∈ cR[L]^1} R_t(x)` (the first sentence of [AFK26, Definition 4.22 (b)] at
arity `1`).  Correspondence with the printed definitions. -/
def TypingProjectionTarget : Prop :=
  ∀ (M : Type v) (C : baseTemplateLanguage.{u}.Structure M),
    @Sentenceω.Realize _ templateSentence.{u} M C →
      ∀ x : M, (RelMap (L := baseTemplateLanguage.{u}) (self := C) (BaseSymbol.closed Nat.one_pos)
        ![x] ↔ ∃ t : ClassSymbol.{u} 1,
          RelMap (L := baseTemplateLanguage.{u}) (self := C) (t.toBaseSymbol Nat.one_pos) ![x])

/-- `σ[L]` gives clause (a) and clause (b).  Correspondence with the printed definitions. -/
private theorem realize_singletons_typing {M : Type v} [baseTemplateLanguage.{u}.Structure M]
    (h : templateSentence.{u}.Realize M) :
    singletonsClause.{u}.Realize M ∧ typingClause.{u}.Realize M := by
  simp only [templateSentence, planClause, structureClause, Sentenceω.realize_def,
    realize_inf] at h ⊢
  exact ⟨h.1.1.1.1.1.1.2, h.1.1.2.1.1⟩

/-- **B.T18, (Singletons), proved.**  Correspondence with the printed definitions. -/
theorem singletonsProjectionTarget : SingletonsProjectionTarget.{u, v} := by
  intro M C h x
  have hs := (@realize_singletons_typing M C h).1
  simp only [singletonsClause, Sentenceω.realize_def, realize_alls] at hs
  exact hs ![x]

/-- **B.T18, typing at arity `1`, proved.**  Correspondence with the printed definitions. -/
theorem typingProjectionTarget : TypingProjectionTarget.{u, v} := by
  intro M C h x
  have ht := (@realize_singletons_typing M C h).2
  simp only [typingClause, Sentenceω.realize_def, realize_ciInf, realize_alls, realize_iff,
    realize_ciSup] at ht
  exact ht 0 ![x]

/-! ### B.T19 -/

/-- **The class reading** of the symbols `cR[L]` in a structure of the positional base language:
`R_t` holds of a tuple when some positional symbol `p` in the renaming class of `t` holds of it
(`SymbolReading.ofClasses`); the members of the class of `t` are the `p` whose type has class `t`
at `ω₁`.  Correspondence with the printed definitions. -/
def classSymbolReading (M : Type v) [baseLanguage.{u}.Structure M] :
    baseLanguage.SymbolReading.{v, u + 1} M :=
  baseLanguage.SymbolReading.ofClasses (M := M) ClassSymbol.{u}
    fun _ t ↦ {p | (baseLanguage.type p).globalClass = t.1.1}

/-- **Target B.T19, clause (5) for the chosen templates**: every representative `r` of a class
`t ∈ cR[L]` (in particular the template that `L` chooses in that class) is a legal template of
[AFK26, Definition 4.29] with labels in `{-∞} ∪ ω₁ ∪ {∞}`, and its rows are strongly coded, the
range clause (5).  Correspondence with the printed definitions. -/
def ChosenTemplateTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (t : ClassSymbol.{u} n) (r : StageType.{u} ω₁ n), r.toClass = t.1.1 →
    r.IsLegalTemplate ω₁ ∧ r.rows.IsStronglyCoded

/-- **Target B.T19, the positional members**: every positional symbol `p` in the renaming class of
`t ∈ cR[L]` has a scheme that is a cell renaming of the scheme of the chosen representative
`Quotient.out t`.  Correspondence with the printed definitions. -/
def PositionalMemberTarget : Prop :=
  ∀ ⦃n : ℕ⦄ (t : ClassSymbol.{u} n) (p : baseLanguage.{u}.Relations n),
    (baseLanguage.type p).globalClass = t.1.1 →
      ∃ e : Fin (baseLanguage.type p).card ≃ Fin (Quotient.out t.1.1).card,
        (Quotient.out t.1.1).toScheme.IsCellRenaming (baseLanguage.type p).toScheme e

/-- **Target B.T19, the class reading presents strongly coded templates**, in every structure of
the positional base language.  Correspondence with the printed definitions. -/
def ClassReadingTarget : Prop :=
  ∀ (M : Type v) [baseLanguage.{u}.Structure M], (classSymbolReading M).PresentsStronglyCoded

/-- A cell renaming of stage types is a cell renaming of their schemes.  Native construction. -/
theorem StageType.IsCellRenaming.exists_scheme_isCellRenaming {α : Ordinal.{u}} {n : ℕ}
    {s t : StageType.{u} α n} (h : s.IsCellRenaming t) :
    ∃ e : Fin t.card ≃ Fin s.card, s.toScheme.IsCellRenaming t.toScheme e := by
  obtain ⟨k, σ, rfl⟩ := h
  exact ⟨σ, rfl, rfl, fun _ ↦ rfl, rfl⟩

/-- **B.T19, clause (5) for the chosen templates, proved**, from
`TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate`.
Correspondence with the printed definitions. -/
theorem chosenTemplateTarget : ChosenTemplateTarget.{u} := by
  intro n t r hr
  have h : r.toClass.IsStronglyCodedLegal := hr ▸ t.1.2
  exact ⟨(TemplateClass.isStronglyCodedLegal_toClass_iff_isLegalTemplate le_rfl r).mp h, h.2⟩

/-- **B.T19, the positional members, proved**: the class of `p` at `ω₁` is the class of the
chosen representative, and at a stage at most `ω₁` equal classes are cell renamings.
Correspondence with the printed definitions. -/
theorem positionalMemberTarget : PositionalMemberTarget.{u} := by
  intro n t p hp
  have h : (baseLanguage.type p).globalClass = (Quotient.out t.1.1).toClass := by
    rw [hp]
    exact (Quotient.out_eq _).symm
  have h' : (Quotient.out t.1.1).IsCellRenaming
      ((baseLanguage.type p).reduce (Cardinal.isSuccLimit_omega 1).isSuccPrelimit) :=
    (StageType.toClass_eq_toClass_iff.mp h).symm
  exact h'.exists_scheme_isCellRenaming

/-- **B.T19, the class reading presents strongly coded templates, proved**, by
`SymbolReading.presentsStronglyCoded_ofClasses_of_isCellRenaming` with the chosen representatives
`Quotient.out t`.  Correspondence with the printed definitions. -/
theorem classReadingTarget : ClassReadingTarget.{u, v} := by
  intro M _
  refine baseLanguage.SymbolReading.presentsStronglyCoded_ofClasses_of_isCellRenaming
    (fun _ t ↦ (Quotient.out t.1.1).toScheme) (fun _ t ↦ ?_) (fun _ t p hp ↦ ?_)
  · exact (chosenTemplateTarget t _ (Quotient.out_eq _)).2
  · exact positionalMemberTarget t p hp

end VaughtConjecture
