/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.Theorem436

/-!
# Exactly `ℵ₁` classes of models of `σ[L]`: the count of [AFK26, Theorem 4.36]

Numbering as in the current draft of [AFK26].  `σ[L]` is `templateSentence.{0}`, a sentence of
`baseTemplateLanguage.{0}` (`L_c[L]`); its models coded on `ℕ` are InfinitaryLogic's
`ModelsOf templateSentence.{0}`, and their isomorphism classes, in `L_c[L]`, are
`Quotient (isoSetoid templateSentence.{0})`.  This file proves that there are exactly `ℵ₁`
classes (`templateSentenceAlephOneTarget`), the first conjunct of
`MainTheorem.HasThinAlephOneSpectrum templateSentence.{0}` (`Theorem436Target`).  Thinness, the
second conjunct, is not addressed here.

## The maximal stage of a class

Every coded model `B` of `σ[L]` (on `ℕ`, countable and nonempty) has a unique maximal lift
`(γ, H)` on `ℕ`: `γ < ω₁`, `H` maximal at `γ`, `H↾L_c[L] = B` (`sentenceMaximalLiftTarget`).  The
**maximal stage** of `B` is `γ` (`codedMaximalStage`), and it depends only on the class of `B`
(`maximalStageInvariantTarget`), which gives `maximalStageOfClass`.

**The greatest lift stage, not the least projection-fixing stage.**  The maximal stage is the
level at which the unique maximal lift is maximal ([AFK26, Definition 2.20]), the greatest lift
stage of `B` (`MaximalIffGreatestTarget`).  It is defined using the greatest lift stage, rather
than the least projection-fixing stage (`IsLeast (fixingStages G) ρ`, `Boundedness/Rank`,
`liftRanks`).  No equality or inequality between these notions is asserted or used here.

## The count

`Counting.mk_eq_aleph_one_of_rank` with the maximal stage as the rank:

* **below `ω₁`** (`maximalStageOfClass_lt`): by `sentenceMaximalLiftTarget`;
* **countable fibres** (`countable_setOf_maximalStageOfClass_eq`): a class of maximal stage `γ`
  has a maximal lift isomorphic, in the full language, to a member of the countable set `S γ` of
  (b) (`uniformMaximalRepresentativesTarget`); two classes sent to the same member have
  isomorphic maximal lifts, hence isomorphic base reducts (`baseReductEquiv`), hence are equal;
* **not countable** (`not_countable_templateClasses`): the maximal stages are unbounded below `ω₁`
  (`exists_le_maximalStageOfClass`, from `unboundedMaximalStagesTarget`, the base identification
  `templateBaseModelsTarget`, the reduction to `ℕ` `MainTheorem.exists_mem_modelsOf_equiv`, and
  `maximalStageInvariantTarget`), and a countable set of classes has bounded maximal stages
  (InfinitaryLogic's `InfinitaryLogic.countable_iff_rank_bounded`).

No premise beyond the statement; the four conditions are used only through (b), and (d) is not
used.
-/

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### The maximal stage of a coded model -/

/-- A coded model of `σ[L]` satisfies `σ[L]` on `ℕ` (InfinitaryLogic's
`mem_modelsOf_iff_realize`).  Correspondence with the printed definitions. -/
theorem realize_templateSentence_of_mem_modelsOf (c : ModelsOf templateSentence.{0}) :
    @Sentenceω.Realize _ templateSentence.{0} ℕ c.1.toStructure :=
  (mem_modelsOf_iff_realize c.1 _).mp c.2

/-- **The maximal lift of a coded model of `σ[L]`**: the unique pair `(γ, H)` on `ℕ` with
`γ < ω₁`, `H` maximal at `γ`, and `H↾L_c[L]` the coded structure (`sentenceMaximalLiftTarget`).
Correspondence with the printed definitions. -/
def codedMaximalLift (c : ModelsOf templateSentence.{0}) :
    Ordinal.{0} × templateLanguage.{0}.Structure ℕ :=
  (sentenceMaximalLiftTarget ℕ inferInstance inferInstance c.1.toStructure
    (realize_templateSentence_of_mem_modelsOf c)).exists.choose

/-- The maximal lift of a coded model is at a countable level, maximal there, and has the coded
structure as its base reduct.  Correspondence with the printed definitions. -/
theorem codedMaximalLift_spec (c : ModelsOf templateSentence.{0}) :
    (codedMaximalLift c).1 < ω₁ ∧ IsMaximalAt (codedMaximalLift c).1 (codedMaximalLift c).2 ∧
      baseReduct (codedMaximalLift c).2 = c.1.toStructure :=
  (sentenceMaximalLiftTarget ℕ inferInstance inferInstance c.1.toStructure
    (realize_templateSentence_of_mem_modelsOf c)).exists.choose_spec

/-- **The maximal stage of a coded model of `σ[L]`**: the level `γ` of its unique maximal lift.
Defined using the greatest lift stage, rather than the least projection-fixing stage
(`fixingStages`, `liftRanks`); no equality or inequality between these notions is asserted or
used here.  Correspondence with the printed definitions. -/
def codedMaximalStage (c : ModelsOf templateSentence.{0}) : Ordinal.{0} :=
  (codedMaximalLift c).1

/-- **Isomorphic coded models have the same maximal stage**: their maximal lifts have isomorphic
base reducts, so `maximalStageInvariantTarget` applies.  Correspondence with the printed
definitions. -/
theorem codedMaximalStage_eq_of_rel {a b : ModelsOf templateSentence.{0}}
    (h : (isoSetoid templateSentence.{0}).r a b) : codedMaximalStage a = codedMaximalStage b := by
  obtain ⟨ha1, ha2, ha3⟩ := codedMaximalLift_spec a
  obtain ⟨hb1, hb2, hb3⟩ := codedMaximalLift_spec b
  have h' : Nonempty (@Language.Equiv baseTemplateLanguage.{0} ℕ ℕ
      (baseReduct (codedMaximalLift a).2) (baseReduct (codedMaximalLift b).2)) := by
    rw [ha3, hb3]
    exact h
  exact (maximalStageInvariantTarget ℕ ℕ inferInstance inferInstance _ _ _ _ ha1 hb1 ha2 hb2 h').1

/-! ### The maximal stage of a class -/

/-- **The maximal stage of an isomorphism class** of coded models of `σ[L]`
(`codedMaximalStage` of any representative, `codedMaximalStage_eq_of_rel`).  Defined using the
greatest lift stage, rather than the least projection-fixing stage (`fixingStages`, `liftRanks`);
no equality or inequality between these notions is asserted or used here.  Correspondence with
the printed definitions. -/
def maximalStageOfClass : Quotient (isoSetoid templateSentence.{0}) → Ordinal.{0} :=
  Quotient.lift codedMaximalStage fun _ _ h ↦ codedMaximalStage_eq_of_rel h

/-- The maximal stage of the class of a coded model is its maximal stage.  Correspondence with the
printed definitions. -/
theorem maximalStageOfClass_mk (a : ModelsOf templateSentence.{0}) :
    maximalStageOfClass (Quotient.mk _ a) = codedMaximalStage a :=
  rfl

/-- **The maximal stage is countable** (`sentenceMaximalLiftTarget`).  Correspondence with the
printed definitions. -/
theorem maximalStageOfClass_lt (q : Quotient (isoSetoid templateSentence.{0})) :
    maximalStageOfClass q < ω₁ :=
  Quotient.inductionOn (motive := fun q ↦ maximalStageOfClass q < ω₁) q
    fun a ↦ (codedMaximalLift_spec a).1

/-- **Countable fibres of the maximal stage**: for `γ < ω₁`, countably many classes have maximal
stage `γ`.  Each such class has a maximal lift at `γ`, isomorphic in the full language to a member
of the countable set `S γ` of `uniformMaximalRepresentativesTarget`; the choice of that member is
injective, since isomorphic maximal lifts have isomorphic base reducts (`baseReductEquiv`).
Correspondence with the printed definitions. -/
theorem countable_setOf_maximalStageOfClass_eq {γ : Ordinal.{0}} (hγ : γ < ω₁) :
    {q | maximalStageOfClass q = γ}.Countable := by
  obtain ⟨S, hS⟩ := uniformMaximalRepresentativesTarget.{0}
  obtain ⟨hSc, -, hcov⟩ := hS γ hγ
  have hex (q : {q | maximalStageOfClass q = γ}) : ∃ H ∈ S γ,
      Nonempty (@Language.Equiv templateLanguage.{0} ℕ ℕ (codedMaximalLift q.1.out).2 H) := by
    have hst : codedMaximalStage q.1.out = γ := by
      rw [← maximalStageOfClass_mk, Quotient.out_eq]
      exact q.2
    obtain ⟨-, hmax, -⟩ := codedMaximalLift_spec q.1.out
    have hmax' : IsMaximalAt γ (codedMaximalLift q.1.out).2 :=
      Eq.mp (congrArg (fun a ↦ IsMaximalAt a (codedMaximalLift q.1.out).2) hst) hmax
    exact hcov ℕ _ hmax'
  have := hSc.to_subtype
  refine Set.countable_coe_iff.mp (Function.Injective.countable
    (f := fun q ↦ (⟨(hex q).choose, (hex q).choose_spec.1⟩ : S γ)) fun q q' hqq' ↦ ?_)
  have hH : (hex q).choose = (hex q').choose := congrArg Subtype.val hqq'
  obtain ⟨e⟩ := (hex q).choose_spec.2
  obtain ⟨e'⟩ := (hex q').choose_spec.2
  rw [hH] at e
  have g := @Language.Equiv.comp templateLanguage.{0} ℕ ℕ (codedMaximalLift q.1.out).2
    (hex q').choose ℕ (codedMaximalLift q'.1.out).2
    (@Language.Equiv.symm templateLanguage.{0} ℕ ℕ (codedMaximalLift q'.1.out).2
      (hex q').choose e') e
  have hb := baseReductEquiv g
  rw [(codedMaximalLift_spec q.1.out).2.2, (codedMaximalLift_spec q'.1.out).2.2] at hb
  apply Subtype.ext
  rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
  exact Quotient.sound (s := isoSetoid templateSentence.{0}) ⟨hb⟩

/-- **The maximal stages of the classes are unbounded below `ω₁`**: for every `β < ω₁` some class
has maximal stage at least `β`.  A structure `H` on `ℕ` maximal at `γ ≥ β`
(`unboundedMaximalStagesTarget`) has a base reduct satisfying `σ[L]` (`templateBaseModelsTarget`),
isomorphic to a coded model (`MainTheorem.exists_mem_modelsOf_equiv`), whose maximal stage is `γ`
(`maximalStageInvariantTarget`).  Correspondence with the printed definitions. -/
theorem exists_le_maximalStageOfClass {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ q : Quotient (isoSetoid templateSentence.{0}), β ≤ maximalStageOfClass q := by
  obtain ⟨γ, hβγ, hγ, H, hH⟩ := unboundedMaximalStagesTarget.{0} β hβ
  have hB : @Sentenceω.Realize _ templateSentence.{0} ℕ (baseReduct H) :=
    (templateBaseModelsTarget ℕ inferInstance inferInstance (baseReduct H)).mp
      ⟨γ, hγ, H, hH.1, rfl⟩
  let _ : baseTemplateLanguage.{0}.Structure ℕ := baseReduct H
  obtain ⟨c, hc, ⟨e⟩⟩ := MainTheorem.exists_mem_modelsOf_equiv hB
  obtain ⟨h1, h2, h3⟩ := codedMaximalLift_spec ⟨c, hc⟩
  have e' : Nonempty (@Language.Equiv baseTemplateLanguage.{0} ℕ ℕ (baseReduct H)
      (baseReduct (codedMaximalLift ⟨c, hc⟩).2)) := by
    rw [h3]
    exact ⟨e⟩
  have hγeq := (maximalStageInvariantTarget ℕ ℕ inferInstance inferInstance γ _ H _ hγ h1 hH h2
    e').1
  exact ⟨Quotient.mk _ ⟨c, hc⟩, hβγ.trans_eq hγeq⟩

/-- **The classes of models of `σ[L]` are not countable**: a countable set of classes has maximal
stages bounded below `ω₁` (InfinitaryLogic's `InfinitaryLogic.countable_iff_rank_bounded`, with
`maximalStageOfClass_lt` and `countable_setOf_maximalStageOfClass_eq`), against
`exists_le_maximalStageOfClass`.  Correspondence with the printed definitions. -/
theorem not_countable_templateClasses :
    ¬ Countable (Quotient (isoSetoid templateSentence.{0})) := by
  intro h
  obtain ⟨β, hβ, hb⟩ := (InfinitaryLogic.countable_iff_rank_bounded maximalStageOfClass
    maximalStageOfClass_lt (fun _ hα ↦ (countable_setOf_maximalStageOfClass_eq hα).to_subtype)
    Set.univ).mp Set.countable_univ
  obtain ⟨q, hq⟩ := exists_le_maximalStageOfClass hβ
  exact (hb q (Set.mem_univ q)).not_ge hq

/-! ### Exactly `ℵ₁` classes -/

/-- **Target: exactly `ℵ₁` classes of models of `σ[L]`** [AFK26, Theorem 4.36, the count]: the
models of `σ[L]` (`templateSentence.{0}`) coded on `ℕ` have exactly `ℵ₁` isomorphism classes.
This is the first conjunct of `MainTheorem.HasThinAlephOneSpectrum templateSentence.{0}`
(`Theorem436Target`); thinness is not part of it.  Proved (`templateSentenceAlephOneTarget`).
Correspondence with the printed definitions. -/
def TemplateSentenceAlephOneTarget : Prop :=
  Cardinal.mk (Quotient (isoSetoid templateSentence.{0})) = Cardinal.aleph 1

/-- **Exactly `ℵ₁` classes of models of `σ[L]`** (`TemplateSentenceAlephOneTarget`):
`Counting.mk_eq_aleph_one_of_rank` with the maximal stage as the rank (`maximalStageOfClass_lt`,
`countable_setOf_maximalStageOfClass_eq`, `not_countable_templateClasses`).  Correspondence with
the printed definitions. -/
theorem templateSentenceAlephOneTarget : TemplateSentenceAlephOneTarget :=
  Counting.mk_eq_aleph_one_of_rank maximalStageOfClass_lt
    (fun _ hα ↦ countable_setOf_maximalStageOfClass_eq hα) not_countable_templateClasses

end

end VaughtConjecture
