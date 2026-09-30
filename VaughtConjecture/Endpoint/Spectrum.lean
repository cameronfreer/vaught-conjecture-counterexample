/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.CodeTransport
import InfinitaryLogic.Descriptive.ScottDefinability
import InfinitaryLogic.Descriptive.StructureIsoSetoid
import VaughtConjecture.Counting.Separation
import VaughtConjecture.Language.Density

/-!
# The spectrum of a sentence on coded countable models

Roadmap, Layer 6 (the two independent bounds, thinness by descriptive separation, the upper bound
by Scott separation on the persistent core, and the all-countable-carrier bridge) and the
reduction of the main theorem to expansion domains; `IMPLEMENTATION.md`, checkpoint 6 (thinness
and the all-countable bridge); semantic contract, item 1.

**The statement.**  `HasThinAlephOneSpectrum φ` is the statement of the roadmap sketch
`Suggested.lean`, verbatim: the models of `φ` coded on `ℕ` have exactly `ℵ₁` isomorphism classes
(`Quotient (isoSetoid φ)`, the infinitary-logic library's classes of coded models), and there is
no perfect set of pairwise nonisomorphic such models.  Thinness is absence of a perfect
isomorphism antichain, not a bound below the continuum.

**Truth on classes.**  For a countable relational language `L` and a sentence `φ`, the truth of
a sentence `θ` on a class of coded models of `φ` (`classTruth φ θ`) is actual satisfaction of `θ`
by any representative code; it is well defined because the models of a sentence form an
isomorphism-invariant set of codes (the library's `isomorphismInvariant_modelsOf`).  The quotient
map is a presentation of the classes in the sense of the library's descriptive theorems, with
truth read back as satisfaction on codes (`classTruth_mk`).

* **Scott separation** (`classTruth_separates`): distinct classes are separated by a sentence,
  since each class is isolated by a Scott sentence (`exists_classTruth_iff_eq`, the library's
  `isolatedPresentation_of_surjective`).
* **Descriptive separation** (`isThinOnNatModels_of_countable_truth_sides`): if every sentence
  has a countable truth side or a countable false side on the classes, then `φ` is thin on its
  coded models, an instantiation of the library's
  `SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits` (invariant analytic separation
  and López–Escobar, transported to an arbitrary countable relational language through the
  small-vocabulary presentation).  It is used for thinness only.

**The counting composition.**  For a `Filtration` of the classes (`Counting.Filtration`) on
whose domains every sentence is eventually uniform (`IsUniformOnFiltration`):

* thinness (`isThinOnNatModels_of_filtration`): every sentence has a countable truth side
  (`Filtration.countable_truth_side`), and descriptive separation applies;
* exactly `ℵ₁` classes (`mk_eq_aleph_one_of_filtration`): Scott separation and uniformity make
  the persistent core a subsingleton, and its complement is covered by the `ℵ₁` many countable
  exceptions (`Filtration.mk_eq_aleph_one_of_separation`);
* together, `hasThinAlephOneSpectrum_of_filtration` for a language in `Language.{0, 1}`.

**The base language.**  For the density sentence (`baseLanguage.densitySentence`):

* a code satisfies the density sentence exactly when it is a type assignment whose realization
  is exactly consistent, covering, and has the finite-cut receiving property
  (`mem_modelsOf_densitySentence_iff`); isomorphism of two coded models is isomorphism of their
  realizations (`structureIsoSetoid_r_iff_isIso`), so the classes are the classes of the coded
  realizations (`mk_eq_mk_iff_isIso`);
* the **ℕ-carrier reduction** (`exists_mem_modelsOf_equiv`): every countably infinite model of a
  sentence, on a carrier in any universe, is isomorphic to a coded model on `ℕ`.  The absence of
  finite models of the density sentence rests on the cap-to-model theorem of Layer 3
  (`infinite_of_realize_densitySentence_of_capToModel`), so the reduction of every countable model
  of the density sentence to a code is stated with that hypothesis, in
  `VaughtConjecture.Endpoint.Assembly`.

Nothing in this file assumes a statement of Layers 3–6; of Layer 6 it proves only the compositions
from a filtration, which, with the uniformity of sentences, is a hypothesis here.

## Placement

The following general results are stated here and belong elsewhere:

* `realize_boundedFormulaω_equiv` and `realize_sentenceω_equiv` (transport of infinitary
  satisfaction along an isomorphism between carriers in different universes): the
  infinitary-logic library's `BoundedFormulaω.realize_equiv` and `LomegaEquiv.of_equiv` require
  one carrier universe, and should be generalized in place to carriers in different universes,
  which makes these two redundant;
* `qrank_lt_omega_one` (every infinitary formula has countable quantifier rank) in the
  infinitary-logic library's `Lomega1omega/QuantifierRank`;
* `classTruth` with its lemmas, and `exists_mem_modelsOf_equiv`, in the infinitary-logic
  library's `Descriptive/StructureIsoSetoid` and `Descriptive/CodeTransport`.

## References

The main theorem is [Kni26, Theorem 1.0.1], for R. W. Knight, *A counterexample to Vaught's
Conjecture using generalised Stone spaces* (draft, 20 February 2026).
-/

universe u v w z

namespace VaughtConjecture.Endpoint

open FirstOrder Language Structure Cardinal Set Counting
open scoped Ordinal

/-! ### Placement: infinitary satisfaction across carrier universes -/

section Placement

variable {L : Language.{u, v}} {M : Type w} {N : Type z} [L.Structure M] [L.Structure N]

/-- **Isomorphisms preserve infinitary satisfaction across carrier universes.** -/
theorem realize_boundedFormulaω_equiv (e : M ≃[L] N) {α : Type*} {n : ℕ}
    (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize (e ∘ v) (e ∘ xs) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => exact (e.toEmbedding.realize_equal_comp t₁ t₂).symm
  | rel R ts => exact (e.toEmbedding.realize_rel_comp R ts).symm
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.Realize]
    exact Iff.imp (ihφ xs) (ihψ xs)
  | all φ ih =>
    simp only [BoundedFormulaInf.Realize]
    refine ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
    · have h1 := (ih (Fin.snoc xs (e.symm y))).mp (h (e.symm y))
      rwa [Fin.comp_snoc, e.apply_symm_apply] at h1
    · have h1 := h (e x)
      rw [← Fin.comp_snoc] at h1
      exact (ih (Fin.snoc xs x)).mpr h1
  | iSup φs ih =>
    simp only [BoundedFormulaInf.Realize]
    exact exists_congr fun i ↦ ih i xs
  | iInf φs ih =>
    simp only [BoundedFormulaInf.Realize]
    exact forall_congr' fun i ↦ ih i xs

/-- **Isomorphic structures satisfy the same infinitary sentences**, for carriers in different
universes. -/
theorem realize_sentenceω_equiv (e : M ≃[L] N) (φ : L.Sentenceω) :
    φ.Realize M ↔ φ.Realize N := by
  have h := realize_boundedFormulaω_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  rwa [comp_empty_elim e, comp_fin_elim0 e] at h

/-- **Every infinitary formula has countable quantifier rank.** -/
theorem qrank_lt_omega_one {α : Type*} {n : ℕ} (φ : L.BoundedFormulaω α n) : φ.qrank < ω₁ := by
  induction φ with
  | falsum | equal | rel => exact Ordinal.omega_pos 1
  | imp φ ψ ihφ ihψ => exact max_lt ihφ ihψ
  | all φ ih => exact (isSuccLimit_omega 1).succ_lt ih
  | iSup φs ih => exact Ordinal.iSup_lt_omega_one ih
  | iInf φs ih => exact Ordinal.iSup_lt_omega_one ih

end Placement

/-! ### The statement -/

/-- **Thin `ℵ₁` spectrum**: the models of `φ` coded on `ℕ` have exactly `ℵ₁` isomorphism
classes, and there is no perfect set of pairwise nonisomorphic such models.  This is the
statement of the roadmap, whose binders include the countability of the language: it is part of
the intended statement (a countable relational language), though the body does not use it. -/
@[nolint unusedArguments]
def HasThinAlephOneSpectrum {L : Language.{0, 1}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω) : Prop :=
  Cardinal.mk (Quotient (isoSetoid φ)) = Cardinal.aleph 1 ∧
    ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

/-! ### Truth on the classes of coded models -/

section ClassTruth

variable {L : Language.{u, v}} [L.IsRelational]

variable (φ : L.Sentenceω)

/-- The **truth of a sentence on a class** of coded models of `φ`: satisfaction by any
representative code (well defined by the library's `isomorphismInvariant_modelsOf`). -/
def classTruth (θ : L.Sentenceω) : Quotient (isoSetoid φ) → Prop :=
  Quotient.lift (fun c : ModelsOf φ ↦ c.1 ∈ ModelsOf θ) fun _ _ h ↦
    propext (isomorphismInvariant_modelsOf θ _ _ (isoSetoid_r_iff.mp h))

variable {φ}

/-- Truth on the class of a code is satisfaction by the code. -/
@[simp] theorem classTruth_mk (θ : L.Sentenceω) (c : ModelsOf φ) :
    classTruth φ θ (Quotient.mk (isoSetoid φ) c) ↔ c.1 ∈ ModelsOf θ :=
  Iff.rfl

variable [Countable (Σ n, L.Relations n)]

/-- **Scott isolation of a class**: each class of coded models is defined by a sentence, the
Scott sentence of a representative code (the library's `isolatedPresentation_of_surjective`, for
the quotient map as a presentation). -/
theorem exists_classTruth_iff_eq (q : Quotient (isoSetoid φ)) :
    ∃ σ : L.Sentenceω, ∀ p, classTruth φ σ p ↔ p = q :=
  isolatedPresentation_of_surjective Subtype.val (Quotient.mk (isoSetoid φ))
    Quotient.mk_surjective (fun _ _ h ↦ Quotient.sound h) (classTruth φ) (fun _ _ ↦ Iff.rfl) q

/-- **Scott separation**: distinct classes of coded models are separated by a sentence. -/
theorem classTruth_separates {p q : Quotient (isoSetoid φ)} (h : p ≠ q) :
    ∃ θ : L.Sentenceω, ¬ (classTruth φ θ p ↔ classTruth φ θ q) := by
  obtain ⟨σ, hσ⟩ := exists_classTruth_iff_eq q
  exact ⟨σ, by simp [hσ, h]⟩

/-- **Descriptive separation**: if every sentence holds on only countably many classes or fails
on only countably many classes, then `φ` is thin on its coded models (an instantiation of the
library's `SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits`). -/
theorem isThinOnNatModels_of_countable_truth_sides
    (hsplit : ∀ θ : L.Sentenceω, {q | classTruth φ θ q}.Countable ∨
      {q | ¬ classTruth φ θ q}.Countable) :
    φ.IsThinOnNatModels :=
  SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits L φ (Quotient.mk (isoSetoid φ))
    (classTruth φ) (fun _ _ ↦ Iff.rfl) hsplit

end ClassTruth

/-! ### The counting composition -/

section Composition

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ n, L.Relations n)]
  {φ : L.Sentenceω}

variable (φ) in
/-- **Uniformity of sentences on a filtration** of the classes of coded models of `φ`: the truth
of each sentence is constant on some domain below `ω₁`. -/
def IsUniformOnFiltration (F : Filtration (Quotient (isoSetoid φ))) : Prop :=
  ∀ θ : L.Sentenceω, ∃ ξ, ξ < ω₁ ∧
    ∀ p ∈ F.domain ξ, ∀ q ∈ F.domain ξ, (classTruth φ θ p ↔ classTruth φ θ q)

/-- **Thinness from a filtration**: if every sentence is uniform on some domain of a filtration of
the classes, then `φ` is thin on its coded models. -/
theorem isThinOnNatModels_of_filtration (F : Filtration (Quotient (isoSetoid φ)))
    (hF : IsUniformOnFiltration φ F) : φ.IsThinOnNatModels :=
  isThinOnNatModels_of_countable_truth_sides fun θ ↦
    have ⟨_, hξ, h⟩ := hF θ
    F.countable_truth_side _ hξ h

/-- **Exactly `ℵ₁` classes from a filtration**: if every sentence is uniform on some domain of a
filtration of the classes, the coded models of `φ` have exactly `ℵ₁` isomorphism classes. -/
theorem mk_eq_aleph_one_of_filtration (F : Filtration (Quotient (isoSetoid φ)))
    (hF : IsUniformOnFiltration φ F) : #(Quotient (isoSetoid φ)) = ℵ₁ :=
  F.mk_eq_aleph_one_of_separation (classTruth φ) (fun _ _ ↦ classTruth_separates) hF

/-- **The thin `ℵ₁` spectrum from a filtration**: a filtration of the classes of coded models of
`φ` on whose domains every sentence is eventually uniform gives exactly `ℵ₁` classes and no
perfect set of pairwise nonisomorphic coded models. -/
theorem hasThinAlephOneSpectrum_of_filtration {L : Language.{0, 1}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] {φ : L.Sentenceω} (F : Filtration (Quotient (isoSetoid φ)))
    (hF : IsUniformOnFiltration φ F) : HasThinAlephOneSpectrum φ :=
  ⟨mk_eq_aleph_one_of_filtration F hF, isThinOnNatModels_of_filtration F hF⟩

end Composition

/-! ### The ℕ-carrier reduction -/

section Carrier

variable {L : Language.{u, v}} [L.IsRelational]

/-- **The ℕ-carrier reduction**: a countably infinite model of `φ`, on a carrier in any universe,
is isomorphic to the structure of a coded model of `φ` on `ℕ`. -/
theorem exists_mem_modelsOf_equiv {φ : L.Sentenceω} {M : Type w} [L.Structure M] [Countable M]
    [Infinite M] (h : φ.Realize M) :
    ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
      Nonempty (@Language.Equiv L M ℕ _ c.toStructure) := by
  obtain ⟨_⟩ := nonempty_denumerable M
  let e : M ≃ ℕ := Denumerable.eqv M
  refine ⟨StructureSpaceOn.encodeViaEquiv e, ?_, StructureSpaceOn.encodeViaEquiv_iso e⟩
  obtain ⟨i⟩ := StructureSpaceOn.encodeViaEquiv_iso (L := L) e
  exact (SmallVocabulary.mem_modelsOf_iff_realize L _ φ).mpr
    ((@realize_sentenceω_equiv L M ℕ _ (StructureSpaceOn.encodeViaEquiv e).toStructure i φ).mp h)

end Carrier

/-! ### The density sentence on coded models -/

section Density

open baseLanguage

/-- The **realization of a code** of a structure of the base language on `ℕ`. -/
noncomputable def codeRealization (c : StructureSpace baseLanguage.{u}) :
    Realization.{u, 0} ω ℕ :=
  @toRealization ℕ c.toStructure

/-- **Coded models of the density sentence**: a code satisfies the density sentence exactly when
it is a type assignment whose realization is exactly consistent, covering, and has the finite-cut
receiving property. -/
theorem mem_modelsOf_densitySentence_iff (c : StructureSpace baseLanguage.{u}) :
    c ∈ ModelsOf densitySentence.{u} ↔ @IsTypeAssignment ℕ c.toStructure ∧
      (codeRealization c).IsConsistent ∧ (codeRealization c).IsCovering ∧
        (codeRealization c).HasFiniteCutReceiving := by
  rw [SmallVocabulary.mem_modelsOf_iff_realize, @realize_densitySentence_iff ℕ c.toStructure]
  exact ⟨fun ⟨hT, _, h⟩ ↦ ⟨hT, h⟩, fun ⟨hT, h⟩ ↦ ⟨hT, inferInstance, h⟩⟩

/-- A code satisfying the density sentence is a type assignment. -/
theorem isTypeAssignment_of_mem_modelsOf_densitySentence {c : StructureSpace baseLanguage.{u}}
    (hc : c ∈ ModelsOf densitySentence.{u}) : @IsTypeAssignment ℕ c.toStructure :=
  ((mem_modelsOf_densitySentence_iff c).mp hc).1

/-- **Isomorphism of coded models of the density sentence is isomorphism of their
realizations.** -/
theorem structureIsoSetoid_r_iff_isIso {c d : StructureSpace baseLanguage.{u}}
    (hc : c ∈ ModelsOf densitySentence.{u}) (hd : d ∈ ModelsOf densitySentence.{u}) :
    (structureIsoSetoid baseLanguage.{u}).r c d ↔
      (codeRealization c).IsIso (codeRealization d) :=
  (@isIso_toRealization_iff ℕ ℕ c.toStructure d.toStructure
    (isTypeAssignment_of_mem_modelsOf_densitySentence hc)
    (isTypeAssignment_of_mem_modelsOf_densitySentence hd)).symm

/-- **The classes of coded models of the density sentence are the classes of their
realizations**: two coded models have the same class exactly when their realizations are
isomorphic. -/
theorem mk_eq_mk_iff_isIso {c d : ModelsOf densitySentence.{u}} :
    Quotient.mk (isoSetoid densitySentence.{u}) c = Quotient.mk (isoSetoid densitySentence) d ↔
      (codeRealization c.1).IsIso (codeRealization d.1) :=
  Quotient.eq.trans (isoSetoid_r_iff.trans (structureIsoSetoid_r_iff_isIso c.2 d.2))

end Density

end VaughtConjecture.Endpoint
