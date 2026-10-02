/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.Assembly

/-!
# The main theorem on all countable carriers: the reduction to `ℕ`

Roadmap, Layer 6 (combine the two bounds, then apply the reduction to `ℕ`) and the reduction of
the main theorem to expansion domains (the all-countable-carrier version); `IMPLEMENTATION.md`,
"Scope and completion" (both formulations, with the reduction to `ℕ` explicit) and checkpoint 6;
semantic contract, item 1.

**Countable models on the carriers of a universe.**  For a language `L` and a sentence `φ`, a
countable model of `φ` on a carrier in the universe `w` (`CountableModel.{w} φ`) is a countable
type `carrier : Type w` with an `L`-structure satisfying `φ`.  Two of them are isomorphic when
their carriers are `L`-isomorphic (`CountableModel.isoSetoid`), and the **classes of countable
models** of `φ` on the carriers of `w` are the quotient `CountableModelClass.{w} φ`, a type in the
universe `max u v (w + 1)` for `L : Language.{u, v}` (the universe `w + 1` for the base language,
`Language.{0, 1}`).  The universe `w` is fixed: the classes on the carriers of all universes at once
do not form a type.

**The reduction to `ℕ`.**  A coded model `c` on `ℕ` gives the countable model
`CountableModel.ofCode c` on `ULift.{w} ℕ`, with the structure of `c` transported along
`Equiv.ulift`, isomorphic to `c` (`CountableModel.ofCodeEquiv`).  On classes this is
`classOfCode`, from the classes of coded models (`Quotient (isoSetoid φ)`, the infinitary-logic
library's classes) to the classes on the carriers of `w`.

* It is **injective** (`classOfCode_injective`), with no hypothesis on `φ`: isomorphic transported
  models have isomorphic codes.
* Every **infinite** countable model is in its range (`mk_mem_range_classOfCode`): it is isomorphic
  to a coded model, by the reduction to `ℕ` of a countably infinite model
  (`exists_mem_modelsOf_equiv` of `VaughtConjecture.MainTheorem.Spectrum`: the library's
  `StructureSpaceOn.encodeViaEquiv` along a bijection of the carrier with `ℕ`, and the invariance
  of infinitary satisfaction under isomorphism across carrier universes).
* So when `φ` has **no finite models** on the carriers of `w`, the reduction to `ℕ` is a bijection
  of classes (`codedClassEquiv`), and the two counts agree up to the lift of universes
  (`lift_mk_codedClass_eq`).  Conversely, if every countable model on a carrier of `w` is
  isomorphic to a coded model, then `φ` has no finite models there
  (`infinite_of_exists_mem_modelsOf_equiv`): the two forms of the hypothesis are interchangeable.

For the density sentence the absence of finite models is not proved in this repository: it is
derived from the cap-to-model theorem of Layer 3 (`CapToModel.infinite`), a hypothesis of
`VaughtConjecture.MainTheorem.Assembly`.  It is not added here as a separate hypothesis.

**The statement on all countable carriers.**  `HasThinAlephOneSpectrumOnCountableCarriers.{w} φ`
has the form of `HasThinAlephOneSpectrum φ`: the countable models of `φ` on the carriers of `w`
have exactly `ℵ₁` isomorphism classes, and there is no perfect set of pairwise nonisomorphic models
coded on `ℕ`.  Its second clause is the thinness of `HasThinAlephOneSpectrum` itself, unchanged:
the library's `IsThinOnNatModels` concerns perfect sets in the Polish space of codes on `ℕ`, and the
countable models on the carriers of a universe carry no topology, so the thinness statement has no
counterpart on all countable carriers.  Under the absence of finite models the two statements are
equivalent (`hasThinAlephOneSpectrumOnCountableCarriers_iff`).

## The conditional theorems

The theorems on all countable carriers are derived from the theorems on `ℕ` of
`VaughtConjecture.MainTheorem.Assembly`, with the same hypotheses, none of them proved here:

* `densitySentence_hasThinAlephOneSpectrumOnCountableCarriers_of_expansionDomains`,
  `…_of_presentations`, and `…_of_scatteredTails`: the thin `ℵ₁` spectrum of the density sentence
  on the carriers of `w`, from the hypotheses of the corresponding theorem on `ℕ` and the
  cap-to-model theorem for the carriers of `w`;
* `vaughtCounterexample_allCarriers_of_expansionDomains`, `…_of_presentations`, and
  `…_of_scatteredTails`: the conclusion of the corresponding theorem on `ℕ` together with the thin
  `ℵ₁` spectrum on the carriers of `w`, derived from that conclusion alone (it contains the
  reduction to `ℕ` of every countable model, which excludes finite models).

The reduction to `ℕ` uses neither sentence separation nor López–Escobar: the theorems here add to
the theorems on `ℕ` only transport along bijections of carriers.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe w u v

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Structure Cardinal

/-! ### Countable models on the carriers of a universe -/

section CountableModels

variable {L : Language.{u, v}}

/-- A **countable model** of `φ` on a carrier in the universe `w`. -/
structure CountableModel (φ : L.Sentenceω) : Type (max u v (w + 1)) where
  /-- The carrier. -/
  carrier : Type w
  /-- The structure on the carrier. -/
  [str : L.Structure carrier]
  /-- The carrier is countable. -/
  [countable : Countable carrier]
  /-- The structure satisfies `φ`. -/
  realize : φ.Realize carrier

attribute [instance] CountableModel.str CountableModel.countable

/-- **Isomorphism of countable models**: their carriers are `L`-isomorphic. -/
def CountableModel.isoSetoid (φ : L.Sentenceω) : Setoid (CountableModel.{w} φ) where
  r M N := Nonempty (M.carrier ≃[L] N.carrier)
  iseqv := ⟨fun M ↦ ⟨Language.Equiv.refl L M.carrier⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ ↦ ⟨f.comp e⟩⟩

/-- The **classes of countable models** of `φ` on the carriers of the universe `w`: the countable
models up to isomorphism. -/
abbrev CountableModelClass (φ : L.Sentenceω) : Type (max u v (w + 1)) :=
  Quotient (CountableModel.isoSetoid.{w} φ)

/-- Two countable models have the same class exactly when they are isomorphic. -/
theorem CountableModelClass.mk_eq_mk_iff {φ : L.Sentenceω} {M N : CountableModel.{w} φ} :
    (⟦M⟧ : CountableModelClass.{w} φ) = ⟦N⟧ ↔ Nonempty (M.carrier ≃[L] N.carrier) :=
  Quotient.eq

end CountableModels

/-! ### The reduction to `ℕ` -/

section Reduction

variable {L : Language.{u, v}} [L.IsRelational] {φ : L.Sentenceω}

/-- The **countable model of a code** on the carriers of `w`: the structure of a coded model of
`φ` on `ℕ`, transported to `ULift.{w} ℕ` along `Equiv.ulift`. -/
noncomputable def CountableModel.ofCode (c : ModelsOf φ) : CountableModel.{w} φ :=
  letI := c.1.toStructure
  letI : L.Structure (ULift.{w} ℕ) := Equiv.ulift.symm.inducedStructure
  { carrier := ULift.{w} ℕ
    realize := (realize_sentenceω_equiv (Equiv.ulift.symm.inducedStructureEquiv) φ).mp
      ((SmallVocabulary.mem_modelsOf_iff_realize L c.1 φ).mp c.2) }

/-- The countable model of a code is isomorphic to the coded model on `ℕ`. -/
noncomputable def CountableModel.ofCodeEquiv (c : ModelsOf φ) :
    @Language.Equiv L (CountableModel.ofCode.{w} c).carrier ℕ _ c.1.toStructure :=
  letI := c.1.toStructure
  letI : L.Structure (ULift.{w} ℕ) := Equiv.ulift.symm.inducedStructure
  (Equiv.ulift.symm.inducedStructureEquiv).symm

/-- **Countably infinite models reduce to codes**: a countable model of `φ` on an infinite carrier
in the universe `w` is isomorphic to the countable model of a code. -/
theorem CountableModel.exists_ofCode_equiv (M : CountableModel.{w} φ) [Infinite M.carrier] :
    ∃ c : ModelsOf φ, Nonempty ((CountableModel.ofCode.{w} c).carrier ≃[L] M.carrier) := by
  obtain ⟨c, hc, ⟨e⟩⟩ := exists_mem_modelsOf_equiv M.realize
  exact ⟨⟨c, hc⟩, ⟨@Language.Equiv.comp L _ ℕ _ c.toStructure _ _
    (@Language.Equiv.symm L M.carrier ℕ _ c.toStructure e) (ofCodeEquiv ⟨c, hc⟩)⟩⟩

variable (φ) in
/-- **The reduction to `ℕ` on classes**: the class of a coded model of `φ` goes to the class of
its countable model on `ULift.{w} ℕ`. -/
noncomputable def classOfCode : Quotient (isoSetoid φ) → CountableModelClass.{w} φ :=
  Quotient.map CountableModel.ofCode fun c d ⟨e⟩ ↦
    ⟨@Language.Equiv.comp L _ ℕ _ d.1.toStructure _ _
      (@Language.Equiv.symm L _ ℕ _ d.1.toStructure (CountableModel.ofCodeEquiv d))
      (@Language.Equiv.comp L _ ℕ _ c.1.toStructure ℕ d.1.toStructure e
        (CountableModel.ofCodeEquiv c))⟩

/-- The reduction to `ℕ` of the class of a code is the class of its countable model. -/
@[simp] theorem classOfCode_mk (c : ModelsOf φ) :
    classOfCode.{w} φ ⟦c⟧ = ⟦CountableModel.ofCode c⟧ :=
  rfl

/-- **The reduction to `ℕ` is injective on classes**, with no hypothesis on `φ`: coded models
whose countable models on `ULift.{w} ℕ` are isomorphic are isomorphic. -/
theorem classOfCode_injective : Function.Injective (classOfCode.{w} φ) := by
  rintro ⟨c⟩ ⟨d⟩ h
  obtain ⟨e⟩ := CountableModelClass.mk_eq_mk_iff.mp h
  exact Quotient.sound ⟨@Language.Equiv.comp L ℕ _ c.1.toStructure _ ℕ d.1.toStructure
    (CountableModel.ofCodeEquiv d)
    (@Language.Equiv.comp L ℕ _ c.1.toStructure _ _ _ e
      (@Language.Equiv.symm L _ ℕ _ c.1.toStructure (CountableModel.ofCodeEquiv c)))⟩

/-- **The class of a countably infinite model is the class of a code.** -/
theorem mk_mem_range_classOfCode (M : CountableModel.{w} φ) [Infinite M.carrier] :
    ⟦M⟧ ∈ Set.range (classOfCode.{w} φ) := by
  obtain ⟨c, hc⟩ := M.exists_ofCode_equiv
  exact ⟨⟦c⟧, CountableModelClass.mk_eq_mk_iff.mpr hc⟩

/-- **Absence of finite models from the reduction to `ℕ`**: if every countable model of `φ` on a
carrier in the universe `w` is isomorphic to a coded model, then every such model is infinite. -/
theorem infinite_of_exists_mem_modelsOf_equiv
    (hred : ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
      ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
        Nonempty (@Language.Equiv L M ℕ _ c.toStructure))
    {M : Type w} [L.Structure M] [Countable M] (h : φ.Realize M) : Infinite M := by
  obtain ⟨c, -, ⟨e⟩⟩ := hred M h
  let := c.toStructure
  exact Infinite.of_injective _ e.symm.injective

/-- **The reduction to `ℕ`, as a bijection of classes**: if `φ` has no finite models on the
carriers of the universe `w`, the classes of coded models of `φ` correspond to the classes of
countable models of `φ` on the carriers of `w`. -/
noncomputable def codedClassEquiv
    (hinf : ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M → Infinite M) :
    Quotient (isoSetoid φ) ≃ CountableModelClass.{w} φ :=
  Equiv.ofBijective (classOfCode.{w} φ) ⟨classOfCode_injective, fun q ↦
    q.inductionOn fun M ↦ have := hinf M.carrier M.realize; mk_mem_range_classOfCode M⟩

/-- The bijection of classes is the reduction to `ℕ` on classes. -/
@[simp] theorem codedClassEquiv_apply
    (hinf : ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M → Infinite M)
    (q : Quotient (isoSetoid φ)) : codedClassEquiv hinf q = classOfCode.{w} φ q :=
  rfl

/-- **The counts agree**: with no finite models on the carriers of `w`, the classes of coded models
of `φ` and the classes of countable models of `φ` on the carriers of `w` have the same cardinality,
up to the lift of universes. -/
theorem lift_mk_codedClass_eq
    (hinf : ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M → Infinite M) :
    lift.{max u v (w + 1)} #(Quotient (isoSetoid φ)) = lift.{v} #(CountableModelClass.{w} φ) :=
  lift_mk_eq'.mpr ⟨codedClassEquiv hinf⟩

end Reduction

/-! ### The statement on all countable carriers -/

section Statement

/-- **Thin `ℵ₁` spectrum on all countable carriers** (in the universe `w`): the countable models
of `φ` on the carriers of `w` have exactly `ℵ₁` isomorphism classes, and there is no perfect set
of pairwise nonisomorphic models coded on `ℕ`.  The second clause is the thinness of
`HasThinAlephOneSpectrum`, which concerns the Polish space of codes on `ℕ` and has no counterpart
on all countable carriers.  As for `HasThinAlephOneSpectrum`, the binders include the
countability of the language, part of the intended statement though the body does not use it. -/
@[nolint unusedArguments]
def HasThinAlephOneSpectrumOnCountableCarriers {L : Language.{0, 1}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω) : Prop :=
  #(CountableModelClass.{w} φ) = Cardinal.aleph 1 ∧
    ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

variable {L : Language.{0, 1}} [L.IsRelational] [Countable (Σ n, L.Relations n)]
  {φ : L.Sentenceω}

/-- **The two spectra agree** when `φ` has no finite models on the carriers of `w`. -/
theorem hasThinAlephOneSpectrumOnCountableCarriers_iff
    (hinf : ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M → Infinite M) :
    HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ↔ HasThinAlephOneSpectrum φ := by
  have h := lift_mk_codedClass_eq hinf
  refine and_congr_left' ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [h', lift_aleph, Ordinal.lift_one] at h
    rw [← lift_inj.{1, w + 1}, h, lift_aleph, Ordinal.lift_one]
  · rw [h', lift_aleph, Ordinal.lift_one] at h
    rw [← lift_inj.{w + 1, 1}, ← h, lift_aleph, Ordinal.lift_one]

/-- **The thin `ℵ₁` spectrum on all countable carriers from the spectrum on `ℕ` and the reduction
to `ℕ`**: if every countable model of `φ` on a carrier in the universe `w` is isomorphic to a coded
model (so that `φ` has no finite models there), the thin `ℵ₁` spectrum of `φ` on `ℕ` gives that on
the carriers of `w`. -/
theorem HasThinAlephOneSpectrum.onCountableCarriers (hs : HasThinAlephOneSpectrum φ)
    (hred : ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
      ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
        Nonempty (@Language.Equiv L M ℕ _ c.toStructure)) :
    HasThinAlephOneSpectrumOnCountableCarriers.{w} φ :=
  (hasThinAlephOneSpectrumOnCountableCarriers_iff
    fun _ _ _ h ↦ infinite_of_exists_mem_modelsOf_equiv hred h).mpr hs

end Statement

/-! ### The density sentence on all countable carriers -/

section Density

open baseLanguage

/-- **The reduction to `ℕ` for the density sentence, given the cap-to-model theorem**: the
classes of models of the density sentence coded on `ℕ` correspond to the classes of its countable
models on the carriers of the universe `w`. -/
noncomputable def CapToModel.codedClassEquiv (hcap : CapToModel.{w}) :
    DensityClass ≃ CountableModelClass.{w} densitySentence.{0} :=
  MainTheorem.codedClassEquiv fun _ _ _ h ↦ hcap.infinite h

/-- **The main theorem on all countable carriers, conditionally**: the hypotheses of
`densitySentence_hasThinAlephOneSpectrum_of_expansionDomains` and the cap-to-model theorem for the
carriers of `w` give exactly `ℵ₁` classes of countable models of the density sentence on the
carriers of `w`, and no perfect set of pairwise nonisomorphic coded models.  The hypotheses are
statements of Layers 3–6 of the roadmap, not proved here. -/
theorem densitySentence_hasThinAlephOneSpectrumOnCountableCarriers_of_expansionDomains
    (D : ExpansionDomains DensityClass) (ha : D.HasLogicalAgreement densityTruth)
    (hc : D.HasCountableLosses) (hn : D.HasNonemptyLosses) (hcap : CapToModel.{w}) :
    HasThinAlephOneSpectrumOnCountableCarriers.{w} densitySentence.{0} :=
  (hasThinAlephOneSpectrumOnCountableCarriers_iff fun _ _ _ h ↦ hcap.infinite h).mpr
    (densitySentence_hasThinAlephOneSpectrum_of_expansionDomains D ha hc hn)

/-- **The main theorem on all countable carriers, conditionally, by full presentations**: the
hypotheses of `densitySentence_hasThinAlephOneSpectrum_of_presentations` and the cap-to-model
theorem for the carriers of `w` give the thin `ℵ₁` spectrum of the density sentence on the
carriers of `w`.  The hypotheses are statements of the full-presentation route (roadmap,
"Reduction to full presentations") and of Layer 3 of the roadmap, not proved here. -/
theorem densitySentence_hasThinAlephOneSpectrumOnCountableCarriers_of_presentations
    (P : FullPresentations DensityClass) (hb : P.HasBoundedComparison densityTruth)
    (hu : UncountablyManyClasses) (hcap : CapToModel.{w}) :
    HasThinAlephOneSpectrumOnCountableCarriers.{w} densitySentence.{0} :=
  (hasThinAlephOneSpectrumOnCountableCarriers_iff fun _ _ _ h ↦ hcap.infinite h).mpr
    (densitySentence_hasThinAlephOneSpectrum_of_presentations P hb hu)

/-- **The main theorem on all countable carriers, conditionally, by full presentations with
scattered tails**: the hypotheses of `densitySentence_hasThinAlephOneSpectrum_of_scatteredTails`
and the cap-to-model theorem for the carriers of `w` give the thin `ℵ₁` spectrum of the density
sentence on the carriers of `w`.  The hypotheses are statements of the full-presentation route
(roadmap, "Reduction to full presentations") and of Layer 3 of the roadmap, not proved here. -/
theorem densitySentence_hasThinAlephOneSpectrumOnCountableCarriers_of_scatteredTails
    (P : FullPresentations DensityClass) (hs : P.HasScatteredTails)
    (hu : UncountablyManyClasses) (hcap : CapToModel.{w}) :
    HasThinAlephOneSpectrumOnCountableCarriers.{w} densitySentence.{0} :=
  (hasThinAlephOneSpectrumOnCountableCarriers_iff fun _ _ _ h ↦ hcap.infinite h).mpr
    (densitySentence_hasThinAlephOneSpectrum_of_scatteredTails P hs hu)

/-- **A thin uncountable infinitary class on all countable carriers, conditionally**: under the
hypotheses of `vaughtCounterexample_of_expansionDomains`, there are a countable relational
language and a sentence of `L_{ω₁,ω}` whose models coded on `ℕ` have exactly `ℵ₁` isomorphism
classes with no perfect set of pairwise nonisomorphic ones, whose countable models on the carriers
of the universe `w` also have exactly `ℵ₁` isomorphism classes, and every countable model of
which, on a carrier in `w`, is isomorphic to a coded one.  The statement on all countable carriers
is derived from the conclusion of `vaughtCounterexample_of_expansionDomains` by the reduction to
`ℕ`.  The hypotheses are statements of Layers 3–6 of the roadmap, not proved here. -/
theorem vaughtCounterexample_allCarriers_of_expansionDomains (D : ExpansionDomains DensityClass)
    (ha : D.HasLogicalAgreement densityTruth) (hc : D.HasCountableLosses)
    (hn : D.HasNonemptyLosses) (hcap : CapToModel.{w}) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) := by
  obtain ⟨L, _, _, φ, hs, hred⟩ := vaughtCounterexample_of_expansionDomains D ha hc hn hcap
  exact ⟨L, inferInstance, inferInstance, φ, hs, hs.onCountableCarriers hred, hred⟩

/-- **A thin uncountable infinitary class on all countable carriers, conditionally, by full
presentations**: the conclusion of `vaughtCounterexample_of_presentations`, under its hypotheses,
together with exactly `ℵ₁` isomorphism classes of countable models on the carriers of the
universe `w`, derived from it by the reduction to `ℕ`.  The hypotheses are statements of the
full-presentation route (roadmap, "Reduction to full presentations") and of Layer 3 of the
roadmap, not proved here. -/
theorem vaughtCounterexample_allCarriers_of_presentations (P : FullPresentations DensityClass)
    (hb : P.HasBoundedComparison densityTruth) (hu : UncountablyManyClasses)
    (hcap : CapToModel.{w}) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) := by
  obtain ⟨L, _, _, φ, hs, hred⟩ := vaughtCounterexample_of_presentations P hb hu hcap
  exact ⟨L, inferInstance, inferInstance, φ, hs, hs.onCountableCarriers hred, hred⟩

/-- **A thin uncountable infinitary class on all countable carriers, conditionally, by full
presentations with scattered tails**: the conclusion of `vaughtCounterexample_of_scatteredTails`,
under its hypotheses, together with exactly `ℵ₁` isomorphism classes of countable models on the
carriers of the universe `w`, derived from it by the reduction to `ℕ`.  The hypotheses are
statements of the full-presentation route (roadmap, "Reduction to full presentations") and of
Layer 3 of the roadmap, not proved here. -/
theorem vaughtCounterexample_allCarriers_of_scatteredTails (P : FullPresentations DensityClass)
    (hs : P.HasScatteredTails) (hu : UncountablyManyClasses) (hcap : CapToModel.{w}) :
    ∃ (L : Language.{0, 1}) (_ : L.IsRelational) (_ : Countable (Σ n, L.Relations n))
      (φ : L.Sentenceω), HasThinAlephOneSpectrum φ ∧
        HasThinAlephOneSpectrumOnCountableCarriers.{w} φ ∧
        ∀ (M : Type w) [L.Structure M] [Countable M], φ.Realize M →
          ∃ c : StructureSpace L, c ∈ ModelsOf φ ∧
            Nonempty (@Language.Equiv L M ℕ _ c.toStructure) := by
  obtain ⟨L, _, _, φ, hs, hred⟩ := vaughtCounterexample_of_scatteredTails P hs hu hcap
  exact ⟨L, inferInstance, inferInstance, φ, hs, hs.onCountableCarriers hred, hred⟩

end Density

end VaughtConjecture.MainTheorem
