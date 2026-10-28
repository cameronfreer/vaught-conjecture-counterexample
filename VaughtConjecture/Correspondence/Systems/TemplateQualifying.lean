/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.TemplateWeak
import VaughtConjecture.Correspondence.Systems.Maximality

/-!
# `K[L]` as a qualifying system, with qualifying sentence `σ[L]`

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  The weak
system `templateWeakSystem` (carriers in universe `0`), with the base sublanguage
`templateBaseSublanguage`, satisfies the four conditions of [AFK26, Definition 2.23]
(`templateQualifyingSystem`), each from the corresponding result for `K[L]`:

* (a) `base_maximal`: `maximalCoverageBaseTarget`, read through
  `templateWeakSystem_isInBase_iff` and `templateWeakSystem_isMaximalAt_iff`;
* (b) `fewMaximal`: the countable set of representatives on `ℕ` of `maximalCountTarget` at each
  countable level, indexed by itself (a type in universe `1`, reindexed in universe `0` by
  `WeakSystem.hasFewMaximal_of_family`);
* (c) `eventuallyDetermined`: `eventualDeterminationOfBaseTarget`; a closed tuple of a structure
  of `L_c[L]` is a tuple with `P_n`, and the threshold `ξ` of `K[L]` serves for every `ζ ≥ ξ`, so
  in particular for every `ζ > ξ`, the printed strict form;
* (d) `invariant_occurs`: `invariantOccurrenceTarget` on `ℕ`, with `templateInvariant_eq`.

Moreover the members of `K_β[L]` on countable carriers are infinite (`infinitudeTarget`,
`templateQualifyingSystem_countableMembersInfinite`), and `σ[L]` (`templateSentence`) axiomatizes
the base on all countable nonempty carriers (`templateBaseModelsTarget`,
`templateWeakSystem_isBaseSentenceOnCarriers`), so it is a qualifying sentence for the system
(`templateQualifyingSystem_isQualifyingSentence`, through InfinitaryLogic's
`mem_modelsOf_iff_realize`).  Together: `templateQualifyingSentenceTarget`
(`TemplateQualifyingSentenceTarget`).

**Inputs from `K[L]`.**  Conditions (a) and (c) come from the maximal completion of `K[L]`
(`maximalCompletionTarget`), whose proof uses Reconstruction (`reconstructionTarget`,
[AFK26, Proposition 4.34]).  The uniqueness of maximal lifts (`maximalLiftUniqueTarget`) and the
isomorphism invariance of the maximal stage (`maximalStageInvariantTarget`) are not used, here or
in any declaration this file depends on.
-/

namespace VaughtConjecture

open FirstOrder Language Structure Correspondence

/-! ### The four conditions -/

/-- **Condition (a) for `K[L]`, in the abstract form** [AFK26, Definition 2.23 (a)]: every member
of the base on a countable carrier is the reduct of a structure maximal at some level
(`maximalCoverageBaseTarget`).  Correspondence with the printed definitions. -/
theorem templateWeakSystem_base_maximal (M : Type) [Countable M]
    (B : baseTemplateLanguage.{0}.Structure M)
    (hB : templateWeakSystem.IsInBase templateBaseSublanguage B) :
    ∃ G : templateLanguage.{0}.Structure M, templateWeakSystem.IsMaximal G ∧
      templateBaseSublanguage.reduct G = B := by
  obtain ⟨γ, hγ, H, hH, hHB⟩ :=
    (maximalCoverageBaseTarget M inferInstance B).mp ((templateWeakSystem_isInBase_iff B).mp hB)
  exact ⟨H, ⟨⟨γ, hγ⟩, (templateWeakSystem_isMaximalAt_iff ⟨γ, hγ⟩ H).mpr hH⟩, hHB⟩

/-- **Condition (b) for `K[L]`, in the abstract form** [AFK26, Definitions 2.20 and 2.23 (b)]: at
each countable level the structures on `ℕ` of `maximalCountTarget`, indexed by their countable
set, are maximal and represent every maximal structure on a countable carrier.  Correspondence
with the printed definitions. -/
theorem templateWeakSystem_hasFewMaximal : templateWeakSystem.{0}.HasFewMaximal := by
  refine WeakSystem.hasFewMaximal_of_family fun β ↦ ?_
  obtain ⟨S, hS, hmax, hrep⟩ := maximalCountTarget.{0} β.1 β.2
  refine ⟨S, hS.to_subtype, fun _ ↦ ℕ, fun _ ↦ inferInstance, fun H ↦ H.1,
    fun H ↦ (templateWeakSystem_isMaximalAt_iff β H.1).mpr (hmax H.1 H.2), fun M _ G hG ↦ ?_⟩
  obtain ⟨H, hH, e⟩ := hrep M G ((templateWeakSystem_isMaximalAt_iff β G).mp hG)
  exact ⟨⟨H, hH⟩, e⟩

/-- **A closed tuple of a structure of `L_c[L]` is a tuple with `P_n`**: the only symbol of
`L_c[L]` whose image is `P_n` is `P_n`.  Correspondence with the printed definitions. -/
theorem templateBaseSublanguage_isClosedTuple_iff {M : Type}
    (B : baseTemplateLanguage.{0}.Structure M) {n : ℕ} (a : Fin n → M) :
    templateBaseSublanguage.IsClosedTuple B a ↔
      ∃ hn : 0 < n,
        RelMap (L := baseTemplateLanguage.{0}) (self := B) (BaseSymbol.closed hn) a := by
  constructor
  · rintro ⟨hn, r, hr, ha⟩
    refine ⟨hn, ?_⟩
    cases r with
    | closed => exact ha
    | base c h0 hn' => cases hr
  · rintro ⟨hn, ha⟩
    exact ⟨hn, BaseSymbol.closed hn, rfl, ha⟩

/-- **Condition (c) for `K[L]`, in the abstract form** [AFK26, Definitions 2.21 and 2.23 (c)]:
every member of the base on a countable carrier is eventually determined
(`eventualDeterminationOfBaseTarget`, whose threshold `ξ` serves for every `ζ ≥ ξ`, hence for
every `ζ > ξ`).  Correspondence with the printed definitions. -/
theorem templateWeakSystem_eventuallyDetermined (M : Type) [Countable M]
    (B : baseTemplateLanguage.{0}.Structure M)
    (hB : templateWeakSystem.IsInBase templateBaseSublanguage B) :
    templateWeakSystem.IsEventuallyDetermined templateBaseSublanguage B := by
  intro n a ha
  obtain ⟨hn, ha⟩ := (templateBaseSublanguage_isClosedTuple_iff B a).mp ha
  obtain ⟨ξ, hξ, c, ⟨G, hG, hGB, hGa⟩, hall⟩ := eventualDeterminationOfBaseTarget M inferInstance B
    ((templateWeakSystem_isInBase_iff B).mp hB) hn a ha
  exact ⟨⟨ξ, hξ⟩, ⟨TemplateSymbol.invariant c hn, trivial⟩, ⟨G, ⟨hG, hGB⟩, hGa⟩,
    fun ζ hξζ G' hG' ↦ hall ζ.1 hξζ.le ζ.2 G' hG'.1 hG'.2⟩

/-- **Condition (d) for `K[L]`, in the abstract form** [AFK26, Definition 2.23 (d)]: every
invariant `Q_c` holds of some tuple of some member of `K_β[L]` on `ℕ`
(`invariantOccurrenceTarget`).  Correspondence with the printed definitions. -/
theorem templateWeakSystem_invariant_occurs {n : ℕ} (Q : templateSignature.{0}.Invariant n) :
    ∃ (M : Type) (_ : Countable M) (_ : Nonempty M) (β : SystemLevel)
      (G : templateLanguage.{0}.Structure M),
      G ∈ templateWeakSystem.K β M ∧ ∃ x : Fin n → M, RelMap (L := templateLanguage.{0})
        (self := G) Q.1 x := by
  obtain ⟨c, hn, rfl⟩ := templateInvariant_eq Q
  obtain ⟨β, hβ, -, G, hG, -, t, ht⟩ :=
    invariantOccurrenceTarget.{0, 0, 0} ℕ inferInstance inferInstance hn c
  exact ⟨ℕ, inferInstance, inferInstance, ⟨β, hβ⟩, G, hG, t, ht⟩

/-! ### The qualifying system -/

/-- **`K[L]` as a qualifying system** [AFK26, Definition 2.23 and Theorem 4.23]: the weak system
`templateWeakSystem` on carriers in universe `0`, with the base sublanguage
`templateBaseSublanguage` and the four conditions (a)–(d) above.  Correspondence with the printed
definitions. -/
def templateQualifyingSystem : QualifyingSystem.{0, 1, 0, 1, 0} templateDiagram.{0}
    templateInvariantSystem.{0} templateBaseSublanguage.{0} where
  toWeakSystem := templateWeakSystem
  base_maximal := templateWeakSystem_base_maximal
  fewMaximal := templateWeakSystem_hasFewMaximal
  eventuallyDetermined := templateWeakSystem_eventuallyDetermined
  invariant_occurs _ Q := templateWeakSystem_invariant_occurs Q

/-- **The members of `K[L]` on countable carriers are infinite** (`infinitudeTarget`).
Correspondence with the printed definitions. -/
theorem templateQualifyingSystem_countableMembersInfinite :
    templateQualifyingSystem.CountableMembersInfinite :=
  fun β M _ G hG ↦ infinitudeTarget β.1 M β.2 G hG

/-! ### The qualifying sentence -/

/-- **`σ[L]` axiomatizes the base of the weak system on all countable nonempty carriers**
([AFK26, Theorem 4.23]; `templateBaseModelsTarget`).  Correspondence with the printed
definitions. -/
theorem templateWeakSystem_isBaseSentenceOnCarriers :
    templateWeakSystem.{0}.IsBaseSentenceOnCarriers templateBaseSublanguage
      templateSentence.{0} :=
  fun M _ _ B ↦ (templateBaseModelsTarget M inferInstance inferInstance B).symm.trans
    (templateWeakSystem_isInBase_iff B).symm

/-- **`σ[L]` is a qualifying sentence for `K[L]`** ([AFK26, Definitions 2.24 and 2.26], coded):
the models of `σ[L]` coded on `ℕ` are the members of the base on `ℕ`
(`WeakSystem.isBaseSentence_of_isBaseSentenceOnCarriers`, through InfinitaryLogic's
`mem_modelsOf_iff_realize`).  Correspondence with the printed definitions. -/
theorem templateQualifyingSystem_isQualifyingSentence :
    templateQualifyingSystem.IsQualifyingSentence templateSentence.{0} :=
  WeakSystem.isBaseSentence_of_isBaseSentenceOnCarriers templateBaseSublanguage
    templateWeakSystem_isBaseSentenceOnCarriers

/-- **`K[L]` is a qualifying system with qualifying sentence `σ[L]`**
(`TemplateQualifyingSentenceTarget`): `templateBaseSublanguage`, `templateQualifyingSystem`,
`templateQualifyingSystem_countableMembersInfinite` and
`templateQualifyingSystem_isQualifyingSentence`.  Correspondence with the printed definitions. -/
theorem templateQualifyingSentenceTarget : TemplateQualifyingSentenceTarget :=
  ⟨templateBaseSublanguage, templateQualifyingSystem, rfl, fun _ _ ↦ rfl,
    templateQualifyingSystem_countableMembersInfinite,
    templateQualifyingSystem_isQualifyingSentence⟩

end VaughtConjecture
