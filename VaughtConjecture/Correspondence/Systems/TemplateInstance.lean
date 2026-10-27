/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Targets
import VaughtConjecture.Correspondence.TemplateSystem.Theorem436

/-!
# `K[L]` as a qualifying system: the instance map

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  This file
states, as targets, that the template system `K[L]` (`templateStageClass`, for the invariance
diagram `templateDiagram` and the invariant system `templateInvariantSystem`, at universe `0`) is
an instance of the abstract structures of `VaughtConjecture.Correspondence.Systems`.  The instance
is constructed, and the targets are proved, in later files: `templateBaseSublanguage`
(`VaughtConjecture.Correspondence.Systems.TemplateBase`), `templateWeakSystem`
(`VaughtConjecture.Correspondence.Systems.TemplateWeak`), `templateQualifyingSystem`
(`VaughtConjecture.Correspondence.Systems.TemplateQualifying`), and the second proof of
[AFK26, Theorem 4.36], `theorem436Target_abstract`
(`VaughtConjecture.Correspondence.Systems.Theorem436`).  The table records which existing
declarations provide each field.

* `D`, `S`, `WeakSystem.compatibleWith`: `templateDiagram`, `templateInvariantSystem`,
  `isCompatibleWith_templateInvariantSystem`.
* `BaseSublanguage.incl`, `incl_injective`: `baseInclusion`, `baseInclusion_injective`.
* `BaseSublanguage.mem_range_iff`: `not_isInvariant_toTemplateSymbol` (one direction); the other
  direction (every non-invariant symbol is a base symbol) is the small lemma
  `exists_toTemplateSymbol_of_not_isInvariant`.
* `BaseSublanguage.reduct`: `baseReduct` (definitionally, once `incl = baseInclusion`).
* `WeakSystem.K β M`: `templateStageClass M β.1`.
* `S.projection β`: `projectStructure β.1` (`templateInvariantSystem_projection`).
* `WeakSystem.nonempty`: `nonempty_of_mem_templateStageClass`.
* `isoClosed`, `isCompatible`, `fixed`, `projection_mem`: `weakSystemClausesTarget` (with
  `isCompatible_templateDiagram_iff`, `templateInvariantSystem_projection`).
* `WeakSystem.dense`: `weakSystemClausesTarget` and `TemplateDensityTranslationTarget`.
* `WeakSystem.IsMaximalAt`: `IsMaximalAt` (after `templateInvariantSystem_projection`).
* `QualifyingSystem.base_maximal`: `maximalCoverageBaseTarget`.
* `QualifyingSystem.fewMaximal`: `maximalCountTarget`, `uniformMaximalRepresentativesTarget`
  (representatives on `ℕ`).
* `QualifyingSystem.eventuallyDetermined`: `eventualDeterminationOfBaseTarget` (its `ξ ≤ ζ`
  gives the printed `ζ > ξ`).
* `QualifyingSystem.invariant_occurs`: `invariantOccurrenceTarget` at `ℕ`, with
  `templateInvariant_eq`.
* `WeakSystem.CountableMembersInfinite`: `infinitudeTarget`.
* `IsQualifyingSentence templateSentence`: `templateBaseModelsTarget` at `ℕ`,
  `mem_modelsOf_iff_realize`.
* `[Countable (Σ n, L_c.Relations n)]`: `baseLanguageCountableTarget` (an instance).
* `Theorem436Target`: `theorem436Target_of_qualifyingSentenceTarget`, from Theorem 2.27.

The existing proof of `Theorem436Target` (`VaughtConjecture.Correspondence.TemplateSystem`) uses
the uniqueness of maximal lifts and Reconstruction for `K[L]` (`maximalStageInvariantTarget`).  The
abstract theorem assumes neither Reconstruction nor uniqueness of maximal lifts.  This `K[L]`
instance uses Reconstruction through maximal completion in conditions (a) and (c), but does not use
maximal-lift uniqueness or maximal-stage invariance.
-/

universe v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal Correspondence

/-- **Target: the base sublanguage of `K[L]`**: a base sublanguage `L_c[L]` of `templateSignature`
whose inclusion is `baseInclusion`.  Inputs: `baseInclusion_injective`,
`not_isInvariant_toTemplateSymbol`, and the converse (every symbol of `L_b[L] ∪ L_c[L]` that is not
an invariant is the image of a base symbol).  Proved (`templateBaseSublanguageTarget`).
Correspondence with the printed definitions. -/
def TemplateBaseSublanguageTarget : Prop :=
  ∃ E : templateSignature.{0}.BaseSublanguage baseTemplateLanguage.{0}, E.incl = baseInclusion

/-- **Target: density of `K[L]` in the abstract form**: for the invariant system of the legal
classes, `α`-density in the form of [AFK26, Definition 2.10 (c)] for the diagram `ID[L]`
(`InvarianceDiagram.IsDenseAt`) is `ProjectedDensityAt α`.  Inputs: `templateInvariant_eq`,
`templateInvariantSystem_τ_mk`.  Proved (`templateDensityTranslationTarget`).  Correspondence with
the printed definitions. -/
def TemplateDensityTranslationTarget : Prop :=
  ∀ (α : SystemLevel) (M : Type v) (G : templateLanguage.{0}.Structure M),
    templateDiagram.IsDenseAt templateInvariantSystem α G ↔ ProjectedDensityAt α.1 G

/-- **Target: `K[L]` is a weak system** [AFK26, Definition 2.17 and Theorem 4.23]: a weak system for
`templateDiagram` and `templateInvariantSystem`, with carriers in the universe `v`, whose classes
are `templateStageClass`.  Inputs: the table of the module docstring.  Proved
(`templateWeakSystemTarget`).  Correspondence with the printed definitions. -/
def TemplateWeakSystemTarget : Prop :=
  ∃ W : WeakSystem.{0, 1, v} templateDiagram.{0} templateInvariantSystem.{0},
    ∀ (β : SystemLevel) (M : Type v), W.K β M = templateStageClass M β.1

/-- **Target: `K[L]` is a qualifying system with qualifying sentence `σ[L]`**
[AFK26, Definitions 2.23 and 2.26, Theorem 4.23], at universe `0` for the carriers: a base
sublanguage with inclusion `baseInclusion`, a qualifying system whose classes are
`templateStageClass`, whose members on countable carriers are infinite, and for which
`templateSentence` is a qualifying sentence.  Inputs: the table of the module docstring.  Proved
(`templateQualifyingSentenceTarget`).  Correspondence with the printed definitions. -/
def TemplateQualifyingSentenceTarget : Prop :=
  ∃ (E : templateSignature.{0}.BaseSublanguage baseTemplateLanguage.{0})
    (W : QualifyingSystem.{0, 1, 0, 1, 0} templateDiagram.{0} templateInvariantSystem.{0} E),
    E.incl = baseInclusion ∧ (∀ (β : SystemLevel) (M : Type), W.K β M = templateStageClass M β.1) ∧
      W.CountableMembersInfinite ∧ W.IsQualifyingSentence templateSentence.{0}

/-- **[AFK26, Theorem 4.36] from the abstract Theorem 2.27 and the instance**: a composition,
applied in `theorem436Target_abstract`.  Correspondence with the printed definitions. -/
theorem theorem436Target_of_qualifyingSentenceTarget
    (h227 : ∀ (E : templateSignature.{0}.BaseSublanguage baseTemplateLanguage.{0})
      (W : QualifyingSystem.{0, 1, 0, 1, 0} templateDiagram.{0} templateInvariantSystem.{0} E),
      W.HasThinAlephOneSpectrumTarget templateSentence.{0})
    (h : TemplateQualifyingSentenceTarget) : Theorem436Target :=
  let ⟨E, W, _, _, hinf, hφ⟩ := h
  h227 E W hφ hinf

end VaughtConjecture
