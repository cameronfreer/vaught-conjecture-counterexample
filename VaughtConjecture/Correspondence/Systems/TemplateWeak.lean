/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.TemplateBase

/-!
# `K[L]` as a weak system

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For the
invariance diagram `ID[L]` (`templateDiagram`) and the invariant system of the legal classes
(`templateInvariantSystem`), at universe `0`:

* `templateDensityTranslationTarget` (`TemplateDensityTranslationTarget`): `α`-density in the
  abstract form of [AFK26, Definition 2.10 (c)] (`InvarianceDiagram.IsDenseAt`) is
  `ProjectedDensityAt α`.  Every invariant is a symbol `Q_c` (`templateInvariant_eq`), and
  `τ_α(Q_s) = τ_α(Q_u)` exactly when `τ_α(s) = τ_α(u)` (`templateInvariant_ext_iff`,
  `templateInvariantClass_project`).
* `templateWeakSystem` and `templateWeakSystemTarget` (`TemplateWeakSystemTarget`,
  [AFK26, Definition 2.17 and Theorem 4.23]): the weak system whose classes are
  `K_β[L] = templateStageClass M β`, on carriers in any universe `v`.  Its fields:
  `compatibleWith` is `isCompatibleWith_templateInvariantSystem`; `nonempty` is
  `nonempty_of_mem_templateStageClass`; `isoClosed` is the first clause of
  `weakSystemClausesTarget` (the source carrier is countable as it injects into the countable
  target); `isCompatible` and `fixed` are clauses of `templateStageClass`, read through
  `isCompatible_templateDiagram_iff` and `templateInvariantSystem_projection`; `dense`, for
  `α < β`, is `projectedDensityAt_of_satisfiesDensityAt` (as in `weakSystemClausesTarget`) read
  through `templateDensityTranslationTarget`; `projection_mem`, for `α < β`, is `projectionTarget`
  (stated there for `α ≤ β`).
* The base and maximality of the abstract weak system are those of `K[L]`:
  `templateWeakSystem_isInBase_iff` (`WeakSystem.IsInBase` along `templateBaseSublanguage` is
  `IsInTemplateBase`) and `templateWeakSystem_isMaximalAt_iff` (`WeakSystem.IsMaximalAt β` is
  `IsMaximalAt β.1`, through `templateInvariantSystem_projection`).
-/

universe v

namespace VaughtConjecture

open FirstOrder Language Structure Correspondence

/-- **Density in the abstract form is `ProjectedDensityAt`** (`TemplateDensityTranslationTarget`):
the invariants `Q` on `n + m` places and `R` on `n` places of the abstract form are `Q_u` and
`Q_t` (`templateInvariant_eq`), and the witness `Q'` with `τ_α(Q') = τ_α(Q)` is `Q_s` with
`τ_α(s) = τ_α(u)`.  Correspondence with the printed definitions. -/
theorem templateDensityTranslationTarget : TemplateDensityTranslationTarget.{v} := by
  intro α M G
  constructor
  · intro h n m hn t u hp x hx
    obtain ⟨y, Q', hQ', hy⟩ := h ⟨TemplateSymbol.invariant u (Nat.lt_add_right m hn), trivial⟩
      ⟨TemplateSymbol.invariant t hn, trivial⟩ hp x hx
    obtain ⟨s, hs, rfl⟩ := templateInvariant_eq Q'
    refine ⟨y, s, ?_, hy⟩
    have hc := templateInvariant_ext_iff.mp hQ'
    change templateInvariantClass (templateInvariantProject α.1 _) =
      templateInvariantClass (templateInvariantProject α.1 _) at hc
    rw [templateInvariantClass_project, templateInvariantClass_project] at hc
    exact hc
  · intro h n m Q R hp x hx
    obtain ⟨t, hn, rfl⟩ := templateInvariant_eq R
    obtain ⟨u, hnm, rfl⟩ := templateInvariant_eq Q
    obtain ⟨y, s, hs, hy⟩ := h hn t u hp x hx
    refine ⟨y, ⟨TemplateSymbol.invariant s hnm, trivial⟩, templateInvariant_ext_iff.mpr ?_, hy⟩
    change templateInvariantClass (templateInvariantProject α.1 _) =
      templateInvariantClass (templateInvariantProject α.1 _)
    rw [templateInvariantClass_project, templateInvariantClass_project]
    exact hs

/-! ### The weak system -/

/-- **`K[L]` as a weak system** [AFK26, Definition 2.17 and Theorem 4.23]: the classes
`K_β[L] = templateStageClass M β.1` for the diagram `ID[L]` and the invariant system of the legal
classes, with carriers in the universe `v`.  The inputs of each field are listed in the module
docstring.  Correspondence with the printed definitions. -/
def templateWeakSystem : WeakSystem.{0, 1, v} templateDiagram.{0} templateInvariantSystem.{0} where
  K β M := templateStageClass M β.1
  compatibleWith := isCompatibleWith_templateInvariantSystem
  nonempty _ _ _ hG := nonempty_of_mem_templateStageClass hG
  isoClosed β M N _ G H hG hGH := by
    obtain ⟨g⟩ := hGH
    have hM : Countable M :=
      Function.Injective.countable (@Language.Equiv.injective templateLanguage.{0} M N G H g)
    exact (weakSystemClausesTarget M hM β.1 β.2 G hG).1 N H ⟨g⟩
  isCompatible _ _ G hG := (isCompatible_templateDiagram_iff G).mpr hG.2.1
  fixed β _ G hG := (templateInvariantSystem_projection β G).trans hG.2.2.1
  dense α β M G hαβ hG := (templateDensityTranslationTarget α M G).mpr
    (projectedDensityAt_of_satisfiesDensityAt α.2 (hG.2.2.2 _ (blockStage_strictMono hαβ)))
  projection_mem α β M hM G hαβ hG := by
    rw [templateInvariantSystem_projection]
    exact projectionTarget β.1 α.1 M hM β.2 hαβ.le G hG

/-- The classes of `templateWeakSystem` are `templateStageClass`.  Correspondence with the
printed definitions. -/
@[simp] theorem templateWeakSystem_K (β : SystemLevel) (M : Type v) :
    templateWeakSystem.K β M = templateStageClass M β.1 :=
  rfl

/-- **`K[L]` is a weak system** (`TemplateWeakSystemTarget`): `templateWeakSystem`.
Correspondence with the printed definitions. -/
theorem templateWeakSystemTarget : TemplateWeakSystemTarget.{v} :=
  ⟨templateWeakSystem, fun _ _ ↦ rfl⟩

/-! ### The base and maximality -/

/-- **The base of the abstract weak system is the base of `K[L]`**: along
`templateBaseSublanguage`, a structure of `L_c[L]` is in the base of `templateWeakSystem`
exactly when it is in `IsInTemplateBase`.  Correspondence with the printed definitions. -/
theorem templateWeakSystem_isInBase_iff {M : Type v} (B : baseTemplateLanguage.{0}.Structure M) :
    templateWeakSystem.IsInBase templateBaseSublanguage B ↔ IsInTemplateBase B :=
  ⟨fun ⟨β, G, hG, hGB⟩ ↦ ⟨β.1, β.2, G, hG, hGB⟩,
    fun ⟨β, hβ, G, hG, hGB⟩ ↦ ⟨⟨β, hβ⟩, G, hG, hGB⟩⟩

/-- **Maximality in the abstract weak system is maximality in `K[L]`**: `G` is maximal at `β` in
`templateWeakSystem` ([AFK26, Definition 2.20], `WeakSystem.IsMaximalAt`) exactly when
`IsMaximalAt β.1 G`; the projection of the invariant system is `projectStructure`
(`templateInvariantSystem_projection`).  Correspondence with the printed definitions. -/
theorem templateWeakSystem_isMaximalAt_iff (β : SystemLevel) {M : Type v}
    (G : templateLanguage.{0}.Structure M) :
    templateWeakSystem.IsMaximalAt β G ↔ IsMaximalAt β.1 G := by
  refine ⟨fun ⟨hG, h⟩ ↦ ⟨hG, fun β' hβ' hββ' G' hG' hproj ↦ ?_⟩,
    fun ⟨hG, h⟩ ↦ ⟨hG, fun β' hββ' G' hG' hproj ↦ ?_⟩⟩
  · exact h ⟨β', hβ'⟩ hββ' G' hG' ((templateInvariantSystem_projection β G').trans hproj)
  · exact h β'.1 β'.2 hββ' G' hG' ((templateInvariantSystem_projection β G').symm.trans hproj)

end VaughtConjecture
