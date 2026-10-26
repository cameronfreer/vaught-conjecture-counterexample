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

end VaughtConjecture
