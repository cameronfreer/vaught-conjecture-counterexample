/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.TemplateInstance

/-!
# The base sublanguage of `K[L]`

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  The language
`L_c[L]` (`baseTemplateLanguage`) with the inclusion `baseInclusion` is a base sublanguage of the
template signature in the sense of [AFK26, Convention 2.3]
(`Correspondence.GeometrySignature.BaseSublanguage`):

* `exists_toTemplateSymbol_of_not_isInvariant`: every symbol of `L_b[L] ∪ L_c[L]` that is not an
  invariant (`P_n`, or `R_c` with `τ₀(c) = c`) is the image of a symbol of `L_c[L]`; with
  `not_isInvariant_toTemplateSymbol`, the range of the inclusion is exactly the set of symbols
  that are not invariants;
* `templateBaseSublanguage`: the base sublanguage, with inclusion `baseInclusion`
  (`baseInclusion_injective`); its reduct is `baseReduct`, definitionally
  (`templateBaseSublanguage_reduct`);
* `templateBaseSublanguageTarget`: `TemplateBaseSublanguageTarget` holds.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Correspondence

/-- **Every symbol that is not an invariant is a base symbol**: a symbol of `L_b[L] ∪ L_c[L]`
that is not an invariant `Q_c` is `P_n` or `R_c`, the image of the base symbol of the same name.
Correspondence with the printed definitions. -/
theorem exists_toTemplateSymbol_of_not_isInvariant {k : ℕ} {R : TemplateSymbol.{u} k}
    (hR : ¬ R.IsInvariant) : ∃ r : BaseSymbol.{u} k, r.toTemplateSymbol = R := by
  cases R with
  | closed hn => exact ⟨BaseSymbol.closed hn, rfl⟩
  | invariant c hn => exact (hR trivial).elim
  | base c h0 hn => exact ⟨BaseSymbol.base c h0 hn, rfl⟩

/-- **The base sublanguage `L_c[L]`** [AFK26, Convention 2.3 and Definition 4.17]: the inclusion
`baseInclusion`, injective on symbols (`baseInclusion_injective`), whose range is the set of
symbols of `L_b[L] ∪ L_c[L]` that are not invariants (`not_isInvariant_toTemplateSymbol` and
`exists_toTemplateSymbol_of_not_isInvariant`).  Correspondence with the printed definitions. -/
def templateBaseSublanguage : templateSignature.{u}.BaseSublanguage baseTemplateLanguage.{u} where
  incl := baseInclusion
  incl_injective := baseInclusion_injective
  mem_range_iff _ R :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ not_isInvariant_toTemplateSymbol r,
      fun hR ↦ exists_toTemplateSymbol_of_not_isInvariant (R := R) hR⟩

/-- The inclusion of `templateBaseSublanguage` is `baseInclusion`.  Correspondence with the
printed definitions. -/
@[simp] theorem templateBaseSublanguage_incl :
    templateBaseSublanguage.{u}.incl = baseInclusion :=
  rfl

/-- **The reduct along `templateBaseSublanguage` is `baseReduct`**, definitionally.
Correspondence with the printed definitions. -/
@[simp] theorem templateBaseSublanguage_reduct {M : Type v}
    (G : templateLanguage.{u}.Structure M) : templateBaseSublanguage.reduct G = baseReduct G :=
  rfl

/-- **The base sublanguage of `K[L]`** (`TemplateBaseSublanguageTarget`):
`templateBaseSublanguage`, whose inclusion is `baseInclusion`.  Correspondence with the printed
definitions. -/
theorem templateBaseSublanguageTarget : TemplateBaseSublanguageTarget :=
  ⟨templateBaseSublanguage, rfl⟩

end VaughtConjecture
