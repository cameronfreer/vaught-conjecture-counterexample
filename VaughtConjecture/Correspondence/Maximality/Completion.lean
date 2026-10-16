/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Counting.OrdinalAttainment
import VaughtConjecture.Correspondence.Maximality.Targets
import VaughtConjecture.Correspondence.Proposition434

/-!
# Maximal-lift completion: targets of [AFK26, Theorem 4.36, Claim 4.37]

Numbering as in the current draft of [AFK26].  `τ_ξ` is `projectStructure ξ`, `K_β[L]` is
`templateStageClass M β`, `N↾L_c[L]` is `baseReduct N`, the lift stages of a base structure `B` of
`L_c[L]` on `M` are `liftStages M B` (the `ξ < ω₁` with some `G ∈ K_ξ[L]`, `G↾L_c[L] = B`), and
maximality at `γ` is the printed [AFK26, Definition 2.20] (`IsMaximalAt`, with its allowance for an
unchanged higher lift).

[AFK26, Theorem 4.36, Claim 4.37]: for every `β ∈ ω₁` and `M ∈ K_β` there is a unique `N ∈ K` with
`τ_β(N) = M` and `N` maximal.  The proof of the claim also shows that every lift of the base
structure is a projection of it, and the proof of Theorem 4.36 concludes that every model of the
base class is eventually determined ([AFK26, Definition 2.21 and Definition 2.23 (c)]).  The
printed proof of the claim builds the lifts `M_ξ` by recursion on `ξ` and stops at a successor
or at a stage fixed by the lifts above it (Boundedness).  Here no recursion and no rank is used:
the lift stages of the base structure have an **attained greatest element**, and the lift at that
stage is the maximal completion.  Everything is on the original carrier `M`; no carrier is renamed.

This file **states** the targets.  None is proved here; every proof is later work.

## The plan, every input named

**(1) The greatest lift stage** (`GreatestLiftStageTarget β M B`).  Apply
`exists_isGreatest_of_closed` (`Counting/OrdinalAttainment.lean`) to `P ξ := ξ ∈ liftStages M B`:

* inhabited at `β`: `G ∈ K_β[L]` with `baseReduct G = B`, and `β < ω₁`;
* closed downward: for `a ≤ b ∈ liftStages M B` with lift `G'`, the projection `τ_a(G')` is in
  `K_a[L]` (`projectionTarget`, B.T9; `Countable M`, `b < ω₁`) and has base reduct `B`
  (`baseReduct_projectStructure`);
* closed at the nonzero countable limits: `limitsTarget` (B.T11, `Correspondence/Limits/Assembly`;
  `Countable M`), whose premise is exactly lifts at every lower level with no coherence;
* bounded: `stageBoundTarget` (`Correspondence/Boundedness/StageBound`; `Countable M`) gives
  `A < ω₁` above every lift stage; take `δ = A`.

The conclusion `∃ ρ, IsGreatest {a | P a} ρ ∧ β ≤ ρ ∧ ρ < A` gives `ρ < ω₁` from `A < ω₁`.  Pure
composition; no new lemma, no ordinal infrastructure, no rank and no statement that a rank equals a
stage.  The greatest element is attained (`IsGreatest`), not only a supremum.

**(1′) Maximal at `γ` is greatest lift stage** (`MaximalIffGreatestTarget γ M`).  For
`H ∈ K_γ[L]`, `γ < ω₁`, on a countable carrier: `IsMaximalAt γ H ↔
IsGreatest (liftStages M (baseReduct H)) γ`.  This is the one short lemma beyond composition.

* `←` (no strictness): `γ ∈ liftStages` by `H` itself; a lift `G'` at `γ' > γ` with `τ_γ(G') = H`
  has `baseReduct G' = baseReduct H` (`baseReduct_projectStructure`), so `γ' ∈ liftStages`, against
  `γ' ≤ γ`; the printed clause holds vacuously.
* `→` (strictness): a lift `G'` of `baseReduct H` at `γ' > γ`, `γ' < ω₁`, has `τ_γ(G') = H`
  (`projectStructure_eq_of_baseReduct_eq`, `Correspondence/Reconstruction/Coherence`), so `H = G'`
  by maximality (`IsMaximalAt.eq_of_projectStructure_eq`), so `G' ∈ K_{γ'}[L]` is fixed by `τ_γ`,
  against `strictnessTarget_of_countable` (`Correspondence/Maximality/Targets`).  Equivalently,
  through `maximalNoSuccessorTarget`: the lift stages are closed downward (as in (1)), so a lift
  stage above `γ` gives one at `γ + 1`, whose lift projects to `H` and is a successor of `H`.

**(2) Existence** (`MaximalCompletionTarget β M`).  From (1) with `B = baseReduct G`, choose the
lift `H ∈ K_γ[L]` at the greatest stage `γ`.  `τ_β(H) = G` by `projectStructure_eq_of_baseReduct_eq`
(`β ≤ γ < ω₁`, `Countable M`); `IsMaximalAt γ H` by (1′, `←`), the base reduct of `H` being
`baseReduct G`.

**(3) Uniqueness** (`MaximalLiftUniqueTarget M`, and its form over `G`,
`MaximalCompletionUniqueTarget β M`).  For two maximal structures `H ∈ K_γ[L]`, `H' ∈ K_{γ'}[L]`
with equal base reducts: (1′, `→`) makes `γ` and `γ'` both greatest elements of the one set
`liftStages M (baseReduct H)`, so **`γ = γ'` by `IsGreatest.unique`**; then
`reconstructionTarget` (B.T10) at `γ` gives `H = H'`.  Over `G`: `τ_β(H) = G = τ_β(H')` gives
equal base reducts (`baseReduct_projectStructure`).  Strictness enters only through (1′, `→`).

**(4) Every lift is a projection** (`LowerLiftsAreProjectionsTarget β M`).  For the maximal
completion `(γ, H)` of `G`: every `ξ ≤ γ` is a lift stage, with lift `τ_ξ(H)` (`projectionTarget`,
`baseReduct_projectStructure`); a lift `G'` of the literal base `baseReduct G` at a stage `ξ < ω₁`
has `ξ ≤ γ` (the greatest lift stage, (1′, `→`)) and `G' = τ_ξ(H)`
(`projectStructure_eq_of_baseReduct_eq`).  Composition.

**(5) Sentence-facing** (`SentenceMaximalLiftTarget M`).  On a countable nonempty carrier, a model
`B` of `templateSentence` has a lift `G₀ ∈ K₀[L]`
(`exists_lift_zero_of_realize_templateSentence`, B.T12 through
`realize_templateSentence_iff_exists_lift`, `Correspondence/Sentence/Correspondence`); (2) at
`β = 0` gives a maximal `(γ, H)` with base reduct `B`; (3, `MaximalLiftUniqueTarget`) gives
uniqueness of the pair.  Composition.

**(6) Eventual determination** (`EventualDeterminationTarget M`, and the printed form for models of
the sentence, `SentenceEventualDeterminationTarget M`).  For `H` maximal at `γ < ω₁` and a tuple
`t` with invariant `Q_c` in `H`: the stages `ζ < ω₁` at which some lift of `baseReduct H` has
`Q_c(t)` have a least element `ξ ≤ γ` (an `IsLeast` of the occurrence stages, not of the lift
stages); the **actual threshold lift** is `τ_ξ(H) ∈ K_ξ[L]` and it has `Q_c(t)`; every lift at a
stage `ζ ≥ ξ` has `Q_c(t)`, in particular `τ_ζ(H)` for `ξ ≤ ζ ≤ γ`.  Inputs: (4) (the lifts are the
`τ_ζ(H)`, `ζ ≤ γ`), `relMap_projectStructure_invariant`, at most one invariant per tuple
(`IsTemplateCompatible.eq_of_relMap_invariant`), so `τ_ζ(H) ⊨ Q_c(t)` exactly when
`c.project ζ = c`; this set of `ζ` is closed upward (`LegalClass.project_project_of_ge`) and
contains `γ` (`IsTemplateCompatible.project_eq_of_relMap_invariant`, `H` fixed by `τ_γ`); its least
element exists by well-foundedness of the ordinals.  **New lemma needed**: the characterization
`τ_ζ(H) ⊨ Q_c(t) ↔ c.project ζ = c` for `H ⊨ Q_c(t)`, a short composition of the two lemmas
named.  The printed form takes a closed tuple of a model `B` of the sentence and reads its
invariant in the maximal lift (`Correspondence.IsStructuredGeometry.closed_iff`), then (5) and (6).

**Not used.**  No recursion on stages, no rank (`fixingStages`, `liftRanks`), no statement that the
rank of a structure equals its stage, no Scott rank, no new ordinal infrastructure.  Strictness is
used only through `strictnessTarget_of_countable` (or `maximalNoSuccessorTarget`).
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The greatest lift stage -/

/-- **Target: the greatest lift stage** [AFK26, Theorem 4.36, Claim 4.37]: on a countable carrier,
for `β < ω₁` and `G ∈ K_β[L]` with `G↾L_c[L] = B`, the lift stages of `B` have an attained greatest
element `γ`, with `β ≤ γ < ω₁`.  Stated.  Plan: `exists_isGreatest_of_closed` on membership in
`liftStages M B`, with `projectionTarget`, `baseReduct_projectStructure`, `limitsTarget` and
`stageBoundTarget`.  Correspondence with the printed definitions. -/
def GreatestLiftStageTarget (β : Ordinal.{u}) (M : Type v)
    (B : baseTemplateLanguage.{u}.Structure M) : Prop :=
  Countable M → β < ω₁ → ∀ G ∈ templateStageClass M β, baseReduct G = B →
    ∃ γ, IsGreatest (liftStages M B) γ ∧ β ≤ γ ∧ γ < ω₁

/-- **Target: maximal at `γ` is greatest lift stage**: on a countable carrier, for `γ < ω₁` and
`H ∈ K_γ[L]`, `H` is maximal at `γ` exactly when `γ` is the greatest lift stage of `H↾L_c[L]`.
Stated.  The direction to maximality needs no strictness; the direction from maximality uses
`strictnessTarget_of_countable`.  Correspondence with the printed definitions. -/
def MaximalIffGreatestTarget (γ : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → γ < ω₁ → ∀ H ∈ templateStageClass M γ,
    (IsMaximalAt γ H ↔ IsGreatest (liftStages M (baseReduct H)) γ)

/-! ### The maximal completion -/

/-- **`(γ, H)` is a maximal completion of `G` at `β`**: `β ≤ γ < ω₁`, `H ∈ K_γ[L]` on the same
carrier, `τ_β(H) = G`, and `H` is maximal at `γ` (the membership `H ∈ K_γ[L]` is also the first
clause of `IsMaximalAt`).  Correspondence with the printed definitions. -/
def IsMaximalCompletion {M : Type v} (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M)
    (γ : Ordinal.{u}) (H : templateLanguage.{u}.Structure M) : Prop :=
  β ≤ γ ∧ γ < ω₁ ∧ H ∈ templateStageClass M γ ∧ projectStructure β H = G ∧ IsMaximalAt γ H

/-- **Target: maximal completion** [AFK26, Theorem 4.36, Claim 4.37, existence]: on a countable
carrier, for `β < ω₁`, every `G ∈ K_β[L]` has a maximal completion `(γ, H)` on the same carrier,
with `γ` the greatest lift stage of `G↾L_c[L]`.  Stated.  Plan: `GreatestLiftStageTarget` at
`baseReduct G`, a lift `H` at the greatest stage, `projectStructure_eq_of_baseReduct_eq` for
`τ_β(H) = G`, and `MaximalIffGreatestTarget` (direction to maximality) for `IsMaximalAt γ H`.
Correspondence with the printed definitions. -/
def MaximalCompletionTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → β < ω₁ → ∀ G ∈ templateStageClass M β,
    ∃ γ H, IsMaximalCompletion β G γ H ∧ IsGreatest (liftStages M (baseReduct G)) γ

/-- **Target: uniqueness of the maximal lift of a base structure**: on a countable carrier, two
structures maximal at countable stages `γ` and `γ'`, with equal base reducts, have `γ = γ'` and are
equal.  Stated.  Plan: `MaximalIffGreatestTarget` (direction from maximality) makes `γ` and `γ'`
greatest elements of the same set `liftStages M (baseReduct H)`, so `γ = γ'` by
`IsGreatest.unique`; then `reconstructionTarget` at `γ` gives `H = H'`.  Correspondence with the
printed definitions. -/
def MaximalLiftUniqueTarget (M : Type v) : Prop :=
  Countable M → ∀ (γ γ' : Ordinal.{u}) (H H' : templateLanguage.{u}.Structure M),
    γ < ω₁ → γ' < ω₁ → IsMaximalAt γ H → IsMaximalAt γ' H' → baseReduct H = baseReduct H' →
      γ = γ' ∧ H = H'

/-- **Target: uniqueness of the maximal completion** [AFK26, Theorem 4.36, Claim 4.37,
uniqueness]: on a countable carrier, two maximal completions `(γ, H)` and `(γ', H')` of the same
`G` at `β` are equal: `γ = γ'` and `H = H'`.  Stated.  Plan: `τ_β(H) = G = τ_β(H')` gives equal base
reducts (`baseReduct_projectStructure`), then `MaximalLiftUniqueTarget`; `γ = γ'` is
`IsGreatest.unique` on `liftStages M (baseReduct G)`.  Correspondence with the printed
definitions. -/
def MaximalCompletionUniqueTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → ∀ (G : templateLanguage.{u}.Structure M) (γ γ' : Ordinal.{u})
    (H H' : templateLanguage.{u}.Structure M),
    IsMaximalCompletion β G γ H → IsMaximalCompletion β G γ' H' → γ = γ' ∧ H = H'

/-- **Target: every lift is a projection of the maximal completion** [AFK26, Theorem 4.36,
Claim 4.37, "every lift of `M` is of the form `τ_ζ(M_γ)` for some `ζ ≤ γ`"]: on a countable carrier,
for a maximal completion `(γ, H)` of `G` at `β`, every `ξ ≤ γ` carries the lift `τ_ξ(H) ∈ K_ξ[L]`,
and every lift `G' ∈ K_ξ[L]` of the literal base `G↾L_c[L]` at a stage `ξ < ω₁` has `ξ ≤ γ` and
`G' = τ_ξ(H)`.  Stated.  Plan: `projectionTarget`, `baseReduct_projectStructure`,
`MaximalIffGreatestTarget` (direction from maximality) for `ξ ≤ γ`, and
`projectStructure_eq_of_baseReduct_eq`.  Correspondence with the printed definitions. -/
def LowerLiftsAreProjectionsTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → ∀ (G : templateLanguage.{u}.Structure M) (γ : Ordinal.{u})
    (H : templateLanguage.{u}.Structure M), IsMaximalCompletion β G γ H →
    (∀ ξ ≤ γ, projectStructure ξ H ∈ templateStageClass M ξ) ∧
      ∀ ξ < ω₁, ∀ G' ∈ templateStageClass M ξ, baseReduct G' = baseReduct G →
        ξ ≤ γ ∧ G' = projectStructure ξ H

/-! ### Sentence-facing consequences -/

/-- **Target: every countable nonempty model of `σ[L]` has a unique maximal lift** [AFK26,
Theorem 4.36, Definition 2.23 (a) for `K[L]`]: on a countable nonempty carrier, for every structure
`B` of `L_c[L]` with `B ⊨ σ[L]` (`templateSentence`), there is exactly one pair `(γ, H)` with
`γ < ω₁`, `H` maximal at `γ`, and `H↾L_c[L] = B`, on the same carrier.  Stated.  Plan:
`exists_lift_zero_of_realize_templateSentence`, `MaximalCompletionTarget` at `β = 0`, and
`MaximalLiftUniqueTarget`.  Correspondence with the printed definitions. -/
def SentenceMaximalLiftTarget (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    @Sentenceω.Realize _ templateSentence.{u} M B →
      ∃! p : Ordinal.{u} × templateLanguage.{u}.Structure M,
        p.1 < ω₁ ∧ IsMaximalAt p.1 p.2 ∧ baseReduct p.2 = B

/-- **Target: eventual determination at an attained threshold** [AFK26, Theorem 4.36, from
Claim 4.37 and Reconstruction]: on a countable carrier, let `H` be maximal at `γ < ω₁` and let `t`
have the invariant `Q_c` in `H`.  Among the stages `ζ < ω₁` at which some lift of `H↾L_c[L]` has
`Q_c(t)` there is a least one, `ξ ≤ γ`; the projection `τ_ξ(H)` is an actual lift at `ξ`
(`τ_ξ(H) ∈ K_ξ[L]`) with `Q_c(t)`; `Q_c(t)` holds in `τ_ζ(H)` for every `ξ ≤ ζ ≤ γ`, and in every
lift of `H↾L_c[L]` at every stage `ζ` with `ξ ≤ ζ < ω₁`.  Stated.  Plan:
`LowerLiftsAreProjectionsTarget`, `relMap_projectStructure_invariant`,
`IsTemplateCompatible.eq_of_relMap_invariant`,
`IsTemplateCompatible.project_eq_of_relMap_invariant`, `LegalClass.project_project_of_ge`, and
well-foundedness of the ordinals.  Correspondence with the printed definitions. -/
def EventualDeterminationTarget (M : Type v) : Prop :=
  Countable M → ∀ (γ : Ordinal.{u}) (H : templateLanguage.{u}.Structure M), γ < ω₁ →
    IsMaximalAt γ H → ∀ {n : ℕ} (hn : 0 < n) (c : LegalClass.{u} n) (t : Fin n → M),
      RelMap (L := templateLanguage.{u}) (self := H) (TemplateSymbol.invariant c hn) t →
        ∃ ξ ≤ γ,
          IsLeast {ζ | ζ < ω₁ ∧ ∃ G ∈ templateStageClass M ζ, baseReduct G = baseReduct H ∧
            RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t} ξ ∧
          projectStructure ξ H ∈ templateStageClass M ξ ∧
          RelMap (L := templateLanguage.{u}) (self := projectStructure ξ H)
            (TemplateSymbol.invariant c hn) t ∧
          (∀ ζ, ξ ≤ ζ → ζ ≤ γ → RelMap (L := templateLanguage.{u})
            (self := projectStructure ζ H) (TemplateSymbol.invariant c hn) t) ∧
          ∀ ζ, ξ ≤ ζ → ζ < ω₁ → ∀ G ∈ templateStageClass M ζ, baseReduct G = baseReduct H →
            RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t

/-- **Target: models of `σ[L]` are eventually determined** [AFK26, Definition 2.21 and
Definition 2.23 (c) for `K[L]`], as printed: on a countable nonempty carrier, for every model `B` of
`σ[L]` and every closed tuple `t` of `B` (`B ⊨ P_n(t)`), there are `ξ < ω₁` and an invariant `Q_c`
such that some lift of `B` in `K_ξ[L]` has `Q_c(t)`, and every lift of `B` in `K_ζ[L]`,
`ξ ≤ ζ < ω₁`, has `Q_c(t)` (the printed clause asks this for `ζ > ξ`).  Stated.  Plan:
`SentenceMaximalLiftTarget` for the maximal lift `H`,
`Correspondence.IsStructuredGeometry.closed_iff` in `H` for the invariant of `t`, then
`EventualDeterminationTarget`.  Correspondence with the printed definitions. -/
def SentenceEventualDeterminationTarget (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    @Sentenceω.Realize _ templateSentence.{u} M B →
      ∀ {n : ℕ} (hn : 0 < n) (t : Fin n → M),
        RelMap (L := baseTemplateLanguage.{u}) (self := B) (BaseSymbol.closed hn) t →
          ∃ ξ < ω₁, ∃ c : LegalClass.{u} n,
            (∃ G ∈ templateStageClass M ξ, baseReduct G = B ∧
              RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t) ∧
            ∀ ζ, ξ ≤ ζ → ζ < ω₁ → ∀ G ∈ templateStageClass M ζ, baseReduct G = B →
              RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hn) t

end VaughtConjecture
