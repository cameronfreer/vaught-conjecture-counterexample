/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Counting.OrdinalAttainment
import VaughtConjecture.Correspondence.Maximality.Targets
import VaughtConjecture.Correspondence.Proposition434

/-!
# Maximal-lift completion: [AFK26, Theorem 4.36, Claim 4.37]

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

This file states the targets and proves each of them by the route below.

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
element exists by well-foundedness of the ordinals.  **The one further lemma**
(`relMap_projectStructure_invariant_iff_project_eq`): for a compatible `H` with `H ⊨ Q_c(t)`,
`τ_ζ(H) ⊨ Q_c(t) ↔ c.project ζ = c`, for every ordinal `ζ`.  The printed form takes a closed
tuple of a model `B` of the sentence and reads its invariant in the maximal lift
(`Correspondence.IsStructuredGeometry.closed_iff`), then (5) and (6).

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
element `γ`, with `β ≤ γ < ω₁`.  Proved; route: `exists_isGreatest_of_closed` on membership in
`liftStages M B`, with `projectionTarget`, `baseReduct_projectStructure`, `limitsTarget` and
`stageBoundTarget`.  Correspondence with the printed definitions. -/
def GreatestLiftStageTarget (β : Ordinal.{u}) (M : Type v)
    (B : baseTemplateLanguage.{u}.Structure M) : Prop :=
  Countable M → β < ω₁ → ∀ G ∈ templateStageClass M β, baseReduct G = B →
    ∃ γ, IsGreatest (liftStages M B) γ ∧ β ≤ γ ∧ γ < ω₁

/-- **The greatest lift stage exists** (`GreatestLiftStageTarget β M B` for every `β`, `M`, `B`):
`exists_isGreatest_of_closed` on membership in `liftStages M B`, inhabited at `β`, closed downward
by `projectionTarget` and `baseReduct_projectStructure`, closed at the nonzero countable limits by
`limitsTarget`, and bounded by `stageBoundTarget`.  Correspondence with the printed definitions. -/
theorem greatestLiftStageTarget (β : Ordinal.{u}) (M : Type v)
    (B : baseTemplateLanguage.{u}.Structure M) : GreatestLiftStageTarget β M B := by
  intro hc hβ G hG hGB
  obtain ⟨A, hA, hS⟩ := stageBoundTarget M hc B
  obtain ⟨γ, hγ, hβγ, hγA⟩ := exists_isGreatest_of_closed (P := (· ∈ liftStages M B))
    (show β ∈ liftStages M B from ⟨hβ, G, hG, hGB⟩)
    (fun a b hab hb ↦ by
      obtain ⟨hbω, G', hG', hB'⟩ := hb
      exact ⟨hab.trans_lt hbω, projectStructure a G', projectionTarget b a M hc hbω hab G' hG',
        by rw [baseReduct_projectStructure, hB']⟩)
    (fun l hl hlω h ↦ ⟨hlω, limitsTarget l M hc hl hlω B fun a ha ↦ (h a ha).2⟩)
    hS hA
  exact ⟨γ, hγ, hβγ, hγA.trans hA⟩

/-- **Target: maximal at `γ` is greatest lift stage**: on a countable carrier, for `γ < ω₁` and
`H ∈ K_γ[L]`, `H` is maximal at `γ` exactly when `γ` is the greatest lift stage of `H↾L_c[L]`.
Proved.  The direction to maximality needs no strictness; the direction from maximality uses
`strictnessTarget_of_countable`.  Correspondence with the printed definitions. -/
def MaximalIffGreatestTarget (γ : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → γ < ω₁ → ∀ H ∈ templateStageClass M γ,
    (IsMaximalAt γ H ↔ IsGreatest (liftStages M (baseReduct H)) γ)

/-- **Maximal at `γ` is greatest lift stage** (`MaximalIffGreatestTarget γ M` for every `γ`, `M`).
To maximality: a lift at `γ' > γ` projecting to `H` has the base reduct of `H`
(`baseReduct_projectStructure`), so `γ'` would be a lift stage above the greatest.  From
maximality: a lift `G'` of `H↾L_c[L]` at `γ' > γ` has `τ_γ(G') = H`
(`projectStructure_eq_of_baseReduct_eq`), hence `H = G'` by maximality, and `G'` is fixed by `τ_γ`,
against `strictnessTarget_of_countable`.  Correspondence with the printed definitions. -/
theorem maximalIffGreatestTarget (γ : Ordinal.{u}) (M : Type v) : MaximalIffGreatestTarget γ M := by
  intro hc hγ H hH
  constructor
  · intro hmax
    refine ⟨⟨hγ, H, hH, rfl⟩, fun ξ hξS ↦ le_of_not_gt fun hlt ↦ ?_⟩
    obtain ⟨hξ, G', hG', hB⟩ := hξS
    have hp : projectStructure γ G' = H :=
      projectStructure_eq_of_baseReduct_eq hc hξ hlt.le hG' hH hB
    exact strictnessTarget_of_countable γ hc ξ hξ hlt G' hG'
      (hp.trans (hmax.eq_of_projectStructure_eq hξ hlt hG' hp))
  · intro hgr
    refine ⟨hH, fun γ' hγ' hγγ' G' hG' h ↦ absurd (hgr.2 ?_) (not_le.mpr hγγ')⟩
    refine ⟨hγ', G', hG', ?_⟩
    rw [← h, baseReduct_projectStructure]

/-- **A lift of the base of a maximal structure is a projection of it**: on a countable carrier,
if `H` is maximal at `γ < ω₁` and `G ∈ K_ξ[L]`, `ξ < ω₁`, has the base reduct of `H`, then `ξ ≤ γ`
(`maximalIffGreatestTarget`) and `G = τ_ξ(H)` (`projectStructure_eq_of_baseReduct_eq`).
Correspondence with the printed definitions. -/
theorem IsMaximalAt.le_and_eq_projectStructure {M : Type v} (hc : Countable M)
    {γ ξ : Ordinal.{u}} {H G : templateLanguage.{u}.Structure M} (hγ : γ < ω₁)
    (hH : IsMaximalAt γ H) (hξ : ξ < ω₁) (hG : G ∈ templateStageClass M ξ)
    (hB : baseReduct G = baseReduct H) : ξ ≤ γ ∧ G = projectStructure ξ H := by
  have hξγ : ξ ≤ γ := ((maximalIffGreatestTarget γ M hc hγ H hH.1).mp hH).2
    (show ξ ∈ liftStages M (baseReduct H) from ⟨hξ, G, hG, hB⟩)
  exact ⟨hξγ, (projectStructure_eq_of_baseReduct_eq hc hγ hξγ hH.1 hG hB.symm).symm⟩

/-! ### The maximal completion -/

/-- **`(γ, H)` is a maximal completion of `G` at `β`**: `β ≤ γ < ω₁`, `H ∈ K_γ[L]` on the same
carrier, `τ_β(H) = G`, and `H` is maximal at `γ` (the membership `H ∈ K_γ[L]` is also the first
clause of `IsMaximalAt`).  Correspondence with the printed definitions. -/
def IsMaximalCompletion {M : Type v} (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M)
    (γ : Ordinal.{u}) (H : templateLanguage.{u}.Structure M) : Prop :=
  β ≤ γ ∧ γ < ω₁ ∧ H ∈ templateStageClass M γ ∧ projectStructure β H = G ∧ IsMaximalAt γ H

/-- **Target: maximal completion** [AFK26, Theorem 4.36, Claim 4.37, existence]: on a countable
carrier, for `β < ω₁`, every `G ∈ K_β[L]` has a maximal completion `(γ, H)` on the same carrier,
with `γ` the greatest lift stage of `G↾L_c[L]`.  Proved; route: `GreatestLiftStageTarget` at
`baseReduct G`, a lift `H` at the greatest stage, `projectStructure_eq_of_baseReduct_eq` for
`τ_β(H) = G`, and `MaximalIffGreatestTarget` (direction to maximality) for `IsMaximalAt γ H`.
Correspondence with the printed definitions. -/
def MaximalCompletionTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → β < ω₁ → ∀ G ∈ templateStageClass M β,
    ∃ γ H, IsMaximalCompletion β G γ H ∧ IsGreatest (liftStages M (baseReduct G)) γ

/-- **The maximal completion exists** (`MaximalCompletionTarget β M` for every `β`, `M`): the lift
at the greatest lift stage (`greatestLiftStageTarget`), which projects to `G`
(`projectStructure_eq_of_baseReduct_eq`) and is maximal (`maximalIffGreatestTarget`).
Correspondence with the printed definitions. -/
theorem maximalCompletionTarget (β : Ordinal.{u}) (M : Type v) : MaximalCompletionTarget β M := by
  intro hc hβ G hG
  obtain ⟨γ, hgr, hβγ, hγ⟩ := greatestLiftStageTarget β M (baseReduct G) hc hβ G hG rfl
  obtain ⟨-, H, hH, hHB⟩ := hgr.1
  have hgrH : IsGreatest (liftStages M (baseReduct H)) γ := by
    rw [hHB]
    exact hgr
  exact ⟨γ, H, ⟨hβγ, hγ, hH, projectStructure_eq_of_baseReduct_eq hc hγ hβγ hH hG hHB,
    (maximalIffGreatestTarget γ M hc hγ H hH).mpr hgrH⟩, hgr⟩

/-- **Target: uniqueness of the maximal lift of a base structure**: on a countable carrier, two
structures maximal at countable stages `γ` and `γ'`, with equal base reducts, have `γ = γ'` and are
equal.  Proved; route: `MaximalIffGreatestTarget` (direction from maximality) makes `γ` and `γ'`
greatest elements of the same set `liftStages M (baseReduct H)`, so `γ = γ'` by
`IsGreatest.unique`; then `reconstructionTarget` at `γ` gives `H = H'`.  Correspondence with the
printed definitions. -/
def MaximalLiftUniqueTarget (M : Type v) : Prop :=
  Countable M → ∀ (γ γ' : Ordinal.{u}) (H H' : templateLanguage.{u}.Structure M),
    γ < ω₁ → γ' < ω₁ → IsMaximalAt γ H → IsMaximalAt γ' H' → baseReduct H = baseReduct H' →
      γ = γ' ∧ H = H'

/-- **The maximal lift of a base structure is unique** (`MaximalLiftUniqueTarget M` for every `M`):
`γ` and `γ'` are greatest elements of the same set of lift stages (`maximalIffGreatestTarget`), so
`γ = γ'` (`IsGreatest.unique`), and `H = H'` by Reconstruction at `γ` (`reconstructionTarget`).
Correspondence with the printed definitions. -/
theorem maximalLiftUniqueTarget (M : Type v) : MaximalLiftUniqueTarget.{u} M := by
  intro hc γ γ' H H' hγ hγ' hH hH' hB
  have h := (maximalIffGreatestTarget γ M hc hγ H hH.1).mp hH
  have h' := (maximalIffGreatestTarget γ' M hc hγ' H' hH'.1).mp hH'
  rw [← hB] at h'
  obtain rfl := h.unique h'
  exact ⟨rfl, reconstructionTarget γ M hc hγ H hH.1 H' hH'.1 hB⟩

/-- **Target: uniqueness of the maximal completion** [AFK26, Theorem 4.36, Claim 4.37,
uniqueness]: on a countable carrier, two maximal completions `(γ, H)` and `(γ', H')` of the same
`G` at `β` are equal: `γ = γ'` and `H = H'`.  Proved; route: `τ_β(H) = G = τ_β(H')` gives equal base
reducts (`baseReduct_projectStructure`), then `MaximalLiftUniqueTarget`; `γ = γ'` is
`IsGreatest.unique` on `liftStages M (baseReduct G)`.  Correspondence with the printed
definitions. -/
def MaximalCompletionUniqueTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → ∀ (G : templateLanguage.{u}.Structure M) (γ γ' : Ordinal.{u})
    (H H' : templateLanguage.{u}.Structure M),
    IsMaximalCompletion β G γ H → IsMaximalCompletion β G γ' H' → γ = γ' ∧ H = H'

/-- **The maximal completion is unique** (`MaximalCompletionUniqueTarget β M` for every `β`, `M`):
`τ_β(H) = G = τ_β(H')` gives equal base reducts (`baseReduct_projectStructure`), then
`maximalLiftUniqueTarget`.  Correspondence with the printed definitions. -/
theorem maximalCompletionUniqueTarget (β : Ordinal.{u}) (M : Type v) :
    MaximalCompletionUniqueTarget β M := by
  intro hc G γ γ' H H' h h'
  obtain ⟨-, hγ, -, hHG, hH⟩ := h
  obtain ⟨-, hγ', -, hH'G, hH'⟩ := h'
  refine maximalLiftUniqueTarget M hc γ γ' H H' hγ hγ' hH hH' ?_
  rw [← baseReduct_projectStructure (β := β) H, ← baseReduct_projectStructure (β := β) H', hHG,
    hH'G]

/-- **Target: every lift is a projection of the maximal completion** [AFK26, Theorem 4.36,
Claim 4.37, "every lift of `M` is of the form `τ_ζ(M_γ)` for some `ζ ≤ γ`"]: on a countable carrier,
for a maximal completion `(γ, H)` of `G` at `β`, every `ξ ≤ γ` carries the lift `τ_ξ(H) ∈ K_ξ[L]`,
and every lift `G' ∈ K_ξ[L]` of the literal base `G↾L_c[L]` at a stage `ξ < ω₁` has `ξ ≤ γ` and
`G' = τ_ξ(H)`.  Proved; route: `projectionTarget`, `baseReduct_projectStructure`,
`MaximalIffGreatestTarget` (direction from maximality) for `ξ ≤ γ`, and
`projectStructure_eq_of_baseReduct_eq`.  Correspondence with the printed definitions. -/
def LowerLiftsAreProjectionsTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → ∀ (G : templateLanguage.{u}.Structure M) (γ : Ordinal.{u})
    (H : templateLanguage.{u}.Structure M), IsMaximalCompletion β G γ H →
    (∀ ξ ≤ γ, projectStructure ξ H ∈ templateStageClass M ξ) ∧
      ∀ ξ < ω₁, ∀ G' ∈ templateStageClass M ξ, baseReduct G' = baseReduct G →
        ξ ≤ γ ∧ G' = projectStructure ξ H

/-- **Every lift is a projection of the maximal completion** (`LowerLiftsAreProjectionsTarget β M`
for every `β`, `M`): `projectionTarget` below `γ`, and `IsMaximalAt.le_and_eq_projectStructure`
for a lift of `G↾L_c[L] = H↾L_c[L]`.  Correspondence with the printed definitions. -/
theorem lowerLiftsAreProjectionsTarget (β : Ordinal.{u}) (M : Type v) :
    LowerLiftsAreProjectionsTarget β M := by
  intro hc G γ H h
  obtain ⟨-, hγ, hH, hHG, hmax⟩ := h
  refine ⟨fun ξ hξ ↦ projectionTarget γ ξ M hc hγ hξ H hH, fun ξ hξ G' hG' hB ↦ ?_⟩
  have hB' : baseReduct G' = baseReduct H := by
    rw [hB, ← hHG, baseReduct_projectStructure]
  exact hmax.le_and_eq_projectStructure hc hγ hξ hG' hB'

/-! ### Sentence-facing consequences -/

/-- **Target: every countable nonempty model of `σ[L]` has a unique maximal lift** [AFK26,
Theorem 4.36, Definition 2.23 (a) for `K[L]`]: on a countable nonempty carrier, for every structure
`B` of `L_c[L]` with `B ⊨ σ[L]` (`templateSentence`), there is exactly one pair `(γ, H)` with
`γ < ω₁`, `H` maximal at `γ`, and `H↾L_c[L] = B`, on the same carrier.  Proved; route:
`exists_lift_zero_of_realize_templateSentence`, `MaximalCompletionTarget` at `β = 0`, and
`MaximalLiftUniqueTarget`.  Correspondence with the printed definitions. -/
def SentenceMaximalLiftTarget (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ B : baseTemplateLanguage.{u}.Structure M,
    @Sentenceω.Realize _ templateSentence.{u} M B →
      ∃! p : Ordinal.{u} × templateLanguage.{u}.Structure M,
        p.1 < ω₁ ∧ IsMaximalAt p.1 p.2 ∧ baseReduct p.2 = B

/-- **Every countable nonempty model of `σ[L]` has a unique maximal lift**
(`SentenceMaximalLiftTarget M` for every `M`): a lift at level zero
(`exists_lift_zero_of_realize_templateSentence`), its maximal completion
(`maximalCompletionTarget` at `0`), and uniqueness (`maximalLiftUniqueTarget`).
Correspondence with the printed definitions. -/
theorem sentenceMaximalLiftTarget (M : Type v) : SentenceMaximalLiftTarget.{u} M := by
  intro hc hne B hB
  have := hne
  obtain ⟨G₀, hG₀, hG₀B⟩ := exists_lift_zero_of_realize_templateSentence B hB
  obtain ⟨γ, H, ⟨-, hγ, -, hHG, hH⟩, -⟩ :=
    maximalCompletionTarget 0 M hc (Cardinal.isSuccLimit_omega 1).pos G₀ hG₀
  have hHB : baseReduct H = B := by
    rw [← hG₀B, ← hHG, baseReduct_projectStructure]
  refine ⟨(γ, H), ⟨hγ, hH, hHB⟩, fun p hp ↦ ?_⟩
  obtain ⟨hp1, hpmax, hpB⟩ := hp
  obtain ⟨h1, h2⟩ := maximalLiftUniqueTarget M hc p.1 γ p.2 H hp1 hγ hpmax hH (hpB.trans hHB.symm)
  exact Prod.ext h1 h2

/-! ### Eventual determination -/

/-- **The invariant of a tuple in a projection**: if `H` is compatible and `H ⊨ Q_c(t)`, then
`τ_ζ(H) ⊨ Q_c(t)` exactly when `τ_ζ(c) = c`, for every ordinal `ζ`.  The projection reads `Q_c(t)`
from some `Q_{c'}(t)` in `H` with `τ_ζ(c') = c` (`relMap_projectStructure_invariant`), and `t` has
at most one invariant in `H` (`IsTemplateCompatible.eq_of_relMap_invariant`), so `c' = c`.
Correspondence with the printed definitions. -/
theorem relMap_projectStructure_invariant_iff_project_eq {M : Type v}
    {H : templateLanguage.{u}.Structure M} (hH : IsTemplateCompatible H) {n : ℕ} {hn : 0 < n}
    {c : LegalClass.{u} n} {t : Fin n → M}
    (ht : RelMap (L := templateLanguage.{u}) (self := H) (TemplateSymbol.invariant c hn) t)
    (ζ : Ordinal.{u}) :
    RelMap (L := templateLanguage.{u}) (self := projectStructure ζ H)
      (TemplateSymbol.invariant c hn) t ↔ c.project ζ = c := by
  rw [relMap_projectStructure_invariant]
  constructor
  · rintro ⟨c', hc', hx⟩
    rwa [hH.eq_of_relMap_invariant hx ht] at hc'
  · intro h
    exact ⟨c, h, ht⟩

/-- **Target: eventual determination at an attained threshold** [AFK26, Theorem 4.36, from
Claim 4.37 and Reconstruction]: on a countable carrier, let `H` be maximal at `γ < ω₁` and let `t`
have the invariant `Q_c` in `H`.  Among the stages `ζ < ω₁` at which some lift of `H↾L_c[L]` has
`Q_c(t)` there is a least one, `ξ ≤ γ`; the projection `τ_ξ(H)` is an actual lift at `ξ`
(`τ_ξ(H) ∈ K_ξ[L]`) with `Q_c(t)`; `Q_c(t)` holds in `τ_ζ(H)` for every `ξ ≤ ζ ≤ γ`, and in every
lift of `H↾L_c[L]` at every stage `ζ` with `ξ ≤ ζ < ω₁`.  Every legal class `c` on `n > 0` points
is allowed, those fixed by `τ_0` (the rank-zero invariants) included.

**Least threshold versus an attained determination stage.**  The printed eventual determination
([AFK26, Definition 2.21]) asks only for *some* stage `ξ` with a lift at `ξ` having `Q_c(t)` and
`Q_c(t)` in every lift above it; `γ` itself is such a stage, with the lift `H`.  This target is a
strengthening: `ξ` is the **least** stage at which any lift of `H↾L_c[L]` has `Q_c(t)` (`IsLeast`),
the lift witnessing it is the actual projection `τ_ξ(H)`, and the conclusion holds from `ξ` on.

Proved; route: `IsMaximalAt.le_and_eq_projectStructure`,
`relMap_projectStructure_invariant_iff_project_eq`,
`IsTemplateCompatible.project_eq_of_relMap_invariant`, `LegalClass.project_project_of_ge`, and
the least element of a nonempty set of ordinals (`csInf_mem`).  Correspondence with the printed
definitions. -/
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

/-- **Eventual determination at the least threshold** (`EventualDeterminationTarget M` for every
`M`).  `τ_ζ(H) ⊨ Q_c(t)` exactly when `τ_ζ(c) = c`
(`relMap_projectStructure_invariant_iff_project_eq`); the stages `ζ` with `τ_ζ(c) = c` contain `γ`
(`IsTemplateCompatible.project_eq_of_relMap_invariant`, `H` fixed by `τ_γ`) and are closed upward
(`LegalClass.project_project_of_ge`); `ξ` is their least element (`csInf_mem`).  Every lift of
`H↾L_c[L]` at a countable stage `ζ` is `τ_ζ(H)` with `ζ ≤ γ`
(`IsMaximalAt.le_and_eq_projectStructure`).  Correspondence with the printed definitions. -/
theorem eventualDeterminationTarget (M : Type v) : EventualDeterminationTarget.{u} M := by
  intro hc γ H hγ hmax n hn c t ht
  have hH := hmax.1
  have key := relMap_projectStructure_invariant_iff_project_eq hH.2.1 ht
  have hγS : c.project γ = c := hH.2.1.project_eq_of_relMap_invariant hH.2.2.1 ht
  set ξ := sInf {ζ : Ordinal.{u} | c.project ζ = c}
  have hξS : c.project ξ = c := csInf_mem (s := {ζ : Ordinal.{u} | c.project ζ = c}) ⟨γ, hγS⟩
  have hξγ : ξ ≤ γ := csInf_le' (s := {ζ : Ordinal.{u} | c.project ζ = c}) hγS
  have hup : ∀ ζ, ξ ≤ ζ → c.project ζ = c := fun ζ hξζ ↦
    calc c.project ζ = (c.project ξ).project ζ := by rw [hξS]
      _ = c.project ξ := c.project_project_of_ge hξζ
      _ = c := hξS
  have hproj : projectStructure ξ H ∈ templateStageClass M ξ :=
    projectionTarget γ ξ M hc hγ hξγ H hH
  refine ⟨ξ, hξγ, ⟨⟨hξγ.trans_lt hγ, projectStructure ξ H, hproj, baseReduct_projectStructure H,
    (key ξ).mpr hξS⟩, fun ζ hζS ↦ ?_⟩, hproj, (key ξ).mpr hξS,
    fun ζ hξζ _ ↦ (key ζ).mpr (hup ζ hξζ), fun ζ hξζ hζ G hG hB ↦ ?_⟩
  · obtain ⟨hζ, G, hG, hB, hGt⟩ := hζS
    obtain ⟨-, rfl⟩ := hmax.le_and_eq_projectStructure hc hγ hζ hG hB
    exact csInf_le' (s := {ζ : Ordinal.{u} | c.project ζ = c}) ((key ζ).mp hGt)
  · obtain ⟨-, rfl⟩ := hmax.le_and_eq_projectStructure hc hγ hζ hG hB
    exact (key ζ).mpr (hup ζ hξζ)

/-- **Target: models of `σ[L]` are eventually determined** [AFK26, Definition 2.21 and
Definition 2.23 (c) for `K[L]`], as printed: on a countable nonempty carrier, for every model `B` of
`σ[L]` and every closed tuple `t` of `B` (`B ⊨ P_n(t)`), there are `ξ < ω₁` and an invariant `Q_c`
such that some lift of `B` in `K_ξ[L]` has `Q_c(t)`, and every lift of `B` in `K_ζ[L]`,
`ξ ≤ ζ < ω₁`, has `Q_c(t)`.  The printed clause asks this only for `ζ > ξ`; the non-strict
inequality `ξ ≤ ζ` here strengthens it (it also covers the lifts at `ξ` itself).  Proved; route:
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

/-- **Models of `σ[L]` are eventually determined** (`SentenceEventualDeterminationTarget M` for
every `M`): the maximal lift `H` of `B` (`sentenceMaximalLiftTarget`); the closed tuple `t` has an
invariant `Q_c` in `H` (`Correspondence.IsStructuredGeometry.closed_iff`); then
`eventualDeterminationTarget`, with the threshold lift `τ_ξ(H)`.  Correspondence with the printed
definitions. -/
theorem sentenceEventualDeterminationTarget (M : Type v) :
    SentenceEventualDeterminationTarget.{u} M := by
  intro hc hne B hB n hn t ht
  obtain ⟨⟨γ, H⟩, ⟨hγ, hH, hHB⟩, -⟩ := sentenceMaximalLiftTarget M hc hne B hB
  subst hHB
  have hcl : RelMap (L := templateLanguage.{u}) (self := H) (TemplateSymbol.closed hn) t := ht
  obtain ⟨Q, hQ, hQt⟩ := (hH.1.2.1.1.closed_iff hn t).mp hcl
  rcases Q with _ | ⟨c, hn'⟩ | _ <;> try exact hQ.elim
  obtain ⟨ξ, hξγ, -, hmem, hrel, -, hall⟩ :=
    eventualDeterminationTarget M hc γ H hγ hH hn c t hQt
  exact ⟨ξ, hξγ.trans_lt hγ, c, ⟨projectStructure ξ H, hmem, baseReduct_projectStructure H, hrel⟩,
    hall⟩

end VaughtConjecture
