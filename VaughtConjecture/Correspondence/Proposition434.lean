/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Boundedness.StageBound
import VaughtConjecture.Correspondence.Limits.Assembly
import VaughtConjecture.Correspondence.Reconstruction.Reconstruction
import VaughtConjecture.Correspondence.Sentence.Correspondence

/-!
# [AFK26, Proposition 4.34]

Numbering as in the current draft of [AFK26].  The printed statement: "For every `β ∈ ω₁` and every
`M ⊨ σ[L]` the following hold.  (Boundedness) The set `{rank_τ(N) : N ∈ K and N↾L_c[L] = M}` is
countable.  (Reconstruction) If `N, R ∈ K_β` and `N↾L_c[L] = R↾L_c[L] = M` then `N = R`.
(Limits) If `β` is a limit ordinal and for all `α < β` there is an `N_α ∈ K_α` with
`N_α↾L_c[L] = M` then there is an `N_β ∈ K_β` such that `N_β↾L_c[L] = M`."

Here `σ[L]` is `templateSentence`, `K_β` is `templateStageClass M β`, `N↾L_c[L]` is `baseReduct N`,
`K = ⋃_{β < ω₁} K_β`, and `rank_τ(N)` is the least fixing stage of `N` (`liftRanks M B` collects
them).  Level `β` is the label stage `blockStage β = ω + ω · β`.

`Proposition434Clauses β M B` is the three printed clauses at the level `β` for a base structure
`B` of `L_c[L]` on `M`:

* **Boundedness** (`boundedness`): the lift ranks form a countable set; the bound `A < ω₁` is
  added, as in B.T15 (`BoundednessTarget`, `boundednessTarget`), and follows from countability.
* **Reconstruction** (`reconstruction`): literal equality of two lifts in `K_β` over the same base
  `B` (B.T10, `ReconstructionTarget`, `reconstructionTarget`).
* **Limits at a nonzero limit** (`limits`): "limit ordinal" is read as `Order.IsSuccLimit β`, which
  excludes `0`, as in the proof of [AFK26, Theorem 4.36], Claim 4.37 ("If `β` is a non-zero limit
  ordinal").  The lower lifts are given level by level, with no coherence hypothesis (B.T11,
  `LimitsTarget`, `limitsTarget`).

**The stronger result** (`proposition434Clauses_of_countable`): the three clauses hold for every
base structure `B` on a countable carrier and every `β < ω₁`, with no sentence premise and no
nonemptiness.  This is where the printed premise `M ⊨ σ[L]` is dropped: Boundedness,
Reconstruction and Limits quantify over the lifts of `B`, and a base without lifts satisfies them
trivially.

**The sentence-facing statement** (`Proposition434Target M`, proved as `proposition434Target`):
the premises `Countable M` (the structures of [AFK26] are countable), `Nonempty M` (their domains
are nonempty, [AFK26, §1]), `β < ω₁` and `M ⊨ σ[L]`, as printed, and the three clauses.  It is
derived from the stronger result; `Nonempty M` and the sentence premise are not used.

**The zero level** (`exists_lift_zero_of_realize_templateSentence`, a separate theorem).  Read
with `0` as a limit, (Limits) at `0` has a vacuous hypothesis and says that `M` has a lift in
`K₀`.  This is B.T12 (`realize_templateSentence_iff_exists_lift`) and uses `Nonempty M` and the
sentence premise; it is not one of the three clauses.

No language for the template system without clause (5), no spectrum transfer and no statement of
[AFK26, Proposition 4.35] is made.

Correspondence with the printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-- **The clauses of [AFK26, Proposition 4.34]** at the level `β` for a base structure `B` of
`L_c[L]` on `M`: (Boundedness), (Reconstruction) and (Limits), the last at a nonzero limit.
Correspondence with the printed definitions. -/
structure Proposition434Clauses (β : Ordinal.{u}) (M : Type v)
    (B : baseTemplateLanguage.{u}.Structure M) : Prop where
  /-- (Boundedness): the ranks of the lifts of `B` in `K` form a countable set (bounded below
  `ω₁`). -/
  boundedness : (liftRanks M B).Countable ∧ ∃ A < ω₁, ∀ ρ ∈ liftRanks M B, ρ < A
  /-- (Reconstruction): two lifts of `B` in `K_β` are equal. -/
  reconstruction : ∀ G ∈ templateStageClass M β, ∀ H ∈ templateStageClass M β,
    baseReduct G = B → baseReduct H = B → G = H
  /-- (Limits), at a nonzero limit `β`: lifts of `B` at every lower level give a lift at `β`. -/
  limits : Order.IsSuccLimit β → (∀ ξ < β, ∃ G ∈ templateStageClass M ξ, baseReduct G = B) →
    ∃ G ∈ templateStageClass M β, baseReduct G = B

/-- **[AFK26, Proposition 4.34] without the sentence premise**: on a countable carrier, for every
`β < ω₁` and every base structure `B` of `L_c[L]` (satisfying `σ[L]` or not), the three clauses
hold.  From `boundednessTarget`, `reconstructionTarget` and `limitsTarget`.
Correspondence with the printed definitions. -/
theorem proposition434Clauses_of_countable {M : Type v} (hc : Countable M) {β : Ordinal.{u}}
    (hβ : β < ω₁) (B : baseTemplateLanguage.{u}.Structure M) : Proposition434Clauses β M B where
  boundedness := boundednessTarget M hc B
  reconstruction G hG H hH hGB hHB := reconstructionTarget β M hc hβ G hG H hH (hGB.trans hHB.symm)
  limits hlim h := limitsTarget β M hc hlim hβ B h

/-- **Target: [AFK26, Proposition 4.34]**, sentence-facing, as printed: on a countable nonempty
carrier `M`, for every `β < ω₁` and every structure `B` of `L_c[L]` on `M` with `B ⊨ σ[L]`, the
clauses `Proposition434Clauses β M B` hold.  Correspondence with the printed definitions. -/
def Proposition434Target (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ β : Ordinal.{u}, β < ω₁ →
    ∀ B : baseTemplateLanguage.{u}.Structure M, @Sentenceω.Realize _ templateSentence.{u} M B →
      Proposition434Clauses β M B

/-- **[AFK26, Proposition 4.34], proved**, from `proposition434Clauses_of_countable`; the premises
`Nonempty M` and `B ⊨ σ[L]` are not used.  Correspondence with the printed definitions. -/
theorem proposition434Target (M : Type v) : Proposition434Target.{u, v} M :=
  fun hc _ _ hβ B _ ↦ proposition434Clauses_of_countable hc hβ B

/-- **The zero level** (B.T12, one direction): on a nonempty carrier, a model of `σ[L]` has a lift
in `K₀[L]`, the level `blockStage 0 = ω`.  This is (Limits) read at `0`, which is not one of the
three clauses.  Correspondence with the printed definitions. -/
theorem exists_lift_zero_of_realize_templateSentence {M : Type v} [Nonempty M]
    (B : baseTemplateLanguage.{u}.Structure M) (h : @Sentenceω.Realize _ templateSentence.{u} M B) :
    ∃ G ∈ templateStageClass M (0 : Ordinal.{u}), baseReduct G = B :=
  (realize_templateSentence_iff_exists_lift B).mp h

end VaughtConjecture
