/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Boundedness.Targets
import VaughtConjecture.Correspondence.Limits.Assembly
import VaughtConjecture.Correspondence.Reconstruction.Targets
import VaughtConjecture.Correspondence.Sentence.Targets

/-!
# [AFK26, Proposition 4.34]: the combined statement

Numbering as in the current draft of [AFK26].  The printed statement: "For every `β ∈ ω₁` and every
`M ⊨ σ[L]` the following hold.  (Boundedness) The set `{rank_τ(N) : N ∈ K and N↾L_c[L] = M}` is
countable.  (Reconstruction) If `N, R ∈ K_β` and `N↾L_c[L] = R↾L_c[L] = M` then `N = R`.
(Limits) If `β` is a limit ordinal and for all `α < β` there is an `N_α ∈ K_α` with
`N_α↾L_c[L] = M` then there is an `N_β ∈ K_β` such that `N_β↾L_c[L] = M`."

Here `σ[L]` is `templateSentence`, `K_β` is `templateStageClass M β`, `N↾L_c[L]` is `baseReduct N`,
`K = ⋃_{β < ω₁} K_β`, and `rank_τ(N)` is the least fixing stage of `N` (`liftRanks M B` collects
them).  Level `β` is the label stage `blockStage β = ω + ω · β`.

`Proposition434Target M` states the proposition on a carrier `M`, with the premises `Countable M`
(the structures of [AFK26] are countable), `Nonempty M` (their domains are nonempty, [AFK26, §1]),
`β < ω₁`, and `M ⊨ σ[L]`, and the clauses of `Proposition434Clauses`:

* **Boundedness** (`boundedness`): the lift ranks form a countable set; the bound `A < ω₁` is
  added, as in B.T15 (`BoundednessTarget`, proved as `boundednessTarget`), and follows from
  countability.
* **Reconstruction** (`reconstruction`): literal equality of two lifts in `K_β` over the same base
  `B` (B.T10, `ReconstructionTarget`, proved as `reconstructionTarget`).
* **Limits at a nonzero limit** (`limits`): "limit ordinal" is read as `Order.IsSuccLimit β`, which
  excludes `0`, as in the proof of [AFK26, Theorem 4.36], Claim 4.37 ("If `β` is a non-zero limit
  ordinal").  The lower lifts are given level by level, with no coherence hypothesis (B.T11,
  `LimitsTarget`, proved as `limitsTarget`).
* **The zero level** (`levelZero`, a separate line): read with `0` as a limit, (Limits) at `0` has
  a vacuous hypothesis and says that `M` has a lift in `K₀`.  It is to be obtained from B.T12
  (`SentenceCorrespondenceTarget`, proved as `sentenceCorrespondenceTarget`), which uses
  `Nonempty M` and the sentence premise; it is not part of the other three clauses.

**Where the printed premise `M ⊨ σ[L]` is dropped.**  The proved component targets are stronger
than the printed clauses: `boundednessTarget`, `reconstructionTarget` and `limitsTarget` hold for
every base structure `B` of `L_c[L]` on a countable carrier, with no sentence premise and no
`Nonempty M` (a base without lifts has no lift ranks, and Reconstruction and Limits quantify over
lifts).  The sentence premise and `Nonempty M` are used only by the zero level, through B.T12.

**Not part of this statement.**  The separation of the density sentence from `σ[L]` for the class
reading (D8, `classStructureSeparationTarget`) is a separate theorem, neither a premise nor a
clause here.  No language for the template system without clause (5), no spectrum transfer and no
statement of [AFK26, Proposition 4.35] is made.

Stated, not proved.  Correspondence with the printed definitions.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-- **The clauses of [AFK26, Proposition 4.34]** at the level `β` for a base structure `B` of
`L_c[L]` on `M`, with the zero level as a separate line.
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
  /-- (Limits) read at the zero level: `B` has a lift in `K₀` (from B.T12). -/
  levelZero : β = 0 → ∃ G ∈ templateStageClass M (0 : Ordinal.{u}), baseReduct G = B

/-- **Target: [AFK26, Proposition 4.34]**, on a countable nonempty carrier `M`: for every
`β < ω₁` and every structure `B` of `L_c[L]` on `M` with `B ⊨ σ[L]`, the clauses
`Proposition434Clauses β M B` hold.  Stated, not proved.
Correspondence with the printed definitions. -/
def Proposition434Target (M : Type v) : Prop :=
  Countable M → Nonempty M → ∀ β : Ordinal.{u}, β < ω₁ →
    ∀ B : baseTemplateLanguage.{u}.Structure M, @Sentenceω.Realize _ templateSentence.{u} M B →
      Proposition434Clauses β M B

end VaughtConjecture
