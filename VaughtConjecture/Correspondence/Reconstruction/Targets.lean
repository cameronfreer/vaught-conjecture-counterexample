/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.DonorDensity

/-!
# Targets of Reconstruction

Numbering as in the current draft of [AFK26].  Write `λ_ξ = blockStage ξ = ω + ω · ξ`; the
manuscript level `ξ` is the label stage `λ_ξ`, and **level zero is the label stage
`λ_0 = ω`**, not the literal stage `0`.  `τ_ξ` is `projectStructure ξ`, and `K_β[L]` is
`templateStageClass M β`.

This file states the targets of Reconstruction [AFK26, Proposition 4.34] as propositions, every
premise visible.  None is proved here.  Correspondence with the printed definitions.

* **B.T9, projection** (`ProjectionTarget β ξ M`): for `ξ ≤ β < ω₁` on a countable carrier,
  `τ_ξ` sends `K_β[L]` into `K_ξ[L]` (the countable-stage projection result; the unrestricted
  statement is not stated here).  The base reduct is unchanged by `τ_ξ`
  (`baseReduct_projectStructure`, proved).
* **Base case** (`BaseCaseTarget β M`): for `β < ω₁`, two structures of `K_β[L]` with equal base
  reducts have equal projections to level zero: `τ_0(G) = τ_0(H)`.
* **Successor** (`SuccessorTarget β ξ M`): for `ξ + 1 ≤ β < ω₁` on a countable carrier, two
  structures of `K_β[L]` with `τ_ξ(G) = τ_ξ(H)` have `τ_{ξ+1}(G) = τ_{ξ+1}(H)`.
* **Limit separation** (`LimitSeparationTarget β δ M`): for a limit `δ ≤ β < ω₁`, two structures
  of `K_β[L]` with `τ_ξ(G) = τ_ξ(H)` for every `ξ < δ` have `τ_δ(G) = τ_δ(H)`.  Its class form
  (`ClassSeparationTarget δ n`): two classes at `λ_δ` whose reductions to every `λ_ξ`, `ξ < δ`,
  are equal are equal.  Each equality of reductions is an equality of classes, that is, up to a
  renaming chosen at that stage; no family of renamings coherent across the stages `ξ < δ` is
  assumed.
* **B.T10, Reconstruction** (`ReconstructionTarget β M`): for `β < ω₁` on a countable carrier, two
  structures of `K_β[L]` with equal base reducts are equal, `G = H`, as structures of
  `L_b[L] ∪ L_c[L]` on the same carrier (literal equality).

Equality at a level `ξ` is the equality `τ_ξ(G) = τ_ξ(H)` of structures of `L_b[L] ∪ L_c[L]` on
the same carrier; at `ξ = β` it is `G = H`, since structures of `K_β[L]` are fixed by `τ_β`.
-/

universe u v

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-- **Target B.T9, projection, at countable stages on countable carriers**: for `ξ ≤ β < ω₁` on
a countable carrier `M`, the projection `τ_ξ` sends `K_β[L]` into `K_ξ[L]`.  This is the
countable-stage projection result: the premises `Countable M` and `β < ω₁` are those of the
route taken (through a strongly coded receiving presentation), not shown to be necessary, and the
statement without them is not this target.  Correspondence with the printed definitions. -/
def ProjectionTarget (β ξ : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → β < ω₁ → ξ ≤ β →
    ∀ G ∈ templateStageClass M β, projectStructure ξ G ∈ templateStageClass M ξ

/-- **Target: the base case of Reconstruction**: for `β < ω₁`, two structures of `K_β[L]` on the
same carrier with equal base reducts `G↾L_c[L] = H↾L_c[L]` have equal projections to level zero
(the label stage `ω = blockStage 0`): `τ_0(G) = τ_0(H)`.  Correspondence with the printed
definitions. -/
def BaseCaseTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → ∀ G ∈ templateStageClass M β, ∀ H ∈ templateStageClass M β,
    baseReduct G = baseReduct H → projectStructure 0 G = projectStructure 0 H

/-- **Target: the successor step of Reconstruction**: for `ξ + 1 ≤ β < ω₁` on a countable carrier,
two structures of `K_β[L]` with equal projections to level `ξ` have equal projections to level
`ξ + 1`.  Equality at a level is equality of structures on the same carrier.  Correspondence with
the printed definitions. -/
def SuccessorTarget (β ξ : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → β < ω₁ → ξ + 1 ≤ β →
    ∀ G ∈ templateStageClass M β, ∀ H ∈ templateStageClass M β,
      projectStructure ξ G = projectStructure ξ H →
        projectStructure (ξ + 1) G = projectStructure (ξ + 1) H

/-- **Target: separation at a limit level, on structures**: for a limit `δ ≤ β < ω₁`, two
structures of `K_β[L]` with equal projections to every level `ξ < δ` have equal projections to
level `δ`.  Correspondence with the printed definitions. -/
def LimitSeparationTarget (β δ : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → Order.IsSuccLimit δ → δ ≤ β →
    ∀ G ∈ templateStageClass M β, ∀ H ∈ templateStageClass M β,
      (∀ ξ < δ, projectStructure ξ G = projectStructure ξ H) →
        projectStructure δ G = projectStructure δ H

/-- **Target: separation at a limit level, on classes** (native construction): for a limit `δ`,
two classes at `λ_δ` on `n` points whose reductions to every `λ_ξ`, `ξ < δ`, are equal, are
equal.  Each hypothesis is an equality of classes, so the renaming witnessing it is chosen at the
stage `ξ`; no coherence of these renamings across stages is assumed. -/
def ClassSeparationTarget (δ : Ordinal.{u}) (n : ℕ) : Prop :=
  Order.IsSuccLimit δ → ∀ c d : TemplateClass.{u} (blockStage δ) n,
    (∀ ξ < δ, c.reduce (isSuccPrelimit_blockStage ξ) = d.reduce (isSuccPrelimit_blockStage ξ)) →
      c = d

/-- **Target B.T10, Reconstruction** [AFK26, Proposition 4.34]: for `β < ω₁` on a countable
carrier `M`, two structures of `K_β[L]` with equal base reducts are equal, literally, as
structures of `L_b[L] ∪ L_c[L]` on `M`.  Correspondence with the printed definitions. -/
def ReconstructionTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  Countable M → β < ω₁ → ∀ G ∈ templateStageClass M β, ∀ H ∈ templateStageClass M β,
    baseReduct G = baseReduct H → G = H

end VaughtConjecture
