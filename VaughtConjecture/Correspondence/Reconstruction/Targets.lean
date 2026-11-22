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
  `τ_ξ` sends `K_β[L]` into `K_ξ[L]` (the countable-stage projection result).  The base reduct is
  unchanged by `τ_ξ` (`baseReduct_projectStructure`, proved).
* **Projection on arbitrary carriers** (`ProjectionArbitraryCarrierTarget β ξ M`): the printed
  inclusion `τ_ξ(K_β[L]) ⊆ K_ξ[L]` of [AFK26, Theorem 4.23], the statement of `ProjectionTarget`
  without `Countable M`.  `ProjectionTarget` is its specialization to countable carriers
  (`projectionTarget_of_projectionArbitraryCarrierTarget`).
* **The lifting step of projection** (`ProjectionLiftTarget β ξ M`): one instance of `D[δ]`,
  `δ < λ_ξ`, in `τ_ξ(G)` for `G ∈ K_β[L]` on an arbitrary carrier: for one lower request over a
  realized root `x` and every higher root `t*` of `x` in `G`, a donor `w` over `t*`, its
  occurrence `G ⊨ Q_w(x y)`, the same occurrence `τ_ξ(G) ⊨ Q_{τ_ξ(w)}(x y)`, and agreement of
  `τ_ξ(w)` with the requested class at the cutoff `δ`.  With the projection of compatibility and
  `τ_ξ ∘ τ_ξ = τ_ξ` it gives the density clause of `ProjectionArbitraryCarrierTarget`.
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

/-- **Target: projection on arbitrary carriers** ([AFK26, Theorem 4.23], the inclusion
`τ_ξ(K_β[L]) ⊆ K_ξ[L]`): for `ξ ≤ β < ω₁` and any carrier `M`, the projection `τ_ξ` sends
`K_β[L]` into `K_ξ[L]` on the same carrier.  The premises are those of `ProjectionTarget` without
`Countable M`: `β < ω₁` is the printed range `β ∈ ω₁`, and `ξ ≤ β` includes the case `ξ = β`, where
`τ_β(G) = G`.  `ProjectionTarget β ξ M` is its specialization to countable carriers
(`projectionTarget_of_projectionArbitraryCarrierTarget`).  Proved by
`projectionArbitraryCarrierTarget` in `Correspondence/TemplateSystem/Projection`.
Correspondence with the printed definitions. -/
def ProjectionArbitraryCarrierTarget (β ξ : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → ξ ≤ β →
    ∀ G ∈ templateStageClass M β, projectStructure ξ G ∈ templateStageClass M ξ

open Correspondence in
/-- **Target: the lifting step of projection** (the density clause in the proof of
[AFK26, Theorem 4.23], one lower request at a time): for `ξ ≤ β < ω₁`, a structure `G` of
`K_β[L]` on an arbitrary carrier `M`, and `δ < λ_ξ = ω + ω · ξ`, one request of `D[δ]`
[AFK26, Definition 4.20] in `τ_ξ(G)` is met by projecting an occurrence in `G` over the actual
higher root.  The premises are exactly those of `SatisfiesDensityAt δ (projectStructure ξ G)`,
one quantifier for each printed one:

* "`(Q_u(xy), Q_t(x)) ∈ ID[T]` with `u, t ∈ T`": legal classes `t` on `n ≥ 1` points and `u` on
  `n + m` points with the pair `(Q_u(x y), Q_t(x))` in `ID[L]`;
* the root: a tuple `x : Fin n → M` with `τ_ξ(G) ⊨ Q_t(x)`, an actual finite root of `τ_ξ(G)`.

The conclusion is stated for every higher root of `x`: every legal class `t*` with
`τ_ξ(t*) = t` and `G ⊨ Q_{t*}(x)` (by the definition of `τ_ξ(G)` there is one).  There are
`y : Fin m → M` and a legal class `w` on `n + m` points such that

* `w` lies over `t*` on the first `n` places (`w↾castAdd = t*`): the donor is over the actual
  higher root;
* `G ⊨ Q_w(x y)`: the occurrence in `G` extends the root occurrence `x` itself;
* `τ_ξ(G) ⊨ Q_{τ_ξ(w)}(x y)`: the same occurrence survives projection, over the same `x`;
* `trunc_δ(τ_ξ(w)) ≅_ren trunc_δ(u)`: the agreement that the lower request requires at its cutoff
  `δ`.

The last two conjuncts with `s := τ_ξ(w)` are the conclusion of the lower request.  Intended route
(the printed one): clause (g) [AFK26, Definition 4.11 (g)] at `ξ`, in its class form
(`legalClassTruncRepairTarget`), restores `t*` under `u`: a legal class `v` with `v↾castAdd = t*`
and `trunc_δ(v) ≅_ren trunc_δ(u)`; `D[δ]` in `G` (`δ < λ_ξ ≤ λ_β`) for the pair `(Q_v, Q_{t*})`
at `x` gives `y` and `w` with `G ⊨ Q_w(x y)` and `trunc_δ(w) ≅_ren trunc_δ(v)`; compatibility of
`G` with `ID[L]` gives `w↾castAdd = t*`; and `trunc_δ(τ_ξ(w)) = trunc_δ(w)`
(`TemplateClass.truncEquiv_project_iff`).  The premise `β < ω₁` (a countable stage) is kept; no
countability of the carrier is assumed, and no presentation is used.
Proved by `projectionLiftTarget` in `Correspondence/TemplateSystem/Projection`.  Correspondence
with the printed definitions. -/
def ProjectionLiftTarget (β ξ : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → ξ ≤ β → ∀ G ∈ templateStageClass M β, ∀ δ < blockStage ξ,
    ∀ ⦃n m : ℕ⦄ (hn : 0 < n) (t : LegalClass.{u} n) (u : LegalClass.{u} (n + m)),
      (⟨n + m, TemplateSymbol.invariant u (Nat.lt_add_right m hn),
        atom (L := templateLanguage) (TemplateSymbol.invariant t hn) (Fin.castAdd m)⟩ :
          DiagramPair templateLanguage.{u}) ∈ templateDiagramPairs →
      ∀ x : Fin n → M,
        RelMap (L := templateLanguage.{u}) (self := projectStructure ξ G)
          (TemplateSymbol.invariant t hn) x →
        ∀ t' : LegalClass.{u} n, t'.project ξ = t →
          RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant t' hn) x →
          ∃ (y : Fin m → M) (w : LegalClass.{u} (n + m)),
            w.1.restrictFace (Fin.castAddEmb m) = some t'.1 ∧
            RelMap (L := templateLanguage.{u}) (self := G)
              (TemplateSymbol.invariant w (Nat.lt_add_right m hn)) (Fin.append x y) ∧
            RelMap (L := templateLanguage.{u}) (self := projectStructure ξ G)
              (TemplateSymbol.invariant (w.project ξ) (Nat.lt_add_right m hn)) (Fin.append x y) ∧
            (w.project ξ).1.TruncEquiv δ u.1

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
