/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.Extension.StronglyCodedForcingDonors
import VaughtConjecture.Realization.CapToModel

/-!
# Strongly coded uniformity donors

Roadmap, Layer 3, 3.4 (the uniformity instances) and Correspondence, item 1 (the strongly coded
legal stage types); semantic contract, item 5.  All results here are native constructions of this
repository.

Write `λ_η = blockStage η`.  The unrestricted coface instances
(`StageType.HasNonemptyCofaceInstances`, from the coatom extension property with apex,
`StageType.HasNonemptyCofaceInstances.of_hasApexCoatomExtensions`) give, over every legal stage
type, cofaces with a label in each block `[γ, γ + ω)` below the stage, but say nothing about
strong coding of their rows.  This file states their strongly coded counterparts.

**Targets.**

* **The strongly coded uniformity donor** (`StageType.StronglyCodedUniformityDonorTarget η`): for
  every `ξ < η`, a strongly coded legal stage type on one point at `λ_η` with a label in
  `[λ_ξ, λ_ξ + ω)`.
* **Strongly coded uniformity cofaces** (`StageType.StronglyCodedUniformityCofaceTarget η`): for
  every strongly coded legal `Tp` at `λ_η` on `n` points and every `ξ < η`, a coface `d` of `Tp`
  (legal, with literal face `Tp` along `Fin.castSuccEmb`) with strongly coded rows and a **new**
  cell, of graded index `({Fin.last n}, 1)`, labelled in `[λ_ξ, λ_ξ + ω)`.  A cell whose scope
  contains the new point is not a cell of the face `Tp`.
* **The strongly coded coface instances** (`StageType.HasStronglyCodedCofaceInstances α`): the
  three fields of `StageType.HasNonemptyCofaceInstances α`, with strongly coded legal inputs and
  outputs with strongly coded rows (the outputs are legal by membership in the cofaces).
* **Uniformity from strongly coded receiving**
  (`Realization.StronglyCodedReceivingUniformityTarget α`): at a stage that is zero or a limit,
  a realization with strongly coded legal types and finite-cut receiving for the cofaces with
  strongly coded rows realizes, over every occurrence, a member of the uniformity family of every
  `γ < α` that is zero or a limit; the clause `Realization.IsModel.uniformity`, without
  modelhood.
* **Reference cells from strongly coded receiving**
  (`Realization.StronglyCodedReferenceCellsTarget α`): as
  `Realization.IsModel.exists_extend_uniformity`, the step of the acquisition of calibrated
  contexts that uses uniformity, for an exactly consistent realization with the premises of the
  previous target.

## Placement

This file belongs to Layer 3, 3.4, of `roadmap/README.md`.

## References

The uniformity clause is [Kni26, Definition 3.2.1, clause 4(b)]; the nonemptiness of its instances
is [Kni26, Lemma 4.4.2].  The range clause is that of [AFK26, Definition "legal"].
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace StageType

/-! ### Targets -/

/-- **Target: the strongly coded uniformity donor** at `λ_η` (B.P1): for every `ξ < η`, a strongly
coded legal stage type on one point at `λ_η` in the uniformity family of `λ_ξ`, that is, with a
label in `[λ_ξ, λ_ξ + ω)`. -/
def StronglyCodedUniformityDonorTarget (η : Ordinal.{u}) : Prop :=
  ∀ ξ < η, ∃ d : StageType.{u} (blockStage η) (0 + 1), d.IsStronglyCodedLegal ∧
    d ∈ uniformityFamily (blockStage ξ)

/-- **Target: strongly coded uniformity cofaces** at `λ_η`, over an occurrence's type: for every
strongly coded legal `Tp` at `λ_η` on `n` points and every `ξ < η`, a coface `d` of `Tp` (legal,
with face `Tp` along `Fin.castSuccEmb`) with strongly coded rows and a new cell, of graded index
`({Fin.last n}, 1)`, labelled in `[λ_ξ, λ_ξ + ω)`. -/
def StronglyCodedUniformityCofaceTarget (η : Ordinal.{u}) : Prop :=
  ∀ ⦃n : ℕ⦄ (Tp : StageType.{u} (blockStage η) n), Tp.IsStronglyCodedLegal → ∀ ξ < η,
    ∃ d ∈ Tp.cofaces, d.rows.IsStronglyCoded ∧ ∃ j : Fin d.card,
      d.toCellScheme.gradedIndex j = ({Fin.last n}, 1) ∧
      ((blockStage ξ : Ordinal.{u}) : Label.{u}) ≤ d.label j ∧
      d.label j < ((blockStage ξ + Ordinal.omega0 : Ordinal.{u}) : Label.{u})

variable (α : Ordinal.{u}) in
/-- **The strongly coded coface instances** at a stage `α`: the three statements of
`StageType.HasNonemptyCofaceInstances α`, for strongly coded legal inputs, with outputs whose rows
are strongly coded.  The outputs are legal, as cofaces. -/
structure HasStronglyCodedCofaceInstances : Prop where
  /-- **The strongly coded amalgam over the empty face**: a strongly coded legal `P` on `n` points
  and a strongly coded legal `d` on one point are the faces, along the first `n` points and along
  the last point, of one coface of `P` with strongly coded rows. -/
  exists_amalgam_empty ⦃n : ℕ⦄ (P : StageType.{u} α n) (d : StageType.{u} α 1) :
    P.IsStronglyCodedLegal → d.IsStronglyCodedLegal →
      ∃ Q ∈ P.cofaces, Q.rows.IsStronglyCoded ∧ restrictFace (Fin.natAddEmb n) Q = some d
  /-- **Strongly coded uniformity instances**: for `γ` zero or a limit below `α`, some coface of a
  strongly coded legal stage type with strongly coded rows has a label in `[γ, γ + ω)`. -/
  uniformity ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsStronglyCodedLegal → ∀ γ : Ordinal.{u},
    Order.IsSuccPrelimit γ → γ < α →
      ∃ q ∈ p.cofaces ∩ uniformityFamily γ, q.rows.IsStronglyCoded
  /-- **Strongly coded dominance instances**: for `γ` below `α`, some coface of a strongly coded
  legal stage type on `n` points with strongly coded rows has a label above `γ` at a cell of grade
  `n + 1`. -/
  dominance ⦃n : ℕ⦄ (p : StageType.{u} α n) : p.IsStronglyCodedLegal → ∀ γ : Ordinal.{u},
    γ < α → ∃ q ∈ p.cofaces ∩ dominanceFamily γ, q.rows.IsStronglyCoded

end StageType

namespace Realization

open StageType

variable (α : Ordinal.{u}) (M : Type v)

/-- **Target: uniformity from strongly coded receiving** at a stage `α` that is zero or a limit:
every realization `R` on `M` with strongly coded legal types and finite-cut receiving for the
cofaces with strongly coded rows realizes, over every occurrence `x`, a member of the uniformity
family of every `γ < α` that is zero or a limit. -/
def StronglyCodedReceivingUniformityTarget : Prop :=
  Order.IsSuccPrelimit α → ∀ R : Realization.{u, v} α M,
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ∀ (x : R.Occurrence) (γ : Ordinal.{u}), Order.IsSuccPrelimit γ → γ < α →
      R.RealizesOver x.tuple (uniformityFamily γ)

/-- **Target: reference cells from strongly coded receiving** at a stage `α` that is zero or a
limit: as `Realization.IsModel.exists_extend_uniformity`, for an exactly consistent realization
`R` with strongly coded legal types and finite-cut receiving for the cofaces with strongly coded
rows.  For a list `L` of ordinals that are zero or limits below `α` and `γ < α`, an occurrence `y`
containing `x` as a literal face along `f`, with a bound `K` on finite parts and a floor `B`,
`γ ≤ B < α`, and for every `μ ∈ L` a cell of the type of `y` labelled `μ + k`, `k < K`,
`μ + k ≤ B`. -/
def StronglyCodedReferenceCellsTarget : Prop :=
  Order.IsSuccPrelimit α → ∀ R : Realization.{u, v} α M, R.IsConsistent →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      p.IsStronglyCodedLegal) →
    R.HasFiniteCutReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ∀ (x : R.Occurrence) {γ : Ordinal.{u}}, γ < α → ∀ (L : List Ordinal.{u}),
      (∀ μ ∈ L, Order.IsSuccPrelimit μ ∧ μ < α) →
      ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (K : ℕ) (B : Ordinal.{u}),
        f.trans y.tuple = x.tuple ∧ γ ≤ B ∧ B < α ∧
          ∀ μ ∈ L, ∃ z, ∃ k < K,
            y.type.label z = ((μ + k : Ordinal.{u}) : Label.{u}) ∧ μ + k ≤ B

end Realization

end VaughtConjecture
