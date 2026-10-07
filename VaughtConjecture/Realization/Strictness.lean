/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Expansion

/-!
# Strictness for models

Roadmap, manuscript correspondence, item 5 (uniform fixing bounds from positive niceness:
strictness and serving indices).

**Fixed by projection.**  Projection to a stage `γ` is stage reduction to `γ`, label by label
(`Label.reduce`).  A realization `R` is **fixed by projection at** `γ`
(`Realization.IsFixedAt`) when every label of every type it assigns lies at stage `γ`
(`Label.AtStage`: below `γ`, or the formal top); equivalently, projection to `γ` changes none of
its labels (`isFixedAt_iff_forall_reduce_label`, from `Label.reduce_eq_self_iff`).  An untyped
tuple carries no label.  Every realization at `α` is fixed by projection at `α`
(`isFixedAt_self`, stage correctness), and fixation passes to higher stages
(`IsFixedAt.mono`).  At an index `ξ` projection is to the block stage `λ_ξ` (`blockStage ξ`).

**Strictness for models.**  A model at a stage `α` is fixed by projection at no stage `β < α` that
is zero or a limit (`IsModel.not_isFixedAt`): over an occurrence, given by covering, the uniformity
clause at `γ = β` realizes a type with a label in the block `[β, β + ω)`
(`IsModel.exists_label_mem_block`), which is neither below `β` nor the formal top.  Only covering
and that one clause are used; this is the argument of `IsModel.exists_not_isTopFree_reduce`, read
before reduction.  So, for such `β`, a model at `α` is fixed by projection at `β` exactly when
`α ≤ β` (`IsModel.isFixedAt_iff`), and at a stage `α` that is zero or a limit, `α` is the least
stage that is zero or a limit at which the model is fixed (`IsModel.isLeast_isFixedAt`).  At block
stages: a model at `λ_η` is fixed by projection at the index `ξ` exactly when `η ≤ ξ`
(`IsModel.isFixedAt_blockStage_iff`), so the least index at which its whole assignment is fixed
is `η` itself (`IsModel.isLeast_isFixedAt_blockStage`).

**Strict families and serving indices.**  For a family `F` assigning to every index `ξ` a set of
realizations at `λ_ξ` on one carrier, `ξ` is a **serving index** when `F ξ` is inhabited.  The
family is **strict** (`Realization.IsStrict`) when every member of `F ξ` that is fixed by
projection at an index `ζ` has `ξ ≤ ζ`.  Every family of models is strict
(`isStrict_of_forall_isModel`), in particular the family of the model expansions of one base
structure (`isStrict_isExpansionOf`).  Under strictness every serving index is at most any index
at which all members of the family are fixed (`IsStrict.le_of_forall_isFixedAt`), and for a family
of models no further hypothesis is needed (`le_of_forall_isModel_of_forall_isFixedAt`).  Strictness
fails for families of arbitrary realizations (`VaughtConjecture.Realization.StrictnessExamples`).

## Placement

This file belongs to the manuscript correspondence of `roadmap/README.md`, item 5.
-/

universe u v

namespace VaughtConjecture.Realization

open Ordinal Label

variable {α β γ δ : Ordinal.{u}} {M : Type v}

/-! ### Fixed by projection -/

/-- A realization is **fixed by projection at** the stage `γ` when every label of every type it
assigns lies at stage `γ`: projection to `γ` (stage reduction, label by label) changes none of its
labels. -/
def IsFixedAt (R : Realization.{u, v} α M) (γ : Ordinal.{u}) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
    ∀ d, AtStage γ (p.label d)

variable {R : Realization.{u, v} α M}

/-- A realization is fixed by projection at `γ` exactly when stage reduction to `γ` changes none
of its labels. -/
theorem isFixedAt_iff_forall_reduce_label : R.IsFixedAt γ ↔
    ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
      ∀ d, Label.reduce γ (p.label d) = p.label d := by
  simp only [IsFixedAt, reduce_eq_self_iff]

/-- **Stage correctness**: a realization at `α` is fixed by projection at `α`. -/
theorem isFixedAt_self (R : Realization.{u, v} α M) : R.IsFixedAt α :=
  fun _ _ p _ d ↦ p.atStage d

/-- Fixation by projection passes to higher stages. -/
theorem IsFixedAt.mono (h : R.IsFixedAt γ) (hγδ : γ ≤ δ) : R.IsFixedAt δ :=
  fun _ t p ht d ↦ (h t p ht d).mono hγδ

/-- A realization at `α` is fixed by projection at every stage `γ ≥ α`. -/
theorem isFixedAt_of_le (R : Realization.{u, v} α M) (hαγ : α ≤ γ) : R.IsFixedAt γ :=
  (isFixedAt_self R).mono hαγ

/-! ### Strictness for models -/

/-- **A model has a label in every block below its stage**: for a model `S` at `α` and a stage
`β < α` that is zero or a limit, some type of `S` has a label in the block `[β, β + ω)`.  Over an
occurrence given by covering, this is the uniformity clause at `γ = β`; no other clause of a
model is used. -/
theorem IsModel.exists_label_mem_block {S : Realization.{u, v} α M} (hS : S.IsModel)
    (hβ : Order.IsSuccPrelimit β) (hβα : β < α) :
    ∃ (n : ℕ) (t : Fin n ↪ M) (p : StageType.{u} α n) (d : Fin p.card), S.eval t = some p ∧
      (β : Label.{u}) ≤ p.label d ∧ p.label d < ((β + ω : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨x⟩ := hS.nonempty_occurrence
  obtain ⟨u, -, q, ⟨d, hd, hdω⟩, hq⟩ := hS.uniformity x β hβ hβα
  exact ⟨_, u, q, d, hq, hd, hdω⟩

/-- **Strictness for models**: a model at `α` is not fixed by projection at any stage `β < α`
that is zero or a limit.  The label in the block `[β, β + ω)` given by the uniformity clause at
`γ = β` (`IsModel.exists_label_mem_block`) is neither below `β` nor the formal top. -/
theorem IsModel.not_isFixedAt {S : Realization.{u, v} α M} (hS : S.IsModel)
    (hβ : Order.IsSuccPrelimit β) (hβα : β < α) : ¬ S.IsFixedAt β := by
  intro h
  obtain ⟨n, t, p, d, ht, hd, hdω⟩ := hS.exists_label_mem_block hβ hβα
  rcases h t p ht d with hlt | htop
  · exact hd.not_gt hlt
  · exact (htop ▸ hdω).ne_top rfl

/-- A model fixed by projection at a stage `β` that is zero or a limit has its stage at most
`β`. -/
theorem IsModel.le_of_isFixedAt {S : Realization.{u, v} α M} (hS : S.IsModel)
    (hβ : Order.IsSuccPrelimit β) (h : S.IsFixedAt β) : α ≤ β :=
  not_lt.mp fun hβα ↦ hS.not_isFixedAt hβ hβα h

/-- A model at `α` is fixed by projection at a stage `β` that is zero or a limit exactly when
`α ≤ β`. -/
theorem IsModel.isFixedAt_iff {S : Realization.{u, v} α M} (hS : S.IsModel)
    (hβ : Order.IsSuccPrelimit β) : S.IsFixedAt β ↔ α ≤ β :=
  ⟨hS.le_of_isFixedAt hβ, S.isFixedAt_of_le⟩

/-- **The least fixing stage of a model is its stage**: for a model at a stage `α` that is zero
or a limit, `α` is the least stage that is zero or a limit at which the model is fixed by
projection. -/
theorem IsModel.isLeast_isFixedAt {S : Realization.{u, v} α M} (hS : S.IsModel)
    (hα : Order.IsSuccPrelimit α) :
    IsLeast {β : Ordinal.{u} | Order.IsSuccPrelimit β ∧ S.IsFixedAt β} α :=
  ⟨⟨hα, isFixedAt_self S⟩, fun _ ⟨hβ, h⟩ ↦ hS.le_of_isFixedAt hβ h⟩

/-! ### Block stages -/

/-- **Strictness for models at block stages**: a model at `λ_η` is fixed by projection at the
index `ξ` (at the block stage `λ_ξ`) exactly when `η ≤ ξ`. -/
theorem IsModel.isFixedAt_blockStage_iff {η ξ : Ordinal.{u}}
    {S : Realization.{u, v} (blockStage η) M} (hS : S.IsModel) :
    S.IsFixedAt (blockStage ξ) ↔ η ≤ ξ :=
  (hS.isFixedAt_iff (isSuccPrelimit_blockStage ξ)).trans blockStage_strictMono.le_iff_le

/-- **The least fixing index of a model is its index**: the least index at which the whole
assignment of a model at `λ_η` is fixed by projection is `η`. -/
theorem IsModel.isLeast_isFixedAt_blockStage {η : Ordinal.{u}}
    {S : Realization.{u, v} (blockStage η) M} (hS : S.IsModel) :
    IsLeast {ξ : Ordinal.{u} | S.IsFixedAt (blockStage ξ)} η :=
  ⟨hS.isFixedAt_blockStage_iff.mpr le_rfl, fun _ h ↦ hS.isFixedAt_blockStage_iff.mp h⟩

/-! ### Strict families and serving indices -/

/-- A family `F` of realizations, at the block stage `λ_ξ` for every index `ξ`, is **strict** when
every member of `F ξ` that is fixed by projection at an index `ζ` has `ξ ≤ ζ`. -/
def IsStrict (F : ∀ ξ : Ordinal.{u}, Set (Realization.{u, v} (blockStage ξ) M)) : Prop :=
  ∀ ⦃ξ : Ordinal.{u}⦄, ∀ S ∈ F ξ, ∀ ⦃ζ : Ordinal.{u}⦄, S.IsFixedAt (blockStage ζ) → ξ ≤ ζ

/-- **Every family of models is strict.** -/
theorem isStrict_of_forall_isModel
    {F : ∀ ξ : Ordinal.{u}, Set (Realization.{u, v} (blockStage ξ) M)}
    (hF : ∀ ⦃ξ : Ordinal.{u}⦄, ∀ S ∈ F ξ, S.IsModel) : IsStrict F :=
  fun _ S hS _ h ↦ (hF S hS).isFixedAt_blockStage_iff.mp h

/-- **The model expansions of a base structure form a strict family.** -/
theorem isStrict_isExpansionOf [baseLanguage.{u}.Structure M] :
    IsStrict fun ξ : Ordinal.{u} ↦ {S : Realization.{u, v} (blockStage ξ) M | S.IsExpansionOf} :=
  isStrict_of_forall_isModel fun _ _ hS ↦ hS.isModel

/-- **The bound of serving indices under strictness**: if every member of a strict family is fixed
by projection at the index `A`, every serving index of the family (an index `η` with `F η`
inhabited) is at most `A`. -/
theorem IsStrict.le_of_forall_isFixedAt
    {F : ∀ ξ : Ordinal.{u}, Set (Realization.{u, v} (blockStage ξ) M)} (hF : IsStrict F)
    {A : Ordinal.{u}} (hA : ∀ ⦃ξ : Ordinal.{u}⦄, ∀ S ∈ F ξ, S.IsFixedAt (blockStage A))
    {η : Ordinal.{u}} (hη : (F η).Nonempty) : η ≤ A :=
  let ⟨S, hS⟩ := hη
  hF S hS (hA S hS)

/-- **The bound of serving indices for a family of models**: if every member of a family of models
is fixed by projection at the index `A`, every serving index of the family is at most `A`. -/
theorem le_of_forall_isModel_of_forall_isFixedAt
    {F : ∀ ξ : Ordinal.{u}, Set (Realization.{u, v} (blockStage ξ) M)}
    (hF : ∀ ⦃ξ : Ordinal.{u}⦄, ∀ S ∈ F ξ, S.IsModel) {A : Ordinal.{u}}
    (hA : ∀ ⦃ξ : Ordinal.{u}⦄, ∀ S ∈ F ξ, S.IsFixedAt (blockStage A)) {η : Ordinal.{u}}
    (hη : (F η).Nonempty) : η ≤ A :=
  (isStrict_of_forall_isModel hF).le_of_forall_isFixedAt hA hη

end VaughtConjecture.Realization
