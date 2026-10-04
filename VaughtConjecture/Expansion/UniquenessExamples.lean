/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Definability.BlockFormulas
import VaughtConjecture.Expansion.Uniqueness

/-!
# Examples for uniqueness of model expansions and the limit clause

Special cases of `VaughtConjecture.Expansion.Uniqueness`:

* the three cases of the induction: the base case `Subsingleton (ModelExpansion M ω)` recovered
  from `ModelExpansion.subsingleton` at `ξ = 0`; the successor case from next-block uniqueness;
  the limit step with no hypothesis beyond uniqueness below the limit;
* coherence derived from uniqueness: every family of model expansions below a countable limit is
  coherent;
* limit existence at `λ_ω`;
* the limit clause of the expansion domains is an inclusion; with the downward closure it is an
  equality;
* next-block uniqueness from block determination at every countable block, a stronger hypothesis
  (`ModelExpansion.eq_of_determines`).

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

namespace VaughtConjecture.Expansion

open Ordinal FirstOrder Language Structure baseLanguage

section Cases

variable {M : Type} [baseLanguage.{0}.Structure M]

/-- The base case: at most one model expansion at the base stage `ω`, recovered from uniqueness at
the block stage `λ_0` (it is also unconditional, `ModelExpansion.instSubsingletonOmega`). -/
example (hu : NextBlockUniqueness.{0}) : Subsingleton (ModelExpansion M ω) :=
  blockStage_zero.{0} ▸ ModelExpansion.subsingleton hu (Ordinal.omega_pos 1)

/-- The successor case from next-block uniqueness: two model expansions to `λ_{ξ+1}` with equal
reductions to `λ_ξ` are equal. -/
example (hu : NextBlockUniqueness.{0}) {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    (e e' : ModelExpansion M (blockStage (ξ + 1)))
    (h : e.1.reduce (isSuccPrelimit_blockStage ξ) = e'.1.reduce (isSuccPrelimit_blockStage ξ)) :
    e = e' :=
  Subtype.ext (hu.eq_of_reduce_eq hξ e.1 e'.1 e.2.isModel e'.2.isModel h)

/-- The successor step of the induction: uniqueness at `λ_ξ` and next-block uniqueness give
uniqueness at `λ_{ξ+1}`. -/
example (hu : NextBlockUniqueness.{0}) {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    [Subsingleton (ModelExpansion M (blockStage ξ))] :
    Subsingleton (ModelExpansion M (blockStage (ξ + 1))) :=
  ⟨fun _ _ ↦ ModelExpansion.eq_of_reduceBlock_eq hu hξ (Subsingleton.elim _ _)⟩

/-- The limit step of the induction uses no hypothesis beyond uniqueness below the limit: a
realization at `λ_δ` is determined by its reductions to the earlier block stages. -/
example {δ : Ordinal.{0}} (hδ : Order.IsSuccLimit δ)
    (h : ∀ ξ < δ, Subsingleton (ModelExpansion M (blockStage ξ))) :
    Subsingleton (ModelExpansion M (blockStage δ)) :=
  ⟨fun e e' ↦ Subtype.ext (Realization.eq_of_forall_reduce_eq hδ fun ξ hξ ↦
    congrArg Subtype.val ((h ξ hξ).elim (e.reduceBlock hξ.le) (e'.reduceBlock hξ.le)))⟩

/-- Uniqueness at every countable block stage. -/
example (hu : NextBlockUniqueness.{0}) {ξ : Ordinal.{0}} (hξ : ξ < ω₁)
    (e e' : ModelExpansion M (blockStage ξ)) : e = e' :=
  (ModelExpansion.subsingleton hu hξ).elim e e'

end Cases

section Limit

variable {M : Type} [baseLanguage.{0}.Structure M]

/-- Coherence is derived from uniqueness: every family of model expansions below a countable limit
is coherent. -/
example (hu : NextBlockUniqueness.{0}) {δ : Ordinal.{0}} (hδω : δ < ω₁)
    (e : ∀ ξ < δ, ModelExpansion M (blockStage ξ)) :
    ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ) (h : ζ ≤ ξ), (e ξ hξ).reduceBlock h = e ζ hζ :=
  fun _ _ _ hξ h ↦ ModelExpansion.reduceBlock_eq hu (hξ.trans hδω) h _ _

/-- Limit existence at `λ_ω`: model expansions to every `λ_n`, `n < ω`, give one to `λ_ω`. -/
example (hu : NextBlockUniqueness.{0})
    (h : ∀ ξ < ω, Nonempty (ModelExpansion M (blockStage ξ))) :
    Nonempty (ModelExpansion M (blockStage ω)) :=
  ModelExpansion.nonempty_of_forall_lt hu isSuccLimit_omega0 omega0_lt_omega_one h

end Limit

/-! ### The limit clause of the expansion domains -/

/-- The limit clause is an inclusion; the reverse inclusion is the downward closure, so the
expansion domain at a countable limit is the intersection of the earlier ones. -/
example (hu : NextBlockUniqueness.{0}) {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (hlω : l < ω₁) : (⋂ ξ < l, expansionDomain ξ) = expansionDomain l :=
  (biInter_expansionDomain_subset hu hl hlω).antisymm
    (Set.subset_iInter₂ fun _ hξ ↦ expansionDomain_antitone hξ.le)

/-- The limit clause at `ω`. -/
example (hu : NextBlockUniqueness.{0}) :
    (⋂ ξ < ω, expansionDomain ξ) ⊆ expansionDomain ω :=
  biInter_expansionDomain_subset hu isSuccLimit_omega0 omega0_lt_omega_one

/-! ### Next-block uniqueness from block determination -/

/-- Block determination at every countable block (`CoverThresholds.Determines`, still to be
proved) gives next-block uniqueness: two models at `λ_{ξ+1}` with equal reductions to `λ_ξ` are
model expansions of one base structure, the structure of their common reduction to `ω`, and model
expansions are unique under block determination (`ModelExpansion.eq_of_determines`). -/
example (U : ∀ ξ : Ordinal.{0}, CoverThresholds ξ) (hU : ∀ ξ < ω₁, (U ξ).Determines.{0}) :
    NextBlockUniqueness.{0} := by
  refine ⟨fun {ξ M} hξ R R' hR hR' h ↦ ?_⟩
  let := (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  have hω : ξ + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt hξ
  have hb : ω ≤ blockStage ξ := omega0_le_blockStage ξ
  refine congrArg Subtype.val (ModelExpansion.eq_of_determines (U := U) (η := ξ + 1)
    (fun ζ hζ ↦ hU ζ (hζ.trans hω)) hω ⟨R, hR, rfl⟩ ⟨R', hR', ?_⟩)
  rw [← Realization.reduce_reduce _ (isSuccPrelimit_blockStage ξ) _ hb, ← h,
    Realization.reduce_reduce _ _ _ hb]

end VaughtConjecture.Expansion
