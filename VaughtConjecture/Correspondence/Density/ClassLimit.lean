/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.ClassRealization

/-!
# Coherent limits of class realizations: the targets

Numbering as in the current draft of [AFK26].  Write `λ_ξ = blockStage ξ = ω + ω · ξ`.

**What this file is, and what it is not.**  It states a *conditional* gluing ingredient for the
limit step of [AFK26, Proposition 4.34]: at a nonzero countable limit `δ`, a family of class
realizations at the stages `λ_ξ`, `ξ < δ`, that is coherent under stage reduction, well-formed,
and has donor density, has a limit class realization at `λ_δ` with the same three properties.
Coherence is a **hypothesis** here (`CoherentClassFamily.coherent`).  This is not the limit
conclusion of [AFK26, Proposition 4.34]: in the final assembly, coherence of the lower lifts must
be derived from lifts that exist on their own (after Reconstruction and the projection target
B.T9), and must not be kept as an extra hypothesis.  No modelhood, no unrestricted receiving, and
no correspondence between models and the printed classes is assumed or used.

**Classes, not positions** (native construction).  The members of the family are class
realizations (`ClassRealization`): each tuple carries a class of stage types up to cell renaming
(`TemplateClass`).  Coherence is an equality of class realizations,
`(S ζ).reduce _ = S ξ` for `ξ < ζ < δ`, so at each tuple the renaming witnessing it is chosen at
that pair of stages; representatives of the classes may vary by renaming from stage to stage, and
no coherent positional presentation across the stages is assumed.

## The targets

Stated here as propositions, every premise visible.  None is proved in this file except the
reordering of the cutoff quantifier
(`ClassRealization.hasDonorDensity_iff_forall_hasDonorDensityAt`).

* **Coherent families of classes** (`TemplateClass.IsCoherentFamily c`, for
  `c : ∀ ξ < δ, TemplateClass (λ_ξ) n`): `(c ζ).reduce _ = c ξ` for `ξ < ζ < δ`; the class form,
  at one tuple, of the coherence of `CoherentClassFamily`.
* **Stabilization of a coherent family of classes** (`ClassStabilizationTarget δ n`): for a limit
  `δ`, every coherent family of classes below `δ` is eventually constant up to the reading of the
  stage: some `ξ₀ < δ` has `c ξ = (c ξ₀).castLE _` for every `ξ₀ ≤ ξ < δ`.  It is the class
  analogue of `StageType.IsCoherentFamily.eq_castLE`; the positional proof there tracks the cell
  at a fixed position across the stages, which a class does not have, so the class form needs its
  own argument (expected: the number of cells labelled by the formal top is invariant under
  renaming, can only grow under stage reduction, and so is eventually constant along the family).
* **Descent of a class at `λ_δ`** (`ClassDescentTarget δ n`): for a limit `δ`, every class at
  `λ_δ` is, from some `ξ₀ < δ` on, its reduction to `λ_ξ` read back at `λ_δ`.  A class at `λ_δ`
  has finitely many labels below `λ_δ`, each below some `λ_ξ`.  It gives separation of classes at
  `λ_δ` (two classes with equal reductions to every `λ_ξ`, `ξ < δ`, are equal), which the
  consistency of the limit needs; see *Overlap* below.
* **Gluing of a coherent family of classes** (`ClassFamilyGluingTarget δ n`): for a limit `δ`,
  every coherent family of classes below `δ` has a class at `λ_δ` reducing to each member; the
  class analogue of `StageType.IsCoherentFamily.glue_reduce`.
* **Observation along stage reduction** (`ObservesAtReduceTarget α β n`): for a cutoff `x ≤ β`,
  the reduction of `q` to `β` observes the reduction of `D` at `x` exactly when `q` observes `D`
  at `x` (`TemplateClass.ObservesAt`); the class form of
  `StageType.reduce_mem_receivingFamily_reduce_iff`.
* **The gluing target** (`ClassGluingTarget δ M`): for a limit `δ < ω₁`, every
  `CoherentClassFamily δ M` has a class realization `T` at `λ_δ` with
  `T.reduce _ = S.family ξ _` for every `ξ < δ`, `T.IsWellFormed`, and donor density of `T` at
  every permitted cutoff `x` at `λ_δ`.

**The cutoffs** (native construction).  `ClassRealization.HasDonorDensity` at a stage `α`
already quantifies over every permitted cutoff at `α`, that is every label `x` with
`⊥ < x < α` (`Label.IsPermittedCutoff`).  At `α = λ_δ` these are exactly the cutoffs below the
block stage `λ_δ`: the ordinals `0 < x < λ_δ`, each of which lies below some `λ_ξ`, `ξ < δ`, since
block stages are continuous at limits.  The target states the cutoff quantifier explicitly,
through `ClassRealization.HasDonorDensityAt` (donor density at one cutoff), and
`hasDonorDensity_iff_forall_hasDonorDensityAt` identifies the conjunction over the permitted
cutoffs with `HasDonorDensity`.  The cutoff `λ_δ` itself and the formal top are not permitted
cutoffs at `λ_δ`, and are not claimed.

**Countability.**  The premise `δ < ω₁` of `ClassGluingTarget` records the countable range of
[AFK26, Proposition 4.34]; the expected construction does not use it.

**Overlap.**  Separation of classes at `λ_δ` is stated by Reconstruction as its
`ClassSeparationTarget` (on its own branch, not on `main`).  This file does not restate it under
that name; separation is to be proved here, if needed, as a consequence of `ClassDescentTarget`
under a local name, to be merged with the statement of Reconstruction when both land.

## Placement

This file belongs to the limit step of Reconstruction (roadmap, Layer 4).
-/

universe u v

namespace VaughtConjecture

open Ordinal

noncomputable section

/-! ### Donor density at one cutoff -/

namespace ClassRealization

variable {α : Ordinal.{u}} {M : Type v} (R : ClassRealization.{u, v} α M)

/-- **Donor density at a cutoff `x`** (native construction): `ClassRealization.HasDonorDensity`
with the cutoff fixed.  For every typed tuple `t` of class `p`, every strongly coded legal class
`D` at the stage `α` on `m` points whose face along `g : Fin n ↪ Fin m` is `p` (`n = 0`
included), some injective tuple `u` extends `t` along `g` literally and has a class `q` with the
observation of `D` at `x` up to renaming.  Native construction. -/
def HasDonorDensityAt (x : Label.{u}) : Prop :=
  ∀ ⦃n m : ℕ⦄ (t : Fin n ↪ M) (p : TemplateClass.{u} α n), R.eval t = some p →
    ∀ (D : TemplateClass.{u} α m) (g : Fin n ↪ Fin m), D.IsStronglyCodedLegal →
      D.restrictFace g = some p →
        ∃ u : Fin m ↪ M, g.trans u = t ∧ ∃ q, R.eval u = some q ∧ q.ObservesAt x D

/-- **Donor density is donor density at every permitted cutoff** (`⊥ < x < α`).
Native construction. -/
theorem hasDonorDensity_iff_forall_hasDonorDensityAt :
    R.HasDonorDensity ↔ ∀ x : Label.{u}, Label.IsPermittedCutoff α x → R.HasDonorDensityAt x :=
  ⟨fun h _ hx _ _ t p hp D g hD hDg ↦ h t p hp D g hD hDg _ hx,
    fun h _ _ t p hp D g hD hDg _ hx ↦ h _ hx t p hp D g hD hDg⟩

end ClassRealization

/-! ### Coherent families -/

namespace TemplateClass

variable {δ : Ordinal.{u}} {n : ℕ}

/-- A family of classes at the block stages below `δ` is a **coherent family** when the class at
`ζ` reduces to the class at every `ξ < ζ`.  An equality of classes: the renaming witnessing it is
chosen for each pair of stages.  Native construction. -/
def IsCoherentFamily (c : ∀ ξ < δ, TemplateClass.{u} (blockStage ξ) n) : Prop :=
  ∀ ξ (hξ : ξ < δ) ζ (hζ : ζ < δ), ξ < ζ →
    (c ζ hζ).reduce (isSuccPrelimit_blockStage ξ) = c ξ hξ

end TemplateClass

/-- **A coherent family of class realizations** below `δ` on `M` (native construction): class
realizations at the block stages `λ_ξ`, `ξ < δ`, with explicit coherence under stage reduction
(an equality of class realizations, so renamings of representatives are absorbed tuple by
tuple), each well-formed and with donor density.  Coherence is a hypothesis of every statement
that uses this structure; nothing here derives it.  Native construction. -/
structure CoherentClassFamily (δ : Ordinal.{u}) (M : Type v) where
  /-- The class realization at the block stage `λ_ξ`. -/
  family : ∀ ξ < δ, ClassRealization.{u, v} (blockStage ξ) M
  /-- Coherence: the member at `ζ` reduces to the member at every `ξ < ζ`. -/
  coherent : ∀ ξ (hξ : ξ < δ) ζ (hζ : ζ < δ), ξ < ζ →
    (family ζ hζ).reduce (isSuccPrelimit_blockStage ξ) = family ξ hξ
  /-- Every member is well-formed. -/
  isWellFormed : ∀ ξ (hξ : ξ < δ), (family ξ hξ).IsWellFormed
  /-- Every member has donor density, at every permitted cutoff at its own stage. -/
  hasDonorDensity : ∀ ξ (hξ : ξ < δ), (family ξ hξ).HasDonorDensity

/-! ### The targets -/

/-- **Target: stabilization of a coherent family of classes** (native construction): for a limit
`δ`, every coherent family of classes on `n` points at the block stages below `δ` is eventually
constant up to the reading of the stage: some `ξ₀ < δ` has `c ξ = (c ξ₀).castLE _` for every
`ξ₀ ≤ ξ < δ`.  The class analogue of `StageType.IsCoherentFamily.eq_castLE`, without a cell
position tracked across the stages. -/
def ClassStabilizationTarget (δ : Ordinal.{u}) (n : ℕ) : Prop :=
  Order.IsSuccLimit δ → ∀ c : ∀ ξ < δ, TemplateClass.{u} (blockStage ξ) n,
    TemplateClass.IsCoherentFamily c → ∃ ξ₀, ∃ h₀ : ξ₀ < δ, ∀ ξ (hξ : ξ < δ) (h : ξ₀ ≤ ξ),
      c ξ hξ = (c ξ₀ h₀).castLE (blockStage_mono h)

/-- **Target: descent of a class at a limit block stage** (native construction): for a limit `δ`,
every class `c` on `n` points at `λ_δ` has some `ξ₀ < δ` such that, for every `ξ₀ ≤ ξ < δ`, the
reduction of `c` to `λ_ξ`, read back at `λ_δ`, is `c`. -/
def ClassDescentTarget (δ : Ordinal.{u}) (n : ℕ) : Prop :=
  Order.IsSuccLimit δ → ∀ c : TemplateClass.{u} (blockStage δ) n, ∃ ξ₀ < δ,
    ∀ ξ (hξ : ξ < δ), ξ₀ ≤ ξ →
      (c.reduce (isSuccPrelimit_blockStage ξ)).castLE (blockStage_strictMono hξ).le = c

/-- **Target: gluing a coherent family of classes** (native construction): for a limit `δ`,
every coherent family of classes on `n` points at the block stages below `δ` has a class at
`λ_δ` whose reduction to every `λ_ξ`, `ξ < δ`, is the member at `ξ`.  The class analogue of
`StageType.IsCoherentFamily.glue_reduce`. -/
def ClassFamilyGluingTarget (δ : Ordinal.{u}) (n : ℕ) : Prop :=
  Order.IsSuccLimit δ → ∀ c : ∀ ξ < δ, TemplateClass.{u} (blockStage ξ) n,
    TemplateClass.IsCoherentFamily c → ∃ d : TemplateClass.{u} (blockStage δ) n,
      ∀ ξ (hξ : ξ < δ), d.reduce (isSuccPrelimit_blockStage ξ) = c ξ hξ

/-- **Target: observation along stage reduction** (native construction): for a stage `β` that is
zero or a limit and a cutoff `x ≤ β`, the reduction of `q` to `β` observes the reduction of `D`
at `x` exactly when `q` observes `D` at `x`.  The class form of
`StageType.reduce_mem_receivingFamily_reduce_iff`. -/
def ObservesAtReduceTarget (α β : Ordinal.{u}) (n : ℕ) : Prop :=
  ∀ (hβ : Order.IsSuccPrelimit β) (q D : TemplateClass.{u} α n) (x : Label.{u}), x ≤ β →
    ((q.reduce hβ).ObservesAt x (D.reduce hβ) ↔ q.ObservesAt x D)

/-- **Target: the coherent limit of class realizations** (native construction, conditional on
coherence): for a limit `δ < ω₁`, every coherent family `S` of well-formed class realizations
with donor density at the block stages below `δ` has a class realization `T` at `λ_δ` with

* `T.reduce _ = S.family ξ _` for every `ξ < δ` (equality of class realizations);
* `T.IsWellFormed`;
* donor density of `T` at every permitted cutoff `x` at `λ_δ` (`⊥ < x < λ_δ`, the cutoffs below
  the block stage `λ_δ`), which is `T.HasDonorDensity`
  (`ClassRealization.hasDonorDensity_iff_forall_hasDonorDensityAt`).

Coherence of the family is a premise, not a conclusion; this is not the limit conclusion of
[AFK26, Proposition 4.34], whose assembly must derive the coherence.  The premise `δ < ω₁` is the
countable range of [AFK26, Proposition 4.34]. -/
def ClassGluingTarget (δ : Ordinal.{u}) (M : Type v) : Prop :=
  Order.IsSuccLimit δ → δ < ω₁ → ∀ S : CoherentClassFamily.{u, v} δ M,
    ∃ T : ClassRealization.{u, v} (blockStage δ) M,
      (∀ ξ (hξ : ξ < δ), T.reduce (isSuccPrelimit_blockStage ξ) = S.family ξ hξ) ∧
        T.IsWellFormed ∧
          ∀ x : Label.{u}, Label.IsPermittedCutoff (blockStage δ) x → T.HasDonorDensityAt x

end

end VaughtConjecture
