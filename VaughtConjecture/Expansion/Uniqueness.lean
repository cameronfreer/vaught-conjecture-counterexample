/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Domains
import VaughtConjecture.Realization.Limit

/-!
# Uniqueness of model expansions and continuity of the expansion domains at limits

Roadmap, the reduction of the main theorem to expansion domains (condition 1, continuity at
nonzero countable limits), Layer 5 (coherent countable-limit expansions), and outputs 4
(uniqueness and coherence of partial expansions) and 5 (limit existence) of higher-stage
reconstruction, Layer 4; semantic contract, items 5 and 9.

**Next-block uniqueness.**  `NextBlockUniqueness` is the statement that two models at the block
stage `λ_{ξ+1} = λ_ξ + ω`, `ξ < ω₁`, on one carrier, with the same stage reduction to `λ_ξ`, are
equal.  It is a consequence of normalization (output 2 of higher-stage reconstruction, Layer 4:
every actual next-block model expansion agrees with the structural candidate read from its
reduction), which is still to be proved; here it is an explicit hypothesis, and it is the only
statement of Layer 4 used in this file.  A stronger hypothesis, block determination at every
countable block (`CoverThresholds.Determines`, in `VaughtConjecture.Definability.BlockFormulas`),
gives uniqueness of model expansions directly (`ModelExpansion.eq_of_determines`), hence also
next-block uniqueness (an example in `VaughtConjecture.Expansion.UniquenessExamples`).

**Uniqueness of model expansions** (`ModelExpansion.subsingleton`): a base structure has at most
one model expansion to each block stage `λ_ξ`, `ξ < ω₁`, by transfinite induction on `ξ`.
* At `ξ = 0`, unconditionally: a model expansion to `λ_0 = ω` is the realization of its base
  structure (`ModelExpansion.instSubsingletonOmega`).
* At a successor `ξ + 1`, by `NextBlockUniqueness`: the reductions of two expansions to `λ_ξ` are
  expansions there, equal by the induction hypothesis.
* At a nonzero limit `δ`, unconditionally: a realization at `λ_δ` is determined by its reductions
  to the earlier block stages (`Realization.eq_of_forall_reduce_eq`), which are equal by the
  induction hypothesis.

**Limit existence** (`ModelExpansion.nonempty_of_forall_lt`): for a nonzero limit `δ < ω₁`, a
base structure with a model expansion to every `λ_ξ`, `ξ < δ`, has one to `λ_δ`.  The chosen
expansions below `δ` are coherent because the expansion at each `λ_ζ` is unique, so coherence is
derived from uniqueness, never assumed; the coherent family then glues to a model expansion at
`λ_δ` (`ModelExpansion.nonempty_of_coherent`, which proves every clause of a model for the glued
expansion).

**The limit clause of the expansion domains** (`biInter_expansionDomain_subset`): at a nonzero
limit `l < ω₁`, the expansion domain at `l` contains the intersection of the earlier ones.  A class
in the intersection has, for one fixed code, a model expansion to every earlier `λ_ξ`
(`mem_expansionDomain_iff`, by transport along isomorphisms of codes), and limit existence applies
to that code.  The inclusion is the limit clause of `ExpansionDomains`; the reverse inclusion is
the downward closure (`expansionDomain_antitone`).

The only hypothesis is `NextBlockUniqueness`, used at successor steps; the base case and the limit
step of the induction are unconditional.  No coherence of expansions, no termination of the
expansions of a class below `ω₁`, and no receiving property is assumed.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

namespace Expansion

/-- **Next-block uniqueness of models**: two models at the block stage `λ_{ξ+1} = λ_ξ + ω`,
`ξ < ω₁`, on one carrier in the universe `w`, with the same stage reduction to `λ_ξ`, are equal.
It is a consequence of normalization (output 2 of higher-stage reconstruction, Layer 4 of the
roadmap; checkpoint 5), still to be proved, and is a hypothesis here.  It also follows from block
determination at every countable block, a stronger hypothesis
(`ModelExpansion.eq_of_determines`). -/
structure NextBlockUniqueness : Prop where
  /-- Models at `λ_{ξ+1}` with equal reductions to `λ_ξ` are equal. -/
  eq_of_reduce_eq : ∀ {ξ : Ordinal.{0}} {M : Type w}, ξ < ω₁ →
    ∀ R R' : Realization.{0, w} (blockStage (ξ + 1)) M, R.IsModel → R'.IsModel →
      R.reduce (isSuccPrelimit_blockStage ξ) = R'.reduce (isSuccPrelimit_blockStage ξ) → R = R'

end Expansion

section ModelExpansion

variable {M : Type w} [baseLanguage.{0}.Structure M]

/-- **The successor step of uniqueness**: given next-block uniqueness, two model expansions to
`λ_{ξ+1}`, `ξ < ω₁`, whose reductions to `λ_ξ` are equal, are equal. -/
theorem ModelExpansion.eq_of_reduceBlock_eq (hu : Expansion.NextBlockUniqueness.{w})
    {ξ : Ordinal.{0}} (hξ : ξ < ω₁) {e e' : ModelExpansion M (blockStage (ξ + 1))}
    (h : e.reduceBlock (Order.le_succ ξ) = e'.reduceBlock (Order.le_succ ξ)) : e = e' :=
  Subtype.ext (hu.eq_of_reduce_eq hξ e.1 e'.1 e.2.isModel e'.2.isModel
    (congrArg Subtype.val h))

/-- **Uniqueness of model expansions**, given next-block uniqueness: a base structure has at most
one model expansion to each block stage `λ_ξ`, `ξ < ω₁`.  By transfinite induction on `ξ`: the
base case `λ_0 = ω` is unconditional (`ModelExpansion.instSubsingletonOmega`); the successor step
is next-block uniqueness, applied to the reductions, which are equal by the induction hypothesis;
the limit step is unconditional, by separation of realizations at a limit block stage
(`Realization.eq_of_forall_reduce_eq`). -/
theorem ModelExpansion.subsingleton (hu : Expansion.NextBlockUniqueness.{w}) {ξ : Ordinal.{0}}
    (hξ : ξ < ω₁) : Subsingleton (ModelExpansion M (blockStage ξ)) := by
  induction ξ using Ordinal.limitRecOn with
  | zero =>
    rw [blockStage_zero]
    infer_instance
  | add_one ξ ih =>
    have hξ' : ξ < ω₁ := (Order.lt_add_one_iff.mpr le_rfl).trans hξ
    have := ih hξ'
    exact ⟨fun e e' ↦ ModelExpansion.eq_of_reduceBlock_eq hu hξ' (Subsingleton.elim _ _)⟩
  | limit δ hδ ih =>
    refine ⟨fun e e' ↦ Subtype.ext (Realization.eq_of_forall_reduce_eq hδ fun ζ hζ ↦ ?_)⟩
    have := ih ζ hζ (hζ.trans hξ)
    exact congrArg Subtype.val (Subsingleton.elim (e.reduceBlock hζ.le) (e'.reduceBlock hζ.le))

/-- **Coherence from uniqueness**, given next-block uniqueness: for `ζ ≤ ξ < ω₁`, the reduction
to `λ_ζ` of any model expansion to `λ_ξ` is the given model expansion to `λ_ζ`. -/
theorem ModelExpansion.reduceBlock_eq (hu : Expansion.NextBlockUniqueness.{w})
    {ζ ξ : Ordinal.{0}} (hξ : ξ < ω₁) (h : ζ ≤ ξ) (e : ModelExpansion M (blockStage ξ))
    (e' : ModelExpansion M (blockStage ζ)) : e.reduceBlock h = e' :=
  (ModelExpansion.subsingleton hu (h.trans_lt hξ)).elim _ _

/-- **Limit existence**, given next-block uniqueness: for a nonzero limit `δ < ω₁`, a base
structure with a model expansion to every block stage `λ_ξ`, `ξ < δ`, has a model expansion to
`λ_δ`.  Any choice of the expansions below `δ` is coherent, by uniqueness
(`ModelExpansion.reduceBlock_eq`), so coherence is derived, not assumed; the coherent family glues
to a model expansion at `λ_δ` (`ModelExpansion.nonempty_of_coherent`). -/
theorem ModelExpansion.nonempty_of_forall_lt (hu : Expansion.NextBlockUniqueness.{w})
    {δ : Ordinal.{0}} (hδ : Order.IsSuccLimit δ) (hδω : δ < ω₁)
    (h : ∀ ξ < δ, Nonempty (ModelExpansion M (blockStage ξ))) :
    Nonempty (ModelExpansion M (blockStage δ)) :=
  ModelExpansion.nonempty_of_coherent hδ (fun ξ hξ ↦ (h ξ hξ).some)
    fun _ _ _ hξ hle ↦ ModelExpansion.reduceBlock_eq hu (hξ.trans hδω) hle _ _

end ModelExpansion

namespace Expansion

/-- **The limit clause of the expansion domains**, given next-block uniqueness: at a nonzero limit
`l < ω₁`, the expansion domain at `l` contains the intersection of the earlier ones.  For a class
in the intersection, one fixed code has a model expansion to every `λ_ξ`, `ξ < l`
(`mem_expansionDomain_iff`), hence one to `λ_l` (`ModelExpansion.nonempty_of_forall_lt`).  The
reverse inclusion is the downward closure (`expansionDomain_antitone`). -/
theorem biInter_expansionDomain_subset (hu : NextBlockUniqueness.{0}) {l : Ordinal.{0}}
    (hl : Order.IsSuccLimit l) (hlω : l < ω₁) :
    (⋂ ξ < l, expansionDomain ξ) ⊆ expansionDomain l := by
  intro q hq
  induction q using Quotient.inductionOn with
  | h c =>
    simp only [Set.mem_iInter] at hq
    let := c.1.toStructure
    exact (mem_expansionDomain_iff c).mpr (ModelExpansion.nonempty_of_forall_lt hu hl hlω
      fun ξ hξ ↦ (mem_expansionDomain_iff c).mp (hq ξ hξ))

end Expansion

end VaughtConjecture
