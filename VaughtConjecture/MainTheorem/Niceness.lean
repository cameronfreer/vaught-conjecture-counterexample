/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Terminal
import VaughtConjecture.Expansion.Uniqueness
import VaughtConjecture.Language.Structure

/-!
# Niceness of base reducts from a terminal refinement

Roadmap, the section "Manuscript correspondence (required)", item 5: positive niceness
(milestone 2 of "Uniform fixing bounds from positive niceness"), the implication 5 ⇒ 1 of
"Maximal presentations: equivalent criteria, uniqueness, the optimal bound", terminal collision,
and "Two stopping proofs; positive niceness from a terminal presentation"; `IMPLEMENTATION.md`,
"Manuscript concordance", rows 30 and 33–35.

**The system and its lifts.**  The stage classes are read as the models at the block stages
`λ_α` on a fixed carrier, and a lift at the index `α` of a base structure `M` (a structure of the
base language) is a model expansion of `M` at `λ_α` (`ModelExpansion M (blockStage α)`): a model at
`λ_α` on the carrier of `M` whose base reduct is literally `M`.  That these are the stage classes
of [AFK26] is still to be proved (`README.md`, item 5, first row of its table).  A closed tuple of
`M` is read as a **supported** tuple: an injective tuple typed in the realization of `M` at `ω`
(`baseLanguage.toRealization`), that is, one of which some relation of the base language holds.
The comparison of these with the closed tuples of [AFK26] is still to be proved (concordance
row 29, with item 2).  An invariant realized at a tuple is its stage type; the invariant `Q` of a
lift at `λ_α` is realized at the same tuple by a lift at a higher stage `λ_{α'}` when that lift
evaluates the tuple to `Q` read at `λ_{α'}` (`StageType.castLE`, the same scheme and labels): the
comparison is in the alphabet of all labels.

**Niceness** [AFK26, Definition 2.19] (numbering of the current draft).  A tuple `u` is **nice at
the threshold `α` with the invariant `Q`** (`IsNiceTupleAt`) when
1. some lift of `M` at `α` realizes `Q` at `u` (`IsNiceTupleAt.exists_lift`), and
2. every lift of `M` at every countable index `α' > α` realizes `Q` at `u`
   (`IsNiceTupleAt.forall_lift`).

The tuple is **nice** (`IsNiceTuple`) when it is nice at some countable threshold with some
invariant, and `M` is **nice** (`IsNice`) when every closed tuple is.  Clause 2 quantifies over all
lifts at every higher index, not over one chosen lift; this is positive niceness over all
admissible lifts (concordance row 30), for the family of all model presentations of `M`.

**Maximality gives niceness** (the implication 5 ⇒ 1 of the five criteria).  The **serving
indices** of `M` are the countable indices at which `M` has a lift (`README.md`, item 5), and an
ordinal `ρ` **bounds** them (`BoundsServingIndices`) when each is at most `ρ`.  A lift at a
countable `ρ` that bounds the serving indices is a maximal presentation of `M` in the raw base
encoding.  Its invariant at each closed tuple is
then a niceness threshold at `ρ`, with an actual witness (the lift itself), clause 2 being vacuous
(`isNiceTupleAt_of_boundsServingIndices`); so `M` is nice (`isNice_of_boundsServingIndices`).  This
step uses neither terminality nor the injectivity of model reduction.

**Terminal collision** (`ModelExpansion.boundsServingIndices_of_isTerminalAt`).  A lift at a
countable `ρ` that is terminal at `ρ` (`Realization.IsTerminalAt`) bounds the serving indices,
given next-block uniqueness (`Expansion.NextBlockUniqueness`, still to be proved): the reduction
to `λ_ρ` of a lift at a higher index is a lift at `ρ`, equal to the given one by the uniqueness of
model expansions (`ModelExpansion.subsingleton`), which contradicts terminality
(`Realization.isTerminalAt_iff_forall_lt`).

**Terminal refinement** (`HasMaximalRefinement`, a named hypothesis, still to be proved).  Every
model `V` at a block stage `λ_β` on a countable carrier is literally the stage reduction of a model
`W` at `λ_ρ` on the same carrier, for a countable `ρ ≥ β`, terminal at `ρ`: the specified terminal
refinement of `README.md`, item 5 (concordance row 38).

**Condition (c) of the system** [AFK26, Definition 2.22, clause (c)]: the base reduct of every
model of the system is nice.  Here, conditional on `HasMaximalRefinement` and
`Expansion.NextBlockUniqueness`, both still to be proved, the base reduct of every model at a block
stage on a countable carrier is nice (`Realization.IsModel.isNice_toStructure_reduce`; for a base
structure with a lift, `isNice_of_hasMaximalRefinement`).  One terminal refinement serves every
closed tuple at once: a single maximal presentation supplies an inhabited threshold `ρ` for all
closed tuples, with its own invariant at each as the actual witness
(`exists_isNiceTupleAt_of_hasMaximalRefinement`).  The order of the argument is the one of the
roadmap: a terminal presentation first, then positive niceness; no fixing bound is used, and no
termination hypothesis enters beyond `HasMaximalRefinement`.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

section Niceness

variable (M : Type w) [baseLanguage.{0}.Structure M] {n : ℕ}

/-- **Niceness of a tuple at a threshold** [AFK26, Definition 2.19]: the injective tuple `u` of the
base structure `M` is nice at the threshold `α` with the invariant `Q`, a stage type at `λ_α`.
One field for each of the two clauses of the definition. -/
structure IsNiceTupleAt (u : Fin n ↪ M) (α : Ordinal.{0}) (Q : StageType.{0} (blockStage α) n) :
    Prop where
  /-- Clause 1: some lift of `M` at the threshold `α` realizes `Q` at `u`. -/
  exists_lift : ∃ e : ModelExpansion M (blockStage α), e.1.eval u = some Q
  /-- Clause 2: every lift of `M` at every countable index `α' > α` realizes `Q` at `u`. -/
  forall_lift : ∀ ⦃α' : Ordinal.{0}⦄ (h : α < α'), α' < ω₁ →
    ∀ e : ModelExpansion M (blockStage α'),
      e.1.eval u = some (Q.castLE (blockStage_mono h.le))

/-- **A nice tuple** [AFK26, Definition 2.19]: the injective tuple `u` of `M` is nice at some
countable threshold `α` with some invariant `Q`. -/
def IsNiceTuple (u : Fin n ↪ M) : Prop :=
  ∃ α < ω₁, ∃ Q : StageType.{0} (blockStage α) n, IsNiceTupleAt M u α Q

/-- **A nice base structure** [AFK26, Definition 2.19, last sentence]: every closed tuple of `M`,
read as a tuple supported in the realization of `M` at `ω`, is nice. -/
structure IsNice : Prop where
  /-- Every closed tuple is nice. -/
  isNiceTuple : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M), ((toRealization M).eval u).isSome → IsNiceTuple M u

/-- `ρ` **bounds the serving indices** of `M`: every countable index at which `M` has a lift (a
model expansion at its block stage) is at most `ρ`. -/
def BoundsServingIndices (ρ : Ordinal.{0}) : Prop :=
  ∀ ⦃α : Ordinal.{0}⦄, α < ω₁ → Nonempty (ModelExpansion M (blockStage α)) → α ≤ ρ

variable {M}

/-- **The realization of the base structure is the base reduct of a lift**: for a model
expansion `e` of `M`, the realization of `M` at `ω` is the stage reduction of `e` to `ω`. -/
theorem ModelExpansion.toRealization_eq_reduce {α : Ordinal.{0}} (e : ModelExpansion M α) :
    toRealization M = e.1.reduce isSuccLimit_omega0.isSuccPrelimit := by
  obtain ⟨R, hR⟩ := e
  have h := hR.toStructure_reduce
  change toRealization M = R.reduce _
  rw [← h]
  exact toRealization_toStructure (hR.isModel.hasLegalTypes.reduce _)

/-- **A closed tuple is typed in every lift**: a tuple supported in the realization of `M` at `ω`
has a type in every model expansion of `M`. -/
theorem ModelExpansion.isSome_eval {α : Ordinal.{0}} (e : ModelExpansion M α) {u : Fin n ↪ M}
    (hu : ((toRealization M).eval u).isSome) : (e.1.eval u).isSome := by
  rwa [e.toRealization_eq_reduce, Realization.isSome_reduce_eval] at hu

/-- **Maximality gives a niceness threshold** (the implication 5 ⇒ 1): if `ρ` bounds the serving
indices of `M`, the invariant `Q` of a tuple in a lift at `ρ` makes the tuple nice at `ρ`; the lift
is the actual witness of clause 1, and clause 2 is vacuous. -/
theorem isNiceTupleAt_of_boundsServingIndices {ρ : Ordinal.{0}} (hb : BoundsServingIndices M ρ)
    (e : ModelExpansion M (blockStage ρ)) {u : Fin n ↪ M} {Q : StageType.{0} (blockStage ρ) n}
    (hQ : e.1.eval u = some Q) : IsNiceTupleAt M u ρ Q :=
  ⟨⟨e, hQ⟩, fun _ h hα e' ↦ absurd (hb hα ⟨e'⟩) (not_le.mpr h)⟩

/-- **A maximal presentation makes the base nice**: if `M` has a lift at a countable `ρ` that
bounds its serving indices, then `M` is nice, every closed tuple at the threshold `ρ`. -/
theorem isNice_of_boundsServingIndices {ρ : Ordinal.{0}} (hρ : ρ < ω₁)
    (hb : BoundsServingIndices M ρ) (e : ModelExpansion M (blockStage ρ)) : IsNice M :=
  ⟨fun _ u hu ↦ by
    obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp (e.isSome_eval hu)
    exact ⟨ρ, hρ, Q, isNiceTupleAt_of_boundsServingIndices hb e hQ⟩⟩

/-- **Terminal collision**, given next-block uniqueness: a lift of `M` at a countable `ρ` that is
terminal at `ρ` bounds the serving indices of `M`.  The reduction to `λ_ρ` of a lift at an index
above `ρ` is a lift at `ρ`, hence the given one (`ModelExpansion.subsingleton`), against
terminality (`Realization.isTerminalAt_iff_forall_lt`). -/
theorem ModelExpansion.boundsServingIndices_of_isTerminalAt
    (hu : Expansion.NextBlockUniqueness.{w}) {ρ : Ordinal.{0}} (hρ : ρ < ω₁)
    (e : ModelExpansion M (blockStage ρ)) (he : e.1.IsTerminalAt ρ) :
    BoundsServingIndices M ρ := by
  intro α _ ⟨e'⟩
  by_contra hlt
  have hρα : ρ < α := not_le.mp hlt
  have heq : e'.reduceBlock hρα.le = e := (ModelExpansion.subsingleton hu hρ).elim _ _
  exact Realization.isTerminalAt_iff_forall_lt.mp he (isSuccPrelimit_blockStage α)
    (blockStage_strictMono hρα) e'.1 e'.2.isModel (congrArg Subtype.val heq)

end Niceness

/-- **Terminal refinement on the same carrier** (a named hypothesis, still to be proved): every
model `V` at a block stage `λ_β` on a countable carrier in the universe `w` is literally the stage
reduction of a model `W` at `λ_ρ` on the same carrier, for a countable `ρ ≥ β`, with `W` terminal
at `ρ`.  It is the specified terminal refinement of `README.md`, item 5 (concordance row 38). -/
structure HasMaximalRefinement : Prop where
  /-- Every model on a countable carrier is the reduction of a terminal model above it. -/
  exists_isTerminalAt : ∀ {M : Type w} [Countable M] {β : Ordinal.{0}}
    (V : Realization.{0, w} (blockStage β) M), V.IsModel →
      ∃ ρ : Ordinal.{0}, β ≤ ρ ∧ ρ < ω₁ ∧ ∃ W : Realization.{0, w} (blockStage ρ) M,
        W.IsModel ∧ W.IsTerminalAt ρ ∧ W.reduce (isSuccPrelimit_blockStage β) = V

section Refinement

variable {M : Type w} [baseLanguage.{0}.Structure M] [Countable M]

/-- **A single maximal presentation serves every closed tuple**, conditional on
`HasMaximalRefinement` and `Expansion.NextBlockUniqueness`, both still to be proved: a base
structure `M` on a countable carrier with a lift `V` at `λ_β` has a lift `e` at a countable
`ρ ≥ β` reducing to `V`, terminal at `ρ` and bounding the serving indices of `M`, at which every
closed tuple is nice with its own invariant in `e` as the actual witness. -/
theorem exists_isNiceTupleAt_of_hasMaximalRefinement (hmax : HasMaximalRefinement.{w})
    (hu : Expansion.NextBlockUniqueness.{w}) {β : Ordinal.{0}}
    (V : ModelExpansion M (blockStage β)) :
    ∃ ρ : Ordinal.{0}, β ≤ ρ ∧ ρ < ω₁ ∧ ∃ e : ModelExpansion M (blockStage ρ),
      e.1.reduce (isSuccPrelimit_blockStage β) = V.1 ∧ e.1.IsTerminalAt ρ ∧
      BoundsServingIndices M ρ ∧ ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M), ((toRealization M).eval u).isSome →
        ∃ Q : StageType.{0} (blockStage ρ) n, e.1.eval u = some Q ∧ IsNiceTupleAt M u ρ Q := by
  obtain ⟨ρ, hβρ, hρ, W, hW, ht, hWV⟩ := hmax.exists_isTerminalAt V.1 V.2.isModel
  have hexp : W.IsExpansionOf := ⟨hW, by
    rw [← W.reduce_reduce (isSuccPrelimit_blockStage β) isSuccLimit_omega0.isSuccPrelimit
      (omega0_le_blockStage β), hWV]
    exact V.2.toStructure_reduce⟩
  let e : ModelExpansion M (blockStage ρ) := ⟨W, hexp⟩
  have hb := e.boundsServingIndices_of_isTerminalAt hu hρ ht
  refine ⟨ρ, hβρ, hρ, e, hWV, ht, hb, fun _ u hu' ↦ ?_⟩
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp (e.isSome_eval hu')
  exact ⟨Q, hQ, isNiceTupleAt_of_boundsServingIndices hb e hQ⟩

/-- **Niceness from terminal refinement**, conditional on `HasMaximalRefinement` and
`Expansion.NextBlockUniqueness`, both still to be proved: a base structure on a countable carrier
with a lift at some block stage is nice. -/
theorem isNice_of_hasMaximalRefinement (hmax : HasMaximalRefinement.{w})
    (hu : Expansion.NextBlockUniqueness.{w}) {β : Ordinal.{0}}
    (V : ModelExpansion M (blockStage β)) : IsNice M := by
  obtain ⟨ρ, -, hρ, e, -, -, hb, -⟩ := exists_isNiceTupleAt_of_hasMaximalRefinement hmax hu V
  exact isNice_of_boundsServingIndices hρ hb e

end Refinement

/-- **Condition (c) of the system** [AFK26, Definition 2.22, clause (c)], conditional on
`HasMaximalRefinement` and `Expansion.NextBlockUniqueness`, both still to be proved: the base
reduct of every model at a block stage on a countable carrier is nice. -/
theorem Realization.IsModel.isNice_toStructure_reduce (hmax : HasMaximalRefinement.{w})
    (hu : Expansion.NextBlockUniqueness.{w}) {M : Type w} [Countable M] {β : Ordinal.{0}}
    {V : Realization.{0, w} (blockStage β) M} (hV : V.IsModel) :
    @IsNice M (V.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure :=
  letI := (V.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure
  isNice_of_hasMaximalRefinement hmax hu ⟨V, hV, rfl⟩

end VaughtConjecture
