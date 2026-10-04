/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.AtomicDiagram
import Mathlib.Data.Fin.VecNotation
import VaughtConjecture.Language.Structure

/-!
# Model expansions of base structures and their covers

Roadmap, Layer 2 (reduction of models; the realization/structure correspondence) and the
reduction of the main theorem to expansion domains ("Condition 3 from back-and-forth": model
expansions to the stages `λ_ξ`, charts, and covers); semantic contract, items 4, 9 and 12.

**Block stages.**  The **block stage** of index `ξ` is `λ_ξ = ω + ω · ξ` (`blockStage`): the stage
at which the block `[λ_ξ, λ_ξ + ω)` begins.  So `λ_0 = ω` is the base stage (`blockStage_zero`),
`λ_{ξ+1} = λ_ξ + ω` (`blockStage_add_one`), every block stage is a limit (`isSuccLimit_blockStage`)
at least `ω` (`omega0_le_blockStage`), block stages are strictly increasing
(`blockStage_strictMono`) and at least their index (`le_blockStage`), and they are countable at
countable indices (`blockStage_lt_omega_one`).  The stage `λ_ξ` is a permitted cutoff at the
stage `λ_{ξ+1}` (`isPermittedCutoff_blockStage`).

**Model expansions.**  A realization `R` at stage `α` on the carrier of a base structure `M` (a
structure of `baseLanguage`) is an **expansion** of `M` (`Realization.IsExpansionOf`) when it is a
model whose stage reduction to `ω` has `M` as its structure: the literal equation of structures
on the same carrier, `(R.reduce _).toStructure = ‹_›`.  `ModelExpansion M α` is the type of these
expansions.  The definition is meant for stages `α ≥ ω`, where the reduction to `ω` is the base
reduct; below `ω` the reduction to `ω` only reads a type at the larger stage `ω`
(`StageType.reduce_eq_castLE`).  Neither uniqueness of the expansion at a stage nor coherence of
the expansions at different stages (output 4 of higher-stage reconstruction) is assumed or used:
any expansion is allowed, and two expansions of one base structure at one stage are different
elements.  The stage reduction of an expansion at a stage that is zero or a limit to a limit stage
`ω ≤ β ≤ α` is an expansion (`ModelExpansion.reduce`), by the reduction of models
(`IsModel.reduce`) and the composition law of stage reduction (`Realization.reduce_reduce`);
between block stages this is `ModelExpansion.reduceBlock`.  A model expansion transports along an
isomorphism of base structures, possibly on carriers in different universes
(`ModelExpansion.map`): the transported realization is a model, and its base reduct is the
structure induced by the isomorphism, which is the target structure
(`FirstOrder.Language.Equiv.inducedStructure_eq`).  At the base stage `ω` an expansion is the
realization of its base structure (`ModelExpansion.val_eq_toRealization`), so there is at most one
(`ModelExpansion.instSubsingletonOmega`), and a type assignment has one exactly when its
realization is a model (`ModelExpansion.nonempty_omega_iff`); uniqueness at higher stages is not
proved here.

**Countable stages.**  A model on a countable carrier has a countable stage
(`Realization.IsModel.lt_omega_one`): over one occurrence, the uniformity clause at each block
stage `λ_ζ` with `ζ < ω₁` gives a label in the block `[λ_ζ, λ_ζ + ω)`; the blocks are disjoint,
and the labels of a realization on a countable carrier are countably many
(`Realization.countable_setOf_label`).  So a base structure on a countable carrier has no model
expansion to a stage `α ≥ ω₁` (`ModelExpansion.isEmpty_of_omega_one_le`).

**Covers.**  A tuple `c : Fin k → M` **covers** a stage type `t` in `R` (`Realization.Covers`)
when it is injective and `R` evaluates it to `t`: `c` enumerates an actual occurrence of `t`.
Covers survive stage reduction, by the same tuple (`Realization.Covers.reduce`), the covers in a
transport along a bijection of carriers are the transports of covers (`Realization.covers_map_iff`),
and an injective tuple covers exactly its evaluation (`Realization.covers_iff_eval`).  A tuple `c`
**extends to a cover** of a triple `(m, q, f)` — a stage type `q` on `m` points and an embedding
`f : Fin k ↪ Fin m` of coordinates — in `S` (`Realization.ExtendsToCover`) when some tuple `s`
covering `q` in `S` restricts along `f` to `c`.  The base relations of an expansion are read from
its covers through the base-reduct equation (`Realization.IsExpansionOf.relMap_comp_iff`), so two
covers of one stage type, in expansions of two base structures at any common stage, have the same
atomic type in the base language (`Realization.Covers.sameAtomicType`): the atomic diagram of a
cover is determined by its type.  Every expansion has a cover of a stage type on no points
(`ModelExpansion.exists_covers_zero`), since the empty face of every occurrence is closed.

**Received types after reduction.**  A member `q` of the receiving family of `D` at the cutoff
`β` has the same stage reduction to `β` as `D` (`StageType.reduce_eq_of_mem_receivingFamily`):
the cutoff observation at `β` determines the stage reduction to `β`, since capping at `β` and
reduction to `β` have the same equality kernel (`Label.min_eq_min_iff_reduce_eq`).  This is the
only passage from a cutoff observation to a stage reduction used here; it concerns one received
type at a time, and it is not exact projected receiving (semantic contract, item 12).

## Placement

This file belongs to Layer 2 of `roadmap/README.md`.
-/

universe u v w

namespace VaughtConjecture

open Ordinal FirstOrder Language Structure baseLanguage

/-! ### Block stages -/

/-- The **block stage** `λ_ξ = ω + ω · ξ` of index `ξ`: the stage at which the block
`[λ_ξ, λ_ξ + ω)` begins. -/
def blockStage (ξ : Ordinal.{u}) : Ordinal.{u} :=
  ω + ω * ξ

/-- The block stage of index `0` is the base stage `ω`. -/
@[simp] theorem blockStage_zero : blockStage (0 : Ordinal.{u}) = ω := by
  simp [blockStage]

/-- The next block stage is one block higher: `λ_{ξ+1} = λ_ξ + ω`. -/
theorem blockStage_add_one (ξ : Ordinal.{u}) : blockStage (ξ + 1) = blockStage ξ + ω := by
  rw [blockStage, blockStage, mul_add_one, add_assoc]

/-- The block stage is `ω · (1 + ξ)`. -/
theorem blockStage_eq_mul (ξ : Ordinal.{u}) : blockStage ξ = ω * (1 + ξ) := by
  rw [blockStage, mul_add, mul_one]

/-- Every block stage is a limit. -/
theorem isSuccLimit_blockStage (ξ : Ordinal.{u}) : Order.IsSuccLimit (blockStage ξ) := by
  rw [blockStage_eq_mul]
  exact isSuccLimit_mul_left isSuccLimit_omega0 (lt_of_lt_of_le zero_lt_one (le_self_add))

/-- Every block stage is zero or a limit. -/
theorem isSuccPrelimit_blockStage (ξ : Ordinal.{u}) : Order.IsSuccPrelimit (blockStage ξ) :=
  (isSuccLimit_blockStage ξ).isSuccPrelimit

/-- Every block stage is at least the base stage `ω`. -/
theorem omega0_le_blockStage (ξ : Ordinal.{u}) : ω ≤ blockStage ξ :=
  le_self_add

/-- Block stages are strictly increasing. -/
theorem blockStage_strictMono : StrictMono (blockStage : Ordinal.{u} → Ordinal.{u}) :=
  fun _ _ h ↦ add_lt_add_right (mul_lt_mul_iff_right₀ omega0_pos |>.mpr h) _

/-- Block stages are monotone. -/
theorem blockStage_mono : Monotone (blockStage : Ordinal.{u} → Ordinal.{u}) :=
  blockStage_strictMono.monotone

/-- A block stage is below the next one. -/
theorem blockStage_lt_blockStage_add_one (ξ : Ordinal.{u}) :
    blockStage ξ < blockStage (ξ + 1) :=
  blockStage_strictMono (Order.lt_add_one_iff.mpr le_rfl)

/-- The index of a block stage is at most the block stage: `ξ ≤ ω · ξ ≤ ω + ω · ξ`. -/
theorem le_blockStage (ξ : Ordinal.{u}) : ξ ≤ blockStage ξ :=
  (le_mul_right ξ omega0_pos).trans le_add_self

/-- The block stage of a countable index is countable. -/
theorem blockStage_lt_omega_one {ξ : Ordinal.{u}} (hξ : ξ < ω₁) : blockStage ξ < ω₁ :=
  isPrincipal_add_omega 1 omega0_lt_omega_one
    (isPrincipal_mul_omega 1 omega0_lt_omega_one hξ)

/-- The block stage `λ_ξ` is a permitted cutoff at the next block stage `λ_{ξ+1}`. -/
theorem isPermittedCutoff_blockStage (ξ : Ordinal.{u}) :
    Label.IsPermittedCutoff (blockStage (ξ + 1)) (blockStage ξ : Label.{u}) :=
  Label.isPermittedCutoff_coe.mpr (blockStage_lt_blockStage_add_one ξ)

namespace Realization

/-! ### Expansions of a base structure -/

section Expansion

variable {α β : Ordinal.{u}} {M : Type v} {N : Type w}

/-- A realization `R` at stage `α` on the carrier of a base structure `M` is an **expansion** of
`M` when it is a model whose stage reduction to `ω` has `M` as its structure.  It is meaningful
only for `ω ≤ α`, where the reduction to `ω` is the base reduct. -/
structure IsExpansionOf [baseLanguage.{u}.Structure M] (R : Realization.{u, v} α M) : Prop where
  /-- The realization is a model. -/
  isModel : R.IsModel
  /-- The base reduct: the structure of the reduction to `ω` is the base structure. -/
  toStructure_reduce : (R.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure = ‹_›

/-- A tuple `c` **covers** the stage type `t` in `R` when it is injective and `R` evaluates it to
`t`: `c` enumerates an actual occurrence of `t`. -/
def Covers (R : Realization.{u, v} α M) {k : ℕ} (t : StageType.{u} α k) (c : Fin k → M) : Prop :=
  ∃ h : Function.Injective c, R.eval ⟨c, h⟩ = some t

variable {R : Realization.{u, v} α M} {k : ℕ} {t : StageType.{u} α k} {c : Fin k → M}

/-- An injective tuple covers its type. -/
theorem covers_of_eval (u : Fin k ↪ M) (h : R.eval u = some t) : R.Covers t u :=
  ⟨u.injective, h⟩

/-- A cover is injective. -/
theorem Covers.injective (h : R.Covers t c) : Function.Injective c :=
  h.1

/-- The evaluation of a cover is its type. -/
theorem Covers.eval_eq (h : R.Covers t c) : R.eval ⟨c, h.injective⟩ = some t :=
  h.2

/-- **Covers survive stage reduction**, by the same tuple. -/
theorem Covers.reduce (h : R.Covers t c) (hβ : Order.IsSuccPrelimit β) :
    (R.reduce hβ).Covers (t.reduce hβ) c :=
  ⟨h.1, by rw [reduce_eval, h.2, Option.map_some]⟩

/-- Covers in a transport are the transports of covers. -/
theorem covers_map_iff (e : M ≃ N) {n : ℕ} {t : StageType.{u} α n} {c : Fin n → N} :
    (R.map e).Covers t c ↔ R.Covers t (e.symm ∘ c) := by
  refine ⟨fun ⟨hc, h⟩ ↦ ⟨e.symm.injective.comp hc, h⟩, fun ⟨hc, h⟩ ↦ ⟨?_, h⟩⟩
  exact (Function.Injective.of_comp (f := e.symm) hc)

/-- An injective tuple covers a stage type exactly when it is evaluated to it. -/
theorem covers_iff_eval (u : Fin k ↪ M) : R.Covers t u ↔ R.eval u = some t :=
  ⟨fun h ↦ h.eval_eq, covers_of_eval u⟩

/-- A tuple `c` **extends to a cover** of a triple `(m, q, f)` in `S` when some tuple `s` covering
`q` in `S` restricts along `f` to `c`. -/
def ExtendsToCover (S : Realization.{u, v} α M) (c : Fin k → M)
    (x : Σ m : ℕ, StageType.{u} α m × (Fin k ↪ Fin m)) : Prop :=
  ∃ s : Fin x.1 → M, s ∘ x.2.2 = c ∧ S.Covers x.2.1 s

/-- **The faces of a cover**: under exact consistency, the face of a cover along an injective
selection `s` of coordinates is evaluated to the face of its type along `s`. -/
theorem Covers.eval_comp (hR : R.IsConsistent) (h : R.Covers t c) {m : ℕ} {s : Fin m → Fin k}
    (hs : Function.Injective s) :
    R.eval ⟨c ∘ s, h.injective.comp hs⟩ = StageType.restrictFace ⟨s, hs⟩ t :=
  hR ⟨c, h.injective⟩ t ⟨s, hs⟩ h.eval_eq

/-- **The base relations of an expansion, read from a cover**: in an expansion `R` of `M`, a
relation `P` holds of a selection `c ∘ s` of the coordinates of a cover `c` of `t` exactly when `s`
is injective and the face of `t` along `s`, reduced to `ω`, is the stage type of `P`. -/
theorem IsExpansionOf.relMap_comp_iff [baseLanguage.{u}.Structure M] (hR : R.IsExpansionOf)
    (h : R.Covers t c) {l : ℕ} (P : baseLanguage.{u}.Relations l) (s : Fin l → Fin k) :
    RelMap P (c ∘ s) ↔ ∃ hs : Function.Injective s,
      (StageType.restrictFace ⟨s, hs⟩ t).map
        (StageType.reduce · isSuccLimit_omega0.isSuccPrelimit) = some (type P) := by
  obtain ⟨hmod, hstr⟩ := hR
  subst hstr
  rw [relMap_toStructure]
  constructor
  · rintro ⟨hcs, he⟩
    have hs : Function.Injective s := Function.Injective.of_comp hcs
    refine ⟨hs, ?_⟩
    rw [reduce_eval, h.eval_comp hmod.isConsistent hs] at he
    exact he
  · rintro ⟨hs, he⟩
    refine ⟨h.injective.comp hs, ?_⟩
    rw [reduce_eval, h.eval_comp hmod.isConsistent hs]
    exact he

/-- **Atomic agreement of covers**: two covers of one stage type, in expansions of two base
structures at a common stage, have the same atomic type in the base language.  Equalities agree
because both covers are injective; a relation holds of a selection of coordinates in either
structure exactly when the reduction to `ω` of the face of the common type along the selection is
the stage type of the relation (`IsExpansionOf.relMap_comp_iff`). -/
theorem Covers.sameAtomicType [baseLanguage.{u}.Structure M] [baseLanguage.{u}.Structure N]
    {S : Realization.{u, w} α N} {d : Fin k → N} (hR : R.IsExpansionOf) (hS : S.IsExpansionOf)
    (hc : R.Covers t c) (hd : S.Covers t d) : SameAtomicType (L := baseLanguage.{u}) c d := by
  intro idx
  cases idx with
  | eq i j => exact hc.injective.eq_iff.trans hd.injective.eq_iff.symm
  | rel P s => exact (hR.relMap_comp_iff hc P s).trans (hS.relMap_comp_iff hd P s).symm

end Expansion

end Realization

/-! ### The type of model expansions -/

section ModelExpansion

variable (M : Type v) [baseLanguage.{u}.Structure M]

/-- The **model expansions** of a base structure `M` to the stage `α`: the realizations at `α` on
the carrier of `M` that are expansions of `M`.  No uniqueness is imposed. -/
abbrev ModelExpansion (α : Ordinal.{u}) : Type (max (u + 1) v) :=
  {R : Realization.{u, v} α M // R.IsExpansionOf}

variable {M} {α β : Ordinal.{u}}

/-- **Reduction of a model expansion**: the stage reduction of an expansion at a stage `α` that is
zero or a limit to a limit stage `β` with `ω ≤ β ≤ α` is an expansion at `β`. -/
noncomputable def ModelExpansion.reduce (e : ModelExpansion M α) (hα : Order.IsSuccPrelimit α)
    (hβ : Order.IsSuccLimit β) (hωβ : ω ≤ β) (hβα : β ≤ α) : ModelExpansion M β :=
  ⟨e.1.reduce hβ.isSuccPrelimit, e.2.isModel.reduce hα hβ hβα, by
    rw [Realization.reduce_reduce _ _ _ hωβ]
    exact e.2.toStructure_reduce⟩

/-- The realization of a reduced expansion is the stage reduction. -/
@[simp] theorem ModelExpansion.reduce_val (e : ModelExpansion M α) (hα : Order.IsSuccPrelimit α)
    (hβ : Order.IsSuccLimit β) (hωβ : ω ≤ β) (hβα : β ≤ α) :
    (e.reduce hα hβ hωβ hβα).1 = e.1.reduce hβ.isSuccPrelimit :=
  rfl

/-- **Reduction of a model expansion between block stages**: for `β ≤ ξ`, the stage reduction of
an expansion at `λ_ξ` to `λ_β`. -/
noncomputable def ModelExpansion.reduceBlock {ξ β : Ordinal.{u}}
    (e : ModelExpansion M (blockStage ξ)) (h : β ≤ ξ) : ModelExpansion M (blockStage β) :=
  e.reduce (isSuccPrelimit_blockStage ξ) (isSuccLimit_blockStage β) (omega0_le_blockStage β)
    (blockStage_mono h)

/-- The realization of an expansion reduced between block stages is the stage reduction. -/
@[simp] theorem ModelExpansion.reduceBlock_val {ξ β : Ordinal.{u}}
    (e : ModelExpansion M (blockStage ξ)) (h : β ≤ ξ) :
    (e.reduceBlock h).1 = e.1.reduce (isSuccPrelimit_blockStage β) :=
  rfl

/-- **Transport of a model expansion** along an isomorphism `e : M ≃[baseLanguage] N` of base
structures: the transport of the realization along the underlying bijection is a model
(`IsModel.map`), and its base reduct is the structure induced by `e`, which is the structure of
`N` (`FirstOrder.Language.Equiv.inducedStructure_eq`).  The carriers may lie in different
universes. -/
def ModelExpansion.map {N : Type w} [baseLanguage.{u}.Structure N]
    (f : ModelExpansion M α) (e : M ≃[baseLanguage.{u}] N) : ModelExpansion N α :=
  ⟨f.1.map (e : M ≃ N), f.2.isModel.map _, by
    rw [Realization.reduce_map, Realization.toStructure_map, f.2.toStructure_reduce,
      e.inducedStructure_eq]⟩

/-- The realization of a transported expansion is the transported realization. -/
@[simp] theorem ModelExpansion.map_val {N : Type w} [baseLanguage.{u}.Structure N]
    (f : ModelExpansion M α) (e : M ≃[baseLanguage.{u}] N) : (f.map e).1 = f.1.map (e : M ≃ N) :=
  rfl

/-- Transport along the identity isomorphism is the identity. -/
@[simp] theorem ModelExpansion.map_refl (f : ModelExpansion M α) :
    f.map (Language.Equiv.refl baseLanguage.{u} M) = f :=
  Subtype.ext (Realization.map_refl f.1)

/-- Transport along an isomorphism and then along its inverse is the identity. -/
@[simp] theorem ModelExpansion.map_symm_map {N : Type w} [baseLanguage.{u}.Structure N]
    (f : ModelExpansion M α) (e : M ≃[baseLanguage.{u}] N) : (f.map e).map e.symm = f :=
  Subtype.ext (Realization.map_symm_map f.1 (e : M ≃ N))

/-- **An expansion has a cover of a stage type on no points**: the empty face of any occurrence
is closed. -/
theorem ModelExpansion.exists_covers_zero (e : ModelExpansion M α) :
    ∃ t : StageType.{u} α 0, e.1.Covers t ![] := by
  obtain ⟨x⟩ := e.2.isModel.nonempty_occurrence
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (x.type.isSome_restrictFace_of_zero Function.Embedding.ofIsEmpty)
  refine ⟨t, fun i ↦ i.elim0, ?_⟩
  rw [← ht, ← Realization.eval_face e.2.isModel.isConsistent x]
  congr 1
  ext i
  exact i.elim0

/-! ### Model expansions at the base stage -/

/-- **An expansion at the base stage is the realization of the base structure**: its reduction
to `ω` is itself, so its structure is the base structure, and a realization with legal types is
the realization of its structure (`baseLanguage.toRealization_toStructure`). -/
theorem ModelExpansion.val_eq_toRealization (e : ModelExpansion M (ω : Ordinal.{u})) :
    e.1 = toRealization M := by
  obtain ⟨R, hR⟩ := e
  have h := hR.toStructure_reduce
  rw [Realization.reduce_self] at h
  -- the realization of `⟨R, hR⟩` is `R`; unfold the subtype projection before rewriting the
  -- base structure, which also occurs in the type of `hR`
  change R = toRealization M
  rw [← h]
  exact (toRealization_toStructure hR.isModel.hasLegalTypes).symm

/-- **At most one model expansion at the base stage.** -/
instance ModelExpansion.instSubsingletonOmega :
    Subsingleton (ModelExpansion M (ω : Ordinal.{u})) :=
  ⟨fun e e' ↦ Subtype.ext (e.val_eq_toRealization.trans e'.val_eq_toRealization.symm)⟩

/-- **Model expansions at the base stage**: a type assignment has a model expansion to `ω`
exactly when its realization is a model; the expansion is then that realization. -/
theorem ModelExpansion.nonempty_omega_iff (hT : IsTypeAssignment M) :
    Nonempty (ModelExpansion M (ω : Ordinal.{u})) ↔ (toRealization M).IsModel :=
  ⟨fun ⟨e⟩ ↦ e.val_eq_toRealization ▸ e.2.isModel, fun h ↦
    ⟨⟨toRealization M, h, by rw [Realization.reduce_self]; exact toStructure_toRealization hT⟩⟩⟩

end ModelExpansion

/-! ### Countable carriers have countable stages -/

namespace Realization

variable {α : Ordinal.{u}} {M : Type v}

/-- The labels of a realization on a countable carrier are countably many: each of the countably
many injective tuples has at most one type, with finitely many cells. -/
theorem countable_setOf_label [Countable M] (R : Realization.{u, v} α M) :
    {ℓ : Label.{u} | ∃ (n : ℕ) (t : Fin n ↪ M) (p : StageType.{u} α n) (d : Fin p.card),
      R.eval t = some p ∧ p.label d = ℓ}.Countable := by
  have h : {ℓ : Label.{u} | ∃ (n : ℕ) (t : Fin n ↪ M) (p : StageType.{u} α n) (d : Fin p.card),
      R.eval t = some p ∧ p.label d = ℓ} = ⋃ (n : ℕ) (t : Fin n ↪ M),
        {ℓ | ∃ (p : StageType.{u} α n) (d : Fin p.card), R.eval t = some p ∧ p.label d = ℓ} := by
    ext
    simp
  have (n : ℕ) : Countable (Fin n ↪ M) :=
    Function.Injective.countable (DFunLike.coe_injective (F := Fin n ↪ M))
  rw [h]
  refine Set.countable_iUnion fun n ↦ Set.countable_iUnion fun t ↦ ?_
  cases ht : R.eval t with
  | none => simp
  | some p =>
    refine (Set.finite_range p.label).countable.mono ?_
    rintro ℓ ⟨q, d, hq, rfl⟩
    cases hq
    exact ⟨d, rfl⟩

/-- A label in `[λ_ζ, λ_ζ + ω)` that is below `λ_ζ' + ω` has `ζ ≤ ζ'`: the blocks of distinct
block stages are disjoint. -/
theorem le_of_coe_blockStage_le_of_lt {ζ ζ' : Ordinal.{u}} {ℓ : Label.{u}}
    (h : (blockStage ζ : Label.{u}) ≤ ℓ)
    (h' : ℓ < ((blockStage ζ' + ω : Ordinal.{u}) : Label.{u})) : ζ ≤ ζ' := by
  rw [← blockStage_add_one] at h'
  have : blockStage ζ < blockStage (ζ' + 1) := by exact_mod_cast h.trans_lt h'
  exact Order.lt_add_one_iff.mp (blockStage_strictMono.lt_iff_lt.mp this)

/-- **A model on a countable carrier has a countable stage.**  Otherwise, over a fixed
occurrence, the uniformity clause at each block stage `λ_ζ` with `ζ < ω₁` gives a label in the
block `[λ_ζ, λ_ζ + ω)`; the blocks are disjoint, so these are `ℵ₁` many distinct labels of the
realization, which has only countably many (`countable_setOf_label`). -/
theorem IsModel.lt_omega_one [Countable M] {R : Realization.{u, v} α M} (hR : R.IsModel) :
    α < ω₁ := by
  classical
  by_contra hα
  push Not at hα
  obtain ⟨x⟩ := hR.nonempty_occurrence
  have hu (ζ : Set.Iio (ω₁ : Ordinal.{u})) := hR.uniformity x (blockStage ζ.1)
    (isSuccPrelimit_blockStage _) ((blockStage_lt_omega_one ζ.2).trans_le hα)
  choose t _ q hq hqe using hu
  choose d hd using hq
  let f : Ordinal.{u} → Label.{u} := fun ζ ↦
    if h : ζ < ω₁ then (q ⟨ζ, h⟩).label (d ⟨ζ, h⟩) else ⊥
  have hcount : (Set.Iio (ω₁ : Ordinal.{u})).Countable := by
    refine Set.MapsTo.countable_of_injOn (f := f) ?_ ?_ (countable_setOf_label R)
    · intro ζ hζ
      simp only [f, show ζ < ω₁ from hζ, ↓reduceDIte]
      exact ⟨_, _, _, _, hqe _, rfl⟩
    · intro ζ hζ ζ' hζ' h
      simp only [f, show ζ < ω₁ from hζ, show ζ' < ω₁ from hζ', ↓reduceDIte] at h
      have h1 := hd ⟨ζ, hζ⟩
      have h2 := hd ⟨ζ', hζ'⟩
      rw [h] at h1
      exact le_antisymm (le_of_coe_blockStage_le_of_lt h1.1 h2.2)
        (le_of_coe_blockStage_le_of_lt h2.1 h1.2)
  have := Cardinal.le_aleph0_iff_set_countable.mpr hcount
  rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega, Cardinal.lift_aleph] at this
  simp at this

end Realization

/-- **No model expansions at uncountable stages on countable carriers**: a model on a countable
carrier has a countable stage (`Realization.IsModel.lt_omega_one`). -/
theorem ModelExpansion.isEmpty_of_omega_one_le {M : Type v} [baseLanguage.{u}.Structure M]
    [Countable M] {α : Ordinal.{u}} (h : ω₁ ≤ α) : IsEmpty (ModelExpansion M α) :=
  ⟨fun e ↦ (e.2.isModel.lt_omega_one.trans_le h).false⟩

/-! ### Received types after reduction -/

/-- **The cutoff observation at `β` determines the stage reduction to `β`**: a member of the
receiving family of `D` at the cutoff `β` has the same stage reduction to `β` as `D`. -/
theorem StageType.reduce_eq_of_mem_receivingFamily {α β : Ordinal.{u}} {n : ℕ}
    {D q : StageType.{u} α n} (hβ : Order.IsSuccPrelimit β)
    (hq : q ∈ StageType.receivingFamily D (β : Label.{u})) : q.reduce hβ = D.reduce hβ :=
  StageType.ext hq.1 fun i j hij ↦ Label.min_eq_min_iff_reduce_eq.mp (hq.2 i j hij)

end VaughtConjecture
