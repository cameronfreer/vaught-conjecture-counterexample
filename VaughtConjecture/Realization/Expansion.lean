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
(`blockStage_strictMono`), and they are countable at countable indices
(`blockStage_lt_omega_one`).  The stage `λ_ξ` is a permitted cutoff at the stage `λ_{ξ+1}`
(`isPermittedCutoff_blockStage`).

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
between block stages this is `ModelExpansion.reduceBlock`.

**Covers.**  A tuple `c : Fin k → M` **covers** a stage type `t` in `R` (`Realization.Covers`)
when it is injective and `R` evaluates it to `t`: `c` enumerates an actual occurrence of `t`.
Covers survive stage reduction, by the same tuple (`Realization.Covers.reduce`), and an injective
tuple covers exactly its evaluation (`Realization.covers_iff_eval`).  A tuple `c` **extends to a
cover** of a triple `(m, q, f)` — a stage type `q` on `m` points and an embedding
`f : Fin k ↪ Fin m` of coordinates — in `S` (`Realization.ExtendsToCover`) when some tuple `s`
covering `q` in `S` restricts along `f` to `c`.  The base
relations of an expansion are read from its covers through the base-reduct equation
(`Realization.IsExpansionOf.relMap_comp_iff`), so two covers of one stage type, in expansions of
two base structures at any common stage, have the same atomic type in the base language
(`Realization.Covers.sameAtomicType`): the atomic diagram of a cover is determined by its type.
Every expansion has a cover of a stage type on no points
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

end ModelExpansion

/-! ### Received types after reduction -/

/-- **The cutoff observation at `β` determines the stage reduction to `β`**: a member of the
receiving family of `D` at the cutoff `β` has the same stage reduction to `β` as `D`. -/
theorem StageType.reduce_eq_of_mem_receivingFamily {α β : Ordinal.{u}} {n : ℕ}
    {D q : StageType.{u} α n} (hβ : Order.IsSuccPrelimit β)
    (hq : q ∈ StageType.receivingFamily D (β : Label.{u})) : q.reduce hβ = D.reduce hβ :=
  StageType.ext hq.1 fun i j hij ↦ Label.min_eq_min_iff_reduce_eq.mp (hq.2 i j hij)

end VaughtConjecture
