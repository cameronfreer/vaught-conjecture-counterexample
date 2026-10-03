/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Limit

/-!
# Examples for gluing at a limit block stage

Special cases of `VaughtConjecture.Realization.Limit`, at the first limit index `ω`, whose block
stage is `λ_ω = ω + ω · ω`:

* continuity: an ordinal below `λ_ω` is below some `λ_n`;
* separation: two stage types, and two realizations, at `λ_ω` with the same reductions to every
  `λ_n` are equal;
* modelhood at `λ_ω` is modelhood of the reductions to every `λ_n`;
* the gluing identity: the glued expansion of a coherent family reduces to every member, and
  gluing the reductions of a model expansion at `λ_ω` returns it.

## Placement

This file belongs to Layer 2 of `roadmap/README.md`.
-/

namespace VaughtConjecture

open Ordinal FirstOrder Language

/-! ### Continuity and separation at `λ_ω` -/

/-- An ordinal below `λ_ω` is below some `λ_n` with `n < ω`. -/
example (o : Ordinal.{0}) : o < blockStage ω ↔ ∃ n < ω, o < blockStage n :=
  lt_blockStage_iff isSuccLimit_omega0

/-- Two stage types at `λ_ω` with the same reductions to every `λ_n` are equal. -/
example {k : ℕ} (t t' : StageType.{0} (blockStage ω) k)
    (h : ∀ n < ω,
      t.reduce (isSuccPrelimit_blockStage n) = t'.reduce (isSuccPrelimit_blockStage n)) :
    t = t' :=
  StageType.eq_of_forall_reduce_eq isSuccLimit_omega0 h

/-- Two realizations at `λ_ω` with the same reductions to every `λ_n` are equal. -/
example {M : Type} (R R' : Realization.{0, 0} (blockStage ω) M)
    (h : ∀ n < ω,
      R.reduce (isSuccPrelimit_blockStage n) = R'.reduce (isSuccPrelimit_blockStage n)) :
    R = R' :=
  Realization.eq_of_forall_reduce_eq isSuccLimit_omega0 h

/-- A realization at `λ_ω` is a model exactly when its reductions to every `λ_n` are. -/
example {M : Type} (R : Realization.{0, 0} (blockStage ω) M) :
    R.IsModel ↔ ∀ n < ω, (R.reduce (isSuccPrelimit_blockStage n)).IsModel :=
  Realization.isModel_iff_forall_reduce isSuccLimit_omega0

/-! ### The gluing identity -/

section Glue

variable {M : Type} [baseLanguage.{0}.Structure M] {δ : Ordinal.{0}}

/-- The glued expansion of a coherent family reduces to every member of the family. -/
example (hδ : Order.IsSuccLimit δ) (e : ∀ ξ < δ, ModelExpansion M (blockStage ξ))
    (hcoh : ∀ ζ (hζ : ζ < δ) ξ (hξ : ξ < δ) (h : ζ ≤ ξ), (e ξ hξ).reduceBlock h = e ζ hζ)
    {ξ : Ordinal.{0}} (hξ : ξ < δ) :
    (ModelExpansion.glue hδ e hcoh).reduceBlock hξ.le = e ξ hξ :=
  ModelExpansion.glue_reduceBlock hcoh hξ

/-- The reductions of a model expansion at `λ_δ` form a coherent family, and gluing them returns
the expansion. -/
example (hδ : Order.IsSuccLimit δ) (f : ModelExpansion M (blockStage δ)) :
    ModelExpansion.glue hδ (fun _ hξ ↦ f.reduceBlock hξ.le) (fun _ _ _ _ h ↦ Subtype.ext
      (Realization.reduce_reduce _ _ _ (blockStage_strictMono.le_iff_le.mpr h))) = f :=
  Subtype.ext (Realization.eq_of_forall_reduce_eq hδ fun _ hξ ↦
    congrArg Subtype.val (ModelExpansion.glue_reduceBlock _ hξ))

/-- A coherent family of model expansions below `ω` gives a model expansion to `λ_ω`. -/
example (e : ∀ n < ω, ModelExpansion M (blockStage n))
    (hcoh : ∀ m (hm : m < ω) n (hn : n < ω) (h : m ≤ n), (e n hn).reduceBlock h = e m hm) :
    Nonempty (ModelExpansion M (blockStage ω)) :=
  ModelExpansion.nonempty_of_coherent isSuccLimit_omega0 e hcoh

end Glue

end VaughtConjecture
