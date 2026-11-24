/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Comparison
import VaughtConjecture.ProcessRank.SpanTargets

/-!
# The direct comparison through a span of mutual rigidity, and the catalogue of top patterns

Process rank `ω₁`, the classes with a globally rigid core.

**The direct comparison** (`Realization.nonempty_potentialIso_of_isMutualRigidSpan`).  Let `R`
and `R'` be expansions at a limit stage with finite-cut receiving, with globally rigid cores `x₀`
of type `p` and `y₀` of type `q`, and let `D` be a span of mutual rigidity of `p` and `q`
(`StageType.IsMutualRigidSpan`, a premise here).  Exact receiving at a rigid core
(`Realization.exists_covers_of_isRigidCoreIn`, with finite-extension receiving from finite-cut
receiving, `Realization.IsModel.hasFiniteExtensionReceiving_iff`) gives covers `u` of `D` over `x₀`
and `v` of `D` over `y₀`; each is a globally rigid core, since it contains the injective globally
rigid core below it (`Realization.IsGloballyRigidCore.mono`).  The rooted comparison at the common
type `D` (`Realization.rootedPotentialIso`, in the pointed age of a rigid core,
`StageType.rigidCoreAge`) is a potential isomorphism of the base structures.  No countability of
the carriers is assumed.  Proved, with the span as a premise.

**The catalogue** (`StageType.countable_range_schemeTopPattern`).  The scheme and the set of top
cells of a stage type (`StageType.schemeTopPattern`) range over a countable set at every stage: a
scheme is finite data with coded rows, and a set of cells is finite.  Proved.

**The count** (`Realization.CountableCoreClassesTarget`): any family of expansions at a limit
stage with finite-cut receiving, each with a globally rigid core, has a countable subfamily that
represents every member up to potential isomorphism.  It is to follow from the catalogue and the
direct comparison, given spans of mutual rigidity (`StageType.ExistsMutualRigidSpanTarget`), by
choosing one member for each scheme and top pattern of a core.  Stated.
-/

universe u v w w'

namespace VaughtConjecture

open Finset Label FirstOrder Language

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

/-- The **scheme and top pattern** of a stage type: its scheme and the set of its top cells. -/
def schemeTopPattern (t : StageType.{u} α n) : Σ S : Scheme.{u} n, Set (Fin S.card) :=
  ⟨t.toScheme, {d | t.label d = ⊤}⟩

variable (α n) in
/-- **The catalogue of schemes and top patterns is countable**, at every stage: the cell scheme
is finite data, the rows are coded (`Label.countable_setOf_lt_omega0_sq`), and a set of cells is
finite. -/
theorem countable_range_schemeTopPattern :
    (Set.range (schemeTopPattern : StageType.{u} α n → _)).Countable := by
  let V := {x : Label.{u} | x < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})}
  have : Countable V := Label.countable_setOf_lt_omega0_sq.to_subtype
  let F : (Σ k : ℕ, Σ D : CellScheme (Fin k) (Fin n),
      ((s : Fin k) → D.below (D.gradedIndex s) → V) × Set (Fin k)) →
        Σ S : Scheme.{u} n, Set (Fin S.card) :=
    fun x ↦ ⟨⟨x.1, x.2.1, ⟨fun s d ↦ (x.2.2.1 s d : Label.{u})⟩⟩, x.2.2.2⟩
  refine (Set.countable_range F).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨⟨t.card, t.toCellScheme, fun s d ↦ ⟨t.rows.row s d, t.isCoded s d⟩,
    {d | t.label d = ⊤}⟩, rfl⟩

end StageType

namespace Realization

variable {α : Ordinal.{u}} {n : ℕ} {M : Type v} {N : Type w} [baseLanguage.{u}.Structure M]
  [baseLanguage.{u}.Structure N] {R : Realization.{u, v} α M} {R' : Realization.{u, w} α N}

/-- **Receiving a span over a globally rigid core**: in an expansion at a limit stage with
finite-cut receiving, over a globally rigid core `x₀` of type `p`, a legal `D` with face `p` along
`i` in which the core along `i` is rigid is covered by a tuple `u` with `u ∘ i = x₀`, and `u` is a
globally rigid core. -/
theorem exists_covers_isGloballyRigidCore_of_isRigidCoreIn (hα : Order.IsSuccLimit α)
    (he : R.IsExpansionOf) (hrec : R.HasFiniteCutReceiving) {p : StageType.{u} α n}
    {x₀ : Fin n → M} (hx : R.Covers p x₀) (hcx : R.IsGloballyRigidCore x₀) {m : ℕ}
    {D : StageType.{u} α m} {i : Fin n ↪ Fin m} (hD : D.IsLegal)
    (hi : StageType.restrictFace i D = some p) (hri : D.IsRigidCoreIn i) :
    ∃ u : Fin m → M, R.Covers D u ∧ u ∘ i = x₀ ∧ R.IsGloballyRigidCore u := by
  have hext := (he.isModel.hasFiniteExtensionReceiving_iff hα.isSuccPrelimit).mpr hrec
  obtain ⟨u, hu, hui⟩ := exists_covers_of_isRigidCoreIn he.isModel.isConsistent hα hext hx hD hi hri
  refine ⟨u, hu, hui, hcx.mono hx.injective ?_⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨i k, congrFun hui k⟩

/-- **The direct comparison through a span of mutual rigidity**: two expansions at a limit stage
with finite-cut receiving, with globally rigid cores of types `p` and `q`, have potentially
isomorphic base structures, given a span of mutual rigidity of `p` and `q`.  Both expansions
receive the span over their cores, and the rooted comparison starts at the two covers of the span.
Proved, with the span as a premise. -/
theorem nonempty_potentialIso_of_isMutualRigidSpan (hα : Order.IsSuccLimit α)
    (he : R.IsExpansionOf) (he' : R'.IsExpansionOf) (hrec : R.HasFiniteCutReceiving)
    (hrec' : R'.HasFiniteCutReceiving) {p q : StageType.{u} α n} {x₀ : Fin n → M}
    {y₀ : Fin n → N} (hx : R.Covers p x₀) (hy : R'.Covers q y₀) (hcx : R.IsGloballyRigidCore x₀)
    (hcy : R'.IsGloballyRigidCore y₀) {m : ℕ} {D : StageType.{u} α m} {i j : Fin n ↪ Fin m}
    (hD : StageType.IsMutualRigidSpan p q D i j) :
    Nonempty (PotentialIso baseLanguage.{u} M N) := by
  obtain ⟨hDl, hi, hj, hri, hrj⟩ := hD
  obtain ⟨u, hu, -, hcu⟩ :=
    exists_covers_isGloballyRigidCore_of_isRigidCoreIn hα he hrec hx hcx hDl hi hri
  obtain ⟨v, hv, -, hcv⟩ :=
    exists_covers_isGloballyRigidCore_of_isRigidCoreIn hα he' hrec' hy hcy hDl hj hrj
  have hext := (he.isModel.hasFiniteExtensionReceiving_iff hα.isSuccPrelimit).mpr hrec
  have hext' := (he'.isModel.hasFiniteExtensionReceiving_iff hα.isSuccPrelimit).mpr hrec'
  exact ⟨rootedPotentialIso he he'
    (fun _ _ ι _ hs hsι ↦ hcu.mem_rigidCoreAge he.isModel hu ι hs hsι)
    (fun _ _ ι _ hs hsι ↦ hcv.mem_rigidCoreAge he'.isModel hv ι hs hsι)
    (exactReceivingWithinAt_rigidCoreAge he.isModel.isConsistent hα hext u D)
    (exactReceivingWithinAt_rigidCoreAge he'.isModel.isConsistent hα hext' v D) hu hv⟩

/-- **Target: countably many classes with a globally rigid core.**  At a limit stage, a family of
expansions with finite-cut receiving, each with a globally rigid core, has a countable subfamily
representing every member up to potential isomorphism of the base structures.  Stated. -/
def CountableCoreClassesTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄, Order.IsSuccLimit α → ∀ (ι : Type w') (M : ι → Type w)
    [∀ i, baseLanguage.{u}.Structure (M i)] (R : ∀ i, Realization.{u, w} α (M i)),
    (∀ i, (R i).IsExpansionOf) → (∀ i, (R i).HasFiniteCutReceiving) →
    (∀ i, ∃ (k : ℕ) (p : StageType.{u} α k) (c : Fin k → M i), (R i).Covers p c ∧
      (R i).IsGloballyRigidCore c) →
    ∃ J : Set ι, J.Countable ∧ ∀ i, ∃ j ∈ J, Nonempty (PotentialIso baseLanguage.{u} (M i) (M j))

end Realization

end VaughtConjecture
