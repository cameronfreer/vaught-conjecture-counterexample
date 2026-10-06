/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CoupledGatedExtensionCounterexample
import VaughtConjecture.Realization.PrivateContext

/-!
# Carrying private contexts, for (R1) through a gate

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the private context) and 3.4, row (R1);
the bottom transport condition of `VaughtConjecture.Extension.CoupledGatedExtensionCounterexample`.

**Setting.**  The coupled gated pinned extension property
`StageType.HasCoupledGatedPinnedExtensions α` is false at every stage `α > 1`
(`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`): every coupled gated
extension forces the **bottom transport condition** `StageType.CarriesBottoms` for its private
type, its donor and the label of its cap (`StageType.CoupledGatedExtension.carriesBottoms`), and
the condition fails at a legal private type with a proper anchor below the cap.  A construction of
(R1) through a coupled gate needs a coupled gated extension at the private context it uses, hence
the condition there; so it needs models to acquire private contexts at which the condition holds.
That acquisition is stated here; the extension property restricted to such contexts, and
receiving from it, would come after it.  The condition is necessary for a coupled gated extension;
it is not shown sufficient.

**The predicate.**  Over an occurrence `x` of a realization `R` (the root), for a donor `d` on
`x.arity + 1` points and a floor `γ`, a **carrying private context**
(`Realization.HasCarryingPrivateContext x d γ`) is a private context in the form that
`IsModel.exists_privateContext_isAnchored` acquires (an occurrence `y` containing the root as a
literal face along `f`, of arity above `x.arity + 1`, with a cell `C` of graded index
`(univ, y.arity)` labelled above `γ`, below which `d` is anchored in the type of `y`) whose type
satisfies the bottom transport condition with `d` at the label of `C`.  A realization **acquires
carrying contexts** (`Realization.AcquiresCarryingContexts R`) when it has one over every
occurrence, for every coface of its type and every floor below the stage.  The private context is
acquired existentially, and the construction of (R1) uses one context per cutoff, so the predicate
asks for one carrying context, not that every acquired context carries.

**Status.**
* Stated: `Realization.HasCarryingPrivateContext`, `Realization.AcquiresCarryingContexts`.
* Compiled: a model has a carrying private context for every donor whose new cells are labelled
  `⊥` or `⊤` (`IsModel.hasCarryingPrivateContext_of_forall_label`); and a private context of the
  acquired form at which a coupled gated extension exists, with its cap labelled as the private
  cap, is carrying (`hasCarryingPrivateContext_of_coupledGatedExtension`), so a carrying private
  context is necessary for the route of (R1) through a coupled gate at that root, donor and floor.
* Open: whether every model at a limit stage acquires carrying contexts.  Neither a proof nor a
  refutation is compiled.  What is compiled about it:
  - **Where the condition can fail.**  A lawful labelling of the private type that keeps the
    private cap `C`, a cell of full scope and full grade, so that every cell lies below it, drops
    only cells that the row of `C` reads in a block strictly below the block of its reading of `C`
    itself (`CellScheme.Rows.IsLawful.lt_row_self_of_eq_bot`), and drops everything that the row
    of `C` reads below the end of the block of a dropped cell
    (`CellScheme.Rows.IsLawful.eq_bot_of_row_le_block`).  So the condition holds when the cap
    reads an anchor of every donor label below it in the block of its reading of itself
    (`StageType.carriesBottoms_of_row_mem_block`); it follows that it can fail only at a donor
    cell all of whose anchors the cap reads in lower blocks, through a lawful labelling that
    drops them all (a corollary, not stated as a theorem).
    The first clause of the condition (a donor cell all of whose anchors are dropped is `⊥`) alone
    is met by the labelling `⊥`, and the second (a donor cell none of whose serving cells is
    dropped is not `⊥`) alone by the donor's own labelling; what is open is the two together, at
    the donor cells all of whose anchors the cap reads below its own block.
  - **The conclusions of the acquisition theorems do not give it.**  The refuting input of the
    coupled property satisfies every conclusion of `IsModel.exists_privateContext` (at every floor, and every `N₀ ≤ 2`) and
    of its anchored form, and fails the condition
    (`CoupledGatedExtensionCounterexample.exists_privateContext_not_carriesBottoms`).
    The clauses that the acquisition uses (uniformity, high-arity dominance, exact consistency)
    bound labels; the private cap is the cell that the last dominance step gives, labelled above
    the floor, and none of these clauses, nor generalized saturation or the bottom pattern (which
    prescribe a scheme, and a bottom pattern at the grades below the new arity, but no lower bound
    on a label of full grade), prescribes its row.  Whether a model must have, over every root, a
    private context whose cap reads anchors in its own block (or carries the bottoms otherwise),
    or whether some model has none for some donor, is not decided here.
* Not stated (prospective, the next step only once acquisition is decided): the coupled gated
  pinned extension property restricted to carrying private contexts, and (R1) from it with
  acquisition.  Nothing here is equivalent to (R1), and (R1) is neither proved nor refuted.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- A **carrying private context** over the root `x` for the donor `d` at the floor `γ`: an
occurrence `y` containing `x` as a literal face along `f`, of arity above `x.arity + 1`, with a
cell `C` of graded index `(univ, y.arity)` labelled above `γ` (the private cap), below which `d`
is anchored in the type of `y` (the form of `IsModel.exists_privateContext_isAnchored`), and whose
type satisfies the bottom transport condition with `d` at the label of `C`
(`StageType.CarriesBottoms`). -/
def HasCarryingPrivateContext (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1))
    (γ : Ordinal.{u}) : Prop :=
  ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (C : Fin y.type.card),
    f.trans y.tuple = x.tuple ∧ StageType.restrictFace f y.type = some x.type ∧
      x.arity + 1 < y.arity ∧ y.type.toCellScheme.gradedIndex C = (univ, y.arity) ∧
      (γ : Label.{u}) < y.type.label C ∧ StageType.IsAnchored y.type C d ∧
      StageType.CarriesBottoms y.type d (y.type.label C)

variable (R) in
/-- A realization **acquires carrying contexts**: over every occurrence `x`, for every coface `d`
of its type and every floor `γ` below the stage, it has a carrying private context
(`HasCarryingPrivateContext`).  Whether every model at a limit stage does is open. -/
def AcquiresCarryingContexts : Prop :=
  ∀ (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1)), d ∈ x.type.cofaces →
    ∀ γ : Ordinal.{u}, γ < α → HasCarryingPrivateContext x d γ

/-- **Donors without proper new labels**: over every occurrence of a model, a donor whose new cells
(those whose scope contains the new point) are labelled `⊥` or `⊤` has a carrying private context
at every floor below the stage.  The private context is that of
`IsModel.exists_privateContext_isAnchored`, and the donor's own labelling meets the bottom
transport condition (`StageType.carriesBottoms_of_forall_label`). -/
theorem IsModel.hasCarryingPrivateContext_of_forall_label (hR : R.IsModel) (x : R.Occurrence)
    {d : StageType.{u} α (x.arity + 1)}
    (hd : ∀ j, Fin.last x.arity ∈ d.toCellScheme.scope j → d.label j = ⊥ ∨ d.label j = ⊤)
    {γ : Ordinal.{u}} (hγ : γ < α) : HasCarryingPrivateContext x d γ := by
  obtain ⟨y, f, C, hf, hfp, hn, hC, hγC, hanc⟩ := hR.exists_privateContext_isAnchored x d hγ
  exact ⟨y, f, C, hf, hfp, hn, hC, hγC, hanc, StageType.carriesBottoms_of_forall_label
    fun j hj ↦ (hd j hj).imp_right fun h ↦ by rw [h]; exact le_top⟩

/-- **A coupled gated extension at a private context makes it carrying**: if a private context of
the acquired form over `x` (a literal face along `f`, arity above `x.arity + 1`, a cell `C` of
graded index `(univ, y.arity)` labelled above `γ`, the donor anchored below `C`) has a coupled
gated extension over `f` with donor `d` whose cap carries the label of `C`, it is a carrying
private context (`StageType.CoupledGatedExtension.carriesBottoms`).  So a carrying private context
is necessary for the route of (R1) through a coupled gate at that root, donor and floor. -/
theorem hasCarryingPrivateContext_of_coupledGatedExtension {x y : R.Occurrence}
    {d : StageType.{u} α (x.arity + 1)} {γ : Ordinal.{u}} {f : Fin x.arity ↪ Fin y.arity}
    {C : Fin y.type.card} (hf : f.trans y.tuple = x.tuple)
    (hfp : StageType.restrictFace f y.type = some x.type) (hn : x.arity + 1 < y.arity)
    (hC : y.type.toCellScheme.gradedIndex C = (univ, y.arity))
    (hγC : (γ : Label.{u}) < y.type.label C) (hanc : StageType.IsAnchored y.type C d)
    (E : StageType.CoupledGatedExtension y.type f d) (hE : E.display.label E.cap = y.type.label C) :
    HasCarryingPrivateContext x d γ :=
  ⟨y, f, C, hf, hfp, hn, hC, hγC, hanc, E.carriesBottoms hE⟩

end Realization

end VaughtConjecture
