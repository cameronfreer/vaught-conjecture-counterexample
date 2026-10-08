/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.CarryingContext

/-!
# Tight caps: where the acquisition of carrying private contexts stands

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the private context) and 3.4, row (R1);
the acquisition step of `VaughtConjecture.Realization.CarryingContext`.

**The question.**  Whether every model acquires carrying private contexts
(`Realization.AcquiresCarryingContexts`): over every root, for every donor and every floor `γ`, a
private context whose cap, a cell of full scope and full grade labelled above `γ`, satisfies the
bottom transport condition (`StageType.CarriesBottoms`).  A cell `C` **reads a label `l` in its
own block** (`StageType.ReadsInOwnBlock`) when some cell labelled `l` below `C` is read by the row
of `C` in the block of its reading of `C` itself; a lawful labelling that keeps `C` keeps such a
cell (`StageType.ReadsInOwnBlock.exists_ne_bot`).  These statements on stage types, with
`StageType.IsAnchoredAt`, `StageType.CarriesBottomsAt` and the obstruction below, are in
`VaughtConjecture.Extension.GatedExtension`, beside `StageType.CarriesBottoms`.  A cap **reads the
donor's anchors in its own block** when every donor label below the cap is a visibility
replacement of a label that the cap reads in its own block; such a cap carries the bottoms
(`StageType.carriesBottoms_of_row_mem_block`, and at any grade
`StageType.carriesBottomsAt_of_readsInOwnBlock`).  A cap is **tight** (over a
root type, at a floor) when it reads in its own block every label of the root type at most the
floor and not self-visible at the cap's grade; this notion does not depend on a donor.  The private
cap has full grade, so it is a cell of the last one-point step that produces the private context.

**The obstruction: readings in the own block lie in one block** (compiled,
`StageType.eq_visibilityReplace_of_readsInOwnBlock`).  If a cell reads in its own block two labels,
both strictly below its own label and neither self-visible at its grade, then one is a visibility
replacement of the other, so the two lie in one block.  Compiled consequences: the tight cap family
over a root type with two such labels in different blocks is empty
(`StageType.tightCapFamily_eq_empty`); no model at a stage above `ω` has tight caps
(`Realization.IsModel.not_hasTightCaps`); and tight saturations fail at every stage above `ω` at
which a model exists (`Realization.IsModel.not_hasTightSaturations`); both refutations assume a
model at a stage above `ω`.  Argued, not compiled: when the cap's grade exceeds the finite parts
of the donor's labels, every proper donor label below the cap is not self-visible at the cap's
grade, and neither is its anchor; so reading anchors in the cap's own block can serve only donors
whose proper labels below the cap, not self-visible at its grade, lie in one block.  The bound is
by the grade of the cap, not the arity of the context: at a cap of grade `N` on `N + 1` points a
finite part `N` is below the arity but self-visible at the grade.  The labels `⊥` and `⊤` are
self-visible at every grade.  The identified obstruction survives the redesigns examined (the cap
of full grade and the subfull cap below); it says nothing about other ways to obtain
`StageType.CarriesBottoms`.

**At full grade, no clause of a model asks for a tight cap.**  Compiled (the statements on
saturation and the bottom pattern are in `VaughtConjecture.Realization.Families`, and the member
of every dominance family in `VaughtConjecture.Extension.CoupledGatedExtensionCounterexample`):
* Every nonempty instance of generalized saturation or of the bottom pattern has a member whose
  cells of full grade are all labelled `⊥`
  (`StageType.exists_mem_cofaces_inter_saturationFamily_label_eq_bot`,
  `StageType.exists_mem_cofaces_inter_bottomPatternFamily_label_eq_bot`), hence a member in no
  dominance family (`StageType.exists_mem_cofaces_inter_saturationFamily_not_mem_dominanceFamily`).
* A member of a dominance family need not carry the bottoms at its dominating cell
  (`CoupledGatedExtensionCounterexample.exists_mem_dominanceFamily_not_carriesBottoms`,
  the refuting input of the coupled property; no occurrence of it in a model is exhibited).  This
  refutes only the finite sufficient condition "every member of a dominance family carries", not
  the acquisition.
* A realization **has tight caps** (`Realization.HasTightCaps`) when over every occurrence and at
  every floor it realizes a member of the **tight cap family** (`StageType.tightCapFamily`, inside
  the dominance family): a coface with a tight cell of full grade above the floor.  A model with
  tight caps acquires carrying contexts
  (`Realization.IsModel.acquiresCarryingContexts_of_hasTightCaps`).  `HasTightCaps` is not a clause
  of `IsModel`; it is refuted for every model at every stage above `ω`
  (`Realization.IsModel.not_hasTightCaps`), so that conditional theorem is vacuous above `ω`.  At
  the stage `0` no floor lies below the stage, so `HasTightCaps` and `AcquiresCarryingContexts`
  hold vacuously there (immediate from the definitions, not stated as theorems); `HasTightCaps` is
  open at the stages from `1` to `ω`.

Argued, not compiled: generalized saturation and the bottom pattern prescribe a scheme, rows
included, but give no lower bound on a label of full grade, so no clause asks for a coface on a
prescribed scheme with a label of full grade above a floor; choosing the saturation scheme to
contain the cell of an earlier dominance step does not help, since that cell is not of full grade
after the step.  High-arity dominance bounds a label of full grade at a cell whose row it does not
constrain.

**One grade below full, the clauses give a cap with a prescribed row.**  Availability compares
cells of equal grade: in a legal one-point extension, every cell `T` of the face has a cell of full
scope with the grade of `T` labelled at least as `T` (`StageType.exists_le_label_of_restrictFace`,
compiled).  Over the private cap `T` of `Realization.IsModel.exists_privateContext`, generalized
saturation for a prescribed scheme `S` therefore gives a cell `G` of graded index `(univ, N)` on
`N + 1` points labelled above the floor, whose row is that of `S`: the label bound and the row
concern the same cell, one grade below full.  That is the position of the gate in a display, not of
the private cap: `StageType.HasCoupledGatedPinnedExtensions` asks for a private cap of graded index
`(univ, n)`.  A private context with a **subfull cap** (a cell of full scope and grade one below
the arity) is therefore a **redesign**, not a repair.  The statements on rows that a gate uses
(`CellScheme.Rows.IsGate`, `CellScheme.Rows.cap_le_gate_of_twinsReadGate`,
`CellScheme.Rows.IsLawful.eq_bot_of_gateReads`) ask only that cap and gate have equal grades and
nested scopes, with the grade of the gate as the threshold; the stage-level structures fix that
grade to the private arity.  For the redesign:
* stated: the anchoring and the bottom transport condition at a grade `k`
  (`StageType.IsAnchoredAt`, `StageType.CarriesBottomsAt`; at `k = n` they are `IsAnchored` and
  `CarriesBottoms`, `StageType.isAnchoredAt_iff`, `StageType.carriesBottomsAt_iff`), and a carrying
  context with a subfull cap (`Realization.HasCarryingSubfullContext`).  That a coupled
  gated extension with gate and cap of grade `k` would force `CarriesBottomsAt` at `k` is argued
  from the proof of `StageType.CoupledGatedExtension.carriesBottoms`, not compiled: no such
  extension is defined;
* stated: **tight saturations** (`StageType.HasTightSaturations α`), a statement about legal stage
  types and schemes, not about models: over every legal `p` on `N` points, a legal one-point
  extension scheme with a coface of `p` whose cells of graded index `(univ, N)` are tight (read in
  their own block every label of `p` not self-visible at `N`).  It is false at every stage above
  `ω` at which a model exists (`Realization.IsModel.not_hasTightSaturations`, compiled, assuming a
  model at a stage above `ω`) and undecided at stages at most `ω`;
* compiled: every model has, over every root, for every donor and every floor below the stage, a
  carrying context with a cap one grade below full, conditional on tight saturations
  (`Realization.IsModel.hasCarryingSubfullContext`); vacuous above `ω`, and at the stage `0`, where
  no floor lies below the stage.  Of the clauses of a model it uses uniformity, high-arity
  dominance, legality, exact consistency and generalized saturation.  It constructs no extension
  in the redesign (no coupled gated extension with a cap of grade below full is defined) and does
  not prove (R1).

**What is not claimed.**  `Realization.AcquiresCarryingContexts` and
`Realization.HasCarryingSubfullContext` are neither proved nor refuted for all models: the
refutations above concern only the two sufficient conditions `Realization.HasTightCaps` and
`StageType.HasTightSaturations`, each over a model at a stage above `ω`; they do not show that no
model exists, and no stagewise statement without a model is made.  The two conditional theorems
are kept although vacuous above `ω`; retiring them is a separate change.  No extension property
for a cap one grade below full is defined, and the coupled property restricted to carrying
contexts is not stated (prospective).  Nothing here is equivalent to (R1), and (R1) is neither
proved nor refuted.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.  It keeps the tight cap family and tight
saturations (defined from the families of `VaughtConjecture.Realization.Families` and the readings
of `VaughtConjecture.Extension.GatedExtension`) and the statements on realizations; it imports no
counterexample module.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-! ### The finite hypothesis for caps of grade below full -/

variable (α) in
/-- **Tight saturations** (a named hypothesis on stage types): over every legal stage type `p` on
`N` points there is a scheme `S` on `N + 1` points with a coface of `p`, such that in every coface
of `p` on `S`, every cell of full scope and grade `N` is tight: it reads, in its own block, a cell
labelled `l` for every label `l` of `p` that is not self-visible at `N`.  It concerns schemes and
stage types only, not models: it asks for a legal one-point extension of the scheme of `p` whose
cells of graded index `(univ, N)` read the proper labels of `p` in their own block.  It is false at
every stage above `ω` at which a model exists (`Realization.IsModel.not_hasTightSaturations`,
compiled) and undecided at stages at most `ω`. -/
def HasTightSaturations : Prop :=
  ∀ {N : ℕ} (p : StageType.{u} α N), p.IsLegal →
    ∃ S : Scheme.{u} (N + 1), (p.cofaces ∩ saturationFamily S).Nonempty ∧
      ∀ q ∈ p.cofaces ∩ saturationFamily S, ∀ G : Fin q.card,
        q.toCellScheme.gradedIndex G = (univ, N) →
        ∀ z : Fin p.card, ¬ IsSelfVisible N (p.label z) → q.ReadsInOwnBlock G (p.label z)

/-- The **tight cap family** over `p` at the floor `γ`: the stage types on `n + 1` points with a
cell of full grade labelled above `γ` that is tight: it reads, in its own block, a cell labelled `l`
for every label `l ≤ γ` of `p` not self-visible at `n + 1`.  It lies in the dominance family
(`tightCapFamily_subset_dominanceFamily`); no clause of a model asks for it, and it is empty when
two such labels of `p` lie in different blocks (`tightCapFamily_eq_empty`). -/
def tightCapFamily (p : StageType.{u} α n) (γ : Ordinal.{u}) : Set (StageType.{u} α (n + 1)) :=
  {q | ∃ C, q.toCellScheme.grade C = n + 1 ∧ (γ : Label.{u}) < q.label C ∧
    ∀ z : Fin p.card, ¬ IsSelfVisible (n + 1) (p.label z) → p.label z ≤ (γ : Label.{u}) →
      q.ReadsInOwnBlock C (p.label z)}

/-- The tight cap family lies in the dominance family at the same floor. -/
theorem tightCapFamily_subset_dominanceFamily (p : StageType.{u} α n) (γ : Ordinal.{u}) :
    p.tightCapFamily γ ⊆ dominanceFamily γ :=
  fun _ ⟨C, hC, hγC, _⟩ ↦ ⟨C, hC, hγC⟩

/-! ### The tight cap family is empty over two blocks -/

/-- **The tight cap family is empty over two blocks**: if `p` has cells labelled `μ₀ + k₀` and
`μ₁ + k₁`, with `μ₀ ≠ μ₁` each zero or a limit, `k₀, k₁ < n + 1` (so neither label is self-visible
at the new arity), and both labels at most `γ`, then no stage type on `n + 1` points is in the
tight cap family of `p` at `γ`: its cap would read both labels in its own block
(`eq_visibilityReplace_of_readsInOwnBlock`). -/
theorem tightCapFamily_eq_empty {p : StageType.{u} α n}
    {γ μ₀ μ₁ : Ordinal.{u}} (hμ₀ : Order.IsSuccPrelimit μ₀) (hμ₁ : Order.IsSuccPrelimit μ₁)
    (hne : μ₀ ≠ μ₁) {k₀ k₁ : ℕ} (hk₀ : k₀ < n + 1) (hk₁ : k₁ < n + 1) {z₀ z₁ : Fin p.card}
    (hz₀ : p.label z₀ = ((μ₀ + k₀ : Ordinal.{u}) : Label.{u}))
    (hz₁ : p.label z₁ = ((μ₁ + k₁ : Ordinal.{u}) : Label.{u}))
    (h₀ : μ₀ + k₀ ≤ γ) (h₁ : μ₁ + k₁ ≤ γ) :
    p.tightCapFamily γ = ∅ := by
  ext q
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨C, hCgr, hγC, htight⟩
  have hle : ∀ o : Ordinal.{u}, o ≤ γ → (o : Label.{u}) < q.label C := fun o ho ↦
    lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ho)) hγC
  have hv₀ := not_isSelfVisible_coe_add_natCast hμ₀ hk₀
  have hv₁ := not_isSelfVisible_coe_add_natCast hμ₁ hk₁
  have r₀ := htight z₀ (hz₀ ▸ hv₀) (hz₀ ▸ WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h₀))
  have r₁ := htight z₁ (hz₁ ▸ hv₁) (hz₁ ▸ WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h₁))
  rw [hz₀] at r₀
  rw [hz₁] at r₁
  rw [← hCgr] at hv₀ hv₁
  obtain ⟨j, -, hj⟩ := eq_visibilityReplace_of_readsInOwnBlock r₀ r₁ (hle _ h₀) (hle _ h₁) hv₀ hv₁
  rw [hCgr, visibilityReplace_coe_add_natCast hμ₀ hk₀ j] at hj
  -- the block start of an ordinal label is unique (`Label.add_natCast_eq_add_natCast_iff`)
  exact hne ((add_natCast_eq_add_natCast_iff hμ₁ hμ₀).mp
    (WithTop.coe_injective (WithBot.coe_injective hj))).1.symm

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- A label strictly between `⊥` and some label is an ordinal. -/
private theorem exists_eq_coe_of_ne_bot_of_lt {x c : Label.{u}} (hx : x ≠ ⊥) (hxc : x < c) :
    ∃ o : Ordinal.{u}, x = o := by
  induction x using recBotCoeTop with
  | bot => exact absurd rfl hx
  | coe o => exact ⟨o, rfl⟩
  | top => exact absurd hxc not_top_lt

/-! ### Carrying contexts with a cap of grade below full -/

/-- A **carrying context with a cap of grade below full** over the root `x` for the donor `d` at
the floor `γ`: an occurrence `y` on `N + 1` points containing `x` as a literal face along `f`, with
`x.arity + 1 < N`, and a cell `G` of full scope and grade `N` (one below the arity) labelled above
`γ`, below which `d` is anchored at the grade `N` (`StageType.IsAnchoredAt`), and at which the
type of `y` satisfies the bottom transport condition at the grade `N`
(`StageType.CarriesBottomsAt`).  This is `HasCarryingPrivateContext` with the cap one grade below
full, a different design: the coupled gated pinned extension property asks for a cap of full
grade. -/
def HasCarryingSubfullContext (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1))
    (γ : Ordinal.{u}) : Prop :=
  ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (N : ℕ) (G : Fin y.type.card),
    f.trans y.tuple = x.tuple ∧ StageType.restrictFace f y.type = some x.type ∧
      y.arity = N + 1 ∧ x.arity + 1 < N ∧ y.type.toCellScheme.gradedIndex G = (univ, N) ∧
      (γ : Label.{u}) < y.type.label G ∧ StageType.IsAnchoredAt y.type G N d ∧
      StageType.CarriesBottomsAt y.type d (y.type.label G) N

/-- **Carrying contexts with a cap of grade below full, from tight saturations**: over every
occurrence of a model, for every donor and every floor below the stage, there is a carrying
context with a cap of grade below full, provided the named hypothesis
`StageType.HasTightSaturations α` holds.  That hypothesis is false at every stage above `ω` at
which a model exists (`IsModel.not_hasTightSaturations`), so this theorem is vacuous above `ω`; it
is kept, and `HasCarryingSubfullContext` itself is neither proved nor refuted.

The private context of `IsModel.exists_privateContext` gives an occurrence `w` on `N` points with
a cell `T` of graded index `(univ, N)` labelled above `γ` and the reference cells of the donor's
labels, not self-visible at `N`.  Generalized saturation over `w`, for the scheme that the
hypothesis provides, gives `y` on `N + 1` points.  Availability from the face
(`StageType.exists_le_label_of_restrictFace`) gives a cell `G` of graded index `(univ, N)`
labelled at least as `T`; it reads the reference cells' labels in its own block, so the bottom
transport condition at the grade `N` holds (`StageType.carriesBottomsAt_of_readsInOwnBlock`).  Of
the clauses of a model, uniformity, high-arity dominance, legality, exact consistency, and
generalized saturation are used.  It constructs no extension in the redesign (no coupled gated
extension with a cap of grade below full is defined) and does not prove (R1). -/
theorem IsModel.hasCarryingSubfullContext (hR : R.IsModel)
    (ht : StageType.HasTightSaturations α) (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1))
    {γ : Ordinal.{u}} (hγ : γ < α) : HasCarryingSubfullContext x d γ := by
  obtain ⟨w, f, T, hf, hn, -, hT, hγT, hanc⟩ := hR.exists_privateContext x d hγ 0
  obtain ⟨S, hS, htight⟩ := ht w.type (hR.isLegal _ _ w.eval_tuple)
  obtain ⟨u, hu, q, hqS, he⟩ := hR.saturation w S hS
  have hqp : StageType.restrictFace Fin.castSuccEmb q = some w.type := by
    rw [← hR.isConsistent u q _ he, hu, w.eval_tuple]
  have hq : q ∈ w.type.cofaces ∩ StageType.saturationFamily S :=
    ⟨⟨hR.isLegal _ _ he, hqp⟩, hqS⟩
  obtain ⟨G, hG, hTG⟩ := StageType.exists_le_label_of_restrictFace (hR.isLegal _ _ he) hqp T
  rw [show w.type.toCellScheme.grade T = w.arity from congrArg Prod.snd hT] at hG
  have htuple : (f.trans Fin.castSuccEmb).trans u = x.tuple := by
    rw [Function.Embedding.trans_assoc, hu, hf]
  -- each donor label below `G` is read through a reference cell whose label `G` reads in its block
  have hread : ∀ j : Fin d.card, d.label j ≠ ⊥ → d.label j < q.label G →
      ∃ l, (∃ k ≤ w.arity, d.label j = visibilityReplace w.arity k l) ∧
        q.ReadsInOwnBlock G l := fun j hne hlt ↦ by
    obtain ⟨o, ho⟩ := exists_eq_coe_of_ne_bot_of_lt hne hlt
    obtain ⟨z, i, hi, hzi, hzv, -⟩ := hanc j o ho
    exact ⟨w.type.label z, ⟨i, hi.le, hzi⟩, htight q hq G hG z hzv⟩
  refine ⟨⟨_, u, q, he⟩, f.trans Fin.castSuccEmb, w.arity, G, htuple,
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent htuple, rfl, hn, hG,
    hγT.trans_le hTG, fun j _ hne hlt ↦ ?_,
    StageType.carriesBottomsAt_of_readsInOwnBlock hG fun j _ hne hlt ↦ hread j hne hlt⟩
  obtain ⟨l, ⟨k, hk, hjl⟩, z, -, hzl, -⟩ := hread j hne hlt
  exact ⟨z, k, hk, hzl ▸ hjl⟩

/-! ### Tight caps of full grade -/

variable (R) in
/-- A realization **has tight caps**: over every occurrence `x` and at every floor `γ` below the
stage, it realizes a member of the tight cap family (`StageType.tightCapFamily`): a coface with a
cell of full grade labelled above `γ` that reads, in its own block, every label `l ≤ γ` of the type
of `x` not self-visible at `x.arity + 1`.  This is high-arity dominance with a condition on the row
of the dominating cell; it is not a clause of a model.  It is refuted for every model at every
stage above `ω` (`IsModel.not_hasTightCaps`: the cap would read labels in two blocks in its own
block).  At the stage `0` it holds vacuously (no floor lies below the stage); it is open at the
stages from `1` to `ω`. -/
def HasTightCaps : Prop :=
  ∀ (x : R.Occurrence) (γ : Ordinal.{u}), γ < α →
    R.RealizesOver x.tuple (x.type.tightCapFamily γ)

/-- **Carrying private contexts from tight caps**: over every occurrence of a model with tight
caps, every donor has a carrying private context at every floor below the stage.

Uniformity and dominance give the reference cells of the donor's blocks, labelled at most a floor
`B ≥ γ`, over an occurrence whose arity exceeds their finite parts and the donor's
(`IsModel.exists_referenceCells`); the tight cap over it at the floor `B` reads the reference
cells' labels in its own block, which anchors the donor and gives the bottom transport condition
(`StageType.carriesBottomsAt_of_readsInOwnBlock` at the arity, `StageType.carriesBottomsAt_iff`). -/
theorem IsModel.hasCarryingPrivateContext_of_hasTightCaps (hR : R.IsModel)
    (ht : R.HasTightCaps) (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1))
    {γ : Ordinal.{u}} (hγ : γ < α) : HasCarryingPrivateContext x d γ := by
  obtain ⟨w, f, -, B, μ, hf, hn, hγB, hBα, -, -, hμ, href⟩ := hR.exists_referenceCells x d hγ 0
  obtain ⟨u, hu, q, ⟨C, hCgr, hBC, htight⟩, he⟩ := ht w B hBα
  have htuple : (f.trans Fin.castSuccEmb).trans u = x.tuple := by
    rw [Function.Embedding.trans_assoc, hu, hf]
  have hC : q.toCellScheme.gradedIndex C = (univ, w.arity + 1) :=
    StageType.gradedIndex_eq_univ_of_grade_eq q hCgr
  -- each donor label below `C` is read through a reference cell that `C` reads in its block
  have hread : ∀ j : Fin d.card, d.label j ≠ ⊥ → d.label j < q.label C →
      ∃ l, (∃ k ≤ w.arity + 1, d.label j = visibilityReplace (w.arity + 1) k l) ∧
        q.ReadsInOwnBlock C l := fun j hne hlt ↦ by
    obtain ⟨o, ho⟩ := exists_eq_coe_of_ne_bot_of_lt hne hlt
    obtain ⟨i, hi, rfl⟩ := (hμ j).2 o ho
    obtain ⟨z, k, hk, hz, hkB⟩ := href j
    have hkn : k < w.arity + 1 := by omega
    refine ⟨w.type.label z, ⟨i, by omega, ?_⟩, htight z ?_ ?_⟩ <;> rw [hz]
    · rw [ho, visibilityReplace_coe_add_natCast (hμ j).1 hkn]
    · exact not_isSelfVisible_coe_add_natCast (hμ j).1 hkn
    · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hkB)
  refine ⟨⟨_, u, q, he⟩, f.trans Fin.castSuccEmb, C, htuple,
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent htuple, by simp; omega, hC,
    lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hγB)) hBC,
    fun j _ hne hlt ↦ ?_, StageType.carriesBottomsAt_iff.mp
      (StageType.carriesBottomsAt_of_readsInOwnBlock hC fun j _ hne hlt ↦ hread j hne hlt)⟩
  obtain ⟨l, ⟨k, hk, hjl⟩, z, -, hzl, -⟩ := hread j hne hlt
  exact ⟨z, k, hk, hzl ▸ hjl⟩

/-- **Acquisition from tight caps**: a model with tight caps acquires carrying contexts.  No model
above `ω` has tight caps (`IsModel.not_hasTightCaps`), so this theorem is vacuous above `ω`; it is
kept, and `AcquiresCarryingContexts` itself is neither proved nor refuted. -/
theorem IsModel.acquiresCarryingContexts_of_hasTightCaps (hR : R.IsModel)
    (ht : R.HasTightCaps) : R.AcquiresCarryingContexts :=
  fun x d _ _ hγ ↦ hR.hasCarryingPrivateContext_of_hasTightCaps ht x d hγ

/-! ### Tight caps and tight saturations fail above `ω`

The two sufficient conditions above are refuted at every stage above `ω` at which a model
exists; the conditional theorems `IsModel.acquiresCarryingContexts_of_hasTightCaps` and
`IsModel.hasCarryingSubfullContext` are therefore vacuous there (they are kept here; retiring
them is a separate change).  Neither `AcquiresCarryingContexts`, nor `HasCarryingSubfullContext`,
nor (R1) is refuted. -/

/-- Over a model at a stage above `ω`: an occurrence with reference cells in the blocks of `0` and
`ω`, labelled at most a floor `B` below the stage, whose finite parts are below its arity, and a
cell of full scope and full grade labelled above `B` (uniformity, then high-arity dominance). -/
private theorem exists_occurrence_two_blocks (hR : R.IsModel) (hα : Ordinal.omega0 < α) :
    ∃ (w : R.Occurrence) (B : Ordinal.{u}), B < α ∧
      (∃ z, ∃ k < w.arity, w.type.label z = ((0 + k : Ordinal.{u}) : Label.{u}) ∧ 0 + k ≤ B) ∧
      (∃ z, ∃ k < w.arity, w.type.label z =
        ((Ordinal.omega0 + k : Ordinal.{u}) : Label.{u}) ∧ Ordinal.omega0 + k ≤ B) ∧
      ∃ T : Fin w.type.card, w.type.toCellScheme.gradedIndex T = (univ, w.arity) ∧
        (B : Label.{u}) < w.type.label T := by
  obtain ⟨x⟩ := hR.nonempty_occurrence
  have h0 : (0 : Ordinal.{u}) < α := (Ordinal.omega0_pos).trans hα
  obtain ⟨y, f, K, B, hf, -, hBα, hanc⟩ := hR.exists_extend_uniformity x h0
    [0, Ordinal.omega0] (by
      intro μ hμ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
      rcases hμ with rfl | rfl
      · exact ⟨Ordinal.isSuccPrelimit_zero, h0⟩
      · exact ⟨Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr dvd_rfl, hα⟩)
  obtain ⟨w, f₂, hf₂, hw, T, hT, hBT⟩ := hR.exists_extend_dominance y hBα K
  obtain ⟨z₀, k₀, hk₀, hz₀, hB₀⟩ := hanc 0 (by simp)
  obtain ⟨z₁, k₁, hk₁, hz₁, hB₁⟩ := hanc Ordinal.omega0 (by simp)
  obtain ⟨z₀', hz₀'⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₂ z₀
  obtain ⟨z₁', hz₁'⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₂ z₁
  exact ⟨w, B, hBα, ⟨z₀', k₀, by omega, hz₀'.trans hz₀, hB₀⟩,
    ⟨z₁', k₁, by omega, hz₁'.trans hz₁, hB₁⟩, T, hT, hBT⟩

/-- **No model above `ω` has tight caps.**  Over an occurrence with reference cells in the blocks
of `0` and `ω` labelled at most a floor `B` (`exists_occurrence_two_blocks`), the tight cap family
at `B` is empty (`StageType.tightCapFamily_eq_empty`).  So
`IsModel.acquiresCarryingContexts_of_hasTightCaps` is vacuous above `ω`.  This refutes only the
sufficient condition `HasTightCaps`, over a model at a stage above `ω`, not
`AcquiresCarryingContexts` and not (R1); at the stage `0` `HasTightCaps` holds vacuously, and at
the stages from `1` to `ω` it is neither proved nor refuted. -/
theorem IsModel.not_hasTightCaps (hR : R.IsModel) (hα : Ordinal.omega0 < α) :
    ¬ R.HasTightCaps := by
  intro ht
  obtain ⟨w, B, hBα, ⟨z₀, k₀, hk₀, hz₀, hB₀⟩, ⟨z₁, k₁, hk₁, hz₁, hB₁⟩, -⟩ :=
    exists_occurrence_two_blocks hR hα
  obtain ⟨u, -, q, hq, -⟩ := ht w B hBα
  rw [StageType.tightCapFamily_eq_empty Ordinal.isSuccPrelimit_zero
    (Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr dvd_rfl) Ordinal.omega0_pos.ne
    (by omega : k₀ < w.arity + 1) (by omega : k₁ < w.arity + 1) hz₀ hz₁ hB₀ hB₁] at hq
  exact hq

/-- **Tight saturations fail at every stage above `ω` at which a model exists.**  Over an
occurrence `w` on `N` points with reference cells in the blocks of `0` and `ω` and a cell of
graded index `(univ, N)` labelled above them (`exists_occurrence_two_blocks`), saturation for the
scheme that the hypothesis provides gives a coface with a cell `G` of graded index `(univ, N)`
labelled at least as high (`StageType.exists_le_label_of_restrictFace`), which would read both
labels in its own block (`StageType.eq_visibilityReplace_of_readsInOwnBlock`).  So
`IsModel.hasCarryingSubfullContext` is vacuous above `ω`.  This refutes only the sufficient
condition `StageType.HasTightSaturations`, given a model at a stage above `ω`; it refutes neither
`HasCarryingSubfullContext` nor (R1), and does not show that models are absent at any stage.  At
stages at most `ω` `HasTightSaturations` is neither proved nor refuted. -/
theorem IsModel.not_hasTightSaturations (hR : R.IsModel) (hα : Ordinal.omega0 < α) :
    ¬ StageType.HasTightSaturations α := by
  intro ht
  obtain ⟨w, B, -, ⟨z₀, k₀, hk₀, hz₀, hB₀⟩, ⟨z₁, k₁, hk₁, hz₁, hB₁⟩, T, hT, hBT⟩ :=
    exists_occurrence_two_blocks hR hα
  obtain ⟨S, hS, htight⟩ := ht w.type (hR.isLegal _ _ w.eval_tuple)
  obtain ⟨u, hu, q, hqS, he⟩ := hR.saturation w S hS
  have hqp : StageType.restrictFace Fin.castSuccEmb q = some w.type := by
    rw [← hR.isConsistent u q _ he, hu, w.eval_tuple]
  have hq : q ∈ w.type.cofaces ∩ StageType.saturationFamily S :=
    ⟨⟨hR.isLegal _ _ he, hqp⟩, hqS⟩
  obtain ⟨G, hG, hTG⟩ := StageType.exists_le_label_of_restrictFace (hR.isLegal _ _ he) hqp T
  rw [show w.type.toCellScheme.grade T = w.arity from congrArg Prod.snd hT] at hG
  have hGgr : q.toCellScheme.grade G = w.arity := congrArg Prod.snd hG
  have hμ₁ : Order.IsSuccPrelimit Ordinal.omega0.{u} :=
    Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr dvd_rfl
  have hv₀ := not_isSelfVisible_coe_add_natCast Ordinal.isSuccPrelimit_zero hk₀
  have hv₁ := not_isSelfVisible_coe_add_natCast hμ₁ hk₁
  have r₀ := htight q hq G hG z₀ (hz₀ ▸ hv₀)
  have r₁ := htight q hq G hG z₁ (hz₁ ▸ hv₁)
  rw [hz₀] at r₀
  rw [hz₁] at r₁
  have hle : ∀ o : Ordinal.{u}, o ≤ B → (o : Label.{u}) < q.label G := fun o ho ↦
    lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ho)) (hBT.trans_le hTG)
  rw [← hGgr] at hv₀ hv₁
  obtain ⟨j, -, hj⟩ :=
    StageType.eq_visibilityReplace_of_readsInOwnBlock r₀ r₁ (hle _ hB₀) (hle _ hB₁) hv₀ hv₁
  rw [hGgr, visibilityReplace_coe_add_natCast Ordinal.isSuccPrelimit_zero hk₀ j] at hj
  -- the block start of an ordinal label is unique (`Label.add_natCast_eq_add_natCast_iff`)
  exact Ordinal.omega0_pos.ne ((add_natCast_eq_add_natCast_iff hμ₁ Ordinal.isSuccPrelimit_zero).mp
    (WithTop.coe_injective (WithBot.coe_injective hj))).1.symm

end Realization

end VaughtConjecture
