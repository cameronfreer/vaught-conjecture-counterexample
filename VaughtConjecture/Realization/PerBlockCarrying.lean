/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.TightCap

/-!
# Per-block carrying contexts: one cap and one gate per block of the donor

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the private context, the display and its
gate) and 3.4, row (R1); the acquisition step of `VaughtConjecture.Realization.CarryingContext`,
after `VaughtConjecture.Realization.TightCap`.

**Why one cap per block.**  A cap that reads the donor's anchors in its own block carries the
bottoms (`StageType.carriesBottoms_of_row_mem_block`), but a cell reads in its own block labels
below its own and not self-visible at its grade only within one block
(`StageType.eq_visibilityReplace_of_readsInOwnBlock`).  So one cap can carry in this way only donors
whose proper labels below it lie in one block (argued, not compiled).  This file examines the design
with one cap for each block of the donor's labels.  It is a **redesign** of the private context and
of the display, not a repair of the coupled gated pinned extension property.

**Per-block caps need per-block gates.**  The statements on rows that a gate uses
(`CellScheme.Rows.cap_le_gate_of_twinsReadGate`, `CellScheme.Rows.IsLawful.eq_bot_of_gateReads`,
`CellScheme.Rows.IsLawful.ne_bot_of_gateReads`) ask for a cap and a gate of equal grades and nested
scopes, because availability compares cells of equal grade only.  So a cap of lower grade gives no
lower bound on a gate of full grade, and the readings of that gate carry nothing from it (argued
from the clauses of `CellScheme.Rows.IsLawful`, not compiled).  One gate of the cap's grade per cap
is therefore part of the design.

**Stated and compiled.**  The statements on stage types lie beside their subjects: the display
with several gates beside `StageType.CoupledGatedExtension` (`Extension/GatedExtension`), the
per-block condition and its necessity beside `StageType.CarriesBottoms`
(`Extension/CoupledGatedExtensionCounterexample`), and the statements on readings in the own
block, the condition at a grade `k` and the hypothesis on schemes beside `StageType.ReadsInOwnBlock`
and `StageType.HasTightSaturations` (`Realization/TightCap`).  This file holds the contexts and the
acquisition.
* `StageType.PerBlockCoupledGatedExtension P f d k`: a legal display with literal faces `P` and `d`,
  and `k` gates, each with its own cap (a private cell of graded index `capIndex t`) and its own set
  of donor labels that it reads (`readLabels t`).  Each gate's twins read it at least as its cap,
  and its row reads those donor cells (`CellScheme.Rows.IsGate`).  Only the clauses that the
  necessity lemma uses are stated.  No universal extension property is stated for this design.
* `StageType.CarriesBottomsPerBlock`: one lawful donor labelling for each lawful private labelling,
  satisfying the two clauses of `StageType.CarriesBottoms` at every gate whose cap the private
  labelling keeps.  With one cap of full scope and grade `k` reading every label it is
  `CarriesBottomsAt` at `k` (`StageType.carriesBottomsPerBlock_one_iff_at`), and at full grade
  `CarriesBottoms` (`StageType.carriesBottomsPerBlock_one_iff`).
* **Necessity** (compiled): every per-block coupled gated extension forces it
  (`StageType.PerBlockCoupledGatedExtension.carriesBottomsPerBlock`); with one gate this is
  `StageType.CoupledGatedExtension.carriesBottoms`, derived through
  `StageType.CoupledGatedExtension.toPerBlock` and `StageType.carriesBottomsPerBlock_one_iff`.  At
  the level of realizations, a context at which such an extension exists is a per-block carrying
  context (`Realization.hasCarryingPerBlockContext_of_perBlockCoupledGatedExtension`).
* **The row condition** (compiled; sufficient, not shown necessary): the condition holds when each
  cap reads in its own block an anchor of every donor label below it that it reads
  (`StageType.carriesBottomsPerBlock_of_readsInOwnBlock`).  This is the form "for each block, a
  private cell whose row reads that block's anchors in its own block".  By the same-block lemma,
  the labels that such a cap reads in its own block, strictly below its label and not self-visible
  at its grade, lie in one block.
* `Realization.HasCarryingPerBlockContext` and `Realization.AcquiresPerBlockContexts`: a private
  context with finitely many caps, each of grade above the root's arity plus one and labelled above
  the floor.  The labels below a cap that it reads lie in one block, every new donor label other
  than `⊥` is read by some cap, these labels are anchored at the cap's grade, and the per-block
  condition holds.

**Acquisition: conditional, not decided.**
* Compiled conditionally: every model acquires per-block contexts, given the hypothesis on schemes
  `StageType.HasBlockTightSaturations α`
  (`Realization.IsModel.acquiresPerBlockContexts_of_hasBlockTightSaturations`).  The hypothesis
  says: over every legal `p` on `N` points and every block start `μ`, some legal one-point extension
  scheme with a coface of `p` has all of its cells of graded index `(univ, N)` reading, in their own
  block, every label of `p` in the block of `μ` not self-visible at `N`.
* The construction (`Realization.IsModel.exists_extend_blockCaps`): one step per block.  A
  dominance step gives a cell of full grade labelled above the floor.  Saturation for the scheme
  of the hypothesis, together with availability from the face
  (`StageType.exists_le_label_of_restrictFace`), gives the block's cap one grade below full, with
  the label bound and the row at the same cell.  Later steps keep it as a cell of a face
  (`StageType.exists_readsInOwnBlock_of_restrictFace`).
* The hypothesis is `StageType.HasTightSaturations` restricted to one block at a time
  (`StageType.HasTightSaturations.hasBlockTightSaturations`).  The refutation of the latter above
  `ω` (`Realization.IsModel.not_hasTightSaturations`) needs one cell to read labels of two blocks,
  so it does not apply.  Whether the hypothesis holds is **undecided**: it asks for legal one-point
  extension schemes with prescribed rows, a completion problem of the kind of (R6).  Compiled: such
  a cap labelled beyond its block reads itself at a finite part above its grade
  (`StageType.label_le_of_readsInOwnBlock`).  The library's coding of rows allows this.
* Argued, not compiled: the clauses of a model give a cell with both a prescribed row and a lower
  bound on its label only in this way (availability from the face in a saturation step).  No clause
  prescribes the row of a cell of full grade (`Realization/TightCap`).  So without a hypothesis on
  schemes the acquisition is neither proved nor refuted here.

**The refuting input of the coupled property.**  Its donor has its proper labels in one block, so
one gate per block is one gate there, and the obstruction remains.
* Every family of caps labelled above `1`, in which some cap reads the donor label `1` and some
  cap reads the donor label `⊤`, fails the per-block condition
  (`CoupledGatedExtensionCounterexample.not_carriesBottomsPerBlock`).
* Every family of caps of grade above `0 + 1` with such readers of `1` and of `⊤` fails it
  (`CoupledGatedExtensionCounterexample.not_carriesBottomsPerBlock_of_one_lt_grade`).  The grade
  bound replaces only the bound on the cap labels; the readers are needed, since with no labels
  read the donor's own labelling meets the condition.
* No per-block coupled gated extension has a gate that reads the donor label `1` and a gate that
  reads the donor label `⊤`, both against caps labelled above `1`
  (`CoupledGatedExtensionCounterexample.not_perBlockCoupledGatedExtension`).
* No cap label above `1` satisfies the bottom transport condition at the grade `1`
  (`CoupledGatedExtensionCounterexample.not_carriesBottomsAt_one`).

The per-block design inherits the obstruction there: at the refuting input the bottom transport
obstruction survives the redesigns examined, namely the cap of full grade
(`CoupledGatedExtensionCounterexample.not_carriesBottoms`), the subfull cap
(`CoupledGatedExtensionCounterexample.not_carriesBottomsAt_one`), and one cap and gate per block
(`CoupledGatedExtensionCounterexample.not_carriesBottomsPerBlock`).  The subfull refutation is at
`N = 1` over the empty root, where `Realization.HasCarryingSubfullContext` requires
`x.arity + 1 < N`, which is false; so it refutes the bottom transport condition
`StageType.CarriesBottomsAt` at the subfull grade, not a subfull carrying context.  A
restricted per-block property, asking for a per-block coupled gated extension only at per-block
carrying contexts, excludes that input, which is not per-block carrying.  That property is
**prospective and not stated**.

**What is not claimed.**  `Realization.AcquiresPerBlockContexts` is neither proved nor refuted for
all models.  `StageType.HasBlockTightSaturations` is neither proved nor refuted.  The restricted
per-block extension property is not stated, and its sufficiency for (R1) is not examined; agreement
below the cutoff would have to be re-derived gate by gate.  Nothing here is equivalent to (R1), and
(R1) is neither proved nor refuted.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-! ### Per-block carrying contexts -/

/-- A **per-block carrying context** over the root `x` for the donor `d` at the floor `γ`: an
occurrence `y` containing `x` as a literal face along `f`, of arity above `x.arity + 1`, with `k`
caps `C t`, cells of grade above `x.arity + 1` labelled above `γ`, each reading a set `L t` of
donor labels whose members below the label of `C t` lie in one block `[μ, μ + ω)`; every new donor
label other than `⊥` is read by some cap; the donor labels that a cap reads below its label are
anchored at its grade; and the type of `y` satisfies the per-block bottom transport condition
(`StageType.CarriesBottomsPerBlock`) with these caps.  This is a redesign of the private context
of `HasCarryingPrivateContext` (one cap of full scope and full grade): one cap, and one gate of the
grade of that cap, per block. -/
def HasCarryingPerBlockContext (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1))
    (γ : Ordinal.{u}) : Prop :=
  ∃ (y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (k : ℕ) (C : Fin k → Fin y.type.card)
    (L : Fin k → Set Label.{u}),
    f.trans y.tuple = x.tuple ∧ StageType.restrictFace f y.type = some x.type ∧
      x.arity + 1 < y.arity ∧
      (∀ t, x.arity + 1 < y.type.toCellScheme.grade (C t) ∧ (γ : Label.{u}) < y.type.label (C t) ∧
        ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∀ l ∈ L t, l < y.type.label (C t) →
          ∃ i : ℕ, l = ((μ + i : Ordinal.{u}) : Label.{u})) ∧
      (∀ j, Fin.last x.arity ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → ∃ t, d.label j ∈ L t) ∧
      (∀ t j, Fin.last x.arity ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j ∈ L t →
        d.label j < y.type.label (C t) →
        ∃ z, ∃ i ≤ y.type.toCellScheme.grade (C t),
          d.label j = visibilityReplace (y.type.toCellScheme.grade (C t)) i (y.type.label z)) ∧
      StageType.CarriesBottomsPerBlock y.type d (fun t ↦ y.type.toCellScheme.gradedIndex (C t))
        (fun t ↦ y.type.label (C t)) L

variable (R) in
/-- A realization **acquires per-block contexts**: over every occurrence `x`, for every coface `d`
of its type and every floor below the stage, it has a per-block carrying context
(`HasCarryingPerBlockContext`). -/
def AcquiresPerBlockContexts : Prop :=
  ∀ (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1)), d ∈ x.type.cofaces →
    ∀ γ : Ordinal.{u}, γ < α → HasCarryingPerBlockContext x d γ

/-- **A per-block coupled gated extension makes a context per-block carrying**: a context of the
form of `HasCarryingPerBlockContext`, without the bottom transport condition, at which a per-block
coupled gated extension exists whose caps carry the graded indices and labels of the cells `C t`
and read the sets `L t`, is a per-block carrying context
(`StageType.PerBlockCoupledGatedExtension.carriesBottomsPerBlock`).  So the condition is
necessary for the per-block route at that root, donor and floor. -/
theorem hasCarryingPerBlockContext_of_perBlockCoupledGatedExtension {x y : R.Occurrence}
    {d : StageType.{u} α (x.arity + 1)} {γ : Ordinal.{u}} {f : Fin x.arity ↪ Fin y.arity}
    {k : ℕ} {C : Fin k → Fin y.type.card} (hf : f.trans y.tuple = x.tuple)
    (hfp : StageType.restrictFace f y.type = some x.type) (hn : x.arity + 1 < y.arity)
    (E : StageType.PerBlockCoupledGatedExtension y.type f d k)
    (hX : ∀ t, E.capIndex t = y.type.toCellScheme.gradedIndex (C t))
    (hc : ∀ t, E.display.label (E.cap t) = y.type.label (C t))
    (hC : ∀ t, x.arity + 1 < y.type.toCellScheme.grade (C t) ∧
      (γ : Label.{u}) < y.type.label (C t) ∧ ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧
        ∀ l ∈ E.readLabels t, l < y.type.label (C t) →
          ∃ i : ℕ, l = ((μ + i : Ordinal.{u}) : Label.{u}))
    (hcov : ∀ j, Fin.last x.arity ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
      ∃ t, d.label j ∈ E.readLabels t)
    (hanc : ∀ t j, Fin.last x.arity ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
      d.label j ∈ E.readLabels t → d.label j < y.type.label (C t) →
      ∃ z, ∃ i ≤ y.type.toCellScheme.grade (C t),
        d.label j = visibilityReplace (y.type.toCellScheme.grade (C t)) i (y.type.label z)) :
    HasCarryingPerBlockContext x d γ := by
  have h := E.carriesBottomsPerBlock
  rw [show E.capIndex = fun t ↦ y.type.toCellScheme.gradedIndex (C t) from funext hX,
    show (fun t ↦ E.display.label (E.cap t)) = fun t ↦ y.type.label (C t) from funext hc] at h
  exact ⟨y, f, k, C, E.readLabels, hf, hfp, hn, hC, hcov, hanc, h⟩

/-! ### Acquisition from block-tight saturations -/

/-- **Caps for a list of blocks, from block-tight saturations**: over an occurrence `w` of a model,
for a floor `B` below the stage, a bound `Npad`, and a list of block starts, an occurrence `y`
containing `w` as a literal face with, for each listed block `μ`, a cell `G` of grade above `Npad`
labelled above `B` that reads, in its own block, every label of the type of `w` in the block of
`μ` not self-visible at the grade of `G`.  For each block, one dominance step padding the arity
past `Npad` gives a cell `T` of full grade labelled above `B`; saturation for the scheme that the
hypothesis gives over the result, and availability from the face
(`StageType.exists_le_label_of_restrictFace`), give `G` one grade below full labelled at least as
`T`; later steps keep `G` as a cell of a face (`StageType.exists_readsInOwnBlock_of_restrictFace`).
-/
theorem IsModel.exists_extend_blockCaps (hR : R.IsModel)
    (ht : StageType.HasBlockTightSaturations α) {B : Ordinal.{u}} (hB : B < α) (Npad : ℕ)
    (L : List Ordinal.{u}) (hL : ∀ μ ∈ L, Order.IsSuccPrelimit μ) (w : R.Occurrence) :
    ∃ (y : R.Occurrence) (g : Fin w.arity ↪ Fin y.arity), g.trans y.tuple = w.tuple ∧
      ∀ μ ∈ L, ∃ G : Fin y.type.card, Npad < y.type.toCellScheme.grade G ∧
        (B : Label.{u}) < y.type.label G ∧
        ∀ z : Fin w.type.card, ¬ IsSelfVisible (y.type.toCellScheme.grade G) (w.type.label z) →
          (∃ i : ℕ, w.type.label z = ((μ + i : Ordinal.{u}) : Label.{u})) →
          y.type.ReadsInOwnBlock G (w.type.label z) := by
  induction L generalizing w with
  | nil => exact ⟨w, Function.Embedding.refl _, rfl, by simp⟩
  | cons μ L ih =>
    obtain ⟨w', g₁, hg₁, hw', T, hT, hBT⟩ := hR.exists_extend_dominance w hB Npad
    obtain ⟨S, hS, htight⟩ :=
      ht w'.type (hR.isLegal _ _ w'.eval_tuple) μ (hL μ List.mem_cons_self)
    obtain ⟨u, hu, q, hqS, he⟩ := hR.saturation w' S hS
    have hqp : StageType.restrictFace Fin.castSuccEmb q = some w'.type := by
      rw [← hR.isConsistent u q _ he, hu, w'.eval_tuple]
    have hq : q ∈ w'.type.cofaces ∩ StageType.saturationFamily S :=
      ⟨⟨hR.isLegal _ _ he, hqp⟩, hqS⟩
    obtain ⟨G₀, hG₀, hTG⟩ :=
      StageType.exists_le_label_of_restrictFace (hR.isLegal _ _ he) hqp T
    rw [show w'.type.toCellScheme.grade T = w'.arity from congrArg Prod.snd hT] at hG₀
    obtain ⟨y, g₂, hg₂, hcaps⟩ :=
      ih (fun ν hν ↦ hL ν (List.mem_cons_of_mem _ hν)) ⟨_, u, q, he⟩
    have h₁ : (g₁.trans Fin.castSuccEmb).trans (⟨_, u, q, he⟩ : R.Occurrence).tuple =
        w.tuple := by
      rw [Function.Embedding.trans_assoc, hu, hg₁]
    obtain ⟨G, hGl, hGg, hGr⟩ := StageType.exists_readsInOwnBlock_of_restrictFace
      (Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hg₂) G₀
    refine ⟨y, (g₁.trans Fin.castSuccEmb).trans g₂, by
      rw [Function.Embedding.trans_assoc, hg₂]; exact h₁, fun ν hν ↦ ?_⟩
    rcases List.mem_cons.mp hν with rfl | hν
    · have hGgr : y.type.toCellScheme.grade G = w'.arity :=
        hGg.trans (congrArg Prod.snd hG₀)
      refine ⟨G, by rw [hGgr, hw']; omega, hBT.trans_le (hTG.trans_eq hGl.symm),
        fun z hzv hzμ ↦ ?_⟩
      obtain ⟨z', hz'⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hg₁ z
      rw [← hz'] at hzv hzμ ⊢
      rw [hGgr] at hzv
      exact hGr _ (htight q hq G₀ hG₀ z' hzv hzμ)
    · obtain ⟨G', hG'n, hG'B, hG'r⟩ := hcaps ν hν
      refine ⟨G', hG'n, hG'B, fun z hzv hzμ ↦ ?_⟩
      obtain ⟨z', hz'⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent h₁ z
      rw [← hz'] at hzv hzμ ⊢
      exact hG'r z' hzv hzμ

/-- **Per-block carrying contexts from block-tight saturations**: over every occurrence of a
model, for every donor and every floor below the stage, there is a per-block carrying context,
provided the named hypothesis on schemes `StageType.HasBlockTightSaturations α` holds.

Uniformity gives the reference cells of the donor's blocks, labelled at most a floor `B ≥ γ`, and
dominance pads the arity past their finite parts and the donor's
(`IsModel.exists_referenceCells`); then, block by block,
`IsModel.exists_extend_blockCaps` gives a cap one grade below full in its own step, labelled above
`B`, that reads the reference cell of its block in its own block.  Each new donor label in the block
of a cap and below it is `vr_K` of that reference label (`K` the grade of the cap), so the caps
carry (`StageType.carriesBottomsPerBlock_of_readsInOwnBlock`).  Of the clauses of a model it uses
uniformity, high-arity dominance, legality, exact consistency and generalized saturation. -/
theorem IsModel.hasCarryingPerBlockContext_of_hasBlockTightSaturations (hR : R.IsModel)
    (ht : StageType.HasBlockTightSaturations α) (x : R.Occurrence)
    (d : StageType.{u} α (x.arity + 1)) {γ : Ordinal.{u}} (hγ : γ < α) :
    HasCarryingPerBlockContext x d γ := by
  obtain ⟨w, f₁, -, B, μ, hf₁, hn, hγB, hBα, -, -, hμ, href⟩ := hR.exists_referenceCells x d hγ 0
  obtain ⟨y, f₃, hf₃, hcaps⟩ := hR.exists_extend_blockCaps ht hBα w.arity (List.ofFn μ)
    (fun ν hν ↦ by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hν; exact (hμ j).1) w
  choose C hCn hCB hCr using fun j : Fin d.card ↦ hcaps (μ j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hf : (f₁.trans f₃).trans y.tuple = x.tuple := by
    rw [Function.Embedding.trans_assoc, hf₃, hf₁]
  have hwy : w.arity ≤ y.arity := by simpa using Fintype.card_le_of_embedding f₃
  set Lset : Fin d.card → Set Label.{u} := fun t ↦
    {l | (∃ i < w.arity, l = ((μ t + i : Ordinal.{u}) : Label.{u})) ∨ y.type.label (C t) ≤ l}
  -- each donor label read below its cap is `vr_K` of a label that the cap reads in its block
  have hread : ∀ t j, d.label j ∈ Lset t → d.label j < y.type.label (C t) →
      ∃ l, (∃ k' ≤ y.type.toCellScheme.grade (C t),
        d.label j = visibilityReplace (y.type.toCellScheme.grade (C t)) k' l) ∧
        y.type.ReadsInOwnBlock (C t) l ∧ ∃ z : Fin y.type.card, y.type.label z = l := by
    intro t j hL hlt
    rcases hL with ⟨i, hi, hji⟩ | hle
    · obtain ⟨z, k, hk, hz, -⟩ := href t
      have hkC : k < y.type.toCellScheme.grade (C t) := by have := hCn t; omega
      obtain ⟨z', hz'⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₃ z
      refine ⟨w.type.label z, ⟨i, by have := hCn t; omega, ?_⟩,
        hCr t z (by rw [hz]; exact not_isSelfVisible_coe_add_natCast (hμ t).1 hkC) ⟨k, hz⟩,
        z', hz'⟩
      rw [hji, hz, visibilityReplace_coe_add_natCast (hμ t).1 hkC]
    · exact absurd hle (not_le_of_gt hlt)
  refine ⟨y, f₁.trans f₃, d.card, C, Lset, hf,
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hf, by omega,
    fun t ↦ ⟨by have := hCn t; omega,
      lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hγB)) (hCB t),
      μ t, (hμ t).1, fun l hl hlt ↦ ?_⟩, fun j _ hne ↦ ⟨j, ?_⟩, fun t j _ hne hL hlt ↦ ?_,
    StageType.carriesBottomsPerBlock_of_readsInOwnBlock fun t j _ hne hL hlt ↦ ?_⟩
  · rcases hl with ⟨i, -, rfl⟩ | hle
    · exact ⟨i, rfl⟩
    · exact absurd hle (not_le_of_gt hlt)
  · rcases atStage_iff.mp (d.atStage j) with h | ⟨o, -, h⟩ | h
    · exact absurd h hne
    · obtain ⟨i, hi, rfl⟩ := (hμ j).2 o h.symm
      exact .inl ⟨i, hi, h.symm⟩
    · exact .inr (h ▸ le_top)
  · obtain ⟨l, ⟨k', hk', hjl⟩, -, z, hz⟩ := hread t j hL hlt
    exact ⟨z, k', hk', hz ▸ hjl⟩
  · obtain ⟨l, hvr, hr, -⟩ := hread t j hL hlt
    exact ⟨l, hvr, hr⟩

/-- **Acquisition of per-block contexts from block-tight saturations**: a model acquires
per-block contexts, provided the named hypothesis on schemes `StageType.HasBlockTightSaturations α`
holds. -/
theorem IsModel.acquiresPerBlockContexts_of_hasBlockTightSaturations (hR : R.IsModel)
    (ht : StageType.HasBlockTightSaturations α) : R.AcquiresPerBlockContexts :=
  fun x d _ _ hγ ↦ hR.hasCarryingPerBlockContext_of_hasBlockTightSaturations ht x d hγ

end Realization

end VaughtConjecture
