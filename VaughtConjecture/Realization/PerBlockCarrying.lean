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

**Stated and compiled.**
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
  (`StageType.PerBlockCoupledGatedExtension.carriesBottomsPerBlock`).  At the level of
  realizations, a context at which such an extension exists is a per-block carrying context
  (`Realization.hasCarryingPerBlockContext_of_perBlockCoupledGatedExtension`).
* **The row condition** (compiled, sufficient, not necessary): the condition holds when each cap
  reads in its own block an anchor of every donor label below it that it reads
  (`StageType.carriesBottomsPerBlock_of_readsInOwnBlock`).  This is the form "for each block, a
  private cell whose row reads that block's anchors in its own block".  By the same-block lemma,
  each such cap reads labels of one block only.
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
* Every family of caps above `1` that reads both donor labels fails the per-block condition
  (`CoupledGatedExtensionCounterexample.not_carriesBottomsPerBlock`).
* Every family of caps of grade above `0 + 1` that reads both donor labels fails it
  (`CoupledGatedExtensionCounterexample.not_carriesBottomsPerBlock_of_one_lt_grade`).
* No per-block coupled gated extension reads both donor labels against caps above `1`
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

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-! ### Several gates, each with its own cap -/

/-- A **per-block coupled gated extension** of `P` on `n` points over the face `f`, with donor `d`
on `m + 1` points and `k` gates: a legal display on `n + 1` points whose two faces are literally
`P` and `d`, with, for each `t : Fin k`, a gate `gate t` and a cap `cap t`, a private cell of
graded index `capIndex t` in `P`; the twins of each gate read it at least as its cap
(`CellScheme.Rows.TwinsReadGate`), and the row of each gate reads, against its cap, the donor cells
whose labels lie in `readLabels t` (`CellScheme.Rows.IsGate`, whose clauses ask that cap and gate
have equal grades and nested scopes).  With one gate of graded index `(univ, n)`, a cap of graded
index `(univ, n)` in `P` and every label read, this is the data of `CoupledGatedExtension`.  Only
the clauses that the bottom transport condition uses are stated
(`PerBlockCoupledGatedExtension.carriesBottomsPerBlock`); no universal extension property for it
is stated. -/
structure PerBlockCoupledGatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) (k : ℕ) where
  /-- The display. -/
  display : StageType.{u} α (n + 1)
  /-- The display is legal. -/
  isLegal : display.IsLegal
  /-- The private face of the display is literally `P`. -/
  restrictFace_castSuccEmb : restrictFace Fin.castSuccEmb display = some P
  /-- The donor face of the display is literally `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast f) display = some d
  /-- The gates. -/
  gate : Fin k → Fin display.card
  /-- The caps, private cells of the display. -/
  cap : Fin k → Fin display.card
  /-- The graded index of each cap in the private type. -/
  capIndex : Fin k → Finset (Fin n) × ℕ
  /-- Each cap has the graded index `capIndex t` of the private type, on the private points. -/
  gradedIndex_cap : ∀ t, display.toCellScheme.gradedIndex (cap t) =
    ((capIndex t).1.map Fin.castSuccEmb, (capIndex t).2)
  /-- The labels of the donor cells that each gate reads. -/
  readLabels : Fin k → Set Label.{u}
  /-- The twins of each gate read the gate at least as its cap. -/
  twinsReadGate : ∀ t, display.rows.TwinsReadGate (gate t) (cap t)
  /-- The gate data: the row of each gate reads every donor cell whose label it reads. -/
  isGate : ∀ t, display.rows.IsGate (gate t) (cap t)
    (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    {e | e ∈ display.toCellScheme.visible (Set.range (extendByLast f)) ∧
      display.label e ∈ readLabels t} display.label

/-- The **per-block bottom transport condition** for a private type `P` on `n` points, a one-point
donor `d` on `m + 1` points, and `k` caps given by their graded indices `X t` and labels `c t`,
each with a set `L t` of donor labels that it reads: every lawful labelling `a` of `P` has one
lawful labelling `ρ` of `d` such that, for every `t` at which `a` is not `⊥` at the cells of `P` of
graded index `X t` labelled `c t`, at every new donor cell `j` not labelled `⊥` with label in
`L t`, the two clauses of `CarriesBottoms` hold with the cap label `c t` and visibility replacement
at the grade of `X t`.  With one cap of graded index `(univ, n)` reading every label it is
`CarriesBottoms` (`carriesBottomsPerBlock_one_iff`).  Every per-block coupled gated extension
forces it (`PerBlockCoupledGatedExtension.carriesBottomsPerBlock`). -/
def CarriesBottomsPerBlock (P : StageType.{u} α n) (d : StageType.{u} α (m + 1)) {k : ℕ}
    (X : Fin k → Finset (Fin n) × ℕ) (c : Fin k → Label.{u}) (L : Fin k → Set Label.{u}) :
    Prop :=
  ∀ a : Fin P.card → Label.{u}, P.rows.IsLawful a →
    ∃ ρ : Fin d.card → Label.{u}, d.rows.IsLawful ρ ∧ ∀ t,
      (∀ i, P.toCellScheme.gradedIndex i = X t → P.label i = c t → a i ≠ ⊥) →
      ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j ∈ L t →
        (¬ c t ≤ d.label j →
          (∀ i, ∀ k' ≤ (X t).2, d.label j = visibilityReplace (X t).2 k' (P.label i) →
            a i = ⊥) → ρ j = ⊥) ∧
        ((∀ i, ((∃ k' ≤ (X t).2, d.label j = visibilityReplace (X t).2 k' (P.label i)) ∨
            (c t ≤ P.label i ∧ c t ≤ d.label j)) → a i ≠ ⊥) → ρ j ≠ ⊥)

/-- **One cap of full scope and grade `k` reading every label: the bottom transport condition at
the grade `k`** (`CarriesBottomsAt`).  Forward, take the one cap; backward, where the private
labelling drops the cap the labelling of the donor itself serves. -/
theorem carriesBottomsPerBlock_one_iff_at {P : StageType.{u} α n}
    {d : StageType.{u} α (m + 1)} {c : Label.{u}} {k : ℕ} :
    CarriesBottomsPerBlock P d (fun _ : Fin 1 ↦ ((univ : Finset (Fin n)), k)) (fun _ ↦ c)
      (fun _ ↦ Set.univ) ↔ CarriesBottomsAt P d c k := by
  constructor
  · intro h a ha hcap
    obtain ⟨ρ, hρ, hj⟩ := h a ha
    exact ⟨ρ, hρ, fun j hj' hne ↦ hj 0 hcap j hj' hne trivial⟩
  · intro h a ha
    by_cases hcap : ∀ i, P.toCellScheme.gradedIndex i = (univ, k) → P.label i = c → a i ≠ ⊥
    · obtain ⟨ρ, hρ, hj⟩ := h a ha hcap
      exact ⟨ρ, hρ, fun _ _ j hj' hne _ ↦ hj j hj' hne⟩
    · exact ⟨d.label, d.isLawful, fun _ h ↦ absurd h hcap⟩

/-- **One cap of full scope and full grade reading every label: the bottom transport
condition.** -/
theorem carriesBottomsPerBlock_one_iff {P : StageType.{u} α n} {d : StageType.{u} α (m + 1)}
    {c : Label.{u}} :
    CarriesBottomsPerBlock P d (fun _ : Fin 1 ↦ ((univ : Finset (Fin n)), n)) (fun _ ↦ c)
      (fun _ ↦ Set.univ) ↔ CarriesBottoms P d c :=
  carriesBottomsPerBlock_one_iff_at.trans carriesBottomsAt_iff

/-- **The per-block condition holds at caps that read their anchors in their own block**: let
`C t` be cells of `P`, and suppose that every new donor label `l ∈ L t`, neither `⊥` nor at least
the label of `C t`, is `vr_K(l', k')`, `k' ≤ K` the grade of `C t`, for a label `l'` that the row
of `C t` reads in its own block (`ReadsInOwnBlock`).  Then a lawful labelling of `P` not `⊥` at
`C t` is not `⊥` at a cell labelled `l'`, a possible anchor, and the labelling of the donor itself
meets the condition.  By `eq_visibilityReplace_of_readsInOwnBlock`, the labels `l'` that one cap
reads in this way, below its label and not self-visible at its grade, lie in one block. -/
theorem carriesBottomsPerBlock_of_readsInOwnBlock {P : StageType.{u} α n}
    {d : StageType.{u} α (m + 1)} {k : ℕ} {C : Fin k → Fin P.card} {L : Fin k → Set Label.{u}}
    (hread : ∀ t j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j ∈ L t →
      d.label j < P.label (C t) →
      ∃ l, (∃ k' ≤ P.toCellScheme.grade (C t),
        d.label j = visibilityReplace (P.toCellScheme.grade (C t)) k' l) ∧
        P.ReadsInOwnBlock (C t) l) :
    CarriesBottomsPerBlock P d (fun t ↦ P.toCellScheme.gradedIndex (C t)) (fun t ↦ P.label (C t))
      L := by
  intro a ha
  refine ⟨d.label, d.isLawful, fun t hcap j hj hne hL ↦ ⟨fun hlt hdrop ↦ ?_, fun _ ↦ hne⟩⟩
  obtain ⟨l, ⟨k', hk', hjl⟩, hl⟩ := hread t j hj hne hL (lt_of_not_ge hlt)
  obtain ⟨z, hzl, hz⟩ := hl.exists_ne_bot ha (hcap (C t) rfl rfl)
  exact (hz (hdrop z k' hk' (hzl ▸ hjl))).elim

namespace PerBlockCoupledGatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)} {k : ℕ}
  (E : PerBlockCoupledGatedExtension P f d k)

/-- **Every per-block coupled gated extension forces the per-block bottom transport condition**
for its private type, its donor, and its caps with the labels they read.  The proof of
`CoupledGatedExtension.carriesBottoms`, gate by gate: a lawful labelling of `P` extends to a lawful
labelling `r` of the display (bountifulness at the cap `⊥`); where `r` is not `⊥` at the cap of
`t`, it is not `⊥` at the gate of `t` (the twin–gate coupling), and the readings of that gate carry
`⊥` from the anchors (`CellScheme.Rows.IsLawful.eq_bot_of_gateReads`,
`CellScheme.Rows.IsLawful.ne_bot_of_gateReads`); the donor face of `r` is one labelling of `d` for
all gates at once. -/
theorem carriesBottomsPerBlock :
    CarriesBottomsPerBlock P d E.capIndex (fun t ↦ E.display.label (E.cap t)) E.readLabels := by
  obtain ⟨hfP, hP⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_castSuccEmb
  obtain ⟨hfd, hd⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_extendByLast
  suffices key : CarriesBottomsPerBlock (E.display.comap Fin.castSuccEmb hfP)
      (E.display.comap (extendByLast f) hfd) E.capIndex (fun t ↦ E.display.label (E.cap t))
      E.readLabels by
    rw [hP, hd] at key; exact key
  intro a ha
  obtain ⟨r, hr, -, hra⟩ := Scheme.IsLegal.exists_isLawful_extend E.isLegal hfP
    (isSelfVisible_bot (n + 1)) ha CellScheme.Rows.isLawful_const_bot
    fun _ ↦ by simp only [min_bot_right]
  -- The private cells are the cells of the private face.
  have hpriv : ∀ z ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb),
      ∃ i, E.display.toScheme.cellMap Fin.castSuccEmb i = z := fun z hz ↦ by
    have : z ∈ Set.range (E.display.toScheme.cellMap Fin.castSuccEmb) := by
      rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]; exact hz
    exact this
  refine ⟨fun j ↦ r (E.display.toScheme.cellMap (extendByLast f) j),
    hr.comap (E.display.toScheme.isLowerEmbedding_comap _), fun t hcapa j hj hjb hjL ↦ ?_⟩
  -- The cap of `t` is the private cell of graded index `capIndex t` labelled as it.
  have hcap : r (E.cap t) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := hpriv (E.cap t) (E.isGate t).cap_mem
    have hgi : (E.display.comap Fin.castSuccEmb hfP).toCellScheme.gradedIndex i =
        E.capIndex t := by
      have h := E.display.toScheme.map_comap_gradedIndex Fin.castSuccEmb i
      rw [hi, E.gradedIndex_cap t] at h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      exact Prod.ext ((Finset.map_injective _) h1) h2
    rw [← hi, hra i]
    refine hcapa i hgi ?_
    -- The labels of the private face are those of its cells (`comap_label`, by definition).
    change E.display.label (E.display.toScheme.cellMap Fin.castSuccEmb i) = _
    rw [hi]
  have hG : r (E.gate t) ≠ ⊥ := fun h ↦ hcap (le_bot_iff.mp (h ▸
    CellScheme.Rows.cap_le_gate_of_twinsReadGate hr (E.isGate t).scope_cap_subset
      (E.isGate t).grade_cap (E.twinsReadGate t)))
  have hgr : E.display.toCellScheme.grade (E.gate t) = (E.capIndex t).2 :=
    (E.isGate t).grade_cap.symm.trans (congrArg Prod.snd (E.gradedIndex_cap t))
  set e := E.display.toScheme.cellMap (extendByLast f) j
  have he : e ∈ E.display.toCellScheme.visible (Set.range (extendByLast f)) :=
    Scheme.mem_visibleCells.mp (E.display.toScheme.cellMap_mem _ j)
  have hnew : Fin.last n ∈ E.display.toCellScheme.scope e := by
    -- The scope of a cell of the donor face is the preimage of the scope of its cell
    -- (`Scheme.comap_scope`, by definition).
    have hj' : Fin.last m ∈ (E.display.toCellScheme.scope e).preimage (extendByLast f)
        (extendByLast f).injective.injOn := hj
    simpa using mem_preimage.mp hj'
  have hle : E.display.label e = (E.display.comap (extendByLast f) hfd).label j := rfl
  have heP : e ∉ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb) := fun h ↦ by
    obtain ⟨i, hi⟩ := h hnew
    exact (Fin.castSucc_lt_last i).ne hi
  have hreads := (E.isGate t).reads e ⟨he, hle ▸ hjL⟩ heP
  refine ⟨fun hCe hanc ↦ hr.eq_bot_of_gateReads hG hreads (hle ▸ hjb) (hle ▸ hCe)
      fun z hz i hi hez ↦ ?_,
    fun hanc ↦ hr.ne_bot_of_gateReads hG hreads (hle ▸ hjb) fun z hz hez ↦ ?_⟩
  · obtain ⟨i', hi'⟩ := hpriv z.1 hz
    rw [← hi', hra i']
    rw [hgr, ← hi'] at hez
    rw [hgr] at hi
    exact hanc i' i hi hez
  · obtain ⟨i', hi'⟩ := hpriv z.1 hz
    rw [← hi', hra i']
    rw [hgr, ← hi'] at hez
    exact hanc i' hez

end PerBlockCoupledGatedExtension

/-! ### Readings in the own block in a larger type -/

/-- **A face keeps its readings in the own block**: if `p` is the face of `q` along `f`, every
cell `C` of `p` is a cell of `q` with the label and the grade of `C` that reads, in its own block,
every label that `C` reads in its own block (the rows of a face are the rows of its cells). -/
theorem exists_readsInOwnBlock_of_restrictFace {p : StageType.{u} α m} {q : StageType.{u} α n}
    {f : Fin m ↪ Fin n} (h : restrictFace f q = some p) (C : Fin p.card) :
    ∃ C' : Fin q.card, q.label C' = p.label C ∧
      q.toCellScheme.grade C' = p.toCellScheme.grade C ∧
      ∀ l, p.ReadsInOwnBlock C l → q.ReadsInOwnBlock C' l := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp h
  refine ⟨q.cellMap f C, rfl, rfl, fun l ⟨z, hz, hzl, μ, hμ, i, i', hrz, hrC⟩ ↦
    ⟨q.cellMap f z, ((q.toScheme.isLowerEmbedding_comap f).le_iff z C).mpr hz, hzl, μ, hμ, i, i',
      hrz, hrC⟩⟩

/-- **The self-reading of a cell labelled beyond a label that it reads in its own block**: let the
row of `C` read, in its own block `[μ, μ + ω)`, the label `l` of a cell `z` below it at the finite
part `i` and `C` itself at the finite part `i'`, with `l` below the label of `C` and not
self-visible at the grade `K` of `C`.  If `i' ≤ K`, the label of `C` is at most `vr_K(l, i')`,
that is, within the block of `l`.  So a cap labelled beyond the block of a label that it reads in
its own block reads itself at a finite part above its grade.  The proof uses the locality clause
of the lawfulness of the labels of `P` at `C`: its witness sends the reading of `z` to `l` and
commutes with visibility replacement at `K`. -/
theorem label_le_of_readsInOwnBlock {P : StageType.{u} α n} {C : Fin P.card} {l : Label.{u}}
    (h : P.ReadsInOwnBlock C l) (hl : l < P.label C)
    (hv : ¬ IsSelfVisible (P.toCellScheme.grade C) l) :
    ∃ z, ∃ hz : z ∈ P.toCellScheme.below (P.toCellScheme.gradedIndex C), P.label z = l ∧
      ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ i i' : ℕ,
      P.rows.row C ⟨z, hz⟩ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
      P.rows.row C ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩ =
        ((μ + i' : Ordinal.{u}) : Label.{u}) ∧
      (i' ≤ P.toCellScheme.grade C →
        P.label C ≤ visibilityReplace (P.toCellScheme.grade C) i' l) := by
  obtain ⟨z, hz, hzl, μ, hμ, i, i', hrz, hrC⟩ := h
  refine ⟨z, hz, hzl, μ, hμ, i, i', hrz, hrC, fun hi' ↦ ?_⟩
  obtain ⟨g, σ, hw, heq⟩ := P.isLawful.locality C
  set K := P.toCellScheme.grade C
  have hCg : P.label C ≤ g K := by
    have := heq ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩
    simp only [min_self] at this
    rw [this]; exact min_le_right _ _
  have hCσ : P.label C ≤ σ ((μ + i' : Ordinal.{u}) : Label.{u}) := by
    have := heq ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩
    simp only [min_self] at this
    rw [this, ← hrC]; exact min_le_left _ _
  have hσz : σ ((μ + i : Ordinal.{u}) : Label.{u}) = l := by
    have hgy : g K ≤ g (P.toCellScheme.grade z) :=
      hw.antitone ((CellScheme.mem_below _).mp hz).2
    have := heq ⟨z, hz⟩
    simp only [hzl, min_eq_left hl.le] at this
    rcases min_eq_iff.mp this.symm with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [← hrz]; exact h1
    · exact absurd (h1 ▸ hl.trans_le (hCg.trans hgy)) (lt_irrefl _)
  have hiK : i < K := by
    by_contra hKk
    have hc := hw.visibilityReplace_comm ((μ + i : Ordinal.{u}) : Label.{u}) K
      (hσz ▸ hl.le.trans hCg) K le_rfl
    rw [isSelfVisible_coe_add hμ (not_lt.mp hKk), hσz] at hc
    exact hv hc.symm
  have hc := hw.visibilityReplace_comm ((μ + i : Ordinal.{u}) : Label.{u}) K
    (hσz ▸ hl.le.trans hCg) i' hi'
  rw [visibilityReplace_coe_add_natCast hμ hiK i', hσz] at hc
  exact hCσ.trans_eq hc

/-! ### The finite hypothesis, one block at a time -/

variable (α) in
/-- **Block-tight saturations** (a named hypothesis on stage types and schemes, not on models):
over every legal stage type `p` on `N` points and every block start `μ` (zero or a limit), there
is a scheme `S` on `N + 1` points with a coface of `p` such that, in every coface of `p` on `S`,
every cell of graded index `(univ, N)` reads, in its own block, every label of `p` in the block
`[μ, μ + ω)` that is not self-visible at `N`.  It is `StageType.HasTightSaturations` restricted to
the labels of one block (`HasTightSaturations.hasBlockTightSaturations`); the refutation of the
latter above `ω` (`Realization.IsModel.not_hasTightSaturations`) reads two blocks at one cell, and
does not apply. -/
def HasBlockTightSaturations : Prop :=
  ∀ {N : ℕ} (p : StageType.{u} α N), p.IsLegal → ∀ μ : Ordinal.{u}, Order.IsSuccPrelimit μ →
    ∃ S : Scheme.{u} (N + 1), (p.cofaces ∩ saturationFamily S).Nonempty ∧
      ∀ q ∈ p.cofaces ∩ saturationFamily S, ∀ G : Fin q.card,
        q.toCellScheme.gradedIndex G = (univ, N) →
        ∀ z : Fin p.card, ¬ IsSelfVisible N (p.label z) →
          (∃ i : ℕ, p.label z = ((μ + i : Ordinal.{u}) : Label.{u})) →
          q.ReadsInOwnBlock G (p.label z)

/-- Tight saturations give block-tight saturations. -/
theorem HasTightSaturations.hasBlockTightSaturations (h : HasTightSaturations α) :
    HasBlockTightSaturations α := fun p hp _ _ ↦
  let ⟨S, hS, ht⟩ := h p hp
  ⟨S, hS, fun q hq G hG z hz _ ↦ ht q hq G hG z hz⟩

end StageType

namespace CoupledGatedExtensionCounterexample

open StageType

/-- **The refuting input of the coupled property fails the per-block condition** for every family
of caps in which one cap labelled above `1` reads the donor label `1` and one cap labelled above
`1` reads the donor label `⊤`.  The lawful labelling `⊥, ⊥, ⊥, ω + 1, ω + 2` keeps every cell
labelled above `1` and drops the only possible anchor `z₁` of `e₁`, so the condition asks for a
lawful labelling of the donor `⊥` at `e₁` and not at `e₂`, which the donor's rows forbid
(`eq_bot_of_isLawful_donor`).  The donor's proper labels lie in one block, so here one gate per
block is one gate. -/
theorem not_carriesBottomsPerBlock (α : Ordinal.{u}) (hα : 1 < α) {k : ℕ}
    {X : Fin k → Finset (Fin 2) × ℕ} {c : Fin k → Label.{u}} {L : Fin k → Set Label.{u}}
    {t₁ t₂ : Fin k} (h₁ : (1 : Label.{u}) ∈ L t₁) (hc₁ : (1 : Label.{u}) < c t₁)
    (h₂ : (⊤ : Label.{u}) ∈ L t₂) (hc₂ : (1 : Label.{u}) < c t₂) :
    ¬ CarriesBottomsPerBlock (P α hα) (donor α hα) X c L := by
  intro H
  obtain ⟨ρ, hρ, hj⟩ := H (lab ⊥ (omegaAdd 1) (omegaAdd 2)) isLawful_lab_bot_omegaAdd
  have h1top : (1 : Label.{u}) ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hc₁ le_top)
  -- A cap labelled above `1` is labelled `⊤`, at a cell that the labelling keeps.
  have hkeep : ∀ t, (1 : Label.{u}) < c t → ∀ i, (P α hα).toCellScheme.gradedIndex i = X t →
      (P α hα).label i = c t → lab ⊥ (omegaAdd 1) (omegaAdd 2) i ≠ ⊥ := by
    intro t ht i _ hi
    -- The labels of the private type are `lab 1 ⊤ ⊤` (`P`, by definition).
    change lab 1 ⊤ ⊤ i = c t at hi
    fin_cases i
    · exact absurd (hi ▸ ht) not_lt_bot
    · exact absurd (hi ▸ ht) not_lt_bot
    · exact absurd (hi ▸ ht) (lt_irrefl _)
    · exact WithBot.coe_ne_bot
    · exact WithBot.coe_ne_bot
  have h0 : ρ (0 : Fin 2) = ⊥ := by
    refine (hj t₁ (hkeep t₁ hc₁) (0 : Fin 2) (Finset.mem_univ _)
      (by change (1 : Label.{u}) ≠ ⊥; simp) h₁).1 (not_le_of_gt hc₁) fun i k' _ hik ↦ ?_
    -- The labels of the private type and of the donor are `lab 1 ⊤ ⊤` and `donorLab 1 ⊤`.
    change (1 : Label.{u}) = visibilityReplace _ k' (lab 1 ⊤ ⊤ i) at hik
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact absurd (hik.trans (visibilityReplace_top _ _)) h1top
    · exact absurd (hik.trans (visibilityReplace_top _ _)) h1top
  have h1 : ρ (1 : Fin 2) ≠ ⊥ := by
    refine (hj t₂ (hkeep t₂ hc₂) (1 : Fin 2) (Finset.mem_univ _)
      (by change (⊤ : Label.{u}) ≠ ⊥; simp) h₂).2 fun i hi ↦ ?_
    -- The labels of the private type and of the donor are `lab 1 ⊤ ⊤` and `donorLab 1 ⊤`.
    change (∃ k' ≤ (X t₂).2, (⊤ : Label.{u}) = visibilityReplace _ k' (lab 1 ⊤ ⊤ i)) ∨
      (c t₂ ≤ lab 1 ⊤ ⊤ i ∧ c t₂ ≤ ⊤) at hi
    fin_cases i
    · rcases hi with ⟨k', -, hk⟩ | ⟨hle, -⟩
      · change (⊤ : Label.{u}) = visibilityReplace _ k' ⊥ at hk; simp at hk
      · exact absurd (lt_of_lt_of_le hc₂ hle) not_lt_bot
    · rcases hi with ⟨k', -, hk⟩ | ⟨hle, -⟩
      · change (⊤ : Label.{u}) = visibilityReplace _ k' ⊥ at hk; simp at hk
      · exact absurd (lt_of_lt_of_le hc₂ hle) not_lt_bot
    · rcases hi with ⟨k', -, hk⟩ | ⟨hle, -⟩
      · change (⊤ : Label.{u}) = visibilityReplace _ k' 1 at hk
        exact absurd (visibilityReplace_eq_top_iff.mp hk.symm) h1top
      · exact absurd (lt_of_lt_of_le hc₂ hle) (lt_irrefl _)
    · exact WithBot.coe_ne_bot
    · exact WithBot.coe_ne_bot
  exact h1 (eq_bot_of_isLawful_donor hρ h0)

/-- **The refuting private type has no per-block caps above the root's arity plus one**: every
family of cells of `P α` of grade above `0 + 1`, in which some cell reads the donor label `1` and
some cell reads the donor label `⊤`, fails the per-block condition.  The only cell of grade `2` is
the full cell, labelled `⊤` (`not_carriesBottomsPerBlock`).  So the refuting input is not a
per-block carrying private type at any floor. -/
theorem not_carriesBottomsPerBlock_of_one_lt_grade (α : Ordinal.{u}) (hα : 1 < α) {k : ℕ}
    {C : Fin k → Fin (P α hα).card} {L : Fin k → Set Label.{u}}
    (hC : ∀ t, 0 + 1 < (P α hα).toCellScheme.grade (C t)) {t₁ t₂ : Fin k}
    (h₁ : (1 : Label.{u}) ∈ L t₁) (h₂ : (⊤ : Label.{u}) ∈ L t₂) :
    ¬ CarriesBottomsPerBlock (P α hα) (donor α hα)
      (fun t ↦ (P α hα).toCellScheme.gradedIndex (C t)) (fun t ↦ (P α hα).label (C t)) L := by
  -- A cell of grade above `1` is the full cell `4`, labelled `⊤` (`P`, by definition).
  have key : ∀ i : Fin 5, 0 + 1 < cellGrade i → (1 : Label.{u}) < lab 1 ⊤ ⊤ i := by
    intro i h
    fin_cases i <;> simp [cellGrade] at h
    change (1 : Label.{u}) < ⊤
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  have htop : ∀ t, (1 : Label.{u}) < (P α hα).label (C t) := fun t ↦ key (C t) (hC t)
  exact not_carriesBottomsPerBlock α hα h₁ (htop t₁) h₂ (htop t₂)

/-- **The refuting input fails the bottom transport condition at the grade `1`**: no cap label
above `1` at the cells of graded index `(univ, 1)` carries the bottoms there (the subfull cap of
`Realization/TightCap`, one grade below the full grade `2`).  This is at `N = 1` over the empty
root, where `Realization.HasCarryingSubfullContext` requires `x.arity + 1 < N`, which is false; so
it refutes the bottom transport condition `StageType.CarriesBottomsAt` at the subfull grade, not a
subfull carrying context.  It is `not_carriesBottomsPerBlock`
with one cap of graded index `(univ, 1)` reading every label
(`carriesBottomsPerBlock_one_iff_at`). -/
theorem not_carriesBottomsAt_one (α : Ordinal.{u}) (hα : 1 < α) {c : Label.{u}}
    (hc : (1 : Label.{u}) < c) : ¬ (P α hα).CarriesBottomsAt (donor α hα) c 1 := fun h ↦
  not_carriesBottomsPerBlock α hα (t₁ := 0) (t₂ := 0) (Set.mem_univ _) hc (Set.mem_univ _) hc
    (carriesBottomsPerBlock_one_iff_at.mpr h)

/-- **The refuting input has no per-block coupled gated extension reading the donor above `1`**:
over the empty root, no per-block coupled gated extension of `P α` with the donor has a gate that
reads the donor label `1` and a gate that reads the donor label `⊤`, both against caps labelled
above `1` (`PerBlockCoupledGatedExtension.carriesBottomsPerBlock`, `not_carriesBottomsPerBlock`).
So one gate per block does not remove the obstruction of the coupled property at this input, whose
donor has its proper labels in one block. -/
theorem not_perBlockCoupledGatedExtension (α : Ordinal.{u}) (hα : 1 < α) {f : Fin 0 ↪ Fin 2}
    {k : ℕ} (E : PerBlockCoupledGatedExtension (P α hα) f (donor α hα) k) {t₁ t₂ : Fin k}
    (h₁ : (1 : Label.{u}) ∈ E.readLabels t₁) (hc₁ : (1 : Label.{u}) < E.display.label (E.cap t₁))
    (h₂ : (⊤ : Label.{u}) ∈ E.readLabels t₂)
    (hc₂ : (1 : Label.{u}) < E.display.label (E.cap t₂)) : False :=
  not_carriesBottomsPerBlock α hα h₁ hc₁ h₂ hc₂ E.carriesBottomsPerBlock

end CoupledGatedExtensionCounterexample

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

Uniformity gives the reference cells of the donor's blocks, labelled at most a floor `B ≥ γ`; a
dominance step pads the arity past their finite parts and the donor's; then, block by block,
`IsModel.exists_extend_blockCaps` gives a cap one grade below full in its own step, labelled above
`B`, that reads the reference cell of its block in its own block.  Each new donor label in the block
of a cap and below it is `vr_K` of that reference label (`K` the grade of the cap), so the caps
carry (`StageType.carriesBottomsPerBlock_of_readsInOwnBlock`).  Of the clauses of a model it uses
uniformity, high-arity dominance, legality, exact consistency and generalized saturation. -/
theorem IsModel.hasCarryingPerBlockContext_of_hasBlockTightSaturations (hR : R.IsModel)
    (ht : StageType.HasBlockTightSaturations α) (x : R.Occurrence)
    (d : StageType.{u} α (x.arity + 1)) {γ : Ordinal.{u}} (hγ : γ < α) :
    HasCarryingPerBlockContext x d γ := by
  -- the block start and a bound on the finite part of each label of the donor
  have hblock (j : Fin d.card) : ∃ μ : Ordinal.{u}, (Order.IsSuccPrelimit μ ∧ μ < α) ∧
      ∃ D : ℕ, ∀ o : Ordinal.{u}, d.label j = o → ∃ i < D, o = μ + i := by
    rcases atStage_iff.mp (d.atStage j) with h | ⟨o, ho, h⟩ | h
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, zero_le.trans_lt hγ⟩, 0,
        fun o ho ↦ by simp [h] at ho⟩
    · obtain ⟨i, hi⟩ := Ordinal.exists_eq_add_natCast_of_le_of_lt_add_omega0
        (Ordinal.mul_div_le o Ordinal.omega0)
        (Ordinal.lt_mul_div_add o Ordinal.omega0_ne_zero)
      refine ⟨Ordinal.omega0 * (o / Ordinal.omega0),
        ⟨Ordinal.isSuccPrelimit_iff_omega0_dvd.mpr (dvd_mul_right _ _),
          (Ordinal.mul_div_le o Ordinal.omega0).trans_lt ho⟩,
        i + 1, fun o' ho' ↦ ⟨i, i.lt_succ_self, ?_⟩⟩
      rw [← h] at ho'
      exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hi
    · exact ⟨0, ⟨Ordinal.isSuccPrelimit_zero, zero_le.trans_lt hγ⟩, 0,
        fun o ho ↦ by simp [h] at ho⟩
  choose μ hμ D hD using hblock
  obtain ⟨y₁, f₁, K, B, hf₁, hγB, hBα, hanc⟩ :=
    hR.exists_extend_uniformity x hγ (List.ofFn μ) fun ν hν ↦ by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hν
      exact hμ j
  obtain ⟨w, f₂, hf₂, hw, -⟩ := hR.exists_extend_dominance y₁ hBα (x.arity + 1 + K + univ.sup D)
  obtain ⟨y, f₃, hf₃, hcaps⟩ := hR.exists_extend_blockCaps ht hBα (x.arity + 1 + K + univ.sup D)
    (List.ofFn μ) (fun ν hν ↦ by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hν; exact (hμ j).1) w
  choose C hCn hCB hCr using fun j : Fin d.card ↦ hcaps (μ j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hf : ((f₁.trans f₂).trans f₃).trans y.tuple = x.tuple := by
    rw [Function.Embedding.trans_assoc, hf₃, Function.Embedding.trans_assoc, hf₂, hf₁]
  have hwy : w.arity ≤ y.arity := by simpa using Fintype.card_le_of_embedding f₃
  -- the reference cell of each block, as a cell of `w`
  have href (t : Fin d.card) : ∃ z : Fin w.type.card, ∃ k < K,
      w.type.label z = ((μ t + k : Ordinal.{u}) : Label.{u}) := by
    obtain ⟨z₁, k, hk, hz₁, -⟩ := hanc (μ t) (List.mem_ofFn.mpr ⟨t, rfl⟩)
    obtain ⟨z, hz⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₂ z₁
    exact ⟨z, k, hk, hz.trans hz₁⟩
  have hDle (j : Fin d.card) : D j ≤ univ.sup D := le_sup (mem_univ j)
  set Lset : Fin d.card → Set Label.{u} := fun t ↦
    {l | (∃ i < univ.sup D, l = ((μ t + i : Ordinal.{u}) : Label.{u})) ∨ y.type.label (C t) ≤ l}
  -- each donor label read below its cap is `vr_K` of a label that the cap reads in its block
  have hread : ∀ t j, d.label j ∈ Lset t → d.label j < y.type.label (C t) →
      ∃ l, (∃ k' ≤ y.type.toCellScheme.grade (C t),
        d.label j = visibilityReplace (y.type.toCellScheme.grade (C t)) k' l) ∧
        y.type.ReadsInOwnBlock (C t) l ∧ ∃ z : Fin y.type.card, y.type.label z = l := by
    intro t j hL hlt
    rcases hL with ⟨i, hi, hji⟩ | hle
    · obtain ⟨z, k, hk, hz⟩ := href t
      have hkC : k < y.type.toCellScheme.grade (C t) := by have := hCn t; omega
      obtain ⟨z', hz'⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₃ z
      refine ⟨w.type.label z, ⟨i, by have := hCn t; omega, ?_⟩,
        hCr t z (by rw [hz]; exact not_isSelfVisible_coe_add_natCast (hμ t).1 hkC) ⟨k, hz⟩,
        z', hz'⟩
      rw [hji, hz, visibilityReplace_coe_add_natCast (hμ t).1 hkC]
    · exact absurd hle (not_le_of_gt hlt)
  refine ⟨y, (f₁.trans f₂).trans f₃, d.card, C, Lset, hf,
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
    · obtain ⟨i, hi, rfl⟩ := hD j o h.symm
      exact .inl ⟨i, hi.trans_le (hDle j), h.symm⟩
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
