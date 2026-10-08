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
cell (`StageType.ReadsInOwnBlock.exists_ne_bot`).  A cap **reads the donor's anchors in its own
block** when every donor label below the cap is a visibility replacement of a label that the cap
reads in its own block; such a cap carries the bottoms (`StageType.carriesBottoms_of_row_mem_block`,
and at any grade `StageType.carriesBottomsAt_of_readsInOwnBlock`).  A cap is **tight** (over a
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
which a model exists (`Realization.IsModel.not_hasTightSaturations`).  Argued, not compiled: at a
private context whose arity exceeds the finite parts of the donor's labels, every proper donor
label below the cap is not self-visible at the cap's grade, and neither is its anchor; so reading
anchors in the cap's own block can serve only donors whose proper labels below the cap lie in one
block.  The identified obstruction survives the redesigns examined (the cap of full grade and the
subfull cap below); it says nothing about other ways to obtain `StageType.CarriesBottoms`.

**At full grade, no clause of a model asks for a tight cap.**  Compiled:
* Every nonempty instance of generalized saturation or of the bottom pattern has a member whose
  cells of full grade are all labelled `⊥`
  (`StageType.exists_mem_cofaces_inter_saturationFamily_label_eq_bot`,
  `StageType.exists_mem_cofaces_inter_bottomPatternFamily_label_eq_bot`), hence a member in no
  dominance family (`StageType.exists_mem_cofaces_inter_saturationFamily_not_mem_dominanceFamily`).
* A member of a dominance family need not carry the bottoms at its dominating cell
  (`CoupledGatedExtensionCounterexample.exists_mem_dominanceFamily_not_carriesBottoms`,
  the refuting input of the coupled property).  This refutes only the finite sufficient condition
  "every member of a dominance family carries", not the acquisition.
* A realization **has tight caps** (`Realization.HasTightCaps`) when over every occurrence and at
  every floor it realizes a member of the **tight cap family** (`StageType.tightCapFamily`, inside
  the dominance family): a coface with a tight cell of full grade above the floor.  A model with
  tight caps acquires carrying contexts
  (`Realization.IsModel.acquiresCarryingContexts_of_hasTightCaps`).  `HasTightCaps` is not a clause
  of `IsModel`; it is refuted for every model at every stage above `ω`
  (`Realization.IsModel.not_hasTightCaps`), so that conditional theorem is vacuous above `ω`, and
  it is open at stages at most `ω`.

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
  (`StageType.IsAnchoredAt`, and `StageType.CarriesBottomsAt` in `Extension/GatedExtension`; at
  `k = n` they are `IsAnchored` and `CarriesBottoms`, `StageType.isAnchoredAt_iff`,
  `StageType.carriesBottomsAt_iff`), and a carrying context with a subfull cap
  (`Realization.HasCarryingSubfullContext`).  A per-block coupled gated extension with one gate
  whose cap has graded index `(univ, k)` and reads every label forces `CarriesBottomsAt` at `k`
  (`StageType.PerBlockCoupledGatedExtension.carriesBottomsPerBlock` with
  `StageType.carriesBottomsPerBlock_one_iff_at`; the composite is not stated as a theorem);
* stated: **tight saturations** (`StageType.HasTightSaturations α`), a statement about legal stage
  types and schemes, not about models: over every legal `p` on `N` points, a legal one-point
  extension scheme with a coface of `p` whose cells of graded index `(univ, N)` are tight (read in
  their own block every label of `p` not self-visible at `N`).  It is false at every stage above
  `ω` at which a model exists (`Realization.IsModel.not_hasTightSaturations`, compiled) and
  undecided at stages at most `ω`;
* compiled: every model has, over every root, for every donor and every floor below the stage, a
  carrying context with a cap one grade below full, conditional on tight saturations
  (`Realization.IsModel.hasCarryingSubfullContext`); vacuous above `ω`.  Of the clauses of a model
  it uses uniformity, high-arity dominance, legality, exact consistency and generalized saturation.

**What is not claimed.**  `Realization.AcquiresCarryingContexts` and
`Realization.HasCarryingSubfullContext` are neither proved nor refuted for all models: the
refutations above concern only the two sufficient conditions `Realization.HasTightCaps` and
`StageType.HasTightSaturations`.  The two conditional theorems are kept although vacuous above `ω`;
retiring them is a separate change.  No extension property for a cap one grade below full is
defined, and the coupled property restricted to carrying contexts is not stated (prospective).
Nothing here is equivalent to (R1), and (R1) is neither proved nor refuted.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-! ### Saturation gives no lower bound on a label of full grade -/

/-- The stage type `q` with every cell of full grade relabelled `⊥`; lawful by
`CellScheme.Rows.IsLawful.capTopGrade` at the cap `⊥`. -/
noncomputable def botTopGrade (q : StageType.{u} α (n + 1)) : StageType.{u} α (n + 1) where
  toScheme := q.toScheme
  label i := if q.toCellScheme.grade i = n + 1 then ⊥ else q.label i
  isWellFormed := q.isWellFormed
  isCoded := q.isCoded
  isLawful := by
    simpa only [min_bot_right] using
      q.isLawful.capTopGrade q.grade_le (isSelfVisible_bot (n + 1))
  atStage i := by
    split_ifs
    · exact atStage_bot
    · exact q.atStage i

/-- Below full grade the labels of `botTopGrade` are those of `q`. -/
theorem botTopGrade_label_of_grade_le (q : StageType.{u} α (n + 1)) {i : Fin q.card}
    (hi : q.toCellScheme.grade i ≤ n) : q.botTopGrade.label i = q.label i := by
  -- `botTopGrade` labels by an `if` on the grade (by definition)
  change (if _ then _ else _) = _
  split_ifs with h
  · omega
  · rfl

/-- At full grade `botTopGrade` is labelled `⊥`. -/
theorem botTopGrade_label_of_grade_eq (q : StageType.{u} α (n + 1)) {i : Fin q.card}
    (hi : q.toCellScheme.grade i = n + 1) : q.botTopGrade.label i = ⊥ := by
  -- `botTopGrade` labels by an `if` on the grade (by definition)
  change (if _ then _ else _) = _
  split_ifs
  rfl

/-- Relabelling the cells of full grade `⊥` does not change the face along the initial segment. -/
theorem restrictFace_castSuccEmb_botTopGrade (q : StageType.{u} α (n + 1)) :
    restrictFace Fin.castSuccEmb q.botTopGrade = restrictFace Fin.castSuccEmb q := by
  by_cases hf : univ.map Fin.castSuccEmb ∈ q.toCellScheme.faces
  · rw [restrictFace_of_mem q.botTopGrade Fin.castSuccEmb hf, restrictFace_of_mem q _ hf]
    refine congrArg some (ext rfl fun i j hij ↦ ?_)
    have hgr : q.toCellScheme.grade (q.cellMap Fin.castSuccEmb i) ≤ n := by
      have h := congrArg Prod.snd (q.toScheme.map_comap_gradedIndex Fin.castSuccEmb i)
      exact h.symm.trans_le ((q.comap Fin.castSuccEmb hf).grade_le i)
    simp only [comap_label]
    rw [Fin.ext hij] at hgr ⊢
    exact q.botTopGrade_label_of_grade_le hgr
  · rw [restrictFace_of_notMem q.botTopGrade Fin.castSuccEmb hf, restrictFace_of_notMem q _ hf]

/-- **The bottom-pattern clause bounds no label of full grade from below**: every nonempty
instance of the bottom-pattern family among the cofaces of `p` has a member whose cells of full
grade are all labelled `⊥` (`botTopGrade`: the face and the bottom pattern below full grade are
unchanged). -/
theorem exists_mem_cofaces_inter_bottomPatternFamily_label_eq_bot {p : StageType.{u} α n}
    {S : Scheme.{u} (n + 1)} {ρ : Fin S.card → Label.{u}}
    (h : (p.cofaces ∩ bottomPatternFamily S ρ).Nonempty) :
    ∃ q ∈ p.cofaces ∩ bottomPatternFamily S ρ,
      ∀ i, q.toCellScheme.grade i = n + 1 → q.label i = ⊥ := by
  obtain ⟨q, ⟨hq, hqp⟩, hqS, hpat⟩ := h
  refine ⟨q.botTopGrade, ⟨⟨hq, (restrictFace_castSuccEmb_botTopGrade q).trans hqp⟩, hqS,
    fun i j hij hi ↦ ?_⟩, fun i ↦ q.botTopGrade_label_of_grade_eq⟩
  rw [q.botTopGrade_label_of_grade_le hi]
  exact hpat i j hij hi

/-- **The saturation clause bounds no label of full grade from below**: every nonempty instance
of generalized saturation among the cofaces of `p` has a member whose cells of full grade are all
labelled `⊥`. -/
theorem exists_mem_cofaces_inter_saturationFamily_label_eq_bot {p : StageType.{u} α n}
    {S : Scheme.{u} (n + 1)} (h : (p.cofaces ∩ saturationFamily S).Nonempty) :
    ∃ q ∈ p.cofaces ∩ saturationFamily S,
      ∀ i, q.toCellScheme.grade i = n + 1 → q.label i = ⊥ := by
  obtain ⟨q, hq, hqS⟩ := h
  exact ⟨q.botTopGrade, ⟨⟨hq.1, (restrictFace_castSuccEmb_botTopGrade q).trans hq.2⟩, hqS⟩,
    fun i ↦ q.botTopGrade_label_of_grade_eq⟩

/-- **A prescribed scheme does not meet a dominance family by force**: every nonempty instance of
generalized saturation among the cofaces of `p` has a member in no dominance family.  So no clause
of a model asks for a coface on a prescribed scheme with a label of full grade above a floor. -/
theorem exists_mem_cofaces_inter_saturationFamily_not_mem_dominanceFamily
    {p : StageType.{u} α n} {S : Scheme.{u} (n + 1)}
    (h : (p.cofaces ∩ saturationFamily S).Nonempty) :
    ∃ q ∈ p.cofaces ∩ saturationFamily S, ∀ γ : Ordinal.{u}, q ∉ dominanceFamily γ := by
  obtain ⟨q, hq, hbot⟩ := exists_mem_cofaces_inter_saturationFamily_label_eq_bot h
  refine ⟨q, hq, fun γ ⟨i, hi, hγi⟩ ↦ ?_⟩
  rw [hbot i hi] at hγi
  exact not_lt_bot hγi

/-! ### Availability from the face -/

/-- **Availability from the face**: in a legal stage type `q` on `n + 1` points whose face along
the initial segment is `p`, every cell `T` of `p` has a cell of `q` of full scope, with the grade
of `T`, labelled at least as `T`. -/
theorem exists_le_label_of_restrictFace {p : StageType.{u} α n} {q : StageType.{u} α (n + 1)}
    (hq : q.IsLegal) (h : restrictFace Fin.castSuccEmb q = some p) (T : Fin p.card) :
    ∃ G : Fin q.card, q.toCellScheme.gradedIndex G = (univ, p.toCellScheme.grade T) ∧
      p.label T ≤ q.label G := by
  obtain ⟨hf, rfl⟩ := (restrictFace_eq_some_iff _ _).mp h
  have hgi := q.toScheme.map_comap_gradedIndex Fin.castSuccEmb T
  have hgr : q.toCellScheme.grade (q.cellMap Fin.castSuccEmb T) =
      (q.comap Fin.castSuccEmb hf).toCellScheme.grade T := (congrArg Prod.snd hgi).symm
  obtain ⟨t, ht⟩ := hq.isComplete (univ, (q.comap Fin.castSuccEmb hf).toCellScheme.grade T)
    ⟨q.univ_mem_faces, (q.comap Fin.castSuccEmb hf).isWellFormed.isWellFormed.grade_pos T,
      ((q.comap Fin.castSuccEmb hf).grade_le T).trans (by simp)⟩
  obtain ⟨G, hG, hle⟩ := q.isLawful.availability (q.cellMap Fin.castSuccEmb T) t
    (by rw [show q.toCellScheme.scope t = univ from congrArg Prod.fst ht]; exact subset_univ _)
    (by rw [hgr, show q.toCellScheme.grade t = _ from congrArg Prod.snd ht])
  exact ⟨G, hG.trans ht, hle⟩

/-! ### Readings in the cap's own block, at a given grade -/

/-- The row of a cell `C` of `P` **reads a cell labelled `l` in its own block**: some cell `z`
below `C`, labelled `l`, is read by the row of `C` in the block `[μ, μ + ω)` (`μ` zero or a limit)
of its reading of `C` itself. -/
def ReadsInOwnBlock (P : StageType.{u} α n) (C : Fin P.card) (l : Label.{u}) : Prop :=
  ∃ z, ∃ hz : z ∈ P.toCellScheme.below (P.toCellScheme.gradedIndex C), P.label z = l ∧
    ∃ μ : Ordinal.{u}, Order.IsSuccPrelimit μ ∧ ∃ i i' : ℕ,
      P.rows.row C ⟨z, hz⟩ = ((μ + i : Ordinal.{u}) : Label.{u}) ∧
      P.rows.row C ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩ =
        ((μ + i' : Ordinal.{u}) : Label.{u})

/-- A lawful labelling not `⊥` at `C` is not `⊥` at a cell that the row of `C` reads, labelled
`l`, in its own block (`CellScheme.Rows.IsLawful.ne_bot_of_row_mem_block`). -/
theorem ReadsInOwnBlock.exists_ne_bot {P : StageType.{u} α n} {C : Fin P.card} {l : Label.{u}}
    (h : P.ReadsInOwnBlock C l) {a : Fin P.card → Label.{u}} (ha : P.rows.IsLawful a)
    (hC : a C ≠ ⊥) : ∃ z, P.label z = l ∧ a z ≠ ⊥ := by
  obtain ⟨z, hz, hzl, μ, hμ, i, i', hrz, hrC⟩ := h
  exact ⟨z, hzl, ha.ne_bot_of_row_mem_block hz hμ hrz hrC hC⟩

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

/-- The donor `d` is **anchored at the grade `k`** in `P` below the cell `C`: every new donor cell
whose label is neither `⊥` nor at least that of `C` is labelled `vr_k(P.label z, i)` for a cell
`z` of `P` and some `i ≤ k`.  At `k = n` this is `IsAnchored` (`isAnchoredAt_iff`); a design with
the gate at grade `k` reads the donor through visibility replacement at `k`. -/
def IsAnchoredAt (P : StageType.{u} α n) (C : Fin P.card) (k : ℕ)
    (d : StageType.{u} α (m + 1)) : Prop :=
  ∀ j : Fin d.card, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j < P.label C →
    ∃ z : Fin P.card, ∃ i ≤ k, d.label j = visibilityReplace k i (P.label z)

/-- Anchoring at the arity is `IsAnchored`. -/
theorem isAnchoredAt_iff {P : StageType.{u} α n} {C : Fin P.card} {d : StageType.{u} α (m + 1)} :
    IsAnchoredAt P C n d ↔ IsAnchored P C d :=
  Iff.rfl

/-- **The bottom transport condition at the grade `k` holds at a cap that reads the donor's
anchors in its own block**: let `C` be a cell of graded index `(univ, k)` of `P`, and suppose
every new donor label neither `⊥` nor at least the label of `C` is `vr_k(l, k')`, `k' ≤ k`, for a
label `l` that the row of `C` reads in its own block.
Then a lawful labelling of `P` not `⊥` at `C` is not `⊥` at a cell labelled `l`, which is a
possible anchor, and the labelling of the donor itself meets the condition.  At `k = n` this is
`carriesBottoms_of_row_mem_block`, with the anchor given by its label. -/
theorem carriesBottomsAt_of_readsInOwnBlock {P : StageType.{u} α n}
    {d : StageType.{u} α (m + 1)} {C : Fin P.card} {k : ℕ}
    (hC : P.toCellScheme.gradedIndex C = (univ, k))
    (hread : ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ → d.label j < P.label C →
      ∃ l, (∃ k' ≤ k, d.label j = visibilityReplace k k' l) ∧ P.ReadsInOwnBlock C l) :
    CarriesBottomsAt P d (P.label C) k := by
  intro a ha hcap
  refine ⟨d.label, d.isLawful, fun j hj hne ↦ ⟨fun hlt hdrop ↦ ?_, fun _ ↦ hne⟩⟩
  obtain ⟨l, ⟨k', hk', hjl⟩, hl⟩ := hread j hj hne (lt_of_not_ge hlt)
  obtain ⟨z, hzl, hz⟩ := hl.exists_ne_bot ha (hcap C hC rfl)
  exact (hz (hdrop z k' hk' (hzl ▸ hjl))).elim

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

/-! ### Readings in the own block lie in one block -/

/-- The block start of a label `μ + i` (`μ` zero or a limit, `i` finite) is determined by the
label. -/
private theorem eq_of_coe_add_natCast_eq {μ μ' : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ)
    (hμ' : Order.IsSuccPrelimit μ') {i j : ℕ}
    (h : ((μ + i : Ordinal.{u}) : Label.{u}) = ((μ' + j : Ordinal.{u}) : Label.{u})) : μ = μ' := by
  have h' : μ + i = μ' + j := WithTop.coe_injective (WithBot.coe_injective h)
  obtain ⟨b, rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ
  obtain ⟨b', rfl⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hμ'
  have key (c : Ordinal.{u}) (k : ℕ) : (Ordinal.omega0 * c + k) / Ordinal.omega0 = c := by
    rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 k), add_zero]
  rw [← key b i, h', key]

/-- **Readings in the own block lie in one block**: if the row of a cell `C` reads, in its own
block, cells labelled `l` and `l'`, both labels strictly below the label of `C` and neither
self-visible at the grade `K` of `C`, then `l'` is a visibility replacement `vr_K(l, j)` of `l`
for some `j ≤ K`; in particular `l` and `l'` lie in one block.  The locality witness at `C` sends
each reading below the label of `C` to the label read; a reading with finite part at least `K`
would make that label self-visible at `K`, and commutation with visibility replacement at the
finite part of the second reading gives `l'`.  So the own-block mechanism
(`carriesBottoms_of_row_mem_block`, `carriesBottomsAt_of_readsInOwnBlock`) serves anchors below
the cap and not self-visible at its grade only within one block. -/
theorem eq_visibilityReplace_of_readsInOwnBlock {P : StageType.{u} α n} {C : Fin P.card}
    {l l' : Label.{u}} (h : P.ReadsInOwnBlock C l) (h' : P.ReadsInOwnBlock C l')
    (hl : l < P.label C) (hl' : l' < P.label C)
    (hv : ¬ IsSelfVisible (P.toCellScheme.grade C) l)
    (hv' : ¬ IsSelfVisible (P.toCellScheme.grade C) l') :
    ∃ j ≤ P.toCellScheme.grade C, l' = visibilityReplace (P.toCellScheme.grade C) j l := by
  obtain ⟨z, hz, hzl, μ, hμ, i, i₀, hrz, hrC⟩ := h
  obtain ⟨z', hz', hzl', μ', hμ', j, j₀, hrz', hrC'⟩ := h'
  obtain rfl : μ = μ' := eq_of_coe_add_natCast_eq hμ hμ' (hrC.symm.trans hrC')
  obtain ⟨g, σ, hw, heq⟩ := P.isLawful.locality C
  set K := P.toCellScheme.grade C
  have hCg : P.label C ≤ g K := by
    have := heq ⟨C, P.toCellScheme.mem_below_gradedIndex C⟩
    simp only [min_self] at this
    rw [this]; exact min_le_right _ _
  -- the shifter sends the reading of a cell below `C` with label below `C` to its label
  have hσ : ∀ (y : Fin P.card) (hy : y ∈ P.toCellScheme.below (P.toCellScheme.gradedIndex C)),
      P.label y < P.label C → σ (P.rows.row C ⟨y, hy⟩) = P.label y := by
    intro y hy hlt
    have hgy : g K ≤ g (P.toCellScheme.grade y) :=
      hw.antitone ((CellScheme.mem_below _).mp hy).2
    have := heq ⟨y, hy⟩
    simp only [min_eq_left hlt.le] at this
    rcases min_eq_iff.mp this.symm with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (h1 ▸ hlt.trans_le (hCg.trans hgy)) (lt_irrefl _)
  have hσz : σ ((μ + i : Ordinal.{u}) : Label.{u}) = l := by rw [← hrz, hσ z hz (hzl ▸ hl), hzl]
  have hσz' : σ ((μ + j : Ordinal.{u}) : Label.{u}) = l' := by
    rw [← hrz', hσ z' hz' (hzl' ▸ hl'), hzl']
  -- a reading at a finite part at least `K` would make the label self-visible at `K`
  have hfin : ∀ (k : ℕ) (m : Label.{u}), σ ((μ + k : Ordinal.{u}) : Label.{u}) = m →
      m < P.label C → ¬ IsSelfVisible K m → k < K := by
    intro k m hk hm hvm
    by_contra hKk
    have hc := hw.visibilityReplace_comm ((μ + k : Ordinal.{u}) : Label.{u}) K
      (hk ▸ hm.le.trans hCg) K le_rfl
    rw [isSelfVisible_coe_add hμ (not_lt.mp hKk), hk] at hc
    exact hvm hc.symm
  have hi : i < K := hfin i l hσz hl hv
  have hj : j < K := hfin j l' hσz' hl' hv'
  have hc := hw.visibilityReplace_comm ((μ + i : Ordinal.{u}) : Label.{u}) K
    (hσz ▸ hl.le.trans hCg) j hj.le
  rw [visibilityReplace_coe_add_natCast hμ hi j, hσz', hσz] at hc
  exact ⟨j, hj.le, hc⟩

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
  exact hne (eq_of_coe_add_natCast_eq hμ₁ hμ₀ hj).symm

end StageType

namespace CoupledGatedExtensionCounterexample

/-- **A dominance step need not give a carrying cap**: the refuting private type `P α` is a coface
of its face on the first point that lies in every dominance family, with its full cell `4`
labelled `⊤` above every floor, and the bottom transport condition fails for it and the donor at
that label (`not_carriesBottoms`).  So the finite condition "every member of a dominance family
carries the bottoms at its dominating cell" is false; this refutes that sufficient condition, not
the acquisition of carrying contexts by models. -/
theorem exists_mem_dominanceFamily_not_carriesBottoms (α : Ordinal.{u})
    (hα : 1 < α) :
    ∃ (p : StageType.{u} α 1) (q : StageType.{u} α 2) (C : Fin q.card),
      (∀ γ : Ordinal.{u}, q ∈ p.cofaces ∩ StageType.dominanceFamily γ) ∧
      q.toCellScheme.gradedIndex C = (univ, 2) ∧ (∀ γ : Ordinal.{u}, (γ : Label.{u}) < q.label C) ∧
      ¬ StageType.CarriesBottoms q (donor α hα) (q.label C) := by
  have hf : univ.map (Fin.castSuccEmb : Fin 1 ↪ Fin 2) ∈ (P α hα).toCellScheme.faces := by
    -- The faces of `P α` are the interval plan of `univ` (`cells`, by definition).
    change _ ∈ Geometry.intervalPlan univ; decide +kernel
  -- The cell `4` has grade `2` and is labelled `⊤` (`P`, by definition).
  have htop : ∀ γ : Ordinal.{u}, (γ : Label.{u}) < (P α hα).label (4 : Fin 5) := fun γ ↦ by
    change (γ : Label.{u}) < ⊤
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top γ)
  refine ⟨(P α hα).comap Fin.castSuccEmb hf, P α hα, (4 : Fin 5), fun γ ↦
    ⟨⟨isLegal_P α hα, StageType.restrictFace_of_mem _ _ hf⟩, (4 : Fin 5), rfl, htop γ⟩, rfl, htop,
    not_carriesBottoms α hα ?_ ?_⟩
  · change IsSelfVisible 2 (⊤ : Label.{u})
    exact isSelfVisible_top 2
  · change (⊤ : Label.{u}) ≠ ⊥
    simp

end CoupledGatedExtensionCounterexample

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
generalized saturation are used. -/
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
block) and open at stages at most `ω`. -/
def HasTightCaps : Prop :=
  ∀ (x : R.Occurrence) (γ : Ordinal.{u}), γ < α →
    R.RealizesOver x.tuple (x.type.tightCapFamily γ)

/-- **Carrying private contexts from tight caps**: over every occurrence of a model with tight
caps, every donor has a carrying private context at every floor below the stage.

Uniformity gives the reference cells of the donor's blocks, labelled at most a floor `B ≥ γ`, and
dominance steps raise the arity past their finite parts and the donor's
(`IsModel.exists_referenceCells`); the tight cap over the result at the floor `B` reads the
reference cells' labels in its own block, which anchors the donor and gives the bottom transport
condition (`StageType.carriesBottoms_of_row_mem_block`). -/
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
    fun j _ hne hlt ↦ ?_, StageType.carriesBottoms_of_row_mem_block hC fun j _ hne hlt ↦ ?_⟩
  · obtain ⟨l, ⟨k, hk, hjl⟩, z, -, hzl, -⟩ := hread j hne hlt
    exact ⟨z, k, hk, hzl ▸ hjl⟩
  · obtain ⟨l, ⟨k, hk, hjl⟩, z, hz, hzl, ν, hν, i, i', hrz, hrC⟩ := hread j hne hlt
    exact ⟨z, hz, k, hk, hzl ▸ hjl, ν, hν, i, i', hrz, hrC⟩

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
sufficient condition `HasTightCaps`, not `AcquiresCarryingContexts` and not (R1); at stages at most
`ω` it is neither proved nor refuted. -/
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
condition `StageType.HasTightSaturations`, not `HasCarryingSubfullContext` and not (R1); at stages
at most `ω` it is neither proved nor refuted. -/
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
  exact Ordinal.omega0_pos.ne (StageType.eq_of_coe_add_natCast_eq hμ₁ Ordinal.isSuccPrelimit_zero
    hj).symm

end Realization

end VaughtConjecture
