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
cell (`StageType.ReadsInOwnBlock.exists_ne_bot`).  A cap is **tight** for a donor when it reads in
its own block a label of which every donor label below the cap is a visibility replacement; a
tight cap carries the bottoms (`StageType.carriesBottoms_of_row_mem_block`, and at any grade
`StageType.carriesBottomsAt_of_readsInOwnBlock`).  The private cap has full grade, so it is a cell
of the last one-point step that produces the private context.

**At full grade, no clause of a model asks for a tight cap.**  Compiled:
* Generalized saturation and the bottom pattern prescribe a scheme, rows included, but every
  nonempty instance of either has a member whose cells of full grade are all labelled `⊥`
  (`StageType.exists_mem_cofaces_inter_saturationFamily_label_eq_bot`,
  `StageType.exists_mem_cofaces_inter_bottomPatternFamily_label_eq_bot`), hence a member in no
  dominance family (`StageType.exists_mem_cofaces_inter_saturationFamily_not_mem_dominanceFamily`).
  So no clause asks for a coface on a prescribed scheme with a label of full grade above a floor:
  choosing the saturation scheme to contain the cell of an earlier dominance step does not help,
  since that cell is not of full grade after the step.
* High-arity dominance bounds a label of full grade at a cell whose row it does not prescribe,
  and a member of a dominance family need not carry the bottoms at its dominating cell
  (`CoupledGatedExtensionCounterexample.exists_mem_dominanceFamily_not_carriesBottoms`,
  the refuting input of the coupled property).  This refutes a finite sufficient condition
  ("every member of a dominance family carries"), not the acquisition.
* The clause that would suffice is named: a realization **has tight caps**
  (`Realization.HasTightCaps`) when over every occurrence and at every floor it realizes a member
  of the **tight cap family** (`StageType.tightCapFamily`, inside the dominance family): a coface
  with a cell of full grade above the floor that reads in its own block every label of the root
  type at most the floor and not self-visible at the new arity.  A model with tight caps acquires
  carrying contexts (`Realization.IsModel.acquiresCarryingContexts_of_hasTightCaps`).  Whether
  every model has tight caps is open; it is not a clause of `IsModel`, and a model with none would
  have to be constructed to refute the acquisition this way (the library constructs no model).

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
* stated (prospective, neither proved nor refuted): **tight saturations**
  (`StageType.HasTightSaturations α`), a statement about legal stage types and schemes, not about
  models: over every legal `p` on `N` points, a legal one-point extension scheme with a coface of
  `p` whose cells of graded index `(univ, N)` read in their own block every label of `p` not
  self-visible at `N`.  It is a completion problem of the kind of (R6);
* compiled: every model has, over every root, for every donor and every floor below the stage, a
  carrying context with a cap one grade below full, conditional on tight saturations
  (`Realization.IsModel.hasCarryingSubfullContext`).  Of the clauses of a model it uses
  uniformity, high-arity dominance, legality, exact consistency and generalized saturation.

**What is not claimed.**  `Realization.AcquiresCarryingContexts` is neither proved nor refuted for
all models.  No extension property for a cap one grade below full is defined, and the coupled
property restricted to carrying contexts is not stated (prospective).  Nothing here is equivalent
to (R1), and (R1) is neither proved nor refuted.

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
  change (if _ then _ else _) = _
  split_ifs with h
  · omega
  · rfl

/-- At full grade `botTopGrade` is labelled `⊥`. -/
theorem botTopGrade_label_of_grade_eq (q : StageType.{u} α (n + 1)) {i : Fin q.card}
    (hi : q.toCellScheme.grade i = n + 1) : q.botTopGrade.label i = ⊥ := by
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

/-- The **bottom transport condition at the grade `k`**: `CarriesBottoms` with the cells of graded
index `(univ, k)` labelled `c` in place of those of graded index `(univ, n)`, and visibility
replacement at `k` in place of `n`.  At `k = n` it is `CarriesBottoms` (`carriesBottomsAt_iff`).
It is the condition that the proof of `CoupledGatedExtension.carriesBottoms` gives for a gate and
a cap of grade `k`, a design that is not defined in the library. -/
def CarriesBottomsAt (P : StageType.{u} α n) (d : StageType.{u} α (m + 1)) (c : Label.{u})
    (k : ℕ) : Prop :=
  ∀ a : Fin P.card → Label.{u}, P.rows.IsLawful a →
    (∀ i, P.toCellScheme.gradedIndex i = (univ, k) → P.label i = c → a i ≠ ⊥) →
    ∃ ρ : Fin d.card → Label.{u}, d.rows.IsLawful ρ ∧
      ∀ j, Fin.last m ∈ d.toCellScheme.scope j → d.label j ≠ ⊥ →
        (¬ c ≤ d.label j →
          (∀ i, ∀ k' ≤ k, d.label j = visibilityReplace k k' (P.label i) → a i = ⊥) → ρ j = ⊥) ∧
        ((∀ i, ((∃ k' ≤ k, d.label j = visibilityReplace k k' (P.label i)) ∨
            (c ≤ P.label i ∧ c ≤ d.label j)) → a i ≠ ⊥) → ρ j ≠ ⊥)

/-- The bottom transport condition at the arity is `CarriesBottoms`. -/
theorem carriesBottomsAt_iff {P : StageType.{u} α n} {d : StageType.{u} α (m + 1)}
    {c : Label.{u}} : CarriesBottomsAt P d c n ↔ CarriesBottoms P d c :=
  Iff.rfl

/-- **The bottom transport condition at the grade `k` holds at a tight cap**: let `C` be a cell of
graded index `(univ, k)` of `P`, and suppose every new donor label neither `⊥` nor at least the
label of `C` is `vr_k(l, k')`, `k' ≤ k`, for a label `l` that the row of `C` reads in its own block.
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

/-! ### The finite hypothesis for caps of grade below full -/

variable (α) in
/-- **Tight saturations** (a named hypothesis on stage types, prospective): over every legal
stage type `p` on `N` points there is a scheme `S` on `N + 1` points with a coface of `p`, such
that in every coface of `p` on `S`, every cell of full scope and grade `N` reads, in its own block,
a cell labelled `l` for every label `l` of `p` that is not self-visible at `N`.  It concerns
schemes and stage types only, not models: it asks for a legal one-point extension of the scheme
of `p` whose cells of graded index `(univ, N)` read the proper labels of `p` in their own block.
Neither proved nor refuted. -/
def HasTightSaturations : Prop :=
  ∀ {N : ℕ} (p : StageType.{u} α N), p.IsLegal →
    ∃ S : Scheme.{u} (N + 1), (p.cofaces ∩ saturationFamily S).Nonempty ∧
      ∀ q ∈ p.cofaces ∩ saturationFamily S, ∀ G : Fin q.card,
        q.toCellScheme.gradedIndex G = (univ, N) →
        ∀ z : Fin p.card, ¬ IsSelfVisible N (p.label z) → q.ReadsInOwnBlock G (p.label z)

/-- The **tight cap family** over `p` at the floor `γ`: the stage types on `n + 1` points with a
cell of full grade labelled above `γ` that reads, in its own block, a cell labelled `l` for every
label `l ≤ γ` of `p` not self-visible at `n + 1`.  It lies in the dominance family
(`tightCapFamily_subset_dominanceFamily`); no clause of a model asks for it. -/
def tightCapFamily (p : StageType.{u} α n) (γ : Ordinal.{u}) : Set (StageType.{u} α (n + 1)) :=
  {q | ∃ C, q.toCellScheme.grade C = n + 1 ∧ (γ : Label.{u}) < q.label C ∧
    ∀ z : Fin p.card, ¬ IsSelfVisible (n + 1) (p.label z) → p.label z ≤ (γ : Label.{u}) →
      q.ReadsInOwnBlock C (p.label z)}

/-- The tight cap family lies in the dominance family at the same floor. -/
theorem tightCapFamily_subset_dominanceFamily (p : StageType.{u} α n) (γ : Ordinal.{u}) :
    p.tightCapFamily γ ⊆ dominanceFamily γ :=
  fun _ ⟨C, hC, hγC, _⟩ ↦ ⟨C, hC, hγC⟩

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
`StageType.HasTightSaturations α` holds.

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
of the dominating cell; it is not a clause of a model, and whether every model has tight caps is
open. -/
def HasTightCaps : Prop :=
  ∀ (x : R.Occurrence) (γ : Ordinal.{u}), γ < α →
    R.RealizesOver x.tuple (x.type.tightCapFamily γ)

/-- **Carrying private contexts from tight caps**: over every occurrence of a model with tight
caps, every donor has a carrying private context at every floor below the stage.

Uniformity gives the reference cells of the donor's blocks, labelled at most a floor `B ≥ γ`;
dominance steps raise the arity past their finite parts and the donor's (`exists_extend_dominance`);
the tight cap over the result at the floor `B` reads the reference cells' labels in its own block,
which anchors the donor and gives the bottom transport condition
(`StageType.carriesBottoms_of_row_mem_block`). -/
theorem IsModel.hasCarryingPrivateContext_of_hasTightCaps (hR : R.IsModel)
    (ht : R.HasTightCaps) (x : R.Occurrence) (d : StageType.{u} α (x.arity + 1))
    {γ : Ordinal.{u}} (hγ : γ < α) : HasCarryingPrivateContext x d γ := by
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
  obtain ⟨u, hu, q, ⟨C, hCgr, hBC, htight⟩, he⟩ := ht w B hBα
  have htuple : ((f₁.trans f₂).trans Fin.castSuccEmb).trans u = x.tuple := by
    rw [Function.Embedding.trans_assoc, hu, Function.Embedding.trans_assoc, hf₂, hf₁]
  have hC : q.toCellScheme.gradedIndex C = (univ, w.arity + 1) :=
    StageType.gradedIndex_eq_univ_of_grade_eq q hCgr
  -- each donor label below `C` is read through a reference cell that `C` reads in its block
  have hread : ∀ j : Fin d.card, d.label j ≠ ⊥ → d.label j < q.label C →
      ∃ l, (∃ k ≤ w.arity + 1, d.label j = visibilityReplace (w.arity + 1) k l) ∧
        q.ReadsInOwnBlock C l := fun j hne hlt ↦ by
    obtain ⟨o, ho⟩ := exists_eq_coe_of_ne_bot_of_lt hne hlt
    obtain ⟨i, hi, rfl⟩ := hD j o ho
    obtain ⟨z₁, k, hk, hz₁, hkB⟩ := hanc (μ j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
    obtain ⟨z, hz⟩ := Occurrence.exists_label_eq_of_trans_eq hR.isConsistent hf₂ z₁
    have hDj : D j ≤ univ.sup D := le_sup (mem_univ j)
    have hkn : k < w.arity + 1 := by omega
    refine ⟨w.type.label z, ⟨i, by omega, ?_⟩, htight z ?_ ?_⟩ <;> rw [hz, hz₁]
    · rw [ho, visibilityReplace_coe_add_natCast (hμ j).1 hkn]
    · exact not_isSelfVisible_coe_add_natCast (hμ j).1 hkn
    · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hkB)
  refine ⟨⟨_, u, q, he⟩, (f₁.trans f₂).trans Fin.castSuccEmb, C, htuple,
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent htuple, by simp; omega, hC,
    lt_of_le_of_lt (WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hγB)) hBC,
    fun j _ hne hlt ↦ ?_, StageType.carriesBottoms_of_row_mem_block hC fun j _ hne hlt ↦ ?_⟩
  · obtain ⟨l, ⟨k, hk, hjl⟩, z, -, hzl, -⟩ := hread j hne hlt
    exact ⟨z, k, hk, hzl ▸ hjl⟩
  · obtain ⟨l, ⟨k, hk, hjl⟩, z, hz, hzl, ν, hν, i, i', hrz, hrC⟩ := hread j hne hlt
    exact ⟨z, hz, k, hk, hzl ▸ hjl, ν, hν, i, i', hrz, hrC⟩

/-- **Acquisition from tight caps**: a model with tight caps acquires carrying contexts. -/
theorem IsModel.acquiresCarryingContexts_of_hasTightCaps (hR : R.IsModel)
    (ht : R.HasTightCaps) : R.AcquiresCarryingContexts :=
  fun x d _ _ hγ ↦ hR.hasCarryingPrivateContext_of_hasTightCaps ht x d hγ

end Realization

end VaughtConjecture
