/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryTwin

/-!
# The twin schemes at every block and every cap

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap, the reference cells and the decoder of (R4)); semantic contract, item 8.

**The question.**  The twin schemes (`Continuation.StableRecoveryTwin.twinScheme`) recover the
twin donors through a cap labelled the formal top, with reference labels in the block `λ_ξ`
(`Continuation.StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors`).  In (R4) the cap is
a cell of the stable type of an occurrence, whose stable value is in general a proper ordinal
`λ_ξ + M`; and the labels of a donor may lie in a block `[μ, μ + ω)` below `λ_ξ`, with a
reference cell there (given by uniformity in the acquisition,
`Realization.IsModel.acquiresCalibratedContexts_gradedCap`).  This file runs the twin schemes at
both.

**The data** (`IsTwinCap ξ μ C`).  A base `μ`, zero or a limit, with `μ ≤ λ_ξ`, and a cap value
`C` at `λ_{ξ+1}` with `λ_ξ + 3 ≤ C`: the formal top, or a proper ordinal `λ_ξ + M` with `M ≥ 3`.
The labelled twin scheme `twinTypeAt` labels the root `μ + 2`, the twins `μ + 2` and `μ + 1` in
the order `o`, and the cap and the reading cell `C`; these parameters form a twin tuple
(`isTwinTuple_twinCap`), since `μ + 2 < C` and visibility replacement at `3` turns `μ + 2` into
`μ + 1` (`visibilityReplace_coe_add_natCast`).  The context `contextAt` is its face along the
first three points (the same for both orders, `restrictFace_twinTypeAt_castSuccEmb`), the root
`rootAt` its face along the root embedding (one cell labelled `μ + 2`), and the donor `donorAt`
its face along the root and the new point: the five-cell type `(μ + 2, ⊥, μ + 2, μ + 1, ⊥)` in
the order `o`.

**The result** (`exists_isStableRecoveryScheme_twinFamily`).  For every such `μ`, `C`, every
order of the twins and every `γ < λ_ξ + 3`, the graded cap calibration holds and the twin scheme
of the order is a stable recovery scheme, by `StageType.IsStableRecoveryScheme.of_readsThroughCap`
at the reading cell.  Two cases:

* **a proper cap** (`exists_isStableRecoveryScheme_properCap`): `μ = λ_ξ`, the cap labelled
  exactly `λ_ξ + 3 = λ_ξ + N` (the least value the calibration allows) and `γ = λ_ξ + 2` (the
  largest).  The decoder `CellScheme.Rows.IsLawful.label_eq_of_reading` needs only the strict
  bounds `μ + i < p b` and `μ + n < p b` at the cap, which hold for `i, n < N ≤ M`; none of the
  clauses of `StageType.ReadsThroughCap` mentions the label of the cap.  The label enters only
  through the hypothesis `λ_ξ + N ≤ T⁺ b` of `of_readsThroughCap`, which for a cell of grade `N`
  labelled at least `λ_ξ` is the order law (`StageType.coe_add_grade_le_label`, in
  `VaughtConjecture.Continuation.StableRecovery`).
* **a lower block** (`exists_isStableRecoveryScheme_lowerBlock`): `μ < λ_ξ`, so the root, the
  reference cell and both twins are labelled below `λ_ξ` and are kept by the reduction to `λ_ξ`;
  the lower twin `μ + 1` is still recovered at the offset `1`, against the reference `μ + 2` read
  at `2`.

**What this does not show.**  `StageType.HasStableRecoverySchemes ξ
(StageType.GradedCapCalibration ξ)` stays open at other inputs (so this route to (R4) is not
complete; (R4) follows instead from `StageType.hasLadderGrowthCarriersStableAtSeed_levels`, not
yet reviewed).  The inputs here keep the shape of the twin donors: no label of the donor is the
formal top (the clause on `γ` and the branch at `⊤` of `StageType.ReadsThroughCap` are unused);
`(univ, 3)` is the only graded face of grade `N = 3` containing the cap and the new cells; and the
reference cell is the root itself, so all labels of the donor lie in one block.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryTwinFamily

open Finset Label StageType CandidateCounterexamples StableRecoveryCounterexample
  StableRecoveryTwin
open Ordinal hiding univ

variable (ξ : Ordinal.{u})

/-! ### The data -/

/-- The **data of a twin cap** at `ξ`: a base `μ`, zero or a limit, with `μ ≤ λ_ξ`, and a cap
value `C` at `λ_{ξ+1}` with `λ_ξ + 3 ≤ C` (the formal top or a proper ordinal `λ_ξ + M`,
`M ≥ 3`). -/
structure IsTwinCap (μ : Ordinal.{u}) (C : Label.{u}) : Prop where
  /-- The base is zero or a limit. -/
  isSuccPrelimit : Order.IsSuccPrelimit μ
  /-- The base is at most `λ_ξ`. -/
  le_blockStage : μ ≤ blockStage ξ
  /-- The cap is at least `λ_ξ + 3`. -/
  labelAdd_three_le : labelAdd (blockStage ξ) 3 ≤ C
  /-- The cap is a label at `λ_{ξ+1}`. -/
  atStage : AtStage (blockStage (ξ + 1)) C

variable {ξ} {μ : Ordinal.{u}} {C : Label.{u}}

namespace IsTwinCap

/-- The cap is self-visible at `3`: it is at least `λ_ξ + 3` at the stage `λ_ξ + ω`. -/
theorem isSelfVisible_cap (h : IsTwinCap ξ μ C) : IsSelfVisible 3 C :=
  isSelfVisible_of_coe_add_le (isSuccPrelimit_blockStage ξ)
    (blockStage_add_one ξ ▸ h.atStage) h.labelAdd_three_le

/-- A label `μ + n` with `n < 3` lies below the cap. -/
theorem labelAdd_lt_cap (h : IsTwinCap ξ μ C) {n : ℕ} (hn : n < 3) : labelAdd μ n < C := by
  refine lt_of_lt_of_le ?_ h.labelAdd_three_le
  rcases h.le_blockStage.lt_or_eq with hlt | rfl
  · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      (((isSuccPrelimit_blockStage ξ).add_natCast_lt hlt n).trans_le le_self_add))
  · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
      ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hn)))

/-- A label `μ + n` occurs at `λ_{ξ+1}`. -/
theorem atStage_labelAdd (h : IsTwinCap ξ μ C) (n : ℕ) :
    AtStage (blockStage (ξ + 1)) (labelAdd μ n) := by
  refine .inl ?_
  rw [blockStage_add_one]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_le_add h.le_blockStage le_rfl).trans_lt
      ((add_lt_add_iff_left _).mpr (natCast_lt_omega0 n))))

end IsTwinCap

/-- **The parameters of the twin cap form a twin tuple**: the root and the higher twin `μ + 2`,
the lower twin `μ + 1` and the cap `C`.  Below the cap the root has finite part `2`, which
visibility replacement at `3` keeps and lowers to `1`. -/
theorem isTwinTuple_twinCap (h : IsTwinCap ξ μ C) :
    IsTwinTuple (labelAdd μ 2) (labelAdd μ 2) (labelAdd μ 1) C := by
  have hμ := h.isSuccPrelimit
  have hRC : min (labelAdd μ 2) C = labelAdd μ 2 := min_eq_left (h.labelAdd_lt_cap (by omega)).le
  have hLC : min (labelAdd μ 1) C = labelAdd μ 1 := min_eq_left (h.labelAdd_lt_cap (by omega)).le
  refine ⟨isSelfVisible_coe_add hμ (by omega), isSelfVisible_coe_add hμ (by omega),
    isSelfVisible_coe_add hμ le_rfl, h.isSelfVisible_cap, le_rfl, ?_, le_max_left _ _, ?_, rfl,
    ?_⟩
  · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      ((add_le_add_iff_left _).mpr (Nat.cast_le.mpr (by omega : 1 ≤ 2))))
  · rw [hRC]
    exact visibilityReplace_coe_add_natCast hμ (by omega) 2
  · rw [hRC, hLC, visibilityReplace_coe_add_natCast hμ (by omega) 1, hLC]

/-! ### The labelled twin scheme -/

/-- The **labelled twin scheme** at `λ_{ξ+1}` of a twin cap, for the order `o` of the twins: the
root `μ + 2`, the higher twin `μ + 2` and the lower `μ + 1` (with the cells of their kinds), and
`C` at the cap and the reading cell. -/
noncomputable def twinTypeAt (h : IsTwinCap ξ μ C) (o : Bool) :
    StageType.{u} (blockStage (ξ + 1)) 4 where
  toScheme := twinScheme o
  label := twinLabel (labelAdd μ 2) (twinHi o (labelAdd μ 2) (labelAdd μ 1))
    (twinLo o (labelAdd μ 2) (labelAdd μ 1)) C
  isWellFormed := (isLegal_twinScheme o).isWellFormed
  isCoded := (isLegal_twinScheme o).isCoded
  isLawful := isLawful_twinLabel (by rw [twinHi_twinHi, twinLo_twinHi]; exact isTwinTuple_twinCap h)
  atStage d := by
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    simp only [twinLabel, hk]
    fin_cases k
    · exact atStage_bot
    · exact h.atStage_labelAdd 2
    · cases o
      exacts [h.atStage_labelAdd 1, h.atStage_labelAdd 2]
    · cases o
      exacts [h.atStage_labelAdd 2, h.atStage_labelAdd 1]
    · exact h.atStage
    · exact h.atStage

/-- The **donor** of a twin cap, for the order `o` of the twins: the face of the labelled twin
scheme along the root and the new point, the five-cell type `(μ + 2, ⊥, μ + 2, μ + 1, ⊥)` in the
order `o`. -/
noncomputable def donorAt (h : IsTwinCap ξ μ C) (o : Bool) :
    StageType.{u} (blockStage (ξ + 1)) 2 :=
  (twinTypeAt h o).comap (extendByLast rootEmb) map_extendByLast_mem_faces

/-- The **context** of a twin cap on three points: the face of the labelled twin scheme along the
first three points, with the root, its copies, the cap and dead cells. -/
noncomputable def contextAt (h : IsTwinCap ξ μ C) : StageType.{u} (blockStage (ξ + 1)) 3 :=
  (twinTypeAt h true).comap Fin.castSuccEmb map_castSuccEmb_mem_faces

/-- **The context does not depend on the order of the twins**: the face of the labelled twin
scheme along the first three points is `contextAt` for both orders. -/
theorem restrictFace_twinTypeAt_castSuccEmb (h : IsTwinCap ξ μ C) (o : Bool) :
    restrictFace Fin.castSuccEmb (twinTypeAt h o) = some (contextAt h) := by
  rw [restrictFace_of_mem _ _ map_castSuccEmb_mem_faces]
  cases o
  swap
  · rfl
  refine congrArg some (StageType.ext comap_twinScheme_castSuccEmb fun i j hij ↦ ?_)
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  -- the labels of the faces are those of the twin schemes at the visible cells
  change twinLabel _ _ _ C ((twinScheme.{u} false).cellMap Fin.castSuccEmb ⟨i, hi⟩) =
    twinLabel _ _ _ C ((twinScheme.{u} true).cellMap Fin.castSuccEmb ⟨j, hj⟩)
  have hk : i < 10 := card_comap_castSuccEmb false ▸ hi
  rw [cellMap_castSuccEmb false (i := ⟨i, hk⟩) (j := ⟨i, hi⟩) rfl,
    cellMap_castSuccEmb true (i := ⟨i, hk⟩) (j := ⟨j, hj⟩) hij]
  have h23 : ∀ a : Fin 10, cellKind (contextCells a) ≠ 2 ∧ cellKind (contextCells a) ≠ 3 := by
    decide
  exact kindValue_of_ne (h23 _).1 (h23 _).2

/-- The root embedding spans a closed face of the context. -/
theorem map_rootEmb_mem_faces_contextAt (h : IsTwinCap ξ μ C) :
    univ.map rootEmb ∈ (contextAt h).toCellScheme.faces := by
  refine ((twinTypeAt h true).map_univ_mem_comap_faces_iff _ _ _).mpr ?_
  -- the faces of the twin scheme
  change univ.map (rootEmb.trans Fin.castSuccEmb) ∈ twinCells.faces
  decide

/-- The **root** of a twin cap: the face of the context along the root embedding, one cell
labelled `μ + 2`. -/
noncomputable def rootAt (h : IsTwinCap ξ μ C) : StageType.{u} (blockStage (ξ + 1)) 1 :=
  (contextAt h).comap rootEmb (map_rootEmb_mem_faces_contextAt h)

/-- The root is the face of the context along the root embedding. -/
theorem restrictFace_rootAt (h : IsTwinCap ξ μ C) :
    restrictFace rootEmb (contextAt h) = some (rootAt h) :=
  restrictFace_of_mem _ _ _

/-- The context is legal. -/
theorem isLegal_contextAt (h : IsTwinCap ξ μ C) : (contextAt h).IsLegal :=
  (isLegal_twinScheme true).comap _ map_castSuccEmb_mem_faces

/-- **The donor is a coface of the root**, for either order of the twins. -/
theorem donorAt_mem_cofaces (h : IsTwinCap ξ μ C) (o : Bool) :
    donorAt h o ∈ (rootAt h).cofaces := by
  refine ⟨(isLegal_twinScheme o).comap _ map_extendByLast_mem_faces, ?_⟩
  unfold donorAt
  rw [restrictFace_trans _ _ _ (restrictFace_of_mem (twinTypeAt h o) _ map_extendByLast_mem_faces),
    castSuccEmb_trans_extendByLast,
    ← restrictFace_trans _ _ _ (restrictFace_twinTypeAt_castSuccEmb h o), restrictFace_rootAt]

/-! ### The cap, the reference cell and the labels of the donor -/

/-- The context has ten cells. -/
theorem card_contextAt (h : IsTwinCap ξ μ C) : (contextAt h).card = 10 :=
  card_comap_castSuccEmb true

/-- The cap of the context: its cell `9`, the cell `({0, 1, 2}, 3)` of the twin scheme. -/
noncomputable def capAt (h : IsTwinCap ξ μ C) : Fin (contextAt h).card :=
  ⟨9, by rw [card_contextAt]; omega⟩

/-- The reference cell of the context: its cell `2`, the root `({2}, 1)`. -/
noncomputable def refAt (h : IsTwinCap ξ μ C) : Fin (contextAt h).card :=
  ⟨2, by rw [card_contextAt]; omega⟩

/-- The cap of the context has grade `3`. -/
theorem grade_capAt (h : IsTwinCap ξ μ C) : (contextAt h).toCellScheme.grade (capAt h) = 3 := by
  -- the grade of a cell of the context is the grade of its cell
  change twinCells.grade ((twinScheme.{u} true).cellMap Fin.castSuccEmb (capAt h)) = 3
  rw [cellMap_castSuccEmb true (i := 9) (j := capAt h) rfl]
  rfl

/-- The cap of the context is labelled `C`. -/
theorem label_capAt (h : IsTwinCap ξ μ C) : (contextAt h).label (capAt h) = C := by
  -- the label of a cell of the context is the label of its cell
  change twinLabel _ _ _ C ((twinScheme.{u} true).cellMap Fin.castSuccEmb (capAt h)) = C
  rw [cellMap_castSuccEmb true (i := 9) (j := capAt h) rfl]
  rfl

/-- The reference cell of the context has grade `1`. -/
theorem grade_refAt (h : IsTwinCap ξ μ C) : (contextAt h).toCellScheme.grade (refAt h) = 1 := by
  -- the grade of a cell of the context is the grade of its cell
  change twinCells.grade ((twinScheme.{u} true).cellMap Fin.castSuccEmb (refAt h)) = 1
  rw [cellMap_castSuccEmb true (i := 2) (j := refAt h) rfl]
  rfl

/-- The reference cell of the context is labelled `μ + 2`. -/
theorem label_refAt (h : IsTwinCap ξ μ C) : (contextAt h).label (refAt h) = labelAdd μ 2 := by
  -- the label of a cell of the context is the label of its cell
  change twinLabel _ _ _ C ((twinScheme.{u} true).cellMap Fin.castSuccEmb (refAt h)) = _
  rw [cellMap_castSuccEmb true (i := 2) (j := refAt h) rfl]
  rfl

/-- The donor has five cells. -/
theorem card_donorAt (h : IsTwinCap ξ μ C) (o : Bool) : (donorAt h o).card = 5 := by
  -- the scheme of the donor is the face of the twin scheme, the five-cell scheme
  change ((twinScheme.{u} o).comap (extendByLast rootEmb)).card = 5
  rw [comap_twinScheme_extendByLast]

/-- The labels of the donor: `μ + 2` at the root, `⊥` at the dead cells, and `μ + 2`, `μ + 1` at
the twins in the order `o`. -/
theorem donorAt_label (h : IsTwinCap ξ μ C) (o : Bool) (k : Fin 5) (j : Fin (donorAt h o).card)
    (hkj : (k : ℕ) = j) :
    (donorAt h o).label j = ![labelAdd μ 2, ⊥, twinHi o (labelAdd μ 2) (labelAdd μ 1),
      twinLo o (labelAdd μ 2) (labelAdd μ 1), ⊥] k := by
  -- the label of a cell of the donor is the label of its cell in the twin scheme
  change twinLabel _ _ _ C ((twinScheme.{u} o).cellMap (extendByLast rootEmb) j) = _
  rw [cellMap_extendByLast o (i := k) (j := j) hkj]
  fin_cases k <;> rfl

/-- The scope of a cell of the donor is the scope of the five-cell scheme at its index. -/
theorem donorAt_scope (h : IsTwinCap ξ μ C) (o : Bool) (k : Fin 5) (j : Fin (donorAt h o).card)
    (hkj : (k : ℕ) = j) :
    (donorAt h o).toCellScheme.scope j = fiveCells.scope k := by
  have key : ∀ (k : Fin 5) (x : Fin 2),
      extendByLast rootEmb x ∈ twinCells.scope (donorCells k) ↔ x ∈ fiveCells.scope k := by
    decide
  -- the scope of a cell of the face is the preimage of the scope of its cell
  have hsc : ∀ j' : Fin ((twinScheme.{u} o).comap (extendByLast rootEmb)).card, (k : ℕ) = j' →
      ((twinScheme.{u} o).comap (extendByLast rootEmb)).toCellScheme.scope j' =
        fiveCells.scope k := fun j' hkj' ↦ by
    rw [Scheme.comap_scope, cellMap_extendByLast o (i := k) (j := j') hkj']
    exact Finset.ext fun x ↦ by rw [Finset.mem_preimage]; exact key k x
  exact hsc j hkj

/-- The lower twin of the donor, at the index `3` for `o = true` and `2` for `o = false`, is
labelled `μ + 1` and contains the new point. -/
theorem exists_lowerTwin (h : IsTwinCap ξ μ C) (o : Bool) :
    ∃ j : Fin (donorAt h o).card, Fin.last 1 ∈ (donorAt h o).toCellScheme.scope j ∧
      (donorAt h o).label j = labelAdd μ 1 := by
  have hc := card_donorAt h o
  let k : Fin 5 := if o then 3 else 2
  have hk : (k : ℕ) < (donorAt h o).card := by rw [hc]; exact k.2
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · rw [donorAt_scope h o k ⟨k, hk⟩ rfl]
    cases o <;> decide
  · rw [donorAt_label h o k ⟨k, hk⟩ rfl]
    cases o <;> rfl

/-! ### The calibration and the reading -/

/-- **The graded cap calibration holds for the donor of a twin cap**, for every `γ < λ_ξ + 3`: the
cap has grade `3 > 1` and label `C ≥ λ_ξ + 3`; the ordinal labels `μ + 2` and `μ + 1` of the donor
have finite parts below `3`, with the root `μ + 2` (grade `1`) as reference cell. -/
theorem gradedCapCalibration_contextAt (h : IsTwinCap ξ μ C) (o : Bool) {γ : Ordinal.{u}}
    (hγ : γ < blockStage ξ + 3) :
    GradedCapCalibration ξ (contextAt h) rootEmb (donorAt h o) γ := by
  have hμ := h.isSuccPrelimit
  refine ⟨capAt h, ?_, by rw [grade_capAt]; omega, by rw [grade_capAt]; exact_mod_cast hγ,
    fun j x hx ↦ ?_⟩
  · rw [label_capAt, grade_capAt]
    exact h.labelAdd_three_le
  have hj : (j : ℕ) < 5 := card_donorAt h o ▸ j.2
  have hl := donorAt_label h o ⟨j, hj⟩ j rfl
  rw [hx] at hl
  have hgr : ∀ n : ℕ, n < 3 → (x : Label.{u}) = labelAdd μ n →
      ∃ (μ' : Ordinal.{u}) (n i : ℕ) (a : Fin (contextAt h).card), Order.IsSuccPrelimit μ' ∧
        x = μ' + n ∧ n < (contextAt h).toCellScheme.grade (capAt h) ∧
        i < (contextAt h).toCellScheme.grade (capAt h) ∧
        (contextAt h).toCellScheme.grade a ≤ (contextAt h).toCellScheme.grade (capAt h) ∧
        (contextAt h).label a = ((μ' + i : Ordinal.{u}) : Label.{u}) := fun n hn hxn ↦
    ⟨μ, n, 2, refAt h, hμ, WithTop.coe_injective (WithBot.coe_injective hxn),
      by rw [grade_capAt]; exact hn, by rw [grade_capAt]; omega,
      by rw [grade_capAt, grade_refAt]; omega, label_refAt h⟩
  generalize (⟨j, hj⟩ : Fin 5) = k at hl
  fin_cases k <;> cases o <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, twinHi_true, twinHi_false, twinLo_true, twinLo_false] at hl
  all_goals first
    | exact absurd hl WithBot.coe_ne_bot
    | exact hgr 2 (by omega) hl
    | exact hgr 1 (by omega) hl

/-- **The reading cell reads a twin through the cap**: a new cell `e` labelled `μ + n₀`
(`n₀ ∈ {1, 2}`), read by the reading cell `21` at `n₀`, is read through the cap, with the root
`μ + 2` of the context, read at `2`, as reference cell. -/
theorem readsThroughCap_twinAt (h : IsTwinCap ξ μ C) (o : Bool)
    (b : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card)
    (hb : (twinScheme.{u} o).cellMap Fin.castSuccEmb b = 19) {n₀ : ℕ} (hn₀ : n₀ = 1 ∨ n₀ = 2)
    {e : Fin 23} (hre : kindRow.{u} o 5 (cellKind e) = gridPoint n₀ 0) :
    (contextAt h).ReadsThroughCap (twinScheme.{u} o) b 21 e (labelAdd μ n₀) := by
  have hc10 := card_comap_castSuccEmb.{u} o
  let a : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card := ⟨2, by omega⟩
  have ha : (twinScheme.{u} o).cellMap Fin.castSuccEmb a = 2 :=
    cellMap_castSuccEmb o (i := 2) rfl
  have hgb : (twinScheme.{u} o).toCellScheme.grade
      ((twinScheme.{u} o).cellMap Fin.castSuccEmb b) = 3 := by rw [hb]; rfl
  intro he _
  refine ⟨fun h' ↦ absurd h' WithBot.coe_ne_bot,
    fun h' ↦ absurd (WithBot.coe_injective h') WithTop.coe_ne_top, fun μ' n hμ' h' ↦ ?_⟩
  -- the block and the finite part of the label are unique
  obtain ⟨rfl, rfl⟩ := (add_natCast_eq_add_natCast_iff hμ' h.isSuccPrelimit).mp
    (WithTop.coe_injective (WithBot.coe_injective h')).symm
  have ha21 : (twinScheme.{u} o).cellMap Fin.castSuccEmb a ∈
      (twinScheme.{u} o).toCellScheme.below ((twinScheme.{u} o).toCellScheme.gradedIndex 21) := by
    rw [ha]
    -- membership below a pair is the order of graded indices
    change twinCells.gradedIndex 2 ≤ twinCells.gradedIndex 21
    decide
  refine ⟨by rw [hgb]; omega, a, refAt h, 2, ((0 : ℕ) : Ordinal.{u}), rfl,
    label_refAt h, by rw [hgb]; omega, ha21, ?_, ?_⟩
  · -- the row of the reading cell, by kinds
    change kindRow o 5 (cellKind ((twinScheme.{u} o).cellMap Fin.castSuccEmb a)) = _
    rw [ha]
    rfl
  · exact hre

/-! ### The stable recovery schemes -/

/-- **The twin scheme is a stable recovery scheme** for the context of a twin cap, the root
embedding, the donor of the order `o` and every `γ < λ_ξ + 3`, by
`StageType.IsStableRecoveryScheme.of_readsThroughCap` at the reading cell `21` (the only cell of
`(univ, 3)`): it reads the new cells labelled `⊥` as `⊥`, the twin labelled `μ + 2` at `2` and the
twin labelled `μ + 1` at `1`, where it reads the root `μ + 2` at `2`.  The label `C` of the cap
enters only through `λ_ξ + 3 ≤ C`. -/
theorem isStableRecoveryScheme_twinScheme (h : IsTwinCap ξ μ C) (o : Bool) {γ : Ordinal.{u}}
    (hγ : γ < blockStage ξ + 3) :
    (contextAt h).IsStableRecoveryScheme rootEmb (donorAt h o) γ (twinScheme.{u} o) := by
  have hc10 := card_comap_castSuccEmb.{u} o
  let b : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card := ⟨9, by omega⟩
  have hb : (twinScheme.{u} o).cellMap Fin.castSuccEmb b = 19 :=
    cellMap_castSuccEmb o (i := 9) rfl
  have huniq : ∀ u : Fin 23, twinCells.gradedIndex u = twinCells.gradedIndex 21 → u = 21 := by
    decide
  refine IsStableRecoveryScheme.of_readsThroughCap (restrictFace_rootAt h)
    (donorAt_mem_cofaces h o)
    ⟨(twinTypeAt h o).reduce (isSuccPrelimit_blockStage ξ), ⟨isLegal_twinScheme o, ?_⟩, rfl⟩
    map_extendByLast_mem_faces rfl (b := b) (b₀ := capAt h) rfl ?_ ?_ (s := 21) ?_ ?_ ?_
  · rw [restrictFace_reduce, restrictFace_twinTypeAt_castSuccEmb]
    rfl
  · rw [hb, label_capAt]
    exact h.labelAdd_three_le
  · rw [hb]
    exact_mod_cast hγ
  · rw [hb]
    -- membership below a pair is the order of graded indices
    change twinCells.gradedIndex 19 ≤ twinCells.gradedIndex 21
    decide
  · rw [hb]
    rfl
  intro i j hij hj
  have hj5 : (j : ℕ) < 5 := card_donorAt h o ▸ j.2
  rw [cellMap_extendByLast o (i := ⟨j, hj5⟩) (j := i) hij.symm,
    donorAt_label h o ⟨j, hj5⟩ j rfl]
  have hj0 : (⟨j, hj5⟩ : Fin 5) ≠ 0 := by
    have hs : Fin.last 1 ∈ fiveCells.scope ⟨j, hj5⟩ := by
      rw [← donorAt_scope h o ⟨j, hj5⟩ j rfl]
      exact hj
    have key : ∀ k : Fin 5, Fin.last 1 ∈ fiveCells.scope k → k ≠ 0 := by decide
    exact key _ hs
  generalize (⟨j, hj5⟩ : Fin 5) = k at hj0 ⊢
  have hbot : ∀ e : Fin 23, cellKind e = 0 →
      twinCells.gradedIndex e ≤ twinCells.gradedIndex 21 →
      e ∈ (twinScheme.{u} o).toCellScheme.below ((twinScheme.{u} o).toCellScheme.gradedIndex 21) ∧
        ∀ u, (twinScheme.{u} o).toCellScheme.gradedIndex u =
          (twinScheme.{u} o).toCellScheme.gradedIndex 21 →
          (contextAt h).ReadsThroughCap (twinScheme.{u} o) b u e ⊥ := fun e he0 he21 ↦
    ⟨he21, fun u hu ↦ by
      obtain rfl := huniq u hu
      intro he _
      refine ⟨fun _ ↦ ?_, fun h' ↦ absurd h' bot_ne_top,
        fun μ' n _ h' ↦ absurd h' WithBot.bot_ne_coe⟩
      -- the row of the reading cell, by kinds
      change kindRow o 5 (cellKind e) = ⊥
      rw [he0]
      rfl⟩
  have htwin : ∀ (e : Fin 23) (n₀ : ℕ), (n₀ = 1 ∨ n₀ = 2) →
      twinCells.gradedIndex e ≤ twinCells.gradedIndex 21 →
      kindRow.{u} o 5 (cellKind e) = gridPoint n₀ 0 →
      e ∈ (twinScheme.{u} o).toCellScheme.below ((twinScheme.{u} o).toCellScheme.gradedIndex 21) ∧
        ∀ u, (twinScheme.{u} o).toCellScheme.gradedIndex u =
          (twinScheme.{u} o).toCellScheme.gradedIndex 21 →
          (contextAt h).ReadsThroughCap (twinScheme.{u} o) b u e (labelAdd μ n₀) :=
    fun e n₀ hn₀ he21 hre ↦
      ⟨he21, fun u hu ↦ by
        obtain rfl := huniq u hu
        exact readsThroughCap_twinAt h o b hb hn₀ hre⟩
  fin_cases k
  · exact absurd rfl hj0
  · exact hbot 3 rfl (by decide)
  · cases o
    · exact htwin 6 1 (.inl rfl) (by decide) rfl
    · exact htwin 6 2 (.inr rfl) (by decide) rfl
  · cases o
    · exact htwin 7 2 (.inr rfl) (by decide) rfl
    · exact htwin 7 1 (.inl rfl) (by decide) rfl
  · exact hbot 15 rfl (by decide)

/-- **Stable recovery schemes for the graded cap calibration at every twin cap**: for a base `μ`
(zero or a limit, `μ ≤ λ_ξ`), a cap value `C ≥ λ_ξ + 3` at `λ_{ξ+1}`, an order `o` of the twins
and `γ < λ_ξ + 3`, there are a legal context `T⁺` on three points with a cap of grade `3` labelled
`C` and a reference cell of grade `1` labelled `μ + 2`, the embedding of a root on one point, a
coface `D` of the root with a new cell labelled `μ + 1`, satisfying the graded cap calibration,
and a stable recovery scheme. -/
theorem exists_isStableRecoveryScheme_twinFamily (h : IsTwinCap ξ μ C) (o : Bool)
    {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + 3) :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 3) (f : Fin 1 ↪ Fin 3)
      (P : StageType.{u} (blockStage (ξ + 1)) 1) (D : StageType.{u} (blockStage (ξ + 1)) 2),
      Tp.IsLegal ∧ restrictFace f Tp = some P ∧ D ∈ P.cofaces ∧ γ < blockStage (ξ + 1) ∧
        GradedCapCalibration ξ Tp f D γ ∧
        (∃ b, Tp.toCellScheme.grade b = 3 ∧ Tp.label b = C) ∧
        (∃ a, Tp.toCellScheme.grade a = 1 ∧ Tp.label a = labelAdd μ 2) ∧
        (∃ j : Fin D.card, Fin.last 1 ∈ D.toCellScheme.scope j ∧ D.label j = labelAdd μ 1) ∧
        ∃ E : Scheme.{u} 4, Tp.IsStableRecoveryScheme f D γ E := by
  refine ⟨contextAt h, rootEmb, rootAt h, donorAt h o, isLegal_contextAt h, restrictFace_rootAt h,
    donorAt_mem_cofaces h o, ?_, gradedCapCalibration_contextAt h o hγ,
    ⟨capAt h, grade_capAt h, label_capAt h⟩, ⟨refAt h, grade_refAt h, label_refAt h⟩,
    exists_lowerTwin h o, _, isStableRecoveryScheme_twinScheme h o hγ⟩
  refine hγ.trans ?_
  rw [blockStage_add_one]
  exact (add_lt_add_iff_left _).mpr (natCast_lt_omega0 3)

/-- The inputs of the twin caps lie in the binders of `StageType.HasStableRecoverySchemes`. -/
example (hS : HasStableRecoverySchemes ξ (GradedCapCalibration ξ)) (h : IsTwinCap ξ μ C)
    (o : Bool) {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + 3) (hγ' : γ < blockStage (ξ + 1)) :
    ∃ E, (contextAt h).IsStableRecoveryScheme rootEmb (donorAt h o) γ E :=
  hS (contextAt h) rootEmb (rootAt h) (isLegal_contextAt h) one_pos (restrictFace_rootAt h) _
    (donorAt_mem_cofaces h o) _ hγ' (gradedCapCalibration_contextAt h o hγ)

/-! ### A proper cap and a lower block -/

variable (ξ) in
/-- The twin cap with base `λ_ξ` and the proper cap `λ_ξ + 3`. -/
theorem isTwinCap_properCap :
    IsTwinCap ξ (blockStage ξ) (labelAdd (blockStage ξ) 3) := by
  refine ⟨isSuccPrelimit_blockStage ξ, le_rfl, le_rfl, .inl ?_⟩
  rw [blockStage_add_one]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_iff_left _).mpr (natCast_lt_omega0 3)))

variable (ξ) in
/-- **A proper cap**: with the cap labelled exactly `λ_ξ + 3`, the least value the graded cap
calibration allows at the grade `3`, and `γ = λ_ξ + 2`, the largest it allows, the twin scheme of
either order is a stable recovery scheme for the donor `(λ_ξ + 2, ⊥, λ_ξ + 2, λ_ξ + 1, ⊥)` of
that order.  The decoder reads the lower twin at `λ_ξ + 1 < λ_ξ + 3`. -/
theorem exists_isStableRecoveryScheme_properCap (o : Bool) :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 3) (f : Fin 1 ↪ Fin 3)
      (P : StageType.{u} (blockStage (ξ + 1)) 1) (D : StageType.{u} (blockStage (ξ + 1)) 2),
      Tp.IsLegal ∧ restrictFace f Tp = some P ∧ D ∈ P.cofaces ∧
        blockStage ξ + 2 < blockStage (ξ + 1) ∧
        GradedCapCalibration ξ Tp f D (blockStage ξ + 2) ∧
        (∃ b, Tp.toCellScheme.grade b = 3 ∧ Tp.label b = labelAdd (blockStage ξ) 3) ∧
        (∃ j : Fin D.card, Fin.last 1 ∈ D.toCellScheme.scope j ∧
          D.label j = labelAdd (blockStage ξ) 1) ∧
        ∃ E : Scheme.{u} 4, Tp.IsStableRecoveryScheme f D (blockStage ξ + 2) E := by
  obtain ⟨Tp, f, P, D, hl, hP, hD, hγ, hc, hb, -, hj, hE⟩ :=
    exists_isStableRecoveryScheme_twinFamily (isTwinCap_properCap ξ) o
      (γ := blockStage ξ + 2) ((add_lt_add_iff_left _).mpr (by exact_mod_cast (by omega : 2 < 3)))
  exact ⟨Tp, f, P, D, hl, hP, hD, hγ, hc, hb, hj, hE⟩

/-- **A lower block**: for a base `μ < λ_ξ` (zero or a limit), with the cap labelled `λ_ξ + 3` and
`γ = λ_ξ + 2`, the twin scheme of either order is a stable recovery scheme for the donor
`(μ + 2, ⊥, μ + 2, μ + 1, ⊥)` of that order: the reference cell (the root, labelled `μ + 2`) and
the new labels lie in the block of `μ`, below `λ_ξ`, and are kept by the reduction to `λ_ξ`. -/
theorem exists_isStableRecoveryScheme_lowerBlock (hμ : Order.IsSuccPrelimit μ)
    (hμξ : μ < blockStage ξ) (o : Bool) :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 3) (f : Fin 1 ↪ Fin 3)
      (P : StageType.{u} (blockStage (ξ + 1)) 1) (D : StageType.{u} (blockStage (ξ + 1)) 2),
      Tp.IsLegal ∧ restrictFace f Tp = some P ∧ D ∈ P.cofaces ∧
        blockStage ξ + 2 < blockStage (ξ + 1) ∧
        GradedCapCalibration ξ Tp f D (blockStage ξ + 2) ∧
        (∃ a, Tp.toCellScheme.grade a = 1 ∧ Tp.label a = labelAdd μ 2) ∧
        (∃ j : Fin D.card, Fin.last 1 ∈ D.toCellScheme.scope j ∧ D.label j = labelAdd μ 1) ∧
        ∃ E : Scheme.{u} 4, Tp.IsStableRecoveryScheme f D (blockStage ξ + 2) E := by
  have h : IsTwinCap ξ μ (labelAdd (blockStage ξ) 3) :=
    ⟨hμ, hμξ.le, le_rfl, (isTwinCap_properCap ξ).atStage⟩
  obtain ⟨Tp, f, P, D, hl, hP, hD, hγ, hc, -, ha, hj, hE⟩ :=
    exists_isStableRecoveryScheme_twinFamily h o
      (γ := blockStage ξ + 2) ((add_lt_add_iff_left _).mpr (by exact_mod_cast (by omega : 2 < 3)))
  exact ⟨Tp, f, P, D, hl, hP, hD, hγ, hc, ha, hj, hE⟩

end VaughtConjecture.Continuation.StableRecoveryTwinFamily
