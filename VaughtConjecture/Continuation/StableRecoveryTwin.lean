/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryTwinScheme

/-!
# Stable recovery schemes for the twin donors

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap, the reference cells and the decoder of (R4)); semantic contract, item 8.

**The question.**  (R4) follows from stable recovery schemes for the graded cap calibration at
every `ξ < ω₁` (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`), a finite statement
that is open.  The marker and cap calibration is refuted at the twin root `twinRoot` (one point,
one cell labelled `λ_ξ + 2`) and its two donors `twinDonor₁`, `twinDonor₂`, the lifts
`(λ_ξ + 2, ⊥, λ_ξ + 2, λ_ξ + 1, ⊥)` and `(λ_ξ + 2, ⊥, λ_ξ + 1, λ_ξ + 2, ⊥)` of the five-cell type,
which order its twins both ways over the same face
(`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`).  This file
tests the graded cap calibration at the same root and donors.

**The result** (`exists_isStableRecoveryScheme_twinDonors`).  At every `ξ` there are a legal
context `T⁺` on three points (`contextType`), the embedding of the root as its point `2`
(`rootEmb`), with face `twinRoot`, and `γ = λ_ξ`, satisfying the graded cap calibration for both
donors (`gradedCapCalibration_contextType`), and each donor has a stable recovery scheme: the
twin scheme of its order (`isStableRecoveryScheme_twinScheme`, by
`StageType.IsStableRecoveryScheme.of_readsThroughCap`).  So the conclusion of
`StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds at both inputs;
it is not refuted there.  Three points is the least size of a context with the calibration at these
donors (`three_le_of_gradedCapCalibration`).

**The data.**  The labelled twin scheme (`twinType o`, on the legal scheme `twinScheme o` of
`VaughtConjecture.Continuation.StableRecoveryTwinScheme`) labels the root `λ_ξ + 2`, the higher
twin `λ_ξ + 2`, the lower twin `λ_ξ + 1` (with the cells of their kinds) and the cap and the
reading cell `⊤`.  Its face along the root and the new point is the donor of its order
(`comap_twinType_extendByLast`; the face of the twin scheme there is the five-cell scheme,
`comap_twinScheme_extendByLast`).  Its face along the first three points is `T⁺` for both orders
(`restrictFace_twinType_castSuccEmb`): the root `λ_ξ + 2` with its two copies, the cap `⊤` of
grade `3` at `({0, 1, 2}, 3)`, and dead cells.  The calibration: the cap has grade `3 > 1`, label
`⊤ ≥ λ_ξ + 3` and `λ_ξ < λ_ξ + 3`; the ordinal labels `λ_ξ + 2`, `λ_ξ + 1` of the donors have
finite parts below `3`, with the root (grade `1`, label `λ_ξ + 2`, offset `2 < 3`) as reference
cell.  The coface of `T⁺↓λ_ξ` on the scheme is the reduction of the labelled twin scheme.

**The reading** (`readsThroughCap_twin`).  The only cell of `(univ, 3)` is the reading cell; it
reads the new cells labelled `⊥` (`({3}, 1)` and `({2, 3}, 2)`) as `⊥`, and reads the twin
labelled `λ_ξ + 2` at `2` and the twin labelled `λ_ξ + 1` at `1`, in the block where it reads the
root at `2`.  The lower twin is recovered at an offset other than that of the reference cell
(`n = 1`, `i = 2`).

**The scheme depends on the donor** (`not_isStableRecoveryScheme_twinDonor₁_and_twinDonor₂`): for
every context with an embedding of one point and every `γ`, no scheme is a stable recovery scheme
for both donors (some stage type on it has the face `T⁺`, and its face along the root and the new
point would equal both donors at a twin).  Here the two twin schemes differ only in the row of the
reading cell.  This is a fact about `StageType.IsStableRecoveryScheme` alone, not an obstruction:
`StageType.HasStableRecoverySchemes` chooses the scheme after the donor, and the growth
construction of Layer 3, 3.4, builds its scheme from the donor by design.

**What this does not show.**  `StageType.HasStableRecoverySchemes ξ
(StageType.GradedCapCalibration ξ)` asks for a stable recovery scheme at every legal `T⁺`,
embedding, coface `D` and `γ` with the calibration; it is proved at these two inputs only, and
stays open, and (R4) with it.  The inputs are still special:

* no label of the donors is `⊤`, so the clause on `γ` of `StageType.IsStableRecoveryScheme` and
  the branch at `⊤` of `StageType.ReadsThroughCap` are not used;
* the cap is `⊤` in `T⁺`, and the higher twin copies the reference label (`n = i = 2`);
* `(univ, 3)` is the only graded face of grade `N = 3` containing the cap and the new cells: the
  cap of grade `3` has all three points of `T⁺` as its scope; several such faces need a context of
  at least four points (informal; not compiled);
* the references are in the block `λ_ξ` only (no reference cell below `λ_ξ`);
* the reference cell is the root itself, a cell of the face `twinRoot` along `rootEmb`: the
  private context supplies only the cap.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryTwin

open Finset Label StageType CandidateCounterexamples StableRecoveryCounterexample
open Ordinal hiding univ

/-! ### The face along the root and the new point -/

/-- The **root embedding**: the point of the root is the point `2` of the context. -/
def rootEmb : Fin 1 ↪ Fin 3 := ⟨fun _ ↦ 2, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The root followed by the new point spans `{2, 3}`. -/
theorem map_extendByLast_eq : univ.map (extendByLast rootEmb) = ({2, 3} : Finset (Fin 4)) := by
  decide

/-- The root and the new point span a closed face. -/
theorem map_extendByLast_mem_faces : univ.map (extendByLast rootEmb) ∈ twinCells.faces := by
  rw [map_extendByLast_eq]
  decide

/-- The first three points span a closed face, the context. -/
theorem map_castSuccEmb_mem_faces :
    univ.map (Fin.castSuccEmb : Fin 3 ↪ Fin 4) ∈ twinCells.faces := by
  decide

/-- The cells of the twin scheme visible through the root and the new point, in order: the root,
the dead cell `({3}, 1)`, the twins, and the dead cell `({2, 3}, 2)`. -/
def donorCells : Fin 5 → Fin 23 := ![2, 3, 6, 7, 15]

/-- The enumeration of the cells of the donor's face is increasing. -/
private theorem strictMono_donorCells : StrictMono donorCells := by
  rw [Fin.strictMono_iff_lt_succ]; decide

/-- The enumerated cells are the cells visible through the root and the new point. -/
private theorem mem_range_donorCells (o : Bool) (d : Fin 23) :
    d ∈ Set.range donorCells ↔ d ∈ (twinScheme.{u} o).visibleCells (extendByLast rootEmb) := by
  rw [Set.mem_range, Scheme.visibleCells, Finset.mem_filter, map_extendByLast_eq]
  -- the visible cells, with the scope of the twin scheme
  change (∃ y, donorCells y = d) ↔ d ∈ (univ : Finset (Fin 23)) ∧ twinCells.scope d ⊆ {2, 3}
  revert d
  decide

/-- The cell map of the face along the root and the new point is `donorCells`. -/
theorem cellMap_extendByLast (o : Bool) {i : Fin 5}
    {j : Fin ((twinScheme.{u} o).comap (extendByLast rootEmb)).card} (hij : (i : ℕ) = j) :
    (twinScheme.{u} o).cellMap (extendByLast rootEmb) j = donorCells i :=
  ((twinScheme.{u} o).cellMap_eq_of_strictMono _ strictMono_donorCells
    (mem_range_donorCells o) hij).symm

/-- **The face of the twin scheme along the root and the new point is the five-cell scheme**, for
either order of the twins: the twins' rows read the root and themselves at `ω + 2` and each other
at `1`. -/
theorem comap_twinScheme_extendByLast (o : Bool) :
    (twinScheme.{u} o).comap (extendByLast rootEmb) = fiveCellScheme := by
  have hcard : ((twinScheme.{u} o).comap (extendByLast rootEmb)).card = 5 :=
    (twinScheme.{u} o).card_visibleCells_eq_of_strictMono _ strictMono_donorCells
      (mem_range_donorCells o)
  refine Scheme.ext hcard ?_ ?_ (fun i j hij ↦ ?_) (fun i j hij ↦ ?_)
    (fun s s' t t' hss' htt' ↦ ?_)
  · ext x; simp [twinCells, fiveCells]
  · ext C
    rw [Scheme.mem_comap_faces]
    -- the faces of the twin scheme and of the five-cell scheme
    change C.map (extendByLast rootEmb) ∈ twinCells.faces ↔ C ∈ fiveCells.faces
    revert C
    decide
  · rw [Scheme.comap_scope, cellMap_extendByLast o hij.symm]
    have key : ∀ (j : Fin 5) (x : Fin 2),
        extendByLast rootEmb x ∈ twinCells.scope (donorCells j) ↔ x ∈ fiveCells.scope j := by
      decide
    exact Finset.ext fun x ↦ by rw [Finset.mem_preimage]; exact key j x
  · rw [Scheme.comap_grade, cellMap_extendByLast o hij.symm]
    have key : ∀ j : Fin 5, twinCells.grade (donorCells j) = fiveCells.grade j := by decide
    exact key j
  · rw [Scheme.comap_row]
    -- the rows of the face, by kinds
    change kindRow o (cellKind ((twinScheme.{u} o).cellMap (extendByLast rootEmb) s))
      (cellKind ((twinScheme.{u} o).cellMap (extendByLast rootEmb) t.1)) = fiveCellRows s' t'.1
    rw [cellMap_extendByLast o hss'.symm, cellMap_extendByLast o htt'.symm]
    have key : ∀ a x : Fin 5, fiveCells.gradedIndex x ≤ fiveCells.gradedIndex a →
        kindRow.{u} o (cellKind (donorCells a)) (cellKind (donorCells x)) = fiveCellRows a x := by
      intro a x
      cases o <;> fin_cases a <;> fin_cases x <;> first | (intro; rfl) |
        (intro h; exact absurd h (by decide))
    exact key s' t'.1 t'.2

/-! ### The labelled scheme -/

variable (ξ : Ordinal.{u})

/-- The labels of the labelled scheme: root and higher twin `λ_ξ + 2`, lower twin `λ_ξ + 1`, cap
the formal top. -/
theorem isTwinTuple_marker :
    IsTwinTuple (labelAdd (blockStage ξ) 2) (labelAdd (blockStage ξ) 2) (labelAdd (blockStage ξ) 1)
      ⊤ := by
  have hμ := isSuccPrelimit_blockStage ξ
  refine ⟨isSelfVisible_coe_add hμ (by omega), isSelfVisible_coe_add hμ (by omega),
    isSelfVisible_coe_add hμ le_rfl, isSelfVisible_top _, le_rfl, ?_, le_max_left _ _, ?_,
    by simp, ?_⟩
  · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
      ((add_le_add_iff_left _).mpr (Nat.cast_le.mpr (by omega : 1 ≤ 2))))
  · rw [min_top_right]
    exact visibilityReplace_coe_add_natCast hμ (by omega) 2
  · rw [min_top_right, min_top_right, min_top_right]
    exact (visibilityReplace_coe_add_natCast hμ (by omega) 1).symm

/-- A label `λ_ξ + n` occurs at `λ_{ξ+1}`. -/
private theorem atStage_labelAdd (n : ℕ) :
    AtStage (blockStage (ξ + 1)) (labelAdd (blockStage ξ) n) := by
  refine .inl ?_
  rw [blockStage_add_one]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr
    ((add_lt_add_iff_left _).mpr (natCast_lt_omega0 n)))

/-- The **labelled twin scheme** at `λ_{ξ+1}`, for the order `o` of the twins: the root `λ_ξ + 2`,
the higher twin `λ_ξ + 2` and the lower `λ_ξ + 1` (with the cells of their kinds), and the formal
top at the cap and the reading cell. -/
noncomputable def twinType (o : Bool) : StageType.{u} (blockStage (ξ + 1)) 4 where
  toScheme := twinScheme o
  label := twinLabel (labelAdd (blockStage ξ) 2)
    (twinHi o (labelAdd (blockStage ξ) 2) (labelAdd (blockStage ξ) 1))
    (twinLo o (labelAdd (blockStage ξ) 2) (labelAdd (blockStage ξ) 1)) ⊤
  isWellFormed := (isLegal_twinScheme o).isWellFormed
  isCoded := (isLegal_twinScheme o).isCoded
  isLawful := isLawful_twinLabel (by rw [twinHi_twinHi, twinLo_twinHi]; exact isTwinTuple_marker ξ)
  atStage d := by
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    simp only [twinLabel, hk]
    fin_cases k
    · exact atStage_bot
    · exact atStage_labelAdd ξ 2
    · cases o
      exacts [atStage_labelAdd ξ 1, atStage_labelAdd ξ 2]
    · cases o
      exacts [atStage_labelAdd ξ 2, atStage_labelAdd ξ 1]
    · exact atStage_top
    · exact atStage_top

/-- The **donor** for the order `o` of the twins: `twinDonor₁` (the first twin above the second)
for `o = true`, `twinDonor₂` for `o = false`. -/
noncomputable abbrev twinDonor (o : Bool) : StageType.{u} (blockStage (ξ + 1)) 2 :=
  twinHi o (twinDonor₁ ξ) (twinDonor₂ ξ)

/-- **The face of the labelled twin scheme along the root and the new point is the donor.** -/
theorem comap_twinType_extendByLast (o : Bool) :
    (twinType ξ o).comap (extendByLast rootEmb) map_extendByLast_mem_faces = twinDonor ξ o := by
  cases o <;> refine StageType.ext (comap_twinScheme_extendByLast _) fun i j hij ↦ ?_ <;>
  · change twinLabel _ _ _ ⊤ ((twinScheme.{u} _).cellMap (extendByLast rootEmb) i) = _
    rw [cellMap_extendByLast _ (i := j) hij.symm]
    fin_cases j <;> rfl

/-- The face map of the labelled twin scheme along the root and the new point is the donor. -/
theorem restrictFace_twinType_extendByLast (o : Bool) :
    restrictFace (extendByLast rootEmb) (twinType ξ o) = some (twinDonor ξ o) := by
  rw [restrictFace_of_mem _ _ map_extendByLast_mem_faces, comap_twinType_extendByLast]

/-- The **context** `T⁺` on three points: the face of the labelled twin scheme along the first
three points, with the root, its copies, the cap and dead cells. -/
noncomputable def contextType : StageType.{u} (blockStage (ξ + 1)) 3 :=
  (twinType ξ true).comap Fin.castSuccEmb map_castSuccEmb_mem_faces

/-- The cells of the twin scheme visible through the first three points, in order. -/
def contextCells : Fin 10 → Fin 23 := ![0, 1, 2, 4, 5, 8, 13, 14, 16, 19]

/-- The enumeration of the cells of the context is increasing. -/
private theorem strictMono_contextCells : StrictMono contextCells := by
  rw [Fin.strictMono_iff_lt_succ]; decide

/-- The enumerated cells are the cells visible through the first three points. -/
private theorem mem_range_contextCells (o : Bool) (d : Fin 23) :
    d ∈ Set.range contextCells ↔ d ∈ (twinScheme.{u} o).visibleCells Fin.castSuccEmb := by
  have hu : univ.map (Fin.castSuccEmb : Fin 3 ↪ Fin 4) = {0, 1, 2} := by decide
  rw [Set.mem_range, Scheme.visibleCells, Finset.mem_filter, hu]
  -- the visible cells, with the scope of the twin scheme
  change (∃ y, contextCells y = d) ↔ d ∈ (univ : Finset (Fin 23)) ∧ twinCells.scope d ⊆ {0, 1, 2}
  revert d
  decide

/-- The context has ten cells. -/
theorem card_comap_castSuccEmb (o : Bool) :
    ((twinScheme.{u} o).comap Fin.castSuccEmb).card = 10 :=
  (twinScheme.{u} o).card_visibleCells_eq_of_strictMono _ strictMono_contextCells
    (mem_range_contextCells o)

/-- The cell map of the face along the first three points is `contextCells`. -/
theorem cellMap_castSuccEmb (o : Bool) {i : Fin 10}
    {j : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card} (hij : (i : ℕ) = j) :
    (twinScheme.{u} o).cellMap Fin.castSuccEmb j = contextCells i :=
  ((twinScheme.{u} o).cellMap_eq_of_strictMono _ strictMono_contextCells
    (mem_range_contextCells o) hij).symm

/-- **The face along the first three points does not depend on the order of the twins.** -/
theorem comap_twinScheme_castSuccEmb :
    (twinScheme.{u} false).comap Fin.castSuccEmb = (twinScheme.{u} true).comap Fin.castSuccEmb := by
  have hc : ((twinScheme.{u} false).comap Fin.castSuccEmb).card =
      ((twinScheme.{u} true).comap Fin.castSuccEmb).card :=
    (card_comap_castSuccEmb false).trans (card_comap_castSuccEmb true).symm
  refine Scheme.ext hc
    (by rw [Scheme.comap_ground, Scheme.comap_ground])
    (by ext C; rw [Scheme.mem_comap_faces, Scheme.mem_comap_faces]) (fun i j hij ↦ ?_)
    (fun i j hij ↦ ?_) (fun s s' t t' hss' htt' ↦ ?_)
  · have hk : (i : ℕ) < 10 := card_comap_castSuccEmb false ▸ i.2
    rw [Scheme.comap_scope, Scheme.comap_scope,
      cellMap_castSuccEmb false (i := ⟨i, hk⟩) (j := i) rfl,
      cellMap_castSuccEmb true (i := ⟨i, hk⟩) (j := j) hij]
  · have hk : (i : ℕ) < 10 := card_comap_castSuccEmb false ▸ i.2
    rw [Scheme.comap_grade, Scheme.comap_grade,
      cellMap_castSuccEmb false (i := ⟨i, hk⟩) (j := i) rfl,
      cellMap_castSuccEmb true (i := ⟨i, hk⟩) (j := j) hij]
  · have hk : (s : ℕ) < 10 := card_comap_castSuccEmb false ▸ s.2
    have hk' : (t.1 : ℕ) < 10 := card_comap_castSuccEmb false ▸ t.1.2
    rw [Scheme.comap_row, Scheme.comap_row]
    -- the rows of the faces, by kinds
    change kindRow false (cellKind ((twinScheme.{u} false).cellMap Fin.castSuccEmb s))
        (cellKind ((twinScheme.{u} false).cellMap Fin.castSuccEmb t.1)) =
      kindRow true (cellKind ((twinScheme.{u} true).cellMap Fin.castSuccEmb s'))
        (cellKind ((twinScheme.{u} true).cellMap Fin.castSuccEmb t'.1))
    rw [cellMap_castSuccEmb false (i := ⟨s, hk⟩) (j := s) rfl,
      cellMap_castSuccEmb true (i := ⟨s, hk⟩) (j := s') hss',
      cellMap_castSuccEmb false (i := ⟨t.1, hk'⟩) (j := t.1) rfl,
      cellMap_castSuccEmb true (i := ⟨t.1, hk'⟩) (j := t'.1) htt']
    have h5 : ∀ a : Fin 10, cellKind (contextCells a) ≠ 5 := by decide
    rw [kindRow_of_ne false (h5 _), kindRow_of_ne true (h5 _)]

/-- **The context does not depend on the order of the twins**: the face of the labelled twin
scheme along the first three points is `contextType` for both orders. -/
theorem restrictFace_twinType_castSuccEmb (o : Bool) :
    restrictFace Fin.castSuccEmb (twinType ξ o) = some (contextType ξ) := by
  rw [restrictFace_of_mem _ _ map_castSuccEmb_mem_faces]
  cases o
  swap
  · rfl
  refine congrArg some (StageType.ext comap_twinScheme_castSuccEmb fun i j hij ↦ ?_)
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  -- the labels of the faces are those of the twin schemes at the visible cells
  change twinLabel _ _ _ ⊤ ((twinScheme.{u} false).cellMap Fin.castSuccEmb ⟨i, hi⟩) =
    twinLabel _ _ _ ⊤ ((twinScheme.{u} true).cellMap Fin.castSuccEmb ⟨j, hj⟩)
  have hk : i < 10 := card_comap_castSuccEmb false ▸ hi
  rw [cellMap_castSuccEmb false (i := ⟨i, hk⟩) (j := ⟨i, hi⟩) rfl,
    cellMap_castSuccEmb true (i := ⟨i, hk⟩) (j := ⟨j, hj⟩) hij]
  have h23 : ∀ a : Fin 10, cellKind (contextCells a) ≠ 2 ∧ cellKind (contextCells a) ≠ 3 := by
    decide
  exact kindValue_of_ne (h23 _).1 (h23 _).2

/-- **The root of the context is the twin root.** -/
theorem restrictFace_rootEmb_contextType :
    restrictFace rootEmb (contextType ξ) = some (twinRoot ξ) := by
  rw [restrictFace_trans _ _ _ (restrictFace_twinType_castSuccEmb ξ true),
    ← castSuccEmb_trans_extendByLast,
    ← restrictFace_trans _ _ _ (restrictFace_twinType_extendByLast ξ true)]
  exact restrictFace_of_mem _ _ map_castSuccEmb_mem_faces_fiveCells

/-- The context is legal. -/
theorem isLegal_contextType : (contextType ξ).IsLegal :=
  (isLegal_twinScheme true).comap _ map_castSuccEmb_mem_faces

/-- Both donors are cofaces of the twin root. -/
theorem twinDonor_mem_cofaces (o : Bool) : twinDonor ξ o ∈ (twinRoot ξ).cofaces := by
  cases o
  · exact ⟨isLegal_fiveCellScheme, restrictFace_twinDonor₂ ξ⟩
  · exact twinDonor₁_mem_cofaces ξ

/-! ### The cap and the reference cell of the context -/

/-- The context has ten cells. -/
theorem card_contextType : (contextType ξ).card = 10 := card_comap_castSuccEmb true

/-- The cap of the context: its cell `9`, the cell `({0, 1, 2}, 3)` of the twin scheme. -/
noncomputable def contextCap : Fin (contextType ξ).card := ⟨9, by rw [card_contextType]; omega⟩

/-- The reference cell of the context: its cell `2`, the root `({2}, 1)`. -/
noncomputable def contextRoot : Fin (contextType ξ).card := ⟨2, by rw [card_contextType]; omega⟩

/-- The cap of the context has grade `3`. -/
theorem grade_contextCap : (contextType ξ).toCellScheme.grade (contextCap ξ) = 3 := by
  -- the grade of a cell of the context is the grade of its cell
  change twinCells.grade ((twinScheme.{u} true).cellMap Fin.castSuccEmb (contextCap ξ)) = 3
  rw [cellMap_castSuccEmb true (i := 9) (j := contextCap ξ) rfl]
  rfl

/-- The cap of the context is labelled the formal top. -/
theorem label_contextCap : (contextType ξ).label (contextCap ξ) = ⊤ := by
  -- the label of a cell of the context is the label of its cell
  change twinLabel _ _ _ ⊤ ((twinScheme.{u} true).cellMap Fin.castSuccEmb (contextCap ξ)) = ⊤
  rw [cellMap_castSuccEmb true (i := 9) (j := contextCap ξ) rfl]
  rfl

/-- The root of the context has grade `1`. -/
theorem grade_contextRoot : (contextType ξ).toCellScheme.grade (contextRoot ξ) = 1 := by
  -- the grade of a cell of the context is the grade of its cell
  change twinCells.grade ((twinScheme.{u} true).cellMap Fin.castSuccEmb (contextRoot ξ)) = 1
  rw [cellMap_castSuccEmb true (i := 2) (j := contextRoot ξ) rfl]
  rfl

/-- The root of the context is labelled `λ_ξ + 2`. -/
theorem label_contextRoot : (contextType ξ).label (contextRoot ξ) = labelAdd (blockStage ξ) 2 := by
  -- the label of a cell of the context is the label of its cell
  change twinLabel _ _ _ ⊤ ((twinScheme.{u} true).cellMap Fin.castSuccEmb (contextRoot ξ)) = _
  rw [cellMap_castSuccEmb true (i := 2) (j := contextRoot ξ) rfl]
  rfl

/-- The finite part of a label `λ_ξ + n` is `n`, in every normal form `μ + m` with `μ` zero or a
limit. -/
private theorem eq_of_labelAdd_eq {β μ : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β)
    (hμ : Order.IsSuccPrelimit μ) {n m : ℕ}
    (h : labelAdd β n = ((μ + m : Ordinal.{u}) : Label.{u})) : m = n := by
  have h' : β + n = μ + m := by
    simpa only [labelAdd, WithBot.coe_inj, WithTop.coe_inj] using h
  exact ((Label.add_natCast_eq_add_natCast_iff hβ hμ).mp h').2.symm

/-- The labels of the donors: `λ_ξ + 2` at the root, `⊥` at the dead cells, and `λ_ξ + 2`,
`λ_ξ + 1` at the twins. -/
private theorem twinDonor_label (o : Bool) (j : Fin 5) :
    (twinDonor ξ o).label (Fin.cast (by cases o <;> rfl) j) =
      ![labelAdd (blockStage ξ) 2, ⊥, twinHi o (labelAdd (blockStage ξ) 2)
        (labelAdd (blockStage ξ) 1), twinLo o (labelAdd (blockStage ξ) 2)
        (labelAdd (blockStage ξ) 1), ⊥] j := by
  cases o <;> fin_cases j <;> rfl

/-- **The twin donors need a context of at least three points**: the graded cap calibration for a
twin donor asks for a cap of grade above the finite part `2` of the root label `λ_ξ + 2`, and the
grades of a stage type on `m` points are at most `m` (`StageType.grade_le`). -/
theorem three_le_of_gradedCapCalibration {m : ℕ} {Tp : StageType.{u} (blockStage (ξ + 1)) m}
    {f : Fin 1 ↪ Fin m} {γ : Ordinal.{u}} {o : Bool}
    (h : GradedCapCalibration ξ Tp f (twinDonor ξ o) γ) : 3 ≤ m := by
  obtain ⟨b, -, -, -, href⟩ := h
  have hl := twinDonor_label ξ o 0
  obtain ⟨μ, n, -, -, hμ, ho, hn, -⟩ :=
    href (Fin.cast (by cases o <;> rfl) 0) (blockStage ξ + ((2 : ℕ) : Ordinal.{u})) hl
  have h2 : n = 2 := eq_of_labelAdd_eq (isSuccPrelimit_blockStage ξ) hμ
    (congrArg (fun x : Ordinal.{u} ↦ ((x : Ordinal.{u}) : Label.{u})) ho)
  have := Tp.grade_le b
  omega

/-- **The graded cap calibration holds for both donors**, at `γ = λ_ξ`: the cap of the context has
grade `3 > 1` and label the formal top, `λ_ξ < λ_ξ + 3`; the ordinal labels `λ_ξ + 2` and
`λ_ξ + 1` of the donors have finite parts below `3`, with the root `λ_ξ + 2` (grade `1`) as
reference cell. -/
theorem gradedCapCalibration_contextType (o : Bool) :
    GradedCapCalibration ξ (contextType ξ) rootEmb (twinDonor ξ o) (blockStage ξ) := by
  have hμ := isSuccPrelimit_blockStage ξ
  refine ⟨contextCap ξ, by rw [label_contextCap]; exact le_top, by rw [grade_contextCap]; omega,
    by rw [grade_contextCap]; exact lt_add_of_pos_right _ (by simp), fun j x hx ↦ ?_⟩
  have hj : (j : ℕ) < 5 := by cases o <;> exact j.2
  have hl := twinDonor_label ξ o ⟨j, hj⟩
  rw [show (Fin.cast (by cases o <;> rfl) ⟨j, hj⟩ : Fin (twinDonor ξ o).card) = j from rfl,
    hx] at hl
  have hgr : ∀ n : ℕ, n < 3 → (x : Label.{u}) = labelAdd (blockStage ξ) n →
      ∃ (μ : Ordinal.{u}) (n i : ℕ) (a : Fin (contextType ξ).card), Order.IsSuccPrelimit μ ∧
        x = μ + n ∧ n < (contextType ξ).toCellScheme.grade (contextCap ξ) ∧
        i < (contextType ξ).toCellScheme.grade (contextCap ξ) ∧
        (contextType ξ).toCellScheme.grade a ≤ (contextType ξ).toCellScheme.grade (contextCap ξ) ∧
        (contextType ξ).label a = ((μ + i : Ordinal.{u}) : Label.{u}) := fun n hn hxn ↦
    ⟨blockStage ξ, n, 2, contextRoot ξ, hμ, WithTop.coe_injective (WithBot.coe_injective hxn),
      by rw [grade_contextCap]; exact hn, by rw [grade_contextCap]; omega,
      by rw [grade_contextCap, grade_contextRoot]; omega, label_contextRoot ξ⟩
  generalize (⟨j, hj⟩ : Fin 5) = k at hl
  fin_cases k <;> cases o <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, twinHi_true, twinHi_false, twinLo_true, twinLo_false] at hl
  all_goals first
    | exact absurd hl WithBot.coe_ne_bot
    | exact hgr 2 (by omega) hl
    | exact hgr 1 (by omega) hl

/-! ### The stable recovery schemes -/

/-- `λ_ξ + n = μ + n` for `n ∈ {1, 2}` gives `λ_ξ + 2 = μ + 2`. -/
private theorem labelAdd_two_eq {μ : Ordinal.{u}} {n : ℕ} (hn : n = 1 ∨ n = 2)
    (h : labelAdd (blockStage ξ) n = ((μ + n : Ordinal.{u}) : Label.{u})) :
    labelAdd (blockStage ξ) 2 = ((μ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) := by
  have h' : blockStage ξ + (n : Ordinal.{u}) = μ + n :=
    WithTop.coe_injective (WithBot.coe_injective h)
  have h2 : ((2 : ℕ) : Ordinal.{u}) = ((1 : ℕ) : Ordinal.{u}) + ((1 : ℕ) : Ordinal.{u}) :=
    Nat.cast_add 1 1
  rcases hn with rfl | rfl
  · have : blockStage ξ + ((2 : ℕ) : Ordinal.{u}) = μ + ((2 : ℕ) : Ordinal.{u}) := by
      rw [h2, ← add_assoc, ← add_assoc, h']
    exact congrArg (fun x : Ordinal.{u} ↦ ((x : Ordinal.{u}) : Label.{u})) this
  · exact h

/-- **The reading cell reads a twin through the cap**: a new cell `e` labelled `λ_ξ + n₀`
(`n₀ ∈ {1, 2}`), read by the reading cell `21` at `n₀`, is read through the cap, with the root
`λ_ξ + 2` of the context, read at `2`, as reference cell. -/
theorem readsThroughCap_twin (o : Bool)
    (b : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card)
    (hb : (twinScheme.{u} o).cellMap Fin.castSuccEmb b = 19) {n₀ : ℕ} (hn₀ : n₀ = 1 ∨ n₀ = 2)
    {e : Fin 23} (hre : kindRow.{u} o 5 (cellKind e) = gridPoint n₀ 0) :
    (contextType ξ).ReadsThroughCap (twinScheme.{u} o) b 21 e (labelAdd (blockStage ξ) n₀) := by
  have hc10 := card_comap_castSuccEmb.{u} o
  let a : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card := ⟨2, by omega⟩
  have ha : (twinScheme.{u} o).cellMap Fin.castSuccEmb a = 2 :=
    cellMap_castSuccEmb o (i := 2) rfl
  have hgb : (twinScheme.{u} o).toCellScheme.grade
      ((twinScheme.{u} o).cellMap Fin.castSuccEmb b) = 3 := by rw [hb]; rfl
  intro he _
  refine ⟨fun h ↦ absurd h WithBot.coe_ne_bot,
    fun h ↦ absurd (WithBot.coe_injective h) WithTop.coe_ne_top, fun μ n hμ h ↦ ?_⟩
  obtain rfl : n = n₀ := eq_of_labelAdd_eq (isSuccPrelimit_blockStage ξ) hμ h
  have ha21 : (twinScheme.{u} o).cellMap Fin.castSuccEmb a ∈
      (twinScheme.{u} o).toCellScheme.below ((twinScheme.{u} o).toCellScheme.gradedIndex 21) := by
    rw [ha]
    -- membership below a pair is the order of graded indices
    change twinCells.gradedIndex 2 ≤ twinCells.gradedIndex 21
    decide
  refine ⟨by rw [hgb]; omega, a, contextRoot ξ, 2, ((0 : ℕ) : Ordinal.{u}), rfl,
    (label_contextRoot ξ).trans (labelAdd_two_eq ξ hn₀ h), by rw [hgb]; omega, ha21, ?_, ?_⟩
  · -- the row of the reading cell, by kinds
    change kindRow o 5 (cellKind ((twinScheme.{u} o).cellMap Fin.castSuccEmb a)) = _
    rw [ha]
    rfl
  · exact hre

/-- **The twin scheme is a stable recovery scheme** for the context, the root embedding, the
donor of the order `o` and `γ = λ_ξ`, by `StageType.IsStableRecoveryScheme.of_readsThroughCap`
at the reading cell `21` (the only cell of `(univ, 3)`): it reads the new cells labelled `⊥` (the
cells `({3}, 1)` and `({2, 3}, 2)`) as `⊥`, the twin labelled `λ_ξ + 2` at `2` and the twin
labelled `λ_ξ + 1` at `1`, where it reads the root `λ_ξ + 2` at `2`. -/
theorem isStableRecoveryScheme_twinScheme (o : Bool) :
    (contextType ξ).IsStableRecoveryScheme rootEmb (twinDonor ξ o) (blockStage ξ)
      (twinScheme.{u} o) := by
  have hc10 := card_comap_castSuccEmb.{u} o
  let b : Fin ((twinScheme.{u} o).comap Fin.castSuccEmb).card := ⟨9, by omega⟩
  have hb : (twinScheme.{u} o).cellMap Fin.castSuccEmb b = 19 :=
    cellMap_castSuccEmb o (i := 9) rfl
  have huniq : ∀ u : Fin 23, twinCells.gradedIndex u = twinCells.gradedIndex 21 → u = 21 := by
    decide
  refine IsStableRecoveryScheme.of_readsThroughCap (restrictFace_rootEmb_contextType ξ)
    (twinDonor_mem_cofaces ξ o)
    ⟨(twinType ξ o).reduce (isSuccPrelimit_blockStage ξ), ⟨isLegal_twinScheme o, ?_⟩, rfl⟩
    map_extendByLast_mem_faces (by cases o <;> exact comap_twinScheme_extendByLast _)
    (b := b) (b₀ := contextCap ξ) rfl ?_ ?_ (s := 21) ?_ ?_ ?_
  · rw [restrictFace_reduce, restrictFace_twinType_castSuccEmb]
    rfl
  · rw [hb, label_contextCap]
    exact le_top
  · rw [hb]
    exact lt_add_of_pos_right _ (by rw [show twinCells.grade 19 = 3 from rfl]; simp)
  · rw [hb]
    -- membership below a pair is the order of graded indices
    change twinCells.gradedIndex 19 ≤ twinCells.gradedIndex 21
    decide
  · rw [hb]
    rfl
  intro i j hij hj
  have hj5 : (j : ℕ) < 5 := by cases o <;> exact j.2
  rw [cellMap_extendByLast o (i := ⟨j, hj5⟩) (j := i) hij.symm]
  have hl := twinDonor_label ξ o ⟨j, hj5⟩
  rw [show (Fin.cast (by cases o <;> rfl) ⟨j, hj5⟩ : Fin (twinDonor ξ o).card) = j from rfl] at hl
  rw [hl]
  have hj0 : (⟨j, hj5⟩ : Fin 5) ≠ 0 := by
    have hs : Fin.last 1 ∈ fiveCells.scope ⟨j, hj5⟩ := by cases o <;> exact hj
    have key : ∀ k : Fin 5, Fin.last 1 ∈ fiveCells.scope k → k ≠ 0 := by decide
    exact key _ hs
  generalize (⟨j, hj5⟩ : Fin 5) = k at hj0 ⊢
  have hbot : ∀ e : Fin 23, cellKind e = 0 →
      twinCells.gradedIndex e ≤ twinCells.gradedIndex 21 →
      e ∈ (twinScheme.{u} o).toCellScheme.below ((twinScheme.{u} o).toCellScheme.gradedIndex 21) ∧
        ∀ u, (twinScheme.{u} o).toCellScheme.gradedIndex u =
          (twinScheme.{u} o).toCellScheme.gradedIndex 21 →
          (contextType ξ).ReadsThroughCap (twinScheme.{u} o) b u e ⊥ := fun e he0 he21 ↦
    ⟨he21, fun u hu ↦ by
      obtain rfl := huniq u hu
      intro he _
      refine ⟨fun _ ↦ ?_, fun h ↦ absurd h bot_ne_top, fun μ n _ h ↦ absurd h WithBot.bot_ne_coe⟩
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
          (contextType ξ).ReadsThroughCap (twinScheme.{u} o) b u e
            (labelAdd (blockStage ξ) n₀) := fun e n₀ hn₀ he21 hre ↦
    ⟨he21, fun u hu ↦ by
      obtain rfl := huniq u hu
      exact readsThroughCap_twin ξ o b hb hn₀ hre⟩
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

/-! ### The two donors at one context -/

/-- **Stable recovery schemes for the graded cap calibration exist at the twin donors, at every
`ξ`**: a legal context `T⁺` on three points whose face along the root embedding is the twin root
`twinRoot`, and `γ = λ_ξ < λ_{ξ+1}`, satisfy the graded cap calibration for both donors
`twinDonor₁` and `twinDonor₂`, and each donor has a stable recovery scheme (the twin scheme of its
order of the twins).  So the conclusion of
`StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds at these two
inputs, which share `T⁺`, the embedding and `γ`. -/
theorem exists_isStableRecoveryScheme_twinDonors :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 3) (f : Fin 1 ↪ Fin 3) (γ : Ordinal.{u}),
      Tp.IsLegal ∧ restrictFace f Tp = some (twinRoot ξ) ∧ γ < blockStage (ξ + 1) ∧
      GradedCapCalibration ξ Tp f (twinDonor₁ ξ) γ ∧ GradedCapCalibration ξ Tp f (twinDonor₂ ξ) γ ∧
      (∃ E, Tp.IsStableRecoveryScheme f (twinDonor₁ ξ) γ E) ∧
      ∃ E, Tp.IsStableRecoveryScheme f (twinDonor₂ ξ) γ E :=
  ⟨contextType ξ, rootEmb, blockStage ξ, isLegal_contextType ξ,
    restrictFace_rootEmb_contextType ξ, blockStage_lt_blockStage_add_one ξ,
    gradedCapCalibration_contextType ξ true, gradedCapCalibration_contextType ξ false,
    ⟨_, isStableRecoveryScheme_twinScheme ξ true⟩, ⟨_, isStableRecoveryScheme_twinScheme ξ false⟩⟩

/-- The two inputs lie in the binders of `StageType.HasStableRecoverySchemes`. -/
example (h : HasStableRecoverySchemes ξ (GradedCapCalibration ξ)) (o : Bool) :
    ∃ E, (contextType ξ).IsStableRecoveryScheme rootEmb (twinDonor ξ o) (blockStage ξ) E :=
  h (contextType ξ) rootEmb (twinRoot ξ) (isLegal_contextType ξ) one_pos
    (restrictFace_rootEmb_contextType ξ) _ (twinDonor_mem_cofaces ξ o) _
    (blockStage_lt_blockStage_add_one ξ) (gradedCapCalibration_contextType ξ o)

/-- **No scheme recovers both twin donors**: for every context `T⁺` with an embedding `f` of one
point and every `γ`, no scheme is a stable recovery scheme for both `twinDonor₁` and `twinDonor₂`.
Some stage type on it has face `T⁺` (`StageType.IsStableRecoveryScheme.exists_stageType`), and its
face along `f` followed by the new point would equal both donors at the twin `2`, where they are
`λ_ξ + 2` and `λ_ξ + 1`.  So a stable recovery scheme depends on the donor, not only on `T⁺` and
the root: here the twin schemes of the two orders differ in the row of the reading cell. -/
theorem not_isStableRecoveryScheme_twinDonor₁_and_twinDonor₂ {m : ℕ}
    {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin 1 ↪ Fin m} {γ : Ordinal.{u}}
    {E : Scheme.{u} (m + 1)} (h₁ : Tp.IsStableRecoveryScheme f (twinDonor₁ ξ) γ E)
    (h₂ : Tp.IsStableRecoveryScheme f (twinDonor₂ ξ) γ E) : False := by
  obtain ⟨Q', hQ'E, hQ'f⟩ := h₁.exists_stageType
  obtain ⟨Q, hQ, hQS, hl⟩ := h₁.2 Q' hQ'E hQ'f
  obtain ⟨Q₂, hQ₂, -, hl₂⟩ := h₂.2 Q' hQ'E hQ'f
  obtain rfl : Q = Q₂ := Option.some_inj.mp (hQ.symm.trans hQ₂)
  have hc : Q.card = 5 := congrArg Scheme.card hQS
  have hne : ∀ n : ℕ, labelAdd (blockStage ξ) n ≠ ⊤ := fun n h ↦
    WithTop.coe_ne_top (WithBot.coe_injective h)
  have e₁ := (hl ⟨2, by omega⟩ (2 : Fin 5) rfl).1 (hne 2)
  have e₂ := (hl₂ ⟨2, by omega⟩ (2 : Fin 5) rfl).1 (hne 1)
  exact not_labelAdd_two_le_one (e₁.symm.trans e₂).le

end VaughtConjecture.Continuation.StableRecoveryTwin
