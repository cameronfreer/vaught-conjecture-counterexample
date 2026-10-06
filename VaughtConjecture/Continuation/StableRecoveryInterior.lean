/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.StableRecoveryInteriorScheme

/-!
# A stable recovery scheme with an interior cap: coherent readings at two faces

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion), and Layer 3,
3.3 (the private cap, the marker and the decoder of (R4)); semantic contract, item 8.

**The question.**  (R4) follows from stable recovery schemes for the graded cap calibration at
every `ξ < ω₁` (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`), a finite statement
that is open.  A scheme reading through the cap at one cell `s` of the grade `N` of the cap is a
stable recovery scheme (`StageType.IsStableRecoveryScheme.of_readsThroughCap`), but by
bountifulness the reading constrains every graded face of grade `N` containing the cap and the new
cells.  In the instances of `VaughtConjecture.Continuation.StableRecoveryReading` and
`VaughtConjecture.Continuation.StableRecoveryTwin` there is one such face.  This file tests a
context in which there are two: the scope of the cap avoids both extreme points of the context.

**The input** (`contextType`, `rootEmb`, `rootType`, `donorType`).  The context `T⁺` on the four
points `0 < 1 < 2 < 3` (the interval plan) is the face along the first four points of the
labelled interior scheme (`interiorType`, on `interiorScheme` of
`VaughtConjecture.Continuation.StableRecoveryInteriorScheme`), with parameters the marker
`λ_ξ + 1` at the reference kind and the new kinds, and a cap value `B` at the cap and reading
kinds, for every `B` self-visible at `2`, at least `λ_ξ + 2` and occurring at `λ_{ξ+1}`: the
formal top, or a proper label `λ_ξ + M` with `M ≥ 2`.  The cap is the cell `({1, 2}, 2)`, labelled
`B`; its scope `{1, 2}` avoids the two extreme points `0` and `3` of the context
(`cap_scope_interior`).  The marker is the cell `({1, 2}, 1)`, labelled `λ_ξ + 1`.  The root is
the point `3` (one dead cell), and the donor `D` the face along `{3, 4}`: `⊥` at its new cells
`({4}, 1)` and `({3, 4}, 2)`, and `λ_ξ + 1` at the new cell `({3, 4}, 1)`.  The graded cap
calibration holds for every `γ < λ_ξ + 2` (`gradedCapCalibration_contextType`).

**Two faces, coherent readings.**  The graded faces of grade `2` of the interior scheme containing
the scope of the cap and the new point are `({1, 2, 3, 4}, 2)` and `(univ, 2)`
(`StableRecoveryInterior.eq_of_mem_faces_of_subset`), and each carries a reading cell, of the
reading kind.  The hypothesis of `of_readsThroughCap` holds at both
(`readsThroughCap_of_cellKind_eq_five`), so each reading cell alone makes the interior scheme a
stable recovery scheme (`isStableRecoveryScheme_of_cellKind_eq_five`).  The two readings are
coherent because the scheme is legal: the lawful labellings below the two faces are those of the
same reading triples (`StableRecoveryInterior.exists_of_isLawfulBelow`), and every pair lifts
capped (`StableRecoveryInterior.cappedLift_interiorScheme`).

**Every scheme has two such faces** (`StageType.IsStableRecoveryScheme.exists_face_ne_univ`,
`exists_face_ne_univ_of_isStableRecoveryScheme`).  In a well formed scheme on the points of `T⁺`
and the new point, the new point is an extreme point of the ground set (the points of `T⁺` span a
face), the other extreme point `y` is an extreme point of `T⁺`, and the face `univ \ {y}` contains
every set of points of `T⁺` without extreme points, together with the new point
(`Scheme.exists_face_ne_univ_of_not_mem`).  So at this input every stable recovery scheme, not only
the interior scheme, has a face other than its ground set containing the scope of the cap and the
new point: the two graded faces of grade `2` are forced.

**The result** (`exists_isStableRecoveryScheme_interiorCap`).  At every `ξ`, for every cap value
`B` as above and every `γ < λ_ξ + 2`, the input satisfies the graded cap calibration and has a
stable recovery scheme.  So the conclusion of
`StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds at these inputs;
several graded faces of grade `N` containing the cap and the new cells do not obstruct it here.

**What this does not show.**  The finite statement at every input is not proved, and (R4) stays
open.  The inputs are degenerate in other respects:

* recovery copies the marker: the new label is the reference label (`n = i = 1`, `c = 0` in
  `StageType.ReadsThroughCap`);
* no label of the donor is the formal top, so the clause on `γ` of
  `StageType.IsStableRecoveryScheme` and the branch at the formal top of
  `StageType.ReadsThroughCap` are not used;
* the root is one cell, labelled `⊥`, and `N = k + 1`;
* the two faces are nested (`{1, 2, 3, 4} ⊆ univ`); faces of grade `N` that are not nested need
  more points.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Continuation.StableRecoveryInterior

open Finset Label StageType
open StableRecoveryReading (IsReadingTriple markerLabel isSelfVisible_markerLabel
  eq_one_of_markerLabel_eq markerLabel_lt)
open Ordinal hiding univ

/-! ### The faces of the context and of the donor -/

/-- The **root embedding**: the point of the root is the point `3` of the context. -/
def rootEmb : Fin 1 ↪ Fin 4 := ⟨fun _ ↦ 3, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The root followed by the new point spans `{3, 4}`. -/
theorem map_extendByLast_eq : univ.map (extendByLast rootEmb) = ({3, 4} : Finset (Fin 5)) := by
  decide

/-- The root and the new point span a closed face. -/
theorem map_extendByLast_mem_faces : univ.map (extendByLast rootEmb) ∈ interiorCells.faces := by
  rw [map_extendByLast_eq]
  decide

/-- The first four points span a closed face, the context. -/
theorem map_castSuccEmb_mem_faces :
    univ.map (Fin.castSuccEmb : Fin 4 ↪ Fin 5) ∈ interiorCells.faces := by
  decide

/-- The root spans a closed face. -/
theorem map_rootEmb_mem_faces :
    univ.map (rootEmb.trans (Fin.castSuccEmb : Fin 4 ↪ Fin 5)) ∈ interiorCells.faces := by
  decide

/-- **The scope of the cap is interior**: the scope `{1, 2}` of the cap `({1, 2}, 2)` avoids the
two extreme points `0` and `3` of the context `{0, 1, 2, 3}`, whose deletions `{1, 2, 3}` and
`{0, 1, 2}` are closed faces. -/
theorem cap_scope_interior :
    interiorCells.scope 16 = {1, 2} ∧ ({1, 2, 3} : Finset (Fin 5)) ∈ interiorCells.faces ∧
      ({0, 1, 2} : Finset (Fin 5)) ∈ interiorCells.faces ∧
      (0 : Fin 5) ∉ interiorCells.scope 16 ∧ (3 : Fin 5) ∉ interiorCells.scope 16 := by
  decide

/-- The cells of the interior scheme visible through the root and the new point, in order: the
dead cells `({3}, 1)` and `({4}, 1)`, the new cell `({3, 4}, 1)`, and the dead cell
`({3, 4}, 2)`. -/
def donorCells : Fin 4 → Fin 35 := ![3, 4, 8, 18]

/-- The enumeration of the cells of the donor's face is increasing. -/
private theorem strictMono_donorCells : StrictMono donorCells := by
  rw [Fin.strictMono_iff_lt_succ]; decide

/-- The enumerated cells are the cells visible through the root and the new point. -/
private theorem mem_range_donorCells (d : Fin 35) :
    d ∈ Set.range donorCells ↔ d ∈ interiorScheme.{u}.visibleCells (extendByLast rootEmb) := by
  rw [Set.mem_range, Scheme.visibleCells, Finset.mem_filter, map_extendByLast_eq]
  -- the visible cells, with the scope of the interior scheme
  change (∃ y, donorCells y = d) ↔ d ∈ (univ : Finset (Fin 35)) ∧ interiorCells.scope d ⊆ {3, 4}
  revert d
  decide

/-- The cell map of the face along the root and the new point is `donorCells`. -/
theorem cellMap_extendByLast {i : Fin 4}
    {j : Fin (interiorScheme.{u}.comap (extendByLast rootEmb)).card} (hij : (i : ℕ) = j) :
    interiorScheme.{u}.cellMap (extendByLast rootEmb) j = donorCells i :=
  (interiorScheme.{u}.cellMap_eq_of_strictMono _ strictMono_donorCells mem_range_donorCells
    hij).symm

/-- The face along the root and the new point has four cells. -/
theorem card_comap_extendByLast : (interiorScheme.{u}.comap (extendByLast rootEmb)).card = 4 :=
  interiorScheme.{u}.card_visibleCells_eq_of_strictMono _ strictMono_donorCells
    mem_range_donorCells

/-- The cells of the interior scheme visible through the first four points, in order. -/
def contextCells : Fin 20 → Fin 35 :=
  ![0, 1, 2, 3, 5, 6, 7, 9, 10, 12, 15, 16, 17, 19, 20, 22, 25, 26, 28, 31]

/-- The enumeration of the cells of the context is increasing. -/
private theorem strictMono_contextCells : StrictMono contextCells := by
  rw [Fin.strictMono_iff_lt_succ]; decide

/-- The enumerated cells are the cells visible through the first four points. -/
private theorem mem_range_contextCells (d : Fin 35) :
    d ∈ Set.range contextCells ↔ d ∈ interiorScheme.{u}.visibleCells Fin.castSuccEmb := by
  have hu : univ.map (Fin.castSuccEmb : Fin 4 ↪ Fin 5) = {0, 1, 2, 3} := by decide
  rw [Set.mem_range, Scheme.visibleCells, Finset.mem_filter, hu]
  -- the visible cells, with the scope of the interior scheme
  change (∃ y, contextCells y = d) ↔
    d ∈ (univ : Finset (Fin 35)) ∧ interiorCells.scope d ⊆ {0, 1, 2, 3}
  revert d
  decide

/-- The context has twenty cells. -/
theorem card_comap_castSuccEmb : (interiorScheme.{u}.comap Fin.castSuccEmb).card = 20 :=
  interiorScheme.{u}.card_visibleCells_eq_of_strictMono _ strictMono_contextCells
    mem_range_contextCells

/-- The cell map of the face along the first four points is `contextCells`. -/
theorem cellMap_castSuccEmb {i : Fin 20}
    {j : Fin (interiorScheme.{u}.comap Fin.castSuccEmb).card} (hij : (i : ℕ) = j) :
    interiorScheme.{u}.cellMap Fin.castSuccEmb j = contextCells i :=
  (interiorScheme.{u}.cellMap_eq_of_strictMono _ strictMono_contextCells mem_range_contextCells
    hij).symm

/-! ### The labelled scheme -/

variable (ξ : Ordinal.{u}) {B : Label.{u}}

/-- The **labelled interior scheme** at `λ_{ξ+1}`, for a cap value `B` self-visible at `2` and
occurring at `λ_{ξ+1}`: the marker `λ_ξ + 1` at the reference, new and joint kinds, and `B` at the
cap and reading kinds. -/
noncomputable def interiorType (hB : IsSelfVisible 2 B ∧ AtStage (blockStage (ξ + 1)) B) :
    StageType.{u} (blockStage (ξ + 1)) 5 where
  toScheme := interiorScheme
  label := interiorLabel (markerLabel ξ) (markerLabel ξ) B
  isWellFormed := isLegal_interiorScheme.isWellFormed
  isCoded := isLegal_interiorScheme.isCoded
  isLawful := isLawful_interiorLabel
    ⟨isSelfVisible_markerLabel ξ, isSelfVisible_markerLabel ξ, hB.1, le_rfl, rfl⟩
  atStage d := by
    -- the label of a kind
    change AtStage _ (kindValue _ _ _ (cellKind d))
    obtain ⟨k, hk⟩ : ∃ k, cellKind d = k := ⟨_, rfl⟩
    rw [hk]
    fin_cases k
    · exact atStage_bot
    · exact .inl (markerLabel_lt ξ)
    · exact .inl (markerLabel_lt ξ)
    · exact .inl (markerLabel_lt ξ)
    · exact hB.2
    · exact hB.2

variable (hB : IsSelfVisible 2 B ∧ AtStage (blockStage (ξ + 1)) B)

/-- The **context** `T⁺` on four points: the face of the labelled interior scheme along the first
four points. -/
noncomputable def contextType : StageType.{u} (blockStage (ξ + 1)) 4 :=
  (interiorType ξ hB).comap Fin.castSuccEmb map_castSuccEmb_mem_faces

/-- The **donor** on two points: the face of the labelled interior scheme along the root and the
new point. -/
noncomputable def donorType : StageType.{u} (blockStage (ξ + 1)) 2 :=
  (interiorType ξ hB).comap (extendByLast rootEmb) map_extendByLast_mem_faces

/-- The **root** on one point: the face of the context along the root embedding. -/
noncomputable def rootType : StageType.{u} (blockStage (ξ + 1)) 1 :=
  (contextType ξ hB).comap rootEmb
    (((interiorType ξ hB).map_univ_mem_comap_faces_iff _ _ _).mpr map_rootEmb_mem_faces)

/-- The context is the face of the labelled interior scheme along the first four points. -/
theorem restrictFace_contextType :
    restrictFace Fin.castSuccEmb (interiorType ξ hB) = some (contextType ξ hB) :=
  restrictFace_of_mem _ _ _

/-- The root is the face of the context along the root embedding. -/
theorem restrictFace_rootType : restrictFace rootEmb (contextType ξ hB) = some (rootType ξ hB) :=
  restrictFace_of_mem _ _ _

/-- The context is legal. -/
theorem isLegal_contextType : (contextType ξ hB).IsLegal :=
  isLegal_interiorScheme.comap _ map_castSuccEmb_mem_faces

/-- The donor is a coface of the root. -/
theorem donorType_mem_cofaces : donorType ξ hB ∈ (rootType ξ hB).cofaces := by
  refine ⟨isLegal_interiorScheme.comap _ map_extendByLast_mem_faces, ?_⟩
  unfold donorType
  rw [restrictFace_trans _ _ _
      (restrictFace_of_mem (interiorType ξ hB) _ map_extendByLast_mem_faces),
    castSuccEmb_trans_extendByLast, ← restrictFace_trans _ _ _ (restrictFace_contextType ξ hB),
    restrictFace_rootType]

/-! ### The cap, the marker and the labels of the donor -/

/-- The context has twenty cells. -/
theorem card_contextType : (contextType ξ hB).card = 20 := card_comap_castSuccEmb

/-- The cap of the context: its cell `11`, the cell `({1, 2}, 2)` of the interior scheme. -/
noncomputable def contextCap : Fin (contextType ξ hB).card :=
  ⟨11, by rw [card_contextType]; omega⟩

/-- The marker of the context: its cell `5`, the cell `({1, 2}, 1)` of the interior scheme. -/
noncomputable def contextMarker : Fin (contextType ξ hB).card :=
  ⟨5, by rw [card_contextType]; omega⟩

/-- The cap of the context is the cell `16` of the interior scheme. -/
theorem cellMap_contextCap :
    interiorScheme.{u}.cellMap Fin.castSuccEmb (contextCap ξ hB) = 16 :=
  cellMap_castSuccEmb (i := 11) rfl

/-- The marker of the context is the cell `6` of the interior scheme. -/
theorem cellMap_contextMarker :
    interiorScheme.{u}.cellMap Fin.castSuccEmb (contextMarker ξ hB) = 6 :=
  cellMap_castSuccEmb (i := 5) rfl

/-- The cap of the context has grade `2`. -/
theorem grade_contextCap : (contextType ξ hB).toCellScheme.grade (contextCap ξ hB) = 2 := by
  -- the grade of a cell of the context is the grade of its cell
  change interiorCells.grade (interiorScheme.{u}.cellMap Fin.castSuccEmb (contextCap ξ hB)) = 2
  rw [cellMap_contextCap]
  rfl

/-- The cap of the context is labelled `B`. -/
theorem label_contextCap : (contextType ξ hB).label (contextCap ξ hB) = B := by
  -- the label of a cell of the context is the label of its cell
  change interiorLabel _ _ B (interiorScheme.{u}.cellMap Fin.castSuccEmb (contextCap ξ hB)) = B
  rw [cellMap_contextCap]
  rfl

/-- The scope of the cap of the context is `{1, 2}`: it avoids the extreme points `0` and `3`. -/
theorem scope_contextCap :
    (contextType ξ hB).toCellScheme.scope (contextCap ξ hB) = {1, 2} := by
  -- the scope of a cell of the face is the preimage of the scope of its cell
  change (interiorCells.scope (interiorScheme.{u}.cellMap Fin.castSuccEmb
    (contextCap ξ hB))).preimage Fin.castSuccEmb Fin.castSuccEmb.injective.injOn = _
  rw [cellMap_contextCap]
  ext x
  rw [Finset.mem_preimage]
  revert x
  decide

/-- The marker of the context has grade `1`. -/
theorem grade_contextMarker : (contextType ξ hB).toCellScheme.grade (contextMarker ξ hB) = 1 := by
  -- the grade of a cell of the context is the grade of its cell
  change interiorCells.grade (interiorScheme.{u}.cellMap Fin.castSuccEmb (contextMarker ξ hB)) = 1
  rw [cellMap_contextMarker]
  rfl

/-- The marker of the context is labelled `λ_ξ + 1`. -/
theorem label_contextMarker : (contextType ξ hB).label (contextMarker ξ hB) = markerLabel ξ := by
  -- the label of a cell of the context is the label of its cell
  change interiorLabel _ _ B (interiorScheme.{u}.cellMap Fin.castSuccEmb (contextMarker ξ hB)) =
    markerLabel ξ
  rw [cellMap_contextMarker]
  rfl

/-- The labels of the donor: `⊥` at the dead cells and `λ_ξ + 1` at the new cell `({3, 4}, 1)`. -/
theorem donorType_label (j : Fin (donorType ξ hB).card) (k : Fin 4) (hjk : (j : ℕ) = k) :
    (donorType ξ hB).label j = ![⊥, ⊥, markerLabel ξ, ⊥] k := by
  -- the label of a cell of the face is the label of its cell
  change interiorLabel _ _ B (interiorScheme.{u}.cellMap (extendByLast rootEmb) j) = _
  rw [cellMap_extendByLast (i := k) hjk.symm]
  fin_cases k <;> rfl

/-- The donor has four cells. -/
theorem card_donorType : (donorType ξ hB).card = 4 := card_comap_extendByLast

/-- **The context satisfies the graded cap calibration** for the root embedding, the donor and
every `γ < λ_ξ + 2`, for a cap value `B ≥ λ_ξ + 2`: the cap has grade `2 > 1`; the only ordinal
label of the donor is `λ_ξ + 1`, with the marker as its reference cell. -/
theorem gradedCapCalibration_contextType
    (hBcap : ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤ B)
    {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + ((2 : ℕ) : Ordinal.{u})) :
    GradedCapCalibration ξ (contextType ξ hB) rootEmb (donorType ξ hB) γ := by
  refine ⟨contextCap ξ hB, by rw [grade_contextCap, label_contextCap]; exact hBcap,
    by rw [grade_contextCap]; omega, by rw [grade_contextCap]; exact hγ, fun j o ho ↦ ?_⟩
  have hj : (j : ℕ) < 4 := card_donorType ξ hB ▸ j.2
  have hl := donorType_label ξ hB j ⟨j, hj⟩ rfl
  rw [ho] at hl
  generalize (⟨j, hj⟩ : Fin 4) = k at hl
  fin_cases k
  · exact absurd hl WithBot.coe_ne_bot
  · exact absurd hl WithBot.coe_ne_bot
  · obtain rfl : o = blockStage ξ + ((1 : ℕ) : Ordinal.{u}) :=
      WithTop.coe_injective (WithBot.coe_injective hl)
    refine ⟨blockStage ξ, 1, 1, contextMarker ξ hB, isSuccPrelimit_blockStage ξ, rfl, ?_, ?_, ?_,
      label_contextMarker ξ hB⟩
    · rw [grade_contextCap]; omega
    · rw [grade_contextCap]; omega
    · rw [grade_contextMarker, grade_contextCap]; omega
  · exact absurd hl WithBot.coe_ne_bot

/-! ### The readings at the two faces -/

/-- The reading cells (the cells of the reading kind) have grade `2` and lie above the dead new
cells `4`, `18`, the new cell `8`, the marker `6` and the cap `16`. -/
private theorem below_reading : ∀ s : Fin 35, cellKind s = 5 → interiorCells.grade s = 2 ∧
    ∀ d ∈ ({4, 6, 8, 16, 18} : Finset (Fin 35)),
      interiorCells.gradedIndex d ≤ interiorCells.gradedIndex s := by
  decide

/-- **Each reading cell reads the new cells through the cap**: for a cell `s` of the reading kind
(`({1, 2, 3, 4}, 2)` or `(univ, 2)`), every new cell of the donor lies below the graded index of
`s` and is read there through the cap (`StageType.ReadsThroughCap`) as a cell labelled as in the
donor: the dead new cells as `⊥`, and the new cell labelled `λ_ξ + 1` at `1`, where `s` reads the
marker at `1`.  This is the hypothesis of `StageType.IsStableRecoveryScheme.of_readsThroughCap` at
`s`, at both graded faces of grade `2` containing the cap and the new cell. -/
theorem readsThroughCap_of_cellKind_eq_five {s : Fin 35} (hs : cellKind s = 5) :
    ∀ (i : Fin (interiorScheme.{u}.comap (extendByLast rootEmb)).card)
      (j : Fin (donorType ξ hB).card), (i : ℕ) = j →
      Fin.last 1 ∈ (donorType ξ hB).toCellScheme.scope j →
        interiorScheme.{u}.cellMap (extendByLast rootEmb) i ∈
            interiorCells.below (interiorCells.gradedIndex s) ∧
          ∀ u, interiorCells.gradedIndex u = interiorCells.gradedIndex s →
            (contextType ξ hB).ReadsThroughCap interiorScheme (contextCap ξ hB) u
              (interiorScheme.{u}.cellMap (extendByLast rootEmb) i) ((donorType ξ hB).label j) := by
  intro i j hij hj
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨hgs, hbelow⟩ := below_reading s hs
  have hj4 : (i : ℕ) < 4 := lt_of_lt_of_eq i.2 card_comap_extendByLast
  have hmap : interiorScheme.{u}.cellMap (extendByLast rootEmb) i = donorCells ⟨i, hj4⟩ :=
    cellMap_extendByLast (i := ⟨i, hj4⟩) (j := i) rfl
  rw [hmap, donorType_label ξ hB i ⟨i, hj4⟩ rfl]
  have hj0 : (⟨i, hj4⟩ : Fin 4) ≠ 0 := by
    intro h0
    -- the scope of a cell of the face is the preimage of the scope of its cell
    have hsc : Fin.last 1 ∈ (interiorCells.scope (interiorScheme.{u}.cellMap
        (extendByLast rootEmb) i)).preimage (extendByLast rootEmb)
        (extendByLast rootEmb).injective.injOn := hj
    rw [hmap, h0, Finset.mem_preimage, extendByLast_last] at hsc
    exact absurd hsc (by decide)
  have huniq := fun u hu ↦ eq_of_gradedIndex_eq u s hu
  generalize (⟨i, hj4⟩ : Fin 4) = k at hj0 ⊢
  -- a dead new cell, read as `⊥` by the reading kind
  have hbot (e : Fin 35) (he0 : cellKind e = 0) (he : e ∈ ({4, 6, 8, 16, 18} : Finset (Fin 35))) :
      e ∈ interiorCells.below (interiorCells.gradedIndex s) ∧
        ∀ u, interiorCells.gradedIndex u = interiorCells.gradedIndex s →
          (contextType ξ hB).ReadsThroughCap interiorScheme (contextCap ξ hB) u e ⊥ :=
    ⟨hbelow e he, fun u hu ↦ by
      obtain rfl := huniq u hu
      intro _ _
      refine ⟨fun _ ↦ ?_, fun h ↦ absurd h bot_ne_top, fun μ n _ h ↦ absurd h WithBot.bot_ne_coe⟩
      -- the row of the reading cell, by kinds
      change kindRow (cellKind u) (cellKind e) = ⊥
      rw [hs, he0]
      rfl⟩
  fin_cases k
  · exact absurd rfl hj0
  · exact hbot 4 rfl (by decide)
  · -- the new cell `8`, labelled `λ_ξ + 1`, read at `1` with the marker
    refine ⟨hbelow 8 (by decide), fun u hu ↦ ?_⟩
    obtain rfl := huniq u hu
    have hgb : interiorCells.grade
        (interiorScheme.{u}.cellMap Fin.castSuccEmb (contextCap ξ hB)) = 2 := by
      rw [cellMap_contextCap]; rfl
    refine fun _ _ ↦ ⟨fun h ↦ absurd h WithBot.coe_ne_bot,
      fun h ↦ absurd (WithBot.coe_injective (h : markerLabel ξ = ⊤)) WithTop.coe_ne_top,
      fun μ n hμ h ↦ ?_⟩
    obtain rfl := eq_one_of_markerLabel_eq ξ hμ h
    have ha : interiorScheme.{u}.cellMap Fin.castSuccEmb (contextMarker ξ hB) ∈
        interiorCells.below (interiorCells.gradedIndex u) := by
      rw [cellMap_contextMarker]
      exact hbelow 6 (by decide)
    refine ⟨by rw [interiorScheme_toCellScheme.{u}, hgb]; omega, contextMarker ξ hB,
      contextMarker ξ hB, 1, ((0 : ℕ) : Ordinal.{u}), rfl, (label_contextMarker ξ hB).trans h,
      by rw [interiorScheme_toCellScheme.{u}, hgb]; omega, ha, ?_, ?_⟩
    · -- the row of the reading cell at the marker, by kinds
      change kindRow (cellKind u)
        (cellKind (interiorScheme.{u}.cellMap Fin.castSuccEmb (contextMarker ξ hB))) = _
      rw [cellMap_contextMarker, hs]
      rfl
    · -- the row of the reading cell at the new cell, by kinds
      change kindRow (cellKind u) (cellKind 8) = _
      rw [hs]
      rfl
  · exact hbot 18 rfl (by decide)

/-- **Either reading cell makes the interior scheme a stable recovery scheme** for the context,
the root embedding, the donor and every `γ < λ_ξ + 2` (for a cap value `B ≥ λ_ξ + 2`), by
`StageType.IsStableRecoveryScheme.of_readsThroughCap` at a cell `s` of the reading kind, at
`({1, 2, 3, 4}, 2)` or at `(univ, 2)`. -/
theorem isStableRecoveryScheme_of_cellKind_eq_five
    (hBcap : ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤ B)
    {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + ((2 : ℕ) : Ordinal.{u})) {s : Fin 35}
    (hs : cellKind s = 5) :
    (contextType ξ hB).IsStableRecoveryScheme rootEmb (donorType ξ hB) γ interiorScheme := by
  obtain ⟨hgs, hbelow⟩ := below_reading s hs
  have hgb : interiorCells.grade
      (interiorScheme.{u}.cellMap Fin.castSuccEmb (contextCap ξ hB)) = 2 := by
    rw [cellMap_contextCap]; rfl
  refine IsStableRecoveryScheme.of_readsThroughCap (restrictFace_rootType ξ hB)
    (donorType_mem_cofaces ξ hB)
    ⟨(interiorType ξ hB).reduce (isSuccPrelimit_blockStage ξ), ⟨isLegal_interiorScheme, ?_⟩, rfl⟩
    map_extendByLast_mem_faces rfl (b := contextCap ξ hB) (b₀ := contextCap ξ hB) rfl ?_ ?_
    (s := s) ?_ ?_ (readsThroughCap_of_cellKind_eq_five ξ hB hs)
  · rw [restrictFace_reduce, restrictFace_contextType]
    rfl
  · rw [interiorScheme_toCellScheme.{u}, hgb, label_contextCap]
    exact hBcap
  · rw [interiorScheme_toCellScheme.{u}, hgb]
    exact hγ
  · rw [cellMap_contextCap]
    exact hbelow 16 (by decide)
  · rw [interiorScheme_toCellScheme.{u}, hgb, hgs]

/-- **Stable recovery schemes for the graded cap calibration exist at a context with an interior
cap, at every `ξ`**: for every cap value `B` self-visible at `2`, at least `λ_ξ + 2` and occurring
at `λ_{ξ+1}` (the formal top or a proper label `λ_ξ + M`, `M ≥ 2`), and every `γ < λ_ξ + 2`, a
legal context `T⁺` on four points with a cap of grade `2` labelled `B` whose scope `{1, 2}` avoids
the extreme points `0` and `3`, the embedding of a root on one point, and a coface `D` of the root
with a new cell labelled `λ_ξ + 1`, satisfy the graded cap calibration and have a stable recovery
scheme.  So the conclusion of
`StageType.HasStableRecoverySchemes ξ (StageType.GradedCapCalibration ξ)` holds at these inputs,
where every scheme has at least two graded faces of grade `2` containing the cap and the new
cell. -/
theorem exists_isStableRecoveryScheme_interiorCap (hB2 : IsSelfVisible 2 B)
    (hBat : AtStage (blockStage (ξ + 1)) B)
    (hBcap : ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤ B)
    {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + ((2 : ℕ) : Ordinal.{u})) :
    ∃ (Tp : StageType.{u} (blockStage (ξ + 1)) 4) (f : Fin 1 ↪ Fin 4)
      (P : StageType.{u} (blockStage (ξ + 1)) 1) (D : StageType.{u} (blockStage (ξ + 1)) 2),
      Tp.IsLegal ∧ restrictFace f Tp = some P ∧ D ∈ P.cofaces ∧ γ < blockStage (ξ + 1) ∧
        GradedCapCalibration ξ Tp f D γ ∧
        (∃ b : Fin Tp.card, Tp.label b = B ∧ Tp.toCellScheme.grade b = 2 ∧
          Tp.toCellScheme.scope b = {1, 2}) ∧
        (∃ j : Fin D.card, Fin.last 1 ∈ D.toCellScheme.scope j ∧ D.label j = markerLabel ξ) ∧
        ∃ E : Scheme.{u} 5, Tp.IsStableRecoveryScheme f D γ E := by
  have hB : IsSelfVisible 2 B ∧ AtStage (blockStage (ξ + 1)) B := ⟨hB2, hBat⟩
  have hγ' : γ < blockStage (ξ + 1) := by
    rw [blockStage_add_one]
    exact hγ.trans (add_lt_add_right (natCast_lt_omega0 2) _)
  have hc : 2 < (interiorScheme.{u}.comap (extendByLast rootEmb)).card := by
    rw [card_comap_extendByLast]; omega
  refine ⟨contextType ξ hB, rootEmb, rootType ξ hB, donorType ξ hB, isLegal_contextType ξ hB,
    restrictFace_rootType ξ hB, donorType_mem_cofaces ξ hB, hγ',
    gradedCapCalibration_contextType ξ hB hBcap hγ,
    ⟨contextCap ξ hB, label_contextCap ξ hB, grade_contextCap ξ hB, scope_contextCap ξ hB⟩,
    ⟨⟨2, hc⟩, ?_, donorType_label ξ hB ⟨2, hc⟩ 2 rfl⟩, interiorScheme,
    isStableRecoveryScheme_of_cellKind_eq_five ξ hB hBcap hγ (s := 23) rfl⟩
  -- the scope of a cell of the face is the preimage of the scope of its cell
  change Fin.last 1 ∈ (interiorCells.scope (interiorScheme.{u}.cellMap (extendByLast rootEmb)
    ⟨2, hc⟩)).preimage (extendByLast rootEmb) (extendByLast rootEmb).injective.injOn
  rw [cellMap_extendByLast (i := 2) (j := ⟨2, hc⟩) rfl, Finset.mem_preimage, extendByLast_last]
  decide

/-- The inputs lie in the binders of `StageType.HasStableRecoverySchemes`. -/
example (h : HasStableRecoverySchemes ξ (GradedCapCalibration ξ))
    (hBcap : ((blockStage ξ + ((2 : ℕ) : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ≤ B)
    {γ : Ordinal.{u}} (hγ : γ < blockStage ξ + ((2 : ℕ) : Ordinal.{u})) :
    ∃ E, (contextType ξ hB).IsStableRecoveryScheme rootEmb (donorType ξ hB) γ E :=
  h (contextType ξ hB) rootEmb (rootType ξ hB) (isLegal_contextType ξ hB) one_pos
    (restrictFace_rootType ξ hB) _ (donorType_mem_cofaces ξ hB) _
    (by rw [blockStage_add_one]; exact hγ.trans (add_lt_add_right (natCast_lt_omega0 2) _))
    (gradedCapCalibration_contextType ξ hB hBcap hγ)

/-! ### Every scheme has two graded faces of grade `2` containing the cap and the new point -/

section Faces

variable {m : ℕ}

/-- **A face of the scheme avoiding an extreme point of the context**: in a well formed scheme on
`m + 1` points (`0 < m`) in which the first `m` points span a face, the new point `m` is an extreme
point of the ground set, and so is some other point `y`, which is then an extreme point of the
first `m` points.  So for a set `S` of the first `m` points containing no extreme point of them,
the face `univ \ {y}` is a face other than the ground set containing `S` and the new point.  The
proof uses that a closed set with at least two points has exactly two extreme points
(`Geometry.IsPlan.card_extremes`) and that faces are closed under intersection. -/
theorem _root_.VaughtConjecture.Scheme.exists_face_ne_univ_of_not_mem {E : Scheme.{u} (m + 1)}
    (hE : E.IsWellFormed)
    (hold : univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) ∈ E.toCellScheme.faces)
    (hm : 0 < m) {S : Finset (Fin m)}
    (hS : ∀ y : Fin m, (univ.erase y).map Fin.castSuccEmb ∈ E.toCellScheme.faces → y ∉ S) :
    ∃ F ∈ E.toCellScheme.faces, F ≠ univ ∧ S.map Fin.castSuccEmb ⊆ F ∧ Fin.last m ∈ F := by
  have hP : Geometry.IsPlan univ E.toCellScheme.faces := hE.ground_eq ▸ hE.isWellFormed.isPlan
  have h2 := hP.card_extremes hP.ground_mem (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hold' : univ.erase (Fin.last m) = univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
    ext x
    induction x using Fin.lastCases with
    | last => simp
    | cast x => simp [Fin.castSucc_ne_last]
  -- the new point is one extreme point of the ground set; `y` is the other
  obtain ⟨y, hy, hyl⟩ : ∃ y ∈ Geometry.extremes E.toCellScheme.faces univ, y ≠ Fin.last m := by
    by_contra! h
    have : Geometry.extremes E.toCellScheme.faces univ ⊆ {Fin.last m} := fun y hy ↦
      mem_singleton.mpr (h y hy)
    have := card_le_card this
    rw [card_singleton] at this
    omega
  obtain ⟨y', rfl⟩ := Fin.exists_castSucc_eq.mpr hyl
  have hyF : univ.erase (Fin.castSucc y') ∈ E.toCellScheme.faces := (mem_filter.mp hy).2
  -- `y` is an extreme point of the first `m` points
  have hcap := hP.infClosed hyF hold
  have heq : univ.erase (Fin.castSucc y') ⊓ univ.map (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) =
      (univ.erase y').map Fin.castSuccEmb := by
    ext x
    induction x using Fin.lastCases with
    | last => simp
    | cast x => simp
  rw [mem_coe, heq] at hcap
  have hyS := hS y' hcap
  refine ⟨_, hyF, fun h ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · have := h ▸ mem_univ (Fin.castSucc y')
    simp at this
  · obtain ⟨z, hz, rfl⟩ := mem_map.mp hx
    refine mem_erase.mpr ⟨fun h ↦ hyS ?_, mem_univ _⟩
    rwa [← Fin.castSucc_inj.mp h]
  · exact mem_erase.mpr ⟨(Fin.castSucc_ne_last y').symm, mem_univ _⟩

/-- **Every stable recovery scheme over an interior set has a second face**: if `E` is a stable
recovery scheme for `T⁺` on `m > 0` points and `S` is a set of points of `T⁺` containing no
extreme point of its ground set (no `y` with `univ \ {y}` a face of `T⁺`), then some face of `E`
other than its ground set contains `S` and the new point.  With `S` the scope of a cap of grade
`N` this gives two graded faces of grade `N` of `E` containing the cap and the new point: that
face and the ground set. -/
theorem _root_.VaughtConjecture.StageType.IsStableRecoveryScheme.exists_face_ne_univ
    {ξ : Ordinal.{u}} {k : ℕ} {Tp : StageType.{u} (blockStage (ξ + 1)) m} {f : Fin k ↪ Fin m}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} {E : Scheme.{u} (m + 1)}
    (h : Tp.IsStableRecoveryScheme f D γ E) (hm : 0 < m) {S : Finset (Fin m)}
    (hS : ∀ y : Fin m, univ.erase y ∈ Tp.toCellScheme.faces → y ∉ S) :
    ∃ F ∈ E.toCellScheme.faces, F ≠ univ ∧ S.map Fin.castSuccEmb ⊆ F ∧ Fin.last m ∈ F := by
  obtain ⟨⟨q, ⟨hql, hqf⟩, rfl⟩, -⟩ := h
  obtain ⟨hf, hcomap⟩ := (restrictFace_eq_some_iff _ _).mp hqf
  have hT : q.toScheme.comap Fin.castSuccEmb = Tp.toScheme :=
    (congrArg StageType.toScheme hcomap).trans (reduce_toScheme _ _)
  refine Scheme.exists_face_ne_univ_of_not_mem hql.isWellFormed hf hm fun y hy ↦ hS y ?_
  rw [← hT, Scheme.mem_comap_faces]
  exact hy

end Faces

/-- **At the interior cap every scheme has two graded faces of grade `2` containing the cap and the
new point**: every stable recovery scheme `E` for the context, the root embedding, the donor and
any `γ` has a face `F` other than its ground set containing the scope `{1, 2}` of the cap and the
new point `4`; so `(F, 2)` and `(univ, 2)` are two graded faces of grade `2` of `E` containing the
cap and the new cell.  The interior scheme is one such `E`, with `F = {1, 2, 3, 4}`
(`StableRecoveryInterior.eq_of_mem_faces_of_subset`). -/
theorem exists_face_ne_univ_of_isStableRecoveryScheme {γ : Ordinal.{u}} {E : Scheme.{u} 5}
    (h : (contextType ξ hB).IsStableRecoveryScheme rootEmb (donorType ξ hB) γ E) :
    ∃ F ∈ E.toCellScheme.faces, F ≠ univ ∧ ({1, 2} : Finset (Fin 5)) ⊆ F ∧ (4 : Fin 5) ∈ F := by
  obtain ⟨F, hF, hne, hS, h4⟩ := h.exists_face_ne_univ (S := {1, 2}) (by omega) fun y hy ↦ by
    -- the faces of the context are those of the interior scheme inside the first four points
    change univ.erase y ∈ (interiorScheme.{u}.comap Fin.castSuccEmb).toCellScheme.faces at hy
    rw [Scheme.mem_comap_faces] at hy
    change (univ.erase y).map Fin.castSuccEmb ∈ interiorCells.faces at hy
    revert y
    decide
  refine ⟨F, hF, hne, ?_, h4⟩
  have hmap : ({1, 2} : Finset (Fin 4)).map Fin.castSuccEmb = ({1, 2} : Finset (Fin 5)) := by
    decide
  rwa [hmap] at hS

end VaughtConjecture.Continuation.StableRecoveryInterior
