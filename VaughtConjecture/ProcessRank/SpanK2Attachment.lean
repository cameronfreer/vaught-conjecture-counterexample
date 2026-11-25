/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanMirrorDisjoint
import VaughtConjecture.ProcessRank.SpanTestLegal

/-!
# The attachment of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: the eight-cell attachment on `Fin 4` of
two copies of the test scheme (`ProcessRank.testScheme`), one on each of the pure faces
`leftFace = {0, 1}` and `rightFace = {2, 3}`, over the interval plan of `Fin 4`.

* `ProcessRank.k2Attachment`: the scheme; `ProcessRank.k2AttachmentType`: the stage type at the
  stage `ω ^ 2` with the labels `k2Left` on `{0, 1}` and `k2Right` on `{2, 3}`
  (`ProcessRank.isLawful_k2AttLabel`: witnesses `lowTop id` and `lowTop shiftOmega`, suppressor
  `⊤`).
* `ProcessRank.exists_restrictFace_leftEmb`, `ProcessRank.exists_restrictFace_rightEmb`: the faces
  along the embeddings of `Fin 2` onto `{0, 1}` and `{2, 3}` are the test types with `k2Left` and
  `k2Right` (`ProcessRank.IsTestType`: the test scheme, its rows, and the labels).
* `ProcessRank.scope_k2Attachment`: every cell has scope inside `{0, 1}` or inside `{2, 3}`.
* `ProcessRank.mixedFacesOf_intervalPlan`: the mixed faces of the interval plan of `Fin 4` are
  `{1, 2}`, `{0, 1, 2}` and `{1, 2, 3}`.

Legality of the attachment type is not claimed (it has no cells on the mixed faces); the master
scheme over it, the ladder and the controllers are later work.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- The scopes of the cells of the attachment: the test cells on `{0, 1}`, then on `{2, 3}`. -/
def attScope : Fin 8 → Finset (Fin 4) := ![{0}, {1}, {0, 1}, {0, 1}, {2}, {3}, {2, 3}, {2, 3}]

/-- The grades of the cells of the attachment. -/
def attGrade : Fin 8 → ℕ := ![1, 1, 1, 2, 1, 1, 1, 2]

/-- The test cell copied by a cell of the attachment. -/
def attCell (d : Fin 8) : Fin 4 := ⟨d % 4, Nat.mod_lt _ (by omega)⟩

/-- The coded vector read by every row of the attachment: the test row on each copy. -/
noncomputable def attRow (d : Fin 8) : Label.{u} := testRow (attCell d)

/-- **The attachment of the test with `K = 2`**: eight cells on `Fin 4`, the four cells of the test
scheme on `{0, 1}` and their copies on `{2, 3}`, over the interval plan of `Fin 4`, every row
reading `attRow`. -/
noncomputable def k2Attachment : Scheme.{u} 4 where
  card := 8
  toCellScheme := ⟨univ, Geometry.intervalPlan univ, attScope, attGrade⟩
  rows := ⟨fun _ t ↦ attRow t.1⟩

/-- The labels on the attachment: `k2Left` on `{0, 1}` and `k2Right` on `{2, 3}`. -/
noncomputable def k2AttLabel (d : Fin 8) : Label.{u} :=
  if (d : ℕ) < 4 then k2Left (attCell d) else k2Right (attCell d)

/-- The embedding of `Fin 2` onto `{0, 1}`. -/
def leftEmb : Fin 2 ↪ Fin 4 := Fin.castAddEmb 2

/-- The embedding of `Fin 2` onto `{2, 3}`. -/
def rightEmb : Fin 2 ↪ Fin 4 := Fin.natAddEmb 2

theorem isWellFormed_k2Attachment : k2Attachment.{u}.IsWellFormed :=
  ⟨rfl, ⟨inferInstance, Geometry.isPlan_intervalPlan _, fun d ↦ by
    change (attScope d ∈ Geometry.intervalPlan univ ∧ 0 < attGrade d ∧
      attGrade d ≤ #(attScope d))
    fin_cases d <;> decide⟩⟩

theorem isCoded_k2Attachment : k2Attachment.{u}.IsCoded := fun _ t ↦
  testRow_lt_omega0_sq (attCell t.1)

/-- **Every cell of the attachment lies on one side**: its scope lies in `{0, 1}` or in
`{2, 3}` (the premise `hAtt` of `ProcessRank.MirrorAttachment.cappedLift_mirror_disjoint`). -/
theorem scope_k2Attachment (e : Fin k2Attachment.{u}.card) :
    k2Attachment.{u}.toCellScheme.scope e ⊆ MirrorAttachment.leftFace ∨
      k2Attachment.{u}.toCellScheme.scope e ⊆ MirrorAttachment.rightFace := by
  change attScope e ⊆ MirrorAttachment.leftFace ∨ attScope e ⊆ MirrorAttachment.rightFace
  fin_cases e <;> decide

/-- **The mixed faces of the interval plan of `Fin 4`** are `{1, 2}`, `{0, 1, 2}` and
`{1, 2, 3}`. -/
theorem mixedFacesOf_intervalPlan :
    MirrorAttachment.mixedFacesOf (Geometry.intervalPlan univ) = {{1, 2}, {0, 1, 2}, {1, 2, 3}} :=
        by
  decide

/-! ### The stage type over the attachment -/

theorem k2_loc_left {s d : Fin 8} (hs : (s : ℕ) < 4)
    (h : attScope d ⊆ attScope s ∧ attGrade d ≤ attGrade s) :
    min (k2AttLabel.{u} d) (k2AttLabel s) = lowTop id (attRow d) := by
  rw [attRow, lowTop_testRow]
  revert hs h
  fin_cases s <;> fin_cases d <;>
    first
    | exact fun hs ↦ absurd hs (by decide)
    | exact fun _ h ↦ absurd h (by decide)
    | (intro _ _; simp [k2AttLabel, attCell, k2Left])

theorem k2_loc_right {s d : Fin 8} (hs : ¬ (s : ℕ) < 4)
    (h : attScope d ⊆ attScope s ∧ attGrade d ≤ attGrade s) :
    min (k2AttLabel.{u} d) (k2AttLabel s) = lowTop shiftOmega (attRow d) := by
  rw [attRow, lowTop_testRow, shiftOmega_omega0_add_one]
  revert hs h
  fin_cases s <;> fin_cases d <;>
    first
    | exact fun hs ↦ absurd hs (by decide)
    | exact fun _ h ↦ absurd h (by decide)
    | (intro _ _; simp [k2AttLabel, attCell, k2Right])

/-- **The labels `k2Left` and `k2Right` form a lawful section of the attachment**: the witness
`lowTop id` at the cells of `{0, 1}`, `lowTop shiftOmega` at those of `{2, 3}`, suppressor `⊤`. -/
theorem isLawful_k2AttLabel : k2Attachment.{u}.rows.IsLawful k2AttLabel where
  orderly d := by
    change IsSelfVisible (attGrade d) (k2AttLabel d)
    fin_cases d
    all_goals first
      | exact isSelfVisible_top _
      | exact isSelfVisible_omega0_add_one
      | exact isSelfVisible_omega0_mul_two_add_one
  locality s := by
    by_cases hs : (s : ℕ) < 4
    · refine ⟨fun _ ↦ ⊤, lowTop id, isWitness_lowTop rfl monotone_id (fun _ _ _ ↦ rfl)
        antitone_const (fun n ↦ isSelfVisible_top n), fun d ↦ ?_⟩
      rw [min_top_right]
      exact k2_loc_left hs d.2
    · refine ⟨fun _ ↦ ⊤, lowTop shiftOmega, isWitness_lowTop rfl monotone_shiftOmega
        (fun k i x ↦ (visibilityReplace_shiftOmega k i x).symm) antitone_const
        (fun n ↦ isSelfVisible_top n), fun d ↦ ?_⟩
      rw [min_top_right]
      exact k2_loc_right hs d.2
  availability s t hst hg := ⟨t, rfl, by
    change attScope s ⊆ attScope t at hst
    change attGrade s = attGrade t at hg
    revert hst hg
    fin_cases s <;> fin_cases t <;>
      first
      | exact fun _ _ ↦ le_rfl
      | exact fun _ _ ↦ le_top
      | exact fun h ↦ absurd h (by decide)⟩

/-- **The stage type over the attachment** at the stage `ω ^ 2`, with the labels `k2Left` on
`{0, 1}` and `k2Right` on `{2, 3}`. -/
noncomputable def k2AttachmentType : StageType.{u} (ω ^ 2) 4 where
  toScheme := k2Attachment
  label := k2AttLabel
  isWellFormed := isWellFormed_k2Attachment
  isCoded := isCoded_k2Attachment
  isLawful := isLawful_k2AttLabel
  atStage d := by
    fin_cases d
    all_goals first
      | exact .inr rfl
      | exact atStage_omega0_add_one
      | exact atStage_lit_two_one

/-! ### The faces of the attachment type -/

/-- The cells of the attachment on the left side, in order. -/
def attEmbLeft (j : Fin 4) : Fin k2Attachment.{u}.card := ⟨j + 0, by change _ < 8; omega⟩

theorem strictMono_attEmbLeft : StrictMono attEmbLeft.{u} := fun i j h ↦ by
  change (i : ℕ) + 0 < j + 0
  have : (i : ℕ) < j := h
  omega

theorem mem_visibleCells_leftEmb_iff (d : Fin k2Attachment.{u}.card) :
    d ∈ k2Attachment.{u}.visibleCells leftEmb ↔ (d : ℕ) < 4 := by
  unfold Scheme.visibleCells
  rw [Finset.mem_filter]
  simp only [mem_univ, true_and]
  exact (by decide : ∀ d : Fin 8, attScope d ⊆ univ.map leftEmb ↔ (d : ℕ) < 4) d

theorem mem_range_attEmbLeft_iff (d : Fin k2Attachment.{u}.card) :
    d ∈ Set.range attEmbLeft.{u} ↔ d ∈ k2Attachment.{u}.visibleCells leftEmb := by
  rw [mem_visibleCells_leftEmb_iff]
  constructor
  · rintro ⟨j, rfl⟩
    change (j : ℕ) + 0 < 4
    omega
  · intro h
    have hd8 : (d : ℕ) < 8 := d.2
    exact ⟨⟨d - 0, by omega⟩, Fin.ext (by change (d : ℕ) - 0 + 0 = d; omega)⟩

theorem cellMap_leftEmb {i : Fin (k2Attachment.{u}.comap leftEmb).card} {j : Fin 4}
    (hij : (i : ℕ) = j) : k2Attachment.{u}.cellMap leftEmb i = attEmbLeft.{u} j :=
  (k2Attachment.cellMap_eq_of_strictMono leftEmb strictMono_attEmbLeft mem_range_attEmbLeft_iff
    hij.symm).symm

theorem attCell_attEmbLeft (j : Fin 4) : attCell (attEmbLeft.{u} j) = j :=
  Fin.ext (by change ((j : ℕ) + 0) % 4 = j; omega)

/-- **The face of the attachment type on the left side is the test type with k2Left.** -/
theorem isTestType_comap_leftEmb (hf : univ.map leftEmb ∈ k2AttachmentType.{u}.toCellScheme.faces) :
    IsTestType (k2AttachmentType.{u}.comap leftEmb hf) k2Left := by
  refine ⟨Scheme.ext (k2Attachment.card_visibleCells_eq_of_strictMono leftEmb
    strictMono_attEmbLeft mem_range_attEmbLeft_iff) ?_ ?_ (fun i j hij ↦ ?_) (fun i j hij ↦ ?_)
    (fun s s' t t' _ ht ↦ ?_), fun i j hij ↦ ?_⟩
  · change (univ : Finset (Fin 4)).preimage leftEmb leftEmb.injective.injOn = univ
    simp
  · change (Geometry.intervalPlan univ).preimage (Finset.map leftEmb)
      (map_injective leftEmb).injOn = Geometry.intervalPlan univ
    ext C
    rw [Finset.mem_preimage]
    revert C
    decide
  · change (attScope (k2Attachment.cellMap leftEmb i)).preimage leftEmb leftEmb.injective.injOn =
      testScope j
    rw [cellMap_leftEmb hij]
    clear hij
    ext x
    rw [Finset.mem_preimage]
    revert x
    fin_cases j <;> decide
  · change attGrade (k2Attachment.cellMap leftEmb i) = testGrade j
    rw [cellMap_leftEmb hij]
    clear hij
    fin_cases j <;> rfl
  · change attRow (k2Attachment.cellMap leftEmb t.1) = testRow t'.1
    rw [cellMap_leftEmb ht]
    exact congrArg testRow (attCell_attEmbLeft t'.1)
  · change k2AttLabel (k2Attachment.cellMap leftEmb i) = _
    rw [cellMap_leftEmb hij]
    exact (ite_eq_left (by change (j : ℕ) + 0 < 4; omega)).trans (congrArg _ (attCell_attEmbLeft j))

/-- **The face of the attachment type along the embedding onto the left side** is the test type
with k2Left. -/
theorem exists_restrictFace_leftEmb :
    ∃ p, StageType.restrictFace leftEmb k2AttachmentType.{u} = some p ∧ IsTestType p k2Left := by
  have hf : univ.map leftEmb ∈ k2AttachmentType.{u}.toCellScheme.faces := by
    change univ.map leftEmb ∈ Geometry.intervalPlan univ
    decide
  exact ⟨_, StageType.restrictFace_of_mem _ leftEmb hf, isTestType_comap_leftEmb hf⟩

/-- The cells of the attachment on the right side, in order. -/
def attEmbRight (j : Fin 4) : Fin k2Attachment.{u}.card := ⟨j + 4, by change _ < 8; omega⟩

theorem strictMono_attEmbRight : StrictMono attEmbRight.{u} := fun i j h ↦ by
  change (i : ℕ) + 4 < j + 4
  have : (i : ℕ) < j := h
  omega

theorem mem_visibleCells_rightEmb_iff (d : Fin k2Attachment.{u}.card) :
    d ∈ k2Attachment.{u}.visibleCells rightEmb ↔ ¬ (d : ℕ) < 4 := by
  unfold Scheme.visibleCells
  rw [Finset.mem_filter]
  simp only [mem_univ, true_and]
  exact (by decide : ∀ d : Fin 8, attScope d ⊆ univ.map rightEmb ↔ ¬ (d : ℕ) < 4) d

theorem mem_range_attEmbRight_iff (d : Fin k2Attachment.{u}.card) :
    d ∈ Set.range attEmbRight.{u} ↔ d ∈ k2Attachment.{u}.visibleCells rightEmb := by
  rw [mem_visibleCells_rightEmb_iff]
  constructor
  · rintro ⟨j, rfl⟩
    change ¬ (j : ℕ) + 4 < 4
    omega
  · intro h
    have hd8 : (d : ℕ) < 8 := d.2
    exact ⟨⟨d - 4, by omega⟩, Fin.ext (by change (d : ℕ) - 4 + 4 = d; omega)⟩

theorem cellMap_rightEmb {i : Fin (k2Attachment.{u}.comap rightEmb).card} {j : Fin 4}
    (hij : (i : ℕ) = j) : k2Attachment.{u}.cellMap rightEmb i = attEmbRight.{u} j :=
  (k2Attachment.cellMap_eq_of_strictMono rightEmb strictMono_attEmbRight mem_range_attEmbRight_iff
    hij.symm).symm

theorem attCell_attEmbRight (j : Fin 4) : attCell (attEmbRight.{u} j) = j :=
  Fin.ext (by change ((j : ℕ) + 4) % 4 = j; omega)

/-- **The face of the attachment type on the right side is the test type with k2Right.** -/
theorem isTestType_comap_rightEmb (hf : univ.map rightEmb ∈
    k2AttachmentType.{u}.toCellScheme.faces) :
    IsTestType (k2AttachmentType.{u}.comap rightEmb hf) k2Right := by
  refine ⟨Scheme.ext (k2Attachment.card_visibleCells_eq_of_strictMono rightEmb
    strictMono_attEmbRight mem_range_attEmbRight_iff) ?_ ?_ (fun i j hij ↦ ?_) (fun i j hij ↦ ?_)
    (fun s s' t t' _ ht ↦ ?_), fun i j hij ↦ ?_⟩
  · change (univ : Finset (Fin 4)).preimage rightEmb rightEmb.injective.injOn = univ
    simp
  · change (Geometry.intervalPlan univ).preimage (Finset.map rightEmb)
      (map_injective rightEmb).injOn = Geometry.intervalPlan univ
    ext C
    rw [Finset.mem_preimage]
    revert C
    decide
  · change (attScope (k2Attachment.cellMap rightEmb i)).preimage rightEmb rightEmb.injective.injOn =
      testScope j
    rw [cellMap_rightEmb hij]
    clear hij
    ext x
    rw [Finset.mem_preimage]
    revert x
    fin_cases j <;> decide
  · change attGrade (k2Attachment.cellMap rightEmb i) = testGrade j
    rw [cellMap_rightEmb hij]
    clear hij
    fin_cases j <;> rfl
  · change attRow (k2Attachment.cellMap rightEmb t.1) = testRow t'.1
    rw [cellMap_rightEmb ht]
    exact congrArg testRow (attCell_attEmbRight t'.1)
  · change k2AttLabel (k2Attachment.cellMap rightEmb i) = _
    rw [cellMap_rightEmb hij]
    exact (ite_eq_right (by change ¬ (j : ℕ) + 4 < 4; omega)).trans (congrArg _
        (attCell_attEmbRight j))

/-- **The face of the attachment type along the embedding onto the right side** is the test type
with k2Right. -/
theorem exists_restrictFace_rightEmb :
    ∃ p, StageType.restrictFace rightEmb k2AttachmentType.{u} = some p ∧ IsTestType p k2Right := by
  have hf : univ.map rightEmb ∈ k2AttachmentType.{u}.toCellScheme.faces := by
    change univ.map rightEmb ∈ Geometry.intervalPlan univ
    decide
  exact ⟨_, StageType.restrictFace_of_mem _ rightEmb hf, isTestType_comap_rightEmb hf⟩

end VaughtConjecture.ProcessRank
