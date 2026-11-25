/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ProcessRank.SpanK2GradeTwo

/-!
# The grade-two controllers of the attachment of the test with `K = 2`

Process rank `ω₁`, the finite span of mutual rigidity: one cell at `(univ, 2)` for each state of
the grade-two catalogue `ProcessRank.k2Cat2`, appended to the ladder `ProcessRank.k2Ladder`
(`ProcessRank.k2Grade2`).

**The rows** (`ProcessRank.k2Phi`).  The controller of a state `R` reads an old cell `z` of the
ladder as the controller row `k2ControllerRow R z`, and the controller of a catalogue state `Q`
as the agreement height `agreementHeight (grid 2 16) R Q`.

**Lawfulness and consistency** (`ProcessRank.isLawful_k2Phi`, `ProcessRank.isConsistent_k2Grade2`).
For a catalogue state the row is lawful on the enlarged scheme:
* the old cells below `(univ, 2)` lie below `(univ, 1)`, `({0, 1}, 2)` or `({2, 3}, 2)`
  (`ProcessRank.k2Ladder_mem_cover`), where the row is the controller row, lawful below
  `(univ, 2)` on the ladder;
* at a new cell, of the catalogue state `Q`, the witness is the identity with the suppressor equal
  to the agreement height `κ` of `R` and `Q` up to the grade two: two catalogue states agreeing
  capped at `κ` on the eight attachment cells have controller rows agreeing capped at `κ` on the
  whole old ladder (`Scheme.LadderBaseData.min_stateExtOf_eq`), and the agreement heights compare
  among the new cells by `Label.agreementHeight_tri`;
* availability at a new cell is witnessed by the controller of `R` itself, which reads the top of
  the grid.
Consistency of the enlarged scheme is `Scheme.isConsistent_appendFullCells`.

**The one-member reading** (`ProcessRank.k2Grade2_readMember`): every cell of full scope at the
grade two reads the ladder points and the attachment cells through one rank member and one
monotone table with `⊥` at `0`.  The controller of the separated admitted state is
`ProcessRank.k2SepCell`.

Open: the extension of the prescribed top labels to the enlarged scheme, the common-shadow and
twin conditions, the grades three and four, the four-point span of mutual rigidity of the test
pair, and the countable upper bound on Scott classes.
-/

universe u

namespace VaughtConjecture.ProcessRank

open Finset Label
open scoped Ordinal

/-- **The row of the controller of a state**: the controller row on the old cells of the ladder,
the agreement heights with the catalogue states on the new cells. -/
noncomputable def k2Phi (R : Fin k2AttachmentBase.{u}.S.card → Label.{u}) :
    Fin (k2Ladder.{u}.card + k2Cat2.{u}.card) → Label.{u} :=
  Fin.append (k2ControllerRow R) fun i ↦ agreementHeight (grid 2 16) R (k2Cat2.equivFin.symm i).1

theorem k2Phi_castAdd (R : Fin k2AttachmentBase.{u}.S.card → Label.{u})
    (z : Fin k2Ladder.{u}.card) : k2Phi R (Fin.castAdd _ z) = k2ControllerRow R z :=
  Fin.append_left _ _ z

theorem k2Phi_natAdd (R : Fin k2AttachmentBase.{u}.S.card → Label.{u}) (i : Fin k2Cat2.{u}.card) :
    k2Phi R (Fin.natAdd _ i) = agreementHeight (grid 2 16) R (k2Cat2.equivFin.symm i).1 :=
  Fin.append_right _ _ i

/-- The attachment cells have proper scope. -/
theorem attachment_not_le (e : Fin k2AttachmentBase.{u}.S.card) :
    ¬ ((univ : Finset (Fin 4)), 2) ≤ k2AttachmentBase.{u}.S.toCellScheme.gradedIndex e :=
  (by decide : ∀ e : Fin 8, ¬ ((univ : Finset (Fin 4)), 2) ≤ (attScope e, attGrade e)) e

/-- **No cell of the ladder lies above `(univ, 2)`**: the attachment cells have proper scope, the
ladder points grade one. -/
theorem k2Ladder_not_le (z : Fin k2Ladder.{u}.card) :
    ¬ ((univ : Finset (Fin 4)), 2) ≤ k2Ladder.{u}.toCellScheme.gradedIndex z := by
  induction z using Fin.addCases with
  | left e =>
    erw [Scheme.appendFullCellsScheme_gradedIndex_castAdd]
    exact attachment_not_le e
  | right j =>
    erw [Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact fun h ↦ absurd h.2 (by decide)

/-- **The grade-two scheme**: the ladder with one controller at `(univ, 2)` for each catalogue
state, its row `k2Phi` of the state. -/
noncomputable abbrev k2Grade2 : Scheme.{u} 4 :=
  k2Ladder.appendFullCells 2 k2Cat2.card (fun i ↦ k2Phi (k2Cat2.equivFin.symm i).1)
    k2Ladder_not_le

/-- **Every old cell below `(univ, 2)` lies below `(univ, 1)`, `({0, 1}, 2)` or `({2, 3}, 2)`.** -/
theorem k2Ladder_mem_cover (z : Fin k2Ladder.{u}.card)
    (hz : k2Ladder.{u}.toCellScheme.grade z ≤ 2) :
    k2Ladder.{u}.toCellScheme.gradedIndex z ≤ ((univ : Finset (Fin 4)), 1) ∨
      k2Ladder.{u}.toCellScheme.gradedIndex z ≤ (MirrorAttachment.leftFace, 2) ∨
      k2Ladder.{u}.toCellScheme.gradedIndex z ≤ (MirrorAttachment.rightFace, 2) := by
  induction z using Fin.addCases with
  | left e =>
    have hg : k2Ladder.{u}.toCellScheme.gradedIndex (Fin.castAdd _ e) =
        k2AttachmentBase.{u}.S.toCellScheme.gradedIndex e :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e
    have hge : k2AttachmentBase.{u}.S.toCellScheme.grade e ≤ 2 := by
      have h2 : k2Ladder.{u}.toCellScheme.grade (Fin.castAdd _ e) =
          k2AttachmentBase.{u}.S.toCellScheme.grade e := congrArg Prod.snd hg
      omega
    rw [hg]
    by_cases h1 : k2AttachmentBase.{u}.S.toCellScheme.grade e ≤ 1
    · exact .inl ⟨subset_univ _, h1⟩
    · rcases scope_k2Attachment e with h | h
      exacts [.inr (.inl ⟨h, hge⟩), .inr (.inr ⟨h, hge⟩)]
  | right j =>
    have hg : k2Ladder.{u}.toCellScheme.gradedIndex (Fin.natAdd _ j) =
        ((univ : Finset (Fin 4)), 1) :=
      Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ j
    rw [hg]
    exact .inl le_rfl

/-- The row of a catalogue state takes values in the code grid. -/
theorem k2Phi_mem_codeGrid {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hR : R ∈ k2Cat2)
    (z : Fin (k2Ladder.{u}.card + k2Cat2.{u}.card)) : k2Phi R z ∈ codeGrid 2 16 := by
  obtain ⟨hRB, hl, -, -, -⟩ := mem_k2Cat2.mp hR
  induction z using Fin.addCases with
  | left e =>
    rw [k2Phi_castAdd, k2ControllerRow_of_isLawfulBelow (isLawfulBelow_one_of_two hl)]
    rcases Scheme.LadderBaseData.stateExtOf_cases R _ e with h | h | ⟨d, h⟩ <;> rw [h]
    · exact mem_insert_self _ _
    · exact Seed.one_mem_codeGrid (by decide)
    · exact hRB d
  | right i =>
    rw [k2Phi_natAdd]
    exact grid_subset_codeGrid _ _ (agreementHeight_spec (bot_mem_grid _ _) _ _).1

/-- Appending cells of full scope at a grade `k ≤ K` to a scheme with grades at most `K` keeps the
grades at most `K`. -/
theorem grade_appendFullCells_le {n k M K : ℕ} {S : Scheme.{u} n} {r : Fin M → Fin (S.card + M) →
    Label.{u}} {h : ∀ d, ¬ ((univ : Finset (Fin n)), k) ≤ S.toCellScheme.gradedIndex d}
    (hS : ∀ d, S.toCellScheme.grade d ≤ K) (hk : k ≤ K) (z : Fin (S.card + M)) :
    (S.appendFullCells k M r h).toCellScheme.grade z ≤ K := by
  change (S.appendFullCellsScheme k M).grade z ≤ K
  induction z using Fin.addCases with
  | left d => rw [Scheme.appendFullCellsScheme_grade_castAdd]; exact hS d
  | right i => rw [Scheme.appendFullCellsScheme_grade_natAdd]; exact hk

/-- Every cell of the ladder has grade at most two. -/
theorem k2Ladder_grade_le (z : Fin k2Ladder.{u}.card) : k2Ladder.{u}.toCellScheme.grade z ≤ 2 :=
  grade_appendFullCells_le (h := k2AttachmentBase.noFull)
    (fun e ↦ (by decide : ∀ e : Fin 8, attGrade e ≤ 2) e) (by decide) z

/-- Every cell of the grade-two scheme has grade at most two. -/
theorem k2Grade2_grade_le (z : Fin k2Grade2.{u}.card) : k2Grade2.{u}.toCellScheme.grade z ≤ 2 :=
  grade_appendFullCells_le k2Ladder_grade_le le_rfl z

/-- Every cell of the grade-two scheme lies below `(univ, 2)`. -/
theorem k2Grade2_mem_below (z : Fin k2Grade2.{u}.card) :
    z ∈ k2Grade2.{u}.toCellScheme.below ((univ : Finset (Fin 4)), 2) :=
  ⟨subset_univ _, k2Grade2_grade_le z⟩

/-- **The row of a catalogue state is lawful below `(univ, 2)` on the grade-two scheme.** -/
theorem isLawfulBelow_k2Phi {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hR : R ∈ k2Cat2) :
    k2Grade2.{u}.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 2) fun z ↦ k2Phi R z := by
  classical
  obtain ⟨-, hRl, -, -, -⟩ := mem_k2Cat2.mp hR
  have hR1 := isLawfulBelow_one_of_two hRl
  have hold := isLawfulBelow_k2ControllerRow hR
  have hpart (X : Finset (Fin 4) × ℕ) (hX : ¬ ((univ : Finset (Fin 4)), 2) ≤ X)
      (hX2 : X ≤ ((univ : Finset (Fin 4)), 2)) :
      k2Grade2.{u}.rows.IsLawfulBelow X fun z ↦ k2Phi R z := by
    refine (Scheme.isLawfulBelow_appendFullCells_iff hX).mpr ?_
    exact (CellScheme.Rows.isLawfulBelow_congr (w := fun d ↦ k2ControllerRow R d)
      (w' := fun d ↦ k2Phi R (Fin.castAdd _ d)) fun d _ ↦ (k2Phi_castAdd R d).symm).mp
        (hold.mono hX2)
  obtain ⟨ho1, hl1, ha1⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp
    (hpart ((univ : Finset (Fin 4)), 1) (fun h ↦ absurd h.2 (by decide)) ⟨subset_rfl, by decide⟩)
  obtain ⟨hoL, hlL, haL⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp
    (hpart (MirrorAttachment.leftFace, 2) (fun h ↦ absurd h.1 (by decide))
      ⟨subset_univ _, le_rfl⟩)
  obtain ⟨hoR, hlR, haR⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp
    (hpart (MirrorAttachment.rightFace, 2) (fun h ↦ absurd h.1 (by decide))
      ⟨subset_univ _, le_rfl⟩)
  have hcases {e : Fin k2Ladder.{u}.card}
      (he : Fin.castAdd k2Cat2.card e ∈
        k2Grade2.{u}.toCellScheme.below ((univ : Finset (Fin 4)), 2)) :
      Fin.castAdd k2Cat2.card e ∈ k2Grade2.{u}.toCellScheme.below ((univ : Finset (Fin 4)), 1) ∨
        Fin.castAdd k2Cat2.card e ∈ k2Grade2.{u}.toCellScheme.below
          (MirrorAttachment.leftFace, 2) ∨
        Fin.castAdd k2Cat2.card e ∈ k2Grade2.{u}.toCellScheme.below
          (MirrorAttachment.rightFace, 2) := by
    have hg : k2Grade2.{u}.toCellScheme.gradedIndex (Fin.castAdd k2Cat2.card e) =
        k2Ladder.{u}.toCellScheme.gradedIndex e :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ e
    have he2 : k2Ladder.{u}.toCellScheme.grade e ≤ 2 := by
      have h := he
      rw [CellScheme.mem_below, hg] at h
      exact h.2
    simp only [CellScheme.mem_below, hg]
    exact k2Ladder_mem_cover e he2
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (k2Cat2.equivFin.symm i₀).1 = R :=
    ⟨k2Cat2.equivFin ⟨R, hR⟩, by simp⟩
  refine CellScheme.Rows.isLawfulBelow_iff_forall.mpr
    ⟨fun z hz ↦ ?_, fun s hs ↦ ?_, fun s t ht hst hg ↦ ?_⟩
  · induction z using Fin.addCases with
    | left e =>
      rcases hcases hz with h | h | h
      exacts [ho1 _ h, hoL _ h, hoR _ h]
    | right i =>
      rw [Scheme.appendFullCellsScheme_grade_natAdd, k2Phi_natAdd]
      exact isSelfVisible_of_mem_grid (agreementHeight_spec (bot_mem_grid _ _) _ _).1
  · induction s using Fin.addCases with
    | left e =>
      rcases hcases hs with h | h | h
      exacts [hl1 _ h, hlL _ h, hlR _ h]
    | right i =>
      set κ := agreementHeight (grid 2 16) R (k2Cat2.equivFin.symm i).1 with hκ
      have hκm : κ ∈ grid 2 16 := (agreementHeight_spec (bot_mem_grid _ _) _ _).1
      have hκv : IsSelfVisible 2 κ := isSelfVisible_of_mem_grid hκm
      obtain ⟨-, hQl, -, -, -⟩ := mem_k2Cat2.mp (k2Cat2.equivFin.symm i).2
      have hQ1 := isLawfulBelow_one_of_two hQl
      refine ⟨constStepSuppressor 2 κ, id, ⟨antitone_constStepSuppressor _ _,
        isSelfVisible_constStepSuppressor hκv, rfl, monotone_id, fun _ _ _ _ _ ↦ rfl⟩,
        fun t ↦ ?_⟩
      have htk : k2Grade2.{u}.toCellScheme.grade t ≤ 2 := k2Grade2_grade_le t
      rw [Scheme.appendFullCells_row_natAdd, constStepSuppressor_of_le _ htk, id, k2Phi_natAdd,
        ← hκ]
      obtain ⟨t, -⟩ := t
      dsimp only
      induction t using Fin.addCases with
      | left e =>
        rw [k2Phi_castAdd, k2Phi_castAdd]
        by_cases hκ0 : κ = ⊥
        · rw [hκ0, min_bot_right, min_bot_right]
        rw [k2ControllerRow_of_isLawfulBelow hR1, k2ControllerRow_of_isLawfulBelow hQ1]
        exact Scheme.LadderBaseData.min_stateExtOf_eq (B := k2AttachmentBase) k2_card_le hκ0
          (hκv.mono (by decide)) hQ1 hR1 (agreementHeight_spec (bot_mem_grid _ _) R _).2 e
      | right i' =>
        rw [k2Phi_natAdd, k2Phi_natAdd]
        exact agreementHeight_tri (bot_mem_grid _ _) _ _ _
  · induction t using Fin.addCases with
    | left e =>
      rcases hcases ht with h | h | h
      exacts [ha1 s _ h hst hg, haL s _ h hst hg, haR s _ h hst hg]
    | right i =>
      refine ⟨Fin.natAdd _ i₀, by
        rw [Scheme.appendFullCellsScheme_gradedIndex_natAdd,
          Scheme.appendFullCellsScheme_gradedIndex_natAdd], ?_⟩
      rw [k2Phi_natAdd, hi₀, agreementHeight_self (gridPoint_mem_grid le_rfl)
        (fun _ hx ↦ le_gridPoint_of_mem_grid hx)]
      exact le_gridPoint_of_mem_codeGrid (k2Phi_mem_codeGrid hR s)

/-- **The row of a catalogue state is a lawful section of the grade-two scheme.** -/
theorem isLawful_k2Phi {R : Fin k2AttachmentBase.{u}.S.card → Label.{u}} (hR : R ∈ k2Cat2) :
    k2Grade2.{u}.rows.IsLawful (k2Phi R) :=
  (isLawfulBelow_k2Phi hR).isLawful k2Grade2_mem_below

/-- **The grade-two scheme has consistent rows** (`Scheme.isConsistent_appendFullCells`). -/
theorem isConsistent_k2Grade2 : k2Grade2.{u}.rows.IsConsistent :=
  Scheme.isConsistent_appendFullCells isConsistent_k2Ladder fun i ↦
    isLawful_k2Phi (k2Cat2.equivFin.symm i).2

/-! ### The controllers and the one-member reading -/

/-- **The row of a controller**: the controller of the `i`-th catalogue state reads every cell of
the grade-two scheme through the row labelling of that state. -/
theorem k2Grade2_rowAt_natAdd (i : Fin k2Cat2.{u}.card) (z : Fin k2Grade2.{u}.card) :
    k2Grade2.{u}.rowAt (Fin.natAdd _ i) z = k2Phi (k2Cat2.equivFin.symm i).1 z := by
  have hz : z ∈ k2Grade2.{u}.toCellScheme.below
      (k2Grade2.{u}.toCellScheme.gradedIndex (Fin.natAdd _ i)) := by
    rw [CellScheme.mem_below, Scheme.appendFullCellsScheme_gradedIndex_natAdd]
    exact k2Grade2_mem_below z
  rw [Scheme.rowAt_of_mem hz, Scheme.appendFullCells_row_natAdd]

/-- **The old-cell equation**: a controller reads an old cell of the ladder through the controller
row of its state. -/
theorem k2Grade2_rowAt_natAdd_castAdd (i : Fin k2Cat2.{u}.card) (z : Fin k2Ladder.{u}.card) :
    k2Grade2.{u}.rowAt (Fin.natAdd _ i) (Fin.castAdd _ z) =
      k2ControllerRow (k2Cat2.equivFin.symm i).1 z := by
  rw [k2Grade2_rowAt_natAdd, k2Phi_castAdd]

/-- **The new-controller equation**: a controller reads another controller as the agreement
height of their states. -/
theorem k2Grade2_rowAt_natAdd_natAdd (i i' : Fin k2Cat2.{u}.card) :
    k2Grade2.{u}.rowAt (Fin.natAdd _ i) (Fin.natAdd _ i') =
      agreementHeight (grid 2 16) (k2Cat2.equivFin.symm i).1 (k2Cat2.equivFin.symm i').1 := by
  rw [k2Grade2_rowAt_natAdd, k2Phi_natAdd]

/-- **The controller of the separated admitted state.** -/
noncomputable def k2SepCell : Fin k2Grade2.{u}.card :=
  Fin.natAdd _ (k2Cat2.equivFin ⟨k2SepState, k2SepState_mem⟩)

/-- The controller of the separated admitted state has full scope and grade two, and reads every
cell through the row labelling of the separated admitted state. -/
theorem k2SepCell_spec :
    k2Grade2.{u}.toCellScheme.gradedIndex k2SepCell = ((univ : Finset (Fin 4)), 2) ∧
      ∀ z, k2Grade2.{u}.rowAt k2SepCell z = k2Phi k2SepState z := by
  refine ⟨Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _, fun z ↦ ?_⟩
  rw [k2SepCell, k2Grade2_rowAt_natAdd, Equiv.symm_apply_apply]

set_option quotPrecheck false in
/-- The index of a ladder point for a member. -/
local notation "idx" => ladderIndex 8 (Scheme.rankProf k2AttachmentBase.S 8) Prod.fst
  (Scheme.ladderCeil (Scheme.rankProf k2AttachmentBase.S 8))

/-- **The one-member reading**: every cell of full scope at the grade two of the grade-two scheme
reads the ladder points and the attachment cells through one rank member and one monotone table
with `⊥` at `0`. -/
theorem k2Grade2_readMember (f : Fin k2Grade2.{u}.card)
    (hf : k2Grade2.{u}.toCellScheme.gradedIndex f = ((univ : Finset (Fin 4)), 2)) :
    ∃ (b : Scheme.RankMember k2AttachmentBase.{u}.S 8) (Φ : ℕ → Label.{u}), Monotone Φ ∧
      Φ 0 = ⊥ ∧ (∀ v, k2Grade2.{u}.rowAt f (Fin.castAdd _ (k2LadPt v)) = Φ (idx b v)) ∧
      ∀ e, k2Grade2.{u}.rowAt f (Fin.castAdd _ (Fin.castAdd _ e)) =
        Φ (Scheme.rankProf k2AttachmentBase.S 8 b e) := by
  induction f using Fin.addCases with
  | left z =>
    exfalso
    have hg : k2Grade2.{u}.toCellScheme.gradedIndex (Fin.castAdd _ z) =
        k2Ladder.{u}.toCellScheme.gradedIndex z :=
      Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ z
    exact k2Ladder_not_le z (le_of_eq (hf.symm.trans hg))
  | right i =>
    obtain ⟨b, Φ, hΦ, hΦ0, hl, ha⟩ := k2Cat2_factor (k2Cat2.equivFin.symm i).2
    exact ⟨b, Φ, hΦ, hΦ0, fun v ↦ by rw [k2Grade2_rowAt_natAdd_castAdd, hl],
      fun e ↦ by rw [k2Grade2_rowAt_natAdd_castAdd, ha]⟩

end VaughtConjecture.ProcessRank
