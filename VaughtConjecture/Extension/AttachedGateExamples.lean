/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachedGateCounterexample
import VaughtConjecture.Extension.CoupledGateInstance

/-!
# Examples of attached gated extensions

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate); the attached
gated extensions of `VaughtConjecture.Extension.AttachedGate`.

* **One reader** (`AttachedGateExamples.exists_attachedGatedExtension_two_zero`).  A gated
  extension whose gate has no twins is an attached gated extension with the gate as its only
  reader (`StageType.GatedExtension.toAttachedGatedExtension`).  The gated extension of
  `StageType.GatedExtension.instance_two_zero` is one, so attached gated extensions exist at
  private arity `2` over the empty root, with every hypothesis on the input satisfied.
* **Two readers at `P α`** (`AttachedGateExamples.attachedGatedExtensionP`).  The display
  `CoupledGateInstance.Q α`, whose faces are the private type `GatedExtensionCounterexample.P α`
  and the donor labelled `⊤` over the empty root, is an attached gated extension with gate `9`,
  cap `3` (the full private cell `C₁`), and readers `9` and `10`, the gate being its own ceiling.
  Both readers read the donor cell `5` through the cap, at `3`, at least as they read the cap (at
  `3` and `2`).  The display labels the twin `10` of the gate `⊤`, so not every twin is labelled
  `⊥`.
  At `P α` the row of the gate must read a second reader not as `⊥`
  (`AttachedGateCounterexample.exists_reader`); here it is `10`.  The new donor label is `⊤`, so
  no donor label below the cap needs an anchor: this tests the twins of the gate, not the
  transport of anchors.

Vocabulary: a **reader** is a cell of the graded index of the gate whose row reads every new donor
cell through an anchor or through a private cell labelled at least the cap
(`CellScheme.Rows.IsGate`); the **ceiling** is a reader that the row of the gate reads at least as
the gate itself; **availability** is the second law of a lawful section (a cell of the grade of a
cell `t`, with scope inside that of `t`, lies below some cell of the graded index of `t`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.AttachedGateExamples

open Finset Label

/-- **Attached gated extensions exist at private arity `2`**: for every label `F ≠ ⊥`
self-visible at `2` and at the stage `α`, there are a legal private type `P` on two points, the
type `p` of the empty root, a legal donor `d` on one point, and a cell `C` of `P` of graded index
`(univ, 2)` not labelled `⊥`, below which `d` is anchored, with an attached gated extension of
`P` over the empty root with donor `d` whose cap carries the label of `C`. -/
theorem exists_attachedGatedExtension_two_zero {α : Ordinal.{u}} {F : Label.{u}}
    (hF : IsSelfVisible 2 F) (hFα : AtStage α F) (hF0 : F ≠ ⊥) :
    ∃ (P : StageType.{u} α 2) (p : StageType.{u} α 0) (d : StageType.{u} α 1) (C : Fin P.card),
      P.IsLegal ∧ StageType.restrictFace GatedExtensionExample.emptyRoot P = some p ∧
      d.IsLegal ∧ StageType.restrictFace Fin.castSuccEmb d = some p ∧
      P.toCellScheme.gradedIndex C = (univ, 2) ∧ P.label C ≠ ⊥ ∧ P.IsAnchored C d ∧
      ∃ E : StageType.AttachedGatedExtension P GatedExtensionExample.emptyRoot d,
        E.display.label E.cap = P.label C := by
  obtain ⟨P, p, d, C, hP, hp, hd, hdp, hC, hC0, hanc, E, hcap, huniq⟩ :=
    StageType.GatedExtension.instance_two_zero hF hFα hF0
  exact ⟨P, p, d, C, hP, hp, hd, hdp, hC, hC0, hanc, E.toAttachedGatedExtension huniq, hcap⟩

open CoupledGateInstance
open CoupledGateExamples (cellScope cellGrade eq_of_gradedIndex_nine
  eq_five_of_mem_visible range_castSuccEmb)

private theorem natCast_two_le_three : ((2 : ℕ) : Label.{u}) ≤ ((3 : ℕ) : Label.{u}) :=
  natCast_label_le.mpr (by decide)

private theorem mem_visible_three (α : Ordinal.{u}) :
    cellQ α 3 ∈ (Q α).toCellScheme.visible (Set.range Fin.castSuccEmb) := by
  -- A cell is visible when its scope lies in the range (by definition).
  change ((cellScope 3 : Finset (Fin 3)) : Set (Fin 3)) ⊆ Set.range Fin.castSuccEmb
  rw [range_castSuccEmb, coe_subset]; decide

/-- Each of the cells `9` and `10` reads the donor cell `5` through the cap `3`. -/
private theorem isGate_reader (α : Ordinal.{u}) (K : Fin 12) (hK : K = 9 ∨ K = 10) :
    (Q α).rows.IsGate (cellQ α K) (cellQ α 3)
      ((Q α).toCellScheme.visible (Set.range Fin.castSuccEmb))
      ((Q α).toCellScheme.visible (Set.range (extendByLast GatedExtensionExample.emptyRoot)))
      (Q α).label where
  cap_mem := mem_visible_three α
  -- The scope of a cell of the display is `cellScope` (by definition).
  scope_cap_subset := by
    change cellScope 3 ⊆ cellScope K
    rcases hK with rfl | rfl <;> decide
  grade_cap := by rcases hK with rfl | rfl <;> rfl
  -- The labels of the display are `lab ⊤ ⊤ ⊤` (by definition).
  cap_ne_bot := by
    change lab ⊤ ⊤ ⊤ 3 ≠ ⊥
    simp [lab, kind]
  le_gate e he := by
    rw [eq_five_of_mem_visible he]
    -- The graded index of a cell is its scope and grade (by definition).
    change (cellScope 5, cellGrade 5) ≤ (cellScope K, cellGrade K)
    rcases hK with rfl | rfl <;> exact ⟨by decide, by decide⟩
  reads e he _ := by
    obtain rfl := eq_five_of_mem_visible he
    -- The donor cell is labelled `⊤`, at least the cap: the reader reads it at `3`, at least as
    -- it reads the cap.
    refine .top ⟨cellQ α 3, ?_⟩ (mem_visible_three α) le_rfl ?_ ?_
    · -- The graded index of a cell is its scope and grade (by definition).
      change (cellScope 3, cellGrade 3) ≤ (cellScope K, cellGrade K)
      rcases hK with rfl | rfl <;> exact ⟨by decide, le_rfl⟩
    · -- The labels of the display are `lab ⊤ ⊤ ⊤` (by definition).
      change lab ⊤ ⊤ ⊤ 3 ≤ lab ⊤ ⊤ ⊤ 5
      simp [lab, kind]
    · -- The rows of the display: `3` from `9` to the cap, `2` from `10`, and `3` to the donor.
      rcases hK with rfl | rfl
      · exact le_of_eq rfl
      · exact (le_of_eq rfl).trans (natCast_two_le_three.trans (le_of_eq rfl))

/-- **An attached gated extension of `P α` with two readers**: the display
`CoupledGateInstance.Q α` over the empty root with the donor labelled `⊤`, gate `9`, cap `3`,
readers `9` and `10`, and the gate as its own ceiling. -/
noncomputable def attachedGatedExtensionP (α : Ordinal.{u}) :
    StageType.AttachedGatedExtension (GatedExtensionCounterexample.P α)
      GatedExtensionExample.emptyRoot (donor α) where
  display := Q α
  isLegal := isLegal_Q α
  restrictFace_castSuccEmb := restrictFace_Q α
  restrictFace_extendByLast := restrictFace_donor α
  gate := cellQ α 9
  cap := cellQ α 3
  readers := {cellQ α 9, cellQ α 10}
  ceiling := cellQ α 9
  ceiling_mem := Set.mem_insert _ _
  -- The graded index of a cell is its scope and grade (by definition).
  gradedIndex_gate := by change (cellScope 9, cellGrade 9) = _; rfl
  gradedIndex_cap := by
    change (cellScope 3, cellGrade 3) = (univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3), 2)
    decide +kernel
  gradedIndex_reader K hK := by
    rcases hK with rfl | rfl
    · change (cellScope 9, cellGrade 9) = _; rfl
    · change (cellScope 10, cellGrade 10) = _; rfl
  -- The labels of the display are `lab ⊤ ⊤ ⊤` (by definition).
  label_gate_ne_bot := by
    change lab ⊤ ⊤ ⊤ 9 ≠ ⊥
    simp [lab, kind]
  readsOnly t ht htG htR := by
    rcases eq_of_gradedIndex_nine t ht with h | h
    · exact absurd h htG
    · exact absurd (Or.inr h) htR
  row_gate_le_ceiling := le_rfl
  isGate K hK := by
    rcases hK with rfl | rfl
    exacts [isGate_reader α 9 (.inl rfl), isGate_reader α 10 (.inr rfl)]

/-- The display labels the twin `10` of the gate `⊤`, and `10` is a reader. -/
theorem label_reader_ten (α : Ordinal.{u}) :
    cellQ α 10 ∈ (attachedGatedExtensionP α).readers ∧ (Q α).label (cellQ α 10) = ⊤ := by
  refine ⟨Or.inr rfl, ?_⟩
  -- The labels of the display are `lab ⊤ ⊤ ⊤` (by definition).
  change lab ⊤ ⊤ ⊤ 10 = ⊤
  simp [lab, kind]

end VaughtConjecture.AttachedGateExamples
