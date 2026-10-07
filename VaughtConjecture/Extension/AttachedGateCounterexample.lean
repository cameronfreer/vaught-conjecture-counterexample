/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachedGate
import VaughtConjecture.Extension.GatedExtensionCounterexample

/-!
# The single-ceiling row design fails at the private type `P α`

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): the display and its gate) and 3.3 (the
recovery statements, item 1); the attached gated extensions of
`VaughtConjecture.Extension.AttachedGate`.

Vocabulary: a **reader** of an attached gated extension is a cell of the graded index of the gate
whose row reads every new donor cell through an anchor or through a private cell labelled at least
the cap (`CellScheme.Rows.IsGate`); the **ceiling** is a reader that the row of the gate reads at
least as the gate itself; **availability** is the second law of a lawful section (a cell of the
grade of a cell `t`, with scope inside that of `t`, lies below some cell of the graded index of
`t`).

**The theorem** (`AttachedGateCounterexample.label_gate_eq_bot`).  Let `Q` be a legal stage type on
three points whose face along `Fin.castSuccEmb` is literally the private type
`GatedExtensionCounterexample.P α`.  A cell `G` of `Q` of graded index `(univ, 2)` whose row is `⊥`
at every other cell of that graded index except one cell `K`, which it reads at least as itself, is
labelled `⊥` in `Q`.  `K = G` is allowed: a gate whose row is `⊥` at all its twins.

The two full private cells `C₁`, `C₂` of `P α` are ordered oppositely by the lawful labellings
`labelling ⊤ 2` and `labelling 2 ⊤`, both in the cap ball of the labels `labelling ⊤ ⊤` of `P α` at
`2`.  If `Q` did not label `G` with `⊥`, the lifts of both labellings to `(univ, 2)` at the cap `2`
(bountifulness of `Q`) would keep `G` not `⊥`, so the row of `G` would make `K` dominate every
cell of graded index `(univ, 2)`, and the one row of `K` would order `C₁` and `C₂` both ways
(`StageType.label_eq_bot_of_readsOnly_singleton`).  The lifts have the private faces
`labelling ⊤ 2` and `labelling 2 ⊤`, not the labels of `P α`.

**The consequence for attached gated extensions** (`AttachedGateCounterexample.exists_reader`).
Every attached gated extension of `P α`, over any face and with any donor, has a reader other than
the gate and the ceiling, at which the row of the gate is not `⊥`.  So the row design in which the
gate's row is `⊥` at every twin except one ceiling fails at `P α`.

**What this does not decide.**  The statement is about rows.  It does not say that, in a lawful
labelling with the literal private face `labelling ⊤ ⊤` and the gate not `⊥`, availability from
the private cap reaches a reader other than the ceiling: availability from one cap gives
domination of one full private cell, while the argument above needs domination of both, one in
each lift.  Whether recovery for the literal private face can always go through the ceiling alone
is open.  This is private arity `2`; the argument is stated at every arity
(`StageType.not_forall_le_of_opposite`), but no legal private type of arity at least `4` with two
oppositely ordered full cells is constructed here.  It does not refute (R1), nor the existence of
attached gated extensions with several readers.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.AttachedGateCounterexample

open Finset Label GatedExtensionCounterexample

private theorem natCast_two_lt_top : ((2 : ℕ) : Label.{u}) < ⊤ := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

private theorem natCast_two_ne_bot : ((2 : ℕ) : Label.{u}) ≠ ⊥ := by
  rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot

private theorem capBall_top_two (i : Fin 5) :
    min (labelling (⊤ : Label.{u}) ⊤ i) ((2 : ℕ) : Label.{u}) =
      min (labelling ⊤ ((2 : ℕ) : Label.{u}) i) ((2 : ℕ) : Label.{u}) := by
  fin_cases i <;> simp [labelling]

private theorem capBall_two_top (i : Fin 5) :
    min (labelling (⊤ : Label.{u}) ⊤ i) ((2 : ℕ) : Label.{u}) =
      min (labelling ((2 : ℕ) : Label.{u}) ⊤ i) ((2 : ℕ) : Label.{u}) := by
  fin_cases i <;> simp [labelling]

/-- **A gate that reads only one ceiling is labelled `⊥`** in every legal stage type on three
points whose face along `Fin.castSuccEmb` is literally `P α`. -/
theorem label_gate_eq_bot {α : Ordinal.{u}} (Q : StageType.{u} α 3) (hQ : Q.IsLegal)
    (hQP : StageType.restrictFace Fin.castSuccEmb Q = some (P α)) {G K : Fin Q.card}
    (hG : Q.toCellScheme.gradedIndex G = (univ, 2))
    (hKG : Q.toCellScheme.gradedIndex K = Q.toCellScheme.gradedIndex G)
    (honly : Q.rows.ReadsOnly G {K})
    (hrow : Q.rows.row G ⟨G, Q.toCellScheme.mem_below_gradedIndex G⟩ ≤ Q.rows.row G ⟨K, hKG.le⟩) :
    Q.label G = ⊥ :=
  StageType.label_eq_bot_of_readsOnly_singleton Q hQ hQP (C₁ := (3 : Fin 5)) (C₂ := (4 : Fin 5))
    rfl rfl (c := ((2 : ℕ) : Label.{u})) (by simp) natCast_two_ne_bot
    (p := labelling ⊤ ((2 : ℕ) : Label.{u})) (p' := labelling ((2 : ℕ) : Label.{u}) ⊤)
    isLawful_labelling_top_two isLawful_labelling_two_top capBall_top_two capBall_two_top
    natCast_two_lt_top natCast_two_lt_top hG hKG honly hrow

/-- **Every attached gated extension of `P α` has a second reader**: over any face and with any
donor, some reader other than the gate and the ceiling is read by the row of the gate not as `⊥`.
A statement about the row of the gate. -/
theorem exists_reader {α : Ordinal.{u}} {m : ℕ} {f : Fin m ↪ Fin 2}
    {d : StageType.{u} α (m + 1)} (E : StageType.AttachedGatedExtension (P α) f d) :
    ∃ t ∈ E.readers, ∃ ht : E.display.toCellScheme.gradedIndex t =
        E.display.toCellScheme.gradedIndex E.gate,
      t ≠ E.gate ∧ t ≠ E.ceiling ∧ E.display.rows.row E.gate ⟨t, ht.le⟩ ≠ ⊥ := by
  by_contra h
  push Not at h
  have honly : E.display.rows.ReadsOnly E.gate {E.ceiling} := fun t ht htG htK ↦ by
    by_cases htR : t ∈ E.readers
    · exact h t htR ht htG (by simpa using htK)
    · exact E.readsOnly t ht htG htR
  exact E.label_gate_ne_bot (label_gate_eq_bot E.display E.isLegal E.restrictFace_castSuccEmb
    E.gradedIndex_gate E.gradedIndex_ceiling_eq honly E.row_gate_le_ceiling)

end VaughtConjecture.AttachedGateCounterexample
