/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachedGate
import VaughtConjecture.Realization.GateRecovery
import VaughtConjecture.Realization.Model

/-!
# Receiving through an attached gated extension

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): one occurrence over the private tuple with
the display's bottom pattern) and 3.3 (the recovery statement of (R1), item 1: agreement below a
cutoff); semantic contract, item 12 (receiving one permitted cutoff at a time).

Fix a model `R`, an occurrence `y` of `R` on `n` points (the **private context**), a face `f` of
it, and an attached gated extension `E` of the type of `y` over `f` with donor `d`
(`StageType.AttachedGatedExtension`): a legal display on `n + 1` points with literal faces, a gate
of graded index `(univ, n)` not labelled `⊥`, and **readers** of that graded index, cells whose
rows read every new donor cell through an anchor or through a private cell labelled at least the
cap (`CellScheme.Rows.IsGate`); the row of the gate is `⊥` at every other cell of its graded index
outside the readers, and reads one reader, the **ceiling**, at least as itself.  **Availability**
is the second law of a lawful section: a cell of the grade of a cell `t`, with scope inside that
of `t`, lies below some cell of the graded index of `t`.

**The gate from the bottom-pattern clause** (`IsModel.exists_attachedGate`).  The bottom-pattern
clause ([Kni26, Definition 3.2.1], clause 4(a)ii; `IsModel.bottomPattern`) for the scheme of the
display and its labels is guarded by the nonemptiness of its instance among the cofaces of the
type of `y`, which the display itself witnesses.  The clause realizes a point `u` extending `y`
whose type `q` has the scheme of the display, is a coface of the type of `y` (exact consistency),
and is `⊥` exactly where the display is at every cell of grade at most `n`.  The family tests the
cells of grade at most the old arity `n` (`StageType.bottomPatternFamily`), and the gate has grade
`n`, so `q` is not `⊥` at the gate (`StageType.AttachedGatedExtension.label_gate_ne_bot_of_mem`).
Of the realized labels nothing else is read: in particular not the labels at the twins of the
gate, which the display need not label `⊥`.  The argument is that of
`StageType.GatedExtension.label_gate_ne_bot_of_mem` (`VaughtConjecture.Realization.GateRecovery`),
for the gate of an attached gated extension.

**Recovery** (`StageType.AttachedGatedExtension.recover`).  A stage type `q` on the scheme of the
display with literal private face and not `⊥` at the gate has a donor face, along
`extendByLast f`, in the receiving family of `d` at the label of the cap: its labels are lawful for
the rows of the display, and recovery through the readers
(`CellScheme.Rows.IsLawful.recover_of_readsOnly`) applies.  The reduction to the rows (the literal
private face read off the two equal faces, and the donor face defined because the scheme is that
of the display) follows `StageType.mem_receivingFamily_of_isGate` and
`StageType.GatedExtension.exists_restrictFace_mem_receivingFamily`.

**Receiving at a given attached gated extension**
(`IsModel.realizesOver_receivingFamily_of_attachedGatedExtension`).  Over an occurrence `x` that
is the face of `y` along `f`, for every cutoff `c` at most the label of the cap, the point `u`
extends `x` along `extendByLast f`, and exact consistency labels the extended tuple with the donor
face of `q`: `R` realizes over `x` a member of the receiving family of `d` at `c`.

**What is and is not proved.**  Every statement here is about a **given** attached gated extension
and uses, of the clauses of a model, only legality of types (for the display to be a coface),
exact consistency, and the bottom-pattern clause; no hypothesis on the stage is used.  No
universal hypothesis is introduced.  The existence of an attached gated extension over the private
contexts that a model acquires (`IsModel.exists_privateContext`, whose cap is labelled above any
requested floor below the stage) is **open**: it is the construction of a legal display, a
completion problem over the coatom amalgam with readers at the graded index `(univ, n)`, and the
lifts it must realize at caps not `⊥` include those of
`StageType.AttachedGatedExtension.exists_lift`.  At the private type
`GatedExtensionCounterexample.P α` the row of the gate cannot be `⊥` at every twin but one ceiling
(`AttachedGateCounterexample.exists_reader`); this concerns that row design only.  Finite-cut
receiving for all models, (R1), is not claimed.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.

## References

The model clauses are those of [Kni26, Definition 3.2.1]; the private context is that of
[Kni26, Lemma 8.1.1].
-/

universe u v

namespace VaughtConjecture

open Finset

namespace StageType

namespace AttachedGatedExtension

variable {α : Ordinal.{u}} {n m : ℕ} {P : StageType.{u} α n} {f : Fin m ↪ Fin n}
  {d : StageType.{u} α (m + 1)} (E : AttachedGatedExtension P f d) {q : StageType.{u} α (n + 1)}

/-- **The gate equation**: a member of the bottom-pattern family of the display is not `⊥` at the
gate, a cell of grade `n`, which the family tests.  The proof is that of
`StageType.GatedExtension.label_gate_ne_bot_of_mem`. -/
theorem label_gate_ne_bot_of_mem (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label)
    (i : Fin q.card) (hi : (i : ℕ) = E.gate) : q.label i ≠ ⊥ := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain ⟨rfl, hpat⟩ := hq
  obtain rfl := Fin.ext hi
  exact label_ne_bot_of_mem_bottomPatternFamily ⟨rfl, hpat⟩ _ _ rfl E.grade_gate.le
    E.label_gate_ne_bot

/-- **Recovery for an attached gated extension.**  A stage type on the scheme of the display, with
literal private face `P` and not `⊥` at the gate, has a donor face that agrees with the donor `d`
below the label of the cap. -/
theorem recover (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ saturationFamily E.display.toScheme)
    (hG : ∀ i : Fin q.card, (i : ℕ) = E.gate → q.label i ≠ ⊥) {d' : StageType.{u} α (m + 1)}
    (hd' : restrictFace (extendByLast f) q = some d') :
    d' ∈ receivingFamily d (E.display.label E.cap) := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain rfl : S = E.display.toScheme := hq
  obtain ⟨hfd, hd⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_extendByLast
  obtain ⟨hfd', rfl⟩ := (restrictFace_eq_some_iff _ _).mp hd'
  obtain ⟨_, hQP⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_castSuccEmb
  obtain ⟨_, hqP⟩ := (restrictFace_eq_some_iff _ _).mp hP
  -- The literal private face: `ℓ` is the display's labelling on the private cells (as in
  -- `StageType.mem_receivingFamily_of_isGate`).
  have hlit : ∀ x ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb),
      ℓ x = E.display.label x := by
    intro x hx
    have hx' : x ∈ Set.range (E.display.cellMap Fin.castSuccEmb) := by
      rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]
      exact hx
    obtain ⟨i, rfl⟩ := hx'
    exact label_congr (hqP.trans hQP.symm) (i := i) (j := i) rfl
  obtain ⟨-, -, -, hagree⟩ := E.recover_of_isLawful hℓ hlit (hG E.gate rfl)
  -- The donor face of the display is `d`; its labels are those of the visible cells.
  refine ⟨(congrArg StageType.toScheme hd : _), fun i j hij ↦ ?_⟩
  have hj : d.label j = E.display.label (E.display.cellMap (extendByLast f) i) :=
    label_congr hd.symm (i := j) (j := i) hij.symm
  rw [hj]
  exact hagree _ (Scheme.mem_visibleCells.mp (E.display.cellMap_mem _ i))

/-- **The donor face is defined**: a stage type on the scheme of the display, with literal private
face `P` and not `⊥` at the gate, has a face along `extendByLast f`, which agrees with the donor
below the label of the cap. -/
theorem exists_restrictFace_mem_receivingFamily (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ saturationFamily E.display.toScheme)
    (hG : ∀ i : Fin q.card, (i : ℕ) = E.gate → q.label i ≠ ⊥) :
    ∃ d' : StageType.{u} α (m + 1), restrictFace (extendByLast f) q = some d' ∧
      d' ∈ receivingFamily d (E.display.label E.cap) := by
  have hf : univ.map (extendByLast f) ∈ q.toCellScheme.faces := by
    have hq' : q.toScheme = E.display.toScheme := hq
    rw [hq', ← isSome_restrictFace_iff, E.restrictFace_extendByLast]
    rfl
  exact ⟨_, restrictFace_of_mem q _ hf, E.recover hP hq hG (restrictFace_of_mem q _ hf)⟩

end AttachedGatedExtension

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **The gate from the bottom-pattern clause.**  Over an occurrence `y` of a model, an attached
gated extension `E` of the type of `y` is realized: some point `u` extends `y`, and its type `q`
is a coface of the type of `y`, on the scheme of the display, with the display's bottom pattern on
the cells of grade at most the arity of `y`, and not `⊥` at the gate.  Only legality of types,
exact consistency, and the bottom-pattern clause are used. -/
theorem IsModel.exists_attachedGate (hR : R.IsModel) (y : R.Occurrence) {m : ℕ}
    {f : Fin m ↪ Fin y.arity} {d : StageType.{u} α (m + 1)}
    (E : StageType.AttachedGatedExtension y.type f d) :
    ∃ u : Fin (y.arity + 1) ↪ M, Fin.castSuccEmb.trans u = y.tuple ∧
      ∃ q : StageType.{u} α (y.arity + 1), R.eval u = some q ∧ q ∈ y.type.cofaces ∧
        q ∈ StageType.bottomPatternFamily E.display.toScheme E.display.label ∧
        ∀ i : Fin q.card, (i : ℕ) = E.gate → q.label i ≠ ⊥ := by
  obtain ⟨u, hu, q, ⟨hq, hqb⟩, he⟩ :=
    (hR.bottomPattern y E.display.toScheme E.display.label
      ⟨E.display, ⟨E.isLegal, E.restrictFace_castSuccEmb⟩, rfl, fun _ _ h _ ↦ by
        rw [Fin.ext h]⟩).inter_cofaces hR.isConsistent hR.isLegal
  exact ⟨u, hu, q, he, hq, hqb, E.label_gate_ne_bot_of_mem hqb⟩

/-- **Receiving at a given attached gated extension.**  Let `y` be an occurrence of a model
containing the occurrence `x` as its face along `f`, and `E` an attached gated extension of the
type of `y` over `f` with donor `d`.  For every cutoff `c` at most the label of the cap, `R`
realizes over `x` a member of the receiving family of `d` at `c`.  This is a statement about a
given `E`; it is not finite-cut receiving. -/
theorem IsModel.realizesOver_receivingFamily_of_attachedGatedExtension (hR : R.IsModel)
    (x y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (hf : f.trans y.tuple = x.tuple)
    {d : StageType.{u} α (x.arity + 1)} (E : StageType.AttachedGatedExtension y.type f d)
    {c : Label.{u}} (hc : c ≤ E.display.label E.cap) :
    R.RealizesOver x.tuple (StageType.receivingFamily d c) := by
  obtain ⟨u, hu, q, he, hq, hqb, hG⟩ := hR.exists_attachedGate y E
  have hqP : StageType.restrictFace Fin.castSuccEmb q = some y.type := hq.2
  obtain ⟨d', hd', hmem⟩ :=
    E.exists_restrictFace_mem_receivingFamily hqP
      (StageType.bottomPatternFamily_subset_saturationFamily hqb) hG
  refine ⟨(extendByLast f).trans u, ?_, d', StageType.mem_receivingFamily_of_le hmem hc, ?_⟩
  · rw [← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
      Function.Embedding.trans_assoc, hu, hf]
  · rw [hR.isConsistent u q _ he, hd']

end Realization

end VaughtConjecture
