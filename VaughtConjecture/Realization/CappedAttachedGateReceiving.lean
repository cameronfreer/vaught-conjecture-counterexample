/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.AttachedGate
import VaughtConjecture.Extension.CappedGate
import VaughtConjecture.Realization.AttachedGateReceiving

/-!
# Attached gated extensions with the capped reading

Roadmap, Layer 3, 3.2 (the ordinary construction (R1): one occurrence over the private tuple with
the display's bottom pattern) and 3.3 (the recovery statements, item 1: agreement below a cutoff);
the attached gated extensions of `VaughtConjecture.Extension.AttachedGate`, with the readers read
by the capped reading of `VaughtConjecture.Extension.CappedGate`.

A **capped attached gated extension** (`StageType.CappedAttachedGatedExtension P f d`) has the
fields of an attached gated extension (`StageType.AttachedGatedExtension`) other than its cap and
its exact readings: a legal display on `n + 1` points with literal faces `P` (along
`Fin.castSuccEmb`) and `d` (along `extendByLast f`), a gate of graded index `(univ, n)` not
labelled `⊥`, readers of that graded index, the row of the gate `⊥` at every other cell of its
graded index outside the readers (`CellScheme.Rows.ReadsOnly`) and reading one reader, the
**ceiling**, at least as the gate; and in place of the exact readings, **reference data**
(`CappedDonorReading.PrivateReference`) on the cells of the display, for which every reader is a
capped gate (`CellScheme.Rows.IsCappedGate`) with the private cells the cells visible through
`Fin.castSuccEmb` and the donor cells those visible through `extendByLast f`.

**Recovery below the cut** (`StageType.CappedAttachedGatedExtension.recover`).  A stage type `q`
on the scheme of the display with literal private face `P` and not `⊥` at the gate has a donor
face in the receiving family of `d` at the cut of the display labels
(`CellScheme.Rows.IsLawful.recover_of_readsOnly_capped`).

**Receiving** (`Realization.IsModel.realizesOver_receivingFamily_of_cappedAttachedGatedExtension`).
Over an occurrence `x` that is the face of an occurrence `y` of a model along `f`, a capped
attached gated extension of the type of `y` over `f` with donor `d` gives, for every cutoff `c` at
most the cut of the display labels, a realized member of the receiving family of `d` at `c`: the
bottom-pattern clause over `y` realizes the display's pattern, with the gate not `⊥`.  This is a
statement about a given extension.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.AttachedGateReceiving`.

## References

The bottom-pattern clause is [Kni26, Definition 3.2.1], clause 4(a)ii; the private context is that
of [Kni26, Lemma 8.1.1].
-/

universe u v

namespace VaughtConjecture

open Finset Label CappedDonorReading

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ}

/-- A **capped attached gated extension** of a stage type `P` on `n` points over the face `f`,
with donor `d` on `m + 1` points: a legal display with literal faces `P` and `d`; a gate of
graded index `(univ, n)`, not `⊥` in the display; readers of that graded index; the row of the
gate `⊥` at every other cell of its graded index outside the readers and reading one reader, the
ceiling, at least as the gate; and reference data on the cells of the display for which every
reader is a capped gate, with the private cells visible through `Fin.castSuccEmb` and the donor
cells visible through `extendByLast f`. -/
structure CappedAttachedGatedExtension (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
    (d : StageType.{u} α (m + 1)) where
  /-- The display. -/
  display : StageType.{u} α (n + 1)
  /-- The display is legal. -/
  isLegal : display.IsLegal
  /-- The private face of the display is literally `P`. -/
  restrictFace_castSuccEmb : restrictFace Fin.castSuccEmb display = some P
  /-- The donor face of the display is literally `d`. -/
  restrictFace_extendByLast : restrictFace (extendByLast f) display = some d
  /-- The gate. -/
  gate : Fin display.card
  /-- The readers. -/
  readers : Set (Fin display.card)
  /-- The ceiling, a reader that the gate reads at least as itself. -/
  ceiling : Fin display.card
  /-- The ceiling is a reader. -/
  ceiling_mem : ceiling ∈ readers
  /-- The gate has full scope and grade `n`. -/
  gradedIndex_gate : display.toCellScheme.gradedIndex gate = (univ, n)
  /-- The readers have full scope and grade `n`. -/
  gradedIndex_reader : ∀ K ∈ readers, display.toCellScheme.gradedIndex K = (univ, n)
  /-- The display does not label the gate `⊥`. -/
  label_gate_ne_bot : display.label gate ≠ ⊥
  /-- The row of the gate is `⊥` at every other cell of its graded index outside the readers. -/
  readsOnly : display.rows.ReadsOnly gate readers
  /-- The row of the gate reads the ceiling at least as it reads the gate. -/
  row_gate_le_ceiling : display.rows.row gate ⟨gate, display.toCellScheme.mem_below_gradedIndex _⟩ ≤
    display.rows.row gate
      ⟨ceiling, ((gradedIndex_reader ceiling ceiling_mem).trans gradedIndex_gate.symm).le⟩
  /-- The reference data of the capped reading. -/
  reference : PrivateReference.{u} (Fin display.card)
  /-- Every reader is a capped gate. -/
  isCappedGate : ∀ K ∈ readers, display.rows.IsCappedGate K reference
    (display.toCellScheme.visible (Set.range Fin.castSuccEmb))
    (display.toCellScheme.visible (Set.range (extendByLast f))) display.label

namespace CappedAttachedGatedExtension

variable {P : StageType.{u} α n} {f : Fin m ↪ Fin n} {d : StageType.{u} α (m + 1)}
  (E : CappedAttachedGatedExtension P f d) {q : StageType.{u} α (n + 1)}

/-- The ceiling has the graded index of the gate. -/
theorem gradedIndex_ceiling_eq :
    E.display.toCellScheme.gradedIndex E.ceiling = E.display.toCellScheme.gradedIndex E.gate :=
  (E.gradedIndex_reader E.ceiling E.ceiling_mem).trans E.gradedIndex_gate.symm

/-- The gate has grade `n`. -/
theorem grade_gate : E.display.toCellScheme.grade E.gate = n :=
  congrArg Prod.snd E.gradedIndex_gate

/-- **The gate equation**: a member of the bottom-pattern family of the display is not `⊥` at the
gate, a cell of grade `n`, which the family tests. -/
theorem label_gate_ne_bot_of_mem (hq : q ∈ bottomPatternFamily E.display.toScheme E.display.label)
    (i : Fin q.card) (hi : (i : ℕ) = E.gate) : q.label i ≠ ⊥ := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain ⟨rfl, hpat⟩ := hq
  obtain rfl := Fin.ext hi
  exact label_ne_bot_of_mem_bottomPatternFamily ⟨rfl, hpat⟩ _ _ rfl E.grade_gate.le
    E.label_gate_ne_bot

/-- **Recovery below the cut for a lawful labelling of the display's rows**, literally the display
on the private cells and not `⊥` at the gate. -/
theorem recover_of_isLawful {ℓ : Fin E.display.card → Label.{u}}
    (hℓ : E.display.rows.IsLawful ℓ)
    (hlit : ∀ x ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb),
      ℓ x = E.display.label x) (hG : ℓ E.gate ≠ ⊥) :
    ∀ e ∈ E.display.toCellScheme.visible (Set.range (extendByLast f)),
      min (ℓ e) (E.reference.cut E.display.label) =
        min (E.display.label e) (E.reference.cut E.display.label) :=
  hℓ.recover_of_readsOnly_capped E.readsOnly E.isCappedGate E.ceiling_mem E.gradedIndex_ceiling_eq
    E.row_gate_le_ceiling hlit hG

/-- **Recovery below the cut.**  A stage type on the scheme of the display, with literal private
face `P` and not `⊥` at the gate, has a donor face that agrees with the donor `d` below the cut of
the display labels. -/
theorem recover (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ saturationFamily E.display.toScheme)
    (hG : ∀ i : Fin q.card, (i : ℕ) = E.gate → q.label i ≠ ⊥) {d' : StageType.{u} α (m + 1)}
    (hd' : restrictFace (extendByLast f) q = some d') :
    d' ∈ receivingFamily d (E.reference.cut E.display.label) := by
  obtain ⟨S, ℓ, hw, hc, hℓ, hat⟩ := q
  obtain rfl : S = E.display.toScheme := hq
  obtain ⟨hfd, hd⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_extendByLast
  obtain ⟨hfd', rfl⟩ := (restrictFace_eq_some_iff _ _).mp hd'
  obtain ⟨_, hQP⟩ := (restrictFace_eq_some_iff _ _).mp E.restrictFace_castSuccEmb
  obtain ⟨_, hqP⟩ := (restrictFace_eq_some_iff _ _).mp hP
  -- The literal private face: `ℓ` is the display's labelling on the private cells.
  have hlit : ∀ x ∈ E.display.toCellScheme.visible (Set.range Fin.castSuccEmb),
      ℓ x = E.display.label x := by
    intro x hx
    have hx' : x ∈ Set.range (E.display.cellMap Fin.castSuccEmb) := by
      rw [Scheme.range_cellMap, mem_coe, Scheme.mem_visibleCells]
      exact hx
    obtain ⟨i, rfl⟩ := hx'
    exact label_congr (hqP.trans hQP.symm) (i := i) (j := i) rfl
  have hagree := E.recover_of_isLawful hℓ hlit (hG E.gate rfl)
  -- The donor face of the display is `d`; its labels are those of the visible cells.
  refine ⟨(congrArg StageType.toScheme hd : _), fun i j hij ↦ ?_⟩
  have hj : d.label j = E.display.label (E.display.cellMap (extendByLast f) i) :=
    label_congr hd.symm (i := j) (j := i) hij.symm
  rw [hj]
  exact hagree _ (Scheme.mem_visibleCells.mp (E.display.cellMap_mem _ i))

/-- **The donor face is defined** and agrees with the donor below the cut. -/
theorem exists_restrictFace_mem_receivingFamily (hP : restrictFace Fin.castSuccEmb q = some P)
    (hq : q ∈ saturationFamily E.display.toScheme)
    (hG : ∀ i : Fin q.card, (i : ℕ) = E.gate → q.label i ≠ ⊥) :
    ∃ d' : StageType.{u} α (m + 1), restrictFace (extendByLast f) q = some d' ∧
      d' ∈ receivingFamily d (E.reference.cut E.display.label) := by
  have hf : univ.map (extendByLast f) ∈ q.toCellScheme.faces := by
    have hq' : q.toScheme = E.display.toScheme := hq
    rw [hq', ← isSome_restrictFace_iff, E.restrictFace_extendByLast]
    rfl
  exact ⟨_, restrictFace_of_mem q _ hf, E.recover hP hq hG (restrictFace_of_mem q _ hf)⟩

end CappedAttachedGatedExtension

end StageType

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **Receiving at a given capped attached gated extension.**  Let `y` be an occurrence of a
model containing the occurrence `x` as its face along `f`, and `E` a capped attached gated
extension of the type of `y` over `f` with donor `d`.  For every cutoff `c` at most the cut of the
display labels, `R` realizes over `x` a member of the receiving family of `d` at `c`. -/
theorem IsModel.realizesOver_receivingFamily_of_cappedAttachedGatedExtension (hR : R.IsModel)
    (x y : R.Occurrence) (f : Fin x.arity ↪ Fin y.arity) (hf : f.trans y.tuple = x.tuple)
    {d : StageType.{u} α (x.arity + 1)} (E : StageType.CappedAttachedGatedExtension y.type f d)
    {c : Label.{u}} (hc : c ≤ E.reference.cut E.display.label) :
    R.RealizesOver x.tuple (StageType.receivingFamily d c) := by
  obtain ⟨u, hu, q, ⟨hq, hqb⟩, he⟩ :=
    (hR.bottomPattern y E.display.toScheme E.display.label
      ⟨E.display, ⟨E.isLegal, E.restrictFace_castSuccEmb⟩, rfl, fun _ _ h _ ↦ by
        rw [Fin.ext h]⟩).inter_cofaces hR.isConsistent hR.isLegal
  have hqP : StageType.restrictFace Fin.castSuccEmb q = some y.type := hq.2
  obtain ⟨d', hd', hmem⟩ :=
    E.exists_restrictFace_mem_receivingFamily hqP
      (StageType.bottomPatternFamily_subset_saturationFamily hqb) (E.label_gate_ne_bot_of_mem hqb)
  refine ⟨(extendByLast f).trans u, ?_, d', StageType.mem_receivingFamily_of_le hmem hc, ?_⟩
  · rw [← Function.Embedding.trans_assoc, castSuccEmb_trans_extendByLast,
      Function.Embedding.trans_assoc, hu, hf]
  · rw [hR.isConsistent u q _ he, hd']

end Realization

end VaughtConjecture
