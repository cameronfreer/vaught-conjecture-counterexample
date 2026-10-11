/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.CappedAttachedGateReceiving
import VaughtConjecture.Realization.MarginContext
import VaughtConjecture.Extension.AttachedPredecessorFromCoatoms

/-!
# Finite-cut receiving through capped attached gated extensions

Roadmap, Layer 3, 3.2 (the ordinary construction (R1)) and 3.4 (the receiving rows); the private
context with the margin of `VaughtConjecture.Realization.MarginContext` and the capped attached
gated extensions of `VaughtConjecture.Realization.CappedAttachedGateReceiving`.

**The assembly** (`Realization.IsModel.hasFiniteCutReceiving_of_cappedAttachedGatedExtensions`).
Let `R` be a model at a stage `α` that is zero or a limit.  Assume, as an explicit hypothesis on
stage types at `α`, that every legal stage type `P` on `n` points, with a face `f` on `m` points,
`m + 1 < n`, a legal donor `d` on `m + 1` points whose face along the initial segment is the face of
`P` along `f`, and reference data with the margin on the cells of `P` (full grade `n`, cap of graded
index `(univ, n)`) in whose blocks `d` reads, has a capped attached gated extension over `f` with
donor `d` whose cut is at least the cut of the labels of `P`.  Then `R` has finite-cut receiving.
For a cutoff `ν`, the private context with the margin (`IsModel.exists_marginContext`) has
`ν` below the cut of its labels, and the capped attached gated extension over it gives a realized
member of the receiving family at `ν`
(`IsModel.realizesOver_receivingFamily_of_cappedAttachedGatedExtension`).

**With the attached predecessor**
(`Realization.IsModel.hasFiniteCutReceiving_of_attachedPredecessors`).  Under the coatom extension
property (`StageType.HasCoatomExtensions α`) an attached predecessor exists over every acquired
private context (`StageType.AttachedPredecessor.nonempty_of_hasCoatomExtensions`), so it is
enough that every attached predecessor carries a capped attached gated extension with cut at
least the cut of the private labels: the **gated layer**.

The gated layer is not proved here: it is the construction of a catalogue layer at `(univ, n)`
over the predecessor whose readers read the donor in the capped reading
(`VaughtConjecture.Extension.CappedGate`), with the extensions through the layer at the short caps
along every reader producing a reader again; **open**.  So neither theorem is a proof of (R1).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`, beside
`VaughtConjecture.Realization.CoupledFiniteCutReceiving`.

## References

The model clauses are those of [Kni26, Definition 3.2.1]; the private context is that of
[Kni26, Lemma 8.1.1].
-/

universe u v

namespace VaughtConjecture

open Finset Label CappedDonorReading

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} α M}

/-- **(R1) from capped attached gated extensions over the private contexts with the margin.**  At
a stage that is zero or a limit, a model has finite-cut receiving provided every legal private type
with reference data with the margin, for every legal donor over a face of it whose labels read in
the blocks, has a capped attached gated extension whose cut is at least the cut of its labels.  The
hypothesis is explicit and open. -/
theorem IsModel.hasFiniteCutReceiving_of_cappedAttachedGatedExtensions (hR : R.IsModel)
    (hα : Order.IsSuccPrelimit α)
    (hext : ∀ ⦃n m : ℕ⦄ (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
      (d : StageType.{u} α (m + 1)) (Pr : PrivateReference.{u} (Fin P.card)), P.IsLegal →
      d.IsLegal → StageType.restrictFace Fin.castSuccEmb d = StageType.restrictFace f P →
      m + 1 < n → Pr.fullGrade = n → P.toCellScheme.gradedIndex Pr.cap = (univ, n) →
      Pr.HasMargin P.rows P.label → Pr.ReadsInBlocks d.label →
      ∃ E : StageType.CappedAttachedGatedExtension P f d,
        Pr.cut P.label ≤ E.reference.cut E.display.label) :
    R.HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨ν, hνα, rfl⟩ := isPermittedCutoff_iff.mp hc
  obtain ⟨y, f, Pr, hf, hn, -, hfull, hcap, hP, hblk, -, hcut, -, -⟩ :=
    hR.exists_marginContext hα x d hνα 0
  have hfx : StageType.restrictFace f y.type = some x.type :=
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hf
  obtain ⟨E, hE⟩ := hext y.type f d Pr (hR.isLegal _ _ y.eval_tuple) hd.1 (hd.2.trans hfx.symm)
    hn hfull hcap hP hblk
  exact hR.realizesOver_receivingFamily_of_cappedAttachedGatedExtension x y f hf E
    (hcut.le.trans hE)


/-- **(R1) from the coatom extension property and a gated layer over every attached
predecessor.**  At a stage that is zero or a limit, a model has finite-cut receiving provided the
coatom extension property holds and every attached predecessor of a legal private type with
reference data with the margin, over a face with a legal donor reading in the blocks, carries a
capped attached gated extension whose cut is at least the cut of the private labels.  The coatom
extension property supplies the attached predecessor
(`StageType.AttachedPredecessor.nonempty_of_hasCoatomExtensions`); the second hypothesis, the
gated layer, is explicit and open. -/
theorem IsModel.hasFiniteCutReceiving_of_attachedPredecessors (hR : R.IsModel)
    (hα : Order.IsSuccPrelimit α) (hext : StageType.HasCoatomExtensions.{u} α)
    (hgate : ∀ ⦃n m : ℕ⦄ (P : StageType.{u} α n) (f : Fin m ↪ Fin n)
      (d : StageType.{u} α (m + 1)) (Pr : PrivateReference.{u} (Fin P.card)),
      StageType.AttachedPredecessor P f d → Pr.fullGrade = n →
      P.toCellScheme.gradedIndex Pr.cap = (univ, n) → Pr.HasMargin P.rows P.label →
      Pr.ReadsInBlocks d.label →
      ∃ E : StageType.CappedAttachedGatedExtension P f d,
        Pr.cut P.label ≤ E.reference.cut E.display.label) :
    R.HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨ν, hνα, rfl⟩ := isPermittedCutoff_iff.mp hc
  obtain ⟨y, f, Pr, hf, hn, -, hfull, hcap, hP, hblk, -, hcut, -, -⟩ :=
    hR.exists_marginContext hα x d hνα 0
  have hfx : StageType.restrictFace f y.type = some x.type :=
    Occurrence.restrictFace_eq_some_of_trans_eq hR.isConsistent hf
  obtain ⟨A⟩ := StageType.AttachedPredecessor.nonempty_of_hasCoatomExtensions hext
    (hR.isLegal _ _ y.eval_tuple) hfx hd.1 hd.2 hn
  obtain ⟨E, hE⟩ := hgate y.type f d Pr A hfull hcap hP hblk
  exact hR.realizesOver_receivingFamily_of_cappedAttachedGatedExtension x y f hf E
    (hcut.le.trans hE)

end Realization

end VaughtConjecture
