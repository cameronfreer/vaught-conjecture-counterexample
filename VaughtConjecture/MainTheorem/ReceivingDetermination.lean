/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.ExactReceiving
import VaughtConjecture.MainTheorem.ReceivingDomains

/-!
# (R2) and (R3) for receiving models from acquisition and cutoff determination

Roadmap, Layer 3 ((R2) and (R3) of the table of 3.4) and Layer 5 (the receiving route); semantic
contract, items 5 and 12.

(R2) and (R3) for receiving models (`Realization.ReceivingResidualReceiving`, and
`Realization.HollowReceiving` for `Realization.IsReceivingCoverHollowAtBlock`) ask for exact
one-point receiving only in models that have the finite-cut receiving property.  So the coface can
be realized by the model's own receiving, at a cutoff, instead of by generalized saturation, and
the finite statement about stage types that remains is asked only of the members of a receiving
family.  Each item below is compiled in this repository (theorem named), unless marked otherwise.

**(R2) for receiving models** (`Realization.receivingResidualReceiving_of_cutoffDetermination`):
residual acquisition (`Realization.ResidualAcquisition`) and cutoff determination
(`Realization.CutoffDetermination`) for one predicate `P` on acquired contexts give (R2) for
receiving models.  It is the argument of `Realization.residualReceiving_of_cutoffDetermination`,
with finite-cut receiving of every model at every limit stage replaced by finite-cut receiving of
the given model.

**Hollow cutoff determination** (`Realization.HollowCutoffDetermination`, in
`VaughtConjecture.Continuation.ExactReceiving`, a statement about stage
types, open for every predicate of interest): cutoff determination without the bound on the top
grade of the donor.  For every input, one coface `D'` of the context and one permitted cutoff `δ`
are chosen, and then every member of the receiving family of `D'` at `δ` with face the context
must have the donor as its face.  Scheme determination (`Realization.SchemeDetermination`, the
statement asked when the coface is realized by generalized saturation) implies it
(`Realization.HollowCutoffDetermination.of_schemeDetermination`): every member of a receiving
family lies on the scheme of the family.

**(R3) for receiving models** (`Realization.hollowReceiving_of_hollowCutoffDetermination`,
`Realization.receivingHollowReceiving_of_cutoffDetermination`): hollow acquisition
(`Realization.HollowAcquisition`) and hollow cutoff determination for one predicate give (R3) for
every predicate on realizations that implies the acquisition predicate and finite-cut receiving,
in particular for `Realization.IsReceivingCoverHollowAtBlock` from acquisition at
`Realization.IsCoverHollowAtBlock`.

The predicates of the acquired contexts (the source-gap context of (R2) and the marked-cap context
of (R3)) are not defined in this module; the two compositions are generic in the predicate, and
cutoff determination is not proved for any predicate here.

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Label

namespace Realization

variable {α : Ordinal.{u}}

/-! ### (R2) for receiving models -/

/-- **(R2) for receiving models from residual acquisition and cutoff determination**, for any
predicate `P` on acquired contexts.  The coface is realized over the acquired context by the
finite-cut receiving of the given model, which (R2) for receiving models assumes; no receiving of
any other model is used. -/
theorem receivingResidualReceiving_of_cutoffDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, ℕ → StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hacq : ResidualAcquisition.{u, w} P) (hdet : CutoffDetermination.{u} P) :
    ReceivingResidualReceiving.{u, w} where
  exists_covers α M R K hα hR hrec hcore hK n t c hc d hd hdK := by
    obtain ⟨k, t', c', h, hc', hcc', hP⟩ := hacq.exists_context hα hR hcore hK t c hc
    obtain ⟨D', hD', δ, hδ, hdet'⟩ := hdet.exists_coface t' h hα (hR.isLegal _ _ hc'.eval_eq) hP
      t (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd hdK
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      (hrec.realizesOver_receivingFamily hc' hD' hδ) hdet'

/-! ### (R3) for receiving models -/

/-- **(R3) from hollow acquisition and hollow cutoff determination**, for any predicate `P` on
acquired contexts and every predicate `H'` on realizations that implies the acquisition predicate
`H` and finite-cut receiving.  The coface is realized over the acquired context by the finite-cut
receiving of the given model. -/
theorem hollowReceiving_of_hollowCutoffDetermination
    {H H' : ∀ {α : Ordinal.{u}} {M : Type w}, Realization.{u, w} α M → Prop}
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hacq : HollowAcquisition.{u, w} H P) (hdet : HollowCutoffDetermination.{u} P)
    (hH : ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type w⦄ ⦃R : Realization.{u, w} α M⦄, H' R →
      H R ∧ R.HasFiniteCutReceiving) :
    HollowReceiving.{u, w} H' where
  exists_covers α M R hα hR hH' htop n t c hc d hd := by
    obtain ⟨k, t', c', h, hc', hcc', hP⟩ := hacq.exists_context hα hR (hH hH').1 htop t c hc
    obtain ⟨D', hD', δ, hδ, hdet'⟩ := hdet.exists_coface t' h hα (hR.isLegal _ _ hc'.eval_eq) hP
      t (restrictFace_of_covers hR.isConsistent hc hc' hcc') d hd
    rw [← hcc']
    exact exists_covers_snoc_of_isDeterminedWithin hR.isConsistent hc'
      ((hH hH').2.realizesOver_receivingFamily hc' hD' hδ) hdet'

/-- **(R3) for receiving models from hollow acquisition and hollow cutoff determination**: hollow
acquisition for cover-hollowness at a block stage and hollow cutoff determination, for one
predicate `P`, give `HollowReceiving` for `IsReceivingCoverHollowAtBlock`, the (R3) hypothesis of
the receiving route. -/
theorem receivingHollowReceiving_of_cutoffDetermination
    {P : ∀ {α : Ordinal.{u}} {n k : ℕ}, StageType.{u} α k → (Fin n ↪ Fin k) → Prop}
    (hacq : HollowAcquisition.{u, w} IsCoverHollowAtBlock P)
    (hdet : HollowCutoffDetermination.{u} P) :
    HollowReceiving.{u, w} IsReceivingCoverHollowAtBlock :=
  hollowReceiving_of_hollowCutoffDetermination hacq hdet fun _ _ _ h ↦ h

end Realization

end VaughtConjecture
