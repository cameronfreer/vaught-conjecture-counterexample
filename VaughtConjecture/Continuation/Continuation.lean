/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Candidate
import VaughtConjecture.Continuation.Classification
import VaughtConjecture.Realization.CapToModel
/-!
# Output 3 from stable capped receiving, and the continuation criterion

Roadmap, Layer 4, output 3 of higher-stage reconstruction (the modelhood criterion: non-hollow
unbounded top-grade growth makes the stable candidate a model, by (R4) of the table of Layer 3
with its empty-root base case and the cap-to-model theorem); semantic contract, item 8.

Throughout, `R` is a realization at the block stage `λ_ξ = blockStage ξ` on a carrier `M`, and
`λ_{ξ+1} = blockStage (ξ + 1) = λ_ξ + ω` is the next block stage.  The stable candidate of
`VaughtConjecture.Continuation.Candidate` at `λ_{ξ+1}` is defined from a proof that `R` is stably
lawful; for a model `R` the proof is `Realization.IsModel.isStablyLawful`, and the candidate is
`R.stableCandidate hR.isStablyLawful`.  Stable lawfulness is not a hypothesis here: every model at
a block stage is stably lawful, availability at **twins** (two cells labelled the formal top at
one graded index) coming from the legality of the realized covers (in
`VaughtConjecture.Continuation.Candidate`).

**Output 3 is proved here only conditionally**, on two hypotheses, each still to be proved:

* **(R4)**, stable capped receiving (`StableCappedReceiving`), as stated below;
* **the nonempty coface instances at `λ_{ξ+1}`** (`StageType.HasNonemptyCofaceInstances`, in
  `VaughtConjecture.Realization.Families`): the amalgam of a legal stage type with a legal stage
  type on one point over the empty face, and nonempty uniformity and dominance instances among the
  cofaces of every legal stage type.  All three follow from the coatom extension property with apex
  at `λ_{ξ+1}` (`StageType.HasNonemptyCofaceInstances.of_hasApexCoatomExtensions`, in
  `VaughtConjecture.Extension.FamilyCofaces`, which this layer does not import); that property is
  compiled in this repository (theorem named) (`StageType.hasApexCoatomExtensions_blockStage`).

**(R4)** (`StableCappedReceiving`).  For a model `R` at `λ_ξ`, `ξ < ω₁`, not cover-hollow, with
top-grade supremum `⊤`, and its stable candidate `R.stableCandidate hR.isStablyLawful`: over every
occurrence of the candidate of positive arity, for every coface `D` of its type and every ordinal
`γ < λ_{ξ+1}`, some point extends the occurrence to one whose candidate type `Q` is on the scheme
of `D`, equals `D` at every cell where `D` is not the formal top (bottom included), and exceeds `γ`
at every cell where `D` is the formal top.  Such a `Q` is in the receiving family of `D` at the
cutoff `γ` (`StageType.mem_receivingFamily_of_capped`), so (R4) is finite-cut receiving of the
candidate over positive roots.  The candidate does not depend on the proof of stable lawfulness
from which it is defined, so (R4) is equivalent to its form for the candidate defined from every
such proof (`stableCappedReceiving_iff_forall_isStablyLawful`).  Its proof is to combine the
following, none of which is proved or used here: the acquisition, in `R`, of a private context
calibrated to the stable labels (non-hollowness supplies an attained proper stable value,
unbounded growth a private cap whose stable value is proper and above every requested `γ`); the
growth construction with its section theorem, shared with (R3); the recovery statement of (R3)
and (R4) for restriction-compatible labellings, evaluated on the stable labelling; and the
realization of the constructed scheme over the private context by generalized saturation of `R`.

**The empty root** (`Realization.hasFiniteCutReceiving_of_pos`, in
`VaughtConjecture.Realization.Model`).  (R4) concerns positive roots only.  Over the empty root,
for a one-point donor `D`, covering gives an occurrence of positive arity, the amalgam over the
empty face combines its type with `D` into a coface `Q`, the positive-root statement receives `Q`
over that occurrence, and exact consistency restricts the received type to the new point, where it
lies in the receiving family of `D` (`StageType.exists_restrictFace_mem_receivingFamily`).  This
is the coatom extension at `λ_{ξ+1}`, not the padding by high-arity dominance at `λ_ξ` used in
(R3).

**The assembly** (`Realization.isModel_stableCandidate`) is the cap-to-model theorem at the nonzero
limit stage `λ_{ξ+1}` (`Realization.isModel_of_hasFiniteCutReceiving`):

* the nonempty carrier, legal types, exact consistency and covering of the candidate come from
  those of the model `R` (`Realization.hasLegalTypes_stableCandidate`,
  `Realization.isConsistent_stableCandidate`, `Realization.isCovering_stableCandidate`);
* finite-cut receiving comes from (R4) over positive roots and the amalgam field of the coface
  instances over the empty root (`Realization.hasFiniteCutReceiving_stableCandidate`);
* the uniformity and dominance instances of the clauses of a model are nonempty by the other two
  fields of the coface instances ([Kni26, Lemmas 4.4.2 and 4.4.3]); given finite-cut receiving,
  only these instances are used (`Realization.isModel_stableCandidate_of_hasFiniteCutReceiving`).

**Where non-hollowness and unbounded growth enter.**  In the assembly they are read only as
hypotheses of (R4).  Their role is the receiving of the clauses of a model at `λ_{ξ+1}` that
concern the new block `[λ_ξ, λ_ξ + ω)`:

* **uniformity at `γ = λ_ξ`** is received at the cutoff `L + 1` from a donor with a label `L` in
  `[λ_ξ, λ_ξ + ω)`, so the candidate needs labels in that block.  The candidate of a cover-hollow
  realization has none and is not a model
  (`Realization.not_isModel_stableCandidate_of_isCoverHollow`); without cover-hollowness the
  attained proper stable label
  (`Realization.exists_stableLabel_eq_coe_add_of_not_isCoverHollow`) is such a label of the
  candidate (`Realization.exists_stableCandidate_label_eq_coe_add`);
* **high-arity dominance at `γ = λ_ξ + K`** is received at the cutoff `γ + 1`, so the candidate
  needs labels above `λ_ξ + K` for every `K`.  If every stable label is at most `λ_ξ + K`, the
  candidate is not a model (`Realization.not_isModel_stableCandidate_of_stableLabel_le`); with
  top-grade supremum `⊤`, the order law gives labels of the candidate above every `λ_ξ + K`
  (`Realization.exists_lt_stableCandidate_label`).

These two lemmas are not used in the assembly; they show that the candidate has the labels that
these clauses require, and (R4) is to realize such labels over every root.

**The continuation criterion** (`ContinuationCriterion.of_stableCappedReceiving`).  From (R4) and
the coface instances at every `λ_{ξ+1}` with `ξ < ω₁`, the continuation criterion of
`VaughtConjecture.Continuation.Classification` holds: the expansion of a model `R` that is not
cover-hollow and has top-grade supremum `⊤` is its stable candidate, which reduces to `R`
(`Realization.stableCandidate_reduce`).  So the criterion, and output 3, are conditional on (R4)
and the coface instances at the next block only; under the coatom extension property with apex,
on (R4) and that property at every next block (`ContinuationCriterion.of_hasApexCoatomExtensions`,
in `VaughtConjecture.MainTheorem.CapToModel`).  The derivation uses neither the converse of the
criterion, nor (R1), forcing donors, normalization, or uniqueness of expansions.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.

## References

Models are [Kni26, Definition 3.2.1]; the nonemptiness of the uniformity and dominance instances is
[Kni26, Lemmas 4.4.2 and 4.4.3].
-/

universe u v w

namespace VaughtConjecture

open Ordinal Label StageType

namespace Realization

/-! ### The labels of the candidate in the new block -/

section NewBlock

variable {ξ : Ordinal.{u}} {M : Type v} {R : Realization.{u, v} (blockStage ξ) M}

/-- **Non-hollowness gives a label of the candidate in `[λ_ξ, λ_ξ + ω)`**: if `R` is not
cover-hollow, some type of the candidate has the label `λ_ξ + i` for some `i : ℕ`, at a cell
labelled the formal top in `R` (the attained proper stable label). -/
theorem exists_stableCandidate_label_eq_coe_add (hnh : ¬ R.IsCoverHollow)
    (hlaw : R.IsStablyLawful) :
    ∃ (x : (R.stableCandidate hlaw).Occurrence) (a : Fin x.type.card) (i : ℕ),
      x.type.label a = ((blockStage ξ + i : Ordinal.{u}) : Label.{u}) := by
  obtain ⟨x, a, i, ha, h⟩ := exists_stableLabel_eq_coe_add_of_not_isCoverHollow hnh
  exact ⟨⟨x.arity, x.tuple, _, stableCandidate_eval_of_eval x.eval_tuple⟩, a, i,
    (stableSection_of_eq_top ha).trans h⟩

/-- **Unbounded growth gives labels of the candidate above every `λ_ξ + K`**: if the top-grade
supremum of `R` is `⊤`, then for every `K : ℕ` some type of the candidate has a label above
`λ_ξ + K`, at a cell labelled the formal top in `R` of grade above `K` (the order law). -/
theorem exists_lt_stableCandidate_label (hgrow : R.topGradeSup = ⊤) (hlaw : R.IsStablyLawful)
    (K : ℕ) : ∃ (x : (R.stableCandidate hlaw).Occurrence) (a : Fin x.type.card),
      ((blockStage ξ + K : Ordinal.{u}) : Label.{u}) < x.type.label a := by
  obtain ⟨x, hx⟩ : ∃ x : R.Occurrence, K < x.type.topGrade := by
    by_contra! h
    have hle : R.topGradeSup ≤ K := iSup_le fun x ↦ Nat.cast_le.mpr (h x)
    simp [hgrow] at hle
  obtain ⟨d, hd, hKd⟩ : ∃ d, x.type.label d = ⊤ ∧ K < x.type.toCellScheme.grade d := by
    by_contra! h
    exact hx.not_ge (topGrade_le_iff.mpr h)
  refine ⟨⟨x.arity, x.tuple, _, stableCandidate_eval_of_eval x.eval_tuple⟩, d, ?_⟩
  -- the label of the stable type at `d` is the stable section there
  change _ < R.stableSection x.tuple x.type d
  rcases stableSection_eq_top_or_exists x.eval_tuple hd with h | ⟨i, hi, h⟩
  · rw [h]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  · rw [h]
    exact_mod_cast add_lt_add_right (Nat.cast_lt.mpr (hKd.trans_le hi)) _

end NewBlock

end Realization

/-! ### (R4) and the assembly -/

/-- **Stable capped receiving**, (R4) of the table of Layer 3, still to be proved: for a model `R`
at `λ_ξ`, `ξ < ω₁`, not cover-hollow, with top-grade supremum `⊤`, and its stable candidate
`R.stableCandidate hR.isStablyLawful` (every model is stably lawful,
`Realization.IsModel.isStablyLawful`), over every occurrence of positive arity of the candidate,
for every coface `D` of its type and every ordinal `γ < λ_{ξ+1}`, some point extends the
occurrence to one whose candidate type is on the scheme of `D`, equals `D` at every cell where `D`
is not the formal top, and exceeds `γ` at every cell where `D` is the formal top.  It is to be
proved by the growth construction shared with (R3), calibrated to the stable labels and realized
by generalized saturation of `R`. -/
structure StableCappedReceiving : Prop where
  /-- Receiving of the stable candidate over positive roots, capped at every `γ < λ_{ξ+1}`. -/
  receive ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M) :
    ξ < ω₁ → ∀ hR : R.IsModel, ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, 0 < x.arity →
        ∀ D ∈ x.type.cofaces, ∀ γ : Ordinal.{0}, γ < blockStage (ξ + 1) →
          ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
            ∃ Q, (R.stableCandidate hR.isStablyLawful).eval u = some Q ∧
              Q.toScheme = D.toScheme ∧ ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
                (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
                  (D.label j = ⊤ → (γ : Label.{0}) < Q.label i)

/-- **(R4) for the candidate defined from every proof of stable lawfulness**: (R4) is equivalent
to its form in which the stable candidate of the model is defined from an arbitrary proof `hlaw`
that the model is stably lawful, since the candidate does not depend on that proof. -/
theorem stableCappedReceiving_iff_forall_isStablyLawful :
    StableCappedReceiving.{w} ↔
      ∀ ⦃ξ : Ordinal.{0}⦄ ⦃M : Type w⦄ (R : Realization.{0, w} (blockStage ξ) M),
        ξ < ω₁ → R.IsModel → ∀ hlaw : R.IsStablyLawful, ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
          ∀ x : (R.stableCandidate hlaw).Occurrence, 0 < x.arity → ∀ D ∈ x.type.cofaces,
            ∀ γ : Ordinal.{0}, γ < blockStage (ξ + 1) →
              ∃ u : Fin (x.arity + 1) ↪ M, Fin.castSuccEmb.trans u = x.tuple ∧
                ∃ Q, (R.stableCandidate hlaw).eval u = some Q ∧ Q.toScheme = D.toScheme ∧
                  ∀ (i : Fin Q.card) (j : Fin D.card), (i : ℕ) = j →
                    (D.label j ≠ ⊤ → Q.label i = D.label j) ∧
                      (D.label j = ⊤ → (γ : Label.{0}) < Q.label i) :=
  ⟨fun h _ _ R hξ hR _ ↦ h.receive R hξ hR,
    fun h ↦ ⟨fun _ _ R hξ hR ↦ h R hξ hR hR.isStablyLawful⟩⟩

namespace Realization

variable {ξ : Ordinal.{0}} {M : Type w} {R : Realization.{0, w} (blockStage ξ) M}

/-- **Modelhood of the candidate from finite-cut receiving**: for a model `R`, the stable candidate
with the finite-cut receiving property is a model, given the uniformity and dominance instances of
the coface instances at `λ_{ξ+1}` (the cap-to-model theorem at `λ_{ξ+1}`). -/
theorem isModel_stableCandidate_of_hasFiniteCutReceiving (hR : R.IsModel)
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1)))
    (hr : (R.stableCandidate hR.isStablyLawful).HasFiniteCutReceiving) :
    (R.stableCandidate hR.isStablyLawful).IsModel :=
  have hl := hasLegalTypes_stableCandidate (hlaw := hR.isStablyLawful) hR.hasLegalTypes
  isModel_of_hasFiniteCutReceiving (isSuccLimit_blockStage (ξ + 1)) hR.nonempty hl
    (isConsistent_stableCandidate hR.isConsistent hR.isCovering)
    (isCovering_stableCandidate hR.isCovering) hr
    (fun x γ hγ hγα ↦ hinst.uniformity x.type (hl _ _ x.eval_tuple) γ hγ hγα)
    (fun x γ hγα ↦ hinst.dominance x.type (hl _ _ x.eval_tuple) γ hγα)

/-- **Finite-cut receiving of the candidate**, conditional on (R4): over positive roots by (R4) at
the cutoff `γ`, and over the empty root by the amalgam over the empty face at `λ_{ξ+1}` (the field
`exists_amalgam_empty` of the coface instances; the other two fields are not used).
Non-hollowness and unbounded growth are used only as hypotheses of (R4). -/
theorem hasFiniteCutReceiving_stableCandidate (hξ : ξ < ω₁) (hR : R.IsModel)
    (hnh : ¬ R.IsCoverHollow) (hgrow : R.topGradeSup = ⊤) (hR4 : StableCappedReceiving.{w})
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    (R.stableCandidate hR.isStablyLawful).HasFiniteCutReceiving := by
  refine hasFiniteCutReceiving_of_pos hR.nonempty
    (hasLegalTypes_stableCandidate hR.hasLegalTypes)
    (isConsistent_stableCandidate hR.isConsistent hR.isCovering)
    (isCovering_stableCandidate hR.isCovering) hinst.exists_amalgam_empty
    fun x hx D hD c hc ↦ ?_
  induction c using Label.recBotCoeTop with
  | bot => exact absurd hc not_isPermittedCutoff_bot
  | top => exact absurd hc not_isPermittedCutoff_top
  | coe γ =>
    obtain ⟨u, hu, Q, hQ, hS, hl⟩ :=
      hR4.receive R hξ hR hnh hgrow x hx D hD γ (isPermittedCutoff_coe.mp hc)
    exact ⟨u, hu, Q, mem_receivingFamily_of_capped hS hl, hQ⟩

/-- **Output 3, conditionally**: the stable candidate of a model at `λ_ξ`, `ξ < ω₁`, that is not
cover-hollow and has top-grade supremum `⊤` is a model at `λ_{ξ+1}`, conditional on (R4) (`hR4`)
and the coface instances at `λ_{ξ+1}` (`hinst`), both still to be proved.  The model is stably
lawful (`IsModel.isStablyLawful`); non-hollowness and unbounded growth enter only through (R4). -/
theorem isModel_stableCandidate (hξ : ξ < ω₁) (hR : R.IsModel) (hnh : ¬ R.IsCoverHollow)
    (hgrow : R.topGradeSup = ⊤) (hR4 : StableCappedReceiving.{w})
    (hinst : StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    (R.stableCandidate hR.isStablyLawful).IsModel :=
  isModel_stableCandidate_of_hasFiniteCutReceiving hR hinst
    (hasFiniteCutReceiving_stableCandidate hξ hR hnh hgrow hR4 hinst)

end Realization

/-! ### The continuation criterion -/

/-- **The continuation criterion from stable capped receiving**, conditional on (R4) (`hR4`) and the
coface instances at every `λ_{ξ+1}` with `ξ < ω₁` (`hinst`; from the coatom extension property with
apex there, which is compiled), the first still to be proved: the model expansion is the stable
candidate, which is defined because every model is stably lawful. -/
theorem ContinuationCriterion.of_stableCappedReceiving (hR4 : StableCappedReceiving.{w})
    (hinst : ∀ ξ < ω₁, StageType.HasNonemptyCofaceInstances.{0} (blockStage (ξ + 1))) :
    ContinuationCriterion.{w} :=
  ⟨fun _ _ _ hξ hR hnh hgrow ↦
    ⟨_, Realization.isModel_stableCandidate hξ hR hnh hgrow hR4 (hinst _ hξ),
      Realization.stableCandidate_reduce⟩⟩

end VaughtConjecture
