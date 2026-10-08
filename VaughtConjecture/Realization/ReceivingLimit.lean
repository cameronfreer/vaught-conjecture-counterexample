/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Realization.Limit
import VaughtConjecture.Realization.Receiving

/-!
# Receiving at a limit block stage

Roadmap, Layer 3 (receiving for finite extensions) and Layer 2 (reduction of models); semantic
contract, item 12 (receiving one permitted cutoff at a time).

**The class of receiving models.**  A **receiving model** (`Realization.IsReceivingModel`) is a
model with the finite-cut receiving property.  At a stage `α`, the receiving models form an
auxiliary class `𝒞_α`, in which receiving is a clause of the class and not a theorem about all
models; finite-cut receiving of every model, (R1) of the table of Layer 3, is not claimed here.

**Recovery on the same carrier** (`StageType.reduce_mem_receivingFamily_reduce_iff`,
`Realization.realizesOver_receivingFamily_reduce_iff`).  For a cutoff `c ≤ β`, a stage type `q` is
in the receiving family of `d` at `c` exactly when its reduction to `β` is in the receiving family
of the reduction of `d`: reduction keeps the scheme and does not change the observation at a cap
`c ≤ β` (`Label.min_reduce_of_le`).  So a realization realizes, over a tuple, a member of the
receiving family of `d` at `c` exactly when its stage reduction to `β` realizes a member of the
receiving family of the reduction of `d` at `c`, with the same new point: the actual type of the
received tuple is the type whose reduction was received.  No clause of a model is used.

**The receiving-limit lemma** (`Realization.hasFiniteCutReceiving_of_forall_reduce_blockStage`).
Let `η` be a limit and `R` a realization at the block stage `λ_η`.  If the stage reduction of `R`
to every earlier block stage `λ_ξ`, `ξ < η`, has the finite-cut receiving property, then so does
`R`.  Given an occurrence `x`, a coface `d` of its type, and a permitted cutoff `c < λ_η`: some
earlier block stage `λ_ξ` lies above `c` (`Label.exists_lt_blockStage_of_lt`), and `ξ` depends on
`c` only; the reduction of `d` is a coface of the reduction of the type of `x`
(`StageType.reduce_mem_cofaces`), and `c` is a permitted cutoff at `λ_ξ`; receiving in the
reduction gives a new point, and recovery on the same carrier gives the requested agreement of the
actual type below `c`.  The general form (`Realization.HasFiniteCutReceiving.of_forall_reduce`)
asks, for each permitted cutoff, for one stage `β` that is zero or a limit, above the cutoff, at
which the reduction receives.

*Which earlier reductions.*  Stage reduction is defined only to stages that are zero or a limit,
and the nonzero ones are exactly the block stages (`exists_blockStage_eq_of_isSuccLimit`); at
stage `0` there is no permitted cutoff.  So "every earlier block stage" and "every earlier stage
that is zero or a limit" are the same hypothesis, and the block-stage form is the one the limit
step of a recursion over block stages meets.  At a successor index `η + 1` the lemma has no
analogue: a cutoff `λ_η + k` lies below no block stage below `λ_{η+1}`, so receiving at those
cutoffs is not inherited from any reduction; it belongs to the continuation step.

*No consistency, covering or modelhood* is used by the receiving-limit lemma: the recovery of
the actual occurrence is by the definition of the stage reduction of a realization.

**Converse and characterization**
(`Realization.hasFiniteCutReceiving_iff_forall_reduce_blockStage`).  Conversely receiving
descends to the earlier block stages (`HasFiniteCutReceiving.reduce`), so at a limit block stage
receiving is exactly receiving of every earlier reduction, and likewise for receiving models
(`Realization.isReceivingModel_iff_forall_reduce`).  The glued realization of a coherent family
of receiving models is a receiving model (`Realization.IsReceivingModel.glue`).

**Status.**  The receiving-limit lemma, its converse, and the limit step for receiving models are
proved here.  Receiving at a successor block stage is not inherited from reductions; the
continuation of a receiving model, which must conclude receiving as well as modelhood, is stated
in `VaughtConjecture.Expansion.ReceivingModels` (`Expansion.ReceivingContinuationCriterion`).
Existence of receiving models is not treated.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Label

/-! ### Recovery of the receiving family along stage reduction -/

namespace StageType

variable {β : Ordinal.{u}} {α : Ordinal.{u}} {n : ℕ}

/-- **Receiving families and stage reduction**: for a cutoff `c ≤ β`, the reduction of `q` to `β`
is in the receiving family of the reduction of `d` at `c` exactly when `q` is in the receiving
family of `d` at `c`.  Reduction keeps the scheme and the observation at a cap at most `β`. -/
theorem reduce_mem_receivingFamily_reduce_iff (hβ : Order.IsSuccPrelimit β)
    {d q : StageType.{u} α n} {c : Label.{u}} (hc : c ≤ β) :
    q.reduce hβ ∈ receivingFamily (d.reduce hβ) c ↔ q ∈ receivingFamily d c := by
  refine and_congr Iff.rfl (forall_congr' fun i ↦ forall_congr' fun j ↦ forall_congr' fun _ ↦ ?_)
  -- the labels of a reduction are the reduced labels (`StageType.reduce_label`)
  change min (Label.reduce β (q.label i)) c = min (Label.reduce β (d.label j)) c ↔ _
  exact min_reduce_eq_min_reduce_iff hc

end StageType

namespace Realization

variable {α β : Ordinal.{u}} {M : Type v} {n : ℕ}

/-- **Receiving recovers on the same carrier**: for a cutoff `c ≤ β`, the stage reduction of `R`
to `β` realizes over `t` a member of the receiving family of the reduction of `d` at `c` exactly
when `R` realizes over `t` a member of the receiving family of `d` at `c`.  The new point is the
same; its actual type is the type whose reduction is received. -/
theorem realizesOver_receivingFamily_reduce_iff {R : Realization.{u, v} α M}
    (hβ : Order.IsSuccPrelimit β) {t : Fin n ↪ M} {d : StageType.{u} α (n + 1)}
    {c : Label.{u}} (hc : c ≤ β) :
    (R.reduce hβ).RealizesOver t (StageType.receivingFamily (d.reduce hβ) c) ↔
      R.RealizesOver t (StageType.receivingFamily d c) :=
  ⟨fun h ↦ h.of_reduce hβ fun _ hq ↦ (StageType.reduce_mem_receivingFamily_reduce_iff hβ hc).mp hq,
    fun h ↦ h.reduce hβ fun _ hq ↦ (StageType.reduce_mem_receivingFamily_reduce_iff hβ hc).mpr hq⟩

/-- **Receiving from reductions above each cutoff**: if, for every permitted cutoff `c` at `α`,
some stage `β` that is zero or a limit and above `c` has a stage reduction of `R` with the
finite-cut receiving property, then `R` has it.  The donor and the occurrence are reduced to the
stage chosen for the cutoff, received there at `c`, and recovered on the same carrier
(`realizesOver_receivingFamily_reduce_iff`). -/
theorem HasFiniteCutReceiving.of_forall_reduce {R : Realization.{u, v} α M}
    (h : ∀ c : Label.{u}, IsPermittedCutoff α c → ∃ (β : Ordinal.{u})
      (hβ : Order.IsSuccPrelimit β), c < β ∧ (R.reduce hβ).HasFiniteCutReceiving) :
    R.HasFiniteCutReceiving := by
  intro x d hd c hc
  obtain ⟨β, hβ, hcβ, hrec⟩ := h c hc
  exact (realizesOver_receivingFamily_reduce_iff hβ hcβ.le).mp
    (hrec (x.reduce hβ) (d.reduce hβ) (StageType.reduce_mem_cofaces hβ hd) c ⟨hc.1, hcβ⟩)

/-! ### The receiving-limit lemma -/

variable {η : Ordinal.{u}}

/-- **The receiving-limit lemma**: at a limit block stage `λ_η`, a realization whose stage
reduction to every earlier block stage `λ_ξ`, `ξ < η`, has the finite-cut receiving property has
it.  For a permitted cutoff `c < λ_η`, the earlier block stage is any `λ_ξ > c`
(`Label.exists_lt_blockStage_of_lt`); it depends on `c` only.  No clause of a model is used. -/
theorem hasFiniteCutReceiving_of_forall_reduce_blockStage (hη : Order.IsSuccLimit η)
    {R : Realization.{u, v} (blockStage η) M}
    (h : ∀ ξ < η, (R.reduce (isSuccPrelimit_blockStage ξ)).HasFiniteCutReceiving) :
    R.HasFiniteCutReceiving :=
  HasFiniteCutReceiving.of_forall_reduce fun _ hc ↦
    let ⟨ξ, hξ, hcξ⟩ := Label.exists_lt_blockStage_of_lt hη hc.2
    ⟨_, isSuccPrelimit_blockStage ξ, hcξ, h ξ hξ⟩

/-- **Receiving at a limit block stage is receiving of the earlier reductions**: a realization at
`λ_η`, for a limit `η`, has the finite-cut receiving property exactly when its stage reduction to
every earlier block stage has it.  The forward direction is the descent of receiving
(`HasFiniteCutReceiving.reduce`). -/
theorem hasFiniteCutReceiving_iff_forall_reduce_blockStage (hη : Order.IsSuccLimit η)
    {R : Realization.{u, v} (blockStage η) M} :
    R.HasFiniteCutReceiving ↔
      ∀ ξ < η, (R.reduce (isSuccPrelimit_blockStage ξ)).HasFiniteCutReceiving :=
  ⟨fun h _ hξ ↦ h.reduce (isSuccPrelimit_blockStage η) _ (blockStage_strictMono hξ).le,
    hasFiniteCutReceiving_of_forall_reduce_blockStage hη⟩

/-! ### Receiving models -/

variable (R : Realization.{u, v} α M) in
/-- A **receiving model**: a model with the finite-cut receiving property.  The receiving models
at a stage form the auxiliary class `𝒞_α`. -/
def IsReceivingModel : Prop :=
  R.IsModel ∧ R.HasFiniteCutReceiving

/-- **Stage reduction of a receiving model**: the reduction of a receiving model at a stage that
is zero or a limit to a smaller limit stage is a receiving model (`IsModel.reduce`,
`HasFiniteCutReceiving.reduce`). -/
theorem IsReceivingModel.reduce {R : Realization.{u, v} α M} (hR : R.IsReceivingModel)
    (hα : Order.IsSuccPrelimit α) (hβ : Order.IsSuccLimit β) (hβα : β ≤ α) :
    (R.reduce hβ.isSuccPrelimit).IsReceivingModel :=
  ⟨hR.1.reduce hα hβ hβα, hR.2.reduce hα hβ.isSuccPrelimit hβα⟩

/-- **Receiving models at a limit block stage**: a realization at `λ_η`, for a limit `η`, is a
receiving model exactly when its stage reduction to every earlier block stage is. -/
theorem isReceivingModel_iff_forall_reduce (hη : Order.IsSuccLimit η)
    {R : Realization.{u, v} (blockStage η) M} :
    R.IsReceivingModel ↔
      ∀ ξ < η, (R.reduce (isSuccPrelimit_blockStage ξ)).IsReceivingModel := by
  rw [IsReceivingModel, isModel_iff_forall_reduce hη,
    hasFiniteCutReceiving_iff_forall_reduce_blockStage hη]
  exact ⟨fun h ξ hξ ↦ ⟨h.1 ξ hξ, h.2 ξ hξ⟩, fun h ↦ ⟨fun ξ hξ ↦ (h ξ hξ).1, fun ξ hξ ↦ (h ξ hξ).2⟩⟩

/-- **Gluing a coherent family of receiving models**: the glued realization of a coherent family
of receiving models below a limit `η` is a receiving model.  Its stage reductions are the members
of the family (`IsCoherentFamily.glue_reduce`). -/
theorem IsReceivingModel.glue {R : ∀ ξ < η, Realization.{u, v} (blockStage ξ) M}
    {hη : Order.IsSuccLimit η} (hc : IsCoherentFamily R)
    (hR : ∀ ξ (hξ : ξ < η), (R ξ hξ).IsReceivingModel) : (glue R hη).IsReceivingModel :=
  (isReceivingModel_iff_forall_reduce hη).mpr fun ξ hξ ↦ hc.glue_reduce hξ ▸ hR ξ hξ

end Realization

end VaughtConjecture
