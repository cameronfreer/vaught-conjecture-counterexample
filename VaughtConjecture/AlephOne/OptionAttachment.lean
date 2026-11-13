/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TopFreePinnedExtension
import VaughtConjecture.Realization.ChartChain
import VaughtConjecture.Realization.Model

/-!
# Exact one-point attachment over a countable realization

Stage 2 of the `ℵ₁` companion construction: one new point is attached to a countable realization,
keeping every old evaluation and realizing a prescribed top-free donor over a given occurrence.

**Top-free types.**  A realization has top-free types when every type it assigns is top-free
(`Realization.HasTopFreeTypes`).

**The new point.**  The carrier of the extension is `Option M`, with the old points `some a` and
the new point `none`; a tuple of old points followed by the new point is
`Realization.appendNone`.

**The statements** (all stated and open):

* compatible one-point attachments along a monotone sequence of occurrences, one finite step at a
  time (`Realization.ExistsCompatibleAttachmentsTarget`), from the top-free pinned extension
  (`StageType.exists_isTopFree_pinned_extension`); no countability;
* the attachment on `Option M` over a countable carrier `M`
  (`Realization.OptionAttachmentTarget`): an exactly consistent covering realization with legal
  top-free types on `Option M` that gives every tuple of old points its old evaluation, `none`
  included, and gives a given occurrence followed by the new point the prescribed donor.  The
  intended proof takes an exhaustive chain of occurrences through the given occurrence
  (`Realization.ExistsExhaustiveOccurrenceChainTarget`), compatible attachments along it, and the
  realization of the chain of charts `appendNone (c k).tuple`
  (`Realization.ChartChainRealizationTarget`).

Countability is of the old carrier only; the stage is any limit ordinal.  The statement is a
construction over a given realization.

## Placement

This file is Stage 2 (exact countable attachment) of the `ℵ₁` companion construction over the
density sentence; that construction is not yet recorded in `roadmap/COMPANIONS.md`.
-/

universe u v

namespace VaughtConjecture.Realization

variable {α : Ordinal.{u}} {M : Type v}

/-- A realization **has top-free types** when every type it assigns is top-free. -/
def HasTopFreeTypes (R : Realization.{u, v} α M) : Prop :=
  ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p → p.IsTopFree

/-- A tuple of old points followed by the new point: the tuple `t` of `M`, read in `Option M`,
followed by `none`. -/
def appendNone {n : ℕ} (t : Fin n ↪ M) : Fin (n + 1) ↪ Option M :=
  Fin.Embedding.snoc (t.trans Function.Embedding.some) (a := none) (by simp)

/-- **Target: compatible one-point attachments along a chain of occurrences.**  At a limit stage,
in an exactly consistent realization with legal top-free types, along a monotone sequence `c` of
occurrences, a top-free coface `d` of the type of `c 0` extends to top-free cofaces `Q k` of the
types of `c k`, with `Q 0 = d`, each the restriction of the next along the face map `g` of `c k`
in `c (k + 1)` extended by the new point (`extendByLast g`).  The face map is unique, so the
statement quantifies over every face map.  No countability.  Stated; open. -/
def ExistsCompatibleAttachmentsTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄, Order.IsSuccLimit α → ∀ (R : Realization.{u, v} α M),
    R.IsConsistent → R.HasLegalTypes → R.HasTopFreeTypes →
    ∀ (c : ℕ → R.Occurrence), Monotone c → ∀ d ∈ (c 0).type.cofaces, d.IsTopFree →
      ∃ Q : ∀ k, StageType.{u} α ((c k).arity + 1), Q 0 = d ∧
        (∀ k, Q k ∈ (c k).type.cofaces ∧ (Q k).IsTopFree) ∧
        ∀ k (g : Fin (c k).arity ↪ Fin (c (k + 1)).arity),
          g.trans (c (k + 1)).tuple = (c k).tuple →
            StageType.restrictFace (extendByLast g) (Q (k + 1)) = some (Q k)

/-- **Target: exact one-point attachment over a countable realization.**  At a limit stage `α`
(of any cardinality), let `R` be an exactly consistent covering realization with legal top-free
types on a countable carrier `M`, `x` an occurrence of `R`, and `d` a top-free coface of the type
of `x`.  Some exactly consistent covering realization `S` with legal top-free types on `Option M`
gives every tuple of old points its evaluation in `R` (`none` included) and gives the tuple of `x`
followed by the new point `none` the type `d`.  Construction over a given realization;
countability is of the old carrier only.  Stated; open. -/
def OptionAttachmentTarget : Prop :=
  ∀ ⦃α : Ordinal.{u}⦄ ⦃M : Type v⦄ [Countable M], Order.IsSuccLimit α →
    ∀ (R : Realization.{u, v} α M), R.IsConsistent → R.IsCovering → R.HasLegalTypes →
      R.HasTopFreeTypes → ∀ (x : R.Occurrence), ∀ d ∈ x.type.cofaces, d.IsTopFree →
        ∃ S : Realization.{u, v} α (Option M), S.IsConsistent ∧ S.IsCovering ∧
          S.HasLegalTypes ∧ S.HasTopFreeTypes ∧
          (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M), S.eval (t.trans Function.Embedding.some) = R.eval t) ∧
          S.eval (appendNone x.tuple) = some d

end VaughtConjecture.Realization
