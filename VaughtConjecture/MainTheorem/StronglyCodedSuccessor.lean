/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.StronglyCodedCalibratedContexts

/-!
# The successor in the strongly coded receiving class, and strongly coded terminality

Roadmap, Layer 4 (output 3 of higher-stage reconstruction, and the terminal classification: hollow
unbounded growth) and Correspondence, item 1 (the strongly coded legal stage types).

**The class.**  A realization `R` at a stage `α` is in the **strongly coded receiving class**
(`Realization.IsStronglyCodedReceiving`) when it is exactly consistent, covering, with legal types,
with strongly coded types (the rows of every actual type are strongly coded) and with finite-cut
receiving for the cofaces with strongly coded rows
(`Realization.HasFiniteCutReceivingIn`).  The class is stated at every stage; it is used at the
block stages `λ_ξ` and `λ_{ξ+1}`.  It is not the class of models: saturation, the bottom pattern,
uniformity and dominance are not among its clauses, and receiving is required only for strongly
coded cofaces.

**The successor.**  For `R` in the class at `λ_ξ`, stable lawfulness holds
(`Realization.isStablyLawful_of_hasLegalTypes`), so the stable candidate
`R.stableCandidate hR.isStablyLawful` at `λ_{ξ+1}` is defined, and it reduces literally to `R`
(`Realization.stableCandidate_reduce`: `(R.stableCandidate _).reduce
(isSuccPrelimit_blockStage ξ) = R`, the reduction of `Realization.IsTerminalAt`).

* `Realization.StronglyCodedSuccessorTarget ξ M`: for `R` in the class at `λ_ξ`, not cover-hollow
  and with top-grade supremum `⊤`, the stable candidate is in the class at `λ_{ξ+1}` and reduces
  literally to `R`.
* `Realization.StronglyCodedEmptyRootTarget ξ M`: the clause of strongly coded finite-cut receiving
  of the candidate over the occurrences on no points.  (R4) concerns positive roots only; over the
  empty root, a one-point donor is combined with the type of an occurrence of positive arity by
  the strongly coded amalgam over the empty face.  This needs a point of the carrier.

**Terminality in the class.**  `Realization.IsStronglyCodedTerminalAt ξ R`: `R` is in the class at
`λ_ξ` and no realization in the class at `λ_{ξ+1}` reduces literally to `R`.  This is not
`Realization.IsTerminalAt` (which quantifies over models at `λ_{ξ+1}`), nor
`Realization.IsReceivingTerminalAt` (which quantifies over receiving models at `λ_{ξ+1}`).

* `Realization.StronglyCodedTerminalHollowTarget ξ M`: a realization terminal in the class at `ξ`
  with top-grade supremum `⊤` is cover-hollow.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture

open Finset Label StageType

namespace Realization

/-! ### The strongly coded receiving class -/

variable {α : Ordinal.{u}} {M : Type v}

/-- A realization is in the **strongly coded receiving class** when it is exactly consistent,
covering, with legal types, with strongly coded types and with finite-cut receiving for the
cofaces with strongly coded rows. -/
structure IsStronglyCodedReceiving (R : Realization.{u, v} α M) : Prop where
  /-- Exact consistency. -/
  isConsistent : R.IsConsistent
  /-- Covering. -/
  isCovering : R.IsCovering
  /-- Legal types. -/
  hasLegalTypes : R.HasLegalTypes
  /-- Strongly coded types: the rows of every actual type are strongly coded. -/
  isStronglyCoded : ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n), R.eval t = some p →
    p.rows.IsStronglyCoded
  /-- Finite-cut receiving for the cofaces with strongly coded rows. -/
  receiving : R.HasFiniteCutReceivingIn fun t ↦ t.rows.IsStronglyCoded

/-- A realization in the strongly coded receiving class at a block stage is stably lawful
(`Realization.isStablyLawful_of_hasLegalTypes`). -/
theorem IsStronglyCodedReceiving.isStablyLawful {ξ : Ordinal.{u}}
    {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsStronglyCodedReceiving) :
    R.IsStablyLawful :=
  isStablyLawful_of_hasLegalTypes hR.isConsistent hR.isCovering hR.hasLegalTypes

/-- A realization at `λ_ξ` is **terminal in the strongly coded receiving class at `ξ`** when it is
in the class and no realization in the class at `λ_{ξ+1}` on the same carrier has it as its stage
reduction to `λ_ξ`. -/
def IsStronglyCodedTerminalAt (ξ : Ordinal.{u}) (R : Realization.{u, v} (blockStage ξ) M) :
    Prop :=
  R.IsStronglyCodedReceiving ∧ ¬ ∃ R' : Realization.{u, v} (blockStage (ξ + 1)) M,
    R'.IsStronglyCodedReceiving ∧ R'.reduce (isSuccPrelimit_blockStage ξ) = R

/-! ### Targets -/

variable (ξ : Ordinal.{u}) (M)

/-- **Target: the successor in the strongly coded receiving class**.  For `R` in the class at
`λ_ξ`, not cover-hollow and with top-grade supremum `⊤`, the stable candidate
`R.stableCandidate hR.isStablyLawful` is in the class at `λ_{ξ+1}`, and its stage reduction to
`λ_ξ` is `R` literally. -/
def StronglyCodedSuccessorTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsStronglyCodedReceiving),
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      (R.stableCandidate hR.isStablyLawful).IsStronglyCodedReceiving ∧
        (R.stableCandidate hR.isStablyLawful).reduce (isSuccPrelimit_blockStage ξ) = R

/-- **Target: strongly coded receiving of the successor over the empty root**.  For `R` in the
class at `λ_ξ`, not cover-hollow and with top-grade supremum `⊤`, over every occurrence of the
stable candidate on no points, every coface of its type with strongly coded rows (a strongly coded
legal stage type on one point) and every permitted cutoff at `λ_{ξ+1}`, the candidate receives
the coface. -/
def StronglyCodedEmptyRootTarget : Prop :=
  ∀ (R : Realization.{u, v} (blockStage ξ) M) (hR : R.IsStronglyCodedReceiving),
    ¬ R.IsCoverHollow → R.topGradeSup = ⊤ →
      ∀ x : (R.stableCandidate hR.isStablyLawful).Occurrence, x.arity = 0 →
        ∀ D ∈ x.type.cofaces, D.rows.IsStronglyCoded → ∀ c : Label.{u},
          IsPermittedCutoff (blockStage (ξ + 1)) c →
            (R.stableCandidate hR.isStablyLawful).RealizesOver x.tuple (receivingFamily D c)

/-- **Target: terminality in the strongly coded receiving class with unbounded growth is
hollowness**.  A realization at `λ_ξ` terminal in the class at `ξ` with top-grade supremum `⊤` is
cover-hollow. -/
def StronglyCodedTerminalHollowTarget : Prop :=
  ∀ R : Realization.{u, v} (blockStage ξ) M, R.IsStronglyCodedTerminalAt ξ →
    R.topGradeSup = ⊤ → R.IsCoverHollow

end Realization

end VaughtConjecture
