/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Density.ReceivingIn
import VaughtConjecture.Correspondence.Presentation.CoherentRenaming

/-!
# Targets of the presentation checkpoint

Numbering as in the current draft of [AFK26].  Write `λ_β = blockStage β = ω + ω · β`.  This file
states four targets as propositions, every premise visible; none is proved here, and no implication
among them is compiled.  Native construction throughout.

**Strongly coded presentations.**  A realization `R` at `λ_β` is used below with four properties,
always written out:

* `R.IsConsistent` (exact consistency) and `R.IsCovering`;
* strongly coded legal types: `∀ ⦃n⦄ (t : Fin n ↪ M) p, R.eval t = some p → p.IsStronglyCodedLegal`;
* `R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded)`: finite-extension receiving
  for the legal donors with strongly coded rows.

The four targets:

* **B.T7, presentation** (`PresentationTarget β M`): for `β < ω₁`, a countable nonempty carrier,
  every well-formed class realization at `λ_β` with donor density is the class reading of a
  realization with the four properties.
* **B.T8, alignment** (`AlignmentTarget β M`): for `β < ω₁` and a countable carrier, two
  realizations at `λ_β` with the four properties and the same class reading are related by a
  coherent renaming (`Realization.CoherentRenaming`), not only tuple by tuple
  (`Realization.IsCellRenamingOf`).
* **Reduction alignment** (`ReductionAlignmentTarget β ξ M`): for `ξ ≤ β < ω₁` and a countable
  carrier, if two realizations at `λ_β` with the four properties have reductions to `λ_ξ` with the
  same class reading, the **reductions** are related by a coherent renaming.  Nothing is concluded
  about the realizations at `λ_β`.
* **Lifting** (`LiftingTarget η M`): under the premises of the restricted next-block
  determination `Realization.eq_stableCandidate_stronglyCoded` (for both realizations at
  `λ_{η+1}`: types with strongly coded rows, exact consistency, covering, legal types, and
  finite-extension receiving for the strongly coded legal donors), every coherent renaming of the
  reductions to `λ_η` lifts, with the same bijections, to a coherent renaming of the realizations
  at `λ_{η+1}`.

**What is not assumed.**  No target infers equality of class readings at a higher stage from
equality of class readings of reductions: that inference is Reconstruction [AFK26,
Proposition 4.34], a later step.  The lifting target takes a coherent renaming of the reductions as
its hypothesis, and its conclusion (a coherent renaming at `λ_{η+1}`) gives equal class readings
at `λ_{η+1}` only through `Realization.classReading_eq_of_coherentRenaming`.  The lifting target is
a successor step; limit stages are not covered by it.
-/

universe u v

namespace VaughtConjecture

open Ordinal

/-- **Target B.T7, presentation** (native construction): for `β < ω₁` and a countable nonempty
carrier `M`, every well-formed class realization `S` at `λ_β = ω + ω · β` with donor density is the
class reading of a realization `R` at `λ_β` that is exactly consistent, covering, with strongly
coded legal types, and with finite-extension receiving for the strongly coded legal donors. -/
def PresentationTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → Countable M → Nonempty M →
    ∀ S : ClassRealization.{u, v} (blockStage β) M, S.IsWellFormed → S.HasDonorDensity →
      ∃ R : Realization.{u, v} (blockStage β) M, R.IsConsistent ∧ R.IsCovering ∧
        (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage β) n), R.eval t = some p →
          p.IsStronglyCodedLegal) ∧
        R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) ∧ R.classReading = S

/-- **Target B.T8, alignment** (native construction): for `β < ω₁` and a countable carrier `M`, two
realizations `R`, `R'` at `λ_β`, each exactly consistent, covering, with strongly coded legal types,
and with finite-extension receiving for the strongly coded legal donors, with the same class
reading, are related by a coherent renaming: bijections of cells at every typed tuple preserving
labels, scopes, grades and rows and commuting with every face cell map. -/
def AlignmentTarget (β : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → Countable M → ∀ R R' : Realization.{u, v} (blockStage β) M,
    R.IsConsistent → R.IsCovering →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage β) n), R.eval t = some p →
      p.IsStronglyCodedLegal) →
    R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    R'.IsConsistent → R'.IsCovering →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage β) n), R'.eval t = some p →
      p.IsStronglyCodedLegal) →
    R'.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    R.classReading = R'.classReading → Nonempty (Realization.CoherentRenaming R R')

/-- **Target: reduction alignment** (native construction): for `ξ ≤ β < ω₁` and a countable
carrier `M`, if two realizations `R`, `R'` at `λ_β`, each exactly consistent, covering, with
strongly coded legal types, and with finite-extension receiving for the strongly coded legal
donors, have reductions to `λ_ξ` with the same class reading, then the **reductions** are related
by a coherent renaming.  The conclusion is about the reductions only: equality of the class
readings of `R` and `R'` at `λ_β` is neither assumed nor concluded (that would be Reconstruction,
[AFK26, Proposition 4.34], a later step). -/
def ReductionAlignmentTarget (β ξ : Ordinal.{u}) (M : Type v) : Prop :=
  β < ω₁ → ξ ≤ β → Countable M → ∀ R R' : Realization.{u, v} (blockStage β) M,
    R.IsConsistent → R.IsCovering →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage β) n), R.eval t = some p →
      p.IsStronglyCodedLegal) →
    R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    R'.IsConsistent → R'.IsCovering →
    (∀ ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} (blockStage β) n), R'.eval t = some p →
      p.IsStronglyCodedLegal) →
    R'.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    (R.reduce (isSuccPrelimit_blockStage ξ)).classReading =
      (R'.reduce (isSuccPrelimit_blockStage ξ)).classReading →
    Nonempty (Realization.CoherentRenaming (R.reduce (isSuccPrelimit_blockStage ξ))
      (R'.reduce (isSuccPrelimit_blockStage ξ)))

/-- **Target: lifting a coherent renaming through one block** (native construction): let `R`, `R'`
be realizations at `λ_{η+1}` satisfying, each, the premises of the restricted next-block
determination `Realization.eq_stableCandidate_stronglyCoded`: every occurrence has a type with
strongly coded rows, exact consistency, covering, legal types (`Realization.HasLegalTypes`), and
finite-extension receiving for the legal donors with strongly coded rows.  Then every coherent
renaming `c` of their reductions to `λ_η` lifts to a coherent renaming `c'` of `R` and `R'` with
the same bijections of cells at every typed tuple (stage reduction keeps the cells).

The hypothesis is a coherent renaming of the reductions, not equality of class readings at
`λ_{η+1}`, and equality of the class readings of `R` and `R'` is not assumed from equality of the
class readings of the reductions: that inference is Reconstruction [AFK26, Proposition 4.34], a
later step.  Successor step only; limit stages are not covered. -/
def LiftingTarget (η : Ordinal.{u}) (M : Type v) : Prop :=
  ∀ R R' : Realization.{u, v} (blockStage (η + 1)) M,
    (∀ x : R.Occurrence, x.type.rows.IsStronglyCoded) → R.IsConsistent → R.IsCovering →
    R.HasLegalTypes → R.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    (∀ x : R'.Occurrence, x.type.rows.IsStronglyCoded) → R'.IsConsistent → R'.IsCovering →
    R'.HasLegalTypes → R'.HasFiniteExtensionReceivingIn (fun t ↦ t.rows.IsStronglyCoded) →
    ∀ c : Realization.CoherentRenaming (R.reduce (isSuccPrelimit_blockStage η))
      (R'.reduce (isSuccPrelimit_blockStage η)),
      ∃ c' : Realization.CoherentRenaming R R', ∀ ⦃n : ℕ⦄ (t : Fin n ↪ M)
        ⦃p q : StageType.{u} (blockStage (η + 1)) n⦄ (hp : R.eval t = some p)
        (hq : R'.eval t = some q),
        c'.cellEquiv t hp hq =
          c.cellEquiv t (R.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hp)
            (R'.reduce_eval_of_eval_eq_some (isSuccPrelimit_blockStage η) hq)

end VaughtConjecture
