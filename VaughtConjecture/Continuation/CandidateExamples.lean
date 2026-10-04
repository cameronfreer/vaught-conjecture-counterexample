/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.Candidate

/-!
# Examples for the stable candidate

Special cases of `VaughtConjecture.Continuation.Candidate`:

* **the block index `ξ = 0`** (`λ_0 = ω`, `λ_1 = ω + ω`): the candidate reduces to `R`; at a cell
  labelled the formal top the stable section is the formal top or `ω + i` with `i` at least the
  grade;
* **position matching**: along a permutation `e` of the coordinates of a typed tuple, the stable
  offset at the reindexed type is the stable offset at the transported cell.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u v

namespace VaughtConjecture.Continuation.CandidateExamples

open Ordinal Realization StageType

variable {ξ : Ordinal.{u}} {M : Type v} {k : ℕ}

/-! ### The block index `ξ = 0` -/

/-- At `ξ = 0`, the reduction of the candidate at `ω + ω` to `ω` is `R`. -/
example {R : Realization.{u, v} (blockStage 0) M} (hlaw : R.IsStablyLawful) :
    (R.stableCandidate hlaw).reduce (isSuccPrelimit_blockStage 0) = R :=
  stableCandidate_reduce

/-- At `ξ = 0`, the stable section at a cell labelled the formal top is the formal top or `ω + i`
with `i` at least the grade of the cell. -/
example {R : Realization.{u, v} (blockStage 0) M} {u : Fin k ↪ M}
    {t : StageType.{u} (blockStage 0) k} (ht : R.eval u = some t) {d : Fin t.card}
    (hd : t.label d = ⊤) :
    R.stableSection u t d = ⊤ ∨ ∃ i : ℕ, t.toCellScheme.grade d ≤ i ∧
      R.stableSection u t d = ((ω + i : Ordinal.{u}) : Label.{u}) := by
  simpa only [blockStage_zero] using stableSection_eq_top_or_exists ht hd

/-! ### Position matching -/

/-- **Stable offsets along a permutation**: at the tuple reindexed along a bijection `e`, the
stable offset of a cell of the reindexed type is that of the transported cell.  The bijection need
not be monotone. -/
example {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsConsistent) (hc : R.IsCovering)
    {u : Fin k ↪ M} {t : StageType.{u} (blockStage ξ) k} (ht : R.eval u = some t)
    (e : Fin k ≃ Fin k) (i : Fin (t.reindex e).card) :
    R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) (e.toEmbedding.trans u)
        (t.reindex e) i =
      R.stableOffset (blockStage (ξ + 1)) (isSuccPrelimit_blockStage ξ) u t
        (t.cellMap e.toEmbedding i) :=
  stableOffset_comap hR hc ht e.toEmbedding _ i

end VaughtConjecture.Continuation.CandidateExamples
