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
  offset at the reindexed type is the stable offset at the transported cell;
* **bounded stable labels**: stable labels at most `ω + 3` refute modelhood of
  the candidate, by high-arity dominance at `γ = ω + 3`;
* **cover-hollow realizations**: a realization whose types are top-free is
  cover-hollow, hence stably lawful, and its candidate is not a model, by uniformity at `γ = λ_ξ`;
* **twins**: without two cells labelled the formal top at one graded index, availability needs no
  hypothesis; a top-free type has none.  The failure of availability for a pointwise minimum of two
  lawful lifts with twins is the stage-type example of `VaughtConjecture.Stage.ThresholdExamples`;
  no realization-level counterexample is claimed.  Stable availability for twin types in models is
  open, with no conditional statement here; synchronizing cofaces and twin ordering, the
  hypotheses on single types examined for it, are refuted in
  `VaughtConjecture.Continuation.CandidateCounterexamples`;
* **a model expansion**: at `ξ = 0`, the reduction of an exactly consistent
  realization at `ω + ω` with legal types and finite-extension receiving is stably lawful, given
  forcing donors at `0`.

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

/-! ### Bounded stable labels -/

/-- **Bounded stable labels refute modelhood**: at `ξ = 0`, if every stable label is at most
`ω + 3`, the candidate is not a model (high-arity dominance at `γ = ω + 3` fails). -/
example {R : Realization.{u, v} (blockStage 0) M} (hlaw : R.IsStablyLawful)
    (hK : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} (blockStage 0) n), R.eval u = some t →
      ∀ d, t.label d = ⊤ →
        R.stableLabel (blockStage (0 + 1)) (isSuccPrelimit_blockStage 0) u t d ≤
          ((ω + (3 : ℕ) : Ordinal.{u}) : Label.{u})) :
    ¬ (R.stableCandidate hlaw).IsModel :=
  not_isModel_stableCandidate_of_stableLabel_le (K := 3) (by simpa only [blockStage_zero] using hK)
    hlaw

/-! ### Cover-hollow realizations -/

/-- **A top-free realization**: it is cover-hollow, so stably lawful with no hypothesis, and its
candidate is not a model, since no label of the candidate lies in `[λ_ξ, λ_ξ + ω)`. -/
example {R : Realization.{u, v} (blockStage ξ) M} (h : ∀ x : R.Occurrence, x.type.IsTopFree) :
    ∃ hlaw : R.IsStablyLawful, ¬ (R.stableCandidate hlaw).IsModel :=
  ⟨isStablyLawful_of_isCoverHollow (isCoverHollow_of_isTopFree h),
    not_isModel_stableCandidate_of_isCoverHollow (isCoverHollow_of_isTopFree h) _⟩

/-- In a cover-hollow realization the candidate evaluates every tuple to its type in `R`, read at
`λ_{ξ+1}`. -/
example {R : Realization.{u, v} (blockStage ξ) M} (hh : R.IsCoverHollow) (u : Fin k ↪ M) :
    (R.stableCandidate (isStablyLawful_of_isCoverHollow hh)).eval u =
      (R.eval u).map (castLE · (blockStage_lt_blockStage_add_one ξ).le) :=
  stableCandidate_eval_of_isCoverHollow hh _ u

/-! ### Twins -/

/-- **No twins in a top-free type**: the cells labelled the formal top (there are none) have
distinct graded indices, so availability of the stable section needs no hypothesis there. -/
example {t : StageType.{u} (blockStage ξ) k} (ht : t.IsTopFree) :
    Set.InjOn t.toCellScheme.gradedIndex {d | t.label d = ⊤} :=
  fun d hd ↦ absurd hd (ht d)

/-- **Stable lawfulness without twins**: an exactly consistent covering realization whose types
have no two cells labelled the formal top at one graded index is stably lawful; no model is
used. -/
example {R : Realization.{u, v} (blockStage ξ) M} (hR : R.IsConsistent) (hc : R.IsCovering)
    (hinj : ∀ ⦃n : ℕ⦄ (u : Fin n ↪ M) (t : StageType.{u} (blockStage ξ) n), R.eval u = some t →
      Set.InjOn t.toCellScheme.gradedIndex {d | t.label d = ⊤}) :
    R.IsStablyLawful :=
  isStablyLawful_of_injOn_gradedIndex hR hc hinj

/-! ### A model expansion -/

/-- **A model expansion at `ξ = 0`**: given forcing donors at `0`, the reduction to `ω` of an
exactly consistent realization at `ω + ω` with legal types and finite-extension receiving is stably
lawful. -/
example (hF : ForcingDonors.{u} 0) {R' : Realization.{u, v} (blockStage (0 + 1)) M}
    (hR' : R'.IsConsistent) (hl' : R'.HasLegalTypes) (hrec' : R'.HasFiniteExtensionReceiving) :
    (R'.reduce (isSuccPrelimit_blockStage 0)).IsStablyLawful :=
  isStablyLawful_of_reduce_eq hF hR' hl' hrec' rfl

end VaughtConjecture.Continuation.CandidateExamples
