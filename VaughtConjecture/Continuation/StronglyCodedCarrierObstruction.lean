/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Label.FieldLadder
import VaughtConjecture.Realization.GrowthCarrier

/-!
# A carrier with a second ladder rung is not strongly coded

Roadmap, Layer 3 ((R3) and (R4), the growth carrier) and Correspondence, item 1 (the strongly
coded legal stage types).  All results here are native constructions of this repository.

The ladder clauses of the carrier contract (`StageType.HasLadderGrowthCarriers`,
`StageType.HasLadderGrowthCarriersStable`, `StageType.HasLadderGrowthCarriersStableAtSeed`) ask
for rungs `r a i`, `i < H`, of graded index `(univ, 1)` whose diagonal is
`Label.ladderSource (i + 1) (i + 1)`.  For `i ≥ 1` that diagonal is `ω · i + 3`
(`Label.ladderSource`), of finite part `3`, while strong coding at the grade one allows finite
part at most `2` (`Label.isStronglyCoded_coe_omega0_mul_add`).  So the rung `i = 1` (the
**second rung**, present exactly when the ladder has a member `a` and height `H ≥ 2`) is a cell
whose row is not strongly coded at its grade.

* `Label.not_isStronglyCoded_ladderSource_diag`: the diagonal `ladderSource (i + 1) (i + 1)`,
  `i ≥ 1`, is not strongly coded at any grade at most one.
* `Scheme.not_isStronglyCoded_of_rowAt_ladderSource_diag`: a scheme with a cell of grade at most
  one reading such a diagonal at itself is not strongly coded.
* `Scheme.not_isStronglyCoded_of_secondRung`, `GrowthCarrier.not_isStronglyCoded_of_secondRung`,
  `StageType.not_isStronglyCoded_of_secondRung`: a scheme, a growth carrier, and every stage type
  on the scheme of a growth carrier satisfying the rung and diagonal clauses of the ladder contract
  with the second rung present (a member `a` and `1 < H`) are not strongly coded.

**Scope.**  These refute strong coding of carriers containing the second rung only.  They say
nothing about carriers without it (no member, or `H = 1`), nor about carriers outside the ladder
contract, nor about the strongly coded recovery targets of
`VaughtConjecture.Continuation.StronglyCodedRecoveryTarget`.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label
open Ordinal hiding univ

namespace Label

/-- **The ladder diagonal above the first rung is not strongly coded at grade one** (native
construction): for `i ≥ 1`, `ladderSource (i + 1) (i + 1) = ω · i + 3` has finite part `3`, above
the bound `k + 1 ≤ 2` of strong coding at a grade `k ≤ 1`. -/
theorem not_isStronglyCoded_ladderSource_diag {k i : ℕ} (hk : k ≤ 1) (hi : 1 ≤ i) :
    ¬ IsStronglyCoded k (ladderSource.{u} (i + 1) (i + 1)) := by
  have h0 : ¬ min (i + 1) (i + 1) = 0 := by omega
  have h1 : 2 ≤ i + 1 ∧ i + 1 ≤ i + 1 := ⟨by omega, le_rfl⟩
  unfold ladderSource
  rw [ite_eq_right h0, ite_eq_left h1, isStronglyCoded_coe_omega0_mul_add]
  omega

/-- **The second rung's diagonal is not strongly coded at grade one**: `ladderSource 2 2 = ω + 3`
(native construction). -/
theorem not_isStronglyCoded_one_ladderSource_two :
    ¬ IsStronglyCoded 1 (ladderSource.{u} 2 2) :=
  not_isStronglyCoded_ladderSource_diag (i := 1) le_rfl le_rfl

end Label

namespace Scheme

variable {n : ℕ}

/-- **A cell reading a ladder diagonal above the first rung at itself is not strongly coded**
(native construction): if a cell `c` of grade at most one has `rowAt c c` equal to
`ladderSource (i + 1) (i + 1)` with `i ≥ 1`, the rows of the scheme are not strongly coded.  The
value is not `⊥`, so `c` lies below its own graded index and the entry is a row value of `c`. -/
theorem not_isStronglyCoded_of_rowAt_ladderSource_diag {S : Scheme.{u} n} {c : Fin S.card}
    {i : ℕ} (hc : S.toCellScheme.grade c ≤ 1) (hi : 1 ≤ i)
    (hrow : S.rowAt c c = ladderSource (i + 1) (i + 1)) : ¬ S.rows.IsStronglyCoded := by
  intro h
  have hne : S.rowAt c c ≠ ⊥ := by
    rw [hrow, Ne, ladderSource_eq_bot_iff]
    omega
  have hmem := mem_below_of_rowAt_ne_bot hne
  have hsc := h c ⟨c, hmem⟩
  rw [← rowAt_of_mem hmem, hrow] at hsc
  exact not_isStronglyCoded_ladderSource_diag hc hi hsc

/-- **A scheme with a second ladder rung is not strongly coded** (native construction).  Premises:
the rung and diagonal clauses of the ladder contract (`StageType.HasLadderGrowthCarriers`): rungs
`r a i`, `i < H`, of graded index `(univ, 1)` whose diagonal `rowAt (r a i) (r a i)` is
`ladderSource (i + 1) (i + 1)`; and **the second rung exists**: a member `a` and `1 < H`.  The rung
`r a 1` has grade one and diagonal `ladderSource 2 2 = ω + 3`.  This refutes strong coding of
schemes containing that rung only. -/
theorem not_isStronglyCoded_of_secondRung {S : Scheme.{u} n} {Mb : Type} {H : ℕ}
    (r : Mb → ℕ → Fin S.card)
    (hr : ∀ a, ∀ i < H, S.toCellScheme.gradedIndex (r a i) = (univ, 1))
    (hrd : ∀ a, ∀ i < H, S.rowAt (r a i) (r a i) = ladderSource (i + 1) (i + 1))
    (a : Mb) (hH : 1 < H) : ¬ S.rows.IsStronglyCoded :=
  not_isStronglyCoded_of_rowAt_ladderSource_diag (congrArg Prod.snd (hr a 1 hH)).le le_rfl
    (hrd a 1 hH)

end Scheme

namespace GrowthCarrier

variable {J n : ℕ} {C : Scheme.{u} J} {P : Scheme.{u} (n + 1)} {e : Fin n ↪ Fin J}

/-- **A growth carrier with a second ladder rung is not strongly coded** (native construction):
`Scheme.not_isStronglyCoded_of_secondRung` for the carrier scheme.  Premises: the rung and
diagonal clauses of the ladder contract (`StageType.HasLadderGrowthCarriers`,
`StageType.HasLadderGrowthCarriersStableAtSeed`) and **the second rung exists** (a member `a` and
`1 < H`).  It refutes strong coding of carriers containing that rung only: not of other carriers,
and not of the strongly coded recovery targets. -/
theorem not_isStronglyCoded_of_secondRung (G : GrowthCarrier C P e) {Mb : Type} {H : ℕ}
    (r : Mb → ℕ → Fin G.scheme.card)
    (hr : ∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1))
    (hrd : ∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = ladderSource (i + 1) (i + 1))
    (a : Mb) (hH : 1 < H) : ¬ G.scheme.rows.IsStronglyCoded :=
  Scheme.not_isStronglyCoded_of_secondRung r hr hrd a hH

end GrowthCarrier

namespace StageType

variable {α : Ordinal.{u}} {J n : ℕ} {C : Scheme.{u} J} {P : Scheme.{u} (n + 1)}
  {e : Fin n ↪ Fin J}

/-- **No stage type on a carrier with a second ladder rung is strongly coded** (native
construction): a stage type `q` on the scheme of a growth carrier `G` satisfying the rung and
diagonal clauses of the ladder contract, with **the second rung present** (a member `a` and
`1 < H`), has rows that are not strongly coded.  This applies to the coface `q` carrying stable
recovery on the carrier scheme (`GrowthCarrier.isStableRecoveryScheme`,
`StageType.IsStableRecoveryScheme.isCutoffStableRecovery`); it refutes strong coding of stage
types on carriers containing that rung only. -/
theorem not_isStronglyCoded_of_secondRung {q : StageType.{u} α (J + 1)}
    (G : GrowthCarrier C P e) (hq : q.toScheme = G.scheme) {Mb : Type} {H : ℕ}
    (r : Mb → ℕ → Fin G.scheme.card)
    (hr : ∀ a, ∀ i < H, G.scheme.toCellScheme.gradedIndex (r a i) = (univ, 1))
    (hrd : ∀ a, ∀ i < H, G.scheme.rowAt (r a i) (r a i) = ladderSource (i + 1) (i + 1))
    (a : Mb) (hH : 1 < H) : ¬ q.rows.IsStronglyCoded := by
  rw [hq]
  exact G.not_isStronglyCoded_of_secondRung r hr hrd a hH

end StageType

end VaughtConjecture
