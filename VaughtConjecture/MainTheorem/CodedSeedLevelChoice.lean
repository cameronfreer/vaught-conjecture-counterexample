/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SeedLevelChoice
import VaughtConjecture.MainTheorem.CodedLevelChain
import VaughtConjecture.MainTheorem.CodedLevelFaces

/-!
# The coded levels at the seed choice

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.SeedLevelChoice` about the levels over the padded
grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of `VaughtConjecture.MainTheorem.SeedLevelChoice`, with
the facts of the padded base replaced by those of the coded base
(`VaughtConjecture.Extension.CodedLadderBase`, `VaughtConjecture.Extension.CodedLadderLift`) and the
coded mirror lifts (`VaughtConjecture.MainTheorem.CodedMirrorLift`); the statements there that do
not mention the levels or the base are used unchanged.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-! ### The block bound -/

variable {I g}

/-! ### Lifts below a level pass to the higher levels -/

/-- **A lift into a pair of grade at most `i + 1` is the same in every level from the grade
`i + 1` on**: the next levels add cells at the grade above only. -/
theorem codedLvLevel_cappedLift_iff_of_le {H B : ℕ} {d : StageType.{u} α (n + 1)}
    {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
    {Q : GrowthRequests I.left d.toScheme} {i : ℕ} {X : Finset (Fin (m + 2)) × ℕ} {k : ℕ}
    (hki : k ≤ i + 1) (h : X ≤ ((univ : Finset (Fin (m + 2))), k)) :
    ∀ J, i ≤ J → ((I.codedLvLevel g H B hd Q J).S.rows.CappedLift h ↔
      (I.codedLvLevel g H B hd Q i).S.rows.CappedLift h)
  | J, hJ => by
    induction J, hJ using Nat.le_induction with
    | base => exact Iff.rfl
    | succ J hiJ ih =>
      exact (ALvl.cappedLift_nS_iff (B := B) (I.codedLvLevel g H B hd Q J)
        (I.lvCat g B hd Q (J + 2)) h fun h' ↦ absurd h'.2 (by simp only; omega)).trans ih

end Seed

namespace StageType

end StageType

end VaughtConjecture
