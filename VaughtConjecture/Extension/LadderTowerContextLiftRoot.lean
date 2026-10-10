/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.GrowthRelativeLift
import VaughtConjecture.Extension.LadderTowerContextLift

/-!
# The root lift of a legal donor at a grade

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the recognizing growth carrier).

A legal donor `d` on `n + 1` points with root face `p` (`0 < n`) lifts capped from the root face
to the full face at every grade `K` with `1 ≤ K ≤ n + 1`, at every cap self-visible at `K`
(bountifulness).  **The root lift at a grade** (`StageType.IsLegal.exists_rootLift_le`): a lawful
section `ρ` of the root face vanishing above `K` and a lawful section `v` of `d` agreeing with it
capped at `γ` on the root cells of grade at most `K` give a lawful section of `d` equal to `ρ` on
the root, vanishing above `K`, with the observation of `v` at `γ` at every cell of grade at most
`K`.  At `K = n + 1` it is `StageType.IsLegal.exists_rootLift` with a cap self-visible at the
arity; here the cap need only be self-visible at `K`.

## References

Bountifulness is [Kni26, Definition 2.5.14].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ}

end StageType

end VaughtConjecture
