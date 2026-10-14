/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelMirror
import VaughtConjecture.MainTheorem.CodedLevelGrades

/-!
# The faces of the coded levels

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.ReplicatedLevelMirror` about the levels over the
padded grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of `VaughtConjecture.MainTheorem.ReplicatedLevelMirror`,
with the facts of the padded base replaced by those of the coded base
(`VaughtConjecture.Extension.CodedLadderBase`, `VaughtConjecture.Extension.CodedLadderLift`) and the
coded mirror lifts (`VaughtConjecture.MainTheorem.CodedMirrorLift`); the statements there that do
not mention the levels or the base are used unchanged.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B j : ℕ}
  {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop} {N : I.ALvl g H j}

variable {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **Every level has the faces of the amalgam.** -/
theorem faces_codedLvLevel : ∀ j,
    (I.codedLvLevel g H B hd Q j).S.toCellScheme.faces = I.amalgam.toCellScheme.faces
  | 0 => rfl
  | j + 1 => faces_codedLvLevel j

end Seed

end VaughtConjecture
