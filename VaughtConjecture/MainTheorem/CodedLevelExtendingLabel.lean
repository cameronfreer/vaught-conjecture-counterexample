/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelExtendingLabel
import VaughtConjecture.MainTheorem.CodedLevelFaces
import VaughtConjecture.MainTheorem.CodedLevelGrades

/-!
# The extending labelling of the replicated coded level

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.LevelExtendingLabel` about the levels over the
padded grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of `VaughtConjecture.MainTheorem.LevelExtendingLabel`,
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
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

/-! ### Rendering: the section of a good level is lawful on the whole scheme -/

/-! ### Expansion: the extending labelling -/

/-! ### The levels -/

variable {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **Every level with its copies has a lawful labelling extending the labels of the attachment**,
under the hypotheses of `Seed.hasExtendingLabelLevel`. -/
theorem hasExtendingLabelLevel_rep_coded (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hB : 2 * (I.attachment g).card ≤ B) (j : ℕ) (hj : j + 1 ≤ m + 2) :
    (codedLvLevel_good (B := B) (hd := hd) hH hcard hQ hB j hj).HasExtendingLabelRep :=
  (codedLvLevel_good hH hcard hQ hB j hj).hasExtendingLabelRep
    (attachAdmits_compressedLabel hd hpair hQ (j + 1))

end Seed

end VaughtConjecture
