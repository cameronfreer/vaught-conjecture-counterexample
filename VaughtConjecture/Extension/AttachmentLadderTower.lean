/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.BaseLadderTower
import VaughtConjecture.Extension.SeedAttachment

/-!
# The ladder tower over the attachment

Roadmap, Layer 3 ((R3) and (R4), the base of the replicated carrier).

The attachment of a donor to a context inside a seed (`Seed.attachmentType`) is ladder base data
(`Seed.attachmentBase`): no cell of full scope, well formed, consistent and coded.  The ladder
tower over it (`Scheme.LadderBaseData.ladderTower`) has all the laws of
`VaughtConjecture.Extension.BaseLadderTower`; it is complete at the full faces and at the faces of
the context and the donor, and its mixed faces carry no cell: they receive the copies of its cells
of full scope (`CellScheme.Mirror`).

## References

The amalgam is [Kni26, Definition 4.3.1].
-/

universe u

namespace VaughtConjecture

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-- **The attachment as ladder base data.** -/
noncomputable def attachmentBase : Scheme.LadderBaseData.{u} (m + 2) where
  S := (I.attachmentType g).toScheme
  noFull := I.noFullOne_attachment g
  wf := I.isWellFormed_attachment g
  cons := I.isConsistent_attachment g
  coded := I.isCoded_attachment g

@[simp] theorem attachmentBase_S : (I.attachmentBase g).S = (I.attachmentType g).toScheme := rfl

end Seed

end VaughtConjecture
