/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CodedLadderLift
import VaughtConjecture.MainTheorem.LevelCarrierCoding

/-!
# The strongly coded grade-one base of the seed construction

Roadmap, Layer 3 ((R3) and (R4), the growth carrier of the levels) and Correspondence, item 1 (the
strongly coded legal stage types).  All results here are native constructions of this repository.

The base of the seed construction, the padded grade-one base over the attachment, is not strongly
coded (`Seed.not_isStronglyCoded_lvBase_seedHeightLevel`).  The coded ladder base over the same
attachment (`Scheme.LadderBaseData.codedLadderBase`), with the same cell scheme, is strongly coded
at every height when both coatom types of the seed are
(`Seed.isStronglyCoded_codedLadderBase_attachment`), and it is well formed, consistent and coded
and lifts into the full face of grade one under the premises of the padded base
(`VaughtConjecture.Extension.CodedLadderLift`).

**Scope.**  This concerns the grade-one base only, not the subsequent levels of the construction.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.Seed

variable {α : Ordinal.{u}} {m n : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)

/-- **The coded ladder base over the attachment is strongly coded** (native construction), at
every height `H`, when both coatom types of the seed are strongly coded: the attachment is
(`Seed.isStronglyCoded_attachment`), and the rows of the ladder points take strongly coded values
at grade one (`Scheme.isStronglyCoded_codedLadderBase`). -/
theorem isStronglyCoded_codedLadderBase_attachment (hl : I.left.rows.IsStronglyCoded)
    (hr : I.right.rows.IsStronglyCoded) (H : ℕ) :
    ((I.attachmentBase g).codedLadderBase H).rows.IsStronglyCoded :=
  (I.attachmentBase g).isStronglyCoded_codedLadderBase H (I.isStronglyCoded_attachment g hl hr)

end VaughtConjecture.Seed
