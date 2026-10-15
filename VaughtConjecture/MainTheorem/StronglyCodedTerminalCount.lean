/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.StronglyCodedComparison
import VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier
import VaughtConjecture.MainTheorem.StronglyCodedLowDisplay

/-!
# The terminal isomorphism theorem and the terminal count in the strongly coded class

Roadmap, Layer 4 (the terminal classification and the count of terminal isomorphism classes).

The conditional statements `Realization.stronglyCodedTerminalIsoTarget` and
`Realization.stronglyCodedTerminalCountTarget`
(`VaughtConjecture.MainTheorem.StronglyCodedComparison`) keep restricted (R2),
`Realization.StronglyCodedResidualReceiving`, and restricted (R3),
`Realization.StronglyCodedHollowReceiving`, as explicit premises.  Both are proved, for every stage
and carrier and with no premise: (R2) as `Realization.stronglyCodedResidualReceiving`
(`VaughtConjecture.MainTheorem.StronglyCodedLowDisplay`) and (R3) as
`Realization.stronglyCodedHollowReceiving`
(`VaughtConjecture.MainTheorem.StronglyCodedGrowthCarrier`).  This file instantiates them.

* `Realization.stronglyCodedTerminalIso` (proved: native construction): two realizations on
  countable carriers, terminal in the strongly coded receiving class at `ξ` and sharing a
  restricted terminal property, are isomorphic realizations.
* `Realization.stronglyCodedTerminalClasses_countable` (proved: native construction): for
  `ξ < ω₁`, only countably many isomorphism classes of realizations on `ℕ` are terminal in the
  strongly coded receiving class at `ξ`.

"Unconditional" here means that no restricted (R2) or (R3) premise remains.  The stage bound
`ξ < ω₁` of the count remains, and so does countability of the carriers in the isomorphism
theorem.  The count is the native count of isomorphism classes of strongly coded terminal
realizations on `ℕ`; it is not [AFK26, Proposition 4.35].  The connection of this terminality with
manuscript maximality, and the assembly of representatives in the full language, are separate and
not addressed here.  The conditional statements are kept unchanged.

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture

open Ordinal

namespace Realization

/-- **Shared restricted terminal properties determine the isomorphism class, unconditionally**
(proved: native construction).  Two realizations at `λ_ξ` on countable carriers, terminal in the
strongly coded receiving class at `ξ`, with a common restricted terminal property, are isomorphic
realizations.  This is `Realization.stronglyCodedTerminalIsoTarget` with restricted (R2)
(`Realization.stronglyCodedResidualReceiving`) and restricted (R3)
(`Realization.stronglyCodedHollowReceiving`) instantiated on both carriers; "unconditional" means
that no (R2) or (R3) premise remains, while countability of `M` and `N` remains a premise. -/
theorem stronglyCodedTerminalIso {ξ : Ordinal.{0}} {M N : Type w} [Countable M] [Countable N]
    {R : Realization.{0, w} (blockStage ξ) M} {S : Realization.{0, w} (blockStage ξ) N}
    (hR : R.IsStronglyCodedTerminalAt ξ) (hS : S.IsStronglyCodedTerminalAt ξ)
    {P : TerminalProperty ξ} (hRP : R.HasRestrictedTerminalProperty P)
    (hSP : S.HasRestrictedTerminalProperty P) : R.IsIso S :=
  stronglyCodedTerminalIsoTarget ξ M N (stronglyCodedResidualReceiving ξ M)
    (stronglyCodedResidualReceiving ξ N) (stronglyCodedHollowReceiving ξ M)
    (stronglyCodedHollowReceiving ξ N) inferInstance inferInstance R S hR hS P hRP hSP

/-- **Countably many strongly coded terminal isomorphism classes, unconditionally** (proved:
native construction).  For `ξ < ω₁`, only countably many isomorphism classes of realizations on
`ℕ` are terminal in the strongly coded receiving class at `ξ`.  This is
`Realization.stronglyCodedTerminalCountTarget` with restricted (R2)
(`Realization.stronglyCodedResidualReceiving ξ ℕ`) and restricted (R3)
(`Realization.stronglyCodedHollowReceiving ξ ℕ`) instantiated.  "Unconditional" means that no
(R2) or (R3) premise remains; the stage bound `ξ < ω₁` remains.  It is the native count of
isomorphism classes of strongly coded terminal realizations on `ℕ`, not
[AFK26, Proposition 4.35]: the connection with manuscript maximality and the assembly of
representatives in the full language are separate. -/
theorem stronglyCodedTerminalClasses_countable {ξ : Ordinal.{0}} (hξ : ξ < ω₁) :
    (stronglyCodedTerminalClasses ξ).Countable :=
  stronglyCodedTerminalCountTarget ξ hξ (stronglyCodedResidualReceiving ξ ℕ)
    (stronglyCodedHollowReceiving ξ ℕ)

end Realization

end VaughtConjecture
