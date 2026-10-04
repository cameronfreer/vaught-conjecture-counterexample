/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.FamilyCofaces
import VaughtConjecture.MainTheorem.Assembly
import VaughtConjecture.Realization.CapToModel

/-!
# The cap-to-model theorem at `ω` from the coatom extension property with apex

Roadmap, Layer 3, 3.4 (the cap-to-model theorem); the main theorem's hypothesis `CapToModel`.

The hypothesis `CapToModel.{w}` of the main theorem (a realization at stage `ω`, on a carrier in
`Type w`, with a nonempty carrier, legal types, exact consistency, covering, and finite-cut
receiving, is a model) follows from the coatom extension property with apex at `ω`
(`CapToModel.of_hasApexCoatomExtensions`): it is the cap-to-model theorem at the nonzero limit
stage `ω` (`Realization.isModel_of_hasFiniteCutReceiving`), whose two nonemptiness hypotheses hold
at every legal type, uniformity under the plain coatom extension property
(`StageType.nonempty_cofaces_inter_uniformityFamily`) and dominance under the form with apex
(`StageType.nonempty_cofaces_inter_dominanceFamily`).  The coatom extension property with apex at
`ω` is not proved.

## Placement

This file belongs to the main theorem of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.MainTheorem

open StageType
open scoped Ordinal

/-- **The cap-to-model theorem at `ω`** from the coatom extension property with apex at `ω`, for
the realizations on the carriers of every universe `w`. -/
theorem CapToModel.of_hasApexCoatomExtensions (hext : HasApexCoatomExtensions.{0} ω) :
    CapToModel.{w} :=
  ⟨fun _ hne hl hc hcov hr ↦ Realization.isModel_of_hasFiniteCutReceiving
    Ordinal.isSuccLimit_omega0 hne hl hc hcov hr
    (fun x _ _ hγ ↦ nonempty_cofaces_inter_uniformityFamily hext.hasCoatomExtensions
      Ordinal.isSuccLimit_omega0.isSuccPrelimit (hl _ _ x.eval_tuple) hγ)
    (fun x _ hγ ↦ nonempty_cofaces_inter_dominanceFamily hext
      Ordinal.isSuccLimit_omega0.isSuccPrelimit (hl _ _ x.eval_tuple) hγ)⟩

end VaughtConjecture.MainTheorem
