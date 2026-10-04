/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Agreement
import VaughtConjecture.Realization.FiniteCutReceiving

/-!
# Receiving for models from the gated pinned extension property

Roadmap, Layer 3, the table of 3.4, row (R1), in the form in which the one-sided donor transfer
of Layer 5 uses it; semantic contract, item 12.

`Expansion.FiniteCutReceiving` is the statement that every model at a countable limit stage has
the finite-cut receiving property, (R1) of the table of Layer 3.  It follows from the gated pinned
extension property at every countable limit stage
(`finiteCutReceiving_of_hasGatedPinnedExtensions`, by
`Realization.IsModel.hasFiniteCutReceiving_of_hasGatedPinnedExtensions`), and so does
finite-extension receiving of models (`finiteExtensionReceiving_of_hasGatedPinnedExtensions`,
through `FiniteCutReceiving.finiteExtensionReceiving`).  The limit and countability of the stage
are used only to instantiate the hypothesis; the passage from finite-cut to finite-extension
receiving uses that the stage is a limit and exact consistency of models.

The gated pinned extension property (`StageType.HasGatedPinnedExtensions`) is a named hypothesis,
still to be proved, so these statements are (R1) **conditional on it**, not a proof of (R1).  With
it, the theorems of `VaughtConjecture.Expansion.Agreement` that take finite-extension receiving
as a hypothesis hold under the gated pinned extension property instead
(`VaughtConjecture.Expansion.GatedReceivingExamples`).

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.Expansion

open Ordinal

/-- **Finite-cut receiving for models, conditional on the gated pinned extension property** at
every countable limit stage.  This is (R1) of the table of Layer 3 conditional on that named
hypothesis, still to be proved; it is not a proof of (R1). -/
theorem finiteCutReceiving_of_hasGatedPinnedExtensions
    (hg : ∀ ⦃α : Ordinal.{0}⦄, Order.IsSuccLimit α → α < ω₁ →
      StageType.HasGatedPinnedExtensions α) :
    FiniteCutReceiving.{w} :=
  ⟨fun hα hω _ hR ↦ hR.hasFiniteCutReceiving_of_hasGatedPinnedExtensions (hg hα hω)⟩

/-- **Finite-extension receiving for models, conditional on the gated pinned extension
property** at every countable limit stage (`FiniteCutReceiving.finiteExtensionReceiving`). -/
theorem finiteExtensionReceiving_of_hasGatedPinnedExtensions
    (hg : ∀ ⦃α : Ordinal.{0}⦄, Order.IsSuccLimit α → α < ω₁ →
      StageType.HasGatedPinnedExtensions α) :
    FiniteExtensionReceiving.{w} :=
  (finiteCutReceiving_of_hasGatedPinnedExtensions hg).finiteExtensionReceiving

end VaughtConjecture.Expansion
