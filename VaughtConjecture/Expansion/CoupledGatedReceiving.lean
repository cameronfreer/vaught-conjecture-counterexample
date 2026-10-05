/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Expansion.Agreement
import VaughtConjecture.Realization.CoupledFiniteCutReceiving

/-!
# Receiving for models from the coupled gated pinned extension property

Roadmap, Layer 3, the table of 3.4, row (R1), in the form in which the one-sided donor transfer
of Layer 5 uses it; semantic contract, item 12.

`Expansion.FiniteCutReceiving` is the statement that every model at a countable limit stage has
the finite-cut receiving property, (R1) of the table of Layer 3.  It follows from the coupled gated
pinned extension property at every countable limit stage
(`finiteCutReceiving_of_hasCoupledGatedPinnedExtensions`, by
`Realization.IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions`), and so does
finite-extension receiving of models (`finiteExtensionReceiving_of_hasCoupledGatedPinnedExtensions`,
through `FiniteCutReceiving.finiteExtensionReceiving`).  The limit and countability of the stage
are used only to instantiate the hypothesis; the passage from finite-cut to finite-extension
receiving uses that the stage is a limit and exact consistency of models.

The coupled gated pinned extension property (`StageType.HasCoupledGatedPinnedExtensions`) is a
named hypothesis that is **open**: it is proved at one input only
(`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`), and its open point is cap lowering,
stated in its docstring.  So these statements are (R1) **conditional on it, and not a proof of
(R1)**.  They are vacuous if the hypothesis fails at some countable limit stage, and nothing here
rules out that it fails at every one.  The gated pinned extension property, of which it is the
correction, fails at every stage (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`).
With the coupled property, the theorems of `VaughtConjecture.Expansion.Agreement` that take
finite-extension receiving as a hypothesis hold under it instead
(`VaughtConjecture.Expansion.CoupledGatedReceivingExamples`).

## Placement

This file belongs to Layer 5 of `roadmap/README.md`.
-/

universe w

namespace VaughtConjecture.Expansion

open Ordinal

/-- **Finite-cut receiving for models, conditional on the coupled gated pinned extension
property** at every countable limit stage.  This is (R1) of the table of Layer 3 conditional on
that named hypothesis, which is open; it is not a proof of (R1). -/
theorem finiteCutReceiving_of_hasCoupledGatedPinnedExtensions
    (hg : ∀ ⦃α : Ordinal.{0}⦄, Order.IsSuccLimit α → α < ω₁ →
      StageType.HasCoupledGatedPinnedExtensions α) :
    FiniteCutReceiving.{w} :=
  ⟨fun hα hω _ hR ↦ hR.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions (hg hα hω)⟩

/-- **Finite-extension receiving for models, conditional on the coupled gated pinned extension
property** at every countable limit stage (`FiniteCutReceiving.finiteExtensionReceiving`); the
hypothesis is open, so this is not a proof of (R1). -/
theorem finiteExtensionReceiving_of_hasCoupledGatedPinnedExtensions
    (hg : ∀ ⦃α : Ordinal.{0}⦄, Order.IsSuccLimit α → α < ω₁ →
      StageType.HasCoupledGatedPinnedExtensions α) :
    FiniteExtensionReceiving.{w} :=
  (finiteCutReceiving_of_hasCoupledGatedPinnedExtensions hg).finiteExtensionReceiving

end VaughtConjecture.Expansion
