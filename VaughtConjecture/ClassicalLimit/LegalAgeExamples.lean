/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.ClassicalLimit.LegalAge

/-!
# Examples for the age of legal charts

Special cases of `VaughtConjecture.ClassicalLimit.LegalAge`:

* the one-point top-free chart belongs to the age of legal charts, by the inclusion of the age of
  top-free charts (`topFreeAge_subset_legalAge`);
* the one-point chart with the bottom label belongs to the age of legal charts.

## Placement

This file belongs to the section "The intended construction: the finite age and its classical
limit" of `roadmap/README.md`.
-/

namespace VaughtConjecture.ClassicalLimit.LegalAgeExamples

/-- The one-point top-free chart belongs to the age of legal charts. -/
example {α : Ordinal.{0}} : topFreeChart α (TopFreeIndex.point α) ∈ legalAge α :=
  topFreeAge_subset_legalAge (topFreeChart_mem_topFreeAge _)

/-- The one-point chart with the bottom label belongs to the age of legal charts. -/
example {α : Ordinal.{0}} : legalChart α (LegalIndex.point α) ∈ legalAge α :=
  legalChart_mem_legalAge _

end VaughtConjecture.ClassicalLimit.LegalAgeExamples
