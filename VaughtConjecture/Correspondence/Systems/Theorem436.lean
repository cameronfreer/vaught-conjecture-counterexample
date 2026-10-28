/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.TemplateQualifying
import VaughtConjecture.Correspondence.Systems.Spectrum

/-!
# [AFK26, Theorem 4.36] by the abstract route

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  The printed
proof of [AFK26, Theorem 4.36]: `K[L]` is a qualifying system with qualifying sentence `σ[L]`
([AFK26, Theorem 4.23 and Definition 2.23]), so the abstract [AFK26, Theorem 2.27] applies.  This
file states and proves `Theorem436Target` along that route, as `theorem436Target_abstract`: the
abstract Theorem 2.27 (`QualifyingSystem.hasThinAlephOneSpectrumTarget`) applied to the instance
(`templateQualifyingSentenceTarget`), composed by `theorem436Target_of_qualifyingSentenceTarget`.

This is a **second, separately stated proof**.  It is separate from and does not replace the
concrete proof `theorem436Target` (`VaughtConjecture.Correspondence.TemplateSystem.BackAndForth`),
which counts through the maximal stage and uses the uniqueness of maximal lifts
(`maximalLiftUniqueTarget`) and the isomorphism invariance of the maximal stage
(`maximalStageInvariantTarget`) for `K[L]`; the route here uses neither.  Both routes use
Reconstruction for `K[L]` (`reconstructionTarget`, [AFK26, Proposition 4.34]), here through the
maximal completion behind conditions (a) and (c).

The sentence is `σ[L]` (`templateSentence`) itself: it is **not** identified with the repository's
public sentence `baseLanguage.densitySentence`, and no spectrum result is transferred to or from
it.
-/

namespace VaughtConjecture

open Correspondence

/-- **[AFK26, Theorem 4.36] by the abstract route** (`Theorem436Target`, a second proof): the
abstract [AFK26, Theorem 2.27] (`QualifyingSystem.hasThinAlephOneSpectrumTarget`) for the
qualifying system `K[L]` with qualifying sentence `σ[L]` (`templateQualifyingSentenceTarget`),
composed by `theorem436Target_of_qualifyingSentenceTarget`.  Separate from, and not a replacement
of, the concrete proof `theorem436Target`.  Not identified with any statement about
`baseLanguage.densitySentence`.  Correspondence with the printed definitions. -/
theorem theorem436Target_abstract : Theorem436Target :=
  theorem436Target_of_qualifyingSentenceTarget
    (fun _ W ↦ W.hasThinAlephOneSpectrumTarget templateSentence.{0})
    templateQualifyingSentenceTarget

end VaughtConjecture
