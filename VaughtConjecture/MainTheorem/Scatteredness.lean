/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFScatteredSentence

/-!
# Thinness from countably many back-and-forth classes at every level

Roadmap, Layer 6 (thinness) and "Reduction to full presentations" (the third conclusion of the
fundamental theorem there); `IMPLEMENTATION.md`, "The full-presentation route" (the scatteredness
form of the thinness composition).

**The statement.**  Let `K` be a set of codes on `ℕ` of structures in a countable relational
language `L`.  If for every `η < ω₁` the codes in `K` fall into only countably many classes of
back-and-forth equivalence at level `η` (the infinitary-logic library's `CodeBFEquiv η`,
restricted to `K`), then `K` contains no nonempty perfect set of pairwise nonisomorphic codes
(`isThinOn_of_countable_bfClasses`).  The hypothesis counts **classes** of the relation restricted
to `K`, not codes: the quotient of `K` by `CodeBFEquiv η` is countable.  For the models of a
sentence `φ` this is `isThinOnNatModels_of_countable_bfClasses`, with the library's
restriction `bfEquivSetoid φ η` of `CodeBFEquiv η` to the codes of models of `φ`; the conclusion
is the library's thinness `φ.IsThinOnNatModels`, the form of
`isThinOnNatModels_of_countable_truth_sides`.  Cf. the scattered sentences of [Mon, §XII.1]
(countably many `≡_α`-classes of models for every `α < ω₁`), recalled in the module docstring of
`VaughtConjecture.MainTheorem.Spectrum`; no comparison of `CodeBFEquiv η` with [Mon]'s `≡_α`
is used or proved here.

**Quotations.**  Both theorems are quotations of InfinitaryLogic (at the pin): the hypothesis of
`isThinOn_of_countable_bfClasses` is, by definition, InfinitaryLogic's
`FirstOrder.Language.BFScattered K`, and the two theorems are its
`FirstOrder.Language.isThinOn_of_bfScattered` (`Descriptive/BFScattered`) and
`FirstOrder.Language.Sentenceω.isThinOnNatModels_of_bfScattered`
(`Descriptive/BFScatteredSentence`).  Their statements here are unchanged.  Neither is more
general than InfinitaryLogic's (the hypotheses and conclusions are the same), so neither is kept
for generality.  InfinitaryLogic's proof: the range of a Cantor antichain in `K` is analytic, so
the library's **uniform back-and-forth separation** (`exists_uniform_bfSeparation`: an analytic
set of nonisomorphic pairs is separated at one level, by boundedness of the analytic family of the
forced back-and-forth trees), applied to the off-diagonal of the range, gives one level `η < ω₁`
at which its distinct points are not back-and-forth equivalent; the class map at `η` then injects
Cantor space into the countable quotient of `K`; and a perfect antichain in the (completely
metrizable) space of codes yields a Cantor antichain.  The level is the one of the library's
theorem, an `Ordinal.{0}` below `Ordinal.omega 1`, with no `Ordinal.lift` and no offset.

**The lemmas on closed antichains.**  The steps of the same argument for a nonempty perfect
pairwise nonisomorphic `P ⊆ K` are kept with their statements:

* the **off-diagonal** `P.offDiag` (Mathlib's `Set.offDiag`), the pairs of distinct points of `P`,
  is analytic when `P` is closed (`analyticSet_offDiag`), and has no isomorphic pair
  (`offDiag_noniso`, a quotation of InfinitaryLogic's
  `FirstOrder.Language.not_structureIso_of_mem_offDiag`);
* one level `η < ω₁` separates the distinct points of a closed antichain
  (`exists_forall_not_codeBFEquiv_of_isClosed`, a quotation of InfinitaryLogic's
  `FirstOrder.Language.exists_forall_not_codeBFEquiv_of_analyticSet`, which separates every
  analytic antichain);
* a nonempty perfect set of codes is uncountable (`not_countable_of_perfect`; the library's
  `Perfect.mk_eq_continuum`, in the Polish space of codes).  InfinitaryLogic states this only in a
  metric space (`Perfect.mk_eq_continuum` assumes `MetricSpace`), and the space of codes carries
  a metric only after a choice of compatible complete metric
  (`TopologicalSpace.upgradeIsCompletelyMetrizable`), so the statement for codes, with no metric
  in it, is kept here.

**Back-and-forth equivalence as a setoid.**  `codeBFEquivSetoid L η` is the library's
`CodeBFEquiv η` on all codes, an equivalence relation by reflexivity, symmetry, and transitivity
of `BFEquiv`; it is InfinitaryLogic's `FirstOrder.Language.codeBFEquivSetoid L η` by definition.
The library's `bfEquivSetoid φ η` is its restriction to the codes of models of `φ`
(`bfEquivSetoid_eq_comap`, true by definition and a quotation of InfinitaryLogic's statement), as
`isoSetoid φ` is the restriction of `structureIsoSetoid L`.

## Placement

This file belongs to Layer 6 of `roadmap/README.md`.

## References

Scattered sentences are [Mon, §XII.1], for A. Montalbán, *Computable Structure Theory: Beyond
the arithmetic* (draft, 22 April 2025).  The boundedness of analytic families of well-founded
trees behind `exists_uniform_bfSeparation` is [MarDST, Corollary 5.16], for D. Marker,
*Descriptive Set Theory* (lecture notes, Math 512).
-/

universe u v

namespace VaughtConjecture.MainTheorem

open FirstOrder Language Cardinal Set MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-! ### Back-and-forth equivalence of codes as a setoid -/

variable (L) in
/-- **Back-and-forth equivalence at level `α`** on all codes on `ℕ`: the library's
`CodeBFEquiv α`, an equivalence relation.  By definition the library's
`FirstOrder.Language.codeBFEquivSetoid L α`. -/
def codeBFEquivSetoid (α : Ordinal.{0}) : Setoid (StructureSpace L) :=
  FirstOrder.Language.codeBFEquivSetoid L α

/-- The library's back-and-forth setoid on the codes of models of `φ` is the restriction of
`codeBFEquivSetoid L α`.  A quotation of InfinitaryLogic's
`FirstOrder.Language.bfEquivSetoid_eq_comap` (at the pin). -/
theorem bfEquivSetoid_eq_comap (φ : L.Sentenceω) (α : Ordinal.{0}) :
    bfEquivSetoid φ α = (codeBFEquivSetoid L α).comap (Subtype.val : ModelsOf φ → _) :=
  FirstOrder.Language.bfEquivSetoid_eq_comap φ α

/-! ### The off-diagonal of a set of codes -/

omit [L.IsRelational] in
/-- **The off-diagonal of a closed set of codes is analytic**: a closed set is Borel, hence
analytic in the Polish space of codes, and the off-diagonal of an analytic set in a Hausdorff space
is analytic (InfinitaryLogic's `MeasureTheory.AnalyticSet.offDiag`, at the pin). -/
theorem analyticSet_offDiag [Countable (Σ l, L.Relations l)] {P : Set (StructureSpace L)}
    (hP : IsClosed P) : AnalyticSet P.offDiag :=
  hP.measurableSet.analyticSet.offDiag

/-- **The off-diagonal of a pairwise nonisomorphic set of codes has no isomorphic pair.**  The
hypothesis is pairwise nonisomorphism in the form of the library's `HasPerfectAntichainOn`.  A
quotation of InfinitaryLogic's `FirstOrder.Language.not_structureIso_of_mem_offDiag` (at the
pin). -/
theorem offDiag_noniso {P : Set (StructureSpace L)}
    (hP : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∀ p ∈ P.offDiag, ¬ (structureIsoSetoid L).r p.1 p.2 :=
  not_structureIso_of_mem_offDiag hP

/-! ### Thinness -/

variable [Countable (Σ l, L.Relations l)]

omit [L.IsRelational] in
/-- **A nonempty perfect set of codes is uncountable**: it has the cardinality of the continuum
(the library's `Perfect.mk_eq_continuum`), in the Polish space of codes.  Kept here because
InfinitaryLogic's `Perfect.mk_eq_continuum` assumes a metric space, and the space of codes gets
one only after a choice of compatible complete metric
(`TopologicalSpace.upgradeIsCompletelyMetrizable`), made inside the proof; the statement has no
metric in it. -/
theorem not_countable_of_perfect {P : Set (StructureSpace L)} (hperf : Perfect P)
    (hne : P.Nonempty) : ¬ P.Countable := by
  -- a complete metric compatible with the topology; `hperf` is unaffected
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  rw [← le_aleph0_iff_set_countable, hperf.mk_eq_continuum hne, not_le]
  exact aleph0_lt_continuum

/-- **One back-and-forth level separates a closed antichain**: for a closed set `P` of pairwise
nonisomorphic codes, there is `η < ω₁` at which no two distinct points of `P` are
back-and-forth equivalent (the library's `exists_uniform_bfSeparation`, applied to the
off-diagonal).  A quotation of InfinitaryLogic's
`FirstOrder.Language.exists_forall_not_codeBFEquiv_of_analyticSet` (at the pin), which separates
every analytic antichain; a closed set of codes is analytic. -/
theorem exists_forall_not_codeBFEquiv_of_isClosed {P : Set (StructureSpace L)} (hP : IsClosed P)
    (hanti : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y :=
  exists_forall_not_codeBFEquiv_of_analyticSet hP.measurableSet.analyticSet hanti

/-- **Thinness from countably many back-and-forth classes at every level**: if for every
`η < ω₁` the restriction of `CodeBFEquiv η` to a set `K` of codes has countably many classes,
then `K` contains no nonempty perfect set of pairwise nonisomorphic codes.  A quotation of
InfinitaryLogic's `FirstOrder.Language.isThinOn_of_bfScattered` (at the pin): the hypothesis is
`FirstOrder.Language.BFScattered K`, by definition. -/
theorem isThinOn_of_countable_bfClasses {K : Set (StructureSpace L)}
    (hK : ∀ η : Ordinal.{0}, η < Ordinal.omega 1 →
      Countable (Quotient ((codeBFEquivSetoid L η).comap (Subtype.val : K → _)))) :
    IsThinOn (structureIsoSetoid L) K :=
  isThinOn_of_bfScattered hK

/-- **Thinness of a sentence from countably many back-and-forth classes at every level**: if for
every `η < ω₁` the codes of models of `φ` fall into countably many classes of back-and-forth
equivalence at level `η` (the library's `bfEquivSetoid φ η`), then `φ` is thin on its coded
models.  A quotation of InfinitaryLogic's
`FirstOrder.Language.Sentenceω.isThinOnNatModels_of_bfScattered` (at the pin). -/
theorem isThinOnNatModels_of_countable_bfClasses {φ : L.Sentenceω}
    (h : ∀ η : Ordinal.{0}, η < Ordinal.omega 1 → Countable (Quotient (bfEquivSetoid φ η))) :
    φ.IsThinOnNatModels :=
  Sentenceω.isThinOnNatModels_of_bfScattered h

end VaughtConjecture.MainTheorem
