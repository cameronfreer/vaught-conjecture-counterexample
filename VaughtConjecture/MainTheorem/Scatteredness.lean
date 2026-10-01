/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFSeparation
import InfinitaryLogic.ModelTheory.MorleyCounting

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

**The proof.**  Let `P ⊆ K` be nonempty, perfect, and pairwise nonisomorphic.

* The **off-diagonal** `P.offDiag` (Mathlib's `Set.offDiag`), the pairs of distinct points of
  `P`, is an analytic set (`analyticSet_offDiag`): it is `P ×ˢ P` minus the diagonal
  (`Set.prod_sdiff_diagonal`), `P ×ˢ P` is closed since `P` is, the diagonal is closed in the
  Hausdorff space of pairs of codes, so their difference is Borel, hence analytic in the Polish
  space of pairs of codes (the library's Polish and Borel structure on the space of codes, for
  countably many relation symbols).
* No pair of the off-diagonal is isomorphic (`offDiag_noniso`), since `P` is pairwise
  nonisomorphic.
* The library's **uniform back-and-forth separation** (`exists_uniform_bfSeparation`: an analytic
  set of nonisomorphic pairs is separated at one level, by boundedness of the analytic family of
  the forced back-and-forth trees) gives `η < ω₁` with `¬ CodeBFEquiv η x y` for all distinct
  `x y ∈ P` (`exists_forall_not_codeBFEquiv_of_isClosed`).  The level is the one of the library's
  theorem, an `Ordinal.{0}` below `Ordinal.omega 1`, with no `Ordinal.lift` and no offset.
* So the class map of `CodeBFEquiv η` is injective on `P`, and the classes met by `K` are as many
  as the classes of the restriction to `K` (Mathlib's second isomorphism theorem
  `Setoid.comapQuotientEquiv`); hence `P` is countable.  But a nonempty perfect set of codes is
  uncountable (`not_countable_of_perfect`; the library's `Perfect.mk_eq_continuum`, in the Polish
  space of codes).

**Back-and-forth equivalence as a setoid.**  `codeBFEquivSetoid L η` is the library's
`CodeBFEquiv η` on all codes, an equivalence relation by reflexivity, symmetry, and transitivity
of `BFEquiv`; the library's `bfEquivSetoid φ η` is its restriction to the codes of models of `φ`
(`bfEquivSetoid_eq_comap`, by definition), as `isoSetoid φ` is the restriction of
`structureIsoSetoid L`.

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
`CodeBFEquiv α`, an equivalence relation. -/
def codeBFEquivSetoid (α : Ordinal.{0}) : Setoid (StructureSpace L) where
  r := CodeBFEquiv α
  iseqv :=
    { refl := fun c ↦ @BFEquiv.refl L ℕ c.toStructure 0 α Fin.elim0
      symm := fun {c d} h ↦ @BFEquiv.symm L ℕ c.toStructure ℕ d.toStructure 0 α
        Fin.elim0 Fin.elim0 h
      trans := fun {c d e} h₁ h₂ ↦ @BFEquiv.trans L ℕ c.toStructure ℕ d.toStructure
        ℕ e.toStructure (n := 0) (α := α) (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0)
        h₁ h₂ }

/-- The library's back-and-forth setoid on the codes of models of `φ` is the restriction of
`codeBFEquivSetoid L α`. -/
theorem bfEquivSetoid_eq_comap (φ : L.Sentenceω) (α : Ordinal.{0}) :
    bfEquivSetoid φ α = (codeBFEquivSetoid L α).comap (Subtype.val : ModelsOf φ → _) :=
  rfl

/-! ### The off-diagonal of a set of codes -/

omit [L.IsRelational] in
/-- **The off-diagonal of a closed set of codes is analytic**: it is `P ×ˢ P` minus the
diagonal, `P ×ˢ P` is closed, the diagonal is closed, so their difference is Borel, hence analytic
in the Polish space of pairs of codes. -/
theorem analyticSet_offDiag [Countable (Σ l, L.Relations l)] {P : Set (StructureSpace L)}
    (hP : IsClosed P) : AnalyticSet P.offDiag := by
  rw [← Set.prod_sdiff_diagonal]
  exact ((hP.prod hP).measurableSet.diff isClosed_diagonal.measurableSet).analyticSet

/-- **The off-diagonal of a pairwise nonisomorphic set of codes has no isomorphic pair.**  The
hypothesis is pairwise nonisomorphism in the form of the library's `HasPerfectAntichainOn`. -/
theorem offDiag_noniso {P : Set (StructureSpace L)}
    (hP : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∀ p ∈ P.offDiag, ¬ (structureIsoSetoid L).r p.1 p.2 :=
  fun _ hp hr ↦ hp.2.2 (hP _ hp.1 _ hp.2.1 hr)

/-! ### Thinness -/

variable [Countable (Σ l, L.Relations l)]

omit [L.IsRelational] in
/-- **A nonempty perfect set of codes is uncountable**: it has the cardinality of the continuum
(the library's `Perfect.mk_eq_continuum`), in the Polish space of codes. -/
theorem not_countable_of_perfect {P : Set (StructureSpace L)} (hperf : Perfect P)
    (hne : P.Nonempty) : ¬ P.Countable := by
  -- a complete metric compatible with the topology; `hperf` is unaffected
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  rw [← le_aleph0_iff_set_countable, hperf.mk_eq_continuum hne, not_le]
  exact aleph0_lt_continuum

/-- **One back-and-forth level separates a closed antichain**: for a closed set `P` of pairwise
nonisomorphic codes, there is `η < ω₁` at which no two distinct points of `P` are
back-and-forth equivalent (the library's `exists_uniform_bfSeparation`, applied to the
off-diagonal). -/
theorem exists_forall_not_codeBFEquiv_of_isClosed {P : Set (StructureSpace L)} (hP : IsClosed P)
    (hanti : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y := by
  obtain ⟨η, hη, hsep⟩ :=
    exists_uniform_bfSeparation (analyticSet_offDiag hP) (offDiag_noniso hanti)
  exact ⟨η, hη, fun x hx y hy hxy ↦ hsep (x, y) (Set.mem_offDiag.mpr ⟨hx, hy, hxy⟩)⟩

/-- **Thinness from countably many back-and-forth classes at every level**: if for every
`η < ω₁` the restriction of `CodeBFEquiv η` to a set `K` of codes has countably many classes,
then `K` contains no nonempty perfect set of pairwise nonisomorphic codes. -/
theorem isThinOn_of_countable_bfClasses {K : Set (StructureSpace L)}
    (hK : ∀ η : Ordinal.{0}, η < Ordinal.omega 1 →
      Countable (Quotient ((codeBFEquivSetoid L η).comap (Subtype.val : K → _)))) :
    IsThinOn (structureIsoSetoid L) K := by
  rintro ⟨P, hperf, hne, hPK, hanti⟩
  obtain ⟨η, hη, hsep⟩ := exists_forall_not_codeBFEquiv_of_isClosed hperf.closed hanti
  -- the classes met by `K` are the classes of the restriction (second isomorphism theorem)
  have hcount := (Setoid.comapQuotientEquiv (Subtype.val : K → _)
    (codeBFEquivSetoid L η)).symm.countable_iff.mpr (hK η hη)
  rw [countable_coe_iff, range_comp, Subtype.range_coe] at hcount
  refine not_countable_of_perfect hperf hne
    (MapsTo.countable_of_injOn (fun x hx ↦ mem_image_of_mem _ (hPK hx)) (fun x hx y hy hxy ↦ ?_)
      hcount)
  by_contra hne
  exact hsep x hx y hy hne (Quotient.exact hxy)

/-- **Thinness of a sentence from countably many back-and-forth classes at every level**: if for
every `η < ω₁` the codes of models of `φ` fall into countably many classes of back-and-forth
equivalence at level `η` (the library's `bfEquivSetoid φ η`), then `φ` is thin on its coded
models. -/
theorem isThinOnNatModels_of_countable_bfClasses {φ : L.Sentenceω}
    (h : ∀ η : Ordinal.{0}, η < Ordinal.omega 1 → Countable (Quotient (bfEquivSetoid φ η))) :
    φ.IsThinOnNatModels :=
  isThinOn_of_countable_bfClasses fun η hη ↦ bfEquivSetoid_eq_comap φ η ▸ h η hη

end VaughtConjecture.MainTheorem
