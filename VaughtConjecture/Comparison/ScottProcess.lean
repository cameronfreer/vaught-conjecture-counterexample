/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.ScottProcess.SemanticBridge

/-!
# A potential isomorphism gives equal Scott processes

Roadmap, Layer 0, "Countable construction and comparison".  For infinite structures `M` and `N`
of a relational language `L`, on carriers in any two universes, a potential isomorphism
`P : PotentialIso L M N` makes their semantic Scott processes
(`InfinitaryLogic.ScottProcess.Semantic.scottProcessOf`) of every positive length equal.

**Proof.**  The rows of the process of `M` are the semantic entries `sf L α a` of the injective
tuples `a` of `M`.  Through `P`, every tuple `a` of `M` is matched to a tuple `b` of `N`
(`PotentialIso.exists_right`), back-and-forth equivalent to `a` at every level
(`PotentialIso.family_bfEquiv`); level `0` keeps the equality pattern
(`BFEquiv.eq_iff_eq`), so `b` is injective, and equal entries are back-and-forth equivalence
(`sf_eq_iff_bfEquiv`), so `sf L α b = sf L α a`.  So each row of the process of `M` is contained
in the corresponding row of the process of `N`, and the converse holds through
`PotentialIso.symm`.

No countability, cardinality or rank hypothesis enters.  The statement is generic in the
language and may later be placed beside the Scott-process API of InfinitaryLogic.

**Results (all proved).**

* `exists_sf_eq_of_potentialIso`: the matching of semantic entries.
* `scottProcessOf_eq_of_potentialIso`, and its target form `ScottProcessOfEqOfPotentialIsoTarget`.
-/

namespace VaughtConjecture.Comparison

open FirstOrder Language InfinitaryLogic.ScottProcess.Semantic

universe u v w w'

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M]
  [L.Structure N]

/-- **Matching of semantic entries through a potential isomorphism**: every injective tuple `a` of
`M` has an injective tuple `b` of `N` with the same semantic entry at level `α`.  The tuple
matched to `a` by `P` is back-and-forth equivalent to `a` at `α` and has its equality pattern. -/
theorem exists_sf_eq_of_potentialIso [Infinite M] [Infinite N] (P : PotentialIso L M N)
    (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) : ∃ b : Fin n ↪ N, sf L α b = sf L α a := by
  obtain ⟨b, hb⟩ := P.exists_right (⇑a)
  have h : BFEquiv (L := L) α n (⇑a) b := P.family_bfEquiv α hb
  have hinj : Function.Injective b := fun i j hij ↦ a.injective ((h.eq_iff_eq i j).2 hij)
  exact ⟨⟨b, hinj⟩, ((sf_eq_iff_bfEquiv α a ⟨b, hinj⟩).2 h).symm⟩

/-- **A potential isomorphism gives equal Scott processes**: infinite structures of a relational
language with a potential isomorphism, on carriers in any two universes, have the same semantic
Scott process of every positive length.  Each row of one process is contained in the
corresponding row of the other (`exists_sf_eq_of_potentialIso`, for `P` and `P.symm`). -/
theorem scottProcessOf_eq_of_potentialIso [Infinite M] [Infinite N] (P : PotentialIso L M N)
    {δ : Ordinal.{0}} (hδ : 0 < δ) : scottProcessOf L M δ hδ = scottProcessOf L N δ hδ := by
  ext α hα n x
  simp only [scottProcessOf_Φ, Set.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact exists_sf_eq_of_potentialIso P α a
  · rintro ⟨b, rfl⟩
    exact exists_sf_eq_of_potentialIso P.symm α b

/-- **Target (generic): a potential isomorphism gives equal Scott processes.**  For a relational
language and infinite structures `M` and `N` on carriers in any two universes, a potential
isomorphism makes the semantic Scott processes of every positive length equal.  Proved
(`scottProcessOfEqOfPotentialIsoTarget`). -/
def ScottProcessOfEqOfPotentialIsoTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] ⦃M : Type w⦄ ⦃N : Type w'⦄ [L.Structure M]
    [L.Structure N] [Infinite M] [Infinite N], PotentialIso L M N →
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ), scottProcessOf L M δ hδ = scottProcessOf L N δ hδ

/-- A potential isomorphism gives equal Scott processes (`scottProcessOf_eq_of_potentialIso`). -/
theorem scottProcessOfEqOfPotentialIsoTarget : ScottProcessOfEqOfPotentialIsoTarget.{u, v, w, w'} :=
  fun _ _ _ _ _ _ _ _ P _ hδ ↦ scottProcessOf_eq_of_potentialIso P hδ

end VaughtConjecture.Comparison
