/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Scott.OrbitRank

/-!
# Invariance of the counted conditions under potential isomorphism

Companion programme over the density sentence, process rank `ω₁`.  Conventions as in
`VaughtConjecture.ProcessRank.RankConventions`: `r(a) = orbitRank a`, `R(M) = sup_a (r(a))`,
`S(M) = sup_a (r(a) + 1) = internalScottRank M`.

The counts of `VaughtConjecture.ProcessRank.Targets` are counts of classes under potential
isomorphism.  The conditions counted are a sentence of `L_{ω₁,ω}` (the density sentence) and a
value of `R(M)` or `S(M)`.  Both are invariant under potential isomorphism, for structures on
carriers in any two universes:

* `RealizeIffOfPotentialIsoTarget` (stated): potentially isomorphic structures satisfy the same
  sentences of `L_{ω₁,ω}`.  Route: a potential isomorphism gives back-and-forth equivalence of the
  empty tuples at every level (`PotentialIso.implies_BFEquiv_all`), in particular at the
  quantifier rank of the sentence, and equivalence at that rank gives agreement on it.
* `RanksLiftEqOfPotentialIsoTarget` (stated): potentially isomorphic structures have the same
  `R` and the same `S`, after lifting to a common universe.  Route: every tuple `a` of `M` is
  matched by the potential isomorphism to a tuple `a'` of `N` equivalent to it at every level, and
  equivalence at a level with `a` is equivalence at that level with `a'` (`BFEquiv.trans` through
  matched tuples), so `r(a)` and `r(a')` agree after lifting, and the suprema are over the same
  values.

So the classes are well defined on each predicate: a class meets the predicate exactly when all
its members satisfy it.
-/

universe u v w w'

namespace VaughtConjecture.ProcessRank

open FirstOrder Language

/-- **Target: potentially isomorphic structures satisfy the same sentences of `L_{ω₁,ω}`**, for a
relational language and structures on carriers in any two universes.  Stated. -/
def RealizeIffOfPotentialIsoTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] ⦃M : Type w⦄ ⦃N : Type w'⦄ [L.Structure M]
    [L.Structure N], Nonempty (PotentialIso L M N) →
      ∀ φ : L.Sentenceω, Sentenceω.Realize φ M ↔ Sentenceω.Realize φ N

/-- **Target: potentially isomorphic structures have the same process rank and the same internal
Scott rank**, for a relational language and structures on carriers in any two universes:
`R(M) = sup_a (r(a))` and `S(M) = sup_a (r(a) + 1)` agree with those of `N` after lifting to a
common universe.  Stated. -/
def RanksLiftEqOfPotentialIsoTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] ⦃M : Type w⦄ ⦃N : Type w'⦄ [L.Structure M]
    [L.Structure N], Nonempty (PotentialIso L M N) →
      Ordinal.lift.{w'} (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) =
          Ordinal.lift.{w} (⨆ x : (Σ n : ℕ, Fin n → N), orbitRank (L := L) x.2) ∧
        Ordinal.lift.{w'} (internalScottRank (L := L) M) =
          Ordinal.lift.{w} (internalScottRank (L := L) N)

end VaughtConjecture.ProcessRank
