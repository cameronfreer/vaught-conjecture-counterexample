/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.StructureSpace
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Isomorphism classes of coded structures, and the number of codes on an infinite carrier

For a relational language `L` and a carrier `α`, the infinitary-logic library codes a structure
on `α` by its Boolean answers to the relation queries: a **relation query** is a relation symbol
with a tuple of `α` of its arity (`RelQueryOn L α`), a **structure code** is a map from the
queries to `Bool` (`StructureSpaceOn L α`), and a code decodes to the structure on `α` in which a
relation holds of a tuple when the code answers `true` (`StructureSpaceOn.toStructure`).  Since
`L` has no function symbols, a structure is determined by its answers
(`StructureSpaceOn.toStructure_ofStructure`).

This file counts **isomorphism classes**, not codes.

* `StructureCode.isoSetoid L α`: two codes are related when their decoded structures are
  isomorphic.  `StructureCode.Classes L α P` is the quotient of the codes satisfying a predicate
  `P` by this relation.  `P` need not be invariant under isomorphism.
* `StructureCode.structureIsoSetoid L Q`: on the sigma type of structures on carriers in `Type w`
  satisfying a predicate `Q`, two members are related when they are isomorphic.
  `StructureCode.StructureClasses L Q` is the quotient.

**Statements** (stated; proofs are later work).

* `StructureCode.CardLeTarget`: on an infinite carrier `α`, a relational language with countably
  many relation symbols has at most `2 ^ #α` structure codes.  Route: a query is determined by its
  symbol (with its arity) and the list of its tuple entries, so there are at most `ℵ₀ · #α = #α`
  queries, and a code is a map from the queries to `Bool`.
* `StructureCode.ExistsIsoCodeTarget`: a structure on a carrier `M` of the same cardinality as
  `α` is isomorphic to the decoded structure of a code on `α`.  Route: transport the structure
  along a bijection `M ≃ α` and encode it (`StructureSpaceOn.encodeViaEquiv`,
  `StructureSpaceOn.encodeViaEquiv_iso`).
-/

universe u v w w'

namespace VaughtConjecture.StructureCode

open Cardinal FirstOrder Language

section Classes

variable (L : Language.{u, v}) [L.IsRelational]

/-- **Isomorphism of decoded structures** on the codes on a carrier `α`: two codes are related
when the structures they decode to are isomorphic. -/
def isoSetoid (α : Type w) : Setoid (StructureSpaceOn L α) where
  r c d := Nonempty (@Language.Equiv L α α c.toStructure d.toStructure)
  iseqv :=
    ⟨fun c ↦ ⟨@Language.Equiv.refl L α c.toStructure⟩,
      fun {c d} ⟨e⟩ ↦ ⟨@Language.Equiv.symm L α α c.toStructure d.toStructure e⟩,
      fun {c d b} ⟨e⟩ ⟨f⟩ ↦
        ⟨@Language.Equiv.comp L α α c.toStructure d.toStructure α b.toStructure f e⟩⟩

/-- **The isomorphism classes of the codes satisfying `P`**: the quotient of the codes on `α`
satisfying `P` by isomorphism of their decoded structures (`StructureCode.isoSetoid`).  The
predicate is not assumed invariant under isomorphism; a class is represented by a code satisfying
`P`. -/
def Classes (α : Type w) (P : StructureSpaceOn L α → Prop) : Type (max v w) :=
  Quotient ((isoSetoid L α).comap (Subtype.val : {c // P c} → StructureSpaceOn L α))

/-- **Isomorphism** on the structures on carriers in `Type w` satisfying a predicate `Q`: two
members of the sigma type are related when they are isomorphic. -/
def structureIsoSetoid (Q : ∀ (M : Type w) [L.Structure M], Prop) :
    Setoid (Σ M : Type w, {inst : L.Structure M // @Q M inst}) where
  r x y := Nonempty (@Language.Equiv L x.1 y.1 x.2.1 y.2.1)
  iseqv :=
    ⟨fun x ↦ ⟨@Language.Equiv.refl L x.1 x.2.1⟩,
      fun {x y} ⟨e⟩ ↦ ⟨@Language.Equiv.symm L x.1 y.1 x.2.1 y.2.1 e⟩,
      fun {x y z} ⟨e⟩ ⟨f⟩ ↦
        ⟨@Language.Equiv.comp L x.1 y.1 x.2.1 y.2.1 z.1 z.2.1 f e⟩⟩

/-- **The isomorphism classes of the structures satisfying `Q`** on carriers in `Type w`: the
quotient of the sigma type of a carrier and a structure on it satisfying `Q` by isomorphism
(`StructureCode.structureIsoSetoid`). -/
def StructureClasses (Q : ∀ (M : Type w) [L.Structure M], Prop) : Type (max u v (w + 1)) :=
  Quotient (structureIsoSetoid L Q)

end Classes

/-- **Target: at most `2 ^ #α` structure codes on an infinite carrier** (stated).  For a
relational language with countably many relation symbols (of all arities together) and an
infinite carrier `α`, the codes on `α` number at most `2 ^ #α`. -/
def CardLeTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] [Countable (Σ n, L.Relations n)] ⦃α : Type w⦄
    [Infinite α], #(StructureSpaceOn L α) ≤ 2 ^ Cardinal.lift.{v} #α

/-- **Target: a structure on a carrier of the cardinality of `α` is isomorphic to a decoded code
on `α`** (stated).  For a relational language `L`, a structure on a carrier `M` and a carrier `α`
with `#M = #α` (lifted to a common universe), some code on `α` decodes to a structure isomorphic
to the given one. -/
def ExistsIsoCodeTarget : Prop :=
  ∀ ⦃L : Language.{u, v}⦄ [L.IsRelational] ⦃M : Type w⦄ [L.Structure M] ⦃α : Type w'⦄,
    Cardinal.lift.{w'} #M = Cardinal.lift.{w} #α →
    ∃ c : StructureSpaceOn L α, Nonempty (@Language.Equiv L M α _ c.toStructure)

end VaughtConjecture.StructureCode
