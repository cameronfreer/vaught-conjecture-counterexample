/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.Family
import VaughtConjecture.Counting.StructureCodes

/-!
# Exactly `2 ^ ℵ₁` isomorphism classes of models of cardinality `ℵ₁`

The carrier is `Carrier = ω₁.ToType`, of cardinality `ℵ₁`.  A **code** (`AlephOne.Code`) is a
structure code of the base language on the carrier: a map from the relation queries (a relation
symbol with a tuple of its arity) to `Bool`.  The base language has no function symbols and no
constants (`baseLanguage.isRelational`), so a structure on the carrier is the decoded structure of
its code.  `Code.Decoded c` is the carrier with the structure decoded from `c`.

The objects counted are **isomorphism classes**.  For a predicate `P` on codes,
`StructureCode.Classes baseLanguage Carrier P` is the quotient of the codes satisfying `P` by
isomorphism of their decoded structures; for a predicate `Q` on structures,
`StructureCode.StructureClasses baseLanguage Q` is the quotient of the sigma type of a carrier in
`Type` and a structure on it satisfying `Q` by isomorphism.

**Statements** (stated; proofs are later work).

* `AlephOne.CodeCardLeTarget`: there are at most `2 ^ ℵ₁` codes.  Route: the general bound
  `StructureCode.CardLeTarget` (countably many symbols, `ℵ₁` finite lists from the carrier, so at
  most `ℵ₁` queries) at the carrier.
* `AlephOne.CodeClassesCardEqTarget` (the count): there is a family of codes indexed by the maps
  `ω₁ → Bool` whose decoded structures have the conclusions of
  `AlephOne.existsAlephOneFamilyScottRankTarget` (models of the density sentence, internal Scott
  rank `ω₁`, semantic Scott process of rank `ω₁` beyond `ω₁ + 1`, one common semantic Scott
  process at every positive length, pairwise nonisomorphic), such that **every** predicate on
  codes containing the family has exactly `2 ^ ℵ₁` isomorphism classes.  Route: the family theorem
  transported to the carrier along bijections (`StructureCode.ExistsIsoCodeTarget`); the upper
  bound passes to the quotient (`AlephOne.CodeCardLeTarget`); pairwise nonisomorphism makes the
  map from `ω₁ → Bool` to the classes injective, and `#(ω₁ → Bool) = 2 ^ ℵ₁`.
* `AlephOne.ModelClassesCardEqTarget` (first consequence): the models of the density sentence of
  cardinality `ℵ₁` on carriers in `Type` fall into exactly `2 ^ ℵ₁` isomorphism classes.  Route:
  each is isomorphic to the decoded structure of a code (`StructureCode.ExistsIsoCodeTarget`), so
  the classes inject into the classes of the codes of models, which number `2 ^ ℵ₁` by the count;
  the family gives the lower bound.
* `AlephOne.ScottClassModelClassesCardEqTarget` (second consequence): there is a model `N` of the
  density sentence of cardinality `ℵ₁` and internal Scott rank `ω₁` such that the models of the
  density sentence of cardinality `ℵ₁` with the semantic Scott process of `N` at every positive
  length already fall into exactly `2 ^ ℵ₁` isomorphism classes.  Route: as for the first
  consequence, with `N` a member of the coded family.

The count is about all codes satisfying the predicate, not only about the family: the family enters
only through the lower bound.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence, recorded in
`roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction").
-/

namespace VaughtConjecture.AlephOne

open Ordinal FirstOrder Language InfinitaryLogic.ScottProcess.Semantic StructureCode

/-- The carrier `ω₁.ToType` is infinite: it has `ℵ₁` points (`AlephOne.mk_carrier`). -/
instance infinite_carrier : Infinite Carrier :=
  Cardinal.infinite_iff.mpr (mk_carrier ▸ Cardinal.aleph0_le_aleph 1)

/-- A **code**: a structure code of the base language on the carrier `ω₁.ToType`, a map from the
relation queries (a relation symbol with a tuple of the carrier of its arity) to `Bool`. -/
abbrev Code : Type 1 :=
  StructureSpaceOn baseLanguage.{0} Carrier

/-- The carrier with the structure decoded from the code `c`: a relation holds of a tuple when `c`
answers `true` to the query. -/
def Code.Decoded (_c : Code) : Type :=
  Carrier

/-- The decoded structure of a code. -/
noncomputable instance (c : Code) : baseLanguage.{0}.Structure c.Decoded :=
  c.toStructure

/-- The decoded structure of a code is on an infinite carrier. -/
instance (c : Code) : Infinite c.Decoded :=
  inferInstanceAs (Infinite Carrier)

/-- **Target: at most `2 ^ ℵ₁` codes** (stated).  The structure codes of the base language on the
carrier `ω₁.ToType` number at most `2 ^ ℵ₁`. -/
def CodeCardLeTarget : Prop :=
  Cardinal.mk Code ≤ 2 ^ Cardinal.aleph 1

/-- **Target: every predicate on codes containing the coded family has exactly `2 ^ ℵ₁`
isomorphism classes** (stated; existence of the family, then a statement about every predicate).
There is a family `F` of codes on the carrier `ω₁.ToType`, indexed by the maps `ω₁ → Bool`, whose
decoded structures satisfy the density sentence, have internal Scott rank `ω₁` and semantic Scott
process of rank `ω₁` at every length beyond `ω₁ + 1`, all have the same semantic Scott process of
every positive length, and are pairwise nonisomorphic; and for every predicate `P` on codes with
`P (F A)` for every `A`, the quotient of the codes satisfying `P` by isomorphism of their decoded
structures has cardinality `2 ^ ℵ₁`. -/
def CodeClassesCardEqTarget : Prop :=
  ∃ F : (Carrier → Bool) → Code,
    (∀ A, Sentenceω.Realize baseLanguage.densitySentence.{0} (F A).Decoded ∧
      internalScottRank (L := baseLanguage.{0}) (F A).Decoded = (ω₁ : Ordinal.{0}) ∧
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
        (scottProcessOf baseLanguage.{0} (F A).Decoded δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
    (∀ A A' ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
      scottProcessOf baseLanguage.{0} (F A).Decoded δ hδ =
        scottProcessOf baseLanguage.{0} (F A').Decoded δ hδ) ∧
    (∀ A A', A ≠ A' → IsEmpty ((F A).Decoded ≃[baseLanguage.{0}] (F A').Decoded)) ∧
    ∀ P : Code → Prop, (∀ A, P (F A)) →
      Cardinal.mk (Classes baseLanguage.{0} Carrier P) = 2 ^ Cardinal.aleph 1

/-- **Target: exactly `2 ^ ℵ₁` isomorphism classes of models of the density sentence of
cardinality `ℵ₁`** (stated).  The quotient of the sigma type of a carrier `M` in `Type` and a
structure of the base language on `M` satisfying the density sentence, with `#M = ℵ₁`, by
isomorphism has cardinality `2 ^ ℵ₁`. -/
def ModelClassesCardEqTarget : Prop :=
  Cardinal.mk (StructureClasses baseLanguage.{0} fun (M : Type) [baseLanguage.{0}.Structure M] ↦
      Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
        Cardinal.mk M = Cardinal.aleph 1) =
    2 ^ Cardinal.aleph 1

/-- **Target: exactly `2 ^ ℵ₁` isomorphism classes of models of cardinality `ℵ₁` in one Scott
class** (stated; existence of the reference model, then a count).  There is a structure `N` of the
base language on an infinite carrier in `Type`, satisfying the density sentence, of cardinality
`ℵ₁` and internal Scott rank `ω₁`, with semantic Scott process of rank `ω₁` at every length beyond
`ω₁ + 1`, such that the quotient by isomorphism of the sigma type of a carrier `M` in `Type` and a
structure of the base language on `M` satisfying the density sentence, with `#M = ℵ₁`, `M`
infinite and the semantic Scott process of `M` equal to that of `N` at every positive length, has
cardinality `2 ^ ℵ₁`. -/
def ScottClassModelClassesCardEqTarget : Prop :=
  ∃ (N : Type) (_ : baseLanguage.{0}.Structure N) (_ : Infinite N),
    Sentenceω.Realize baseLanguage.densitySentence.{0} N ∧ Cardinal.mk N = Cardinal.aleph 1 ∧
    internalScottRank (L := baseLanguage.{0}) N = (ω₁ : Ordinal.{0}) ∧
    (∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
      (scottProcessOf baseLanguage.{0} N δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
    Cardinal.mk (StructureClasses baseLanguage.{0} fun (M : Type) [baseLanguage.{0}.Structure M] ↦
        Sentenceω.Realize baseLanguage.densitySentence.{0} M ∧
          Cardinal.mk M = Cardinal.aleph 1 ∧
          ∃ _ : Infinite M, ∀ ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
            scottProcessOf baseLanguage.{0} M δ hδ = scottProcessOf baseLanguage.{0} N δ hδ) =
      2 ^ Cardinal.aleph 1

end VaughtConjecture.AlephOne
