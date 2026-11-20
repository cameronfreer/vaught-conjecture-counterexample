/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.AlephOne.OrderReading
import VaughtConjecture.AlephOne.ScottAnalysis
import VaughtConjecture.Realization.RootChange

/-!
# Recovering the code from the base structure, and `2 ^ ℵ₁` models of cardinality `ℵ₁`

A **repeated code** is a parameter `A : J → Bool` read along a repetition scheme
`r : ω₁ → J` (`CodedOrder.HasUnboundedFibres`): the shape of the phase `ξ` is
`BlockShape.ofBit (A (r ξ))`, so that the bit sequence of the shapes is `A ∘ r`
(`Phase.shapeBitTarget`).  A **full condition** is a phase condition at stage `ω₁`, on the carrier
`ω₁.ToType` with phases indexed by `ω₁.ToType`, with every phase completed and every point a block
point; its realization is then covering.  Its **base structure** is the structure of the reduction
of its realization to `ω`, as in `VaughtConjecture.Realization.RootChange`.

Two full conditions on the same carrier carry two base structures on the same type, so an
isomorphism between them is written with both structures explicit (`@Language.Equiv`).

**Statements** (all stated; none proved in this file yet).

* `Phase.TailEquivalentOfBaseEquivTarget` (given-condition, any shapes): if two full conditions
  have isomorphic base structures, the coded orders of the bit sequences of their shapes are
  tail-equivalent.
* `Phase.CodeEqOfBaseEquivTarget` (given-condition, the primary statement): for any two full
  conditions realizing repeated codes `A` and `A'` along the same repetition scheme, with any
  schedules of requests, an isomorphism of their base structures gives `A = A'`.  The statement
  quantifies over the conditions, so it does not depend on the choices made in an existence proof.
* `Phase.ExistsAlephOneFamilyTarget` (existence): a family, indexed by the `2 ^ ℵ₁` maps
  `ω₁ → Bool`, of models of the density sentence of cardinality `ℵ₁`, pairwise nonisomorphic.
* `Phase.ExistsAlephOneFamilyScottRankTarget` (existence, optional strengthening): the same family
  with every member of internal Scott rank `ω₁` and semantic Scott process of rank `ω₁` at every
  length beyond `ω₁ + 1`.

The given-condition statements are about every full condition satisfying their hypotheses and
assert no existence; the existence statements choose one full condition per code.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence, recorded in
`roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction"), and states the item recorded there as
not yet proved, `2 ^ ℵ₁` pairwise nonisomorphic models.
-/

universe w

namespace VaughtConjecture.AlephOne.Phase

open Ordinal Realization FirstOrder Language InfinitaryLogic.ScottProcess.Semantic

/-! ### Given-condition statements -/

/-- **Target: base-isomorphic full conditions have tail-equivalent coded orders** (stated;
given-condition).  At stage `ω₁`, on the carrier `ω₁.ToType` with phases indexed by `ω₁.ToType`,
for any shapes `shape` and `shape'` and any schedules of requests `req` and `req'`, let `c` and
`c'` be phase conditions with every phase completed and every point a block point.  If the base
structures of `c.real` and `c'.real` (the structures of their reductions to `ω`) are isomorphic,
then the coded orders of the bit sequences of the two families of shapes are tail-equivalent. -/
def TailEquivalentOfBaseEquivTarget : Prop :=
  ∀ (shape shape' : (ω₁ : Ordinal.{0}).ToType → BlockShape)
    (req req' : (ω₁ : Ordinal.{0}).ToType →
      PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
    (c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType shape req)
    (c' : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType shape' req'),
    c.phases = Set.univ → c.dom = Set.univ → c'.phases = Set.univ → c'.dom = Set.univ →
    Nonempty (@Language.Equiv baseLanguage.{0} (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType
      (c.real.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
      (c'.real.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure) →
    Order.TailEquivalent (CodedOrder (shapeBits shape)) (CodedOrder (shapeBits shape'))

/-- **Target: the base structure of a full condition determines its repeated code** (stated;
given-condition).  Let `r : ω₁ → J` be a repetition scheme (every fibre unbounded) and
`A, A' : J → Bool` two parameters.  At stage `ω₁`, on the carrier `ω₁.ToType` with phases indexed
by `ω₁.ToType`, let `c` be a phase condition for the shapes `BlockShape.ofBit ∘ A ∘ r` and `c'` one
for the shapes `BlockShape.ofBit ∘ A' ∘ r`, with any schedules of requests `req` and `req'`, each
with every phase completed and every point a block point.  If the base structures of `c.real` and
`c'.real` (the structures of their reductions to `ω`) are isomorphic, then `A = A'`.  The
repetition scheme is the same for both conditions; the schedules may differ and are not assumed
to schedule every request. -/
def CodeEqOfBaseEquivTarget : Prop :=
  ∀ ⦃J : Type w⦄ (r : (ω₁ : Ordinal.{0}).ToType → J), CodedOrder.HasUnboundedFibres r →
    ∀ (A A' : J → Bool)
      (req req' : (ω₁ : Ordinal.{0}).ToType →
        PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType)
      (c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
        (ω₁ : Ordinal.{0}).ToType (BlockShape.ofBit ∘ A ∘ r) req)
      (c' : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
        (ω₁ : Ordinal.{0}).ToType (BlockShape.ofBit ∘ A' ∘ r) req'),
      c.phases = Set.univ → c.dom = Set.univ → c'.phases = Set.univ → c'.dom = Set.univ →
      Nonempty (@Language.Equiv baseLanguage.{0} (ω₁ : Ordinal.{0}).ToType
        (ω₁ : Ordinal.{0}).ToType
        (c.real.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure
        (c'.real.reduce Ordinal.isSuccLimit_omega0.isSuccPrelimit).toStructure) →
      A = A'

/-! ### Existence statements -/

/-- **Target: `2 ^ ℵ₁` pairwise nonisomorphic models of the density sentence of cardinality `ℵ₁`**
(stated; existence).  There is a family of structures of the base language on carriers in `Type`,
indexed by the maps `ω₁ → Bool`, each satisfying the density sentence and of cardinality `ℵ₁`,
such that the members at distinct indices are not isomorphic; the index set has cardinality
`2 ^ ℵ₁`. -/
def ExistsAlephOneFamilyTarget : Prop :=
  ∃ (M : ((ω₁ : Ordinal.{0}).ToType → Bool) → Type)
    (_ : ∀ A, baseLanguage.{0}.Structure (M A)),
    (∀ A, Sentenceω.Realize baseLanguage.densitySentence.{0} (M A) ∧
      Cardinal.mk (M A) = Cardinal.aleph 1) ∧
    (∀ A A', A ≠ A' → IsEmpty (M A ≃[baseLanguage.{0}] M A')) ∧
    Cardinal.mk ((ω₁ : Ordinal.{0}).ToType → Bool) = 2 ^ Cardinal.aleph 1

/-- **Target: `2 ^ ℵ₁` pairwise nonisomorphic models of cardinality `ℵ₁` and Scott rank `ω₁`**
(stated; existence; an optional strengthening of `Phase.ExistsAlephOneFamilyTarget`).  There is a
family of structures of the base language on infinite carriers in `Type`, indexed by the maps
`ω₁ → Bool`, each satisfying the density sentence, of cardinality `ℵ₁` and internal Scott rank
`ω₁`, with semantic Scott process of rank `ω₁` at every length beyond `ω₁ + 1`, such that the
members at distinct indices are not isomorphic; the index set has cardinality `2 ^ ℵ₁`. -/
def ExistsAlephOneFamilyScottRankTarget : Prop :=
  ∃ (M : ((ω₁ : Ordinal.{0}).ToType → Bool) → Type)
    (_ : ∀ A, baseLanguage.{0}.Structure (M A)) (_ : ∀ A, Infinite (M A)),
    (∀ A, Sentenceω.Realize baseLanguage.densitySentence.{0} (M A) ∧
      Cardinal.mk (M A) = Cardinal.aleph 1 ∧
      internalScottRank (L := baseLanguage.{0}) (M A) = (ω₁ : Ordinal.{0}) ∧
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
        (scottProcessOf baseLanguage.{0} (M A) δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
    (∀ A A', A ≠ A' → IsEmpty (M A ≃[baseLanguage.{0}] M A')) ∧
    Cardinal.mk ((ω₁ : Ordinal.{0}).ToType → Bool) = 2 ^ Cardinal.aleph 1

end VaughtConjecture.AlephOne.Phase
