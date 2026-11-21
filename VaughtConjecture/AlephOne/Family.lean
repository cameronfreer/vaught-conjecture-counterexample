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
isomorphism between them is written with both structures explicit (`@Language.Equiv`).  For the
same reason the exterior orders are always passed explicitly (`Realization.exteriorLinearOrder`):
the points outside a root form a subtype of the carrier `ω₁.ToType`, which also inherits the order
of the carrier, and the two orders mean different things.

**Statements** (all proved, each by the theorem of the same name in lower camel case).

* `Phase.TailEquivalentOfBaseEquivTarget` (given-condition, any shapes): if two full conditions
  have isomorphic base structures, the coded orders of the bit sequences of their shapes are
  tail-equivalent.  Route: the first blocks are countably infinite closed roots and the exterior
  orders above them are the tails of the coded orders (`Phase.omegaOneOrderReadingTarget`); the
  two exterior orders are tail-equivalent (`Realization.baseEquivExteriorTailEquivalentTarget`);
  tail equivalence is symmetric and transitive.
* `Phase.CodeEqOfBaseEquivTarget` (given-condition, the primary statement): for any two full
  conditions realizing repeated codes `A` and `A'` along the same repetition scheme, with any
  schedules of requests, an isomorphism of their base structures gives `A = A'`.  The statement
  quantifies over the conditions, so it does not depend on the choices made in an existence proof.
  Route: `Phase.TailEquivalentOfBaseEquivTarget` and the recovery of the parameter
  (`CodedOrder.tailEquivalentInjectiveTarget`).
* `AlephOne.ExistsAlephOneFamilyScottRankTarget` (existence): a family, indexed by the `2 ^ ℵ₁`
  maps `ω₁ → Bool`, of models of the density sentence of cardinality `ℵ₁`, each of internal Scott
  rank `ω₁` and semantic Scott process of rank `ω₁` at every length beyond `ω₁ + 1`, all with the
  same semantic Scott process of every positive length, and pairwise nonisomorphic.  The member at
  `A` is the base structure of a full condition for the repeated code `A` along a repetition scheme
  on `ω₁`, with a schedule serving every request (`Phase.existsFullPhaseReceivingModelTarget`).
* `AlephOne.ExistsAlephOneFamilyTarget` (existence): the same family without the Scott
  conclusions.

The given-condition statements are about every full condition satisfying their hypotheses and
assert no existence; the existence statements choose one full condition per code.

## Placement

This file belongs to the `ℵ₁` companion construction over the density sentence, recorded in
`roadmap/COMPANIONS.md` ("The `ℵ₁` companion construction"): it proves the item `2 ^ ℵ₁` pairwise
nonisomorphic models of cardinality `ℵ₁`.
-/

universe u v w

namespace VaughtConjecture.AlephOne.Phase

open Ordinal Realization FirstOrder Language

/-! ### Three lemmas -/

/-- A phase condition all of whose points are block points has a covering realization. -/
theorem PhaseCondition.isCovering_real_of_dom_eq_univ {α : Ordinal.{u}} {X : Type v}
    {Φ : Type w} [LinearOrder Φ] {shape : Φ → BlockShape} {req : Φ → PhaseRequest α X}
    (c : PhaseCondition α X Φ shape req) (hdom : c.dom = Set.univ) : c.real.IsCovering :=
  fun _ t ↦ c.isCovering t (by
    have h := Set.subset_univ (Set.range t)
    rwa [← hdom] at h)

/-- A linear order with a tail isomorphic to the whole of a linear order is tail-equivalent to
it. -/
theorem tailEquivalent_of_orderIso {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β]
    {U : Set α} (hU : IsUpperSet U) (hne : U.Nonempty) (e : U ≃o β) :
    Order.TailEquivalent α β :=
  ⟨U, Set.univ, hU, isUpperSet_univ, hne, ⟨e ⟨hne.some, hne.some_mem⟩, trivial⟩,
    ⟨e.trans (OrderIso.Set.univ (α := β)).symm⟩⟩

/-- The countable ordinals are uncountable. -/
theorem uncountable_omegaOne : Uncountable (ω₁ : Ordinal.{0}).ToType := by
  rw [← Cardinal.aleph0_lt_mk_iff, CodedOrder.mk_omegaOne]
  exact Cardinal.aleph0_lt_aleph_one

/-! ### Given-condition statements -/

/-- **Target: base-isomorphic full conditions have tail-equivalent coded orders** (proved;
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

/-- **The coded order of the shapes is tail-equivalent to the exterior order above the first
block** of a full condition, the exterior order passed explicitly: the order reading
(`Phase.omegaOneOrderReadingTarget`) is an isomorphism from a tail of the coded order onto the
whole exterior. -/
theorem tailEquivalent_exterior {shape : (ω₁ : Ordinal.{0}).ToType → BlockShape}
    {req : (ω₁ : Ordinal.{0}).ToType →
      PhaseRequest.{0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType}
    (c : PhaseCondition.{0, 0, 0} (ω₁ : Ordinal.{0}) (ω₁ : Ordinal.{0}).ToType
      (ω₁ : Ordinal.{0}).ToType shape req) (hph : c.phases = Set.univ)
    (hdom : c.dom = Set.univ) (hc : c.real.IsCovering)
    (hB : (c.real.closure c.isConsistent hc).IsClosed (Set.range (c.block firstPhase)))
    (hBi : (Set.range (c.block firstPhase)).Infinite) :
    @Order.TailEquivalent (CodedOrder (shapeBits shape))
      {x : (ω₁ : Ordinal.{0}).ToType // x ∉ Set.range (c.block firstPhase)} _
      (c.real.exteriorLinearOrder c.isConsistent hc hB hBi) := by
  obtain ⟨-, -, -, -, hU, hne, ⟨e, -⟩⟩ := omegaOneOrderReadingTarget shape req c hph hdom hc
  let eo : @OrderIso (codedTail (shapeBits shape) firstPhase)
      {x : (ω₁ : Ordinal.{0}).ToType // x ∉ Set.range (c.block firstPhase)} _
      (c.real.exteriorLinearOrder c.isConsistent hc hB hBi).toLE := e
  exact @tailEquivalent_of_orderIso _ _ _ (c.real.exteriorLinearOrder c.isConsistent hc hB hBi)
    _ hU hne eo

/-- **Base-isomorphic full conditions have tail-equivalent coded orders**, the target form: each
coded order is tail-equivalent to the exterior order above the first block
(`Phase.tailEquivalent_exterior`), and the two exterior orders are tail-equivalent
(`Realization.baseEquivExteriorTailEquivalentTarget`, the first blocks being countably infinite
closed roots on an uncountable carrier); symmetry and transitivity of tail equivalence
conclude. -/
theorem tailEquivalentOfBaseEquivTarget : TailEquivalentOfBaseEquivTarget := by
  intro shape shape' req req' c c' hph hdom hph' hdom' he
  have hc := c.isCovering_real_of_dom_eq_univ hdom
  have hc' := c'.isCovering_real_of_dom_eq_univ hdom'
  have : Uncountable (ω₁ : Ordinal.{0}).ToType := uncountable_omegaOne
  obtain ⟨-, hBc, hBi, hB, -⟩ := omegaOneOrderReadingTarget shape req c hph hdom hc
  obtain ⟨-, hCc, hCi, hC, -⟩ := omegaOneOrderReadingTarget shape' req' c' hph' hdom' hc'
  have hext := baseEquivExteriorTailEquivalentTarget c.real c'.real c.isConsistent hc
    c'.isConsistent hc' c.hasLegalTypes c'.hasLegalTypes he hB hBi hBc hC hCi hCc
  have h₁ := tailEquivalent_exterior c hph hdom hc hB hBi
  have h₂ := tailEquivalent_exterior c' hph' hdom' hc' hC hCi
  have htrans := Order.tailEquivalentTransTarget.{0, 0, 0}
  have hsymm := Order.tailEquivalentSymmTarget.{0, 0}
  unfold Order.TailEquivalentTransTarget at htrans
  unfold Order.TailEquivalentSymmTarget at hsymm
  exact @htrans _ _ _ _ (c'.real.exteriorLinearOrder c'.isConsistent hc' hC hCi) _
    (@htrans _ _ _ _ (c.real.exteriorLinearOrder c.isConsistent hc hB hBi)
      (c'.real.exteriorLinearOrder c'.isConsistent hc' hC hCi) h₁ hext)
    (@hsymm _ _ _ (c'.real.exteriorLinearOrder c'.isConsistent hc' hC hCi) h₂)

/-- **Target: the base structure of a full condition determines its repeated code** (proved;
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

/-- **The base structure of a full condition determines its repeated code**, the target form: the
bit sequences of the shapes are `A ∘ r` and `A' ∘ r` (`Phase.shapeBitTarget`), their coded orders
are tail-equivalent (`Phase.tailEquivalentOfBaseEquivTarget`), and the parameter is recovered
(`CodedOrder.tailEquivalentInjectiveTarget`, countable sets of countable ordinals being bounded
above). -/
theorem codeEqOfBaseEquivTarget : CodeEqOfBaseEquivTarget.{w} := by
  intro J r hr A A' req req' c c' hph hdom hph' hdom' he
  have h := tailEquivalentOfBaseEquivTarget _ _ req req' c c' hph hdom hph' hdom' he
  have hb : ∀ B : J → Bool, shapeBits (BlockShape.ofBit ∘ B ∘ r) = B ∘ r :=
    fun B ↦ shapeBitTarget.{0}.2.2.2.2.1 (B ∘ r)
  rw [hb A, hb A'] at h
  exact CodedOrder.tailEquivalentInjectiveTarget (fun _ hs ↦ CodedOrder.omegaOne_bddAbove hs) hr
    A A' h

end VaughtConjecture.AlephOne.Phase

namespace VaughtConjecture.AlephOne

open Ordinal Realization FirstOrder Language InfinitaryLogic.ScottProcess.Semantic

/-! ### Existence statements -/

/-- **Target: `2 ^ ℵ₁` pairwise nonisomorphic models of cardinality `ℵ₁` and Scott rank `ω₁`, in
one Scott class** (proved; existence).  There is a family of structures of the base language on
infinite carriers in `Type`, indexed by the maps `ω₁ → Bool`, each satisfying the density
sentence, of cardinality `ℵ₁` and internal Scott rank `ω₁`, with semantic Scott process of rank
`ω₁` at every length beyond `ω₁ + 1`, all with the same semantic Scott process of every positive
length, such that the members at distinct indices are not isomorphic; the index set has
cardinality `2 ^ ℵ₁`. -/
def ExistsAlephOneFamilyScottRankTarget : Prop :=
  ∃ (M : ((ω₁ : Ordinal.{0}).ToType → Bool) → Type)
    (_ : ∀ A, baseLanguage.{0}.Structure (M A)) (_ : ∀ A, Infinite (M A)),
    (∀ A, Sentenceω.Realize baseLanguage.densitySentence.{0} (M A) ∧
      Cardinal.mk (M A) = Cardinal.aleph 1 ∧
      internalScottRank (L := baseLanguage.{0}) (M A) = (ω₁ : Ordinal.{0}) ∧
      ∀ ⦃δ : Ordinal.{0}⦄ (hδ : (ω₁ : Ordinal.{0}) + 1 < δ),
        (scottProcessOf baseLanguage.{0} (M A) δ (zero_le.trans_lt hδ)).IsRank ω₁) ∧
    (∀ A A' ⦃δ : Ordinal.{0}⦄ (hδ : 0 < δ),
      scottProcessOf baseLanguage.{0} (M A) δ hδ = scottProcessOf baseLanguage.{0} (M A') δ hδ) ∧
    (∀ A A', A ≠ A' → IsEmpty (M A ≃[baseLanguage.{0}] M A')) ∧
    Cardinal.mk ((ω₁ : Ordinal.{0}).ToType → Bool) = 2 ^ Cardinal.aleph 1

/-- **`2 ^ ℵ₁` pairwise nonisomorphic models of cardinality `ℵ₁` and Scott rank `ω₁`, in one Scott
class**, the target form.  Along a repetition scheme `r` on `ω₁`
(`CodedOrder.existsUnboundedFibresOmegaOneTarget`), the member at `A` is the base structure of a
full condition for the shapes `BlockShape.ofBit ∘ A ∘ r`, with a schedule serving every request,
whose realization is a receiving model with top-free types
(`Phase.existsFullPhaseReceivingModelTarget`).  Modelhood is
`AlephOne.realizeDensitySentenceTarget`, the cardinality `AlephOne.mk_carrier`, the ranks
`AlephOne.realizationScottRankOmegaOneOfModelTarget`, the common Scott process
`AlephOne.realizationsScottProcessEqOfModelTarget` (the form of
`AlephOne.realizationsScottProcessEqTarget` with the carriers' infinitude from the models), and
nonisomorphism `Phase.codeEqOfBaseEquivTarget`. -/
theorem existsAlephOneFamilyScottRankTarget : ExistsAlephOneFamilyScottRankTarget := by
  obtain ⟨r, hr⟩ := CodedOrder.existsUnboundedFibresOmegaOneTarget
  choose req hreq c hph hdom hrm htf using fun A : (ω₁ : Ordinal.{0}).ToType → Bool ↦
    Phase.existsFullPhaseReceivingModelTarget (Phase.BlockShape.ofBit ∘ A ∘ r)
  refine ⟨fun _ ↦ Carrier,
    fun A ↦ ((c A).real.reduce isSuccLimit_omega0.isSuccPrelimit).toStructure,
    fun A ↦ (hrm A).1.infinite (Ordinal.omega_pos 1), fun A ↦ ?_,
    fun A A' _ hδ ↦ realizationsScottProcessEqOfModelTarget (c A).real (c A').real (hrm A)
      (htf A) (hrm A') (htf A') hδ,
    fun A A' hne ↦ ⟨fun e ↦ hne (Phase.codeEqOfBaseEquivTarget r hr A A' (req A) (req A') (c A)
      (c A') (hph A) (hdom A) (hph A') (hdom A') ⟨e⟩)⟩, by simp⟩
  obtain ⟨hS, hP⟩ := realizationScottRankOmegaOneOfModelTarget (c A).real (hrm A) (htf A)
  exact ⟨realizeDensitySentenceTarget (c A).real (hrm A), mk_carrier,
    hS.trans (Ordinal.lift_id _), hP⟩

/-- **Target: `2 ^ ℵ₁` pairwise nonisomorphic models of the density sentence of cardinality `ℵ₁`**
(proved; existence).  There is a family of structures of the base language on carriers in `Type`,
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

/-- **`2 ^ ℵ₁` pairwise nonisomorphic models of the density sentence of cardinality `ℵ₁`**, the
target form: `AlephOne.existsAlephOneFamilyScottRankTarget` without the Scott conclusions. -/
theorem existsAlephOneFamilyTarget : ExistsAlephOneFamilyTarget := by
  obtain ⟨M, inst, _, hM, -, hne, hcard⟩ := existsAlephOneFamilyScottRankTarget
  exact ⟨M, inst, fun A ↦ ⟨(hM A).1, (hM A).2.1⟩, hne, hcard⟩

end VaughtConjecture.AlephOne
