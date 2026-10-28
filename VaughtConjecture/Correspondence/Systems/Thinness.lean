/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.BFClasses

/-!
# [AFK26, Theorem 2.25 (b)] for an arbitrary qualifying system

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For a
qualifying system `W` (`QualifyingSystem D S E`) and a qualifying sentence `φ`
(`QualifyingSystem.IsQualifyingSentence`, coded on `ℕ`):

* `QualifyingSystem.countableClassesWithoutLiftTarget`
  (`QualifyingSystem.CountableClassesWithoutLiftTarget`): for every countable `β`, the coded
  classes with a member without a lift at `β` are countably many.  A code `c` without a lift at `β`
  is a model of `φ`, so in the base; by condition (a) (`base_maximal`) it is the reduct of a
  structure `G` maximal at some level `δ`.  Then `δ < β`: otherwise `τ_β(G)` would be a lift of `c`
  at `β` (`WeakSystem.projection_mem_of_le`, `BaseSublanguage.reduct_projection`).  By condition (b)
  (`fewMaximal`) at `δ`, `G` is isomorphic to one of countably many representatives `H_δ i`, so
  `c` is isomorphic to the reduct of `H_δ i` (`BaseSublanguage.reductEquiv`); for each pair
  `(δ, i)` at most one coded class arises, and the pairs with `δ < β` are countably many
  (`Cardinal.countable_Iio_of_lt_omega_one`).
* `QualifyingSystem.noPerfectSetTarget` (`QualifyingSystem.NoPerfectSetTarget`,
  [AFK26, Theorem 2.25 (b)], coded): no perfect set of pairwise nonisomorphic models of `φ` coded
  on `ℕ` (`noPerfectSetTarget_of_thinnessTarget` with Theorem 2.19, `WeakSystem.thinnessTarget`).

The qualifying-system conditions used are (a) and (b); conditions (c) and (d) are not used.
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}
variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ}
variable {Lc : Language.{wc, wc'}} {E : σ.BaseSublanguage Lc}

namespace QualifyingSystem

/-- **The levels below a countable level are countably many**
(`Cardinal.countable_Iio_of_lt_omega_one` along the injective inclusion of `SystemLevel` into the
ordinals).  Correspondence with the printed definitions. -/
theorem countable_setOf_lt (β : SystemLevel) : {δ : SystemLevel | δ < β}.Countable :=
  (Cardinal.countable_Iio_of_lt_omega_one β.2).preimage Subtype.val_injective

variable [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)]

/-- **The countable part `A_β`** (`CountableClassesWithoutLiftTarget`, proof of
[AFK26, Theorem 2.25 (b)], coded): for a qualifying sentence `φ` and a countable `β`, the coded
classes with a member without a lift at `β` are countably many.  Such a member `c` is the reduct of
a structure `G` maximal at some `δ` (condition (a), `base_maximal`); `δ < β`, since otherwise
`τ_β(G)` is a lift of `c` at `β` (`WeakSystem.projection_mem_of_le`,
`BaseSublanguage.reduct_projection`).  By condition (b) (`fewMaximal`) at `δ`, `G` is isomorphic to
a representative `H_δ i`, and then `c` to its reduct (`BaseSublanguage.reductEquiv`): the class of
`c` is the only coded class isomorphic to that reduct.  Countably many `δ < β`
(`countable_setOf_lt`) and countably many `i` for each.  Correspondence with the printed
definitions. -/
theorem countableClassesWithoutLiftTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : W.CountableClassesWithoutLiftTarget φ := by
  intro hφ β
  choose ι hι C hC H hmax hrep using W.fewMaximal
  -- the coded classes isomorphic to the reduct of the representative `H δ i`
  let T (δ : SystemLevel) (i : ι δ) : Set (Quotient (isoSetoid φ)) :=
    {q | ∃ c : ModelsOf φ, Quotient.mk (isoSetoid φ) c = q ∧
      Nonempty (@Language.Equiv Lc ℕ (C δ i) c.1.toStructure (E.reduct (H δ i)))}
  have hT (δ : SystemLevel) (i : ι δ) : (T δ i).Countable := by
    refine Set.Subsingleton.countable ?_
    rintro _ ⟨c, rfl, ⟨g⟩⟩ _ ⟨c', rfl, ⟨g'⟩⟩
    exact Quotient.sound ⟨@Language.Equiv.comp Lc ℕ (C δ i) c.1.toStructure
      (E.reduct (H δ i)) ℕ c'.1.toStructure
      (@Language.Equiv.symm Lc ℕ (C δ i) c'.1.toStructure (E.reduct (H δ i)) g') g⟩
  have hU : (⋃ δ ∈ {δ : SystemLevel | δ < β}, ⋃ i : ι δ, T δ i).Countable :=
    (countable_setOf_lt β).biUnion fun δ _ ↦ by
      have := hι δ
      exact Set.countable_iUnion fun i ↦ hT δ i
  refine hU.mono ?_
  rintro q ⟨c, rfl, hno⟩
  obtain ⟨G, ⟨δ, hGmax⟩, hGc⟩ := W.base_maximal ℕ c.1.toStructure ((hφ c.1).mp c.2)
  have hδ : δ < β := by
    by_contra hle
    exact hno (S.projection β G)
      ⟨W.toWeakSystem.projection_mem_of_le (not_lt.mp hle) hGmax.1,
        by rw [E.reduct_projection, hGc]⟩
  obtain ⟨i, ⟨g⟩⟩ := hrep δ ℕ G hGmax
  have hc : Nonempty (@Language.Equiv Lc ℕ (C δ i) c.1.toStructure (E.reduct (H δ i))) := by
    rw [← hGc]
    exact ⟨E.reductEquiv g⟩
  exact Set.mem_biUnion hδ (Set.mem_iUnion.mpr ⟨i, c, rfl, hc⟩)

/-- **[AFK26, Theorem 2.25 (b)], coded** (`NoPerfectSetTarget`): for a qualifying sentence `φ`,
there is no perfect set of pairwise nonisomorphic models of `φ` coded on `ℕ`.  Theorem 2.19
(`WeakSystem.thinnessTarget`) with the countable part (`countableClassesWithoutLiftTarget`), by
`noPerfectSetTarget_of_thinnessTarget`.  No infiniteness premise.  Correspondence with the printed
definitions. -/
theorem noPerfectSetTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : W.NoPerfectSetTarget φ :=
  noPerfectSetTarget_of_thinnessTarget (W.toWeakSystem.thinnessTarget E φ)
    (W.countableClassesWithoutLiftTarget φ)

end QualifyingSystem

end VaughtConjecture.Correspondence
