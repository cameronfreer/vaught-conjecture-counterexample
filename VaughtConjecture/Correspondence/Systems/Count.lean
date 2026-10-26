/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Representation
import VaughtConjecture.Correspondence.Systems.RankBound
import VaughtConjecture.Counting.Separation

/-!
# [AFK26, Theorem 2.25 (a)] for an arbitrary qualifying system: the general count

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For a
qualifying system `W` (`QualifyingSystem D S E`, carriers in universe `0`), the isomorphism classes
of the base on the canonical carriers `Fin (n + 1)` and `ℕ` (`WeakSystem.BaseClasses`) are counted.
Finite carriers are counted with `ℕ`, by the same argument; no infiniteness is assumed.

**At most `ℵ₁`** (`QualifyingSystem.mk_baseClasses_le_aleph_one`), the printed route: the
representative of a class (`WeakSystem.baseClassRep`) is in the base, so by condition (a)
(`base_maximal`) it is the reduct of a structure `G` maximal at some level `δ`; by condition (b)
(`fewMaximal`) at `δ`, `G` is isomorphic to one of countably many representatives `H_δ i`, so the
class representative is isomorphic to the reduct of `H_δ i` (`BaseSublanguage.reductEquiv`).  At
most one class has a representative isomorphic to that reduct
(`WeakSystem.eq_of_equiv_baseClassRep`).  So the classes are covered by countable sets indexed by
the countable levels, and there are at most `ℵ₁` of them
(`Counting.mk_le_aleph_one_of_countable_cover`).  The finite carriers enter through the same
coverage: no count of finite models from the countability of the language is used.
-/

universe w w' wc wc'

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}
variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ}
variable {Lc : Language.{wc, wc'}} {E : σ.BaseSublanguage Lc}

namespace QualifyingSystem

/-! ### At most `ℵ₁` -/

/-- **[AFK26, Theorem 2.25 (a)], the upper bound, general form**: the base of a qualifying system
has at most `ℵ₁` isomorphism classes on the canonical carriers.  Each class representative is the
reduct of a structure maximal at some level `δ` (condition (a)), isomorphic to one of countably
many representatives at `δ` (condition (b)); at most one class arises from each representative
(`WeakSystem.eq_of_equiv_baseClassRep`), and the levels are countable ordinals
(`Counting.mk_le_aleph_one_of_countable_cover`).  Finite carriers included.  Correspondence with
the printed definitions. -/
theorem mk_baseClasses_le_aleph_one (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) :
    Cardinal.mk (W.toWeakSystem.BaseClasses E) ≤ Cardinal.aleph 1 := by
  choose ι hι C hC H hmax hrep using W.fewMaximal
  -- the classes whose representative is isomorphic to the reduct of `H δ i`
  let T (δ : SystemLevel) (i : ι δ) : Set (W.toWeakSystem.BaseClasses E) :=
    {x | Nonempty (@Language.Equiv Lc (W.toWeakSystem.baseClassCarrier E x) (C δ i)
      (W.toWeakSystem.baseClassRep E x) (E.reduct (H δ i)))}
  have hT (δ : SystemLevel) (i : ι δ) : (T δ i).Subsingleton := by
    rintro x ⟨g⟩ y ⟨g'⟩
    exact W.toWeakSystem.eq_of_equiv_baseClassRep E
      ⟨@Language.Equiv.comp Lc _ (C δ i) (W.toWeakSystem.baseClassRep E x) (E.reduct (H δ i)) _
        (W.toWeakSystem.baseClassRep E y)
        (@Language.Equiv.symm Lc _ (C δ i) (W.toWeakSystem.baseClassRep E y) (E.reduct (H δ i))
          g') g⟩
  let Q (a : Ordinal.{0}) : Set (W.toWeakSystem.BaseClasses E) :=
    ⋃ (h : a < ω₁), ⋃ i : ι ⟨a, h⟩, T ⟨a, h⟩ i
  refine Counting.mk_le_aleph_one_of_countable_cover (Q := Q) (fun a ha ↦ ?_) fun x ↦ ?_
  · have := hι ⟨a, ha⟩
    exact Set.countable_iUnion fun h ↦ Set.countable_iUnion fun i ↦ (hT ⟨a, h⟩ i).countable
  · obtain ⟨G, ⟨δ, hGmax⟩, hGx⟩ := W.base_maximal _ (W.toWeakSystem.baseClassRep E x)
      (W.toWeakSystem.isInBase_baseClassRep E x)
    obtain ⟨i, ⟨g⟩⟩ := hrep δ _ G hGmax
    have hx : x ∈ T δ i := by
      change Nonempty (@Language.Equiv Lc _ (C δ i) (W.toWeakSystem.baseClassRep E x)
        (E.reduct (H δ i)))
      rw [← hGx]
      exact ⟨E.reductEquiv g⟩
    exact ⟨δ.1, δ.2, Set.mem_iUnion.mpr ⟨δ.2, Set.mem_iUnion.mpr ⟨i, hx⟩⟩⟩

end QualifyingSystem

end VaughtConjecture.Correspondence
