/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Maximality
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

**The rank bound is transported along base isomorphisms**
(`WeakSystem.isFixedAt_of_isLiftAt_of_equiv`,
`WeakSystem.forall_isLiftAt_isFixedAt_iff_of_equiv`):
if `B ≅ B'` as `L_c`-structures (on countable carriers) and every lift of `B'` is fixed at `α`, then
every lift of `B` is fixed at `α`.  A lift `G` of `B` at `β` is carried along the bijection to a
lift of `B'` at `β` (`WeakSystem.isoClosed`, `BaseSublanguage.reduct_inducedStructure`), which is
fixed at `α`; projection commutes with the transport
(`InvariantSystem.projection_inducedStructure`), and transporting back recovers `G`.

**At least `ℵ₁`** (`QualifyingSystem.aleph_one_le_mk_baseClasses`), the printed route: if the
classes were countably many, the bounds `α_x` of Lemma 2.22 for their representatives
(`WeakSystem.existsRankBoundTarget`, from condition (c), `eventuallyDetermined`) would have a
countable supremum `α*`.  Some invariant `Q` is not fixed by `τ_α*` (`InvariantSystem.ne_univ`); by
condition (d) (`invariant_occurs`) it holds of a tuple of some `G ∈ K_β` on a countable nonempty
carrier.  The reduct of `G` is in the base, so isomorphic to the representative of a class `y`
(`WeakSystem.exists_equiv_baseClassRep`); every lift of that representative is fixed at
`α_y ≤ α*`, so by the transport `G` is fixed at `α*`.  Then `Q` holds in `τ_α*(G)`, so it is
`τ_α*(Q')` for an invariant `Q'` (`InvariantSystem.relMap_projection_of_isInvariant`), and
`τ_α*(Q) = τ_α*(τ_α*(Q')) = Q` (`InvariantSystem.comp`): a contradiction.  The member `G` of
condition (d) may live on a finite carrier; it is moved to `Fin (n + 1)` or `ℕ` by
`WeakSystem.exists_equiv_baseClassRep`, with no infiniteness.

**Exactly `ℵ₁`** (`QualifyingSystem.mkBaseClassesEqAlephOneTarget`,
`QualifyingSystem.MkBaseClassesEqAlephOneTarget`): the two bounds.

No uniqueness of maximal lifts, Reconstruction or canonical maximal-stage rank is used.
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

/-! ### Transport of the rank bound along base isomorphisms -/

namespace WeakSystem

variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-- **The rank bound is transported along a base isomorphism**: if `g : B ≅ B'` is an isomorphism
of `L_c`-structures, the carrier of `B'` is countable, and every lift of `B'` (at any level) is
fixed at `α`, then every lift of `B` is fixed at `α`.  The lift `G` of `B` is carried along the
bijection of `g` to a lift of `B'` (`WeakSystem.isoClosed`,
`BaseSublanguage.reduct_inducedStructure`, `BaseSublanguage.eq_inducedStructure_of_equiv`), which
is fixed at `α`; projection commutes with the transport
(`InvariantSystem.projection_inducedStructure`), and transporting back recovers `G`
(`GeometrySignature.inducedStructure_symm_inducedStructure`).  Correspondence with the printed
definitions. -/
theorem isFixedAt_of_isLiftAt_of_equiv.{v} (W : WeakSystem.{w, w', v} D S) {α β : SystemLevel}
    {M N : Type v} [Countable N] {B : Lc.Structure M} {B' : Lc.Structure N}
    (g : @Language.Equiv Lc M N B B')
    (h : ∀ (β' : SystemLevel) (G' : L.Structure N), W.IsLiftAt E β' G' B' → S.IsFixedAt α G')
    {G : L.Structure M} (hG : W.IsLiftAt E β G B) : S.IsFixedAt α G := by
  let e : M ≃ N := @Language.Equiv.toEquiv Lc M N B B' g
  have hG' : W.IsLiftAt E β (@Equiv.inducedStructure L M N G e) B' := by
    refine ⟨W.isoClosed hG.1 ⟨@Equiv.inducedStructureEquiv L M N G e⟩, ?_⟩
    rw [E.reduct_inducedStructure, hG.2]
    exact (E.eq_inducedStructure_of_equiv g).symm
  have hfix := h β _ hG'
  unfold InvariantSystem.IsFixedAt at hfix ⊢
  rw [← σ.inducedStructure_symm_inducedStructure G e, S.projection_inducedStructure, hfix]

/-- **The rank bound is invariant under base isomorphism**, on countable carriers: for `B ≅ B'`,
every lift of `B` is fixed at `α` exactly when every lift of `B'` is
(`isFixedAt_of_isLiftAt_of_equiv` both ways).  Correspondence with the printed definitions. -/
theorem forall_isLiftAt_isFixedAt_iff_of_equiv.{v} (W : WeakSystem.{w, w', v} D S)
    {α : SystemLevel} {M N : Type v} [Countable M] [Countable N] {B : Lc.Structure M}
    {B' : Lc.Structure N} (g : @Language.Equiv Lc M N B B') :
    (∀ (β : SystemLevel) (G : L.Structure M), W.IsLiftAt E β G B → S.IsFixedAt α G) ↔
      ∀ (β : SystemLevel) (G' : L.Structure N), W.IsLiftAt E β G' B' → S.IsFixedAt α G' :=
  ⟨fun h _ _ hG' ↦ W.isFixedAt_of_isLiftAt_of_equiv E (@Language.Equiv.symm Lc M N B B' g) h hG',
    fun h _ _ hG ↦ W.isFixedAt_of_isLiftAt_of_equiv E g h hG⟩

end WeakSystem

namespace QualifyingSystem

/-! ### At least `ℵ₁` -/

/-- **[AFK26, Theorem 2.25 (a)], the lower bound, general form**: the base of a qualifying system
has at least `ℵ₁` isomorphism classes on the canonical carriers.  If they were countably many, the
bounds of Lemma 2.22 for the class representatives (`WeakSystem.existsRankBoundTarget`, condition
(c)) would have a countable supremum `α*`; an invariant `Q` not fixed by `τ_α*`
(`InvariantSystem.ne_univ`) holds in some `G ∈ K_β` on a countable nonempty carrier (condition
(d)); the reduct of `G` is isomorphic to a class representative
(`WeakSystem.exists_equiv_baseClassRep`), so `G` is fixed at `α*`
(`WeakSystem.isFixedAt_of_isLiftAt_of_equiv`), and then `Q` is in the image of `τ_α*`, hence fixed
by it (`InvariantSystem.comp`).  No infiniteness.  Correspondence with the printed
definitions. -/
theorem aleph_one_le_mk_baseClasses (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) :
    Cardinal.aleph 1 ≤ Cardinal.mk (W.toWeakSystem.BaseClasses E) := by
  refine Cardinal.aleph_one_le_iff.mpr (lt_of_not_ge fun hle ↦ ?_)
  have := Cardinal.mk_le_aleph0_iff.mp hle
  -- Lemma 2.22 for each class representative
  have hbound (x : W.toWeakSystem.BaseClasses E) : ∃ α : SystemLevel,
      ∀ (β : SystemLevel) (G : L.Structure (W.toWeakSystem.baseClassCarrier E x)),
        W.IsLiftAt E β G (W.toWeakSystem.baseClassRep E x) → S.IsFixedAt α G :=
    W.toWeakSystem.existsRankBoundTarget E _ _
      (W.eventuallyDetermined _ _ (W.toWeakSystem.isInBase_baseClassRep E x))
  choose α hα using hbound
  -- the supremum of the bounds is countable
  have hsup : (⨆ x, ((α x).1 + 1)) < ω₁ :=
    InfinitaryLogic.iSup_add_one_lt_omega1 (fun x ↦ (α x).1) fun x ↦ (α x).2
  let αs : SystemLevel := ⟨⨆ x, ((α x).1 + 1), hsup⟩
  have hle (x : W.toWeakSystem.BaseClasses E) : α x ≤ αs :=
    show (α x).1 ≤ ⨆ x, ((α x).1 + 1) from
      (Order.lt_add_one_iff.mpr le_rfl).le.trans (Ordinal.le_iSup (fun x ↦ (α x).1 + 1) x)
  -- an invariant not fixed at the supremum
  obtain ⟨⟨n, Q⟩, hQ⟩ : ∃ Q : Σ n, σ.Invariant n, S.τ αs Q.2 ≠ Q.2 := by
    by_contra h
    exact S.ne_univ αs (Set.eq_univ_of_forall fun Q ↦ by_contra fun hQ ↦ h ⟨Q, hQ⟩)
  -- it occurs in a member of `K`, whose reduct is isomorphic to a class representative
  obtain ⟨M, _, _, β, G, hG, a, ha⟩ := W.invariant_occurs Q
  obtain ⟨y, ⟨g⟩⟩ := W.toWeakSystem.exists_equiv_baseClassRep E M (E.reduct G) ⟨β, G, hG, rfl⟩
  have hfix : S.IsFixedAt αs G :=
    W.toWeakSystem.isFixedAt_of_isLiftAt_of_equiv E g
      (fun β' G' hG' ↦ (hα y β' G' hG').mono (hle y)) ⟨hG, rfl⟩
  have ha' : RelMap (L := L) (self := S.projection αs G) Q.1 a := by
    rw [hfix]
    exact ha
  obtain ⟨Q', hQ', -⟩ := (S.relMap_projection_of_isInvariant αs G Q.2 a).mp ha'
  have hQQ' : S.τ αs Q' = Q := Subtype.ext hQ'
  exact hQ (by rw [← hQQ', (S.comp le_rfl Q').1])

/-- **[AFK26, Theorem 2.25 (a)], general form** (`MkBaseClassesEqAlephOneTarget`): the base of a
qualifying system has exactly `ℵ₁` isomorphism classes on the canonical carriers `Fin (n + 1)` and
`ℕ`, finite members counted with the others and no infiniteness assumed
(`mk_baseClasses_le_aleph_one`, `aleph_one_le_mk_baseClasses`).  Correspondence with the printed
definitions. -/
theorem mkBaseClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) :
    W.MkBaseClassesEqAlephOneTarget :=
  le_antisymm W.mk_baseClasses_le_aleph_one W.aleph_one_le_mk_baseClasses

end QualifyingSystem

end VaughtConjecture.Correspondence
