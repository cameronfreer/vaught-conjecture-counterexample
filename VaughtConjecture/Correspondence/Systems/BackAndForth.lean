/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.Systems.Projection
import VaughtConjecture.Correspondence.Systems.Targets

/-!
# [AFK26, Proposition 2.18] for an arbitrary weak system

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  For a weak
system `W` (`WeakSystem D S`), members `G ∈ K_β` on `M` and `H ∈ K_β` on `N` with `M` and `N`
countable, and a base sublanguage `E`, this file compares tuples pattern-matched at a level
`ι ≤ β` (`InvariantSystem.IsPatternMatchedAt`) with InfinitaryLogic's `BFEquiv ι` of the reducts
`E.reduct G` and `E.reduct H`.  Levels are system levels (`SystemLevel`) throughout.

**Matching descends to lower levels** (no density):

* `InvariantSystem.relMap_projection_τ_of_le`: if `τ_ι(G) ⊨ Q(a)` and `ι' ≤ ι`, then
  `τ_ι'(G) ⊨ τ_ι'(Q)(a)` (`τ_ι' ∘ τ_ι = τ_ι'` on structures and on invariants);
* `InvariantSystem.IsMatchedAt.mono`, `InvariantSystem.IsPatternMatchedAt.mono`: matching at `ι`
  gives matching at every `ι' ≤ ι`, with the invariant `τ_ι'(Q)` and the same tuples;
* `InvariantSystem.IsMatchedAt.symm`, `InvariantSystem.IsPatternMatchedAt.symm`: the roles of the
  two structures exchanged.

**Atomic agreement**:

* `WeakSystem.projection_mem_of_le`: for `ι ≤ β` and `G ∈ K_β` on a countable carrier,
  `τ_ι(G) ∈ K_ι` (`WeakSystem.projection_mem` for `ι < β`, `WeakSystem.fixed` for `ι = β`), so
  `τ_ι(G)` is compatible with `D` (`WeakSystem.isCompatible_projection_of_le`);
* `InvarianceDiagram.IsCompatible.relMap_comp_iff`: in two structures compatible with `D`, tuples
  `a` and `b` with one common invariant `Q` satisfy the same relations along every sequence of
  places (for each `R` and `j` exactly one of `(Q(x), R(x_j))`, `(Q(x), ¬R(x_j))` is a pair of
  `D`, and both structures satisfy the pairs);
* `InvarianceDiagram.IsCompatible.injective_of_relMap_invariant`: a tuple with an invariant is
  injective ([AFK26, Definition 2.2 (b)] and the first clause of Definition 2.1);
* `WeakSystem.eq_iff_of_isPatternMatchedAt` (repeated entries: `x i = x j ↔ y i = y j`, since
  `x = a ∘ f`, `y = b ∘ f` with `a` and `b` injective) and
  `WeakSystem.relMap_reduct_iff_of_isPatternMatchedAt` (a symbol of `L_c` along a sequence of places
  `g` holds of `x ∘ g` in `G↾L_c` exactly when it holds of `y ∘ g` in `H↾L_c`; `τ_ι` does not change
  it);
* `WeakSystem.sameAtomicType_of_isPatternMatchedAt`: `SameAtomicType` of `x` and `y` in the
  reducts, for tuples pattern-matched at any `ι ≤ β`.
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

/-- **An atomic formula `R(x_j)` holds of `x` exactly when `R` holds of `x ∘ j`.**  Correspondence
with the printed definitions. -/
theorem realize_atom_iff {M : Type v} [L.Structure M] {n k : ℕ} (R : L.Relations k)
    (j : Fin k → Fin n) (x : Fin n → M) : (atom R j).Realize x ↔ RelMap R (x ∘ j) := by
  simp only [atom, Formula.realize_rel, Term.realize_var]
  rfl

/-! ### Matching descends to lower levels -/

namespace InvariantSystem

variable {S : InvariantSystem.{0} σ}

/-- **An invariant of a projection descends**: if `τ_ι(G) ⊨ Q(a)` and `ι' ≤ ι`, then
`τ_ι'(G) ⊨ τ_ι'(Q)(a)`.  Correspondence with the printed definitions. -/
theorem relMap_projection_τ_of_le {ι ι' : SystemLevel} (h : ι' ≤ ι) {M : Type v}
    (G : L.Structure M) {n : ℕ} (Q : σ.Invariant n) {a : Fin n → M}
    (ha : RelMap (L := L) (self := S.projection ι G) Q.1 a) :
    RelMap (L := L) (self := S.projection ι' G) (S.τ ι' Q).1 a := by
  rw [← S.projection_projection_of_le h G]
  exact (S.relMap_projection_of_isInvariant ι' (S.projection ι G) (S.τ ι' Q).2 a).mpr
    ⟨Q, rfl, ha⟩

/-- **Matching descends to lower levels**: tuples matched at `ι` by `Q` are matched at every
`ι' ≤ ι` by `τ_ι'(Q)`.  Correspondence with the printed definitions. -/
theorem IsMatchedAt.mono {ι ι' : SystemLevel} (h : ι' ≤ ι) {M N : Type v} {G : L.Structure M}
    {H : L.Structure N} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hm : S.IsMatchedAt ι G H a b) : S.IsMatchedAt ι' G H a b := by
  obtain ⟨Q, ha, hb⟩ := hm
  exact ⟨S.τ ι' Q, relMap_projection_τ_of_le h G Q ha, relMap_projection_τ_of_le h H Q hb⟩

/-- **Pattern matching descends to lower levels**: the same tuples and map of positions, with the
matching of `IsMatchedAt.mono`.  Correspondence with the printed definitions. -/
theorem IsPatternMatchedAt.mono {ι ι' : SystemLevel} (h : ι' ≤ ι) {M N : Type v}
    {G : L.Structure M} {H : L.Structure N} {n : ℕ} {x : Fin n → M} {y : Fin n → N}
    (hm : S.IsPatternMatchedAt ι G H x y) : S.IsPatternMatchedAt ι' G H x y := by
  obtain ⟨k, a, b, f, hx, hy, hab⟩ := hm
  exact ⟨k, a, b, f, hx, hy, hab.mono h⟩

/-- **Matching is symmetric**: the same invariant, the roles of `G` and `H` exchanged.
Correspondence with the printed definitions. -/
theorem IsMatchedAt.symm {ι : SystemLevel} {M N : Type v} {G : L.Structure M}
    {H : L.Structure N} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hm : S.IsMatchedAt ι G H a b) : S.IsMatchedAt ι H G b a := by
  obtain ⟨Q, ha, hb⟩ := hm
  exact ⟨Q, hb, ha⟩

/-- **Pattern matching is symmetric**: the same witnesses, the roles of `G` and `H` exchanged.
Correspondence with the printed definitions. -/
theorem IsPatternMatchedAt.symm {ι : SystemLevel} {M N : Type v} {G : L.Structure M}
    {H : L.Structure N} {n : ℕ} {x : Fin n → M} {y : Fin n → N}
    (hm : S.IsPatternMatchedAt ι G H x y) : S.IsPatternMatchedAt ι H G y x := by
  obtain ⟨k, a, b, f, hx, hy, hab⟩ := hm
  exact ⟨k, b, a, f, hy, hx, hab.symm⟩

end InvariantSystem

/-! ### Compatible structures -/

namespace InvarianceDiagram.IsCompatible

variable {D : InvarianceDiagram σ}

/-- **A tuple with an invariant is injective** in a structure compatible with `D`: the invariant
gives `P_n` ([AFK26, Definition 2.2 (b)]), which holds only of tuples of distinct points (the
first clause of [AFK26, Definition 2.1]).  Correspondence with the printed definitions. -/
theorem injective_of_relMap_invariant {M : Type v} {G : L.Structure M}
    (hG : @InvarianceDiagram.IsCompatible L σ D M G) {n : ℕ} (Q : σ.Invariant n) {a : Fin n → M}
    (ha : RelMap (L := L) (self := G) Q.1 a) : Function.Injective a := by
  have hn := σ.pos_of_relations Q.1
  exact hG.isStructuredGeometry.isGeometry.injective hn a
    ((hG.isStructuredGeometry.closed_iff hn a).mpr ⟨Q.1, Q.2, ha⟩)

/-- **One invariant determines the relations along every sequence of places, across two
structures**: if `G` and `H` are compatible with `D`, `G ⊨ Q(a)` and `H ⊨ Q(b)`, then
`G ⊨ R(a ∘ j)` exactly when `H ⊨ R(b ∘ j)`, for every symbol `R` and sequence `j`.  Exactly one of
`(Q(x), R(x_j))` and `(Q(x), ¬R(x_j))` is a pair of `D` (the second clause of
[AFK26, Definition 2.4]), and both structures satisfy the pairs.  Correspondence with the printed
definitions. -/
theorem relMap_comp_iff {M N : Type v} {G : L.Structure M} {H : L.Structure N}
    (hG : @InvarianceDiagram.IsCompatible L σ D M G)
    (hH : @InvarianceDiagram.IsCompatible L σ D N H) {n : ℕ} (Q : σ.Invariant n)
    {a : Fin n → M} {b : Fin n → N} (ha : RelMap (L := L) (self := G) Q.1 a)
    (hb : RelMap (L := L) (self := H) Q.1 b) {k : ℕ} (R : L.Relations k) (j : Fin k → Fin n) :
    RelMap (L := L) (self := G) R (a ∘ j) ↔ RelMap (L := L) (self := H) R (b ∘ j) := by
  rcases (D.exactlyOne Q.1 R j Q.2).or with h | h
  · exact iff_of_true ((@realize_atom_iff L M G n k R j a).mp (hG.satisfiesPairs _ h a ha))
      ((@realize_atom_iff L N H n k R j b).mp (hH.satisfiesPairs _ h b hb))
  · exact iff_of_false
      (fun h' ↦ (@Formula.realize_not L M G _ _ _).mp (hG.satisfiesPairs _ h a ha)
        ((@realize_atom_iff L M G n k R j a).mpr h'))
      (fun h' ↦ (@Formula.realize_not L N H _ _ _).mp (hH.satisfiesPairs _ h b hb)
        ((@realize_atom_iff L N H n k R j b).mpr h'))

end InvarianceDiagram.IsCompatible

/-! ### Atomic agreement -/

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ} (W : WeakSystem.{w, w', v} D S)
variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-- **Projection to a level at most `β`**: for `G ∈ K_β` on a countable carrier and `ι ≤ β`,
`τ_ι(G) ∈ K_ι` (`projection_mem` for `ι < β`; for `ι = β`, `τ_β(G) = G` by `fixed`).
Correspondence with the printed definitions. -/
theorem projection_mem_of_le {β ι : SystemLevel} (h : ι ≤ β) {M : Type v} [Countable M]
    {G : L.Structure M} (hG : G ∈ W.K β M) : S.projection ι G ∈ W.K ι M := by
  rcases h.lt_or_eq with h | rfl
  · exact W.projection_mem h hG
  · rw [W.fixed hG]
    exact hG

/-- **The projection to a level at most `β` is compatible with `D`** (`projection_mem_of_le` and
`isCompatible`).  Correspondence with the printed definitions. -/
theorem isCompatible_projection_of_le {β ι : SystemLevel} (h : ι ≤ β) {M : Type v}
    [Countable M] {G : L.Structure M} (hG : G ∈ W.K β M) :
    @InvarianceDiagram.IsCompatible L σ D M (S.projection ι G) :=
  W.isCompatible (W.projection_mem_of_le h hG)

variable {W}

/-- **Repeated entries agree** for tuples pattern-matched at a level `ι ≤ β`: `x i = x j` exactly
when `y i = y j`.  With `x = a ∘ f`, `y = b ∘ f` and `a`, `b` carrying one invariant in the
compatible structures `τ_ι(G)` and `τ_ι(H)`, both `a` and `b` are injective
(`InvarianceDiagram.IsCompatible.injective_of_relMap_invariant`), so both sides say `f i = f j`.
Correspondence with the printed definitions. -/
theorem eq_iff_of_isPatternMatchedAt {M N : Type v} [Countable M] [Countable N] {β : SystemLevel}
    {G : L.Structure M} {H : L.Structure N} (hG : G ∈ W.K β M) (hH : H ∈ W.K β N)
    {ι : SystemLevel} (hι : ι ≤ β) {n : ℕ} {x : Fin n → M} {y : Fin n → N}
    (hm : S.IsPatternMatchedAt ι G H x y) (i j : Fin n) : x i = x j ↔ y i = y j := by
  obtain ⟨k, a, b, f, rfl, rfl, Q, ha, hb⟩ := hm
  simp only [Function.comp_apply]
  rw [((W.isCompatible_projection_of_le hι hG).injective_of_relMap_invariant Q ha).eq_iff,
    ((W.isCompatible_projection_of_le hι hH).injective_of_relMap_invariant Q hb).eq_iff]

/-- **Symbols of `L_c` agree** for tuples pattern-matched at a level `ι ≤ β`: for a symbol `r` of
`L_c` and a sequence of places `g`, `G↾L_c ⊨ r(x ∘ g)` exactly when `H↾L_c ⊨ r(y ∘ g)`.  The image
of `r` is not an invariant, so `τ_ι` does not change it; `τ_ι(G)` and `τ_ι(H)` are compatible
with `D`, and `x ∘ g = a ∘ (f ∘ g)`, `y ∘ g = b ∘ (f ∘ g)`
(`InvarianceDiagram.IsCompatible.relMap_comp_iff`).  Correspondence with the printed
definitions. -/
theorem relMap_reduct_iff_of_isPatternMatchedAt {M N : Type v} [Countable M] [Countable N]
    {β : SystemLevel} {G : L.Structure M} {H : L.Structure N} (hG : G ∈ W.K β M)
    (hH : H ∈ W.K β N) {ι : SystemLevel} (hι : ι ≤ β) {n : ℕ} {x : Fin n → M} {y : Fin n → N}
    (hm : S.IsPatternMatchedAt ι G H x y) {l : ℕ} (r : Lc.Relations l) (g : Fin l → Fin n) :
    RelMap (L := Lc) (self := E.reduct G) r (x ∘ g) ↔
      RelMap (L := Lc) (self := E.reduct H) r (y ∘ g) := by
  obtain ⟨k, a, b, f, rfl, rfl, Q, ha, hb⟩ := hm
  have hr := E.not_isInvariant_incl r
  change RelMap (L := L) (self := G) (E.incl.onRelation r) (a ∘ f ∘ g) ↔
    RelMap (L := L) (self := H) (E.incl.onRelation r) (b ∘ f ∘ g)
  rw [← S.relMap_projection_of_not_isInvariant ι G hr,
    ← S.relMap_projection_of_not_isInvariant ι H hr]
  exact (W.isCompatible_projection_of_le hι hG).relMap_comp_iff
    (W.isCompatible_projection_of_le hι hH) Q ha hb _ (f ∘ g)

/-- **Atomic agreement** for tuples pattern-matched at a level `ι ≤ β`: `x` and `y` have the same
atomic type in the reducts `G↾L_c` and `H↾L_c` (InfinitaryLogic's `SameAtomicType`: the equality
indices by `eq_iff_of_isPatternMatchedAt`, repeated entries included; the relation indices by
`relMap_reduct_iff_of_isPatternMatchedAt`).  Correspondence with the printed definitions. -/
theorem sameAtomicType_of_isPatternMatchedAt {M N : Type v} [Countable M] [Countable N]
    {β : SystemLevel} {G : L.Structure M} {H : L.Structure N} (hG : G ∈ W.K β M)
    (hH : H ∈ W.K β N) {ι : SystemLevel} (hι : ι ≤ β) {n : ℕ} {x : Fin n → M} {y : Fin n → N}
    (hm : S.IsPatternMatchedAt ι G H x y) :
    @SameAtomicType Lc M (E.reduct G) n N (E.reduct H) x y := by
  intro idx
  cases idx with
  | eq i j => exact eq_iff_of_isPatternMatchedAt hG hH hι hm i j
  | rel r g => exact relMap_reduct_iff_of_isPatternMatchedAt E hG hH hι hm r g

end WeakSystem

end VaughtConjecture.Correspondence
