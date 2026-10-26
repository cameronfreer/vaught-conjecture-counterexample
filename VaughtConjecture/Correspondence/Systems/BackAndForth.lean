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

**Forth and back**, for levels `ι < ι₁ ≤ β` (BFEquiv's successor clause uses `ι₁ = ι + 1`):

* `InvarianceDiagram.IsCompatible.exists_extension`: in a structure compatible with `D`, a tuple
  `a` with an invariant `Q` and a point `c` not among its entries extend to a tuple `w` with an
  invariant `P`, `a` kept literally and `c` at one new place, with `(P(x̄ ȳ), Q(x̄))` a pair of `D`;
* `WeakSystem.forth_of_isPatternMatchedAt`: tuples pattern-matched at `ι₁` extend, by any point
  of `M` and a suitable point of `N`, to tuples pattern-matched at `ι`.  An entry of the
  witnessing tuple is answered by the corresponding entry; a genuinely new point by `ι`-density
  of `τ_ι₁(H) ∈ K_ι₁` (`WeakSystem.dense`, `WeakSystem.projection_mem_of_le`);
* `WeakSystem.back_of_isPatternMatchedAt`: the same, by any point of `N`, by symmetry.
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

/-! ### Forth and back -/

/-- **An invariant along an equality of arities**: an invariant holding of `z` on `n` places gives
an invariant holding of `z ∘ Fin.cast e.symm` on `n'` places, for `e : n = n'`.  Native
construction. -/
theorem exists_relMap_invariant_cast {M : Type v}
    {G : L.Structure M} {n n' : ℕ} (e : n = n') (P : σ.Invariant n) {z : Fin n → M}
    (hz : RelMap (L := L) (self := G) P.1 z) :
    ∃ P' : σ.Invariant n', RelMap (L := L) (self := G) P'.1 (z ∘ Fin.cast e.symm) := by
  subst e
  exact ⟨P, hz⟩

/-- **The closed extension of a tuple with an invariant by a new point**: in a structure `G'`
compatible with `D`, if `G' ⊨ Q(a)` and `c` is not an entry of `a`, there are `l`, a tuple `w` on
`k + (l + 1)` places extending `a` literally (`w ∘ Fin.castAdd (l + 1) = a`) with `c` at the place
`Fin.natAdd k 0`, and an invariant `P` with `G' ⊨ P(w)` such that `(P(x̄ ȳ), Q(x̄))` is a pair of
`D`.  Route: `Fin.snoc a c` is injective (`a` is, by
`InvarianceDiagram.IsCompatible.injective_of_relMap_invariant`); the second clause of
[AFK26, Definition 2.1] extends it to a tuple with `P_{k+1+l}`, which carries an invariant
([AFK26, Definition 2.2 (b)]), recast along `k + 1 + l = k + (l + 1)`
(`exists_relMap_invariant_cast`); of `(P(x̄ ȳ), Q(x̄))` and `(P(x̄ ȳ), ¬Q(x̄))` exactly one is
a pair of `D`, and the second would contradict `G' ⊨ Q(a)`.  Correspondence with the printed
definitions. -/
theorem InvarianceDiagram.IsCompatible.exists_extension {D : InvarianceDiagram σ} {M : Type v}
    {G : L.Structure M} (hG : @InvarianceDiagram.IsCompatible L σ D M G) {k : ℕ}
    (Q : σ.Invariant k) {a : Fin k → M} (ha : RelMap (L := L) (self := G) Q.1 a) {c : M}
    (hc : c ∉ Set.range a) :
    ∃ (l : ℕ) (w : Fin (k + (l + 1)) → M) (P : σ.Invariant (k + (l + 1))),
      w ∘ Fin.castAdd (l + 1) = a ∧ w (Fin.natAdd k 0) = c ∧
        RelMap (L := L) (self := G) P.1 w ∧
        (⟨k + (l + 1), P.1, atom Q.1 (Fin.castAdd (l + 1))⟩ : DiagramPair L) ∈ D.pairs := by
  have hinj : Function.Injective (Fin.snoc a c : Fin (k + 1) → M) :=
    Fin.snoc_injective_of_injective (hG.injective_of_relMap_invariant Q ha) hc
  obtain ⟨l, z, hz, hzP⟩ :=
    hG.isStructuredGeometry.isGeometry.exists_closed (Nat.succ_pos k) _ hinj
  obtain ⟨P₀, hP₀, hzP₀⟩ := (hG.isStructuredGeometry.closed_iff _ z).mp hzP
  have e : k + 1 + l = k + (l + 1) := by omega
  obtain ⟨P, hw⟩ := exists_relMap_invariant_cast (G := G) e ⟨P₀, hP₀⟩ hzP₀
  have hwa : z ∘ Fin.cast e.symm ∘ Fin.castAdd (l + 1) = a := by
    funext i
    have hi : Fin.cast e.symm (Fin.castAdd (l + 1) i) = Fin.castAdd l (Fin.castSucc i) :=
      Fin.ext rfl
    have := congrFun hz (Fin.castSucc i)
    simp only [Function.comp_apply, Fin.snoc_castSucc] at this
    simp only [Function.comp_apply, hi, this]
  have hwc : (z ∘ Fin.cast e.symm) (Fin.natAdd k 0) = c := by
    have hi : Fin.cast e.symm (Fin.natAdd k (0 : Fin (l + 1))) = Fin.castAdd l (Fin.last k) :=
      Fin.ext rfl
    have := congrFun hz (Fin.last k)
    simp only [Function.comp_apply, Fin.snoc_last] at this
    simp only [Function.comp_apply, hi, this]
  refine ⟨l, z ∘ Fin.cast e.symm, P, hwa, hwc, hw, ?_⟩
  rcases (D.exactlyOne P.1 Q.1 (Fin.castAdd (l + 1)) P.2).or with h | h
  · exact h
  · refine ((@Formula.realize_not L M G _ _ _).mp (hG.satisfiesPairs _ h _ hw)
      ((@realize_atom_iff L M G _ _ Q.1 _ _).mpr ?_)).elim
    rw [Function.comp_assoc, hwa]
    exact ha

namespace WeakSystem

variable {D : InvarianceDiagram σ} {S : InvariantSystem.{0} σ} {W : WeakSystem.{w, w', v} D S}

/-- **The forth step**: for `G ∈ K_β` on `M` and `H ∈ K_β` on `N` (countable carriers), levels
`ι < ι₁ ≤ β`, and tuples `x`, `y` pattern-matched at `ι₁`, every point `c` of `M` has a point `d`
of `N` such that `Fin.snoc x c` and `Fin.snoc y d` are pattern-matched at `ι`; the old tuples are
kept literally.  Write `x = a ∘ f`, `y = b ∘ f` with `τ_ι₁(G) ⊨ Q(a)` and `τ_ι₁(H) ⊨ Q(b)`.

* **`c` is an entry `a p` of the witnessing tuple**: `d = b p`, the same tuples `a`, `b` read
  along `Fin.snoc f p`, matched at `ι` by `τ_ι(Q)` (`InvariantSystem.IsMatchedAt.mono`).
* **`c` is a genuinely new point**: `τ_ι₁(G)` is compatible with `D`
  (`isCompatible_projection_of_le`), so `a` extends to `w` on `k + (l + 1)` places with `c` at
  `Fin.natAdd k 0`, an invariant `P` with `τ_ι₁(G) ⊨ P(w)`, and the pair `(P(x̄ ȳ), Q(x̄))` of `D`
  (`InvarianceDiagram.IsCompatible.exists_extension`).  `τ_ι₁(H) ∈ K_ι₁`
  (`projection_mem_of_le`) is `ι`-dense (`dense`, `ι < ι₁`), which gives `y'` and an invariant
  `P'` with `τ_ι(P') = τ_ι(P)` and `τ_ι₁(H) ⊨ P'(Fin.append b y')`, the old tuple `b` kept
  literally.  Then `d = Fin.append b y' (Fin.natAdd k 0)`, and `w`, `Fin.append b y'` are matched
  at `ι` by `τ_ι(P)`, read along `Fin.snoc (Fin.castAdd (l + 1) ∘ f) (Fin.natAdd k 0)`.

Correspondence with the printed definitions. -/
theorem forth_of_isPatternMatchedAt {M N : Type v} [Countable M] [Countable N]
    {β : SystemLevel} {G : L.Structure M} {H : L.Structure N} (hG : G ∈ W.K β M)
    (hH : H ∈ W.K β N) {ι ι₁ : SystemLevel} (hlt : ι < ι₁) (hle : ι₁ ≤ β) {n : ℕ}
    {x : Fin n → M} {y : Fin n → N} (hm : S.IsPatternMatchedAt ι₁ G H x y) (c : M) :
    ∃ d : N, S.IsPatternMatchedAt ι G H (Fin.snoc x c) (Fin.snoc y d) := by
  obtain ⟨k, a, b, f, rfl, rfl, Q, ha, hb⟩ := hm
  by_cases hc : c ∈ Set.range a
  · -- the point is already an entry of the witnessing tuple
    obtain ⟨p, rfl⟩ := hc
    refine ⟨b p, k, a, b, Fin.snoc f p, ?_, ?_,
      InvariantSystem.IsMatchedAt.mono hlt.le ⟨Q, ha, hb⟩⟩
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  · -- a genuinely new point
    obtain ⟨l, w, P, hwa, hwc, hw, hpair⟩ :=
      (W.isCompatible_projection_of_le hle hG).exists_extension Q ha hc
    obtain ⟨y', P', hP', hP'b⟩ := W.dense hlt (W.projection_mem_of_le hle hH) P Q hpair b hb
    -- the old tuple is kept literally
    have hold : Fin.append b y' ∘ Fin.castAdd (l + 1) = b :=
      funext fun i ↦ Fin.append_left b y' i
    refine ⟨Fin.append b y' (Fin.natAdd k 0), k + (l + 1), w, Fin.append b y',
      Fin.snoc (Fin.castAdd (l + 1) ∘ f) (Fin.natAdd k 0), ?_, ?_, S.τ ι P,
      InvariantSystem.relMap_projection_τ_of_le hlt.le G P hw, ?_⟩
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [hwc]
      · simpa using (congrFun hwa (f j)).symm
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simp only [Fin.snoc_castSucc, Function.comp_apply]
        exact (congrFun hold (f j)).symm
    · rw [← hP']
      exact InvariantSystem.relMap_projection_τ_of_le hlt.le H P' hP'b

/-- **The back step**: under the hypotheses of `forth_of_isPatternMatchedAt`, every point `d` of
`N` has a point `c` of `M` such that `Fin.snoc x c` and `Fin.snoc y d` are pattern-matched at
`ι`.  The forth step with the roles of `(M, G)` and `(N, H)` exchanged
(`InvariantSystem.IsPatternMatchedAt.symm`); its two cases (an entry of the witnessing tuple, a
genuinely new point) are those of the forth step.  Correspondence with the printed definitions. -/
theorem back_of_isPatternMatchedAt {M N : Type v} [Countable M] [Countable N]
    {β : SystemLevel} {G : L.Structure M} {H : L.Structure N} (hG : G ∈ W.K β M)
    (hH : H ∈ W.K β N) {ι ι₁ : SystemLevel} (hlt : ι < ι₁) (hle : ι₁ ≤ β) {n : ℕ}
    {x : Fin n → M} {y : Fin n → N} (hm : S.IsPatternMatchedAt ι₁ G H x y) (d : N) :
    ∃ c : M, S.IsPatternMatchedAt ι G H (Fin.snoc x c) (Fin.snoc y d) := by
  obtain ⟨c, h⟩ := forth_of_isPatternMatchedAt hH hG hlt hle hm.symm d
  exact ⟨c, h.symm⟩

end WeakSystem

end VaughtConjecture.Correspondence
