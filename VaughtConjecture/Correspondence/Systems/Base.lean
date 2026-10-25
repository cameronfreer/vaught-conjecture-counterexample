/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Correspondence.TemplateSystem.WeakSystem

/-!
# The abstract data of [AFK26, §2]: the base sublanguage, fixed structures, rank, density

Numbering as in the current draft of [AFK26] (the published v1 reads identically).  This file and
the other files of `VaughtConjecture.Correspondence.Systems` state the abstract objects of
[AFK26, §2.4–2.6] for an **arbitrary** geometry signature `σ` on a language `L`, invariance
diagram `D` and invariant system `S` (`VaughtConjecture.Correspondence.InvariantSystem`).  Only
definitions, structures and the statements of theorems (as `…Target` propositions) are given;
nothing about them is proved here.

**Statements in this file.**

* `SystemLevel`: the countable ordinals `{β : Ordinal.{0} // β < ω₁}`, the index type of
  `InvariantSystem.{0}` (an abbreviation, definitionally that subtype).
* `GeometrySignature.BaseSublanguage σ Lc` [AFK26, Convention 2.3]: a language `Lc` with an
  injective inclusion `Lc →ᴸ L` whose range is exactly the symbols of `L` that are not
  invariants (`L_c = L ∖ L_b`).  Its reduct `BaseSublanguage.reduct` is `M ↦ M↾L_c`, on the same
  carrier ([AFK26, Definition 2.2]: `M` is a lift of `M↾L_c`).  `Lc` is relational
  (`BaseSublanguage.isRelational`, a one-line term); its countability is the stated target
  `BaseSublanguage.CountableRelationsTarget` and is an explicit instance premise wherever coded
  models are used.  A closed tuple of an `Lc`-structure is `BaseSublanguage.IsClosedTuple`.
* `InvariantSystem.IsFixedAt S β G` [AFK26, Definition 2.7]: `τ_β(G) = G`, through the existing
  `InvariantSystem.projection`; this is the reading of "rank at most `β`".  The ranks of an
  invariant and of a structure, as least levels, are `InvariantSystem.invariantRank` and
  `InvariantSystem.structureRank`; their agreement with `IsFixedAt` is the stated target
  `InvariantSystem.FixedAtIffRankLeTarget`.
* `InvarianceDiagram.IsDenseAt D S α G` [AFK26, Definition 2.10 (c)], at `β = ω₁` (the form used
  by [AFK26, Definition 2.17]); clauses (a) and (b) of Definition 2.10 are compatibility with `D`.
* `InvariantSystem.IsMatchedAt S ι G H a b`: the relation `I_ι` of the proof of
  [AFK26, Proposition 2.18] — the tuples carry one common invariant in `τ_ι(G)` and `τ_ι(H)` —
  and `InvariantSystem.IsPatternMatchedAt`, its extension to arbitrary tuples read along one
  common map of positions from matched tuples.
* `IsCountableUpToIso P`: the structures on one carrier with property `P` fall into countably
  many isomorphism classes (used for the coding passage of "few maximal models").

**Universes.**  The ordinal universe is `0` throughout (`InvariantSystem.{0}`, as InfinitaryLogic's
`bfEquivSetoid` and the counting lemmas require).  The languages `L` and `Lc` and the carriers are
in arbitrary universes here; the universes `Language.{0, 1}` of `Lc` are imposed only where
`MainTheorem.HasThinAlephOneSpectrum` is used.
-/

universe w w' wc wc' v

namespace VaughtConjecture.Correspondence

open FirstOrder Language Structure Ordinal

/-- **The countable ordinals as levels** [AFK26, Definition 2.6]: `{β : Ordinal.{0} // β < ω₁}`,
the index type of `InvariantSystem.{0}`.  An abbreviation, definitionally the subtype.
Correspondence with the printed definitions. -/
abbrev SystemLevel : Type 1 := {β : Ordinal.{0} // β < ω₁}

variable {L : Language.{w, w'}} {σ : GeometrySignature L}

/-! ### The base sublanguage `L_c` -/

namespace GeometrySignature

variable (σ) in
/-- **The base sublanguage `L_c`** [AFK26, Convention 2.3]: a language `Lc` with an inclusion
`Lc →ᴸ L` that is injective on symbols and whose range is exactly the set of symbols of `L` that
are not invariants, `L_c = L ∖ L_b` (`L_a ⊆ L_c` by `GeometrySignature.not_isInvariant_closed`).
The language `Lc` is a parameter, so its universes are visible in every statement.
Correspondence with the printed definitions. -/
structure BaseSublanguage (Lc : Language.{wc, wc'}) where
  /-- The inclusion `L_c ⊆ L`. -/
  incl : Lc →ᴸ L
  /-- The inclusion is injective on symbols. -/
  incl_injective : incl.Injective
  /-- The range of the inclusion is the set of symbols that are not invariants. -/
  mem_range_iff ⦃n : ℕ⦄ (R : L.Relations n) :
    (∃ r : Lc.Relations n, incl.onRelation r = R) ↔ ¬ σ.IsInvariant R

namespace BaseSublanguage

variable {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc)

/-- **The reduct `G↾L_c`** [AFK26, Definition 2.2]: the reduct of `G` along the inclusion, a
structure on the same carrier; `G` is a **lift** of `G↾L_c`.  Correspondence with the printed
definitions. -/
@[instance_reducible] def reduct {M : Type v} (G : L.Structure M) : Lc.Structure M :=
  @LHom.reduct Lc L E.incl M G

/-- **`L_c` is relational**: a function symbol of `Lc` would map to one of `L`, which has none.
Correspondence with the printed definitions. -/
theorem isRelational (E : σ.BaseSublanguage Lc) : Lc.IsRelational :=
  fun n ↦ ⟨fun f ↦ (σ.isEmpty_functions n).false (E.incl.onFunction f)⟩

/-- **Target: `L_c` is countable** [AFK26, Convention 2.3, `|L_c^n| ≤ ω`]: countably many relation
symbols of `Lc` in all arities, from `GeometrySignature.countable_setOf_not_isInvariant` and the
injectivity of the inclusion.  Stated, not proved here; every statement about coded models carries
`[Countable (Σ n, Lc.Relations n)]` as an explicit instance premise.  Correspondence with the
printed definitions. -/
def CountableRelationsTarget : Prop :=
  Countable (Σ n, Lc.Relations n)

/-- **A closed tuple of an `L_c`-structure** [AFK26, Definitions 2.1 and 2.21]: `0 < n` and the
symbol of `Lc` whose image is `P_n` holds of the tuple (that symbol is unique by injectivity of
the inclusion, and exists by `mem_range_iff`).  Correspondence with the printed definitions. -/
def IsClosedTuple {M : Type v} (B : Lc.Structure M) {n : ℕ} (a : Fin n → M) : Prop :=
  ∃ (hn : 0 < n) (r : Lc.Relations n), E.incl.onRelation r = σ.closed n hn ∧
    RelMap (L := Lc) (self := B) r a

end BaseSublanguage

end GeometrySignature

/-! ### Fixed structures and rank -/

namespace InvariantSystem

variable (S : InvariantSystem.{0} σ)

/-- **`G` is fixed at level `β`** ("rank at most `β`", [AFK26, Definition 2.7]):
`τ_β(G) = G`, for the projection `InvariantSystem.projection`.  This is the form in which
[AFK26, Definition 2.17] ("with rank at most `β`") is read; its agreement with the least-level
rank is `FixedAtIffRankLeTarget`.  Correspondence with the printed definitions. -/
def IsFixedAt (β : SystemLevel) {M : Type v} (G : L.Structure M) : Prop :=
  S.projection β G = G

/-- **The `τ`-rank of an invariant** [AFK26, Definition 2.6]: the least countable `β` with
`τ_β(Q) = Q` (one exists by `InvariantSystem.exists_fixed`).  Correspondence with the printed
definitions. -/
noncomputable def invariantRank {n : ℕ} (Q : σ.Invariant n) : Ordinal.{0} :=
  sInf {β : Ordinal.{0} | ∃ hβ : β < ω₁, S.τ ⟨β, hβ⟩ Q = Q}

/-- **The `τ`-rank of a structure** [AFK26, Definition 2.7]: the least countable `β` with
`τ_β(G) = G`.  When `G` is fixed at no countable level the set is empty and the value is `0`
(`sInf ∅ = 0`); statements therefore use `IsFixedAt`, never this value alone.  Correspondence with
the printed definitions. -/
noncomputable def structureRank {M : Type v} (G : L.Structure M) : Ordinal.{0} :=
  sInf {β : Ordinal.{0} | ∃ hβ : β < ω₁, S.IsFixedAt ⟨β, hβ⟩ G}

/-- **Target: fixed at `β` exactly when the rank is at most `β`** [AFK26, Definition 2.7]: for a
structure fixed at some countable level, `G` is fixed at `β` exactly when its rank is at most
`β`.  The forward direction is the definition of the least element; the converse needs
`τ_γ ∘ τ_β = τ_β` on structures for `β ≤ γ` (from `InvariantSystem.comp`).  Stated.
Correspondence with the printed definitions. -/
def FixedAtIffRankLeTarget : Prop :=
  ∀ (M : Type v) (G : L.Structure M), (∃ γ : SystemLevel, S.IsFixedAt γ G) →
    ∀ β : SystemLevel, S.IsFixedAt β G ↔ S.structureRank G ≤ β.1

/-- **The back-and-forth relation `I_ι`** of the proof of [AFK26, Proposition 2.18]: tuples `a` of
`M` and `b` of `N` of the same length carry one common invariant `Q` in the projections `τ_ι(G)`
and `τ_ι(H)`.  The printed `I_ι` also asks that `a` and `b` be closed; for structures compatible
with a diagram this follows from [AFK26, Definition 2.2 (b)] (an invariant holds only of closed
tuples).  Correspondence with the printed definitions. -/
def IsMatchedAt (ι : SystemLevel) {M : Type v} {N : Type v} (G : L.Structure M)
    (H : L.Structure N) {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∃ Q : σ.Invariant n, RelMap (L := L) (self := S.projection ι G) Q.1 a ∧
    RelMap (L := L) (self := S.projection ι H) Q.1 b

/-- **Matching through a common tuple pattern** at level `ι`: tuples `x` of `M` and `y` of `N` on
`n` places, not necessarily injective and possibly empty, are read along **one** map of positions
`f : Fin n → Fin k` from tuples `a` and `b` matched at `ι` (`IsMatchedAt`): `x = a ∘ f` and
`y = b ∘ f`.  The induction behind [AFK26, Proposition 2.18] for InfinitaryLogic's `BFEquiv`
runs over arbitrary tuples (repeated entries, the empty tuple), so it is stated for this
relation; matched closed tuples are pattern-matched along `f = id`.  Correspondence with the
printed definitions. -/
def IsPatternMatchedAt (ι : SystemLevel) {M : Type v} {N : Type v} (G : L.Structure M)
    (H : L.Structure N) {n : ℕ} (x : Fin n → M) (y : Fin n → N) : Prop :=
  ∃ (k : ℕ) (a : Fin k → M) (b : Fin k → N) (f : Fin n → Fin k),
    x = a ∘ f ∧ y = b ∘ f ∧ S.IsMatchedAt ι G H a b

end InvariantSystem

/-! ### Density -/

/-- **`α`-density** [AFK26, Definition 2.10 (c)], at `β = ω₁` (so `L_b[τ, ω₁] = L_b`, the form
used in [AFK26, Definition 2.17]): whenever `(Q(x̄ ȳ), R(x̄)) ∈ D` for invariants `Q` on `n + m`
places and `R` on `n` places, every `x̄` with `G ⊨ R(x̄)` extends to some `x̄ ȳ` with
`G ⊨ Q*(x̄ ȳ)` for an invariant `Q*` with `τ_α(Q*) = τ_α(Q)` (the printed disjunction over all
such `Q*`).  Clauses (a) and (b) of Definition 2.10 are compatibility with `D`
(`InvarianceDiagram.IsCompatible`), a separate clause of a weak system.  Correspondence with the
printed definitions. -/
def InvarianceDiagram.IsDenseAt (D : InvarianceDiagram σ) (S : InvariantSystem.{0} σ)
    (α : SystemLevel) {M : Type v} (G : L.Structure M) : Prop :=
  ∀ ⦃n m : ℕ⦄ (Q : σ.Invariant (n + m)) (R : σ.Invariant n),
    (⟨n + m, Q.1, atom R.1 (Fin.castAdd m)⟩ : DiagramPair L) ∈ D.pairs →
    ∀ x : Fin n → M, RelMap (L := L) (self := G) R.1 x →
      ∃ (y : Fin m → M) (Q' : σ.Invariant (n + m)), S.τ α Q' = S.τ α Q ∧
        RelMap (L := L) (self := G) Q'.1 (Fin.append x y)

/-! ### Countably many structures up to isomorphism, on one carrier -/

/-- **Countably many classes on one carrier**: the structures on `X` with property `P` are
isomorphic, each, to a member of one countable set of structures on `X`.  Correspondence with the
printed definitions. -/
def IsCountableUpToIso {X : Type v} (P : L.Structure X → Prop) : Prop :=
  ∃ T : Set (L.Structure X), T.Countable ∧
    ∀ G : L.Structure X, P G → ∃ H ∈ T, Nonempty (@Language.Equiv L X X G H)

end VaughtConjecture.Correspondence
