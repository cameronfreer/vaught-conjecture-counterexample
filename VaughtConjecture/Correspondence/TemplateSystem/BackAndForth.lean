/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.MorleyCounting
import VaughtConjecture.Correspondence.TemplateSystem.AlephOne
import VaughtConjecture.MainTheorem.Scatteredness

/-!
# Back-and-forth equivalence in `K[L]`: the statements of [AFK26, Proposition 2.18] for `K[L]`

Numbering as in the current draft of [AFK26].  `K_η[L]` is `templateStageClass M η`, `τ_ι` is
`projectStructure ι`, and `σ[L]` is `templateSentence`.  This file **states** the back-and-forth
comparison of [AFK26, Proposition 2.18] for `K[L]`, with a tuple-level core, its passage to the
empty tuple of models of `σ[L]` coded on `ℕ`, the countability of the back-and-forth classes, and
the thinness half of [AFK26, Theorem 4.36].  Only one-line compositions are proved.

## System levels and label cutoffs

Every level in this file is a **system level** `ι` (or `η`, `β`): the index of `K_ι[L]` and of the
projection `τ_ι`, and the level of InfinitaryLogic's back-and-forth relation `BFEquiv ι`.  The
**label cutoff** of `ι` is the block stage `λ_ι = blockStage ι = ω + ω · ι`, at which `τ_ι` reads
labels (`LegalClass.project ι`); it never appears as a level of `BFEquiv`.  The comparison is
`BFEquiv ι` against matching at the system level `ι`, not at `λ_ι`.

## The InfinitaryLogic notions, as used here

* `FirstOrder.Language.BFEquiv (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N)`
  (InfinitaryLogic, `Scott/BackAndForth.lean`), by `Ordinal.limitRecOn` on the ordinal level `α`:
  - level `0` (`BFEquiv.zero`): `SameAtomicType a b`, that is, for every atomic index
    `idx : L.AtomicIdx n`, `idx.holds a ↔ idx.holds b`, where an index is an equality
    `eq i j` (`a i = a j`) or a relation `rel R f` along an arbitrary map `f : Fin l → Fin n`
    (`RelMap R (a ∘ f)`).  The tuples need not be injective: **repeated entries are allowed**, and
    the equality indices record the pattern of repetitions;
  - level `Order.succ α` (`BFEquiv.succ`): `BFEquiv α n a b`, and forth (every `m : M` has
    `n' : N` with `BFEquiv α (n + 1) (Fin.snoc a m) (Fin.snoc b n')`) and back (symmetrically);
  - a limit level `α` (`BFEquiv.limit`): `BFEquiv γ n a b` for every `γ < α`;
  - `BFEquiv.monotone`: a higher level gives every lower one.
* `FirstOrder.Language.bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0})`
  (InfinitaryLogic, `ModelTheory/MorleyCounting.lean`): on the codes of models of `φ` on `ℕ`,
  `BFEquiv α 0 Fin.elim0 Fin.elim0` of the decoded structures, at the **empty tuple**;
  isomorphism refines it (`isoSetoid_refines_bfEquivSetoid`).
* `MainTheorem.isThinOnNatModels_of_countable_bfClasses`
  (`VaughtConjecture/MainTheorem/Scatteredness.lean`): if
  `∀ η < Ordinal.omega 1, Countable (Quotient (bfEquivSetoid φ η))`, then `φ.IsThinOnNatModels`,
  which is `¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels`.

## The matching relation

`IsMatchedAt ι G H x y`, for tuples `x : Fin n → M` and `y : Fin n → N` that need **not** be
injective: there are `k > 0`, a legal class `c` on `k` points, tuples `a : Fin k → M`,
`b : Fin k → N`, and **one** map `f : Fin n → Fin k` with `x = a ∘ f`, `y = b ∘ f`,
`τ_ι(G) ⊨ Q_c(a)` and `τ_ι(H) ⊨ Q_c(b)`.  The pairs `(a, b)` are the pairs of the back-and-forth
system `I_ι` of the proof of [AFK26, Proposition 2.18] (closed tuples with the same invariant in
the `ι`-projections); `x` and `y` are read from them along the same pattern `f`, so repeated
entries of `x` and `y` occur at the same places.  At the top level `ι = η`, `τ_η(G) = G` for
`G ∈ K_η[L]`, so the matching is by invariants of `G` and `H` themselves.  For closed injective
tuples it is sharing an invariant (`f = id`); at the empty tuple (`n = 0`, `f = Fin.elim0`) it is
the realization of a common invariant in `τ_ι(G)` and `τ_ι(H)`.

## The statements and their status

* (i) `AtomicAgreementTarget`: matching at level `0` gives `SameAtomicType` of the base reducts.
  Stated.  Inputs: compatibility of `τ_0(G) ∈ K_0[L]` (`weakSystemClausesTarget`,
  `projectionTarget`); an invariant tuple is injective
  (`IsTemplateCompatible.injective_of_relMap_invariant`), so `x i = x j ↔ f i = f j ↔ y i = y j`;
  a symbol `R` of `L_c[L]` holds of `a ∘ g` exactly when `c.Holds R g` (the diagram pairs,
  `IsTemplateCompatible.satisfiesPairs`, `mk_atom_mem_templateDiagramPairs_iff` and
  `mk_not_atom_mem_templateDiagramPairs_iff`), and `τ_0` does not change `R`.  **First new
  argument**: the reading `RelMap G R (a ∘ g) ↔ c.1.Holds R g` for a compatible `G` with
  `G ⊨ Q_c(a)`, if not already present.
* (ii) `ForthStepTarget` and `BackStepTarget`: matching at `succ ι ≤ η` extends, in each
  direction, to matching at `ι` of `(Fin.snoc x m, Fin.snoc y m')`.  Stated.  Inputs: the closure
  clause of the geometry (`IsGeometry.exists_closed`, applied to `a` extended by `m` when `m` is
  not among the entries of `a`; otherwise the old index); the invariant `Q_d` of the closed
  extension in `τ_{ι+1}(G)` and the pair `(Q_d(x̄ ȳ), Q_c(x̄)) ∈ ID[L]`; `ProjectedDensityAt ι`
  of `τ_{ι+1}(H) ∈ K_{ι+1}[L]` (`weakSystemClausesTarget`, `projectionTarget`), which gives
  `Q_s` with `τ_ι(s) = τ_ι(d)`; then `τ_ι` of both sides (`relMap_projectStructure_invariant`,
  `projectStructure_projectStructure_of_le`).  **First new argument**: the pair
  `(Q_d(x̄ ȳ), Q_c(x̄)) ∈ templateDiagramPairs` from `τ_{ι+1}(G) ⊨ Q_d(a a*)` and `⊨ Q_c(a)`
  (the face of `d` along `Fin.castAdd` is `c`, by uniqueness of invariants).
* (iii) `MatchedAtMonotoneTarget`: matching at `ι'` gives matching at every `ι ≤ ι'`.  This is the
  limit clause (at a limit level `BFEquiv` is the conjunction of the lower levels) and the first
  conjunct of the successor clause.  Stated.  Inputs: `relMap_projectStructure_invariant` and
  `projectStructure_projectStructure_of_le`; no density.
* `BackAndForthCoreTarget` (the tuple-level core): for `G ∈ K_η[L]` and `H ∈ K_η[L]` on countable
  carriers, `η < ω₁`, matching at a system level `ι ≤ η` gives `BFEquiv ι` of the base reducts.
  Stated.  Plan: induction on `ι` (`Ordinal.limitRecOn`), with (i) at `0`, (iii) and (ii) at
  successors (`BFEquiv.succ`), (iii) at limits (`BFEquiv.limit`).
* `BackAndForthEmptyTupleTarget`: two coded models of `σ[L]` with lifts in `K_β[L]` that realize
  a common invariant are `bfEquivSetoid templateSentence β`-related.  Stated.  What is matched at
  `n = 0`: one invariant `Q_c` (of any arity `k > 0`) realized in both lifts.  Plan: the core at
  `ι = η = β`, `n = 0`, `f = Fin.elim0`, and the equality of the base reducts with the decoded
  structures.
* `RealizedInvariantTarget`: every member of `K_β[L]` realizes some invariant.  Stated.  Inputs:
  a point of the nonempty carrier, `IsGeometry.exists_closed` on the one-point tuple, and
  `IsStructuredGeometry.closed_iff`.
* `CountableBFClassesTarget`: for every `β < ω₁`, countably many classes of
  `bfEquivSetoid templateSentence β`.  Stated.  Plan, [AFK26, Theorem 2.19]:
  - a coded model whose maximal stage (`maximalStageOfClass`) is at least `β` has a lift in
    `K_β[L]`, the projection `τ_β(H)` of its maximal lift (`projectionTarget`,
    `baseReduct_projectStructure`); choose an invariant realized in it (`RealizedInvariantTarget`);
    it is fixed by `τ_β` (`IsTemplateCompatible.project_eq_of_relMap_invariant`), so it lies in the
    countable set of `β`-invariants (`templateInvariantSystem`, field `countable`); two models with
    the same chosen invariant are related (`BackAndForthEmptyTupleTarget`);
  - the coded models of maximal stage `< β` fall into countably many isomorphism classes
    (`countable_setOf_maximalStageOfClass_eq` over the countably many `γ < β`), and isomorphism
    refines `bfEquivSetoid` (`isoSetoid_refines_bfEquivSetoid`).
* `ThinnessTarget`: `¬ templateSentence.{0}.HasPerfectSetOfPairwiseNonisomorphicNatModels`.
  Stated.  From `CountableBFClassesTarget` by `MainTheorem.isThinOnNatModels_of_countable_bfClasses`
  (`thinnessTarget_of_countableBFClassesTarget`, a one-line composition).
* `Theorem436Target` from `ThinnessTarget` and `templateSentenceAlephOneTarget`
  (`theorem436Target_of_thinnessTarget`, a one-line composition).

The first genuinely new argument on the critical path is in (ii): the closed extension of a matched
tuple by one point and the diagram pair `(Q_d(x̄ ȳ), Q_c(x̄))` for its invariant.
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

/-! ### The matching relation -/

/-- **Matching at a system level `ι`** (the back-and-forth system `I_ι` of the proof of
[AFK26, Proposition 2.18], read on arbitrary tuples): tuples `x` of `M` and `y` of `N` on `n`
places, not necessarily injective, are read along one map `f : Fin n → Fin k` from tuples `a`, `b`
on `k > 0` places that carry the same invariant `Q_c` in the `ι`-projections `τ_ι(G)` and
`τ_ι(H)`.  `ι` is a system level; `τ_ι` reads labels at the cutoff `λ_ι = blockStage ι`.
Correspondence with the printed definitions. -/
def IsMatchedAt (ι : Ordinal.{u}) {M : Type v} {N : Type w}
    (G : templateLanguage.{u}.Structure M) (H : templateLanguage.{u}.Structure N) {n : ℕ}
    (x : Fin n → M) (y : Fin n → N) : Prop :=
  ∃ (k : ℕ) (hk : 0 < k) (c : LegalClass.{u} k) (a : Fin k → M) (b : Fin k → N)
    (f : Fin n → Fin k), x = a ∘ f ∧ y = b ∘ f ∧
      RelMap (L := templateLanguage.{u}) (self := projectStructure ι G)
        (TemplateSymbol.invariant c hk) a ∧
      RelMap (L := templateLanguage.{u}) (self := projectStructure ι H)
        (TemplateSymbol.invariant c hk) b

/-! ### The three ingredients -/

section Ingredients

variable (M : Type v) (N : Type w)

/-- **Target (i): atomic agreement at level `0`**: on countable carriers, for `η < ω₁`,
`G ∈ K_η[L]` and `H ∈ K_η[L]`, tuples matched at the system level `0` have the same atomic type in
the base reducts (`SameAtomicType`: equalities among the places, repeated entries included, and
every symbol of `L_c[L]` along every map of places).  Stated; not proved.  Correspondence with the
printed definitions. -/
def AtomicAgreementTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N), IsMatchedAt 0 G H x y →
        @SameAtomicType baseTemplateLanguage.{u} M (baseReduct G) n N (baseReduct H) x y

/-- **Target (ii), forth: the extension step at a successor level**: on countable carriers, for
`η < ω₁`, `G ∈ K_η[L]`, `H ∈ K_η[L]` and a system level `ι` with `succ ι ≤ η`, if `x` and `y` are
matched at `succ ι`, then every point `m` of `M` has a point `m'` of `N` with `Fin.snoc x m` and
`Fin.snoc y m'` matched at `ι`.  Stated; not proved.  Correspondence with the printed
definitions. -/
def ForthStepTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ ι : Ordinal.{u}, Order.succ ι ≤ η → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
        IsMatchedAt (Order.succ ι) G H x y →
          ∀ m : M, ∃ m' : N, IsMatchedAt ι G H (Fin.snoc x m) (Fin.snoc y m')

/-- **Target (ii), back: the extension step at a successor level**, the other direction: every
point `m'` of `N` has a point `m` of `M` with `Fin.snoc x m` and `Fin.snoc y m'` matched at `ι`.
Stated; not proved.  Correspondence with the printed definitions. -/
def BackStepTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ ι : Ordinal.{u}, Order.succ ι ≤ η → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
        IsMatchedAt (Order.succ ι) G H x y →
          ∀ m' : N, ∃ m : M, IsMatchedAt ι G H (Fin.snoc x m) (Fin.snoc y m')

/-- **Target (iii): matching descends to lower levels** (the limit clause, and the first conjunct
of the successor clause): matching at a system level `ι'` gives matching at every `ι ≤ ι'`, for
arbitrary structures.  Stated; not proved.  Correspondence with the printed definitions. -/
def MatchedAtMonotoneTarget : Prop :=
  ∀ (G : templateLanguage.{u}.Structure M) (H : templateLanguage.{u}.Structure N)
    (ι ι' : Ordinal.{u}), ι ≤ ι' → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
      IsMatchedAt ι' G H x y → IsMatchedAt ι G H x y

/-- **Target: the tuple-level core of [AFK26, Proposition 2.18] for `K[L]`**: on countable
carriers, for `η < ω₁`, `G ∈ K_η[L]` and `H ∈ K_η[L]`, tuples matched at a system level `ι ≤ η`
are back-and-forth equivalent at level `ι` in the base reducts: `BFEquiv ι` of
`(G↾L_c[L], x)` and `(H↾L_c[L], y)`.  The level of `BFEquiv` is the system level `ι`, not the
label cutoff `λ_ι`.  Stated; not proved; plan: induction on `ι` with `AtomicAgreementTarget`,
`ForthStepTarget`, `BackStepTarget` and `MatchedAtMonotoneTarget`.  Correspondence with the
printed definitions. -/
def BackAndForthCoreTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ ι : Ordinal.{u}, ι ≤ η → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
        IsMatchedAt ι G H x y →
          @BFEquiv baseTemplateLanguage.{u} M (baseReduct G) N (baseReduct H) ι n x y

end Ingredients

/-! ### The empty tuple and the classes -/

/-- **Target: the passage to the empty tuple** [AFK26, Proposition 2.18, for `K[L]`]: for
`β < ω₁` and two models of `σ[L]` coded on `ℕ`, with lifts `G₁ ∈ K_β[L]` and `G₂ ∈ K_β[L]` on `ℕ`
(`G_i↾L_c[L]` the decoded structure) that realize one common invariant `Q_c` (of any arity
`k > 0`), the two codes are related by `bfEquivSetoid templateSentence β`, that is,
`BFEquiv β 0 Fin.elim0 Fin.elim0`.  At `n = 0` the matching at the system level `β` is exactly
this common invariant (`f = Fin.elim0`, `τ_β(G_i) = G_i`).  Stated; not proved.  Correspondence with
the printed definitions. -/
def BackAndForthEmptyTupleTarget : Prop :=
  ∀ β : Ordinal.{0}, β < ω₁ → ∀ c₁ c₂ : ModelsOf templateSentence.{0},
    ∀ G₁ ∈ templateStageClass ℕ β, ∀ G₂ ∈ templateStageClass ℕ β,
      baseReduct G₁ = c₁.1.toStructure → baseReduct G₂ = c₂.1.toStructure →
      (∃ (k : ℕ) (hk : 0 < k) (c : LegalClass.{0} k) (a b : Fin k → ℕ),
        RelMap (L := templateLanguage.{0}) (self := G₁) (TemplateSymbol.invariant c hk) a ∧
        RelMap (L := templateLanguage.{0}) (self := G₂) (TemplateSymbol.invariant c hk) b) →
        (bfEquivSetoid templateSentence.{0} β).r c₁ c₂

/-- **Target: every member of `K_β[L]` realizes an invariant**: some `Q_c` holds of some tuple.
Stated; not proved; route: a point of the (nonempty) carrier, the closure clause of the geometry
on the one-point tuple (`IsGeometry.exists_closed`), and `IsStructuredGeometry.closed_iff`.
Correspondence with the printed definitions. -/
def RealizedInvariantTarget (M : Type v) : Prop :=
  ∀ β : Ordinal.{u}, ∀ G ∈ templateStageClass M β,
    ∃ (k : ℕ) (hk : 0 < k) (c : LegalClass.{u} k) (a : Fin k → M),
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hk) a

/-- **Target: countably many back-and-forth classes at every level** (the input of
`MainTheorem.isThinOnNatModels_of_countable_bfClasses`; [AFK26, Theorem 2.19 and
Theorem 2.25 (b)] for `K[L]`): for every `β < ω₁`, the classes of
`bfEquivSetoid templateSentence β` on the models of `σ[L]` coded on `ℕ` are countably many.
Stated; not proved; the plan is in the module docstring.  Correspondence with the printed
definitions. -/
def CountableBFClassesTarget : Prop :=
  ∀ β : Ordinal.{0}, β < ω₁ → Countable (Quotient (bfEquivSetoid templateSentence.{0} β))

/-! ### Thinness and the assembly -/

/-- **Target: thinness of `σ[L]`** [AFK26, Theorem 4.36, the second conclusion]: there is no
perfect set of pairwise nonisomorphic models of `σ[L]` coded on `ℕ`.  This is the second conjunct
of `Theorem436Target`.  Stated; open; from `CountableBFClassesTarget`
(`thinnessTarget_of_countableBFClassesTarget`).  Correspondence with the printed definitions. -/
def ThinnessTarget : Prop :=
  ¬ templateSentence.{0}.HasPerfectSetOfPairwiseNonisomorphicNatModels

/-- **Thinness from countably many back-and-forth classes**:
`MainTheorem.isThinOnNatModels_of_countable_bfClasses`.  Correspondence with the printed
definitions. -/
theorem thinnessTarget_of_countableBFClassesTarget (h : CountableBFClassesTarget) :
    ThinnessTarget :=
  MainTheorem.isThinOnNatModels_of_countable_bfClasses h

/-- **[AFK26, Theorem 4.36] from thinness**: `Theorem436Target` is the count
(`templateSentenceAlephOneTarget`, proved) together with thinness.  Correspondence with the
printed definitions. -/
theorem theorem436Target_of_thinnessTarget (h : ThinnessTarget) : Theorem436Target :=
  ⟨templateSentenceAlephOneTarget, h⟩

end VaughtConjecture
