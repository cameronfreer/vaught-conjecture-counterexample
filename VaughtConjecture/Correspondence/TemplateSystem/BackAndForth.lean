/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.MorleyCounting
import VaughtConjecture.Correspondence.TemplateSystem.AlephOne
import VaughtConjecture.MainTheorem.Scatteredness

/-!
# Back-and-forth equivalence in `K[L]`: [AFK26, Proposition 2.18] for `K[L]`, and thinness

Numbering as in the current draft of [AFK26].  `K_η[L]` is `templateStageClass M η`, `τ_ι` is
`projectStructure ι`, and `σ[L]` is `templateSentence`.  This file proves the back-and-forth
comparison of [AFK26, Proposition 2.18] for `K[L]`, with a tuple-level core, its passage to the
empty tuple of models of `σ[L]` coded on `ℕ`, the countability of the back-and-forth classes, the
thinness half of [AFK26, Theorem 4.36], and with the count `templateSentenceAlephOneTarget` the
statement `Theorem436Target` itself (`theorem436Target`).

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

## The statements, all proved

* (i) `atomicAgreementTarget`: matching at level `0` gives `SameAtomicType` of the base reducts.
  `τ_0(G)` and `τ_0(H)` are compatible (`projectionTarget`); invariant tuples are injective
  (`IsTemplateCompatible.injective_of_relMap_invariant`), so `x i = x j ↔ f i = f j ↔ y i = y j`
  (repeated entries); a symbol `R` of `L_c[L]` holds of `a ∘ g` exactly when `c.Holds R g`
  (`IsTemplateCompatible.relMap_comp_iff`), and `τ_0` does not change `R`.
* (ii) `forthStepTarget` and `backStepTarget`: matching at `succ ι ≤ η` extends, in each
  direction, to matching at `ι` of `(Fin.snoc x m, Fin.snoc y m')`.  Two cases: **the point is an
  entry of the witnessing closed tuple** (the same witnesses, along `Fin.snoc f p`), and **a
  genuinely new point** (`IsTemplateCompatible.exists_closed_extension`: the closure clause
  `IsGeometry.exists_closed`, the invariant `Q_d` of the closed extension and the pair
  `(Q_d(x̄ ȳ), Q_c(x̄)) ∈ ID[L]`; then `ProjectedDensityAt ι` of `τ_{ι+1}(H) ∈ K_{ι+1}[L]`
  (`weakSystemClausesTarget`), with the old tuple preserved literally,
  `Fin.append b y' ∘ Fin.castAdd (l + 1) = b`).  The back step is the forth step with the roles
  exchanged (`IsMatchedAt.symm`).
* (iii) `matchedAtMonotoneTarget`: matching at `ι'` gives matching at every `ι ≤ ι'`
  (`relMap_projectStructure_project_of_le`); no density.
* `backAndForthCoreTarget` (the tuple-level core): for `G ∈ K_η[L]` and `H ∈ K_η[L]` on countable
  carriers, `η < ω₁`, matching at a system level `ι ≤ η` gives `BFEquiv ι` of the base reducts.
  Induction on `ι` (`Ordinal.limitRecOn`): (i) at `0`; at `ι + 1`, `BFEquiv.succ` with the
  induction hypothesis at `ι` applied to (iii) and to (ii); at a limit, `BFEquiv.limit` with the
  induction hypothesis at each `γ < ι` applied to (iii).  Monotonicity is used together with the
  induction, not alone.
* `backAndForthEmptyTupleTarget`: two coded models of `σ[L]` with lifts in `K_β[L]` that realize
  a common invariant are `bfEquivSetoid templateSentence β`-related.  What is matched at `n = 0`:
  one invariant `Q_c` (of any arity `k > 0`) realized in both lifts.
* `realizedInvariantTarget`: every member of `K_β[L]` realizes some invariant
  (`IsTemplateCompatible.exists_relMap_invariant_comp`).
* `countableBFClassesTarget`: for every `β < ω₁`, countably many classes of
  `bfEquivSetoid templateSentence β` ([AFK26, Theorem 2.19]): the classes of maximal stage at
  least `β` inject into the countable set of invariants fixed at `β` (the field `countable` of
  `templateInvariantSystem`, through `realizedInvariantTarget` and
  `eq_of_realize_same_invariant`); the classes of maximal stage below `β` are images of the
  countably many isomorphism classes of maximal stage `γ < β`
  (`countable_setOf_maximalStageOfClass_eq`, `isoSetoid_refines_bfEquivSetoid`).
* `thinnessTarget`: `¬ templateSentence.{0}.HasPerfectSetOfPairwiseNonisomorphicNatModels`, by
  `MainTheorem.isThinOnNatModels_of_countable_bfClasses`.
* `theorem436Target`: `MainTheorem.HasThinAlephOneSpectrum templateSentence.{0}`, from
  `templateSentenceAlephOneTarget` and `thinnessTarget`.
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

/-- **Matching is symmetric**: the same witnesses, with the roles of `G` and `H` exchanged.
Correspondence with the printed definitions. -/
theorem IsMatchedAt.symm {ι : Ordinal.{u}} {M : Type v} {N : Type w}
    {G : templateLanguage.{u}.Structure M} {H : templateLanguage.{u}.Structure N} {n : ℕ}
    {x : Fin n → M} {y : Fin n → N} (h : IsMatchedAt ι G H x y) : IsMatchedAt ι H G y x := by
  obtain ⟨k, hk, c, a, b, f, hx, hy, ha, hb⟩ := h
  exact ⟨k, hk, c, b, a, f, hy, hx, hb, ha⟩

/-- **An invariant of a projection descends**: if `τ_ι'(G) ⊨ Q_c(a)` and `ι ≤ ι'`, then
`τ_ι(G) ⊨ Q_{τ_ι(c)}(a)` (`projectStructure_projectStructure_of_le`,
`relMap_projectStructure_invariant`).  Correspondence with the printed definitions. -/
theorem relMap_projectStructure_project_of_le {ι ι' : Ordinal.{u}} (hle : ι ≤ ι') {M : Type v}
    {G : templateLanguage.{u}.Structure M} {k : ℕ} {hk : 0 < k} {c : LegalClass.{u} k}
    {a : Fin k → M}
    (ha : RelMap (L := templateLanguage.{u}) (self := projectStructure ι' G)
      (TemplateSymbol.invariant c hk) a) :
    RelMap (L := templateLanguage.{u}) (self := projectStructure ι G)
      (TemplateSymbol.invariant (c.project ι) hk) a := by
  rw [← projectStructure_projectStructure_of_le G hle]
  exact ⟨c, rfl, ha⟩

/-- **An invariant along an equality of arities**: an invariant of `z` on `n` places gives an
invariant of `z ∘ Fin.cast e.symm` on `n'` places, for `e : n = n'`.  Native construction. -/
theorem exists_relMap_invariant_cast {M : Type v} {G : templateLanguage.{u}.Structure M}
    {n n' : ℕ} (e : n = n') (z : Fin n → M) (hn : 0 < n) (d : LegalClass.{u} n)
    (h : RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant d hn) z) :
    ∃ (d' : LegalClass.{u} n') (hn' : 0 < n'),
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant d' hn')
        (z ∘ Fin.cast e.symm) := by
  subst e
  exact ⟨d, hn, h⟩

/-- **The closed extension of an invariant tuple by a new point** (the case of a genuinely new
point in the extension steps): in a compatible `G`, if `G ⊨ Q_c(a)` and `m` is not an entry of
`a`, there are `l`, a tuple `w` on `k + (l + 1)` places with an invariant `Q_d`, extending `a`
literally (`w ∘ Fin.castAdd (l + 1) = a`) and with `m` at the place `Fin.natAdd k 0`, and the pair
`(Q_d(x̄ ȳ), Q_c(x̄))` is in `ID[L]`.  Route: `Fin.snoc a m` is injective
(`IsTemplateCompatible.injective_of_relMap_invariant`, `Fin.snoc_injective_of_injective`); the
closure clause of the geometry (`IsGeometry.exists_closed`) and `IsStructuredGeometry.closed_iff`
give a closed extension with an invariant, recast along `k + 1 + l = k + (l + 1)`
(`exists_relMap_invariant_cast`); the pair by `IsTemplateCompatible.relMap_comp_iff` and
`mk_atom_mem_templateDiagramPairs_iff`.  Correspondence with the printed definitions. -/
theorem IsTemplateCompatible.exists_closed_extension {M : Type v}
    {G : templateLanguage.{u}.Structure M} (hG : IsTemplateCompatible G) {k : ℕ} (hk : 0 < k)
    {c : LegalClass.{u} k} {a : Fin k → M}
    (ha : RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hk) a)
    {m : M} (hm : m ∉ Set.range a) :
    ∃ (l : ℕ) (w : Fin (k + (l + 1)) → M) (d : LegalClass.{u} (k + (l + 1)))
      (hd : 0 < k + (l + 1)), w ∘ Fin.castAdd (l + 1) = a ∧ w (Fin.natAdd k 0) = m ∧
        RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant d hd) w ∧
        (⟨k + (l + 1), TemplateSymbol.invariant d hd,
          Correspondence.atom (L := templateLanguage) (TemplateSymbol.invariant c hk)
            (Fin.castAdd (l + 1))⟩ : Correspondence.DiagramPair templateLanguage.{u}) ∈
          templateDiagramPairs := by
  have hinj : Function.Injective (Fin.snoc a m : Fin (k + 1) → M) :=
    Fin.snoc_injective_of_injective (hG.injective_of_relMap_invariant ha) hm
  obtain ⟨l, z, hz, hzP⟩ := hG.1.isGeometry.exists_closed (Nat.succ_pos k) _ hinj
  obtain ⟨Q, hQ, hQz⟩ := (hG.1.closed_iff _ z).mp hzP
  rcases Q with _ | ⟨d, hd⟩ | _ <;> try exact (hQ : False).elim
  have e : k + 1 + l = k + (l + 1) := by omega
  obtain ⟨d', hd', hw⟩ := exists_relMap_invariant_cast e z hd d hQz
  have hwa : z ∘ Fin.cast e.symm ∘ Fin.castAdd (l + 1) = a := by
    funext i
    have hi : Fin.cast e.symm (Fin.castAdd (l + 1) i) = Fin.castAdd l (Fin.castSucc i) :=
      Fin.ext rfl
    have := congrFun hz (Fin.castSucc i)
    simp only [Function.comp_apply, Fin.snoc_castSucc] at this
    simp only [Function.comp_apply, hi, this]
  have hwq : (z ∘ Fin.cast e.symm) (Fin.natAdd k 0) = m := by
    have hi : Fin.cast e.symm (Fin.natAdd k (0 : Fin (l + 1))) = Fin.castAdd l (Fin.last k) :=
      Fin.ext rfl
    have := congrFun hz (Fin.last k)
    simp only [Function.comp_apply, Fin.snoc_last] at this
    simp only [Function.comp_apply, hi, this]
  refine ⟨l, z ∘ Fin.cast e.symm, d', hd', hwa, hwq, hw,
    (mk_atom_mem_templateDiagramPairs_iff hd' d' _ _).mpr ((hG.relMap_comp_iff hw _ _).mp ?_)⟩
  rw [Function.comp_assoc, hwa]
  exact ha

/-! ### The three ingredients -/

section Ingredients

variable (M : Type v) (N : Type w)

/-- **Target (i): atomic agreement at level `0`**: on countable carriers, for `η < ω₁`,
`G ∈ K_η[L]` and `H ∈ K_η[L]`, tuples matched at the system level `0` have the same atomic type in
the base reducts (`SameAtomicType`: equalities among the places, repeated entries included, and
every symbol of `L_c[L]` along every map of places).  Proved (`atomicAgreementTarget`).
Correspondence with the
printed definitions. -/
def AtomicAgreementTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N), IsMatchedAt 0 G H x y →
        @SameAtomicType baseTemplateLanguage.{u} M (baseReduct G) n N (baseReduct H) x y

/-- **(i) Atomic agreement at level `0`** (`AtomicAgreementTarget M N`).  Write `x = a ∘ f`,
`y = b ∘ f` with `τ_0(G) ⊨ Q_c(a)` and `τ_0(H) ⊨ Q_c(b)`; `τ_0(G) ∈ K_0[L]` and `τ_0(H) ∈ K_0[L]`
are compatible (`projectionTarget`).  Equalities, repeated entries included: `a` and `b` are
injective (`IsTemplateCompatible.injective_of_relMap_invariant`), so
`x i = x j ↔ f i = f j ↔ y i = y j`.  A symbol `R` of `L_c[L]` along `g`: `τ_0` does not change
it, and it holds of `a ∘ (f ∘ g)` exactly when `c.Holds R (f ∘ g)`
(`IsTemplateCompatible.relMap_comp_iff`), on both sides.  Correspondence with the printed
definitions. -/
theorem atomicAgreementTarget : AtomicAgreementTarget.{u, v, w} M N := by
  rintro hcM hcN η hη G hG H hH n _ _ ⟨k, hk, c, a, b, f, rfl, rfl, ha, hb⟩ idx
  have hG0 := (projectionTarget η 0 M hcM hη zero_le G hG).2.1
  have hH0 := (projectionTarget η 0 N hcN hη zero_le H hH).2.1
  cases idx with
  | eq i j =>
    change a (f i) = a (f j) ↔ b (f i) = b (f j)
    rw [(hG0.injective_of_relMap_invariant ha).eq_iff,
      (hH0.injective_of_relMap_invariant hb).eq_iff]
  | rel R g =>
    cases R with
    | closed hl =>
      exact (hG0.relMap_comp_iff ha (TemplateSymbol.closed hl) (f ∘ g)).trans
        (hH0.relMap_comp_iff hb (TemplateSymbol.closed hl) (f ∘ g)).symm
    | base c' h0 hl =>
      exact (hG0.relMap_comp_iff ha (TemplateSymbol.base c' h0 hl) (f ∘ g)).trans
        (hH0.relMap_comp_iff hb (TemplateSymbol.base c' h0 hl) (f ∘ g)).symm

/-- **Target (ii), forth: the extension step at a successor level**: on countable carriers, for
`η < ω₁`, `G ∈ K_η[L]`, `H ∈ K_η[L]` and a system level `ι` with `succ ι ≤ η`, if `x` and `y` are
matched at `succ ι`, then every point `m` of `M` has a point `m'` of `N` with `Fin.snoc x m` and
`Fin.snoc y m'` matched at `ι`.  Proved (`forthStepTarget`).  Correspondence with the printed
definitions. -/
def ForthStepTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ ι : Ordinal.{u}, Order.succ ι ≤ η → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
        IsMatchedAt (Order.succ ι) G H x y →
          ∀ m : M, ∃ m' : N, IsMatchedAt ι G H (Fin.snoc x m) (Fin.snoc y m')

/-- **(ii) The forth step** (`ForthStepTarget M N`).  Write `x = a ∘ f`, `y = b ∘ f` with
`τ_{ι+1}(G) ⊨ Q_c(a)` and `τ_{ι+1}(H) ⊨ Q_c(b)`, both in `K_{ι+1}[L]` (`projectionTarget`).

* **The point `m` is an entry `a p` of the witnessing tuple**: the same witnesses at `ι`
  (`relMap_projectStructure_project_of_le`), read along `Fin.snoc f p`; `m' = b p`.
* **The point `m` is new** (not an entry of `a`): `Fin.snoc a m` is injective, and the closure
  clause of the geometry (`IsGeometry.exists_closed`) extends it to a closed tuple, recast as
  `w : Fin (k + (l + 1)) → M` with `w ∘ Fin.castAdd (l + 1) = a` and `w q = m`
  (`q = Fin.natAdd k 0`), with an invariant `Q_d` in `τ_{ι+1}(G)`
  (`IsStructuredGeometry.closed_iff`, `exists_relMap_invariant_cast`).  The pair
  `(Q_d(x̄ ȳ), Q_c(x̄))` is in `ID[L]` (`IsTemplateCompatible.relMap_comp_iff`,
  `mk_atom_mem_templateDiagramPairs_iff`).  `ι`-density of `τ_{ι+1}(H)`
  (`weakSystemClausesTarget`, `ProjectedDensityAt ι`) gives `y'` and `s` with
  `τ_ι(s) = τ_ι(d)` and `τ_{ι+1}(H) ⊨ Q_s(Fin.append b y')`, the old tuple preserved literally:
  `Fin.append b y' ∘ Fin.castAdd (l + 1) = b` (`Fin.append_left`).  Then `m' = Fin.append b y' q`,
  and the witnesses at `ι` are `w`, `Fin.append b y'`, the class `τ_ι(d)`, along
  `Fin.snoc (Fin.castAdd (l + 1) ∘ f) q`.

Correspondence with the printed definitions. -/
theorem forthStepTarget : ForthStepTarget.{u, v, w} M N := by
  intro hcM hcN η hη G hG H hH ι hs n x y hm m
  obtain ⟨k, hk, c, a, b, f, rfl, rfl, ha, hb⟩ := hm
  have hsη : Order.succ ι < ω₁ := hs.trans_lt hη
  have hG' := projectionTarget η (Order.succ ι) M hcM hη hs G hG
  have hH' := projectionTarget η (Order.succ ι) N hcN hη hs H hH
  have hle : ι ≤ Order.succ ι := Order.le_succ ι
  by_cases hmem : m ∈ Set.range a
  · -- the extension point is already an entry of the witnessing closed tuple
    obtain ⟨p, rfl⟩ := hmem
    refine ⟨b p, k, hk, c.project ι, a, b, Fin.snoc f p, ?_, ?_,
      relMap_projectStructure_project_of_le hle ha, relMap_projectStructure_project_of_le hle hb⟩
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  · -- a genuinely new point
    obtain ⟨l, w, d', hd', hwa, hwq, hw, hpair⟩ :=
      hG'.2.1.exists_closed_extension hk ha hmem
    set q : Fin (k + (l + 1)) := Fin.natAdd k 0
    have hpd := (weakSystemClausesTarget N hcN (Order.succ ι) hsη _ hH').2.2.2.1 ι
      (Order.lt_succ ι)
    obtain ⟨y', s, hsd, hs'⟩ := hpd hk c d' hpair b hb
    -- the old tuple is preserved literally
    have hold : Fin.append b y' ∘ Fin.castAdd (l + 1) = b := funext fun i ↦ Fin.append_left b y' i
    refine ⟨Fin.append b y' q, k + (l + 1), hd', d'.project ι, w, Fin.append b y',
      Fin.snoc (Fin.castAdd (l + 1) ∘ f) q, ?_, ?_, relMap_projectStructure_project_of_le hle hw,
      ?_⟩
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [hwq]
      · simpa using (congrFun hwa (f j)).symm
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simp only [Fin.snoc_castSucc, Function.comp_apply]
        exact (congrFun hold (f j)).symm
    · rw [← hsd]
      exact relMap_projectStructure_project_of_le hle hs'

/-- **Target (ii), back: the extension step at a successor level**, the other direction: every
point `m'` of `N` has a point `m` of `M` with `Fin.snoc x m` and `Fin.snoc y m'` matched at `ι`.
Proved (`backStepTarget`).  Correspondence with the printed definitions. -/
def BackStepTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ ι : Ordinal.{u}, Order.succ ι ≤ η → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
        IsMatchedAt (Order.succ ι) G H x y →
          ∀ m' : N, ∃ m : M, IsMatchedAt ι G H (Fin.snoc x m) (Fin.snoc y m')

/-- **(ii) The back step** (`BackStepTarget M N`): the forth step with the roles of `(M, G)` and
`(N, H)` exchanged (`forthStepTarget N M`, `IsMatchedAt.symm`); its two cases (an entry of the
witnessing tuple, a genuinely new point) are those of `forthStepTarget`.  Correspondence with the
printed definitions. -/
theorem backStepTarget : BackStepTarget.{u, v, w} M N := by
  intro hcM hcN η hη G hG H hH ι hs n x y hm m'
  obtain ⟨m, h⟩ := forthStepTarget N M hcN hcM η hη H hH G hG ι hs y x hm.symm m'
  exact ⟨m, h.symm⟩

/-- **Target (iii): matching descends to lower levels** (the limit clause, and the first conjunct
of the successor clause): matching at a system level `ι'` gives matching at every `ι ≤ ι'`, for
arbitrary structures.  Proved (`matchedAtMonotoneTarget`).  Correspondence with the printed
definitions. -/
def MatchedAtMonotoneTarget : Prop :=
  ∀ (G : templateLanguage.{u}.Structure M) (H : templateLanguage.{u}.Structure N)
    (ι ι' : Ordinal.{u}), ι ≤ ι' → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
      IsMatchedAt ι' G H x y → IsMatchedAt ι G H x y

/-- **(iii) Matching descends to lower levels** (`MatchedAtMonotoneTarget M N`): the same tuples
and map, with the class `τ_ι(c)` (`relMap_projectStructure_project_of_le`).  Correspondence with
the printed definitions. -/
theorem matchedAtMonotoneTarget : MatchedAtMonotoneTarget.{u, v, w} M N := by
  rintro G H ι ι' hle n x y ⟨k, hk, c, a, b, f, hx, hy, ha, hb⟩
  exact ⟨k, hk, c.project ι, a, b, f, hx, hy, relMap_projectStructure_project_of_le hle ha,
    relMap_projectStructure_project_of_le hle hb⟩

/-- **Target: the tuple-level core of [AFK26, Proposition 2.18] for `K[L]`**: on countable
carriers, for `η < ω₁`, `G ∈ K_η[L]` and `H ∈ K_η[L]`, tuples matched at a system level `ι ≤ η`
are back-and-forth equivalent at level `ι` in the base reducts: `BFEquiv ι` of
`(G↾L_c[L], x)` and `(H↾L_c[L], y)`.  The level of `BFEquiv` is the system level `ι`, not the
label cutoff `λ_ι`.  Proved (`backAndForthCoreTarget`), by induction on `ι` with
`AtomicAgreementTarget`,
`ForthStepTarget`, `BackStepTarget` and `MatchedAtMonotoneTarget`.  Correspondence with the
printed definitions. -/
def BackAndForthCoreTarget : Prop :=
  Countable M → Countable N → ∀ η : Ordinal.{u}, η < ω₁ →
    ∀ G ∈ templateStageClass M η, ∀ H ∈ templateStageClass N η,
      ∀ ι : Ordinal.{u}, ι ≤ η → ∀ {n : ℕ} (x : Fin n → M) (y : Fin n → N),
        IsMatchedAt ι G H x y →
          @BFEquiv baseTemplateLanguage.{u} M (baseReduct G) N (baseReduct H) ι n x y

/-- **The tuple-level core** (`BackAndForthCoreTarget M N`), by induction on the system level `ι`
(`Ordinal.limitRecOn`), for all tuples at once:

* `ι = 0`: `BFEquiv.zero` and atomic agreement (`atomicAgreementTarget`);
* `ι + 1 ≤ η`: `BFEquiv.succ`; the first conjunct by the induction hypothesis at `ι` applied to the
  matching at `ι` (`matchedAtMonotoneTarget`), the forth and back conjuncts by the induction
  hypothesis at `ι` applied to the extensions (`forthStepTarget`, `backStepTarget`);
* `ι` a limit: `BFEquiv.limit`; for `γ < ι`, the induction hypothesis at `γ` applied to the
  matching at `γ` (`matchedAtMonotoneTarget`).

Monotonicity of matching is used together with the induction hypothesis, never alone.
Correspondence with the printed definitions. -/
theorem backAndForthCoreTarget : BackAndForthCoreTarget.{u, v, w} M N := by
  intro hcM hcN η hη G hG H hH ι
  induction ι using Ordinal.limitRecOn with
  | zero =>
    intro _ n x y hm
    rw [@BFEquiv.zero baseTemplateLanguage.{u} M (baseReduct G) N (baseReduct H) n x y]
    exact atomicAgreementTarget M N hcM hcN η hη G hG H hH x y hm
  | add_one ι ih =>
    intro hle n x y hm
    rw [← Order.succ_eq_add_one] at hle hm ⊢
    rw [@BFEquiv.succ baseTemplateLanguage.{u} M (baseReduct G) N (baseReduct H) n ι x y]
    have hle' : ι ≤ η := (Order.le_succ ι).trans hle
    refine ⟨ih hle' x y (matchedAtMonotoneTarget M N G H ι _ (Order.le_succ ι) x y hm),
      fun m ↦ ?_, fun m' ↦ ?_⟩
    · obtain ⟨m', h⟩ := forthStepTarget M N hcM hcN η hη G hG H hH ι hle x y hm m
      exact ⟨m', ih hle' _ _ h⟩
    · obtain ⟨m, h⟩ := backStepTarget M N hcM hcN η hη G hG H hH ι hle x y hm m'
      exact ⟨m, ih hle' _ _ h⟩
  | limit ι hlim ih =>
    intro hle n x y hm
    rw [@BFEquiv.limit baseTemplateLanguage.{u} M (baseReduct G) N (baseReduct H) n ι hlim x y]
    intro γ hγ
    exact ih γ hγ (hγ.le.trans hle) x y (matchedAtMonotoneTarget M N G H γ ι hγ.le x y hm)

end Ingredients

/-! ### The empty tuple and the classes -/

/-- **Target: the passage to the empty tuple** [AFK26, Proposition 2.18, for `K[L]`]: for
`β < ω₁` and two models of `σ[L]` coded on `ℕ`, with lifts `G₁ ∈ K_β[L]` and `G₂ ∈ K_β[L]` on `ℕ`
(`G_i↾L_c[L]` the decoded structure) that realize one common invariant `Q_c` (of any arity
`k > 0`), the two codes are related by `bfEquivSetoid templateSentence β`, that is,
`BFEquiv β 0 Fin.elim0 Fin.elim0`.  At `n = 0` the matching at the system level `β` is exactly
this common invariant (`f = Fin.elim0`, `τ_β(G_i) = G_i`).  Proved
(`backAndForthEmptyTupleTarget`).  Correspondence with
the printed definitions. -/
def BackAndForthEmptyTupleTarget : Prop :=
  ∀ β : Ordinal.{0}, β < ω₁ → ∀ c₁ c₂ : ModelsOf templateSentence.{0},
    ∀ G₁ ∈ templateStageClass ℕ β, ∀ G₂ ∈ templateStageClass ℕ β,
      baseReduct G₁ = c₁.1.toStructure → baseReduct G₂ = c₂.1.toStructure →
      (∃ (k : ℕ) (hk : 0 < k) (c : LegalClass.{0} k) (a b : Fin k → ℕ),
        RelMap (L := templateLanguage.{0}) (self := G₁) (TemplateSymbol.invariant c hk) a ∧
        RelMap (L := templateLanguage.{0}) (self := G₂) (TemplateSymbol.invariant c hk) b) →
        (bfEquivSetoid templateSentence.{0} β).r c₁ c₂

/-- **The passage to the empty tuple** (`BackAndForthEmptyTupleTarget`): the empty tuples are
matched at the system level `β` along `Fin.elim0` (`τ_β(G_i) = G_i`), so the core
(`backAndForthCoreTarget ℕ ℕ` at `ι = η = β`, `n = 0`) gives `BFEquiv β 0` of the base reducts,
which are the decoded structures.  Correspondence with the printed definitions. -/
theorem backAndForthEmptyTupleTarget : BackAndForthEmptyTupleTarget := by
  rintro β hβ c₁ c₂ G₁ hG₁ G₂ hG₂ h₁ h₂ ⟨k, hk, c, a, b, ha, hb⟩
  have hm : IsMatchedAt β G₁ G₂ (Fin.elim0 : Fin 0 → ℕ) (Fin.elim0 : Fin 0 → ℕ) := by
    refine ⟨k, hk, c, a, b, Fin.elim0, funext fun i ↦ i.elim0, funext fun i ↦ i.elim0, ?_, ?_⟩
    · rw [hG₁.2.2.1]
      exact ha
    · rw [hG₂.2.2.1]
      exact hb
  have h := backAndForthCoreTarget ℕ ℕ inferInstance inferInstance β hβ G₁ hG₁ G₂ hG₂ β le_rfl
    _ _ hm
  change @BFEquiv baseTemplateLanguage.{0} ℕ c₁.1.toStructure ℕ c₂.1.toStructure β 0
    Fin.elim0 Fin.elim0
  rw [← h₁, ← h₂]
  exact h

/-- **Target: every member of `K_β[L]` realizes an invariant**: some `Q_c` holds of some tuple.
Proved (`realizedInvariantTarget`); route: a point of the (nonempty) carrier, the closure clause of
the geometry
on the one-point tuple (`IsGeometry.exists_closed`), and `IsStructuredGeometry.closed_iff`.
Correspondence with the printed definitions. -/
def RealizedInvariantTarget (M : Type v) : Prop :=
  ∀ β : Ordinal.{u}, ∀ G ∈ templateStageClass M β,
    ∃ (k : ℕ) (hk : 0 < k) (c : LegalClass.{u} k) (a : Fin k → M),
      RelMap (L := templateLanguage.{u}) (self := G) (TemplateSymbol.invariant c hk) a

/-- **Every member of `K_β[L]` realizes an invariant** (`RealizedInvariantTarget M`): a point `p`
of the nonempty carrier; the one-point tuple at `p` is a sequence of places of a tuple with an
invariant (`IsTemplateCompatible.exists_relMap_invariant_comp`, from `IsGeometry.exists_closed`
and `IsStructuredGeometry.closed_iff`).  Correspondence with the printed definitions. -/
theorem realizedInvariantTarget (M : Type v) : RealizedInvariantTarget.{u, v} M := by
  intro β G hG
  obtain ⟨p⟩ := hG.1
  obtain ⟨k, hk, c, a, -, ha, -⟩ := hG.2.1.exists_relMap_invariant_comp one_pos fun _ ↦ p
  exact ⟨k, hk, c, a, ha⟩

/-- **Target: countably many back-and-forth classes at every level** (the input of
`MainTheorem.isThinOnNatModels_of_countable_bfClasses`; [AFK26, Theorem 2.19 and
Theorem 2.25 (b)] for `K[L]`): for every `β < ω₁`, the classes of
`bfEquivSetoid templateSentence β` on the models of `σ[L]` coded on `ℕ` are countably many.
Proved (`countableBFClassesTarget`).  Correspondence with the printed
definitions. -/
def CountableBFClassesTarget : Prop :=
  ∀ β : Ordinal.{0}, β < ω₁ → Countable (Quotient (bfEquivSetoid templateSentence.{0} β))

/-- **The lift at `β` of a coded model of maximal stage at least `β`**: the projection `τ_β(H)`
of its maximal lift `(γ, H)`, `β ≤ γ`, is in `K_β[L]` (`projectionTarget`) and has the decoded
structure as its base reduct (`baseReduct_projectStructure`).  Correspondence with the printed
definitions. -/
theorem projectStructure_codedMaximalLift_mem {β : Ordinal.{0}} (c : ModelsOf templateSentence.{0})
    (h : β ≤ codedMaximalStage c) :
    projectStructure β (codedMaximalLift c).2 ∈ templateStageClass ℕ β ∧
      baseReduct (projectStructure β (codedMaximalLift c).2) = c.1.toStructure :=
  ⟨projectionTarget _ β ℕ inferInstance (codedMaximalLift_spec c).1 h _
      (codedMaximalLift_spec c).2.1.1,
    (baseReduct_projectStructure _).trans (codedMaximalLift_spec c).2.2⟩

/-- **Two coded models of maximal stage at least `β` whose lifts at `β` realize one invariant are
back-and-forth equivalent at `β`** (`backAndForthEmptyTupleTarget` with the lifts
`projectStructure_codedMaximalLift_mem`).  Correspondence with the printed definitions. -/
theorem eq_of_realize_same_invariant {β : Ordinal.{0}} (hβ : β < ω₁)
    {x x' : Quotient (bfEquivSetoid templateSentence.{0} β)} (hx : β ≤ codedMaximalStage x.out)
    (hx' : β ≤ codedMaximalStage x'.out) (Q : Σ n, templateSignature.{0}.Invariant n)
    (ha : ∃ a : Fin Q.1 → ℕ, RelMap (L := templateLanguage.{0})
      (self := projectStructure β (codedMaximalLift x.out).2) Q.2.1 a)
    (ha' : ∃ a : Fin Q.1 → ℕ, RelMap (L := templateLanguage.{0})
      (self := projectStructure β (codedMaximalLift x'.out).2) Q.2.1 a) : x = x' := by
  obtain ⟨n, Q⟩ := Q
  obtain ⟨c, hk, rfl⟩ := templateInvariant_eq Q
  obtain ⟨a, ha⟩ := ha
  obtain ⟨a', ha'⟩ := ha'
  obtain ⟨hm, hb⟩ := projectStructure_codedMaximalLift_mem x.out hx
  obtain ⟨hm', hb'⟩ := projectStructure_codedMaximalLift_mem x'.out hx'
  have h := backAndForthEmptyTupleTarget β hβ x.out x'.out _ hm _ hm' hb hb'
    ⟨n, hk, c, a, a', ha, ha'⟩
  rw [← Quotient.out_eq x, ← Quotient.out_eq x']
  exact Quotient.sound h

/-- **Countably many back-and-forth classes at every level** (`CountableBFClassesTarget`),
[AFK26, Theorem 2.19] for `K[L]`.  Fix `β < ω₁`; every class `x` has a representative code.

* **Maximal stage at least `β`**: the lift `τ_β(H)` in `K_β[L]`
  (`projectStructure_codedMaximalLift_mem`) realizes an invariant
  (`realizedInvariantTarget`), fixed by `τ_β`
  (`IsTemplateCompatible.project_eq_of_relMap_invariant`), hence in the countable set of
  invariants fixed at `β` (the field `countable` of `templateInvariantSystem`).  Choosing one is
  injective on these classes (`eq_of_realize_same_invariant`).
* **Maximal stage below `β`**: the class is the image of an isomorphism class of maximal stage
  `γ < β`; these are countably many (`countable_setOf_maximalStageOfClass_eq` over the countably
  many `γ < β`, `Cardinal.countable_Iio_of_lt_omega_one`), and isomorphism refines `bfEquivSetoid`
  (`isoSetoid_refines_bfEquivSetoid`).

Correspondence with the printed definitions. -/
theorem countableBFClassesTarget : CountableBFClassesTarget := by
  intro β hβ
  let toBF : Quotient (isoSetoid templateSentence.{0}) →
      Quotient (bfEquivSetoid templateSentence.{0} β) :=
    Quotient.lift (fun c ↦ Quotient.mk (bfEquivSetoid templateSentence.{0} β) c)
      fun _ _ h ↦ Quotient.sound (isoSetoid_refines_bfEquivSetoid _ _ h)
  -- the classes of maximal stage below `β`
  have hlow : (toBF '' {q | maximalStageOfClass q < β}).Countable := by
    refine Set.Countable.image ?_ _
    have he : {q | maximalStageOfClass q < β} =
        ⋃ γ ∈ Set.Iio β, {q | maximalStageOfClass q = γ} := by
      ext q
      simp
    rw [he]
    exact (Cardinal.countable_Iio_of_lt_omega_one hβ).biUnion fun γ hγ ↦
      countable_setOf_maximalStageOfClass_eq (lt_trans hγ hβ)
  -- the classes of maximal stage at least `β`
  let S := {Q : Σ n, templateSignature.{0}.Invariant n |
    templateInvariantSystem.τ ⟨β, hβ⟩ Q.2 = Q.2}
  have hS : S.Countable := templateInvariantSystem.countable ⟨β, hβ⟩
  let A := {x : Quotient (bfEquivSetoid templateSentence.{0} β) | β ≤ codedMaximalStage x.out}
  have hex (x : A) : ∃ Q ∈ S, ∃ a : Fin Q.1 → ℕ, RelMap (L := templateLanguage.{0})
      (self := projectStructure β (codedMaximalLift x.1.out).2) Q.2.1 a := by
    obtain ⟨hmem, -⟩ := projectStructure_codedMaximalLift_mem x.1.out x.2
    obtain ⟨k, hk, c, a, ha⟩ := realizedInvariantTarget ℕ β _ hmem
    exact ⟨⟨k, ⟨TemplateSymbol.invariant c hk, trivial⟩⟩,
      (templateInvariantProject_eq_self_iff β _).mpr
        (hmem.2.1.project_eq_of_relMap_invariant hmem.2.2.1 ha), a, ha⟩
  have hA : A.Countable := by
    have := hS.to_subtype
    refine Set.countable_coe_iff.mp (Function.Injective.countable
      (f := fun x : A ↦ (⟨(hex x).choose, (hex x).choose_spec.1⟩ : S)) fun x x' hxx' ↦ ?_)
    have hQ : (hex x).choose = (hex x').choose := congrArg Subtype.val hxx'
    exact Subtype.ext (eq_of_realize_same_invariant hβ x.2 x'.2 _ (hex x).choose_spec.2
      (hQ ▸ (hex x').choose_spec.2))
  -- every class is in one of the two parts
  have hcover : (Set.univ : Set (Quotient (bfEquivSetoid templateSentence.{0} β))) ⊆
      A ∪ toBF '' {q | maximalStageOfClass q < β} := by
    rintro x -
    by_cases h : β ≤ codedMaximalStage x.out
    · exact Or.inl h
    · exact Or.inr ⟨Quotient.mk _ x.out, not_le.mp h, Quotient.out_eq x⟩
  exact Set.countable_univ_iff.mp ((hA.union hlow).mono hcover)

/-! ### Thinness and the assembly -/

/-- **Target: thinness of `σ[L]`** [AFK26, Theorem 4.36, the second conclusion]: there is no
perfect set of pairwise nonisomorphic models of `σ[L]` coded on `ℕ`.  This is the second conjunct
of `Theorem436Target`.  Proved (`thinnessTarget`), from `CountableBFClassesTarget`
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

/-- **Thinness of `σ[L]`** (`ThinnessTarget`): `thinnessTarget_of_countableBFClassesTarget` with
`countableBFClassesTarget`.  Correspondence with the printed definitions. -/
theorem thinnessTarget : ThinnessTarget :=
  thinnessTarget_of_countableBFClassesTarget countableBFClassesTarget

/-- **[AFK26, Theorem 4.36] for `σ[L]`** (`Theorem436Target`): the models of `σ[L]` coded on `ℕ`
have exactly `ℵ₁` isomorphism classes (`templateSentenceAlephOneTarget`) and no perfect set of
pairwise nonisomorphic coded models (`thinnessTarget`).  Correspondence with the printed
definitions. -/
theorem theorem436Target : Theorem436Target :=
  theorem436Target_of_thinnessTarget thinnessTarget

end VaughtConjecture
