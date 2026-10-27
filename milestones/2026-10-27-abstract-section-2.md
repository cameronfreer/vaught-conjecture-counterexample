# Milestone: Abstract Section 2: counting, thinness, and the K[L] instance, 27 October 2026

The formal counterpart of the abstract theorems of Section 2 of [AFK26] for arbitrary weak and
qualifying systems — Proposition 2.18, Theorem 2.19, Lemma 2.22, Theorem 2.25 (a) and (b), and
Theorem 2.27 in a form coded on `ℕ` — and of their instance for the template system `K[L]`, which
gives a second proof of Theorem 4.36; their axioms, and the checks that verify them, at one commit.
Proposed tag: `abstract-section-2-2026-10-27`, an annotated tag on the commit below.  The records
of Propositions 4.34 and 4.35, of Theorem 4.36 and of Proposition 4.30
(`2026-10-15-proposition-4-34.md`, `2026-10-15-proposition-4-35.md`, `2026-10-25-theorem-4-36.md`,
`2026-10-25-proposition-4-30.md`) and the addendum of the published-version audit
(`2026-10-25-published-v1-audit.md`) are unchanged.

## The verified commit

| Item | Value |
| --- | --- |
| Commit | `3e0bf29228ed3938ee01afc0dae13b08b77c7fe9` (`main`, "The template system is a qualifying system with qualifying sentence sigma[L], and a second proof of Theorem 4.36 by the abstract route of Section 2 (#261)") |
| Tree | `9494226ceaa20ad60225ad5af200d676da481b89` |
| Toolchain | `leanprover/lean4:v4.35.0-rc3` (`lean-toolchain`) |
| InfinitaryLogic | [`cameronfreer/infinitary-logic`](https://github.com/cameronfreer/infinitary-logic) at `eb9f12dc983778eec067c0875170798efd34c7f0` (v6.1.0) |
| ComputableModelTheory | [`cameronfreer/computable-model-theory`](https://github.com/cameronfreer/computable-model-theory) at `a1fe76155a98f03933f7de0811e03b2473dd2e21` |
| Mathlib | the fork [`cameronfreer/mathlib4`](https://github.com/cameronfreer/mathlib4) at `346a4bd3f95e8591976c91259badc6d2c300f638`, inherited from InfinitaryLogic's manifest (`lake-manifest.json`) |
| Manuscript | [AFK26], the hash-pinned source draft (not part of this repository), SHA-256 of its source `654b2780d08e9aee902d0553576c8f58f82730ccba7f4926757e45b1c02a755f`; Definitions 2.6–2.8, 2.10, 2.17, 2.20, 2.21 and 2.23, Proposition 2.18, Theorems 2.19, 2.25 and 2.27, and Theorem 4.36 read identically, in number and text, in the published version [AFK26] v1 ([hexagon:2610.00188v1](https://hexagonmath.org/2610.00188v1), PDF SHA-256 `2b3f3aa14c32174a8dae4e343f234cb08ea1027031a14dcd7c651ab6b7d8668d`), per the audit of 25 October 2026 |

The remaining revisions of `lake-manifest.json` are inherited and are recorded there.  CI: the
pull-request checks of #261 passed at its head `774d819`, whose tree is the tree of the squash
commit above (job `build`: build with warnings as errors, `scripts/check.sh --no-build`, the
dependency manifest; job `comparator-replay`; run
[40527961135](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/40527961135),
completed with success on 27 October 2026 (UTC)), and the `main` run
[40532231152](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/40532231152)
passed at the squash-merge commit `3e0bf29`, including the build and the clean Comparator (job
`comparator-clean`: a fresh clone, the root library built from nothing, then
`comparator/check.sh --exact` on the reference statement), completed with success on
27 October 2026 (UTC; job `build` at 16:01:05, job `comparator-clean` at 16:25:58).  The jobs of
that run, as defined for a push to `main`, are `build` and `comparator-clean`; `comparator-replay`
runs only on pull requests and is skipped.

The mathematics was merged in five steps, each a squash merge into `main`; the commit above
carries all five.

| PR | Squash-merge commit | Content | `main` run |
| --- | --- | --- | --- |
| #256 | `45ebabd` | the structures and statements of Section 2; the foundations (projection, rank, maximality, the coding passage) and Lemma 2.22 | [40359441423](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/40359441423), passed, clean Comparator included |
| #257 | `feaab8b` | Proposition 2.18 | [40364918405](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/40364918405), passed, clean Comparator included |
| #259 | `a0cd9f1` | Theorem 2.19 and Theorem 2.25 (b) | [40517554063](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/40517554063), passed, clean Comparator included |
| #260 | `c6d772c` | Theorem 2.25 (a) and Theorem 2.27 | [40532119863](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/40532119863), passed, clean Comparator included |
| #261 | `3e0bf29` | `K[L]` as a qualifying system with qualifying sentence `σ[L]`, and the second proof of Theorem 4.36 | [40532231152](https://github.com/cameronfreer/vaught-conjecture-counterexample/actions/runs/40532231152), passed, clean Comparator included |

The agreement of the audited statements with the published version is a statement about the
manuscript's text; it is distinct from the verification of the Lean theorems, which is what the CI
runs establish.

## The abstract results

Namespace `VaughtConjecture.Correspondence`, directory `VaughtConjecture/Correspondence/Systems/`
(19 files, 3423 lines, all added by #256–#261; no file outside the directory was changed by these
pull requests).  The data are an arbitrary geometry signature `σ` on a language `L`, an invariance
diagram `D`, an invariant system `S : InvariantSystem.{0} σ`, and a base sublanguage
`E : σ.BaseSublanguage Lc`.  Three conclusions are kept distinct below: the general count of
Theorem 2.25 (a); the specialization of Theorem 2.27 coded on `ℕ`; and the second proof of
Theorem 4.36, which is the `K[L]` instance of the abstract theorems.

### 1. Theorem 2.25 (a), general form: exactly `ℵ₁` classes of the base, finite carriers included

The type counted is the isomorphism classes of members of the base on the positive finite carriers
`Fin (n + 1)` and on `ℕ` (`Systems/WeakSystem.lean`):

```lean
abbrev BaseClasses (W : WeakSystem.{w, w', 0} D S) : Type (max wc wc') :=
  (Σ n : ℕ, Quotient (W.baseIsoSetoid E (Fin (n + 1)))) ⊕ Quotient (W.baseIsoSetoid E ℕ)
```

The statement (`Systems/Targets.lean`) and its proof (`Systems/Count.lean`):

```lean
def MkBaseClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) : Prop :=
  Cardinal.mk (W.toWeakSystem.BaseClasses E) = Cardinal.aleph 1

theorem mkBaseClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) :
    W.MkBaseClassesEqAlephOneTarget
```

The base of every qualifying system (carriers in universe `0`) has exactly `ℵ₁` isomorphism
classes on the canonical carriers.  There is no sentence and no infiniteness premise: members of
the base on finite carriers are counted with the others, and their contribution is not assumed
countable on the ground that the language is countable.  That the canonical carriers represent
every member of the base on a countable nonempty carrier, up to isomorphism, is proved
(`baseClassesRepresentTarget`; cover `exists_equiv_baseClassRep`, separation
`eq_of_equiv_baseClassRep`).  The upper bound (`mk_baseClasses_le_aleph_one`) follows the printed
route: by condition (a) each class representative is the reduct of a structure maximal at some
level `δ`, by condition (b) that structure is isomorphic to one of countably many representatives
at `δ`, and at most one class arises from each (`Counting.mk_le_aleph_one_of_countable_cover`).
The lower bound (`aleph_one_le_mk_baseClasses`) also follows the printed route: were the classes
countably many, the bounds of Lemma 2.22 for their representatives (from condition (c)) would have a
countable supremum `α*`; an invariant not fixed by `τ_α*` (`InvariantSystem.ne_univ`) occurs in a
member of `K` (condition (d)), whose reduct is isomorphic to a class representative; the rank bound
is transported along that base isomorphism (`WeakSystem.isFixedAt_of_isLiftAt_of_equiv`), so the
member is fixed at `α*` and the invariant is in the image of `τ_α*`, hence fixed by it
(`InvariantSystem.comp`), a contradiction.  The member given by condition (d) may lie on a finite
carrier; it is moved to `Fin (n + 1)` or `ℕ` by a bijection, with no infiniteness.

For a sentence, the general form counts InfinitaryLogic's coded classes on every `Fin (n + 1)` and
on `ℕ` (`Systems/Spectrum.lean`):

```lean
def IsBaseSentenceOnCarriers (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω) : Prop :=
  ∀ (M : Type) [Countable M] [Nonempty M] (B : Lc.Structure M),
    @Sentenceω.Realize Lc φ M B ↔ W.IsInBase E B

def MkModelClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    [Lc.IsRelational] [Countable (Σ n, Lc.Relations n)] (φ : Lc.Sentenceω) : Prop :=
  W.toWeakSystem.IsBaseSentenceOnCarriers E φ →
    Cardinal.mk ((Σ n : ℕ, Quotient (isoSetoidOn φ (n + 1))) ⊕ Quotient (isoSetoid φ)) =
      Cardinal.aleph 1

theorem mkModelClassesEqAlephOneTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : W.MkModelClassesEqAlephOneTarget E φ
```

If `φ` axiomatizes the base on all countable nonempty carriers, finite or infinite, its coded
classes on all the canonical carriers together number exactly `ℵ₁`: they are in bijection with
`BaseClasses` (`WeakSystem.modelClassesEquiv`).  No infiniteness premise.

Neither proof uses Reconstruction, uniqueness of maximal lifts, a canonical maximal-stage rank or
successor strictness; none of these is a field of `QualifyingSystem` or a hypothesis of any abstract
statement.

### 2. Theorem 2.27, coded on `ℕ`: a specialization, not the unrestricted printed theorem

A qualifying sentence is one whose models coded on `ℕ` are exactly the members of the base on `ℕ`
(`Systems/WeakSystem.lean`, `Systems/QualifyingSystem.lean`):

```lean
def IsBaseSentence (W : WeakSystem.{w, w', 0} D S) [Lc.IsRelational]
    [Countable (Σ n, Lc.Relations n)] (φ : Lc.Sentenceω) : Prop :=
  ∀ c : StructureSpace Lc, c ∈ ModelsOf φ ↔ W.IsInBase E c.toStructure

def IsQualifyingSentence (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) [Lc.IsRelational]
    [Countable (Σ n, Lc.Relations n)] (φ : Lc.Sentenceω) : Prop :=
  W.toWeakSystem.IsBaseSentence E φ
```

The extra hypothesis of the statements that count only models coded on `ℕ`, never a field and not
a printed condition:

```lean
def CountableMembersInfinite : Prop :=
  ∀ (β : SystemLevel) (M : Type v) [Countable M] (G : L.Structure M), G ∈ W.K β M → Infinite M
```

The statement (`Systems/Targets.lean`) and its proof (`Systems/Spectrum.lean`), with the variables
of their section:

```lean
variable {Lc₀ : Language.{0, 1}} [Lc₀.IsRelational] [Countable (Σ n, Lc₀.Relations n)]
variable {E₀ : σ.BaseSublanguage Lc₀}

def HasThinAlephOneSpectrumTarget (W : QualifyingSystem.{w, w', 0, 1, 0} D S E₀)
    (φ : Lc₀.Sentenceω) : Prop :=
  W.IsQualifyingSentence φ → W.CountableMembersInfinite → MainTheorem.HasThinAlephOneSpectrum φ

theorem hasThinAlephOneSpectrumTarget (W : QualifyingSystem.{w, w', 0, 1, 0} D S E₀)
    (φ : Lc₀.Sentenceω) : W.HasThinAlephOneSpectrumTarget φ
```

For a qualifying sentence `φ` of a countable relational language `L_c` in the universes
`Language.{0, 1}`, and under the explicit premise `CountableMembersInfinite`, the models of `φ` coded
on `ℕ` have exactly `ℵ₁` isomorphism classes and there is no perfect set of pairwise
nonisomorphic coded models.  It is the composition (`hasThinAlephOneSpectrumTarget_of`) of the
`ℕ`-coded count `mkClassesEqAlephOneTarget` — `BaseClasses` restricted to its summand on `ℕ`, the
finite summands being empty under `CountableMembersInfinite` (`isEmpty_finClasses`) — with
Theorem 2.25 (b) (`noPerfectSetTarget`, below).  The `ℕ`-coded upper bound
`mkClassesLeAlephOneTarget` (at most `ℵ₁`) has no infiniteness premise.  Printed Theorem 2.27
concerns all countable models of a sentence of an arbitrary countable `L_c`, with no infiniteness
hypothesis; this statement is the specialization to models coded on `ℕ`, with
`CountableMembersInfinite` and `Language.{0, 1}` explicit, and it does not replace the general
conclusion 1.

### 3. Theorem 4.36 by the abstract route: the `K[L]` instance, a second proof

The proposition is the one of the record of Theorem 4.36, unchanged
(`Correspondence/TemplateSystem/Theorem436.lean`):

```lean
def Theorem436Target : Prop :=
  MainTheorem.HasThinAlephOneSpectrum templateSentence.{0}
```

The second proof (`Systems/Theorem436.lean`):

```lean
theorem theorem436Target_abstract : Theorem436Target
```

It applies the coded specialization of Theorem 2.27
(`QualifyingSystem.hasThinAlephOneSpectrumTarget`) to the instance, composed by
`theorem436Target_of_qualifyingSentenceTarget`.  The printed proof of Theorem 4.36 cites
Theorem 2.25 directly; the organization of the Lean proof is not claimed to be the printed one.  The instance is
(`Systems/TemplateInstance.lean`, proved in `Systems/TemplateQualifying.lean`):

```lean
def TemplateQualifyingSentenceTarget : Prop :=
  ∃ (E : templateSignature.{0}.BaseSublanguage baseTemplateLanguage.{0})
    (W : QualifyingSystem.{0, 1, 0, 1, 0} templateDiagram.{0} templateInvariantSystem.{0} E),
    E.incl = baseInclusion ∧ (∀ (β : SystemLevel) (M : Type), W.K β M = templateStageClass M β.1) ∧
      W.CountableMembersInfinite ∧ W.IsQualifyingSentence templateSentence.{0}

theorem templateQualifyingSentenceTarget : TemplateQualifyingSentenceTarget
```

`K[L]` (the classes `templateStageClass`, for the diagram `templateDiagram` and the invariant system
`templateInvariantSystem`) is a qualifying system whose members on countable carriers are infinite,
and `σ[L]` (`templateSentence`) is a qualifying sentence for it.  `theorem436Target_abstract` is
separate from, and does not replace, the concrete proof `theorem436Target`
(`Correspondence/TemplateSystem/BackAndForth.lean`); both prove the same proposition.

**Reconstruction.**  The abstract theorems assume neither Reconstruction nor uniqueness of maximal
lifts.  This `K[L]` instance uses Reconstruction (`reconstructionTarget`, [AFK26, Proposition
4.34]) through maximal completion (`maximalCompletionTarget`) in conditions (a) and (c), but uses
neither maximal-lift uniqueness (`maximalLiftUniqueTarget`) nor maximal-stage invariance
(`maximalStageInvariantTarget`); the concrete `theorem436Target` uses all three.  This dependency
split is the finding of the lane that constructed the instance, obtained by following the transitive
constant dependencies of the two theorems and recorded in the description of #261; the check's
output was not archived, and the record attributes the finding to that report.  The second proof is therefore not free of Reconstruction; it differs from the first in not
counting through the maximal stage.

## The structures

`Systems/Base.lean`, `Systems/WeakSystem.lean`, `Systems/QualifyingSystem.lean`.  Levels are
`SystemLevel = {β : Ordinal.{0} // β < ω₁}` (an abbreviation, the index type of
`InvariantSystem.{0}`).

- **`GeometrySignature.BaseSublanguage σ Lc`** ([AFK26, Convention 2.3]): a language `Lc`, given as
  a parameter so that its universes are visible, with an inclusion `incl : Lc →ᴸ L`, injective on
  symbols (`incl_injective`), whose range is exactly the symbols of `L` that are not invariants
  (`mem_range_iff`); the reduct `BaseSublanguage.reduct` is `G ↦ G↾L_c` on the same carrier.  `Lc`
  is relational (`BaseSublanguage.isRelational`) and countable (`countableRelationsTarget`); in the
  coded statements the countability is an explicit instance premise.
- **`WeakSystem D S`** ([AFK26, Definition 2.17]), fields (docstrings omitted):

```lean
structure WeakSystem (D : InvarianceDiagram σ) (S : InvariantSystem.{0} σ) where
  K : SystemLevel → ∀ M : Type v, Set (L.Structure M)
  compatibleWith : D.IsCompatibleWith S
  nonempty ⦃β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ : G ∈ K β M → Nonempty M
  isoClosed ⦃β : SystemLevel⦄ ⦃M N : Type v⦄ [Countable N] ⦃G : L.Structure M⦄
    ⦃H : L.Structure N⦄ : G ∈ K β M → Nonempty (@Language.Equiv L M N G H) → H ∈ K β N
  isCompatible ⦃β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ :
    G ∈ K β M → @InvarianceDiagram.IsCompatible L σ D M G
  fixed ⦃β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ : G ∈ K β M → S.IsFixedAt β G
  dense ⦃α β : SystemLevel⦄ ⦃M : Type v⦄ ⦃G : L.Structure M⦄ :
    α < β → G ∈ K β M → D.IsDenseAt S α G
  projection_mem ⦃α β : SystemLevel⦄ ⦃M : Type v⦄ [Countable M] ⦃G : L.Structure M⦄ :
    α < β → G ∈ K β M → S.projection α G ∈ K α M
```

  Countability is a premise of the membership assertions (`[Countable N]` on `isoClosed`,
  `[Countable M]` on `projection_mem`), not a clause of `K`; nonemptiness is the field `nonempty`.
  The base is `IsInBase` (some lift `IsLiftAt` in some `K_β`, on the same carrier).
- **Maximality** ([AFK26, Definition 2.20]), with the printed allowance of an unchanged higher lift
  (`G` may itself belong to `K_{β*}` for `β* > β`; only a different lift is forbidden):

```lean
def IsMaximalAt (β : SystemLevel) {M : Type v} (G : L.Structure M) : Prop :=
  G ∈ W.K β M ∧ ∀ β' : SystemLevel, β < β' → ∀ G' ∈ W.K β' M, S.projection β G' = G → G = G'
```

  Few maximal models (`HasFewMaximal`): at each level, countably many countable carriers, finite or
  infinite, with structures maximal at that level, representing every structure maximal there on a
  countable carrier.
- **Eventual determination** ([AFK26, Definition 2.21]), with the printed **strict** inequality
  `α* > α`:

```lean
def IsEventuallyDeterminedTuple {M : Type v} (B : Lc.Structure M) {n : ℕ} (a : Fin n → M) :
    Prop :=
  ∃ (α : SystemLevel) (Q : σ.Invariant n),
    (∃ G : L.Structure M, W.IsLiftAt E α G B ∧ RelMap (L := L) (self := G) Q.1 a) ∧
    ∀ α' : SystemLevel, α < α' → ∀ G : L.Structure M, W.IsLiftAt E α' G B →
      RelMap (L := L) (self := G) Q.1 a
```

  `IsEventuallyDetermined` asks this of every closed tuple (`BaseSublanguage.IsClosedTuple`).
- **`QualifyingSystem D S E`** ([AFK26, Definition 2.23]), extending `WeakSystem D S`, one field
  per condition (docstrings omitted):

```lean
structure QualifyingSystem (D : InvarianceDiagram σ) (S : InvariantSystem.{0} σ)
    {Lc : Language.{wc, wc'}} (E : σ.BaseSublanguage Lc) extends WeakSystem.{w, w', v} D S where
  base_maximal (M : Type v) [Countable M] (B : Lc.Structure M) :
    toWeakSystem.IsInBase E B → ∃ G : L.Structure M, toWeakSystem.IsMaximal G ∧ E.reduct G = B
  fewMaximal : toWeakSystem.HasFewMaximal
  eventuallyDetermined (M : Type v) [Countable M] (B : Lc.Structure M) :
    toWeakSystem.IsInBase E B → toWeakSystem.IsEventuallyDetermined E B
  invariant_occurs ⦃n : ℕ⦄ (Q : σ.Invariant n) :
    ∃ (M : Type v) (_ : Countable M) (_ : Nonempty M) (β : SystemLevel) (G : L.Structure M),
      G ∈ K β M ∧ ∃ x : Fin n → M, RelMap (L := L) (self := G) Q.1 x
```

  Condition (a) is the inclusion of the printed equality `K_{-∞} = {M↾L_c : M ∈ K maximal}` that is
  not automatic (the reverse inclusion holds for every weak system).  Condition (d) is the printed
  existential occurrence on a countable nonempty carrier, with no infiniteness.  Countability is an
  explicit premise of (a) and (c) and part of the witness of (d); nonemptiness is explicit in (d).
  Reconstruction, uniqueness of maximal lifts and successor strictness are not fields.

## The other theorems of Section 2

| Printed | Statement | Proved by | Scope and differences |
| --- | --- | --- | --- |
| Proposition 2.18, arbitrary tuples | `WeakSystem.BFEquivOfPatternMatchedTarget` | `bfEquivOfPatternMatchedTarget` | conclusion `BFEquiv`, replacing the printed relation |
| Proposition 2.18, closed tuples | `WeakSystem.BFEquivOfMatchedTarget` | `bfEquivOfMatchedTarget` | conclusion `BFEquiv`, replacing the printed relation |
| Proposition 2.18, common-invariant formulation | `WeakSystem.BFEquivOfCommonInvariantTarget` | `bfEquivOfCommonInvariantTarget` | conclusion `BFEquiv`, replacing the printed relation `≡_β` |
| Theorem 2.19, back-and-forth content | `WeakSystem.CountableBFClassesTarget` | `countableBFClassesTarget` | coded on `ℕ` |
| Theorem 2.19 | `WeakSystem.ThinnessTarget` | `thinnessTarget` | coded on `ℕ` |
| Lemma 2.22 | `WeakSystem.ExistsRankBoundTarget` | `existsRankBoundTarget` | — |
| Definition 2.20, coding passage | `WeakSystem.FewMaximalCodingTarget` | `fewMaximalCodingTarget` | carriers in universe `0` |
| coding passage for the base | `WeakSystem.BaseClassesRepresentTarget` | `baseClassesRepresentTarget` | carriers in universe `0` |
| proof of Theorem 2.25 (b) | `QualifyingSystem.CountableClassesWithoutLiftTarget` | `countableClassesWithoutLiftTarget` | coded on `ℕ` |
| Theorem 2.25 (b) | `QualifyingSystem.NoPerfectSetTarget` | `noPerfectSetTarget` | coded on `ℕ` |
| Definition 2.7, rank | `InvariantSystem.FixedAtIffRankLeTarget` | `fixedAtIffRankLeTarget` | some fixing level exists |

"Coded on `ℕ`" means that the class is read through a sentence of `L_c` whose models coded on `ℕ`
are the members of the base on `ℕ`, and that the conclusion concerns InfinitaryLogic's coded models
(`isoSetoid φ`, `bfEquivSetoid φ`, `HasPerfectSetOfPairwiseNonisomorphicNatModels`); `L_c` is then
relational and countable by instance premises, and the carriers of the system are in universe `0`.

**Proposition 2.18** (`Systems/BackAndForth.lean`).  The common-invariant formulation, with
`BFEquiv` replacing the printed relation:

```lean
def BFEquivOfCommonInvariantTarget (W : WeakSystem.{w, w', v} D S) : Prop :=
  ∀ (M N : Type v) [Countable M] [Countable N] (β : SystemLevel) (G : L.Structure M)
    (H : L.Structure N), G ∈ W.K β M → H ∈ W.K β N →
    (∃ (n : ℕ) (Q : σ.Invariant n) (a : Fin n → M) (b : Fin n → N),
      RelMap (L := L) (self := G) Q.1 a ∧ RelMap (L := L) (self := H) Q.1 b) →
    @BFEquiv Lc M (E.reduct G) N (E.reduct H) β.1 0 Fin.elim0 Fin.elim0
```

Members of `K_β` on countable carriers realizing a common invariant have reducts that are
back-and-forth equivalent at level `β` at the empty tuple — equivalence, not isomorphism.  The proof
is the induction on the level for tuples matched through a common pattern of positions
(`InvariantSystem.IsPatternMatchedAt`: `x = a ∘ f`, `y = b ∘ f` for one map of positions `f` and
tuples `a`, `b` with a common invariant in `τ_ι(G)` and `τ_ι(H)`), which covers repeated entries and
the empty tuple, as InfinitaryLogic's `BFEquiv` requires: atomic agreement from compatibility of the
projections with `D`, forth and back (an existing entry answered by its partner, a new point through
`ι`-density of the projection), and `Ordinal.limitRecOn`.  The closed-tuple form is the case
`f = id`.  The weak-system fields used are `isCompatible`, `fixed`, `dense` and `projection_mem`.

**Theorem 2.19** (`Systems/BFClasses.lean`).  The stated target and the stronger named theorem that
proves it:

```lean
def CountableBFClassesTarget (W : WeakSystem.{w, w', 0} D S) (φ : Lc.Sentenceω) : Prop :=
  W.IsBaseSentence E φ → (∀ β : SystemLevel, (W.classesWithoutLift E φ β).Countable) →
    ∀ η : Ordinal.{0}, η < ω₁ → Countable (Quotient (bfEquivSetoid φ η))

theorem countable_bfClasses_of_countable_classesWithoutLift
    (hA : ∀ β : SystemLevel, (W.classesWithoutLift E φ β).Countable) (η : Ordinal.{0})
    (hη : η < ω₁) : Countable (Quotient (bfEquivSetoid φ η))
```

The second does not require `IsBaseSentence`; it still concerns the coded models of the sentence
`φ` (`countableBFClassesTarget` is a wrapper of it).  At the
level `β = η` the classes of `bfEquivSetoid φ η` split in two.  The classes whose chosen code has
no lift at `β` are counted through isomorphism classes: they are images of the classes of
`classesWithoutLift E φ β`, countable by hypothesis, under the passage from isomorphism to
back-and-forth equivalence.  The classes whose chosen code has a lift at `β` are covered by the
countably many invariants fixed at `β` (`InvariantSystem.countable`): every member of `K_β` holds
one (`exists_relMap_fixed_invariant`), and two such classes holding one invariant are equal by
Proposition 2.18.  Thinness (`thinnessTarget`, and `not_hasPerfectSet_of_countable_classesWithoutLift`
without the sentence hypothesis) follows by `MainTheorem.isThinOnNatModels_of_countable_bfClasses`.

**Lemma 2.22** (`Systems/RankBound.lean`):

```lean
def ExistsRankBoundTarget (W : WeakSystem.{w, w', v} D S) : Prop :=
  ∀ (M : Type v) [Countable M] (B : Lc.Structure M), W.IsEventuallyDetermined E B →
    ∃ α : SystemLevel, ∀ (β : SystemLevel) (G : L.Structure M), W.IsLiftAt E β G B →
      S.IsFixedAt α G
```

The bound is the supremum of the successor thresholds `α_ā + 1` over the countably many closed
tuples `ā` of `B` — the carrier's countability is used directly here — so every threshold lies
strictly below it, as the strict inequality of Definition 2.21 requires.  A lift at a level at most
the bound is fixed there by monotonicity; a lift above it agrees with its projection to the bound on
every invariant, as both carry `Q_ā` on every closed tuple, an invariant holds only of closed
tuples ([AFK26, Definition 2.2 (b)]), and distinct invariants of one arity hold of no common tuple
(Definition 2.2 (c)).  Neither maximality, Reconstruction nor uniqueness of maximal lifts is used.

**Theorem 2.25 (b)** (`Systems/Thinness.lean`):

```lean
def NoPerfectSetTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E) (φ : Lc.Sentenceω) :
    Prop :=
  W.IsQualifyingSentence φ → ¬ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

theorem noPerfectSetTarget (W : QualifyingSystem.{w, w', wc, wc', 0} D S E)
    (φ : Lc.Sentenceω) : W.NoPerfectSetTarget φ
```

No infiniteness premise.  The coded classes with a member without a lift at `β` are countable
(`countableClassesWithoutLiftTarget`): such a member is the reduct of a structure maximal at some
`δ` (condition (a)), `δ < β` since otherwise its projection to `β` would be a lift, and condition
(b) at each of the countably many `δ < β`; then Theorem 2.19.  Conditions (c) and (d) are not used.

**The coding passage for few maximal models** (`Systems/Maximality.lean`):

```lean
def FewMaximalCodingTarget (W : WeakSystem.{w, w', 0} D S) : Prop :=
  W.HasFewMaximal ↔ W.HasFewMaximalOnCanonicalCarriers
```

Few maximal models over all countable carriers is equivalent to countably many classes on each
positive finite carrier `Fin (n + 1)` and on `ℕ`; finite carriers are treated as `ℕ` is, by a
bijection and the transport of maximality (`IsMaximalAt.of_equiv`).  The countable sets on the
canonical carriers need not consist of maximal structures; the representatives of `HasFewMaximal`
are maximal.

## The `K[L]` instance

`Systems/TemplateBase.lean`, `Systems/TemplateWeak.lean`, `Systems/TemplateQualifying.lean`.  Each
field of the abstract structures is given by an existing declaration for `K[L]`, read through
small translation lemmas; the new lemmas are `exists_toTemplateSymbol_of_not_isInvariant`,
`templateDensityTranslationTarget` and `templateBaseSublanguage_isClosedTuple_iff`.

| Abstract field or premise | `K[L]` | Proved by |
| --- | --- | --- |
| `D`, `S` | `templateDiagram`, `templateInvariantSystem` | — |
| `BaseSublanguage` (`incl`, `incl_injective`, `mem_range_iff`) | `templateBaseSublanguage` | `baseInclusion`, `baseInclusion_injective`, `not_isInvariant_toTemplateSymbol` and `exists_toTemplateSymbol_of_not_isInvariant`; the reduct is `baseReduct`, definitionally |
| `WeakSystem.K β M` | `templateStageClass M β.1` | `templateWeakSystem_K` (by `rfl`) |
| `compatibleWith` | | `isCompatibleWith_templateInvariantSystem` |
| `nonempty` | | `nonempty_of_mem_templateStageClass` |
| `isoClosed` | | the first clause of `weakSystemClausesTarget` (the source carrier is countable, as it injects into the target) |
| `isCompatible`, `fixed` | | clauses of `templateStageClass`, through `isCompatible_templateDiagram_iff` and `templateInvariantSystem_projection` |
| `dense` (`α < β`) | | `projectedDensityAt_of_satisfiesDensityAt`, through `templateDensityTranslationTarget` |
| `projection_mem` (`α < β`) | | `projectionTarget` (stated for `α ≤ β`, with `Countable M`) |
| base, maximality | `IsInTemplateBase`, `IsMaximalAt` | `templateWeakSystem_isInBase_iff`, `templateWeakSystem_isMaximalAt_iff` |
| (a) `base_maximal` | | `maximalCoverageBaseTarget` (from `maximalCompletionTarget`) |
| (b) `fewMaximal` | | `maximalCountTarget` (Proposition 4.35) at each countable level, representatives on `ℕ`, reindexed by `WeakSystem.hasFewMaximal_of_family` |
| (c) `eventuallyDetermined` | | `eventualDeterminationOfBaseTarget` (from `maximalCompletionTarget`), whose threshold `ξ` serves for every `ζ ≥ ξ`, hence for every `ζ > ξ`; `templateBaseSublanguage_isClosedTuple_iff` |
| (d) `invariant_occurs` | | `invariantOccurrenceTarget` on `ℕ`, with `templateInvariant_eq` |
| `CountableMembersInfinite` | | `infinitudeTarget` |
| `IsBaseSentenceOnCarriers templateSentence` | | `templateBaseModelsTarget` (`templateWeakSystem_isBaseSentenceOnCarriers`) |
| `IsQualifyingSentence templateSentence` | | `WeakSystem.isBaseSentence_of_isBaseSentenceOnCarriers`, through InfinitaryLogic's `mem_modelsOf_iff_realize` |
| `[Countable (Σ n, L_c.Relations n)]` | | the instance from `baseLanguageCountableTarget` |

The weak system `templateWeakSystem : WeakSystem.{0, 1, v}` has carriers in any universe `v`; the
qualifying system `templateQualifyingSystem : QualifyingSystem.{0, 1, 0, 1, 0}` has carriers in
universe `0`.  `templateQualifyingSentenceTarget` assembles the base sublanguage, the qualifying
system, `templateQualifyingSystem_countableMembersInfinite` and
`templateQualifyingSystem_isQualifyingSentence`.

## Formalization choices and scope

The five design decisions recorded in `Systems/Targets.lean`:

1. **Indices.**  Levels are `SystemLevel`, the index type of `InvariantSystem.{0}`; raw ordinals
   appear only in the conclusions about `bfEquivSetoid`.
2. **Occurrence and carriers.**  Condition (d) is the printed existential occurrence on a countable
   nonempty carrier; no infiniteness is part of any structure.  Few maximal models allows finite
   carriers, as printed; its passage to the canonical carriers is separate
   (`HasFewMaximalOnCanonicalCarriers`, `FewMaximalCodingTarget`).  The statements that count only
   models on `ℕ` and need it display `CountableMembersInfinite` as an explicit premise.
3. **Countability.**  A premise, not a clause of `K`; nonemptiness is explicit.  Lemma 2.22 uses the
   countability of the carrier directly, to bound the thresholds of all closed tuples.
4. **Back-and-forth.**  Definition 2.15 and Proposition 2.16 are not formalized; InfinitaryLogic's
   `BFEquiv` and `bfEquivSetoid` and the thinness theorem
   `MainTheorem.isThinOnNatModels_of_countable_bfClasses` are used in their place.
5. **Universes.**  Ordinals in universe `0`; carriers in an arbitrary universe for the uncoded
   statements and in universe `0` for the coded ones and for the count; `L` and `L_c` in arbitrary
   universes, except `L_c : Language.{0, 1}` in Theorem 2.27; the base sublanguage explicit.

Further choices in the formalization of the printed text:

1. the base sublanguage takes `Lc` as a parameter, not a field, so its universes are visible;
2. the weak system has the field `compatibleWith`, the printed standing hypothesis that `D` and
   `S` are compatible ([AFK26, Definition 2.8]);
3. countability is a premise on the carriers of asserted membership, not a clause of `K`;
4. closure under projection is for `α < β`, as printed, where the `K[L]` statement is for
   `α ≤ β`; the case `α = β` follows from `fixed`;
5. `CountableMembersInfinite` is a premise only of the `ℕ`-coded count `= ℵ₁` and of
   Theorem 2.27, which are corollaries and do not replace the general conclusions;
6. the carriers of the coded statements are in universe `0`;
7. the countable sets on the canonical carriers need not consist of maximal structures (the
   passage to representatives with the property is by invariance under isomorphism); the
   representatives of `HasFewMaximal` are maximal.

Theorem 2.25 (a) is stated in its general form on the base classes on `Fin (n + 1)` and `ℕ`, with
no infiniteness premise, and in the form for a sentence through `IsBaseSentenceOnCarriers`;
Proposition 2.18 is proved through the relation of matching along a common pattern of positions,
with the closed-tuple form as a consequence.

## Axioms

Every declaration of the library at this commit uses at most the three axioms `propext`,
`Classical.choice` and `Quot.sound` (`scripts/check.sh`, the library-wide audit, in the `build`
job of the `main` run 40532231152 at the squash-merge commit; the same audit passed in the
pull-request checks of #261 at `774d819`, whose tree is that of the squash commit, over 15356
declarations).

## What is not claimed, at the pinned commit

The inventory below describes the pinned commit, not the current state of the repository.

- Definition 2.15 (back-and-forth systems of closed tuples, `≡_β`) and Proposition 2.16 are
  replaced, not formalized: Proposition 2.18 concludes `BFEquiv β` (InfinitaryLogic's Karp-style
  relation), and Theorem 2.19 counts the classes of `bfEquivSetoid` and concludes thinness through
  `MainTheorem.isThinOnNatModels_of_countable_bfClasses`, where the printed Theorem 2.19 bounds
  `≡_β`-antichains.  No correspondence between `BFEquiv` and the printed `≡_β` is claimed or
  stated.  The printed closed-tuple relation `≡_β` is not an equivalence relation ([AFK26, §2.4]
  says so); `BFEquiv` at the empty tuple is (`bfEquivSetoid`).
- Theorem 2.27 is proved in the `ℕ`-coded form `hasThinAlephOneSpectrumTarget` only, with
  `CountableMembersInfinite` explicit and `L_c : Language.{0, 1}`.  The unrestricted printed
  theorem — all countable models, no infiniteness hypothesis, an arbitrary countable `L_c` — is not
  stated, and neither is its final sentence (a counterexample to Vaught's conjecture).  Theorem
  2.25 (b) is likewise stated for models coded on `ℕ`.  The general count (conclusion 1) and its
  form for a sentence count the members on nonempty carriers, as in [AFK26, §1]; the empty structure
  is not counted.
- Universes: the ordinal universe is `0` throughout (`InvariantSystem.{0}`, as `bfEquivSetoid` and
  the counting lemmas require); the coded statements and the general count have their carriers in
  universe `0`; Proposition 2.18, Lemma 2.22 and the structures have carriers in an arbitrary
  universe.
- No identification of the repository's transcription `templateSentence` of `σ[L]` with its public
  sentence `baseLanguage.densitySentence` is made, and no spectrum result is transferred in either
  direction.
- `theorem436Target_abstract` is a second proof of `Theorem436Target`; it does not replace
  `theorem436Target`, and it uses Reconstruction (above).  The record of Theorem 4.36
  (`2026-10-25-theorem-4-36.md`) is unchanged; its bullet stating that the abstract theorems of
  Section 2 are not stated describes its pinned commit.
- The projection theorem `projectionTarget` still carries `Countable M`; the abstract field
  `projection_mem` carries `[Countable M]` too, so the instance uses `projectionTarget` as it
  stands.  Removing the premise is later work, as in the record of Proposition 4.30.  Theorem 4.23
  for an arbitrary template system `T` is not stated; the instance uses the existing results for
  `K[L]`.
- `README.md`, `formalization.yaml` and `roadmap/IMPLEMENTATION.md` still say that the abstract
  Theorems 2.25 and 2.27 for arbitrary systems are not claimed (or not formalized); they are stale at
  this commit.  The module docstring of `Systems/Base.lean` still says that nothing about the
  statements of the directory is proved in its files; it is out of date at this commit.
- The audit of the published version covers, in Section 2, only the statements named in the table
  of the verified commit (Definitions 2.6–2.8, 2.10, 2.17, 2.20, 2.21 and 2.23, Proposition 2.18,
  Theorems 2.19, 2.25 and 2.27).  Convention 2.3, Definitions 2.1, 2.2, 2.4, 2.5, 2.24 and 2.26,
  Lemma 2.22, Definition 4.17 and Theorem 4.23, also cited by the files of
  `Correspondence/Systems/`, are not among the audited statements; for them the correspondence is
  to the pinned draft.
- Verification applies to the pinned commit.  Comparator checks the repository's reference
  statement (the main theorem through `comparator/Challenge.lean`); it does not separately
  check the manuscript dictionary or each new theorem.  Those are checked by the build and the
  axiom audit.
