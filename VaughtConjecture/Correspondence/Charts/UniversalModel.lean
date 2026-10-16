/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Construction.DenseChain
import VaughtConjecture.Continuation.ExactAge
import VaughtConjecture.Correspondence.Density.DonorDensity
import VaughtConjecture.MainTheorem.StronglyCodedSuccessor

/-!
# The universal chart model at a countable stage: statements

Numbering as in the current draft of [AFK26].  Write `λ_β = blockStage β = ω + ω · β`, `K_β[L]`
for `templateStageClass M β` and `C_β[L]` for the charts `IsTemplateChart β`.  This file states
targets only.  Proved elsewhere: the finite steps (`FreshPlacementTarget`,
`UniversalPointStepTarget`, `UniversalTaskStepTarget`) in
`VaughtConjecture.Correspondence.Charts.UniversalSteps`, and the chart reading
(`ChartEmbeddingClosedRangeTarget`, `ClassReadingChartEmbeddingTarget`,
`ExactRealizationOfEmbeddingTarget`) in `VaughtConjecture.Correspondence.Charts.UniversalReading`.
The other targets are **stated**.

## The printed statement

[AFK26, Lemma 4.33]: for each `β ∈ ω₁` there is a structure `F_β ∈ K_β` such that every chart in
`C_β[L]` embeds into `F_β`, and whenever `Q_s, Q_t` are fixed at `β`, `(Q_t(x y), Q_s(x)) ∈ ID[L]`
and `F_β ⊨ Q_s(a)`, there is `b` with `F_β ⊨ Q_t(a b)`.  The printed proof: `C_β[L]` has
countably many isomorphism types and HP, JEP, AP ([AFK26, Proposition 4.32]), so the standard
Fraïssé construction applies; the extension property gives `D[δ]` for every `δ < ω + ω · β`.

## The formal statement (`UniversalChartModelTarget β M`)

For `β < ω₁` and a **prescribed** countably infinite carrier `M`, one structure `G` is chosen
**before** any chart, root or donor is named (`∃ G ∈ templateStageClass M β, …`, with every
request quantified inside), and it satisfies three clauses about that same `G`:

| Clause | Definition | Content |
| --- | --- | --- |
| membership | `G ∈ templateStageClass M β` | `K_β[L]`, [AFK26, Definition 4.21] |
| (a) universality | `EmbedsEveryChart β G` | every chart embeds into `G` |
| (b) positive roots | `ExtendsOverChartRoots β G` | `ι : C ↪ D`, `e : C ↪ G` give `e'` (*) |
| (b) empty root | `ExtendsOverEmptyRoot β G` | every chart embeds, exactly realized |

(*) for charts `C`, `D` and embeddings `ι : C ↪ D`, `e : C ↪ G`, some `e' : D ↪ G` has
`ι ; e' = e` (the commuting square) and realizes `D` exactly.

**Embeddings** are `FirstOrder.Language.Embedding` of `templateLanguage` (every symbol, every
tuple, repetitions allowed), the morphisms of `C_β[L]` ([AFK26, Definition 4.31]); between charts
of stage types they are the face maps up to renaming (`StageType.embeddingEquivFace`).  The
commuting square is stated on point maps: `ι.toEmbedding.trans e'.toEmbedding = e.toEmbedding`.

**Closed faces.**  A chart embedding `ι : C ↪ D` always has closed range in `D`
(`ChartEmbeddingClosedRangeTarget`): `C ⊨ P_n` of its enumeration, and `ι` preserves `P_n`.  So
"`C` a closed face of `D`" is not an extra premise of clause (b); `IsTemplateChart.hereditary` is
the converse direction (a nonempty closed set of a chart carries a chart).

**Exact donor realization** (`RealizesChartExactly β G D e'`): for every presentation of `D` by a
template `t` with enumeration `eD` (`IsChartPresentation β D t eD`, the data of
`IsTemplateChart`), the decoder reads the image tuple as the class of `t` literally:
`(decode β G).eval (eD.toEmbedding.trans e'.toEmbedding) = some t.toClass`.  The decoder reads
through the invariant symbols (`decodeEval`: the class `c` with `G ⊨ Q_c`), so this is "the image
of `D` realizes the type of `D`", stated at the block stage, not only at `ω₁`.  For `β < ω₁` it
follows from the embedding, for every `G` (`realizesChartExactly_of_embedding`; the premise of
compatibility in `ExactRealizationOfEmbeddingTarget` is not used); it is stated as a clause so
that the exactness is visible.

**Positive and empty roots.**  A chart has `n ≥ 1` points (the templates of [AFK26] have nonempty
underlying sets, `IsTemplateChart`), so in `ExtendsOverChartRoots` the root `C` is nonempty: this
is the printed second bullet, with an arbitrary chart embedding in place of the initial segment
`x` of `x y`.  The structure on no points is **not** a chart; the root on no points is auxiliary,
and its case is stated separately as `ExtendsOverEmptyRoot`: every chart `D` embeds, with exact
realization (the commuting square over the empty root is vacuous).  `ExtendsOverEmptyRoot` gives
clause (a), `EmbedsEveryChart`, which is the printed first bullet.

## Construction plan (the strongly coded universal realization)

The construction is positional, at the stage `λ_β`, on the prescribed carrier `M`, by a
Rasiowa–Sikorski scheduling of countably many requirements.  It does **not** start from a
structure of `K_β[L]` or from any class realization with donor density.

* **Conditions** (`UniversalCondition λ_β M`): an injective tuple `W : Fin N ↪ M` and a strongly
  coded legal stage type `w` at `λ_β` on `N` points (`StageType.IsStronglyCodedLegal`).  The
  positional type of a tuple whose points are points of `W` is its face of `w`.
* **Order** (`UniversalCondition.Extends c d`): `d` extends `c` along some `e` with
  `e.trans d.W = c.W` and `restrictFace e d.w = some c.w`, literally.
* **Initial condition** `c₀`: the empty tuple with the strongly coded legal stage type on no
  points (the face on no points, `StageType.isSome_restrictFace_of_zero`, of a strongly coded legal
  one-point type, `StageType.exists_stronglyCodedLegal_onePoint`; faces keep strong coding and
  legality, `StageType.isStronglyCoded_of_restrictFace`, `StageType.IsLegal.restrictFace`).
* **Requirements**, indexed by `ι = M ⊕ Σ k m, (Fin k ↪ M) × StageType λ_β m × (Fin k ↪ Fin m)`:
  1. a **point** `a : M`: `a` is a point of the tuple of the condition.  This is the
     **enumeration of the carrier**: the requirements `inl a` range over all of `M`.
  2. an **exact task** `(t, D, g)`: the root `t` is a face of the tuple of the condition, and if
     its type `p` is the face of a strongly coded legal `D` along `g`, some face of the condition
     extends `t` along `g` and has type `D` literally (`UniversalCondition.ExactTaskDone`).
  `ι` is countable: `M` is countable, `Fin k ↪ M` is countable, and there are countably many
  stage types at `λ_β` (`StageType.countable`, with `Cardinal.countable_Iio_of_lt_omega_one` and
  `blockStage_lt_omega_one`).
* **Scheduling**: `Construction.exists_monotone_forall_exists_mem` (the Rasiowa–Sikorski lemma)
  from `c₀`, given that every requirement is dense (the two step targets below), gives a chain
  `c₀ ≤ c₁ ≤ ⋯` meeting every requirement.
* **Invariants at each finite step** (each step is an `Extends`):
  (I1) the type of the condition is strongly coded legal at `λ_β` (every type of every tuple is
  strongly coded); (I2) **literal root preservation**: the old tuple is a face of the new one,
  point by point, and the old type is literally the face of the new type; (I3) the points added by
  a task are fresh (outside the old tuple), so the old tuple is never identified with new points.
* **Point step** (`UniversalPointStepTarget`): add the missing points one at a time by the exact
  pinned extension over the empty face (`StageType.exists_stronglyCoded_pinned_extension` with
  `StageType.hasStronglyCodedApexCoatomExtensions`, built on `StageType.addStrongApex`) and a
  strongly coded legal one-point type.  Not joint embedding: an amalgam with a one-point type may
  put the new point on an old one.
* **Task step** (`UniversalTaskStepTarget`), **the first genuinely new construction**: first a
  point step for the points of `t`; then the strongly coded amalgam of `D` and `w` over the literal
  face `p` (`StageType.exists_stronglyCoded_amalgam_of_isSuccPrelimit` at `λ_β`, a limit by
  `isSuccPrelimit_blockStage`): a strongly coded legal `D⁺` with faces `w` along `i` and `D` along
  `j`, `f ; i = g ; j`; then place the points of `D⁺` outside `i` on fresh points of `M`
  (`FreshPlacementTarget`, which uses `Infinite M`).  The donor is realized exactly: the face of
  `D⁺` along `j` is `D` itself.  No donor density of a given structure is used (contrast the task
  step `ClassRealization.exists_le_taskDone` of the presentation, which receives through donor
  density of a given class realization and only at a cutoff).
* **Limit** (`UniversalChainLimitTarget`): the type of a tuple is its face of the type of any
  condition of the chain containing its points (well defined by (I2)).  Exact consistency,
  covering, legal and strongly coded types follow from the conditions; exact receiving within the
  strongly coded legal stage types (`Realization.ExactReceivingWithin`) from the exact tasks;
  finite-cut receiving for strongly coded cofaces from exact receiving (the donor itself is in each
  of its receiving families, `StageType.self_mem_receivingFamily`, as in
  `Realization.ExactReceivingWithin.hasFiniteCutReceiving`).  So the limit is in the strongly
  coded receiving class (`Realization.IsStronglyCodedReceiving`) with exact receiving
  (`StronglyCodedUniversalRealizationTarget`).
* **Reading** (`StronglyCodedUniversalReadingTarget`): `G = R.classReading.toStructure`.
  Membership in `K_β[L]` as in `successorReadingTarget`, at `β` instead of `β + 1`: the class
  reading is well formed (`Realization.IsConsistent.classReading`,
  `Realization.IsCovering.classReading`, `Realization.classReading_hasLegalTypes`), has donor
  density (`Realization.hasFiniteExtensionReceivingIn_isStronglyCoded_iff`,
  `Realization.HasFiniteExtensionReceivingIn.hasDonorDensity_classReading`), and B.T5/B.T6
  (`decoderRoundTrip`, `mem_templateStageClass_iff`) give membership.  The chart clauses use the
  reading of chart embeddings (`ClassReadingChartEmbeddingTarget`): an embedding of a chart
  presented by `t` into `G` is a tuple whose type is a renaming of `t`.  Over a root of type
  `p'`, a renaming of the template of `C`, the donor template is renamed so that its face is `p'`
  literally (`StageType.exists_restrictFace_renameCells`, `isStronglyCodedLegal_renameCells_iff`);
  exact receiving then extends the root tuple literally, and the class of the received type is the
  class of the donor template.  Cell alignment happens before receiving; the root point map is
  not changed.

## What does not qualify, and why

| Result | Given structure in `K_β[L]` | Exact donor | Carrier `M` | Strongly coded |
| --- | --- | --- | --- | --- |
| `stronglyCodedPresentationTarget` | premise | no (cutoff) | yes | yes |
| all-legal Fraïssé limit | none | yes | no (its own) | no |
| `IsStronglyCodedReceiving` | none | no (cutoff) | yes | yes |
| this file | none | yes | yes | yes |

* `stronglyCodedPresentationTarget` (B.T7 with the decoder): for a **given** `G ∈ K_β[L]`, a
  realization in the strongly coded receiving class with class reading `decode β G`.  Its premise
  is a structure already in `K_β[L]`, i.e. a dense class realization (donor density of
  `decode β G`): it presents a given structure, it does not construct one.  Its receiving is at a
  permitted cutoff, up to renaming in the class reading, so it gives no exact donor realization,
  and a given `G` need not contain every chart.
* The all-legal Fraïssé limit (`exists_isFraisseLimit_legalAge`,
  `exactReceivingWithin_reconstruct_of_legalAge`, `isModel_reconstruct_of_legalAge`): a countable
  structure of `hullLanguage α` whose reconstruction is a model with exact receiving of every legal
  donor.  Its age is all legal charts, not only the strongly coded ones, so it realizes types that
  are not strongly coded: its realization is not in `Realization.IsStronglyCodedReceiving`, its
  class reading does not have strongly coded legal types (`ClassRealization.HasLegalTypes`), and
  the charts of [AFK26, Definition 4.31] do not see those tuples.  Its language is
  `hullLanguage α`, not `templateLanguage`, and its carrier is the limit's own, not the prescribed
  `M`.
* `Realization.HasFiniteCutReceivingIn` and `Realization.IsStronglyCodedReceiving`: one-point
  receiving of strongly coded cofaces at a permitted cutoff; the received type agrees with the
  donor below the cutoff only.  Exact realization is `Realization.ExactReceivingWithin`.
* `ClassRealization.HasDonorDensity` and `SatisfiesDensityAt`: density up to renaming, by capped
  observation or raw truncation; consequences of universality (`UniversalityDensityTarget`), not
  the universal property.

## Positional receiving, internally

Positional receiving is the implementation of the chart statements, not their statement:
`Realization.ExactReceivingWithin` (exact, literal root, literal donor) is what the task step
produces and what the chart clause (b) is read from; `Realization.HasFiniteCutReceivingIn`
(cutoff, strongly coded cofaces) is the receiving clause of `IsStronglyCodedReceiving`, and through
`Realization.hasFiniteExtensionReceivingIn_isStronglyCoded_iff` and
`Realization.HasFiniteExtensionReceivingIn.hasDonorDensity_classReading` it gives the donor density
of the class reading, hence membership in `K_β[L]`.

## Relation to density

Universality implies density: a compatible, `τ_β`-fixed structure with the positive-root clause
satisfies `D[α]` for every `α < λ_β` (`UniversalityDensityTarget`, the printed argument): for a root
`Q_t(x)` and a donor `u` of any rank, the donor `τ_β(u)` has the same truncation at `α < λ_β` and
is a chart at `β`, and the positive-root clause realizes it over `x`.  The empty root is not
needed for `D[α]` (`n ≥ 1` there); it is the case `n = 0` of `ClassRealization.HasDonorDensity`,
which `D[α]` does not have.  On the construction route membership comes from receiving instead
(the reading above); `UniversalityDensityTarget` is the intrinsic route.  Membership is part of
`UniversalChartModelTarget`, so no separate membership target is stated.

## Targets, premises, intended inputs, first new construction

* `UniversalChartModelTarget β M` (`β < ω₁`, `Countable M`, `Infinite M`): from
  `StronglyCodedUniversalRealizationTarget` and `StronglyCodedUniversalReadingTarget`, with
  `G = R.classReading.toStructure`.
* `StronglyCodedUniversalRealizationTarget β M` (`β < ω₁`, `Countable M`, `Infinite M`): the
  scheduling above; first new construction: `UniversalTaskStepTarget`.
* `StronglyCodedUniversalReadingTarget β M` (`β < ω₁`, `Nonempty M`; `Nonempty M` also follows
  from covering and exact receiving of a one-point donor): membership as in
  `successorReadingTarget`; first new statement: `ClassReadingChartEmbeddingTarget`.
* `ClassReadingChartEmbeddingTarget β M` (`β < ω₁`, exact consistency): the chart reading of a
  consistent realization; inputs `StageType.exists_restrictFace_iff_of_isCellRenaming`,
  `StageType.globalClass_eq_iff`, `StageType.holds_comp_iff`.
* `ChartEmbeddingClosedRangeTarget β`, `ExactRealizationOfEmbeddingTarget β M`: the two remarks
  above; inputs `StageType.restrictFace_refl`, the negative pairs of `templateDiagramPairs`.
* `UniversalityDensityTarget β M` (`β < ω₁`, compatibility, `τ_β`-fixation): the printed density
  argument; inputs `satisfiesDensityAt_iff`, `TemplateClass.project`, the chart of a stage type.
* `FreshPlacementTarget M` (`Infinite M`), `UniversalPointStepTarget λ_β M` (`λ_β` zero or a
  limit), `UniversalTaskStepTarget λ_β M` (`λ_β` zero or a limit, `Infinite M`),
  `UniversalChainLimitTarget λ_β M` (no premise beyond the chain): the four steps of the
  construction.
-/

universe u v w

namespace VaughtConjecture

open FirstOrder Language Structure Ordinal

noncomputable section

/-! ### Chart clauses of a structure -/

section Clauses

variable {M : Type v}

/-- **A presentation of a chart by a template** ([AFK26, Definition 4.31]): the data of
`IsTemplateChart β D`, a stage type `t` at the block stage `ω + ω · β` on `n ≥ 1` points that is a
legal template with labels in `{-∞} ∪ ω₁ ∪ {∞}`, and an enumeration `e` of the points of `D`
carrying every relation of the chart of `t` to `D` and back.  `IsTemplateChart β D` is
`∃ n t e, IsChartPresentation β D t e`.  Correspondence with the printed definitions. -/
def IsChartPresentation (β : Ordinal.{u}) {P : Type w} (D : templateLanguage.{u}.Structure P)
    {n : ℕ} (t : StageType.{u} (blockStage β) n) (e : Fin n ≃ P) : Prop :=
  0 < n ∧ t.IsLegalTemplate ω₁ ∧ ∀ {k : ℕ} (r : TemplateSymbol.{u} k) (xs : Fin k → Fin n),
    RelMap (L := templateLanguage.{u}) (self := D) r (e ∘ xs) ↔ t.Holds r xs

/-- **Exact realization of a chart along an embedding**: for every presentation of `D` by a
template `t` with enumeration `eD`, the decoder reads the image tuple in `G` as the class of `t` at
the block stage, literally.  Native construction. -/
def RealizesChartExactly (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) {P : Type w}
    (D : templateLanguage.{u}.Structure P)
    (e : @Language.Embedding templateLanguage.{u} P M D G) : Prop :=
  ∀ (n : ℕ) (t : StageType.{u} (blockStage β) n) (eD : Fin n ≃ P), IsChartPresentation β D t eD →
    (decode β G).eval (eD.toEmbedding.trans e.toEmbedding) = some t.toClass

/-- **Clause (a), universality** ([AFK26, Lemma 4.33], first bullet): every chart in `C_β[L]`
embeds into `G`.  Correspondence with the printed definitions. -/
def EmbedsEveryChart (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) : Prop :=
  ∀ (P : Type w) (D : templateLanguage.{u}.Structure P), IsTemplateChart β D →
    Nonempty (@Language.Embedding templateLanguage.{u} P M D G)

/-- **Clause (b) over positive roots** ([AFK26, Lemma 4.33], second bullet, along an arbitrary
chart embedding): for charts `C` and `D` in `C_β[L]` (`C` has `n ≥ 1` points), every embedding
`ι : C ↪ D` (whose range is closed, `ChartEmbeddingClosedRangeTarget`) and every embedding
`e : C ↪ G`, some embedding `e' : D ↪ G` extends `e` along `ι` (`ι ; e' = e` on points, the
commuting square) and realizes `D` exactly (`RealizesChartExactly`).  Native construction. -/
def ExtendsOverChartRoots (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) : Prop :=
  ∀ (N : Type w) (C : templateLanguage.{u}.Structure N) (P : Type w)
    (D : templateLanguage.{u}.Structure P), IsTemplateChart β C → IsTemplateChart β D →
    ∀ (ι : @Language.Embedding templateLanguage.{u} N P C D)
      (e : @Language.Embedding templateLanguage.{u} N M C G),
      ∃ e' : @Language.Embedding templateLanguage.{u} P M D G,
        ι.toEmbedding.trans e'.toEmbedding = e.toEmbedding ∧ RealizesChartExactly β G D e'

/-- **Clause (b) over the empty root** (auxiliary: the structure on no points is not a chart):
every chart `D` in `C_β[L]` embeds into `G` with exact realization.  The commuting square over the
empty root is vacuous; this clause gives clause (a).  Native construction. -/
def ExtendsOverEmptyRoot (β : Ordinal.{u}) (G : templateLanguage.{u}.Structure M) : Prop :=
  ∀ (P : Type w) (D : templateLanguage.{u}.Structure P), IsTemplateChart β D →
    ∃ e' : @Language.Embedding templateLanguage.{u} P M D G, RealizesChartExactly β G D e'

/-- **An embedding of `D` into `G` with point map `x` on the enumeration `eD`**: some embedding
`e : D ↪ G` has `eD ; e = x` on points.  Native construction. -/
def EmbedsAlong (G : templateLanguage.{u}.Structure M) {P : Type w}
    (D : templateLanguage.{u}.Structure P) {n : ℕ} (eD : Fin n ≃ P) (x : Fin n ↪ M) : Prop :=
  ∃ e : @Language.Embedding templateLanguage.{u} P M D G, eD.toEmbedding.trans e.toEmbedding = x

end Clauses

/-! ### The universal chart model -/

section Model

variable (β : Ordinal.{u}) (M : Type v)

/-- **Target: the universal chart model** ([AFK26, Lemma 4.33]).  For `β < ω₁` and a prescribed
countably infinite carrier `M`, one structure `G ∈ K_β[L]` on `M`, chosen before any request, in
which every chart embeds (clause (a)), and over which every chart embedding extends every
embedding of its root, with a commuting square and exact realization, both over positive roots and
over the empty root (clause (b)).  Native construction. -/
def UniversalChartModelTarget : Prop :=
  β < ω₁ → Countable M → Infinite M →
    ∃ G ∈ templateStageClass M β, EmbedsEveryChart.{u, v, w} β G ∧
      ExtendsOverChartRoots.{u, v, w} β G ∧ ExtendsOverEmptyRoot.{u, v, w} β G

/-- **Target: the strongly coded universal realization**.  For `β < ω₁` on a countably infinite
carrier, a realization at `λ_β` in the strongly coded receiving class with exact receiving of
every strongly coded legal donor: over every cover `c` of a type `t` and every strongly coded
legal `D` restricting to `t` along `g`, some cover `u` of `D` itself has `u ∘ g = c` (literal root
preservation; the case `n = 0` is the empty root).  Built by the scheduling of this file, without
any given structure of `K_β[L]` or class realization with donor density.  Native construction. -/
def StronglyCodedUniversalRealizationTarget : Prop :=
  β < ω₁ → Countable M → Infinite M →
    ∃ R : Realization.{u, v} (blockStage β) M, R.IsStronglyCodedReceiving ∧
      R.ExactReceivingWithin
        (fun m ↦ {D : StageType.{u} (blockStage β) m | D.IsStronglyCodedLegal})

/-- **Target: the class reading of a strongly coded universal realization** is a universal chart
model.  For `β < ω₁` on a nonempty carrier, if `R` at `λ_β` is in the strongly coded receiving
class with exact receiving of every strongly coded legal donor, its class-reading structure
`G = R.classReading.toStructure` is in `K_β[L]` and satisfies clauses (a) and (b).
Native construction. -/
def StronglyCodedUniversalReadingTarget : Prop :=
  β < ω₁ → Nonempty M → ∀ R : Realization.{u, v} (blockStage β) M,
    R.IsStronglyCodedReceiving →
    R.ExactReceivingWithin
        (fun m ↦ {D : StageType.{u} (blockStage β) m | D.IsStronglyCodedLegal}) →
      R.classReading.toStructure ∈ templateStageClass M β ∧
        EmbedsEveryChart.{u, v, w} β R.classReading.toStructure ∧
        ExtendsOverChartRoots.{u, v, w} β R.classReading.toStructure ∧
        ExtendsOverEmptyRoot.{u, v, w} β R.classReading.toStructure

/-- **Target: the chart reading of a consistent realization**.  For `β < ω₁` and an exactly
consistent realization `R` at `λ_β`, the embeddings of a chart presented by `t` into the
class-reading structure of `R`, with point map `u` on the enumeration, are exactly the injective
tuples `u` whose class is the class of `t`.  Native construction. -/
def ClassReadingChartEmbeddingTarget : Prop :=
  β < ω₁ → ∀ R : Realization.{u, v} (blockStage β) M, R.IsConsistent →
    ∀ (P : Type w) (D : templateLanguage.{u}.Structure P) (n : ℕ)
      (t : StageType.{u} (blockStage β) n) (eD : Fin n ≃ P), IsChartPresentation β D t eD →
      ∀ x : Fin n ↪ M,
        EmbedsAlong R.classReading.toStructure D eD x ↔ R.classReading.eval x = some t.toClass

/-- **Target: exact realization from an embedding**.  For `β < ω₁` and a compatible structure
`G`, every embedding of a chart into `G` realizes the chart exactly.  Native construction. -/
def ExactRealizationOfEmbeddingTarget : Prop :=
  β < ω₁ → ∀ G : templateLanguage.{u}.Structure M, IsTemplateCompatible G →
    ∀ (P : Type w) (D : templateLanguage.{u}.Structure P),
      IsTemplateChart β D → ∀ e : @Language.Embedding templateLanguage.{u} P M D G,
        RealizesChartExactly β G D e

/-- **Target: universality implies density** (the printed argument of [AFK26, Lemma 4.33]).  For
`β < ω₁`, a compatible structure fixed by `τ_β` that satisfies clause (b) over positive roots
satisfies `D[α]` for every `α < ω + ω · β`.  Correspondence with the printed definitions. -/
def UniversalityDensityTarget : Prop :=
  β < ω₁ → ∀ G : templateLanguage.{u}.Structure M, IsTemplateCompatible G →
    projectStructure β G = G → ExtendsOverChartRoots.{u, v, w} β G →
      ∀ α < blockStage β, SatisfiesDensityAt α G

end Model

section ClosedRange

variable (β : Ordinal.{u})

/-- **Target: chart embeddings have closed range**: an embedding of a chart in `C_β[L]` into a
structure has a range closed in it (`IsClosedIn`), since it preserves `P_n` of the enumeration of
the chart.  So the root of a chart embedding is a closed face.  Native construction. -/
def ChartEmbeddingClosedRangeTarget : Prop :=
  ∀ (N : Type w) (C : templateLanguage.{u}.Structure N) (P : Type w)
    (D : templateLanguage.{u}.Structure P), IsTemplateChart β C →
    ∀ ι : @Language.Embedding templateLanguage.{u} N P C D,
      IsClosedIn D (Set.range ι.toEmbedding)

end ClosedRange

/-! ### The construction: conditions, steps and the limit -/

/-- **A condition of the universal construction** at a stage `α` on a carrier `M` (native
construction): an injective tuple `W` with a strongly coded legal stage type `w` on its points.
No class realization is given; the type is chosen by the construction. -/
structure UniversalCondition (α : Ordinal.{u}) (M : Type v) where
  /-- The number of points. -/
  N : ℕ
  /-- The tuple. -/
  W : Fin N ↪ M
  /-- The positional type of the tuple. -/
  w : StageType.{u} α N
  /-- The type is strongly coded legal. -/
  isStronglyCodedLegal : w.IsStronglyCodedLegal

namespace UniversalCondition

variable {α : Ordinal.{u}} {M : Type v}

/-- **Extension of conditions with literal root preservation** (native construction): the tuple
of `c` is the face of the tuple of `d` along `e`, point by point, and the type of `c` is literally
the face of the type of `d` along `e`. -/
def Extends (c d : UniversalCondition.{u, v} α M) : Prop :=
  ∃ e : Fin c.N ↪ Fin d.N, e.trans d.W = c.W ∧ StageType.restrictFace e d.w = some c.w

/-- **An exact task done at a condition** (native construction): the root `t` is a face of the
tuple of `c` along some `h`, and if its type `p` (the face of the type of `c` along `h`) is the
face along `g` of a strongly coded legal `D`, some face `i.trans c.W` of the tuple of `c` extends
`t` along `g` and has the type `D` itself. -/
def ExactTaskDone (c : UniversalCondition.{u, v} α M) {k m : ℕ} (t : Fin k ↪ M)
    (D : StageType.{u} α m) (g : Fin k ↪ Fin m) : Prop :=
  ∃ h : Fin k ↪ Fin c.N, h.trans c.W = t ∧ ∀ p, StageType.restrictFace h c.w = some p →
    D.IsStronglyCodedLegal → StageType.restrictFace g D = some p →
      ∃ i : Fin m ↪ Fin c.N, g.trans (i.trans c.W) = t ∧ StageType.restrictFace i c.w = some D

end UniversalCondition

section Steps

/-- **Target: fresh placement** (native construction): on an infinite carrier, every injective
tuple `W` on `N` points extends along any embedding `i : Fin N ↪ Fin N'` to an injective tuple on
`N'` points; the points outside the range of `i` go to points outside the range of `W`. -/
def FreshPlacementTarget (M : Type v) : Prop :=
  Infinite M → ∀ ⦃N N' : ℕ⦄ (i : Fin N ↪ Fin N') (W : Fin N ↪ M),
    ∃ U : Fin N' ↪ M, i.trans U = W

variable (α : Ordinal.{u}) (M : Type v)

/-- **Target: the point step** (native construction): at a stage that is zero or a limit, every
condition extends to one whose tuple contains finitely many given points. -/
def UniversalPointStepTarget : Prop :=
  Order.IsSuccPrelimit α → ∀ (c : UniversalCondition.{u, v} α M) (A : Finset M),
    ∃ d : UniversalCondition.{u, v} α M, c.Extends d ∧ ∀ a ∈ A, a ∈ Set.range d.W

/-- **Target: the exact task step** (native construction; the first genuinely new construction):
at a stage that is zero or a limit, on an infinite carrier, every condition extends to one at
which a given exact task is done, by a point step, the strongly coded amalgam of the donor with
the type of the condition over the literal root face, and fresh placement of the new points. -/
def UniversalTaskStepTarget : Prop :=
  Order.IsSuccPrelimit α → Infinite M → ∀ (c : UniversalCondition.{u, v} α M) {k m : ℕ}
    (t : Fin k ↪ M) (D : StageType.{u} α m) (g : Fin k ↪ Fin m),
    ∃ d : UniversalCondition.{u, v} α M, c.Extends d ∧ d.ExactTaskDone t D g

/-- **Target: the limit of a chain of conditions** (native construction): a chain of conditions,
each extending the previous one, that meets every point requirement and every exact task gives a
realization in the strongly coded receiving class, with exact receiving of every strongly coded
legal donor, that reads every condition of the chain literally (the type of a face of the tuple of
a condition is the face of its type). -/
def UniversalChainLimitTarget : Prop :=
  ∀ cs : ℕ → UniversalCondition.{u, v} α M, (∀ n, (cs n).Extends (cs (n + 1))) →
    (∀ a : M, ∃ n, a ∈ Set.range (cs n).W) →
    (∀ ⦃k m : ℕ⦄ (t : Fin k ↪ M) (D : StageType.{u} α m) (g : Fin k ↪ Fin m),
      ∃ n, (cs n).ExactTaskDone t D g) →
    ∃ R : Realization.{u, v} α M, R.IsStronglyCodedReceiving ∧
      R.ExactReceivingWithin (fun m ↦ {D : StageType.{u} α m | D.IsStronglyCodedLegal}) ∧
      ∀ (n : ℕ) ⦃k : ℕ⦄ (h : Fin k ↪ Fin (cs n).N),
        R.eval (h.trans (cs n).W) = StageType.restrictFace h (cs n).w

end Steps

end

end VaughtConjecture
