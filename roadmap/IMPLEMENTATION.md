# Implementation roadmap: spine, layers, discipline, checkpoints

This document sharpens [`README.md`](README.md) into an implementation order with explicit
semantic guards and acceptance checkpoints.  Where the two differ, this one prevails; in
particular the upper bound below goes through Scott separation on the persistent core, and
thinness through the library's thinness theorem for countable sentence splits, not through
Morley's dichotomy.  `README.md` remains the mathematical roadmap, `SEMANTIC_CONTRACT.md` fixes
the meanings to preserve, and [`Suggested.lean`](Suggested.lean) /
[`SuggestedInterfaces.lean`](SuggestedInterfaces.lean) give selected, nonexhaustive Lean
statements.  Do not turn their abstract structure fields into substitutes for the constructions.

The two documents number their parts differently.  The table maps the layers and summits of
`README.md` to the layers and checkpoints below.  The checkpoint order is the build order
(the finite extension constructions, checkpoint 2, before the realizations, syntax, and
countable chain construction, checkpoint 3), not the layer numbering of either document.

| `README.md` | Layers here | Checkpoints |
| --- | --- | --- |
| Layer 0, Summit 0: general results | used in 1–5 (below) | with their first application |
| Layer 1, Summit 1: finite semantic kernel, closed charts | 1; stage types, faces of 2 | 1 |
| Layer 2, Summit 2: realizations, syntax, chain construction | 2; chain construction of 3 | 3; 4 |
| Layer 3, Summit 3: finite extensions, receiving, recovery | 3; first uses of 1 | 2–5 (below) |
| Layer 4, Summit 4: continuation, terminal comparisons | 4 | 5 |
| Layer 5, Summit 5: expansion domains and logical agreement | 5 | 5 (unique limit expansions), 6 |
| Layer 6, Summit 6: the two independent bounds | 5 and the spine | 6 |
| (none; companions) | milestones A–C (`COMPANIONS.md`) | not core checkpoints |

The general results of Layer 0 are used in layers 1 (lifting), 2 (finite hulls), 3 (chain
construction), 4 (directed limits, back-and-forth, subsingleton covers), and 5 (countable
losses), each at the checkpoint of its first application.  Layer 2 of `README.md` reaches
checkpoint 3 and, with the fidelity theorem, checkpoint 4.  Layer 3 of `README.md` is spread over
four checkpoints: 2 (item 3.1, the construction of every row of its table with its section
theorem), 3 (the first uses of rows 5 and 6: top-free existence and general model existence),
4 (items 3.2 and 3.3 for rows 1–4, the first use of row 1, and the cap-to-model theorem), and 5
(the first uses of rows 2–4).  The companion milestones are summarized under "Companion
boundaries".

## Environment

Lean `v4.35.0-rc3`; InfinitaryLogic at the revision pinned in `lakefile.toml`; Mathlib
inherited from InfinitaryLogic's manifest.  Nothing else is imported.  Search the
pinned InfinitaryLogic first and delete any local lemma that duplicates one already upstream.

## Scope and completion

Construct an explicitly countable relational language and an `L_{ω₁,ω}` sentence whose countable
models have exactly `ℵ₁` isomorphism classes and no perfect isomorphism antichain.  The sentence is
the density sentence of layer 2 (the structural clauses and the one-point capped-extension clause).
State both the natural-number-code and the all-countable-carrier formulations, with the
no-finite-model bridge explicit.  This is not a first-order Vaught result and is not a comparison
with the continuum.

The core is complete only after every finite construction, realization over a root, recovery
of donor labels, syntax correspondence, the equivalence of the density sentence with the
four-family sentence (layer 2), and statement of the main theorem below is proved.
Completion is not limited to the signatures in the sketches.  Each definition needs its usable
basic API: projections, extensionality, identity/composition, restriction, transport, and
representative examples.

Under-specified extensions are not part of this roadmap.  Separate companion roadmaps may
cover hull algebra/cardinality (`HULL_ALGEBRA.md`), model-code topology, `T∞` (the set of
sentences true in all but countably many classes) and its logical filtration, effective syntax,
and uncountable models; `COMPANIONS.md` organizes the filtration and `T∞`, chart homogeneity,
and a geometric obstruction as three optional milestones.  They are not prerequisites of this
core.

## The mathematical spine

Let `Q` be countable base models modulo isomorphism, with actual satisfaction `truth φ q`.
At block `λξ = ω + ω·ξ`, let `Dξ` mean existence of a model expansion.  The construction
establishes:

1. `D0 = Q`, decreasingness, and continuity at countable nonzero limits.
2. Countable successor losses, by fixed-stage terminal comparison.
3. Cofinally nonempty losses, witnessed independently by top-free terminal models.
4. Agreement in `Dη` on sentences of quantifier rank at most `η`.
5. Scott separation of distinct classes and faithful satisfaction on model codes.

Countable-loss induction gives countable complements.  Scott separation makes the persistent core
`⋂_η Dη` subsingleton.  Its complement is covered by `ℵ₁` many countable exceptions, so `|Q| ≤ ℵ₁`;
disjoint cofinal losses give the reverse inequality.  This counting argument (countable complements
and Scott separation give at most `ℵ₁` classes) belongs to the setting of minimal counterexamples of
Harnik–Makkai [HM77]; see Larson [Lar14], Remark 10.9, and its discussion of minimal
counterexamples.  Separately, homogeneous domains give one countable truth side for each sentence,
and the library's thinness theorem `Sentenceω.isThinOnNatModels_of_countable_sentence_splits`
(`Descriptive/SentenceSplits`) rules out a perfect antichain.  Neither Morley's dichotomy nor
eventual stopping belongs in this proof.  There is no measurable structure or measurable choice of
representatives on `Q`.

The general counting argument above needs cofinal nonemptiness, not nonemptiness of every
successor loss.  The concrete top-free construction proves the stronger statement.  Do not
replace either hypothesis by mere nonemptiness of the domains.

## Required layers and first applications

### 1. Finite geometry and guarded label algebra

Define raw finite plans, graded cells with scopes, semantic rows, visibility replacement, and
lawful labels separately from their laws.  Establish the plan characterization by finite convex
geometries with exactly two extreme points on every nonsingleton closed set.  Preserve physical
cell multiplicities: distinct cells can share a graded index.  Preserve the actual ordered-cell
semantics until an order-independence theorem is proved.

Distinguish orderly labellings [Kni26, Definition 2.3.4] from legal schemes, the domains of
[Kni26, Definition 2.6.1] (both are defined in Layer 3 of `README.md`).  Distinguish bottom,
ordinal zero, proper labels, and formal top.  Stage labels are below the stage or top; bottom is
below zero.  Keep two notions of cap apart.  A permitted cutoff satisfies `⊥ < δ < α`, which
allows ordinal zero; receiving and density quantify over permitted cutoffs.  A self-visible cap
at grade `j` is a label `c` with `vr_j(c, j) = c` (bottom, top, or a `j`-times successor), which
excludes ordinal zero for `j ≥ 1`; bountifulness and lawful capping concern self-visible caps.
The transformation relation is **nontransitive**; prove only the guarded composition, cap, jump,
band, and truncation rules actually used, and never declare a transitivity instance.

Prove lawful restriction and the exact lifting calculus.  Bountifulness is per cap, at every cap
self-visible at the target grade ([Kni26, Definition 2.5.14], clause 7); the lift is not
available in general at other caps.  Capping a lawful section at a cap self-visible at a bound on
its grades is lawful ([Kni26, Lemma 2.5.8]); capping at an arbitrary cutoff need not be.  The
calculus does not rely on the printed statements of [Kni26] that Layer 1 of `README.md` lists as
incorrect (among them the transitivity of Lemma 2.3.14 and the pointwise minimum of Lemma 2.5.11).

Per-cap lifting does not give simultaneous preservation of all compatible caps, and the construction
does not need it.  When a prescription `p` differs from the face `a` of the ambient section, let `m`
be the least value of `min (pᵢ, aᵢ)` over the differing coordinates; the compatible caps are the
caps self-visible at the target grade and at most `m`, and they need not have a maximum.  At target
grade 3 with `m = ω·2 + 1` they are bottom and the ordinals `i` and `ω + i` with `3 ≤ i < ω`; with
`pᵢ = ω + 1` and `aᵢ = ω + 2` they are bottom and the natural numbers `i ≥ 3`.  When they do have a
maximum, a lift at it preserves every compatible cap, because caps nest under `min`
(`min (min x m) c = min x c` for `c ≤ m`); when `p` is literally the face of `a`, the ambient
section itself preserves every cap.  Simultaneous preservation in general is not proved.  Its only
known route is the sketch lemma `preserves_all_compatible_observations`
(`SuggestedInterfaces.lean`), under injectivity of restriction, i.e. uniqueness of extension, which
is not available in general (`README.md`, Layer 0).  It is not needed: density asks for one
extension for each cutoff, and different cutoffs may use different extensions.  Each per-cap lift
preserves its cap on **all** target coordinates, including auxiliaries and future fields (defined in
Layer 3 of `README.md`).  A statement that recovers only a few labels from the observation does not
weaken the lifting requirement.

First applications: the coatom extension construction and the two required applications of the
shared decoding lemma, to the growth construction of rows 3 and 4 and to the LOW construction of
row 2 (Layer 3 of `README.md`, item 3.1).  Avoid a general categorical formalism before these
examples work.

### 2. Types, partial faces, realizations, and explicit syntax

A type contains its finite scheme and lawful stage-bounded labels.  A realization assigns an
optional type to each injective finite tuple.  Exact consistency is conditional on an **actual
parent**; it includes the `none` result for invisible faces of that parent.  It does not say
that every subtuple of an undefined parent is undefined.  Likewise restriction composition
requires the intermediate face to be defined.  The sketch deliberately retains those guards.

Separate face restriction, ordinal reduction, and cap observation.  Establish reindexing and
stage reduction identities before dependent transport spreads.  From consistency and covering
alone derive directed actual covers and finite hulls.  Do not identify a two-generator hull with
an evaluated two-point root.

At stage `ω`, take one `n`-ary relation symbol for each legal stage type of arity `n`, and no
functions.  Prove symbol countability; spell out the finite coding and bounded bottom/natural/top
tables if a computable coding of the symbols is included.  The structural base theory records
injective tuples, unique labels, exact face coherence, covering, and nonemptiness.  Define the
density sentence by these structural clauses and the one-point capped-extension clause; it is the
sentence of the main theorem.  Keep nonemptiness explicit until its redundancy is proved.  Cutoffs
here are natural numbers, including zero.

Density quantifies `∀ root, ∀ donor, ∀ cutoff, ∃ extension` on the fixed donor scheme.
Different cutoffs may use different points.  Prove both satisfaction directions, the
realization/structure round trips, isomorphism preservation and reflection, and no finite
models.  The density sentence is the preferred presentation.  Its equivalence with the
four-family sentence (the structural clauses together with the four extension families of
`SEMANTIC_CONTRACT.md`, item 5, and [Kni26, Definition 3.2.1], clause 4) is a required fidelity
theorem and part of the completion criterion.  Its direction from the four-family sentence to the
density sentence still uses the finite-cut receiving statement (row 1 of the table of
Layer 3 of `README.md`), which therefore remains a prerequisite of completion.  Its direction
from the density sentence to the four-family sentence uses the cap-to-model theorem (item 3.4 of
that layer), which needs only the coatom extension construction; the cap-to-model theorem is
therefore proved at checkpoint 4 with the fidelity theorem, before stable modelhood uses it again
at checkpoint 5.

### 3. Finite extensions, realization over roots, recovery of labels, and one chain construction

Layer 3 of `README.md` is the specification of this layer.  It defines the vocabulary (root,
donor type and donor occurrence, receiving over a root, permitted cutoff and self-visible cap,
private context with its private cap, marker, and reference cells, master chart, padding,
freshness, bottom pattern, literal-top prescription, orderly and lawful labellings, legal scheme,
fields, state vectors, catalogue, decoder, and future fields, owners, ownerwise decoding,
long-row locality, the section theorem, display, gate and gate equation, the coatom extension
construction, pinned and exact pinned extension, restriction-compatible labelling, `Correct`,
LOW, and the cap-to-model theorem) and consists of four items, built in this order:

1. **Statements of the finite extension constructions, and the section theorem.**  For each: input
   data, compatibility conditions, the constructed finite object (a legal scheme with its
   embeddings and, where the row uses one, a display, as data), and its literal equations,
   among them that the private type and the donor type are the literal ordered face-map
   restrictions of the constructed scheme.  Every root size and padding length; designated
   freshness; literal retention of the root and of every row, occurrence, and label of the
   master chart; bottom patterns and literal-top prescriptions given separately; bountifulness
   at every self-visible cap of the target grade, each lift preserving its cap on every target
   coordinate, auxiliaries and future fields included; future fields retained literally.  Per-cap
   lifting is not simultaneous preservation, which is neither proved nor needed (layer 1 above).
   The shared decoding lemma supplies the lawful sections: from a lawful input and a cellwise
   value map that is a witness bounded by the top grade, the mapped section is lawful provided
   each owner has short rows or satisfies mapped locality.  Long-row locality of an inherited
   owner is the transport of the original rows' lawfulness along the exact base table, using the
   decoder's bottom reflection.  The growth construction (rows 3 and 4) and the LOW construction
   (row 2) are both required applications.  The two-witness splice for the rows of the proof of
   [Kni26, Lemma 5.3.5] other than the top-witness row is also proved here.
2. **One occurrence, then labelled evaluation.**  The realization extends by **one actual
   occurrence** of the constructed scheme over the private context, by a row-specific model
   clause: the bottom-pattern clause with the display and the gate (row 1); row 1 itself, with
   the LOW display as donor (row 2); generalized saturation, with no display (rows 3 and 4).
   Root, private context, donor values, and gate equation all concern that occurrence.  For
   rows 3 and 4 the recovery statement is proved for every restriction-compatible labelling
   whose private face lies in the prescribed bottom class, then applied to the actual labels
   (row 3) or to the stable labelling (row 4).  Rows 3 and 4 share the constructed scheme and
   the recovery statement; their acquired data, the labelling evaluated, and their existence
   hypotheses stay separate.
3. **`Correct`, LOW, and the recovery statements.**  `Correct` consists of three clauses capped
   at the value of the private cap, which can be top: bottom, reference with its offset
   replacement, and a marker lower bound; it has no gate.  LOW is gate-free: its forcing puts
   every donor-top field above the cutoff and the private gap value once the cutoff exceeds the
   non-top donor maximum, and its recovery returns the donor exactly, tops included, from
   agreement with the display below a cutoff above the rounded non-top donor maximum.  Agreement
   below a cutoff, exact recovery of proper labels, literal-top recovery (from LOW, or from
   `Correct` when the private cap is top), and above-threshold inequalities are different
   conclusions.  Agreement below one permitted cutoff cannot distinguish a proper label above
   the cutoff from top.  Each recovery lemma lists the observations it reads and does not
   require recovery of the whole type of the constructed occurrence.
4. **Extension statements and first uses** (the table of `README.md`, Layer 3): finite-cut
   receiving, first used by the one-sided donor transfer (and by the four-family-to-density
   direction of layer 2); exact residual receiving, by the residual comparison; exact
   hollow-growth receiving, by the hollow comparison; capped receiving for the stable candidate,
   by stable modelhood; the top-free pinned extension, by the top-free capped chain
   construction; the exact pinned extension, by general model existence.  Each row records its
   exact hypotheses, its conclusion, and its import boundary.  Rows 1–4 conclude on one
   occurrence over the literal root and have recovery theorems; rows 5 and 6 are extension
   statements about charts, without an occurrence or a recovery theorem.  The positive-length
   root restrictions and the empty-root base cases are explicit, and the cap-to-model theorem is
   stated with the table.

Use one countable chain construction on finite master conditions, with the exact and the capped
finite extension hypotheses stated separately.  Derive partial states from the master; do not
store synchronized copies.  Absorb the root before deciding its request.  A supported invisible
face is not an unsupported tuple.  Resolve repeated and delayed requests monotonically.  Use
Mathlib's cofinal-chain machinery and prove the coherent union once.

First applications: general model existence (row 6) and the top-free capped construction (row 5).
The modules of the finite extension constructions must not import the infinite chain construction.
Direct limits of structures, a generic result of infinitary logic, stay outside this layer: they
replace no finite extension construction and no decoding or recovery statement.

### 4. Stable continuation and terminal comparison

Build rooted covers and their monotone natural offsets.  The completed value lives in `ℕ∞`,
decoded back to labels: infinity decodes to formal top, not `α + ω`.  Keep consistency-only
stable uniqueness/naturality, consistency-plus-covering stable lawfulness, and
receiving/modelhood as different theorem layers.

Construct the stable realization and literal reduct before proving modelhood.  Normalize any
genuine expansion pointwise to the structural candidate; handle undefined tuples using the
literal reduct.  Derive modelhood separately by cap receiving (row 4 of the table of Layer 3
of `README.md`) and the cap-to-model theorem of checkpoint 4.  Keep positive-root requirements
and the empty-root base case explicit.

Use selected-chart rooted back-and-forth, not a second fair-chain comparison.  The chosen root
must belong to the extendible family; atomic agreement alone does not suffice.  Count terminal
classes by an overlapping countable family of singleton conditions: specified rigid-core type,
coreless eventual top grade, and hollow growth.  Do not construct a complete profile invariant.
Discharge grade zero via the empty rigid core.  Preserve the original anchor definition;
stable-label fixedness is a characterization under stated hypotheses.

### 5. Unique expansions, domains, and the main theorem

Prove unique partial expansions and countable-limit existence.  Coherence of a family of lower
expansions is derived from uniqueness, not a hidden hypothesis.  Map successor losses to
terminal classes.  Independently construct top-free terminal models at each countable block;
expansion uniqueness is what places their **base classes** in the corresponding successor
differences.

Prove the one-sided finite-donor transfer first, using only target consistency and finite-cut
receiving (row 1).  Symmetrize for back-and-forth: one block buys one level, with no extra `ω`
factor.  Handle repeated coordinates and empty tuples.  Apply the sentence-agreement argument once,
keeping the cardinality conclusion separate from the descriptive thinness conclusion.  In
`SuggestedInterfaces.lean`, `SentenceAgreementDomains` is a structure (countable-stage domains
with countable complements, eventual constancy of each sentence on them, and separation of
distinct classes by a sentence) with two proved lemmas: `persistent_subsingleton` (the
persistent core has at most one element) and `countable_truth_side`.  The `ℵ₁` step (the
persistent core is a subsingleton and the remaining classes lie in `ℵ₁ · ℵ₀` many exceptions,
so `|Q| ≤ ℵ₁`) is a target still to be proved, not a lemma of the sketch.

## Upstream building blocks

In the pinned InfinitaryLogic:

- `PotentialIso.ofExtensionFamily` and the countable potential-isomorphism corollaries
  (`Karp/`);
- Scott isolation and countable definability on a presentation of the classes
  (`Descriptive/ScottDefinability`, e.g. `exists_sentence_of_countable_of_presentation`), and
  constancy of sentence families off countably many classes (`Descriptive/ObservableConstancy`);
- thinness from single-sentence splits on a presentation of the classes,
  `Sentenceω.isThinOnNatModels_of_countable_sentence_splits` (`Descriptive/SentenceSplits`).
  Its only hypotheses are that the truth predicate is actual satisfaction read through the
  presentation and that every sentence has a countable truth side; it does not use Scott
  isolation, ranks, measurability on `Q`, or Borelness of the class;
- `exists_countable_aElementary_substructure`;
- the generic finite-support closure (`FiniteSupportClosure`) with its two-generator
  cardinality theorem (`TwoGeneratorCardinality`);
- `compl_countable_of_loss` (`OrdinalCountability`), which gives the countable domain
  complements.  The same module's `mk_eq_aleph_one_of_domains` is not used for the upper
  bound: `|Q| ≤ ℵ₁` is the direct cover of the spine (the persistent core is a subsingleton
  and each complement `Q \ Dη` is countable).  That theorem assumes global eventual departure
  (every point leaves some domain) and nonempty domains, and yields the equality only from
  both.  On the complement of the persistent core, departure holds, but nonemptiness requires
  every domain to contain a class outside the core, which is the lower-bound input.  It may
  therefore be quoted, if at all, only for the final equality once both bounds are known, with
  its eventual-departure hypothesis discharged on the complement of the core;
- the Gδ/Polish model-code spaces;
- `internalScottRank_le_of_orbits_determined` (`Scott/OrbitRank`), used only by the companion
  full-chart orbit theory (milestone B of `COMPANIONS.md`).

`SuggestedInterfaces.lean` checks representative names, so a pin bump that removes one fails
when the sketch is checked (the checks are run by CI).  Coding a `Type w` carrier on `ℕ` needs a
transfer of infinitary isomorphism across universes; do not assume that a statement within a
single universe covers it.

## Automation and API discipline

- Make constructor projections, identity reindexings, and canonical cell transport
  directional `[simp]` lemmas.  Use `ext` on data, and narrow `simp only` for dependent face
  equations.  Do not unfold whole schemes/models globally.
- Separate natural-index arithmetic (`omega`) from ordinal/band inequalities; expose exact
  band-comparison lemmas before asking automation to solve goals.
- Use `funext`, `Function.Embedding.ext`, `Subtype.ext`, and proof irrelevance to finish
  transport bookkeeping.  Give explicit structure instances where a structure is coded, rather
  than letting inference pick an unintended structure.
- Reuse finite `decide`/`fin_cases` checks of examples of rows and schemes.  A finite
  enumeration checks examples; it is not a proof of the general characterization.
- Restriction, reduction, and cap rewrites must have distinct names/rule sets.  Never declare
  transformation transitivity as a `simp` lemma or a typeclass instance.
- Name and test the general lemmas on actual applications before adding automation:
  per-cap lift, ownerwise decoding, finite synchronization, and recovery of donor labels from
  the same occurrence.  Avoid a tactic that conceals missing side conditions.

## Checkpoint order and acceptance

Each checkpoint needs both its abstract API and a concrete application:

1. Finite geometry, scalar label algebra, transport regressions.
2. Item 3.1 of Layer 3 of `README.md`: the legal finite extension construction of every row of
   its table, as data with its literal equations, bountifulness at every self-visible cap with
   cap preservation on every target coordinate, and the section theorem by the shared decoding
   lemma, with its applications to the growth and LOW constructions; small, empty, top/bottom
   and invisible cases.
3. Realizations, literal syntax correspondence, countable chain construction, general model
   existence (the first use of row 6, the exact pinned extension) and top-free existence (the
   first use of row 5, the top-free pinned extension).
4. Items 3.2 and 3.3 for rows 1–4: for each row, the extension of the realization by one actual
   occurrence over the literal root and the recovery theorem (by `Correct` and labelled
   evaluation, by LOW, or through the gate), with all its equations on that occurrence and at
   every permitted cutoff; the first use of row 1, the one-sided donor transfer; the
   cap-to-model theorem; and the fidelity theorem of layer 2, the equivalence of the density
   sentence with the four-family sentence, whose two directions use row 1 and the cap-to-model
   theorem.
5. Structural continuation, three terminal comparisons (the first uses of rows 2 and 3), stable
   modelhood (the first use of row 4, with the cap-to-model theorem), unique limit expansions.
6. Domain hypotheses of the counting theorem, independent bounds, thinness and all-countable
   bridge.

At every checkpoint: full build, strict per-file checks, no `sorry`, standard axioms only,
universe/empty/repeated-coordinate regressions, and review of semantic statements.  Audit proof
dependencies **and** import closures separately.  Passing CI is not a substitute for checking
the statements against the roadmap and the semantic contract.

The library may grow Lean while shortening the informal proof.  Prefer applications of standard
logic and descriptive set theory, and exact statements of the constructions, over a smaller
file count.  Do not reproduce compatibility layers, abandoned proof strategies, rank detours,
or lemmas with no application.

## Companion boundaries

Companion topics: definable domain/logical cuts with strict loss-rank lower bounds; canonical
top-free classes converging sentencewise; the joint embedding and amalgamation properties (JEP/AP)
of finite closed charts; local automorphisms of self-embeddings; and the arbitrary-carrier
Scott/`T∞` theory dichotomy.  These do not assert strong AP, a proper self-embedding, uncountable
categoricity, Scott-rank equality, or existence of a model of all of `T∞`.  The main theorem is
proved without them; if any is added, give it a separate definite completion criterion.  Direct
limits of structures, a generic result of infinitary logic, belong with the generic library and
these companion results, not with the finite constructions of layer 3.
[`COMPANIONS.md`](COMPANIONS.md) gives these topics and the full-chart orbit theory below such
criteria, as three milestones (A: filtration and infinitary theory; B: top-free chart homogeneity
and its consequences; C: a geometric obstruction).

### Full-chart orbit theory: a companion checkpoint

The targets of this checkpoint are now milestones B and C of [`COMPANIONS.md`](COMPANIONS.md),
which states each with its hypotheses, upstream ingredients, instantiation, regressions, and
non-claims, and gives the companion sketch [`SuggestedCompanions.lean`](SuggestedCompanions.lean).
In summary: in the full stage chart language (not the base reduct), a countable nonempty top-free
realization with exact consistency, covering, and finite-cut receiving has automorphism orbits
defined by explicit first-order chart formulas, hence isolated complete types, atomicity,
internal Scott rank at most `ω` in the library's convention, and, by a separate generic theorem,
primeness among models of its complete theory in arbitrary universes; separately, consistency and
covering alone exclude every infinite set whose permutations all extend to automorphisms, a
theorem kept below receiving by an import guard.  Milestone A of `COMPANIONS.md` treats the
definable cuts, witness convergence, and the Scott/`T∞` dichotomy listed above.

**Completion criterion.**  This companion checkpoint is complete when milestones B and C of
`COMPANIONS.md` meet their completion criteria.  It is not a core checkpoint, and the main
theorem does not depend on it.
