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
classical limit of the top-free witnesses, checkpoint 3), not the layer numbering of either
document.

| `README.md` | Layers here | Checkpoints |
| --- | --- | --- |
| Layer 0, Summit 0: general results | used in 1–5 (below) | with their first application |
| Layer 1, Summit 1: finite semantic kernel, closed charts | 1; stage types, faces of 2 | 1 |
| Layer 2, Summit 2: realizations, syntax, hull operations | 2 | 3; 4 |
| Layer 3, Summit 3: finite extensions, receiving, recovery | 3; first uses of 1 | 2–5 (below) |
| Top-free witnesses: the finite age, its classical limit | 3 (steps 1–7) | 3 (1–6); 4, 5 (7) |
| Layer 4, Summit 4: continuation, terminal comparisons | 4 | 5 |
| Layer 5, Summit 5: expansion domains and logical agreement | 5 | 5 (unique limit expansions), 6 |
| Layer 6, Summit 6: the two independent bounds | 5 and the spine | 6 |
| (none; companions) | milestones A–C (`COMPANIONS.md`) | not core checkpoints |

The general results of Layer 0 are used in layers 1 (lifting), 2 (finite hulls), 3 (the
classical limit: Fraïssé existence, ultrahomogeneous extension, factorization of tuples through
the age), 4 (directed limits, back-and-forth, subsingleton covers), and 5 (countable losses),
each at the checkpoint of its first application.  Layer 2 of `README.md` reaches
checkpoint 3 and, with the fidelity theorem, checkpoint 4.  Layer 3 of `README.md` is spread over
four checkpoints: 2 (item 3.1, the construction of every row of its table with its section
theorem), 3 (the first uses of rows 5 and 6: the amalgamation of top-free charts and receiving
in the classical limit),
4 (items 3.2 and 3.3 for rows 1–3, the recovery statement of rows 3 and 4 for every
restriction-compatible labelling, the first use of row 1, and the cap-to-model theorem), and 5
(items 3.2 and 3.3 for row 4 after the structural candidate, and the first uses of rows 2–4).
Checkpoint 2 is subdivided: the completion of the coatom extension construction (row 6) is
checkpoints 2.1–2.7 (below), the seven checkpoints of `README.md`, Layer 3, 3.1, under "Row 6".
The construction of the top-free witnesses, the finite age and its classical limit, is the
section of that name in `README.md`, after Layer 3; its seven steps, with their acceptance
criteria and checkpoints, are under "The top-free witnesses: milestone order and acceptance"
below.  The companion milestones are summarized under "Companion boundaries".

## Environment

Lean `v4.35.0-rc3`; InfinitaryLogic at the revision pinned in `lakefile.toml`; Mathlib
inherited from InfinitaryLogic's manifest.  Nothing else is imported at present.  After the
repin under "Dependency pins" below, ComputableModelTheory is the one further dependency.
Search the pinned libraries first and delete any local lemma that duplicates one already
upstream.

## Scope and completion

Construct an explicitly countable relational language and an `L_{ω₁,ω}` sentence whose countable
models have exactly `ℵ₁` isomorphism classes and no perfect isomorphism antichain.  The sentence is
the density sentence of layer 2 (the structural clauses and the one-point capped-extension clause).
State both the natural-number-code and the all-countable-carrier formulations, with the
no-finite-model bridge explicit.  This is not a first-order Vaught result and is not a comparison
with the continuum.

The core is complete only after every finite construction, realization over a root, recovery
of donor labels, syntax correspondence, the equivalence of the density sentence with the
four-family sentence (layer 2), the top-free witness at every countable block (the
reconstruction of a classical limit meeting its acceptance criterion), and statement of the main
theorem below is proved.
Completion is not limited to the signatures in the sketches.  Each definition needs its usable
basic API: projections, extensionality, identity/composition, restriction, transport, and
representative examples.

Under-specified extensions are not part of this roadmap.  Separate companion roadmaps may
cover the definability consequences of the hull operations and hull cardinality
(`HULL_ALGEBRA.md`, §4; the operations themselves are core, layer 2), model-code topology,
`T∞` (the set of sentences true in all but countably many classes) and its logical filtration,
effective syntax, and uncountable models; `COMPANIONS.md` organizes the filtration and `T∞`,
chart homogeneity, and a geometric obstruction as three optional milestones.  They are not
prerequisites of this core.

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

**Hull operations.**  At every stage, construct the definable total binary hull operations
(`HULL_ALGEBRA.md`) and prove the five facts of `README.md`, Layer 2, and only these: finite
hulls and their generation by two extreme points; definable total hull operations with values in
the hull of the arguments; preservation of the operations by chart embeddings (and by embeddings
of the relational reducts of exactly consistent covering realizations), including the default
value where no chart witness exists; closed images of embeddings; and the correspondence between
finite expanded substructures and actual charts (a chart is read as its partial realization with
the operations computed in it).  Preservation is proved from the chart witnessing each operation,
not from definability alone.  The closed-image proofs import no cardinality material.  Nothing
else of `HULL_ALGEBRA.md` is core: cardinal bounds, uncountable maximality, the descriptive
consequences, the inclusions in `dcl` and `acl`, and the equality (1) for infinite sets stay
downstream.

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

### 3. Finite extensions, realization over roots, recovery of labels, and the classical limit

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
   value map that is a witness bounded by the top grade (a witness of [Kni26, Definition 2.3.9]
   whose suppressor is top up to that grade and bottom above, so that clause 5 still constrains
   it above the grade), the mapped section is lawful provided each owner has short rows or
   satisfies mapped locality.  Long-row locality of an inherited owner is the transport of the
   original rows' lawfulness along the exact base table, using the decoder's bottom reflection.
   The growth construction (rows 3 and 4) and the LOW construction (row 2) are both required
   applications.  The two-witness splice is also proved here: for a top-labelled cell `Σ` of
   grade `J ≤ K` below a top-witness cell `Θ`, a witness from `E(Σ)` to the labels below `Σ`
   and a witness from `E(Σ)` to the row of `Θ` capped at its entry at `Σ` combine into a
   witness from `E(Σ)` to the labels where they are below `α` and, where they are top, to the
   band map of the capped row with a base (zero or a limit) that the capped row does not fall
   below there.  It replaces the transitivity step in the proof of
   [Kni26, Lemma 5.3.5] for the rows other than the top-witness row.  Row 6 is reduced to the
   coatom extension property at a stage, whose proof, in its apex form, is the completion of the
   amalgam of [Kni26, Definition 4.3.1] by cells of full scope (checkpoints 2.1–2.7 below).
2. **One occurrence, then labelled evaluation.**  The realization extends by **one actual
   occurrence** of the constructed scheme over the private context, by a row-specific model
   clause: the bottom-pattern clause with the display and the gate (row 1); row 1 itself, with
   the LOW display as donor (row 2); generalized saturation, with no display (rows 3 and 4).
   Root, private context, donor values, and gate equation all concern that occurrence.  For
   rows 3 and 4 the recovery statement is proved for every restriction-compatible labelling
   whose private face lies in the prescribed bottom class, then applied to the actual labels
   (row 3) or to the stable labelling (row 4).  That statement uses no stable labelling; the
   acquisition of row 4's calibrated data, its occurrence, and its evaluation need the
   structural candidate and come at checkpoint 5.  Rows 3 and 4 share the constructed scheme
   and the recovery statement; their acquired data, the labelling evaluated, and their
   existence hypotheses stay separate.
3. **`Correct`, LOW, and the recovery statements.**  `Correct` consists of three clauses capped
   at the value of the private cap, which can be top: bottom, reference with its offset
   replacement, and a marker lower bound; it has no gate.  LOW is gate-free: its forcing puts
   every donor-top field above the cutoff and the private gap value once the cutoff exceeds the
   non-top donor maximum, and its recovery returns the donor exactly, tops included, from
   agreement with the display below a cutoff above the rounded non-top donor maximum.  Agreement
   below a cutoff, exact recovery of the labels that are not top (bottom and proper, from LOW
   or from the bottom and reference clauses of `Correct`), literal-top recovery (from LOW, or
   from `Correct` when the private cap is top), and above-threshold inequalities are different
   conclusions.  Agreement below one permitted cutoff cannot distinguish a proper label above
   the cutoff from top.  Each recovery lemma lists the observations it reads and does not
   require recovery of the whole type of the constructed occurrence.
4. **Extension statements and first uses** (the table of `README.md`, Layer 3): finite-cut
   receiving, first used by the one-sided donor transfer (and by the four-family-to-density
   direction of layer 2); exact residual receiving, by the residual comparison; exact
   hollow-growth receiving, by the hollow comparison; capped receiving for the stable candidate,
   by stable modelhood; the top-free pinned extension, by receiving in the classical limit
   (step 6 below); the exact pinned extension, through the plain form of the coatom extension
   property, by the amalgamation of top-free charts (step 2 below).  Each row records its
   exact hypotheses, its conclusion, and its import boundary.  Rows 1–4 conclude on one
   occurrence over the literal root and have recovery theorems; rows 5 and 6 are extension
   statements about charts, without an occurrence or a recovery theorem.  The positive-length
   root restrictions and the empty-root base cases are explicit, and the cap-to-model theorem is
   stated with the table.

The countable models of the main theorem are the top-free witnesses, constructed by the finite
age and its classical limit (seven steps, under "The top-free witnesses: milestone order and
acceptance" below), not by a chain construction.  Derive the partial realization of a finite
chart from the chart; do not store synchronized copies.  A supported invisible face is not an
unsupported tuple.

First applications: the amalgamation of top-free charts (step 2, from the plain form of the
coatom extension property and capping) and receiving in the classical limit (step 6, rows 6
and 5).  The modules of the finite extension constructions import neither the classical limit
nor the chain construction.  Direct limits of structures and the classical existence theorem
(prospective) belong to the two libraries: they replace no finite extension
construction and no decoding or recovery statement.

### 4. Stable continuation and terminal comparison

Build rooted covers and their monotone natural offsets.  The completed value lives in `ℕ∞`,
decoded back to labels: infinity decodes to formal top, not `α + ω`.  Keep consistency-only
stable uniqueness/naturality, consistency-plus-covering stable lawfulness, and
receiving/modelhood as different theorem layers.

Construct the stable realization and literal reduct before proving modelhood.  Normalize any
genuine expansion pointwise to the structural candidate; handle undefined tuples using the
literal reduct.  Derive modelhood separately by cap receiving (row 4 of the table of Layer 3
of `README.md`) and the cap-to-model theorem of checkpoint 4.  Row 4's calibrated data, its
occurrence, and the evaluation of the stable labelling by the recovery statement of checkpoint
4 are built here, after the structural candidate.  Keep positive-root requirements and the
empty-root base case explicit.

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
expansion uniqueness, with same-carrier transport, is what places their **base classes** in the
corresponding successor differences: together they exclude another, higher expansion of the base
reduct.  Eventual stopping of every model is a consequence of the filtration, not an input.

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

## The top-free witnesses: milestone order and acceptance

`README.md`, section "The top-free witnesses: the finite age and its classical limit", is the
specification.  At the stage `λ = λ_η` (a nonzero countable limit), `L_λ` is the relational
stage chart language and `L^h_λ` its definitional expansion by the hull operations; the age of
top-free charts is the representative class of the finite `L^h_λ`-structures of the top-free
legal stage types at `λ`.  The steps are proved in this order; in particular amalgamation (step
2) precedes the existence of any infinite model (step 3), so that the limit is built from the
age and not recognized afterwards in a model constructed otherwise.

1. **Finite top-free charts.**  Acceptance: the family is constructed as data (a finite
   `L^h_λ`-structure for each top-free legal stage type at `λ`, its relations literally the
   visible faces with their types and no relation at a supported invisible face); the index is
   countable and contains the empty chart; each member is finitely generated.  Regressions: the
   empty chart, a one-point chart, a chart with an invisible pair, distinct cells sharing a
   graded index.
2. **Hereditary closure, amalgamation, joint embedding.**  Acceptance: the finitely generated
   substructures of a member are exactly its closed faces with their literal restrictions;
   amalgamation of two top-free charts over a common face, by the plain form of the coatom
   extension property followed by capping at a proper cap self-visible at the arity of the
   amalgam and above all labels of both charts, with the literal commuting square
   `f₁.trans g₁ = f₂.trans g₂` and literal restrictions to both charts; joint embedding as the
   case of the empty chart; the hypotheses of `isFraisse_representativeClass` in exactly its
   form (literal square).  Regressions: the empty common chart, a common chart equal to one of
   the two, equal charts with equal face embeddings, a common chart that is the hull of two of
   its points and has more than two points.  Strong amalgamation is not claimed or needed.  No
   infinite model is imported.
3. **Classical existence.**  Acceptance: `isFraisse_representativeClass` applied to the family,
   then the classical existence theorem (prospective), giving a countable
   `L^h_λ`-structure with
   `IsFraisseLimit`; the countability hypotheses (`[Countable (Σ l, L.Functions l)]`, countably
   many isomorphism types) are proved for `L^h_λ` and the age, not assumed.
4. **Reconstruction of partial evaluation.**  Acceptance: the evaluation of an injective tuple is
   defined from the chart relations of the limit, and the literal recovery and uniqueness
   clauses of the acceptance criterion (`SEMANTIC_CONTRACT.md`, item 11) are proved from the
   factorization of tuples through representatives.
5. **Consistency, covering, top-freeness, nonempty carrier.**  Acceptance: each proved from the
   factorization of one finite tuple through one representative; exact partial restriction with
   `none` at invisible faces; covering for arbitrary tuples `Fin n → M`, the empty tuple and
   repeated coordinates included; every evaluated type in the age.
6. **Receiving.**  Acceptance: for every root, one-point donor type, and permitted cutoff, an
   occurrence over the literal root from row 5 and `IsUltrahomogeneous.extend_embedding`, with
   all its equations on that one occurrence; exact receiving for top-free donors (cutoff above
   every label of the donor); for donors containing top, one extension for each cutoff, with no
   claim of one extension for all cutoffs or of recovery of a top.  Regressions: the empty
   root, a donor with top labels at two different cutoffs, a donor with bottom labels.
7. **Modelhood, infinitude, terminality.**  Acceptance: modelhood by the cap-to-model theorem
   (checkpoint 4); infinitude, with freshness of the received point over the whole finite
   chart: for a finite set `F`, the root is an actual occurrence `t` containing `F` (covering)
   and the donor a one-point coface of its type ([Kni26, Proposition 4.3.23], which supplies
   only the coface, a stage type on one more point, not a point of the realization); the
   receiving criterion, all equations on one injective occurrence extending `t` literally, puts
   the new point outside the whole chart `t`, hence outside `F`; terminality from top-freeness
   and the new band required at the next block, using only the reduction of models (layer 2).
   The placement of the base class in the loss at `η`, by expansion uniqueness and same-carrier
   transport, belongs to layer 5 (checkpoint 5).

**Dependency boundaries.**  The age argument (steps 1–7) imports Mathlib, InfinitaryLogic,
ComputableModelTheory, layers 0–2, and the finite kernel (layer 1, the coatom extension
construction with rows 5 and 6, and the cap-to-model theorem).  The classical part, steps 3–5,
imports no `Construction/` module and no module of rows 1–4, of structural continuation, or of
the expansion domains; steps 6 and 7 add only row 5, the cap-to-model theorem, and the
reduction of models.  The upstream
theorems import no module of this repository.  The chain construction (`Construction/`, the
chain unions of partial realizations, and the conditional chain construction of models) is
needed neither for top-free existence nor for saturated existence: the saturated model of
[Kni26, Proposition 4.4.5] is the classical limit of the uncapped age of all legal stage types
(hereditary, amalgamating by the plain form of the coatom extension property, countably many
isomorphism types).  No checkpoint of the main theorem depends on the chain construction.  It is
retained for an effective presentation, conditional on effective input data (an effective
enumeration of the age and an effective amalgamation procedure; the classical Fraïssé
construction uses choice and supplies no computable presentation), and as the existing
conditional development whose partial-realization statements (`StageType.chartRealization`,
`StageType.isConsistent_chartRealization`, `StageType.chartRealization_eval_eq_none_iff`) are
reused in steps 1, 4, and 5; its chain-union statements are not used by steps 1–7.

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
- `internalScottRank_le_of_orbits_determined` (`Scott/OrbitRank`), on which the library's
  orbit-formula rank bound (`README.md`, Layer 0) rests; this repository does not apply it
  directly, but quotes the rank bound (companion milestone B of `COMPANIONS.md`).

In the pinned Mathlib (`Mathlib/ModelTheory/Fraisse.lean`): `age`, `Hereditary`,
`JointEmbedding`, `Amalgamation`, `IsFraisse`, `IsUltrahomogeneous`, `IsFraisseLimit`,
`IsUltrahomogeneous.extend_embedding`, `IsFraisseLimit.nonempty_equiv`, and
`age.fg_substructure`, with the hypotheses recorded in `README.md`, Layer 0.  Mathlib has no
existence theorem for Fraïssé limits.

Not at the current pins, and therefore not checked by the sketches: from ComputableModelTheory
(prospective: neither available upstream nor pinned), the classical Fraïssé theorems
(`representativeClass`, `isFraisse_representativeClass`, `FGCofinal`, `ExtensionRich`,
`isFraisseLimit_of_extensionRich`, `SequenceExtension`, `amalgamationRich_of_sequenceExtension`,
`age_directLimit_eq`, `countable_directLimit`, `isFraisseLimit_directLimit`, and the existence
theorem), the factorization of tuples through the age (`exists_factor_tuple_of_age_subset`,
`exists_factor_embedding_of_age_subset`), and orbit isolation and countable prime structures
(`IsolatesTuple`, `IsAtomic`, `isolatesTuple_of_orbit_formula`, `isAtomic_of_orbit_formulas`,
`IsolatesTuple.realize_iff`, `IsolatesTuple.typesWith_eq_singleton`,
`exists_elementaryEmbedding_of_countable_atomic`); from InfinitaryLogic, available upstream (merged
at `cca6949`) and not yet available at our pinned dependency, applied here once the manifest records
that pin and the signatures are checked against it: the rank comparison of the Scott process
(`selfStabilizesCompletely_iff_orbitRank_le`, `bfStabilizationOrdinal_self_eq_iSup_orbitRank`,
`stabilizesAt_of_orbitRank_le`, `rank_le_of_orbitRank_le`, `lift_rank_le_internalScottRank`,
`internalScottRank_le_lift_rank_add_one`).  Their statement shapes and hypotheses are in
`README.md`, Layer 0; where the repinned versions name them differently, those names prevail.

Available upstream (merged in InfinitaryLogic at `cca6949`, its pull request #141), not yet
available at our pinned dependency: applied here once the manifest records that pin and the
signatures are checked against it.  No sketch assumes or `#check`s them before then:
`BoundedFormula.qrank_toLω_lt_omega0` (`Lomega1omega/QuantifierRank`);
`orbit_determined_of_orbitFormula`, `exists_finite_orbit_threshold`,
`orbitRank_lt_omega0_of_orbitFormula`, and `internalScottRank_le_omega0_of_orbitFormulas`
(`Scott/OrbitFormulaThreshold`, under `[L.IsRelational]`, any carrier `M : Type w`, no
countability or nonemptiness); `BoundedFormulaω.realize_comp_of_localAutomorphisms`,
`BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms`, and
`BoundedFormulaω.realize_comp_append_of_localAutomorphisms` (`Lomega1omega/LocalAutomorphism`,
any language and carrier).

**An intended generic interface of InfinitaryLogic (prospective: neither available upstream nor
pinned; a statement still to be proved upstream, a separate library milestone).**  Statement: for a
countable relational language, every analytic set `A` of pairs of structures on `ℕ` containing no
isomorphic pair is uniformly separated at some countable back-and-forth level: there is `α < ω₁`
such that no pair `(M, N) ∈ A` is back-and-forth equivalent at level `α`.  Three checkpoints: (1) a
coded forced back-and-forth tree whose assignment is Borel, whose infinite branches correspond to
isomorphisms, and whose rank is bounded below through back-and-forth equivalence, with the rank
convention stated precisely (no ordinal offset assumed); (2) uniform separation from the boundedness
of analytic families of well-founded trees; (3) two applications: cocountable concentration in one
back-and-forth class at every countable level excludes a perfect isomorphism antichain, and an
invariant relatively Borel subset of a Borel class of structures is saturated under some countable
back-and-forth level, so that under concentration one side is countable in isomorphism
classes.  Dependency direction: basic topology, analytic coding, and well-founded ranks, then
analytic tree boundedness, then uniform back-and-forth separation, then thinness and invariant-Borel
concentration; López–Escobar, invariant separation, and the model-theoretic boundedness route are
excluded from this path by import and proof-dependency guards.  Combined with the cocountable
concentration of the expansion domains (classes in `D_η` agree at back-and-forth level `η`), it
would give thinness without sentence minimality and without López–Escobar.  It does not replace the
working thinness route (`Sentenceω.isThinOnNatModels_of_countable_sentence_splits`, from countable
truth sides), the Gδ/Polish model-code results stay optional, and any improvement it brings is
described as reduced dependencies of the thinness proof, not as a smaller trusted kernel.

`SuggestedInterfaces.lean` checks representative names, so a pin bump that removes one fails
when the sketch is checked (the checks are run by CI).  Coding a `Type w` carrier on `ℕ` needs a
transfer of infinitary isomorphism across universes; do not assume that a statement within a
single universe covers it.

### Dependency pins

The intended repins, made together in `lakefile.toml` and `lake-manifest.json` once the upstream
versions exist:

- **InfinitaryLogic**: from the current revision (`a58f81a`, the merge of its pull request #134) to
  the intended pin `cca6949`, the merge of its pull request #141 on top of `a640bbb` (the merge of
  #140): it contains the rank comparison of the Scott process (#140) and the orbit-formula threshold
  and rank bound and local-automorphism preservation of `README.md`, Layer 0 (#141).  Toolchain and
  Mathlib are the same as at the current pin.  These statements are available upstream (merged in
  InfinitaryLogic at `cca6949`), not yet available at our pinned dependency: applied here once the
  manifest records that pin and the signatures are checked against it.  No sketch assumes or
  `#check`s them before then.  The imports are the narrow modules
  `InfinitaryLogic.Scott.OrbitFormulaThreshold` and
  `InfinitaryLogic.Lomega1omega.LocalAutomorphism`, never `InfinitaryLogic.All`.
- **ComputableModelTheory**: added as a direct dependency, at a version containing its pull
  requests #37 (merged: toolchain `v4.35.0-rc3` and its own repin of InfinitaryLogic, whose
  own pin, `38c4bae`, predates #140), #38 (extension-rich families) and #39 (representative
  classes and extension-rich direct limits), both open, the classical existence theorem, and
  the modules on orbit isolation and countable prime structures and on the factorization of
  tuples through the age.  **The classical existence theorem is prospective: neither available
  upstream nor pinned.**  The theorem itself is classical,
  but its statement and proof in ComputableModelTheory do not yet exist; no statement of this
  roadmap relies on it as pinned until this subsection records a pin containing it.
- **Mathlib and the toolchain** agree across the three: one Lean toolchain (`v4.35.0-rc3` at
  present) and one Mathlib commit (at present the fork commit `346a4bd`, inherited from
  InfinitaryLogic).  The manifest holds one revision of each dependency, so ComputableModelTheory
  must be built against the InfinitaryLogic revision pinned here, and the toolchain check of
  `scripts/check.sh` extends to ComputableModelTheory.

**Prospective dependencies (neither available upstream nor pinned):** the classical existence
theorem, the factorization of tuples through the age, and orbit isolation and countable prime
structures (ComputableModelTheory, where #38 and #39 are open).  No statement of this roadmap relies
on any of them as pinned until this subsection records a pin containing it.  The statements of
InfinitaryLogic's pull request #141 are not in this list: they are available upstream (merged in
InfinitaryLogic at `cca6949`), not yet available at our pinned dependency: applied here once the
manifest records that pin and the signatures are checked against it.

Until then, the statements of the two libraries not at the current pins (marked *available
upstream* or *prospective* elsewhere) are named in prose only
(`README.md`, Layer 0), never `#check`ed in the sketches.

### Applications of library theorems

The development produces the following, and only these, as hypotheses of library theorems:

- **the ages:** for each countable block `η`, the family of finite top-free charts at `λ_η` as
  finite `L^h_λ`-structures, with finite generation, a countable inhabited index, hereditary
  closure, joint embedding, and amalgamation with the literal commuting square (steps 1–2);
- **orbit formulas (first interface):** for every finite tuple `a` of a countable top-free model
  read in the relational stage chart language `L_λ` (the empty tuple and repeated coordinates
  included), a first-order formula of `L_λ` defining exactly its automorphism orbit: the
  containing-chart formula `θ_a(x̄) := ∃ z̄, P_p(z̄) ∧ ⋀_i x_i = z_{ι(i)}` of an actual chart `z̄`
  of type `p` containing `a` at the positions `ι` (`orbitDefinedBy_chartOrbitFormula` in
  `SuggestedCompanions.lean`), from chart homogeneity;
- **local automorphisms (second interface):** for each relevant self-embedding and finite tuple,
  an automorphism agreeing with the self-embedding on the tuple (`COMPANIONS.md`, B2).

Everything after these two interfaces is an application:

| This development proves | The library supplies (InfinitaryLogic, pull request #141) |
| --- | --- |
| The containing-chart formula defines the tuple's orbit | `exists_finite_orbit_threshold` |
| (the same) | `orbitRank_lt_omega0_of_orbitFormula` |
| Every tuple has such an orbit formula | `internalScottRank_le_omega0_of_orbitFormulas` |
| Local agreement of a self-embedding | `realize_embedding_comp_of_localAutomorphisms` |
| The same local agreement, with finite parameters | `realize_comp_append_of_localAutomorphisms` |

These are available upstream (merged in InfinitaryLogic at `cca6949`), not yet available at our
pinned dependency: applied here once the manifest records that pin and the signatures are checked
against it ("Dependency pins").  Three qualifications:

1. Countability belongs to the construction-specific homogeneity proof (the back-and-forth of
   `COMPANIONS.md`, B2, or ultrahomogeneity of the countable limit), not to the generic rank
   theorems: the library's orbit-formula theorems hold on arbitrary carriers, but that does not
   generalize the production of orbit formulas here.
2. The rank conclusion is `≤ ω`: different tuples may need orbit formulas of different finite
   ranks.  There is neither a uniform finite bound nor an equality with the rank of a Scott
   process or with the expansion height.
3. Atomicity and primeness remain separate applications: the orbit formulas feed both the
   first-order route (isolation, atomicity, primeness, from ComputableModelTheory) and the
   infinitary rank route (InfinitaryLogic); the rank route is not derived from atomicity.

Languages: the Fraïssé construction uses the functional hull expansion `L^h_λ`; the orbit-rank
applications use the relational stage chart language `L_λ` (the threshold and rank theorems need
`[L.IsRelational]`).  They are connected by the automorphism correspondence in the one direction
used: every automorphism of the `L^h_λ`-structure is an automorphism of its `L_λ`-reduct.  Chart
homogeneity in `L_λ` follows from ultrahomogeneity of the `L^h_λ`-structure `M`: the points of two
actual occurrences of one type span substructures isomorphic to the finite structure of that
type (step 4, by the factorization of tuples), and the isomorphism between them extends to an
automorphism of `M`.  The converse direction holds for a realization with its definitional
expansion (`HULL_ALGEBRA.md`, §5), and for `M` once the reconstruction roundtrip
(`SEMANTIC_CONTRACT.md`, item 11) identifies its operations with the definable hull operations;
it is not used.  The language of each conclusion is stated with it: orbit formulas, orbit
ranks, and the internal Scott rank are in `L_λ`; preservation of infinitary formulas by
self-embeddings is in the language of the embedding.  The imports are
`InfinitaryLogic.Scott.OrbitFormulaThreshold` and `InfinitaryLogic.Lomega1omega.LocalAutomorphism`,
not `InfinitaryLogic.All`; they bring no López–Escobar or descriptive-set-theoretic machinery.

The development also quotes:

- classical existence (prospective) and `isFraisse_representativeClass`
  (ComputableModelTheory), for the limit (step 3);
- the factorization of tuples through the age (ComputableModelTheory), for the reconstruction
  (steps 4–5);
- `IsUltrahomogeneous.extend_embedding` (Mathlib), for receiving (step 6);
- `isolatesTuple_of_orbit_formula`, `isAtomic_of_orbit_formulas`, and
  `exists_elementaryEmbedding_of_countable_atomic` (ComputableModelTheory), for the atomicity of
  a top-free witness and its primeness among models of its complete first-order theory
  (`COMPANIONS.md`, B3);
- the rank comparison of the Scott process (InfinitaryLogic), for stabilization at `ω` of the
  process of an infinite top-free witness of length `δ` with `ω + 1 < δ`, and its rank at most
  `ω` when it terminates.

These conclusions concern the full stage chart language and the witness's own first-order
theory, not its base reduct and not every model of the infinitary sentence.  The rank of the
process is not identified with the internal rank, nor either with the block index or the
expansion height.  Only the ages are needed for the main theorem; the two interfaces are used by
companion milestone B.  The separate bounded back-and-forth interface ("Upstream building
blocks") is still needed for the proposed simplification of thinness.

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
   and invisible cases.  Status of row 6: the amalgam of two coatom stage types, its literal
   restrictions, and its consistent and bountiful rows are established, and row 6 follows from
   the coatom extension property, with nothing used about the stage; the proof of that property
   in its apex form, the completion of the amalgam, is checkpoints 2.1–2.7.
3. Realizations, literal syntax correspondence, the hull operations with their five facts;
   then steps 1–6 of the top-free witnesses, in order: finite top-free charts, hereditary
   closure and amalgamation and joint embedding (through the plain form of the coatom extension
   property, the first use of row 6), classical existence (prospective),
   reconstruction, consistency and
   covering and top-freeness, and receiving (the first use of row 5).
4. Items 3.2 and 3.3 for rows 1–3: for each row, the extension of the realization by one actual
   occurrence over the literal root and the recovery theorem (by `Correct` and labelled
   evaluation, by LOW, or through the gate), with all its equations on that occurrence and at
   every permitted cutoff; the recovery statement of rows 3 and 4 for every
   restriction-compatible labelling whose private face lies in the prescribed bottom class; the
   first use of row 1, the one-sided donor transfer; the cap-to-model theorem, with the
   modelhood and infinitude of the top-free witnesses (step 7); and the fidelity theorem of
   layer 2, the equivalence of the density sentence with the four-family sentence, whose two
   directions use row 1 and the cap-to-model theorem.
5. Structural continuation (the structural stable candidate); then items 3.2 and 3.3 for row 4
   (the acquisition of its calibrated data, its occurrence, and the evaluation of the stable
   labelling by the recovery statement of checkpoint 4); three terminal comparisons (the first
   uses of rows 2 and 3), stable modelhood (the first use of row 4, with the cap-to-model
   theorem), unique limit expansions, and the terminality of the top-free witnesses with the
   placement of their base classes in the losses (step 7).
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

### Checkpoints 2.1–2.7: the completion of the coatom extension construction

Row 6 is reduced to the coatom extension property at a stage (`README.md`, Layer 3, 3.1, under
"Row 6"): any two legal stage types on the two coatoms of `m + 2` points that agree literally on
their common face (a closed face of both) are the literal faces, labels included, of one legal
stage type on `m + 2` points.  Its apex form asks in addition for a cell of full scope and full
grade carrying the maximum label [Kni26, Corollary 4.3.22], and the plain form follows from it.
Established: the amalgam [Kni26, Definition 4.3.1], with consistent and bountiful rows
[Kni26, Lemma 4.3.2] and literal restrictions to both coatoms, labels included, and not complete
(no cell of full scope); the exact pinned extension, [Kni26, Proposition 4.3.23], and
amalgamation over a common face from the plain form, with nothing used about the stage;
[Kni26, Proposition 4.3.24] for legal schemes, by the bottom labelling.  The cells of the amalgam,
with their rows and labels, are the boundary of its completion.  The stage enters only in the
proof of the property.  That proof, in the apex form, is the completion of the amalgam by cells
of full scope, in seven checkpoints of the mathematics (not a count of pull requests; the larger
ones split):

- **2.1. The seed.**  The finite input of the completion is defined from the amalgam (both
  coatom types, their common face, the amalgamated rows).  A seed is that input together with
  the conditions it must satisfy, each stated explicitly (legality, lifting, literal
  restrictions); the recursion of 2.6 starts from a seed.  That the amalgam of two legal coatom
  types is a seed is proved here, from `Coatom.isConsistent_amalgamType`,
  `Coatom.isBountiful_amalgamType`, and the restriction theorems
  `Coatom.restrictFace_left_amalgamType` and `Coatom.restrictFace_right_amalgamType`.  The apex
  theorem is stated with the conclusion of the recursion of 2.6 as a hypothesis and proved from
  it: the truncation to the stage (below), the apex, and the literal restrictions to both
  coatoms.
- **2.2. Coding.**  The construction works under the library's coding (row entries below `ω²`),
  not under the offset bound of [Kni26, Lemma 2.5.13] (its clause beginning "Indeed": finite part
  at most the grade plus one), which is not correct as stated (`README.md`, Layer 1).
  Acceptance includes an input violating that bound, universe polymorphism, and orderliness of
  the constructed rows derived from consistency rather than assumed.  No later checkpoint of the
  completion (2.3–2.7) begins until this one is settled.  If the weaker coding cannot be carried
  through, identify the first indispensable use of the bound; do not strengthen the legality
  predicate.
- **2.3. Transformation algebra.**  Lawful transformations, normal forms, coded encoders and
  decoders (defined with 2.3); the numerical decoding identities are kept separate from
  lawfulness and from cap preservation.
- **2.4. Lifting and alignment.**  Carrying sections across grade cuts (the restrictions to the
  cells of grade at most a given grade) and source prefixes (defined with 2.4), owner alignment,
  restoration of lower prescriptions (the prescribed labels at the grades below the one being
  built); the cap preserved on every coordinate, and the locality of inherited long rows
  explicit.
- **2.5. The two small arities.**  `m = 0` and `m = 1` as two separately stated constructions on
  their actual rows: arbitrary lawful prescriptions, literal top, the boundary retained, the cap
  preserved on every auxiliary cell.
- **2.6. Recursion on the grade.**  One grade step from the predecessor grade already
  established first, then the general step; lawfulness, consistency, the prefix equations, and
  unrestricted lifting (the last two defined with 2.6) are distinct statements.
- **2.7. The theorem.**  At a stage that is zero or a limit the apex form holds; hence the plain
  form and row 6.  The improvement from limit stages to zero-or-limit stages is a separate lemma,
  with the zero stage handled explicitly.  That truncation to the stage fails at successor stages
  does not prove that the property fails there; that would need its own counterexample.  Whether
  it holds at successor stages is open and not needed.

The completion constructs lawful finite extensions and nothing more.  It imports only Layers
0–1, the stage types, the amalgam, and the section theorem of `README.md`, Layer 3, 3.1 (with
the shared decoding lemma); it does not depend on realizations, receiving, or any later step
toward the main theorem.  At a stage that is zero or a limit, it truncates the completed lawful
labelling to the stage once, as in the proof of [Kni26, Corollary 4.3.22], rather than every
intermediate decoded value, and proves that the truncation keeps both prescribed faces literally
(`CellScheme.Rows.IsLawful.reduce`, `Label.AtStage.reduce_eq`); it reuses the capped-lifting
calculus and the section theorem; it carries no intermediate construction that the proof does
not use.

The bountifulness of the naive completion of [Kni26, Definition 4.3.14] (full-scope cells
indexed by all lawful coded patterns, same-grade rows given by meet heights), the statement of
[Kni26, Lemma 4.3.20], is unproved, not refuted; Definition 4.3.6 needs explicit bindings before
that statement is definite.  Ties do propagate between full-scope cells: a tie of a lawful
section at a value below the cap that is not self-visible at the grade of a full-scope cell
forces equal row entries there, hence the same tie in every lawful section.  Bountifulness
prescribes one face, and there such a tie is already a tie of the prescription, so this
mechanism separates no two cells of the face (the instance of Lemma 4.3.19 separates cells of
different coatoms).  No counterexample is known.  Neither that statement, nor the printed proof
of Lemma 4.3.20, nor the joint lifting of [Kni26, Lemma 4.3.19] is relied on: conclusions 1–3
of Lemma 4.3.19 cannot hold together under the natural readings of efficiency
([Kni26, Definition 4.3.6], whose bindings the text leaves open), since an instance with cap 2
and prescriptions 3 and 4 forces 3 = 4 (`README.md`, Layer 1 and Layer 3, 3.1).  The
construction chosen builds grade by grade over the boundary, in one fixed order of its cells,
chooses the full-scope cell that serves each lift (defined with 2.6) before extending on the
other coatom, and tops out in a single apex cell.

## Companion boundaries

Companion topics: definable domain/logical cuts with strict loss-rank lower bounds; canonical
top-free classes converging sentencewise; local automorphisms of self-embeddings; and the
arbitrary-carrier Scott/`T∞` theory dichotomy.  The joint embedding and amalgamation properties
of finite top-free charts are step 2 of the top-free witnesses and
belong to the core.  These do not assert strong AP, a proper self-embedding, uncountable
categoricity, Scott-rank equality, or existence of a model of all of `T∞`.  The main theorem is
proved without them; if any is added, give it a separate definite completion criterion.  Direct
limits of structures and the classical existence theorem (prospective) belong
to the two libraries, not to
the finite constructions of layer 3.
[`COMPANIONS.md`](COMPANIONS.md) gives these topics and the full-chart orbit theory below such
criteria, as three milestones (A: filtration and infinitary theory; B: top-free chart homogeneity
and its consequences; C: a geometric obstruction).

### Full-chart orbit theory: a companion checkpoint

The targets of this checkpoint are milestones B and C of [`COMPANIONS.md`](COMPANIONS.md),
which states each with its hypotheses, upstream ingredients, instantiation, regressions, and
non-claims, and gives the companion sketch [`SuggestedCompanions.lean`](SuggestedCompanions.lean).
In summary: in the full stage chart language (not the base reduct), a countable nonempty top-free
realization with exact consistency, covering, and finite-cut receiving has automorphism orbits
defined by explicit first-order chart formulas, hence isolated complete types, atomicity,
internal Scott rank at most `ω` in the library's convention, and primeness among models of its
complete theory in arbitrary universes.  The development proves the orbit formulas and the
local automorphism property; the isolation, atomicity, primeness, rank, and preservation
theorems are quoted from the two libraries ("Applications of library theorems" above).
Separately, consistency and covering alone bound every set of absolute indiscernibles (a set
whose permutations all extend to automorphisms) by two points, a theorem kept below receiving by
an import guard.  Milestone A of
`COMPANIONS.md` treats the definable cuts, witness convergence, and the Scott/`T∞` dichotomy
listed above.

**Completion criterion.**  This companion checkpoint is complete when milestones B and C of
`COMPANIONS.md` meet their completion criteria.  It is not a core checkpoint, and the main
theorem does not depend on it.
