# Implementation roadmap: spine, layers, discipline, checkpoints

This document sharpens [`README.md`](README.md) into an implementation order with explicit semantic
guards and acceptance checkpoints.  Where the two differ, this one prevails; in particular the upper
bound of the expansion-domain route below goes through Scott separation on the persistent core, and
thinness through the library's thinness theorem for countable sentence splits, not through Morley's
dichotomy.  `README.md` remains the mathematical roadmap, `SEMANTIC_CONTRACT.md` fixes the meanings
to preserve, and [`Suggested.lean`](Suggested.lean) /
[`SuggestedInterfaces.lean`](SuggestedInterfaces.lean) give selected, nonexhaustive Lean statements.
Do not turn their abstract structure fields into substitutes for the constructions.

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
| Layer 6, Summit 6: the upper and lower bounds | 5 and the spine | 6 |
| (none; companions) | milestones A–C (`COMPANIONS.md`) | not core checkpoints |
| Reduction to full presentations | the full-presentation route (below) | its own order (below) |
| Manuscript correspondence (required) | the concordance (below) | its own criteria (below) |

The general results of Layer 0 are used in layers 1 (lifting), 2 (finite hulls), 3 (the
classical limit: Fraïssé existence, ultrahomogeneous extension, factorization of tuples through
the age), 4 (directed limits, back-and-forth, subsingleton covers), and 5 (countable losses),
each at the checkpoint of its first application.  Layer 2 of `README.md` reaches
checkpoint 3 and, with the fidelity theorem, checkpoint 4.  Layer 3 of `README.md` is spread over
four checkpoints: 2 (item 3.1, the construction of every statement of its table with its section
theorem), 3 (the first uses of (R5) and (R6): the amalgamation of top-free charts and receiving
in the classical limit),
4 (items 3.2 and 3.3 for (R1)–(R3), the recovery statement of (R3) and (R4) for every
restriction-compatible labelling, the first use of (R1), and the cap-to-model theorem), and 5
(items 3.2 and 3.3 for (R4) after the structural candidate, and the first uses of (R2)–(R4)).
Checkpoint 2 is subdivided: the completion of the coatom extension construction (R6) is
checkpoints 2.1–2.7 (below), the seven checkpoints of `README.md`, Layer 3, 3.1, under "(R6)".
The construction of the top-free witnesses, the finite age and its classical limit, is the
section of that name in `README.md`, after Layer 3; its seven steps, with their acceptance
criteria and checkpoints, are under "The top-free witnesses: milestone order and acceptance"
below.  The companion milestones are summarized under "Companion boundaries".

## Environment

Lean `v4.35.0-rc3`; InfinitaryLogic and ComputableModelTheory at the revisions pinned in
`lakefile.toml` (`e460cb6` and `a1fe761`); Mathlib inherited from InfinitaryLogic's manifest.
Nothing else is imported.
Search the pinned libraries first and delete any local lemma that duplicates one already
upstream.

## Scope and completion

Construct an explicitly countable relational language and an `L_{ω₁,ω}` sentence whose countable
models have exactly `ℵ₁` isomorphism classes and no perfect isomorphism antichain.  The sentence is
the density sentence of layer 2 (the structural clauses and the one-point capped-extension clause).
State both the natural-number-code and the all-countable-carrier formulations, with the reduction to
`ℕ` explicit (no finite models, so every countable model is isomorphic to a coded model on `ℕ`).
Both formulations are stated in the library, `HasThinAlephOneSpectrum` and
`HasThinAlephOneSpectrumOnCountableCarriers` (with `codedClassEquiv` between the classes of codes
and the classes on all countable carriers, `MainTheorem/AllCarriers`), and their compositions are
compiled conditionally (checkpoint 6).  This is not a first-order Vaught result and is not a
comparison with the continuum.

The core is complete only after every finite construction, realization over a root, recovery of
donor labels, syntax correspondence, the equivalence of the density sentence with the four-family
sentence (layer 2), the top-free witness at every countable block (obtained by finite-age
reconstruction from a classical limit, meeting its acceptance criterion), and statement of the main
theorem below is proved.  Completion is not limited to the signatures in the sketches.  The
manuscript correspondence ("Manuscript concordance" below) is required for the claim that the
development matches [Kni26] and [AFK26], not for the main theorem, and has its own completion
criteria.  Each definition needs its usable basic API: projections, extensionality,
identity/composition, restriction, transport, and representative examples.

Under-specified extensions are not part of this roadmap.  Separate companion roadmaps may cover the
definability consequences of the hull operations and hull cardinality (`HULL_ALGEBRA.md`, §4; the
operations themselves are core, layer 2), model-code topology, `T∞` (the set of sentences true in
all but countably many classes) and its agreement filtration, effective syntax, and uncountable
models; `COMPANIONS.md` organizes the filtration and `T∞`, chart homogeneity, and a geometric
obstruction as three optional milestones.  They are not prerequisites of this core.

## The mathematical spine

Let `Q` be countable base models modulo isomorphism, with actual satisfaction `truth φ q`.
At block `λξ = ω + ω·ξ`, let `Dξ` mean existence of a model expansion.  The construction
establishes:

1. `D0 = Q`, decreasingness, and continuity at countable nonzero limits.
2. Countable successor losses, by fixed-stage terminal comparison.
3. Cofinally nonempty losses, witnessed by a separate construction of top-free terminal models.
4. Agreement in `Dη` on sentences of quantifier rank at most `η`.
5. Scott separation of distinct classes and faithful satisfaction on model codes.

Countable-loss induction gives countable complements.  Scott separation makes the persistent core
`⋂_η Dη` subsingleton.  Its complement is covered by `ℵ₁` many countable exceptions, so `|Q| ≤ ℵ₁`;
disjoint cofinal losses give the reverse inequality.  With a Scott sentence for each class, the
agreement in `Dη` and the cofinally nonempty losses (hypotheses of this count, not its conclusions)
also make the persistent core empty, by eventual departure (`COMPANIONS.md`, "Further companion
results", terminal refinement; compiled conditionally, `ExpansionDomains.core_eq_empty`,
`MainTheorem/LastStage`); the count uses only the subsingleton form, and departure is not an
input to it.  This counting argument (countable complements and Scott separation give at most `ℵ₁`
classes) belongs to the setting of minimal counterexamples of Harnik–Makkai [HM77]; see Larson
[Lar14], Remark 10.9, and its discussion of minimal counterexamples.  Separately, homogeneous
domains give one countable truth side for each sentence, and the library's thinness theorem
`Sentenceω.isThinOnNatModels_of_countable_sentence_splits` (`Descriptive/SentenceSplits`) rules out
a perfect antichain.  Neither Morley's dichotomy nor eventual stopping belongs in this proof.  There
is no measurable structure or measurable choice of representatives on `Q`.

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
shared decoding lemma, to the growth construction of (R3) and (R4) and to the LOW construction of
(R2) (Layer 3 of `README.md`, item 3.1).  Avoid a general categorical formalism before these
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
consequences, and the equality (1) for infinite sets stay downstream.  Separately, layer 2 proves
that geometric hull closure is contained in definable closure in the full stage chart language,
by the unique-coordinate formulas, with no equality with `dcl` or `acl` asserted.  A description
of finite tuples by hull, hull chart type, and coordinate map (canonical up to reindexing; empty
and repeated tuples included) is stated only if a use for it is identified.

Density quantifies `∀ root, ∀ donor, ∀ cutoff, ∃ extension` on the fixed donor scheme.  An
all-finite-extension presentation of receiving (donors with any finite number of new points),
equivalent to the one-point presentation, keeps the same quantifier order.  The many-point form
implies the one-point form at once.  The converse proceeds one point at a time along a chain of
visible faces of the donor's plan at an auxiliary cap.  The bounded-observation lifting of layer 1
is available at caps self-visible at the target grade, not at every permitted cutoff, so for a
requested cutoff `c` at stage `α` the chain is run at an auxiliary ordinal `c'` chosen strictly
between the requested cutoff and the stage, `c < c' < α` (a permitted cutoff, so never the formal
top), self-visible at the donor's arity `k`.  Such a `c'` is given by
`Label.exists_lt_lt_isSelfVisible (hβ : Order.IsSuccPrelimit β) (ho : o < β) (k : ℕ) :
∃ c : Ordinal, o < c ∧ c < β ∧ IsSelfVisible k (c : Label)` (`Label/Visibility`, namespace `Label`),
applied with `o := c`, with witness `c' = c + (k + 1)`.  Its hypotheses hold here only because (i)
the requested cutoff `c` is an ordinal below the stage (it is a permitted cutoff,
`isPermittedCutoff_coe`), and (ii) the stage is zero or a limit (`Order.IsSuccPrelimit`).  Each step
takes a lawful coface of the actual type with the donor's observation at `c'`; this stronger
agreement at `c'` is preserved throughout the finite chain of extensions, after which one passes
down to `c` by capping.  The stage hypothesis (ii) stays in the statement.  At stage zero there are
no permitted cutoffs, so that case is vacuous; it is not a source of a witness.  No generalization
to successor stages follows from this argument.  The presentation is stated first at stage `ω` and
at the stages `λ_ξ` (all limits), under the countability hypotheses the argument needs.
Different cutoffs may use different points.  Prove both satisfaction directions, the
realization/structure round trips, isomorphism preservation and reflection, and no finite
models.  The density sentence is the preferred presentation.  Its equivalence with the
four-family sentence (the structural clauses together with the four extension families of
`SEMANTIC_CONTRACT.md`, item 5, and [Kni26, Definition 3.2.1], clause 4) is a required fidelity
theorem and part of the completion criterion.  Its direction from the four-family sentence to the
density sentence still uses the finite-cut receiving statement (R1) of the table of
Layer 3 of `README.md`, which therefore remains a prerequisite of completion.  Its direction
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
long-row locality, the section theorem, display, gate, twins of the gate, and gate equation, the
coatom extension construction, pinned and exact pinned extension, restriction-compatible labelling,
`Correct`, LOW, and the cap-to-model theorem) and consists of four items, built in this order:

1. **Statements of the finite extension constructions, and the section theorem.**  For each: input
   data, compatibility conditions, the constructed finite object (a legal scheme with its
   embeddings and, where the statement uses one, a display, as data), and its literal equations,
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
   original rows' lawfulness along the exact base table; it uses no bottom reflection of the
   decoder.
   The growth construction of (R3) and (R4) and the LOW construction of (R2) are both required
   applications.  The two-witness splice is also proved here: for a top-labelled cell `Σ` of
   grade `J ≤ K` below a top-witness cell `Θ`, a witness from `E(Σ)` to the labels below `Σ`
   and a witness from `E(Σ)` to the row of `Θ` capped at its entry at `Σ` combine into a
   witness from `E(Σ)` to the labels where they are below `α` and, where they are top, to the
   band map of the capped row with a base (zero or a limit) that the capped row does not fall
   below there.  It replaces the transitivity step in the proof of
   [Kni26, Lemma 5.3.5] for the rows other than the top-witness row.  (R6) is reduced to the
   coatom extension property at a stage, whose proof, in its apex form, is the completion of the
   amalgam of [Kni26, Definition 4.3.1] by cells of full scope (checkpoints 2.1–2.7 below).
2. **One occurrence, then labelled evaluation.**  The realization extends by **one actual
   occurrence** of the constructed scheme over the private context, by a model clause that depends
   on the statement: for (R1), the bottom-pattern clause with the display, read on the whole graded
   index of the gate (the gate not bottom, its twins bottom; gate recovery reads this pattern,
   `README.md`, Layer 3, 3.3, recovery item 1); for (R2), (R1) itself, with the LOW display as
   donor; for (R3) and (R4), generalized saturation, with no display.
   Root, private context, donor values, and gate equation all concern that occurrence.  For
   (R3) and (R4) the recovery statement is proved for every restriction-compatible labelling
   whose private face lies in the prescribed bottom class, then applied to the actual labels
   (R3) or to the stable labelling (R4).  That statement uses no stable labelling; the
   acquisition of the calibrated data of (R4), its occurrence, and its evaluation need the
   structural candidate and come at checkpoint 5.  (R3) and (R4) share the constructed scheme
   and the recovery statement; their acquired data, the labelling evaluated, and their
   existence hypotheses stay separate.
3. **`Correct`, LOW, and the recovery statements.**  `Correct` consists of three clauses capped at
   the value of the private cap, which can be top: bottom, reference with its offset replacement,
   and a marker lower bound; it has no gate.  LOW is gate-free: its forcing puts every donor-top
   field above the cutoff and the private gap value once the cutoff exceeds the non-top donor
   maximum, and its recovery returns the donor exactly, tops included, from agreement with the
   display below a cutoff above the rounded non-top donor maximum.  Agreement below a cutoff, exact
   recovery of the labels that are not top (bottom and proper, from LOW or from the bottom and
   reference clauses of `Correct`), literal-top recovery (from LOW, or from `Correct` when the
   private cap is top), and above-threshold inequalities are different conclusions.  Agreement below
   one permitted cutoff cannot distinguish a proper label above the cutoff from top.  Each recovery
   lemma lists the observations it reads and does not require recovery of the whole type of the
   constructed occurrence.  Cutoff observations, stage reductions, and exact extension within a
   specified age are kept apart (the density boundary, `README.md`, Layer 3, 3.3): cutoff-by-cutoff
   receiving gives exact projected receiving only after projected-donor lifting over the particular
   actual root being extended is proved, a statement to be proved in each application (for every
   actual root and every projected donor over it, the lift depending on both), and coherence of the
   projections is not accepted as a proof of it.
4. **Extension statements and first uses** (the table of `README.md`, Layer 3): finite-cut
   receiving, first used by the one-sided donor transfer (and by the four-family-to-density
   direction of layer 2); exact residual receiving, by the residual comparison; exact
   hollow-growth receiving, by the hollow comparison; capped receiving for the stable candidate,
   by stable modelhood; the top-free pinned extension, by receiving in the classical limit
   (step 6 below); the exact pinned extension, through the plain form of the coatom extension
   property, by the amalgamation of top-free charts (step 2 below).  Each statement records its
   exact hypotheses, its conclusion, and its import boundary.  (R1)–(R4) conclude on one
   occurrence over the literal root and have recovery theorems; (R5) and (R6) are extension
   statements about charts, without an occurrence or a recovery theorem.  The positive-length
   root restrictions and the empty-root base cases are explicit, and the cap-to-model theorem is
   stated with the table.

The countable models of the main theorem are the top-free witnesses, constructed by the finite
age and its classical limit (seven steps, under "The top-free witnesses: milestone order and
acceptance" below), not by a chain construction.  Derive the partial realization of a finite
chart from the chart; do not store synchronized copies.  A supported invisible face is not an
unsupported tuple.

First applications: the amalgamation of top-free charts (step 2, from the plain form of the coatom
extension property and capping) and receiving in the classical limit (step 6, (R5) over a whole
chart, that is the capped coface, which needs no coatom extension).  The modules of the finite
extension constructions import neither the classical limit nor the chain construction.  Direct
limits of structures and the classical existence theorem (available at the pin) belong to the two
libraries: they replace no finite extension construction and no decoding or recovery statement.

### 4. Stable continuation and terminal comparison

Build rooted covers and their monotone natural offsets.  The completed value lives in `ℕ∞`,
decoded back to labels: infinity decodes to formal top, not `α + ω`.  Keep consistency-only
stable uniqueness/naturality, consistency-plus-covering stable lawfulness, and
receiving/modelhood as different theorem layers.
Consistency and covering give the order law and locality of the stable labelling
(`Realization.orderly_stableSection`, `Realization.locality_stableSection`) and availability when
no type has twins, two cells labelled `⊤` at one graded index
(`Realization.isStablyLawful_of_injOn_gradedIndex`); with legal types, availability holds also at
twins (`Realization.availability_stableSection_of_hasLegalTypes`, through
`StageType.exists_forcesThreshold_twin_face`), so every exactly consistent covering realization
with legal types at a block stage is stably lawful (`Realization.isStablyLawful_of_hasLegalTypes`),
and in particular every model at a block stage (`Realization.IsModel.isStablyLawful`); these are
compiled in this repository (theorem named). Two hypotheses on single stage types that would
give availability at twins through every lift are refuted (negative special cases): synchronizing
cofaces, in three forms
(`Continuation.CandidateCounterexamples.not_unrestrictedSynchronizingCofaces`,
`Continuation.CandidateCounterexamples.not_synchronizingCofaces_blockStage`,
`Continuation.CandidateCounterexamples.not_synchronizingCofacesOnLifts`), and twin ordering
(`Continuation.CandidateCounterexamples.not_twinOrdering_blockStage`). On the type that refutes twin
ordering every lift gives the cell of smaller scope the label of the larger twin, and both orders of
the twins occur; the transfer that holds happens inside the forcing cover, from a forced level.

Construct the stable realization and literal reduct before proving modelhood.  Normalize any
genuine expansion pointwise to the structural candidate; handle undefined tuples using the
literal reduct.  Derive modelhood separately by cap receiving (statement (R4) of the table of
Layer 3 of `README.md`) and the cap-to-model theorem of checkpoint 4.  The calibrated data of
(R4), its occurrence, and the evaluation of the stable labelling by the recovery statement of
checkpoint 4 are built here, after the structural candidate.  Keep positive-root requirements
and the empty-root base case explicit.

Use selected-chart rooted back-and-forth, not a second fair-chain comparison.  The coreless
comparisons are instances of one exact-age comparison theorem (same exact age, exact receiving);
the rigid-core case is treated in the language naming the core by constants, where the analogues
of B2 and B3.1–B3.2, B3.4 of companion milestone B are stated, from the exact receiving over roots
containing the core (not from top-freeness); the rank bound B3.3 needs a relational language, so
for it the core is named by one unary relation per core point.  Explicit exact-age Scott
sentences, `Π^in_2` after naming the core and `Σ^in_3` after existentially quantifying the
constants away, are a syntactic-complexity target, distinct from the internal Scott-rank bound
`≤ ω`: not derived from it, and no implication between them is asserted.  The chosen root
must belong to the extendible family; atomic agreement alone does not suffice.  Count terminal
classes by an overlapping countable family of singleton conditions: specified rigid-core type,
coreless eventual top grade, and hollow growth.  Do not construct a complete profile invariant.
Eventual top grade zero is the rigid-core case: the empty tuple is then a rigid core
(`TerminalProperty`, `Realization.HasTerminalProperty`).  Preserve the original no-anchor predicate
(the meaning of "hollow", `SEMANTIC_CONTRACT.md`, item 8); stable-label fixedness is a
characterization under stated hypotheses.  The compiled statements of output 3, the terminal count,
and (R3) are presently formulated with cover-hollowness (`Realization.IsCoverHollow`), and (R4)
is declared (`StableCappedReceiving`, assuming that the model is not cover-hollow) and is not
proved; cover-hollowness is a
separate named predicate whose stable-label fixedness holds for every realization at a block stage,
with no hypothesis (`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`); the equivalence of
cover-hollowness with the original no-anchor predicate is still to be proved.

**The finite lifting statements, organized around the attained least lift** (`README.md`, Layer 3,
3.1, "The attained least lift" and "Least, not unique"; Layer 4, "Status", outputs 2 and 3 and the
structural successors; "Endpoints and shared foundations", "The finite lifting boundary").  These
are roadmap targets related to items 1, 4, and 5 of `README.md`, "Manuscript correspondence
(required)", not rows of the concordance: no statement of [Kni26] or [AFK26] is identified with
them.  Each statement with its hypotheses and marker.  Here `β` is the lower stage, `q` a stage type
at `β`, and a lift of `q` a stage type at `β + ω` whose reduction to `β` is `q` (same scheme and
rows).

1. *The attained least lift* (prospective).  Hypotheses: `β` a limit stage, the stage hypothesis
   under which the statement is formulated, and a **legal** stage type `q` at `β`
   (`StageType.IsLegal`), an explicit hypothesis: the availability law is existential, so the
   cell-wise minima of the lifts of an arbitrary stage type need not be attained by one lawful
   labelling.  Any further hypothesis its proof needs is recorded with it.  Conclusion: a lift `q₀`
   of `q` with `q₀.label d ≤ Q.label d` for every lift `Q` of `q` and every cell `d`, one lawful
   labelling attaining every minimum at once.  The threshold forced by a rooted cover is identified
   by testing against this one lift, not by combining lifts chosen separately at the cells.
   Compiled in this repository (theorem named), cell by cell: each minimum is attained by some lift
   (`StageType.exists_lift_label_eq_ofOffset`, for `β` zero or a limit).  The statement validates no
   ordering of twins fixed in advance: the twin-ordering hypothesis is refuted
   (`Continuation.CandidateCounterexamples.not_twinOrdering_blockStage`, compiled in this repository
   (theorem named)).
2. *The limit-stage monotonicity* (prospective in its derived form; the monotonicity of thresholds
   along extensions of rooted covers).  Hypotheses: those of 1.  Per-cover form (Layers 1–3,
   `Stage/`): along extensions of rooted covers the least lifts increase on the face of the root.
   Supremum form (Layer 4, `Continuation/Normalization`): the stable offset is the supremum of the
   offsets of the least lifts, and the stable label its decoding (`Label.ofOffset`).  Compiled in
   this repository (theorem named), with provisional offsets in place of least lifts:
   `StageType.ForcesThreshold.trans_face` and `StageType.provisionalOffset_le_trans_face`, which are
   themselves the forms for an arbitrary second stage (only `β` zero or a limit is assumed) and are
   kept as separate statements; the supremum through the definitions `Realization.stableOffset` and
   `Realization.stableLabel`.
3. *The threshold characterization* (prospective in its derived form).  Hypotheses: those of 1, a
   rooted cover `(q, f)` of a root `p`, and a cell `d` labelled `⊤` in `p`.  Per-cover form (Layers
   1–3): `(q, f)` forces `n` at `d` exactly when every lift is at least `β + n` there (the
   definition), exactly when the least lift is.  Supremum form (Layer 4): `n` is at most the stable
   offset exactly when the least lift of some rooted cover is at least `β + n` at `d`.  Compiled in
   this repository (theorem named), with forcing in place of the least lift:
   `StageType.ForcesThreshold` (`Stage/Threshold`) and `Realization.natCast_le_stableOffset_iff`
   (`Continuation/Normalization`).
4. *Structural successor leastness* (the "least" property prospective).  Hypotheses: `R` an exactly
   consistent covering realization at `λ_ξ`; a coherent next-block assignment (a
   restriction-compatible labelling of `R` whose values are lifts to `λ_{ξ+1}`).  Conclusion: the
   stable section is at most the assignment at every cell.  Compiled in this repository (theorem
   named; `Realization.stableCandidate` is defined in this repository): the candidate with its
   literal reduct, legal types, covering, and exact consistency (`Continuation/Candidate`);
   soundness (`Realization.Covers.le_label_of_forcesThreshold`), the domination for an assignment
   that is an exactly consistent realization reducing to `R`; and, conditional on finite-extension
   receiving and `ForcingDonors`, the equality of such a realization with the candidate
   (`Realization.label_eq_stableLabel`).  Attainment (the candidate is lawful) from exact
   consistency, covering, and legal types, with no receiving and no further clause of modelhood
   (`Realization.isStablyLawful_of_hasLegalTypes`, `Realization.IsModel.isStablyLawful`): compiled
   in this repository (theorem named).
5. *Finite nonuniqueness* (prospective; a caution).  Hypotheses: `β` zero or a limit and `q` at `β`.
   Conclusions: literal weakening, `q.castLE`, is the greatest lift (its ingredients
   `StageType.reduce_castLE` and `StageType.reduce_self` are compiled in this repository (theorem
   named)); the lifts of `q` form a singleton exactly when `q.IsTopFree` (the lift capped at
   `β + K`, `StageType.capLift`, defined in this repository, a lift by `StageType.capLift_reduce`,
   compiled in this repository (theorem named)); so the least lift, where it exists, and the
   greatest agree exactly when `q` is top-free.  These belong to Layers 1–3 (`Stage/`).  A pointwise
   minimum of lifts need not be lawful (the type of
   `Continuation.CandidateCounterexamples.not_twinOrdering_blockStage`; informal, not compiled as a
   separate statement; [Kni26, Lemma 2.5.11] is not relied on, `README.md`, Layer 1); this negative
   special case is to be compiled in `Continuation/CandidateCounterexamples` (Layer 4), on the
   five-cell scheme defined there (`fiveCells`, `fiveCellRows`, `fiveCellScheme`).
   "Least lift" is never replaced by "unique lift".
6. *The separation of leastness from modelhood.*  Statements 1–5, 8, and 9 do not make the candidate
   a model: receiving, (R1)–(R4), stays its own statement; (R4) (`StableCappedReceiving`) and the
   coface instances at `λ_{ξ+1}` (`StageType.HasNonemptyCofaceInstances`), both defined in this
   repository and still to be proved, remain the content of output 3, compiled from them as
   `ContinuationCriterion.of_stableCappedReceiving` (compiled in this repository (theorem named)).
   Exact lifting over a separately prescribed higher root (`Seed.TwoFaceLift`, defined in this
   repository, and `StageType.HasApexCoatomExtensions`) still needs its own proof; leastness alone
   does not give it.  `ContinuationCriterion` (`Continuation/Classification`) stays a hypothesis of
   the count, still to be proved.
7. *The dependency order.*  (i) The finite row algebra and the arithmetic of visibility; (ii) the
   lawful provisional lift and the finite recovery of labels in a band; (iii) the attained finite
   leastness (statement 1) and the gap between the least and the greatest lift (statement 5); (iv)
   the consequences at limit stages and the observations on rooted covers: the per-cover forms of 2
   and 3; (v) the stable candidate and its leastness: the supremum forms of 2 and 3, and statements
   4 and 8; (vi) continuation and terminal classification, separately: statements 6 and 9 and output
   3.  Statement 1 depends on (i) and (ii) only, not on the limit-stage monotonicity.  Steps
   (i)–(iv), with the composition of capped lifts (`CellScheme.Rows.CappedLift.trans`), belong to
   Layers 1–3, whose modules import no module of `Continuation/` or `Expansion/`; steps (v) and (vi)
   and the negative special case of statement 5 belong to Layer 4 and import them.  The stage
   hypothesis of 1 is a hypothesis of every statement derived from it.
8. *The least and the greatest structural successor* (prospective; Layer 4).  Hypotheses: `R` a
   consistent realization at `λ_ξ`, and, for the least, covering as well; no countability and no
   nonempty carrier.  A structural successor of `R` is a consistent realization at `λ_{ξ+1}` whose
   reduct to `λ_ξ` is `R`.  Conclusions: literal weakening (`StageType.castLE` on each type, `⊤`
   kept) is a structural successor and the greatest, from consistency alone; the stable candidate
   (`Realization.stableCandidate`, defined in this repository), where it is lawful, is the least;
   each is attained by one coherent realization, least (greatest) at every coordinate at once, and
   every structural successor lies between them.  Not claimed: the lawfulness of a labelling between
   them, or closure under pointwise minima.  The rows stay fixed: stage projection changes the
   labels only, and any other representation of the rows is used only through a transport checked
   to preserve lawfulness, cells, faces, and reduction.
9. *Cover-hollowness as the equality of the two* (prospective; Layer 4).  Hypotheses: `R` a model at
   `λ_ξ`.  Conclusions: the least and the greatest structural successor of `R` are equal exactly
   when `R.IsCoverHollow`.  For cover-hollow `R` the candidate is lawful
   (`Realization.isStablyLawful_of_isCoverHollow`) and is literal weakening
   (`Realization.stableCandidate_eval_of_isCoverHollow`), both compiled in this repository (theorem
   named).  Conversely, a model is stably lawful (`Realization.IsModel.isStablyLawful`, compiled in
   this repository (theorem named)), so its candidate is defined, and it is literal weakening only
   if every cell labelled the formal top has the formal top as its stable label, which is
   cover-hollowness (`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`, compiled in this
   repository (theorem named)).  The equivalence of this equality with cover-hollowness holds for
   every stably lawful `R`; models are taken because there the candidate is a structural
   successor.  Then the structural successors form a subsingleton, and each is the stable
   candidate.  Not a continuation theorem: a structural successor need not be a model, and the
   uniqueness supplies no expansion; for a model that is not cover-hollow the two differ, with no
   conflict with the uniqueness of model expansions.  Stated for models only, with
   cover-hollowness, not hollowness in the sense of `SEMANTIC_CONTRACT.md`, item 8.
10. *Complementary global routes* (`README.md`, the section on the top-free witnesses,
    "Complementary global routes").  Separate statements with their own hypotheses, none derived
    from statements 1–9: classical Fraïssé existence for terminal examples at one level (the
    top-free witnesses); Scott isolation with countable-limit existence for maximal presentations of
    a prescribed base (concordance rows 40 and 31–36); terminal presentations for countability;
    global termination as a companion route (`COMPANIONS.md`).

**Completion criteria of the finite lifting statements.**  Each statement above is complete on its
own criterion, with its stage hypothesis stated, and none is complete because another is.

1. *The attained least lift* (statement 1): the statement compiled for legal stage types at a limit
   stage, with the lifts at the next block stage on the unchanged scheme and rows, and the literal
   reduct equation (the reduction of `q₀` to `β` is `q`); the per-cover forms of 2 and 3 derived
   from it in Layers 1–3 and the supremum forms in Layer 4, each with that stage hypothesis; the
   forms for an arbitrary second stage kept; no pointwise minimum of chosen lifts used.
2. *Structural successor leastness* (statement 4): the "least" property compiled for coherent
   next-block assignments; attainment from exact consistency, covering, and legal types, with no
   receiving and no further clause of modelhood; the case of an assignment that is a realization
   reducing to `R` derived from soundness.
3. *Least, not unique* (statement 5): literal weakening the greatest lift; the singleton criterion
   for `β` zero or a limit; the pointwise minimum on the twin-ordering type compiled as a negative
   special case in `Continuation/`.
4. *The separation of leastness from modelhood* (statement 6): a separate continuation proof for
   modelhood, output 3 compiled from (R4) and the coface instances at the next block, with the
   lawfulness, leastness, and uniqueness of the candidate not used in place of either.
5. *The structural successors* (statements 8 and 9): statement 8's conclusions compiled (literal
   weakening a structural successor and the greatest; the candidate, where lawful, the least; every
   structural successor between them); literal root and reduct equations for lifting, the reduct of
   each structural successor equal to `R` as an equation of realizations, literal weakening included
   (`StageType.reduce_castLE` with `StageType.reduce_self` on each type), and the face of its value
   at a rooted cover along the root equal to its value at the root, literally; the equivalence of 9
   compiled for models only.
6. *Complementary global routes* (statement 10): for classical reconstruction, a round trip on the
   given carrier (the literal round trip of the acceptance criterion of finite-age reconstruction,
   `README.md`, on the carrier of the limit itself); each route compiled as its own theorem, its
   hypotheses listed, none taking a statement 1–9 as input.

### 5. Unique expansions, domains, and the main theorem

Prove unique partial expansions and countable-limit existence.  Coherence of a family of lower
expansions is derived from uniqueness, not a hidden hypothesis.  Map successor losses to terminal
classes.  Take the top-free witnesses (the section on them) at each countable block; expansion
uniqueness, with same-carrier transport, is what places their **base classes** in the corresponding
successor differences: together they exclude another, higher expansion of the base reduct.  Eventual
stopping is not an input: conditions 1–4 give it for every class outside the persistent core, which
has at most one class, and no statement here assumes it for every model.

Sections 4 and 5 together are **higher-stage reconstruction** (`README.md`, head of Layer 4, which
lists its five outputs, each a statement still to be proved): the structural candidate, its
normalization, and the separate modelhood criterion (section 4); the partial-expansion API, namely
reduction, uniqueness, coherence, and transport under isomorphism; and limit existence, with
coherence derived from uniqueness (this section).  Outputs 1–3 and 5, and the uniqueness, coherence,
and transport under isomorphism of output 4, belong to checkpoint 5; the reduction of models in
output 4 is layer 2 (checkpoint 3).  A proof that the candidate is uniquely determined is never
accepted as a proof that it exists as a model.  Higher-stage reconstruction is distinct from
finite-age reconstruction, the construction of the top-free witnesses below, whose acceptance
criterion is `SEMANTIC_CONTRACT.md`, item 11.

Prove the one-sided finite-donor transfer first, using only target consistency and finite-cut
receiving (R1).  Symmetrize for back-and-forth: one block buys one level, with no extra `ω`
factor.  Handle repeated coordinates and empty tuples.  Apply the sentence-agreement argument once,
keeping the cardinality conclusion separate from the descriptive thinness conclusion.  In
`SuggestedInterfaces.lean`, `SentenceAgreementDomains` is a structure (countable-stage domains
with countable complements, eventual constancy of each sentence on them, and separation of
distinct classes by a sentence) with two proved lemmas: `persistent_subsingleton` (the
persistent core has at most one element) and `countable_truth_side`.  The `ℵ₁` step (the
persistent core is a subsingleton and the remaining classes lie in `ℵ₁ · ℵ₀` many exceptions,
so `|Q| ≤ ℵ₁`) is a target still to be proved, not a lemma of the sketch.

The comparison is to be proved in its back-and-forth form (`README.md`, "Condition 3 from
back-and-forth", a theorem to prove): any two members of `D_η` are `BFEquiv η` on the empty tuple.
The one-block transfer gives the forth and back clauses of InfinitaryLogic's graded-matching
theorem `bfEquiv_of_gradedMatching` (at the pin, signatures checked; with the match (ii) of
`README.md`, layer 0, the height guard and the selector inside the relation), applied with height
`η`; on abstract hypotheses for the expansions, charts, and covers, this passage is
`ExpansionMatchData.bfEquiv_of_expansionMatch`, compiled in this repository (theorem named).  Its
initial match is a separate statement, not a
consequence of the extension laws: the empty set is closed in both expansions (existence), and the
two empty charts have the same type at `λ_η` (compatibility, by `StageType.eq_of_zero`).  Sentence
agreement at quantifier rank at most `η` is then the corollary `BFEquiv_implies_agreeQR` (available
at the pin, signatures checked), not a separate induction on sentences.  On this route thinness also
has the scatteredness form: `D_η` lies in one back-and-forth class at `η` and has countable
complement, so the codes of models meet countably many classes of `bfEquivSetoid Φ η`, and
InfinitaryLogic's `isThinOn_of_bfScattered` applies, with no López–Escobar.  This application is
compiled conditional on the cap-to-model theorem, (R1), forcing donors at every countable block
index, the continuation criterion, (R2) and (R3), each still to be proved
(`densitySentence_isThinOnNatModels_of_terminalClassification_bfScattered`,
`MainTheorem/ScatteredDomains`): `bfScattered_of_countable_compl` (`MainTheorem/Scatteredness`;
cocountable sets of back-and-forth equivalent classes give `BFScattered`, through
InfinitaryLogic's `bfScattered_of_countable_bfObservations`), `codeBFEquiv_of_mem_expansionDomain`
(one back-and-forth class in `D_η`, conditional on (R1)),
`densitySentence_bfScattered_of_modelExpansions` (conditional on the cap-to-model theorem,
next-block uniqueness, (R1) and countable losses; the complements are
`ExpansionDomains.compl_countable` for `modelExpansionDomains`),
`densitySentence_bfScattered_of_terminalClassification`, the thinness theorems
`densitySentence_isThinOnNatModels_of_modelExpansions_bfScattered` and
`densitySentence_isThinOnNatModels_of_terminalClassification_bfScattered`, and
`FullPresentations.HasScatteredTails.of_bfScattered` (`MainTheorem/Assembly`; back-and-forth
scatteredness gives scattered tails to every family of full presentations).  Checked on the proof
terms, the thinness theorem of `MainTheorem/ScatteredDomains` with the hypotheses of the terminal
classification contains neither `sentence_separates_analytic_classes` nor any López–Escobar
constant, while `densitySentence_isThinOnNatModels_of_terminalClassification` contains both.  The
minimality form, from countable truth sides, is kept.

**Eventual departure and the last stage** (`MainTheorem/LastStage`, compiled in this repository
(theorem named); `COMPANIONS.md`, terminal refinement, items 1 and 2).  On any `ExpansionDomains`:
* `ExpansionDomains.notMem_of_isolating`: an observation isolating `q` and constant on a domain
  with two members excludes `q` from it (no hypothesis on the domains);
* `ExpansionDomains.HasNonemptyLosses.nontrivial_domain`: nonempty losses at `ξ` and `ξ + 1` give
  two members of `D_ξ` (the field `antitone`);
* `ExpansionDomains.notMem_of_isolating_of_qrank_le`: under `ExpansionDomains.HasRankAgreement`
  (condition 3 in sentence form, rank `≤ η` at stage `η`, no offset) and nonempty losses, a class
  isolated by a sentence of rank `δ < ω₁` is not in `D_δ`;
* `ExpansionDomains.exists_notMem_of_isolating_of_cofinal` and `exists_notMem_of_isolating`:
  under `HasLogicalAgreement` and cofinally (or all) nonempty losses, an isolated class leaves the
  domains below `ω₁`; `ExpansionDomains.core_eq_empty`: with every class isolated, the persistent
  core is empty;
* `ExpansionDomains.lastStage` (the supremum of the stages containing `q`; no hypothesis), with
  `le_lastStage`, `lastStage_le_omega_one` and `lastStage_eq_omega_one_of_mem_core` (`ω₁` on the
  persistent core), which use the field `domain_eq_empty_of_omega_one_le` (through
  `lt_omega_one_of_mem`, directly or via `bddAbove_setOf_mem`); `isGreatest_lastStage` (attained
  and below `ξ` once `q ∉ D_ξ`, `ξ < ω₁`;
  the fields `zero`, `antitone` and `limit` only), and `mem_domain_iff_le_lastStage_of_notMem`,
  `mem_loss_iff_lastStage_eq_of_notMem` (which add `domain_eq_empty_of_omega_one_le`, through
  `le_lastStage`); under isolation, logical agreement and nonempty losses, `exists_lastStage`,
  `lastStage_lt_omega_one`, `mem_domain_iff_le_lastStage`, `mem_loss_iff_lastStage_eq`,
  `loss_eq_preimage_lastStage`, `domain_eq_setOf_le_lastStage`; under the sharp agreement,
  `lastStage_lt_qrank`;
* for the classes of coded models (Scott isolation, `exists_classTruth_iff_eq`):
  `core_eq_empty_of_classTruth` and the `…_of_classTruth` forms; for the actual expansion domains,
  `modelExpansionDomains_hasRankAgreement` (for `modelExpansionDomains hcap hnext`, under (R1));
  `expansionDomain_core_eq_empty`, under
  next-block uniqueness, finite-cut receiving ((R1)), and the coatom extension property with apex
  at every countable block stage, which at `0` gives `CapToModel`
  (`CapToModel.of_hasApexCoatomExtensions`), so `CapToModel` is not a premise of it; and
  `mem_expansionDomain_iff_le_lastStage`, `mem_expansionDomain_loss_iff_lastStage_eq`,
  `lastStage_modelExpansionDomains_lt_qrank`, whose statements mention `modelExpansionDomains hcap
  hnext` and so take `CapToModel` as well; each of these hypotheses is still to be proved.

The count does not use them, and no hypothesis of a main-theorem statement changes.  Global
termination is not used.  The terminal expansion at the last stage (terminal refinement, item 3) is
not stated.  The classes terminal at `β`, `MainTheorem.terminalClasses β`
(`MainTheorem/TerminalClasses`, compiled in this repository (theorem named)), contain the loss at
`β` (`MainTheorem.loss_subset_terminalClasses`, unconditional).  A further target, not stated
(prospective; it depends on next-block uniqueness): the classes terminal at `β` are the fibre of
the last stage at `β`, `terminalClasses β = lastStage (modelExpansionDomains hcap hnext) ⁻¹' {β}`,
which identifies the losses with the terminal classes.  At a repin containing `2cd44c3` ("Dependency
pins", "Upstream statements quoted, not compiled here"), `ExpansionDomains.notMem_of_isolating` is
`notMem_of_isolating_of_uniform` applied to the set `D_ξ`, and `ExpansionDomains.lastStage_lt_qrank`
combines `stage_lt_rank_of_isolating` with the greatest-stage theorem; the local proofs may then
quote them, with the statements kept.

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
   countable and contains the empty chart; each member is finitely generated.  Special cases:
   the empty chart, a one-point chart, a chart with an invisible pair, distinct cells sharing a
   graded index.  Status: compiled in this repository (theorem named), `ClassicalLimit/Age`
   (`topFreeAge`, `countable_topFreeIndex`, `fg_topFreeChart`, `nonempty_topFreeAge`), with the
   special cases in `ClassicalLimit/AgeExamples`.
2. **Hereditary closure, amalgamation, joint embedding.**  Acceptance: the finitely generated
   substructures of a member are exactly its closed faces with their literal restrictions;
   amalgamation of two top-free charts over a common face, by the plain form of the coatom
   extension property followed by capping at a proper cap self-visible at the arity of the
   amalgam and above all labels of both charts, with the literal commuting square
   `f₁.trans g₁ = f₂.trans g₂` and literal restrictions to both charts; joint embedding as the
   case of the empty chart; the hypotheses of `isFraisse_representativeClass` in exactly its
   form (literal square).  Special cases: the empty common chart, a common chart equal to one of
   the two, equal charts with equal face embeddings, a common chart that is the hull of two of
   its points and has more than two points.  Strong amalgamation is not claimed or needed.  No
   infinite model is imported.  Status: compiled in this repository (theorem named).  Hereditary
   closure, with no hypothesis: `exists_equiv_topFreeChart` (exactly the hypothesis `hsub` of
   `isFraisse_representativeClass`) and `hereditary_topFreeAge` (`ClassicalLimit/Age`). Amalgamation
   and joint embedding, conditional on the coatom extension property `StageType.HasCoatomExtensions`
   at the stage (still to be proved) and on a stage that is a nonzero limit:
   `exists_amalgam_topFreeChart`, `exists_jointEmbedding_topFreeChart`, and `isFraisse_topFreeAge`
   (`ClassicalLimit/Amalgamation`), through the capped amalgam `StageType.exists_isTopFree_amalgam`;
   the special cases are in `ClassicalLimit/AmalgamationExamples`, stated for an arbitrary top-free
   chart where no legal type on three or more points is constructed.
3. **Classical existence.**  Acceptance: `isFraisse_representativeClass` applied to the family,
   then the classical existence theorem (available at the pin), giving a countable
   `L^h_λ`-structure with
   `IsFraisseLimit`; the countability hypotheses (`[Countable (Σ l, L.Functions l)]`, countably
   many isomorphism types) are proved for `L^h_λ` and the age, not assumed.  Status: compiled in
   this repository (theorem named), under the hypotheses of step 2 and the countability of the
   stage: `exists_isFraisseLimit_topFreeAge` (`ClassicalLimit/Amalgamation`).
4. **Reconstruction of partial evaluation.**  Acceptance: the evaluation of an injective tuple is
   defined from the chart relations of the limit, and the literal recovery and uniqueness
   clauses of the acceptance criterion (`SEMANTIC_CONTRACT.md`, item 11) are proved from the
   factorization of tuples through representatives.  Status: met; compiled in this repository
   (theorem named), in `ClassicalLimit/Reconstruction`, for a structure whose age is contained in
   the age of top-free charts (top-free chart coverage), the limit being a hypothesis: `reconstruct`
   (no hypothesis on the structure), `exists_eq_trans_topFreeChart`, `reconstruct_eval_trans_chart`,
   `reconstruct_eval_eq_some_iff`, `relMap_rel_iff_reconstruct_eval`, `eq_of_relMap_rel`,
   `injective_of_relMap_rel`, and `reconstruct_eval_eq_some_iff_exists_embedding`; the roundtrip of
   `HULL_ALGEBRA.md`, §5, in direction (a) for every realization with legal types
   (`reconstruct_toHullStructure`) and in direction (b) under top-free chart coverage
   (`toHullStructure_reconstruct`), for the operations `Realization.hullOp`.  The special cases are
   in `ClassicalLimit/ReconstructionExamples`.
5. **Consistency, covering, top-freeness, nonempty carrier.**  Acceptance: each proved from the
   factorization of one finite tuple through one representative; exact partial restriction with
   `none` at invisible faces; covering for arbitrary tuples `Fin n → M`, the empty tuple and
   repeated coordinates included; every evaluated type in the age.  Status: met; compiled in this
   repository (theorem named), in `ClassicalLimit/Reconstruction`, under top-free chart coverage:
   `isConsistent_reconstruct`, `isCovering_reconstruct`, `exists_comp_eq_reconstruct_eval` (tuples
   `Fin n → M`), `isTopFree_of_reconstruct_eval`, and `mem_topFreeAge_of_reconstruct_eval` (every
   evaluated type in the age); the nonempty carrier under the converse inclusion of ages
   (`nonempty_of_topFreeAge_subset`); all of them, with legal types, for a structure whose age is
   the age of top-free charts (`reconstruct_of_age_eq`) and for a Fraïssé limit of it
   (`reconstruct_of_isFraisseLimit`).  Ultrahomogeneity is not used.
6. **Receiving.**  Acceptance: for every root, one-point donor type, and permitted cutoff, an
   occurrence over the literal root from (R5) and `IsUltrahomogeneous.extend_embedding`, with all
   its equations on that one occurrence; exact receiving for top-free donors (cutoff above every
   label of the donor); for donors containing top, one extension for each cutoff, with no claim of
   one extension for all cutoffs or of recovery of a top.  Special cases: the empty root, a donor
   with top labels at two different cutoffs, a donor with bottom labels.  Status: met; compiled in
   this repository (theorem named), in `ClassicalLimit/Receiving`, for a structure whose age is the
   age of top-free charts and which is ultrahomogeneous, at a stage that is zero or a limit:
   `hasFiniteCutReceiving_reconstruct`, `hasFiniteCutReceiving_reconstruct_of_isFraisseLimit`,
   `hasFiniteExtensionReceiving_reconstruct`, and exact extension of top-free donors within the age,
   with no stage hypothesis (`exists_reconstruct_eval_eq_of_isTopFree`); the special cases, and
   exact receiving of a top-free donor, are in `ClassicalLimit/ReceivingExamples`.  The root is a
   whole actual occurrence, so (R5) is used only over a whole chart (the capped coface), and the
   proof uses the age equality, ultrahomogeneity, and capping: neither
   `StageType.HasCoatomExtensions` nor modelhood is a hypothesis, and only the existence of the
   limit (step 3) needs `StageType.HasCoatomExtensions`.  Finite-cut receiving descends along stage
   reduction, one permitted cutoff at a time (`HasFiniteCutReceiving.reduce`,
   `Realization/Receiving`), which is not exact projected receiving.
7. **Modelhood, infinitude, terminality.**  Acceptance: modelhood by the cap-to-model theorem
   (checkpoint 4); infinitude, with freshness of the received point over the whole finite
   chart: for a finite set `F`, the root is an actual occurrence `t` containing `F` (covering)
   and the donor a one-point coface of its type ([Kni26, Proposition 4.3.23], which supplies
   only the coface, a stage type on one more point, not a point of the realization); the
   receiving criterion, all equations on one injective occurrence extending `t` literally, puts
   the new point outside the whole chart `t`, hence outside `F`; terminality from top-freeness
   and the labels in the new block `[λ, λ + ω)` required at the next block, using only the
   reduction of models (layer 2).
   The placement of the base class in the loss at `η`, by expansion uniqueness and same-carrier
   transport, belongs to layer 5 (checkpoint 5).  Status: the base-reduct part is compiled in this
   repository (theorem named): for a structure whose age is the age of top-free charts and which is
   ultrahomogeneous, at a limit stage `α ≥ ω`, the base-language structure of the reduction of the
   reconstruction to `ω` satisfies the density sentence
   (`realize_densitySentence_reconstruct_reduce`, `ClassicalLimit/Receiving`, through
   `hasFiniteCutReceiving_reconstruct_reduce` and the descent `HasFiniteCutReceiving.reduce`), with
   modelhood neither used nor claimed.  The clauses of modelhood that do not concern extensions (a
   nonempty carrier, legal types, exact consistency, covering) are compiled for a structure whose
   age is the age of top-free charts (`reconstruct_of_age_eq`).  Modelhood at `λ`, infinitude, and
   terminality are compiled in this repository (theorem named), in `ClassicalLimit/Modelhood`, for
   a structure whose age is the age of top-free charts and which is ultrahomogeneous, at a nonzero
   limit stage: modelhood by the cap-to-model theorem at a limit stage
   (`Realization.isModel_of_hasFiniteCutReceiving`), conditional on the nonemptiness of the
   instances of uniformity and dominance, which the coatom extension property with apex gives
   (`isModel_reconstruct_of_hasApexCoatomExtensions`); infinitude under
   `StageType.HasCoatomExtensions` (`infinite_of_age_eq_of_hasCoatomExtensions`); and terminality
   with no hypothesis beyond top-free chart coverage (`reduce_ne_reconstruct`).  The existence of
   the limit rests on `StageType.HasCoatomExtensions`, and both coatom extension properties are
   still to be proved.

**Dependency boundaries.** The age argument (steps 1–7) imports Mathlib, InfinitaryLogic,
ComputableModelTheory (its entry module `ComputableModelTheory.Classical`), layers 0–2, and the
finite kernel (layer 1, the coatom extension construction with (R5) and (R6), and the cap-to-model
theorem). Steps 1–7 import no `Construction/` module; the classical part, steps 3–5, imports no
module of (R1)–(R4), of structural continuation, or of the expansion domains; steps 6 and 7 add only
(R5), the cap-to-model theorem, and the reduction of models. The upstream theorems import no module
of this repository. The chain construction (`Construction/`, the chain unions of partial
realizations, and the conditional chain construction of models) is needed neither for top-free
existence nor for saturated existence: the saturated model of [Kni26, Proposition 4.4.5] is
reconstructed from the classical limit of the uncapped age of all legal stage types (hereditary,
amalgamating by the plain form of the coatom extension property, countably many isomorphism types).
No checkpoint of the main theorem depends on the chain construction. It is retained for an effective
presentation only, conditional on effective input data (an effective enumeration of the age and an
effective amalgamation procedure; the classical Fraïssé construction uses choice and supplies no
computable presentation). The partial-realization statements of the conditional chain development
(`StageType.chartRealization`, `StageType.isConsistent_chartRealization`,
`StageType.chartRealization_eval_eq_none_iff`, in `Realization/Partial.lean`, outside
`Construction/`, in the library) are not used by steps 1–5 as compiled, which read a chart as the
face realization of its stage type (`StageType.faceRealization`, `StageType.faceRealization_eval`,
in the same module, and `StageType.relMap_chart`); the chain-union statements are not used by steps
1–7. As compiled, steps 1–5 (`ClassicalLimit/Age`, `ClassicalLimit/Amalgamation`, and
`ClassicalLimit/Reconstruction`, which imports only `ClassicalLimit/Age`) import
ComputableModelTheory only through
its entry module `ComputableModelTheory.Classical`, no module of InfinitaryLogic and no
`Construction/` module, and, of the finite extension constructions, only `Extension/Basic` and
`Extension/PinnedExtension` (for the one-point scheme and the zero-point lemmas) and
`Extension/SectionTheorem` with `Extension/WitnessAlgebra`, an import these steps do not use: the
capping lemma is in `Scheme/Row`, and the capping API, used through `Stage/Cap`, is in `Stage/`
("Placement record"). As compiled,
step 6 and the base-reduct part of step 7 (`ClassicalLimit/Receiving`) add to these only
`Realization/Receiving` (finite-extension receiving and its descent along stage reduction) and
`Language/Density` with `Language/Structure`, `Language/Sentence`, and `Language/Satisfaction` (for
the density sentence of the base reduct), which bring InfinitaryLogic's `Lomega1omega` modules
(layer 0); no `Construction/`, `MainTheorem/`, or `Expansion/` module, and no module of layers 4–5.

## The full-presentation route

The spine above is the expansion-domain route, the first endpoint. The full-presentation route of
`README.md`, "Reduction to full presentations", is a second route to the main theorem, retained
beside it; the two are compared as complete verified proofs.  Neither changes the other's
statements, and the expansion-domain composition stays as it is.

**Order.**  The route is tested in the order that exposes its new mathematics earliest, before
any construction is adapted to it:

1. **the generic presentation-counting theorem:** the fundamental theorem of `README.md` from its
   hypotheses (the count at one level, scatteredness from countably many observed types, the
   least-level filtration under a common starting observation, and the lower-bound criterion);
2. **projected extension to back-and-forth:** (AE) gives approximate comparison (InfinitaryLogic's
   `bfEquiv_of_gradedMatching` gives `BFEquiv`; on abstract hypotheses this is
   `FullPresentation.bfEquiv_comp_of_obs_eq`, compiled in this repository (theorem named)), and
   approximate comparison gives the sentence form of bounded comparison through
   `BFEquiv_implies_agreeQR`; for model expansions to `λ_η` from an arbitrary common chart with a
   selector, the comparison is `ModelExpansion.bfEquiv_comp_of_covers`, with formula form
   `ModelExpansion.realize_comp_iff_of_covers` (`Expansion/Agreement`), compiled conditional on
   `Expansion.FiniteExtensionReceiving` ((R1), still to be proved); it goes through
   `ExpansionMatchData.bfEquiv_of_match`, a parallel result, not an instance of
   `FullPresentation.bfEquiv_comp_of_obs_eq`;
3. **a concrete full-presentation construction from the terminal classification:** the full
   presentations of the terminal models (pointed at the named core, residual, hollow) and of the
   top-free age, to see whether the new organization shortens the argument that faces the
   construction (in place of the one-block transfer and the limit continuity of layer 5).

**The nine formal statements, with their homes.**  The generic pieces go to the library where
their notions live; "this repository" means the layers of `README.md`.

1. *Structured geometry:* cofinal, intersection-closed finite supports, their hulls, and a
   uniform interpretation of each finite invariant across models.  Home: this repository (the
   hulls with layer 0, "Finite closure", beside InfinitaryLogic's `FiniteSupportClosure`; the
   uniform base diagram of a stage type with layer 2).
2. *Observation syntax:* countable level sets, commuting projections, and their
   interpretation on finite closed tuples, with separate levels or level-indexed predicates,
   never a single exclusive partition by full labels.  Home: this repository (the generic shape
   `FullPresentation.LevelObservations`, with `FullPresentation.ObservedPresentation`, in the
   library module `Comparison/GradedMatchingApplications`, which `Suggested.lean`, section 6,
   quotes; the instance is stage reduction, `StageType.reduce` with `StageType.reduce_reduce`).
3. *(AE):* the target's actual root kept exactly, the extended diagrams compared only at the lower
   level, the target's restrictions retained.  Home: the instance in this repository (the projected
   finite-extension rule, one case for each ordered pair of kinds of allowed ages, or, between
   presentations reducing to model expansions at `λ_{η+1}` (the downward closure of layer 5), the
   finite-extension presentation of finite-cut receiving of the target (layer 3, "Receiving for
   finite extensions", compiled as `HasFiniteCutReceiving.hasFiniteExtensionReceiving` in
   `Realization/Receiving`, resting on (R1), which is still to be proved and is to be supplied in
   the form `Expansion.FiniteCutReceiving`), run at an auxiliary self-visible cap strictly between
   `λ_η` and `λ_{η+1}`: iterated one-point receiving retains each actual root literally, but the
   next donor coface need not restrict literally to the newly received root, and the
   bounded-observation lifting at that cap repairs it at each step; `README.md`, "Reduction to full
   presentations"); the passage to `BFEquiv` by InfinitaryLogic's `bfEquiv_of_gradedMatching` (at
   the pin, signatures checked), with the height guard and the selection of coordinates inside the
   relation (the match (i) of `README.md`, layer 0), compiled on abstract hypotheses as
   `FullPresentation.bfEquiv_comp_of_obs_eq` (`Comparison/GradedMatchingApplications`), compiled in
   this repository (theorem named); its instantiation to the presentations of the construction is
   not elaborated.
4. *Exact comparison* for prescribed pointed or unpointed full ages, reusing standard
   uniqueness rather than a separate comparison for each terminal case.  Home: fullness and equal
   ages give extension pairs in both directions, hence an isomorphism: ComputableModelTheory's
   rooted uniqueness (`isExtensionPair_of_age_subset`,
   `exists_equiv_comp_eq_of_age_subset_of_countable`, available at the pin `a1fe761`, signatures
   checked; Mathlib-only imports; its application to full structures is expected, not
   elaborated), and
   eventually Mathlib's `ModelTheory/Fraisse`; the relational exact-age comparison for
   realizations, in this repository (layer 4).
5. *A countable list of allowed full extension laws at each level, and a full presentation of every
   base model* (not replaceable by countability of the label alphabet), including the persistent
   class or the weakening to all but countably many classes.  Home: this repository (layer 4, the
   terminal classification by exact ages, read in the other direction).  The counting composition is
   conditional on this coverage (the hypothesis `FullPresentations`). The known way to establish it
   goes through global termination (every class leaves the expansion domains at a countable stage,
   where its terminal expansion is full for its terminal exact age); the finite-stage arguments do
   not cover the persistent class (`README.md`, "The persistent core").  Eventual departure, the
   first half of global termination, is terminal refinement, item 1 (`COMPANIONS.md`, "Further
   companion results"), compiled conditionally (`ExpansionDomains.core_eq_empty`,
   `MainTheorem/LastStage`) from hypotheses of the expansion-domain count (the agreement of
   condition 3 and the nonempty losses of condition 4, with a Scott sentence for each class), not
   from its conclusions; under them the persistent core is
   empty.  The second half, that the terminal expansion is full for its terminal exact age, is the
   first special statement and is not part of terminal refinement.  A proof of this route may take
   departure from terminal refinement without circularity, stating its dependence on conditions 3
   and 4 of the expansion-domain route (not on its count); departure proves neither terminal
   fullness nor the coverage itself.  A proof of this route that does not depend on conditions 3 and
   4 covers every class, the persistent class included, by its own argument.
6. *Noncollapse of the base reducts* (occurrence of all auxiliary invariants is
   insufficient).  Home: this repository (the top-free witnesses with expansion uniqueness and
   same-carrier transport, layer 6); the generic isolating-level criterion in sentence form in
   `Counting/Separation`, and in back-and-forth form in InfinitaryLogic, `Scott`.
7. *Small back-and-forth quotients and the analytic-pair boundedness argument;* minimality
   is a further assertion needing a common starting observation on high presentations.  Home:
   InfinitaryLogic, `Descriptive/BFSeparation` (`exists_uniform_bfSeparation`, available at the
   pin `e460cb6`, signatures checked); the composition is `MainTheorem/Scatteredness`
   and the scattered-tails theorems of `MainTheorem/Assembly` (pull request #42; "The
   scatteredness form" below).  The minimality form is already covered through sentences by
   `Sentenceω.isThinOnNatModels_of_countable_sentence_splits`.
8. *A translation from the templates of [AFK26] to the fixed-row and separate-labelling
   convention,* stating exactly which coordinates stage reduction changes (the labels, not the
   rows).  Home: this repository (`README.md`, layer 2, "The templates of [AFK26] and the stage
   types here").
9. *A corrected comparison for the introductory example of full trees,* with its rank
   convention explicit; the same-index equivalence of the draft cannot be a formal statement as
   written (`LITERATURE.md`, §9).  Home: this repository, among the optional examples
   (`COMPANIONS.md`, "Further companion results", "Full trees").

**Lean statements of the route.**  Pull request #38 ("Layers 5–6: the full-presentation route to
the main theorem, as a conditional composition", merged) states the route as a conditional
composition beside the expansion-domain composition, which is unchanged:

- `Counting/Filtration`: `Filtration.ofRank` (the tails `{x | η ≤ r x}` of a rank below `ω₁`
  whose fibres at the levels below `ω₁` are countable,
  `hfib : ∀ α, α < ω₁ → {x | r x = α}.Countable`, on an uncountable type), `leastLevel`, and
  `Filtration.ofCountableCover` (domain `η` equal to `(⋃ α < η, Q α)ᶜ`); `Counting/Separation`:
  `mk_le_aleph_one_of_countable_cover`;
- `MainTheorem/Spectrum`: `IsUniformOnFiltration.of_qrank_le`, the counterpart for a
  `Filtration` of `ExpansionDomains.HasLogicalAgreement.of_qrank_le`;
- `MainTheorem/Assembly`: the hypotheses `FullPresentations X` (fields `presentedAt`,
  `countable_presentedAt`, `exists_mem_presentedAt`, and `presentedAt_eq_empty_of_omega_one_le`,
  no presentations at the levels at or above `ω₁`), `FullPresentations.HasBoundedComparison truth`
  (bounded comparison in its minimality form: the classes of the tail at `η` agree on every
  sentence of quantifier rank at most `η`), and `UncountablyManyClasses`
  (`ℵ₁ ≤ #DensityClass`), with the conditional theorems
  `densitySentence_isThinOnNatModels_of_presentations`,
  `densitySentence_hasThinAlephOneSpectrum_of_presentations`, and
  `vaughtCounterexample_of_presentations`;
- with pull request #42 (the scatteredness form, below): `MainTheorem/Scatteredness`, and in
  `MainTheorem/Assembly` the hypothesis `FullPresentations.HasScatteredTails` (with
  `FullPresentations.HasScatteredTails.countable_quotient` and its converse
  `FullPresentations.HasScatteredTails.of_countable_quotient`) and the conditional theorems
  `densitySentence_isThinOnNatModels_of_scatteredTails`,
  `densitySentence_hasThinAlephOneSpectrum_of_scatteredTails`, and
  `vaughtCounterexample_of_scatteredTails`;
- the two applications of graded matching (`Comparison/GradedMatchingApplications`, layer 0 of
  `README.md`), on abstract hypotheses, through InfinitaryLogic's `bfEquiv_of_gradedMatching`: the
  observation shapes `FullPresentation.LevelObservations`, `FullPresentation.ObservedPresentation`,
  `FullPresentation.AtomicAtZero`, and `FullPresentation.ApproxExtension`, the relation
  `FullPresentation.ObsMatch`, and approximate comparison,
  `FullPresentation.bfEquiv_comp_of_obs_eq`; for condition 3 of the expansion-domain route,
  `ExpansionMatchData`, `ExpansionMatchData.Match`, `ExpansionMatchData.bfEquiv_of_match`, and
  `ExpansionMatchData.bfEquiv_of_expansionMatch`;
- the all-countable-carrier formulation (`MainTheorem/AllCarriers`): `CountableModel`,
  `CountableModelClass`, `codedClassEquiv`, `HasThinAlephOneSpectrumOnCountableCarriers` with
  `hasThinAlephOneSpectrumOnCountableCarriers_iff`,
  `densitySentence_not_perfectSetDichotomyAllCountable`, the three theorems
  `densitySentence_hasThinAlephOneSpectrumOnCountableCarriers_of_expansionDomains`,
  `…_of_presentations`, and `…_of_scatteredTails`, and the three theorems
  `vaughtCounterexample_allCarriers_of_expansionDomains`, `…_of_presentations`, and
  `…_of_scatteredTails`, each with the hypotheses of its counterpart on `ℕ` and the cap-to-model
  theorem `CapToModel` (still to be proved), from which the absence of finite models is derived.

Recorded with it: the count uses only `FullPresentations` (`#X ≤ ℵ₁`), and bounded comparison is
used only for thinness; the proof term of the main conditional theorem avoids `classTruth_separates`
(Scott separation on the empty core is unused), while thinness still goes through sentence
separation; `FullPresentations` contains the global claim that every class, a persistent one
included, has a full presentation (statement 5 above, and `README.md`, "The persistent core"); and
the weaker form, countably many back-and-forth classes in each tail, is
`FullPresentations.HasScatteredTails`, composed by pull request #42 (below).  The reduced
dependencies of that composition, checked on the proof terms: the scattered-tails thinness and
spectrum theorems contain neither `sentence_separates_analytic_classes` nor any López–Escobar
constant, while `densitySentence_isThinOnNatModels_of_presentations` contains both.

**The scatteredness form: pull request #42.**  The thinness composition in scatteredness form
(countably many back-and-forth classes at each level `η < ω₁` exclude a perfect antichain, with no
sentence definability of the class) is composed from `exists_uniform_bfSeparation`
(InfinitaryLogic's pull requests #142–#144, at our pinned dependency since this repository's pull
request #41) in pull request #42, "Layer 6: thinness from countably many
back-and-forth classes at every level, by analytic separation": the pairs of distinct points of a
hypothetical perfect antichain form an analytic set with no isomorphic pair, so one level `η`
separates them, and only countably many classes occur at `η`.  Its statements:

- `MainTheorem/Scatteredness` (every statement generic; none mentions the density sentence; for a
  countable relational language): `codeBFEquivSetoid` (the library's `CodeBFEquiv η` as a setoid
  on all codes) and `bfEquivSetoid_eq_comap` (the library's `bfEquivSetoid φ η` is its
  restriction to the codes of models of `φ`); `analyticSet_offDiag` and `offDiag_noniso` (the
  pairs of distinct points of a closed pairwise nonisomorphic set of codes form an analytic set
  with no isomorphic pair); `not_countable_of_perfect`;
  `exists_forall_not_codeBFEquiv_of_isClosed` (one level separates a closed antichain);
  `isThinOn_of_countable_bfClasses` (if for every `η < ω₁` the restriction of `CodeBFEquiv η` to a
  set `K` of codes has countably many classes, then `K` contains no nonempty perfect set of
  pairwise nonisomorphic codes; the hypothesis counts classes, not codes) and
  `isThinOnNatModels_of_countable_bfClasses` (the same for the codes of models of a sentence `φ`,
  with `bfEquivSetoid φ η`, concluding `φ.IsThinOnNatModels`);
- `MainTheorem/Assembly`: the hypothesis `FullPresentations.HasScatteredTails` (the codes of the
  models whose classes lie in the tail at `η` meet only countably many classes of
  `bfEquivSetoid densitySentence η`), with `FullPresentations.HasScatteredTails.countable_quotient`
  (countably many classes at `η` among all the codes of models) and its converse
  `FullPresentations.HasScatteredTails.of_countable_quotient`, and the conditional theorems
  `densitySentence_isThinOnNatModels_of_scatteredTails` (neither bounded comparison nor the lower
  bound is used), `densitySentence_hasThinAlephOneSpectrum_of_scatteredTails` (with
  `UncountablyManyClasses`, the count as in
  `densitySentence_hasThinAlephOneSpectrum_of_presentations`), and
  `vaughtCounterexample_of_scatteredTails` (the counterpart of
  `vaughtCounterexample_of_presentations`).

It weakens the thinness hypothesis of the second conditional composition from the minimality form
`FullPresentations.HasBoundedComparison` to the hypothesis of the fundamental theorem; both
conditional compositions are kept.

**The graded back-and-forth theorem, retired** (`README.md`, layer 0, where it is stated with all
its hypotheses).  For structures `M` and `N` and relations `R α n a b` between `n`-tuples of `M` and
`N`, for `α` up to an explicit height `h` (`h : Ordinal.{0}` in both applications), with the zero
clause (`R 0` gives `SameAtomicType`), descent (`R α` gives `R β` for `β ≤ α ≤ h`), and forth and
back from `R (α + 1)` into `R α` on one-point extensions, it gives `BFEquiv α n a b` for every `α ≤
h` and every pair with `R α n a b`; the initial match, a pair related at the height, is a separate
hypothesis in each application.  It is the special case of InfinitaryLogic's generic form (the next
paragraph) with initial match at the height.  Its two intended applications, approximate comparison
of full presentations (item 3 above) and the back-and-forth form of condition 3 of the
expansion-domain route (layer 5, section 5 above), both compile through the generic form, so it is
retired as a target of this repository, not proved here and not moved ("Placement record").

**The upstream graded-matching theorem.**  InfinitaryLogic's `bfEquiv_of_gradedMatching`
(`Scott/GradedMatching`; at the pin, signatures checked), a generic form of the theorem above, takes
a relation defined at every ordinal, in any language, and guards its laws by the height (lowering
for `β ≤ α ≤ height`, forth and back for `α + 1 ≤ height`); from `α ≤ height` and a pair related at
level `α` (the initial match) it concludes `BFEquiv`.  Each of the two applications therefore puts
the height guard `α ≤ η` and the selection of coordinates inside the relation, with height `η`: for
approximate comparison, a proof of `α ≤ η`, equal observations at `α` of two closed tuples, and a
selection of their coordinates; for condition 3, model expansions of the two fixed base models to
`λ_α`, a common chart, two covers, and a selector `Fin n → Fin k`, with the common empty chart as
initial match and no uniqueness of expansions used (`README.md`, layer 0, the matches (i) and (ii)).
For condition 3 the initial match is two separate lemmas, existence of the empty chart in both
expansions and compatibility of the two empty charts.  Both applications are compiled through the
upstream theorem, on abstract hypotheses, in `Comparison/GradedMatchingApplications`:
`FullPresentation.bfEquiv_comp_of_obs_eq` and `ExpansionMatchData.bfEquiv_of_expansionMatch`, each
compiled in this repository (theorem named), the second with the two hypotheses
`exists_empty_chart` and `compat`; in both, a match of closed sets is carried to the tuple relation
by a selector, so that repeated coordinates and the empty tuple are covered (`README.md`, layer 0).
Their instantiation to the construction is not elaborated.  The local theorem above is retired, and
the construction layers supply only atomic agreement, lowering, forth and back, and an explicit
initial match, without an ordinal induction of their own.  Nothing is needed from
ComputableModelTheory for it.

**Prospective interfaces of InfinitaryLogic** (neither available upstream nor pinned, except the
second, which is now available upstream in family form, below; the statements are specified here,
generically, with no construction):

- *invariant Borel observations* (`Descriptive`): an isomorphism-invariant Borel map on codes of
  models on `ℕ`, into a countably separated space, is constant on the `BFEquiv α`-classes for
  some `α < ω₁`; measurability is on codes only, never on the class quotient, and no sentence is
  recovered;
- *limits of chains of bounded equivalence* (`Scott/BlockBackAndForth`): an analogue for
  `BlockBFEquiv` of [Mon, Lemma XII.6], by the same construction, with its offset to be determined:
  for increasing countable ordinals `α_i` and countable structures `A_i` with `A_i` and `A_{i+1}`
  `BlockBFEquiv`-equivalent at `α_i` plus that offset (empty tuples), a countable structure
  `BlockBFEquiv α_i`-equivalent to every `A_i`; [Mon]'s offset `+3` is for its own relation [Mon,
  Definition II.32] and is not transferred; it supports the rank-filtration comparison of
  `COMPANIONS.md`, "Further companion results", only through the passage between [Mon]'s convention
  and InfinitaryLogic's, which is still to be proved.

The isolating-level lower bound, formerly listed here, is available at the pin `e460cb6`
(`Scott/IsolatingLevel`, signatures checked; "Dependency pins"): over a countable relational
language a countable family of countable structures has a level `γ < ω₁` at which empty-tuple
`BFEquiv0` implies isomorphism (`exists_isolating_level`, the supremum of the stabilization
ordinals); hence, if every countable level has two nonisomorphic `BFEquiv0`-related members, the
index is uncountable (`not_countable_of_forall_unisolated`).  No application of it is compiled in
this repository.  A per-class proof of the lower-bound criterion of `README.md` ("Reduction to
full presentations"), isolating one class at a time with no countability of the classes (where
`README.md` bounds the isolating levels of countably many classes by one `γ`), can quote Scott
separation (`exists_countable_strict_stage_bound_of_isolation` and
`IsolatedPresentation.exists_countable_strict_stage_bound`; available upstream, not yet at our
pinned dependency: signatures verified against the upstream source at `2cd44c3`, not compiled
here; "Dependency pins"): every class leaves the domains strictly before a countable stage.  The
domains having two or more members at every countable stage, the classes are then uncountable,
since countably many countable bounds have a countable supremum (`iSup_add_one_lt_omega1`,
`OrdinalCountability`, available at the pin, not `#check`ed in `SuggestedInterfaces.lean`) at
which the domain is nonempty.  With countable complements of the domains in addition,
`mk_eq_aleph_one_of_domains` (available at the pin, signatures checked) gives exactly `ℵ₁`
classes.  Both are prospective applications, not compiled here.

## Manuscript concordance

The milestone of `README.md`, "Manuscript correspondence (required)", spans layers 2–5 here (layers
2–6 of `README.md`).  It concerns the correspondence with [Kni26] and [AFK26], kept distinct: each
row of the concordance below names its source, and both are cited only by numbered statements:
those of [Kni26] that the roadmap already cites (listed in `LITERATURE.md`, "Bibliographic access
record"), and those of [AFK26] in the numbering of its current version, the version named in that
record, or in the numbering of an earlier version, marked as such and named by its date in that
record; a notion with no numbered statement is named by its source and described in words.  Each
row gives a notion of the manuscript that the proof uses, the declarations of this repository that
concern it (or *prospective*), and one of three statuses:

- **proved correspondence** (P): a theorem of this repository is named that compares the
  manuscript's notion with a declaration here clause by clause, or a definition-level
  identification is named: a declaration with one clause for each clause of the manuscript's
  definition, the comparison of the clauses recorded with the declaration, every departure from a
  printed clause proved equivalent to it by a named theorem, and every notion its clauses use
  itself in proved correspondence or corrected.  A corrected notion (C) counts toward P only if
  every one of its differences from the printed definition is either a recorded correction or
  proved equivalent; a row whose clauses use a notion with a part still to be proved records that
  part as S in its status (rows 8 and 11, `P; domains: S (row 6)`);
- **corrected manuscript definition or statement** (C): the manuscript's definition or statement is
  replaced by a corrected one, the correction recorded where named; a theorem about the corrected
  notion is noted when one exists;
- **still to be proved** (S): every other row.  In particular, existing citation numbers alone do
  not establish a correspondence (a docstring citing a numbered statement records what a
  declaration is meant to state, not that it states it), and a compiled declaration with the same
  role as the manuscript's notion is not evidence of fidelity to the manuscript without the
  clause-by-clause comparison; a row whose only evidence is such a declaration, or a conditional
  theorem whose hypotheses are still to be proved, has this status.

The availability markers are those of `README.md`, Layer 0; an argument with no theorem named in
this repository is prospective here.  Rows are added as notions are reached.  A row becomes P only
when the theorem or the definition-level identification that performs the comparison is named, and
becomes C only when the correction is recorded.  Row 29 is P, row 14 is P for the printed
definitions of §2 that it names and C for the language of templates, their diagram, and its lemma
(Definitions 4.17 and 4.18, Lemma 4.19), and row 1 is C with its truncation function P.  Rows 2–5 and 43
are P, by the definition-level identifications of `VaughtConjecture/Correspondence` named in their
notes.  Row 6 is S: `IsBountiful` is the printed definition required at every stage that is zero
or a limit (note 6), and at `ω₁` only the implication from `IsBountiful` is proved.  The other
rows whose declaration carries the manuscript's number but whose clauses have not been compared
are S, with the compiled declarations listed in the notes.  A line with the first two cells empty
continues the row above it: a further notion of the same row, with its own status.
Rows 41–47 concern the legal templates of the current draft of [AFK26] and cite its numbering
(its §4, "The Counterexample");
rows 9 and 10 cite the numbering of their own notes.  Rows 43–47 read the row system of a template
as the fixed semantic rows of a scheme, not as the coherent local rows of row 9 (note 43); row 43
identifies lawful labellings, and does not make the legal schemes here the legal templates of
[AFK26] (note 45).

| Row | Source | Manuscript notion | Status |
| --- | --- | --- | --- |
| 1 | [AFK26] | the observation index `ξ`, Definitions 3.20 and 4.16 | C |
| | | its truncation function, Definitions 3.12 and 4.9 | P |
| 2 | [Kni26] | visibility replacement, Definition 2.2.3 | P |
| 3 | [Kni26] | witnesses and transformation, Definition 2.3.9 | P |
| 4 | [Kni26] | lawful labellings, Definition 2.5.4; orderly labellings, Definition 2.3.4 | P |
| 5 | [Kni26] | lawful capping, Lemma 2.5.8 | P |
| 6 | [Kni26] | bountiful rows, Definition 2.5.14 | S |
| 7 | [Kni26] | domains (legal schemes), Definition 2.6.1 | C; bountifulness at ω₁: S (row 6) |
| 8 | [Kni26] | stage types and face maps, Definitions 3.1.1 and 3.1.5 | P; domains: S (row 6) |
| 9 | [AFK26] | templates, Definitions 4.6 and 4.10 | C; item 1: S |
| 10 | [AFK26] | the stage operation on templates (truncation), Definitions 4.6 and 4.10 | C |
| 11 | [Kni26] | realizations and models, Definition 3.2.1 | P; domains: S (row 6) |
| 12 | [Kni26] | the four extension families as a sentence, Definition 3.2.1, clause 4 | S |
| 13 | [Kni26] | the density sentence against clause 4 (the fidelity theorem of this roadmap) | S |
| 14 | [AFK26] | geometries and structured geometries, Convention 2.3, Definitions 2.1 and 2.2 | P |
| | | invariance diagram and system compatible, Definitions 2.4–2.6 and 2.8 | P |
| | | the language and diagram of templates, Definitions 4.17 and 4.18, Lemma 4.19 | C |
| 15 | [Kni26] | the amalgam of two coatom types, Definition 4.3.1, and Lemma 4.3.2 | P; C, P, S |
| 16 | [Kni26] | the completion of the amalgam, Definition 4.3.14 | C |
| 17 | [Kni26] | the coatom extension with apex, Corollary 4.3.22 | S |
| 18 | [Kni26] | the exact pinned one-point extension, Proposition 4.3.23 | S |
| 19 | [Kni26] | nonempty uniformity and dominance instances, Lemmas 4.4.2 and 4.4.3 | S |
| 20 | [Kni26] | the saturated model, Definition 4.1.1 and Proposition 4.4.5 | S |
| 21 | [Kni26] | the private context, Lemma 8.1.1, clauses 3 and 4 | S |
| 22 | [Kni26] | `Correct`, Definition 8.3.1 | S |
| 23 | [AFK26] | invariants and projections, 1 October 2026 version: Definitions 3.2 and 3.4 | C |
| | | the same, current version: Definitions 2.2 and 2.6 | P (row 14) |
| 24 | [AFK26] | back-and-forth systems, 1 October 2026 version: Definition 4.1, Theorem 4.2 | C |
| | | the same, current version: Definition 2.16 and Theorem 2.17 | C (a starting match specified) |
| 25 | [AFK26] | density at an observation, two-index form (item 3; no numbered statement) | S |
| 26 | [AFK26] | comparison of models with a common invariant (item 4; no numbered statement) | S |
| 27 | [AFK26] | maximal presentations, class–level incidence (item 5; no numbered statement) | S |
| 28 | [AFK26] | same-index equivalence (item 6), 1 October 2026 version: Proposition 8.6 | C |
| | | full trees, current version: Definition 3.10 | S |
| 29 | [AFK26] | closed tuples as supported tuples, Definition 2.1 (item 2) | P |
| 30 | [AFK26] | niceness, Definition 2.19; condition (c) of Definition 2.22 (current draft) | S |
| 31 | [AFK26] | a uniform fixing stage of a family (item 5; no numbered statement) | S |
| 32 | [AFK26] | the bound of serving indices under strictness (item 5; no numbered statement) | S |
| 33 | [AFK26] | maximal presentations of a literal base (item 5; no numbered statement) | S |
| 34 | [AFK26] | five equivalent criteria for them (item 5; no numbered statement) | S |
| 35 | [AFK26] | literal uniqueness of maximal presentations (item 5; no numbered statement) | S |
| 36 | [AFK26] | the optimal all-presentation bound (item 5; no numbered statement) | S |
| 37 | [AFK26] | density bounding the returned invariant (item 3; no numbered statement) | S |
| 38 | [AFK26] | terminal refinement of a higher presentation (item 5; no numbered statement) | S |
| 39 | [AFK26] | exactly one expansion over a domain (item 5; no numbered statement) | S |
| 40 | [AFK26] | maximal presentations by Scott isolation (item 5; no numbered statement) | S |
| 41 | [AFK26] | visibility maps and self-visibility, Definition 4.24 | C |
| 42 | [AFK26] | the relation `u ⇒ v` on labellings of a frame, Definition 4.25 | C |
| 43 | [AFK26] | lawful local labellings, Definition 4.26 | P |
| 44 | [AFK26] | the balls `B_γ(q)` and bountiful rows, Definition 4.26 | S |
| 45 | [AFK26] | legal templates, Definition 4.27 | S; clause 1: C |
| 46 | [AFK26] | a template system of legal templates, Lemma 4.28 (statement) | S |
| 47 | [AFK26] | the counterexample, Theorem 4.29 (statement) | S |

The items are those of `README.md`, "Manuscript correspondence (required)".  Notes to the rows:

1. [AFK26] reads its projection of index `β` at the stage `ω · β` (Definitions 3.20 and 4.16).
   Corrected (C): the printed index `0` reads the stage `0`, at which the projections are not
   compatible with the base relations (`Correspondence.not_isCompatibleWith_omega0MulSystem`,
   row 14).  Here the observation index `ξ` is read at `blockStage ξ`, defined as `ω + ω * ξ`,
   the printed stage of the index `1 + ξ` (`blockStage_eq_mul : blockStage ξ = ω * (1 + ξ)`,
   `Realization/Expansion`).  With the diagram of row 14, only the index `0` is forced to change:
   the printed system corrected at the index `0` alone is compatible and agrees with the printed
   one at every positive index (`Correspondence.isCompatibleWith_omega0MulMaxOneSystem`,
   `Correspondence.omega0MulMaxOneSystem_τ_of_ne_zero`); the shift by one at the other finite
   indices is the convention of `blockStage` (`λ_0 = ω`).  (With the printed `L_c` of
   Definition 4.17 in place of the base relations, compatibility would fail at every finite index;
   note 14.)  Theorems about the corrected notion, compiled in this repository (theorem named), in
   `Correspondence/StageIndexing` unless noted: the two indexings differ by the reindexing
   `ξ ↦ 1 + ξ` (`Correspondence.omega0MulSystem_τ_one_add`, `Correspondence/InvariantSystem`); at
   zero, the printed indices of the block stages are the positive ordinals
   (`exists_blockStage_eq_omega0_mul_iff`, with `blockStage_natCast`); at limits, block stages are
   continuous (`isNormal_blockStage`, `blockStage_eq_iSup_of_isSuccLimit`); the two indexings
   agree from `ω` on (`blockStage_eq_omega0_mul_of_omega0_le`); and the block stages of countable
   index are the limit ordinals below `ω₁` (`isSuccLimit_and_lt_omega_one_iff`), the stages of the
   later of the two versions of 4 October 2026 of [AFK26] (its Definition 4.23; the earlier
   version of that date defines them in its Definition 4.15, and the current version does not
   define stages).  Proved correspondence (P): the printed truncation function (Definitions 3.12
   and 4.9) is `Label.reduce`, clause by clause (`Label.reduce_coe_eq_ite`, `Label.reduce_bot`,
   `Label.reduce_top`, `Label/Basic`).  Printed material, not used here: Definition 4.20 asks for
   density at the index `ω · β` (density at an index being read through the projection of that
   index, Definition 2.10), which by Definition 4.16 is the truncation at `ω² · β`, not at
   `ω · β`.
2. `Label.visibilityReplace` (`Label/Visibility`).  The definition-level identification
   `Label.printedVisibilityReplace_iff` (`Correspondence/Visibility`), compiled in this repository
   (theorem named): a map of labels satisfies the three clauses of the definition
   (`Label.PrintedVisibilityReplace`) exactly when it is `Label.visibilityReplace K m`.
   Departures: the normal form `ω * (o / ω) + o % ω` in place of the printed `μ + j`
   (`Label.visibilityReplace_coe_add`, `Label.exists_eq_add_natCast_isSuccPrelimit`, both in
   `Label/Visibility`), and the value `m` not restricted to `m ≤ K` (harmless:
   `Label.printedVisibilityReplace_iff` holds for every `m`).  The labels of Definition 2.2.1, the
   only notion the clauses use: `Label.printed_order_add`.  Definition 2.2.2, the operation without
   a threshold, is a numbered definition that Definition 2.2.3 restates and does not use.
3. `Label.IsWitness`, `Label.TransformsTo` (`Label/Transform`).  The definition-level
   identification `Label.printedTransformsTo_iff`, at every stage that is zero or a limit, and
   `Label.printedTransformsTo_omega_one_iff`, on the printed labels `{-∞} ∪ ω₁ ∪ {∞}`
   (`Correspondence/Witness`), compiled in this repository (theorem named); the clauses are the
   fields of `Label.PrintedWitness`.  Departures: non-strict antitonicity in clause 1 (Mathlib's
   `antitone_iff_forall_lt`), the orientation of the equation of clause 2, and the range of the
   labels (`Label.PrintedWitness.isWitness_comp_reduce`, `Label.IsWitness.printedWitness_reduce`),
   and the finiteness of the printed `D` (harmless: `Label.printedTransformsTo_iff` holds for every
   type of cells).  The relation is identified, not the witness predicate: `Label.PrintedWitness`
   and `Label.IsWitness` are not equivalent for the same pair, and witnesses correspond up to stage
   reduction by the same two theorems.  Guarded composition only (`README.md`, layer 1) concerns
   [Kni26, Lemma 2.3.14], a statement about the relation and not its definition: the relation is
   not transitive (`Label.TransformsTo.not_transitive`).
4. `CellScheme.Rows.IsLawful` (`Scheme/Row`).  The definition-level identification
   `CellScheme.Rows.printedRespects_iff` (`Correspondence/Lawful`), compiled in this repository
   (theorem named): for cells with graded index in the graded plan, at a stage that is zero or a
   limit, the orderly labellings respecting the semantics (`CellScheme.Rows.PrintedRespects`) are
   the lawful sections; the order law is Definition 2.3.4 (`Label.printedOrderly_iff`), locality
   clause 1, availability clause 2.  On the printed labels `{-∞} ∪ ω₁ ∪ {∞}` it is
   `CellScheme.Rows.printedRespects_omega_one_iff`, compiled in this repository (theorem named).
   Departures: the orientation of the orderly equation (`Label.printedOrderly_iff`); the cap of
   clause 1 is the partial operation of Definition 2.3.7, defined for every orderly labelling
   (`CellScheme.Rows.printedCapDefined_below`); the relation of clause 1 is that of row 3; the
   quantifiers range over the graded plan; the range of the labels, as in row 3; the orderliness
   of each `E(Σ)` that the printed semantics requires and the finiteness of the printed `D`
   (harmless: `CellScheme.Rows.printedRespects_iff` holds without either).  The identifications
   take no `Geometry.IsPlan` hypothesis and hold for every family of faces, in particular for
   plans; Definition 2.6.1 (row 7) is not used by Definition 2.5.4.  The notions the clauses use
   are identified in `Correspondence/Lawful` and row 3: `P̂` by `CellScheme.mem_gradedFaces`,
   `D↾⟨B, j⟩` by `CellScheme.mem_below_iff_exists_mem_gradedFaces`, the arity by
   `CellScheme.grade`, and `⇒` by row 3.  So neither the correspondence of `Geometry.IsPlan` with
   Definition 2.1.1 (no row) nor row 7 is a prerequisite of this row.
5. `CellScheme.Rows.IsLawful.min_const` (`Scheme/Row`), with the special case
   `CellScheme.Rows.IsLawful.min_const_of_isSelfVisible` as a corollary: compiled in this
   repository (theorem named).  The printed statement is
   `CellScheme.Rows.PrintedRespects.min_const` (`Correspondence/Lawful`), compiled in this
   repository (theorem named), `IsLawful.min_const` transported along the identification of
   row 4; the printed `γ` is an ordinal, here any label at the stage.  Restricting `γ` to the stage
   is the printed typing: an ordinal `γ ≥ ω₁` would make `p ∧ γ` leave `{-∞} ∪ ω₁ ∪ {∞}` whenever
   some `p(Σ) = ∞`, and would otherwise give `p ∧ γ = p`.
6. `CellScheme.Rows.IsBountiful` (`Scheme/Bountiful`); status S.  The clauses are the fields of
   `CellScheme.Rows.PrintedLiftHypotheses` and `CellScheme.Rows.PrintedLiftConclusion`
   (`Correspondence/Bountiful`).  Compiled in this repository (theorem named), for finitely many
   cells with graded index in the graded plan: `IsBountiful` is equivalent to the printed
   definition at every stage that is zero or a limit and carries the values of the rows
   (`CellScheme.Rows.isBountiful_iff_forall_printedBountiful`).  Compiled in this repository
   (theorem named): `IsBountiful` implies the printed definition at each such stage
   (`CellScheme.Rows.IsBountiful.printedBountiful`), in particular at `ω₁`
   (`CellScheme.Rows.IsBountiful.printedBountiful_omega_one`).  No theorem gives the converse at a
   single stage, in particular at `ω₁`.  What is missing is the upward transfer of the printed
   definition from `ω₁` to larger limit stages, prospective: a collapse of labels preserving
   lawfulness, in the style of [Kni26, Lemmas 2.3.3 and 2.5.13].  The downward transfer, from a
   larger limit stage to a smaller one such as `ω₁`, follows by the argument of
   `CellScheme.Rows.IsBountiful.printedBountiful` but is not a named theorem either.  Restricting
   the universe does not remove the gap: `Label.{0}` already contains uncountable ordinals
   (`Ordinal.omega.{0} 1`), and `IsBountiful` quantifies over all labels.  The other departures
   are harmless, by named theorems: `≺` in clause 1 read strictly
   (`CellScheme.Rows.printedBountiful_iff_forall_lt`, from the reflexive case
   `CellScheme.Rows.PrintedLiftHypotheses.exists_printedLiftConclusion_of_eq`); the partial caps
   (`CellScheme.Rows.PrintedLiftHypotheses.printedCapDefined`,
   `CellScheme.Rows.PrintedLiftConclusion.printedCapDefined`); and the consistency of `E`
   ([Kni26, Definition 2.5.12], `CellScheme.Rows.IsConsistent` in `Scheme/Row`) that the definition
   presupposes (`CellScheme.Rows.isBountiful_iff_forall_printedBountiful` and
   `CellScheme.Rows.IsBountiful.printedBountiful` hold without it).
7. `Scheme.IsLegal` (`Stage/Legal`), with the coding clause `Scheme.IsCoded` (`Stage/Scheme`);
   status C, with bountifulness at `ω₁` S (row 6).  The clauses of the definition are the fields of
   `CellScheme.Rows.PrintedDomain` (`Correspondence/Legal`); compiled in this repository (theorem
   named): consistency [Kni26, Definition 2.5.12] is `CellScheme.Rows.IsConsistent`
   (`CellScheme.Rows.printedConsistent_iff`), and at a stage that is zero or a limit the printed
   definition is well-formedness, consistency, the printed bountifulness at that stage, and
   completeness (`CellScheme.Rows.printedDomain_iff`).  Compiled in this repository (theorem named):
   a legal scheme is a domain as printed at every stage that is zero or a limit and carries the
   values of its rows (`Scheme.IsLegal.printedDomain`), in particular at `ω₁`
   (`Scheme.IsLegal.printedDomain_omega_one`); and a scheme is legal exactly when its ground set is
   all of its points, its rows are coded, and it is a domain as printed at every such stage
   (`Scheme.isLegal_iff_forall_printedDomain`).  The correction: the coding clause `Scheme.IsCoded`
   (every row value bottom or below `ω ^ 2`) is imposed as a clause, not derived.  The printed
   definition bounds no value, and the printed clauses compared here, the fields of
   `CellScheme.Rows.PrintedDomain`, which omit the recoverability clause, do not imply the range
   bound `Scheme.IsCoded` (`Scheme.exists_printedDomain_not_isCoded`, compiled in this repository
   (theorem named): the scheme on one point whose single cell has the formal top as row satisfies
   them at every stage that is zero or a limit and is not coded).  The bound comes from the coding
   described after [Kni26, Definition 2.6.2], which stores each `E(Σ)` in `{-∞} ∪ ω ^ 2` by the
   first clause of [Kni26, Lemma 2.5.13], a function equivalent under `⇔` when only the functions
   respecting `E` matter; that clause is not compiled, the effect of the replacement on consistency,
   bountifulness, and completeness is not stated there, and the offset bound of the same lemma is
   not correct as stated (`README.md`, Layer 1) and is not used.  The recoverability clause, that
   `⟨B,j⟩`, `P↾B`, `D↾⟨B,j⟩`, and `E↾⟨B,j⟩` are recovered from a cell, has no field: it holds by
   representation (`README.md`, layer 3, vocabulary) and is not compared.  The codes of the cells
   are forgotten, as a second part of the correction: the coding after [Kni26, Definition 2.6.2]
   gives each `Ξ ∈ D_{B,j}` a natural-number code `⌜⌜Ξ⌝⌝`, one-to-one, which the map `Df` of
   [Kni26, Proposition 2.6.3, clause 5] keeps; here the cells are the positions `Fin card`, and
   `Scheme` has no code accessor, so printed domains that differ only in their codes correspond to
   the same scheme, and the face maps of row 8 are compared on positions.  Bountifulness is
   `IsBountiful`, the printed definition at every stage that is zero or a limit; at `ω₁` only the
   implication from `IsBountiful` is proved (row 6, S).  This difference is neither a recorded
   correction nor proved equivalent, so it is recorded as S in the status of this row and of the
   rows whose clauses use domains (rows 8 and 11): their identifications hold over legal schemes,
   and a coded scheme that is a domain as printed at `ω₁` but not at some other stage that is zero
   or a limit would not be legal.  Two routes make this row plain C and rows 8 and 11 plain P:
   (a) the converse at `ω₁` of row 6 for coded rows, `PrintedBountiful ω₁ → IsBountiful`; or
   (b) recording the requirement at every stage as part of the correction of this row, with its
   reason stated (the steps of the construction that use bountifulness at the stages `α < ω₁`);
   without a stated reason, (b) would only relabel the part still to be proved.  The points are
   `Fin n`, the ground set all of them.
8. `StageType`, `StageType.IsLegal`, `StageType.restrictFace` (`Stage/Basic`, `Stage/Legal`), `none`
   at invisible faces.  The definition-level identifications of `Correspondence/StageType`, compiled
   in this repository (theorem named).  Types, [Kni26, Definition 3.1.1]: the clauses are the fields
   of `Scheme.PrintedType` (a plan on the points, a domain on it, labels at the stage `α`, respect
   of the semantics); for `α ≤ ω₁` a labelling is a type as printed exactly when the scheme is legal
   and the labelling is a lawful section with labels at stage `α`
   (`Scheme.printedType_omega_one_iff`; at a general stage `Scheme.printedType_iff`), so a stage
   type is legal exactly when its scheme and labels are a type as printed
   (`StageType.isLegal_iff_printedType`), and the legal stage types correspond to the types as
   printed by forgetting the laws (`StageType.legalEquivPrintedType`).  Face maps,
   [Kni26, Definition 3.1.5]: the clauses are the fields of `StageType.PrintedFaceMap` (definedness
   at `ran f ∈ P`; the plan `(Pf)(P)` of [Kni26, Definition 2.1.9]; the map `Df` of
   [Kni26, Proposition 2.6.3, clause 5] on cells, scopes, arities, and rows; the labels); the face
   map is `u` exactly when `u` is a printed face map with its cells numbered in increasing order
   (`StageType.restrictFace_eq_some_iff_exists_printedFaceMap`), and it is undefined exactly when
   `ran f ∉ P` (`StageType.restrictFace_eq_none_iff`); the laws of the definition are
   `StageType.restrictFace_refl`, `StageType.restrictFace_trans_of_bind_eq_some`
   (`S^α (f ∘ g) ⊇ (S^α g) ∘ (S^α f)`), and, along bijections, `StageType.reindex_reindex`.  Basis
   of P: the clauses use the domains of row 7 (C, with bountifulness at `ω₁` S, row 6; the field
   `Scheme.PrintedType.domain` is the corrected definition), respect (row 4, P), and the coding of
   row 7; through row 6 the types are identified over legal schemes only, so the status is
   `P; domains: S (row 6)`.  Departures, recorded with the module: the points `Fin n`; the stage `α`
   unrestricted (harmless: the identifications hold for every `α ≤ ω₁`, limit or not); `⇒` at a
   stage `θ`, printed at `ω₁`; the scheme of a type carried as data; and the codes of the cells
   forgotten, part of the correction of row 7.  The printed `Df` keeps the code `⌜⌜Ξ⌝⌝` of each
   cell; neither `Scheme` nor `StageType.PrintedFaceMap` has a code accessor, so the preservation
   of codes is not compared.  The strict monotonicity of the positional map `φ` (`StrictMono φ`) is
   the convention that numbers the cells of the face in the increasing order of the positions of the
   corresponding cells of `t`; it preserves the order of the enumeration, not codes (a one-cell
   domain with code `5` and one with code `7` both have the identity `Fin 1 → Fin 1` as positional
   map).  The face maps are identified with the printed ones under this renumbering of the cells of
   `D'` by positions, and the status above holds on that convention.  The stage types have fixed
   coded rows (row 9); in
   [Kni26, Definition 3.1.1] too the semantics is the one associated with the domain.
9. `StageType` (a `Scheme` with fixed coded rows and a separate `label`); the correction is
   recorded in `README.md`, layer 2, "The templates of [AFK26] and the stage types here".  It is
   carried by theorems compiled in this repository (theorem named), `Correspondence/Template`: the
   printed template as `Correspondence.Template`, one field for each clause of Definitions 4.4–4.6
   (the frame conditions of Definitions 4.2 and 4.4 as `Correspondence.IsFrame`, with the plan of
   Definition 4.1 as `Geometry.IsPlan`, whose comparison with that definition is not recorded),
   the well-formed cell schemes of the stage types being exactly the frames with finitely many
   cells and positive grades (`Correspondence.isWellFormed_iff_isFrame`; a printed graded face
   allows the grade `0`),
   the coherent local rows `r_d(e) = min(p(e), p(d))` (`Correspondence.coherentRows`), the labels
   from the diagonal (`Correspondence.diagonal_coherentRows`), both round trips between lawful
   labellings and coherent row systems (`Correspondence.lawfulRowsEquiv`,
   `StageType.toTemplate_ofCoherentRows`, `StageType.ofCoherentRows_toTemplate`,
   `StageType.eq_of_toTemplate_eq`), compatibility with projection
   (`StageType.toTemplate_reduce`: entrywise reduction, the printed truncation of Definition 4.10)
   and with restriction (`StageType.coherentRows_comap`, with `StageType.restrictFace_eq_none_iff`
   for undefined faces).  Item 1, still to be proved: the fidelity question of `README.md`,
   item 1 (whether the legal templates of Definition 4.27, with the lawful local labellings and
   bountiful rows of Definition 4.26, are the coherent ones; not compared here).
10. `StageType.reduce`, on labels only, coherent by `StageType.reduce_reduce` (`Stage/Basic`).
11. `Realization`, `Realization.IsModel` (`Realization/Model`).  The definition-level identification
    `Realization.printedModel_tupleEval_iff` (`Correspondence/Model`), compiled in this repository
    (theorem named): at a stage `α ≤ ω₁` that is zero or a limit, a realization, read on all finite
    tuples (`Realization.tupleEval`), satisfies the printed clauses, the fields of
    `Realization.PrintedModel`, exactly when it is a model; its two directions are
    `Realization.PrintedModel.isModel` and `Realization.IsModel.printedModel`.  The fields keep the
    printed guards and the printed order of the quantifiers: the nonempty carrier; clause 1 in two
    parts (undefined at a repeated entry; a type in `S^α n`, row 8); clause 2 (`S^α f` of row 8,
    defined or not); clause 3 (`a⌢x`); and clauses 4(a)i, 4(a)ii, 4(b), and 4(c), each with its
    parameters and guards (a domain `D` with `D⟨n,n⟩ = dom p`; a labelling `q'` respecting the
    semantics of `D` with `q'↾dom p = p`; `γ` not a successor with `0 ≤ γ < α`; `γ < α`) before `y`
    and `q`.  A set `U` of clause 4 is read as the members of `(S^α ι_{n,n+1})⁻¹(p)` satisfying the
    condition of its kind, the manuscript's own reading: [Kni26, Lemma 4.4.1] states that every such
    `U` is nonempty, and [Kni26, Lemmas 4.4.2 and 4.4.3] prove it as "some `q` with `q_a = p`
    satisfies the condition of the kind".  Every printed clause is met by the identification.
    Departures, each proved equivalent at those stages by named theorems: realizations evaluate only
    injective tuples (`Realization.tupleEval_ofTupleEval`, `Realization.ofTupleEval_tupleEval`); the
    conclusions of clause 4 in `IsModel` omit `(S^α ι_{n,n+1})⁻¹(p)`
    (`Realization.RealizesOver.inter_cofaces`); the guards of clauses 4(a)i and 4(a)ii in `IsModel`
    are the nonemptiness of the family among the cofaces
    (`StageType.nonempty_cofaces_inter_saturationFamily_iff`,
    `StageType.nonempty_cofaces_inter_bottomPatternFamily_iff`, with
    `Scheme.map_univ_mem_faces_of_comap_eq` for `D⟨n,n⟩ = dom p`); covering by faces instead of
    initial segments (`Realization.isCovering_iff_exists_castAdd`); and the labelling of clause
    4(a)ii unrestricted in `IsModel` (`StageType.nonempty_cofaces_inter_bottomPatternFamily_iff`).
    Basis of P: the clauses use the domains of row 7 (C, with bountifulness at `ω₁` S, row 6), the
    types and face maps of row 8 (P, with the codes of the cells forgotten and the cells of a face
    numbered by positions, the convention of row 7, so clause 2 is compared on that convention),
    and respect (row 4, P); through row 6 the identification is
    over legal schemes, both for `S^α n` in clause 1 and for the domains `D` of clause 4(a), so the
    status is `P; domains: S (row 6)`; the four families are written out in the fields, so row 12,
    which compares two declarations of this repository, is not a prerequisite.
12. `baseLanguage.fourFamilySentence`; `baseLanguage.realize_fourFamilySentence_iff`
    (`Language/Satisfaction`), compiled in this repository (theorem named): the sentence holds
    exactly when the realization of the structure is a model at `ω`.  It compares two declarations
    of this repository; the correspondence with clause 4 goes through row 11.
13. The fidelity theorem,
`baseLanguage.realize_densitySentence_iff_fourFamilySentence_of_hasFiniteCutReceiving_of_capToModel`
    (`Language/Density`), compiled in this repository (theorem named), conditional on (R1) and the
    cap-to-model theorem, both still to be proved; the four-family side rests on row 12.
14. Definition-level identification (`Correspondence/InvariantSystem`, with the comparison of the
    clauses recorded there): Convention 2.3 as `GeometrySignature`, Definitions 2.1 and 2.2 as
    `IsGeometry` and `IsStructuredGeometry`, Definition 2.4 as `InvarianceDiagram`, Definition 2.5
    as `InvarianceDiagram.IsCompatible`, Definition 2.6 as `InvariantSystem`, and Definition 2.8 as
    `InvarianceDiagram.IsCompatibleWith`, one field for each printed clause; the maps `τ_β` of an
    invariant system are indexed, as printed, by the countable ordinals `β < ω₁` (the subtype
    `{β : Ordinal // β < ω₁}`), so a system is determined by its maps at the printed indices
    (`Correspondence.InvariantSystem.ext`, compiled in this repository (theorem named)); P for these
    printed definitions, every notion their clauses use being P (Definition 2.2, Convention 2.3):
    the definitions are generic in the signature `σ : GeometrySignature L`, so the invariants of an
    instance do not enter them.  Definition 2.7 (the projection of a structure and its rank) and
    Lemma 2.9 (projections preserve compatibility): not compiled.  For the base language and the
    realizations, compiled in this repository (theorem named), with the diagram supplied here: the
    invariance diagram of the legal stage types at stage `ω₁` with the base relations at `ω`
    (`Correspondence.stageDiagram`) satisfies each clause of Definition 2.4, the projections to the
    block stages (`Correspondence.blockSystem`) each clause of Definition 2.6, and they are
    compatible (`Correspondence.isCompatibleWith_blockSystem`); the compatible structures are
    exactly the structures of the exactly consistent covering realizations with legal types at
    stage `ω₁`, by literal mutually inverse maps
    (`Correspondence.isCompatible_iff_exists_toInvariantStructure_eq`,
    `Correspondence.toRealization_toInvariantStructure`,
    `Correspondence.invariantLanguage.toInvariantStructure_toRealization`), with the base relations
    of the reduction to `ω` (`Realization.relMap_base_iff`); the relations of [AFK26] have positive
    arity, so no nonemptiness clause enters.  Corrected (C), Definitions 4.17, 4.18 and
    Lemma 4.19: the printed diagram of the templates (Definition 4.18) has the templates as its
    invariants, ranges over all templates `t` (not only `t ∈ T`), and has a clause for an order
    symbol `≤`, carried over from the diagram of trees (Definition 3.6), that is not a symbol of
    the language of templates (Definitions 4.15 and 4.17); the diagram of the legal stage types is
    supplied in its place.  The two diagrams are not compared clause by clause because their
    invariants differ: such a comparison needs the identification of the templates with the legal
    stage types, which is row 9, item 1, still to be proved.  The clause map, recorded for that
    comparison: the clause for `≤` has no counterpart; the clause "`P_k`, distinct places, a closed
    set" is `InvariantSymbol.HoldsAt` at `closed` through `StageType.restrictFace` (defined exactly
    when the places span a face, `StageType.restrictFace_eq_none_iff`); and the clause "`Q_{t*}`
    or `R_{t*}`, with `t*` isomorphic to a renaming of the restriction of `t`" is `HoldsAt` at
    `invariant` and at `base` through `restrictFace`, with the base relations at `ω` in place of
    `R_{t*}`.  The base relations are the types at `ω`, fixed by the printed `τ_1` as in the proof
    of Lemma 4.22; Definition 4.17 prints `L_c` as `L_a` with the symbols `R_t` of the templates
    fixed by `τ_ω` (labels below `ω²`).  With that printed
    `L_c`, and the isomorphism of the third clause of Definition 4.18 read as preserving rows,
    Lemma 4.19 would fail at every finite index `β`: for a template `t` fixed by `τ_ω` with a label
    `λ`, `ω · β ≤ λ < ω²`, the pair `(Q_t, R_t)` is in the diagram and `(τ_β(Q_t), R_t)` is not
    (an informal observation; not compiled).  And the printed indexing is not compatible at the
    index `0`, and, with the diagram supplied here, only there
    (`Correspondence.not_isCompatibleWith_omega0MulSystem`,
    `Correspondence.isCompatibleWith_omega0MulMaxOneSystem`), so the block indexing of row 1 is
    used.  Earlier comparisons of two declarations of this repository: at `ω`,
    `baseLanguage.toStructure_toRealization`, `baseLanguage.toRealization_toStructure`,
    `baseLanguage.realize_structuralSentence_iff_toRealization`; for structures covered by top-free
    charts, at any stage, `reconstruct_toHullStructure`, `toHullStructure_reconstruct`.  The round
    trip in the stage chart language at a general fixed countable stage (`README.md`, item 2):
    prospective.
15. `Coatom.amalgam`, `Coatom.amalgamType` (`Extension/CoatomAmalgam`), from
    `Coatom.amalgamCellScheme` and `Coatom.amalgamRows` (`Extension/CoatomScheme`): the amalgam
    of two coatom types and its rows.  The status is given for Definition 4.3.1 (P) and for the
    three conclusions of Lemma 4.3.2 (C, P, S, in order), separately.
    - *Definition 4.3.1*, P.  The definition-level identification `Coatom.printedAmalgam_iff`
      (`Correspondence/Amalgam`), compiled in this repository (theorem named): a cell scheme with
      rows satisfies the clauses `D = D^a ∪ D^b` and `E = E^a ∪ E^b` (the fields of
      `Coatom.PrintedAmalgam`) exactly when it is `Coatom.amalgamCellScheme h` with
      `Coatom.amalgamRows h`, reindexed along a bijection of cells sending the cells of `D^a` and
      `D^b` to the given ones.  For the amalgam here: `Coatom.printedAmalgam_amalgam` and
      `Coatom.printedAmalgam_amalgamType`, compiled in this repository (theorem named).  The
      setting of [Kni26, §4.3]: `A = Fin (m + 2)`; the plan `Q ∪ R ∪ {A}` of Definition 2.1.1,
      clause 3(c), is `Coatom.amalgamFaces`; the equality of the restrictions of `D^a` and `D^b`
      to `⟨A \ {a, b}, n - 2⟩` (equivalently, as printed, `D^a_{⟨A \ {b}, n - 2⟩} =
      D^b_{⟨A \ {a}, n - 2⟩}`) is the hypothesis `h`, literal equality of the restricted schemes,
      with the codes forgotten and the common-face numbering preserved (the corrected
      representation of domains, row 7); the cells of the common face are identified by
      `Coatom.overlap h`.  Departures, both
      harmless by `Coatom.printedAmalgam_iff`: the merged enumeration of the cells of
      `Coatom.amalgam` (it holds for every bijection of cells), and the laws of `D^a` and `D^b`
      (it holds without them).  The definition uses no legality: it uses only the representation
      of domains of row 7, a scheme with its rows (the semantics as rows, row 7's notion), with
      the cells as positions and codes forgotten; its status is on that convention and does not
      depend on row 6.  The clause `eq_iff` is, in the direction "if", the equality of the two
      restrictions in the setting, and in the direction "only if", Proposition 2.6.3, clause 6.
      The labels of `Coatom.amalgamType` are those of the two types
      (`Coatom.amalgamType_label_posLeft`, `Coatom.amalgamType_label_posRight`); Definition 4.3.1
      does not mention them.
    - *Lemma 4.3.2, "`D` is a domain"*, C: not correct as stated.  A domain has a complete
      semantics (Definitions 2.6.1 and 2.5.15; `CellScheme.IsComplete` is Definition 2.5.15
      verbatim), and the graded face `⟨A, 1⟩` of the plan carries no cell:
      `Coatom.not_isComplete_amalgamType` and `Coatom.not_isLegal_amalgamType`, compiled in this
      repository (theorem named).  The corrected statement, compiled in this repository (theorem
      named): every other graded face carries a cell (`Coatom.exists_gradedIndex_eq_amalgamType`),
      and the scheme is well formed and coded (`Coatom.isWellFormed_amalgam`,
      `Coatom.isCoded_amalgam`).  The end of [Kni26, §4.2] calls the union "consistent
      and bountiful; it is merely not complete".  `LITERATURE.md` does not yet list this
      conclusion among the printed statements that are not correct as stated; it is to be added
      to that list when the list is next brought up to date.
    - *Lemma 4.3.2, "`E` is a consistent semantics"*, P: `Coatom.printedRespects_row_amalgam`,
      compiled in this repository (theorem named).  At every stage that is zero or a limit and
      carries the values of the rows, if every row of `D^a` and of `D^b` respects the semantics
      below it as printed (Definition 2.5.12, through row 4), so does every row of the amalgam;
      respecting includes the orderliness that a semantics requires (Definition 2.5.3).
    - *Lemma 4.3.2, "`E` is bountiful"*, S: it rests on row 6.  Compiled in this repository
      (theorem named): `Coatom.isBountiful_amalgamType`, in the sense of `IsBountiful`;
      `Coatom.printedBountiful_omega_one_amalgamType`, the printed definition at `ω₁` for the
      amalgam of legal stage types (whose rows are bountiful in the sense of `IsBountiful`); and
      `Coatom.forall_printedBountiful_amalgam`, the printed definition at every stage that is zero
      or a limit, from the same for `D^a` and `D^b`.  From the printed definition at `ω₁` alone
      for `D^a` and `D^b`, nothing is proved: that needs the converse of
      `CellScheme.Rows.IsBountiful.printedBountiful` at a single stage, which row 6 lacks.
16. The completion of checkpoints 2.1–2.7 replaces it; the bountifulness of the printed completion
    is unproved, not refuted.
17. `StageType.HasApexCoatomExtensions` (`Extension/PinnedExtension`), a hypothesis.
18. `StageType.exists_extension` (`Extension/PinnedExtension`), conditional on
    `StageType.HasCoatomExtensions`, still to be proved.
19. `StageType.nonempty_cofaces_inter_uniformityFamily` and
    `StageType.nonempty_cofaces_inter_dominanceFamily` (`Extension/FamilyCofaces`), conditional on
    `StageType.HasCoatomExtensions` and `StageType.HasApexCoatomExtensions` respectively, both
    still to be proved.
20. The classical limit of the uncapped age (`README.md`, the section on the top-free witnesses):
    prospective.
21. `Realization.IsModel.exists_privateContext` (`Realization/PrivateContext`); status S.  Only
    clauses 3 and 4 of Lemma 8.1.1 are compared; clauses 1 and 2 (the hollow case) are not.
    Clauses 3 and 4 are the fields of `Realization.PrintedPrivateContext`
    (`Correspondence/PrivateContext`), with the cells `Ω_μ` of clause 3 as data, since clause 4(d)
    refers to them.  Compiled in this repository (theorem named):
    `Realization.IsModel.exists_printedPrivateContext`, derived from the conclusion of
    `exists_privateContext`.  For a model at a positive stage (the printed stage is a limit),
    every occurrence `x`, every donor on `x.arity + 1` points, and every `K`, it gives an
    extension meeting clause 3 and, with `N` the arity of the extension, the bounds (a)–(d) of
    clause 4 ((b) for the given `K`) and a cell `Ω` of full scope and arity `N` labelled above
    every label of the donor below `∞`.  Not met: the alternative of clause 4 for infinite
    characteristic arity, `p'(Ω) = ∞`; the characteristic arity (Definition 5.4.1) has no
    counterpart here.  Departures: `x` is a literal face of the extension along an embedding, not
    an initial segment (not proved equivalent here); the hypotheses of Proposition 7.3.3
    (hollowness or finite characteristic arity, a core, the donor extending the type of `x`) are
    not assumed (harmless: `Realization.IsModel.exists_printedPrivateContext` holds without
    them).  Clause 3 and the structure concern limits `μ` only; the conclusion of
    `exists_privateContext`, which treats every block start, also gives a cell with label in
    `[0, ω)` when some label of the donor lies there, outside the comparison.  The row stays S
    for three reasons: clauses 1 and 2 are not compared; the alternative `p'(Ω) = ∞` of clause 4
    is not produced; and the literal face is not proved equivalent to the initial segment.  The
    printed proof of clause 4 cites high-arity dominance as clause 4(a) of Definition 3.2.1, where
    it is clause 4(c) (`LITERATURE.md`): a correction of the citation that does not affect the
    statement; the proofs here use uniformity, clause 4(b), and high-arity dominance, clause 4(c)
    (`Realization.IsModel.uniformity`, `Realization.IsModel.dominance`).
22. Prospective (`README.md`, layer 3, 3.3).
23. The corrected statements are those of the version of 1 October 2026 (its Definitions 3.2
    and 3.4: the composition law in one order, which does not give nested ranges, and a single
    exclusive partition by invariants holding both a full invariant and its projections), replaced
    by `FullPresentation.LevelObservations`, `FullPresentation.ObservedPresentation`
    (`Comparison/GradedMatchingApplications`): separate level sets, explicit projections; the
    correction is recorded in `LITERATURE.md`, §9.  The current Definitions 2.2 and 2.6 are P
    (row 14): Definition 2.6(c) has the composition law in both orders, and the projection of a
    structure is a separate structure (Definition 2.7, not compiled); the disjunction of
    Definition 2.2(b), over `ℵ₁` invariants for the stage types, is transcribed by its
    satisfaction, not as a sentence of `L_{ω₁,ω}`.
24. InfinitaryLogic's `BFEquiv` with a specified initial match;
    `FullPresentation.bfEquiv_comp_of_obs_eq`.  Corrected against the version of 1 October 2026
    (its Definition 4.1 and Theorem 4.2: the same full invariant at every level, every family of
    matches allowed to be empty), which the current Definition 2.16 no longer has (its last family
    is nonempty, and its matches are closed tuples with the same relations of `L_c`).  Corrected
    against the current text: the systems of Definition 2.16 have no starting match (the empty
    tuple is not closed, as the remark after the definition says); a specified starting match is
    used here, and the conclusion of Theorem 2.17 is read for these systems.  Both corrections are
    recorded in `LITERATURE.md`, §9.
25. Prospective; ingredient `StageType.reduce_eq_of_mem_receivingFamily` (`Realization/Expansion`).
26. `ExpansionMatchData.bfEquiv_of_expansionMatch`; `Expansion.bfEquiv_of_modelExpansions` and,
    from an arbitrary common chart, `ModelExpansion.bfEquiv_comp_of_covers` and its formula form
    `ModelExpansion.realize_comp_iff_of_covers`, conditional on
    `Expansion.FiniteExtensionReceiving`, still to be proved; the structural form: prospective.
27. `FullPresentations` (`MainTheorem/Assembly`), a structure of hypotheses storing sets of classes
    at levels with countability and coverage, not presentations or maximality; and
    `vaughtCounterexample_of_presentations` (`MainTheorem/Assembly`), whose hypotheses include it.
    The class–level incidence translation and the three properties it must preserve (incidence of
    classes at levels, countability of levels, coverage) are those of item 5; until they are
    proved, `FullPresentations` stays prospective as an instance of the system of [AFK26].
    Countability of levels, read with terminal model expansions of codes in place of maximal
    presentations, is `MainTheorem.countable_isoClasses_terminalAt`
    (`MainTheorem/TerminalClasses`), compiled in this repository (theorem named),
    conditional on (R1), `ContinuationCriterion`, (R2), and (R3), each still to be proved.
28. What is corrected is a statement of the version of 1 October 2026: the same-index
    equivalence of full trees (its Proposition 8.6) is false (an informal counterexample,
    `LITERATURE.md`, §9; not compiled); it is absent from the current version.  The current
    Definition 3.10 (the `β`-full trees, followed by an extension lemma for full trees,
    Lemma 3.11) is cited to locate the notion and is not compared (S).  `COMPANIONS.md`, "Full
    trees": prospective.
29. The closed tuples of [AFK26] (Definition 2.1: the tuples satisfying `P_n`), in the structure
    of an exactly consistent realization (row 14), are the injective tuples whose set of points is
    a support (`Realization.relMap_closed_iff_isSupport`), equivalently, under covering, a finite
    closed set of the canonical closure (`Realization.relMap_closed_iff_isClosed`), both in
    `Correspondence/InvariantSystem`, compiled in this repository (theorem named).  Ingredients:
    `Realization.isSome_eval_iff_isSupport` (`Realization/Hull`), `Realization.isClosed_coe_iff`
    and `Realization.isClosed_iff_of_finite` (`Realization/Closure`); stage reduction keeps typed
    and untyped tuples (`Realization.isSome_reduce_eval`, `Realization/Transport`) and the closure
    (`Realization.closure_reduce`, `Realization/Closure`).  Milestone 1 of the uniform fixing
    bounds (`README.md`, item 5).
30. Niceness of a tuple and of a base structure ([AFK26, Definition 2.19], in the numbering of the
    current draft): `IsNiceTupleAt` (one field for each of its two clauses), `IsNiceTuple` and
    `IsNice` (`MainTheorem/Niceness`), read in the raw base encoding: the lifts at `α` are the model
    expansions at `λ_α`, the closed tuples the supported tuples of positive arity of the
    realization of the base at `ω` (row 29), and the invariant at a higher stage is compared by
    `StageType.castLE`.  The empty tuple is excluded: it is supported in every base structure with
    a lift, but not closed in [AFK26] (Definition 2.1 has `P_n` only for `n ≥ 1`).  Positive
    niceness for the base reduct of every model at a block stage on a countable carrier, with one
    threshold `ρ` for all closed tuples and the invariant of each in a lift at `ρ` as the actual
    witness: `exists_isNiceTupleAt_of_hasTerminalRefinement`, `isNice_of_hasTerminalRefinement`, and
    `Realization.IsModel.isNice_toStructure_reduce` (condition (c) of [AFK26, Definition 2.22]),
    compiled conditional on `HasTerminalRefinement.{w}` (row 38) and
    `Expansion.NextBlockUniqueness.{w}`; at `w = 0`, the refinement is derived from (R1),
    next-block uniqueness, and the countable-block apex property, each still to be proved.
    Status S: the hypotheses and the identification of the lifts with those of [AFK26] are still
    to be proved (the first row of the table of item 5); the closed-tuples comparison is recorded
    in row 29.  No declaration of this repository names
    a fixing rank.  Milestone 2; it is the row "invariance over all admissible presentations, with
    an inhabited threshold" of the table of item 5.  For the models here it is derived from a
    terminal presentation of each base, which supplies it immediately by terminal collision and the
    injectivity of model reduction (the inequality step of row 35, then 5 ⇒ 1 of row 34), with no
    further stabilization argument.  The terminal presentations come from either of two distinct
    stopping proofs, both prospective: (i) the countable-slot argument (the termination argument of
    [AFK26]), or (ii) the Scott route of row 40.  For (i), "countably many slots, each used at most
    once" alone does not establish even the stopping half of global termination.  A proof along it
    is to supply (a) which events use a slot, (b) why every relevant continuation uses a fresh slot,
    and (c) why exhausting those events yields an actual terminal presentation; countably many
    events may still continue through a countable limit, whose supremum is not by itself an
    attainment or a terminality proof.  That its conclusion is eventual departure, the stopping half
    of global termination (`README.md`, "The persistent core"), and not terminal fullness, which is
    the first special statement, is prospective, to be supplied by (a)–(c).  Neither may use
    positive niceness, and neither is a dependency of the expansion-domain endpoint.
31. Prospective: no declaration of this repository states it.  Its ingredients for labels are
    compiled in this repository (theorem named): `Label.reduce_eq_self_iff` (fixed by projection
    exactly at the labels of the stage), and `Label.reduce_reduce_of_le`, `Label.atStage_reduce`
    and `Label.AtStage.mono` for the law with `min` (`Label/Basic`).  The bound for one arity is
    `StageProjection.exists_uniform_fixing_stage` (available at the pin `e460cb6`, signatures
    checked; "Dependency pins").  Milestone 3; the conditional statement uses no termination.
32. Its strictness half is compiled in this repository (theorem named), with no hypothesis
    beyond modelhood: a model at `λ_η` is fixed by projection at the index `ξ` exactly when
    `η ≤ ξ` (`Realization.IsModel.isFixedAt_blockStage_iff`, from
    `Realization.IsModel.not_isFixedAt`, the uniformity clause at `γ = λ_ξ`;
    `Realization/Strictness`), so the least fixing index of a model's whole assignment is its index
    (`Realization.IsModel.isLeast_isFixedAt_blockStage`) and every family of models is strict
    (`Realization.isStrict_of_forall_isModel`, `Realization.isStrict_isExpansionOf`).  The bound
    of serving indices under strictness is compiled for families of realizations at the block
    stages on one carrier (`Realization.IsStrict.le_of_forall_isFixedAt`,
    `Realization.le_of_forall_isModel_of_forall_isFixedAt`).  The negative special case (the
    constant family of the all-undefined assignment) is compiled
    (`Realization.StrictnessExamples.not_isStrict_undefinedFamily`).  Strictness does not use
    `COMPANIONS.md`, "Fixing ranks of finite charts".  The row stays S: its application to the
    uniform fixing stage of the construction (milestone 3) and the identification of these
    statements with those of [AFK26] are still to be proved.  Milestone 4.
    The row is required for item 5, whether or not the main theorem uses a bound of serving
    indices: the completion criterion of item 5 asks every row of the item to be P or C, so
    matching the manuscript needs milestone 4.
33. In the raw base encoding, a maximal presentation of a base structure `M` is a model expansion
    of `M` at `λ_ρ`, `ρ < ω₁`, such that `ρ` bounds the serving indices of `M`
    (`BoundsServingIndices`, `MainTheorem/Niceness`: every countable index at which `M` has a
    model expansion is at most `ρ`).  In the common invariant encoding no declaration of this
    repository states a model presentation of a literal base or its maximality (`README.md`, item
    5, "Maximal presentations: equivalent criteria, uniqueness, the optimal bound").  Related
    declarations, none of them this notion:
    `Realization.IsTerminalAt` with `Realization.isTerminalAt_iff_forall_lt`
    (`Continuation/Terminal`), terminality at a block, which a maximal presentation has; in the raw
    base encoding, `Realization.IsExpansionOf.isTerminalAt` (same module), compiled in this
    repository (theorem named): with no model expansion at the next block, every expansion is
    terminal; and `FullPresentations`, with `presentedAt`, on `DensityClass`
    (`MainTheorem/Assembly`), the class–level incidence of row 27, which stores no presentation.
    The conversion between the raw base and the common invariant encodings: prospective.  In the raw
    base encoding, maximal (and terminal) model expansions of the base structure of a model on a
    countable carrier are compiled conditional on `Expansion.FiniteCutReceiving` ((R1)),
    `Expansion.NextBlockUniqueness`, and `StageType.HasApexCoatomExtensions` at every countable
    block stage, each still to be proved: `MainTheorem.exists_isGreatest_servingIndex` and
    `MainTheorem.exists_maximalRefinement_of_modelExpansion` (`MainTheorem/MaximalRefinement`).  The
    row stays S: the hypotheses are open, and the notion of the manuscript is read in the common
    invariant encoding.
34. Prospective.  1 ⇒ 2 is the uniform fixing stage of row 31 for the family of model
    presentations, through `StageProjection.exists_uniform_fixing_stage` (available at the pin
    `e460cb6`, signatures checked; "Dependency pins"), and is the only step using a countable
    carrier; 2 ⇔ 4 uses strictness for models (row 32; compiled,
    `Realization.IsModel.isFixedAt_blockStage_iff`); 4 ⇒ 5 uses bounded-stage attainment, whose
    ingredients are compiled in this repository (theorem named) in the raw base encoding:
    `Realization.IsModel.reduce` (`Realization/Model`), `ModelExpansion.nonempty_of_coherent`
    (`Realization/Limit`), and `ModelExpansion.nonempty_of_forall_lt` (`Expansion/Uniqueness`,
    conditional on `Expansion.NextBlockUniqueness`, still to be proved).  So 4 ⇒ 5, and with it the
    equivalence and that of 2–5 for arbitrary carriers, is conditional on the injectivity of model
    reduction (row 35), an explicit hypothesis until proved; 5 ⇒ 1 uses maximality and the strict
    threshold only, and is compiled in this repository (theorem named) in the raw base encoding,
    with no hypothesis: `isNiceTupleAt_of_boundsServingIndices` and `isNice_of_boundsServingIndices`
    (`MainTheorem/Niceness`).  4 ⇒ 5 is route (a) of milestone 5 of `README.md`, item 5, "Uniform
    fixing bounds from positive niceness", with the dependencies named there.  The equivalence
    characterizes termination for one base; it is not a separate proof of termination.  In the raw
    base encoding, 4 ⇒ 5 is compiled conditional on `Expansion.NextBlockUniqueness`, on any carrier:
    `MainTheorem.exists_isGreatest_servingIndex_of_le` (`MainTheorem/MaximalRefinement`), through
    `exists_isGreatest_of_closed` (`Counting/OrdinalAttainment`, Layer 0, no hypothesis).  That
    ordinal statement is not the same as the greatest-stage statements of `OrdinalUtil`
    ("Dependency pins", **Upstream statements quoted, not compiled here**), but follows from each:
    `exists_greatest_stage_lt_omega1` assumes `P 0` (here from `P β` by downward closure) and a
    bound `ξ ≤ A` only below `ω₁` (here `A = δ`), and concludes `P ξ ↔ ξ ≤ ρ`; the general forms
    `exists_forall_iff_le_of_bounded_of_isSuccLimit_closed` and
    `exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed` assume closure at every successor
    limit (here vacuous above `δ`, where `P` fails).  It is to be replaced by a quotation of one
    of them at a repin containing `c16de09` and `2cd44c3` ("Placement record").
35. Prospective, conditional on the injectivity of model reduction at each countable index (two
    model presentations of the base at one index are equal), an explicit hypothesis until proved.
    Both its steps use it: the inequality at `ρ` (terminal collision, which also uses
    `Realization.IsModel.reduce` and `Realization.isTerminalAt_iff_forall_lt`), the equality at
    `η`.  Its raw form at one block, in the raw base encoding, is `ModelExpansion.subsingleton`
    (`Expansion/Uniqueness`), compiled in this repository (theorem named), conditional on
    `Expansion.NextBlockUniqueness`, still to be proved, which is derived from (R1) and
    `ForcingDonors` by `Expansion.NextBlockUniqueness.of_forcingDonors`
    (`Expansion/UniquenessOfForcing`), compiled in this repository (theorem named); its limit
    step is `Realization.eq_of_forall_reduce_eq` (`Realization/Limit`).  That theorem compares two
    expansions at one block; it bounds no index and supplies no terminal presentation.  The
    terminality of the reconstructed top-free realization, `reduce_ne_reconstruct`
    (`ClassicalLimit/Modelhood`), compiled in this repository (theorem named), concerns the
    realization, not its base reduct.  In the raw base encoding, literal uniqueness (both steps) is
    compiled conditional on `Expansion.NextBlockUniqueness`, on any carrier:
    `MainTheorem.exists_le_reduceBlock_eq_of_isTerminalAt` (`MainTheorem/MaximalRefinement`).
36. Prospective.  It rests on row 32 (its strictness half compiled), on the inequality step of
    row 35 (so on the injectivity of model reduction at `ρ` only), and on `COMPANIONS.md`,
    "Fixing ranks are zero or successors"
    and "Limit heights are unattained suprema", each still to be proved.  No declaration of this
    repository names a fixing rank (row 30).  Its inequality step, in the raw base encoding, is the
    first component of `MainTheorem.exists_le_reduceBlock_eq_of_isTerminalAt` (row 35).
37. Prospective: no declaration of this repository states density at an observation (row 25) or
    its witness-bounded form.  The fixation of the returned invariant rests on
    `Realization.reduce_eval` and `Realization.isSome_reduce_eval` (`Realization/Transport`),
    compiled in this repository (theorem named); the equivalence with the donor-bounded form is
    stated on a realization fixed by projection at `β` and rests on the two-index theorem of
    row 25: the two are equivalent formulations of density there.  Exact face preservation is
    supplied separately by `Realization.IsConsistent` (`Realization/Basic`), clause 2 of
    `Realization.IsModel`, and is part of neither predicate.  It keeps the root and the realizing
    occurrence together and supplies no projected-donor lifting.
38. Compiled conditionally (the last sentences of this note).  Compiled in this repository
    (theorem named): `Realization.IsTerminalAt` with
    `Realization.isTerminalAt_iff_forall_lt` (`Continuation/Terminal`),
    `Realization.IsModel.reduce` (`Realization/Model`), and `Realization.IsModel.lt_omega_one`
    with `le_blockStage` (`Realization/Expansion`), which give `β < ω₁` before the given model is
    read as a model presentation (the planned route; the compiled form below does not use them).
    The terminal model is on the same carrier as the given model,
    not on an isomorphic copy.  A terminal presentation of the base comes from either stopping
    proof of note 30 (the countable-slot argument, or the Scott route of row 40, whose maximal
    presentation is terminal); literal-reduct uniqueness is row 35, conditional on the
    injectivity of model reduction.  Through the Scott route no global termination theorem is
    used; the stage index is not assumed countable.  Compiled conditional on
    `Expansion.FiniteCutReceiving` ((R1)), `Expansion.NextBlockUniqueness`, and
    `StageType.HasApexCoatomExtensions` at every countable block stage, each still to be proved,
    through the Scott route: `MainTheorem.exists_maximalRefinement`
    (`MainTheorem/MaximalRefinement`): a model `V` at `λ_β` on a countable carrier `X` is the stage
    reduction to `λ_β`, literally, of a model `W` at `λ_ρ` on `X`, `β ≤ ρ < ω₁`, terminal at `ρ`,
    and every model on `X` at a block stage `λ_η` with the base structure of `V` has `η ≤ ρ`;
    `β < ω₁` is derived from `β ≤ ρ`.  Maximality up to isomorphism of the base, on any carrier,
    follows by `MainTheorem.le_of_modelExpansion_of_equiv` (through `ModelExpansion.map`).
39. Prospective as a combined statement, which is not named, in two forms: carrier-general (a
    base structure on any carrier, with `ξ < ω₁` an explicit hypothesis) and coded (codes on
    `ℕ`, where `ξ < ω₁` follows from `Expansion.expansionDomain_eq_empty`).  Its ingredients are
    compiled in this repository (theorem named; `ModelExpansion.map` is a definition):
    `Expansion.mem_expansionDomain_iff` and
    `Expansion.expansionDomain_eq_empty` (`Expansion/Domains`), `ModelExpansion.map` and
    `ModelExpansion.val_eq_toRealization` (`Realization/Expansion`), and either
    `ModelExpansion.subsingleton` (`Expansion/Uniqueness`), conditional on
    `Expansion.NextBlockUniqueness`, still to be proved, or `ModelExpansion.eq_of_determines`
    (`Definability/BlockFormulas`), conditional on block determination.  None of them, and not
    `Expansion.NextBlockUniqueness` either, assumes a countable carrier;
    `Realization.IsModel.lt_omega_one`, which does, is not used.  The domain guard
    (`COMPANIONS.md`, "Quantitative reconstruction", second row) is prospective.  Recorded with
    it (`Definability/BlockFormulas`): `blockFormula`, `qrank_blockFormula_le` (no hypothesis),
    and, conditional on block determination, `realize_blockFormula_iff`,
    `ModelExpansion.relMap_toChartStructure_iff`, and `ModelExpansion.map_eq_of_determines`.  No
    new structure of hypotheses is introduced.
40. Steps 1–5 compiled conditionally (the last sentences of this note).  The second stopping
    proof of note 30.  Scott isolation for one class, at the
    pin: `stabilizationOrdinal_spec` with `stabilizationOrdinal_lt_omega1'` (signatures
    checked), or `scottSentence_characterizes` with `scottFormula_qrank_le` and
    `BFEquiv_implies_agreeQR` (signatures checked), the latter form also using
    `stabilizationOrdinal_lt_omega1'` for the hypothesis of `scottFormula_qrank_le`;
    `BFEquiv.monotone` lowers the level (available at the pin, signatures not yet checked by
    CI).  `SuggestedInterfaces.lean` `#check`s `stabilizationOrdinal_spec` and
    `stabilizationOrdinal_lt_omega1'`.  The isolating level of a countable family
    (`exists_isolating_level`, `Scott/IsolatingLevel`, available at the pin `e460cb6`, signatures
    checked; "Dependency pins") is not used.  Comparison: `Expansion.bfEquiv_of_modelExpansions`,
    and its agreement form on
    the sentences of quantifier rank at most `β`, `Expansion.mem_modelsOf_iff_of_modelExpansions`
    for codes or `Expansion.realize_iff_of_modelExpansions` for any carriers, each conditional on
    `Expansion.FiniteExtensionReceiving`.  Losses: `hasNonemptyLosses_of_hasApexCoatomExtensions`,
    conditional on `CapToModel`, `StageType.HasApexCoatomExtensions`, and
    `Expansion.NextBlockUniqueness`.  From the base to a code on `ℕ`: the conversion between the
    two encodings (still to be proved), the density sentence for the base structure
    (`realize_toStructure_densitySentence_iff`, with (R1)), `CapToModel.infinite` and
    `exists_mem_modelsOf_densitySentence_equiv_of_capToModel` (`MainTheorem/Assembly`,
    conditional on `CapToModel`), `ModelExpansion.map`, and `Expansion.mem_expansionDomain_iff`.
    Attainment: `Realization.IsModel.reduce` and `ModelExpansion.nonempty_of_forall_lt`, the
    latter conditional on `Expansion.NextBlockUniqueness`.  These are compiled in this repository
    (theorem named; `ModelExpansion.map` is a definition), except the library statements and the
    conversion; their hypotheses are still to be proved.  Positive niceness (5 ⇒ 1 of row 34) is
    prospective; the strict bound and the attainment are compiled conditionally (below).  The
    route proves stopping for each base that is a model as its conclusion and assumes no
    termination; it is not a dependency of the expansion-domain endpoint and is not combined with
    the conditional of row 31 in a cycle.
    The maximal presentation it yields at `ρ` is terminal.  Read in the coded encoding (through
    the conversion, still to be proved), the class of the base lies in the loss at `ρ`
    (`Expansion.mem_expansionDomain_iff` with `ModelExpansion.map`), hence among the classes
    terminal at `ρ` (`MainTheorem.loss_subset_terminalClasses`, unconditional), of which there
    are countably many at each countable level (`MainTheorem.countable_isoClasses_terminalAt`,
    compiled in this repository (theorem named), conditional on (R1), `ContinuationCriterion`,
    (R2), and (R3), each still to be proved); the loss alone is already countable under the same
    hypotheses (`Expansion.expansionDomain_loss_countable`).  The terminality of the presentation
    itself transports to the code along the isomorphism (`Realization.IsTerminalAt.map`,
    unconditional).
    Steps 1–5, in the raw base encoding, are compiled
    conditional on `Expansion.FiniteCutReceiving` ((R1)), `Expansion.NextBlockUniqueness`, and
    `StageType.HasApexCoatomExtensions` at every countable block stage, each still to be proved
    (`MainTheorem/MaximalRefinement`): the isolating sentence `MainTheorem.exists_isolates` (the
    Scott sentence, through `scottSentence_characterizes`), of quantifier rank below `ω₁`
    (`MainTheorem.qrank_lt_omega_one`, `MainTheorem/Spectrum`); two classes in each countable
    domain, `MainTheorem.expansionDomain_nontrivial` (per block,
    `nonempty_loss_of_hasApexCoatomExtensions` at `δ` and `δ + 1`, without `CapToModel`); the
    subsingleton domain `MainTheorem.expansionDomain_subsingleton_of_isolates` and the strict bound
    `MainTheorem.lt_qrank_of_isolates`, with the agreement taken between the base structure on its
    own carrier and the codes of the classes of the domain
    (`Expansion.realize_iff_of_modelExpansions`), so that neither the conversion between the
    encodings nor a code of the base is used; the attainment
    `MainTheorem.exists_isGreatest_servingIndex`; and the terminal refinement of row 38.  The bound
    is the quantifier rank of the chosen isolating sentence, not a Scott rank.  Positive niceness
    and the forms in the common invariant encoding are prospective.
41. `Label.visibilityReplace`, `Label.IsSelfVisible` (`Label/Visibility`).  The correction,
    recorded in `Correspondence/Current/Visibility`: the printed clause sends `ω · α + n` to the
    natural number `i` or `n`; it is read as `ω · α + i` or `ω · α + n`, the operation of
    [Kni26, Definition 2.2.3] (row 2).  Read literally, the image of every ordinal is finite
    (`Label.PrintedVisibilityMap.apply_coe_lt_omega0`), no ordinal `≥ ω` is self-visible
    (`Label.PrintedVisibilityMap.apply_ne_self`), and the map is not visibility replacement
    (`Label.PrintedVisibilityMap.ne_visibilityReplace`).  The corrected clauses
    (`Label.CorrectedVisibilityMap`) are visibility replacement on the labels at the stage
    (`Label.correctedVisibilityMap_iff`; on `{-∞} ∪ ω₁ ∪ {∞}`,
    `Label.correctedVisibilityMap_omega_one_iff`), self-visibility is `Label.IsSelfVisible`
    (`Label.CorrectedVisibilityMap.apply_eq_self_iff`), the printed domain `α ∈ ω₁` is that of the
    stage `ω₁` (`Label.omega0_mul_add_natCast_lt_omega_one_iff`), and the definition of [Kni26] is
    the corrected one at every stage
    (`Label.printedVisibilityReplace_iff_forall_correctedVisibilityMap`); all compiled in this
    repository (theorem named).
42. `Label.PrintedTransformsTo` (row 3), that is `Label.TransformsTo`.  The printed relation
    (`Label.PrintedFrameWitness`, `Label.PrintedFrameTransformsTo`,
    `Correspondence/Current/Transform`) has no monotonicity clause for the shifter.  The
    corrections: clause 4 of [Kni26, Definition 2.3.9] (monotonicity) restored; "visible at `k`"
    read as self-visibility (Definition 4.24); the visibility map that of row 41.  Compiled in
    this repository (theorem named): the two printed witnesses differ exactly by monotonicity
    (`Label.printedWitness_iff_printedFrameWitness`); the relations of [Kni26] and of this
    development give the printed one (`Label.PrintedTransformsTo.printedFrameTransformsTo`,
    `Label.TransformsTo.printedFrameTransformsTo`); and the omission is not harmless: at `ω₁` the
    printed relation reverses the order of two labels of grade `1`, which neither of the others
    does (`Label.exists_printedFrameTransformsTo_not_transformsTo`).
43. `CellScheme.Rows.IsLawfulBelow` (`Scheme/Row`).  The definition-level identification
    `CellScheme.Rows.printedLawfulLocal_iff`, at every stage that is zero or a limit, and
    `CellScheme.Rows.printedLawfulLocal_omega_one_iff`, on the printed labels
    (`Correspondence/Current/LocalLabelling`), compiled in this repository (theorem named); the
    clauses are the fields of `CellScheme.Rows.PrintedLawfulLocal`.  *The reading* (rows 43–47):
    the row system `Σ` of a template is the fixed semantic rows `R : D.Rows` of a cell scheme.
    This is not the representation of item 1 and row 9, in which a labelling `p` is represented
    by its coherent local rows `min(p(e), p(d))`; the two readings make different objects legal
    (under the coherent-rows reading clause 4 of Definition 4.27 would forbid `⊤` and labels
    `≥ ω ^ 2` in `p`, note 45), and which one [AFK26] intends is part of the fidelity question of
    item 1.  The identification holds for every row system, so the status P does not depend on
    the reading.  Departures: the cell `e'` of Availability ranges over `D` but is read in `D↓U`
    (`CellScheme.mem_below_of_gradedIndex_eq`); `D↓d` is computed in `D` (transported along a
    bijection in the proof of the identification); the range of the labels, as in row 3.  The
    notions the clauses use: self-visibility (row 41, C), the relation `⇒` (row 42, C), and the
    frame, row system, graded faces, and cells below a graded face of [AFK26, Definitions 4.2 and
    4.4–4.6], transcribed literally (the frame is the gradings of a `CellScheme`, the row system
    is `D.Rows`), with `CellScheme.below` and the printed graded faces
    `CellScheme.printedGradedFaces` (grade `0` allowed; `CellScheme.mem_printedGradedFaces_iff`;
    lawfulness is defined below every pair).  The definition of [Kni26] (row 4) is the same
    lawfulness (`CellScheme.Rows.printedLawfulLocal_iff_printedRespects`, compiled in this
    repository (theorem named)).
44. `CellScheme.Rows.IsBountiful` (`Scheme/Bountiful`); status S.  The rows are read as in
    note 43.  The clauses are the fields of `CellScheme.Rows.PrintedBallHypotheses`, with the ball
    `CellScheme.Rows.printedBall` and the definition `CellScheme.Rows.PrintedBountifulRows`
    (`Correspondence/Current/Bountiful`).  Compiled in this repository (theorem named), for
    finitely many cells with graded index in the graded plan: `IsBountiful` is the printed
    definition at every stage that is zero or a limit and carries the values of the rows,
    together with the extension of every labelling lawful below a graded face to one lawful below
    every larger graded face (the cap `-∞`)
    (`CellScheme.Rows.isBountiful_iff_forall_printedBountifulRows_and_capBot`); `IsBountiful`
    implies the printed definition at each such stage
    (`CellScheme.Rows.IsBountiful.printedBountifulRows`), in particular at `ω₁`
    (`CellScheme.Rows.IsBountiful.printedBountifulRows_omega_one`).  Not proved: the converse at a
    single stage (as in row 6), and the cap `-∞`, which the printed definition omits (`γ ∈ ω₁`)
    and [Kni26, Definition 2.5.14] includes (clause 4).  Harmless by named theorems, when every
    cell has a graded face of positive grade (the hypothesis `hD`; clause 1 of Definition 4.27
    instead asks for cells of grade `0`, note 45): the printed graded faces of grade `0`
    (`CellScheme.Rows.printedBountifulRows_iff_gradedFaces`); and the cap `∞` (in the proof of the
    characterization).  The two printed definitions are related by
    `CellScheme.Rows.forall_printedBountiful_iff_forall_printedBountifulRows_and_capBot`, compiled
    in this repository (theorem named).
45. `Scheme.IsLegal` with `Scheme.IsCoded` (`Stage/Legal`, `Stage/Scheme`; row 7); the printed
    definition `CellScheme.Rows.PrintedLegal`, the corrected one `CellScheme.Rows.CorrectedLegal`
    (`Correspondence/Current/LegalTemplate`), with the rows read as in note 43.  Clause 1 (C): a
    printed graded face may have grade `0`, and clause 1 then fails for every frame whose cells have
    positive grade (`CellScheme.Rows.not_printedLegal`, compiled in this repository (theorem
    named)).  Within [AFK26] clause 1 is consistent, since its frames may have cells of grade `0`;
    the correction is one of the graded faces of [AFK26, Definition 4.2], taken of positive grade as
    in [Kni26, Definition 2.1.8], which the frames here follow, and clause 1 becomes
    `CellScheme.IsComplete`.  No theorem relates a printed legal template with cells of grade `0` to
    a corrected one.  `Correspondence.IsFrame` (`Correspondence/Template`, row 9) follows
    Definition 4.2 literally and permits cells of grade `0`, as does
    `CellScheme.printedGradedFaces`; their correspondence is still to be proved.  Clause 2 is
    consistency (row 43), clause 3 is row 44 (S).  Agreement on lawful labellings (row 43) is not
    correspondence of legal schemes: clause 4 (`CellScheme.Rows.HasPrintedRange`, `i ≤ g(d)`) is an
    offset bound, which legality here deliberately omits (`README.md`, Layer 3, "legal scheme" and
    checkpoint 2.2).  It is strictly stronger than `Scheme.IsCoded`
    (`CellScheme.Rows.HasPrintedRange.row_lt`), and one tighter than the offset bound `j ≤ k + 1` of
    [Kni26, Lemma 2.5.13]: `CodingExamples.pointRow 2` is legal, satisfies that bound
    (`Scheme.isStronglyCoded_pointRow_two`), and violates clause 4
    (`Scheme.not_hasPrintedRange_pointRow_two`, `Scheme.exists_isLegal_not_hasPrintedRange`), all
    compiled in this repository (theorem named).  So the two classes differ: with clause 1
    corrected and clause 3 required at every stage together with the cap `-∞`, the legal templates
    of [AFK26] are exactly the legal schemes satisfying clause 4
    (`Scheme.isLegal_and_hasPrintedRange_iff`), a strictly smaller class; that a legal template as
    printed (clause 3 at `ω₁` only) is a legal scheme is not proved (row 44).  Under the reading of
    note 43, resolution (2) of the fidelity question of item 1 can hold only up to this bound.
    Compiled in this repository (theorem named): `Scheme.IsLegal.correctedLegal` (a legal scheme
    with clause 4 satisfies the corrected definition at every stage `θ ≥ ω ^ 2` that is zero or a
    limit), `Scheme.IsLegal.correctedLegal_omega_one`,
    and the equivalence `Scheme.isLegal_and_hasPrintedRange_iff` (with the corrected definition at
    every such stage and the cap `-∞` of row 44).  Departures that are not fields: the plan
    conditions of [AFK26, Definition 4.1] (supplied by `Scheme.IsWellFormed` in the equivalence),
    and the finiteness of the cells (`Fin card`; `[Finite ι]` in row 44).  Still to be proved:
    legality from the corrected definition at the single stage `ω₁`, and whether every legal scheme
    is equivalent to one satisfying clause 4.
46. Statement only.  Compiled in this repository (theorem named), in `Stage/Legal`: the legal stage
    types are closed under the face maps (`StageType.IsLegal.restrictFace`), reindexing
    (`StageType.IsLegal.reindex`), and stage reduction (`StageType.isLegal_reduce_iff`), and there
    are countably many on `n` points at a countable stage (`StageType.countable_setOf_isLegal`);
    the base language has one relation symbol for each legal stage type at `ω` (`baseLanguage`,
    `Language/Basic`).  Under the reading of note 43, the first clause of Lemma 4.28 (all
    templates in `L` are legal templates) fails for the legal stage types here as they stand: at
    every stage there is a legal stage type on a scheme violating clause 4
    (`StageType.exists_isLegal_not_hasPrintedRange`, compiled in this repository (theorem named),
    on `CodingExamples.pointRow 2`; note 45).  So a literal identification of `L` with the legal
    stage types is ruled out, not pending.  Either of two results would address this range
    obstruction, and neither
    is chosen here: (a) a proof that the class restricted by clause 4 suffices for the main
    theorem (it is not known to be preserved by the coatom amalgam and the completion, and
    legality may not be strengthened, `README.md`, Layer 3, checkpoint 2.2); or (b) a correction
    of clause 4 of Definition 4.27, recorded as C.  Under the coherent-rows reading of row 9 the
    witness does not apply: it is the bottom labelling, its coherent local rows are all `⊥`, and
    it satisfies clause 4; there clause 4 bounds the labels (note 43), and its effect on Lemma 4.28
    is not recorded.  That the legal stage types form a template system of [AFK26] representing
    every legal template up to relabelling isomorphism is still to be proved: under the reading of
    note 43 after one of (a) and (b); under the coherent-rows reading it rests on item 1's fidelity
    question (row 9, item 1: S) and row 45, with clause 4 bounding the labels.
47. Statement only.  The corresponding statement here is the main theorem in its conditional
    composition `vaughtCounterexample_of_expansionDomains` (`MainTheorem/Assembly`), compiled in
    this repository (theorem named), whose hypotheses are still to be proved.  Under the reading
    of note 43 a template carries no labelling, so `σ[L]` and `baseLanguage` are indexed by
    different kinds of object (templates, legal stage types); their underlying schemes differ by
    clause 4 (`CodingExamples.pointRow 2`, note 46), and a comparison of the two languages needs
    the representation of item 1 (row 9) in any case.  So `σ[L]` cannot be literally
    `densitySentence` as things stand; under the reading of note 43, their identification needs
    one of the two resolutions of note 46, and then rows 12 and 13.  The first assertion of Theorem 4.29, about
    the system `K[L]`, has no counterpart here (prospective).

**Completion criteria, item by item** (the items of `README.md`, "Manuscript correspondence
(required)").  For every item, each row of the concordance that it concerns is P or C, with its
source named.

1. *Template correspondence:* the coherent local rows of a lawful labelling, the recovery of the
   labels from the diagonal, both round trips, and compatibility with `StageType.restrictFace`
   (undefined faces included) and with `StageType.reduce`, each a compiled theorem; and one of the
   two resolutions of the fidelity question, either the manuscript's adoption of the restricted
   class (recorded here and in `LITERATURE.md`) or a compiled theorem identifying the intended
   legal templates of [AFK26] with it.  The index translation is restated with the identity of
   `blockStage`.
2. *The complete diagram round trip:* at every countable stage, the correspondence between the
   structures of the stage chart language satisfying the structural clauses and the exactly
   consistent covering realizations with legal types on a nonempty carrier, by literal inverse
   maps, with the acceptance list of the item (every relation and its negation, `none` at invisible
   faces, repeated coordinates and empty tuples, literal recovery both ways) compiled; no
   countability of the alphabet of all stages is used.
3. *The two-index density theorem:* the equivalence, for observation indices `α ≤ β` and a root
   fixed at `β`, by downward projection of legal donors; the density for `α < β` from the
   construction; the relation between density at block observations and `HasFiniteCutReceiving`,
   as a theorem or a recorded non-implication; and the non-lifting special case of an actual
   model, as a compiled example.
4. *The structural comparison:* a theorem with hypotheses legal types, exact consistency, covering,
   finite-cut receiving of the two realizations, and an explicit common chart, concluding
   `BFEquiv η` of the selected tuples (empty and repeated included) and agreement on formulas of
   quantifier rank at most `η`; and its application from modelhood, with (R1), recovering
   `Expansion.bfEquiv_of_modelExpansions`.
5. *The concrete instance:* each statement of the table of the item proved for the construction,
   with no field assuming a difficult conclusion; the class–level incidence translation of maximal
   presentations, with its three properties, proved before `FullPresentations` is identified with
   anything of [AFK26]; and the two counting endpoints kept with their termination dependence
   explicit, the second never silently quoted for the first.
6. *The tree discussion:* the three refutations compiled as examples (the same-index equivalence
   stated in the version of 1 October 2026 of [AFK26] (its Proposition 8.6), and non-implications
   1 and 5 of "Checkpoint order and acceptance"); the positive classification of density for trees
   is not part of this criterion.

**Completion criteria of the uniform fixing bounds, milestone by milestone** (`README.md`,
"Manuscript correspondence (required)", item 5, "Uniform fixing bounds from positive niceness";
rows 29–32, each still to be proved; the strictness half of row 32 is compiled).  Each milestone
is complete on its own criterion, and none is complete because a later one is.

1. *Closedness is supportedness:* the combined statement, that in an exactly consistent covering
   realization an injective tuple is supported exactly when its set of points is closed, compiled
   (the empty tuple included), with the preservation of supported and unsupported tuples by
   projection; row 29 becomes P or C with item 2.
2. *Positive niceness:* for every actual closed tuple of every countable model of the
   construction, a threshold at which an actual admissible presentation exists (the set of
   thresholds inhabited) and one value taken at the tuple by every admissible presentation at
   every higher index, quantified over all admissible lifts, not over one chosen lift; its use of
   termination stated as a hypothesis or marked in its proof.
3. *The uniform fixing stage:* the conditional theorem with exactly hypotheses 1–3 of the
   sub-item, compiled through `StageProjection.exists_uniform_fixing_stage` (available at the pin
   `e460cb6`, signatures checked), with no ordinal induction of its own and none of the excluded
   assumptions; the empty family and a base assignment with no supported tuple as compiled
   examples; and its application to the data of 2, stage correctness retained, the bound chosen
   before the quantifiers over indices, presentations, arities, and coordinates.
4. *Serving indices* (required for item 5, row 32, whether or not the main theorem uses a bound
   of serving indices): strictness for the models of the construction proved as a separate
   theorem, the bound of serving indices derived from it, and the negative special case (the
   constant family of the all-undefined assignment, fixed at `0` and serving at every index)
   compiled as an example.  Compiled in this repository (theorem named):
   `Realization.IsModel.isFixedAt_blockStage_iff`, `Realization.IsStrict.le_of_forall_isFixedAt`
   and `Realization.le_of_forall_isModel_of_forall_isFixedAt` (`Realization/Strictness`), and
   `Realization.StrictnessExamples.not_isStrict_undefinedFamily`; the milestone is complete once
   the bound is applied to the uniform fixing stage of 3.
5. *The separate statements:* the existence and coverage of maximal presentations, the terminal
   comparison, and noncollapse each proved by its own argument, with its dependencies stated.  The
   bounds of 2–4 are not sufficient for any of them alone; they are cited only with the additional
   hypotheses named in the milestone.  Existence by bounded-stage attainment (for the model
   presentations of one base): 4 with a model base, downward model reduction
   (`Realization.IsModel.reduce`), the injectivity of model reduction at each countable index
   (`ModelExpansion.subsingleton`, conditional on `Expansion.NextBlockUniqueness`), and limit
   coherence (`ModelExpansion.nonempty_of_forall_lt`, under the same hypothesis); coverage by
   this route applies it to a model base of every base class.  Noncollapse by the alternative
   route (`COMPANIONS.md`, "An alternative route to the lower bound"): the uniform fixing stage
   of 3, as the bound for each class of step (iv), with steps (i)–(iii) there (fixing ranks of
   realized charts cofinal in `ω₁`) and the bounded-levels criterion.  No presentation at the
   supremum of the serving indices is inferred from 4 alone, and the default noncollapse
   statement (nonempty losses) cites none of 1–4.

**Completion criteria of maximal presentations, statement by statement** (`README.md`, "Manuscript
correspondence (required)", item 5, "Maximal presentations: equivalent criteria, uniqueness, the
optimal bound"; rows 33–36, each still to be proved).  Each statement is complete on its own
criterion, and none is complete because another is.  Each states its dependencies by name.  The
injectivity of model reduction at each countable index (raw form `ModelExpansion.subsingleton`,
conditional on `Expansion.NextBlockUniqueness`) is a dependency that criterion 5 of the uniform
fixing bounds (above) names for existence by bounded-stage attainment; it is an explicit
hypothesis of each statement of 2–4 that uses it, until it is proved as a theorem first, and
`Expansion.NextBlockUniqueness` is not counted as proved.

1. *Maximal presentations:* the model presentations of a literal base invariant assignment at every
   countable index, and their maximality, defined; a maximal presentation terminal
   (`Realization.IsTerminalAt`) as a compiled theorem; and the conversion between the raw base and
   the common invariant encodings compiled as its own statement before a theorem of one encoding
   is quoted in the other; row 33 becomes P or C with row 27.
2. *The five criteria:* each implication compiled, only 1 ⇒ 2 assuming a countable carrier, and
   2–5 equivalent for arbitrary carriers when the base is a model; 2 ⇔ 3 ⇔ 4 and 5 ⇒ 4 without
   the injectivity of model reduction, and 5 ⇒ 1 from maximality and the strict threshold only;
   the pointwise equivalences of the three sorts of bound at every proposed ordinal, without
   inhabitation.  4 ⇒ 5 is bounded-stage attainment (a greatest serving index, the supplied bound
   not required to be serving), the existence route of criterion 5 of the uniform fixing bounds,
   compiled with the dependencies named there, each a separate theorem: a model base, downward
   model reduction (`Realization.IsModel.reduce`), the injectivity of model reduction at each
   countable index (`ModelExpansion.subsingleton`, conditional on
   `Expansion.NextBlockUniqueness`), and limit coherence (`ModelExpansion.nonempty_of_forall_lt`,
   under the same hypothesis); so both equivalences carry the injectivity of model reduction as an
   explicit hypothesis.  The intended quotation for bounded-stage attainment is
   `exists_greatest_stage_lt_omega1` (`OrdinalUtil`; available upstream, not yet at our pinned
   dependency: signatures verified against the upstream source at `2cd44c3`, not compiled here;
   "Dependency pins"), with `P` the serving indices, `hzero` from a model base, `hdown` from
   downward model reduction, `hlim` from limit coherence, and `hA` and `hbound` from criterion 4
   (a prospective application).  Bounded-stage attainment is compiled here conditionally, in the
   raw base encoding: `MainTheorem.exists_isGreatest_servingIndex_of_le`, conditional on
   `Expansion.NextBlockUniqueness`, through the local ordinal statement
   `exists_isGreatest_of_closed` (`Counting/OrdinalAttainment`; note 34), which the quotation
   replaces at a repin containing `c16de09` and `2cd44c3` ("Placement record").  The negative
   special case (the everywhere-undefined assignment: criteria 1 and 4 vacuous, criterion 5 false)
   compiled as an example.  No proof of criterion 1 that uses termination is cited as a proof of
   termination.
3. *Literal uniqueness:* for a terminal model presentation at `ρ`, every model presentation at `η`
   has `η ≤ ρ` and is literally its reduct, with no countability assumed; two terminal model
   presentations of one base have the same index and are equal; and no extension of a partial
   diagram, an approximate assignment, or a projected donor is derived from it.  Its named
   dependencies: the injectivity of model reduction, the same as in 4 ⇒ 5 (an explicit hypothesis
   of both steps: at `ρ` for the inequality, which is terminal collision, with downward model
   reduction `Realization.IsModel.reduce` and `Realization.isTerminalAt_iff_forall_lt`; and at
   `η` for the equality).
4. *The optimal bound:* both equivalences at every ordinal `ξ`, stated with the given terminal
   presentation; `ρ` as the least upper bound; for a nonzero limit `ρ`, that no finite invariant
   has fixing rank `ρ`; and no identification of `ρ` with a Scott rank.  Its named dependencies:
   the inequality step of literal uniqueness (3), that is, terminal collision, hence the
   injectivity of model reduction at `ρ` only, as an explicit hypothesis (the equality step, at
   `η`, is not used); strictness for models (row 32; compiled); and `COMPANIONS.md`, "Fixing
   ranks are zero or successors", for the limit case.

**Completion criteria of witness-bounded density, terminal refinement, unique reconstruction,
the Scott route, and the stopping proofs** (`README.md`, "Manuscript correspondence
(required)", items 3 and 5, and "Acceptance criteria of the correspondence"; rows 30 and 37–40,
each still to be proved).  Each target is complete on its own criterion, with its dependencies
named, and none is complete because another is.

1. *Equivalent density formulations:* the predicate bounding the returned invariant stated, and
   its equivalence with the donor-bounded form of row 25, for `α ≤ β` on a realization fixed by
   projection at `β`, compiled through `Realization.reduce_eval`; exact face preservation taken
   from `Realization.IsConsistent`, not folded into either predicate; the root and the realizing
   occurrence kept together; no lifting over a projected root derived from it.
2. *Specified terminal refinement:* for every model at a block stage `λ_β` on a countable
   carrier, a model on the same carrier (not an isomorphic copy), terminal at a countable
   `ρ ≥ β`, whose stage reduction to `λ_β` is literally the given model, compiled with `β` not
   assumed countable (`β < ω₁` derived first, from `Realization.IsModel.lt_omega_one` and
   `le_blockStage`, or, as in the compiled form of note 38, from `β ≤ ρ`).  Its named
   dependencies: a terminal presentation of the base from either stopping proof (5 below) and
   literal uniqueness (row 35), under the injectivity of model reduction.
3. *Unique reconstruction:* the `∃!` statement in its carrier-general form (no countability of
   the carrier added; `ξ < ω₁` explicit) and its coded form (a code whose class lies in
   `expansionDomain ξ`), compiled with `Expansion.NextBlockUniqueness` or block determination (or
   a proof of either) as its only hypothesis of uniqueness, and documented with the block
   formulas, their rank budget `ω·η`, the base-reduct equations, and transport along
   isomorphisms; no new structure of hypotheses.
4. *The Scott route:* each step of the chain compiled as its own theorem (Scott isolation for one
   class, the strict bound on serving stages, the attained maximum, positive niceness), with its
   named dependencies: conditions 3 and 4 of the expansion-domain reduction, Scott isolation at
   the pin, the conversion between the two encodings with the transport of the base to a code on
   `ℕ`, the injectivity of model reduction, and countable-limit existence.  The isolating level
   of a countable family is not among them; if it is ever used, it is quoted only once
   "Dependency pins" records a pin containing it, signatures checked.  No hypothesis or lemma
   about termination enters; the conditional of row 31 and this route are not used in a cycle;
   and the expansion-domain endpoint does not depend on it.  The intended quotations (available
   upstream, not yet at our pinned dependency: signatures verified against the upstream source at
   `2cd44c3`, not compiled here; "Dependency pins"; a prospective application) are Scott
   separation for the strict bound on serving stages (`stage_lt_rank_of_isolating` for one class,
   at the rank of its isolating sentence, with nonsingletonness of the domain there from an
   element of a loss at a countable stage at or above that rank and an element of the next domain
   (condition 4 at that stage and at the next); or
   `IsolatedPresentation.exists_countable_strict_stage_bound` for all classes at once) and
   `exists_greatest_stage_lt_omega1` for the attained maximum.  These two steps are compiled here
   (note 40), in the raw base encoding, conditional on `Expansion.FiniteCutReceiving` ((R1)),
   `Expansion.NextBlockUniqueness`, and `StageType.HasApexCoatomExtensions` at every countable
   block stage: the strict bound by `MainTheorem.expansionDomain_nontrivial`,
   `MainTheorem.expansionDomain_subsingleton_of_isolates`, and `MainTheorem.lt_qrank_of_isolates`,
   which specialize `notMem_of_isolating_of_uniform` to the domain at the quantifier rank of the
   isolating sentence, and the attained maximum by `exists_isGreatest_of_closed`
   (`Counting/OrdinalAttainment`).  At a repin containing `c16de09` and `2cd44c3`, the
   quotations replace them: `exists_isGreatest_of_closed` by the greatest-stage statement, and the
   local two-class argument by Scott separation ("Placement record").
5. *The stopping proofs and positive niceness:* each stopping proof that is used (the
   countable-slot argument; the Scott route, 4 above) stated as its own theorem, concluding a
   terminal presentation of each base that is a model, with its own dependencies, the two not
   merged; a proof of the countable-slot argument provides (a) which events use a slot, (b) why
   every relevant continuation uses a fresh slot, and (c) why exhausting those events yields an
   actual terminal presentation, attained and terminal, not only the supremum of countably many
   stages (`README.md`, item 5, "Two stopping proofs; positive niceness from a terminal
   presentation", (i)); positive niceness compiled from an actual terminal presentation
   (terminal collision and the injectivity of model reduction, then 5 ⇒ 1 of row 34), with no
   further stabilization argument and with no stopping proof using it; neither stopping proof a
   dependency of the expansion-domain endpoint.

The five acceptance criteria of `README.md` ("Acceptance criteria of the correspondence") apply to
every item: reconstruction, density, finite objects, rank budgets, and priorities.

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
  complements.  The same module's `mk_le_aleph_one_of_domains` (at the pin, signatures checked)
  is exactly the upper bound `#X ≤ ℵ₁` for domains whose complements below `ω₁` are countable and
  which every point leaves, with neither monotonicity nor nonempty domains;
  `mk_eq_aleph_one_of_domains` adds both for the equality.  The spine does not use them for
  `|Q| ≤ ℵ₁`, which is its direct cover (the persistent core is a subsingleton and each complement
  `Q \ Dη` is countable).  With eventual departure (`COMPANIONS.md`, terminal refinement, from the
  agreement in `Dη` and the nonempty losses with a Scott sentence for each class; compiled
  conditionally, `ExpansionDomains.exists_notMem_of_isolating`, `MainTheorem/LastStage`), every
  class leaves some domain and `mk_le_aleph_one_of_domains` applies to the expansion domains
  directly; this would be a second proof of the upper bound through departure, not taken by the
  spine (departure is not an input to the count), and is not compiled;
- the Gδ/Polish model-code spaces;
- `internalScottRank_le_of_orbits_determined` (`Scott/OrbitRank`), on which the library's
  orbit-formula rank bound (`README.md`, Layer 0) rests; this repository does not apply it
  directly, but quotes the rank bound (companion milestone B of `COMPANIONS.md`).

In the pinned Mathlib (`Mathlib/ModelTheory/Fraisse.lean`): `age`, `Hereditary`,
`JointEmbedding`, `Amalgamation`, `IsFraisse`, `IsUltrahomogeneous`, `IsFraisseLimit`,
`IsUltrahomogeneous.extend_embedding`, `IsFraisseLimit.nonempty_equiv`, and
`age.fg_substructure`, with the hypotheses recorded in `README.md`, Layer 0.  Mathlib has no
existence theorem for Fraïssé limits.

In the pinned ComputableModelTheory (`a1fe761`, signatures checked): the classical Fraïssé theorems
(`representativeClass`, `isFraisse_representativeClass`, `representativeClass_countable_quotient`,
`FGCofinal`, `ExtensionRich`, `isFraisseLimit_of_extensionRich`, `SequenceExtension`,
`amalgamationRich_of_sequenceExtension`, `age_directLimit_eq`, `countable_directLimit`,
`isFraisseLimit_directLimit`), the factorization of tuples through the age
(`exists_factor_tuple_of_age_subset`, `exists_factor_embedding_of_age_subset`), and orbit isolation
and countable prime structures (`IsolatesTuple`, `IsAtomic`, `isolatesTuple_of_orbit_formula`,
`isAtomic_of_orbit_formulas`, `IsolatesTuple.realize_iff`, `IsolatesTuple.typesWith_eq_singleton`,
`exists_elementaryEmbedding_of_countable_atomic`).  Also at the pin `a1fe761`, signatures checked
and `#check`ed in `SuggestedInterfaces.lean`: classical Fraïssé existence
(`exists_fraisseSequence`, `exists_isFraisseLimit_representativeClass`,
`exists_isFraisseLimit_of_isFraisse`; `ModelTheory/FraisseExistence`), rooted universality and
uniqueness (`ExtendsRepresentatives`, `isExtensionPair_of_age_subset`,
`exists_embedding_comp_eq_of_age_subset_of_countable`,
`exists_equiv_comp_eq_of_age_subset_of_countable`; `ModelTheory/RootedExtension`), isolation and
primeness over named finite parameters (`isAtomic_named_of_orbit_formulas`,
`exists_elementaryEmbedding_named`; `ModelTheory/NamedParameters`), and the entry module
`ComputableModelTheory.Classical`, the narrow import of all of these, which the sketch imports.
Their statement shapes and hypotheses are in `README.md`, Layer 0; where the pinned versions name
them differently, those names prevail.

In the pinned InfinitaryLogic (`e460cb6`, signatures checked): the rank comparison of the Scott
process (its pull request #140, merged at `a640bbb`: `selfStabilizesCompletely_iff_orbitRank_le`,
`bfStabilizationOrdinal_self_eq_iSup_orbitRank`, `stabilizesAt_of_orbitRank_le`,
`rank_le_of_orbitRank_le`, `lift_rank_le_internalScottRank`,
`internalScottRank_le_lift_rank_add_one`), and the statements of its pull request #141;
`SuggestedInterfaces.lean` `#check`s both lists:
`BoundedFormula.qrank_toLω_lt_omega0` (`Lomega1omega/QuantifierRank`);
`orbit_determined_of_orbitFormula`, `exists_finite_orbit_threshold`,
`orbitRank_lt_omega0_of_orbitFormula`, and `internalScottRank_le_omega0_of_orbitFormulas`
(`Scott/OrbitFormulaThreshold`, under `[L.IsRelational]`, any carrier `M : Type w`, no
countability or nonemptiness); `BoundedFormulaω.realize_comp_of_localAutomorphisms`,
`BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms`, and
`BoundedFormulaω.realize_comp_append_of_localAutomorphisms` (`Lomega1omega/LocalAutomorphism`,
any language and carrier).

**A generic interface of InfinitaryLogic (available at the pin `e460cb6`, signatures checked and
`#check`ed in `SuggestedInterfaces.lean`; its pull requests #142, #143, and #144).** Statement: for
a relational language (no countability of its symbols), every analytic set `A` of pairs of
structures on `ℕ` containing no isomorphic pair is uniformly separated at some countable
back-and-forth level: there is `α < ω₁` such that no pair `(M, N) ∈ A` is back-and-forth equivalent
at level `α`; in Lean, `exists_uniform_bfSeparation (hA : AnalyticSet A) (hA_noniso : ∀ p ∈ A, ¬
(structureIsoSetoid L).r p.1 p.2) : ∃ α < ω₁, ∀ p ∈ A, ¬ CodeBFEquiv α p.1 p.2`
(`Descriptive/BFSeparation`), with `CodeBFEquiv.monotone`, `exists_uniform_bfSeparation_forall_ge`,
and `exists_uniform_bfSeparation_of_analyticSets`; levels in `Ordinal.{0}`, no offset; its proof
does not use López–Escobar. Its three checkpoints: (1) a coded forced back-and-forth tree whose
assignment is Borel, whose infinite branches correspond to isomorphisms, and whose rank is bounded
below through back-and-forth equivalence, with the rank convention stated precisely (no ordinal
offset assumed); (2) uniform separation from the boundedness of analytic families of well-founded
trees; (3) two applications: cocountable concentration in one back-and-forth class at every
countable level excludes a perfect isomorphism antichain, and an invariant relatively Borel subset
of a Borel class of structures is saturated under some countable back-and-forth level, so that under
concentration one side is countable in isomorphism classes. Checkpoints (1) and (2) are at the pin;
the thinness application of (3) is now upstream, InfinitaryLogic's `isThinOn_of_bfScattered`
(`Descriptive/BFScattered`, at the pin), quoted in this repository as
`isThinOn_of_countable_bfClasses` (formerly a local composition; "The full-presentation
route"), and the saturation application is the prospective interface of
invariant Borel observations listed there. Dependency direction: basic topology, analytic coding,
and well-founded ranks, then analytic tree boundedness, then uniform back-and-forth separation, then
thinness and invariant-Borel concentration; López–Escobar, invariant separation, and the
model-theoretic boundedness route are excluded from this path by import and proof-dependency guards.
Combined with the cocountable concentration of the expansion domains (classes in `D_η` agree at
back-and-forth level `η`), it gives thinness without sentence minimality and without López–Escobar
(the compiled composition, `isThinOn_of_countable_bfClasses`, is applied to full presentations;
for the expansion domains, the composition is the scatteredness form of `README.md`, Layer 6, from
the back-and-forth form of condition 3, compiled conditional on the hypotheses of
`densitySentence_isThinOnNatModels_of_terminalClassification`, each still to be proved:
`densitySentence_isThinOnNatModels_of_terminalClassification_bfScattered`). It does not replace the
working thinness route (`Sentenceω.isThinOnNatModels_of_countable_sentence_splits`, from countable
truth sides), the Gδ/Polish model-code results stay optional, and any improvement it brings is
described as reduced dependencies of the thinness proof, not as a smaller trusted kernel.

`SuggestedInterfaces.lean` checks representative names, so a pin bump that removes one fails
when the sketch is checked (the checks are run by CI).  Coding a `Type w` carrier on `ℕ` needs a
transfer of infinitary isomorphism across universes; do not assume that a statement within a
single universe covers it.

**Library boundary.**  The development quotes the interfaces of InfinitaryLogic that it adopts:
graded matching (`bfEquiv_of_gradedMatching`, applied in `Comparison/GradedMatchingApplications`),
the rank tails and least levels of `OrdinalCountability` (quoted in `Counting/`), and
`BFScattered` (available at the pin, signatures checked in `roadmap/SuggestedInterfaces.lean`;
quoted in `MainTheorem/Scatteredness`, which also derives it from countable complements by
`bfScattered_of_countable_bfObservations`, and applied to the expansion domains in
`MainTheorem/ScatteredDomains`); a
coherent-retraction interface once one is available at a pin.  It needs no new layer of
ComputableModelTheory.

### Dependency pins

The pins, recorded in `lakefile.toml` and `lake-manifest.json`; they are current.
"Available at the pin (signatures checked)" means that `SuggestedInterfaces.lean` `#check`s the
name and its signature at the pin; it does not assert that the hypotheses hold in any setting of
this roadmap.  An application is claimed only where a compiled theorem applying the statement is
named (`README.md`, Layer 0):

- **InfinitaryLogic**: the current pin is `e460cb6`, the merge of its pull request #162, reached
  from `cf80917` (the merge of its pull request #156) by this repository's pull request #97;
  `cf80917` was reached from `def5cc0` (the merge of its pull request #152) by this repository's
  pull request #63;
  `def5cc0` was reached from `8a15ca5` (the merge of its pull request #148) by this repository's
  pull request #49, and `8a15ca5` from `098fb36` (the merge of its pull request #146) by this
  repository's pull request #45.  The statements of `8a15ca5` are available at our pinned
  dependency `e460cb6` (signatures checked; `SuggestedInterfaces.lean` `#check`s them): the rank
  comparison of the Scott process, #140; the orbit-formula threshold and rank bound and
  local-automorphism preservation of `README.md`, Layer 0, #141; analytic tree boundedness, #142;
  the coded forced back-and-forth tree, #143; uniform back-and-forth separation,
  `Descriptive/BFSeparation`, #144; the ordinal-indexed `Σ^in_α`/`Π^in_α` hierarchy,
  `Lomega1omega/InHierarchy`, #145; Montalbán's explicit Scott sentence from a family of orbit
  formulas (#147, `Scott/MontalbanSentence`: `montalbanSentence`, `IsOrbitFormulaFamily`,
  `realize_montalbanSentence`, `montalbanSentence_self`,
  `nonempty_equiv_of_realize_montalbanSentence`, `montalbanSentence_characterizes`, and the pointed
  forms `montalbanSentencePointed`, `IsOrbitFormulaFamilyPointed`,
  `montalbanSentencePointed_characterizes`) and its complexity bound
  in the signed hierarchy (#148, `Scott/MontalbanComplexity`: `isPiIn_atomicDiagram`,
  `isPiIn_montalbanSentence`, `isPiIn_montalbanSentencePointed`,
  `exists_isPiIn_scottSentence_of_sigmaIn_orbits`, `exists_isPiIn_pointed_of_sigmaIn_orbits`, and
  `exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits`).  Between `8a15ca5` and `def5cc0`
  there are three merges, available at the pin (signatures checked; `SuggestedInterfaces.lean`
  `#check`s them; no application compiled in this repository):
  - forgetting finitely many parameters (#149, `Scott/ForgetParameters`): `existsTuple_isScott`,
    the existential closure over the parameters of a formula characterizing `(M, c)` is a Scott
    sentence of `M` among countable structures; `isSigmaIn_existsTuple_iff`, the closure keeps
    the class `Σ^in_α` for `1 ≤ α`; `exists_isSigmaIn_scottSentence_of_sigmaIn_orbits_over`,
    `Σ^in_α` orbits over a parameter tuple (`1 ≤ α`) give a `Σ^in_{α+2}` Scott sentence; and
    `exists_isSigmaIn_three_scottSentence_of_sigmaIn_one_orbits_over`, `Σ^in_1` orbits over
    parameters give a `Σ^in_3` Scott sentence (for the `Σ^in_3` Scott sentence obtained by
    existentially quantifying a named rigid core, `README.md`, Layer 4, and `COMPANIONS.md`, B4);
  - rank tails and the least level of a cover (#150, `OrdinalCountability`): `rankTail`,
    `rankTail_cofinal_losses_iff`, `biInter_rankTail_eq_empty`,
    `mk_le_aleph_one_of_countable_fibers`, `mk_eq_aleph_one_of_countable_fibers`, `leastLevel`,
    `countable_fibers_leastLevel`, and `rankTail_leastLevel`, with `mk_le_aleph_one_of_domains`
    split out of the earlier theorems, beside the earlier `countable_iff_rank_bounded` (the
    interface "ranks with countable fibres", listed as prospective before the repin to
    `def5cc0`); the
    generic statements of `Counting/Filtration` and `Counting/Separation` are proved as quotations
    of these, with their statements kept ("Placement record");
  - graded matching (#152, `Scott/GradedMatching`, `bfEquiv_of_gradedSystem` and
    `bfEquiv_of_gradedMatching`): a family of relations graded up to a height bound, with atomic
    agreement at level `0`, lowering, and forth and back one level down, relates at a level
    `α ≤ height` only `BFEquiv α` pairs (a generic form of the graded back-and-forth theorem of
    `README.md`, Layer 0, whose initial match is a pair related at the height, `α = height`).

  Between `def5cc0` and `cf80917` there are five merges, available at the pin (signatures checked;
  `SuggestedInterfaces.lean` `#check`s the statements named here, except the companions noted; no
  application compiled in this repository except that of the moved `Perfect.mk_eq_continuum` in
  `MainTheorem/Scatteredness` and the quotations of the thinness statements noted below):
  - placement of the isomorphism-transport lemmas (#151): `SameAtomicType.map_equiv` now in
    `Scott/AtomicDiagram` and `BFEquiv.map_equiv` in `Scott/BFEquivRelabel`, below the Karp
    modules (signatures checked); names and statements unchanged;
  - placement of the perfect-set cardinality (#154): `Perfect.mk_eq_continuum` (a nonempty perfect
    subset of a complete, second-countable metric space has the cardinality of the continuum)
    moved from `Descriptive/PerfectAntichain` to the topology-only module `Topology/Perfect`, same
    name and statement, still imported by `Descriptive/PerfectAntichain`; and a note in
    `Scott/BackAndForth` that the definition of `BFEquiv` needs no relational language
    (relationality enters with the comparison to formula agreement, `BFEquiv_implies_agreeQR`);
  - thinness from countably many back-and-forth classes at every level (#153,
    `Descriptive/BFScattered` and `Descriptive/BFScatteredSentence`): `BFScattered K` (for every
    `η < ω₁` the restriction of `CodeBFEquiv η` to `K` has countably many classes), with no
    definability of `K`; `not_hasCantorAntichainOn_of_bfScattered`
    (signatures checked), for every relational language; `isThinOn_of_bfScattered`,
    for countably many relation symbols; and `Sentenceω.isThinOnNatModels_of_bfScattered`, through
    `bfEquivSetoid_eq_comap`; with `codeBFEquivSetoid`, and with the analyticity of the
    off-diagonal of an analytic set in a Hausdorff space, `MeasureTheory.AnalyticSet.offDiag`
    (signatures checked).  The scatteredness form of thinness in `MainTheorem/Scatteredness`
    (Layer 6) is absorbed as quotations, with its statements kept:
    `isThinOn_of_countable_bfClasses` quotes `isThinOn_of_bfScattered`,
    `isThinOnNatModels_of_countable_bfClasses` quotes `Sentenceω.isThinOnNatModels_of_bfScattered`,
    `bfEquivSetoid_eq_comap` quotes InfinitaryLogic's `bfEquivSetoid_eq_comap`,
    `exists_forall_not_codeBFEquiv_of_isClosed` quotes
    `exists_forall_not_codeBFEquiv_of_analyticSet`, `offDiag_noniso` quotes
    `not_structureIso_of_mem_offDiag`, `analyticSet_offDiag` applies
    `MeasureTheory.AnalyticSet.offDiag`, and `codeBFEquivSetoid` is InfinitaryLogic's
    `codeBFEquivSetoid` by definition;
  - the rank conventions (#155): documentation only (`Scott/Height/Defs`: the cross-structure
    ranks in `Ordinal.{0}` and the internal orbit ranks in `Ordinal.{w}`, with the comparisons
    proved and those refuted on the empty carrier and the infinite pure set); no statement changed;
  - orbit-rank bounds and recognition at the rank of a Scott sentence (#156,
    `Scott/OrbitFormulaThreshold` and `Scott/SentenceRecognition`), for relational languages: an
    infinitary orbit formula `φ : L.Formulaω (Fin n)` bounds the orbit rank by
    `Ordinal.lift φ.qrank` (`orbitRank_le_lift_qrank_of_infinitaryOrbitFormula`), and orbit
    formulas of rank `< α` for every tuple bound the internal Scott rank by `Ordinal.lift α`
    (`internalScottRank_le_of_infinitaryOrbitFormulas`), for the prospective base-reduct orbit-rank
    bounds (`COMPANIONS.md`, "Further companion results"); and a sentence, or a formula on `Fin 0`
    read as a sentence, of rank at most `β` that characterizes a countable `M` among the countable
    structures in its carrier universe gives `StabilizesAt M β` and `stabilizationOrdinal M ≤ β`:
    `stabilizesAt_of_sentence_rank` and `stabilizationOrdinal_le_of_sentence_rank` (signatures
    checked), `stabilizesAt_of_formula_rank` and `stabilizationOrdinal_le_of_formula_rank` (the
    other companions in `Scott/SentenceRecognition` are not `#check`ed), for the prospective
    recognition of a supplied model (the same item); whole-model recognition through the empty
    tuple only.

  Toolchain and Mathlib are the same as at `8a15ca5` and `def5cc0`.  The imports are the narrow
  modules (`InfinitaryLogic.Scott.OrbitFormulaThreshold`,
  `InfinitaryLogic.Lomega1omega.LocalAutomorphism`, `InfinitaryLogic.Descriptive.BFSeparation`,
  `InfinitaryLogic.Lomega1omega.InHierarchy`, `InfinitaryLogic.Scott.MontalbanComplexity`,
  `InfinitaryLogic.Scott.ForgetParameters`, `InfinitaryLogic.Scott.GradedMatching`,
  `InfinitaryLogic.OrdinalCountability`, `InfinitaryLogic.Descriptive.BFScattered`,
  `InfinitaryLogic.Descriptive.BFScatteredSentence`, `InfinitaryLogic.Scott.SentenceRecognition`,
  `InfinitaryLogic.Scott.OrbitParameters`, `InfinitaryLogic.Scott.InternalRankBounds`,
  `InfinitaryLogic.Scott.IsolatingLevel`, `InfinitaryLogic.UniformFixation`,
  `InfinitaryLogic.Topology.Perfect`, and the others the sketch names), never
  `InfinitaryLogic.All`.
- **ComputableModelTheory**: the current pin is `a1fe761`, the merge of its pull request #58,
  reached from `3a8f630` (the merge of its pull request #57) by this repository's pull request
  #97; `3a8f630` was reached from `0e9935b` (the merge of its pull request #53) by this
  repository's pull request #63; `0e9935b` was reached from `37f6c42` (the merge of its pull
  request #51) by this repository's pull request #49, and `37f6c42` from `0401c95` (the merge of
  its pull request #47) by this repository's pull request #45.  Representative classes,
  extension-rich families and direct limits, the factorization of tuples through the age, orbit
  isolation, and countable prime structures, rooted universality and uniqueness (#42), classical
  Fraïssé existence (#44), the entry module `ComputableModelTheory.Classical` (#45), and isolation
  and primeness over named finite parameters (#46) are available at our pinned dependency `a1fe761`
  (signatures checked; `SuggestedInterfaces.lean` `#check`s them through the entry module).  It also
  contains the seeded effective back-and-forth and computable automorphisms extending an isomorphism
  between finitely generated substructures of a computably homogeneous structure
  (`ModelTheory/Computable/AutomorphismExtension`); finite elimination (#52, #53,
  `Computability/FiniteElimination`: over a fixed prefix, if refutation persists, a sequence of
  selections that never selects a refuted candidate, replaces a selection only once it is refuted,
  and from some stage on selects only candidates of index at most a given bound makes only finitely
  many selections); attachments and their transport along connecting data (#54,
  `ModelTheory/Computable/Attachment`); and the audit of finite diagrams against rooted extension
  (#57, `ModelTheory/ClosedDiagramAdapterAudit`, compiled checks with no library declaration), all
  outside the entry module and not used here.  None of the modules behind the entry module changed
  between `37f6c42` and `3a8f630`: between `0e9935b` and `3a8f630` only `ModelTheory/Computable`
  and the audit module changed, and the entry module imports neither; between `3a8f630` and
  `a1fe761` (its pull request #58) no declaration changed: only its InfinitaryLogic pin and the
  docstrings of `ModelTheory/Computable/InfinitaryBridge` and its audit, outside the entry
  module's imports.  Its own InfinitaryLogic pin is `6480603` (infinitary-logic's release v6.0.0,
  the merge of its pull request #161), an ancestor of the revision `e460cb6` pinned here; this
  repository's manifest governs (see the next item).
- **Mathlib and the toolchain** agree across the three: one Lean toolchain (`v4.35.0-rc3` at
  present) and one Mathlib commit (at present the fork commit `346a4bd`, inherited from
  InfinitaryLogic).  The manifest holds one revision of each dependency, so ComputableModelTheory
  must be built against the InfinitaryLogic revision pinned here, and the toolchain check of
  `scripts/check.sh` extends to ComputableModelTheory.

**Available at the pin `e460cb6`, after `cf80917`** (InfinitaryLogic's merges #157–#162; same
toolchain and Mathlib; signatures checked: `SuggestedInterfaces.lean` `#check`s the statements
named here; no application compiled in this repository, except the agreement of `existsLastVars`
with `existsTupleFrom` below and the application of `bfScattered_of_countable_bfObservations`):
thinness from countable back-and-forth observations (#157, `Descriptive/BFScattered`).  If for
every `η < ω₁` a map `obs η` on a set `C` of codes has countable range and any two codes with the
same observation are `CodeBFEquiv η`, then `C` is back-and-forth scattered
(`bfScattered_of_countable_bfObservations`, applied in `bfScattered_of_countable_compl`,
`MainTheorem/Scatteredness`, for the expansion domains of `MainTheorem/ScatteredDomains`), carries
no Cantor antichain for isomorphism, for every relational language
(`not_hasCantorAntichainOn_of_countable_bfObservations`), and, for countably many relation symbols,
is thin (`isThinOn_of_countable_bfObservations`).  The same merge moves
`countable_quotient_of_countable_range` to `Descriptive/PerfectAntichain` (not used here).
Eliminating orbit parameters (#158, `Scott/OrbitParameters`: `existsOrbitParams`,
`realize_existsOrbitParams_iff_orbit`, `qrank_existsOrbitParams`), which also adds
`BoundedFormulaω.qrank_inf`, `qrank_sup`, and `BoundedFormulaω.qrank_mapFreeVars` to
`Lomega1omega/QuantifierRank` (the first and third were declared in `Definability/Syntax` before
the repin to `e460cb6` and are now InfinitaryLogic's), and the closure of the last `n` of
`k + n` free variables `existsTupleFrom k n` with `realize_existsTupleFrom` to
`Scott/MontalbanSentence`; quantifier-rank bounds for Montalbán's Scott sentences (#159,
`Scott/MontalbanQuantifierRank`:
`qrank_montalbanSentence_le`, rank at most `α + ω` from a family of rank at most `α`, and the rank
of the tuple quantifier blocks, `qrank_existsTupleFrom` and `qrank_existsTuple`, each adding
exactly `n`).  `existsTupleFrom k m` agrees with `existsLastVars m` of `Definability/Syntax`, by the
same recursion, and `realize_existsTupleFrom` and `qrank_existsTupleFrom` are
`realize_existsLastVars` and `qrank_existsLastVars` read through that agreement; the agreement is
compiled in `Definability/BlockFormulasExamples`, and `Definability/Syntax` keeps its own
declarations ("Placement record").  Cross-rank comparisons and the derived `+ ω` bounds (#160,
`Scott/InternalRankBounds`: `internalScottRank_add_omega0_eq`,
`lift_stabilizationOrdinal_le_internalScottRank_add_omega0` and
`lift_scottHeight_le_internalScottRank_add_omega0`); uniform fixation (#161, `UniformFixation`:
stage projections `StageProjection`, the label rank `StageProjection.labelRank`, and
`StageProjection.exists_uniform_fixing_stage`: over a countable coordinate type, stage correctness
at countable stages and eventual invariance of every coordinate give one countable stage fixing
every admissible presentation at every countable stage); and a countable isolating level (#162,
`Scott/IsolatingLevel`: `exists_isolating_level`, for a countable family of countable structures
over a countable relational language some `γ < ω₁` at which `BFEquiv0` gives an isomorphism, with
`exists_isolating_level_iff` and `not_countable_of_forall_unisolated`).

Uniform fixation (#161, `InfinitaryLogic/UniformFixation`), as stated there: a `StageProjection I`
on one label type `I` has `project : Ordinal.{0} → I → I` with the law
`project α (project β i) = project (min α β) i` at every ordinal; for `ℓ : C → I`,
`FixedAt α ℓ := ∀ c, S.project α (ℓ c) = ℓ c`; and, writing `ω₁` for `Ordinal.omega 1`,
`EventuallyInvariant Adm c := ∃ α < ω₁, ∃ ℓ, Adm α ℓ ∧`
`∀ β, α < β → β < ω₁ → ∀ ℓ', Adm β ℓ' → ℓ' c = ℓ c` (a strict threshold, with an admissible
witness at the threshold itself).  The theorem `StageProjection.exists_uniform_fixing_stage`
takes `[Countable C]`, `(Adm : Ordinal.{0} → (C → I) → Prop)`,
`(hstage : ∀ α, α < ω₁ → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)` and
`(hev : ∀ c, EventuallyInvariant Adm c)`, and concludes
`∃ A < ω₁, ∀ β, β < ω₁ → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ`.  No countability of `I` or of `Adm` is
assumed, nor any admissible presentation at a high stage; `C` empty gives `A = 0`.  Its
application (`README.md`, "Manuscript correspondence (required)", item 5, "Uniform fixing bounds
from positive niceness"), one arity at a time, restricts the coordinates to the supported
injective tuples of `R`, and takes `project γ := reduce (blockStage γ)`, label by label, at
`Ordinal.{0}`; the law with `min` follows from `Label.reduce_reduce_of_le`,
`Label.atStage_reduce`, `Label.AtStage.mono` and `Label.reduce_eq_self_iff` (with
`blockStage_mono`).  The same module proves `exists_uniform_fixing_stage_of_eventually_const`,
a countable uniform stage from eventual constancy alone, with no admissible member required at
the threshold (the admissible witness at the threshold is what yields the explicit bound
`⨆ c, (α_c + 1)`), and `exists_classwise_labelRank_bound`, one countable bound on `labelRank`
(the least stage fixing a label, not a Scott rank), the form for fixing ranks matching milestone 3
there.

The isolating level for a countable family, available at the pin `e460cb6` (signatures
checked), has the following scope.  Over a countable relational language, for
`M : ι → Type w` with `[Countable ι]` and every `M i` countable, `exists_isolating_level` gives
`∃ γ < ω₁, ∀ i j, BFEquiv0 (M i) (M j) γ → Nonempty (M i ≃[L] M j)`;
`exists_isolating_level_iff` gives the same with `↔`; and `not_countable_of_forall_unisolated`
is the contrapositive: if every level below `ω₁` has a nonisomorphic pair related by `BFEquiv0`,
the index type is not countable.  The level is the supremum of the stabilization ordinals of
the members; it is not claimed least, it is not a Scott rank, and it decides isomorphism
between members of the family only.  The Scott route to maximal presentations (`README.md`,
"Manuscript correspondence (required)", item 5; prospective; row 40) does not use this family
theorem: it isolates one class at a time by `stabilizationOrdinal_spec` with
`stabilizationOrdinal_lt_omega1'`, or by `scottSentence_characterizes` through
`BFEquiv_implies_agreeQR` (all available at the pin, signatures checked).

**Available upstream, not yet available at our pinned dependency:** of InfinitaryLogic, at
`30c186f` (the merge of its pull request #163, after the pin `e460cb6`; same toolchain and
Mathlib), concentration at back-and-forth levels (`Descriptive/BFConcentration`); at `c16de09`
(the merge of its pull request #170, after `30c186f`; the statements entered with its pull
request #165; same toolchain and Mathlib), the attainment of a greatest countable stage
(`OrdinalUtil`, namespace `InfinitaryLogic`, with Mathlib imports only); and at `2cd44c3` (the
merge of its pull request #169, which contains `c16de09`; same toolchain and Mathlib), Scott
separation for rank-uniform domains (`OrdinalCountability`, `Lomega1omega/QuantifierRank`,
`Descriptive/ScottDefinability`).  Of ComputableModelTheory: none (its `main` is the pin
`a1fe761`).  A statement merged upstream after the pins above is listed here, recorded here only
and never `#check`ed in the sketches, until a repin containing it is recorded in this subsection
(a repin to a revision containing `2cd44c3` is listed as a possible future checkpoint, "Checkpoint
order and acceptance"; none has been made, and none is decided).

**Upstream statements quoted, not compiled here.**  The definition of "signatures checked" at the
head of this subsection does not apply to the Lean blocks below.  They are the statements of
`c16de09` and `2cd44c3`, as merged (hypotheses included), available upstream, not yet at our
pinned dependency: signatures verified against the upstream source at `2cd44c3` (which contains
`c16de09`), not compiled here (neither compiled against our pin `e460cb6` nor `#check`ed in
`SuggestedInterfaces.lean`); no application is compiled in this repository.  Local statements
compiled in place of the greatest-stage statement and of Scott separation, to be replaced by
these at a repin containing them, are listed in the "Placement record"
(`Counting/OrdinalAttainment` and `MainTheorem/MaximalRefinement`).

- *Greatest attained stage* (`OrdinalUtil`): a predicate on stages that holds at `0`, is closed
  downward, is closed under successor limits below `ω₁`, and is bounded on the stages below `ω₁`
  by a countable `A` has a greatest stage `ρ ≤ A`, and holds exactly at the stages `ξ ≤ ρ`, at
  every ordinal `ξ`, not only below `ω₁` (downward closure is global):

  ```lean
  theorem exists_greatest_stage_lt_omega1 (P : Ordinal.{0} → Prop) (hzero : P 0)
      (hdown : ∀ {α β}, α ≤ β → P β → P α)
      (hlim : ∀ l, Order.IsSuccLimit l → l < Ordinal.omega 1 → (∀ ξ, ξ < l → P ξ) → P l)
      {A : Ordinal.{0}} (hA : A < Ordinal.omega 1)
      (hbound : ∀ ξ, ξ < Ordinal.omega 1 → P ξ → ξ ≤ A) :
      ∃ ρ, ρ ≤ A ∧ P ρ ∧ ∀ ξ, P ξ ↔ ξ ≤ ρ
  ```

  with the general forms `exists_forall_iff_le_of_bounded_of_isSuccLimit_closed` (on
  `Ordinal.{u}`, with no countability and with limit closure at every successor limit) and
  `exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed` (the same, stated with
  `IsGreatest`).  The form with `(Cardinal.aleph 1).ord` and the conclusion restricted to
  `ξ < (Cardinal.aleph 1).ord` follows by `Cardinal.ord_aleph`, the equation
  `(Cardinal.aleph o).ord = Ordinal.omega o`.
- *Scott separation* (`OrdinalCountability`, namespace `InfinitaryLogic`; `Sat` and `rank` are
  parameters and the proofs use no model theory): an observation `φ` isolating a point `q`
  excludes `q` from every set of two or more points on which `φ` is constant; so along decreasing
  domains on which the observations of rank at most the stage agree, `q` lies in no domain at
  or above the rank of `φ` when the domain at that rank has two or more points, and, when every
  point is isolated by an observation of countable rank and every domain at a countable stage
  has two or more points, every point leaves the domains strictly before a countable stage:

  ```lean
  theorem notMem_of_isolating_of_uniform {X : Type u} {F : Type v}
      (Sat : F → X → Prop) {D : Set X} {q : X} {φ : F}
      (hiso : ∀ x, Sat φ x ↔ x = q)
      (huniform : ∀ ⦃x y⦄, x ∈ D → y ∈ D → (Sat φ x ↔ Sat φ y))
      (htwo : D.Nontrivial) :
      q ∉ D

  theorem lt_index_of_isolating_of_antitone {X : Type u} {F : Type v}
      {ι : Type w} [LinearOrder ι] (Sat : F → X → Prop)
      (D : ι → Set X) (hanti : Antitone D) {q : X} {φ : F} {ζ : ι}
      (hiso : ∀ x, Sat φ x ↔ x = q)
      (huniform : ∀ ⦃x y⦄, x ∈ D ζ → y ∈ D ζ → (Sat φ x ↔ Sat φ y))
      (htwo : (D ζ).Nontrivial) {η : ι} (hq : q ∈ D η) :
      η < ζ

  theorem lt_rank_of_isolating_of_antitone {X : Type u} {F : Type v}
      {ι : Type w} [LinearOrder ι] (Sat : F → X → Prop)
      (rank : F → ι) (D : ι → Set X) (hanti : Antitone D) {q : X} {φ : F}
      (hiso : ∀ x, Sat φ x ↔ x = q)
      (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
      (htwo : (D (rank φ)).Nontrivial) {η : ι} (hq : q ∈ D η) :
      η < rank φ

  theorem stage_lt_rank_of_isolating {X : Type u} {F : Type v}
      (Sat : F → X → Prop) (rank : F → Ordinal.{0})
      (D : Ordinal.{0} → Set X) (hanti : Antitone D) {q : X} {φ : F}
      (hiso : ∀ x, Sat φ x ↔ x = q)
      (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
      (htwo : (D (rank φ)).Nontrivial) {η : Ordinal.{0}} (hq : q ∈ D η) :
      η < rank φ

  theorem exists_countable_strict_stage_bound_of_isolation {X : Type u} {F : Type v}
      (Sat : F → X → Prop) (rank : F → Ordinal.{0})
      (D : Ordinal.{0} → Set X) (hanti : Antitone D)
      (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η →
        ∀ ⦃x y⦄, x ∈ D η → y ∈ D η → (Sat φ x ↔ Sat φ y))
      (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial)
      (hisolate : ∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q) (q : X) :
      ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ
  ```

  Every formula of `Lω₁ω`, in every language, has countable quantifier rank
  (`Lomega1omega/QuantifierRank`; a syntactic fact):

  ```lean
  theorem FirstOrder.Language.BoundedFormulaω.qrank_lt_omega1 {L : Language.{u, v}} {α : Type*} :
      ∀ {n : ℕ} (φ : L.BoundedFormulaω α n), φ.qrank < Ordinal.omega 1
  theorem FirstOrder.Language.Sentenceω.qrank_lt_omega1 {L : Language.{u, v}}
      (φ : L.Sentenceω) : φ.qrank < Ordinal.omega 1
  ```

  and an isolated presentation (`IsolatedPresentation truth`: every class is the only one
  satisfying some sentence) isolates each class by a sentence of countable quantifier rank, so
  the countable strict bound holds for the domains of its classes
  (`Descriptive/ScottDefinability`):

  ```lean
  theorem FirstOrder.Language.IsolatedPresentation.exists_qrank_lt_omega1 {L : Language.{u, v}}
      {Q : Type w} {truth : L.Sentenceω → Q → Prop}
      (hisol : IsolatedPresentation truth) (q : Q) :
      ∃ σ : L.Sentenceω, σ.qrank < Ordinal.omega 1 ∧ ∀ s, truth σ s ↔ s = q

  theorem FirstOrder.Language.IsolatedPresentation.exists_countable_strict_stage_bound
      {L : Language.{u, v}} {Q : Type w}
      {truth : L.Sentenceω → Q → Prop} (hisol : IsolatedPresentation truth)
      (D : Ordinal.{0} → Set Q) (hanti : Antitone D)
      (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ : L.Sentenceω, φ.qrank ≤ η →
        ∀ ⦃x y⦄, x ∈ D η → y ∈ D η → (truth φ x ↔ truth φ y))
      (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial) (q : Q) :
      ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ
  ```

**The scope of these statements.**  In Scott separation the bound is the quantifier rank of a
chosen isolating sentence: it is not an internal Scott rank, not a stabilization ordinal, and not
an attained stage (attainment is the separate greatest-stage theorem, under its closure
hypotheses), and two isolating sentences of different ranks give different bounds, the larger
not the least strict bound.  Agreement at stage `η` is for the sentences of quantifier rank **at
most** `η` (the convention of `EquivQRω`); under agreement only for ranks strictly below `η` the
bound at the rank (`stage_lt_rank_of_isolating`) fails, and a countable strict bound needs
`θ := rank φ + 1`, with agreement and nonsingletonness at that later stage.  Nonsingletonness of
the domains (`Set.Nontrivial`) is essential: neither nonemptiness nor an ambient `Nontrivial`
type replaces it.  No countability of classes is assumed, and the hypotheses of
`exists_countable_strict_stage_bound_of_isolation` imply that the class space is uncountable, so
on a countable class space it applies only vacuously (the exclusion and the bound at the rank
are not vacuous on finite spaces).  Under antitonicity its conclusion is `q ∉ D θ`, the
hypothesis that every point leaves the domains, of `mk_le_aleph_one_of_domains` and
`mk_eq_aleph_one_of_domains` (`OrdinalCountability`, available at the pin, signatures checked).
Where the nonsingletonness at `θ` is obtained from an element of `D θ \ D (θ + 1)` and an element of
`D (θ + 1)`, that pair is to be required only at the countable stages `θ < ω₁`: required at every
ordinal, it is inconsistent with isolation, agreement and antitonicity, since the countable bound
forces `D ω₁ = ∅`.  In the greatest-stage theorem each of `hzero`, downward closure, limit closure
and a countable bound is needed (the stages `ξ < ω` without limit closure, and `ξ < ω₁` with the
bound `A = ω₁`, have no greatest stage).  Both statements use `Ordinal.omega 1`; a statement written
with `(Cardinal.aleph 1).ord` is converted by `Cardinal.ord_aleph`.

**Available at the pin `e460cb6` since `cf80917`, used by `COMPANIONS.md`, "Quantitative
reconstruction", targets 2 and 3** (listed as available upstream before the repin to `cf80917`):
the bound of an orbit rank by the quantifier rank of an infinitary orbit formula
(`orbitRank_le_lift_qrank_of_infinitaryOrbitFormula`) with its corollary
`internalScottRank_le_of_infinitaryOrbitFormulas` (strict bounds `qrank φ < α` giving
`internalScottRank M ≤ Ordinal.lift α`), and the bounds of the stabilization ordinal by the
rank of a characterizing sentence or formula with no free variables
(`stabilizesAt_of_sentence_rank`, `stabilizationOrdinal_le_of_sentence_rank`,
`stabilizesAt_of_formula_rank`, `stabilizationOrdinal_le_of_formula_rank`; a relational language,
with no countability of the language).  Signatures checked (`SuggestedInterfaces.lean` `#check`s
them).

**Prospective dependencies (neither available upstream nor pinned):** the InfinitaryLogic statements
listed under "The full-presentation route": invariant Borel observations and limits of chains of
bounded equivalence (the analogue for `BlockBFEquiv` of the chain-limit lemma).  The local graded
back-and-forth theorem is retired: both of its intended applications compile through the upstream
`bfEquiv_of_gradedMatching` (at the pin, signatures checked), on abstract hypotheses (`README.md`,
Layer 0, for where the height guard and the selection of coordinates go).  No statement of this
roadmap relies on any of them, or on the statements available upstream, as pinned until this
subsection records a pin containing it; until then they are recorded here only (`README.md`,
Layer 0), never `#check`ed in the sketches.

### Applications of library theorems

The development produces the following, and only these, as hypotheses of library theorems:

- **the ages:** for each countable block `η`, the family of finite top-free charts at `λ_η` as
  finite `L^h_λ`-structures, with finite generation, a countable inhabited index, hereditary
  closure, joint embedding, and amalgamation with the literal commuting square (steps 1–2).  These
  are compiled in this repository (theorem named), in `ClassicalLimit/Age` and
  `ClassicalLimit/Amalgamation`, with joint embedding and amalgamation conditional on the coatom
  extension property `StageType.HasCoatomExtensions` (still to be proved);
  `isFraisse_representativeClass` and the classical existence theorem are applied there
  (`isFraisse_topFreeAge`, `exists_isFraisseLimit_topFreeAge`, step 3), under the same condition;
- **orbit formulas (first interface):** for every finite tuple `a` of a countable top-free model
  read in the relational stage chart language `L_λ` (the empty tuple and repeated coordinates
  included), a first-order formula of `L_λ` defining exactly its automorphism orbit: the
  containing-chart formula `θ_a(x̄) := ∃ z̄, P_p(z̄) ∧ ⋀_i x_i = z_{ι(i)}` of an actual chart `z̄`
  of type `p` containing `a` at the positions `ι` (`orbitDefinedBy_chartOrbitFormula` in
  `SuggestedCompanions.lean`), from chart homogeneity;
- **local automorphisms (second interface):** for each relevant self-embedding and finite tuple,
  an automorphism agreeing with the self-embedding on the tuple (`COMPANIONS.md`, B2).

Everything after these two interfaces is an application: those of InfinitaryLogic are compiled on
abstract hypotheses in `SuggestedCompanions.lean`, section B (one-line applications, proved); those
of ComputableModelTheory are recorded there as `sorry` targets; none is yet instantiated to a
construction of this repository.  The table has five lines for four facts
proved here: the first fact is split over two lines, one for each library theorem it feeds.

| This development proves | The library supplies (InfinitaryLogic, pull request #141) |
| --- | --- |
| The containing-chart formula defines the tuple's orbit | `exists_finite_orbit_threshold` |
| (the same) | `orbitRank_lt_omega0_of_orbitFormula` |
| Every tuple has such an orbit formula | `internalScottRank_le_omega0_of_orbitFormulas` |
| Local agreement | `BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms` |
| Local agreement, finite parameters | `BoundedFormulaω.realize_comp_append_of_localAutomorphisms` |

These are available at the pin `e460cb6` (signatures checked; "Dependency pins").
Three qualifications:

1. Countability belongs to the construction-specific homogeneity proof (the back-and-forth of
   `COMPANIONS.md`, B2, or ultrahomogeneity of the countable limit), not to the generic rank
   theorems: the library's orbit-formula theorems hold on arbitrary carriers, but that does not
   generalize the production of orbit formulas here.
2. The rank conclusion is `≤ ω`: different tuples may need orbit formulas of different finite
   ranks.  There is neither a uniform finite bound nor an equality with the rank of a Scott
   process or with the expansion height.
3. Atomicity and primeness remain separate applications: the orbit formulas feed both the
   first-order route (isolation, atomicity, primeness, from ComputableModelTheory, at the pin) and
   the infinitary rank route (InfinitaryLogic); the rank route is not derived from atomicity.

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

The development is also to quote (expected applications, not elaborated here; each library
statement is available at the pin):

- the factorization of tuples through the age (ComputableModelTheory), for steps 4–5 of finite-age
  reconstruction;
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
blocks"), now at the pin, is applied by the scatteredness form of thinness
(`isThinOn_of_countable_bfClasses`).

## Automation and API discipline

- Make constructor projections, identity reindexings, and canonical cell transport
  directional `[simp]` lemmas.  Use `ext` on data, and narrow `simp only` for dependent face
  equations.  Do not unfold whole schemes/models globally.
- Separate natural-index arithmetic (`omega`) from ordinal inequalities (blocks `[μ, μ + ω)` and
  bands `[α, α + K]`); expose exact block- and band-comparison lemmas before asking automation to
  solve goals.
- Use `funext`, `Function.Embedding.ext`, `Subtype.ext`, and proof irrelevance to finish
  the transport equations.  Give explicit structure instances where a structure is coded, rather
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

1. Finite geometry, scalar label algebra, and transport, with their special cases.
2. Item 3.1 of Layer 3 of `README.md`: the legal finite extension construction of every statement
   of its table, as data with its literal equations, bountifulness at every self-visible cap with
   cap preservation on every target coordinate, and the section theorem by the shared decoding
   lemma, with its applications to the growth and LOW constructions; small, empty, top/bottom
   and invisible cases.  Status of (R6): the amalgam of two coatom stage types, its literal
   restrictions, and its consistent and bountiful rows are established, and (R6) follows from
   the coatom extension property, with nothing used about the stage; the proof of that property
   in its apex form, the completion of the amalgam, is checkpoints 2.1–2.7.
3. Realizations, literal syntax correspondence, the hull operations with their five facts; then
   steps 1–6 of the top-free witnesses, in order: finite top-free charts, hereditary closure and
   amalgamation and joint embedding (through the plain form of the coatom extension property, the
   first use of (R6)), classical existence (available at the pin), reconstruction of partial
   evaluation, consistency and covering and top-freeness, and receiving (the first use of (R5)).
   Status: the hull operations with their five facts are compiled for finite charts, items 4–5 where
   they identify embeddings and substructures for a legal chart (for item 4, one of the two charts
   legal), legality being essential for item 5 (`README.md`, Layer 2, "Status for finite charts";
   `Language/HullOperations`, `Language/HullDefinability`); for exactly consistent covering
   realizations the two-charts theorem (`Realization.eq_of_eval_eq_some`), item 1 for pairs, under
   legality along the hull of the pair (`Realization.exists_hullOp_eq_of_mem_finiteHull`), item 2,
   and item 3 for embeddings of realizations, and for embeddings of stage-chart-language structures
   whose source has legal types, are compiled (`README.md`, Layer 2, "Status for realizations";
   `Realization/TwoCharts`), and items 4–5 remain to be proved for realizations; steps 1–3 of the
   top-free witnesses are compiled, the amalgamation and joint embedding of step 2 and step 3
   conditional on `StageType.HasCoatomExtensions`, and steps 4 and 5 under top-free chart coverage,
   the limit being a hypothesis ("The top-free witnesses: milestone order and acceptance"); step 6
   is compiled for an ultrahomogeneous structure whose age is the age of top-free charts, with no
   hypothesis `StageType.HasCoatomExtensions`, which only the existence of such a structure (step 3)
   needs.
4. Items 3.2 and 3.3 for (R1)–(R3): for each of them, the extension of the realization by one actual
   occurrence over the literal root and the recovery theorem (by `Correct` and labelled
   evaluation, by LOW, or through the gate), with all its equations on that occurrence and at
   every permitted cutoff; the recovery statement of (R3) and (R4) for every
   restriction-compatible labelling whose private face lies in the prescribed bottom class; the
   first use of (R1), the one-sided donor transfer; the cap-to-model theorem, with the
   modelhood and infinitude of the top-free witnesses (step 7); and the fidelity theorem of
   layer 2, the equivalence of the density sentence with the four-family sentence, whose two
   directions use (R1) and the cap-to-model theorem.
   Status and route of (R1).  Receiving of the top-free witnesses (4a, step 6 of the top-free
   witnesses, for an ultrahomogeneous structure whose age is the age of top-free charts, which
   exists under `StageType.HasCoatomExtensions`) and the descent of finite-cut receiving along stage
   reduction are compiled in this repository (theorem named): `hasFiniteCutReceiving_reconstruct`
   and `realize_densitySentence_reconstruct_reduce` (`ClassicalLimit/Receiving`), and
   `HasFiniteCutReceiving.reduce` (`Realization/Receiving`).  They do not give (R1) for all models
   (`README.md`, Layer 3, vocabulary, the receiving item), which condition 3, the fidelity direction
   at stage `ω`, and (R2) need.  General (R1) is split as (R6) is: 4b-i, the acquisition of the
   private context from the clauses of a model (uniformity and high-arity dominance, with exact
   consistency; generalized saturation is not used); 4b-ii, the ordinary construction as data
   (the gated scheme on the private points and one new point, with its literal private and donor
   faces, its display, and its gate of graded index `(univ, n)`); 4b-iii, gate recovery, a finite
   statement about rows (`README.md`, Layer 3, 3.3, recovery item 1); 4b-iv, the assembly of
   `Expansion.FiniteCutReceiving`.  The legality of the gated scheme contains exact pinned
   extensions and a final layer of full scope controlled at
   the grade of the gate, which the abstract coatom extension property does not supply; so the
   construction of 4b-ii is first stated as a named gated-extension property, a hypothesis in the
   pattern of `StageType.HasCoatomExtensions`, and 4b-iv is proved conditionally on it; the property
   itself is then proved alongside or after checkpoints 2.6–2.7.  The conditional theorem does not
   complete (R1) (`README.md`, Summit 3). Status: 4a and the descent are compiled. 4b-i, the
   private context (`Realization.IsModel.exists_privateContext`, `Realization/PrivateContext`, and
   its anchored form `Realization.IsModel.exists_privateContext_isAnchored`), acquired by clauses
   4(b) and 4(c) with exact consistency only, with no marker and no reference cell requested for
   the block of the cutoff (the private cap is labelled above the cutoff); 4b-iii, gate recovery,
   for rows (`CellScheme.Rows.IsGate.recover`, `Extension/Gate`) and for a gated extension
   (`StageType.GatedExtension.recover`, `Realization/GateRecovery`), with no legality, no
   completion, and no (R6), and with the twin–gate coupling in place of the bottom pattern of the
   twins (`CellScheme.Rows.IsGate.recover_of_twinsReadGate`,
   `StageType.CoupledGatedExtension.exists_restrictFace_mem_receivingFamily`); and 4b-iv,
   conditional on the gated-extension property, stated as
   `StageType.HasCoupledGatedPinnedExtensions` (`Extension/GatedExtension`), with generalized
   saturation over the private context, witnessed by the display, and no hypothesis on the stage
   (`Realization.IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions`,
   `Realization/CoupledFiniteCutReceiving`,
   `Expansion.finiteCutReceiving_of_hasCoupledGatedPinnedExtensions`), are compiled in this
   repository (theorem named). The first form of the property, `StageType.HasGatedPinnedExtensions`,
   whose displays label the twins of the gate `⊥`, is refuted at every stage
   (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`, compiled in this repository
   (theorem named)); the coupled form replaces that clause by the condition on rows
   `CellScheme.Rows.TwinsReadGate` and holds at the refuting input
   (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`, compiled in this repository
   (theorem named)). 4b-ii, the construction as data, and with it
   `StageType.HasCoupledGatedPinnedExtensions`, is open. Its open point is cap lowering (CL),
   stated in its docstring, the uniform form of what the construction needs, a strengthening not
   shown necessary: a failure of (CL) refutes the coupled design only at a pair that a forcing
   prescription from an anchored legal donor actually realizes. At a stage where the hypothesis
   fails the conditional theorem is vacuous, and nothing rules that out. The conditional theorem
   receives one permitted cutoff at a time and is not exact projected receiving. Projected-donor
   lifting is not part of checkpoint 4 (`README.md`, Layer 3, 3.3, the density boundary). This
   status concerns (R1) only: (R2), (R3), and the fidelity theorem of this checkpoint remain to be
   proved; the cap-to-model theorem at a limit stage is compiled
   (`Realization.isModel_of_hasFiniteCutReceiving`, `Realization/CapToModel`) conditional on the
   nonemptiness of the instances of uniformity and dominance, which the coatom extension property
   with apex gives (`CapToModel.of_hasApexCoatomExtensions`, at `ω`).
5. Structural continuation (the structural stable candidate); then items 3.2 and 3.3 for (R4)
   (the acquisition of its calibrated data, its occurrence, and the evaluation of the stable
   labelling by the recovery statement of checkpoint 4); three terminal comparisons (the first
   uses of (R2) and (R3)), stable modelhood (the first use of (R4), with the cap-to-model
   theorem), unique limit expansions, and the terminality of the top-free witnesses with the
   placement of their base classes in the losses (step 7).
   Status (each named hypothesis with its own status in `DASHBOARD.md`). Normalization (outputs 1–2
   of `README.md`, Layer 4) is compiled in this repository (theorem named): forcing thresholds and
   the provisional offset (`StageType.ForcesThreshold`, `StageType.provisionalOffset`,
   `Stage/Threshold`, Layer 1); the stable offset and the stable label, a supremum over rooted
   covers, with soundness unconditional (`Realization.stableLabel`,
   `Realization.Covers.le_label_of_forcesThreshold`, `Continuation/Normalization`); and the
   threshold lemma, the normalization of labels, and determination by the reduction
   (`Realization.le_label_iff_exists_forcesThreshold`, `Realization.label_eq_stableLabel`,
   `Realization.eq_of_reduce_eq_of_forcingDonors`), conditional on finite-extension receiving (from
   (R1)) and on forcing donors (`ForcingDonors`). Next-block uniqueness is derived from (R1)
   (checkpoint 4) and forcing donors (`Expansion.NextBlockUniqueness.of_forcingDonors`). Forcing
   donors is still to be proved; it is compiled conditional on the coatom extension property at
   `λ_{η+1}` (`forcingDonors_of_hasCoatomExtensions`, `Extension/ForcingDonorsCoatom`), by a finite
   construction without (R1) and without a completion, so it waits for checkpoint 2.7; one- and
   two-point inputs up to the threshold `4` are compiled unconditionally
   (`forcingDonorsUpTo_one_four`, `forcingDonorsUpTo_two_four`). The structural candidate
   (output 1) is compiled (`Realization.stableCandidate`, `Continuation/Candidate`), with exact
   consistency, covering, the order law, and locality from exact consistency and covering, and
   availability from legal types, also at twins (two cells labelled `⊤` at one graded index), so
   that every model at a block stage is stably lawful (`Realization.IsModel.isStablyLawful`); two
   hypotheses on single types are refuted (section 4 above). Output 3 (stated as the hypothesis
   `ContinuationCriterion`) is compiled conditionally on (R4) and the coface instances at the next
   block (`ContinuationCriterion.of_stableCappedReceiving`); (R4) and the coatom extension
   property with apex at `λ_{ξ+1}` are still to be proved. Under (R1), forcing donors and the coface
   instances, (R4) is equivalent to `ContinuationCriterion`
   (`Expansion.stableCappedReceiving_iff_continuationCriterion`, `Expansion/StableReceiving`), so it
   is a reformulation of output 3, not a weaker step. For `λ_ξ ≤ γ`, (R4) at one occurrence
   (`Realization.StablyReceivesAt`, `Continuation/StableReceiving`) is exact receiving in the model
   of the reduction of the donor together with the calibration of the stable labels at the new cells
   reducing to the top; the evaluation step and the acquisition of the marker and cap calibration
   are compiled, so (R4) follows from the finite statement `StageType.HasStableRecoverySchemes` for
   `StageType.MarkerCapCalibration` at every `ξ < ω₁`
   (`StableCappedReceiving.of_hasStableRecoverySchemes_markerCap`), a finite hypothesis that is
   false (`Continuation.StableRecoveryCounterexample.not_forall_hasStableRecoverySchemes_markerCap`,
   `Continuation/StableRecoveryCounterexample`).
   `StableCappedReceiving.of_hasStableRecoverySchemes_markerCap` rests on that refuted hypothesis
   and is to be retired, with an audit of its uses, once this refutation is on `main` (not retired
   here).  (R4) also follows from the same statement for the graded cap calibration
   (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`, `Continuation/StableRecovery`;
   acquisition compiled, the finite statement open; it holds at every instance with a scheme
   reading through a cap, `StageType.IsStableRecoveryScheme.of_readsThroughCap`; `README.md`,
   Layer 4, status, output 3). Step 7 is
   compiled conditionally (`README.md`, the section on the top-free witnesses): the loss at `η`
   under uniqueness at `λ_η` (`nonempty_loss_of_topFreeWitness`), and per block under
   `StageType.HasApexCoatomExtensions` at `λ_η` and uniqueness of the model expansions at `λ_η`
   (`nonempty_loss_of_hasApexCoatomExtensions`, `MainTheorem/LowerBound`).

   **Condition 2 and the count at one level: checkpoints A–F.**  Condition 2 of the reduction
   (countable successor losses) is complete at E, conditionally on output 3
   (`ContinuationCriterion`), (R1), (R2), and (R3).  F is the count at one level for the terminal
   models (`README.md`, "Reduction to full presentations"), a strengthening of E's count that
   condition 2 does not need.  Each checkpoint is compiled in this repository (theorem named);
   its hypotheses are listed below.

   | Checkpoint | Content | Module |
   | --- | --- | --- |
   | A | exact receiving within an age; the exact-age comparison | `Continuation/ExactAge` |
   | B | terminality, top grade, admissible top supports, rigid cores | `Continuation/Terminal` |
   | C | the countable index of terminal properties; the cover | `Continuation/Classification` |
   | D | the comparison of expansions sharing a property | `Continuation/Comparison` |
   | E | losses are terminal; one class per property; the count | `Expansion/Losses` |
   | F | the classes terminal at a level; the cover; the count | `MainTheorem/TerminalClasses` |

   - A: `Realization.nonempty_equiv_of_exactReceivingWithin`, pointed
     `Realization.exists_equiv_comp_eq_of_exactReceivingWithinAt`; no named hypothesis.
   - B: `Realization.IsTerminalAt`, `Realization.topGradeSup`, `StageType.IsRigidCoreIn`,
     `Realization.IsGloballyRigidCore`, `Realization.IsModel.isGloballyRigidCore_empty_iff`; no
     named hypothesis.
   - C: `countable_terminalProperty`, unconditional; the cover
     `Realization.exists_hasTerminalProperty`, conditional on `ContinuationCriterion` (used once,
     contrapositively).
   - D: `Realization.nonempty_equiv_of_isGloballyRigidCore`, from finite-extension receiving
     ((R1)); `Realization.nonempty_equiv_of_residual`, conditional on
     `Realization.ResidualReceiving` ((R2)); `Realization.nonempty_equiv_of_hollow`, conditional on
     `Realization.HollowReceiving` ((R3)), with the hollowness predicate a parameter. Terminality
     is not used.
   - E: `ModelExpansion.isTerminalAt_of_mem_loss`, unconditional;
     `Expansion.subsingleton_classes_of_property`, conditional on (R1), (R2), and (R3) for
     `Realization.IsCoverHollowAtBlock`; `Expansion.expansionDomain_loss_countable`, conditional on
     these and `ContinuationCriterion`, through `Counting.countable_of_subsingleton_cover`
     (Layer 0); the main theorem with no hypothesis of countable losses,
     `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`
     (`MainTheorem/ModelExpansionDomains`).
   - C and E, with the hollow property restricted to models without a globally rigid core
     (`Continuation/RestrictedHollow`): the cover `Realization.exists_hasRestrictedTerminalProperty`
     from `Realization.exists_hasTerminalProperty` (the step itself,
     `Realization.exists_hasRestrictedTerminalProperty_of_hasTerminalProperty`, has no
     hypothesis); `Expansion.subsingleton_classes_of_restrictedProperty` and
     `Expansion.expansionDomain_loss_countable_of_restrictedTerminalClassification`, with (R3) for
     `Realization.IsCoverHollowWithoutRigidCoreAtBlock`, implied by (R3) for
     `Realization.IsCoverHollowAtBlock` (`Realization.HollowReceiving.withoutRigidCore`; strictly
     weaker not shown); the main theorem
     `densitySentence_hasThinAlephOneSpectrum_of_restrictedTerminalClassification`; and, for F,
     `MainTheorem.countable_isoClasses_terminalAt_of_restrictedTerminalClassification`.
   - F: `MainTheorem.loss_subset_terminalClasses`, unconditional;
     `MainTheorem.terminalClasses_subset_iUnion`, conditional on `ContinuationCriterion`;
     `MainTheorem.countable_isoClasses_terminalAt` (countably many classes terminal at each
     countable level), conditional on these and on (R1), (R2), and (R3) for
     `Realization.IsCoverHollowAtBlock`, through E's `Expansion.subsingleton_classes_of_property`
     and `Counting.countable_of_subsingleton_cover`; the rigid-core comparison keeping the core,
     `ModelExpansion.exists_equiv_comp_eq_of_isGloballyRigidCore` (`Expansion/Losses`),
     conditional on (R1); the transport of terminality along a bijection of carriers,
     `Realization.IsTerminalAt.map` (`Continuation/Terminal`), unconditional.  Examples:
     `MainTheorem/TerminalClassesExamples` (the losses from the count, the base block `β = 0`,
     the pointed comparison at the empty core).
6. Domain hypotheses of the counting theorem, the upper and lower bounds, thinness, and the
   reduction to `ℕ` (all countable carriers).  Status: the conditional compositions of both routes
   are compiled, on `ℕ` (`MainTheorem/Assembly`) and on all countable carriers
   (`MainTheorem/AllCarriers`), with the domain hypotheses of the expansion-domain route, or
   `FullPresentations` with its comparison and lower-bound hypotheses, as hypotheses, and, for the
   statements about countable models on arbitrary carriers, the cap-to-model theorem `CapToModel`
   (still to be proved).  The absence of finite models used by the reduction to `ℕ` comes from
   `CapToModel`, or from the coatom extension property at `ω`
   (`infinite_of_realize_densitySentence_of_hasCoatomExtensions`, with hypothesis
   `StageType.HasCoatomExtensions` at `ω`, still to be proved); once that property is proved, the
   reduction to `ℕ` for the density sentence no longer needs `CapToModel`.

   **The main theorem: three forms.**
   `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`
   (`MainTheorem/ModelExpansionDomains`) is compiled conditionally on seven named hypotheses:
   `CapToModel`, (R1), forcing donors, `ContinuationCriterion`, (R2), (R3), and nonempty losses.
   `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions`,
   with its form on all countable carriers
   `vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions`
   (`MainTheorem/Composition`), is compiled conditionally on six: (R1), forcing donors,
   `ContinuationCriterion`, (R2), (R3), and `StageType.HasApexCoatomExtensions` at every countable
   block stage.  Derived in it, not assumed: `CapToModel` (`CapToModel.of_hasApexCoatomExtensions`,
   at `λ_0 = ω`, for the carriers of every universe), next-block uniqueness
   (`Expansion.NextBlockUniqueness.of_forcingDonors`), countable losses
   (`Expansion.expansionDomain_loss_countable`), and nonempty losses
   (`hasNonemptyLosses_of_hasApexCoatomExtensions`).  The seven-hypothesis form is kept; the
   six-hypothesis form is obtained from it by the two derivations above
   (`CapToModel.of_hasApexCoatomExtensions`, `hasNonemptyLosses_of_hasApexCoatomExtensions`).  No
   converse is known; the seven-hypothesis form is not derived from the six-hypothesis form.
   `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'`,
   with its form on all countable carriers
   `vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'`
   (`MainTheorem/Composition`), is compiled conditionally on five: (R1), `ContinuationCriterion`,
   (R2), (R3), and `StageType.HasApexCoatomExtensions` at every countable block stage.  It is the
   six-hypothesis form applied with forcing donors at every countable block derived from
   `StageType.HasApexCoatomExtensions` at the next block stage
   (`forcingDonors_of_forall_hasApexCoatomExtensions`, `Extension/ForcingDonorsCoatom`).  Derived
   in it, not assumed: `CapToModel` (from the coatom extension property with apex at `λ_0 = ω`),
   forcing donors (from it at the next block stage), next-block uniqueness (from (R1) and forcing
   donors), countable losses (from (R1), `ContinuationCriterion`, (R2) and (R3)), and nonempty
   losses (from the coatom extension property with apex and next-block uniqueness).  No compiled
   theorem derives next-block uniqueness or countable losses from the coatom extension property
   with apex alone; both derivations use (R1).  The hypothesis count went from seven to six to five
   only by these compiled derivations; no hypothesis is proved, and the seven- and six-hypothesis
   forms are kept.  The five-hypothesis restricted form, with (R3) restricted, is a separate
   statement (prospective).

7. Acceptance lemma 1 (same-level maximal realization; `README.md`, "Reduction to full
   presentations"): for a countable `β`, on every countably infinite carrier, a model at
   `λ_β = blockStage β` that realizes every legal stage type at `λ_β`, receives every legal donor
   exactly over every actual root, and is cover-hollow and terminal at `β`, with a prescribed
   tuple covering a prescribed legal stage type.  Status: compiled conditional on
   `StageType.HasApexCoatomExtensions (blockStage β)` and `ForcingDonors β`, both still to be
   proved (`exists_sameLevelMaximal`, `exists_sameLevelMaximal_covers`,
   `MainTheorem/SameLevelMaximal`).  The realization is the reconstruction of a Fraïssé limit of
   the uncapped age of all legal charts (`exists_isFraisseLimit_legalAge`, under
   `StageType.HasCoatomExtensions` only), a model with exact receiving of legal donors under the
   apex form (`exists_saturated_reconstruct`); `ForcingDonors β` enters only for cover-hollowness
   (`Realization.isCoverHollow_of_exactReceivingWithin`), and terminality of every cover-hollow
   realization at a block stage is compiled with no hypothesis
   (`Realization.IsCoverHollow.isTerminalAt`).  `ContinuationCriterion`, (R1), uniqueness of
   expansions, and global termination are not used.  Unbounded top-grade growth of the realization
   is still to be proved and is not used.

**A listed future repin, outside the order 1–7.**  A repin of InfinitaryLogic to a revision
containing `2cd44c3` (or the release tag that follows it) has been neither made nor decided.  A
controlled move, if undertaken, would be a separate checkpoint, before the first application of
the greatest-stage theorem or of Scott separation, done as the move to `e460cb6` (this
repository's pull request #97): the revisions in `lakefile.toml` and `lake-manifest.json` changed
as in that pull request, which edited the manifest by hand, and the `lakefile.toml` comment on
bumping (which runs `lake update InfinitaryLogic`) and its list of merged pull requests updated to
match; the toolchain and Mathlib checked against InfinitaryLogic's manifest at the new revision;
ComputableModelTheory built against it; call sites adapted with no statement changed; the
statements listed as available upstream ("Dependency pins") `#check`ed in
`SuggestedInterfaces.lean`; and that subsection updated.  Until such a repin is recorded in
"Dependency pins", no statement here applies the greatest-stage theorem or Scott separation.

**Six non-implications, as examples.**  Each is a statement that fails in general, to be shown by
an example in the examples module of its layer; only the second is compiled.

1. Rank domination is not strict increase: on a rooted tree, a labelling by ordinals that is at
   least as large at a parent as at each child need not be a rank (strictly larger at a parent than
   at each child).  Where: `COMPANIONS.md`, "Further companion results", "Full trees".  Not
   compiled.
2. A finite cap does not distinguish the formal top from a sufficiently high proper label: at a
   permitted cutoff `c` of a stage `α`, the labels `c` and `⊤` have the same observation at `c`,
   while stage reduction to `α` keeps them apart.  Where: layer 1, and the flattening of finite
   parts in 2.4–2.5.  Compiled in this repository (theorem named):
   `Label.IsPermittedCutoff.exists_min_eq_min_reduce_ne` (`Label/Cap`).
3. Receiving at every permitted cutoff below a limit `δ` does not give receiving at the cutoff `δ`:
   different cutoffs may be served by different occurrences, and none need agree with the donor
   below `δ`.  Where: layer 3 (`README.md`, Layer 3, 3.4), with the examples of receiving.  Not
   compiled.
4. Coherent projection does not lift an arbitrary projected donor over a prescribed root: lifting
   depends on the root, not only on its projection.  Where: layer 3 (`README.md`, Layer 3, 3.3, the
   density boundary, whose four-point example of abstract observation systems is informal).  Not
   compiled.
5. Branching at nodes of high rank does not give the extension property at nodes of low rank.
   Where: `COMPANIONS.md`, "Full trees".  Not compiled.
6. That every member of a class `K` has a full presentation, with all its labels, does not make `K`
   the class of models of a sentence of `L_{ω₁,ω}` in the base language; the fundamental theorem
   uses no definability of `K` (`README.md`, "Reduction to full presentations").  Where: the
   full-presentation route, with the examples of `MainTheorem/Examples`.  Not compiled.

At every checkpoint: full build, strict per-file checks, no `sorry`, standard axioms only,
universe/empty/repeated-coordinate special cases, and review of semantic statements.  Audit proof
dependencies **and** import closures separately.  Passing CI is not a substitute for checking
the statements against the roadmap and the semantic contract.

The library may grow Lean while shortening the informal proof.  Prefer applications of standard
logic and descriptive set theory, and exact statements of the constructions, over a smaller
file count.  Do not reproduce compatibility layers, abandoned proof strategies, rank detours,
or lemmas with no application.

### Checkpoints 2.1–2.7: the completion of the coatom extension construction

(R6) is reduced to the coatom extension property at a stage (`README.md`, Layer 3, 3.1, under
"(R6)"): any two legal stage types on the two coatoms of `m + 2` points that agree literally on
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
  built); the cap preserved on every coordinate, and the locality of inherited long rows explicit.
  Established, compiled in this repository (theorem named): 2.4a, grade cuts (`Extension/GradeCut`),
  source prefixes (`Extension/SourcePrefix`), restoration with the one-grade lift decomposition
  (`CellScheme.Rows.exists_restoration`, `CellScheme.Rows.cappedLift_of_ownerCappedLift`,
  `Extension/Restoration`: an owner label at most the cap gives the lift below the cap, and an owner
  label above the cap, the cap `⊥` included, an owner-capped lift restored at the owner label, which
  is the shape of the recursion step of 2.6), and inherited long-row locality
  (`CellScheme.Rows.IsLawful.map_of_isLowerEmbedding`, `Extension/InheritedLocality`); and 2.4b-i,
  positive-cap transport of lawfulness, with the bottom pattern as the only obstruction and a cap
  other than `⊥` necessary (`CellScheme.Rows.IsLawful.map_of_bot_iff`,
  `CellScheme.Rows.IsLawfulBelow.map_of_min_eq`, `Extension/CapTransport`), and the flattened source
  of the prescription, the source of the owner alignment
  (`CellScheme.Rows.IsLawfulBelow.flattenedSource_prescription`, `Extension/FlattenedSource`).
  Flattening keeps the prescribed face and the observation at every cap through the encoder's own
  decoder at a coding grade `K ≤ m`, and only for that decoder; the cap observation transfers to any
  decoder that agrees with it on the labels short at `m`
  (`Label.min_apply_flattenedSource_of_agree`).  And 2.4b-ii, the alignment of owners: the
  owner-local alignment, for every lawful source short at the grade of the owner
  (`Label.exists_ownerAlignment`, `CellScheme.Rows.IsLawfulBelow.exists_ownerAlignment`) and on the
  flattened source (`CellScheme.Rows.IsLawfulBelow.exists_ownerAlignment_flattenedSource`;
  `Extension/OwnerAlignment`); the aligned encoding, with the literal reading of the prescription
  capped at the owner label and the transfer of the cap observation to every cell below the target
  pair, the new cells and the cells of the other coatom included
  (`CellScheme.Rows.IsLawfulBelow.exists_alignedEncoding`, `Label.alignedDecode_alignedEncode`,
  `Label.min_alignedDecode_eq`; `Extension/AlignedEncoding`); the decoding to owner-capped lifts
  from a source with lifts at its ambient (`CellScheme.Rows.hasOwnerCappedLifts_of_source`), the
  serving cell (`CellScheme.Rows.hasOwnerCappedLifts_of_rows`), the boundary lift across the other
  coatom (`CellScheme.Rows.exists_lift_of_boundary`, `CellScheme.Rows.cappedLiftAt_of_boundary`),
  the cap `⊥` with literal top (`CellScheme.Rows.hasOwnerCappedLifts_bot_of_boundary`), and the
  one-grade lift (`CellScheme.Rows.hasOwnerCappedLifts_of_boundary`,
  `CellScheme.Rows.cappedLift_of_boundary`; `Extension/OwnerCappedLift`).  2.4 is complete.  The
  one-grade lift from `(C, j + 1)` to `(B, j + 1)` takes six hypotheses: (1) finiteness below
  `(C, j + 1)`, and cells of graded index `(C, j + 1)` and `(B, j + 1)`; (2) the lift at the lower
  grade, from `(C, j)` to `(B, j)`; (3) the boundary lifts, from `(C, j + 1)` to the coatom `U`
  containing it and from the common face `O` to the other coatom `V`; (4) at every cell of graded
  index `(B, j + 1)`, a row lawful below `(B, j + 1)`, short at `j + 1`, never the formal top, along
  which the rows extend from the boundary at every positive cap self-visible at `j + 1`; (5) the
  extension from the boundary at the cap `⊥`; (6) at `j = 0`, the shortness of (4) on the actual
  rows of grade `1`.  (1)–(3) come from the scheme reached after grade `j` and from the amalgam;
  (4)–(6) are placed under 2.5 and 2.6.  **Shortness.**  The alignment uses a source short at the
  grade of the owner, while the normal forms of 2.3 are strongly coded but not short (finite parts
  up to the grade plus one); in the one-grade step that source is the row of the serving cell, and
  the tail codes of the aligned encoding are translations of strongly coded codes, which need not
  be strongly coded themselves.
- **2.5. The two small arities.**  `m = 0` and `m = 1` as two separately stated constructions on
  their actual rows: arbitrary lawful prescriptions, literal top, the boundary retained, the cap
  preserved on every auxiliary cell.  The full-scope cells of each grade are indexed by the
  canonical (rank-normalized) lawful patterns of the cells below, not by all short coded patterns;
  the rows between them are agreement heights on a grid.  Acceptance for 2.5a includes the
  canonical catalogue and the key lemma, relative room.  Established, compiled in this repository
  (theorem named): 2.5a.  The canonical code (`Label.canonicalCode`, `Extension/FieldLayer`), a
  rank normalization written directly rather than the flattened source of 2.4 (whose ranks count
  successor blocks and which is not idempotent): idempotence (`Label.canonicalCode_canonicalCode`),
  prefix stability (`Label.canonicalCode_eq_of_min_eq`), relative room
  (`Label.min_canonicalCode_eq`), and the literal-reading decoder (`Label.literalDecoder`, a witness
  bounded by the grade that reads the code literally and keeps the cap; it need not be the identity
  on the labels `[ω * c, h)` of the strip of a cap `h = ω * c + k`, the strip of `README.md`,
  Layer 3, 3.1, (R6)).  The canonical field layer (`Scheme.fieldLayer`): consistent, well formed,
  coded, new rows short at the grade and never `⊤` (`Scheme.isShort_ne_top_row_fieldLayer`), with
  no hypothesis on the grades of the old cells; and, over a scheme whose cells all have grade `k`
  and lie below one of the two pairs of the boundary, extension at the cap `⊥`
  (`Scheme.exists_isLawful_fieldLayer`) and extension from the boundary at `⊥` and at every
  positive self-visible cap along every new row (`Scheme.extendsFromBoundary_bot_fieldLayer`,
  `Scheme.extendsFromBoundary_fieldLayer`).  So hypotheses (4)–(6) of the one-grade lift
  `CellScheme.Rows.cappedLift_of_boundary` of 2.4b-ii hold for this layer over a scheme whose cells
  all have grade `1` (`m = 0`), at every positive self-visible cap; no variant restricted to the
  source caps of the owner alignment is needed.  For 2.5b, where old cells of other grades occur,
  they are proved through the orbit codes (below); for 2.6, see there.  The completion at
  `m = 0` (`Seed.exists_completionBelowFullGrade_zero`,
  `Seed.nonempty_completionBelowFullGrade_zero`, `Extension/SmallArities`), with bountifulness by
  the coatoms, the lifts off the full face from the amalgam through a source prefix, and no stage
  hypothesis.  The flat catalogue (all lawful short coded patterns over a fixed alphabet) is
  refuted (`SmallArityExamples.not_isBountiful_flatRows`).
  2.5b (`m = 1`) is compiled in this repository (theorem named), with no hypothesis on the stage:
  the orbit codes (`Label.orbitCode`, `Extension/OrbitCode`; label strips, not automorphism
  orbits), the field layer at mixed grades and the short-cap one-grade lift
  (`CellScheme.Rows.cappedLift_of_boundary_short`), the lifts from a coatom to the full face
  (`Seed.cappedLift_fieldLayerOne_one`, `Seed.cappedLift_fieldLayerOne_two`), and the completion
  (`Seed.nonempty_completionBelowFullGrade_one`; at both small arities,
  `Seed.nonempty_completionBelowFullGrade_of_le_one`, `Extension/SmallArityOne`). The decision on
  the cap during a lift at grade `2` is verified: the lift at grade `1` serves as the boundary lift
  into `(univ, 1)`, and the cap is kept on the new cells of grade `1`
  (`SmallArityOneExamples.exists_lift_fourCellPairSeed`). So 2.5 is complete.
  `StageType.HasCoatomExtensions` needs every arity and is still to be proved (2.6–2.7).
- **2.6. Recursion on the grade.**  One grade step from the predecessor grade already
  established first, then the general step; lawfulness, consistency, the prefix equations, and
  unrestricted lifting (the last two defined with 2.6) are distinct statements.  The one grade step
  is `CellScheme.Rows.cappedLift_of_boundary` (2.4) once the new rows of full scope satisfy its
  hypotheses (4) and (5): their consistency, their shortness at grade at least `2` (from their
  support), never the formal top (used only at the owner cell), and the extension from the
  boundary, along the row of each serving cell at every positive cap self-visible at the grade, and
  at the cap `⊥`; and, for the legality of the scheme reached, their coding.  Bountifulness then
  follows with `CellScheme.Rows.isBountiful_of_coatoms`,
  `CompletionBelowFullGrade.cappedLift_of_ne_univ`, and `CellScheme.Rows.cappedLift_of_fst_eq`.
  If 2.6 needs it, the extension from the boundary may be weakened to the boundary labellings that
  the proof supplies: never the formal top and, when the serving row is coded, below `ω²`.
  The grade step uses the canonical catalogue at every grade; its normalization must handle values
  not self-visible at the grade (the labels of cells of lower grade), and the cap on the layers of
  lower grade during the lifts at a higher grade is the design point to settle with 2.5b.
  Status, compiled in this repository (theorem named) unless marked otherwise. 2.6a: the tower of
  field layers (`Seed.tower`, `Extension/Tower`), the lifting invariant (`Seed.TowerInvariant`),
  and the step (`Seed.towerInvariant_succ`), which uses the amalgam boundary at every cap and, at
  the short positive caps, the two-face lift `2FL(j)` (`Seed.TwoFaceLift`) at the grades
  `2 ≤ j + 1 ≤ m`; the step to the top grade `m + 1` needs only the invariant at `m`
  (`Seed.towerInvariant_top`). 2.6b: `2FL(1)` at every arity (`Seed.twoFaceLift_one`,
  `Extension/TwoFaceLift`: the serving cell, the source cap without an owner, the prescription
  falling in the first case of the owner alignment `Label.exists_ownerAlignment` because every
  value of a row at the grade `1` is self-visible there, the two-face aligned encoding, the
  extension of the canonical code, and decoding). 2.6c: bountifulness, legality below
  the full grade, and the completion from the invariant at the top grade (`Seed.isBountiful_tower`,
  `Seed.isLegalBelowFullGrade_tower`, `Seed.completionBelowFullGradeOfTowerInvariant`); the
  completion is unconditional at `m ≤ 2` (`Seed.nonempty_completionBelowFullGrade_of_le_two`).
  Refuted, each for a legal seed (negative special cases): the union fill as a universal statement
  (`UnionFillCounterexample.not_unionFill_seed`; its case within the face holds,
  `Seed.exists_lift_union_of_lt_grade`), and `2FL(2)`
  (`TwoFaceLiftCounterexample.not_twoFaceLift_two`, for `TwoFaceLiftCounterexample.seed4` on five
  points), so `2FL(j)`, `j ≥ 2`, is a hypothesis on the seed and not a property of every seed
  (`TwoFaceLiftCounterexample.not_forall_twoFaceLift`). That seed has a completion
  (`TwoFaceLiftCounterexample.nonempty_completionBelowFullGrade_seed4`) by the dead-cell step
  (`Seed.towerInvariant_succ_of_dead`, `Extension/DeadCellStep`), and per seed the completion holds
  when each grade `2 ≤ j < m` has `2FL(j)` or `Seed.DeadAt j`
  (`Seed.towerInvariant_of_twoFaceLift_or_deadAt`,
  `Seed.nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt`). That this case split covers
  every seed is refuted, and the exact hypothesis of the step, the existential two-face lift
  `2FL∃(j)`, is compiled and fails for a legal seed (both under 2.7).
- **2.7. The theorem.**  At a stage that is zero or a limit the apex form holds; hence the plain
  form and (R6).  The improvement from limit stages to zero-or-limit stages is a separate lemma,
  with the zero stage handled explicitly.  That truncation to the stage fails at successor stages
  does not prove that the property fails there; that would need its own counterexample.  Whether
  it holds at successor stages is open and not needed.
  Status: still to be proved (the statement is `StageType.HasApexCoatomExtensions` at the stages
  that are zero or a limit), and not refuted. The completion below the full grade gives the apex
  form (`StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`,
  compiled in this repository (theorem named)), quantifying over the seeds of every arity. 2.7 is
  not conditioned on the universal two-face lift, which is false at every stage (2.6), and no
  theorem is stated under it. A *boundary triple*
  (`Extension/Tower`) for the one-grade lift from `(C, j + 1)` to `(B, j + 1)` is a triple of pairs
  `U, V ≤ (B, j + 1)` and `O ≤ U, V` with `(C, j + 1) ≤ U`, every cell below both `U` and `V`
  lying below `O`, together with capped lifts from `(C, j + 1)` to `U` and from `O` to `V`; it is
  the input of `CellScheme.Rows.cappedLift_of_boundary_short`. Neither boundary triple
  of the library for the step to `j + 1 ≤ m` serves every seed: the triple through `(D, j + 1)`
  uses `2FL(j)`, refuted at `j = 2`, and the triple through `(univ, j)` uses the union fill,
  refuted at the grade `2`.
  Compiled in this repository (theorem named): the existential two-face lift `2FL∃(j)`
  (`Seed.TwoFaceLiftExists`, `Extension/TwoFaceLiftExists`): for every catalogue entry `a` at
  `j + 1`, every cap `h` self-visible and short at `j + 1` with `⊥ < h`, and every `w_C` lawful
  below `(C, j + 1)` agreeing with `a` capped at `h`, some `w_D` lawful below `(D, j + 1)`, equal
  to `w_C` on the cells of the common face of grade at most `j + 1` and agreeing with `a` capped at
  `h`, is such that the glued labelling has the conclusion of `2FL(j)`. It is the step of the
  tower, stated exactly: for `j ≤ m` and under the invariant at `j`, the invariant at `j + 1`
  holds exactly when `2FL∃(j)` does (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`), and the
  invariant at the top grade holds exactly when `2FL∃(j)` holds at the grades `2 ≤ j < m`
  (`Seed.towerInvariant_top_iff`). Sufficiency (`Seed.towerInvariant_succ_of_twoFaceLiftExists`)
  uses `CellScheme.Rows.cappedLift_of_boundaries_short` with the degenerate triple
  `U = V = O = (C, j + 1)` at the positive caps, so no separate choosing variant of the one-grade
  lift is needed. `2FL(j)` implies `2FL∃(j)` for `j ≤ m`
  (`Seed.twoFaceLiftExists_of_twoFaceLift`), and so does `Seed.DeadAt j` under the invariant at `j`
  (`Seed.twoFaceLiftExists_of_deadAt`); a seed with `2FL∃(j)` at the grades `2 ≤ j < m` has a
  completion below the full grade (`Seed.nonempty_completionBelowFullGrade_of_twoFaceLiftExists`).
  Refuted, each for a legal seed on five points (negative special cases): the coverage of every
  seed by the case split `2FL(j) ∨ Seed.DeadAt j`
  (`CaseSplitCounterexample.not_forall_twoFaceLift_or_deadAt`, at `CaseSplitCounterexample.seed5`,
  where `2FL∃(2)` holds: `CaseSplitCounterexample.twoFaceLiftExists_and_not_twoFaceLift_or_deadAt`),
  and `2FL∃(2)` itself, for the seed `TwoFaceLiftExistsCounterexample.seedL` of the coatom types
  `TwoFaceLiftExistsCounterexample.TL` and `CaseSplitCounterexample.T5`
  (`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_seedL`). So `2FL∃(j)` at the grades
  `2 ≤ j < m` for every seed is false at every stage
  (`TwoFaceLiftExistsCounterexample.not_forall_twoFaceLiftExists`), and for `seedL` the invariant
  of the tower fails at the top grade
  (`TwoFaceLiftExistsCounterexample.not_towerInvariant_top_seedL`). No theorem is stated under the
  universal form of `2FL∃(j)`, and 2.7 is not conditioned on it. The per-seed completions remain:
  at `m ≤ 2`, under the case split or under `2FL∃(j)` (2.6 and above), and for the two seeds above
  (`TwoFaceLiftCounterexample.nonempty_completionBelowFullGrade_seed4`,
  `CaseSplitCounterexample.nonempty_completionBelowFullGrade_seed5`). For `seedL`, the identified
  obstruction (every new cell of the tower at `(univ, 2)` where the catalogue entry of the failure
  reaches its cap reads the cells `({3}, 1)` and `({4}, 1)` at one value) survives the redesigns
  examined (argued, not formalized; the module docstring of
  `Extension/TwoFaceLiftExistsCounterexample`).
  Compiled in this repository (theorem named), outside the tower: `seedL` has a completion below
  the full grade (`ThinCompletion.nonempty_completionBelowFullGrade_seedL`,
  `Extension/ThinCompletion`), the **thin completion**, the amalgam with one new cell at each
  graded face `(univ, k)` of full scope below the full grade, labelled `⊤` at the cells of grade
  `4` and `⊥` elsewhere. The identified obstruction does not apply to it: its only cell at
  `(univ, 2)` reads `({3}, 1)` strictly below `({4}, 1)`
  (`ThinCompletionExamples.row_newCell_two_lt`). With the apex added it gives, at every stage, a
  legal stage type on five points whose faces along the two coatoms are `TL` and `T5`, with a cell
  of full scope and full grade carrying the largest label
  (`ThinCompletionExamples.exists_coatomExtension_seedL`, `Extension/ThinCompletionExamples`); so
  `seedL` is not a counterexample to `StageType.HasApexCoatomExtensions` at `m = 3`.
  The ordered-layer step at `m = 3` (`Extension/OrderedLayerStep`, `Extension/OrderedLayerTop`,
  `Extension/OrderedLayerExamples`, `Extension/OrderedLayerObstruction`; compiled in this repository
  (theorem named) unless marked otherwise). The layer scheme `OrderedLayer.layerScheme I ρ` is the
  amalgam followed by one new cell at each `(univ, k)`, `k = 1, …, 4`, whose row reads the graded
  indices by `ρ k`. Named hypothesis `Seed.OrderedLayerStep I ρ`: coded rows; each new row lawful
  below `(univ, k)`; the capped lifts from `(C, k)` and `(D, k)` into `(univ, k)` (the only lifts
  needing capping, `OrderedLayer.isBountiful_layerScheme`); a lawful extension of the glued
  labelling. It gives a completion (`Seed.OrderedLayerStep.completion`) and is exactly legality of
  the layer scheme with a lawful extension (`Seed.orderedLayerStep_iff`), a restriction of the
  completion and strictly stronger than it (`seedHG` has a completion and no ordered-layer step,
  `CrossedCouplingCounterexample.not_forall_hasOrderedLayerStep_of_nonempty`). For seeds with
  bottom apexes (`Seed.HasBottomApexes`,
  `Seed.hasBottomApexes_of_addApex`) and the top row at `(univ, 4)`, the step follows from its
  fields at `k ≤ 3` (`Seed.OrderedLayerStepBelowTop.orderedLayerStep`,
  `OrderedLayer.cappedLift_four`), and those lifts reduce to the grade `3`
  (`OrderedLayer.cappedLift_of_lift_three`). Instances:
  `seed4`, `seed5`, `seedL` (`Seed.orderedLayerStep_seed4`, `Seed.orderedLayerStep_seed5`,
  `Seed.orderedLayerStep_seedL`), the mirror `seedLM` of `seedL` with rows oriented `D` before `C`
  (`Seed.orderedLayerStep_seedLM`, `Extension/ThinCompletionMirrorExamples`), and `seedLL` of `TL`
  with itself, with rows reading both coatoms at one value (`Seed.orderedLayerStep_seedLL`,
  `Extension/ThinCompletionTLTL`). The orientation is forced and depends on the seed
  (`Seed.OrderedLayerStep.thinRow_lt_of_TL_T5`, `Seed.OrderedLayerStep.rowsLM_lt_of_T5_TL`,
  `not_exists_orderedLayerStep_seedL_seedLM`). Forced separations in every completion of every seed
  (`CompletionBelowFullGrade.exists_separating_of_forcesTop`, from `Seed.ForcesTop`); two opposite
  forcings at one grade give two cells at one graded face of full scope
  (`CompletionBelowFullGrade.exists_ne_of_forcesTop`) and exclude the ordered-layer step
  (`Seed.not_hasOrderedLayerStep_of_forcesTop`). Refuted (negative special case named): the
  ordered-layer step for every seed on five points
  (`CrossedCouplingCounterexample.not_forall_hasOrderedLayerStep`), at the legal seed
  `CrossedCouplingCounterexample.seedHG` of the types `TH`, `TG` coupled crosswise to two parameters
  of the common face (`Extension/CrossedCouplingTypes`, `Extension/CrossedCouplingCounterexample`;
  `CrossedCouplingCounterexample.exists_ne_seedHG`: every completion has two cells at `(univ, 1)`).
  No theorem is stated under the refuted universal form. This refutes the step, not the completion.
  The multi-layer step at `m = 3` (`Extension/MultiLayerStep`, `Extension/CrossedCouplingScheme`,
  `Extension/CrossedCouplingCompletion`; compiled in this repository (theorem named) unless marked
  otherwise). The multi-layer scheme `OrderedLayer.multiLayerScheme I M r` is the amalgam followed
  by `M k` new cells at each `(univ, k + 1)`, the `i`-th with row `r k i`, read off cells. Named
  hypothesis `Seed.MultiLayerStep I M r`: positive multiplicities; coded rows; each new row lawful
  below its graded index; the capped lifts from `(C, k)` and `(D, k)` into `(univ, k)`
  (`OrderedLayer.isBountiful_multiLayerScheme`); a lawful extension of the glued labelling. It
  gives a completion (`Seed.MultiLayerStep.completion`) and is exactly legality of the
  multi-layer scheme with a lawful extension (`Seed.multiLayerStep_iff`); with arbitrary rows it
  reformulates the completion at `m = 3` (argued, not formalized). `seedHG` has a completion below
  the full grade (`CrossedCouplingCounterexample.nonempty_completionBelowFullGrade_seedHG`,
  `CrossedCouplingCounterexample.completionHG`), every field proved: the multi-layer step of
  every seed of the types `TH` and `TG` with two new cells at `(univ, 1)`, one per forced
  separation, and one at each `(univ, k)`, `k = 2, 3, 4`
  (`CrossedCouplingCounterexample.multiLayerStep_HG`); its lawful labellings are labellings by
  kinds of `A_C`, `A_D`, `H`, `G` with the couplings of both types
  (`CrossedCouplingCounterexample.isLawful_kindLabel`,
  `CrossedCouplingCounterexample.exists_of_isLawfulBelow_univ`); the lifts
  `CrossedCouplingCounterexample.cappedLift_C_of_le_three`,
  `CrossedCouplingCounterexample.cappedLift_D_of_le_three`,
  `CrossedCouplingCounterexample.cappedLift_four_HG`, which, like `OrderedLayer.cappedLift_four`,
  quotes the lift at the grade `4` from the grade `3` in a scheme over the amalgam of a seed with
  bottom apexes (`OrderedLayer.cappedLift_four_of_oldCells`); the coatom extension of `TH` and `TG`
  with apex at every stage (`CrossedCouplingCounterexample.exists_coatomExtension_seedHG`).
  The canonical multi-layer scheme at `m = 3` (`Extension/CanonicalMultiScheme`,
  `Extension/CanonicalMultiSchemeCounterexample`, `Extension/CanonicalMultiSchemeExamples`;
  compiled in this repository (theorem named) unless marked otherwise). For every seed and copy
  rows `R`: two copies of the cells at `(C, k)` and `(D, k)` at each `(univ, k)`, reading through
  their bases (`OrderedLayer.canonicalMultiScheme`); forcedness
  (`OrderedLayer.eq_copyOrig_of_isLawfulBelow`); the lifts from the common face
  (`Seed.hasCommonFaceLifts`). Named hypothesis: the product clause `Seed.CanonicalProduct I R j`,
  a sufficient hypothesis for the step, not a field of `Seed.MultiLayerStep`. It gives the
  classification as pairs agreeing on the common face (`OrderedLayer.isLawfulBelow_canonical_iff`)
  and the lifts (`OrderedLayer.cappedLift_of_canonicalProduct`). The conditional step theorems,
  with the status of each hypothesis: (a) `Seed.canonicalMultiStep_of_product` assumes the product
  clause at the grades 1–4 (refuted at the grade 4 at all six compiled seeds, so this form applies
  at none of them), `hcode` (copy rows coded) and `hpair` (copy rows lawful below both coatoms),
  the last two conditions on the choice of copy rows; (b)
  `Seed.canonicalMultiStep_of_productBelowTop` assumes the product clause at the grades 1–3 (holds
  for `seedHG`, `OrderedLayer.CanonicalHG.canonicalProduct`; refuted at the grades 2, 3 for the
  other five seeds), `hcode` and `hpair` at those grades (compiled for `seedHG`,
  `OrderedLayer.CanonicalHG.rowsHG_lt`, `OrderedLayer.CanonicalHG.isLawfulBelow_rowsHG`),
  `Seed.HasBottomApexes` (compiled for all six seeds) and `hR3`, the top row at the grade 4 (a
  choice of the copy rows); its grade 4 comes from the grade 3
  (`OrderedLayer.cappedLift_four_of_oldCells`), not from the product clause. With every
  hypothesis compiled, the second form completes `seedHG`
  (`Seed.nonempty_completionBelowFullGrade_canonical_seedHG`). Both completions of `seedHG` obtain
  the grade 4 from the labelling of `Ω` alone at the top row through
  `OrderedLayer.cappedLift_four_of_oldCells`, never from a fibre product, and under the top row the
  labellings of the decoding refutation are not lawful below `(univ, 4)`
  (`OrderedLayer.eq_bot_of_grade_four_canonical`). Refuted (negative special cases
  named), for every copy rows: at the grades 2–4 for `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL`
  (`Seed.not_canonicalProduct_seed4` and its companions, by crossing,
  `OrderedLayer.not_canonicalProduct_of_crossing`), and at the grade 4 for all six seeds
  (`Seed.not_canonicalProduct_seedHG`, by decoding,
  `OrderedLayer.not_canonicalProduct_of_decoding`).
  This refutes the family as a fibre product at those seeds, not the family's step (which holds
  for `seedHG` at the grade 4, where the clause fails) and not the completion.
  Oriented copy rows (`Extension/CanonicalMultiSchemeOriented`,
  `Extension/CanonicalMultiSchemeOrientedExamples`; compiled in this repository (theorem named)
  unless marked otherwise). Layer rows oriented toward a coatom (`OrderedLayer.IsOriented ρ b`, a
  condition on the rows alone) give the oriented copy rows `OrderedLayer.orientedRows I ρ`, under
  which both copies of a grade read every old cell by the layer row; the lawful labellings are, on
  the old cells, those of the layer scheme (`OrderedLayer.isLawfulBelow_oriented_iff`), a
  restriction of the pairs. Under oriented rows the step of the family *is* the ordered-layer step
  (`Seed.canonicalMultiStep_oriented_iff`, an exact reformulation: both copies of a grade read
  alike, so the family adds nothing to the layer scheme), with no further hypothesis; the clause
  for these rows is the ordered-layer step itself, with oriented rows (`Seed.HasOrientedLayerStep`).
  The orientations are compiled for `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL`
  (`OrderedLayer.isOriented_layerRows4` and its companions); with the ordered-layer steps
  (`Seed.orderedLayerStep_seed4`, `…_seed5`, `…_seedL`, `…_seedLM`, `…_seedLL`), which already
  complete these five seeds, they give `Seed.HasOrientedLayerStep` there.  What is new is only that
  the canonical multi-layer scheme itself has a step at them
  (`Seed.nonempty_completionBelowFullGrade_seed4_oriented` and its companions); every one of the six
  compiled seeds has a step of the family
  (`Seed.hasCanonicalMultiStep_seed4_seed5_seedL_seedLM_seedLL_seedHG`), and no seed refutes it.
  Refuted (negative special cases named; corollaries, through the iff, of
  `CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG` and
  `not_exists_orderedLayerStep_seedL_seedLM`), for oriented rows only: at `seedHG`
  (`Seed.not_canonicalMultiStep_oriented_seedHG`, `Seed.not_hasOrientedLayerStep_seedHG`) and as one
  choice for both `seedL` and `seedLM` (`Seed.not_exists_canonicalMultiStep_oriented_seedL_seedLM`);
  this refutes neither the family nor the completion. Open: copy rows giving the step of the family
  for every seed on five points (`Seed.HasCanonicalMultiStep` for every seed), and the completion at
  `m ≥ 3` for every seed.

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
different coatoms).  For the variant whose full-scope cells are indexed by all lawful short coded
patterns over a fixed finite alphabet, with agreement-height rows, bountifulness fails already at
`m = 0` and for every block bound at least `3` (in particular `2 N + 1` for `N` cells): a pattern
constant at the top block of the alphabet, as ambient, leaves no room above the cap for a
prescription with four distinct values on one point, once two lower constant patterns are pinned
by the cap (compiled in this repository (theorem named):
`SmallArityExamples.not_isBountiful_flatRows`).  Whether this applies to Definition 4.3.14
depends on the bindings of Definition 4.3.6; it does not apply when the patterns are
rank-normalized, as in the canonical field layer of 2.5.  Neither the statement of
Lemma 4.3.20, nor its printed proof, nor the joint lifting of [Kni26, Lemma 4.3.19] is relied on:
conclusions 1–3 of Lemma 4.3.19 cannot hold together under the natural readings of efficiency
([Kni26, Definition 4.3.6], whose bindings the text leaves open), since an instance with cap 2
and prescriptions 3 and 4 forces 3 = 4 (`README.md`, Layer 1 and Layer 3, 3.1).  The
construction chosen builds grade by grade over the boundary, in one fixed order of its cells,
chooses the full-scope cell that serves each lift (defined with 2.6) before extending on the
other coatom, and tops out in a single apex cell.

## The common core of the receiving routes

**The observation.**  The open finite hypotheses of the receiving routes, and the completion of the
coatom amalgam, ask for objects over a context (for (R1)–(R4), a context acquired in a model) whose
cells of full scope (graded index `(univ, g)`) satisfy a condition on their rows at prescribed
cells.  (R2) and (R3) ask for a legal one-point extension: the cells of full scope read each new top
of the donor at least as a private top (the reading context, a condition on stage types of the route
to determination with a private top, not on `main`; on `main`, (R2) follows from (R1) for every
model at every limit stage, `Realization.ResidualAcquisition` and `Realization.CutoffDetermination`,
and (R3) from `Realization.HollowAcquisition` and `Realization.SchemeDetermination`, README, "Status
of (R2) and (R3)").  (R1) and (R4) ask for schemes: (R1), per block, a scheme on which every coface
of the context has its cells of full scope of the top grade read the labels of one block in their
own block (block-tight saturations, `IsBlockTight` = "some scheme, and every coface on it …"); (R4),
a scheme carrying a coface of the stage reduction `T⁺↓β` whose cells of full scope of the cap's
grade read the new cells of the donor through the cap (the cap-reading scheme of the stable recovery
through a reading cell).  The completion asks for a coatom extension, with no condition on the rows.
These row-prescription conditions recur across the routes.  The four gaps stay separate: the
implications below count only as compiled, each under the **compatibility hypothesis**: the route's
prescription is compatible with the faces (`StageType.IsFaceCompatible`, defined under "The
statement" below) at the input.  For (R1) that hypothesis fails at the known refuting context
(below).

**The statement** (`Extension/PrescribedFullRows`).  A context `t'` on `k` points and a donor `d`
on `n + 1` points with the common face `t` (the face of `t'` along `h` and of `d` along the first
points); a **full-row prescription** `Φ` (`StageType.FullRowPrescription`), at each grade `g` a
condition on the readings of the known cells (those of `t'` and `d`) and of the cell itself by a
cell of graded index `(univ, g)`; a **prescribed extension** (`StageType.IsPrescribedExtension`), a
legal one-point extension of `t'` carrying `d` along `h` whose scheme extends `t'` and `d` with the
rows prescribed by `Φ` (`StageType.ExtendsWithPrescribedRows`, a condition on the scheme, so at a
stage that is zero or a limit, `Order.IsSuccPrelimit α`, generalized saturation reaches it:
`Realization.IsModel.realizesOver_extendsWithPrescribedRows`).
**Admissibility** of a row at a labelling of the known cells (`StageType.IsAdmissibleRow`): the
readings meet `Φ`, are coded, are lawful below `(univ, g)` in the rows of `t'` and of `d`, and
transform to the labelling capped at a value at least the label of the known cell served.
**Compatibility with the faces** (`StageType.IsFaceCompatible`): admissibility at every lawful
labelling of `t'` and some lawful labelling of `d` agreeing with it on `t`; **at the labels of
`t'`** (`StageType.IsFaceCompatibleAtLabels`): at the labels of `t'` only, with some lawful
labelling of `d`.  The common core is `StageType.HasPrescribedFullRows α`: every prescription
compatible with the faces over legal `t'` and `d` has a prescribed extension.  Its labels form is
`StageType.HasPrescribedFullRowsAtLabels α`.

**Compiled.**

1. Forcing: a reading of `x` at least as `s` at every cell of a graded index of the grade of `s`
   forces `p s ≤ p x` in every lawful section (`CellScheme.Rows.IsLawful.le_of_forall_row_le`);
   every lawful labelling of a face of a legal stage type extends to it
   (`StageType.exists_isLawful_extend_of_restrictFace`).
2. Necessity of both compatibility conditions for a prescribed extension
   (`StageType.IsPrescribedExtension.isFaceCompatible`,
   `StageType.IsPrescribedExtension.isFaceCompatibleAtLabels`), through
   `StageType.ExtendsWithPrescribedRows.isAdmissibleAt`.
3. The labels form is **false at every stage**
   (`PrescribedFullRowsCounterexample.not_hasPrescribedFullRowsAtLabels`): over
   `GatedExtensionCounterexample.P α` with the empty root and the one-point donor, the prescription
   that every cell of graded index `(univ, 2)` reads `C₂` at least as `C₁` is compatible at the
   labels of the context (`⊤, ⊤`; `PrescribedFullRowsCounterexample.isFaceCompatibleAtLabels`) and
   has no prescribed extension, since the lawful labelling `3, 2` extends to every legal one-point
   extension of `GatedExtensionCounterexample.P α`
   (`PrescribedFullRowsCounterexample.not_isPrescribedExtension`).  It is not
   compatible uniformly (`PrescribedFullRowsCounterexample.not_isFaceCompatible`), so the uniform
   form is not tested by this input (its compatibility premise fails there).  The labels form
   implies the uniform form (`StageType.HasPrescribedFullRowsAtLabels.hasPrescribedFullRows`); that
   implication is vacuous, its hypothesis being refuted, and is kept only as the comparison of the
   two forms.
4. The empty prescription (`StageType.emptyPrescription`): the coatom extension property makes it
   compatible (`StageType.HasCoatomExtensions.hasCompatibleEmptyPrescription`) and gives a
   prescribed extension for it (`StageType.HasCoatomExtensions.isPrescribedExtension_empty`); the
   core with its compatibility gives the coatom extension property
   (`StageType.HasPrescribedFullRows.hasCoatomExtensions`); so under the core the coatom extension
   property is equivalent to `StageType.HasCompatibleEmptyPrescription α`
   (`StageType.HasPrescribedFullRows.hasCoatomExtensions_iff`).  The core alone does not give the
   coatom extension property.
5. The routes (`Extension/PrescribedFullRowsRoutes`, with the routes' conditions stated in full):
   - (R2)/(R3): a prescribed extension for the reading prescription of a choice of private tops is
     a reading coface (`PrescribedFullRows.IsPrescribedExtension.isReadingContext`); the core with
     the compatibility of that prescription gives a reading context
     (`StageType.HasPrescribedFullRows.isReadingContext`); a reading context determines a choice
     whose reading prescription is compatible
     (`PrescribedFullRows.IsReadingContext.exists_isFaceCompatible`), so under the core, at a legal
     input `(t', d)`, `IsReadingContext t' h d` is equivalent to the existence of a choice `σ` with
     `IsTopChoice t' d σ` whose reading prescription is compatible; and a reading context forces,
     at every lawful labelling `a` of the context, a lawful labelling of the donor agreeing on the
     common face under which every new top is at least `a` at some private top of at least its
     grade
     (`PrescribedFullRows.IsReadingContext.forall_exists_le`).  The route's open passage from a
     graded context with a top to a reading context is not derived from the core.
   - (R1): a prescribed extension for the block prescription (old cells read in the own block) is
     block-tight (`PrescribedFullRows.IsPrescribedExtension.isBlockTight`); the core with the
     compatibility of every block prescription over the empty face gives block-tight saturations
     (`StageType.HasPrescribedFullRows.hasBlockTightSaturations`).  The block prescription is **not
     compatible** wherever the context has a lawful labelling that is `⊥` at a cell of the block,
     not self-visible at the top grade `N`, and not `⊥` at a cell of grade `N`
     (`PrescribedFullRows.not_isFaceCompatible_block`, with
     `PrescribedFullRows.not_isAdmissibleRow_block`).  At the refuting context of the per-block
     route, `CoupledGatedExtensionCounterexample.P α` (not on `main`), these hypotheses hold at
     every stage `α > 1`: that module proves the context legal (`isLegal_P`), its cell `z₁` is
     labelled `1` and not self-visible at the grade `2`, and it has the lawful labelling
     `⊥, ⊥, ⊥, ω + 1, ω + 2` (`isLawful_lab_bot_omegaAdd`).  So the hypothesis of
     `hasBlockTightSaturations` fails at every `α > 1` (argued from those compiled pieces; the
     joining lemma is to be compiled once that module lands), and the (R1) arrow is **not a
     reduction**.  The cause is the domain of `Φ`: it names only known cells, while block-tightness
     accepts any cell with the label, new cells included.  Redesigning the prescription to read
     cells of the donor would have to be re-tested at this input.
   - (R4): a prescribed extension for the cap prescription is a cap-reading scheme when the cap's
     grade exceeds the number of points of the donor's root
     (`PrescribedFullRows.IsPrescribedExtension.isCapReadingScheme`,
     `StageType.HasPrescribedFullRows.exists_isCapReadingScheme`).  This is only the part of the
     sufficient condition for a stable recovery scheme concerning the scheme
     (`StageType.IsStableRecoveryScheme.of_readsThroughCap`, on `main`); the composition with the
     cap's label and the calibration is not compiled here.
   - The completion: a step of the canonical multi-layer scheme of a seed
     (the multi-layer step `Seed.MultiLayerStep` on `OrderedLayer.canonicalMultiScheme`) is **not
     an instance** (argued, not compiled):
     it asks for a completion of one shape (two copies at each graded index of full scope, reading
     through their originals), while a prescribed extension for the empty prescription is a coatom
     extension of any shape.

**Status of each named hypothesis, separately.**

- `StageType.HasPrescribedFullRowsAtLabels α`: refuted at every stage.
- `StageType.HasPrescribedFullRows α`: open, a hypothesis introduced here.  Not refuted at the
  inputs tested: at `GatedExtensionCounterexample.P α` the refuting prescription is not uniformly
  compatible, so the input does not test it; at the six compiled seeds and the amalgam of `seedHG`
  the completion's coatom extensions are prescribed extensions for the empty prescription, so that
  prescription is compatible there by necessity (argued from the routes' own analyses of those
  inputs).  At the twin input of (R4) the route's analysis gives a stable recovery scheme,
  not a prescribed extension for the cap prescription, so the input does not test the core.
  Sufficiency of compatibility is unproved (it is the hypothesis itself): compatibility is asked
  per lawful labelling and per served cell, and a construction of a prescribed extension would
  still need finitely many fixed rows serving every lawful labelling, rows lawful on all of the
  extension (including the cells that are neither known cells nor the cell itself), and legality
  of the extension at every graded face.
- `StageType.HasCompatibleEmptyPrescription α`: open; implied by the coatom extension property.
- The coatom extension property (`StageType.HasCoatomExtensions α`): still to be proved, unchanged.
- Block-tight saturations ((R1), per block): undecided, unchanged.  The arrow from the core is
  vacuous at `CoupledGatedExtensionCounterexample.P α` for every `α > 1` (argued; item 5), so the
  core gives nothing here.
- The reading-context property at a legal input ((R2)/(R3)): under the core it is equivalent to a
  choice of private tops with a compatible reading prescription (item 5), and the forcing condition
  above is necessary.  Obtaining a reading context from a graded context with a top is open,
  unchanged, and not derived from the core.
- Cap-reading schemes at the calibrated inputs ((R4)): open, unchanged; conditional on the core and
  the compatibility of the cap prescription; the composition to a stable recovery scheme is not
  compiled here.
- The canonical multi-layer step (completion): open as a statement about every seed, unchanged,
  not an instance (argued).
- (R1)–(R4): neither proved nor refuted.

**What the routes have in common that fails.**  Compatibility at the labels of the context does not
make a prescription have a prescribed extension: bountifulness of the one-point extension at the cap
`⊥` makes every lawful labelling of the context count, and a reading prescribed at every cell of a
graded index forces an order on each of them.  The refuting prescription has the shape of
`ReadsAtLeast`, but between two cells `C₁`, `C₂` of the context of the same grade that the rows
order both ways; it is not the reading prescription of (R2)/(R3) for any choice (the donor has no
new top, so every reading prescription holds trivially there), and the refutation says nothing
about (R2) or (R3).  The uniform form is not tested by the refuting input.  For (R1) the uniform
form gives nothing at the per-block route's refuting context (item 5).

**The first clause that does not close.**  A general proof of `StageType.HasPrescribedFullRows`
constructs, at the empty prescription, coatom extensions at every input where the empty
prescription is compatible.  The completion results of checkpoints 2.1–2.7 give coatom extensions
only from completions below the full grade
(`StageType.HasCoatomExtensions.of_completionBelowFullGrade`), open as a statement about every
seed at `m ≥ 3`;
that is the first clause of a general proof that does not close.

**No clause of a model prescribes full rows** (argued, not compiled): no clause of
`Realization.IsModel` prescribes the row of a cell of full scope; generalized saturation only
reaches a coface on a prescribed scheme, which is why the core is stated on stage types.

**Restatements.**  The (R4) condition is `main`'s own `StageType.ReadsThroughCap`
(`Continuation/StableRecovery`), used directly.  `Extension/PrescribedFullRowsRoutes` states
`ReadsAtLeast`, `IsReadingContext`, `ReadsInOwnBlock` and `HasBlockTightSaturations` in full,
because the modules of the (R2)/(R3) route and of the per-block route are not on `main`;
`IsBlockTight` is new (the per-input body of `HasBlockTightSaturations`).  The four restatements
were checked `rfl`-equal to the routes' own declarations at the heads of the routes' branches; that
check is outside the repository.  When those modules land, the restatements are replaced by their
declarations: `ReadsAtLeast` and `IsReadingContext` by the (R2)/(R3) module's (moving
`exists_isFaceCompatible` and `forall_exists_le` beside them); `ReadsInOwnBlock` and
`HasBlockTightSaturations` by the per-block module's (keeping `IsBlockTight` beside them, and
compiling the joining lemma of item 5).  The composition of `IsCapReadingScheme` with the cap's
label and the calibration to a stable recovery scheme
(`StageType.IsStableRecoveryScheme.of_readsThroughCap`) is not compiled here.

## Companion boundaries

Companion topics: definable domain/logical cuts with strict loss-rank lower bounds; canonical
top-free classes converging sentencewise; local automorphisms of self-embeddings; and the
arbitrary-carrier Scott/`T∞` theory dichotomy.  The joint embedding and amalgamation properties of
finite top-free charts are step 2 of the top-free witnesses and belong to the core.  These do not
assert strong AP, a proper self-embedding, uncountable categoricity, Scott-rank equality, or
existence of a model of all of `T∞`.  Terminal refinement (eventual departure by Scott isolation,
the last admitted stage, and the terminal expansion; the first two compiled conditionally in
`MainTheorem/LastStage`, the third a conditional target) is never an input to the count, and its
eventual departure is proved from hypotheses of the count (the agreement of
condition 3 and the nonempty losses of condition 4, with Scott sentences), not from its conclusions;
the agreement filtration (defined by `T∞`) and the rank filtration (defined by Scott rank) are
defined differently; no relation between them is asserted, and any comparison is a separate
prospective theorem (`COMPANIONS.md`, "Further companion results").  Quantitative reconstruction
(base-language definitions and Scott sentences with bounds on their quantifier rank) and its
recognition and base-reduct orbit-rank targets are companion statements, used by neither route,
with their own completion criterion (`COMPANIONS.md`, "Further companion results"); its first row
is compiled conditionally on block determination (`Definability/BlockFormulas`), and the rest is
prospective.  The main
theorem is proved without them; if any is added, give it a separate definite completion criterion.
Direct limits of structures and the classical existence theorem (available at the pin) belong to the
two libraries, not to the finite constructions of layer 3.  [`COMPANIONS.md`](COMPANIONS.md) gives
these topics and the full-chart orbit theory below such criteria, as three milestones (A: filtration
and infinitary theory; B: top-free chart homogeneity and its consequences; C: a geometric
obstruction).

### Full-chart orbit theory: a companion checkpoint

The targets of this checkpoint are milestones B and C of [`COMPANIONS.md`](COMPANIONS.md),
which states each with its hypotheses, upstream ingredients, instantiation, special cases, and
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

## Placement record

Where a declaration of the library should live, when it is stated elsewhere, is recorded here and
not in the module that states it (`README.md`, "Library conventions", **Placement**): that module's
`## Placement` section gives only its place in the roadmap.  The entries are grouped by the module
that states the declarations; each names the destination.  Statements still to be proved, in no
module yet, are grouped last ("Statements not yet in any module").  The declarations of the Layer 2
modules under `Language/` and `Realization/` whose own notes name earlier files move to those files
directly, in the Layer 2 consolidation (pull request #34), and are not recorded here; until it
lands, their notes stay in those modules.

**Prescribed rows (Layer 3, 3.4).**

- Done: `CellScheme.Rows.IsLawful.le_of_forall_row_le` is in `Scheme/Row`; `Scheme.rowAt`,
  `Scheme.faceCell`, `Scheme.cellMap_cellMap`, `Scheme.cellMap_congr` and the lemmas of `rowAt`
  and `faceCell` are in `Stage/Scheme`; `StageType.faceCell`,
  `StageType.comap_toScheme_of_restrictFace`, `StageType.label_faceCell`,
  `StageType.grade_faceCell`, `StageType.scope_faceCell`, `StageType.isLawful_comp_faceCell`,
  `StageType.last_notMem_scope_faceCell` and `StageType.exists_faceCell_eq_of_last_notMem` are in
  `Stage/Basic`; `StageType.exists_isLawful_extend_of_restrictFace` is in `Stage/Legal`;
  `StageType.faceCell_faceCell` and `StageType.last_mem_scope_faceCell_iff` are in
  `Extension/PinnedExtension`, beside `extendByLast` (which `Stage/Basic` does not import).  The
  (R4) condition is `main`'s `StageType.ReadsThroughCap` (`Continuation/StableRecovery`).
- `Extension/PrescribedFullRowsRoutes`: the remaining restatements of the routes' conditions are
  replaced by the routes' declarations (`Continuation/AvailableTopDetermination`,
  `Realization/TightCap`, `Realization/PerBlockCarrying`) when those modules land.

**Finite geometry and the coatom amalgam (Layer 3, (R6)).**

- `Geometry/PlanAttachment`: `restrict_restrict` and `IsPlan.restrict_self`, a statement about
  convex geometries (it uses only `subset_of_mem`), to `Geometry.ConvexGeometry`, beside
  `mem_restrict`.
- `Extension/Basic`: `Fin.Embedding.univ_map_snoc` to Mathlib, `Mathlib.Data.Fin.Tuple.Embedding`,
  beside `Fin.Embedding.snoc`; `pos_of_univ_map_ne` and `univ_map_castLEEmb_ne`, facts about
  embeddings of `Fin`, are candidates for Mathlib with it.
- `Extension/Merge`: `Merge` is order theory on finite chains, not about schemes; it belongs in an
  `Order/` folder of the library, and is a candidate for Mathlib.
- `Extension/CoatomScheme`: `Geometry.IsPlan.map` to `Geometry.Plan`, beside `IsPlan.preimage`;
  `Scheme.scope_eq_of_eq`, `Scheme.grade_eq_of_eq`, `Scheme.row_eq_of_eq`, and
  `Scheme.mem_faces_iff_of_eq` to `Stage.Scheme`;
  `CellScheme.IsLowerEmbedding.image_below_gradedIndex` to `Scheme.Cell`.
- `Extension/CoatomAmalgam`: `StageType.label_eq_of_eq` to `Stage.Basic`, beside `StageType.ext`.
- `Extension/Gluing`: `Rows.isLawfulBelow_iff_forall` and `Rows.IsLawfulBelow.glue` to
  `Scheme.Row`, after the lawful sections; the lifting statements to `Scheme.Bountiful`, after
  `CellScheme.Rows.CappedLift.trans`.
- `Extension/PinnedExtension`: `StageType.card_eq_zero`, `StageType.faces_eq_of_zero`,
  `StageType.eq_of_zero`, and `StageType.isSome_restrictFace_of_zero` to `Stage.Basic`;
  `Scheme.IsLegal.toStageType` with `Scheme.IsLegal.isLegal_toStageType` to `Stage.Legal`;
  `Scheme.onePoint` with `Scheme.isLegal_onePoint` to `Stage.LegalExamples`, where they replace
  the private `point`.
- `Extension/PartBelowFullGrade`: `Scheme.cellsBelowFullGrade`, `Scheme.partBelowFullGrade`, and
  `Scheme.IsLegal.isLegalBelowFullGrade_partBelowFullGrade` to `Extension/Apex`, beside
  `Scheme.IsLegalBelowFullGrade`.

**Coding (checkpoint 2.2).**

- `Extension/Coding`: the label statements (`Label.IsStronglyCoded`, `Label.codedAlphabet`, and
  their lemmas) to `Label.Basic`; `CellScheme.Rows.IsCoded`, `CellScheme.Rows.IsStronglyCodedAt`,
  `CellScheme.Rows.IsStronglyCoded`, and the lemmas on their preservation to `Scheme.Row`;
  `Scheme.isCoded_iff`, `Scheme.isCoded_of_isLowerEmbedding`, and
  `Scheme.isCoded_of_isLowerEmbedding_of_isStronglyCodedAt` to `Stage.Scheme`.
- `Extension/CodingExamples`: `CodingExamples.pointRow` to `Stage.LegalExamples`, once
  `Scheme.IsLegal.toStageType` is in `Stage.Legal` (the entry for `Extension/PinnedExtension`).
  `Correspondence/Current/LegalTemplate` imports `Extension/CodingExamples` for
  `CellScheme.Rows.IsStronglyCoded` and `Label.lt_omega0_sq_iff` (`Extension/Coding`),
  `Scheme.IsLegal.toStageType`
  (`Extension/PinnedExtension`), and `CodingExamples.pointRow`.

**The transformation algebra (checkpoints 2.1 and 2.3).**

- `Extension/WitnessAlgebra`: its statements to `Label.Transform`, after the guarded composition;
  `IsShort` and the flattening of finite parts (`flatten`, `flattenOrd`, and their lemmas)
  beside the self-visible labels of `Label.Visibility`; its block arithmetic beside the blocks
  of `Label.OrdinalVisibility`.
- `Extension/CodedSection`: the block coding (`blockEncode`, `blockDecode`, and their lemmas) to a
  module `Label/Coding.lean` beside `Label.Transform`; `CellScheme.Rows.IsLawful.exists_blockEncode`
  to `Scheme.Row`, after the lawful sections.  Its private block arithmetic
  (`mod_le_mod_of_div_eq`, `mod_lt_mod_of_div_eq`, `omega0_mul_add_lt`, `omega0_mul_add_div`,
  `omega0_mul_add_mod`, `visibilityReplace_omega0_mul_add`, `omega0_mul_natCast_add_lt`)
  duplicates the public rules of `Extension/WitnessAlgebra`, which replace it.  The existential
  coded copy (`CellScheme.Rows.IsLawful.exists_blockEncode`, `Label.IsWitness.blockEncode`) is a
  consequence of the universal form, `Label.isWitness_blockEncode_stepSuppressor` with
  `CellScheme.Rows.IsLawful.map_of_bot_reflecting`, and is to be replaced by it.
- `Extension/Encoders`: the label statements to `Label/Coding.lean`, beside the block coding;
  the lawfulness statements to `Scheme.Row`.  The encoders of 2.3 are built on the block coding
  of `Extension/CodedSection` (there is no second coding) and use the block arithmetic of
  `Extension/WitnessAlgebra`.
- `Extension/SectionTheorem`: the capping lemma (`CellScheme.Rows.IsLawful.min_const`,
  `CellScheme.Rows.IsLawful.min_const_of_isSelfVisible`, and their forms below a pair) is now in
  `Scheme/Row`. The section theorem and its bottom-reflecting form
  (`CellScheme.Rows.IsLawful.map_of_isShort_or`, `CellScheme.Rows.IsLawful.map_of_bot_reflecting`)
  belong in `Scheme.Row`, after the lawful sections; they stay in `Extension/` while they use the
  witness algebra of `Extension/WitnessAlgebra`.
- `Extension/OwnerwiseDecoding`: to `Scheme.Row`, beside the section theorem, once the strongly
  coded decoder is placed.
- `Extension/Apex`: `Scheme.appendFullCell` and its laws, `Scheme.mem_range_comp_cellMap_iff`,
  `Scheme.cellMap_eq_of_strictMono_of_mem_range`, and `Scheme.comap_eq_of_strictMono` to
  `Stage.Scheme`, beside `Scheme.cellMap_eq_of_strictMono`;
  `StageType.restrictFace_eq_of_strictMono` to `Stage.Basic`, beside
  `StageType.restrictFace_trans`; `Scheme.IsLegalBelowFullGrade` to `Stage.Legal`, beside
  `Scheme.IsLegal`.  The choice in `apexCodes` can be replaced by the finite set
  `univ.image w` of the labels, by the universal form of the coded copy.

**The chain construction (not used by the main theorem).**

- `Construction/ChainModel`: `StageType.onePoint` and `StageType.isLegal_onePoint` to
  `Stage.LegalExamples` (replacing the private `point`, the same stage type at stage `0`); the
  instance `StageType.instSubsingletonZero` to `Stage.Basic`; `Realization.RealizesCofaces` and
  its two consequences to `Realization.Model` and `Language.Density`.
- The other placement notes of the chain construction (in `Scheme/Lifting`, `Scheme/Transport`,
  and `Stage/Legal`) are not recorded: the library already holds those declarations at their
  destinations, or no longer has them.  `IsBountiful.comap_of_image_eq`,
  `IsBountiful.comap`, and `IsBountiful.reindex` stay in `Scheme/Transport`, which has no
  placement note.
- Duplicates between the chain construction and the coatom extension construction, to be kept
  once: the zero-point lemmas (`StageType.card_eq_zero`, `StageType.faces_eq_of_zero`,
  `StageType.eq_of_zero`, `StageType.isSome_restrictFace_of_zero`) and the zero-point instance
  `StageType.instSubsingletonZero`; the one-point scheme (`Scheme.onePoint`,
  `Scheme.isLegal_onePoint`, `Scheme.IsLegal.toStageType`) and `StageType.onePoint`; the
  one-point extension `StageType.exists_extension` ([Kni26, Proposition 4.3.23]) and
  `Construction.nonempty_cofaces_of_hasExactPinnedExtensions`; and the face followed by the new
  point, `extendByLast` and `Construction.pinnedFace`, equal by `rfl`.

**Languages and the main theorem (Layers 2 and 6).**

- `Language/Sentence`: the formula helpers `BoundedFormulaω.distinct`,
  `BoundedFormulaω.realize_distinct`, and `BoundedFormulaω.realize_alls` hold for an arbitrary
  language, and `Structure.ext_of_isRelational` (added to `Language/Basic` by #34) for a
  relational one; they are candidates for upstreaming.
- `MainTheorem/Spectrum`: the statements that belong upstream (the cross-universe transport
  `realize_boundedFormulaω_equiv` and `realize_sentenceω_equiv`, `qrank_lt_omega_one`,
  `classTruth` with its lemmas, and `exists_mem_modelsOf_equiv`) are recorded in `COMPANIONS.md`,
  A3, **Upstream ingredients**: each with its upstream module, except the two `realize_*_equiv`
  lemmas, which become redundant once `BoundedFormulaω.realize_equiv` and `LomegaEquiv.of_equiv`
  are generalized across carrier universes.
- `MainTheorem/MaximalRefinement`: at a repin containing `c16de09` and `2cd44c3`, the two-class
  argument (`expansionDomain_subsingleton_of_isolates` with `lt_qrank_of_isolates`) is to be
  derived from `notMem_of_isolating_of_uniform` (`OrdinalCountability`), with the statements kept.
  Its attained greatest index is the Layer 0 statement of `Counting/OrdinalAttainment` (below,
  "Counting").
- `MainTheorem/Scatteredness` (pull request #42): every statement is generic (none mentions the
  density sentence), and its statements are quotations of InfinitaryLogic (at the pin `e460cb6`):
  `isThinOn_of_countable_bfClasses` of `isThinOn_of_bfScattered` (`Descriptive/BFScattered`),
  `isThinOnNatModels_of_countable_bfClasses` of `Sentenceω.isThinOnNatModels_of_bfScattered`
  (`Descriptive/BFScatteredSentence`), `bfEquivSetoid_eq_comap` of its namesake, `offDiag_noniso` of
  `not_structureIso_of_mem_offDiag`, `exists_forall_not_codeBFEquiv_of_isClosed` of
  `exists_forall_not_codeBFEquiv_of_analyticSet`, and `analyticSet_offDiag` through
  `MeasureTheory.AnalyticSet.offDiag`; `codeBFEquivSetoid` is InfinitaryLogic's by definition.
  `bfScattered_of_countable_compl` is not a quotation: it applies
  `bfScattered_of_countable_bfObservations` (for every relational language), beside which, in
  `Descriptive/BFScattered`, it belongs upstream.
  `not_countable_of_perfect` stays local: InfinitaryLogic's `Perfect.mk_eq_continuum` assumes a
  metric space, and the space of codes gets one only after a choice of compatible complete metric
  (`TopologicalSpace.upgradeIsCompletelyMetrizable`); to Mathlib, as the uncountability of a
  nonempty perfect set in a completely metrizable space (`Topology/MetricSpace/Perfect`, beside
  `Perfect.exists_nat_bool_injection`).
- `MainTheorem/Assembly`: in the proof of `FullPresentations.HasScatteredTails.countable_quotient`,
  the local map from the classes of the density sentence to
  `Quotient (bfEquivSetoid densitySentence η)` re-derives InfinitaryLogic's
  `bfProj densitySentence η` (`ModelTheory/MorleyCounting`), and the image of codes in
  `FullPresentations.HasScatteredTails` is in effect the range `bfProjRange` of the tail, stated as
  an image of codes; the proof is to use `bfProj` and `bfProj_mk` in place of the local derivation,
  in a later change of proofs only (no statement changes, and no Lean change here).

- `MainTheorem/LastStage`: the attained greatest index `exists_isGreatest_of_closed` is imported
  from `Counting/OrdinalAttainment` (Layer 0), with no local copy.
  `ExpansionDomains.notMem_of_isolating` and `ExpansionDomains.lastStage_lt_qrank` are local forms
  of InfinitaryLogic's Scott separation (`OrdinalCountability`, available upstream at `2cd44c3`,
  not at the pin `e460cb6`), to be proved by quotation at a repin containing it.

**Lifting and alignment (checkpoint 2.4; Layer 3, (R6)).**

- `Extension/GradeCut`: the cell statements to `Scheme.Cell`; the statements on rows, lawfulness,
  coding, and lifts to `Scheme.Row` and `Scheme.Transport`, the coding beside `Rows.IsCoded`.
- `Extension/SourcePrefix`: `IsSourcePrefix` and the `IsLowerEmbedding.*_of_scope_eq` lemmas to
  `Scheme.Cell`; the lawfulness and lift statements to `Scheme.Transport`.
- `Extension/Restoration`: `Label.min_eq_min_of_le` to `Label.Cap`; `CellScheme.splice` and
  `IsLawfulBelow.splice` to `Scheme.Row`, beside `IsLawfulBelow.glue`; restoration and the lifts to
  `Scheme.Bountiful`.
- `Extension/InheritedLocality`: `Label.transformsTo_comp_equiv_iff` to `Label.Transform`, beside
  `TransformsTo.reindex`; the locality statements to `Scheme.Row`; the section theorem along a lower
  embedding beside `IsLawful.map_of_isShort_or`.
- `Extension/CapTransport`: the label rules and the witness interpolation to `Label.Transform`,
  beside the guarded composition; the transport of lawfulness (`map_of_bot_iff`, `map_of_min_eq`,
  and `map_of_apply_eq_bot`, which generalizes `map_of_bot_reflecting`) to `Scheme.Row`, beside
  `IsLawful.map_of_isShort_or`.
- `Extension/FlattenedSource`: the flattening and decoding identities to a module
  `Label/Coding.lean`, beside the encoder; the lawfulness and prescription statements to
  `Scheme.Row`.
- `Extension/OwnerAlignment`: the strip lemmas and `Label.exists_ownerAlignment` to
  `Label.Transform`, beside the capped witness; the form below a pair
  (`CellScheme.Rows.IsLawfulBelow.exists_ownerAlignment` and its flattened-source instance) to
  `Scheme.Bountiful`.
- `Extension/AlignedEncoding`: `Label.unshift`, the tail and high codes, `Label.alignedEncode`, and
  `Label.alignedDecode` to a module `Label/Coding.lean`, beside the encoder;
  `Label.IsWitness.comp_of_commute` and `Label.TransformsTo.of_read` to `Label.Transform`, beside
  the guarded composition; the lawfulness of the aligned encoding to `Scheme.Row`.
- `Extension/OwnerCappedLift`: to `Scheme.Bountiful`, beside `CellScheme.Rows.HasOwnerCappedLifts`.

**The small arities (checkpoint 2.5; Layer 3, (R6)).**

- `Extension/FieldLayer`: the label statements, in the namespace `Label` (the grid points and the
  grid, the value rank, the canonical map and the canonical code, the literal-reading decoder, and
  agreement heights), to a module `Label/Coding.lean`, beside the encoder, except
  `Label.eq_of_min_eq_of_lt` and `Label.le_of_min_eq_of_le`, to `Label.Cap`;
  `CellScheme.Rows.IsLawful.canonicalCode` to `Scheme.Row`, beside the section theorem;
  `Scheme.appendFullCells` and its laws to `Stage.Scheme`, beside `Scheme.appendFullCell`; the
  canonical catalogue, the field rows, and `Scheme.fieldLayer` in place.
- `Extension/SmallArities` and `Extension/SmallArityExamples`: checkpoint 2.5, in place.
- `Extension/OrderedLayerStep`, `Extension/OrderedLayerTop`, `Extension/MultiLayerStep`,
  `Extension/CrossedCouplingScheme`, and `Extension/CrossedCouplingCompletion`: checkpoint 2.7, in
  place.  Their statements about appended cells and suppressors are beside the definitions
  they concern: `Scheme.appendFullCells_row_castAdd` in `Extension/FieldLayer`, beside
  `Scheme.appendFullCells_row_natAdd` (it moves with the laws of `Scheme.appendFullCells`);
  `Label.constStepSuppressor_of_le` in `Label/StepWitness`, beside `Label.constStepSuppressor`;
  `OrderedLayer.noneAbove_appendFullCells` in `Extension/OrderedLayerStep`, beside
  `OrderedLayer.NoneAbove` and `OrderedLayer.noneAbove_addLayerCell`.  The capped lift at the
  grade `4` from the grade `3` in a scheme over the amalgam of a seed with bottom apexes
  (`OrderedLayer.cappedLift_four_of_oldCells`) is stated once, in `Extension/OrderedLayerTop`, and
  quoted for the layer scheme (`OrderedLayer.cappedLift_four`) and for the multi-layer scheme of
  `seedHG` (`CrossedCouplingCounterexample.cappedLift_four_HG`).  The order lemma forcing two new
  cells of one graded index by their readings (`OrderedLayer.eq_of_forced_pair`) and the row of an
  old cell of grade `4` over a seed with bottom apexes (`OrderedLayer.row_multiOldCell_eq_bot_iff`)
  are in `Extension/MultiLayerStep`, quoted by `seedHG` and by the canonical multi-layer scheme.
  The strip shifter as a witness up to the grade `1`
  (`TwoFaceLiftCounterexample.isWitness_stripShifter_one`) is in
  `Extension/TwoFaceLiftCounterexample`, beside `TwoFaceLiftCounterexample.isWitness_stripShifter`,
  quoted by `seedHG` and by the canonical multi-layer scheme.
- `Extension/CanonicalMultiScheme`, `Extension/CanonicalMultiSchemeCounterexample`, and
  `Extension/CanonicalMultiSchemeExamples`: checkpoint 2.7, in place.  The decoding lemma
  `Label.TransformsTo.false_of_decoding` and `Label.visibilityReplace_three_fixed` belong in
  `Label/Transform` and `Label/Visibility`.  The labelling of `Ω` alone at the grade `4` in a
  scheme whose cells of grade `4` have rows `⊥` exactly below the grade `4`
  (`OrderedLayer.isLawfulBelow_omega_of_rows`) is in `Extension/OrderedLayerTop`, quoted by the
  layer scheme (`OrderedLayer.isLawfulBelow_omegaLabel`) and by the canonical multi-layer scheme.
  The kind-by-kind transformation (`CrossedCouplingCounterexample.transformsTo_val_of_kind`) and
  the witnesses of the rows of kinds `A_D`, `A_C`, `H`, `G`
  (`CrossedCouplingCounterexample.transformsTo_val_ad`, `transformsTo_val_ac`,
  `transformsTo_val_h`, `transformsTo_val_g`) are in `Extension/CrossedCouplingScheme`, quoted by
  `seedHG` and by the copies of the canonical multi-layer scheme.
- `Extension/CanonicalMultiSchemeOriented` and `Extension/CanonicalMultiSchemeOrientedExamples`:
  checkpoint 2.7, in place.  The reindexing rule `Label.TransformsTo.of_comp` (the pointwise form
  of `Label.TransformsTo.reindex`) belongs in `Label/Transform`, beside it.
  `Seed.HasCanonicalMultiStep` and `Seed.HasCanonicalMultiStep.nonempty_completionBelowFullGrade`
  are in `Extension/CanonicalMultiScheme`, beside `Seed.canonicalMultiStep_of_product`.

**Hull operations, the top-free age, and graded matching (Layers 0 and 2; the top-free
witnesses).**

- `Language/HullOperations`, `Language/HullDefinability`, and their examples modules: Layer 2, in
  place.  The rigidity lemma for plans (`Geometry.IsPlan.apply_eq_of_mem_hull`) is in
  `Geometry/Plan`, where it belongs.
- `Realization/TwoCharts` and `Realization/TwoChartsExamples`: Layer 2, in place.
- `ClassicalLimit/Age` and `ClassicalLimit/AgeExamples`: steps 1–2 of the top-free witnesses, in
  place.
- `ClassicalLimit/Receiving` and `ClassicalLimit/ReceivingExamples`: step 6 and the base-reduct part
  of step 7 of the top-free witnesses, in place.
- `ClassicalLimit/Reconstruction` and `ClassicalLimit/ReconstructionExamples`: steps 4–5 of the
  top-free witnesses, in place.
- `ClassicalLimit/Amalgamation`: the capping API has moved, `StageType.cap` with its laws
  (`cap_toScheme`, `cap_label`, `isLegal_cap`, `isTopFree_cap`, `restrictFace_cap`),
  `StageType.IsTopFree.exists_label_le`, and `StageType.exists_cap` to `Stage/Cap`, and
  `StageType.grade_le` to `Stage/Basic`. Left: `StageType.exists_isTopFree_amalgam`, to a module of
  `Extension/` (for instance `Extension/Capping.lean`, importing `Extension/PinnedExtension` and
  `Stage/Cap`), since (R5) needs it and cannot import `ClassicalLimit/`; and
  `TopFreeIndex.restrictFace_empty`, to `ClassicalLimit/Age`, beside `TopFreeIndex.empty`. The
  import of `Extension/SectionTheorem` here and in `Extension/FamilyCofaces` is used only for the
  capping lemma, now in `Scheme/Row`, which is to replace it.
- `ClassicalLimit/LegalAge` and `ClassicalLimit/LegalAgeExamples`: the uncapped age of all legal
  charts (its hereditary property, `isFraisse_legalAge`, `exists_isFraisseLimit_legalAge`), the
  occurrence of every legal stage type (`exists_covers_reconstruct_of_legalAge`), exact receiving
  (`exactReceivingWithin_reconstruct_of_legalAge`), and modelhood
  (`isModel_reconstruct_of_legalAge`), in place, beside the age of top-free charts.  The family
  (`LegalIndex`, `legalChart`, `legalAge`, `legalChart_mem_legalAge`) and the inclusion
  `topFreeAge_subset_legalAge` are in `ClassicalLimit/Age`; the reconstruction under legal chart
  coverage (`exists_eq_trans_legalChart`, `isConsistent_reconstruct_of_legalAge`,
  `isCovering_reconstruct_of_legalAge`, `exists_embedding_of_reconstruct_eval_of_legalAge`) is in
  `ClassicalLimit/Reconstruction`, where the top-free exact consistency and covering are its case;
  exact extension along a chart embedding (`exists_reconstruct_eval_eq_of_embedding`), shared by
  the top-free and the legal exact extension, is in `ClassicalLimit/Receiving`; and
  `Realization.ExactReceivingWithin.hasFiniteCutReceiving` is in `Continuation/ExactAge`.  The
  capped top-free amalgamation and receiving stay separate: the legal age needs no cap.
- `Comparison/GradedMatchingApplications`: Layer 0, in place.  The local graded back-and-forth
  theorem (`README.md`, Layer 0) is retired, not moved: both of its applications compile through
  InfinitaryLogic's `bfEquiv_of_gradedMatching`.
- `MainTheorem/AllCarriers`: `infinite_of_realize_densitySentence_of_hasCoatomExtensions` concerns
  only the density sentence and the coatom extension property; it is a candidate for
  `Language/Density`, beside the density sentence, if the imports allow it.

**Receiving for finite extensions (Layer 3).**

- `Realization/Receiving`: Layer 3, item "Receiving for finite extensions", in place under
  `Realization/`: it imports only the realizations of Layer 2, Layer 1, and `Extension/Basic`, the
  boundary of (R1).  The stage-type lemmas it uses (`StageType.mem_receivingFamily_of_le`,
  `StageType.mem_receivingFamily_trans`, `StageType.reindex_mem_receivingFamily`, and the repair
  `StageType.exists_restrictFace_eq_mem_receivingFamily`) are in `Realization/Families`, beside
  `StageType.receivingFamily`.
- `Realization/ReceivingExamples`: in place.  The examples of the global forms
  (`Expansion.FiniteCutReceiving`) are in `Expansion/AgreementExamples`, since this module imports
  no module of Layer 5.
- `Realization/Receiving`, continued: the descent of finite-cut receiving along stage reduction
  (`HasFiniteCutReceiving.reduce`) is in place.  The induction of
  `HasFiniteCutReceiving.exists_extend_of_mem_receivingFamily` repeats the base case (a face onto
  the whole donor, reindexed) and the choice of the next closed point of `StageType.exists_amalgam`
  (`Extension/PinnedExtension`); a lemma shared by the two, in a module both import (for instance
  `Extension/Basic`, or `Stage/` for the closed-point choice), is a later change of proofs only,
  with no statement change.

**Quantitative reconstruction, row 1 (`COMPANIONS.md`, "Further companion results").**

- `Definability/Syntax`: Layer 0.  It imports no module of this repository (only InfinitaryLogic's
  `Lomega1omega/QuantifierRank` and `Scott/Formula`).  Its existential closure `existsLastVars`,
  with `realize_existsLastVars` and `qrank_existsLastVars`, duplicates InfinitaryLogic's
  `existsTupleFrom`, `realize_existsTupleFrom` (`Scott/MontalbanSentence`) and
  `qrank_existsTupleFrom` (`Scott/MontalbanQuantifierRank`) at the pin `e460cb6`: the same
  recursion, any language, and the same rank `φ.qrank + m`, added on the right.  It is kept
  deliberately: importing those modules would bring `Scott/Sentence`, `Scott/OrbitRank`,
  `Scott/Stabilization` and `Karp/PotentialIso`, and, for the rank, `Scott/QuantifierRank` and
  `Karp/CarrierTheorem`, into the import closure of this module, which needs only the two modules
  above.  The agreement
  (`existsLastVars m φ = existsTupleFrom k m φ`, with the semantics and the rank read through it)
  is compiled in `Definability/BlockFormulasExamples`, which may import the wider modules.  The
  duplication is to be resolved by a placement change: either InfinitaryLogic moves the tuple
  blocks and their rank to a module with this module's narrow imports, and `existsLastVars` becomes
  `existsTupleFrom` here, or this module adopts the wider imports.  `extendFormula` with
  `extensionEquations`, `realize_extendFormula`, `qrank_extendFormula`,
  `realize_extensionEquations`, and `qrank_extensionEquations` are candidates for InfinitaryLogic,
  beside `existsTupleFrom` (the closure they use).  Its former
  `BoundedFormulaω.qrank_mapFreeVars` and `BoundedFormulaω.qrank_inf` are InfinitaryLogic's at the
  pin `e460cb6` (same names and statements); the module makes the first a `simp` lemma.
- `Realization/BlockStages` (formerly `Definability/BlockStages`): Layers 1–2 (labels and stage
  types at the block stages), in place under `Realization/`; its one-block lemmas
  (`StageType.eq_of_reduce_eq_of_threshold_iff` and the threshold lemmas) are used by the
  normalization of Layer 4, and it states that every successor-limit ordinal is a block stage
  (`exists_blockStage_eq_of_isSuccLimit`).
- `Definability/BlockFormulas` and `Definability/BlockFormulasExamples`: quantitative
  reconstruction, row 1, in place; `Realization.covers_iff_eval` and `Realization.ExtendsToCover`
  are now in `Realization/Expansion`, and `Realization.IsExpansionOf.relMap_iff` is to move there.
  The private legal two-point stage type of the examples is a copy of the one in
  `Realization/ModelExamples`, so that no examples module is imported.
- `Definability/BlockDetermination` and `Definability/BlockDeterminationExamples`: row 1, the
  forcing thresholds and block determination for them (`forcingThresholds`,
  `forcingThresholds_determines`), in place, under the row-1 import guard; the receiving hypothesis
  is taken per model expansion so that no `Expansion/` module is imported.
  `Expansion/BlockDetermination`: the global form
  (`Expansion.FiniteExtensionReceiving.forcingThresholds_determines`), a companion corollary in
  Layer 5 that the main theorem does not import.
- The import guard of `Definability/*` (its forbidden prefixes are listed in `README.md`, "Import
  guards") is to be added with the other guards of `scripts/check.sh`.

**Counting (Layers 0, 5–6).**

- `Counting/OrdinalAttainment`: Layer 0, a general ordinal statement (Mathlib only, no
  construction imports).  `exists_isGreatest_of_closed`, used by `MainTheorem/MaximalRefinement` and
  `MainTheorem/LastStage`,
  is to be replaced at a repin containing `c16de09` and `2cd44c3` by a quotation of the
  greatest-stage statements of InfinitaryLogic (`OrdinalUtil`; "Dependency pins", **Upstream
  statements quoted, not compiled here**), from which it follows (note 34).
- `Counting/Filtration` and `Counting/Separation`: their generic statements are proved as quotations
  of InfinitaryLogic's `OrdinalCountability` (at the pin `e460cb6`), with their statements kept:
  `Filtration.ofRank` is built from `rankTail` (its domain is `rankTail r` by definition), and
  the lemmas on `ofRank`, the least-level lemmas, `domain_ofCountableCover`, and the three counts
  `mk_eq_aleph_one_of_rank`, `mk_le_aleph_one_of_rank`, and `mk_le_aleph_one_of_countable_cover`
  each apply one InfinitaryLogic statement.  The conventions, recorded in the module docstring of
  `Counting/Filtration`:
  - the restriction `α < ω₁` inside `leastLevel` (`sInf {α | α < ω₁ ∧ x ∈ Q α}`, against
    InfinitaryLogic's `sInf {α | x ∈ Q α}`), which keeps the least level below `ω₁` with no
    hypothesis; the two agree under the cover (`leastLevel_eq_leastLevel_of_cover`), and the
    restricted form is InfinitaryLogic's least level of the family restricted to levels below `ω₁`
    (`leastLevel_eq_leastLevel_inter`, by definition);
  - fibres as sets (`{x | r x = α}.Countable`), against subtypes in InfinitaryLogic;
  - `Order.succ η`, in InfinitaryLogic, is definitionally `η + 1`.

  `Filtration` itself (the hypothesis bundle of the count with a countable persistent core),
  `Filtration.compl_countable`, the counts of `Counting/Separation` that allow a nonempty core, and
  `Counting/Domains` stay local: InfinitaryLogic has no such bundle, and its `mk_*_of_domains` need
  every point to leave.  Deleted, as unused or used only where InfinitaryLogic's statement serves
  directly: `countable_setOf_rank_lt` (InfinitaryLogic's `countable_of_forall_rank_lt` with the
  conversion of fibres), `le_leastLevel_iff` (`rankTail_leastLevel` with the cover),
  `iInter_setOf_le_rank_eq_empty` (`FullPresentations.core_toFiltration` in `MainTheorem/Assembly`
  now applies `biInter_rankTail_eq_empty`), and `forall_exists_le_rank_iff` (the example of
  `Counting/Separation` now applies `countable_iff_rank_bounded`; `README.md`, "What the count of
  this route no longer uses", now cites `rankTail_cofinal_losses_iff` and
  `countable_iff_rank_bounded`).  `leastLevel_le` is kept, with no hypothesis `α < ω₁`: for `α < ω₁`
  it is InfinitaryLogic's `leastLevel_le_of_mem` (which needs no cover) for the family restricted to
  levels below `ω₁`, and for `α ≥ ω₁` the conclusion holds because `leastLevel Q x < ω₁` with no
  hypothesis.

**Normalization, terminal classification, and the stable candidate (Layers 1, 4–5).**

- `Stage/Threshold`: Layer 1, in place. `natCast_le_iSup_iff_of_ne_zero`, a fact about `ℕ∞`, is a
  Mathlib candidate, beside the supremum lemmas of `ENat`; `Label.ofOffset` with its laws concerns
  labels only and goes to `Label/`.
- `Continuation/Normalization`, `Continuation/Hollow`, `Continuation/Terminal`,
  `Continuation/ExactAge`, `Continuation/Comparison`, `Continuation/Classification`,
  `Continuation/Candidate`, `Continuation/CandidateCounterexamples`, and their examples modules:
  Layer 4, in place. `ContinuationCriterion`, the statement of output 3, is in
  `Continuation/Classification`, where the cover of the terminal models uses it; a module proving
  output 3 imports `Continuation/Classification`, or the structure moves to that module, a move to
  record here. `Realization.IsCoverHollowAtBlock` is beside `Realization.IsCoverHollow` in
  `Continuation/Hollow`.
- `Continuation/StableReceiving` and its examples module: Layer 4, in place.
  `Expansion/StableReceiving` and its examples module: Layer 4, placed in `Expansion/` because the
  equivalence of (R4) with the continuation criterion takes (R1) as `Expansion.FiniteCutReceiving`
  (`Expansion/Agreement`, Layer 5), and no module of `Continuation/` imports a module of
  `Expansion/`.
- `Expansion/UniquenessOfForcing`: Layer 5, in place, separate from `Expansion/BlockDetermination`
  so that the import closure of the main theorem contains no `Definability/` module.
  `Expansion/Losses`: Layer 5, in place. `Counting/Domains`:
  `Counting.countable_of_subsingleton_cover`, a general result of Layer 0, in place.
- `Continuation/RestrictedHollow` and its examples module: Layer 4, in place; it holds
  `Realization.IsCoverHollowWithoutRigidCore` and its form at a block stage, the restricted
  terminal properties with their cover, and `Realization.HollowReceiving.withoutRigidCore`.  It
  imports `Continuation/Classification` and `Continuation/Comparison`, grouping the restricted
  predicate with its classification and comparison interfaces. The restricted forms of
  the comparison of model expansions, of the subsingleton step, and of the countable losses are in
  `Expansion/Losses`, that of the count of the terminal classes in `MainTheorem/TerminalClasses`,
  and those of the main theorem in `MainTheorem/ModelExpansionDomains`, beside the unrestricted
  ones.
- `Continuation/Hollow` (importing `Continuation/Terminal` and `Continuation/ExactAge`):
  `Realization.isCoverHollow_of_exactReceivingWithin`, `Realization.IsCoverHollow.isTerminalAt`,
  and `StageType.exists_forcesThreshold_of_label_eq_top` (the form of `ForcingDonors` used for
  cover-hollowness), Layer 4, in place.  `StageType.ForcesThreshold.congr_root`, a fact about
  forcing alone, is in `Stage/Threshold`, beside `StageType.ForcesThreshold`.
- `MainTheorem/SameLevelMaximal` (acceptance lemma 1): `exists_saturated_reconstruct`,
  `exists_sameLevelMaximal_reconstruct`, `exists_sameLevelMaximal_covers`, and
  `exists_sameLevelMaximal`, in place.  `exists_equiv_extend_tuple` (private) is the case of a
  finite range of Mathlib's `Cardinal.extend_function_of_lt`, from which it is derived.
- `Extension/OwnerCappedLift`: `CellScheme.Rows.cappedLift_of_boundary_short` is the case of equal
  boundary triples of `CellScheme.Rows.cappedLift_of_boundaries_short`, from which it is to be
  derived when the file is next opened (a change of proofs only).

**Statements not yet in any module.**

- The bound of the provisional offset by the top grade, the optional bound (d) of the
  normalization (prospective), stated with `StageType.provisionalOffset`.  Its forcing form is
  compiled: if every grade of `q` is at most `K` and `β + K < α`, then `(q, f)` does not force
  `K + 1` at a cell labelled the formal top (`StageType.not_forcesThreshold_of_grade_le`,
  `Stage/Threshold`).  The bound itself waits for `StageType.topGrade` (`Continuation/Terminal`) to
  move to `Stage/`.
- `TiedLayer` (prospective; recorded in `Extension/ForcingDonors`): a completion below the full
  grade with one prescribed tie at an intermediate grade.  It is not needed for forcing donors:
  unconditionally for two-point inputs (`exists_forcingDonor_twoPoint_le_two`), and in general
  under the coatom extension property (`forcingDonors_of_hasCoatomExtensions`).  `TiedLayer`
  itself is neither proved nor refuted.
- The ordinary construction of (R1) as data (4b-ii), the proof of
  `StageType.HasCoupledGatedPinnedExtensions` (open; its first form
  `StageType.HasGatedPinnedExtensions` is refuted); (R2), (R3), (R4); and output 3, the proof of
  `ContinuationCriterion`.
- The graded back-and-forth theorem (`README.md`, Layer 0), formerly listed here,
  is retired, not moved: both of its intended applications, approximate comparison of full
  presentations and the back-and-forth form of condition 3 of the expansion-domain route, compile
  through InfinitaryLogic's `bfEquiv_of_gradedMatching` (`Comparison/GradedMatchingApplications`,
  Layer 0).

## Dependency tracking

Which checkpoint uses which statement is recorded here, not in the docstrings: a docstring states
the mathematical role of its statement, what it is used to prove.  The checkpoints are those of
the completion of the coatom extension construction, 2.1–2.7 above.  Unless noted, the
statements of a module are used at the checkpoints given with its heading.

**Coding** (`Extension/Coding`).

- `Label.codedAlphabet`, the finite alphabet of codes of bounded block and offset: 2.3, 2.6.
- `Label.lt_omega0_sq_of_mem_codedAlphabet`, codes lie below `ω²`: 2.6.
- `Label.finite_setOf_isStronglyCoded_lt`, finitely many strongly coded labels below a block: 2.3.
- The coding of the completion, from the module's analysis: the amalgam (a), the inherited rows
  (b), the apex, whose row is the coded copy of the labels (its coding is treated with the apex,
  not by the bottom-row lemma (c)), the other new rows, with values in the coded alphabet of their
  grade (d), and the finiteness of the catalogue (e): 2.3–2.6.
- The one lifting step above an input row, which uses the coding of the input (a new entry in a
  block above every value of the row, below `ω²`): 2.4.

**Encoders** (`Extension/Encoders`; 2.5, 2.6 unless noted).

- `Label.isWitness_strongEncode`: boundary labels transform to their normal form, lawfully.
- `Label.isWitness_strongDecode`: the decoder of the section theorem.
- `Label.isStronglyCoded_strongEncode`: a new cell of grade `K` with rows from codes is strongly
  coded.
- `Label.strongEncode_mem_codedAlphabet`: the catalogue at grade `K` is finite.
- `Label.injOn_strongEncode`, used through `Label.forall_min_strongEncode_eq_iff`, and
  `Label.forall_min_strongEncode_eq_iff` itself.
- `Label.isSelfVisible_strongEncode`: the caps are self-visible at `K`.
- `Label.strongDecode_min_strongEncode`: a lift capped at the code of a cap decodes to the
  decoded lift capped at the cap; 2.6.
- `Label.min_strongDecode_eq_min_strongDecode` and `Label.min_strongDecode_eq_of_min_eq`: 2.6.
- `CellScheme.Rows.IsLawful.strongEncode`; and the shortness of the new full-scope rows, from
  their construction.

**Normal form** (`Extension/NormalForm`; 2.5, 2.6).

- `Label.transformsTo_strongEncode_comp` and `Label.strongEncode_comp_transformsTo`.
- `Label.strongDecode_comp_strongEncode_comp`: the inherited owners in ownerwise decoding.
- `CellScheme.Rows.IsLawful.exists_stronglyCoded`: the boundary labels of a seed replaced by a
  strongly coded catalogue vector.
- `CellScheme.Rows.IsLawfulBelow.exists_stronglyCoded`: the row of a new cell of a given scope
  and grade.

**The section theorem and capping** (`Extension/SectionTheorem`; the capping lemmas are now in
`Scheme/Row`).

- `CellScheme.Rows.IsLawful.min_const`, through `CellScheme.Rows.IsLawfulBelow.min_const`: 2.5.
- `CellScheme.Rows.IsLawful.map_of_isShort_or`, through ownerwise decoding: 2.5, 2.6.
- `CellScheme.Rows.IsLawful.map_of_bot_reflecting`: 2.5, 2.6.
- `CellScheme.Rows.IsLawfulBelow.min_const_of_isSelfVisible`: 2.5.

**Ownerwise decoding** (`Extension/OwnerwiseDecoding`; 2.5, 2.6).

All in the namespace `CellScheme.Rows.IsLawful`:

- `strongDecode_locality_of_decode_eq_on_below`: the inherited owners, decoded along the exact
  base table, with no bottom reflection.
- `strongDecode_locality_of_isShort_row`: the new full-scope owners, whose rows are short.
- `strongDecode_of_ownerwise`: the decoded source section of the completion.

**The witness algebra** (`Extension/WitnessAlgebra`, in the namespace `Label`; 2.5, 2.6 unless
noted).

- `IsShort`; `isWitness_comp_flatten`; `IsWitness.exists_eq_comp_of_isShort`;
  `IsWitness.le_apply_visibilityReplace`; `TransformsTo.exists_isWitness_capped`;
  `TransformsTo.map_of_isShort`; `TransformsTo.map_of_bot_reflecting`;
  `IsWitness.transformsTo_comp`.
- `IsWitness.max`: the shifter of the locality of a new full-scope cell, the maximum of the capped
  witness of an owner and a second witness; 2.6.
- `IsWitness.finsetSup`: interpolation across mixed grades; 2.5.

**The alignment of owners** (`Extension/OwnerAlignment`, `Extension/AlignedEncoding`,
`Extension/OwnerCappedLift`; 2.6, and 2.5 for the lift at grade `1`).

- `CellScheme.Rows.cappedLift_of_boundary`: the one grade step, under hypotheses (1)–(6) of 2.4.
- `CellScheme.Rows.hasOwnerCappedLifts_of_boundary`: the owner-capped lifts of the decomposition
  `CellScheme.Rows.cappedLift_of_ownerCappedLift`, at every cap self-visible at the grade.

**Condition 2, normalization, and the lower bound** (checkpoint 5; `Continuation/`,
`Expansion/`, `MainTheorem/`).

- Checkpoint A (`Continuation/ExactAge`) is used by D, through the rigid-core age
  (`StageType.rigidCoreAge`) and exact receiving within it; B (`Continuation/Terminal`) by C and D.
- Checkpoint C uses `ContinuationCriterion` once, contrapositively, in
  `Realization.exists_hasTerminalProperty`; D uses (R1) through
  `Expansion.FiniteCutReceiving.finiteExtensionReceiving` for the rigid-core case, and (R2), (R3)
  as the named hypotheses of the residual and hollow cases.
- Checkpoint E uses C, D, and `Counting.countable_of_subsingleton_cover`; the main theorem uses
  forcing donors only for next-block uniqueness, that is, for the limit clause of the domains.
- Checkpoint F uses C, and E's `Expansion.subsingleton_classes_of_property`; neither condition 2
  nor the main theorem uses F.
- Normalization: the threshold lemma uses finite-extension receiving at the cutoff `λ_η` (from
  (R1)) and forcing donors; next-block uniqueness uses both
  (`Expansion.NextBlockUniqueness.of_forcingDonors`). Forcing donors follows from the coatom
  extension property (`forcingDonors_of_hasCoatomExtensions`), so it waits on 2.7.
- The lower bound (step 7) uses next-block uniqueness only at the successor blocks `ξ + 1 ≤ η`, and
  none at `η = 0` (`eq_reconstruct_of_blockStage_zero`); the cap-to-model hypothesis of
  `densitySentence_hasThinAlephOneSpectrum_of_hasApexCoatomExtensions` is derived from the coatom
  extension property with apex at `η = 0`.
- The six-hypothesis form of the main theorem (`MainTheorem/Composition`) uses the coatom
  extension property with apex at `η = 0` for `CapToModel`, at every countable block stage for
  nonempty losses, and nowhere else; (R1) for next-block uniqueness, logical agreement and countable
  losses; forcing donors for next-block uniqueness only; `ContinuationCriterion`, (R2) and (R3) for
  countable losses only.  The five-hypothesis form (same module) uses the same hypotheses except
  forcing donors (`hF`), in the same places, and in addition the coatom extension property with
  apex at each successor block stage `λ_{ξ+1}` for forcing donors at `ξ`
  (`forcingDonors_of_forall_hasApexCoatomExtensions`).
