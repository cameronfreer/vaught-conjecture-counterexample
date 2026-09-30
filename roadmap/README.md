# Labelled finite convex geometries and a thin uncountable infinitary class

## Objective and completion criterion

Develop a reusable library of finite closed diagrams, extension of bounded observations, countable realization, stable refinement, and infinitary comparison. Its principal application is the **specified Knight construction**: a countable relational language \(L_K\) and a sentence \(\Phi_K\in L_{\omega_1,\omega}\) whose countable isomorphism classes number exactly \(\aleph_1\), with no perfect isomorphism antichain.

The organizing invariant is a **continuous decreasing family of expansion domains with countable successor losses and increasing logical agreement**. Do not require a total stopping rank, exhaustive rank layers, characteristic arity, a canonical terminal representative, or a Borel structure on the quotient of models.

This README is the definitive mathematical roadmap. `Suggested.lean` records selected interfaces and human-owned theorem targets; finishing only that file is not completion. `SEMANTIC_CONTRACT.md` fixes the meanings that a rewrite must preserve. `EXPOSITIONS.md` gives three informal accounts. `SIMPLIFICATIONS.md` distinguishes present results from proposals, and `SOURCE_AUDIT.md` supplies source provenance. `VALIDATION.md` records what was and was not checked.

An **independent rewrite** must construct the finite objects and their laws in the new library, using Mathlib and the pinned infinitary-logic library but not importing the current `VaughtConjecture.Knight` implementation or re-exporting its endpoint. The current source is a mathematical specification and comparison oracle, not an axiom supplying the desired producer. A refactor inside the current implementation is also useful, but is not independent completion. `CurrentEndpointChecks.lean` is explicitly an integration-only checker.

## Mathematical interface to the endpoint

Let \(Q\) be the set of countable base-model isomorphism classes and
\[
\lambda_\xi=\omega+\omega\cdot\xi,\qquad
D_\xi=\{q\in Q:q\text{ admits a model expansion to }\lambda_\xi\}.
\]
Establish, for countable indices:

1. \(D_0=Q\), the domains decrease, and \(D_\delta=\bigcap_{\xi<\delta}D_\xi\) at nonzero countable limits.
2. Each successor loss \(D_\xi\setminus D_{\xi+1}\) is countable.
3. Models in \(D_\eta\) agree on every sentence of quantifier rank at most \(\eta\).
4. Each successor loss is nonempty, by an independent top-free construction.

The first two imply countable domain complements. The third gives countable truth or falsehood sides for every sentence. The existing invariant-separation and witnessed-Morley theorems yield thinness and the upper bound. The fourth gives the lower bound by disjointness of losses. The literal sentence correspondence and absence of finite models give the all-countable-carrier version. No global eventual-departure theorem occurs in this interface.

The first three conditions do not by themselves yield the lower bound. Nonempty domains alone are not a substitute for nonempty losses. Nor does high-stage existence alone produce terminal witnesses.

## Library conventions

Use the standard library's ordinals, cardinalities, `Finset`, `Set`, embeddings, filters, closure operators, syntax, satisfaction, Scott analysis, coded structure spaces, and isomorphism relation. Use the infinitary-logic library's existing domain-countability and sentence-split results instead of redeveloping parallel abstractions. Read ranks and ordinal multiplication with their actual conventions: \(\omega\cdot\xi\) is not \(\xi\cdot\omega\), and block indices are not automatically Scott ranks.

Separate raw finite data from the proposition asserting their laws. A scheme owns its cells, scopes, grades, rows, and face geometry. A stage type owns its scheme and label section. An occurrence owns its literal tuple and evaluated type. A constructor returns concrete data and proves laws about those data. A record field asserting the existence of the desired receiver is not its construction.

Use observations \(\operatorname{obs}_c(q)\), not a presumed lawful cap endomorphism. The observation can take values outside the space of lawful sections. Preserve the permitted-cap test. Keep face restriction, stage reduction, and capped observation as different operations.

### Layer 0 — General results with no Knight imports

**Finite closure.** Develop finite closure operators and anti-exchange geometry, using standard notions. Prove that a finite hull operator has at most one finitary extension to all subsets, and that equality or equivariance on finite hulls extends to the global closure. The general result is reusable; the concrete global wrappers are optional for the endpoint.

**Capped extension.** For a restriction map between lawful section spaces and compatible observations, prove that lifting a prescribed face while preserving the ambient observation is equivalent to surjectivity from an observation fibre onto the corresponding face fibre. Do not assume injectivity, unrestricted caps, or that the observation itself is lawful.

**Directed finite observations.** Develop the bounded/eventually-constant versus unbounded/escaping dichotomy for monotone natural-valued functions on a directed preorder. Prove finite synchronization and appropriate cofinal-reindexing invariance. Reuse filters and \(\mathbb N_\infty\); do not install a new notion of infinitary convergence.

**Countable construction and comparison.** Reuse the dense-set chain theorem and the standard countable potential-isomorphism theorem. Provide the smallest adapters for finite-master conditions and rooted extendible families. Atomic compatibility of an arbitrary root is not enough: the root must belong to the selected extension family.

**Counting and observation.** Prove countability from a countable cover by subsingleton conditions; reuse the existing countable-loss theorem. Develop sentence splitting on a faithful class presentation without a measurable structure on its quotient.

**Summit 0:** these tools are independently usable and their proofs have no construction imports. Do not create a generic framework larger than its two or three real clients require.

### Layer 1 — Finite semantic kernel and closed charts

Define the recursive finite visible-face plans and prove their equivalence with the required subclass of finite convex geometries: every nonsingleton closed set has exactly two extreme points. Develop intersections, restriction, hulls, extremes, and the two-generator property. A two-generator hull need not have size two.

Define the actual graded cells, semantic rows, extended-ordinal labels, visibility replacement, lawful sections, and all-permitted-cap bountifulness. Retain the order, availability, and locality laws from the semantic contract. Prove restriction, transport, pullback, zero/bottom cases, and the bounded transformations actually used by the construction. Guarded composition must retain its guards; do not invent a transitivity instance for a transformation relation that fails unrestricted composition.

Define countable stage types and exact partial face maps, preserving undefined faces. Establish stage-reduction coherence and all countability results needed for the language and requests.

**Summit 1:** a transparent finite semantic category with lawful restriction and exact cap-ball lifting statements, but no model existence assumed.

### Layer 2 — Realizations, syntax, and the common scheduler

Define realizations with exact partial evaluation, consistency, covering, and the four unchanged extension families. Prove isomorphism transport and reduction of models. Derive canonical finite hulls from consistency and covering alone, and prove that actual finite supports are precisely the finite closed sets. Upper-level comparisons should use these hulls where they only need a containing chart; the generic scheduler itself remains geometry-independent.

Construct the base-stage relational language and the literal infinitary sentence. Prove its equivalence with modelhood in both directions, round trips, and isomorphism preservation/reflection. Encode bottom-pattern parameters through their finite observational quotient; do not quantify over an uncountable collection of labellings in the sentence. Prove there are no finite models.

A condition has one finite master chart. Derive its partial realization rather than storing two independently synchronized states. Distinguish a supported invisible face from an unsupported tuple. Absorb roots before request classification. Establish the countable cofinal requirements and the union theorem once, then instantiate it for the exact-family and top-free capped clients without identifying their service contracts.

**Summit 2:** an actual sentence and a countable-construction theorem with the exact finite service premise still explicit. An abstract realization calculus is not a substitute for syntax correspondence.

### Layer 3 — Constructed suppliers, installation, and readback

Construct the finite coface suppliers serving the four model families. Prove the required arbitrary-root and arbitrary-padding statements, including empty roots and roots larger than the small comparison grade where the contract permits them. Preserve designated fresh coordinates and literal master/root equations.

Keep three boundaries visible:

- **Finite construction:** legal finite geometry and rows, arbitrary compatible inputs, every permitted cap, and all installed auxiliary obligations.
- **Installation:** the stated model clauses realize an occurrence of an appropriate supplied diagram over the original root.
- **Readback:** that actual occurrence yields the exact proper, literal-top, or above-threshold information required by its consumer.

Construct ordinary finite-cut receiving, the constrained residual comparison supply, hollow-growth supply, and stable-candidate capped supply. Factor common row calculations and installation only where the complete input and output contracts agree. Ordinary cutoff receiving is weaker than literal top recovery and must not be used as its substitute.

Instantiate the scheduler to obtain countable models and the top-free capped client. The finite work ends before scheduling: finite suppliers and installers must not import their infinite chain consumers.

**Summit 3:** every receiver and existence client has a constructed producer, not an admission predicate or an assumed realization of a new auxiliary diagram.

### Layer 4 — Structural continuation and terminal comparisons

Construct the provisional observations on actual rooted covers. Prove the geometric directedness and transported-cell equations before applying the numerical limit lemma. Build the stable candidate from consistency and covering; prove lawfulness, its exact partial evaluation, and literal reduct before proving modelhood.

Show that every genuine next-block model expansion equals the structural candidate by pointwise normalization. Keep this uniqueness direction separate from existence. For non-hollow unbounded top-grade growth, construct finite cap receiving of the candidate and apply the general cap-to-model theorem. The selected occurrence package is not a required intermediate step.

Retain the original anchor definition of hollowness, and prove its equivalent stable-label fixedness formulation for models. Define top-grade growth directly through covers, not through characteristic arity. Prove the three comparisons:

- same actual globally rigid-core type implies isomorphism;
- no rigid core and the same positive eventual top grade imply isomorphism;
- hollow top-grade growth implies mutual isomorphism.

Count terminal classes using the countable family of conditions
\[
\left(\sum_n S_n^\alpha\right)\sqcup\mathbb N\sqcup\{*\}.
\]
Derive positivity rather than excluding grade zero by assumption. Non-hollow growth prolongation is enough to cover terminal models; a full biconditional characterization of all possible continuation is not a required strengthening.

**Summit 4:** constructed countable terminal fibres and non-hollow growth continuation. No characteristic theory or global termination theorem is a premise.

### Layer 5 — Expansion domains and logical agreement

Construct the expansion domain on actual isomorphism classes. Prove downward closure and literal same-carrier normalization. Establish coherent countable-limit expansions; decreasing sets alone do not prove continuity.

Map successor losses into fixed-stage terminal classes and obtain countability. Apply the generic countable-loss lemma. Prove whole-finite-cover transfer in one block and derive the sharp sentence comparison at block \(\eta\), not merely at block \(\omega\cdot\eta\). Use the existing infinitary back-and-forth semantics, including empty and repeated parameter tuples.

**Summit 5:** every actual infinitary sentence has a countable truth side or false side on the concrete class presentation.

### Layer 6 — The two independent bounds

For the upper bound, delegate to invariant sentence separation and the witnessed Morley alternative. State thinness as absence of a perfect isomorphism antichain, not cardinality below the continuum. Measurability belongs on model codes; no quotient-Borel hypothesis is permitted.

For the lower bound, construct a top-free terminal model at every countable block. Prove that its base class is in that block's loss using expansion uniqueness, then choose from pairwise disjoint losses. This branch must not consume terminal countability, a cardinality conclusion, or eventual departure of every model.

Combine the two bounds, then apply the no-finite-model bridge. Export exact \(\aleph_1\) spectra and perfect-set failures for both natural-number and all-countable carriers.

**Summit 6:** the specified infinitary sentence has the four endpoint properties without producer hypotheses. There is no first-order endpoint in this roadmap.

## Optional developments: downstream, not completion debts

**Closure and definability.** Export global preservation from finite preservation, and investigate the definitional expansion by binary hull operations described in `HULL_ALGEBRA.md`. This gives a candidate route to identifying closed sets with generated substructures and to \(\operatorname{cl}\subseteq\operatorname{dcl}\). Equality with definable or algebraic closure is a separate theorem requiring more information.

**Characteristics and stopping.** Retain characteristic arity, stable spectra, full continuation criteria, canonical stopping towers, eventual departure, and rank comparisons as independent consumers. The current source already has an alternative direct domain count and an eventual-departure theorem; those are not new missing producers.

**Alternative stabilization.** The existing structural construction and finite synchronization suffice. A redesign using product closedness may remain a useful independent implementation, but is not a prerequisite.

**Scott processes, computability, and Polish actions.** Build pointed comparison, exact rank relationships when proved, and action/effective applications as separate libraries. A one-way back-and-forth bound does not identify the expansion tower with a Scott process or its stage index with Scott rank.

## Validation and dependency ownership

Use the supplied Lean/infinitary-logic pins together. Do not mix the current forked Mathlib pin with a separately pinned TauCeti dependency; “TauCeti-style” describes the human-owned layered specification, not a requirement to import the TauCeti repository.

At every summit, elaborate all modules, audit all declarations for placeholders and unexpected axioms, and check the literal statement against the semantic contract. Maintain separate checks for module imports and proof-term dependencies. A small theorem can import a large compatibility layer; a smaller file count does not prove a smaller mathematical dependency. Historical facades should depend on the core, not conversely.

The preparation of this bundle performed source and import-graph inspection only. It supplies no new compiled proof. See `VALIDATION.md` for the exact limits and proposed checks.
