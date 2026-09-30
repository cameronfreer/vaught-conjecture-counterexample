# Labelled finite convex geometries and a thin uncountable infinitary class

## Objective and completion criterion

Develop a reusable library of finite closed diagrams, extension of bounded observations, countable realization, stable refinement, and infinitary comparison. Its principal application is the **specified construction**: a countable relational language \(L\) and a sentence \(\Phi\in L_{\omega_1,\omega}\) whose countable isomorphism classes number exactly \(\aleph_1\), with no perfect isomorphism antichain.

The organizing invariant is a **continuous decreasing family of expansion domains with countable successor losses and increasing logical agreement**. Do not require a total stopping rank, exhaustive rank layers, characteristic arity, a canonical terminal representative, or a Borel structure on the quotient of models.

This README is the mathematical roadmap; `IMPLEMENTATION.md` refines it into an implementation order with semantic guards and acceptance checkpoints, and prevails where the two differ. `Suggested.lean` records selected Lean statements and human-owned theorem targets; proving only the statements in that file does not complete the project. `SEMANTIC_CONTRACT.md` fixes the meanings that any reformulation must preserve. `EXPOSITIONS.md` gives three informal accounts. 


## Reduction of the main theorem to expansion domains

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

The first two imply countable domain complements. The third gives countable truth or falsehood sides for every sentence, and the library's thinness theorem for countable sentence splits turns these into thinness. For the upper bound, Scott separation (distinct classes are separated by a sentence) and the third condition make the persistent core \(\bigcap_{\eta<\omega_1}D_\eta\) a subsingleton; every other class lies in one of the \(\aleph_1\) many countable complements \(Q\setminus D_\eta\), so \(|Q|\le\aleph_1\). Morley's dichotomy would also give the upper bound from thinness; it is not used. The fourth gives the lower bound by disjointness of losses. The literal sentence correspondence and absence of finite models give the all-countable-carrier version. No global eventual-departure theorem occurs in this reduction.

The first three conditions do not by themselves yield the lower bound. Nonempty domains alone are not a substitute for nonempty losses. Nor does high-stage existence alone produce terminal witnesses.

## Library conventions

**Terminology.** Use mathematical terminology only. Prose, docstrings, and comments speak of languages, sentences, structures, diagrams, realizations, constructions, hypotheses, and theorems, not of roles in a workflow. The name of a declaration describes its mathematical content (what is constructed, or what is asserted), not its place in the development. Workflow vocabulary (pull requests, CI, review) appears only in the contributing notes of the top-level `README.md` and in the checkpoint section of `IMPLEMENTATION.md`. Document-structure vocabulary (layer, summit, checkpoint, acceptance) may appear in the structural sentences of the roadmap documents, which describe how the roadmap is organized. The construction's own vocabulary (chart, face, root, cell, row, label, cap, cutoff, observation, occurrence, realization, expansion, domain, loss, block, band, grade, anchor, hollow, rigid core, top-free, bountiful, lawful section, plan, scheme, hull, extreme point, stage, type, donor, receiving) is mathematical and is used only in its defined sense; the same keep-list contains **summit**, used only as the milestone label at the end of a layer. Some terms are used before their definitions are written: LOW, `Correct`, gate (and gate equations), catalogue fields, ownerwise (short-owner) decoding, long-row locality, orderly rows, legal (scheme, stage type), and the coatom extension construction. They are to be defined by the forthcoming layer-3 specification (layer 3 of `IMPLEMENTATION.md`); they are not on the keep-list, and no definition of them is implied here. In particular:

| Do not write | Write instead |
| --- | --- |
| producer of X | the construction of X; the theorem asserting X |
| consumer, client | the theorem that uses it; application; instance |
| supplier, supply (as a noun) | the finite extension construction |
| receiver | the receiving diagram; the receiving property |
| service contract | the hypotheses on the extension family; hypotheses and conclusions |
| installation, installer | the realization of a diagram over the root |
| readback | recovery of the label (or donor data) from the occurrence or observation |
| receipt | the equation(s) recording … |
| certificate | the hypotheses of the counting theorem, or the theorem's name |
| scheduler | the countable chain construction |
| adapter, framework | a specialization; a general theorem |
| debt, obligation, deliverable | a statement still to be proved; a prerequisite |
| endpoint (of the development) | the main theorem |
| export (a result) | prove, state, deduce |
| handoff, pipeline, front end, package, budget | the mathematical map, construction, statement, or bound meant |

Use the standard library's ordinals, cardinalities, `Finset`, `Set`, embeddings, filters, closure operators, syntax, satisfaction, Scott analysis, coded structure spaces, and isomorphism relation. Use the infinitary-logic library's existing domain-countability and sentence-split results instead of redeveloping parallel abstractions. Read ranks and ordinal multiplication with their actual conventions: \(\omega\cdot\xi\) is not \(\xi\cdot\omega\), and block indices are not automatically Scott ranks.

Define raw finite data separately from the proposition asserting their laws. The cells, scopes, grades, rows, and face geometry are part of the data of a scheme. A stage type consists of its scheme and its label section. An occurrence consists of its literal tuple and its evaluated type. A construction returns concrete data and proves laws about those data. A structure field asserting that the desired receiving diagram exists is not its construction.

Use observations \(\operatorname{obs}_c(q)\), not a presumed lawful cap endomorphism. The observation can take values outside the space of lawful sections. Preserve the permitted-cap test. Keep face restriction, stage reduction, and capped observation as different operations.

### Layer 0 — General results with no construction imports

**Finite closure.** Develop finite closure operators and anti-exchange geometry, using standard notions. Prove that a finite hull operator has at most one finitary extension to all subsets, and that equality or equivariance on finite hulls extends to the global closure. The general result is reusable; the concrete global corollaries are optional for the main theorem.

**Capped extension.** For a restriction map between lawful section spaces and compatible observations, prove that lifting a prescribed face while preserving the ambient observation is equivalent to surjectivity from an observation fibre onto the corresponding face fibre. Do not assume injectivity, unrestricted caps, or that the observation itself is lawful.

**Directed finite observations.** Develop the bounded/eventually-constant versus unbounded/escaping dichotomy for monotone natural-valued functions on a directed preorder. Prove finite synchronization and appropriate cofinal-reindexing invariance. Reuse filters and \(\mathbb N_\infty\); do not introduce a new notion of infinitary convergence.

**Countable construction and comparison.** Reuse the dense-set chain theorem and the standard countable potential-isomorphism theorem. Prove only the specializations needed for finite-master conditions and rooted extendible families. Atomic compatibility of an arbitrary root is not enough: the root must belong to the selected extension family.

**Counting and observation.** Prove countability from a countable cover by subsingleton conditions; reuse the existing countable-loss theorem. Develop sentence splitting on a faithful class presentation without a measurable structure on its quotient.

**Summit 0:** these results are stated independently of the construction, and their proofs do not import it. Do not state a general result in greater generality than its two or three actual applications require.

### Layer 1 — Finite semantic kernel and closed charts

Define the recursive finite visible-face plans and prove their equivalence with the required subclass of finite convex geometries: every nonsingleton closed set has exactly two extreme points. Develop intersections, restriction, hulls, extremes, and the two-generator property. A two-generator hull need not have size two.

Define the actual graded cells, semantic rows, extended-ordinal labels, visibility replacement, lawful sections, and all-permitted-cap bountifulness. Retain the order, availability, and locality laws from the semantic contract (`SEMANTIC_CONTRACT.md`). Prove restriction, transport, pullback, zero/bottom cases, and the bounded transformations actually used by the construction. Guarded composition must retain its guards; do not declare a transitivity instance for a transformation relation that fails unrestricted composition.

Define countable stage types and exact partial face maps, preserving undefined faces. Establish stage-reduction coherence and all countability results needed for the language and requests.

**Summit 1:** a transparent finite semantic category with lawful restriction and exact cap-ball lifting statements, but no model existence assumed.

### Layer 2 — Realizations, syntax, and the countable chain construction

Define realizations with exact partial evaluation, consistency, covering, and the four unchanged extension families. Prove isomorphism transport and reduction of models. Derive canonical finite hulls from consistency and covering alone, and prove that actual finite supports are precisely the finite closed sets. Later comparisons should use these hulls where they only need a containing chart; the general countable chain construction itself does not depend on the geometry.

Construct the base-stage relational language and the literal infinitary sentence \(\Phi\): the density sentence, consisting of the structural clauses (injective tuples, unique labels, exact face coherence, covering, nonemptiness) and the one-point capped-extension clause. Prove its equivalence with modelhood in both directions, round trips, and isomorphism preservation/reflection. Prove the required fidelity theorem: \(\Phi\) is equivalent to the sentence expressing the four extension families, whose model-to-density direction uses ordinary receiving (Layer 3); this equivalence is part of the completion criterion. Encode bottom-pattern parameters through their finite observational quotient; do not quantify over an uncountable collection of labellings in the sentence. Prove there are no finite models.

A condition has one finite master chart. Derive its partial realization rather than storing two independently synchronized states. Distinguish a supported invisible face from an unsupported tuple. Absorb roots before request classification. Establish the countable cofinal requirements and the union theorem once, then apply it to the exact-family construction and to the top-free capped construction without identifying their finite extension hypotheses.

**Summit 2:** an actual sentence and a countable-construction theorem with the exact finite extension hypothesis still explicit. An abstract realization calculus is not a substitute for syntax correspondence.

### Layer 3 — Finite extension constructions, realization over the root, and recovery of donor labels

Construct, for each of the four model families, the finite cofaces it requires. Prove the required arbitrary-root and arbitrary-padding statements, including empty roots and roots larger than the small comparison grade where the hypotheses permit them. Preserve designated fresh coordinates and literal master/root equations.

Keep three steps separate:

- **Finite construction:** legal finite geometry and rows, arbitrary compatible inputs, every permitted cap, and the conditions on every auxiliary row the construction introduces.
- **Realization over the root:** the stated model clauses realize an occurrence of an appropriate constructed diagram over the original root.
- **Recovery of donor labels:** that actual occurrence yields the exact proper, literal-top, or above-threshold information required by the theorem that uses it.

Construct ordinary finite-cut receiving, and the finite extension constructions for the constrained residual comparison, for hollow growth, and for the capped stable candidate. Share row calculations and realizations over the root between these constructions only where their complete hypotheses and conclusions agree. Ordinary cutoff receiving is weaker than literal top recovery and must not be used as its substitute.

Apply the countable chain construction to obtain countable models and the top-free capped models. The finite work ends before the chain construction: the finite extension constructions and the realizations over the root must not import the infinite chain constructions that use them.

**Summit 3:** every receiving property and every existence statement is proved by an explicit construction, not by a predicate asserting admissibility or an assumed realization of a new auxiliary diagram.

### Layer 4 — Structural continuation and terminal comparisons

Construct the provisional observations on actual rooted covers. Prove the geometric directedness and transported-cell equations before applying the numerical limit lemma. Build the stable candidate from consistency and covering; prove lawfulness, its exact partial evaluation, and literal reduct before proving modelhood.

Show that every genuine next-block model expansion equals the structural candidate by pointwise normalization. Keep this uniqueness direction separate from existence. For non-hollow unbounded top-grade growth, construct finite cap receiving of the candidate and apply the general cap-to-model theorem. The selected-occurrence construction is not a required intermediate step.

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

For thinness, apply the library's thinness theorem for countable sentence splits to the countable truth sides of Layer 5. For the upper bound, apply Scott separation on the persistent core: distinct classes are separated by a sentence, so by the agreement of Layer 5 at most one class lies in every domain, and every other class lies in one of \(\aleph_1\) many countable complements. Morley's dichotomy (the witnessed perfect-set alternative) is an alternative route to the upper bound that is not used. State thinness as absence of a perfect isomorphism antichain, not cardinality below the continuum. Measurability belongs on model codes; no quotient-Borel hypothesis is permitted.

For the lower bound, construct a top-free terminal model at every countable block. Prove that its base class is in that block's loss using expansion uniqueness, then choose from pairwise disjoint losses. The proof of the lower bound must not use terminal countability, a cardinality conclusion, or eventual departure of every model.

Combine the two bounds, then apply the no-finite-model bridge. Prove the exact \(\aleph_1\) spectra and perfect-set failures for both natural-number and all-countable carriers.

**Summit 6:** the specified infinitary sentence has the four properties of the main theorem, with no hypotheses asserting that the finite constructions exist. There is no first-order counterpart of the main theorem in this roadmap.

## Optional developments, not required for the main theorem

**Closure and definability.** Deduce global preservation from finite preservation, and investigate the definitional expansion by binary hull operations described in `HULL_ALGEBRA.md`. This gives a candidate route to identifying closed sets with generated substructures and to \(\operatorname{cl}\subseteq\operatorname{dcl}\). Equality with definable or algebraic closure is a separate theorem requiring more information.

**Characteristics and stopping.** Retain characteristic arity, stable spectra, full continuation criteria, canonical stopping towers, eventual departure, and rank comparisons as independent developments built on the core.

**Alternative stabilization.** The existing structural construction and finite synchronization suffice. An alternative proof using product closedness may remain independently useful, but is not a prerequisite.

**Scott processes, computability, and Polish actions.** Build pointed comparison, exact rank relationships when proved, and applications to Polish group actions and computability as separate libraries. A one-way back-and-forth bound does not identify the expansion tower with a Scott process or its stage index with Scott rank.

## Validation and dependencies

Use the pinned Lean and infinitary-logic versions together. Do not mix the current forked Mathlib pin with a separately pinned TauCeti dependency; “TauCeti-style” describes the human-owned layered roadmap, not a requirement to import the TauCeti repository.

At every summit, elaborate all modules, audit all declarations for placeholders and unexpected axioms, and check the literal statement against the semantic contract. Maintain separate checks for module imports and proof-term dependencies. A small theorem can import a large compatibility layer; a smaller file count does not prove a smaller mathematical dependency. Modules kept for historical compatibility should depend on the core, not conversely.
