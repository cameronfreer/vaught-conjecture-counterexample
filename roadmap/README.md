# Labelled finite convex geometries and a thin uncountable infinitary class

## Objective and completion criterion

Develop a reusable library of finite closed diagrams, extension of bounded observations, countable realization, stable refinement, and infinitary comparison. Its principal application is the **specified construction**: a countable relational language \(L\) and a sentence \(\Phi\in L_{\omega_1,\omega}\) whose countable isomorphism classes number exactly \(\aleph_1\), with no perfect isomorphism antichain.

The organizing invariant is a **continuous decreasing family of expansion domains with countable successor losses and increasing logical agreement**. Do not require a total stopping rank, exhaustive rank layers, characteristic arity, a canonical terminal representative, or a Borel structure on the quotient of models.

This README is the mathematical roadmap; `IMPLEMENTATION.md` refines it into an implementation order with semantic guards and acceptance checkpoints (with a table relating its numbering to the layers below), and prevails where the two differ. `Suggested.lean` and `SuggestedInterfaces.lean` record selected Lean statements and human-owned theorem targets; proving only the statements in those files does not complete the project. `SEMANTIC_CONTRACT.md` fixes the meanings that any reformulation must preserve. `EXPOSITIONS.md` gives three informal accounts, `LITERATURE.md` the connections with the literature (with `REFERENCES.bib`), and `HULL_ALGEBRA.md` an optional development. `COMPANIONS.md` states three optional companion milestones (filtration and infinitary theory, top-free chart homogeneity, a geometric obstruction), with their Lean statements in `SuggestedCompanions.lean`; the main theorem does not depend on them.


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

The first two imply countable domain complements. The third gives countable truth or falsehood sides for every sentence, and descriptive separation (invariant analytic separation and López–Escobar, in the form of the library's thinness theorem for countable sentence splits) turns these into thinness; descriptive separation is used for thinness only. For the upper bound, Scott separation (distinct classes are separated by a sentence) and the third condition make the persistent core \(\bigcap_{\eta<\omega_1}D_\eta\) a subsingleton, and its complement is covered by the \(\aleph_1\) many countable exceptions \(Q\setminus D_\eta\), so \(|Q|\le\aleph_1\). Morley's dichotomy would also give the upper bound from thinness; it is not used. The fourth gives the lower bound by disjointness of losses. The literal sentence correspondence and absence of finite models give the all-countable-carrier version. No global eventual-departure theorem occurs in this reduction.

The first three conditions do not by themselves yield the lower bound. Nonempty domains alone are not a substitute for nonempty losses. Nor does high-stage existence alone produce terminal witnesses.

## Library conventions

**Terminology.** Use mathematical terminology only. Prose, docstrings, and comments speak of languages, sentences, structures, diagrams, realizations, constructions, hypotheses, and theorems, not of roles in a workflow. The name of a declaration describes its mathematical content (what is constructed, or what is asserted), not its place in the development. Workflow vocabulary (pull requests, CI, review) appears only in the "Building and checking" and "Contributing" sections of the top-level `README.md`, in the "Environment" section and the sections on upstream building blocks and on checkpoints of `IMPLEMENTATION.md`, in the "Validation and dependencies" section of this file, in the import-guard paragraphs of milestone C of `COMPANIONS.md` (the proposed addition to the check script), and in the bibliographic access notes of `LITERATURE.md`. Document-structure vocabulary (layer, summit, checkpoint, acceptance, companion, milestone) may appear in the structural sentences of the roadmap documents, which describe how the roadmap is organized. The construction's own vocabulary (chart, face, root, cell, row, label, cap, cutoff, observation, occurrence, realization, expansion, domain, loss, block, band, grade, anchor, hollow, rigid core, top-free, bountiful, lawful section, plan, scheme, hull, extreme point, stage, type, donor, capped extension) is mathematical and is used only in its defined sense. The vocabulary of the finite constructions (root, donor occurrence, private context, master chart and master row, padding, freshness, bottom pattern, literal-top prescription, catalogue and catalogue fields, orderly rows, legal scheme and legal stage type, owner, ownerwise decoding, long-row locality, gate and gate equations, the coatom extension construction, pinned extension, `Correct`, LOW, and capped extension over a root) is defined in Layer 3 below, and is used only in those senses. In particular:

| Do not write | Write instead |
| --- | --- |
| producer of X | the construction of X; the theorem asserting X |
| consumer, client | the theorem that uses it; application; instance |
| supplier, supply (as a noun) | the finite extension construction |
| receiver, receiving | the extension diagram; the capped-extension property (Layer 3) |
| service contract | the hypotheses on the extension family; hypotheses and conclusions |
| installation, installer | the extension of the realization by one occurrence over the root |
| readback | recovery of the label (or donor data) from the occurrence or observation |
| receipt | the equation(s) recording … |
| certificate | the hypotheses of the counting theorem, or the theorem's name |
| scheduler | the countable chain construction |
| bootstrap | the base case (the empty root) |
| adapter, framework | a specialization; a general theorem |
| debt, obligation, deliverable | a statement still to be proved; a prerequisite |
| endpoint (of the development) | the main theorem |
| export (a result) | prove, state, deduce |
| handoff, pipeline, front end, package, budget | the mathematical map, construction, statement, or bound meant |

Use the standard library's ordinals, cardinalities, `Finset`, `Set`, embeddings, filters, closure operators, syntax, satisfaction, Scott analysis, coded structure spaces, and isomorphism relation. Use the infinitary-logic library's existing domain-countability and sentence-split results instead of redeveloping parallel abstractions. Read ranks and ordinal multiplication with their actual conventions: \(\omega\cdot\xi\) is not \(\xi\cdot\omega\), and block indices are not automatically Scott ranks.

Define raw finite data separately from the proposition asserting their laws. The cells, scopes, grades, rows, and face geometry are part of the data of a scheme. A stage type consists of its scheme and its label section. An occurrence consists of its literal tuple and its evaluated type. A construction returns concrete data and proves laws about those data. A structure field asserting that the desired extension diagram exists is not its construction.

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

Construct the base-stage relational language and the literal infinitary sentence \(\Phi\): the density sentence, consisting of the structural clauses (injective tuples, unique labels, exact face coherence, covering, nonemptiness) and the one-point capped-extension clause. Prove its equivalence with modelhood in both directions, round trips, and isomorphism preservation/reflection. The density sentence is the preferred presentation of the sentence of the main theorem. Prove the required fidelity theorem: \(\Phi\) is equivalent to the four-family sentence, the sentence expressing the structural clauses and the four extension families of [Kni26, Definition 3.2.1], clause 4 (generalized saturation (a), with the general family (a)i and the bottom patterns (a)ii; uniformity (b); high-arity dominance (c)); this equivalence is part of the completion criterion. Its direction from the four-family sentence to the density sentence uses the finite-cut capped-extension statement, row 1 of the table of Layer 3; that statement therefore remains a prerequisite of the completion criterion even though the main theorem is stated for the density sentence. Encode bottom-pattern parameters through their finite observational quotient; do not quantify over an uncountable collection of labellings in the sentence. Prove there are no finite models.

A condition has one finite master chart. Derive its partial realization rather than storing two independently synchronized states. Distinguish a supported invisible face from an unsupported tuple. Absorb roots before request classification. Establish the countable cofinal requirements and the union theorem once, then apply it to the exact-family construction and to the top-free capped construction without identifying their finite extension hypotheses.

**Summit 2:** an actual sentence and a countable-construction theorem with the exact finite extension hypothesis still explicit. An abstract realization calculus is not a substitute for syntax correspondence.

### Layer 3 — Finite extension constructions, realization over the root, and recovery of donor labels

This layer is the specification of the finite constructions. It defines the vocabulary that the other layers, `IMPLEMENTATION.md`, and `SEMANTIC_CONTRACT.md` use for them, and it consists of five items, the checkpoints of this layer: the statements of the finite extension constructions (3.1), a shared decoding lemma (3.2), one occurrence followed by labelled evaluation (3.3), the definitions of `Correct` and LOW (3.4), and the table of extension statements with their first uses (3.5). `IMPLEMENTATION.md` places these items in its checkpoint order.

**Vocabulary.** Fix a stage \(\alpha\) and a realization \(R\) at \(\alpha\); in the applications \(R\) is a model in the sense of [Kni26, Definition 3.2.1], and stage types and face maps are those of [Kni26, Definitions 3.1.1 and 3.1.5]. For a permitted cutoff \(c\), the observation of a labelling \(q\) is \(\operatorname{obs}_c(q)=(x\mapsto\min(q(x),c))\), on every cell \(x\).

- A **root** is an actual occurrence of \(R\): a literal injective tuple \(t\) of some length \(n\ge0\) together with its evaluated type \(p\). The **empty root** (\(n=0\)) is the base case of every statement below; a statement that needs a root of positive length says so, and then treats the empty root separately.
- A **donor type** over the root is a stage type \(d\) with a face embedding \(f\) of the root's coordinates into those of \(d\) along which \(d\) restricts to \(p\). The occurrence supplying these values, an actual occurrence of type \(d\) in \(R\) or in another realization, is the **donor occurrence**.
- A **capped extension over the root** at a permitted cutoff \(c\) is an actual occurrence \(u\) of \(R\) whose restriction along \(f\) is literally \(t\) and with \(\operatorname{obs}_c(\operatorname{eval}u)=\operatorname{obs}_c(d)\); it is **exact** when \(\operatorname{eval}u=d\). \(R\) has the **finite-cut capped-extension property** when every root, every donor type over it, and every permitted cutoff admit a capped extension; the density sentence asserts this for one-point donors, and the general statement allows donors of any finite arity (finite covers of the root). Capped extension at a cutoff is weaker than exact extension, and it never yields equality at the formal top.
- The **private context** of a construction is an actual occurrence of \(R\) containing the root, obtained from covering; it carries the reference cells, the caps, and the gate that the construction reads. The **master chart** is the given finite chart that a construction extends: the private context, or, in the countable chain construction, the master chart of a condition. Its rows, including the **master row** from which the construction derives its new rows, are part of the data retained literally.
- **Padding** enlarges the arity of the constructed chart by coordinates that carry prescribed labels and no request. **Freshness**: designated coordinates are new points, every cell whose support meets one of them is a new cell of the construction, and new cells are not identified with old cells merely because their roles or observations agree.
- A **bottom pattern** is the finite Boolean pattern recording which cells of a prescription are labelled bottom, as in the bottom-pattern family of [Kni26, Definition 3.2.1], clause 4(a)ii. A **literal-top prescription** requires given cells to carry the formal top itself, not a large proper value.
- The **catalogue** is the countable family of legal schemes (below) that index the requests of the construction. **Catalogue fields** are the cells a construction reserves for the requests of the catalogue; among them the **future fields**, whose grade is above the current cutoff, are not read at that cutoff, but their caps are preserved.
- **Orderly rows** are the generic rows of the ordered-cell semantics of Layer 1. A scheme is **legal** when its rows lie in the bounded row coding of the construction, the coding under which the schemes of each arity are countable and finitely described; a **legal stage type** is a stage type on a legal scheme, and the relation symbols of Layer 2 are indexed by legal stage types.
- An **owner** is a cell whose value a decoding lemma recovers, read through the row governing that cell. A **short owner** is one whose row belongs to the bounded coding introduced by the construction; a **long-row owner** is inherited from the master chart with a row not of that form. **Ownerwise decoding** recovers each owner's value from the observations, below the cap, of the cells of its row (for instance, as a maximum of the observations of designated cells of that row). **Long-row locality** is the statement, proved separately for each inherited long row, that this recovery reads only cells inside the owner's support.
- The **gate** of a construction is a designated cell whose non-bottom value activates a recovery statement; the **gate equations** record the gate's value on the actual occurrence.
- The **coatom extension construction** builds a chart whose two coatom faces (the faces obtained by deleting one of its two extreme points) are two given charts agreeing on their common face, as in the amalgamation of [Kni26, §4.3]; its bountifulness is the instance of [Kni26, Lemma 4.3.20].
- A **pinned extension** of a chart is an extension whose restriction to that chart is literally the chart, labels included; it is **top-free** when no label is the formal top.
- `Correct` and LOW are defined in 3.4.

#### 3.1. Statements of the finite extension constructions

For each finite extension construction, state separately:

- **input data:** the master chart and the root in it, the donor type with its face embedding, the permitted cutoff, the padding length, the designated fresh coordinates, the bottom pattern, the literal-top prescriptions, and the reference data read from the private context;
- **compatibility conditions:** the donor type restricts to the root's type; the prescription agrees with the labels of the private context at the cutoff; the bottom pattern and the literal-top prescriptions are consistent with the donor type; the grade bounds of the row coding hold;
- **constructed finite object:** a legal scheme (plan, cells, grades, rows) with an embedding of the master chart, and a lawful labelling, the **witness**, extending the labels of the master chart; both are data, not propositions asserting existence;
- **literal equations:** restriction along the embedding returns the master chart with its rows and labels, and the root, literally; the designated fresh coordinates are new; the witness has the prescribed bottom pattern and literal tops.

Each statement is proved:

1. for every permitted root size, including the empty root and roots larger than the small comparison grade where the hypotheses permit them, and for every permitted padding length, including zero;
2. with designated freshness and literal retention of the root and of the master chart with its master row;
3. with bottom patterns and literal-top prescriptions given separately: neither is derived from the other, and realizing a bottom pattern does not realize literal tops;
4. with cap preservation on every target coordinate, including the auxiliary cells the construction introduces and the future catalogue fields, even where the recovery statement that uses the construction ignores them.

Lifting one cap at a time and preserving all caps simultaneously are different statements. Per-cap lifting is bountifulness [Kni26, Definition 2.5.14]: for each permitted cap \(c\), every lawful face prescription whose observation at \(c\) is that of the face of the ambient section has a lawful extension with the ambient section's observation at \(c\). Simultaneous preservation asks for one extension with the ambient observation at every compatible cap. It follows from per-cap lifting only under two further hypotheses: the ambient section restricts to the ambient face, and, when the prescription and that face differ at a coordinate where the smaller of the two values is bottom (so that no permitted cap is compatible), some extension of the prescription exists. Under these hypotheses a lift at the largest compatible cap preserves every compatible cap, because caps nest under \(\min\); the argument is that of `IMPLEMENTATION.md`, layer 1. Injectivity of restriction is not a hypothesis, and an exact extension statement is not used.

#### 3.2. The shared decoding lemma

Ownerwise decoding is an explicit target. **Statement:** let a construction come with a decoding map from labellings of the constructed scheme to values of its owners. If, for every owner, the decoded value satisfies the owner's row given the decoded values of the cells of that row (the **ownerwise hypothesis**), then the decoded labelling is lawful, and its observation at each permitted cap is determined by the observation of the input at that cap. For short owners the ownerwise hypothesis is one common lemma, proved once from the bounded row coding. For each long-row owner inherited from the master chart it is proved from long-row locality for that row, which is established from that row's own laws; the decoding lemma takes it as a hypothesis and does not derive it.

Both the hollow-growth construction (row 3 of the table in 3.5) and the LOW construction (row 2) are required applications: each is shown to satisfy the ownerwise hypothesis, for its short owners through the common lemma and for each of its inherited long rows through that row's locality proof. The lemma shares the owner-by-owner argument; it does not identify the rows of the different constructions, and it does not replace any construction's own locality proofs.

#### 3.3. One occurrence, then labelled evaluation

Keep three steps separate:

- **Construction:** the finite object of 3.1, as data, with its lifting properties at every permitted cap and the conditions on every auxiliary row it introduces.
- **Extension of the realization by one occurrence:** the model clauses (the bottom-pattern family of [Kni26, Definition 3.2.1], clause 4(a)ii, and uniformity 4(b) and high-arity dominance 4(c) where the construction needs them) give an actual occurrence \(u\) of \(R\) of the constructed scheme, whose restrictions along the embeddings are literally the private context and the root, and whose type has the witness's bottom pattern. The witness shows that the request made of the model clause is admissible; the recovery statement does not read its values.
- **Labelled evaluation:** the recovery statement is proved for every **lawful restriction-compatible labelling** of the constructed scheme (a lawful labelling that restricts to the actual labels of the private context and has the prescribed bottom pattern), and is then applied to the evaluated type of \(u\), which is one such labelling.

The root, the private context, the donor values, and the gate equations all refer to this one occurrence \(u\): the root and the private context are its literal restrictions, the gate equations are equations about its type, and the recovered donor values are values of its type. Equations recorded on different occurrences, even of the same type, are not combined.

The hollow-growth construction (row 3) and the capped extension for the stable candidate (row 4) share one recovery statement, which takes an occurrence of the common diagram shape and a lawful restriction-compatible labelling, and concludes the recovered observations. Their existence hypotheses stay separate. The hollow-growth statement assumes hollowness and unbounded top-grade growth; the stable-candidate statement assumes the structural stable candidate (the expansion of [Kni26, §5.3]) of a model with non-hollow unbounded top-grade growth. The two are not merged into one hypothesis because their evaluation arguments coincide.

#### 3.4. `Correct` and LOW

Both are conditions on labellings of a constructed scheme, relative to the reference data of the private context and a permitted cap \(c\).

- **`Correct`** at \(c\) holds of a labelling when, below \(c\), its **bottom readings** are the prescribed ones (the cells of the bottom pattern are bottom, the others are not), its **reference readings** agree with the recorded labels of the reference cells of the private context, observed at \(c\), and its **marker readings** (the designated marker cells, the gate among them) have their designated values, observed at \(c\). `Correct` is a condition on observations at \(c\): it says nothing about values at or above \(c\), and it reads no future field.
- **LOW** is the additional forcing by which a construction recovers literal donor tops: rows of the constructed scheme implying that, in every lawful labelling in which the gate is non-bottom, every cell whose donor value is the formal top is labelled by the formal top. LOW is a property of the constructed rows, not a consequence of `Correct`.

The recovery statements are three, with separate hypotheses:

1. **exact recovery of proper values:** a recovered cell whose donor value is a proper ordinal \(\beta\) has value exactly \(\beta\);
2. **literal-top recovery:** under LOW, with the gate non-bottom, a cell whose donor value is the formal top has value the formal top;
3. **above-threshold inequalities:** a cell whose donor value is at or above a threshold has value at or above that threshold, possibly the formal top.

The second does not follow from the first or the third. Equality below a single proper cutoff never alone identifies a top: at a successor stage \(\beta+1\), the proper value \(\beta\) and the formal top have the same observation at every permitted cutoff.

Each decoding or recovery lemma lists the observations it reads (the rows of the owners it decodes, below the cap; the gate; the bottom, reference, and marker readings of `Correct`) and concludes only the donor values its first use needs. It does not require recovery of the whole type of the constructed occurrence (its auxiliary cells, private fields, or future fields), and no first use may assume such a recovery.

#### 3.5. Extension statements and their first uses

Each finite extension construction proves one of the following statements about a realization; its first use is the first theorem that uses it. Every conclusion is an equation, or a list of equations, on one actual occurrence over the literal root.

| Statement | Hypotheses | Conclusion on one occurrence | First use | Import boundary |
| --- | --- | --- | --- | --- |
| 1. Finite-cut capped extension, for one-point donors and for finite covers | \(R\) a model at \(\alpha\); any root, the empty root included; any donor type over it; any permitted cutoff | an occurrence over the root with the donor's observation at the cutoff | the one-sided donor transfer (Layer 5); also the direction from the four-family sentence to the density sentence (Layer 2) | the construction imports Layers 0–1 and the realizations of Layer 2, not the chain construction; the transfer imports row 1, not Layer 4 |
| 2. Exact residual extension (the LOW construction) | \(R\) a model at \(\alpha\) with no rigid core and eventual top grade \(K\) (positive, since eventual grade zero makes the empty tuple a rigid core); a root and donor type within the grade bounds of the residual comparison | an occurrence over the root whose type is the donor's on the requested cells: proper values exactly, literal tops by LOW with the gate equations on the same occurrence | the residual comparison (Layer 4) | the construction does not import any comparison or the chain construction; the comparison imports row 2 |
| 3. Hollow-growth extension | \(R\) a hollow model with unbounded top-grade growth; a root and donor type as in the hollow comparison | an occurrence over the root recovering the donor values the hollow comparison reads, each by a named statement of 3.4 | the hollow comparison (Layer 4) | as for row 2; rows 3 and 4 share only the recovery statement of 3.3 |
| 4. Capped extension for the stable candidate | the structural stable candidate of a model with non-hollow unbounded top-grade growth; a root of positive length (the empty root is the base case, from nonemptiness and covering); a donor type; a permitted cutoff | an occurrence of the candidate over the root with the donor's observation at the cutoff | stable modelhood, through the general cap-to-model theorem (Layer 4) | the construction imports the structural candidate (consistency and covering only), not its modelhood; modelhood imports row 4 |
| 5. Top-free pinned extension | a top-free chart (the master chart of a condition), a top-free request on it, any permitted padding | a top-free pinned extension of the chart meeting the request | the top-free capped chain construction (Layers 2–3), which gives the lower bound of Layer 6 | the construction imports Layer 1 only; the chain construction uses it only through the hypotheses of its union theorem and imports none of rows 1–4 |

Rows 1–4 are the four extension statements used in the rest of the construction; row 5 is used by the top-free capped construction alone, and the exact-family and top-free chain constructions do not identify their finite extension hypotheses. The positive-length restriction of row 4 and the empty-root base case are explicit in its statement; any other row whose construction needs a point of the root states the same restriction and base case. Share row calculations and occurrences over the root between the rows only where their complete hypotheses and conclusions agree. Capped extension at a cutoff (row 1) is weaker than literal-top recovery and is not a substitute for it.

Apply the countable chain construction to obtain countable models and the top-free capped models. The finite work ends before the chain construction: the finite extension constructions and the extensions of realizations by one occurrence must not import the infinite chain constructions that use them.

Direct limits of structures, a generic result of infinitary logic, stay outside this layer: they belong to the generic library and to companion results, and they replace neither a finite extension construction nor a decoding or recovery statement.

**Summit 3:** every row of the table has an actual finite construction (3.1), a proof that the realization extends by one occurrence of it over the literal root (3.3), a recovery theorem for the observations its first use reads (3.2–3.4), and a proved first use. An abstract statement of a row, a predicate asserting admissibility, or an assumed realization of a new auxiliary diagram is not a substitute for any of these. A row whose first use lies in a later layer reaches this summit when that first use is proved; its construction still does not import the first use.

### Layer 4 — Structural continuation and terminal comparisons

Construct the provisional observations on actual rooted covers. Prove the geometric directedness and transported-cell equations before applying the numerical limit lemma. Build the stable candidate from consistency and covering; prove lawfulness, its exact partial evaluation, and literal reduct before proving modelhood.

Show that every genuine next-block model expansion equals the structural candidate by pointwise normalization. Keep this uniqueness direction separate from existence. For non-hollow unbounded top-grade growth, construct the finite capped extensions of the candidate (row 4 of the table of Layer 3) and apply the general cap-to-model theorem. The selected-occurrence construction is not a required intermediate step.

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

For thinness, apply descriptive separation, in the form of the library's thinness theorem for countable sentence splits, to the countable truth sides of Layer 5. For the upper bound, apply Scott separation on the persistent core: distinct classes are separated by a sentence, so by the agreement of Layer 5 the persistent core \(\bigcap_{\eta<\omega_1}D_\eta\) is a subsingleton, and its complement is covered by the \(\aleph_1\) many countable exceptions \(Q\setminus D_\eta\). Morley's dichotomy (the witnessed perfect-set alternative) is an alternative route to the upper bound that is not used. State thinness as absence of a perfect isomorphism antichain, not cardinality below the continuum. Measurability belongs on model codes; no quotient-Borel hypothesis is permitted.

For the lower bound, construct a top-free terminal model at every countable block. Prove that its base class is in that block's loss using expansion uniqueness, then choose from pairwise disjoint losses. The proof of the lower bound must not use terminal countability, a cardinality conclusion, or eventual departure of every model.

Combine the two bounds, then apply the no-finite-model bridge. Prove the exact \(\aleph_1\) spectra and perfect-set failures for both natural-number and all-countable carriers.

**Summit 6:** the specified infinitary sentence has the four properties of the main theorem, with no hypotheses asserting that the finite constructions exist. There is no first-order counterpart of the main theorem in this roadmap.

## Optional developments, not required for the main theorem

**Closure and definability.** Deduce global preservation from finite preservation, and formalize the definitional expansion by binary hull operations described in `HULL_ALGEBRA.md`, which identifies the canonical closure with generated-substructure closure. The inclusion \(\operatorname{cl}\subseteq\operatorname{dcl}\) is deduced from it there. Equality with definable or algebraic closure is a separate theorem requiring more information.

**Status of the optional results.** The table separates established results, whose proofs are known and which remain formalization targets here, from statements that are only deduced or are open.

| Result | Status |
| --- | --- |
| The binary hull operations and the equality of the canonical closure with generated-substructure closure (`HULL_ALGEBRA.md`, (1)) | established, proof known; to be formalized here |
| The seven companion targets A1, A2, A3, B1, B2, B3, and C (`COMPANIONS.md`) | established, proofs known; to be formalized here |
| The inclusions \(\operatorname{cl}\subseteq\operatorname{dcl}\subseteq\operatorname{acl}\) (`HULL_ALGEBRA.md`, (2)) | deduced from (1) in `HULL_ALGEBRA.md`, §4; not counted among the established results |
| Any reverse inclusion, and equality of \(\operatorname{cl}\) with \(\operatorname{dcl}\) or \(\operatorname{acl}\) | open; requires a separate argument |

**Characteristics and stopping.** Retain characteristic arity, stable spectra, full continuation criteria, canonical stopping towers, eventual departure, and rank comparisons as independent developments built on the core.

**Alternative stabilization.** The existing structural construction and finite synchronization suffice. An alternative proof using product closedness may remain independently useful, but is not a prerequisite.

**Scott processes, computability, and Polish actions.** Build pointed comparison, exact rank relationships when proved, and applications to Polish group actions and computability as separate libraries. A one-way back-and-forth bound does not identify the expansion tower with a Scott process or its stage index with Scott rank.

## Validation and dependencies

Use the pinned Lean and infinitary-logic versions together. Do not mix the current forked Mathlib pin with a separately pinned TauCeti dependency; “TauCeti-style” describes the human-owned layered roadmap, not a requirement to import the TauCeti repository.

At every summit, elaborate all modules, audit all declarations for placeholders and unexpected axioms, and check the literal statement against the semantic contract. Maintain separate checks for module imports and proof-term dependencies. A small theorem can import a large compatibility layer; a smaller file count does not prove a smaller mathematical dependency. Modules kept for historical compatibility should depend on the core, not conversely.
