# A definable binary-operation presentation of the canonical hull

**Status:** the construction of the operations and the equality (1) of the canonical closure with generated-substructure closure are established results (at the base stage and, by the same argument with stage types, at every countable stage): their proofs are known, and are the argument below, from the hull and coordinate-formula theorems, which are themselves established results with known proofs, to be formalized here. For realizations they remain formalization targets here. For finite charts (a chart read as the face realization of its stage type) the following are compiled in this repository (theorem named), in `Language/HullOperations` and `Language/HullDefinability`: the two-charts theorem (`StageType.eq_of_restrictFace_eq_some`); the graph formula of each operation, with at most one solution of its unique-coordinate formula (§1: `HullIndex.graphFormula`, `StageType.realize_graphFormula`, `StageType.eq_of_realize_chartWitnessFormula`); §2 (`StageType.hullOp_mem_hull`); §3 (`StageType.exists_hullOp_eq_of_mem_hull`, under legality along the hull of the pair); the inclusion \(\operatorname{cl}\subseteq\operatorname{dcl}\) of (2) (§4: `StageType.definable₁_singleton_of_mem_hull`, under legality along the hull, which cannot be dropped); and §5 for chart embeddings (`StageType.hullOp_map_of_restrictFace`, default value included, and `StageType.hull_map_of_restrictFace`), with the identification of embeddings and substructures under legality: every embedding of two charts is a chart embedding when one of them is legal (`StageType.exists_eq_chartEmbedding`), and the substructures of a legal chart are its closed faces (`StageType.exists_equiv_comap`; legality is essential there, `Language/HullOperationsExamples`). For realizations other than the face realizations of charts these need the two-charts theorem for exactly consistent covering realizations, a statement still to be proved here. The inclusions (2) are a short deduction from (1), recorded in §4; they are not counted among the established results, and no reverse inclusion or equality with \(\operatorname{dcl}\) or \(\operatorname{acl}\) is claimed.

**Place in the roadmap.** Five facts are part of the core, the facts of `README.md`, Layer 2 ("Hull operations: finite charts as finite substructures"), which the classical limit of the top-free witnesses uses: finite hulls and their generators (§3); the definable total hull operations (§§1–2); their preservation by chart embeddings, including the default value when no chart witness exists (§5); closed images of embeddings (§5); and the correspondence between finite expanded substructures and actual charts (§5, with (1) for finite sets). The reconstruction roundtrip of §5 is part of the acceptance criterion of finite-age reconstruction (`SEMANTIC_CONTRACT.md`, item 11). The inclusion \(\operatorname{cl}\subseteq\operatorname{dcl}\) of (2), read in the full stage chart language at each stage and proved by the unique-coordinate formulas of §1, is a Layer 2 statement still to be proved (`README.md`, Layer 2, "Hull closure inside definable closure"), not one of the five facts; equality with \(\operatorname{dcl}\) or \(\operatorname{acl}\) is not asserted. Everything else here stays downstream and optional and is not a premise of the main theorem on the spectrum: the other consequences of §4, the equality (1) for infinite sets, cardinal bounds (§6), uncountable maximality, and the descriptive consequences. The proofs of the core facts, in particular of closed images, import none of the cardinality material.

## Statement

For every exactly consistent covering realization at the base stage (and, with the stage types at \(\lambda\) in place of the base-stage types, at every countable stage \(\lambda\); the classical limit uses it at \(\lambda=\lambda_\eta\)), there is a countable family of **parameter-free first-order definable total binary operations** \((f_i)_{i\in I}\) such that, for every subset \(A\) of its carrier,
\[
\operatorname{cl}(A)
=A\cup\{f_i(a,b):i\in I,\ a,b\in A\}.
\tag{1}
\]
In particular, the canonical closure is exactly generated-substructure closure in the definitional expansion by these operations. The expanded structure is locally finite, and
\[
\operatorname{cl}(A)\subseteq\operatorname{dcl}_L(A)\subseteq\operatorname{acl}_L(A).
\tag{2}
\]
Here definable/algebraic closure is taken in the actual base-language structure. No reverse inclusion is asserted.

## 1. Construct the operations, rather than postulating Skolem functions

Index an operation by a base-stage finite type \(q\) of arity \(m\ge2\), an ordered pair of coordinate indices \(i_0,i_1\) containing its extreme coordinates, and a target coordinate \(j<m\). There are countably many such indices.

Use the first-order formula
\[
\theta_{q,i_0,i_1,j}(x_0,x_1,y)=
\exists z_0\cdots z_{m-1}\bigl(P_q(\bar z)\land
z_{i_0}=x_0\land z_{i_1}=x_1\land z_j=y\bigr).
\]
The chart relation includes injectivity in the realization structure. If \(\theta(a,b,y)\) has any witness, that witness is an actual \(q\)-chart with the prescribed endpoints. The two-charts theorem (an established result with a known proof; compiled for finite charts as `StageType.eq_of_restrictFace_eq_some`, and to be formalized here for realizations) says that any other such chart agrees coordinate by coordinate. Therefore \(\theta(a,b,y)\) has at most one solution, for **every** pair \(a,b\), not merely for a separately supplied chart. This passage uses a witness to apply the uniqueness theorem; it does not assume existence for an arbitrary pair.

Define
\[
f_i(a,b)=
\begin{cases}
y,&\theta_i(a,b,y),\\
a,&\neg\exists y\,\theta_i(a,b,y).
\end{cases}
\]
Its graph is the first-order formula
\[
\theta_i(x_0,x_1,y)\ \lor\
\bigl(\neg\exists z\,\theta_i(x_0,x_1,z)\land y=x_0\bigr).
\]
The default is the first argument, so no distinguished element or new constant is needed. When \(a=b\), a nonsingleton injective chart with two different extreme coordinates cannot be witnessed; the default handles this case. The operations are uniformly definable on the class of consistent covering realizations; no saturation or modelhood assumption beyond those used by chart uniqueness is added.

## 2. Every operation stays inside the two-point hull

If the defining formula has no witness, \(f_i(a,b)=a\in\operatorname{cl}(\{a,b\})\). If it has a witness, its actual chart is generated by the designated extreme coordinates. Its support is therefore the least closed set containing \(a,b\), namely \(h(\{a,b\})\). The output coordinate lies in that hull. Thus
\[
f_i(a,b)\in\operatorname{cl}(\{a,b\})
\]
for every index and every pair. Monotonicity implies that the right-hand side of (1) is contained in \(\operatorname{cl}(A)\).

## 3. Every hull point is obtained by one operation on original generators

Let \(x\in\operatorname{cl}(A)\). The pair-witness theorem (an established result with a known proof, to be formalized here) supplies a finite \(T\subseteq A\), with \(|T|\le2\), such that \(x\in h(T)\). Empty and singleton sets are closed (an established result with a known proof, to be formalized here), so the cases \(|T|\le1\) contribute only points already in \(A\).

Otherwise write \(T=\{a,b\}\) with \(a\ne b\). The finite hull \(H=h(T)\) is an actual chart support. Its extreme points lie in every generating set: if an extreme point were absent from \(T\), removing it would leave a smaller closed set containing \(T\), contrary to minimality of \(H\). Since a nonsingleton closed set has exactly two extremes, its extremes are precisely \(a,b\).

Choose an enumeration \(\bar z\) of this actual chart, its type \(q\), the coordinates of \(a,b\), and the coordinate \(j\) of \(x\). These data index one of the operations above, and \(\theta_i(a,b,x)\) holds. Consequently \(f_i(a,b)=x\). This proves the other inclusion in (1).

In particular, one simultaneous application of all indexed operations to pairs of original generators already gives a closed set. This is a setwise generation statement, not a uniform syntactic normal-form identity for arbitrary terms.

## 4. Consequences and boundaries

The set \(\operatorname{cl}(A)\) contains \(A\) and is closed under every operation by the containment just proved and idempotence of \(\operatorname{cl}\). Every operation-closed set containing \(A\) contains the right-hand side of (1), so it contains \(\operatorname{cl}(A)\). Hence this is generated-substructure closure. Finite sets have finite canonical hulls, so the resulting algebra is locally finite even though the binary signature is countable.

Each output is uniquely first-order definable over its two arguments; equation (1) gives the inclusion in definable closure, at the base stage and, in the full stage chart language, at every stage (`README.md`, Layer 2). The expansion is definitional on the class, so it does not change its isomorphism classes or countable spectrum. It does not make the original class first-order axiomatizable.

The finite-hull preservation theorems (established results with known proofs, to be formalized here) also let higher-stage realizations be compared with their base reducts. Once their immediate global finite-character corollaries are proved, the same hull-generation assertion can be expressed using the base language on those higher-stage models.

What this does **not** prove: equality with full definable or algebraic closure; quantifier elimination; the amalgamation property of any class of finite structures (the amalgamation of top-free charts is a separate finite theorem, step 2 of the classical limit, proved from the coatom extension property); a two-point closed root for receiving; a bound on the size of a pair hull; or a first-order Vaught counterexample. To prove \(\operatorname{dcl}(A)\subseteq\operatorname{cl}(A)\), one would need a separate argument excluding unique definitions of points outside the hull. No such argument is supplied here.

## 5. Finite charts as finite substructures, and embeddings

These facts complete what the classical limit uses (`README.md`, Layer 2, items 3–5), together with the reconstruction roundtrip. They are short consequences of §§1–3 and of the hull theorems cited there. For finite charts and chart embeddings they are compiled, under the legality hypotheses stated in the status line above (essential for the identification of substructures with closed faces); for embeddings of realizations other than the face realizations of charts, and the reconstruction roundtrip, they are statements still to be proved here.

**Finite charts.** A chart \(p\) on \(n\) points determines a finite structure on its points: the relation \(P_q\) holds at a tuple of its points exactly when the tuple spans a visible face whose restriction is \(q\) (its partial realization; a supported invisible face carries no relation), and each operation \(f_i\) is computed by its defining formula inside the chart. Inside a realization, the chart of an actual occurrence and its support with the induced structure are isomorphic: the relations agree by exact consistency, and the operations agree because the hull of two points of the support, and every chart witnessing a defining formula on them, lies inside the support (§2). By (1) for finite sets, the finitely generated substructures of the expansion are exactly the finite closed sets, so they are exactly the supports of actual charts.

**Preservation and reflection of embeddings.** Let \(e\) be an embedding of stage-chart-language structures between exactly consistent covering realizations: an injective map carrying each actual chart to an actual chart of the same type, and carrying no other tuple to an actual chart. For points \(a\ne b\) of the source, the hull \(h(\{a,b\})\) is the support of an actual chart \(C\) whose extreme points are \(a\) and \(b\) (§3); its image \(e(C)\) is an actual chart of the same type, and its support is closed and has extreme points \(e(a)\) and \(e(b)\), so it is the hull of \(\{e(a),e(b)\}\) in the target. A witness of \(\theta_i(e(a),e(b),y)\) in the target is therefore an enumeration of \(e(C)\), and the corresponding enumeration of \(C\) is a witness of \(\theta_i(a,b,\cdot)\) in the source (exact consistency, along the reindexing between the two enumerations); conversely the image of a source witness is a target witness. Hence \(e(f_i(a,b))=f_i(e(a),e(b))\), in the default case as well, and \(e\) is an embedding of the expansions; every embedding of the expansions is one of the relational reducts. In particular the automorphisms of a realization as a stage-chart-language structure and as a structure in the definitional expansion are the same maps: every automorphism of the relational reduct is an automorphism of the expansion, and conversely. For the classical limit, whose operations come from the Fraïssé construction, chart homogeneity in the relational language uses only that automorphisms of the expansion are automorphisms of the reduct (`README.md`, Layer 0); the converse holds there too once the roundtrip below identifies its operations with the definable ones, but it is not used. Chart embeddings, face maps along which restriction is literal, are exactly the embeddings of the corresponding finite structures.

Definability alone would not give this for arbitrary embeddings: an embedding that is not elementary need not preserve a definable function (for automorphisms, definability would suffice). The argument uses that each operation, where its defining formula has a witness, is witnessed by an actual chart on the hull of its two arguments, and that embeddings carry such charts to charts of the same type.

**Closed images of embeddings.** With \(e\) as above, the image of a finite closed set is closed. By the pair-witness theorem for finite sets (§3), the hull of a finite set is the union of the hulls of its pairs of points (and of its points), and \(e\) carries the hull of \(\{a,b\}\) onto the hull of \(\{e(a),e(b)\}\), as just shown; so the hull of \(e(A)\) is the image of the hull of \(A\), which is \(e(A)\) when \(A\) is a finite closed set. The argument uses only exact consistency, covering, and the finite geometry, not the cardinality material of §6 or of the library's `TwoGeneratorCardinality`.

**The reconstruction roundtrip.** Both directions are literal. (a) Reconstructing a realization from its canonical definitional expansion returns that realization: the chart relations of the expansion are the actual charts. (b) Let \(M\) be a structure in the expanded language that is *locally charted*: every finite tuple lies in a finitely generated substructure isomorphic to the finite structure of a chart. Reconstruct its partial evaluation from the chart relations, and expand the reconstructed realization by the definable hull operations: the result has the original relations and the original functions of \(M\). For the functions, take the substructure generated by \(a\) and \(b\); it is isomorphic to the structure of a chart, in which \(f_i(a,b)\) is computed by the defining formula, witnessed by a chart inside it or given by the default. In the default case there is no witness elsewhere: a witness \(\bar z\), charted together with \(a\) and \(b\) (local chart coverage of the tuple \(a,b,\bar z\)), is a visible face of that chart with extreme points \(a,b\), whose support is the hull of \(a,b\) there, hence lies in the substructure generated by \(a\) and \(b\). Local chart coverage is all that is used: homogeneity is needed later, for receiving, and not for the roundtrip. Special cases: the empty carrier where the language allows it, repeated inputs \(f_i(a,a)\) (the default), and every case in which the defining formula has no witness (the default value). The roundtrip is a statement still to be proved here (`SEMANTIC_CONTRACT.md`, item 11).

## 6. A direct cardinal ceiling (optional)

Suppose that infinite hulls preserve cardinality (the closure of an infinite set has the cardinality of the set) and that every proper closed subset of the carrier is countable. Then the carrier has cardinality at most \(\aleph_1\): otherwise choose a subset of cardinality \(\aleph_1\); its closure has cardinality \(\aleph_1\), so it is a proper closed set that is uncountable, a contradiction. No free-set theorem is used. The hypotheses are those of the uncountable consequences, which stay downstream (`COMPANIONS.md`); this section is not a premise of the main theorem, and the core facts of §5 do not import it.
