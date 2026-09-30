# The simplified construction: three expositions

**Scope.** These expositions describe the mathematical argument. The main theorem concerns a specified sentence of **infinitary** logic, not a first-order counterexample. Bibliographic keys refer to `LITERATURE.md` and `REFERENCES.bib`. Page lengths below mean approximate manuscript lengths, not fixed rendered pagination.

## One paragraph

The construction produces a countable relational language and an infinitary sentence whose countable models form an uncountable class that no infinitary sentence can divide into two uncountable collections of isomorphism types. Its finite pieces are labelled finite convex geometries: closed sets have canonical hulls, and each nonsingleton closed set has two extreme points. A carefully designed extension property allows lawful labels on a closed face to be extended while retaining any permitted bounded observation of an ambient labelling. Countable models are assembled by meeting countably many extension requirements. The same finite constructions give comparison and continuation theorems for an ordinal-indexed tower of expansions. At each countable stage, terminal models fall under countably many conditions, each determining at most one isomorphism type: a specified rigid finite core, an eventual top grade without such a core, or hollow unbounded growth. Consequently, the classes admitting expansion to a given stage have countable complement; sufficiently high expansions agree on any prescribed infinitary sentence. Standard invariant separation then excludes a perfect set of pairwise nonisomorphic models. Distinct classes are separated by a sentence, so at most one class admits expansions to every stage, and the others lie in \(\aleph_1\) many countable complements: there are at most \(\aleph_1\) classes. (Morley's theorem would also give this bound; it is not used.) Separately constructed terminal models at every countable stage give at least \(\aleph_1\). No global stopping-rank theorem is needed.

## One page

### A thin uncountable class built from finite closed diagrams

The intended outcome is a countable language \(L\) and a sentence \(\Phi\in L_{\omega_1,\omega}\) with exactly \(\aleph_1\) countable models up to isomorphism, but no perfect set of pairwise nonisomorphic countable models. A useful stronger organizing property is **sentence minimality**: every infinitary sentence is true in only countably many of these isomorphism types, or false in only countably many. The construction can be explained through finite closed diagrams and the domains on which ordinal expansions exist, rather than through a canonical rank assigned to every model.

The finite geometry is familiar. Visible subsets form a finite convex geometry: they are closed under intersection and satisfy anti-exchange. There is an additional restriction: every nonsingleton closed set has exactly two extreme points. In a realization, exact agreement of overlapping charts and the existence of charts containing every finite set produce a canonical finite hull. The global closure is obtained by taking the union of the hulls of finite subsets. Its finite closed sets are precisely the supports of actual charts. Thus the partiality of a chart restriction has a geometric meaning: a subset may fail to be closed.

Each diagram also carries finitely many graded cells and ordinal-valued labels, with bottom and top symbols. The semantic rows constrain which labellings are lawful. The essential extension property is a surjectivity statement. Given an ambient lawful section, a lawful section on a closed face, and a cap self-visible at the grade of the target at which they agree, one can extend the face section while preserving the ambient section's capped observation everywhere. (These caps are not the permitted cutoffs of the density sentence; at a cap that is not self-visible the extension is not available in general.) The finite construction must prove this for every allowed input and every such cap. Stronger variants separately recover exact donor data, including the top symbol; bounded agreement alone does not do that.

The base-stage finite types index the relation symbols of \(L\). The sentence \(\Phi\), the density sentence, says that these relations form a coherent covering system and that every root, donor, and permitted cutoff admit a one-point capped extension. It is proved equivalent to the requirement that models meet four specified families of extension requirements. Countably many dense requirements on finite master charts give countable models. This is a countable extension construction, not an appeal to first-order compactness or to unrestricted Fraïssé amalgamation.

The labels admit successive refinements through blocks \(\lambda_\xi=\omega+\omega\cdot\xi\). Enlarging a finite chart gives monotone numerical observations: a bounded observation eventually stabilizes, while an unbounded one escapes every finite threshold. These determine a lawful stable candidate for the next expansion before its modelhood is considered. Finite receiving proves that non-hollow unbounded growth really continues. The remaining terminal models are covered by countably many descriptions: a specified rigid-core type, a positive eventual top grade in the absence of a rigid core, or hollow growth. Ordinary back-and-forth proves uniqueness within each description. Characteristic arity is unnecessary for this count.

Now let \(Q\) be the set of isomorphism classes of countable base models, and let \(D_\xi\subseteq Q\) consist of classes admitting an expansion to block \(\xi\). These sets decrease continuously at countable limits. Successor losses are countable because they come from terminal models, so \(Q\setminus D_\eta\) is countable for every countable \(\eta\). A one-block comparison transfers a whole finite chart, giving agreement on sentences of quantifier rank at most \(\eta\) throughout \(D_\eta\). Every sentence therefore has a countable truth side or false side.

Invariant analytic separation and López–Escobar turn a hypothetical perfect isomorphism antichain into a sentence splitting it into two uncountable parts, a contradiction. For the upper bound, distinct classes are separated by a sentence (a Scott sentence), while every sentence is constant on a sufficiently high domain; so at most one class lies in every \(D_\eta\), and every other class lies in one of the \(\aleph_1\) many countable complements \(Q\setminus D_\eta\). Hence \(|Q|\le\aleph_1\). The perfect-set form of Morley's theorem would give the same bound from thinness; it is not used. A separate top-free construction supplies a terminal model at each block; uniqueness of expansion places their base classes in pairwise disjoint successor losses, giving the lower bound. The proof does not need to show that every class eventually leaves the expansion domains.

## Five pages

### 1. Finite convex geometry supplies the diagrams

The construction starts with finite combinatorial objects, not with a large pre-existing structure. On a finite set \(A\), specify which subsets are to count as closed. The recursive description glues two diagrams on sets obtained by deleting different points, requires agreement on their common face, and then adds \(A\) itself as a closed set. The resulting family is a finite convex geometry: it contains the empty set and singletons, is closed under intersection, and satisfies anti-exchange. The particular subclass used here has exactly two extreme points in every nonsingleton closed set. These two points generate that closed set, although the pair itself need not be closed and its hull can be arbitrarily large.

This geometry is not decorative. It tells us which restrictions of a finite chart are legitimate charts. A subset outside the closed-set family has no restricted type. The finite object also carries graded cells: a cell has a closed support and a positive integer grade bounded by that support's size. Semantic rows describe the permissible relationships between labels on cells lying below a given support and grade. They enforce order, availability, and locality conditions. At a countable stage \(\alpha\), labels lie in
\[
\{-\infty\}\cup\alpha\cup\{\infty\}.
\]
The formal top \(\infty\) is not an ordinal. It records information that a later expansion may resolve into a new ordinal band.

A stage type is a finite scheme together with a lawful labelling. For countable \(\alpha\), there are only countably many stage types of each finite arity. A realization assigns such a type to certain injective finite tuples. It satisfies **exact consistency**: restricting a typed tuple gives exactly the prescribed partial restriction, including its being undefined. It also satisfies **covering**: every finite tuple is contained in a typed tuple. These are distinct requirements; exact consistency says more than agreement whenever both sides happen to be defined.

From these two structural axioms alone, every finite subset \(F\) of the carrier has a least finite closed superset \(h(F)\). Compute it inside any containing chart; consistency and a common larger chart show that the answer is independent of that choice. The operator
\[
\operatorname{cl}(A)=\bigcup\{h(F):F\subseteq A\text{ finite}\}
\]
is therefore a locally finite, finitary anti-exchange closure. Its finite closed sets are exactly the supports of actual charts. Every individual closure membership has a witness involving at most two elements of the original set. This does not assert that an arbitrary infinite closed set is generated by one pair.

This gives the first useful simplification of language: the models are systems of **labelled finite closed substructures**, even though the formalization initially presents them as partial tuple evaluations. The convex geometry explains the domain of evaluation; the semantic rows explain the additional label constraints. Neither should be confused with the other, and the closure is not assumed to be model-theoretic algebraic closure.

### 2. Extension of bounded observations builds actual models

The central finite theorem concerns restriction of lawful sections. Fix a lawful labelling \(q\) of a finite target diagram and a closed face with restriction map \(r\). For a cap \(c\) self-visible at the grade \(j\) of the target (bottom, top, or a \(j\)-times successor; such caps are not the permitted cutoffs of receiving, which only need \(\bot<c<\alpha\)), define the cap ball around \(q\) by
\[
B_c(q)=\{q'\text{ lawful}:\min(q'(d),c)=\min(q(d),c)\text{ for every cell }d\}.
\]
The extension property is exactly
\[
r[B_c(q)]=B_c(rq).
\]
Thus any lawful face prescription agreeing with the ambient labelling at the cap \(c\) has a lawful extension preserving that same capped observation on the whole target. This is the precise content of bountifulness. It is a surjectivity property, not uniqueness of extension. The word “ball” refers to an observation-equivalence class; no metric is required, and the capped vector itself need not be a lawful section.

The construction must provide actual finite diagrams satisfying this property for every such cap and arbitrary compatible lawful inputs. The property is one cap at a time: one extension preserving all compatible caps at once is neither claimed nor needed, since density asks for one extension for each cutoff. It is not enough to list desirable profiles or exhibit the final numerical values. The special receiving diagrams involve three separate steps. First, construct the finite geometry and semantic rows, proving all of their extension properties. Second, use the model's stated extension clauses to realize an appropriate diagram over the literal prescribed root. Third, recover from that actual occurrence the required relationship with the donor data. Ordinary receiving gives agreement below a proper cutoff; the constrained residual and hollow-growth constructions recover more of the donor data when the classification needs it. In particular, equality below a finite cutoff never by itself establishes equality at the formal top.

At the base stage \(\omega\), put one relation symbol \(P_p\) in the language for every finite type \(p\). There are countably many symbols. Their intended meaning is that an injective tuple is an actual chart of type \(p\). The sentence \(\Phi\) of the main theorem, the density sentence, asserts exact consistency, covering, nonemptiness, and a one-point capped-extension clause: for every root, donor, and cutoff there is a one-point extension. A required theorem proves it equivalent to the \(L_{\omega_1,\omega}\)-sentence asserting the same structural clauses and the four extension families: general extension requests, prescribed bottom patterns, occurrences in the required ordinal bands, and high-grade dominance. Each family asks for **some** member of a specified collection of cofaces, not the exact realization of every conceivable extension. Although one original parameterization uses arbitrary ordinal labellings, the relevant bottom-pattern request depends only on a finite Boolean pattern; this is why that part of the sentence remains countable.

Countable models are assembled by a standard dense-requirement construction. A condition consists of one finite master chart; its partial realization is derived from its faces. Requirements ensure that every point is absorbed and every relevant extension request is met. A root is absorbed before its request is decided. Thereafter exact consistency makes a wrong-type or invisible-face answer permanent. Meeting countably many cofinal requirements produces an increasing chain, whose union has the desired properties.

This resembles the familiar construction of a generic countable structure, but the exact logical strength matters: only the designated extension families have been proved dense. No unrestricted amalgamation property or first-order compactness is being substituted for the finite argument. The exact-family construction and the later top-free capped construction share the countable chain construction, while retaining different finite extension hypotheses.

### 3. Stable refinement and the three terminal comparisons

Higher stages allow the formal top to be resolved into larger ordinal values. The natural stage increments are blocks of length \(\omega\): from \(\alpha\) to \(\alpha+\omega\). For a fixed top-labelled cell in an actual chart, examine its transported copies in larger charts. The semantic rows determine a provisional finite offset. The receiving and consistency calculations ensure monotonicity on the directed family of covers.

The numerical limiting principle is elementary. A bounded monotone natural-valued family eventually takes its greatest attained value; an unbounded family eventually exceeds every prescribed integer. Equivalently, its supremum lies in \(\mathbb N\cup\{\infty\}\). A finite stable offset \(n\) is interpreted as the new ordinal label \(\alpha+n\); an infinite offset is interpreted as the formal top. It is not interpreted as the ordinal \(\alpha+\omega\). Labels that were already below the top retain their old values.

Finite synchronization and the row laws prove that these stable labels form a lawful realization. This **structural stable candidate** exists from consistency and covering alone. Proving that it is a model is a separate problem, because the next stage imposes new extension requirements. Conversely, any genuine next-block model expansion must have exactly these labels. That normalization is proved pointwise, including undefined tuples; it does not assume in advance that the candidate is a model.

Two pieces of information govern the terminal analysis. The **top grade** of a finite chart is the largest grade carrying a top label, or zero when there is no such cell. It is monotone under taking covers. Consequently its directed behaviour is either eventual constancy at a finite value or unbounded growth. Separately, a model is **hollow** when it has no persistent semantic anchor at the top. For models, the existing anchor theorem gives a useful equivalent description: the stable refinement leaves every label unchanged. A non-hollow model therefore has at least one old top cell that acquires a finite value in the next band. Hollowness is not the assertion that the model has no top-labelled cells.

The difficult continuation theorem states that **non-hollow top-grade growth prolongs**. Its proof constructs enough finite capped receiving instances for the structural candidate; a general cap-to-model theorem then gives modelhood. Its reduct is literally the original realization on the same carrier. The selected-occurrence statement is a separate consequence, not a required intermediate formulation of continuation.

To count terminal models at a fixed countable stage, three comparisons suffice. Models with a globally rigid finite core are compared from its finite type. Here rigidity concerns admissible top supports in every larger chart, not the absence of automorphisms. Without a rigid core, models with the same eventual top grade \(K\) are isomorphic by the residual receiving comparison. Such a \(K\) is positive: eventual grade zero makes the empty tuple a rigid core. Finally, hollow models with unbounded top grade are mutually isomorphic by the hollow-growth comparison. Non-hollow growth cannot occur in a terminal model, by continuation.

These comparisons are ordinary countable back-and-forth after the required family of compatible finite charts has been constructed. There are countably many finite core types, countably many possible \(K\), and one hollow-growth condition. Each condition contains at most one isomorphism class. The conditions need not form a disjoint partition or define a canonical invariant. This is the entire terminal-countability argument; characteristic arity and a global stopping theorem are not needed.

### 4. Expansion domains replace a global rank

Write
\[
\lambda_\xi=\omega+\omega\cdot\xi\qquad(\xi<\omega_1),
\]
and let \(Q\) be the set of isomorphism classes of countable models of the base sentence. Define
\[
D_\xi=\{[M]\in Q:M\text{ admits a model expansion to }\lambda_\xi\}.
\]
This definition concerns existence of an expansion. It neither assigns a stopping rank to every class nor assumes that every class eventually stops. Reducing an expansion to an earlier stage shows that the domains decrease, and \(D_0=Q\).

The next fact is genuine mathematics, not formal manipulation of sets: at a countable limit stage, compatible earlier expansions have a limit expansion. The normalization and coherence results let the construction apply to the expansions given by domain membership. Thus, for every nonzero countable limit \(\delta\),
\[
D_\delta=\bigcap_{\xi<\delta}D_\xi.
\]
A class in \(D_\xi\setminus D_{\xi+1}\) has an expansion at block \(\xi\) that cannot continue. Such an expansion is terminal, so the preceding countability theorem shows that this successor loss is countable. This argument does not require a globally chosen terminal expansion for each base model.

A transfinite induction now gives
\[
Q\setminus D_\eta\text{ is countable for every }\eta<\omega_1.
\]
At a successor, add the countable new loss to the earlier complement. At a countable limit, take the countable union of the earlier complements. This elementary set-theoretic lemma is independent of the construction and belongs in the general library.

What do the surviving domains buy logically? Finite receiving transfers an entire finite cover in one block. Applied to a chart containing a tuple and a proposed witness, it gives the successor step of the usual back-and-forth induction. Restrictions handle atomic information, and countable conjunctions and disjunctions handle the limit steps. With the quantifier-rank convention used here, any two models whose classes lie in \(D_\eta\) agree on all sentences of rank at most \(\eta\). One block suffices for a whole finite cover; an extra factor of \(\omega\) in the block index would be wasted.

For an arbitrary infinitary sentence \(\psi\), choose a countable \(\eta\) at least its quantifier rank. The truth of \(\psi\) is constant on \(D_\eta\). One of its truth and falsehood sets on \(Q\) is therefore contained in the countable complement of \(D_\eta\). This is sentence minimality. Notice how little the conclusion needs: continuous decreasing domains with countable losses, and increasing logical agreement on those domains. It does not need a complete classification of all models, a measurable ordinal invariant, equality between expansion height and Scott rank, or eventual departure of every class.

### 5. The descriptive-set-theoretic conclusion and independent lower bound

Return to actual structures with carrier \(\mathbb N\). In a countable relational language these form the usual Polish coding space, and satisfaction of an infinitary sentence is Borel. Isomorphism is the orbit relation of the permutation group of \(\mathbb N\). The quotient \(Q\) is useful as a set of classes, but no standard Borel structure on that quotient is assumed. The argument uses Borel and analytic sets of model codes instead.

Suppose there were a perfect family of pairwise nonisomorphic models of \(\Phi\). Taking a Cantor subfamily, split its parameter space into two disjoint perfect pieces. Saturating their images under isomorphism gives disjoint invariant analytic sets, each containing uncountably many isomorphism classes. Invariant separation supplies a Borel invariant separator. By López–Escobar, this separator is defined by an \(L_{\omega_1,\omega}\)-sentence. That sentence is true on the first uncountable family and false on the second, contradicting sentence minimality. Hence the class is thin: it has no perfect isomorphism antichain.

The upper bound comes from Scott separation on the persistent core. Distinct isomorphism classes of countable models are separated by a sentence, for instance the Scott sentence of either one. A sentence of quantifier rank at most \(\eta\) is constant on \(D_\eta\), so two classes lying in every domain agree on every sentence and are equal: the persistent core \(\bigcap_{\eta<\omega_1}D_\eta\) has at most one element. Every other class lies in some countable complement \(Q\setminus D_\eta\), and there are \(\aleph_1\) many of these, so
\[
|Q|\leq\aleph_1.
\]
Morley's counting theorem, in its perfect-set or witnessed form, would also yield this bound from thinness; that route is not used. Thinness and the cardinal bound are separate conclusions: the bare cardinal trichotomy would leave open a thin class of continuum many types when continuum exceeds \(\aleph_1\), and under CH absence of a perfect antichain is stronger information than the cardinal bound alone. The construction does not assume the continuum hypothesis, nor does it define thinness as having fewer than continuum many classes.

The lower bound uses a separate application of the countable chain construction. At every countable block, it builds a **top-free** model: all labels are proper or bottom, yet the required finite capped requests are met. Such a model is terminal. A putative next expansion would leave its old proper labels unchanged, while the new stage requires occurrences in the new ordinal band. These requirements are incompatible. Expansion normalization and uniqueness ensure that the base isomorphism class of this terminal model really belongs to
\[
L_\xi=D_\xi\setminus D_{\xi+1};
\]
it cannot secretly have a different expansion at the same stage that continues.

Each \(L_\xi\) is therefore nonempty. The sets \(L_\xi\) are pairwise disjoint because the domains decrease. Choosing one member of each loss gives an injection from the countable ordinals into \(Q\), so \(\aleph_1\leq |Q|\). Together with the upper bound this gives exactly \(\aleph_1\) classes and no perfect antichain. The sentence has no finite models, so passing between structures on \(\mathbb N\) and structures on arbitrary countable carriers does not change the spectrum.

The resulting proof has a clean division of labour. The new finite mathematics constructs lawful receiving diagrams and proves the three terminal comparisons and continuation. A standard countable construction supplies existence. An elementary domain argument turns those results into sentence minimality. Standard invariant descriptive set theory provides thinness, Scott separation provides the upper bound, and separately constructed losses provide the lower bound. Global stopping, a characteristic-based classification, and further closure or definability theory can be developed afterward without becoming prerequisites of the main theorem.
