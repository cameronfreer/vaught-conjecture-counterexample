# Companion milestones: filtration, chart homogeneity, and a geometric obstruction

This document organizes three companion milestones.  They are **optional relative to the core
theorem**: the main theorem of [`README.md`](README.md) and [`IMPLEMENTATION.md`](IMPLEMENTATION.md)
is proved without them, and no core layer or checkpoint depends on them.  Each milestone can be
completed on its own: none uses a theorem of another milestone, and each lists the core results it
takes as hypotheses.  [`SuggestedCompanions.lean`](SuggestedCompanions.lean) records
selected statements in their generic form, some proved and some left as deliberate `sorry`
targets; [`SEMANTIC_CONTRACT.md`](SEMANTIC_CONTRACT.md) applies unchanged.  Layer numbers here
are those of `README.md` (layers 0–6); the table at the head of `IMPLEMENTATION.md` relates them
to that document's layers and checkpoints.

**What counts as completion.**  A milestone is complete when its theorems are proved about the
concrete objects of the construction (charts, realizations, the density sentence `Φ`, the
expansion domains), each under exactly its stated hypotheses, together with the generic theorems
they specialize.  A structure whose fields assert the desired conclusions, with projection lemmas
restating them, does not complete any target.  A generic theorem proved with its hypotheses
not yet proved for the construction is progress on a target, not its completion.  The rules
of `README.md` ("Library conventions") apply, including the terminology table and the keep-list.
The literature these milestones rely on is recorded in `LITERATURE.md`, §7.

**Status.** The targets A1, A2, A3, B2, and B3 are established results: their proofs are known, and
are the arguments given with each below. They remain formalization targets here. C, in its two-point
form, is a statement still to be proved here, with its argument given below. B4 is a statement still
to be proved; it quotes a theorem available at the pin (signatures checked), and assumes orbit
formulas of the first signed level. B1, the joint embedding and amalgamation of top-free charts, is
part of the core: it is step 2 of the construction of the top-free witnesses (`README.md`, section
"The top-free witnesses: the finite age and its classical limit"), and its entry below is a pointer.
The deliberate `sorry` targets of the sketch, the ingredients marked "to be located or added
upstream", and the theorems marked "prospective" (neither available upstream nor pinned;
`IMPLEMENTATION.md`, "Dependency pins") are what is not yet formalized or available. The bounded
back-and-forth separation interface, and ComputableModelTheory's rooted uniqueness and isolation and
primeness over named parameters, are available at the pin (signatures checked; `IMPLEMENTATION.md`,
"Dependency pins"). The status covers these statements only, not their non-claims and not further
definability claims (`README.md`, "Status of the optional results").

## Notation

* `Q`: the isomorphism classes of countable models of `Φ`, presented by codes of models on `ℕ`
  with actual satisfaction (`ModelsOf Φ`, `structureIsoSetoid`); `truth ψ q` is satisfaction of
  the sentence `ψ` by the models in the class `q`.
* `λ_η = ω + ω·η`; `D_η ⊆ Q` the classes admitting a model expansion to `λ_η`; the loss at `η` is
  `D_η \ D_{η+1}`.  All indices are countable ordinals.
* `T∞ = {ψ ∈ L_{ω₁,ω} : {q ∈ Q : ¬ truth ψ q} is countable}`, the sentences true in all but
  countably many classes (`cocountableTheory` in the sketch).
* The **stage chart language** at stage `λ` has one relation symbol for each stage type at `λ` of
  each finite arity (the language of layer 2 is the case `λ = ω`).  A realization at `λ` is read
  as a structure in this language: a tuple satisfies the symbol of the type `p` exactly when it is
  an actual chart of type `p`.  The **base reduct** of such a structure is its reduct to the
  language at `ω`.
* A realization is **top-free** when no actual chart carries the formal top label.  The
  **top-free witness** at block `η` is the countable top-free terminal model at `λ_η` constructed
  for the lower bound (layer 6), and `w_η ∈ Q` its base class; by expansion uniqueness `w_η` lies
  in the loss at `η`.

Upstream names below were checked in the pinned InfinitaryLogic (`def5cc0`, signatures checked), the
pinned ComputableModelTheory (`0e9935b`, signatures checked), and Mathlib, except those marked
"available upstream" or "prospective" (`README.md`, Layer 0); the sketch `#check`s or applies only
names available at the current pins.

## Milestone A — filtration and infinitary theory

Core results used as hypotheses: the density sentence and the absence of finite models
(layer 2); countable complements `Q \ D_η` and countable losses (layer 5, via
`compl_countable_of_loss`); the sharp agreement "classes in `D_η` agree on every sentence of
quantifier rank at most `η`" (layer 5); nonempty losses (layer 6, lower bound).

### A1. Definable cuts and losses

**Statement.**  For every countable `η`:

1. there is a sentence `δ_η` with `truth δ_η q ↔ q ∈ D_η` for every `q ∈ Q`;
2. there is a sentence `ℓ_η` with `truth ℓ_η q ↔ q ∈ D_η \ D_{η+1}` for every `q ∈ Q`;
3. if the loss at `η` is nonempty, every sentence defining it on `Q` has quantifier rank
   **strictly above** `η`; the same bound holds for every sentence defining `D_{η+1}` on `Q`.

**Hypotheses.**  (1) and (2): a presentation of `Q` by codes with actual satisfaction, and the
countability of `Q \ D_η`, respectively of the loss.  (3): `D_{η+1} ⊆ D_η`, agreement of the
classes of `D_η` on sentences of rank at most `η`, and `D_{η+1}` nonempty (it contains
`w_{η+1}`).  Generic forms in the sketch: `exists_sentence_defining_of_compl_countable` (proved)
and `lt_qrank_of_defines_loss` (proved).

**Upstream ingredients.**  `exists_sentence_of_countable_of_presentation`,
`sentence_definable_iff_of_presentation`, `truth_not_of_presentation`,
`isolatedPresentation_of_surjective` (`Descriptive/ScottDefinability`); `Sentenceω.qrank`
(`Lomega1omega/QuantifierRank`); `compl_countable_of_loss` (`OrdinalCountability`).

**Instantiation.**  `δ_η` is the negation of the countable disjunction of the Scott sentences
of the classes outside `D_η`, and `ℓ_η` the disjunction of the Scott sentences of the classes in
the loss.  For (3): `w_η` satisfies `ℓ_η` and `w_{η+1}` does not, both lie in `D_η`, and they
agree on every sentence of rank at most `η`; hence `η < qrank ℓ_η`.

**Special cases.**  `η = 0`, where `D_0 = Q` is defined by a sentence of rank `0` (the bound in
(3) concerns losses and `D_{η+1}`, not `D_η`); a nonzero countable limit `η`, where
`D_η = ⋂_{ξ<η} D_ξ` and the agreement used is the one at the limit itself; a loss consisting of a
single class.

**Non-claims.**  No effective or uniform choice of `δ_η` or `ℓ_η`: they depend on enumerations of
countable sets of classes.  No upper bound on their quantifier rank.  No claim that `δ_η` is a
syntactic transcription of "admits an expansion to `λ_η`".  No measurable structure on `Q`.

### A2. Witness convergence

**Statement.**  For every sentence `ψ` and every countable `η ≥ qrank ψ`,
`truth ψ w_η ↔ ψ ∈ T∞`.  Consequently `T∞` is the set of sentences eventually true at the
top-free witnesses, and it is complete and consistent on `Q`: for each `ψ`, exactly one of `ψ` and
`¬ψ` lies in `T∞`.

**Hypotheses.**  Countable complements `Q \ D_η`; agreement on `D_η` at rank `η`; `w_η ∈ D_η`;
`Q` uncountable (from the lower bound).  Generic forms: `truth_iff_mem_cocountableTheory` and
`witness_truth_iff_mem_cocountableTheory` (both proved).  Only `w_η ∈ D_η` is used, so the
statement holds for any choice of witnesses in the domains.

**Upstream ingredients.**  `Sentenceω.qrank`; for countably many sentences at once,
`sentences_constant_off_countable` (`Descriptive/ObservableConstancy`).

**Instantiation.**  `w_η` the base class of the top-free witness at block `η`; the threshold for
`ψ` is `qrank ψ`, a countable ordinal.

**Special cases.**  `ψ` of rank `0`; `η = qrank ψ` exactly (the threshold is attained, not only
exceeded); `η` a limit; the exclusion of `ψ, ¬ψ ∈ T∞` together, which uses the uncountability of
`Q`.

**Non-claims.**  Sentencewise truth convergence only: no convergence of codes in the model-code
space, no coherent embeddings between the witnesses, no limit model.  No model of all of `T∞` is
asserted to exist.  The rank threshold is not claimed to be optimal.

### A3. The Scott/`T∞` dichotomy

**Statement.**  Every model `N` of `Φ`, on an arbitrary carrier in an arbitrary universe,
satisfies exactly one of:

* **(S)** the Scott sentence of some countable model `M` of `Φ` (the library's `scottSentence`);
* **(T)** every sentence of `T∞`.

In case (S), `N` and `M` agree on every `L_{ω₁,ω}` sentence.  In case (T), by the completeness in
A2, the `L_{ω₁,ω}` theory of `N` is exactly `T∞`.

**Hypotheses.**  `Φ` has no finite models (in the universe of `N`); the codes present every model
of `Φ` on `ℕ` up to isomorphism.  Nothing else: the dichotomy itself uses neither thinness nor
the agreement of layer 5; only the description of case (T) in terms of a complete theory uses A2.
Generic form: `scott_xor_cocountableTheory` (target); exclusivity is
`not_realize_isolating_of_cocountableTheory` (proved).

**Required proof.**  The implementation exposes the countable-exception argument.  Exclusivity:
the negation of a Scott sentence fails in exactly one class, so it lies in `T∞`.  Coverage: if
`N` fails some `ψ ∈ T∞`, the classes failing `ψ` are countably many; the fragment generated by
`Φ`, `ψ`, and their Scott sentences is countable; a countable fragment-elementary substructure
`N₀` of `N` satisfies `Φ ∧ ¬ψ`, is infinite, is coded on `ℕ`, and therefore satisfies one of those
Scott sentences, which then holds in `N`.  Agreement in case (S) is the same argument with the
fragment generated by the Scott sentence and the given sentence.  The dichotomy is not stated
under an additional abstract hypothesis (such as a field asserting that every model has a
countable elementary substructure in some class, or asserting the dichotomy).

**Upstream ingredients.**  `exists_countable_aElementary_substructure`
(`ModelTheory/FragmentLowenheimSkolem`); `AElementary.realize_sentence_iff`
(`ModelTheory/AElementary`); `Fragment.generatedTheory`, `Fragment.generatedTheory_countable`,
`Fragment.mem_generatedTheory` (`Lomega1omega/Fragment`); `scottSentence`,
`scottSentence_characterizes` (`Scott/Sentence`, `Scott/RefinementCount`);
`isolatedPresentation_of_surjective`; `StructureSpaceOn.encodeViaEquiv`
(`Descriptive/CodeTransport`); `LomegaEquiv.of_equiv` (`Lomega1omega/Theory`).  To be located or
added upstream: invariance of `L_{ω₁,ω}` satisfaction under isomorphism across carrier universes
(`LomegaEquiv.of_equiv` and `encodeViaEquiv_models` require one universe); the Scott
characterization across universes (`scottSentence_characterizes` requires one universe, but
`realize_scottFormula_iff_BFEquiv` (`Scott/Formula`) and `PotentialIso.ofExtensionFamily` already
work across universes, while the stabilization step (`StabilizesAt`,
`stabilizationOrdinal_stabilizes_of`, through which `scottSentence_characterizes_of` passes) and
the countable back-and-forth step `PotentialIso.countable_toEquiv_graph` are stated for one
universe); a named
lemma that the Scott sentence of a code isolates its class on a presentation (currently the
content of the proof of `isolatedPresentation_of_surjective`, whose statement is existential).
Statements proved in `VaughtConjecture.MainTheorem.Spectrum` for want of upstream versions, with
their natural upstream homes: `realize_boundedFormulaω_equiv` and `realize_sentenceω_equiv` become
redundant once `BoundedFormulaω.realize_equiv` and `LomegaEquiv.of_equiv` are generalized in
place to carriers in different universes; `qrank_lt_omega_one` (`Lomega1omega/QuantifierRank`);
`classTruth` with its lemmas (`Descriptive/StructureIsoSetoid`) and `exists_mem_modelsOf_equiv`
(`Descriptive/CodeTransport`).

**Instantiation.**  The sentence `Φ`, its presentation `Q`, and its `T∞`: every model of `Φ` of
any cardinality either is `L_{ω₁,ω}`-equivalent to a countable model of `Φ` through a Scott
sentence, or has theory `T∞`.

**Special cases.**  `N` countable (case (S) with its own Scott sentence; so no countable model of
`Φ` satisfies `T∞`); `N` on `ℕ` and on another countable carrier; `N` in a universe different from
the codes'; the finite case, excluded by hypothesis (a finite structure is not coded on `ℕ`, and for
a sentence with finite models the dichotomy can fail).

**Non-claims.**  Case (S) gives infinitary agreement, not an isomorphism between differently
sized models.  No uncountable model of `Φ` is asserted to exist, in either case.  No model of all
of `T∞` is asserted to exist.  No uncountable categoricity, no statement about `L_{∞,ω}`.

**Completion criterion (A).**  A1–A3 are proved for `Φ`, `Q`, `D_η`, and `w_η`, with the generic
lemmas proved and the dichotomy proved on an arbitrary carrier in an arbitrary universe through
the countable-exception argument quoted above.  Completion presupposes that the core results
listed at the head of A are proved in the core, in particular the countable losses (and
complements), the sharp agreement, and the existence of the top-free witnesses; a version of
A1–A3 taking them as hypotheses is progress on A, not its completion (as in the preamble).

### A separate library milestone: bounded back-and-forth separation

A generic theorem of InfinitaryLogic, at our pinned dependency (signatures checked;
`IMPLEMENTATION.md`, "Upstream building blocks" and "Dependency pins"): for a relational language,
every analytic set of pairs of structures on `ℕ` containing no isomorphic pair is uniformly
separated at some countable back-and-forth level (`exists_uniform_bfSeparation`,
`Descriptive/BFSeparation`). With cocountable back-and-forth concentration (given here by the
expansion domains, on which classes agree at bounded level) this is expected to yield thinness
without sentence minimality and without López–Escobar; that composition for the expansion domains,
from the back-and-forth form of condition 3 (`README.md`, the reduction to expansion domains and
Layer 6), is not elaborated.  The compiled application is for full presentations with scattered
tails (`densitySentence_isThinOnNatModels_of_scatteredTails`, through
`isThinOn_of_countable_bfClasses`). The working thinness route, from countable truth sides, is kept;
the Gδ/Polish results stay optional; an improvement is described as reduced dependencies, not as a
smaller trusted kernel. Milestone A does not depend on this interface.

**Scatteredness and minimality.** Cocountable concentration in one back-and-forth class at every
level is minimality, and it is more than thinness needs. Countably many back-and-forth classes at
every countable level already exclude a perfect antichain (scatteredness), by the same uniform
separation: a perfect antichain is separated at one level, at which only countably many classes
occur. One common class on a cocountable set at every level is a further assertion. The
full-presentation route (`README.md`, "Reduction to full presentations") gives the weaker hypothesis
from countably many level observations, and the stronger one only under a common starting
observation on every high presentation; its scatteredness composition is
`densitySentence_isThinOnNatModels_of_scatteredTails` (`MainTheorem/Assembly`), through
`isThinOnNatModels_of_countable_bfClasses` (`MainTheorem/Scatteredness`; `README.md`, Layer 6;
`IMPLEMENTATION.md`, "The full-presentation route"). The working thinness route, from countable
truth sides, uses the stronger form, which the expansion domains provide.

**Upstream ingredients of the scatteredness composition** (`README.md`, Layer 6), each with its
compiled use in this repository.  From InfinitaryLogic, available at the pin (signatures
checked): `exists_uniform_bfSeparation` (`Descriptive/BFSeparation`), applied in
`exists_forall_not_codeBFEquiv_of_isClosed` and through it in `isThinOn_of_countable_bfClasses`;
`bfEquivSetoid` (`ModelTheory/MorleyCounting`), in `bfEquivSetoid_eq_comap` and
`isThinOnNatModels_of_countable_bfClasses`, and in `MainTheorem/Assembly` in
`FullPresentations.HasScatteredTails`, `HasScatteredTails.countable_quotient`, and
`HasScatteredTails.of_countable_quotient`; `Perfect.mk_eq_continuum`
(`Descriptive/PerfectAntichain`), in `not_countable_of_perfect`; and
`HasCantorAntichainOn.hasPerfectAntichainOn` (`Descriptive/PerfectAntichain`), used only by the
example of `MainTheorem/Examples` showing that countably many back-and-forth classes are needed,
not by the composition.  From Mathlib: `Set.offDiag`, in `analyticSet_offDiag` and
`offDiag_noniso`; and `Setoid.comapQuotientEquiv`, in `isThinOn_of_countable_bfClasses`.  The
statements of `VaughtConjecture.MainTheorem.Scatteredness`, all generic, belong upstream; their
destinations are recorded in `IMPLEMENTATION.md`, "Placement record".

## Milestone B — top-free chart homogeneity and its consequences

Setting: a stage `λ = λ_ξ`, the stage chart language at `λ` (relational), and a countable
nonempty top-free realization at `λ` satisfying exact consistency, covering, and finite-cut
receiving, read as a structure `M` in that language.  Core results used: the finite semantic
kernel (layer 1), realizations, the chart language, and the hull operations (layer 2), finite-cut
receiving, and the top-free witnesses (`README.md`, the section after layer 3).  The top-free
witnesses satisfy the setting by steps 3–6 of their construction.  For the rigid-core comparison
of layer 4 (`README.md`, Layer 4, "Terminal classification by exact ages"), the analogues of B2 and
B3.1–B3.2, B3.4 are stated in the language naming the supplied finite core by constants, from the
exact receiving over roots containing the core (not from top-freeness); the rank bound B3.3 needs
a relational language, so for it the core is named by one unary relation per core point.

**Dependency chain** (deliberately short):

1. **exact top-free receiving**: over any actual root, a chart of the prescribed type extending
   the root's chart is realized over the literal root.  To be derived from finite-cut receiving
   with a cutoff above the finitely many labels of the prescribed chart; this uses top-freeness
   (agreement below such a cutoff is equality when no label is top);
2. **chart homogeneity** (B2);
3. **orbit formulas** (B3.1);
4. **atomicity** (B3.2) and the **Scott bound** (B3.3);
5. **primeness** (B3.4).

The development proves the finite-chart statements of this chain: exact top-free receiving, chart
homogeneity, the local automorphism property, and the orbit formulas: the two interfaces of
`IMPLEMENTATION.md`, "Applications of library theorems".  Everything after them is an application of
a library theorem, never reproved here (those of InfinitaryLogic compiled on abstract hypotheses in
`SuggestedCompanions.lean`, section B; those of ComputableModelTheory recorded there as targets;
none yet instantiated to the top-free witnesses): "a definable orbit isolates its type", atomicity,
and "countable atomic implies prime" from ComputableModelTheory (at the pin), the last with targets
of arbitrary cardinality and carriers in arbitrary universes; the orbit-formula threshold, the
internal rank bound, and the preservation of infinitary formulas by maps agreeing locally with
automorphisms from InfinitaryLogic (`exists_finite_orbit_threshold`,
`orbitRank_lt_omega0_of_orbitFormula`, `internalScottRank_le_omega0_of_orbitFormulas`,
`BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms`,
`BoundedFormulaω.realize_comp_append_of_localAutomorphisms`), available at our pinned dependency
`def5cc0` (signatures checked).

### B1. Joint embedding and amalgamation of top-free charts (in the core)

This target is step 2 of the construction of the top-free witnesses: `README.md`, section "The
top-free witnesses: the finite age and its classical limit", and `IMPLEMENTATION.md`, "The
top-free witnesses: milestone order and acceptance", which carry its statement (with the literal
commuting square), its proof from the plain form of the coatom extension property and capping,
its special cases, and its non-claims (not strong amalgamation; nothing about charts carrying top
labels).  After the definitional expansion by the hull operations (`README.md`, Layer 2), it is
the amalgamation property of Mathlib's `FirstOrder.Language.Amalgamation` for the age of
top-free charts.  The sketch properties `ChartAmalgamation` and `ChartJointEmbedding` and the
lemma `chartJointEmbedding_of_chartAmalgamation` are in `Suggested.lean`.

### B2. Chart homogeneity and local automorphisms

**Statement.**  (Homogeneity) if `t` and `t'` are actual charts of the same type in `M`, some
automorphism `e` of `M` satisfies `e ∘ t = t'`.  (Local automorphisms) every self-embedding `f`
of `M` agrees with an automorphism on each finite tuple `a`: some automorphism `e` has
`e ∘ a = f ∘ a`.  Consequently every self-embedding preserves every `L_{ω₁,ω}` formula in finitely
many free variables: `M ⊨ φ(a) ↔ M ⊨ φ(f ∘ a)` for every finite tuple `a`.

**Hypotheses.**  The setting above (countability is used by the back-and-forth construction, which
is construction-specific).  The development proves homogeneity and the local agreement property (the
second interface).  Local agreement follows from literal recovery, covering, and homogeneity: cover
`a` by an actual chart `u` of type `p` with `u ∘ ι = a`; `f ∘ u` satisfies `P_p`, so by literal
recovery it is an actual chart of type `p`; homogeneity gives an automorphism `e` with `e ∘ u = f ∘
u`, hence `e ∘ a = f ∘ a`.  Only the preservation of the chart relations by `f` is used, and the
automorphisms are those of the `L_λ`-structure.  Sketch: `AgreesLocally` and `agreesLocally_of_hom`
(proved, for any map preserving the chart relations).  The consequence is an application of
InfinitaryLogic's `BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms` (and, with finitely
many parameters, `BoundedFormulaω.realize_comp_append_of_localAutomorphisms`), available at our
pinned dependency `def5cc0` (signatures checked).  Its hypotheses: any language, no relationality,
countability, infinitude, or nonemptiness, and injectivity of the map a consequence of its
hypothesis.  It is not reproved here.  Sketch: `realize_iff_realize_comp_of_agreesLocally` and
`realize_comp_append_iff_of_agreesLocally` (proved, one-line applications).

**Upstream ingredients.**  `PotentialIso.ofExtensionFamily` (`Karp/PotentialIso`) for the family
"both tuples sit at the same positions of actual charts of the same type" (arbitrary tuples, so
repeated coordinates are allowed), `PotentialIso.family_bfEquiv`, and
`exists_automorphism_of_bfEquiv_all` (`Scott/OrbitRank`).  For a top-free witness, homogeneity is
also immediate from ultrahomogeneity (`IsFraisseLimit`), the two actual charts spanning finite
substructures of the definitional expansion (`README.md`, Layer 2, items 3–5).  Orbit formulas and
the rank bounds stay in the relational stage chart language `L_λ`.  Chart homogeneity in `L_λ`
follows from ultrahomogeneity of the `L^h_λ`-structure `M`: the points of two actual occurrences of
one type span substructures isomorphic to the finite structure of that type (step 4 of the top-free
witnesses, by the factorization of tuples), the isomorphism between them extends to an automorphism
of `M`, and every automorphism of an `L^h_λ`-structure is an automorphism of its `L_λ`-reduct.  Only
this direction is used.  The converse holds for a realization with its definitional expansion
(`HULL_ALGEBRA.md`, §5), and for `M` once the reconstruction roundtrip (`SEMANTIC_CONTRACT.md`, item
11) identifies its operations with the definable hull operations of the reconstructed realization;
it is not used.

**Instantiation.**  The top-free witness at block `ξ`, as a structure in the stage chart
language at `λ_ξ`.

**Special cases.**  The empty tuple (the identity automorphism); tuples with repeated
coordinates; `f` the identity; a two-point tuple whose hull is large; charts of different sizes
containing the same tuple.

**Non-claims.**  No proper (non-surjective) self-embedding is constructed or asserted to exist.
Nothing about realizations with top labels, about embeddings between different realizations, or
about maps that are embeddings only for the base reduct.

### B3. Orbit theory in the full stage chart language

These targets concern the **full stage chart language**; none transfers automatically to the
base reduct.  The development proves the orbit formulas; the generic theorems are quoted.

1. **Orbit formulas.**  For a finite tuple `a` in `M`, choose an actual containing chart of type
   `p`.  Existentially quantify its coordinates, assert its chart relation, and identify the free
   tuple with its selected coordinates:
   `θ_a(x̄) := ∃ z̄, P_p(z̄) ∧ ⋀_i x_i = z_{ι(i)}`.
   Prove that this first-order formula defines the automorphism orbit of `a`, using chart
   homogeneity (B2).  Repeated coordinates and the empty tuple are permitted.  Hypotheses: exact
   consistency, covering, finite-cut receiving, and top-freeness (countability for B2).  Sketch:
   the property `OrbitDefinedBy`, the formula `chartOrbitFormula`, and
   `orbitDefinedBy_chartOrbitFormula` (proved, from literal recovery of the chart relations,
   `RecoversRelations`, and chart homogeneity).
2. **Isolation and atomicity** (generic).  A definable automorphism orbit isolates the tuple's
   complete type over the structure's own complete first-order theory: universal implications `∀ x̄,
   θ_a → ψ` transfer to arbitrary models of that theory, and `θ_a` picks out a singleton in the
   space of complete types.  Uniqueness within the one model is not enough.  This gives atomicity
   without strengthening the hypotheses on the realization.  Sketch:
   `typesWith_eq_singleton_of_orbitDefinedBy` (target), `TypesIsolated`,
   `typesIsolated_of_orbitDefinedBy` (proved from the target
   `typesWith_eq_singleton_of_orbitDefinedBy`).  Ingredients: Mathlib's `Theory.CompleteType`,
   `Theory.typeOf`, `Theory.typesWith`, `Formula.equivSentence`, `completeTheory`
   (`ModelTheory/Types`, `ModelTheory/Semantics`).  At the pin (`0e9935b`, signatures checked), from
   ComputableModelTheory: `IsolatesTuple` and `IsAtomic`,
   `isolatesTuple_of_orbit_formula` (under `[Nonempty M]`; orbit formulas of `L` without constants
   naming the tuple), `isAtomic_of_orbit_formulas`, and `IsolatesTuple.typesWith_eq_singleton`
   (under `[Nonempty M] [M ⊨ T]`); the sketch target is the composite of
   `isolatesTuple_of_orbit_formula` and `IsolatesTuple.typesWith_eq_singleton`, and `TypesIsolated`
   is `IsAtomic` over the complete theory, stated through the type space. InfinitaryLogic's
   `isolatingFormula` (`ModelTheory/TypeIsolation`) is a different notion: an `L_{ω₁,ω}` formula
   isolating a realized infinitary type among the types realized in one structure.
3. **Scott bound** (an application).  From the orbit formulas of B3.1, InfinitaryLogic's
   `exists_finite_orbit_threshold` and `orbitRank_lt_omega0_of_orbitFormula` give each tuple a
   finite threshold, and `internalScottRank_le_omega0_of_orbitFormulas` gives `internalScottRank ≤
   ω` in the library's convention, the supremum over all tuples of the orbit rank plus one, `⨆ a,
   orbitRank a + 1` (so finite but unbounded orbit ranks give exactly `ω`). These are available at
   our pinned dependency `def5cc0` (signatures checked).  They hold under `[L.IsRelational]` and
   without countability, nonemptiness, or infinitude of `M`; they are not reproved here.  Sketch:
   `exists_finite_threshold_of_orbitDefinedBy`, `orbitRank_lt_omega0_of_orbitDefinedBy`, and
   `internalScottRank_le_omega0_of_orbitDefinedBy` (proved, one-line applications).  The stage
   chart language is relational, so they apply to `M` in it, not in the definitional expansion.  The
   conclusion is `≤ ω`, not `< ω`, and not an equality.  The rank comparison of the Scott process
   (InfinitaryLogic, on the same terms) then gives, under `[L.IsRelational] [Infinite M]`,
   stabilization at `ω` of the process of length `δ` when `ω + 1 < δ`, and rank at most `ω` when the
   process terminates; the rank of the process is not identified with the internal rank.
4. **Primeness** (generic, a separate theorem).  A countable structure all of whose types are
   isolated embeds elementarily into every model of its complete theory: enumerate only the
   source, extend finite tuples preserving every first-order formula, and take the union.  The
   target is any model of the complete theory, in an arbitrary universe, with no receiving or
   countability assumption.  Sketch: `nonempty_elementaryEmbedding_of_typesIsolated` (target).
   Ingredients: Mathlib's `ElementaryEmbedding` (`ModelTheory/ElementaryMaps`).  At the pin
   (`0e9935b`, signatures checked), from ComputableModelTheory:
   `exists_elementaryEmbedding_of_countable_atomic`,
   under `[Countable M] [Nonempty M] [N ⊨ L.completeTheory M]`, with separate universes,
   function symbols allowed, and no countability of the language or of `N`; the sketch target is
   its composite with the identification of `TypesIsolated` with `IsAtomic`.

**Instantiation.**  For the top-free witness at block `ξ`, in the stage chart language at `λ_ξ`:
its orbits are defined by the existential formulas `θ_a`; it is atomic; its internal Scott rank is
at most `ω`; it is a prime model of its complete first-order theory in that language.

**Special cases.**  The empty tuple (its orbit formula is `∃ z̄, P_p(z̄)` for the chosen chart);
repeated coordinates (`ι` not injective); a tuple lying in charts of different sizes (the orbit
formula does not depend on the chart chosen, up to equivalence in `M`); universe independence
(source in `Type w`, target in `Type w'` for primeness; `Ordinal.{w}` for the internal Scott
rank).

**Non-claims.**  Full stage chart language only: nothing about the base reduct, whose Scott
analysis is the subject of A1.  No rank equality, and no identification of the internal Scott rank
with the block index, the expansion height, or a Scott rank of the base class.  Primeness is for
the complete first-order theory, not for an infinitary theory.  Uniqueness of countable atomic
models is a standard consequence and is not required.

**Completion criterion (B).**  B2 and B3 are proved for every countable nonempty top-free
realization satisfying exact consistency, covering, and finite-cut receiving, each under exactly
its stated hypotheses, with the generic isolation, atomicity, primeness, rank, and preservation
theorems quoted from the two libraries (whose modules import no module of this repository).  B1
is part of the core and is not a condition of this milestone.

### B4. Scott sentences of the top-free witness from its orbit formulas (existence only)

Two statements are kept apart.  The **generic existence** of *a* Scott sentence from orbit formulas
is Montalbán's theorem (InfinitaryLogic, available at the pin `def5cc0`, signatures checked;
`README.md`, Layer 0): for a countable structure in a relational language with countably many
relation symbols, and a family of orbit formulas indexed by all tuples, the sentence
`montalbanSentence` characterizes the structure among countable structures in its carrier universe
(`montalbanSentence_characterizes`); if `1 ≤ α` and every formula of the family is in `IsSigmaIn α`,
the sentence is in `IsPiIn (α + 1)` (`isPiIn_montalbanSentence`, with no orbit property), so orbit
formulas in `IsSigmaIn α` give a Scott sentence in `IsPiIn (α + 1)`
(`exists_isPiIn_scottSentence_of_sigmaIn_orbits`; pointed:
`exists_isPiIn_pointed_of_sigmaIn_orbits`), and level zero is a separate result (orbit formulas in
`IsSigmaIn 0` give a Scott sentence in `IsPiIn 2`,
`exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits`).  The displayed sentence includes, for
each tuple, its atomic diagram `D_a` (`atomicDiagram`), a countable conjunction of atoms and negated
atoms.  The **particular exact-age sentences** of `README.md`, Layer 4, and their literal complexity
are construction-specific statements still to be proved; this item says nothing about them.

**Statement** (a statement still to be proved; the general theorem is available at the pin,
signatures checked; `IMPLEMENTATION.md`, "Dependency pins").  Let `M` be the top-free witness at a
block `ξ`, read in the relational stage chart language at `λ_ξ`, and suppose that language has
countably many relation symbols.  Assume B3.1: each orbit formula `θ_a` defines the automorphism
orbit of `a`.  Suppose these formulas, read as infinitary formulas, are in `IsSigmaIn 1` (to be
proved, by the signed traversal of the existential formula `∃ z̄, P_p(z̄) ∧ ⋀_i x_i = z_{ι(i)}`,
whose conjunction is finite).  Then the general theorem at `α = 1`
(`exists_isPiIn_scottSentence_of_sigmaIn_orbits`) gives a sentence in `IsPiIn (1 + 1)`, that is
`IsPiIn 2`, that characterizes `M` among the countable structures of that language in its carrier
universe: a `Π^in_2` Scott sentence of `M`.  For a rigid-core terminal model (`README.md`, Layer 4),
given orbit formulas over the named core in `IsSigmaIn 1` (the analogue of B3.1 in the language
naming the core, to be proved), the pointed form gives a `Π^in_2` formula whose free variables are
the core, and existentially quantifying the core gives a `Σ^in_3` Scott sentence.

**Non-claims.**  B4 is not a condition of the completion criterion (B).  Existence only: these
sentences need not be the exact-age sentences, and no normal form or quantifier-rank bound follows
from membership in a signed class.  Full stage chart language only: nothing about the base reduct
or about the models of `Φ`, whose Scott ranks are unbounded (`README.md`, "Standard definitions").

## Milestone C — a geometric obstruction

**Statement.**  Let a realization on a carrier `M` of any cardinality satisfy exact consistency
and covering, read as a structure in its full stage chart language.  Every set of **absolute
indiscernibles** (a set `S ⊆ M` every permutation of which extends to an automorphism of `M`) has
at most two elements.

**Proof.**  Let `x`, `y`, `z` be three distinct points of `S`.  Their hull `H` is a nonsingleton
finite closed set, and its two extreme points lie among `x`, `y`, `z` (an extreme point of the
hull of a set lies in the set, `HULL_ALGEBRA.md`, §3); so one of the three is not an extreme
point of `H` and another is.  An automorphism carries actual charts to actual charts of the same
type, hence the hull of a finite set to the hull of its image and the two intrinsic extreme
points of that hull to those of the image hull.  The transposition of a non-extreme and an
extreme point of `H`, fixing the third point, would extend to an automorphism mapping `H` onto
itself and an extreme point to a non-extreme one, which is impossible.  Sketch:
`false_of_swap_extreme` (proved, for an abstract extreme-point map commuting with a set of
self-maps).

**Hypotheses.**  Exact consistency and covering only: neither receiving nor top-freeness, nor
modelhood or countability.  The canonical finite hulls and their generation by two extreme points
come from layer 2 (`README.md`, Layer 2, item 1) and the geometry from layer 1.

**Status.**  A statement still to be proved here; the argument is the one above.

**Import guard.**  The module proving this theorem and the modules it imports must not include any
module of the finite extension constructions or receiving (layer 3), of model existence (the
classical limit of the top-free witnesses, or the retained chain construction), of structural
continuation (layer 4), or of the expansion domains (layer 5).  The guard is on the import closure,
not only on the direct imports.  The check reads Lean's own record of the import closure, not the
source text, so every form of import (`public`, `meta`, `import all`, the root module
`VaughtConjecture`, indented lines) is covered.  The generic theorems of B3.2 and B3.4 are quoted
from ComputableModelTheory (at the pin), whose modules import Mathlib only, so they need no guard
here.  The addition to `scripts/check.sh` below is a proposal, not yet part of `scripts/`: the
module names are to be fixed when these modules exist.  It consists of a driver body
`scripts/ImportGuard.lean`, in the pattern of `scripts/AxiomAudit.lean`, run through `lake env
lean`:

```lean
/-
Import guard body for the `VaughtConjecture` library.

`scripts/check.sh` generates, for each guarded module, a driver that imports that module and
appends the command below.  It fails if the import closure of the module contains a module whose
name has one of the forbidden prefixes (as a sequence of name components).
-/
import Lean

open Lean in
run_cmd do
  let some root ← IO.getEnv "IMPORT_GUARD_MODULE" | throwError "IMPORT_GUARD_MODULE is not set"
  let some pre ← IO.getEnv "IMPORT_GUARD_FORBIDDEN" | throwError "IMPORT_GUARD_FORBIDDEN is not set"
  let root := root.toName
  let forbidden := ((pre.splitOn " ").filter (· ≠ "")).map String.toName
  let closure := (← getEnv).allImportedModuleNames
  unless closure.contains root do
    throwError "import guard: the driver does not import {root}"
  let bad := closure.filter fun m => m != root && forbidden.any (·.isPrefixOf m)
  unless bad.isEmpty do
    for m in bad do logError m!"{root} imports {m}, which its import closure must avoid"
    throwError "import guard failed for {root} ({bad.size} forbidden module(s))"
  logInfo m!"import guard: the import closure of {root} ({closure.size} modules) avoids {forbidden}"
```

and, in `scripts/check.sh` after the build:

```sh
echo "== import guards"
# import_guard MODULE PREFIX...: fail if the import closure of the built MODULE contains a module
# named PREFIX or PREFIX.<components>, for one of the PREFIXes.
import_guard() {
  local root=$1; shift
  local driver=".lake/import-guard/$root.lean"
  mkdir -p .lake/import-guard
  { echo "import $root"; echo "import Lean"
    sed -n '/^open Lean in/,$p' scripts/ImportGuard.lean; } > "$driver"
  IMPORT_GUARD_MODULE=$root IMPORT_GUARD_FORBIDDEN="$*" lake env lean "$driver"
}
# Placeholders: <HullObstruction> is the module of milestone C; the prefixes name the modules of
# model existence (the classical limit and the chain construction), layer 3, 4, and 5.
import_guard VaughtConjecture.<HullObstruction> \
  VaughtConjecture.<ClassicalLimit> VaughtConjecture.<ChainConstruction> \
  VaughtConjecture.<Receiving> \
  VaughtConjecture.<StructuralContinuation> VaughtConjecture.<Domains>
```

A prefix matches whole name components: `VaughtConjecture.Receiving` excludes
`VaughtConjecture.Receiving` and `VaughtConjecture.Receiving.Core`, not
`VaughtConjecture.ReceivingData`.

**Upstream ingredients.**  Mathlib's `Equiv.swap`; the finite hulls and their extreme points
from layer 2.  No cardinality material (`TwoGeneratorCardinality`) is used.

**Instantiation.**  Every realization with exact consistency and covering: models of `Φ` read in
the stage language at `ω`, their expansions at every stage, the top-free realizations, and the
structural stable candidate before its modelhood is proved.  In particular no model of `Φ` has
three points all of whose permutations are induced by automorphisms.

**Special cases.**  A set of exactly three points (the threshold of the argument); sets of at most
two points, about which nothing is claimed; three points whose hull has more than three points;
uncountable carriers; realizations that are not models.

**Non-claims.**  No claim of sharpness (that some realization has two absolute indiscernibles),
of the same bound in a reduct language (the base reduct, or any language without the chart
relations of the stage), or that hull closure is full definable closure.  It does not exclude
infinite sets of order-indiscernibles, infinite orbits, or weaker homogeneity (for instance, sets
on which the automorphisms act transitively), and it says nothing about the size of automorphism
groups.

**Completion criterion (C).**  The generic theorem is proved in a module with no construction
imports; the preservation of the two extreme points of a finite hull by automorphisms is proved
for realizations from exact consistency and covering; the instance for an arbitrary realization
is stated and proved; and the import guard is in place and passes.

## Further companion results

These are statements still to be proved.  None is an input to the main theorem.

* **Greatest refinements.**  The **greatest refinement** of a model is its expansion to the
  largest stage `λ_ξ` to which it expands (the set of such `ξ` is an initial segment closed under
  limits by limit continuity, so it has a largest element unless it is all of `ω₁`; the expansion
  is unique by expansion uniqueness); its **height** is that `ξ`, or `ω₁` for a class in the
  persistent core.  Targets: the naturality of greatest refinements under isomorphism, and their
  relationship to the expansion domains (a class lies in `D_ξ` exactly when its height is at
  least `ξ`).  The count of the main theorem does not use them.
* **Terminal refinement** (every item a conditional target, to be proved; none is an input to the
  counting theorem).  Hypotheses, all explicit: conditions 1–4 of the expansion-domain reduction
  (`README.md`), which are hypotheses of the count, not its conclusions; Scott isolation, a Scott
  sentence `σ_q` for each class `q`, of countable quantifier rank and true in `q` only
  (`scottSentence_characterizes`); and, for 3 only, expansion uniqueness and the countable family of
  terminal conditions of layer 4.  No conclusion of the count (the countable complements `Q \ D_η`,
  the bound `|Q| ≤ ℵ₁`, the uncountability of `Q`) is used.  Under these hypotheses, the targets, in
  order:
  1. **Eventual departure** (a theorem to be proved).  *Assume that the expansion domains `D_η`
     satisfy conditions 1–4, in particular the agreement on `D_β`: any two classes in `D_β` satisfy
     the same sentences of quantifier rank at most `β`; that every class `q` has a Scott sentence
     `σ_q` of countable quantifier rank (true in `q` and in no other class); and that the successor
     losses are cofinally nonempty: for every `γ < ω₁` there is `β ≥ γ` with `D_β \ D_{β+1} ≠ ∅`.
     Then no class lies in every `D_η`.*  Proof: if `q` lay in every `D_η`, choose `β` at least the
     quantifier rank of `σ_q` with some `p ∈ D_β \ D_{β+1}`; both `p` and `q` lie in `D_β`, so
     agreement on `D_β` makes `p` satisfy `σ_q`, hence `p = q`; but `q ∈ D_{β+1}` and `p ∉ D_{β+1}`.
     Of these hypotheses the proof uses only the agreement on every `D_β`, the Scott sentences, and
     the cofinally nonempty losses; the last are redundant under conditions 1–4, since condition 4
     makes every successor loss nonempty, and are listed because the same argument applies to any
     family of domains with that agreement and cofinally nonempty successor losses (on the
     least-level filtration of the full-presentation route departure is immediate, the tails of a
     total rank having empty intersection, `biInter_rankTail_eq_empty`).  **Corollary** (conditional
     on the same hypotheses): under condition 4 the persistent core `⋂_{η<ω₁} D_η` is empty.
     **Control:** the argument uses isolation of each class by one sentence; pairwise separation
     (for `p ≠ q`, some sentence true in one and false in the other) does not suffice for it,
     because the rank of a sentence separating `q` from `p` depends on `p` while the class lost at
     `β` varies with `β`, so no level need lie above the rank of the sentence separating `q` from
     the class lost there.  For instance, on `Q = ω₁ ∪ {q}` with `D_β = {q} ∪ [β, ω₁)` and, for each
     `α < ω₁`, a sentence of rank `α + 1` true at `α` only, the agreement and the cofinally
     nonempty losses hold and distinct points are separated, yet `q` lies in every `D_β`.

     **Cofinally nonempty successor losses** (a separate lemma, to be proved).  *Let `D_η ⊆ Q`, for
     `η < ω₁`, satisfy `D_0 = Q`, `D_ζ ⊆ D_ξ` for `ξ ≤ ζ`, continuity `D_δ = ⋂_{ξ<δ} D_ξ` at nonzero
     countable limits `δ`, countable complements `Q \ D_η` for every `η < ω₁` (from countable
     successor losses, by `compl_countable_of_loss`), and a countable persistent core
     `⋂_{η<ω₁} D_η`.  If `Q` is uncountable, the successor losses are cofinally nonempty.*  Proof:
     if every loss at or above `γ` were empty, then `D_η = D_γ` for every `η ≥ γ` (successors by
     the empty losses, limits by continuity), so the persistent core would be `D_γ`, and
     `Q = (Q \ D_γ) ∪ D_γ` would be countable.  The hypothesis on the core is needed: the constant
     family `D_η = Q` on an uncountable `Q` has no losses.  The core is empty for the tails
     `{q : η ≤ r(q)}` of a rank `r` below `ω₁` (`biInter_rankTail_eq_empty`), in particular for the
     least-level filtration, and for the tails of a rank with countable fibres the equivalence with
     uncountability is InfinitaryLogic's `rankTail_cofinal_losses_iff` (at the pin, signatures
     checked).  Conversely, cofinally nonempty successor losses of decreasing domains are pairwise
     disjoint and make `Q` uncountable with no further hypothesis (`aleph_one_le_mk_of_cofinal`,
     compiled in this repository (theorem named)).  On the expansion-domain route the lemma is not
     needed: condition 4 gives every successor loss nonempty;
  2. **the last admitted stage** (a definition conditional on 1): for a class `q` that leaves the
     expansion domains, the least `ξ` with `q ∉ D_ξ` is a successor `ζ + 1` (`D_0 = Q`, and limit
     continuity excludes a limit), and `λ_ζ` is then called the last admitted stage of `q`; `q` lies
     in the loss `D_ζ \ D_{ζ+1}`;
  3. **the terminal expansion** (to be proved, given 2): the expansion of a model in `q` to its last
     admitted stage is unique by expansion uniqueness and terminal, and is covered by the countable
     family of terminal conditions of layer 4 (rigid-core type, positive eventual top grade, hollow
     growth).

  None of these is proved, and no class is asserted to have a last admitted stage or a terminal
  expansion before 1 is proved.  If 1–3 are proved, the greatest refinement above (itself a target)
  is the terminal expansion, and no class has height `ω₁`.  Terminal refinement is not a
  prerequisite of the counting theorem, and its eventual departure is not downstream of the count:
  it uses hypotheses of the count (the agreement of condition 3 and the nonempty losses of condition
  4, with Scott isolation), not its conclusions.  The full-presentation route (`README.md`, "The
  persistent core") may therefore take eventual departure from here without circularity; it then
  depends on conditions 3 and 4 of the expansion-domain route, not on its count, and states that
  dependence.  Departure proves neither terminal fullness (the fullness of the terminal expansion
  for its terminal exact age, the first special statement there, which is not part of terminal
  refinement) nor full-presentation coverage; a full-presentation proof that does not depend on
  conditions 3 and 4 must cover every class, a persistent class included, by its own argument.
* **Quantitative reconstruction** (prospective: a companion pathway of bounded checkpoints, not a
  prerequisite of the main theorem by either route; it is used by neither route).  It asks for
  explicit base-language syntax for the expansions recovered by higher-stage reconstruction
  (`README.md`, Layer 4, outputs 1–5), with bounds on its quantifier rank.  Each row of the table
  below is a separate statement to be proved: **to construct the specified formula and prove that
  its quantifier rank is at most the displayed ordinal**.  The rank is that of the particular
  constructed syntax, in the library's convention (`BoundedFormulaω.qrank`, InfinitaryLogic, at the
  pin, signatures checked); membership in a signed class (`IsSigmaIn`, `IsPiIn`) and membership in a
  normal form (`IsSigmaInNF`, `IsPiInNF`) are separate claims, not asserted here.  A **contract** of
  the pathway is one of these statements, or the transfer bound below, with its hypotheses fixed
  with it.  Here `η` is a countable block index and the stage is `λ_η`; a **supplied expanded
  model** is a countable base model together with its expansion to `λ_η`, of a coreless exact age
  (top-free, residual, or hollow; `README.md`, Layer 4), and a **supplied `k`-coordinate core
  model** is a countable base model together with its expansion to `λ_η`, of an exact age pointed
  at a rigid core of `k` points, named by `k` coordinates.

  | Statement (the formula to construct) | Bound (quantifier rank ≤) |
  | --- | ---: |
  | Definitions of the chart predicates at `λ_η` in the base language (pointed: formulas whose free variables are the chart's points) | `ω·η` |
  | A sentence defining the expansion to `λ_η`, relative to base models | `ω·(η+1)` |
  | An absolute Scott sentence for a supplied expanded model (of an exact age, top-free in particular) | `ω·(η+2)` |
  | An absolute Scott sentence for a supplied `k`-coordinate core model | `ω·(η+2)+k` |

  The second row is the syntactic transcription of "admits an expansion to `λ_η`" that A1 does not
  claim: the sentence `δ_η` of A1 is assembled from Scott sentences of classes and carries no rank
  bound.  The **domain guard** is the theorem that the sentence of the second row holds in a base
  model exactly when that model admits a model expansion to `λ_η`.  **Successor substitution**
  defines the chart predicates at `λ_{η+1}` by substituting the definitions at `λ_η` into formulas
  recovering the labels of the next block (formulas of quantifier rank at most `ω` in the chart
  predicates at `λ_η`, a bound that is part of the first row's statement), and **cofinal-limit
  conjunction** defines them at a limit block by a conjunction along a cofinal sequence of lower
  blocks.

  **The central contract** (a theorem to be proved).  Let `σ` be a supplied expanded Scott sentence,
  a sentence of the stage chart language at `λ_η` of quantifier rank at most `ρ` (for the last row,
  the formula whose free variables are the `k` core coordinates).  Its **relative transfer** is the
  base-language sentence (for the last row, formula) obtained by substituting the definitions of the
  first row for the chart predicates of `σ` and conjoining the sentence of the second row.  Then
  **qrank(relative transfer) ≤ max{ω·(η+1), ω·η + ρ}**: by induction on `σ`, substituting
  definitions of rank at most `ω·η` is to add at most `ω·η`, on the left.  The table follows by
  supplying the syntax bounds for each row: for the last two rows, a bound `ρ` on the expanded Scott
  sentence, computed for the constructed syntax (if the optional normal form `IsPiInNF 2` of the
  exact-age sentences of Layer 4 is constructed, `ρ ≤ ω·2` for the normalized formula by
  `IsPiInNF.qrank_le`, and the transfer is then of the normalized formula, not of the original
  syntax tree), together with the calculations below: the base-model conjunct for both rows, and the
  `+k` calculation for the last.

  1. **The `+k` row needs its own syntactic calculation.**  Forgetting parameters (InfinitaryLogic,
     `Scott/ForgetParameters`, at the pin, signatures checked:
     `exists_isSigmaIn_three_scottSentence_of_sigmaIn_one_orbits_over`, the generic existence of a
     `Σ^in_3` Scott sentence from `Σ^in_1` orbits over parameters, through the existential closure
     `existsTuple` and `existsTuple_isScott`) supplies the semantic mechanism only.  The rank
     statement to prove is that existentially closing the `k` named coordinates adds at most `k` to
     the bound.  One existential quantifier adds one to the rank (`qrank_existsLastVar`, at the pin,
     signatures checked); the statement for the closure `existsTuple k` is to be proved.  Membership
     in `Σ^in_3` gives no rank bound, and the normal form `IsSigmaInNF 3` gives only `ω·3`
     (`IsSigmaInNF.qrank_le`).
  2. **The base-model conjunct.**  The relative transfer is to isolate the supplied model only among
     base models.  The passage from relative to absolute isolation must explicitly bound the
     base-model conjunct: the base-theory conjunct (the density sentence `Φ`) and the
     structure/realization correspondence (Layer 2: a base-language structure satisfies `Φ` exactly
     when, read as a realization, it is a model) close that step.  The rank of the base-theory
     conjunct is part of the statement to be proved, not assumed below the displayed ordinal; the
     correspondence is the theorem that makes that conjunct suffice.

  **Qualifications.**  The absolute Scott contracts (the last two rows) carry the countability and
  fixed-carrier-universe qualifications of InfinitaryLogic's Scott theorems: they characterize the
  supplied model among the countable structures in its carrier universe, as
  `scottSentence_characterizes` (for a relational language with countably many relation symbols) and
  `existsTuple_isScott` do (at the pin, signatures checked), not among structures of every
  cardinality or in every universe (the characterization across universes is among the ingredients
  of A3 to be located or added upstream).

  **Non-claims** (the boundaries of the pathway):
  - Definitions do not provide expansion existence; the domain guard is a separate theorem.
  - Uniqueness does not provide defining formulas; successor substitution and cofinal-limit
    conjunction construct them.
  - Relative isolation is not an absolute Scott sentence; the base-theory conjunct and the
    structure/realization correspondence supply that final step.
  - These are syntax bounds, not optimal ranks and not height equalities (no identification with
    Scott heights, stabilization ordinals or internal Scott rank — cf. the rank-filtration item).
  - Global termination remains outside this pathway and outside the first endpoint (the main theorem
    by the expansion-domain route).
  - Every contract is to be proved here for this library's own definitions.

  **Recognition and base-reduct orbit ranks** (three further companion targets, prospective and
  explicitly unfinished; the hypotheses of each are fixed with its statement).  They are kept apart:
  1. **Domain recognition** (distinct from recognition of a model): membership in `D_η` is invariant
     under sufficiently high back-and-forth equivalence, that is, a countable base model
     back-and-forth equivalent on the empty tuple, at a level to be determined, to a model of a
     class in `D_η` lies in a class of `D_η`.  It is supported by the domain-defining sentence (the
     second row), with the level to be determined.  A pointed statement is required for the chart
     predicates (the first row), since they have free variables: tuples back-and-forth equivalent at
     a level to be determined, in models of classes of `D_η`, satisfy the same chart predicates at
     `λ_η`.
  2. **Recognition of a supplied model**: sufficiently high back-and-forth equivalence to the
     supplied model forces isomorphism.  It is supported by its Scott sentence (the last two rows);
     the level is the sentence's rank in the library's convention.  Back-and-forth equivalence at
     that level on the empty tuple carries the sentence across (`BFEquiv_implies_agreeQR`, for a
     relational language), and the sentence characterizes the supplied model among the countable
     structures in its carrier universe, in the form of `scottSentence_characterizes` (for a
     relational language with countably many relation symbols; both at the pin, signatures checked).
  3. **Base-reduct orbit-rank bounds**: bounds on the orbit ranks of tuples in the **base** reduct,
     not in the stage chart language of Layer 4 and of B3.  Before any bound is stated, the
     **parameter-free** orbit formulas (one for each tuple, with exactly the tuple's coordinates
     free and no parameters), the **pointed** formulas over the named core, if there is one (with
     the core as parameters, as in the library's `IsOrbitFormulaFamilyPointed`), and the rank
     convention (`orbitRank` and `internalScottRank`, the supremum `⨆ a, orbitRank a + 1`, as in the
     library, at the pin, signatures checked) are to be specified.  An unpointed Scott-sentence
     bound is not automatically a bound for every tuple's orbit: a bound on the rank of a Scott
     sentence of the base model is not, without a further argument, a bound on the orbit rank of
     each tuple.  The numerical bound `≤ ω` of B3.3 alone does not transfer: translating the
     stage-language orbit formulas into the base language and lifting base-reduct automorphisms
     along the same bijection must both be proved (uniqueness of the expansion supplies the
     transport argument for the lifting).

  **Completion criterion.**  Each row is a bounded checkpoint, complete when its formula is
  constructed for the concrete objects of the construction (the chart predicates at `λ_η`, the
  expansion domains, the supplied model) and its rank bound is proved, under exactly its stated
  hypotheses; the second row also needs the domain guard; the last two rows need the central
  contract and the base-model calculation (2), and the last row also the `+k` calculation (1).  The
  three targets have their own statements and are complete only when those are proved; no row is a
  condition of any other milestone.

  Related items: higher-stage reconstruction (`README.md`, Layer 4, outputs 1–5), whose expansions
  the first two rows define; Layer 4 and B4 (orbit formulas in the stage chart language; the generic
  existence of a Scott sentence is kept apart from the literal complexity of the exact-age
  sentences); terminal refinement (above), which uses Scott sentences of countable quantifier rank
  and no explicit bound on that rank; and the rank-filtration item (below), whose comparison these
  syntax bounds do not give.
* **Minimal unboundedness.**  `Φ` is minimally unbounded [Mon, Definition XII.4]: it is
  unbounded, but for every sentence `ψ` one of `Φ ∧ ψ` and `Φ ∧ ¬ψ` is bounded.  The second
  clause follows from the countable truth sides: one of `Φ ∧ ψ` and `Φ ∧ ¬ψ` has countably many
  countable models up to isomorphism, hence models of bounded Scott rank (countably many
  countable ordinals are bounded below `ω₁`).  Unboundedness is a separate statement: it follows
  from the main theorem, since a scattered sentence whose models have bounded Scott ranks has
  only countably many countable models [Mon, §XII.1]; it also needs `Φ` scattered, which follows
  from the absence of a perfect antichain by Silver's theorem on the Borel relations `≡_α`
  [Mon, §XII.1], a statement still to be proved here.  For a scattered sentence such as `Φ`,
  the countable truth sides and the second clause are equivalent; they differ only for sentences
  that are not scattered.  Here Scott rank is [Mon]'s parametrized Scott rank [Mon, Definition
  II.16].  By [Mon, Theorem XII.7] every counterexample `Θ` has a sentence `φ` with `Θ ∧ φ` a
  minimally unbounded counterexample; for `Φ` no strengthening is needed.
* **The agreement filtration and club agreement.**  The **agreement filtration** is canonical,
  defined from `Φ` through `T∞` alone: at a countable level `η`, `A_η` is the set of classes `q ∈ Q`
  in which every sentence of `T∞` of quantifier rank at most `η` is true.  The club agreement for
  expansion domains concerns this filtration, not Scott rank.  **Club agreement** (a statement to be
  proved here; argument sketched).  Hypotheses: `D_η` is a filtration of `Q` with `D_0 = Q`,
  continuity at nonzero countable limits, countable complements, and agreement of its classes on
  every sentence of quantifier rank at most `η` (the expansion domains, or the least-level
  filtration of the full-presentation route, `README.md`, "Reduction to full presentations"), and
  `Q` is uncountable.  Conclusion: `D_η ⊆ A_η` for every `η`, and `D_η = A_η` for every `η` in some
  closed unbounded set `C ⊆ ω₁`.  For the inclusion: a sentence of `T∞` of rank at most `η` is
  constant on the uncountable set `D_η` and fails on only countably many classes, so it holds on
  `D_η`.  For the club: `¬σ_q ∈ T∞` for the Scott sentence `σ_q` of each class; let `f(ξ)` be the
  supremum of the quantifier ranks of `σ_q` over the countably many `q ∉ D_ξ`, and let `C` be the
  nonzero limits `η` with `f(ξ) < η` for every `ξ < η`; for `η ∈ C` and `q ∉ D_η`, continuity gives
  `ξ < η` with `q ∉ D_ξ`, so `¬σ_q` has rank below `η` and fails in `q`, and `q ∉ A_η`.  The
  argument uses no Scott rank, and club agreement relates the agreement filtration to `D_η` only: it
  identifies neither with a filtration by Scott rank.
* **The rank filtration and its comparison** (prospective: a separate target, needing its own
  theorem).  The **rank filtration** is defined by lower bounds on Scott rank: at level `η`, `R_η`
  is the set of classes of Scott rank at least `η`, in a stated convention.  For a minimally
  unbounded sentence (unbounded, with the second clause above) there is a closed unbounded set
  `C ⊆ ω₁` such that, for `α ∈ C`, the models of Scott rank at least `α` form exactly one
  `≡_α`-class [Mon, Lemma XII.8].  This is stated in [Mon]'s convention: `≡_α` defined by moves of
  finite tuples [Mon, Definition II.32] and the parametrized Scott rank; its proof uses the
  sentences `ψ_{A,α}` defining the `≡_α`-class of a structure [Mon, Lemma XII.5].  **The
  rank-filtration comparison** (prospective; its hypotheses are part of its statement and are to be
  fixed with it): for `Φ`, with the conclusions of the main theorem and the passage between
  conventions below as hypotheses, a closed unbounded set of levels `η` on which `R_η` is compared
  with `D_η` (the expansion domains, or the least-level filtration of the full-presentation route,
  `README.md`, "Reduction to full presentations") and with `A_η`, the form of the comparison (an
  equality, or an inclusion in one direction) to be determined with the theorem.  Nothing is
  asserted about the relation between `R_η`, in [Mon]'s convention, and `A_η` or `D_η`, at any
  level, in either direction: neither club agreement nor any result stated here gives it (the
  one-sided comparison below is in InfinitaryLogic's conventions), and the results stated here do
  not identify expansion heights with Scott ranks.  The passage between [Mon]'s convention and the
  one-point `BFEquiv` of the main theorem is a statement still to be proved (`README.md`, "Standard
  definitions").  A supporting statement, recorded as a prospective lemma of InfinitaryLogic
  (`IMPLEMENTATION.md`, "The full-presentation route"): an analogue for `BlockBFEquiv` of [Mon,
  Lemma XII.6] (a chain of countable structures, each equivalent to the next at an increasing
  sequence of levels with a fixed offset, has a countable limit structure equivalent to each term at
  its level), by the same construction, with its offset to be determined.  It supports the
  rank-filtration comparison only through the passage between [Mon]'s convention and
  InfinitaryLogic's, which is still to be proved.

  **A one-sided rank comparison** (prospective: a statement to be proved, in InfinitaryLogic's
  conventions, not [Mon]'s).  The notions, as defined at the pin `def5cc0` (signatures checked), for
  any language `L` and a countable structure `M` (the theorems used below add their own instances,
  given with each; the base language is relational with countably many relation symbols): the
  **stabilization ordinal** (`Scott/Sentence`), the least level at which empty-tuple back-and-forth
  equivalence with `M` characterizes `M` up to isomorphism among the countable structures in its
  carrier universe,

  ```lean
  def StabilizesAt (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
    ∀ (N : Type w) [L.Structure N] [Countable N], BFEquiv0 (L := L) M N α ↔ Nonempty (M ≃[L] N)

  noncomputable def stabilizationOrdinal (M : Type w) [L.Structure M] [Countable M] :
      Ordinal.{0} :=
    sInf {α : Ordinal.{0} | StabilizesAt (L := L) M α}
  ```

  and the **Scott height** (`Scott/Height/Defs`), the least level from which back-and-forth
  equivalence of tuples of every length with tuples of `M` no longer refines,

  ```lean
  noncomputable def scottHeight (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
    sInf {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
      (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
      BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}
  ```

  Statement, for a level `η < ω₁`, with its hypotheses explicit.  (a) Any two classes of `D_η` are
  empty-tuple `BFEquiv η`, by condition 3 in its back-and-forth form (`README.md`).  Any two classes
  of `A_η` are empty-tuple `BFEquiv η` under the hypotheses of A2 (countable complements `Q \ D_η`,
  agreement on `D_η` at rank `η`, `Q` uncountable), which make `T∞` complete: the Scott formula at
  `η` of a countable model of one class has quantifier rank at most `η` (`scottFormula_qrank_le`,
  under `[Countable (Σ l, L.Relations l)]`, `[Countable M]`, and `η < ω₁`; no relationality) and
  holds in a model exactly when that model is `BFEquiv η` to it on the empty tuple
  (`realize_scottFormula_iff_BFEquiv`, under the same hypotheses); its negation, also of rank at
  most `η`, fails in that class, which lies in `A_η`, so by completeness the formula itself lies in
  `T∞` and holds throughout `A_η`.  (b) If `A_η` contains two classes (or `D_η` does), then every
  countable model `M` of every class of `A_η` (respectively `D_η`) has
  `η < stabilizationOrdinal M ≤ scottHeight M`.  First, at `scottHeight M` the analysis stabilizes
  for tuples of every length (`scottHeight_stabilizesCompletely`, under `[L.IsRelational]` and
  `[Countable (Σ l, L.Relations l)]`), so empty-tuple equivalence there characterizes isomorphism
  among countable structures in the carrier universe of `M` (`BFEquiv_stabilization_implies_equiv`,
  under `[L.IsRelational]`); hence `StabilizesAt M (scottHeight M)`, the set whose infimum is
  `stabilizationOrdinal M` is nonempty, and `stabilizationOrdinal M ≤ scottHeight M`.  Second, a
  model of another class is `BFEquiv η` to `M` and not isomorphic to it, so `StabilizesAt M α` fails
  for every `α ≤ η` (back-and-forth equivalence is monotone in the level); as the set is nonempty,
  its infimum lies in it, and `η < stabilizationOrdinal M`.  Invariance of the stabilization ordinal
  under isomorphism is not used.  This is an inclusion, a one-sided bound, not an agreement: no
  reverse inclusion and no equality of levels is asserted.  It does not transfer to the internal
  Scott rank, and there is no identification of the stabilization ordinal or the Scott height with
  `internalScottRank`: the countably infinite set in the language with no relations has internal
  Scott rank `1` (`internalScottRank_pureSet`, `Scott/OrbitRank`, at the pin, signatures checked)
  and is recognized at no finite level (finite sets with at least `n` elements are `BFEquiv n` to
  it), so its stabilization ordinal is `ω`, a claim not formalized upstream.
* **Full trees.**  The introductory example of full rooted well-founded trees of finite
  sequences (`LITERATURE.md`, §9), with its rank convention explicit: equally ranked countable
  full well-founded trees are isomorphic; and the finite-extension estimate, that finite
  ancestor-closed subtrees matched with ranks agreeing after capping at `δ + m` admit, for an
  extension by `m` vertices added parent before child, a match in a full target with agreement
  after capping at `δ`.  The same-index equivalence of [AFK26, Proposition 8.6] is not a
  statement: it is false (`LITERATURE.md`, §9).
* **No invariant probability measure.**  No probability measure on the model-code space that is
  invariant under the permutations of `ℕ` is concentrated on the codes of models of `Φ`, derived
  from the finite equivariant pair hulls (the hull of two points, preserved by automorphisms and
  permutations of codes) and whole-hull two-generation, by the argument of the
  trivial-definable-closure criterion for invariant measures concentrated on classes of countable
  structures [AFP16]: an invariant measure would give an exchangeable random finite hull of two
  points strictly larger than the two points.
* **Gδ code sets in the stage chart language** (prospective; a separate target, not a
  consequence of an upstream theorem).  Fix the stage chart language `L_λ` and the coding space
  `StructureSpace L_λ` of InfinitaryLogic (codes on `ℕ`: for each relation symbol and tuple of
  natural numbers, whether the relation holds), with its product topology (the product of the
  discrete space `Bool`), or the same coding on another countable carrier, the empty carrier
  included.  Targets: the set of codes satisfying the exact-age sentence of each exact age
  (`README.md`, Layer 4, in its finitary form) is Gδ, and so is the set of codes satisfying the
  pointed rigid-core formula at a fixed parameter tuple; both directly from their clauses (an
  atomic chart reading is clopen, a request at a fixed root is open, and the structural and
  request clauses are countable intersections), with neither López–Escobar nor Scott
  classification.  The set for the unpointed core, the union over parameter tuples, is a
  countable union of Gδ sets; it is not claimed to be Gδ.  Identifying these sets with
  isomorphism classes needs a supplied realization.  These are statements about codes in the
  stage chart language, not about the models of `Φ`.
* **Examples** (optional).  Examples, proved in Lean, of realizations in which every one-point
  coface is received at every cutoff, showing that receiving alone does not classify terminal
  models: the terminal comparisons of layer 4 need
  the specialized decoding of (R2) and (R3), not receiving at a cutoff alone.

## Downstream: the direct cardinal ceiling

The uncountable consequences stay downstream of the core and of these milestones.  Their carrier
bound is the direct argument of `HULL_ALGEBRA.md`, §6: once infinite hulls preserve cardinality
and every proper closed set is countable, closing a subset of cardinality `ℵ₁` of a
hypothetically larger carrier gives an uncountable proper closed set; no free-set theorem is
used.  It is a statement still to be proved here, and neither it nor any other optional
consequence blocks finite-age reconstruction, which is part of the core.
