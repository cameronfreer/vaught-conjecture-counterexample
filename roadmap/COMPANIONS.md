# Companion milestones: filtration, chart homogeneity, and a geometric obstruction

This document organizes three companion milestones.  They are **optional relative to the core
theorem**: the main theorem of [`README.md`](README.md) and [`IMPLEMENTATION.md`](IMPLEMENTATION.md)
is proved without them, and no core layer or checkpoint depends on them.  Each milestone is
independently completable: none uses a theorem of another milestone, and each lists the core
results it takes as hypotheses.  [`SuggestedCompanions.lean`](SuggestedCompanions.lean) records
selected statements in their generic form, some proved and some left as deliberate `sorry`
targets; [`SEMANTIC_CONTRACT.md`](SEMANTIC_CONTRACT.md) applies unchanged.  Layer numbers here
are those of `README.md` (layers 0–6); the table at the head of `IMPLEMENTATION.md` relates them
to that document's layers and checkpoints.

**What counts as completion.**  A milestone is complete when its theorems are proved about the
concrete objects of the construction (charts, realizations, the density sentence `Φ`, the
expansion domains), each under exactly its stated hypotheses, together with the generic theorems
they specialize.  A structure whose fields assert the desired conclusions, with projection lemmas
reading them back, does not complete any target.  A generic theorem proved with its hypotheses
left undischarged for the construction is progress on a target, not its completion.  The rules
of `README.md` ("Library conventions") apply, including the terminology table and the keep-list.
The literature these milestones rely on is recorded in `LITERATURE.md`, §7.

**Status.**  The seven targets A1, A2, A3, B1, B2, B3, and C are established results: their
proofs are known, and are the arguments given with each below.  They remain formalization targets
here.  The deliberate `sorry` targets of the sketch and the ingredients marked "to be located or
added upstream" are what is not yet formalized.  The status covers these seven statements only,
not their non-claims and not further definability claims (`README.md`, "Status of the optional
results").

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

Upstream names below were checked in the pinned InfinitaryLogic and Mathlib; the sketch
`#check`s the ones it uses.

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

**Regressions.**  `η = 0`, where `D_0 = Q` is defined by a sentence of rank `0` (the bound in (3)
concerns losses and `D_{η+1}`, not `D_η`); a nonzero countable limit `η`, where `D_η = ⋂_{ξ<η} D_ξ`
and the agreement used is the one at the limit itself; a loss consisting of a single class.

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

**Regressions.**  `ψ` of rank `0`; `η = qrank ψ` exactly (the threshold is attained, not only
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

**Instantiation.**  The sentence `Φ`, its presentation `Q`, and its `T∞`: every model of `Φ` of
any cardinality either is `L_{ω₁,ω}`-equivalent to a countable model of `Φ` through a Scott
sentence, or has theory `T∞`.

**Regressions.**  `N` countable (case (S) with its own Scott sentence; so no countable model of `Φ`
satisfies `T∞`); `N` on `ℕ` and on another countable carrier; `N` in a universe different from
the codes'; the finite case, excluded by hypothesis (a finite structure is not coded on `ℕ`, and
for a sentence with finite models the dichotomy can fail).

**Non-claims.**  Case (S) gives infinitary agreement, not an isomorphism between differently
sized models.  No uncountable model of `Φ` is asserted to exist, in either case.  No model of all
of `T∞` is asserted to exist.  No uncountable categoricity, no statement about `L_{∞,ω}`.

**Completion criterion (A).**  A1–A3 are proved for `Φ`, `Q`, `D_η`, and `w_η`, with the generic
lemmas proved and the dichotomy proved on an arbitrary carrier in an arbitrary universe through
the countable-exception argument quoted above.  Completion presupposes that the core results
listed at the head of A are proved in the core, in particular the countable losses (and
complements), the sharp agreement, and the existence of the top-free witnesses; a version of
A1–A3 taking them as hypotheses is progress on A, not its completion (as in the preamble).

## Milestone B — top-free chart homogeneity and its consequences

Setting: a stage `λ = λ_ξ`, the stage chart language at `λ`, and a countable nonempty top-free
realization at `λ` satisfying exact consistency, covering, and finite-cut receiving, read as a
structure `M` in that language.  Core results used: the finite semantic kernel (layer 1),
realizations and the chart language (layer 2), finite-cut receiving and top-free existence
(layer 3).

**Dependency chain** (deliberately short):

1. **exact top-free receiving**: over any actual root, a chart of the prescribed type extending
   the root's chart is realized over the literal root.  To be derived from finite-cut receiving
   with a cutoff above the finitely many labels of the prescribed chart; this uses top-freeness
   (agreement below such a cutoff is equality when no label is top);
2. **chart homogeneity** (B2);
3. **orbit formulas** (B3.1);
4. **atomicity** (B3.2) and the **Scott bound** (B3.3);
5. **primeness** (B3.4).

The generic arguments "a definable orbit isolates its type" and "countable atomic implies prime"
are separate from the construction and lie below the chart theorems; the second allows targets
of arbitrary cardinality and carriers in independent universes.  Chart JEP/AP (B1) is a finite
statement that does not depend on this chain.

### B1. Joint embedding and amalgamation of top-free charts

**Statement.**  For the finite closed top-free charts at `λ` (stage types with no top label):
(JEP) any two charts are restrictions of one chart; (AP) if charts `p₁`, `p₂` restrict along
`f₁ : Fin k ↪ Fin m₁` and `f₂ : Fin k ↪ Fin m₂` to the same chart `r`, there are a chart `p` and
embeddings `g₁`, `g₂` with the **literal commuting root equation** `f₁.trans g₁ = f₂.trans g₂`
and `restrict g₁ p = some p₁`, `restrict g₂ p = some p₂`.

**Hypotheses.**  The plans, lawful labels, and exact partial restriction of layer 1; the
amalgam is a top-free lawful chart whose geometry is a recursive visible-face plan.  Sketch:
the properties `ChartAmalgamation` and `ChartJointEmbedding` (definitions), and
`chartJointEmbedding_of_chartAmalgamation` (proved: amalgamation over the empty chart gives joint
embedding when every chart restricts to one empty chart).

**Upstream ingredients.**  None for the finite statement.  Mathlib's
`FirstOrder.Language.JointEmbedding` and `FirstOrder.Language.Amalgamation` (`ModelTheory/Fraisse`)
concern classes of finitely generated structures under all embeddings and are not used.

**Instantiation.**  The charts occurring in the top-free realizations at block `ξ`.

**Regressions.**  The empty root (`k = 0`, giving JEP); a root equal to one of the two charts;
`p₁ = p₂` with `f₁ = f₂`; a root that is the hull of two of its points but has more than two
points (`SEMANTIC_CONTRACT.md`, item 2); distinct cells sharing a graded index.

**Non-claims.**  Not strong amalgamation: the images of `g₁` and `g₂` may meet outside the image
of the root.  Not amalgamation of arbitrary induced finite substructures: a subset that is not
closed has no chart.  Nothing about charts carrying top labels.  No Fraïssé-limit uniqueness is
asserted.

### B2. Chart homogeneity and local automorphisms

**Statement.**  (Homogeneity) if `t` and `t'` are actual charts of the same type in `M`, some
automorphism `e` of `M` satisfies `e ∘ t = t'`.  (Local automorphisms) every self-embedding `f`
of `M` agrees with an automorphism on each finite tuple `a`: some automorphism `e` has
`e ∘ a = f ∘ a`.  Consequently every self-embedding preserves every `L_{ω₁,ω}` formula:
`M ⊨ φ(a) ↔ M ⊨ φ(f ∘ a)`.

**Hypotheses.**  The setting above (countability is used by the back-and-forth construction).
Generic form of the consequence: `realize_comp_iff_of_agrees_with_automorphism` (proved).

**Upstream ingredients.**  `PotentialIso.ofExtensionFamily` (`Karp/PotentialIso`) for the family
"both tuples sit at the same positions of actual charts of the same type" (arbitrary tuples, so
repeated coordinates are allowed), `PotentialIso.family_bfEquiv`, and
`exists_automorphism_of_bfEquiv_all` (`Scott/OrbitRank`); `BoundedFormulaω.realize_equiv`
(`Lomega1omega/Theory`).

**Instantiation.**  The top-free witness at block `ξ`, as a structure in the stage chart
language at `λ_ξ`.

**Regressions.**  The empty tuple (the identity automorphism); tuples with repeated coordinates;
`f` the identity; a two-point tuple whose hull is large; charts of different sizes containing the
same tuple.

**Non-claims.**  No proper (non-surjective) self-embedding is constructed or asserted to exist.
Nothing about realizations with top labels, about embeddings between different realizations, or
about maps that are embeddings only for the base reduct.

### B3. Orbit theory in the full stage chart language

These targets concern the **full stage chart language**; none transfers automatically to the
base reduct.  Search the pinned libraries before reproducing these generic arguments.

1. **Orbit formulas.**  For a finite tuple `a` in `M`, choose an actual containing chart of type
   `p`.  Existentially quantify its coordinates, assert its chart relation, and identify the free
   tuple with its selected coordinates:
   `θ_a(x̄) := ∃ z̄, P_p(z̄) ∧ ⋀_i x_i = z_{ι(i)}`.
   Prove that this first-order formula defines the automorphism orbit of `a`, using chart
   homogeneity (B2).  Repeated coordinates and the empty tuple are permitted.  Hypotheses: exact
   consistency, covering, finite-cut receiving, and top-freeness (countability for B2).  Sketch:
   the property `OrbitDefinedBy`.
2. **Isolation and atomicity** (generic).  A definable automorphism orbit isolates the tuple's
   complete type over the structure's own complete first-order theory: universal implications
   `∀ x̄, θ_a → ψ` transfer to arbitrary models of that theory, and `θ_a` picks out a singleton in
   the space of complete types.  Uniqueness within the one model is not enough.  This gives
   atomicity without strengthening the hypotheses on the realization.  Sketch:
   `typesWith_eq_singleton_of_orbitDefinedBy` (target), `TypesIsolated`,
   `typesIsolated_of_orbitDefinedBy` (proved from the target
   `typesWith_eq_singleton_of_orbitDefinedBy`).  Ingredients: Mathlib's `Theory.CompleteType`,
   `Theory.typeOf`, `Theory.typesWith`, `Formula.equivSentence`, `completeTheory`
   (`ModelTheory/Types`, `ModelTheory/Semantics`).  A notion of isolated type or atomic model is
   not in the pinned libraries: to be located or added upstream.  InfinitaryLogic's
   `isolatingFormula` (`ModelTheory/TypeIsolation`) is a different notion: an `L_{ω₁,ω}` formula
   isolating a realized infinitary type among the types realized in one structure.
3. **Scott bound.**  First-order formulas have finite quantifier rank; back-and-forth
   equivalence at the rank of an orbit formula determines the tuple's orbit.  Quote
   `internalScottRank_le_of_orbits_determined` (`Scott/OrbitRank`) to obtain
   `internalScottRank ≤ ω` in the library's convention, the supremum over all tuples of the orbit
   rank plus one, `⨆ a, orbitRank a + 1` (so finite but unbounded orbit ranks give exactly `ω`).
   Sketch: `internalScottRank_le_omega0_of_finite_levels` (proved) and
   `internalScottRank_le_omega0_of_orbitDefinedBy` (target; its hypothesis `[Countable M]` is
   that of the bridge `BFEquiv_implies_agree_formulas_omega`).  Ingredients: `Formula.toLω`,
   `Formula.realize_toLω` (`Lomega1omega/Operations`), `BFEquiv_implies_agree_formulas_omega`
   (`Scott/QuantifierRank`), and, between the ordinal universes (`internalScottRank` uses
   `Ordinal.{w}` for a carrier in `Type w`, the quantifier rank and the bridge use `Ordinal.{0}`),
   `BFEquiv.ofOrdinalLift` and `BFEquiv.toOrdinalLift` (`Scott/BackAndForth`).  To be added
   upstream: finiteness of the quantifier rank of `toLω` of a first-order formula.
4. **Primeness** (generic, a separate theorem).  A countable structure all of whose types are
   isolated embeds elementarily into every model of its complete theory: enumerate only the
   source, extend finite tuples preserving every first-order formula, and take the union.  The
   target is any model of the complete theory, in an arbitrary universe, with no receiving or
   countability assumption.  Sketch: `nonempty_elementaryEmbedding_of_typesIsolated` (target).
   Ingredients: Mathlib's `ElementaryEmbedding` (`ModelTheory/ElementaryMaps`); the primeness
   argument itself is not in the pinned libraries: to be located or added upstream.

**Instantiation.**  For the top-free witness at block `ξ`, in the stage chart language at `λ_ξ`:
its orbits are defined by the existential formulas `θ_a`; it is atomic; its internal Scott rank is
at most `ω`; it is a prime model of its complete first-order theory in that language.

**Regressions.**  The empty tuple (its orbit formula is `∃ z̄, P_p(z̄)` for the chosen chart);
repeated coordinates (`ι` not injective); a tuple lying in charts of different sizes (the orbit
formula does not depend on the chart chosen, up to equivalence in `M`); universe independence
(source in `Type w`, target in `Type w'` for primeness; `Ordinal.{w}` for the internal Scott
rank).

**Non-claims.**  Full stage chart language only: nothing about the base reduct, whose Scott
analysis is the subject of A1.  No rank equality, and no identification of the internal Scott rank
with the block index, the expansion height, or a Scott rank of the base class.  Primeness is for
the complete first-order theory, not for an infinitary theory.  Uniqueness of countable atomic
models is a standard consequence and is not required.

**Completion criterion (B).**  B1 is proved for the top-free finite closed charts; B2 and B3 are
proved for every countable nonempty top-free realization satisfying exact consistency, covering,
and finite-cut receiving, each under exactly its stated hypotheses; the generic isolation and
primeness theorems are proved in modules that import no construction module (checked by an
import guard of the form given under C).

## Milestone C — a geometric obstruction

**Statement.**  Let a realization on a carrier `M` of any cardinality satisfy exact consistency
and covering.  Then no infinite subset `S ⊆ M` has the property that every permutation of `S`
extends to an automorphism of the realization.  (Four distinct points already suffice.)

**Proof.**  Two-generation: of three distinct points, one lies in the hull of the other two,
since the hull of the three is a nonsingleton closed set whose two extreme points lie among them
and generate it.  Pointwise hull fixation: an automorphism fixing two points fixes their hull
pointwise, since the chart on that hull is determined by its type and its extreme coordinates
(`SEMANTIC_CONTRACT.md`, item 10), an argument to be carried out from exact consistency, covering,
and the finite geometry alone.  Then, with `p` in the hull of `q` and `r` and a fourth point `s`,
the transposition of `p` and `s` fixes `q` and `r` but moves `p`.  Sketch: `false_of_swap`,
`false_of_four_points`, and `not_forall_perm_extends_of_infinite` (all proved, for an abstract
binary hull and a set of self-maps); `mem_closure_pair_of_twoGeneration` and
`not_forall_perm_extends_of_twoGeneration` (proved) derive the three-point form from whole-hull
two-generation of a closure operator on finite sets.

**Hypotheses.**  Exact consistency and covering only: not top-freeness, modelhood, receiving, or
countability.  The canonical finite hulls come from layer 2 and the geometry from layer 1.

**Import guard.**  The module proving this theorem and the modules it imports must not include
any module of the finite extension constructions or receiving (layer 3), of the countable chain
construction or model existence (layers 2 and 3), of structural continuation (layer 4), or of the
expansion domains (layer 5).  The guard is on the import closure, not only on the direct imports.
The check reads Lean's own record of the import closure, not the source text, so every form of
import (`public`, `meta`, `import all`, the root module `VaughtConjecture`, indented lines) is
covered.  The addition to `scripts/check.sh` below is a proposal, not yet part of `scripts/`: the
module names are to be fixed when these modules exist, and the same check applies to the generic
modules of B3.2 and B3.4, whose import closure must avoid every construction module.  It consists
of a driver body `scripts/ImportGuard.lean`, in the pattern of `scripts/AxiomAudit.lean`, run
through `lake env lean`:

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
  mkdir -p .lake/import-guard
  { echo "import $root"; echo "import Lean"; sed -n '/^open Lean in/,$p' scripts/ImportGuard.lean; } \
    > ".lake/import-guard/$root.lean"
  IMPORT_GUARD_MODULE=$root IMPORT_GUARD_FORBIDDEN="$*" lake env lean ".lake/import-guard/$root.lean"
}
# Placeholders: <HullObstruction> is the module of milestone C; the prefixes name the modules of
# layers 2 (chain construction), 3, 4, and 5.
import_guard VaughtConjecture.<HullObstruction> \
  VaughtConjecture.<ChainConstruction> VaughtConjecture.<Receiving> \
  VaughtConjecture.<StructuralContinuation> VaughtConjecture.<Domains>
```

A prefix matches whole name components: `VaughtConjecture.Receiving` excludes
`VaughtConjecture.Receiving` and `VaughtConjecture.Receiving.Core`, not
`VaughtConjecture.ReceivingData`.

**Upstream ingredients.**  The generic finite-support closure (`FiniteSupportClosure`, with
`setClosure`) and the whole-hull two-generation hypothesis of `TwoGeneratorCardinality` (the hull
of every finite set is the hull of at most two of its points), which the canonical finite hulls
of layer 2 are to satisfy; Mathlib's `ClosureOperator`, `Equiv.swap`, and
`Set.Infinite.natEmbedding`.

**Instantiation.**  Every realization with exact consistency and covering: models of `Φ` read in
the stage language at `ω`, their expansions at every stage, the top-free realizations, and the
structural stable candidate before its modelhood is proved.  In particular no model of `Φ` has an
infinite set all of whose permutations are induced by automorphisms.

**Regressions.**  A set of exactly four points (the threshold of the argument); sets of at most
three points, about which nothing is claimed; uncountable carriers; realizations that are not
models.

**Non-claims.**  This is a restriction imposed by the geometry, not by the model-existence
machinery.  It does not exclude infinite sets of order-indiscernibles, infinite orbits, or
weaker homogeneity (for instance, sets on which the automorphisms act transitively), and it says
nothing about the size of automorphism groups.

**Completion criterion (C).**  The generic theorem is proved in a module with no construction
imports; two-generation and pointwise hull fixation are proved for realizations from exact
consistency and covering; the instance for an arbitrary realization is stated and proved; and the
import guard is in place and passes.
