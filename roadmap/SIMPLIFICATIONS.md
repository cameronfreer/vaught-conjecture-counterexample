# Further simplifications: what is new and what is already done

This review is based on the current source, not on treating earlier proposals as outstanding work. Its strongest new mathematical proposal is proved informally in `HULL_ALGEBRA.md`; all proposed Lean changes remain uncompiled.

## 1. Lead the paper with domains and sentence minimality

The correct small interface is not “every model has a finite tuple of ordinal invariants.” It is:
\[
D_0=Q,\quad D_\eta\text{ decreases continuously},\quad
D_\xi\setminus D_{\xi+1}\text{ countable},\quad
D_\eta\text{ logically uniform through rank }\eta.
\]
Add independently constructed nonempty losses for the lower bound. This is already the preferred proof, not a new theorem. The further simplification is editorial and architectural: make this interface the main theorem of the general library and move global rank theory out of the statement of the construction's objective.

The terminal descriptions are a **countable cover by at-most-one-class conditions**. Do not turn them back into a canonical invariant or a disjoint classification tree. “A core of this type exists” is enough. This avoids least-core choices, uniqueness of descriptors, and characteristic normalization.

## 2. Present the hull as generated-substructure closure

The current source already supplies global finitary anti-exchange closure, two-generator witnesses, finite-hull preservation, and first-order formulas uniquely recovering chart coordinates from extreme coordinates. These now justify a further deduction:
\[
\operatorname{cl}(A)=A\cup\{f_i(a,b):i\in I,\ a,b\in A\}
\]
for a countable family of parameter-free definable total binary operations. Their construction and both inclusions are in `HULL_ALGEBRA.md`.

This would let the paper describe a locally finite definitional expansion whose finitely generated substructures are the actual closed charts. Above the finite kernel, much of the prose about partial evaluation can be replaced by familiar generated-substructure language. The original relational syntax and its precise construction must still be given once, and partial finite-master support still matters during scheduling.

The payoff is not a claim that all of `dcl` or `acl` equals the hull. It is the rigorously narrower identification of the hull with generated closure, and the inclusion `cl ⊆ dcl`. Nor should the receiver be restricted to closed two-point roots: a pair can generate a large chart, and its arity and labelled faces remain essential.

## 3. Finish global naturality with one generic finite-character lemma

The current source already proves finite-hull invariance for literal reductions, structural stable lift, and isomorphisms. The global statements follow from
\[
\operatorname{cl}(A)=\bigcup_{F\subseteq_{\mathrm{fin}}A}h(F).
\]
For an isomorphism \(e\), finite-hull equivariance gives
\[
e[\operatorname{cl}_R(A)]=\operatorname{cl}_{R'}(e[A]),
\]
because finite subsets of \(e[A]\) pull back to finite subsets of \(A\). For same-carrier reductions, equality of finite hulls gives equality of closures directly.

Prove this once for finite-support closure, then add the application wrappers. No additional finite receiver, modelhood theorem, or stabilization redesign is required. This is worthwhile inexpensive library completion, still optional for the endpoint.

## 4. Use stable-label fixedness as the public interpretation of hollowness

`AnchorStable.lean` already proves `isHollow_iff_stable_identity`. It says, for models, that hollowness is exactly the stable refinement leaving every label unchanged. The original persistent-anchor inequalities are needed to prove the finite receiving machinery, but need not be the first explanation encountered by the reader.

A clean exposition therefore defines the stable candidate structurally, proves the anchor equivalence, and thereafter reads “hollow” as “no top acquires a finite new-band value.” This is a proved equivalence, not a newly weakened definition. Keep the anchor formulation as the finite producer's access theorem, and do not conflate hollow with top-free.

## 5. Prune real compatibility edges, with modest measured claims

The source-import closure of the preferred endpoint contains 732 local modules. `ConstructedTerminalCountability` imports `GrowthProlongationBoundary` to state the simple implication called `GrowthAnchorProlongationAt`, while that boundary file also imports characteristic-related compatibility material.

Extract the operational implication into a lower module, or state it directly and move the historical equivalence downstream. Simulating deletion of that single import edge reduces the reachable closure from **732 to 730**. This is not a dramatic size reduction and not a verified patch. It is a direction-of-dependency repair.

Crucially, `TopGradeStableSpectrum` remains reachable through
`NonHollowGrowthProlongation → CapStableModel → NonHollowGrowthReceivingCore → AnchorStable`.
A real separation must also inspect this anchor/stable-value bridge. The source's proof is already characteristic-free at the counting point; this cleanup concerns imports and lower-level API ownership, not a newly discovered logical gap. Do not report a two-file graph change as removal of the characteristic theory.

## 6. Normalize containing-chart choices, not every occurrence object

Canonical finite hulls can replace arbitrary padded covers wherever a consumer only needs the least actual chart containing a finite tuple. One current residual comparison already uses this. Candidate additional clients are rooted comparison adapters and structural transport lemmas.

Do not force the generic scheduler to import Knight closure geometry, and do not erase a larger chart when its auxiliary cells or grades are needed by the finite supplier. The useful rule is: use the least hull for support acquisition, retain the supplied occurrence when its semantics are part of the proof.

## 7. Preserve the remaining essential distinctions

The source has already removed several detours: characteristic-based terminal counting, bespoke scheduling, occurrence-package modelhood in the default prolongation proof, global stopping in the preferred endpoint, and the extra ordinal factor in finite-cover comparison. The direct alternative domain count is also already implemented. None should be advertised as future work.

Further shrinking must respect three boundaries:

- The finite supplier proves arbitrary-input, all-permitted-cap lawfulness, including auxiliary obligations; a final observation theorem is weaker.
- Installation produces an actual occurrence from the existing model clauses; catalogue membership or a proposed chart type does not supply it.
- Readback distinguishes exact proper values, literal tops, and capped agreement.

These are distinct mathematical assertions. A paper may collect them in a single well-stated finite lemma, but a proof audit should continue to see all three.

## 8. A standard consequence worth stating in the paper

Let \(T_\infty\) consist of infinitary sentences true on all but countably many isomorphism classes of models of \(\Phi\). Sentence minimality and uncountability imply that exactly one of \(\psi,\neg\psi\) belongs to \(T_\infty\). It is closed under countable conjunctions, and every countable subset of it is realized by uncountably many countable models: remove the countable union of exceptional classes.

Nevertheless no countable model realizes all of \(T_\infty\). For each countable \(M\), its Scott sentence isolates its class; the negation of that sentence belongs to \(T_\infty\). This is a direct consequence of the constructed sentence minimality and Scott isolation, not a new construction-specific theorem or a claim of first-order compactness. It helps explain what the homogeneous expansion domains approach: a coherent cocountable infinitary theory rather than a single countable generic model.
