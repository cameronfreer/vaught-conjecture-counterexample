# Dashboard

A summary of the state of the main theorem, by layer, with the named hypotheses of the main
theorem and the open mathematics.  [`README.md`](README.md) (the status paragraphs of its layers)
and [`IMPLEMENTATION.md`](IMPLEMENTATION.md) (the status of its checkpoints) are the sources and
prevail where this page differs from them.

**Rules.**  Every entry either names a theorem compiled in this repository on `main` (marked
*compiled*, with the hypotheses that it takes) or carries one of the markers of `README.md`,
Layer 0, and of the status paragraphs: *still to be proved* (a statement of the roadmap with no
proof here), *prospective* (specified, with no statement in the library yet), *open* (no proof and
no refutation is known), or *refuted* (false, with the negative special case named).  A theorem
proved under named hypotheses is *compiled conditionally*; each of those hypotheses keeps its own
status, and a conditional theorem never counts as a proof of its hypotheses.

**Convention for the percentages.**  The percentage of a layer is an editorial estimate of
the share of the roadmap's statements for that layer that are compiled, a conditional theorem
counting as compiled and its hypotheses being counted where they are stated.  It is an estimate of
progress, not a measure of proof: no percentage below 100 bounds the work that remains, and a
percentage of 100 would not by itself mean that the hypotheses of a layer are proved.

## Layers

| Layer | Estimate | Compiled (examples of theorems named) | Main open items |
| --- | --- | --- | --- |
| 0, general results | 97% | `Counting.countable_of_subsingleton_cover` | prospective upstream interfaces |
| 1, finite kernel | 98% | `StageType.provisionalOffset` | the bound (d) of the offset (prospective) |
| 2, realizations, syntax | 95% | `Realization.eq_of_eval_eq_some` | hull items 4–5 for realizations |
| 3, the completion (R6) | 72% | `Seed.nonempty_completionBelowFullGrade_of_le_two` | the step at `m ≥ 3` |
| 3, receiving | 90% | `Expansion.finiteCutReceiving_of_hasGatedPinnedExtensions` | 4b-ii; (R2)–(R4) |
| 4, continuation | 62% | `Realization.stableCandidate` | twins; output 3 |
| 5, domains, agreement | 85% | `Expansion.expansionDomain_loss_countable` | the hypotheses below |
| 6, the bounds | 90% | `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification` | the hypotheses below |
| Manuscript correspondence | 20% | the concordance rows (`IMPLEMENTATION.md`) | no row is P |
| **Overall** | **≈ 78%** | | |

Notes on the rows, each with its marker:

- *Layer 3, the completion.*  Compiled: 2.1–2.5; the tower and its invariant
  (`Seed.towerInvariant_succ`, `Seed.towerInvariant_top`); `2FL(1)` (`Seed.twoFaceLift_one`); the
  completion below the full grade at `m ≤ 2`; per seed, under `2FL(j)` or `Seed.DeadAt j` at each
  grade `2 ≤ j < m` (`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt`).  Refuted:
  the union fill (`UnionFillCounterexample.not_unionFill_seed`) and `2FL(2)`
  (`TwoFaceLiftCounterexample.not_twoFaceLift_two`, hence
  `TwoFaceLiftCounterexample.not_forall_twoFaceLift`).  Still to be proved, not refuted:
  `StageType.HasCoatomExtensions`, `StageType.HasApexCoatomExtensions`.  Prospective: the
  existential two-face lift `2FL∃(j)` and the choosing one-grade lift.
- *Layer 3, receiving.*  Compiled: finite-extension receiving from finite-cut receiving, for an
  exactly consistent realization at a stage that is zero or a limit
  (`Realization.HasFiniteCutReceiving.hasFiniteExtensionReceiving`); gate recovery
  (`StageType.GatedExtension.recover`); (R1) conditional on `StageType.HasGatedPinnedExtensions`
  (`Realization.IsModel.hasFiniteCutReceiving_of_hasGatedPinnedExtensions`); the cap-to-model
  theorem at a limit stage, conditional on the nonemptiness of the instances of uniformity and
  dominance (`Realization.isModel_of_hasFiniteCutReceiving`); the top-free witnesses, steps 1–7,
  conditionally: steps 2–3 under `StageType.HasCoatomExtensions`, and step 7 under
  `StageType.HasApexCoatomExtensions` at `λ_η` and the uniqueness of model expansions at `λ_η`
  (`nonempty_loss_of_hasApexCoatomExtensions`).  Still to be proved: 4b-ii, the gated
  construction as data; (R2), (R3), (R4).
- *Layer 4.*  Compiled: normalization, conditional on finite-extension receiving and forcing donors
  (`Realization.label_eq_stableLabel`); the structural candidate given its lawfulness
  (`Realization.stableCandidate`), lawful without twins
  (`Realization.isStablyLawful_of_injOn_gradedIndex`); cover-hollowness and stable-label fixedness
  (`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`); the exact-age comparison
  (`Realization.nonempty_equiv_of_exactReceivingWithin`); the three comparisons, the rigid-core one
  conditional on finite-extension receiving (from (R1);
  `Realization.nonempty_equiv_of_isGloballyRigidCore`), the residual and hollow ones on (R2) and
  (R3) (`Realization.nonempty_equiv_of_residual`, `Realization.nonempty_equiv_of_hollow`); the
  cover of the terminal models, conditional on the continuation criterion
  (`Realization.exists_hasTerminalProperty`).  Open: stable availability at twins.  Still to be
  proved: output 3; the equivalence of cover-hollowness (with which the compiled statements are
  formulated) and the original no-anchor predicate (the meaning of "hollow",
  `SEMANTIC_CONTRACT.md`, item 8); the exact-age Scott sentences.
- *Layers 5 and 6.*  Compiled conditionally on the hypotheses below, or on statements derived
  from them (next-block uniqueness; finite-extension receiving, from (R1)): uniqueness and limit
  existence (`ModelExpansion.subsingleton`, `ModelExpansion.nonempty_of_forall_lt`, under
  next-block uniqueness), next-block uniqueness
  (`Expansion.NextBlockUniqueness.of_forcingDonors`), logical agreement
  (`Expansion.bfEquiv_of_modelExpansions`), countable losses
  (`Expansion.expansionDomain_loss_countable`), nonempty losses
  (`hasNonemptyLosses_of_hasApexCoatomExtensions`, also on the coatom extension property with
  apex at every countable block stage; item 7 below), and the thin `ℵ₁` spectrum
  (`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`).

## The named hypotheses of the main theorem

`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`
(`MainTheorem/ModelExpansionDomains`) is compiled conditionally on the seven hypotheses below.
Each is a separate statement with its own status; none of them is derived from another in the
library.

| Hypothesis | Lean | Used for |
| --- | --- | --- |
| the cap-to-model theorem at `ω` | `CapToModel` | the first domain |
| (R1), finite-cut receiving of models | `Expansion.FiniteCutReceiving` | uniqueness, agreement |
| forcing donors | `ForcingDonors` (every `ξ < ω₁`) | next-block uniqueness |
| the continuation criterion (output 3) | `ContinuationCriterion` | the terminal cover |
| (R2), exact residual receiving | `Realization.ResidualReceiving` | the residual comparison |
| (R3), exact hollow-growth receiving | `Realization.HollowReceiving` | the hollow comparison |
| nonempty losses (condition 4) | the hypothesis `hn` | the lower bound |

Status of each:

1. `CapToModel`: still to be proved.  Compiled conditionally on the coatom extension property with
   apex at `ω` (`CapToModel.of_hasApexCoatomExtensions`), which is still to be proved.
2. `Expansion.FiniteCutReceiving`: still to be proved.  Compiled conditionally on the gated pinned
   extension property (`Expansion.finiteCutReceiving_of_hasGatedPinnedExtensions`), which is still
   to be proved (4b-ii).  It is also used for the rigid-core comparison.
3. `ForcingDonors`: still to be proved, by a finite construction of Layer 3 from the completion
   below the full grade (prospective).
4. `ContinuationCriterion`: still to be proved (sufficiency only; the converse is not stated).
5. `Realization.ResidualReceiving`: still to be proved (the LOW construction).
6. `Realization.HollowReceiving` for `Realization.IsCoverHollowAtBlock`: still to be proved (the
   growth construction).
7. Nonempty losses: still to be proved.  Compiled conditionally on the coatom extension property
   with apex at every countable block stage and on next-block uniqueness
   (`hasNonemptyLosses_of_hasApexCoatomExtensions`, stated for the bundled domains, which also take
   `CapToModel`; per block, `nonempty_loss_of_hasApexCoatomExtensions`); this is not composed with
   the theorem above in a compiled statement.

There is no hypothesis of countable losses and none of next-block uniqueness: the first is
`Expansion.expansionDomain_loss_countable`, the second
`Expansion.NextBlockUniqueness.of_forcingDonors`, each compiled conditionally on hypotheses in the
list.

## The research front

Each item is open or still to be proved; none is assumed by a theorem of the library except as a
named hypothesis.  A result marked *under review, not yet merged* is not on `main` and is not
counted as compiled.

1. **Layer 3 at `m ≥ 3`** (open).  The existential two-face lift `2FL∃(j)`, with a choosing
   variant of `CellScheme.Rows.cappedLift_of_boundary_short` (both prospective, stated in prose in
   `README.md`, Layer 3, 3.1, (R6), 2.7); whether every seed has `2FL(j)` or `Seed.DeadAt j` at each
   grade (undecided on `main`).  The two prospective statements would give
   `StageType.HasApexCoatomExtensions` (an implication not yet stated in the library), hence the
   coatom extension hypotheses of the cap-to-model theorem, the top-free witnesses, and output 3.
   Under review, not yet merged: the per-grade disjunction `2FL(j) ∨ Seed.DeadAt j` does not cover
   every seed at `m = 3`, while `2FL∃(j)` is equivalent to the step of the tower and holds on the
   seed at `m = 3` where the disjunction fails (a seed other than `seed4`), so 2.7 is to be
   conditioned on `2FL∃`.
2. **Stable availability at twins** (open).  Apart from the case of an existing next-block
   expansion (`Realization.isStablyLawful_of_reduce_eq`, which presupposes what output 3 is to
   construct), no conditional statement of it is made.  Refuted hypotheses on single types:
   `Continuation.CandidateCounterexamples.not_synchronizingCofaces_blockStage` (with two variants)
   and `Continuation.CandidateCounterexamples.not_twinOrdering_blockStage`.
3. **4b-ii** (still to be proved): the gated construction as data, that is,
   `StageType.HasGatedPinnedExtensions`.  Under review, not yet merged: that property is refuted at
   every stage, so the conditional (R1) (`Expansion.finiteCutReceiving_of_hasGatedPinnedExtensions`)
   is vacuous, and a corrected gate predicate is to be designed.
4. **Forcing donors** (still to be proved): the finite construction behind `ForcingDonors`.
5. **Output 3, part D, and (R4)** (still to be proved): (R4) over positive roots, the empty root by
   the coatom extension over the empty face, the coatom extension properties at `λ_{ξ+1}`, and the
   lawfulness of the candidate (`Realization.IsStablyLawful`), from the twin-free case or, at
   twins, item 2.
6. **The attained least lift and structural successor leastness** (prospective).  One lift of a
   legal stage type at a limit stage `β` to `β + ω`, least at every cell (each minimum is attained
   separately: `StageType.exists_lift_label_eq_ofOffset`); the threshold forced by a cover is read
   off that one lift, and the threshold characterization and the limit-stage monotonicity are
   derived from it under that stage hypothesis; the least lift itself rests on the finite row
   algebra and the lawful provisional lift only, not on that monotonicity.  The stable section at
   most every coherent next-block assignment
   (`README.md`, Layer 3, 3.1, "The attained least lift"; Layer 4, "Status", output 2 refined).
   The structural successors of a consistent realization `R` (the consistent realizations at the
   next block with reduct `R`) lie between the stable candidate, the least (covering used), and
   literal weakening, the greatest; for a model the two are equal exactly when it is cover-hollow
   (`Realization.IsCoverHollow`).  Least, not unique: literal weakening is the greatest lift, a
   pointwise minimum of lifts need not be lawful, and the twin-ordering hypothesis stays refuted.
   None of these makes the candidate a model (output 3, item 5 above), and none gives exact
   lifting over a separately prescribed higher root.  Separate global routes: classical Fraïssé
   existence, Scott isolation with countable-limit existence, terminal presentations, and global
   termination (`README.md`, the section on the top-free witnesses, "Complementary global
   routes"; `IMPLEMENTATION.md`, §4, statements 1–10 with their completion criteria).
