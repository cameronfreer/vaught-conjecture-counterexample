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
| 3, the completion (R6) | 72% | `Seed.nonempty_completionBelowFullGrade_of_le_two` | the completion at `m ≥ 3` |
| 3, receiving | 90% | `Expansion.finiteCutReceiving_of_hasCoupledGatedPinnedExtensions` | 4b-ii; (R2)–(R4) |
| 4, continuation | 62% | `Realization.stableCandidate` | output 3: (R4), the apex property |
| 5, domains, agreement | 85% | `Expansion.expansionDomain_loss_countable` | the hypotheses below |
| 6, the bounds | 90% | `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification` | the hypotheses below |
| Manuscript correspondence | 25% | `CellScheme.Rows.printedRespects_iff`; the concordance rows (`IMPLEMENTATION.md`) | rows 2–5, 29 and 43 P, and row 14 for the printed definitions of [AFK26, §2] that it names; row 1 C, with its truncation function P; rows 6 and 44 S (one direction at `ω₁`); rows 8/11 P on corrected row 7 with domains S; row 15 P/C/P/S by part; the remaining rows S or C |
| **Overall** | **≈ 78%** | | |

Notes on the rows, each with its marker:

- *Layer 3, the completion.*  Compiled: 2.1–2.5; the tower and its invariant
  (`Seed.towerInvariant_succ`, `Seed.towerInvariant_top`); `2FL(1)` (`Seed.twoFaceLift_one`); the
  completion below the full grade at `m ≤ 2`; per seed, under `2FL(j)` or `Seed.DeadAt j` at each
  grade `2 ≤ j < m` (`Seed.nonempty_completionBelowFullGrade_of_twoFaceLift_or_deadAt`); the
  existential two-face lift `2FL∃(j)` (`Seed.TwoFaceLiftExists`), the step of the tower stated
  exactly (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`, `Seed.towerInvariant_top_iff`).
  Refuted: the union fill (`UnionFillCounterexample.not_unionFill_seed`); `2FL(2)`
  (`TwoFaceLiftCounterexample.not_twoFaceLift_two`, hence
  `TwoFaceLiftCounterexample.not_forall_twoFaceLift`); the coverage of every seed by the case split
  `2FL(j) ∨ Seed.DeadAt j` (`CaseSplitCounterexample.not_forall_twoFaceLift_or_deadAt`); and
  `2FL∃(2)` for the legal seed `TwoFaceLiftExistsCounterexample.seedL`
  (`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_seedL`, hence
  `TwoFaceLiftExistsCounterexample.not_forall_twoFaceLiftExists`).  Compiled for `seedL` outside
  the tower: its thin completion (`ThinCompletion.nonempty_completionBelowFullGrade_seedL`) and the
  coatom extension of `TL` and `T5` with apex at every stage
  (`ThinCompletionExamples.exists_coatomExtension_seedL`).  Compiled at `m = 3`, conditionally on
  the named hypothesis `Seed.OrderedLayerStep` (one new cell per graded face of full scope): the
  completion (`Seed.OrderedLayerStep.completion`); the hypothesis is exactly legality of the layer
  scheme with a lawful extension (`Seed.orderedLayerStep_iff`), automatic at the top grade for
  seeds with bottom apexes
  (`Seed.OrderedLayerStepBelowTop.orderedLayerStep`), with instances `seed4`, `seed5`, `seedL`,
  `seedLM`, `seedLL`; forced separations in every completion
  (`CompletionBelowFullGrade.exists_separating_of_forcesTop`).  Refuted: the ordered-layer step for
  every seed on five points (`CrossedCouplingCounterexample.not_forall_hasOrderedLayerStep`, at the
  legal seed `CrossedCouplingCounterexample.seedHG`, every completion of which has two cells at
  `(univ, 1)`).  Compiled: `seedHG` has a completion below the full grade, the multi-layer scheme
  with two new cells at `(univ, 1)`, one per forced separation
  (`CrossedCouplingCounterexample.nonempty_completionBelowFullGrade_seedHG`, from
  `Seed.MultiLayerStep`), so the ordered-layer step is strictly stronger than the completion
  (`CrossedCouplingCounterexample.not_forall_hasOrderedLayerStep_of_nonempty`).  Compiled for
  every seed on five points: the canonical multi-layer scheme (two copies of `(C, k)` and `(D, k)`
  at each `(univ, k)`), with forcedness and the lifts from the common face.  Compiled,
  conditionally on named hypotheses: its multi-layer step, hence a completion.
  `Seed.canonicalMultiStep_of_product` assumes (i) the product clause `Seed.CanonicalProduct` at
  the grades 1–4, a sufficient hypothesis, not a field of the step: refuted at the grade 4 at all
  six compiled seeds, so this form applies at none of them; (ii) `hcode`, copy rows coded; (iii)
  `hpair`, copy rows lawful below both coatoms; (ii) and (iii) are conditions on the choice of copy
  rows.  `Seed.canonicalMultiStep_of_productBelowTop` assumes (i) at the grades 1–3 only (holds for
  `seedHG`; refuted at the grades 2, 3 for the other five seeds), (ii) and (iii) at those grades,
  (iv) `Seed.HasBottomApexes` (compiled for all six seeds), and (v) `hR3`, the top row at the
  grade 4 (a choice of the copy rows); it takes the grade 4 from the grade 3, not from the product
  clause, and completes `seedHG` with every hypothesis compiled
  (`Seed.nonempty_completionBelowFullGrade_canonical_seedHG`).  Refuted, for every copy rows: the
  product clause at the grades 2–4 for `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` and at the
  grade 4 for `seedHG` (`Seed.not_canonicalProduct_seed4`, `Seed.not_canonicalProduct_seedHG`), a
  refutation of the family as a fibre product, not of the family's step (which holds for `seedHG`
  at the grade 4) nor of the completion.  Compiled, with no hypothesis beyond the orientation of
  the layer rows: under oriented copy rows (`OrderedLayer.orientedRows`, for layer rows with
  `OrderedLayer.IsOriented`) the step of the family *is* the ordered-layer step
  (`Seed.canonicalMultiStep_oriented_iff`, an exact reformulation: both copies of a grade read
  alike).  The five seeds `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` were already completed by
  their ordered-layer steps (`Seed.orderedLayerStep_seed4` and its companions); what is new is only
  that the canonical multi-layer scheme itself has a step at them
  (`Seed.nonempty_completionBelowFullGrade_seed4_oriented` and its companions), so all six compiled
  seeds have a step of the family
  (`Seed.hasCanonicalMultiStep_seed4_seed5_seedL_seedLM_seedLL_seedHG`).  Refuted, for oriented
  rows only, as corollaries of `CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG` and
  `not_exists_orderedLayerStep_seedL_seedLM` through the iff: at `seedHG`
  (`Seed.not_canonicalMultiStep_oriented_seedHG`) and as one choice for `seedL` and `seedLM`
  (`Seed.not_exists_canonicalMultiStep_oriented_seedL_seedLM`).  Compiled, for every copy rows: the
  orientation forced on a copy by a forcing from its coatom
  (`Seed.MultiLayerStep.copyRows_lt_of_forcesTop`; at `seedHG` the copy of `(D, 2)` reads toward
  `C` and the copy of `(C, 3)` toward `D`, at `seedL` and `seedLM` the copies of the forcing coatom
  at the grades 2, 3; at `seed5` the copies of `(D, 2)`, `(D, 3)`, `Seed.copyRows_lt_of_T5_T5`).
  Refuted, for the own-side rows only (`OrderedLayer.ownSideRows`, each copy reading its own
  coatom's values other than `⊥` above the other's): at `seedHG`, `seedL`, `seedLM`
  (`Seed.not_ownSideStep_seedHG`, `…_seedL`, `…_seedLM`), not the family nor the completion;
  undecided at `seed4`, `seed5`, `seedLL`.  Open: copy rows giving the step of the family for every
  seed on five points.  Still to be
  proved, not refuted: `StageType.HasCoatomExtensions`,
  `StageType.HasApexCoatomExtensions`.
- *Layer 3, receiving.*  Compiled: finite-extension receiving from finite-cut receiving, for an
  exactly consistent realization at a stage that is zero or a limit
  (`Realization.HasFiniteCutReceiving.hasFiniteExtensionReceiving`); gate recovery
  (`StageType.GatedExtension.recover`) and with the twin–gate coupling
  (`CellScheme.Rows.IsGate.recover_of_twinsReadGate`); (R1) conditional on
  `StageType.HasCoupledGatedPinnedExtensions`, which is open
  (`Realization.IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions`); the refutation
  of the first form `StageType.HasGatedPinnedExtensions`
  (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`); the coupled form at the refuting
  input (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`); the cap-to-model
  theorem at a limit stage, conditional on the nonemptiness of the instances of uniformity and
  dominance (`Realization.isModel_of_hasFiniteCutReceiving`); the top-free witnesses, steps 1–7,
  conditionally: steps 2–3 under `StageType.HasCoatomExtensions`, and step 7 under
  `StageType.HasApexCoatomExtensions` at `λ_η` and the uniqueness of model expansions at `λ_η`
  (`nonempty_loss_of_hasApexCoatomExtensions`).  Still to be proved: 4b-ii, the gated
  construction as data; (R2), (R3), (R4).
- *Layer 4.*  Compiled: normalization, conditional on finite-extension receiving and forcing donors
  (`Realization.label_eq_stableLabel`); forcing donors, conditional on the coatom extension
  property (`forcingDonors_of_hasCoatomExtensions`); the structural candidate
  (`Realization.stableCandidate`), stably lawful for every model at a block stage
  (`Realization.IsModel.isStablyLawful`), and more generally for every exactly consistent covering
  realization with legal types at a block stage (`Realization.isStablyLawful_of_hasLegalTypes`);
  output 3 and the
  continuation criterion, conditional on (R4) and the coface instances at the next block
  (`ContinuationCriterion.of_stableCappedReceiving`); conversely (R4) from the criterion, (R1) and
  forcing donors (`Expansion.stableCappedReceiving_of_continuationCriterion`), so the two are
  equivalent under (R1), forcing donors and the coface instances
  (`Expansion.stableCappedReceiving_iff_continuationCriterion`); (R4) from the finite statement
  `StageType.HasStableRecoverySchemes` for the marker and cap calibration
  (`StableCappedReceiving.of_hasStableRecoverySchemes_markerCap`), a hypothesis refuted at every `ξ`
  (`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`), and for the
  graded cap calibration, open, whose acquisition is compiled
  (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`,
  `Realization.IsModel.acquiresCalibratedContexts_gradedCap`); cover-hollowness and stable-label
  fixedness (`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`); the exact-age comparison
  (`Realization.nonempty_equiv_of_exactReceivingWithin`); the three comparisons, the rigid-core one
  conditional on finite-extension receiving (from (R1);
  `Realization.nonempty_equiv_of_isGloballyRigidCore`), the residual and hollow ones on (R2) and
  (R3) (`Realization.nonempty_equiv_of_residual`, `Realization.nonempty_equiv_of_hollow`); the cover
  of the terminal models, conditional on the continuation criterion
  (`Realization.exists_hasTerminalProperty`).  Still to be proved: (R4) and the coatom extension
  property with apex at the next block, for output 3; the equivalence of cover-hollowness (with
  which the compiled statements are formulated) and the original no-anchor predicate (the meaning of
  "hollow", `SEMANTIC_CONTRACT.md`, item 8); the exact-age Scott sentences.
- *Layers 5 and 6.*  Compiled conditionally on the hypotheses below, or on statements derived
  from them (next-block uniqueness; finite-extension receiving, from (R1)): uniqueness and limit
  existence (`ModelExpansion.subsingleton`, `ModelExpansion.nonempty_of_forall_lt`, under
  next-block uniqueness), next-block uniqueness
  (`Expansion.NextBlockUniqueness.of_forcingDonors`), logical agreement
  (`Expansion.bfEquiv_of_modelExpansions`), countable losses
  (`Expansion.expansionDomain_loss_countable`), countably many classes terminal at each level
  (`MainTheorem.countable_isoClasses_terminalAt`, on (R1), the continuation criterion, (R2), and
  (R3)), nonempty losses
  (`hasNonemptyLosses_of_hasApexCoatomExtensions`, also on the coatom extension property with
  apex at every countable block stage; item 7 below), and the thin `ℵ₁` spectrum
  (`densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`, and with `CapToModel` and
  nonempty losses derived from the coatom extension property with apex at every countable block
  stage,
  `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions`,
  and with forcing donors also derived from it,
  `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'`).
  Also compiled, and not used by the count: eventual departure and the last stage of a class
  (`COMPANIONS.md`, terminal refinement, items 1–2), abstractly under logical agreement, nonempty
  losses, and isolation (`ExpansionDomains.core_eq_empty`,
  `ExpansionDomains.mem_loss_iff_lastStage_eq`), and for the actual expansion domains under
  next-block uniqueness, finite-cut receiving ((R1)), and the coatom extension property with apex
  at every countable block stage, which also gives `CapToModel` (`expansionDomain_core_eq_empty`).
  Positive niceness of the
  base reduct of every model at a block stage on a countable carrier
  (`Realization.IsModel.isNice_toStructure_reduce`, `MainTheorem/Niceness`; manuscript
  correspondence, row 30, S), with one threshold for all closed tuples
  (`exists_isNiceTupleAt_of_hasTerminalRefinement`), compiled conditional on
  `HasTerminalRefinement.{w}` (the specified terminal refinement, row 38) and next-block uniqueness.
  At `w = 0` the refinement is derived from (R1), next-block uniqueness, and the countable-block
  apex property, all still open; the main theorem does not use niceness.
- *Manuscript correspondence, item 5.*  Compiled conditionally on (R1), next-block uniqueness,
  and the coatom extension property with apex at every countable block stage: the maximal
  refinement of a prescribed model (`MainTheorem.exists_maximalRefinement`); rows 33–36, 38, 40
  stay S.
- *Acceptance lemma 1 (same-level maximal realization).*  Compiled conditionally on
  `StageType.HasApexCoatomExtensions` at `λ_β` and `ForcingDonors β` (`exists_sameLevelMaximal`).
  Terminality of every cover-hollow realization at a block stage is compiled with no hypothesis
  (`Realization.IsCoverHollow.isTerminalAt`, Layer 4).
- *Layer 6, thinness in scatteredness form.*  Compiled conditionally on the cap-to-model theorem,
  (R1), forcing donors at every countable block index, the continuation criterion, (R2) and (R3),
  each still to be proved, with neither sentence separation nor López–Escobar
  (`densitySentence_isThinOnNatModels_of_terminalClassification_bfScattered`).

## Targets from the unconditional route

Prospective (`IMPLEMENTATION.md`, "Targets from the unconditional route"): one contract for each
hypothesis of the five-hypothesis form, complete only when that hypothesis is compiled for every
input.  U1, (R1) through an attached gated scheme (a gate at `⊤` realized by the bottom-pattern
clause), first; U2, `StableCappedReceiving` by calibrated receiving in the model, then the
continuation criterion; U3, (R3) and (R2) by exact recovery; U4, the apex property by a completion
over the whole boundary.  The known failures (the gated and coupled inputs, `seedL`, the twin
donors, the grade of private tops) are their tests.  No status on this page changes.

## The named hypotheses of the main theorem

Three forms of the main theorem on `ℕ` are compiled, each conditionally on named hypotheses.  The
five-hypothesis form is the stronger statement and implies the six-hypothesis form; all three are
kept.  At present the fewest hypotheses are five.  The count went from seven to six to five only
by compiled derivations; no hypothesis of the list is proved.

- **Seven hypotheses.**  `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification`
  (`MainTheorem/ModelExpansionDomains`) is compiled conditionally on hypotheses 1–7 of the table
  below: `CapToModel`, (R1), forcing donors, the continuation criterion, (R2), (R3), and nonempty
  losses.
- **Six hypotheses.**
  `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions`
  (`MainTheorem/Composition`; on all countable carriers,
  `vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions`) is
  compiled conditionally on hypotheses 2–6 and 8: (R1), forcing donors, the continuation
  criterion, (R2), (R3), and the coatom extension property with apex at every countable block
  stage.  Hypotheses 1 and 7 are derived in it: `CapToModel` from hypothesis 8 at `λ_0 = ω`
  (`CapToModel.of_hasApexCoatomExtensions`), and nonempty losses from hypothesis 8 and next-block
  uniqueness (`hasNonemptyLosses_of_hasApexCoatomExtensions`).  It is obtained from the first form
  by the two derivations above.
- **Five hypotheses.**
  `densitySentence_hasThinAlephOneSpectrum_of_terminalClassification_of_hasApexCoatomExtensions'`
  (`MainTheorem/Composition`; on all countable carriers,
  `vaughtCounterexample_allCarriers_of_terminalClassification_of_hasApexCoatomExtensions'`) is
  compiled conditionally on hypotheses 2, 4–6 and 8: (R1), the continuation criterion, (R2), (R3),
  and the coatom extension property with apex at every countable block stage.  It is obtained from
  the six-hypothesis form by deriving hypothesis 3 from hypothesis 8 at the next block stage
  (`forcingDonors_of_forall_hasApexCoatomExtensions`).  In it `CapToModel` is derived from
  hypothesis 8, forcing donors from hypothesis 8, next-block uniqueness from hypotheses 2 and 3,
  countable losses from hypotheses 2 and 4–6, and nonempty losses from hypothesis 8 and next-block
  uniqueness.  No compiled theorem derives next-block uniqueness or countable losses from
  hypothesis 8 alone; both derivations use (R1).  The five-hypothesis restricted form, with
  hypothesis 6 restricted, is a separate statement (prospective).

Each hypothesis is a separate statement with its own status.  None of them is derived from another
in the library, except hypotheses 1 and 7, which are derived from hypothesis 8 (with next-block
uniqueness, from hypotheses 2 and 3, for hypothesis 7), hypothesis 3, which is derived from
hypothesis 8 (`forcingDonors_of_forall_hasApexCoatomExtensions`; the six-hypothesis form takes
it, the five-hypothesis form derives it), and hypothesis 4, which is derived from hypothesis 8
together with (R4) (`ContinuationCriterion.of_hasApexCoatomExtensions`); (R4) is in none of the
lists.

| Hypothesis | Lean | Used for | Seven | Six | Five |
| --- | --- | --- | --- | --- | --- |
| 1. the cap-to-model theorem at `ω` | `CapToModel` | the first domain | yes | derived | derived |
| 2. (R1), finite-cut receiving of models | `Expansion.FiniteCutReceiving` | uniqueness, agreement | yes | yes | yes |
| 3. forcing donors | `ForcingDonors` (every `ξ < ω₁`) | next-block uniqueness | yes | yes | derived |
| 4. the continuation criterion (output 3) | `ContinuationCriterion` | the terminal cover | yes | yes | yes |
| 5. (R2), exact residual receiving | `Realization.ResidualReceiving` | the residual comparison | yes | yes | yes |
| 6. (R3), exact hollow-growth receiving | `Realization.HollowReceiving` | the hollow comparison | yes | yes | yes |
| 7. nonempty losses (condition 4) | the hypothesis `hn` | the lower bound | yes | derived | derived |
| 8. the coatom extension property with apex | `StageType.HasApexCoatomExtensions` (every `λ_η`, `η < ω₁`) | hypotheses 1, 3 and 7 | no | yes | yes |

Status of each:

1. `CapToModel`: still to be proved.  Compiled conditionally on the coatom extension property with
   apex at `ω` (`CapToModel.of_hasApexCoatomExtensions`), which is still to be proved.
2. `Expansion.FiniteCutReceiving`: still to be proved.  Compiled conditionally on the coupled
   gated pinned extension property
   (`Expansion.finiteCutReceiving_of_hasCoupledGatedPinnedExtensions`), which is open (4b-ii).  It
   is also used for the rigid-core comparison.
3. `ForcingDonors`: still to be proved.  Compiled conditionally on the coatom extension property
   at `λ_{ξ+1}` (`forcingDonors_of_hasCoatomExtensions`, `Extension/ForcingDonorsCoatom`), hence on
   the coatom extension property with apex at every countable block stage
   (`forcingDonors_of_forall_hasApexCoatomExtensions`), hypothesis 8.  The six-hypothesis form
   keeps forcing donors as its hypothesis `hF`; the five-hypothesis form derives them.
   Unconditionally: one- and two-point inputs up to the threshold `4`
   (`forcingDonorsUpTo_one_four`, `forcingDonorsUpTo_two_four`).
4. `ContinuationCriterion`: still to be proved (sufficiency only; the converse is not stated).
   Compiled conditionally on (R4) and the coatom extension property with apex at every successor
   block stage (`ContinuationCriterion.of_hasApexCoatomExtensions`); (R4) is still to be proved,
   so the six- and five-hypothesis forms keep the criterion as a hypothesis.
5. `Realization.ResidualReceiving`: still to be proved (the LOW construction).  Exactly
   reformulated as exact receiving of the legal types of top grade at most `K`
   (`Realization.residualReceiving_iff`).  A reduction is compiled: it follows from (R1) for every
   model at every limit stage (a receiving hypothesis that ranges over every limit stage at fixed
   universe levels and is not supplied by the countable-stage `Expansion.FiniteCutReceiving`,
   item 2), `Realization.ResidualAcquisition P`, and `Realization.CutoffDetermination P`
   (`Realization.residualReceiving_of_cutoffDetermination`), for a predicate `P` on acquired
   contexts not yet defined: the reduction is a template, and its hypotheses are not statements
   still to be proved (no predicate `P` is defined in the library, and neither acquisition nor
   determination is proved beyond the rigid-core instance).  For `P` always true, acquisition is
   immediate and determination fails (compiled; top-free roots,
   `Continuation/ExactReceivingExamples`), which shows only that determination is not vacuous.
   The cofaces in which the root is a rigid core need only (R1) in the same form
   (`Realization.ResidualReceiving.of_not_isRigidCoreIn`).
6. `Realization.HollowReceiving` for `Realization.IsCoverHollowAtBlock`: still to be proved (the
   growth construction).  Exactly reformulated as exact receiving of all legal types
   (`Realization.hollowReceiving_iff`).  A reduction is compiled: it follows from
   `Realization.HollowAcquisition H P` and `Realization.SchemeDetermination P` with
   `H := Realization.IsCoverHollowAtBlock` (`Realization.hollowReceiving_of_schemeDetermination`,
   no receiving used), for a predicate `P` not yet defined: a template, as in item 5 (for `P`
   always true, acquisition is immediate and determination fails, compiled).  With item 6, the
   count uses (R3) at every cover-hollow model with unbounded growth, a globally rigid core
   included (item 6′ below excludes it).  (R3) forces a globally rigid core of a cover-hollow
   model with unbounded growth to be rigid in every legal donor over its type
   (`Realization.HollowReceiving.isRigidCoreIn`).
7. Nonempty losses: still to be proved.  Compiled conditionally on the coatom extension property
   with apex at every countable block stage and on next-block uniqueness
   (`hasNonemptyLosses_of_hasApexCoatomExtensions`, stated for the bundled domains, which also take
   `CapToModel`; per block, `nonempty_loss_of_hasApexCoatomExtensions`); composed with
   hypotheses 2–6 in the six-hypothesis form, and with hypotheses 2 and 4–6 in the
   five-hypothesis form.
8. `StageType.HasApexCoatomExtensions` at every countable block stage: still to be proved, not
   refuted (Layer 3, 3.1, the open part of (R6); the row "Layer 3, the completion" above).

**An alternative hypothesis set.**
`densitySentence_hasThinAlephOneSpectrum_of_restrictedTerminalClassification`
(`MainTheorem/ModelExpansionDomains`) is compiled conditionally on items 1–5 and 7 of the
seven-hypothesis form and, in place of item 6:

6′. `Realization.HollowReceiving` for `Realization.IsCoverHollowWithoutRigidCoreAtBlock`
   (cover-hollowness at a block stage without a globally rigid core): still to be proved.

Its terminal properties are the restricted ones (`Realization.HasRestrictedTerminalProperty`,
`Continuation/RestrictedHollow`), whose hollow property excludes a globally rigid core; the cover
survives (`Realization.exists_hasRestrictedTerminalProperty`), and the models with a globally rigid
core go through the rigid-core comparison, on (R1) only; the count of the terminal classes
holds in the same form
(`MainTheorem.countable_isoClasses_terminalAt_of_restrictedTerminalClassification`).  Item 6
implies item 6′ (`Realization.HollowReceiving.withoutRigidCore`): weaker or equal; strictly weaker
not shown.  The six- and five-hypothesis forms with item 6′ in place of item 6 are not compiled
(separate compositions, prospective).  An informal argument, not compiled beyond its first step
(`Realization.HollowReceiving.isRigidCoreIn`, item 6 above), is a risk for item 6 and not for
item 6′: if every legal stage type had a legal one-point coface in which the root is not rigid,
item 6 would force every cover-hollow model with unbounded growth to have no globally rigid
core.  Neither is proved, and item 6 is not claimed to be false.

There is no hypothesis of countable losses and none of next-block uniqueness in any form: the
first is `Expansion.expansionDomain_loss_countable`, the second
`Expansion.NextBlockUniqueness.of_forcingDonors`, each compiled conditionally on hypotheses in the
list.

## The research front

Each item is open or still to be proved; none is assumed by a theorem of the library except as a
named hypothesis.

1. **Layer 3 at `m ≥ 3`** (open): the completion below the full grade for every seed at `m ≥ 3`.
   The existential two-face lift `2FL∃(j)` is the step of the tower, stated exactly
   (`Seed.towerInvariant_succ_iff_twoFaceLiftExists`, `Seed.towerInvariant_top_iff`, compiled in
   this repository (theorem named)), and it fails at `j = 2` for the legal seed
   `TwoFaceLiftExistsCounterexample.seedL`
   (`TwoFaceLiftExistsCounterexample.not_twoFaceLiftExists_two_seedL`, refuted), so `2FL∃(j)` for
   every seed is false at every stage
   (`TwoFaceLiftExistsCounterexample.not_forall_twoFaceLiftExists`) and the invariant of the tower
   of `seedL` fails at the top grade
   (`TwoFaceLiftExistsCounterexample.not_towerInvariant_top_seedL`).  The per-grade case split
   `2FL(j) ∨ Seed.DeadAt j` does not cover every seed
   (`CaseSplitCounterexample.not_forall_twoFaceLift_or_deadAt`, refuted), while the seed where it
   fails has a completion (`CaseSplitCounterexample.nonempty_completionBelowFullGrade_seed5`).  No
   theorem is conditioned on the universal form of `2FL∃(j)`.  For `seedL` the identified
   obstruction survives the redesigns examined (argued, not formalized), and `seedL` has a
   completion below the full grade outside the tower, the thin completion
   (`ThinCompletion.nonempty_completionBelowFullGrade_seedL`, compiled in this repository (theorem
   named)), which with the apex added gives the coatom extension of `TL` and `T5` with apex at
   every stage (`ThinCompletionExamples.exists_coatomExtension_seedL`, compiled in this repository
   (theorem named)).  A completion below the full grade for every seed of two legal coatom types
   gives `StageType.HasApexCoatomExtensions` at the stages that are zero or a limit
   (`StageType.HasApexCoatomExtensions.of_completionBelowFullGrade`, compiled in this repository
   (theorem named)), hence the coatom extension hypotheses of the cap-to-model theorem, the top-free
   witnesses, and output 3.  At `m = 3` the ordered-layer step `Seed.OrderedLayerStep` (one new
   cell per graded face of full scope; `README.md`, Layer 3, 3.1, (R6), 2.7) gives the completion
   and holds for `seed4`, `seed5`, `seedL`, its mirror `seedLM` and `seedLL` (compiled in this
   repository (theorem named)); for every seed it is refuted
   (`CrossedCouplingCounterexample.not_forall_hasOrderedLayerStep`, negative special case named):
   the legal seed `CrossedCouplingCounterexample.seedHG` has two opposite forced separations at the
   grade `1`, so every completion of it has two new cells at `(univ, 1)`.  It has one: the
   multi-layer step `Seed.MultiLayerStep` (several new cells per graded face of full scope, rows
   read off cells; `Seed.MultiLayerStep.completion`) holds for it with two new cells at
   `(univ, 1)`, one per forced separation, every field of the completion proved
   (`CrossedCouplingCounterexample.multiLayerStep_HG`,
   `CrossedCouplingCounterexample.nonempty_completionBelowFullGrade_seedHG`, compiled in this
   repository (theorem named)), so the ordered-layer step is strictly stronger than the completion
   (`CrossedCouplingCounterexample.not_forall_hasOrderedLayerStep_of_nonempty`).  The systematic
   family, two copies of the cells at `(C, k)` and `(D, k)` at each `(univ, k)` (the canonical
   multi-layer scheme), is compiled for every seed on five points with forcedness and the lifts
   from the common face.  It completes a seed under named hypotheses, each with its status:
   `Seed.canonicalMultiStep_of_product` assumes the product clause `Seed.CanonicalProduct` at the
   grades 1–4 (a sufficient hypothesis, not a field of the step; refuted at the grade 4 at all six
   compiled seeds, so this form applies at none of them), `hcode` (copy rows coded) and `hpair`
   (copy rows lawful below both coatoms), the last two conditions on the choice of copy rows;
   `Seed.canonicalMultiStep_of_productBelowTop` assumes the product clause at the grades 1–3 only,
   `hcode` and `hpair` at those grades, `Seed.HasBottomApexes` (compiled for all six seeds) and
   `hR3` (the top row at the grade 4, a choice of the copy rows), and takes the grade 4 from the
   grade 3, not from the product clause.  With every hypothesis compiled it completes `seedHG`
   (`Seed.nonempty_completionBelowFullGrade_canonical_seedHG`); all compiled in this repository
   (theorem named).  The product clause is refuted (negative special cases named, for every copy
   rows) at the grades 2–4 for `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL` and at the grade 4 for
   all six seeds: this refutes the family as a fibre product at those seeds, not the family's step
   (which holds for `seedHG` at the grade 4) and not the completion.
   Oriented copy rows (`OrderedLayer.orientedRows`, both copies of a grade reading every old cell by
   the row of an ordered-layer step whose rows are oriented, `OrderedLayer.IsOriented`) restrict the
   pairs to the lawful labellings of the layer scheme (`OrderedLayer.isLawfulBelow_oriented_iff`),
   and under them the step of the family *is* the ordered-layer step
   (`Seed.canonicalMultiStep_oriented_iff`, an exact reformulation: both copies of a grade read
   alike, so the family adds nothing to the layer scheme), with no further hypothesis; compiled in
   this repository (theorem named).  The five seeds `seed4`, `seed5`, `seedL`, `seedLM`, `seedLL`,
   where the product clause fails, were already completed by their ordered-layer steps
   (`Seed.orderedLayerStep_seed4`, `…_seed5`, `…_seedL`, `…_seedLM`, `…_seedLL`); what is new is
   only that the canonical multi-layer scheme itself has a step at them
   (`Seed.nonempty_completionBelowFullGrade_seed4_oriented` and its companions), so all six compiled
   seeds have a step of the family
   (`Seed.hasCanonicalMultiStep_seed4_seed5_seedL_seedLM_seedLL_seedHG`), and no seed refutes it.
   Oriented rows are refuted (negative special cases named; corollaries, through the iff, of
   `CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG` and
   `not_exists_orderedLayerStep_seedL_seedLM`) at `seedHG`
   (`Seed.not_canonicalMultiStep_oriented_seedHG`) and as one choice for `seedL` and `seedLM`
   (`Seed.not_exists_canonicalMultiStep_oriented_seedL_seedLM`): a refutation of oriented rows as a
   choice uniform in the seed, not of the family nor of the completion.  Neither
   compiled sufficient clause (the product clause below the top grade, the oriented ordered-layer
   step) holds at every compiled seed.  Own-side copy rows (`OrderedLayer.ownSideRows`, defined for
   every seed: each copy reads its own coatom's cells as its original does, shifted into a higher
   block, every value other than `⊥` above every value it reads on the other coatom) are refuted
   (negative special cases named) at `seedHG`, `seedL` and `seedLM` (`Seed.not_ownSideStep_seedHG`,
   `…_seedL`, `…_seedLM`, from `Seed.not_ownSideStep_of_forcesTop`): there every step of the
   family, for every copy rows, has a copy forced to read the other way
   (`Seed.MultiLayerStep.copyRows_lt_of_forcesTop`, `Seed.copyRows_lt_two_of_TH_TG`,
   `Seed.copyRows_lt_three_of_TH_TG`, `Seed.copyRows_lt_of_TL_T5`, `Seed.copyRows_lt_of_T5_TL`);
   compiled in this repository (theorem named).  A refutation of the own-side rows, not of the
   family nor of the completion; at `seed4`, `seed5`, `seedLL` the own-side step is undecided (at
   `seed5` a forcing constrains the copies, `Seed.copyRows_lt_of_T5_T5`, but only with `P d₁ = ⊥`
   (argued, not formalized), outside the refutation).  The direction of the shift is a choice: the
   rows first specified were the mirror rows (other side shifted up), reversed to match `rowsHG` at
   the grade 1 (`README.md` 2.7).  Through a cell `d₂` off the own side that the other original
   reads above `⊥`, the necessary condition can refute only rows with the own side above, never the
   mirror rows (argued, not formalized; on the common face it constrains the own original's row),
   which are the next test.  Open: copy rows giving the step of the family for every seed on five
   points (`Seed.HasCanonicalMultiStep` for every seed), which must meet the orientations forced
   on the copies, and the completion at `m ≥ 3` for every seed.
2. **Stable availability at twins** (compiled): from legal types
   (`Realization.availability_stableSection_of_hasLegalTypes`), so every model at a block stage is
   stably lawful (`Realization.IsModel.isStablyLawful`), and so is every exactly consistent
   covering realization with legal types at a block stage
   (`Realization.isStablyLawful_of_hasLegalTypes`).  Refuted hypotheses on single types, negative
   special cases:
   `Continuation.CandidateCounterexamples.not_synchronizingCofaces_blockStage` (with two variants)
   and `Continuation.CandidateCounterexamples.not_twinOrdering_blockStage`.
3. **4b-ii** (open): the gated construction as data, that is,
   `StageType.HasCoupledGatedPinnedExtensions`.  Its first form,
   `StageType.HasGatedPinnedExtensions`, is refuted at every stage
   (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`, compiled in this repository
   (theorem named)).  The coupled form holds at the refuting input
   (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`, compiled in this repository
   (theorem named)) and is open in general.  Its open point is cap lowering (CL), the uniform form
   of what the construction needs, a strengthening not shown necessary: a failure of (CL) refutes
   the coupled design only at a pair that a forcing prescription from an anchored legal donor
   actually realizes.  At a stage where the hypothesis fails the conditional (R1)
   (`Expansion.finiteCutReceiving_of_hasCoupledGatedPinnedExtensions`) is vacuous, and nothing
   rules that out.
   *The attached gate* (a redesign, by step).  An attached gated extension
   (`StageType.AttachedGatedExtension`) has readers of graded index `(univ, n)`, each reading
   every new donor cell through the anchors; the row of the gate is `⊥` at the other twins and
   reads one reader at least as itself; no label of a twin is prescribed.  Compiled in this
   repository (theorem named): recovery through whichever reader availability reaches
   (`CellScheme.Rows.IsLawful.recover_of_readsOnly`); the gate from the bottom-pattern clause
   (`Realization.IsModel.exists_attachedGate`); receiving at a given attached gated extension
   (`Realization.IsModel.realizesOver_receivingFamily_of_attachedGatedExtension`); the lifts its
   legality forces at caps not `⊥` (`StageType.AttachedGatedExtension.exists_lift`; that nothing
   is forced at the cap `⊥` is argued, not formalized); and, a negative special case of a row
   design, at `GatedExtensionCounterexample.P α` the gate's row cannot be `⊥` at every twin but one
   ceiling (`AttachedGateCounterexample.exists_reader`), while two readers are realized there
   (`AttachedGateExamples.attachedGatedExtensionP`, donor labelled `⊤`).  Open: an attached gated
   extension over the private contexts that models acquire; whether availability from the
   literal-face cap must reach a reader other than the ceiling.  (R1) is neither proved nor
   refuted.
4. **Forcing donors** (still to be proved unconditionally): reduced to the coatom extension
   property (`forcingDonors_of_hasCoatomExtensions`); nothing beyond it remains.
5. **Output 3, part D, and (R4)** (still to be proved): (R4) over positive roots, the empty root by
   the coatom extension over the empty face, and the coatom extension properties at `λ_{ξ+1}`; the
   lawfulness of the candidate is item 2.  Compiled conditionally on (R4) and the coface instances:
   `ContinuationCriterion.of_stableCappedReceiving`.  (R4) is not weaker than output 3: under (R1),
   forcing donors and the coface instances they are equivalent
   (`Expansion.stableCappedReceiving_iff_continuationCriterion`).  At one occurrence, (R4) is exact
   receiving in the model of the reduction of the donor, tops included, with the calibration of the
   stable labels at the new cells reducing to the top
   (`Realization.stablyReceivesAt_iff_of_mem_cofaces`); donors with no such cell are received from
   (R1) for the model (`Realization.exists_stableCandidate_eval_eq_of_hasFiniteCutReceiving`).  The
   evaluation step and the acquisition of the marker and cap calibration are compiled; (R4) follows
   from `StageType.HasStableRecoverySchemes` for `StageType.MarkerCapCalibration`
   (`StableCappedReceiving.of_hasStableRecoverySchemes_markerCap`), a finite hypothesis that is
   false at every `ξ`, over a root with no private point and the twins of the five-cell type
   (`Continuation.StableRecoveryCounterexample.not_hasStableRecoverySchemes_markerCap`); (R4) is
   not refuted.  The calibration is weaker than the design of `README.md`, Layer 3, 3.3, and than
   the coupled gate form of (R1) (`StageType.HasCoupledGatedPinnedExtensions`): it lacks the cap of
   full scope and full grade, the reference cells and the arity bound.  The graded cap calibration
   (`StageType.GradedCapCalibration`: a cap of grade `N` above the arity of the root, labelled at
   least `λ_ξ + N`, and reference cells of grade at most `N` with offsets below `N`) excludes that
   instance, its acquisition is compiled
   (`Realization.IsModel.acquiresCalibratedContexts_gradedCap`, from non-hollowness, growth,
   uniformity and covering), and (R4) follows from stable recovery
   schemes for it (`StableCappedReceiving.of_hasStableRecoverySchemes_gradedCap`; open, still to be
   proved).  A scheme that carries a coface of `T⁺↓λ_ξ`, has the scheme of `D` as its face along
   `f` followed by the new point, and has a cell `s` of grade `N`, the grade of a cap labelled at
   least `λ_ξ + N` (with `γ < λ_ξ + N`), whose scope contains the scope of the cap, such that every
   new cell of `D` lies below the graded index of `s` and every cell of that graded index reads the
   new cells through the cap and reference cells, is a stable recovery scheme
   (`StageType.IsStableRecoveryScheme.of_readsThroughCap`, from availability and the decoder at
   one reading cell, `CellScheme.Rows.IsLawful.label_eq_of_reading`).  This reading is not
   confined to one graded index (informal; not compiled: by bountifulness at the cap `⊥` and
   completeness it constrains every graded face of grade `N` containing the cap, a reference cell
   and a new cell).  The existence of such schemes is not proved, and no instance is compiled.  The
   acquisition of the design's cap of full scope and full grade is not compiled.
6. **The attained least lift and structural successor leastness** (prospective).  One lift of a
   legal stage type at a limit stage `β` to `β + ω`, least at every cell (each minimum is attained
   separately: `StageType.exists_lift_label_eq_ofOffset`); the threshold forced by a cover is read
   off that one lift, and the threshold characterization and the limit-stage monotonicity are
   derived from it under that stage hypothesis; the least lift itself rests on the finite row
   algebra and the lawful provisional lift only, not on that monotonicity.  The stable section is
   at most every coherent next-block assignment
   (`README.md`, Layer 3, 3.1, "The attained least lift"; Layer 4, "Status", output 2 refined).
   The structural successors of a consistent realization `R` (the consistent realizations at the
   next block with reduct `R`) lie between the stable candidate, where it is lawful, the least
   (covering used), and literal weakening, the greatest; for a model the two are equal exactly
   when it is cover-hollow (`Realization.IsCoverHollow`).  Least, not unique: literal weakening
   is the greatest lift, a pointwise minimum of lifts need not be lawful, and the twin-ordering
   hypothesis stays refuted.
   None of these makes the candidate a model (output 3, item 5 above), and none gives exact
   lifting over a separately prescribed higher root.  Separate global routes: classical Fraïssé
   existence, Scott isolation with countable-limit existence, terminal presentations, and global
   termination (`README.md`, the section on the top-free witnesses, "Complementary global
   routes"; `IMPLEMENTATION.md`, §4, statements 1–10 with their completion criteria).
7. **The common core of the receiving routes** (open; the labels form refuted).  One hypothesis on
   stage types, prescribed rows at the cells of full scope (`StageType.HasPrescribedFullRows`: over
   legal stage types, every prescription on the rows of the cells of full scope that is
   *compatible with the faces*, i.e. admits, at every lawful labelling of the context, rows that
   are coded, lawful in both faces and transform to that labelling, is met by a legal one-point
   extension), implies parts of the routes' finite hypotheses at inputs where the route's
   prescription is compatible with the faces (`Extension/PrescribedFullRowsRoutes`, compiled in
   this repository (theorems named)); route by route:
   - (R2)/(R3), the reading context of the route to determination with a private top (that route
     is not on `main`): the core with a compatible reading prescription gives a reading context
     (`StageType.HasPrescribedFullRows.isReadingContext`); conversely a reading context makes some
     reading prescription compatible
     (`PrescribedFullRows.IsReadingContext.exists_isFaceCompatible`).
     So, under the core and at a legal input, the reading-context property is equivalent to a
     choice of private tops with a compatible reading prescription.  Obtaining a reading context
     from a graded context with a top, the route's open step, is not derived from the core.
   - (R1): *block-tight saturations* (per block, some scheme on which every coface of the context
     has its cells of full scope of the top grade read the labels of the block in their own block)
     follow from the core only under the compatibility of every block prescription
     (`StageType.HasPrescribedFullRows.hasBlockTightSaturations`), and that hypothesis fails at the
     known refuting context: the block prescription is not compatible wherever the context has a
     lawful labelling `⊥` at a block cell and not `⊥` at a cell of the top grade
     (`PrescribedFullRows.not_isFaceCompatible_block`, compiled), which holds at the per-block
     route's refuting context `CoupledGatedExtensionCounterexample.P α` for every `α > 1` (argued
     from compiled pieces of that route, not on `main`; the joining lemma is to be compiled once
     it lands).  It is not a reduction.
   - (R4): the core with a compatible cap prescription gives a cap-reading scheme
     (`StageType.HasPrescribedFullRows.exists_isCapReadingScheme`), only the part concerning the
     scheme of the sufficient condition for a stable recovery scheme
     (`StageType.IsStableRecoveryScheme.of_readsThroughCap`); the composition with the cap's label
     and the calibration is not compiled here.
   - The completion is not an instance (argued): under the core the coatom extension property is
     equivalent to the compatibility of the empty prescription
     (`StageType.HasPrescribedFullRows.hasCoatomExtensions_iff`), an additional open hypothesis
     (`StageType.HasCompatibleEmptyPrescription`), and the canonical multi-layer step fixes the
     shape of the completion.

   Compatibility is necessary (`StageType.IsPrescribedExtension.isFaceCompatible`, compiled).  The
   form compatible only at the labels of the context is refuted at every stage at
   `GatedExtensionCounterexample.P α`
   (`PrescribedFullRowsCounterexample.not_hasPrescribedFullRowsAtLabels`, refuted); the uniform
   form is not tested by that input, whose compatibility premise fails
   (`PrescribedFullRowsCounterexample.not_isFaceCompatible`), and is open.  A general proof of the
   core first meets the open completion of item 1.  The routes' gaps are unchanged and kept
   separate.
