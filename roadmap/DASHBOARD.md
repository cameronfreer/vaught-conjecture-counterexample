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
| 3, receiving | 90% | `Realization.HasFiniteCutReceiving.hasFiniteExtensionReceiving` | (R1) (4b-ii refuted; the (R1) conditional theorems under it are retired, after an audit of the uses of the refuted hypothesis as well as the calls by name; `IMPLEMENTATION.md`, checkpoint 4); (R2)–(R4) |
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
  (`CellScheme.Rows.IsGate.recover_of_twinsReadGate`); the bottom transport condition that every
  coupled gated extension forces (`StageType.CoupledGatedExtension.carriesBottoms`); the
  refutation of the first form `StageType.HasGatedPinnedExtensions`
  (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`); the coupled form at the inputs on
  `GatedExtensionCounterexample.P α` (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`,
  `CoupledGateInstance.coupledGatedPinnedExtension_donor`, and with every anchored legal one-point
  donor, `CoupledGateOnePointDonors.coupledGatedPinnedExtension_P`); the cap-to-model theorem at a
  limit stage, conditional on the nonemptiness of the instances of uniformity and dominance
  (`Realization.isModel_of_hasFiniteCutReceiving`); the top-free witnesses, steps 1–7,
  conditionally: steps 2–3 under `StageType.HasCoatomExtensions`, and step 7 under
  `StageType.HasApexCoatomExtensions` at `λ_η` and the uniqueness of model expansions at `λ_η`
  (`nonempty_loss_of_hasApexCoatomExtensions`).  Refuted: 4b-ii, the coupled gated pinned extension
  property, at every stage above `1`
  (`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`); the (R1) theorems
  stated conditional on it, vacuous there, are retired.  Undecided:
  the acquisition of carrying private contexts by every model
  (`Realization.AcquiresCarryingContexts`, item 3 below); compiled conditionally: from tight caps
  (`Realization.IsModel.acquiresCarryingContexts_of_hasTightCaps`, not a clause of a model), and
  with the cap one grade below full, a redesign, from the hypothesis on schemes
  `StageType.HasTightSaturations` (`Realization.IsModel.hasCarryingSubfullContext`).  Refuted above
  `ω`, each given a model at a stage above `ω`: `Realization.HasTightCaps` for every model at every
  stage above `ω` (`Realization.IsModel.not_hasTightCaps`; vacuous at the stage `0`, where no floor
  lies below the stage, and open at the stages from `1` to `ω`), and `StageType.HasTightSaturations`
  at every stage above `ω` at which a model exists (`Realization.IsModel.not_hasTightSaturations`),
  so both conditional theorems are vacuous above `ω`; acquisition itself is not refuted, and nothing
  here shows models absent at any stage.  Still to be proved: (R1) by another construction, or by
  the coupled one restricted to carrying private contexts (prospective); (R2), (R3), (R4).
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
  `Realization.IsModel.acquiresCalibratedContexts_gradedCap`), with a stable recovery scheme for
  it at one input at every `ξ`, reading the new cell through the cap
  (`Continuation.StableRecoveryReading.exists_isStableRecoveryScheme_gradedCap`), and at the twin
  donors of the refutation, with one context of three points
  (`Continuation.StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors`), and at four
  further tests: a proper cap and lower blocks
  (`Continuation.StableRecoveryTwinFamily.exists_isStableRecoveryScheme_twinFamily`), a new cell
  labelled `⊤` (`Continuation.StableRecoveryTopCell.exists_isStableRecoveryScheme_topCell`), and
  an interior cap with two graded faces of grade `N`
  (`Continuation.StableRecoveryInterior.exists_isStableRecoveryScheme_interiorCap`);
  cover-hollowness and stable-label fixedness
  (`Realization.isCoverHollow_iff_forall_stableLabel_eq_top`); the exact-age comparison
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
- *Manuscript correspondence, [AFK26] of 7 October.*  The concordance cites the draft of
  7 October 2026; rows 48–56 are new to the concordance, all S.  Adopted there and recorded without a change of
  status: the block indexing of row 1 in §4, the fixed rows of rows 9 and 10, the corrections of
  rows 41 and 42, the cap `-∞` of row 44, and clause 1 of row 45; its range clause of legality is
  now strong coding (row 45).  [AFK26] states Propositions 4.32 (amalgamation of charts, where
  hypothesis 8 enters), 4.34 and 4.35 without proof and sketches Lemma 4.33.  Their counterparts
  here are compiled (the hereditary property, `hereditary_legalAge`, with no hypothesis) or
  compiled conditionally on the hypotheses below, and every compiled form of the main theorem is
  conditional on the five named hypotheses, or on hypotheses derived from them, each still to be
  proved.
- *Acceptance lemma 1 (same-level maximal realization).*  Compiled conditionally on
  `StageType.HasApexCoatomExtensions` at `λ_β` and `ForcingDonors β` (`exists_sameLevelMaximal`).
  Terminality of every cover-hollow realization at a block stage is compiled with no hypothesis
  (`Realization.IsCoverHollow.isTerminalAt`, Layer 4).
- *Manuscript correspondence, item 5.*  Compiled: strictness for models, from modelhood alone
  (`Realization.IsModel.isFixedAt_blockStage_iff`: a model at `λ_η` is fixed by projection at the
  index `ξ` exactly when `η ≤ ξ`, from the uniformity clause); the bound of serving indices,
  given strictness and an index at which every member is fixed
  (`Realization.IsStrict.le_of_forall_isFixedAt`); and the negative special case (`Realization.StrictnessExamples.not_isStrict_undefinedFamily`).  Row 32
  stays S: the uniform fixing stage of the construction it applies to is prospective.
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
2. `Expansion.FiniteCutReceiving`: still to be proved.  The coupled gated pinned extension
   property, under which it was compiled conditionally, is refuted at every stage above `1` (4b-ii,
   `CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`), so that conditional
   was vacuous and is retired; no conditional form of (R1) remains compiled.  It is also used for
   the rigid-core comparison.
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
   still to be proved (no predicate `P` on pairs `(t', h)` is defined in the library, and neither acquisition nor
   determination is proved beyond the rigid-core instance).  For `P` always true, acquisition is
   immediate and determination fails (compiled; top-free roots,
   `Continuation/ExactReceivingExamples`), which shows only that determination is not vacuous.
   The cofaces in which the root is a rigid core need only (R1) in the same form
   (`Realization.ResidualReceiving.of_not_isRigidCoreIn`).  Templates with the donor, compiled
   (`Continuation/AnchoredDetermination`): (R2) follows from (R1) in the same all-limit-stage form,
   `Realization.DonorAcquisition Q P`, and `Realization.CutoffDonorDetermination P`
   (`Realization.residualReceiving_of_cutoffDonorDetermination`).  For the anchored private
   context (`StageType.IsAnchoredContext`), donor acquisition holds in every model
   (`Realization.donorAcquisition_isAnchoredContext`) and cutoff determination with a donor is
   refuted (`AnchoredDeterminationCounterexample.not_cutoffDonorDetermination`: a top-free anchored
   context over the empty root, with the one-point donor labelled `⊤`).  This refutes the
   predicate, not (R2).  A predicate for which determination holds must give, at a limit stage, at
   each non-rigid donor (for legal `t'` satisfying it whose face along `h` has `d` as a legal
   coface), a context that is not top-free, with a top available to a new cell of a coface
   carrying the donor (`Realization.CutoffDonorDetermination.exists_hasAvailablePrivateTop`); a
   rigid context suffices (`Realization.cutoffDonorDetermination_isRigidContext`), but its
   acquisition is not proved.
   With that condition built in (`Continuation/AvailableTopDetermination`), the anchored context
   with a top (`StageType.IsAnchoredContextWithTop`; in a legal coface an available private top
   is any top of the context, `StageType.hasAvailablePrivateTop_iff_not_isTopFree`): donor
   acquisition holds in the models with no globally rigid core under the coatom extension property
   at every limit stage, which is still to be proved and gives the coface carrying the donor
   (`Realization.donorAcquisition_isAnchoredContextWithTop`); cutoff determination with a donor is
   refuted (`AvailableTopDeterminationCounterexample.not_cutoffDonorDetermination`: a context
   whose tops have grade 1, a donor with a new top of grade 2).  This refutes the predicate, not
   (R2).  For a predicate for which determination holds, at a limit stage, over a legal context
   satisfying it at a non-rigid donor (a legal one-point coface of the face of the context along
   `h`), the top grade of the context is at least the grade of every new top of the donor
   (`Realization.CutoffDonorDetermination.grade_le_topGrade`,
   `Realization.CutoffDonorDetermination.topGrade_le`).  For the graded predicate
   (`StageType.IsGradedTopContext`), residual donor acquisition for the donors of top grade at
   most `K` holds under the coatom extension property at every limit stage
   (`Realization.residualDonorAcquisition_isGradedTopContext`) and determination is open (it holds
   at a compiled instance, and over a coface that reads the new tops as a private top,
   `Realization.cutoffDonorDetermination_isReadingContext`); so (R2) is compiled conditionally on
   (R1) in the stronger form above, the coatom extension property at every limit stage, and that
   open determination statement
   (`Realization.residualReceiving_of_cutoffDonorDetermination_isGradedTopContext`), a template.
6. `Realization.HollowReceiving` for `Realization.IsCoverHollowAtBlock`: still to be proved (the
   growth construction).  Exactly reformulated as exact receiving of all legal types
   (`Realization.hollowReceiving_iff`).  A reduction is compiled: it follows from
   `Realization.HollowAcquisition H P` and `Realization.SchemeDetermination P` with
   `H := Realization.IsCoverHollowAtBlock` (`Realization.hollowReceiving_of_schemeDetermination`,
   no receiving used), for a predicate `P`: a template, as in item 5.  One predicate for (R3) is
   defined (the marked-cap context, below), with acquisition and determination open; for `P`
   always true, acquisition is immediate and determination fails (compiled).  With item 6, the
   count uses (R3) at every cover-hollow model with unbounded growth, a globally rigid core
   included (item 6′ below excludes it).  (R3) forces a globally rigid core of a cover-hollow
   model with unbounded growth to be rigid in every legal donor over its type
   (`Realization.HollowReceiving.isRigidCoreIn`).
   *A candidate predicate* (`Stage/MarkedCap`, `Continuation/MarkedCap`): the marked-cap context
   `StageType.IsMarkedCapContext` (defined in this repository; acquisition and determination open),
   a context with a top cap `c` (full scope, labelled `⊤`, at the top grade `N > n + 1`), a marker
   `r` (least entry of the row of `c` at the cells labelled `⊤`), and `visibilityReplace N (n + 1)
   (row c r) ≤ row c a` at every cell `a` of the root labelled `⊤`; with reference cells for a
   donor, `StageType.IsAnchoredMarkedCapContext` (defined in this repository).  Cover-hollowness
   reads the tops through forcing, and forcing is read by the rows (compiled in this repository
   (theorem named): `StageType.ForcesThreshold.le_grade_and_visibilityReplace_rowAt_le`, and at a
   cover-hollow realization with legal types
   `Realization.IsCoverHollow.exists_forcesThreshold_rowAt`): for a legal rooted cover at a limit
   stage `β`, with its lifts at `β + ω`, that forces `L` at a top of its root, `L ≤ N` and the row
   inequality at `L` hold for every top cap and marker.  When the forcing comes from the order law
   or from rows, the inequality already follows from the minimality of the marker; its content is in
   thresholds forced by all lifts otherwise, which no compiled instance exhibits.  The proof is a
   lawful lift whose labels at the tops are the band map of the row of the top cap from the block
   of the marker (`StageType.IsMarker.exists_lift`); its locality is the two-witness splice of
   Layer 3, 3.1 (`Label.TransformsTo.splice_bandMap`, compiled in this repository (theorem
   named)).  `GatedExtensionCounterexample.P α` is a marked-cap context over the empty root
   (compiled).  The finite step of acquisition is compiled
   (`StageType.isMarkedCapContext_of_forcesThreshold`); one cover of top grade above `n + 1` forcing
   `n + 1` at every top of a root at once is prospective, and `Realization.HollowAcquisition` and
   `Realization.SchemeDetermination` for the predicate are open, so item 6 is not reduced.  The
   three refuted determination statements are excluded: the empty root of the apex point and the
   capped two-point context refuting the anchored context (`StageType.IsAnchoredContext`) are
   top-free (compiled in this repository (theorem named)), and the context refuting the anchored
   context with a top (`AvailableTopDeterminationCounterexample`) has top grade at most `1` over a
   root on one point (the exclusion of every such context compiled in this repository (theorem
   named); the bound on that context is proved there as a private statement).
   The template with the
   donor (`Realization.hollowReceiving_of_cutoffDonorDetermination`, any `H`, with (R1) in the
   stronger form of item 5) gives nothing for the anchored context: donor acquisition holds for it
   and cutoff determination with a donor is refuted for it, as in item 5; nor for the anchored
   context with a top, refuted as in item 5.  For the graded predicate, donor acquisition holds in
   every model satisfying `H` with unbounded growth under the coatom extension property at every
   limit stage (`Realization.donorAcquisition_isGradedTopContext`) and determination is open, as in
   item 5 (`Realization.hollowReceiving_of_cutoffDonorDetermination_isGradedTopContext`, any `H`,
   a template).
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

**The hypotheses by property of the tower** (`README.md`, "The tower and its four properties").
The seven-hypothesis form above, grouped by the property of the tower of model expansions that
each hypothesis serves. The six- and five-hypothesis derivations and the separate restricted-R3
form are retained as stated above; no hypothesis, status, or percentage changes.

| Property of the tower | Named hypotheses (numbered as above) |
| --- | --- |
| the bottom of the tower, `D₀ = Q` | 1, `CapToModel` |
| (R) reconstruction | 3, forcing donors, with 2, (R1), through next-block uniqueness |
| (L) coherent limits | none: compiled with no hypothesis (`Realization.IsModel.glue`) |
| (D) projected extension | 2, (R1) |
| (T), terminal existence | 7, nonempty losses, with (R) placing each witness in its loss |
| (T), terminal countability | 4, the continuation criterion; 5, (R2); 6, (R3); 2, (R1) |

In the last row (R1) serves the rigid-core comparison.  Terminal countability is not used by the
lower bound, and enters no statement of terminal refinement (conditionally compiled at universe
zero under (R1), next-block uniqueness, and apex at every countable block stage).

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
   Profile catalogues (`Extension/ProfileCatalogue`, `Extension/ProfileCatalogueExamples`;
   compiled in this repository (theorem named) unless marked otherwise; a test of one scheme, not
   of the completion, `StageType.HasApexCoatomExtensions` or hypothesis 8): one new cell at
   `(univ, j)` per normalized profile (a labelling of all the cells of the amalgam, values in a
   fixed bounded value set `Label.grid k N`) lawful on the grade-`j` cut, rows by agreement heights
   of whole profiles (`ProfileCatalogue.profileScheme`, literally a `multiLayerScheme`).  Two
   departures from the intended construction: agreement heights instead of a selected section on
   the lower new cells, and a fixed grid instead of the rank-normalized patterns of `README.md`
   2.5; so the construction as intended is neither confirmed nor refuted.  At every seed of `TL` and
   `T5`, with the *ambient labelling* the lawful labelling whose capped observation a capped lift
   keeps: with catalogues at the grades 1 and 2 only, at the configuration of the seedL refutation
   (a tie at `({3}, 1)`, `({4}, 1)`, the cap `4` the ambient label at `({0, 1, 2}, 3)`, the
   prescription `(ω + 1, ⊤, ⊤)` on `C`), the capped lift from `(C, 3)` fails and the refutation
   transfers (`ProfileCatalogue.not_exists_lift_two`, `ProfileCatalogue.not_cappedLift_two`,
   negative special case named); with the catalogue at the grade 3 added, that ambient is excluded
   (`ProfileCatalogue.not_isLawfulBelow_three`).  That the rows at the grade 3 see the cap in
   general is argued from these two, not compiled; `ProfileCatalogue.not_exists_lift_two` refutes,
   as stated, the diagnosis that the values of grade-2 profiles at `({0, 1, 2}, 3)` remove the
   obstruction.  A configured lift at the tie profile with its own cap `3` exists for every top
   layer `J ≤ 3` and bound `N ≥ 3` (`ProfileCatalogue.exists_lift_tie`; not the refuted
   configuration, and not the lift at every ambient); at `N = 1`, `J = 3` it fails
   (`ProfileCatalogue.not_exists_lift_tie_one`; for every `J ≥ 2`,
   `ProfileCatalogue.not_exists_lift_tie_one_of_two_le`), `N = 2` is open.
   With the grade-3 catalogue the scheme still does not lift capped from `(C, 3)`, at the top of its
   bounded value set (`ProfileCatalogue.not_cappedLift_three`, negative special case named; the
   flat catalogue over a fixed alphabet also fails at the top of its alphabet,
   `SmallArityExamples.not_cappedLift_flatRows`, proved separately, with different combinatorics,
   and neither failure is derived from the other).  Normalization by rank, leaving room above every
   value, is a proposed repair (prospective) until its preservation properties compile.  Of the
   fields of `Seed.MultiLayerStep`: `pos` fails by construction for every `J ≤ 3` (no cell at
   `(univ, 4)`), `row_lt`, `isLawfulBelow_row` and `exists_isLawful` are not proved,
   `cappedLift_left` at `k = 3` is refuted for `J = 2, 3` and every other lift is not proved, so
   neither scheme is a completion as it stands.  `seedHG`: the grade-1 catalogue has both forced
   separations (`ProfileCatalogue.exists_separating_cells_seedHG`).  The completion at `m ≥ 3` for
   every seed and hypothesis 8 stay open.
2. **Stable availability at twins** (compiled): from legal types
   (`Realization.availability_stableSection_of_hasLegalTypes`), so every model at a block stage is
   stably lawful (`Realization.IsModel.isStablyLawful`), and so is every exactly consistent
   covering realization with legal types at a block stage
   (`Realization.isStablyLawful_of_hasLegalTypes`).  Refuted hypotheses on single types, negative
   special cases:
   `Continuation.CandidateCounterexamples.not_synchronizingCofaces_blockStage` (with two variants)
   and `Continuation.CandidateCounterexamples.not_twinOrdering_blockStage`.
3. **4b-ii** (refuted): the gated construction as data, that is,
   `StageType.HasCoupledGatedPinnedExtensions`, is false at every stage above `1`
   (`CoupledGatedExtensionCounterexample.not_hasCoupledGatedPinnedExtensions`, compiled in this
   repository (theorem named)).  The input: a legal private type on two points with a proper anchor
   below the cap (a cell of grade `1` labelled `1`), the empty root, and a legal donor on one point
   with two cells.  Every coupled gated extension forces the bottom transport condition
   `StageType.CarriesBottoms` (`StageType.CoupledGatedExtension.carriesBottoms`): a lawful private
   labelling is the private face of a lawful labelling of the display (bountifulness at the cap
   `⊥`), and the one witness at the gate carries its values at the anchors, through `vr_n`, to the
   donor face.  The private labelling that drops the anchor and keeps the cap is carried to a donor
   labelling that the donor's rows forbid.  Only the clauses of a coupled gated extension are used,
   not cap lowering (CL), so the refutation holds whatever the display.  Its first form,
   `StageType.HasGatedPinnedExtensions`, is refuted at every stage
   (`GatedExtensionCounterexample.not_hasGatedPinnedExtensions`).  The coupled form is compiled at
   inputs without a proper anchor, on `GatedExtensionCounterexample.P α`, whose labels are `⊥` and
   `⊤` (`CoupledGateExamples.exists_coupledGatedExtension_comap_g₁`,
   `CoupledGateInstance.coupledGatedPinnedExtension_donor`, and with every anchored legal one-point
   donor, `CoupledGateOnePointDonors.coupledGatedPinnedExtension_P`).  The (R1) theorems stated
   conditional on the property were vacuous and are retired.  (R1) itself is not refuted.  The
   condition holds when the cap reads an anchor of every donor label below it in
   the block of its reading of the cap itself (`StageType.carriesBottoms_of_row_mem_block`); it is
   necessary for the property, not shown sufficient.  **Acquisition, the first step of a repair**
   (undecided): whether every model acquires carrying private contexts
   (`Realization.AcquiresCarryingContexts`, stated in `Realization/CarryingContext`: over every
   root, for every coface and floor, a private context of the acquired form satisfying the
   condition).  Compiled: for donors whose new cells are labelled `⊥` or `⊤`
   (`Realization.IsModel.hasCarryingPrivateContext_of_forall_label`); necessity for the coupled
   route (`Realization.hasCarryingPrivateContext_of_coupledGatedExtension`); the refuting input
   satisfies the finite stage-type and label conditions of the acquisition output, with `N₀ ≤ 2`,
   and fails the condition
   (`CoupledGatedExtensionCounterexample.exists_privateContext_not_carriesBottoms`; no occurrence
   in an actual model is exhibited); and, of the cells that the cap's row reads at ordinals, a
   lawful private labelling that keeps the cap drops only those read in a block strictly below its
   reading of itself (`CellScheme.Rows.IsLawful.lt_row_self_of_eq_bot`).  The existing acquisition
   proof does not establish control of the cap's row jointly with its label above the floor
   (generalized saturation prescribes a whole scheme when its nonemptiness guard holds);
   acquisition from the full model axioms is undecided.
   **Where acquisition stands** (`Realization/TightCap`).  At full grade no clause of a model asks
   for a tight cap (one that reads, in its own block, every label of the root at most the floor and
   not self-visible at its grade).  Compiled: every nonempty instance of generalized saturation or
   of the bottom pattern has a member labelled `⊥` at every cell of full grade, hence in no
   dominance family (`StageType.exists_mem_cofaces_inter_saturationFamily_not_mem_dominanceFamily`,
   `StageType.exists_mem_cofaces_inter_bottomPatternFamily_label_eq_bot`); a member of a dominance
   family need not carry
   (`CoupledGatedExtensionCounterexample.exists_mem_dominanceFamily_not_carriesBottoms`, a
   refutation of that finite sufficient condition, not of acquisition; no occurrence of it in a
   model is exhibited).  Compiled conditionally: a model with tight caps acquires carrying contexts
   (`Realization.IsModel.acquiresCarryingContexts_of_hasTightCaps`); `Realization.HasTightCaps`,
   dominance with the row of the dominating cell constrained, is not a clause of a model; it is
   refuted for every model at every stage above `ω` (`Realization.IsModel.not_hasTightCaps`,
   compiled, given a model at a stage above `ω`), so that theorem is vacuous above `ω`; at the stage
   `0` `HasTightCaps` and acquisition hold vacuously (no floor lies below the stage), and
   `HasTightCaps` is open at the stages from `1` to `ω`.  One grade below full, availability gives a
   cell with a prescribed row and a label above the floor
   (`StageType.exists_le_label_of_restrictFace`, compiled): that is the position of the gate, so a
   private cap there is a redesign of the private context, not a repair of the coupled property,
   which asks for a cap of full grade.  Compiled conditionally on the hypothesis on schemes
   `StageType.HasTightSaturations` (a legal one-point extension scheme whose cells of full scope and
   grade one below full read the proper labels of the face in their own block): every model has,
   over every root, for every donor and floor, a carrying context with a cap one grade below full
   (`Realization.IsModel.hasCarryingSubfullContext`, with `StageType.CarriesBottomsAt` at that
   grade).  `HasTightSaturations` is false at every stage above `ω` at which a model exists
   (`Realization.IsModel.not_hasTightSaturations`, compiled, given a model at a stage above `ω`), so
   that theorem is vacuous above `ω`; it is undecided at stages ≤ `ω`.  That theorem constructs no
   extension in the redesign and does not prove (R1).  **The obstruction**: if a cell reads in its
   own block two labels below its own, neither self-visible at its grade, the two lie in one block
   (one is a visibility replacement of the other;
   `StageType.eq_visibilityReplace_of_readsInOwnBlock`, compiled, with
   `StageType.tightCapFamily_eq_empty`).  So reading anchors in the cap's own block can serve only
   donors whose proper labels below the cap, not self-visible at the cap's grade, lie in one block
   (argued, not compiled: when the grade of the cap exceeds the finite parts of the donor's labels,
   every proper donor label below the cap, and its anchor, is not self-visible at that grade; the
   bound is by the grade of the cap, not the arity of the context), and the identified obstruction
   survives the redesigns examined (the cap of full grade and the subfull cap).  It says nothing
   about other ways to obtain the bottom transport condition: acquisition,
   `Realization.HasCarryingSubfullContext` and (R1) are neither proved nor refuted.  The two vacuous
   conditional theorems are kept; retiring them is a separate change.  No extension property for
   that design is defined.  The coupled property restricted to carrying contexts is not stated
   (prospective).
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
   and a new cell).  Such a scheme is compiled at one input, at every `ξ`
   (`Continuation.StableRecoveryReading.exists_isStableRecoveryScheme_gradedCap`): a context of two
   points with a cap of grade `2` labelled `⊤` and the marker `λ_ξ + 1` as reference cell, a root of
   one point, and a donor with a new cell labelled `λ_ξ + 1`, on a legal scheme of ten cells whose
   cell at `(univ, 2)` reads the new cell and the marker at one value; the cap decodes the new cell
   (`Continuation.StableRecoveryReading.IsReadingTriple.eq_of_lt`), and below the marker leaves it
   free (`Continuation.StableRecoveryReading.isReadingTriple_of_le`, for labels self-visible at
   `1` and a cap self-visible at `2`).  So the hypotheses of `of_readsThroughCap` are satisfiable
   with a proper new label (there the reading constrains no other graded face: `(univ, 2)` is the
   only graded face of grade `2` containing both the cap and the new cell).  The input is
   degenerate, so this is feasibility at the smallest sizes only: recovery copies the marker (in
   every lawful labelling with the marker at the reference cell and `⊤` at the cap the new cell
   equals the marker; `n = i = 1`, `c = 0`); no label of `D` is `⊤`, so the clause on `γ` and the
   branch at `⊤` of `StageType.ReadsThroughCap` are not used; the root is one cell labelled `⊥`;
   and `N = k + 1`.  **The twin donors** of `Continuation.StableRecoveryCounterexample` need a
   context of at least three points
   (`Continuation.StableRecoveryTwin.three_le_of_gradedCapCalibration`); with one context of three
   points (the root `λ_ξ + 2` as reference cell, a cap of grade `3` labelled `⊤`) and `γ = λ_ξ` the
   calibration holds for both donors, and each has a stable recovery scheme
   (`Continuation.StableRecoveryTwin.exists_isStableRecoveryScheme_twinDonors`): a legal scheme on
   four points with twenty-three cells (`Continuation.StableRecoveryTwin.isLegal_twinScheme`), whose
   cell at `(univ, 3)` reads the root and the higher twin at `2` and the lower twin at `1` (so
   `n = 1 ≠ i = 2` for the lower twin).  Bountifulness constrains the reading in two places
   (informal; not compiled as necessity statements): a pair of cells reading the twins in both
   orders at each graded face of grade `1` containing them, and the cap reading the root at the
   offset of the reading cell.  No scheme serves both donors
   (`Continuation.StableRecoveryTwin.not_isStableRecoveryScheme_twinDonor₁_and_twinDonor₂`): the
   scheme depends on the donor.  This is a fact about `StageType.IsStableRecoveryScheme` alone, not
   an obstruction: `StageType.HasStableRecoverySchemes` chooses the scheme after the donor, and the
   growth construction of Layer 3, 3.4, builds its scheme from the donor by design.  So the finite
   statement is not refuted where the marker and cap calibration is.  Still special: no label `⊤` in
   the donors (the clause on `γ` unused), the cap `⊤`, the higher twin copying the reference,
   references in the block `λ_ξ` only, `(univ, 3)` the only graded face of grade `N = 3` containing
   the cap and the new cells (several need a context of at least four points; informal; not
   compiled), and the reference cell the root itself (a cell of the face along `f`; the private
   context supplies only the cap).  **Four further tests**, each positive, none a refutation: (b) a
   proper cap, the twin schemes with the cap labelled exactly `λ_ξ + 3 = λ_ξ + N` and `γ = λ_ξ + 2`
   (`Continuation.StableRecoveryTwinFamily.exists_isStableRecoveryScheme_properCap`; every cap
   `C ≥ λ_ξ + 3` and `γ < λ_ξ + 3`,
   `Continuation.StableRecoveryTwinFamily.exists_isStableRecoveryScheme_twinFamily`): no clause of
   `ReadsThroughCap` carries the cap's label, which enters only through `λ_ξ + N ≤ T⁺ b` (the order
   law, `StageType.coe_add_grade_le_label`) and `γ < λ_ξ + N`; (a) a donor with a new cell labelled
   `⊤`, under the cap `λ_ξ + 2` with `γ = λ_ξ + 1`
   (`Continuation.StableRecoveryTopCell.exists_isStableRecoveryScheme_topCell`): the branch at `⊤`
   and the clause on `γ` are used, and the `⊤` cell is recovered as exactly `λ_ξ + 2`
   (`Continuation.StableRecoveryTopCell.label_newCap_eq`); (c) a lower block, references and twins
   `μ + 2, μ + 1` with `μ < λ_ξ`
   (`Continuation.StableRecoveryTwinFamily.exists_isStableRecoveryScheme_lowerBlock`); (d) an
   interior cap (scope without extreme points of the context; four points needed, informal; not
   compiled): every stable recovery scheme then has a face other than its ground set containing the
   cap and the new point (`StageType.IsStableRecoveryScheme.exists_face_ne_univ`), so two graded
   faces of grade `N` contain them (informal; not compiled), and a legal scheme of thirty-five cells
   with a reading cell at both, the reading constraints agreeing across the two faces, is a stable
   recovery scheme, for every cap value `B ≥ λ_ξ + 2` and `γ < λ_ξ + 2`
   (`Continuation.StableRecoveryInterior.exists_isStableRecoveryScheme_interiorCap`).  So reading
   through the cap at two faces does not obstruct the finite statement at that input, and no second
   calibration is refuted.  Still special: recovery copies the marker in (a) and (d), `N = k + 1`
   there, the twin tests read one block through the root, the faces at the interior cap are nested,
   and the four features are tested separately.  The next tests (prospective): the features together
   (an interior cap with the twin donors, a `⊤` cell at an interior cap), faces of grade `N` that
   are not nested, reference cells in two blocks for one donor, and `N > k + 2`.  The finite
   statement at every input with the calibration is still to be proved, and with it (R4).  The
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
   - (R2)/(R3), the reading context of the route to determination with a private top
     (`StageType.IsReadingContext`, `Continuation/AvailableTopDetermination`): the core with a
     compatible reading prescription gives a reading context in its prescribed-row interface
     (`StageType.HasPrescribedFullRows.isReadingContext`); conversely a reading context makes some
     reading prescription compatible
     (`PrescribedFullRows.IsReadingContext.exists_isFaceCompatible`).
     The composition of that interface with the determination templates is not compiled here.
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

## Composition targets and compiled ingredients

Recorded in `IMPLEMENTATION.md`, "The full-presentation route", "Composition targets of the
tower", and in `README.md`, item 5 of "Manuscript correspondence (required)"; no hypothesis,
status, or percentage changes.  The unimplemented assemblies remain prospective and use the
named conditionally compiled ingredients; the niceness consequence in item 3 is already
conditionally compiled:

1. the terminal-presentation instance of the second endpoint, with the main theorem by that route
   on the hypotheses of its current composed form (five: (R1), the continuation criterion, (R2), block
   cover-hollow (R3), and the coatom extension property with apex at every countable block stage;
   the seven/six forms and separate restricted-R3 form are retained), with no termination statement;
2. the four conditions of the system of [AFK26] as one structure of statements, and an abstract
   assembly that may assume
   its conditions (a), (b), and (d) (condition (c), niceness, is not used), distinct from the
   concrete composition that must derive those conditions from the five hypotheses;
3. niceness of base reducts from maximal refinement, conditionally compiled for carriers in
   `Type` under (R1), next-block uniqueness, and apex at every countable block stage; in universe
   `w`, the compiled niceness theorem retains `HasTerminalRefinement.{w}` plus next-block uniqueness;
4. the last admitted stage: the stage of a terminal expansion of a base is the last stage of its
   class, the terminal classes at a block are the loss there, and the tails of the instance of 1
   are the expansion domains (these identifications remain prospective; last-stage attainment
   and its loss fibres are already compiled under `CapToModel`, next-block uniqueness, (R1),
   and apex at every countable block stage);
5. fixing bounds from the Scott bound, and the lower bound along fixing ranks through strictness.

`IMPLEMENTATION.md`, "Manuscript concordance", records separately the retargeting of the
legal-template rows to the current draft of [AFK26] and the identification of its templates with
the stage types (targets; no status changes).
