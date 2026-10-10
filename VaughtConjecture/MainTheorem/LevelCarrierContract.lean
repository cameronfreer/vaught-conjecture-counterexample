/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelCarrier
import VaughtConjecture.MainTheorem.SeedLevelTopFacts

/-!
# The carrier contract at the seed position from the replicated top level

Roadmap, Layer 3 ((R3) and (R4), the growth carrier of the levels re-rendered per grade).

**The contract** (`StageType.hasLadderGrowthCarriersStableAtSeed_levels`): the carrier contract
`StageType.HasLadderGrowthCarriersStableAtSeed` holds, with no hypotheses.  Not yet reviewed.

**The premises**, exactly the binders of the contract: a limit stage (`hα : Order.IsSuccLimit α`);
a legal context `t'` on `m + 1` points (`ht'`) with its first coatom `p'`
(`hp' : restrictFace Fin.castSuccEmb t' = some p'`); a root `g : Fin n ↪ Fin m` with root face `p`
(`hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p`) and `0 < n` (`hn`); a legal one-point
coface `d` of `p` (`hd : d ∈ p.cofaces`); and requests `Q` with the labels pair correct (`hpair`),
calibrated on the class (`hQ`) and with the relative lift on the class (`hrel`).  The seed is that
of `StageType.exists_growthSeed_of_isSuccLimit` (first coatom type `t'`, donor the face of the
amalgam along the root and the new point).  The threshold satisfies `2 ≤ Q.threshold` by the arity
(`n + 1 ≤` threshold, `ClassCalibrated.arity`, with `0 < n`) and `Q.threshold ≤ m + 1` by the grade
of the cap in the context (`StageType.GrowthRequests.threshold_le`, from `grade_le_card`), not by
the arity.

**The seed-fixed parameters**: one parameter set at each seed, the height `Seed.seedHeightLevel`
(`#(I.attachmentBase g) + 1`; only `#attachment ≤ H` is asked, never `#amalgam ≤ H`) and the block
bound `B = Seed.seedBlockBound' I g` (`max (2 · #cells + 1) Seed.seedGridBound`).  This one `B`
is used throughout: the level `I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hdA Q m`,
its bountifulness, its mixed lifts and twins, its legality, its labelling and its completion.  Every
use of `B` is a lower bound.  The strict bound `2 · #cells < B` is
`Seed.two_mul_card_lt_seedBlockBound'`, discharged in `Seed.lvRep_isBountiful_seedChoice'` (the
twins of the lifts from the mixed faces, `Seed.lvLevel_twinGen`); the other uses take
`Seed.two_mul_card_le_seedBlockBound'`.

**The route.**
* *Per-level re-rendering* (`Seed.lvLevel`, `Seed.ALvl.next`): the level at the grade `j + 1`
  renders every state through its own orbit code at `j + 1` and the upper decoder
  (`Label.upperDecoderAt`); no state is asked to be a member of a lower catalogue.
* *Per-grade catalogues with recoding* (`Seed.lvCat`): the states in the code grid, canonical for
  the orbit code at the grade and admitted there; the catalogues of different grades are separate.
* *Plain-grid heights*: the rows of the new cells are the sections and the agreement heights in the
  grid `grid (j + 1) B` (`Seed.ALvl.Φ`).
* *Owner-capped repair and restoration*: the state step (`Seed.exists_stateStep_admitted`,
  `Seed.exists_stateStep_level`, with no relation between the grade and the threshold) gives the
  short lifts; `CellScheme.Rows.hasOwnerCappedLifts_of_rows_short` and
  `CellScheme.Rows.cappedLift_of_ownerCappedLift` give the context lift at every grade
  (`Seed.lvLevel_cappedLift`), and the donor lift is `Seed.lvLevel_cappedLift_donor`.
* *Mirror copies* at the mixed faces (`Seed.ALvl.Good.rep`): the lifts from a mixed face
  (`Seed.cappedLift_mirror_mixed_face`, through `Seed.lvLevel_ladderReading`,
  `Seed.lvLevel_shadowAgree`, `Seed.lvLevel_twinGen`), and bountifulness
  (`Seed.lvRep_isBountiful_seedChoice'`).
* *Legality below the full grade* (`Seed.lvRep_isLegalBelowFullGrade_seedChoice'`): coded, complete
  below the full grade, of grades below `m + 2` (`Seed.ALvl.Good.rep_grade_lt`).
* *The labelling* (`Seed.hasExtendingLabelLevel_rep`): lawful, extending the labels of the
  attachment.
* *Completion by `StageType.addApex`* and *recognition transport* (`Seed.exists_lvRepCarrier`,
  `Seed.lvRepCompletion_ladderController`): the completion has `t'` and `d` as literal faces, and
  every cell of full scope at the threshold is a ladder controller.

**The bottom state.**  At the bottom state the levels above the first read the ladder base as gap
values (`Seed.lvLevel_σ_embed_bot`).  Its cell stores `⊥` on the context and donor cells, so its
admission, cap and positive-value clauses hold at once, and its rung clause reads those gap values
through the table `F` taken from its row; the lift at the cap `⊥` is separate
(`Seed.ALvl.Good.hasOwnerCappedLifts_next_bot`).

**Scope.**  The construction and its facts concern the replicated level at the top grade `m + 1`,
not the levels at lower grades at unrestricted source grades.

**Consequences** (compiled implications): (R3) and (R4) through
`StageType.HasLadderGrowthCarriersStableAtSeed.hasLadderGrowthCarriersStable`, and the thin `ℵ₁`
spectrum from (R2) by `MainTheorem.densitySentence_hasThinAlephOneSpectrum_of_stableAtSeed`.

## References

The completion of [Kni26, Definition 4.3.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace StageType

/-- **The carrier contract at the seed position** (`StageType.HasLadderGrowthCarriersStableAtSeed`):
at the seed of `StageType.exists_growthSeed_of_isSuccLimit` and the seed-fixed choice
`Seed.seedHeightLevel`, `Seed.seedBlockBound'`, the completion of the replicated level at the grade
`m + 1` (legal below the full grade, `Seed.lvRep_isLegalBelowFullGrade_seedChoice'`; with the
lawful labelling extending the actual labels of the attachment, `Seed.hasExtendingLabelLevel_rep`)
is a ladder growth carrier whose cells of full scope at the threshold are ladder controllers
(`Seed.exists_lvRepCarrier`).  Every premise is a binder of the contract. -/
theorem hasLadderGrowthCarriersStableAtSeed_levels : HasLadderGrowthCarriersStableAtSeed.{u} := by
  intro α n m t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  obtain ⟨I, rfl, hdA⟩ :=
    exists_growthSeed_of_isSuccLimit hα ht' hp' ((restrictFace_trans t' _ g hp').trans hte) hd
  have hL := Seed.lvRep_isLegalBelowFullGrade_seedChoice' hte hd hn hdA hpair hQ hrel
  obtain ⟨q, hq, hqe⟩ := Seed.hasExtendingLabelLevel_rep (hd := hdA)
    (Seed.seedHeightLevel_pos I g) (Seed.card_attachmentBase_le_seedHeightLevel I g) hQ hpair
    (Seed.two_mul_card_le_seedBlockBound' I g) m (by omega)
  have hN2 : 2 ≤ Q.threshold := by have := hQ.arity; omega
  exact Seed.exists_lvRepCarrier hα.isSuccPrelimit (Seed.seedHeightLevel_pos I g)
    (Seed.card_attachmentBase_le_seedHeightLevel I g) hQ (Seed.two_mul_card_le_seedBlockBound' I g)
    hN2 _ hL hq hqe

end StageType

end VaughtConjecture
