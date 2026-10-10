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

**The premises**, exactly the binders of the contract: a limit stage `α` (`Order.IsSuccLimit α`),
a legal context `t'` on `m + 1` points with its first coatom `p'`, a root `g : Fin n ↪ Fin m` with
`0 < n` and root face `p`, a legal one-point coface `d` of `p`, and requests `Q` with the labels
pair correct (`hpair`), calibrated on the class (`hQ`) and with the relative lift on the class
(`hrel`).  The seed is that of `StageType.exists_growthSeed_of_isSuccLimit` (first coatom type
`t'`, donor the face of the amalgam along the root and the new point).

**The seed-fixed parameters**: one parameter set at each seed, the height `Seed.seedHeightLevel`
(`#(I.attachmentBase g) + 1`; only `#attachment ≤ H` is asked, never `#amalgam ≤ H`) and the block
bound `Seed.seedBlockBound'` (`max (2 · #cells + 1) Seed.seedGridBound`; every use of the block
bound is a lower bound, the strict one `2 · #cells < B` for the twins of the mixed lifts).

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

The conditional form `StageType.hasLadderGrowthCarriersStableAtSeed_of_codedComplete` isolates the
codedness and the completeness below the full grade.

**The bottom state.**  At the bottom state the levels above the first read the ladder base as gap
values (`Seed.lvLevel_σ_embed_bot`); its cell stores `⊥` on the context and donor cells, so its
controller clauses hold trivially, and the lift at the cap `⊥` is separate
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

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

namespace ALvl.Good

variable {N : I.ALvl g H (m + 1)} (hN : N.Good B (lvAdm hd Q))
include hN

/-- **The replicated level at the grade `m + 1` is legal below the full grade** given its
codedness, its bountifulness and its completeness below the full grade. -/
theorem rep_isLegalBelowFullGrade
    (hfaces : N.S.toCellScheme.faces = I.amalgam.toCellScheme.faces)
    (hcoded : hN.rep.IsCoded) (hbount : hN.rep.rows.IsBountiful)
    (hcomp : ∀ X ∈ hN.rep.toCellScheme.gradedFaces, X.2 < m + 2 →
      ∃ z, hN.rep.toCellScheme.gradedIndex z = X) :
    hN.rep.IsLegalBelowFullGrade where
  isWellFormed := hN.isWellFormed_rep hfaces
  isCoded := hcoded
  isConsistent := hN.isConsistent_rep
  isBountiful := hbount
  grade_lt := hN.rep_grade_lt
  exists_gradedIndex_eq := hcomp

end ALvl.Good

/-- The level at the grade `m + 1` at the seed choice is good. -/
theorem seedTopGood (I : Seed.{u} α m) (g : Fin n ↪ Fin m) {d : StageType.{u} α (n + 1)}
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    (Q : GrowthRequests I.left d.toScheme) {p₀ : StageType.{u} α n}
    {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀} (hQ : Q.ClassCalibrated hte) :
    (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hdA Q m).Good (I.seedBlockBound' g)
      (lvAdm hdA Q) :=
  lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
    (two_mul_card_le_seedBlockBound' I g) m (by omega)

end Seed

namespace StageType

/-- **The carrier contract from the codedness and the completeness of the replicated top level**
(see the module docstring): if, at every seed and requests calibrated on the class, the replicated
level at the grade `m + 1` at the choice `Seed.seedHeightLevel`, `Seed.seedBlockBound'` is coded and
complete below the full grade, then `StageType.HasLadderGrowthCarriersStableAtSeed` holds. -/
theorem hasLadderGrowthCarriersStableAtSeed_of_codedComplete
    (hcc : ∀ {α : Ordinal.{u}} {n m : ℕ} (I : Seed.{u} α m) (g : Fin n ↪ Fin m)
      {d : StageType.{u} α (n + 1)}
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
      (Q : GrowthRequests I.left d.toScheme) {p₀ : StageType.{u} α n}
      {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
      (hQ : Q.ClassCalibrated hte),
      (Seed.seedTopGood I g hdA Q hQ).rep.IsCoded ∧
      ∀ X ∈ (Seed.seedTopGood I g hdA Q hQ).rep.toCellScheme.gradedFaces, X.2 < m + 2 →
        ∃ z, (Seed.seedTopGood I g hdA Q hQ).rep.toCellScheme.gradedIndex z = X) :
    HasLadderGrowthCarriersStableAtSeed.{u} := by
  intro α n m t' g p' hα ht' hp' p hte d hd hn Q hpair hQ hrel
  obtain ⟨I, rfl, hdA⟩ :=
    exists_growthSeed_of_isSuccLimit hα ht' hp' ((restrictFace_trans t' _ g hp').trans hte) hd
  have hN := Seed.seedTopGood I g hdA Q hQ
  obtain ⟨hcoded, hcomp⟩ := hcc I g hdA Q hQ
  have hL := hN.rep_isLegalBelowFullGrade (Seed.faces_lvLevel m) hcoded
    (Seed.lvRep_isBountiful_seedChoice' hte hd hn hdA hpair hQ hrel) hcomp
  obtain ⟨q, hq, hqe⟩ := Seed.hasExtendingLabelLevel_rep (hd := hdA)
    (Seed.seedHeightLevel_pos I g) (Seed.card_attachmentBase_le_seedHeightLevel I g) hQ hpair
    (Seed.two_mul_card_le_seedBlockBound' I g) m (by omega)
  have hN2 : 2 ≤ Q.threshold := by have := hQ.arity; omega
  exact Seed.exists_lvRepCarrier hα.isSuccPrelimit (Seed.seedHeightLevel_pos I g)
    (Seed.card_attachmentBase_le_seedHeightLevel I g) hQ (Seed.two_mul_card_le_seedBlockBound' I g)
    hN2 hN hL hq hqe

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
