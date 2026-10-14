/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.CodedLadderContract
import VaughtConjecture.MainTheorem.CodedLevelCarrier
import VaughtConjecture.MainTheorem.CodedLevelExtendingLabel
import VaughtConjecture.MainTheorem.CodedSeedLevelTopFacts

/-!
# The coded ladder carrier of the replicated coded level

Roadmap, Layer 3 ((R3) and (R4), the growth carrier of the levels) and Correspondence, item 1 (the
strongly coded legal stage types).  All results here are native constructions of this repository.

The replicated coded level at the top grade (`Seed.codedLvLevel`, its copies `Seed.ALvl.Good.rep`)
is completed with the strongly coded apex (`Seed.codedLvRepCompletion`, through
`StageType.addStrongApex`).

* `Seed.isStronglyCoded_codedLvRepCompletion`: the completion of a strongly coded replicated level
  is strongly coded (`StageType.isStronglyCoded_addStrongApex`).
* `Seed.codedLvRep_isStronglyCoded`: the replicated coded level is strongly coded when the
  attachment is (`Seed.ALvl.CodedGood.isStronglyCoded_rep`).
* `Seed.exists_codedLadder_codedLvRepCompletion`: the completion, with the first coatom type and
  the donor as literal faces (`Seed.restrictFace_left_codedLvRepCompletion`,
  `Seed.restrictFace_donor_codedLvRepCompletion`), is a coded ladder carrier
  (`GrowthCarrier.CodedLadder`): coded rungs (`Seed.codedLvRepCompletion_rung_rows`), ladder
  controllers (`Seed.codedLvRepCompletion_ladderController`, transported through the strongly coded
  apex by `Seed.addStrongApex_ladderController_of_levelShape`), and strongly coded rows.
* `Seed.hasCodedLadderCarrier_seedChoice`: at the seed-fixed parameters (`Seed.seedHeightLevel`,
  `Seed.seedBlockBound'`), with the hypotheses of
  `StageType.hasLadderGrowthCarriersStableAtSeed_levels` at the seed, the coded ladder carrier
  target `Seed.HasCodedLadderCarrier` holds, through the
  legality below the full grade (`Seed.codedLvRep_isLegalBelowFullGrade_seedChoice'`) and the
  extending labelling (`Seed.hasExtendingLabelLevel_rep_coded`).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **The completion of a strongly coded replicated level is strongly coded** (native
construction): the old rows are those of the replicated level, and the row of the strongly coded
apex is strongly coded at the full grade (`StageType.isStronglyCoded_addStrongApex`). -/
theorem isStronglyCoded_codedLvRepCompletion (hα : Order.IsSuccPrelimit α)
    {N : I.ALvl g H (m + 1)} {hN : N.Good B (lvAdm hd Q)} (hL : hN.rep.IsLegalBelowFullGrade)
    {q : Fin hN.rep.card → Label.{u}} (hq : hN.rep.rows.IsLawful q)
    (hsc : hN.rep.rows.IsStronglyCoded) :
    (codedLvRepCompletion hα hN hL hq).rows.IsStronglyCoded := by
  unfold codedLvRepCompletion
  exact isStronglyCoded_addStrongApex (t := lvRepType hα hN hL hq) hL (Nat.succ_pos _) hsc

/-- **The replicated coded level is strongly coded** (native construction), at every grade up to
the number of points, when the attachment is strongly coded: the level is a coded good level
(`Seed.codedLvLevel_codedGood`) and its copies read the rows of their originals
(`Seed.ALvl.CodedGood.isStronglyCoded_rep`). -/
theorem codedLvRep_isStronglyCoded (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B)
    (hsc : (I.attachment g).rows.IsStronglyCoded) (j : ℕ) (hj : j + 1 ≤ m + 2) :
    (codedLvLevel_good (hd := hd) hH hcard hQ hB j hj).rep.rows.IsStronglyCoded :=
  (codedLvLevel_codedGood hH hcard hsc hQ hB j hj).isStronglyCoded_rep

/-- **The coded ladder carrier of the replicated coded level** (native construction): at a stage
that is zero or a limit, for requests calibrated on the class with threshold at least `2`, a
height `H > 0` bounding the cells of the attachment and `2 · #cells ≤ B`, if the replicated coded
level at the grade `m + 1` is legal below the full grade, strongly coded, and carries a lawful
labelling `q` extending the labels of the attachment, its completion by the strongly coded apex is
a coded ladder carrier with the context `I.left` and the donor `d` as literal faces. -/
theorem exists_codedLadder_codedLvRepCompletion (hα : Order.IsSuccPrelimit α) (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hQ : Q.ClassCalibrated hte) (hB : 2 * (I.attachment g).card ≤ B) (hN2 : 2 ≤ Q.threshold)
    (hNm : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q)) (hL : hNm.rep.IsLegalBelowFullGrade)
    (hsc : hNm.rep.rows.IsStronglyCoded)
    {q : Fin hNm.rep.card → Label.{u}} (hq : hNm.rep.rows.IsLawful q)
    (hqe : ∀ c, q (hNm.repEmb c) = (I.attachmentType g).label c) :
    ∃ (G : GrowthCarrier I.left.toScheme d.toScheme (g.trans Fin.castSuccEmb)) (Mb : Type)
      (H' : ℕ) (r : Mb → ℕ → Fin G.scheme.card),
      G.scheme = (codedLvRepCompletion hα hNm hL hq).toScheme ∧ G.CodedLadder Q H' r := by
  classical
  have hemb := codedLvLevel_embed_strictMono (I := I) (g := g) (H := H) (B := B) (hd := hd)
    (Q := Q) m
  have hground := ground_codedLvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hfaces := faces_codedLvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hleftF : restrictFace Fin.castSuccEmb (codedLvRepCompletion hα hNm hL hq) = some I.left :=
    restrictFace_left_codedLvRepCompletion hα hemb hground hfaces hL hq hqe
  have hdonF : restrictFace (extendByLast (g.trans Fin.castSuccEmb))
      (codedLvRepCompletion hα hNm hL hq) = some d :=
    restrictFace_donor_codedLvRepCompletion hα hemb hground hfaces hL hq hqe
  have hctx := contextCell_codedLvRepCompletion hα hemb hL hq hleftF hdonF
  have hdon := donorCell_codedLvRepCompletion hα hemb hL hq hleftF hdonF
  obtain ⟨w, hw⟩ := codedLvLevel_hexist (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
    Q.threshold hN2 Q.threshold_le
  refine ⟨GrowthCarrier.ofExtension (isLegal_codedLvRepCompletion hα hL hq) hleftF hdonF,
    Scheme.RankMember (I.attachmentBase g).S H, H,
    fun a i ↦ (Fin.castAdd _ ((I.codedLvLevel g H B hd Q m).embed (lvRung hH a i)) :
      Fin hNm.rep.card).castSucc, rfl,
    { fullCell := ⟨(Fin.castAdd _ w : Fin hNm.rep.card).castSucc,
        (gradedIndex_codedLvRepCompletion_castSucc hα hL hq _).trans
          ((hNm.rep_gradedIndex_castAdd w).trans hw)⟩
      rungs :=
        { height_pos := hH
          gradedIndex_rung := fun a i _ ↦
            (gradedIndex_codedLvRepCompletion_castSucc hα hL hq _).trans
              ((hNm.rep_gradedIndex_castAdd _).trans (codedLvLevel_gradedIndex_lad m _))
          rowAt_diag := fun a i hi ↦ (codedLvRepCompletion_rung_rows hα hH hNm hL hq a i hi).1
          rowAt_pred := fun a i hi hi0 ↦
            (codedLvRepCompletion_rung_rows hα hH hNm hL hq a i hi).2 hi0 }
      controller := fun u hu ↦ ?_
      stronglyCoded := isStronglyCoded_codedLvRepCompletion hα hL hq hsc }⟩
  obtain ⟨u', rfl, a, F, hadm, htop, hrung, hval⟩ :=
    codedLvRepCompletion_ladderController hα hH hcard hQ hB hN2 hNm hL hq u hu
  refine ⟨a, F, ?_, ?_, hrung, fun x hx hx0 ↦ ?_⟩
  · simp only [hctx, hdon]
    exact hadm
  · rw [hctx]
    exact htop
  · rw [hctx] at hx0 ⊢
    exact hval x hx hx0

/-- **The coded ladder carrier at the seed choice** (native construction): at a limit stage, for
the hypotheses of `StageType.hasLadderGrowthCarriersStableAtSeed_levels` at the seed (a root `g`
with face `p`, a legal coface `d` of `p` that is the face of the amalgam along the root and the new
point, `0 < n`, requests with the labels pair correct, calibrated on the class and with the
relative lift on the class), the coded ladder carrier target `Seed.HasCodedLadderCarrier` holds:
when both coatom types are strongly coded, the completion of the replicated coded level at the
seed-fixed parameters is a coded ladder carrier. -/
theorem hasCodedLadderCarrier_seedChoice (hα : Order.IsSuccLimit α) {p : StageType.{u} α n}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd' : d ∈ p.cofaces)
    (hn : 0 < n) {Q : GrowthRequests I.left d.toScheme}
    (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd'.2) : I.HasCodedLadderCarrier g Q := by
  intro hdA hl hr
  have hL := codedLvRep_isLegalBelowFullGrade_seedChoice' hte hd' hn hdA hpair hQ hrel
  obtain ⟨q, hq, hqe⟩ := hasExtendingLabelLevel_rep_coded (hd := hdA)
    (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ hpair
    (two_mul_card_le_seedBlockBound' I g) m (by omega)
  have hN2 : 2 ≤ Q.threshold := by have := hQ.arity; omega
  have hsc := codedLvRep_isStronglyCoded (hd := hdA) (seedHeightLevel_pos I g)
    (card_attachmentBase_le_seedHeightLevel I g) hQ (two_mul_card_le_seedBlockBound' I g)
    (I.isStronglyCoded_attachment g hl hr) m (by omega)
  obtain ⟨G, Mb, H', r, -, hG⟩ := exists_codedLadder_codedLvRepCompletion hα.isSuccPrelimit
    (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
    (two_mul_card_le_seedBlockBound' I g) hN2 _ hL hsc hq hqe
  exact ⟨G, Mb, H', r, hG⟩

end Seed

end VaughtConjecture
