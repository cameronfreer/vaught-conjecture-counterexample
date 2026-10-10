/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.LevelCarrier

/-!
# The carrier contract at the seed position from the replicated top level

Roadmap, Layer 3 ((R3) and (R4), the growth carrier of the levels re-rendered per grade).

At the seed of `StageType.exists_growthSeed_of_isSuccLimit`, with the seed-fixed choice
`Seed.seedHeightLevel`, `Seed.seedBlockBound'` (one parameter set; only `#attachment ≤ H` is asked
of the height, never `#amalgam ≤ H`), the replicated level at the grade `m + 1`:

* is well formed, consistent, bountiful (`Seed.lvRep_isBountiful_seedChoice'`), and of grade below
  `m + 2` (`Seed.ALvl.Good.rep_grade_lt`);
* carries a lawful labelling extending the labels of the attachment
  (`Seed.hasExtendingLabelLevel_rep`, from `VaughtConjecture.MainTheorem.LevelExtendingLabel`);
* given its codedness and its completeness below the full grade, is legal below the full grade
  (`Seed.ALvl.Good.rep_isLegalBelowFullGrade`), and its completion is a ladder growth carrier
  (`Seed.exists_lvRepCarrier`).

**The contract** (`StageType.hasLadderGrowthCarriersStableAtSeed_of_codedComplete`): the carrier
contract `StageType.HasLadderGrowthCarriersStableAtSeed` follows from the codedness and the
completeness below the full grade of the replicated top level at the seed choice — the two inputs
not proved here.  Every other premise is a binder of the contract (`hpair`, `hrel`, `hQ`, a legal
donor coface, `0 < n`, a limit stage).

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

/-- **Every cell of the replicated level at the grade `m + 1` has grade below `m + 2`**: a cell of
full scope has grade at most `m + 1`, a cell of proper scope at most the size of its scope. -/
theorem rep_grade_lt (z : Fin hN.rep.card) : hN.rep.toCellScheme.grade z < m + 2 := by
  change N.S.toCellScheme.grade (N.S.mirrorOrig (I.mixedFaces g) z) < m + 2
  rcases N.inv (N.S.mirrorOrig (I.mixedFaces g) z) with h | h
  · omega
  · have h1 := hN.wf.isWellFormed.grade_le_card (N.S.mirrorOrig (I.mixedFaces g) z)
    have h2 := card_lt_card (ssubset_univ_iff.mpr h)
    simp only [card_univ, Fintype.card_fin] at h2
    omega

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

end StageType

end VaughtConjecture
