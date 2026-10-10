/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SeedLevelDonorLift
import VaughtConjecture.MainTheorem.GrowthStableLadder
import VaughtConjecture.MainTheorem.SeedLevelChoice

/-!
# The coatom lifts of the levels at the strict block bound

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

The lifts of the levels at the seed choice `Seed.seedHeightLevel`, `Seed.seedBlockBound' I g =
max (2 * #attachment + 1) (Seed.seedGridBound I g)` (exceeding twice the number of cells strictly,
`Seed.two_mul_card_lt_seedBlockBound'`), from the lemmas that hold at every block bound
`B ≥ 2 * #attachment` (`Seed.lvLevel_cappedLift'`,
`Seed.lvLevel_cappedLift_iff_of_le`, `Seed.lvLevel_cappedLift_coatom_of_surjective`,
`Seed.ALvl.Good.cappedLift_rep`, `Seed.ALvl.Good.cappedLift_rep_donor`):
* the context lift at every seed (`Seed.lvLevel_cappedLift_seedChoice'`) and with the copies
  (`Seed.lvRep_cappedLift_seedChoice'`);
* the second coatom at an onto root (`Seed.lvLevel_cappedLift_coatom_seedChoice'`) and with the
  copies (`Seed.lvRep_cappedLift_coatom_seedChoice'`);
* at the seed position, with the binders of `StageType.HasLadderGrowthCarriersStableAtSeed`
  (`StageType.lvLevel_cappedLift_coatoms_atSeed'`).

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}
  {p : StageType.{u} α n} {d : StageType.{u} α (n + 1)}

/-- **The context lift of the levels at the strict block bound**, at every seed with the data of
the seed position. -/
theorem lvLevel_cappedLift_seedChoice'
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    ∀ j, j + 1 ≤ m + 1 →
      (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hdA Q j).S.rows.CappedLift
        (X := (univ.erase (Fin.last (m + 1)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  lvLevel_cappedLift' (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hte
    hd.2 hd.1 hn hdA hQ hpair hrel (two_mul_card_le_seedBlockBound' I g)

/-- **The replicated levels at the strict block bound lift from the context coatom**: the level
at the grade `J + 1 ≤ m + 2` with its copies, at every grade `j + 1 ≤ min (J + 1) (m + 1)`. -/
theorem lvRep_cappedLift_seedChoice'
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hpair : ∀ j, Q.CorrectAt I.left.label j (d.label j))
    (hQ : Q.ClassCalibrated hte) (hrel : Q.HasRelativeLiftOnClass hte hd.2) (J : ℕ)
    (hJ : J + 1 ≤ m + 2) (j : ℕ) (hjJ : j ≤ J) (hjm : j + 1 ≤ m + 1) :
    (lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound' I g) (hd := hdA) J hJ).rep.rows.CappedLift
        (X := (univ.erase (Fin.last (m + 1)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  ALvl.Good.cappedLift_rep _ _ rfl subset_rfl
    ((lvLevel_cappedLift_iff_of_le le_rfl _ J hjJ).mpr
      (lvLevel_cappedLift_seedChoice' hte hd hn hdA hpair hQ hrel j hjm))

/-- **The second coatom at an onto root, at the strict block bound.** -/
theorem lvLevel_cappedLift_coatom_seedChoice'
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hg : Function.Surjective g) :
    ∀ j, j + 1 ≤ m + 1 →
      (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hdA Q j).S.rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  lvLevel_cappedLift_coatom_of_surjective (seedHeightLevel_pos I g)
    (card_attachmentBase_le_seedHeightLevel I g) hte hd.1 hn hdA hQ
    (two_mul_card_le_seedBlockBound' I g) hg

/-- **The replicated levels at the strict block bound lift from the second coatom at an onto
root.** -/
theorem lvRep_cappedLift_coatom_seedChoice'
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p) (hd : d ∈ p.cofaces)
    (hn : 0 < n)
    (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hg : Function.Surjective g) (J : ℕ) (hJ : J + 1 ≤ m + 2) (j : ℕ) (hjJ : j ≤ J)
    (hjm : j + 1 ≤ m + 1) :
    (lvLevel_good (seedHeightLevel_pos I g) (card_attachmentBase_le_seedHeightLevel I g) hQ
      (two_mul_card_le_seedBlockBound' I g) (hd := hdA) J hJ).rep.rows.CappedLift
        (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
        (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ :=
  ALvl.Good.cappedLift_rep_donor _ _ rfl (donorFace_eq_coatom_of_surjective g hg).symm.subset
    ((lvLevel_cappedLift_iff_of_le le_rfl _ J hjJ).mpr
      (lvLevel_cappedLift_coatom_seedChoice' hte hd hn hdA hQ hg j hjm))

end Seed

namespace StageType

/-- **The two coatom lifts of the levels at the seed position, at the strict block bound**, with
exactly the binders of `StageType.HasLadderGrowthCarriersStableAtSeed`: at the seed of
`StageType.exists_growthSeed_of_isSuccLimit` and the choice `Seed.seedHeightLevel`,
`Seed.seedBlockBound'`, the context lift at every `j + 1 ≤ m + 1` and, at an onto root, the lift
from the second coatom. -/
theorem lvLevel_cappedLift_coatoms_atSeed' {α : Ordinal.{u}} {n m : ℕ}
    (t' : StageType.{u} α (m + 1)) (g : Fin n ↪ Fin m) (p' : StageType.{u} α m)
    (hα : Order.IsSuccLimit α) (ht' : t'.IsLegal)
    (hp' : restrictFace Fin.castSuccEmb t' = some p') (p : StageType.{u} α n)
    (hte : restrictFace (g.trans Fin.castSuccEmb) t' = some p) (d : StageType.{u} α (n + 1))
    (hd : d ∈ p.cofaces) (hn : 0 < n) (Q : GrowthRequests t' d.toScheme)
    (hpair : ∀ j, Q.CorrectAt t'.label j (d.label j)) (hQ : Q.ClassCalibrated hte)
    (hrel : Q.HasRelativeLiftOnClass hte hd.2) :
    ∃ (I : Seed.{u} α m) (hI : I.left = t')
      (hdA : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d),
      (∀ j, j + 1 ≤ m + 1 →
        (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hdA (hI ▸ Q) j).S.rows.CappedLift
          (X := (univ.erase (Fin.last (m + 1)), j + 1))
          (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩) ∧
      (Function.Surjective g → ∀ j, j + 1 ≤ m + 1 →
        (I.lvLevel g (I.seedHeightLevel g) (I.seedBlockBound' g) hdA (hI ▸ Q) j).S.rows.CappedLift
          (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
          (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩) := by
  obtain ⟨I, rfl, hdA⟩ :=
    exists_growthSeed_of_isSuccLimit hα ht' hp' ((restrictFace_trans t' _ g hp').trans hte) hd
  exact ⟨I, rfl, hdA, Seed.lvLevel_cappedLift_seedChoice' hte hd hn hdA hpair hQ hrel,
    Seed.lvLevel_cappedLift_coatom_seedChoice' hte hd hn hdA hQ⟩

end StageType

end VaughtConjecture
