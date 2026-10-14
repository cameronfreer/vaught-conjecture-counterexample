/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.SeedLevelDonorLift
import VaughtConjecture.MainTheorem.CodedLevelChain

/-!
# The donor lifts of the coded levels

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.SeedLevelDonorLift` about the levels over the padded
grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of `VaughtConjecture.MainTheorem.SeedLevelDonorLift`,
with the facts of the padded base replaced by those of the coded base
(`VaughtConjecture.Extension.CodedLadderBase`, `VaughtConjecture.Extension.CodedLadderLift`) and the
coded mirror lifts (`VaughtConjecture.MainTheorem.CodedMirrorLift`); the statements there that do
not mention the levels or the base are used unchanged.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m}

/-! ### The next level from the donor face -/

namespace ALvl.Good

variable {j : ℕ} {H B : ℕ}
  {N : I.ALvl g H (j + 1)} {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
  {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

variable (hN : N.Good B (lvAdm hd Q))
include hN

end ALvl.Good

/-! ### The levels from the donor face, and from the second coatom at an onto root -/

/-- **The first level lifts from the donor face at the grade one** (the ladder base,
`Scheme.cappedLift_codedLadderBase_rankMember` with `Seed.cappedLift_attachment_univ_one`). -/
theorem codedLvLevel1_cappedLift_donor_one {H : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)))) :
    (I.codedLvLevel1 g H).S.rows.CappedLift
      (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), 1))
      (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨subset_univ _, le_rfl⟩ :=
  Scheme.cappedLift_codedLadderBase_rankMember (hS := (I.attachmentBase g).noFull)
    (I.attachmentBase g).wf hH hcard _
    (fun h ↦ map_extendByLast_ne_univ g (univ_subset_iff.mp h.1))
    (cappedLift_attachment_univ_one hdF hrF hr1 hdF (by simp) (.inr subset_rfl))

/-- **The levels lift from the donor face at every grade `j + 1 ≤ n + 1`**, for requests
calibrated on the class over a legal donor with a nonempty root (no labels pair, no relative
lift): at the grade one the ladder base (`Seed.codedLvLevel1_cappedLift_donor_one`), then the next
level (`Seed.ALvl.Good.cappedLift_next_donor`). -/
theorem codedLvLevel_cappedLift_donor {H B : ℕ} (hH : 0 < H) (hcard :
    (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hdL : d.IsLegal)
    (hn : 0 < n) (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ n + 1 → (I.codedLvLevel g H B hd Q j).S.rows.CappedLift
      (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), j + 1))
      (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨subset_univ _, le_rfl⟩
  | 0, _ => codedLvLevel1_cappedLift_donor_one hH hcard (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; exact hn)
  | j + 1, hj => by
    have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding g
    have hN := codedLvLevel_good (B := B) (hd := hd) hH hcard hQ hB j (by omega)
    have hlow := codedLvLevel_cappedLift_donor hH hcard hte hdL hn hd hQ hB j (by omega)
    have hlift := (ALvl.cappedLift_nS_iff (B := B) (I.codedLvLevel g H B hd Q j)
      (I.lvCat g B hd Q (j + 2)) _ fun h ↦ absurd h.2 (by simp only; omega)).mpr hlow
    exact hN.cappedLift_next_donor hdL hn hQ (by omega) hB hlift

/-- **At an onto root the levels lift from the second coatom at every grade `j + 1 ≤ m + 1`**:
the second coatom is the donor face (`Seed.donorFace_eq_coatom_of_surjective`) and `m ≤ n`. -/
theorem codedLvLevel_cappedLift_coatom_of_surjective {H B : ℕ} (hH : 0 < H)
    (hcard : (I.attachmentBase g).S.card ≤ H) {p₀ : StageType.{u} α n}
    {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀) (hdL : d.IsLegal)
    (hn : 0 < n) (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hB : 2 * (I.attachment g).card ≤ B) (hg : Function.Surjective g) :
    ∀ j, j + 1 ≤ m + 1 → (I.codedLvLevel g H B hd Q j).S.rows.CappedLift
      (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1))
      (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  intro j hj
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_surjective g hg
  have hl := codedLvLevel_cappedLift_donor hH hcard hte hdL hn hd hQ hB j (by omega)
  have key : ∀ (W : Finset (Fin (m + 2)))
      (h : ((W, j + 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), j + 1)),
      W = univ.map (extendByLast (g.trans Fin.castSuccEmb)) →
        (I.codedLvLevel g H B hd Q j).S.rows.CappedLift h := by
    rintro W h rfl
    exact hl
  exact key _ _ (donorFace_eq_coatom_of_surjective g hg).symm

end Seed

end VaughtConjecture
