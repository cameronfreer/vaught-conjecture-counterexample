/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelBountiful
import VaughtConjecture.MainTheorem.CodedLevelChain
import VaughtConjecture.MainTheorem.CodedLevelFaces

/-!
# Bountifulness of the replicated coded levels from their lifts

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.ReplicatedLevelBountiful` about the levels over the
padded grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of
`VaughtConjecture.MainTheorem.ReplicatedLevelBountiful`, with the facts of the padded base replaced
by those of the coded base (`VaughtConjecture.Extension.CodedLadderBase`,
`VaughtConjecture.Extension.CodedLadderLift`) and the coded mirror lifts
(`VaughtConjecture.MainTheorem.CodedMirrorLift`); the statements there that do not mention the
levels or the base are used unchanged.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
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

variable {j : ℕ} {N : I.ALvl g H j} (hN : N.Good B (lvAdm hd Q))
include hN

end ALvl.Good

/-- **The context lift at every grade of a level**: the level at the grade `j + 1` lifts capped
from the context coatom into `(univ, k)` for every `1 ≤ k ≤ j + 1`, under the premises of
`Seed.codedLvLevel_cappedLift'` (kept explicit). -/
theorem codedLvLevel_cappedLift_grade (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hrel : Q.HasRelativeLiftOnClass hte hdp) (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j k, 1 ≤ k → k ≤ j + 1 → j + 1 ≤ m + 1 →
      (I.codedLvLevel g H B hd Q j).S.rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), k))
        (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨erase_subset _ _, le_rfl⟩
  | j, k, hk1, hkj, hjm => by
    rcases Nat.lt_or_ge k (j + 1) with hlt | hge
    · cases j with
      | zero => omega
      | succ j =>
        have hlow := codedLvLevel_cappedLift_grade hH hcard hdp hdL hn hQ hpair hrel hB j k hk1
          (by omega) (by omega)
        exact (ALvl.cappedLift_nS_iff (B := B) (I.codedLvLevel g H B hd Q j)
          (I.lvCat g B hd Q (j + 2)) _ fun h ↦ absurd h.2 (by simp only; omega)).mpr hlow
    · obtain rfl : k = j + 1 := by omega
      exact Seed.codedLvLevel_cappedLift' hH hcard hte hdp hdL hn hd hQ hpair hrel hB j hjm

/-- **The replicated top level is bountiful given two lifts**: the capped lifts into the mixed
faces (`hmixed`) and the lifts from the second coatom into the full face (`hsecond`).  Below the
faces inside the context face or the donor face it is the amalgam; the context lift is proved at
every grade (`Seed.codedLvLevel_cappedLift_grade`, under the explicit premises `hQ`, `hpair`,
`hrel`,
`hdL`, `0 < n`). -/
theorem codedLvRep_isBountiful_of_lifts (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hrel : Q.HasRelativeLiftOnClass hte hdp) (hB : 2 * (I.attachment g).card ≤ B)
    (hN : (I.codedLvLevel g H B hd Q m).Good B (lvAdm hd Q))
    (hmixed : ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄, X ∈ hN.rep.toCellScheme.gradedFaces →
      Y ∈ hN.rep.toCellScheme.gradedFaces → ∀ h : X ≤ Y, Y.1 ∈ I.mixedFaces g →
      hN.rep.rows.CappedLift h)
    (hsecond : ∀ k, 1 ≤ k → k ≤ m + 1 →
      hN.rep.rows.CappedLift (X := (univ.erase (Fin.castSucc (Fin.last m)), k))
        (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨erase_subset _ _, le_rfl⟩) :
    hN.rep.rows.IsBountiful := by
  classical
  have hfaces := faces_codedLvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hproper : ∀ ⦃X Y : Finset (Fin (m + 2)) × ℕ⦄, X ∈ hN.rep.toCellScheme.gradedFaces →
      Y ∈ hN.rep.toCellScheme.gradedFaces → ∀ h : X ≤ Y, Y.1 ≠ univ →
      hN.rep.rows.CappedLift h := by
    intro X Y hX hY h hYu
    by_cases hYc : Y.1 ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
        Y.1 ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))
    · exact hN.cappedLift_rep_of_subset hfaces hX hY h hYc
    · push Not at hYc
      exact hmixed hX hY h ((I.mem_mixedFaces g).mpr ⟨hfaces ▸ hY.1, hYu, hYc.1, hYc.2⟩)
  have hwf := hN.isWellFormed_rep hfaces
  have hzero (x : Fin (m + 2)) : hN.rep.rows.CappedLift (X := (univ.erase x, 0))
      (Y := ((univ : Finset (Fin (m + 2))), 0)) ⟨erase_subset _ _, le_rfl⟩ := by
    refine CellScheme.Rows.cappedLift_of_below_eq_empty ?_ _
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hz
    have h1 : hN.rep.toCellScheme.grade z ≤ 0 := hz.2
    have h2 := hwf.isWellFormed.grade_pos z
    omega
  have hfull (x : Fin (m + 2)) (hx : x = Fin.last (m + 1) ∨ x = Fin.castSucc (Fin.last m)) :
      ∀ k ≤ #(univ.erase x), hN.rep.rows.CappedLift (X := (univ.erase x, k))
        (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨erase_subset _ _, le_rfl⟩ := by
    intro k hk
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact hzero x
    rcases hx with rfl | rfl
    · exact hN.cappedLift_rep _ rfl subset_rfl
        (codedLvLevel_cappedLift_grade hH hcard hdp hdL hn hQ hpair hrel hB m k hk1
            (by omega) le_rfl)
    · exact hsecond k hk1 (by omega)
  have hleftF : univ.erase (Fin.last (m + 1)) ∈ hN.rep.toCellScheme.faces := by
    change _ ∈ (I.codedLvLevel g H B hd Q m).S.toCellScheme.faces
    rw [hfaces, ← Coatom.univ_map_left]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hrightF : univ.erase (Fin.castSucc (Fin.last m)) ∈ hN.rep.toCellScheme.faces := by
    change _ ∈ (I.codedLvLevel g H B hd Q m).S.toCellScheme.faces
    rw [hfaces, ← Coatom.univ_map_right]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_right).1
  refine CellScheme.Rows.isBountiful_of_coatoms (A := univ) (mem_univ (Fin.last (m + 1)))
    (mem_univ (Fin.castSucc (Fin.last m))) (fun B' hB' hBu ↦ ?_) hleftF hrightF hproper
    (hfull _ (.inl rfl)) (hfull _ (.inr rfl))
  exact I.subset_or_subset B' (hfaces ▸ hB') hBu

end Seed

end VaughtConjecture
