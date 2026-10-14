/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelChain
import VaughtConjecture.MainTheorem.CodedLevelGrades

/-!
# The context lifts of the coded levels

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier) and Correspondence, item 1
(the strongly coded legal stage types). All results here are native constructions of this
repository.

The statements of `VaughtConjecture.MainTheorem.ReplicatedLevelChain` about the levels over the
padded grade-one base, for the coded levels (`Seed.codedLvLevel`) over the coded ladder base
(`Seed.codedLvBase`). The proofs are those of `VaughtConjecture.MainTheorem.ReplicatedLevelChain`,
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

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

/-- **The first level lifts from the context coatom at the grade one.** -/
theorem codedLvLevel1_cappedLift_one (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)))) :
    (I.codedLvLevel1 g H).S.rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), 1))
      (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  set C := univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) with hC
  have hCF : C ∈ I.amalgam.toCellScheme.faces :=
    ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hC1 : 1 ≤ #C := by rw [hC, card_map, card_univ, Fintype.card_fin]; omega
  have hXU : ((C, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1) :=
    ⟨subset_univ _, le_rfl⟩
  have hX : ¬ (((univ : Finset (Fin (m + 2))), 1) : Finset (Fin (m + 2)) × ℕ) ≤ (C, 1) :=
    fun h ↦ map_castSuccEmb_ne_univ (univ_subset_iff.mp h.1)
  have hl : (I.codedLvLevel1 g H).S.rows.CappedLift hXU :=
    Scheme.cappedLift_codedLadderBase_rankMember (hS := (I.attachmentBase g).noFull)
      (I.attachmentBase g).wf hH hcard hXU hX
      (cappedLift_attachment_univ_one hdF hrF hr1 hCF hC1 (.inl subset_rfl))
  have key : ∀ (D : Finset (Fin (m + 2)))
      (h : ((D, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1)),
      D = C → (I.codedLvLevel1 g H).S.rows.CappedLift h := by
    rintro D h rfl
    exact hl
  exact key _ _ map_castSuccEmb_eq_ctxCoatom.symm

/-- **The context lift at every grade of the levels**, for requests calibrated on the class at any
threshold, with the explicit premises `hpair`, `hrel`, `hdL`, `0 < n`, and a context with a cell at
`(univ, k)` for every `1 ≤ k ≤ m + 1`. -/
theorem codedLvLevel_cappedLift (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hB : 2 * (I.attachment g).card ≤ B)
    (hX : ∀ k, 2 ≤ k → k ≤ m + 1 → ∃ x : Fin I.left.card,
      I.left.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 1))), k)) :
    ∀ j, j + 1 ≤ m + 1 → (I.codedLvLevel g H B hd Q j).S.rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j + 1)) (Y := ((univ : Finset (Fin (m + 2))), j + 1))
      ⟨erase_subset _ _, le_rfl⟩
  | 0, _ => codedLvLevel1_cappedLift_one hH hcard (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; exact hn)
  | j + 1, hj => by
    have hN := codedLvLevel_good (B := B) (hd := hd) hH hcard hQ hB j (by omega)
    have hlow := codedLvLevel_cappedLift hH hcard hte hdp hdL hn hd hQ hpair hrel hB hX j (by omega)
    have hlift := (ALvl.cappedLift_nS_iff (B := B) (I.codedLvLevel g H B hd Q j)
      (I.lvCat g B hd Q (j + 2)) _ fun h ↦ absurd h.2 (by simp only; omega)).mpr hlow
    exact hN.cappedLift_next hdp hdL hn hQ hpair hrel (by omega) hB (hX (j + 2) (by omega) hj)
      hlift

end Seed

open Finset Label CellScheme StageType

open Finset Label CellScheme StageType

/-- **The context lift at every grade of the levels, at any threshold**: the chain lemma
`Seed.codedLvLevel_cappedLift` with the cells of full scope taken from the first coatom type, which
is
legal.  No relation between the threshold and the grades is asked (the threshold is at most
`m + 1` by calibration only).  The premises `hQ` (calibration on the class), `hpair` (the labels
pair correct), `hrel` (the relative lift on the class), `hdL` (a legal donor) and `0 < n` stay
explicit until their proof is composed at the seed position. -/
theorem Seed.codedLvLevel_cappedLift' {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m}
    {g : Fin n ↪ Fin m} {H B : ℕ} (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hB : 2 * (I.attachment g).card ≤ B) :
    ∀ j, j + 1 ≤ m + 1 → (I.codedLvLevel g H B hd Q j).S.rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j + 1)) (Y := ((univ : Finset (Fin (m + 2))), j + 1))
      ⟨erase_subset _ _, le_rfl⟩ :=
  Seed.codedLvLevel_cappedLift hH hcard hte hdp hdL hn hd hQ hpair hrel hB
    fun _ hk2 hkm ↦ I.exists_gradedIndex_univ_left (by omega) hkm

end VaughtConjecture
