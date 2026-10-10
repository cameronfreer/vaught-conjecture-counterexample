/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelMixedLift
import VaughtConjecture.MainTheorem.SeedLevelStrictChoice

/-!
# Bountifulness of the replicated top level

Roadmap, Layer 3 ((R3) and (R4), the lifts of the levels re-rendered per grade).

**The replicated top level is bountiful** (`Seed.lvRep_isBountiful`): for requests calibrated on
the class, with the labels pair correct (`hpair`), the relative lift on the class (`hrel`), a legal
donor (`hdL`), `0 < n`, a height `H` at least the number of cells of the attachment and a block
bound `B` with `2 · #cells < B` (strict, for the twins of the lifts from the mixed faces), the level
at the grade `m + 1` with its copies at the mixed faces (`Seed.ALvl.Good.rep`) is bountiful.  The
two inputs of `Seed.lvRep_isBountiful_of_lifts`:

* **the lifts into the mixed faces**: through the same grade
  (`CellScheme.Rows.cappedLift_of_fst_eq`); from a mixed face by
  `Seed.lvRep_cappedLift_mixed_mixed`; from a face inside the context face or the donor face
  through the full face (`CellScheme.Rows.cappedLift_of_extend`, with
  `Seed.lvRep_cappedLift_mixed_univ`), the lift into the full face being the lift inside the face
  (`Seed.ALvl.Good.cappedLift_rep_of_subset`) followed by the context lift
  (`Seed.lvLevel_cappedLift_grade`) or the lift from the donor face
  (`Seed.lvLevel_cappedLift_donor`, `Seed.ALvl.Good.cappedLift_rep_donor`);
* **the lifts from the second coatom**: a mixed face when the root is not onto
  (`Seed.mem_mixedFaces_coatom`, `Seed.lvRep_cappedLift_mixed_univ`), the donor face when it is
  (`Seed.lvLevel_cappedLift_coatom_of_surjective`).

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
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

/-- **The replicated top level is bountiful** (see the module docstring). -/
theorem lvRep_isBountiful (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀}
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hQ : Q.ClassCalibrated hte) (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y))
    (hrel : Q.HasRelativeLiftOnClass hte hdp) (hB' : 2 * (I.attachment g).card < B)
    (hN : (I.lvLevel g H B hd Q m).Good B (lvAdm hd Q)) :
    hN.rep.rows.IsBountiful := by
  classical
  have hfaces := faces_lvLevel (I := I) (g := g) (H := H) (B := B) (hd := hd) (Q := Q) m
  have hnm : n ≤ m := by simpa using Fintype.card_le_of_embedding g
  have hcardC : #(univ.erase (Fin.last (m + 1))) = m + 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; rfl
  have hcardD : #(univ.map (extendByLast (g.trans Fin.castSuccEmb))) = n + 1 := by
    rw [card_map, card_univ, Fintype.card_fin]
  have hCF : univ.erase (Fin.last (m + 1)) ∈ hN.rep.toCellScheme.faces := by
    change _ ∈ (I.lvLevel g H B hd Q m).S.toCellScheme.faces
    rw [hfaces, ← Coatom.univ_map_left]
    exact ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hDF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ hN.rep.toCellScheme.faces := by
    change _ ∈ (I.lvLevel g H B hd Q m).S.toCellScheme.faces
    rw [hfaces]
    exact donor_mem_faces hd
  have hmixed_card {U : Finset (Fin (m + 2))} (hU : U ∈ I.mixedFaces g) : #U ≤ m + 1 := by
    have hlt : U ⊂ univ := ssubset_univ_iff.mpr ((I.mem_mixedFaces g).mp hU).2.1
    have := card_lt_card hlt
    simp only [card_univ, Fintype.card_fin] at this
    omega
  -- a face inside the context face or the donor face lifts into the full face
  have hatt_univ (V : Finset (Fin (m + 2))) (k : ℕ) (hVF : V ∈ hN.rep.toCellScheme.faces)
      (hk1 : 1 ≤ k) (hkV : k ≤ #V)
      (hV : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
        V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb))) :
      hN.rep.rows.CappedLift (X := (V, k)) (Y := ((univ : Finset (Fin (m + 2))), k))
        ⟨subset_univ _, le_rfl⟩ := by
    have hXgf : ((V, k) : Finset (Fin (m + 2)) × ℕ) ∈ hN.rep.toCellScheme.gradedFaces :=
      ⟨hVF, hk1, hkV⟩
    rcases hV with hVC | hVD
    · have hVC' : V ⊆ univ.erase (Fin.last (m + 1)) := by
        rwa [← Coatom.univ_map_left]
      have hkC : k ≤ m + 1 := hkV.trans ((card_le_card hVC').trans hcardC.le)
      have hl1 := hN.cappedLift_rep_of_subset hfaces hXgf (Y := (univ.erase (Fin.last (m + 1)), k))
        ⟨hCF, hk1, by change k ≤ #(univ.erase (Fin.last (m + 1))); omega⟩ ⟨hVC', le_rfl⟩
        (.inl (by rw [Coatom.univ_map_left]))
      have hl2 := hN.cappedLift_rep (X := (univ.erase (Fin.last (m + 1)), k))
        (Y := ((univ : Finset (Fin (m + 2))), k)) ⟨erase_subset _ _, le_rfl⟩ rfl subset_rfl
        (lvLevel_cappedLift_grade hH hcard hdp hdL hn hQ hpair hrel hB'.le m k hk1 hkC le_rfl)
      exact hl1.trans hl2
    · have hkD : k ≤ n + 1 := hkV.trans ((card_le_card hVD).trans hcardD.le)
      have hl1 := hN.cappedLift_rep_of_subset hfaces hXgf
        (Y := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), k))
        ⟨hDF, hk1, by change k ≤ #(univ.map (extendByLast (g.trans Fin.castSuccEmb))); omega⟩
        ⟨hVD, le_rfl⟩ (.inr subset_rfl)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hlev := (lvLevel_cappedLift_iff_of_le (H := H) (B := B) (hd := hd) (Q := Q) (i := j)
        (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)), j + 1)) le_rfl
        ⟨subset_univ _, le_rfl⟩ m (by omega)).mpr
        (lvLevel_cappedLift_donor hH hcard hte hdL hn hd hQ hB'.le j hkD)
      have hl2 := hN.cappedLift_rep_donor (X := (univ.map (extendByLast (g.trans Fin.castSuccEmb)),
        j + 1)) (Y := ((univ : Finset (Fin (m + 2))), j + 1)) ⟨subset_univ _, le_rfl⟩ rfl
        subset_rfl hlev
      exact hl1.trans hl2
  refine lvRep_isBountiful_of_lifts hH hcard hdp hdL hn hQ hpair hrel hB'.le hN ?_ ?_
  · -- the lifts into the mixed faces
    rintro ⟨V, k⟩ ⟨U, k'⟩ hX - h hU
    have hkU : k ≤ #U := hX.2.2.trans (card_le_card h.1)
    have hsame : hN.rep.rows.CappedLift (X := (V, k)) (Y := (U, k)) ⟨h.1, le_rfl⟩ := by
      by_cases hVm : V ∈ I.mixedFaces g
      · exact lvRep_cappedLift_mixed_mixed hH hcard hQ hB' (by omega) hN hVm hU h.1 hX.2.1 hX.2.2
          (hkU.trans (hmixed_card hU))
      · have hVu : V ≠ univ := fun he ↦
          ((I.mem_mixedFaces g).mp hU).2.1 (univ_subset_iff.mp (he ▸ h.1))
        have hc : V ⊆ univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∨
            V ⊆ univ.map (extendByLast (g.trans Fin.castSuccEmb)) := by
          by_contra hc
          push Not at hc
          exact hVm ((I.mem_mixedFaces g).mpr ⟨hfaces ▸ hX.1, hVu, hc.1, hc.2⟩)
        exact CellScheme.Rows.cappedLift_of_extend (X := (V, k)) (Y := (U, k))
          (Z := ((univ : Finset (Fin (m + 2))), k)) ⟨h.1, le_rfl⟩ ⟨subset_univ _, le_rfl⟩ rfl
          (hatt_univ V k hX.1 hX.2.1 hX.2.2 hc)
          (lvRep_cappedLift_mixed_univ hH hcard hQ hB' (by omega) hN hU hX.2.1 hkU
            (hkU.trans (hmixed_card hU)))
    exact hsame.trans (CellScheme.Rows.cappedLift_of_fst_eq (R := hN.rep.rows)
      (X := (U, k)) (Y := (U, k')) ⟨subset_rfl, h.2⟩ rfl)
  · -- the lifts from the second coatom
    intro k hk1 hkm
    by_cases hg : Function.Surjective g
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hlev := (lvLevel_cappedLift_iff_of_le (H := H) (B := B) (hd := hd) (Q := Q) (i := j)
        (X := (univ.erase (Fin.castSucc (Fin.last m)), j + 1)) le_rfl
        ⟨erase_subset _ _, le_rfl⟩ m (by omega)).mpr
        (lvLevel_cappedLift_coatom_of_surjective hH hcard hte hdL hn hd hQ hB'.le hg j hkm)
      exact hN.cappedLift_rep_donor _ rfl
        (by rw [donorFace_eq_coatom_of_surjective g hg]) hlev
    · have hU := mem_mixedFaces_coatom (I := I) hg
      exact lvRep_cappedLift_mixed_univ hH hcard hQ hB' (by omega) hN hU hk1
        (by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega) hkm

end Seed

end VaughtConjecture
