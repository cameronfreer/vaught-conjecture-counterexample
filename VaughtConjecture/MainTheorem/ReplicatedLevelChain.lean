/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelLift

/-!
# The context lift at every grade of the re-rendered levels

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

For requests whose threshold is the top grade `m + 1`, a legal context with a cell at `(univ, k)`
for every `1 ≤ k ≤ m + 1`, the level at the grade `j + 1` (`Seed.lvLevel`) lifts capped from the
context coatom into `(univ, j + 1)` for every `j + 1 ≤ m + 1` (`Seed.lvLevel_cappedLift`):

* at the grade one the level is the ladder base, which lifts from the context face
  (`Scheme.cappedLift_ladderBase_rankMember`, `Seed.cappedLift_attachment_univ_one`);
* from the grade `j + 1` to `j + 2` the lift of the next level is the one-level composition
  (`Seed.ALvl.Good.cappedLift_next`), whose lower lift is the lift of the level below, carried into
  the next scheme (`Seed.ALvl.cappedLift_nS_iff`: below a pair not above `(univ, j + 2)` the next
  scheme is the level's scheme).

The levels are the schemes of the slices; the copies of the replicated scheme at the mixed faces
are not part of them.

## References

Bountifulness is [Kni26, Definition 2.5.14]; the growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType
open scoped Ordinal

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}

/-- **Lifts below a pair not above `(univ, j + 1)` in the next scheme are those of the level.** -/
theorem ALvl.cappedLift_nS_iff {j : ℕ} (N : I.ALvl g H j)
    (C : Finset (Fin (I.attachment g).card → Label.{u})) {X Y : Finset (Fin (m + 2)) × ℕ}
    (hXY : X ≤ Y) (hY : ¬ ((univ : Finset (Fin (m + 2))), j + 1) ≤ Y) :
    (N.nS B C).rows.CappedLift hXY ↔ N.S.rows.CappedLift hXY := by
  have h : N.S.toCellScheme.IsSourcePrefix (N.nS B C).toCellScheme (Fin.castAdd _) Y :=
    ⟨Scheme.isLowerEmbedding_castAdd (S := N.S) (j + 1) C.card
      (fun i ↦ N.Φ B C (C.equivFin.symm i).1) N.not_le,
      Scheme.appendFullCellsScheme_scope_castAdd N.S (j + 1) _,
      fun d hd ↦ ⟨⟨d, Scheme.lt_card_of_mem_below hY hd⟩, rfl⟩⟩
  rw [← h.cappedLift_iff hXY le_rfl, Scheme.comap_rows_castAdd]

/-- **The first level lifts from the context coatom at the grade one.** -/
theorem lvLevel1_cappedLift_one (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    (hdF : univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hrF : univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)) ∈ I.amalgam.toCellScheme.faces)
    (hr1 : 1 ≤ #(univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) ∩
      univ.map (extendByLast (g.trans Fin.castSuccEmb)))) :
    (I.lvLevel1 g H).S.rows.CappedLift (X := (univ.erase (Fin.last (m + 1)), 1))
      (Y := ((univ : Finset (Fin (m + 2))), 1)) ⟨erase_subset _ _, le_rfl⟩ := by
  set C := univ.map (Fin.castSuccEmb : Fin (m + 1) ↪ Fin (m + 2)) with hC
  have hCF : C ∈ I.amalgam.toCellScheme.faces :=
    ((StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left).1
  have hC1 : 1 ≤ #C := by rw [hC, card_map, card_univ, Fintype.card_fin]; omega
  have hXU : ((C, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1) :=
    ⟨subset_univ _, le_rfl⟩
  have hX : ¬ (((univ : Finset (Fin (m + 2))), 1) : Finset (Fin (m + 2)) × ℕ) ≤ (C, 1) :=
    fun h ↦ map_castSuccEmb_ne_univ (univ_subset_iff.mp h.1)
  have hl : (I.lvLevel1 g H).S.rows.CappedLift hXU :=
    Scheme.cappedLift_ladderBase_rankMember (hS := (I.attachmentBase g).noFull)
      (I.attachmentBase g).wf hH hcard hXU hX
      (cappedLift_attachment_univ_one hdF hrF hr1 hCF hC1 (.inl subset_rfl))
  have key : ∀ (D : Finset (Fin (m + 2)))
      (h : ((D, 1) : Finset (Fin (m + 2)) × ℕ) ≤ ((univ : Finset (Fin (m + 2))), 1)),
      D = C → (I.lvLevel1 g H).S.rows.CappedLift h := by
    rintro D h rfl
    exact hl
  exact key _ _ map_castSuccEmb_eq_ctxCoatom.symm

/-- **The context lift at every grade of the levels**, for requests whose threshold is the top
grade and a context with a cell at `(univ, k)` for every `1 ≤ k ≤ m + 1`. -/
theorem lvLevel_cappedLift (hH : 0 < H) (hcard : (I.attachmentBase g).S.card ≤ H)
    {p₀ : StageType.{u} α n} {d : StageType.{u} α (n + 1)}
    (hte : restrictFace (g.trans Fin.castSuccEmb) I.left = some p₀)
    (hdp : restrictFace Fin.castSuccEmb d = some p₀) (hdL : d.IsLegal) (hn : 0 < n)
    (hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d)
    {Q : GrowthRequests I.left d.toScheme} (hQ : Q.ClassCalibrated hte)
    (hpair : ∀ y, Q.CorrectAt I.left.label y (d.label y)) (hrel : Q.HasRelativeLiftOnClass hte hdp)
    (hth : Q.threshold = m + 1) (hB : 2 * (I.attachment g).card ≤ B)
    (hX : ∀ k, 2 ≤ k → k ≤ m + 1 → ∃ x : Fin I.left.card,
      I.left.toCellScheme.gradedIndex x = ((univ : Finset (Fin (m + 1))), k)) :
    ∀ j, j + 1 ≤ m + 1 → (I.lvLevel g H B hd Q j).S.rows.CappedLift
      (X := (univ.erase (Fin.last (m + 1)), j + 1)) (Y := ((univ : Finset (Fin (m + 2))), j + 1))
      ⟨erase_subset _ _, le_rfl⟩
  | 0, _ => lvLevel1_cappedLift_one hH hcard (donor_mem_faces hd) (root_mem_faces hte)
      (by rw [card_root]; exact hn)
  | j + 1, hj => by
    have hN := lvLevel_good (B := B) (hd := hd) hH hcard hQ hB j (by omega)
    have hlow := lvLevel_cappedLift hH hcard hte hdp hdL hn hd hQ hpair hrel hth hB hX j (by omega)
    have hlift := (ALvl.cappedLift_nS_iff (B := B) (I.lvLevel g H B hd Q j)
      (I.lvCat g B hd Q (j + 2)) _ fun h ↦ absurd h.2 (by simp only; omega)).mpr hlow
    exact hN.cappedLift_next hdp hdL hn hQ hpair hrel
      (by rcases Nat.lt_or_ge (j + 2) Q.threshold with h | h
          · exact .inr h
          · exact .inl (by omega)) (by omega) hB (hX (j + 2) (by omega) hj) hlift

end Seed

end VaughtConjecture
