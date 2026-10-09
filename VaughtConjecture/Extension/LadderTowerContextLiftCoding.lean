/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.LadderTowerContextLiftReplicated

/-!
# The coding of states reads the ladder through one member

Roadmap, Layer 3 ((R3) and (R4), the bountifulness of the replicated carrier).

The writing of a lawful state `R` of the attachment on the ladder of the replicated scheme is the
positive table of `R` at the base indices of its own rank member `a_R`
(`Seed.replicatedWriting_ladder`).  At the rung `i` of another member `b` the base index is
`min (rankCut H a_R b) (i + 1)` (`Seed.replicatedWriting_rung`): above the cut of the two rank
vectors the writing is **constant along the rungs of `b`** (`Seed.replicatedWriting_rung_eq`).

**What the coding of states forces** (`Seed.exists_member_of_stateCodingR`).  At the cap `⊤` the
coding of states (`Seed.StateCodingR j`) asks the decoded writing of the coded state to equal the
ambient at every cell of the tower below `(univ, j)`, the rungs included.  If the ambient separates
the last two rungs of a member `b` (`H ≥ 2`), the writing cannot be constant there, so the cut is
`H` and the coded state's rank member is `b`: **some state of the catalogue satisfying `A (m + 2)`
has the rank member `b`**.  So `Seed.StateCodingR j` fails as soon as some ambient lawful below
`(univ, j)` separates the last two rungs of a member that is the rank member of no catalogue state,
while some state satisfying `A (m + 2)` reads it on the cells of the attachment below the grade.
The members range over all dense rank vectors with lawful tables, admitted or not; whether such
an ambient exists at a legal context is not decided here.  This is the shape of the failure of the
single-writing form: the ladder values of a lift must be allowed to come from the ambient's own
member, not only from the coded state's writing.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}

variable (H Γ A B') in
/-- The cell of the replicated scheme at a ladder point. -/
noncomputable abbrev ladderCellE
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    Fin (I.replicated g H Γ A B').card :=
  Fin.castAdd _ ((I.attachmentBase g).towerEmb m
    (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p)))

/-- **The writing of a lawful state on the ladder**: the positive table of the state at the base
index of its rank member. -/
theorem replicatedWriting_ladder (hcard : (I.attachmentBase g).S.card ≤ H)
    {R : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    I.replicatedWriting g H Γ A B' R (ladderCellE H Γ A B' p) =
      posTable R (ladderIndex H (Scheme.rankProf (I.attachmentBase g).S H) Prod.fst
        (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H))
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR) p) := by
  change ((I.attachmentBase g).ladderTower H Γ A B' m).v R
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ _)) = _
  rw [Scheme.mirrorOrig_castAdd]
  refine (Scheme.layerTower_v_emb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') R _ m).trans ?_
  change (I.attachmentBase g).stateExt H R _ = _
  rw [Scheme.LadderBaseData.stateExt_of_isLawful hR hcard]
  erw [Fin.append_right]
  rw [Scheme.baseIndex_natAdd, Equiv.symm_apply_apply]
  rfl

/-- **The writing at the rung `i` of a member `b`**: the positive table at the smaller of the cut
of the two rank vectors and `i + 1`. -/
theorem replicatedWriting_rung (hcard : (I.attachmentBase g).S.card ≤ H)
    {R : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (b : Scheme.RankMember (I.attachmentBase g).S H) (i : Fin H) :
    I.replicatedWriting g H Γ A B' R (ladderCellE H Γ A B' (b, Sum.inl i)) =
      posTable R (min (rankCut H (Scheme.rankProf (I.attachmentBase g).S H
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
          (Scheme.rankProf (I.attachmentBase g).S H b)) (i + 1)) := by
  rw [replicatedWriting_ladder hcard hR]
  rfl

/-- **Above the cut the writing is constant along the rungs of a member.** -/
theorem replicatedWriting_rung_eq (hcard : (I.attachmentBase g).S.card ≤ H)
    {R : Fin (I.attachment g).card → Label.{u}} (hR : (I.attachment g).rows.IsLawful R)
    (b : Scheme.RankMember (I.attachmentBase g).S H) {i i' : Fin H}
    (hi : rankCut H (Scheme.rankProf (I.attachmentBase g).S H
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
          (Scheme.rankProf (I.attachmentBase g).S H b) ≤ i + 1)
    (hi' : rankCut H (Scheme.rankProf (I.attachmentBase g).S H
        (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR))
          (Scheme.rankProf (I.attachmentBase g).S H b) ≤ i' + 1) :
    I.replicatedWriting g H Γ A B' R (ladderCellE H Γ A B' (b, Sum.inl i)) =
      I.replicatedWriting g H Γ A B' R (ladderCellE H Γ A B' (b, Sum.inl i')) := by
  rw [replicatedWriting_rung hcard hR, replicatedWriting_rung hcard hR, min_eq_left hi,
    min_eq_left hi']

/-- Rank members whose rank vectors agree up to the height are equal. -/
theorem RankMember_eq_of_rankAgree {a b : Scheme.RankMember (I.attachmentBase g).S H}
    (h : RankAgree (Scheme.rankProf (I.attachmentBase g).S H a)
      (Scheme.rankProf (I.attachmentBase g).S H b) H) : a = b := by
  apply Subtype.ext
  funext d
  have hd := h d
  rw [min_eq_left (Scheme.rankProf_le _ H a d), min_eq_left (Scheme.rankProf_le _ H b d)] at hd
  exact Fin.ext hd

/-- The ladder cells lie below the full face at every grade `j ≥ 1`. -/
theorem ladderCellE_mem_below {j : ℕ} (hj : 1 ≤ j)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    ladderCellE H Γ A B' p ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) := by
  have hgt : (I.replicated g H Γ A B').toCellScheme.gradedIndex (ladderCellE H Γ A B' p) =
      ((univ : Finset (Fin (m + 2))), 1) := by
    refine (Scheme.gradedIndex_mirror_castAdd _).trans ?_
    refine (Scheme.gradedIndex_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
      (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ m).trans ?_
    change ((I.attachmentBase g).S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
    exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _
  rw [CellScheme.mem_below, hgt]
  exact ⟨subset_rfl, hj⟩

/-- **The coding of states forces the ambient's member**: if `Seed.StateCodingR j` holds
(`j ≥ 1`, `H ≥ 2`), then for every ambient `q` lawful below `(univ, j)` separating the last two
rungs of a member `b`, and every complete lawful state `P` satisfying `A (m + 2)` and equal to `q`
on the cells of the attachment below the grade, some state of the catalogue satisfying
`A (m + 2)` has the rank member `b`.  At the cap `⊤` the decoded writing equals the ambient on the
rungs of `b`; were the cut of the coded state's member with `b` below `H`, the writing would be
constant on the last two rungs (`Seed.replicatedWriting_rung_eq`). -/
theorem exists_member_of_stateCodingR {j : ℕ} (hj : 1 ≤ j) (hH2 : 2 ≤ H)
    (hcard : (I.attachmentBase g).S.card ≤ H) (hC : StateCodingR I g H Γ A B' j)
    {q : (I.replicated g H Γ A B').toCellScheme.below
      ((univ : Finset (Fin (m + 2))), j) → Label.{u}}
    (hq : (I.replicated g H Γ A B').rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), j) q)
    {P : Fin (I.attachment g).card → Label.{u}} (hP : (I.attachment g).rows.IsLawful P)
    (hPA : A (m + 2) P)
    (hPq : ∀ (d : (I.replicated g H Γ A B').toCellScheme.below
        ((univ : Finset (Fin (m + 2))), j)) a, I.attachEmb g H Γ A B' a = d.1 → P a = q d)
    (b : Scheme.RankMember (I.attachmentBase g).S H)
    (hsep : q ⟨ladderCellE H Γ A B' (b, Sum.inl ⟨H - 2, by omega⟩), ladderCellE_mem_below hj _⟩ ≠
      q ⟨ladderCellE H Γ A B' (b, Sum.inl ⟨H - 1, by omega⟩), ladderCellE_mem_below hj _⟩) :
    ∃ R ∈ (I.attachmentBase g).towerCat Γ A (m + 2), ∃ hR : (I.attachment g).rows.IsLawful R,
      Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hR = b := by
  obtain ⟨R, hRC, ν, -, -, -, hνq⟩ := hC ⊤ (isSelfVisible_top j) q hq P hP hPA
    fun d a ha ↦ by rw [hPq d a ha]
  have hRl : (I.attachment g).rows.IsLawful R := (Scheme.LadderBaseData.mem_towerCat.mp hRC).2.1
  refine ⟨R, hRC, hRl, ?_⟩
  by_contra hne
  have hcut : rankCut H (Scheme.rankProf (I.attachmentBase g).S H
      (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hRl))
        (Scheme.rankProf (I.attachmentBase g).S H b) ≤ H - 1 := by
    set k := rankCut H (Scheme.rankProf (I.attachmentBase g).S H
      (Scheme.RankMember.ofLawful (I.attachmentBase g).wf hcard hRl))
        (Scheme.rankProf (I.attachmentBase g).S H b) with hk
    have hle : k ≤ H := rankCut_le H _ _
    rcases Nat.lt_or_ge k H with h | h
    · omega
    · exact absurd (RankMember_eq_of_rankAgree ((rankAgree_rankCut H _ _).mono h)) hne
  have heq := replicatedWriting_rung_eq (Γ := Γ) (A := A) (B' := B') hcard hRl b
    (i := ⟨H - 2, by omega⟩) (i' := ⟨H - 1, by omega⟩) (by simp only; omega) (by simp only; omega)
  have h1 := hνq ⟨_, ladderCellE_mem_below hj (b, Sum.inl ⟨H - 2, by omega⟩)⟩
  have h2 := hνq ⟨_, ladderCellE_mem_below hj (b, Sum.inl ⟨H - 1, by omega⟩)⟩
  simp only [min_top_right] at h1 h2
  exact hsep (h1.symm.trans ((congrArg ν heq).trans h2))

end Seed

end VaughtConjecture
