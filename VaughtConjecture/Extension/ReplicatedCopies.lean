/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ReplicatedWriting

/-!
# The copies at a mixed face, and the copied ladder

Roadmap, Layer 3 ((R3) and (R4), the recognition on the copies).

At a mixed face `U` the replicated scheme has one copy (`Seed.copyAt`) of every cell of full scope
of the ladder tower over the attachment of grade at most `|U|`, of scope `U` and the grade of its
original (`Seed.gradedIndex_copyAt`).  The copies at `U` read one another as their originals do
(`Seed.rowAt_copyAt_copyAt`), and read the cells of the attachment inside `U` as their originals
do (`Seed.rowAt_copyAt_attachEmb`).  In particular the copies at `U` of the ladder points
(`Seed.copyLadder`) form a **copied field ladder** with the rows of the ladder
(`Seed.rowAt_copyLadder`), and a copy of a controller reads the copied ladder as the controller
reads the ladder (`Seed.rowAt_copyAt_copyLadder`): the data of `GrowthCarrier.recognizes_of_ladder`
is present inside every mixed face.

## References

The controllers and the growth step are those of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H : ℕ}
  {Γ : Finset Label.{u}} {A : ℕ → (Fin (I.attachmentBase g).S.card → Label.{u}) → Prop} {B' : ℕ}
  {U : Finset (Fin (m + 2))}

variable (H Γ A B') in
/-- **The copy at the mixed face `U`** of a cell `f` of full scope of the tower of grade at most
`|U|`. -/
noncomputable def copyAt (hU : U ∈ I.mixedFaces g) (f : Fin (I.attachTower g H Γ A B').card)
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U) :
    Fin (I.replicated g H Γ A B').card :=
  Fin.natAdd _ ((I.attachTower g H Γ A B').copyEquiv (I.mixedFaces g) ⟨(U, f), hU, hf, hfg⟩)

/-- The original of the copy at `U` of `f` is `f`. -/
theorem mirrorOrig_copyAt (hU : U ∈ I.mixedFaces g) (f : Fin (I.attachTower g H Γ A B').card)
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U) :
    (I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (copyAt H Γ A B' hU f hf hfg) = f := by
  rw [copyAt, Scheme.mirrorOrig_natAdd, Equiv.symm_apply_apply]

/-- The copy at `U` of `f` has the scope `U` and the grade of `f`. -/
theorem gradedIndex_copyAt (hU : U ∈ I.mixedFaces g) (f : Fin (I.attachTower g H Γ A B').card)
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U) :
    (I.replicated g H Γ A B').toCellScheme.gradedIndex (copyAt H Γ A B' hU f hf hfg) =
      (U, (I.attachTower g H Γ A B').toCellScheme.grade f) := by
  change ((I.attachTower g H Γ A B').mirrorScope (I.mixedFaces g) _,
    (I.attachTower g H Γ A B').toCellScheme.grade
      ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) _)) = _
  rw [copyAt, Scheme.mirrorScope_natAdd, Scheme.mirrorOrig_natAdd, Equiv.symm_apply_apply]

/-- **The copies at `U` read one another as their originals do.** -/
theorem rowAt_copyAt_copyAt (hU : U ∈ I.mixedFaces g)
    {f f' : Fin (I.attachTower g H Γ A B').card}
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U)
    (hf' : (I.attachTower g H Γ A B').toCellScheme.scope f' = univ)
    (hfg' : (I.attachTower g H Γ A B').toCellScheme.grade f' ≤ #U)
    (hle : (I.attachTower g H Γ A B').toCellScheme.grade f' ≤
      (I.attachTower g H Γ A B').toCellScheme.grade f) :
    (I.replicated g H Γ A B').rowAt (copyAt H Γ A B' hU f hf hfg)
        (copyAt H Γ A B' hU f' hf' hfg') =
      (I.attachTower g H Γ A B').rowAt f f' := by
  have hmem : copyAt H Γ A B' hU f' hf' hfg' ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex (copyAt H Γ A B' hU f hf hfg)) := by
    rw [CellScheme.mem_below, gradedIndex_copyAt, gradedIndex_copyAt]
    exact ⟨subset_rfl, hle⟩
  rw [Scheme.rowAt_mirror_of_mem hmem, mirrorOrig_copyAt, mirrorOrig_copyAt]

/-- **A copy at `U` reads the cells of the attachment inside `U` as its original does.** -/
theorem rowAt_copyAt_attachEmb (hU : U ∈ I.mixedFaces g)
    {f : Fin (I.attachTower g H Γ A B').card}
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U)
    {c : Fin (I.attachment g).card} (hcs : (I.attachment g).toCellScheme.scope c ⊆ U)
    (hcg : (I.attachment g).toCellScheme.grade c ≤
      (I.attachTower g H Γ A B').toCellScheme.grade f) :
    (I.replicated g H Γ A B').rowAt (copyAt H Γ A B' hU f hf hfg) (I.attachEmb g H Γ A B' c) =
      (I.attachTower g H Γ A B').rowAt f ((I.attachmentBase g).baseCellEmb m c) := by
  have hmem : I.attachEmb g H Γ A B' c ∈ (I.replicated g H Γ A B').toCellScheme.below
      ((I.replicated g H Γ A B').toCellScheme.gradedIndex (copyAt H Γ A B' hU f hf hfg)) := by
    rw [CellScheme.mem_below, gradedIndex_copyAt, gradedIndex_attachEmb]
    exact ⟨hcs, hcg⟩
  rw [Scheme.rowAt_mirror_of_mem hmem, mirrorOrig_copyAt]
  change (I.attachTower g H Γ A B').rowAt f
    ((I.attachTower g H Γ A B').mirrorOrig (I.mixedFaces g) (Fin.castAdd _ _)) = _
  rw [Scheme.mirrorOrig_castAdd]

/-! ### The copied ladder -/

variable (H Γ A B') in
/-- The ladder point `p` of the tower over the attachment. -/
noncomputable abbrev ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    Fin (I.attachTower g H Γ A B').card :=
  (I.attachmentBase g).towerEmb (H := H) (Γ := Γ) (A := A) (B' := B') m
    (Fin.natAdd _ (Scheme.ladderEquiv _ _ H p))

theorem gradedIndex_ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.attachTower g H Γ A B').toCellScheme.gradedIndex (ladCell H Γ A B' p) =
      ((univ : Finset (Fin (m + 2))), 1) := by
  refine (Scheme.gradedIndex_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
    (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ m).trans ?_
  change ((I.attachmentBase g).S.appendFullCellsScheme 1 _).gradedIndex (Fin.natAdd _ _) = _
  exact Scheme.appendFullCellsScheme_gradedIndex_natAdd _ _ _ _

theorem grade_ladCell
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.attachTower g H Γ A B').toCellScheme.grade (ladCell H Γ A B' p) = 1 :=
  congrArg Prod.snd (gradedIndex_ladCell p)

/-- A mixed face is not empty. -/
theorem one_le_card_of_mem_mixedFaces (hU : U ∈ I.mixedFaces g) : 1 ≤ #U := by
  obtain ⟨-, -, hc, -⟩ := (I.mem_mixedFaces g).mp hU
  rcases U.eq_empty_or_nonempty with he | hne
  · exact absurd (he ▸ empty_subset _) hc
  · exact hne.card_pos

variable (H Γ A B') in
/-- **The copied ladder** at the mixed face `U`: the copies at `U` of the ladder points. -/
noncomputable def copyLadder (hU : U ∈ I.mixedFaces g)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    Fin (I.replicated g H Γ A B').card :=
  copyAt H Γ A B' hU (ladCell H Γ A B' p) (congrArg Prod.fst (gradedIndex_ladCell p))
    ((grade_ladCell p).trans_le (one_le_card_of_mem_mixedFaces hU))

/-- The copied ladder points have the scope `U` and the grade `1`. -/
theorem gradedIndex_copyLadder (hU : U ∈ I.mixedFaces g)
    (p : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').toCellScheme.gradedIndex (copyLadder H Γ A B' hU p) = (U, 1) :=
  (gradedIndex_copyAt _ _ _ _).trans (Prod.ext rfl (grade_ladCell p))

/-- **The copied ladder has the rows of the ladder.** -/
theorem rowAt_copyLadder (hU : U ∈ I.mixedFaces g)
    (p q : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').rowAt (copyLadder H Γ A B' hU p) (copyLadder H Γ A B' hU q) =
      ladderSource (Scheme.ladderCeil (Scheme.rankProf (I.attachmentBase g).S H) p)
        (Scheme.baseIndex H (Scheme.rankProf (I.attachmentBase g).S H) p.1
          (Fin.natAdd _ (Scheme.ladderEquiv _ _ H q))) := by
  refine (rowAt_copyAt_copyAt hU _ _ _ _ ?_).trans ?_
  · rw [grade_ladCell, grade_ladCell]
  · exact (Scheme.rowAt_layerTowerEmb (B := (I.attachmentBase g).towerBase H)
      (C := (I.attachmentBase g).towerCat Γ A) (G := fun k ↦ grid k B') _ _ m).trans
      (Scheme.rowAt_ladderBase_ladder (hS := (I.attachmentBase g).noFull)
        (I.attachmentBase g).wf p q)

/-- **A copy of a cell of full scope reads the copied ladder as its original reads the ladder.** -/
theorem rowAt_copyAt_copyLadder (hU : U ∈ I.mixedFaces g)
    {f : Fin (I.attachTower g H Γ A B').card}
    (hf : (I.attachTower g H Γ A B').toCellScheme.scope f = univ)
    (hfg : (I.attachTower g H Γ A B').toCellScheme.grade f ≤ #U)
    (hf1 : 1 ≤ (I.attachTower g H Γ A B').toCellScheme.grade f)
    (q : Scheme.LadderPt (I.attachmentBase g).S (Scheme.RankMember (I.attachmentBase g).S H) H) :
    (I.replicated g H Γ A B').rowAt (copyAt H Γ A B' hU f hf hfg) (copyLadder H Γ A B' hU q) =
      (I.attachTower g H Γ A B').rowAt f (ladCell H Γ A B' q) :=
  rowAt_copyAt_copyAt hU _ _ _ _
    ((grade_ladCell q).trans_le hf1)

end Seed

end VaughtConjecture
