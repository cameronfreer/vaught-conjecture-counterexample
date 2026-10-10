/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.MainTheorem.ReplicatedLevelMirror
import VaughtConjecture.MainTheorem.ReplicatedGradeCode

/-!
# The support of a re-rendered level

Roadmap, Layer 3 ((R3) and (R4), the levels of the replicated carrier re-rendered per grade).

**The values of the upper decoder** (`Label.upperDecoderAt_support`): for every labelling `w` and
every label `x`, the upper decoder `upperDecoderAt k K B w x` is
* at most the least grid point `gridPoint k 0` (that is, `⊥` or a point of the natural block with
  finite part at most `k`): the cap of `x` at the least grid point;
* a grid point `gridPoint K b` with `b ≤ B`: the gap value; or
* a label in the block of a value `w e` (`moveToBlock (w e) v = v`): the reading of a cell `e`,
  which is the block move of `x` to the block of `w e` or the visibility replacement of `w e`.

**The support invariant of the levels** (`Seed.lvLevel_support`): every value of the section of
the level at the grade `j + 1` at a state `P` is at most `gridPoint (j + 1) 0`, a grid point
`gridPoint (j + 2) b` with `b ≤ B`, or a label in the block of a value `P e` of the state.  At the
first level the section is `⊥`, `1`, or a value of the state; at the next levels it is the upper
decoder of the state.  A copy carries the value of its original, so the replicated level has the
same support (`Seed.ALvl.Good.repσ_support`).

No new block is created other than those of the grid points at the top grade: a value of the code
grid in a block `b ≥ 1` other than a grid point of the top grade lies in the block of a value of
the state.

## References

The growth construction is that of [Kni26, §4].
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme StageType

namespace Label

variable {ι : Type*} [Fintype ι]

/-- A label is fixed by the block move to its own block. -/
theorem moveToBlock_self (y : Label.{u}) : moveToBlock y y = y :=
  moveToBlock_eq_self (k := 0) rfl

/-- The visibility replacement of a label lies in the block of the label. -/
theorem moveToBlock_visibilityReplace_self (k : ℕ) (y : Label.{u}) :
    moveToBlock y (visibilityReplace k k y) = visibilityReplace k k y := by
  rw [moveToBlock_visibilityReplace, moveToBlock_self]

open Classical in
/-- **The values of the upper decoder**: at most the least grid point at `k`, a grid point at `K`
of block at most `B`, or a label in the block of a value of `w`. -/
theorem upperDecoderAt_support (k K B : ℕ) (w : ι → Label.{u}) (x : Label.{u}) :
    upperDecoderAt k K B w x ≤ gridPoint k 0 ∨
      (∃ b ≤ B, upperDecoderAt k K B w x = gridPoint K b) ∨
      ∃ e, moveToBlock (w e) (upperDecoderAt k K B w x) = upperDecoderAt k K B w x := by
  unfold upperDecoderAt
  rcases max_choice (orbitDecoder k w (gridPoint k 0) x) (gapValueAt k K B w x) with h | h <;>
    rw [h]
  · -- the orbit decoder
    unfold orbitDecoder
    set s : Finset ι := {d | gridPoint k 0 ≤ visibilityReplace k k (orbitCode k w d)}
    rcases max_choice (min x (gridPoint k 0)) (s.sup fun d ↦ cellReading k w d x) with h' | h' <;>
      rw [h']
    · exact .inl (min_le_right _ _)
    · rcases s.eq_empty_or_nonempty with hs | hs
      · rw [hs, Finset.sup_empty]; exact .inl bot_le
      obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_sup s hs fun d ↦ cellReading k w d x
      rw [hd]
      unfold cellReading
      split_ifs
      · exact .inl bot_le
      · exact .inr (.inr ⟨d, moveToBlock_moveToBlock _ _ _⟩)
      · exact .inr (.inr ⟨d, moveToBlock_visibilityReplace_self k _⟩)
  · -- the gap value
    unfold gapValueAt
    split_ifs
    · exact .inl bot_le
    set s : Finset ι := {d | visibilityReplace k k x ≤ visibilityReplace k k (orbitCode k w d)}
    rcases s.eq_empty_or_nonempty with hs | hs
    · rw [hs, Finset.inf_empty, min_eq_left le_top]
      exact .inr (.inl ⟨B, le_rfl, rfl⟩)
    obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_inf s hs fun d ↦ admissibleBelowAt K B (w d)
    rw [hd]
    rcases min_choice (gridPoint K B) (admissibleBelowAt K B (w d)) with h' | h' <;> rw [h']
    · exact .inr (.inl ⟨B, le_rfl, rfl⟩)
    · rcases mem_grid.mp (mem_grid_of_mem_codeGrid (admissibleBelowAt_mem_codeGrid K B (w d))
        (isSelfVisible_admissibleBelowAt K B (w d))).1 with h0 | ⟨b, hb, hb'⟩
      · rw [h0]; exact .inl bot_le
      · exact .inr (.inl ⟨b, hb, hb'⟩)

end Label

namespace Seed

variable {α : Ordinal.{u}} {m n : ℕ} {I : Seed.{u} α m} {g : Fin n ↪ Fin m} {H B : ℕ}
  {d : StageType.{u} α (n + 1)}
  {hd : restrictFace (extendByLast (g.trans Fin.castSuccEmb)) I.amalgam = some d}
  {Q : GrowthRequests I.left d.toScheme}

/-- **The support invariant of the levels**: every value of the section of the level at the grade
`j + 1` at a state `P` is at most the least grid point `gridPoint (j + 1) 0`, a grid point
`gridPoint (j + 2) b` with `b ≤ B`, or a label in the block of a value of `P`. -/
theorem lvLevel_support (j : ℕ) (P : Fin (I.attachment g).card → Label.{u})
    (z : Fin (I.lvLevel g H B hd Q j).S.card) :
    (I.lvLevel g H B hd Q j).σ P z ≤ gridPoint (j + 1) 0 ∨
      (∃ b ≤ B, (I.lvLevel g H B hd Q j).σ P z = gridPoint (j + 2) b) ∨
      ∃ e, moveToBlock (P e) ((I.lvLevel g H B hd Q j).σ P z) =
        (I.lvLevel g H B hd Q j).σ P z := by
  cases j with
  | zero =>
    change I.lvBaseSec g H P z ≤ gridPoint 1 0 ∨ (∃ b ≤ B, I.lvBaseSec g H P z = gridPoint 2 b) ∨
      ∃ e, moveToBlock (P e) (I.lvBaseSec g H P z) = I.lvBaseSec g H P z
    unfold lvBaseSec
    split_ifs with h
    · rcases Scheme.LadderBaseData.stateExtOf_cases (B' := I.attachmentBase g) P _ z with
        h0 | h1 | ⟨e, he⟩
      · rw [h0]; exact .inl bot_le
      · rw [h1]; exact .inl (le_of_eq (by simp [gridPoint]))
      · rw [he]; exact .inr (.inr ⟨e, moveToBlock_self _⟩)
    · exact .inl bot_le
  | succ j => exact upperDecoderAt_support (j + 2) (j + 3) B P _

/-- **The support invariant of the replicated level**: a copy carries the value of its original. -/
theorem ALvl.Good.repσ_support {j : ℕ} {A : ℕ → (Fin (I.attachment g).card → Label.{u}) → Prop}
    (hN : (I.lvLevel g H B hd Q j).Good B A) (P : Fin (I.attachment g).card → Label.{u})
    (t : Fin ((I.lvLevel g H B hd Q j).S.card +
      (I.lvLevel g H B hd Q j).S.copyCount (I.mixedFaces g))) :
    hN.repσ P t ≤ gridPoint (j + 1) 0 ∨ (∃ b ≤ B, hN.repσ P t = gridPoint (j + 2) b) ∨
      ∃ e, moveToBlock (P e) (hN.repσ P t) = hN.repσ P t :=
  lvLevel_support j P _

end Seed

end VaughtConjecture
