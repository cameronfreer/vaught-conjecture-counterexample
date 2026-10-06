/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.SeparatingCell

/-!
# Ordered rows and the lift of parameters of the thin completion

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the recursion on the grade; here the label-level
part of the thin completion of the asymmetric seed `seedL`, a completion below the full grade
outside the tower route); semantic contract, items 2–4.

The *thin completion* (`VaughtConjecture.Extension.ThinCompletion`) adds to the amalgam of `seedL`
one new cell at each graded face `(univ, k)` of full scope, `k = 1, 2, 3, 4`.  This module holds
what is said about it at the level of labels: the rows of the new cells, their witnesses, the
constraints of the lawful labellings, and the lift of their parameters.  Write `C = {0, 1, 2, 3}`
and `D = {0, 1, 2, 4}` for the two coatoms.

**Kinds and ordered rows.**  The cells of the thin completion have six *kinds* (`kindLabel`):
the dead cells; the live cells of grade `1` of `C`, carrying `A_C`; those of `D` and the new cell
at `(univ, 1)`, carrying `A_D`; the live cells of grade `2` and the new cell at `(univ, 2)`,
carrying `F`; those of grade `3` and the new cell at `(univ, 3)`, carrying `G`; and the cells of
grade `4` (the two apexes and the new cell at `(univ, 4)`), carrying `Ω`.  The row of the new cell
at `(univ, k)` reads the kinds by `thinRow k`.  An *ordered row* reads the live cells of grade `1`
of `C` strictly below those of `D`, in an earlier block: the rows at `(univ, 1)` and `(univ, 2)`
read them at `1` and at `ω + 1`, and the row at `(univ, 2)` reads the live cells of grade `2` at
`ω·2 + 2`.  The row at `(univ, 3)` is the row of the cell `18` of `TL`, read on every cell below
`(univ, 3)`: `1` at the kind `A_C` and `ω + 3` at every other live kind.  The row at `(univ, 4)`
reads only the cells of grade `4`, at `ω + 4`.  Every row value is coded (`thinRow_lt`).

**Witnesses.**  Each new cell transforms its row with the suppressor constant at its own label up
to its grade:

* at `(univ, 1)`, the shifter `blockConst A_C A_D`, `A_C` on the natural numbers and `A_D` above,
  for `A_C ≤ A_D` (`transformsTo_rowOne`);
* at `(univ, 2)`, the *two-strip shifter* `twoStrip a b f`: the strip of `a` on the block `0`, the
  strip of `b` on the block `1`, and `f` above (the strip of `a` at the grade `2` is
  `visibilityReplace 2 j a` for `j` the finite part of the argument, at most `2`).  It is a witness
  for the suppressor `f` when the strip of `a` lies below that of `b` and the strip of `b` below `f`
  (`isWitness_twoStrip`); for `a = A_C ∧ F`, `b = A_D ∧ F` and `f = F` this holds when
  `A_C ≤ A_D` and there is no collision
  (`visibilityReplace_two_two_le_visibilityReplace_two_zero`, `transformsTo_rowTwo`);
* at `(univ, 3)`, the strip shifter at the grade `3` of `TL` (`strip3`), under
  `VisibilityReplaceFixedOfLT A_C G`, `G ≤ A_D` and `G ≤ F` (`transformsTo_rowThree`);
* at `(univ, 4)` and at the apexes, the top shifter (`transformsTo_rowFour`,
  `transformsTo_topShifter`).

**The constraints** (`IsThinLawfulBelow A_C A_D F G`): `A_C`, `A_D`, `F`, `G` self-visible at `1`,
`1`, `2`, `3`; `A_C ≤ A_D`; `G ≤ F`; `G ≤ A_D`; `VisibilityReplaceFixedOfLT A_C G` (the condition of
`TL`: if `A_C < G`, the finite part of `A_C`, if below `3`, is `1`); and no collision:
`A_C = A_D < F` forces `A_C` self-visible at `2`.  These are exactly the constraints of the
labellings of the thin completion lawful below `(univ, 3)`
(`ThinCompletion.isLawfulBelow_thinLabel`, `ThinCompletion.exists_of_isLawfulBelow_three`).  They
are not all the labellings of the amalgam lawful below both coatoms: the new cells impose
`A_C ≤ A_D` (at `(univ, 1)`), `F_C = F_D` (at `(univ, 2)`, which reads both at one value), and the
exclusion of collisions (at `(univ, 2)`, by the collision lemma).

**The lift of parameters** (`exists_thinLift`).  Let the ambient parameters satisfy
`IsThinLawfulBelow`, let `c` be a cap, and let a prescription fix some of the parameters, satisfying
the constraints among themselves and agreeing with the ambient capped at `c`.  The lift keeps the
prescribed parameters; an unprescribed parameter keeps its ambient value below the cap; at or above
the cap it is set to `G := c`, `A_D := ⊤`, `F := max c G`, `A_C := max c G`.  The lifted parameters
satisfy `IsThinLawfulBelow` and agree with the ambient capped at `c`, when `c` is self-visible at
`1`, at `2` unless `F` is prescribed `⊥`, and at `3` unless `G` is prescribed.  Every monotone
constraint passes from the ambient by `le_of_approx`; `VisibilityReplaceFixedOfLT` and the exclusion
of collisions take separate case analyses.  Every capped lift of the thin completion into
`(univ, k)`, `k ≤ 3`, is an instance (`ThinCompletion.exists_lift_left`,
`ThinCompletion.exists_lift_right`).  The lift of the necessary condition of
`VaughtConjecture.Extension.SeparatingCell`, from `(C, 3)` with the prescription `(A, ⊤, ⊤)`, is
`exists_criticalLift`: it sets `A_D := ⊤`, and the new cell at `(univ, 2)` then reads
`A_C = A ≤ ⊤ = A_D`, strictly below when `A ≠ ⊤` (as in the necessary condition); the theorem
also allows `A = ⊤`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ThinCompletion

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftExistsCounterexample

/-! ### The two-strip shifter: the ordered cell at `(univ, 2)` -/

open Classical in
/-- The strip of `A` at the grade `2`, read off the finite part of `x`: `visibilityReplace 2 j A`
for `j = min (finite part of x) 2`. -/
private noncomputable def strip2 (A x : Label.{u}) : Label.{u} :=
  if IsSelfVisible 2 x then visibilityReplace 2 2 A
  else if IsSelfVisible 1 x then visibilityReplace 2 1 A else visibilityReplace 2 0 A

/-- The strip of `A` at a label `ω * q + n` is `visibilityReplace 2 (min n 2) A`. -/
private theorem strip2_block (A : Label.{u}) (q : Ordinal.{u}) (n : ℕ) :
    strip2 A ((ω * q + n : Ordinal.{u}) : Label.{u}) = visibilityReplace 2 (min n 2) A := by
  unfold strip2
  simp only [isSelfVisible_block]
  split_ifs with h2 h1
  · congr 1; omega
  · congr 1; omega
  · congr 1; omega

open Classical in
/-- **The two-strip shifter**: `⊥ ↦ ⊥`; on the block `0` (the natural numbers) the strip of `a`;
on the block `1` (`ω + n`) the strip of `b`; every other label to `f`. -/
noncomputable def twoStrip (a b f x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥
  else if x < ((ω * 1 : Ordinal.{u}) : Label.{u}) then strip2 a x
  else if x < ((ω * 2 : Ordinal.{u}) : Label.{u}) then strip2 b x
  else f

variable {a b f : Label.{u}}

/-- The two-strip shifter fixes `⊥`. -/
theorem twoStrip_bot : twoStrip a b f ⊥ = ⊥ := by unfold twoStrip; simp

/-- The two-strip shifter sends `⊤` to `f`. -/
theorem twoStrip_top : twoStrip a b f ⊤ = f := by
  unfold twoStrip
  rw [ite_eq_right (by simp), ite_eq_right (not_lt.mpr le_top), ite_eq_right (not_lt.mpr le_top)]

/-- The two-strip shifter on a label `ω * q + n`: the strip of `a` on the block `0`, the strip of
`b` on the block `1`, and `f` above. -/
theorem twoStrip_block (q : Ordinal.{u}) (n : ℕ) :
    twoStrip a b f ((ω * q + n : Ordinal.{u}) : Label.{u}) =
      if q < 1 then visibilityReplace 2 (min n 2) a
      else if q < 2 then visibilityReplace 2 (min n 2) b else f := by
  unfold twoStrip
  simp only [coe_block_lt_iff, strip2_block]
  rw [ite_eq_right WithBot.coe_ne_bot]

/-- An ordinal at least `1` and below `2` is `1`. -/
private theorem one_le_lt_two {q : Ordinal.{u}} (h1 : ¬ q < 1) (h2 : q < 2) : q = 1 := by
  have : q ≤ 1 := by
    rw [← one_add_one_eq_two] at h2
    exact Order.lt_add_one_iff.mp h2
  exact le_antisymm this (not_lt.mp h1)

/-- The two-strip shifter is at most `f` when the strips are ordered below `f`. -/
theorem twoStrip_le_f (hab : visibilityReplace 2 2 a ≤ visibilityReplace 2 0 b)
    (hbf : visibilityReplace 2 2 b ≤ f) (x : Label.{u}) : twoStrip a b f x ≤ f := by
  have hb0 : visibilityReplace 2 0 b ≤ visibilityReplace 2 2 b :=
    Label.visibilityReplace_le_visibilityReplace (by omega) b
  by_cases hx : x = ⊥
  · rw [hx, twoStrip_bot]; exact bot_le
  by_cases hxt : x = ⊤
  · rw [hxt, twoStrip_top]
  obtain ⟨q, n, rfl⟩ := exists_block hx hxt
  rw [twoStrip_block]
  split_ifs
  · exact (Label.visibilityReplace_le_visibilityReplace (by omega) a).trans
      (hab.trans (hb0.trans hbf))
  · exact (Label.visibilityReplace_le_visibilityReplace (by omega) b).trans
      hbf
  · exact le_rfl

/-- The two-strip shifter is monotone when the strip of `a` lies below that of `b` and the strip
of `b` below `f`. -/
theorem monotone_twoStrip (hab : visibilityReplace 2 2 a ≤ visibilityReplace 2 0 b)
    (hbf : visibilityReplace 2 2 b ≤ f) : Monotone (twoStrip a b f) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, twoStrip_bot]; exact bot_le
  by_cases hy : y = ⊤
  · rw [hy, twoStrip_top]; exact twoStrip_le_f hab hbf x
  have hy0 : y ≠ ⊥ := fun h ↦ hx (le_bot_iff.mp (h ▸ hxy))
  have hxt : x ≠ ⊤ := fun h ↦ hy (top_le_iff.mp (h ▸ hxy))
  obtain ⟨q, n, rfl⟩ := exists_block hx hxt
  obtain ⟨q', n', rfl⟩ := exists_block hy0 hy
  rw [WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff] at hxy
  rw [twoStrip_block, twoStrip_block]
  have hvr := fun (A : Label.{u}) (i j : ℕ) (h : i ≤ j) ↦
    Label.visibilityReplace_le_visibilityReplace (k := 2) h A
  rcases hxy with hlt | ⟨rfl, hle⟩
  · by_cases h1' : q' < 1
    · exfalso
      rw [Order.lt_one_iff.mp h1'] at hlt
      exact (not_lt.mpr (zero_le (a := q))) hlt
    rw [ite_eq_right h1']
    by_cases h1 : q < 1
    · rw [ite_eq_left h1]
      by_cases h2' : q' < 2
      · rw [ite_eq_left h2']
        exact (hvr a _ 2 (by omega)).trans (hab.trans (hvr b 0 _ (by omega)))
      · rw [ite_eq_right h2']
        exact (hvr a _ 2 (by omega)).trans (hab.trans ((hvr b 0 2 (by omega)).trans hbf))
    · rw [ite_eq_right h1]
      by_cases h2' : q' < 2
      · exfalso
        have hq' := one_le_lt_two h1' h2'
        rw [hq'] at hlt
        exact h1 hlt
      · rw [ite_eq_right h2']
        by_cases h2 : q < 2
        · rw [ite_eq_left h2]; exact (hvr b _ 2 (by omega)).trans hbf
        · rw [ite_eq_right h2]
  · by_cases h1 : q < 1
    · rw [ite_eq_left h1, ite_eq_left h1]; exact hvr a _ _ (by omega)
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : q < 2
      · rw [ite_eq_left h2, ite_eq_left h2]; exact hvr b _ _ (by omega)
      · rw [ite_eq_right h2, ite_eq_right h2]

/-- **The two-strip shifter is a witness** for the suppressor `f` up to the grade `2`, when the
strip of `a` lies below that of `b` (`visibilityReplace 2 2 a ≤ visibilityReplace 2 0 b`) and the
strip of `b` below `f`. -/
theorem isWitness_twoStrip (hf : IsSelfVisible 2 f)
    (hab : visibilityReplace 2 2 a ≤ visibilityReplace 2 0 b)
    (hbf : visibilityReplace 2 2 b ≤ f) :
    IsWitness (constStepSuppressor 2 f) (twoStrip a b f) where
  antitone := antitone_constStepSuppressor 2 f
  isSelfVisible := isSelfVisible_constStepSuppressor hf
  map_bot := twoStrip_bot
  monotone := monotone_twoStrip hab hbf
  visibilityReplace_comm x k hx i hi := by
    by_cases hx0 : x = ⊥
    · rw [hx0, visibilityReplace_bot, twoStrip_bot, visibilityReplace_bot]
    by_cases hk : k ≤ 2
    · by_cases hxt : x = ⊤
      · rw [hxt, visibilityReplace_top, twoStrip_top, (hf.mono hk).visibilityReplace_eq]
      obtain ⟨q, n, rfl⟩ := exists_block hx0 hxt
      have hm : min (if n < k then i else n) 2 = if min n 2 < k then i else min n 2 := by
        split_ifs <;> omega
      rw [visibilityReplace_block, twoStrip_block, twoStrip_block]
      by_cases h1 : q < 1
      · rw [ite_eq_left h1, ite_eq_left h1, visibilityReplace_visibilityReplace_of_le hk, hm]
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : q < 2
        · rw [ite_eq_left h2, ite_eq_left h2, visibilityReplace_visibilityReplace_of_le hk, hm]
        · rw [ite_eq_right h2, ite_eq_right h2]
          exact ((hf.mono hk).visibilityReplace_eq i).symm
    · have hg : constStepSuppressor 2 f k = ⊥ := by
        unfold constStepSuppressor; rw [ite_eq_right hk]
      rw [hg, le_bot_iff] at hx
      rw [hx, visibilityReplace_bot]
      by_cases hxt : x = ⊤
      · rw [hxt, twoStrip_top] at hx
        rw [hxt, visibilityReplace_top, twoStrip_top, hx]
      obtain ⟨q, n, rfl⟩ := exists_block hx0 hxt
      rw [twoStrip_block] at hx
      rw [visibilityReplace_block, twoStrip_block]
      by_cases h1 : q < 1
      · rw [ite_eq_left h1] at hx ⊢
        rw [visibilityReplace_eq_bot_iff] at hx ⊢; exact hx
      · rw [ite_eq_right h1] at hx ⊢
        by_cases h2 : q < 2
        · rw [ite_eq_left h2] at hx ⊢
          rw [visibilityReplace_eq_bot_iff] at hx ⊢; exact hx
        · rw [ite_eq_right h2] at hx ⊢; exact hx

/-- **The strips do not overlap** unless the collision occurs: for `a ≤ b` self-visible at `1`,
`visibilityReplace 2 2 a ≤ visibilityReplace 2 0 b` unless `a = b` with finite part `1`. -/
theorem visibilityReplace_two_two_le_visibilityReplace_two_zero {a b : Label.{u}}
    (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b)
    (hab : a ≤ b) (hnc : a = b → IsSelfVisible 2 a) :
    visibilityReplace 2 2 a ≤ visibilityReplace 2 0 b := by
  rcases hab.lt_or_eq with hlt | rfl
  · by_cases hb2 : IsSelfVisible 2 b
    · rw [(hb2.visibilityReplace_eq 0)]; exact visibilityReplace_two_two_le_of_lt ha hlt
    -- `b = μ + 1`: then `a ≤ μ`, in an earlier block or `⊥`.
    have hb0 : b ≠ ⊥ := ne_bot_of_gt hlt
    have hbt : b ≠ ⊤ := fun h ↦ hb2 (h ▸ isSelfVisible_top 2)
    obtain ⟨q', n', rfl⟩ := exists_block hb0 hbt
    have hn1 : 1 ≤ n' := isSelfVisible_block.mp hb
    have hn2 : ¬ 2 ≤ n' := fun h ↦ hb2 (isSelfVisible_block.mpr h)
    obtain rfl : n' = 1 := by omega
    rw [visibilityReplace_block, ite_eq_left (by omega)]
    by_cases ha0 : a = ⊥
    · rw [ha0, visibilityReplace_bot]; exact bot_le
    have hat : a ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨q, n, rfl⟩ := exists_block ha0 hat
    have hn : 1 ≤ n := isSelfVisible_block.mp ha
    rw [visibilityReplace_block, WithBot.coe_le_coe, WithTop.coe_le_coe]
    rw [WithBot.coe_lt_coe, WithTop.coe_lt_coe] at hlt
    have hq : q < q' := by
      rcases (omega0_mul_add_natCast_le_iff.mp hlt.le) with h | ⟨rfl, h⟩
      · exact h
      · exact absurd (add_lt_add_iff_left _ |>.mp hlt) (by exact_mod_cast (by omega : ¬ n < 1))
    exact (omega0_mul_add_natCast_lt hq _ _).le
  · rw [hnc rfl, (hnc rfl).visibilityReplace_eq 0]

/-! ### The ordered cell at `(univ, 1)` -/

open Classical in
/-- `⊥ ↦ ⊥`, the natural numbers to `a`, every other label to `b`. -/
noncomputable def blockConst (a b x : Label.{u}) : Label.{u} :=
  if x = ⊥ then ⊥ else if x < ((ω * 1 : Ordinal.{u}) : Label.{u}) then a else b

/-- `blockConst a b` on a label `ω * q + n`: `a` on the block `0` and `b` above. -/
theorem blockConst_block (q : Ordinal.{u}) (n : ℕ) :
    blockConst a b ((ω * q + n : Ordinal.{u}) : Label.{u}) = if q < 1 then a else b := by
  unfold blockConst
  simp only [coe_block_lt_iff]
  rw [ite_eq_right WithBot.coe_ne_bot]

/-- **`blockConst a b` is a witness** for the suppressor `b` up to the grade `1`, for `a ≤ b`
self-visible at `1`. -/
theorem isWitness_blockConst (ha : IsSelfVisible 1 a) (hb : IsSelfVisible 1 b) (hab : a ≤ b) :
    IsWitness (constStepSuppressor 1 b) (blockConst a b) where
  antitone := antitone_constStepSuppressor 1 b
  isSelfVisible := isSelfVisible_constStepSuppressor hb
  map_bot := by unfold blockConst; simp
  monotone := by
    intro x y hxy
    unfold blockConst
    by_cases hx : x = ⊥
    · simp [hx]
    have hy : y ≠ ⊥ := fun h ↦ hx (le_bot_iff.mp (h ▸ hxy))
    rw [ite_eq_right hx, ite_eq_right hy]
    by_cases hyω : y < ((ω * 1 : Ordinal.{u}) : Label.{u})
    · rw [ite_eq_left (hxy.trans_lt hyω), ite_eq_left hyω]
    · rw [ite_eq_right hyω]
      split_ifs
      · exact hab
      · exact le_rfl
  visibilityReplace_comm x k hx i hi := by
    by_cases hx0 : x = ⊥
    · rw [hx0, visibilityReplace_bot]; unfold blockConst; simp
    by_cases hxt : x = ⊤
    · have hbt : blockConst a b ⊤ = b := by
        unfold blockConst; rw [ite_eq_right (by simp), ite_eq_right (not_lt.mpr le_top)]
      rw [hxt, visibilityReplace_top, hbt]
      by_cases hk : k ≤ 1
      · exact ((hb.mono hk).visibilityReplace_eq i).symm
      · have hg : constStepSuppressor 1 b k = ⊥ := by
          unfold constStepSuppressor; rw [ite_eq_right hk]
        rw [hxt, hbt, hg, le_bot_iff] at hx
        rw [hx, visibilityReplace_bot]
    obtain ⟨q, n, rfl⟩ := exists_block hx0 hxt
    rw [visibilityReplace_block, blockConst_block, blockConst_block]
    by_cases hk : k ≤ 1
    · split_ifs
      · exact ((ha.mono hk).visibilityReplace_eq i).symm
      · exact ((hb.mono hk).visibilityReplace_eq i).symm
    · have hg : constStepSuppressor 1 b k = ⊥ := by
        unfold constStepSuppressor; rw [ite_eq_right hk]
      rw [hg, le_bot_iff, blockConst_block] at hx
      split_ifs at hx ⊢ <;> rw [hx, visibilityReplace_bot]


/-! ### The rows of the new cells, by kinds -/

/-- The labels of the six **kinds** of cells of the thin completion, in this order: the dead cells
(`⊥`), the live cells of grade `1` of `C` (`A_C`), those of `D` and the new cell at `(univ, 1)`
(`A_D`), the live cells of grade `2` (`F`), those of grade `3` (`G`), and those of grade `4`
(`Ω`). -/
def kindLabel (AC AD F G Ω : Label.{u}) : Fin 6 → Label.{u} := ![⊥, AC, AD, F, G, Ω]

/-- The dead cells carry `⊥`. -/
@[simp] theorem kindLabel_zero (AC AD F G Ω : Label.{u}) : kindLabel AC AD F G Ω 0 = ⊥ := rfl

/-- The **ordered rows** of the new cells of the thin completion, by kinds.  The rows at
`(univ, 1)` and `(univ, 2)` read the live cells of grade `1` of `C` at `1` and those of `D` at
`ω + 1`, in an earlier block; the row at `(univ, 3)` reads the live cells of grade `1` of `C` at
`1` and every other live cell at `ω + 3` (the row of the cell `18` of `TL`); the row at `(univ, 4)`
reads only the cells of grade `4`. -/
noncomputable def thinRow : ℕ → Fin 6 → Label.{u}
  | 1 => kindLabel (gridPoint 1 0) (gridPoint 1 1) ⊥ ⊥ ⊥
  | 2 => kindLabel (gridPoint 1 0) (gridPoint 1 1) (gridPoint 2 2) ⊥ ⊥
  | 3 => kindLabel (gridPoint 1 0) (gridPoint 3 1) (gridPoint 3 1) (gridPoint 3 1) ⊥
  | _ => kindLabel ⊥ ⊥ ⊥ ⊥ (gridPoint 4 1)

/-- The rows of the new cells are coded. -/
theorem thinRow_lt (k : ℕ) (i : Fin 6) :
    thinRow.{u} k i < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) := by
  have hb : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
    WithBot.bot_lt_coe _
  rcases k with _ | _ | _ | _ | k <;> fin_cases i <;>
    first | exact hb | exact gridPoint_lt_omega0_sq _ _

/-- The row at `(univ, 1)` transforms on the cells of grade `1`. -/
theorem transformsTo_rowOne {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 1) (hk : ∀ d, (kind d : ℕ) ≤ 2) {AC AD F G Ω : Label.{u}}
    (hAC : IsSelfVisible 1 AC) (hAD : IsSelfVisible 1 AD) (hle : AC ≤ AD) :
    TransformsTo grade (fun d ↦ thinRow 1 (kind d))
      (fun d ↦ min (kindLabel AC AD F G Ω (kind d)) AD) := by
  refine ⟨constStepSuppressor 1 AD, blockConst AC AD, isWitness_blockConst hAC hAD hle,
    fun d ↦ ?_⟩
  have hg : constStepSuppressor 1 AD (grade d) = AD := by
    unfold constStepSuppressor; rw [ite_eq_left (hgr d)]
  rw [hg]
  dsimp only
  have h := hk d
  generalize kind d = k at h ⊢
  -- In each case, `change` evaluates `kindLabel` and `thinRow 1` at the kind.
  fin_cases k
  · change min ⊥ AD = min (blockConst AC AD ⊥) AD
    unfold blockConst; simp
  · change min AC AD = min (blockConst AC AD (gridPoint 1 0)) AD
    rw [gridPoint, blockConst_block, ite_eq_left (by simp)]
  · change min AD AD = min (blockConst AC AD (gridPoint 1 1)) AD
    rw [gridPoint, blockConst_block, ite_eq_right (by simp)]
  all_goals exact absurd h (by decide)

/-- **The ordered cell at `(univ, 2)`.**  The row at `(univ, 2)` transforms on the cells of grade
at most `2`, through the two-strip shifter, provided `A_C ≤ A_D` and there is no collision
(`A_C = A_D < F` forces `A_C` self-visible at `2`). -/
theorem transformsTo_rowTwo {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 2) (hk : ∀ d, (kind d : ℕ) ≤ 3) {AC AD F G Ω : Label.{u}}
    (hAC : IsSelfVisible 1 AC) (hAD : IsSelfVisible 1 AD) (hF : IsSelfVisible 2 F)
    (hle : AC ≤ AD) (hnc : AC = AD → AC < F → IsSelfVisible 2 AC) :
    TransformsTo grade (fun d ↦ thinRow 2 (kind d))
      (fun d ↦ min (kindLabel AC AD F G Ω (kind d)) F) := by
  have ha : IsSelfVisible 1 (min AC F) := hAC.min (hF.mono (by omega))
  have hb : IsSelfVisible 1 (min AD F) := hAD.min (hF.mono (by omega))
  have hab : min AC F ≤ min AD F := min_le_min_right F hle
  have hnc' : min AC F = min AD F → IsSelfVisible 2 (min AC F) := by
    intro heq
    rcases le_total F AC with hFA | hAF
    · rw [min_eq_right hFA]; exact hF
    · rcases hAF.lt_or_eq with hAF | rfl
      · rw [min_eq_left hAF.le]
        rcases le_total F AD with hFD | hDF
        · rw [min_eq_left hAF.le, min_eq_right hFD] at heq; exact absurd heq hAF.ne
        · rw [min_eq_left hAF.le, min_eq_left hDF] at heq; exact hnc heq hAF
      · rw [min_self]; exact hF
  refine ⟨constStepSuppressor 2 F, twoStrip (min AC F) (min AD F) F,
    isWitness_twoStrip hF (visibilityReplace_two_two_le_visibilityReplace_two_zero ha hb hab hnc')
      (visibilityReplace_le_of_le le_rfl hF (min_le_right _ _)), fun d ↦ ?_⟩
  have hg : constStepSuppressor 2 F (grade d) = F := by
    unfold constStepSuppressor; rw [ite_eq_left (hgr d)]
  rw [hg]
  dsimp only
  have h := hk d
  generalize kind d = k at h ⊢
  -- In each case, `change` evaluates `kindLabel` and `thinRow 2` at the kind.
  fin_cases k
  · change min ⊥ F = min (twoStrip _ _ F ⊥) F
    rw [twoStrip_bot]
  · change min AC F = min (twoStrip _ _ F (gridPoint 1 0)) F
    rw [gridPoint, twoStrip_block, ite_eq_left (by simp), show min 1 2 = 1 from rfl,
      visibilityReplace_two_one_of_isSelfVisible ha, min_assoc, min_self]
  · change min AD F = min (twoStrip _ _ F (gridPoint 1 1)) F
    rw [gridPoint, twoStrip_block, ite_eq_right (by simp), ite_eq_left (by simp),
      show min 1 2 = 1 from rfl,
      visibilityReplace_two_one_of_isSelfVisible hb, min_assoc, min_self]
  · change min F F = min (twoStrip _ _ F (gridPoint 2 2)) F
    rw [gridPoint, twoStrip_block, ite_eq_right (by simp), ite_eq_right (by simp)]
  all_goals exact absurd h (by decide)

/-- The row at `(univ, 3)` (the row of the cell `18` of `TL`, read on every cell below
`(univ, 3)`) transforms on the cells of grade at most `3`, through the strip shifter at the grade
`3`, under `VisibilityReplaceFixedOfLT A_C G`, `G ≤ A_D` and `G ≤ F`. -/
theorem transformsTo_rowThree {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 3) (hk : ∀ d, (kind d : ℕ) ≤ 4) {AC AD F G Ω : Label.{u}}
    (hG : IsSelfVisible 3 G) (hc : VisibilityReplaceFixedOfLT AC G) (hGAD : G ≤ AD) (hGF : G ≤ F) :
    TransformsTo grade (fun d ↦ thinRow 3 (kind d))
      (fun d ↦ min (kindLabel AC AD F G Ω (kind d)) G) := by
  refine ⟨constStepSuppressor 3 G, strip3 AC, isWitness_strip3 hG, fun d ↦ ?_⟩
  have hg : constStepSuppressor 3 G (grade d) = G := by
    unfold constStepSuppressor; rw [ite_eq_left (hgr d)]
  rw [hg]
  have hnl : ¬ (gridPoint 3 1 : Label.{u}) < ((ω : Ordinal.{u}) : Label.{u}) := by
    rw [not_lt, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
    calc (ω : Ordinal.{u}) = ω * ((1 : ℕ) : Ordinal.{u}) := by simp
      _ ≤ _ := le_self_add
  have htop : strip3 AC (gridPoint 3 1) = ⊤ := strip3_of_not_lt (gridPoint_ne_bot 3 1) hnl
  dsimp only
  have h := hk d
  generalize kind d = k at h ⊢
  -- In each case, `change` evaluates `kindLabel` and `thinRow 3` at the kind.
  fin_cases k
  · change min ⊥ G = min (strip3 AC ⊥) G
    rw [strip3_bot]
  · change min AC G = min (strip3 AC (gridPoint 1 0)) G
    rw [show (gridPoint 1 0 : Label.{u}) = ((1 : ℕ) : Label.{u}) from
      TwoFaceLiftCounterexample.v1_eq, strip3_natCast, show min 1 3 = 1 from rfl,
      min_visibilityReplace_three_one hG hc]
  · change min AD G = min (strip3 AC (gridPoint 3 1)) G
    rw [htop, min_top_left, min_eq_right hGAD]
  · change min F G = min (strip3 AC (gridPoint 3 1)) G
    rw [htop, min_top_left, min_eq_right hGF]
  · change min G G = min (strip3 AC (gridPoint 3 1)) G
    rw [htop, min_top_left, min_self]
  · exact absurd h (by decide)

/-- **The top shifter on a row with one nonzero kind.**  If the suppressor `Ω` is self-visible at
`K` and every grade is at most `K`, a row transforms to the labelling that is `Ω` where the row is
not `⊥` and `⊥` where it is. -/
theorem transformsTo_topShifter {D : Type*} (grade : D → ℕ) {K : ℕ} (hgr : ∀ d, grade d ≤ K)
    {Ω : Label.{u}} (hΩ : IsSelfVisible K Ω) (r q : D → Label.{u})
    (hq : ∀ d, q d = if r d = ⊥ then ⊥ else Ω) : TransformsTo grade r q := by
  refine ⟨constStepSuppressor K Ω, topShifter,
    isWitness_topShifter (antitone_constStepSuppressor _ _)
      (isSelfVisible_constStepSuppressor hΩ), fun d ↦ ?_⟩
  have hg : constStepSuppressor K Ω (grade d) = Ω := by
    unfold constStepSuppressor; rw [ite_eq_left (hgr d)]
  rw [hg, hq, topShifter]
  split_ifs <;> simp

/-- The row at `(univ, 4)` transforms, through the top shifter, to `Ω` at the cells of grade `4`
and `⊥` elsewhere. -/
theorem transformsTo_rowFour {D : Type*} (grade : D → ℕ) (kind : D → Fin 6)
    (hgr : ∀ d, grade d ≤ 4) {Ω : Label.{u}} (hΩ : IsSelfVisible 4 Ω) :
    TransformsTo grade (fun d ↦ thinRow 4 (kind d))
      (fun d ↦ min (kindLabel ⊥ ⊥ ⊥ ⊥ Ω (kind d)) Ω) := by
  refine transformsTo_topShifter grade hgr hΩ _ _ fun d ↦ ?_
  generalize kind d = k
  fin_cases k <;> simp [thinRow, kindLabel, gridPoint_ne_bot]


/-! ### The parameter-level capped lift -/

/-- **The constraints of the thin completion below `(univ, 3)`** on the parameters `A_C` (the live
cells of grade `1` of `C`), `A_D` (those of `D`, and the new cell at `(univ, 1)`), `F` (the cells
`(C, 2)`, `(D, 2)` and the new cell at `(univ, 2)`) and `G` (the live cells of grade `3`, and the
new cell at `(univ, 3)`). -/
structure IsThinLawfulBelow (AC AD F G : Label.{u}) : Prop where
  /-- `A_C` is self-visible at `1`. -/
  svAC : IsSelfVisible 1 AC
  /-- `A_D` is self-visible at `1`. -/
  svAD : IsSelfVisible 1 AD
  /-- `F` is self-visible at `2`. -/
  svF : IsSelfVisible 2 F
  /-- `G` is self-visible at `3`. -/
  svG : IsSelfVisible 3 G
  /-- The ordered row at `(univ, 1)`: `A_C ≤ A_D`. -/
  le_AD : AC ≤ AD
  /-- The coupling of `TL` at its cell `18`: `G ≤ F`. -/
  G_le_F : G ≤ F
  /-- The coupling of `T5`: `G ≤ A_D`. -/
  G_le_AD : G ≤ AD
  /-- The condition of `TL` on the finite part of `A_C` below `G`. -/
  visibilityReplaceFixed : VisibilityReplaceFixedOfLT AC G
  /-- No collision at `(univ, 2)`: `A_C = A_D < F` forces `A_C` self-visible at `2`. -/
  noCollision : AC = AD → AC < F → IsSelfVisible 2 AC

/-- The lifted value of a parameter: the prescription if there is one; otherwise the ambient
value if it lies below the cap, and the value `hi ≥ c` otherwise. -/
private noncomputable def liftedParam (P : Option Label.{u}) (qz c hi : Label.{u}) : Label.{u} :=
  open Classical in P.getD (if qz < c then qz else hi)

section Choose

variable {P : Option Label.{u}} {qz c hi : Label.{u}}

/-- The chosen value agrees with the ambient value capped at `c`. -/
private theorem min_liftedParam (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi) :
    min (liftedParam P qz c hi) c = min qz c := by
  unfold liftedParam
  cases P with
  | some a => exact hP a rfl
  | none =>
    simp only [Option.getD_none]
    split_ifs with h
    · rfl
    · rw [min_eq_right hhi, min_eq_right (not_lt.mp h)]

/-- A chosen value below the cap is the ambient value. -/
private theorem liftedParam_eq_of_lt (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi)
    (h : liftedParam P qz c hi < c) : liftedParam P qz c hi = qz := by
  have hm := min_liftedParam hP hhi
  rw [min_eq_left h.le] at hm
  rcases lt_or_ge qz c with hq | hq
  · rw [min_eq_left hq.le] at hm; exact hm
  · rw [min_eq_right hq] at hm; exact absurd hm h.ne

/-- At an ambient value below the cap, the chosen value is the ambient value. -/
private theorem liftedParam_eq_of_q_lt (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi)
    (h : qz < c) : liftedParam P qz c hi = qz := by
  have hm := min_liftedParam hP hhi
  rw [min_eq_left h.le] at hm
  rcases lt_or_ge (liftedParam P qz c hi) c with hx | hx
  · rw [min_eq_left hx.le] at hm; exact hm
  · rw [min_eq_right hx] at hm; exact absurd hm h.ne'

/-- At an ambient value at least the cap, the chosen value is at least the cap. -/
private theorem le_liftedParam_of_le (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi)
    (h : c ≤ qz) : c ≤ liftedParam P qz c hi := by
  have hm := min_liftedParam hP hhi
  rw [min_eq_right h] at hm
  exact min_eq_right_iff.mp hm

/-- A chosen value at least the cap comes from an ambient value at least the cap. -/
private theorem le_of_le_liftedParam (hP : ∀ a ∈ P, min a c = min qz c) (hhi : c ≤ hi)
    (h : c ≤ liftedParam P qz c hi) : c ≤ qz := by
  have hm := min_liftedParam hP hhi
  rw [min_eq_right h] at hm
  exact min_eq_right_iff.mp hm.symm

/-- Unprescribed, at an ambient value at least the cap, the chosen value is `hi`. -/
private theorem liftedParam_none_of_le (h : c ≤ qz) : liftedParam none qz c hi = hi := by
  unfold liftedParam; simp [not_lt.mpr h]

/-- A prescribed value is chosen. -/
private theorem liftedParam_some (a : Label.{u}) : liftedParam (some a) qz c hi = a := rfl

end Choose

/-- A monotone constraint survives the choice if it holds for the ambient and for the values at
or above the cap. -/
private theorem le_of_approx {c xz xw qz qw : Label.{u}} (hq : qz ≤ qw)
    (hz' : qz < c → xz = qz) (hw : xw < c → xw = qw)
    (hhigh : c ≤ xz → c ≤ xw → xz ≤ xw) : xz ≤ xw := by
  by_cases hwc : xw < c
  · rw [hw hwc]
    have : qz < c := hq.trans_lt ((hw hwc) ▸ hwc)
    rw [hz' this]; exact hq
  · by_cases hzc : xz < c
    · exact hzc.le.trans (not_lt.mp hwc)
    · exact hhigh (not_lt.mp hzc) (not_lt.mp hwc)

/-- **The parameter-level capped lift.**  Let `q = (q_AC, q_AD, q_F, q_G)` satisfy
`IsThinLawfulBelow` (the ambient), let `c` be a cap, and let a prescription fix some of the
parameters (`some`), subject to the constraints of `IsThinLawfulBelow` among the prescribed
parameters and agreeing with `q` capped at `c`.  Then some `x` satisfies `IsThinLawfulBelow`, agrees
with `q` capped at `c`, and equals the prescription where it is given.

The choice: an unprescribed parameter keeps its ambient value below the cap; at or above the cap,
`G := c`, `A_D := ⊤`, and `F, A_C := max c G`.  The hypotheses on the cap: `c` self-visible at
`1`; at `2` unless `F` is prescribed `⊥` (the pairs `(·, (univ, 1))`); at `3` unless `G` is
prescribed (the pairs `(·, (univ, j))`, `j ≤ 2`, prescribe `G = ⊥`). -/
theorem exists_thinLift {c : Label.{u}} (hc1 : IsSelfVisible 1 c)
    {PAC PAD PF PG : Option Label.{u}}
    (hc2 : IsSelfVisible 2 c ∨ PF = some ⊥) (hc3 : IsSelfVisible 3 c ∨ PG.isSome)
    {qAC qAD qF qG : Label.{u}} (hq : IsThinLawfulBelow qAC qAD qF qG)
    (svAC : ∀ a ∈ PAC, IsSelfVisible 1 a) (svAD : ∀ a ∈ PAD, IsSelfVisible 1 a)
    (svF : ∀ a ∈ PF, IsSelfVisible 2 a) (svG : ∀ a ∈ PG, IsSelfVisible 3 a)
    (pleAD : ∀ a ∈ PAC, ∀ b ∈ PAD, a ≤ b) (pGF : ∀ g ∈ PG, ∀ f ∈ PF, g ≤ f)
    (pGAD : ∀ g ∈ PG, ∀ b ∈ PAD, g ≤ b)
    (pcond : ∀ a ∈ PAC, ∀ g ∈ PG, VisibilityReplaceFixedOfLT a g)
    (pnc : ∀ a ∈ PAC, ∀ b ∈ PAD, ∀ f ∈ PF, a = b → a < f → IsSelfVisible 2 a)
    (hAC : ∀ a ∈ PAC, min a c = min qAC c) (hAD : ∀ a ∈ PAD, min a c = min qAD c)
    (hF : ∀ a ∈ PF, min a c = min qF c) (hG : ∀ a ∈ PG, min a c = min qG c) :
    ∃ xAC xAD xF xG : Label.{u}, IsThinLawfulBelow xAC xAD xF xG ∧
      min xAC c = min qAC c ∧ min xAD c = min qAD c ∧ min xF c = min qF c ∧
      min xG c = min qG c ∧
      (∀ a ∈ PAC, xAC = a) ∧ (∀ a ∈ PAD, xAD = a) ∧ (∀ a ∈ PF, xF = a) ∧ (∀ a ∈ PG, xG = a) := by
  -- The lifted parameters: the prescription where given; otherwise the ambient below the cap, and
  -- `c`, `⊤`, `max c G`, `max c G` (for `G`, `A_D`, `F`, `A_C`) at or above it.
  set xG := liftedParam PG qG c c with hxG
  set xAD := liftedParam PAD qAD c ⊤ with hxAD
  set xF := liftedParam PF qF c (max c xG) with hxF
  set xAC := liftedParam PAC qAC c (max c xG) with hxAC
  have hcG : c ≤ c := le_rfl
  have hcT : c ≤ ⊤ := le_top
  have hcM : c ≤ max c xG := le_max_left _ _
  -- The approximation facts.
  have eG : xG < c → xG = qG := liftedParam_eq_of_lt hG hcG
  have eG' : qG < c → xG = qG := liftedParam_eq_of_q_lt hG hcG
  have eAD : xAD < c → xAD = qAD := liftedParam_eq_of_lt hAD hcT
  have eAD' : qAD < c → xAD = qAD := liftedParam_eq_of_q_lt hAD hcT
  have eF : xF < c → xF = qF := liftedParam_eq_of_lt hF hcM
  have eF' : qF < c → xF = qF := liftedParam_eq_of_q_lt hF hcM
  have eAC : xAC < c → xAC = qAC := liftedParam_eq_of_lt hAC hcM
  have eAC' : qAC < c → xAC = qAC := liftedParam_eq_of_q_lt hAC hcM
  -- Values at or above the cap, unprescribed.
  have hiG : PG = none → c ≤ xG → xG = c := fun h hle ↦ by
    have hq' : c ≤ qG := le_of_le_liftedParam hG hcG hle
    rw [hxG, h]; exact liftedParam_none_of_le hq'
  have hiAD : PAD = none → c ≤ xAD → xAD = ⊤ := fun h hle ↦ by
    have hq' : c ≤ qAD := le_of_le_liftedParam hAD hcT hle
    rw [hxAD, h]; exact liftedParam_none_of_le hq'
  have hiF : PF = none → c ≤ xF → xF = max c xG := fun h hle ↦ by
    have hq' : c ≤ qF := le_of_le_liftedParam hF hcM hle
    rw [hxF, h]; exact liftedParam_none_of_le hq'
  have hiAC : PAC = none → c ≤ xAC → xAC = max c xG := fun h hle ↦ by
    have hq' : c ≤ qAC := le_of_le_liftedParam hAC hcM hle
    rw [hxAC, h]; exact liftedParam_none_of_le hq'
  -- Self-visibility.
  have hsvG : IsSelfVisible 3 xG := by
    cases hPG : PG with
    | some g => rw [hxG, hPG, liftedParam_some]; exact svG g hPG
    | none =>
      rcases lt_or_ge xG c with h | h
      · rw [eG h]; exact hq.svG
      · rw [hiG hPG h]
        exact hc3.resolve_right (by rw [hPG]; simp)
  have hsvAD : IsSelfVisible 1 xAD := by
    cases hPAD : PAD with
    | some b => rw [hxAD, hPAD, liftedParam_some]; exact svAD b hPAD
    | none =>
      rcases lt_or_ge xAD c with h | h
      · rw [eAD h]; exact hq.svAD
      · rw [hiAD hPAD h]; exact isSelfVisible_top 1
  have hsvF : IsSelfVisible 2 xF := by
    cases hPF : PF with
    | some f => rw [hxF, hPF, liftedParam_some]; exact svF f hPF
    | none =>
      rcases lt_or_ge xF c with h | h
      · rw [eF h]; exact hq.svF
      · rw [hiF hPF h]
        exact (hc2.resolve_right (by rw [hPF]; simp)).max (hsvG.mono (by omega))
  have hsvAC : IsSelfVisible 1 xAC := by
    cases hPAC : PAC with
    | some a => rw [hxAC, hPAC, liftedParam_some]; exact svAC a hPAC
    | none =>
      rcases lt_or_ge xAC c with h | h
      · rw [eAC h]; exact hq.svAC
      · rw [hiAC hPAC h]; exact hc1.max (hsvG.mono (by omega))
  -- `G ≤ A_D`.
  have hGAD : xG ≤ xAD := le_of_approx hq.G_le_AD eG' eAD fun hz hw ↦ by
    cases hPAD : PAD with
    | none => rw [hiAD hPAD hw]; exact le_top
    | some b =>
      have hxb : xAD = b := by rw [hxAD, hPAD, liftedParam_some]
      cases hPG : PG with
      | some g =>
        have hxg : xG = g := by rw [hxG, hPG, liftedParam_some]
        rw [hxg, hxb]; exact pGAD g hPG b hPAD
      | none => rw [hiG hPG hz]; exact hw
  -- `A_C ≤ A_D`.
  have hACAD : xAC ≤ xAD := le_of_approx hq.le_AD eAC' eAD fun hz hw ↦ by
    cases hPAD : PAD with
    | none => rw [hiAD hPAD hw]; exact le_top
    | some b =>
      have hxb : xAD = b := by rw [hxAD, hPAD, liftedParam_some]
      cases hPAC : PAC with
      | some a =>
        have hxa : xAC = a := by rw [hxAC, hPAC, liftedParam_some]
        rw [hxa, hxb]; exact pleAD a hPAC b hPAD
      | none => rw [hiAC hPAC hz]; exact max_le hw hGAD
  -- `G ≤ F`.
  have hGF : xG ≤ xF := le_of_approx hq.G_le_F eG' eF fun hz hw ↦ by
    cases hPF : PF with
    | none => rw [hiF hPF hw]; exact le_max_right _ _
    | some f =>
      have hxf : xF = f := by rw [hxF, hPF, liftedParam_some]
      cases hPG : PG with
      | some g =>
        have hxg : xG = g := by rw [hxG, hPG, liftedParam_some]
        rw [hxg, hxf]; exact pGF g hPG f hPF
      | none => rw [hiG hPG hz]; exact hw
  -- `VisibilityReplaceFixedOfLT A_C G`.
  have hcond : VisibilityReplaceFixedOfLT xAC xG := by
    intro hlt
    rcases lt_or_ge xAC c with hz | hz
    · have hqAC := eAC hz
      have hqlt : qAC < qG := by
        rcases lt_or_ge xG c with hg | hg
        · rw [← hqAC, ← eG hg]; exact hlt
        · exact (hqAC ▸ hz).trans_le (le_of_le_liftedParam hG hcG hg)
      rw [hqAC]; exact hq.visibilityReplaceFixed hqlt
    · have hg : c ≤ xG := hz.trans hlt.le
      cases hPAC : PAC with
      | none => exact absurd hlt (not_lt.mpr (by rw [hiAC hPAC hz]; exact le_max_right _ _))
      | some a =>
        have hxa : xAC = a := by rw [hxAC, hPAC, liftedParam_some]
        cases hPG : PG with
        | none => exact absurd hlt (not_lt.mpr (by rw [hiG hPG hg]; exact hz))
        | some g =>
          have hxg : xG = g := by rw [hxG, hPG, liftedParam_some]
          rw [hxa] at hlt ⊢; rw [hxg] at hlt; exact pcond a hPAC g hPG hlt
  -- No collision.
  have hnc : xAC = xAD → xAC < xF → IsSelfVisible 2 xAC := by
    intro heq hlt
    rcases lt_or_ge xAC c with hz | hz
    · have hqAC := eAC hz
      have hqAD : xAD = qAD := eAD (heq ▸ hz)
      have hqlt : qAC < qF := by
        rcases lt_or_ge xF c with hf | hf
        · rw [← hqAC, ← eF hf]; exact hlt
        · exact (hqAC ▸ hz).trans_le (le_of_le_liftedParam hF hcM hf)
      rw [hqAC]
      exact hq.noCollision (by rw [← hqAC, ← hqAD]; exact heq) hqlt
    · have hw : c ≤ xAD := heq ▸ hz
      cases hPAD : PAD with
      | none => rw [heq, hiAD hPAD hw]; exact isSelfVisible_top 2
      | some b =>
        -- `F` unprescribed: `x_F ≤ x_AD`, no collision.
        cases hPF : PF with
        | none =>
          exfalso
          refine absurd hlt (not_lt.mpr ?_)
          rw [heq]
          rcases lt_or_ge xF c with hf | hf
          · exact hf.le.trans hw
          · rw [hiF hPF hf]; exact max_le hw hGAD
        | some f =>
          have hxf : xF = f := by rw [hxF, hPF, liftedParam_some]
          cases hPAC : PAC with
          | some a =>
            have hxa : xAC = a := by rw [hxAC, hPAC, liftedParam_some]
            have hxb : xAD = b := by rw [hxAD, hPAD, liftedParam_some]
            rw [hxa] at heq hlt ⊢; rw [hxb] at heq; rw [hxf] at hlt
            exact pnc a hPAC b hPAD f hPF heq hlt
          | none =>
            rw [hiAC hPAC hz]
            rcases hc2 with hc2 | hc2
            · exact hc2.max (hsvG.mono (by omega))
            · rw [hPF] at hc2
              rw [hxf, Option.some_inj.mp hc2] at hlt
              exact absurd hlt (not_lt.mpr bot_le)
  -- The constraints hold; agreement capped at `c` and with the prescription hold by construction.
  refine ⟨xAC, xAD, xF, xG,
    ⟨hsvAC, hsvAD, hsvF, hsvG, hACAD, hGF, hGAD, hcond, hnc⟩,
    min_liftedParam hAC hcM, min_liftedParam hAD hcT, min_liftedParam hF hcM,
    min_liftedParam hG hcG,
    fun a ha ↦ by rw [hxAC, Option.mem_def.mp ha, liftedParam_some],
    fun a ha ↦ by rw [hxAD, Option.mem_def.mp ha, liftedParam_some],
    fun a ha ↦ by rw [hxF, Option.mem_def.mp ha, liftedParam_some],
    fun a ha ↦ by rw [hxG, Option.mem_def.mp ha, liftedParam_some]⟩

/-! ### The critical lift and the rows of the new cells -/

/-- **The critical lift**, from `(C, 3)` to `(univ, 3)` with the prescription `(A, ⊤, ⊤)` of the
necessary condition, at every cap `c` self-visible at `3` and every ambient `q` satisfying
`IsThinLawfulBelow` and agreeing with it capped at `c`: some `A_D` completes the prescription to
parameters satisfying `IsThinLawfulBelow`, agreeing with `q` capped at `c`.  (In the thin
completion, the new cell at `(univ, 2)` then carries `F = ⊤` and reads `A_C = A ≤ ⊤ = A_D`; when
`A ≠ ⊤`, as in the necessary condition, it reads `A_C < A_D`, as that condition demands.  The
statement also allows `A = ⊤`.) -/
theorem exists_criticalLift {c A : Label.{u}} (hc : IsSelfVisible 3 c) (hA : IsSelfVisible 1 A)
    (hAc : VisibilityReplaceFixedOfLT A ⊤) {qAC qAD qF qG : Label.{u}}
    (hq : IsThinLawfulBelow qAC qAD qF qG)
    (hAq : min A c = min qAC c) (hFq : min ⊤ c = min qF c) (hGq : min ⊤ c = min qG c) :
    ∃ xAD : Label.{u}, IsThinLawfulBelow A xAD ⊤ ⊤ ∧ min xAD c = min qAD c := by
  obtain ⟨xAC, xAD, xF, xG, hx, -, hAD, -, -, hxa, -, hxf, hxg⟩ :=
    exists_thinLift (hc.mono (by omega)) (PAC := some A) (PAD := none) (PF := some ⊤)
      (PG := some ⊤) (.inl (hc.mono (by omega))) (.inr rfl) hq
      (fun a ha ↦ by rw [Option.mem_def, Option.some_inj] at ha; exact ha ▸ hA)
      (fun _ ha ↦ by simp at ha)
      (fun a ha ↦ by rw [Option.mem_def, Option.some_inj] at ha; exact ha ▸ isSelfVisible_top 2)
      (fun a ha ↦ by rw [Option.mem_def, Option.some_inj] at ha; exact ha ▸ isSelfVisible_top 3)
      (fun _ _ _ hb ↦ by simp at hb)
      (fun g hg f hf ↦ by
        rw [Option.mem_def, Option.some_inj] at hg hf; rw [← hg, ← hf])
      (fun _ _ _ hb ↦ by simp at hb)
      (fun a ha g hg ↦ by
        rw [Option.mem_def, Option.some_inj] at ha hg; rw [← ha, ← hg]; exact hAc)
      (fun _ _ _ hb ↦ by simp at hb)
      (fun a ha ↦ by rw [Option.mem_def, Option.some_inj] at ha; rw [← ha]; exact hAq)
      (fun _ ha ↦ by simp at ha)
      (fun a ha ↦ by rw [Option.mem_def, Option.some_inj] at ha; rw [← ha]; exact hFq)
      (fun a ha ↦ by rw [Option.mem_def, Option.some_inj] at ha; rw [← ha]; exact hGq)
  rw [hxa A rfl, hxf ⊤ rfl, hxg ⊤ rfl] at hx
  exact ⟨xAD, hx, hAD⟩

/-- The row at `(univ, 3)` (`A_C` at `1`, every other live kind at `ω + 3`) satisfies the
constraints: the rows are consistent at the new cell at `(univ, 3)`. -/
theorem isThinLawfulBelow_row_three :
    IsThinLawfulBelow (gridPoint.{u} 1 0) (gridPoint 3 1) (gridPoint 3 1) (gridPoint 3 1) where
  svAC := isSelfVisible_gridPoint 1 0
  svAD := (isSelfVisible_gridPoint 3 1).mono (by omega)
  svF := (isSelfVisible_gridPoint 3 1).mono (by omega)
  svG := isSelfVisible_gridPoint 3 1
  le_AD := by
    rw [gridPoint, gridPoint, WithBot.coe_le_coe, WithTop.coe_le_coe]
    exact (omega0_mul_add_natCast_lt (by simp) _ _).le
  G_le_F := le_rfl
  G_le_AD := le_rfl
  visibilityReplaceFixed _ := by
    rw [gridPoint, visibilityReplace_block]; simp
  noCollision h := absurd h (ne_of_lt (by
    rw [gridPoint, gridPoint, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    exact omega0_mul_add_natCast_lt (by simp) _ _))

/-- The row at `(univ, 2)` (`A_C` at `1`, `A_D` at `ω + 1`, the kind `F` at `ω·2 + 2`; `G` absent)
satisfies the constraints. -/
theorem isThinLawfulBelow_row_two :
    IsThinLawfulBelow (gridPoint.{u} 1 0) (gridPoint 1 1) (gridPoint 2 2) ⊥ where
  svAC := isSelfVisible_gridPoint 1 0
  svAD := isSelfVisible_gridPoint 1 1
  svF := isSelfVisible_gridPoint 2 2
  svG := isSelfVisible_bot 3
  le_AD := gridPoint_le_gridPoint.mpr (by omega)
  G_le_F := bot_le
  G_le_AD := bot_le
  visibilityReplaceFixed h := absurd h (not_lt.mpr bot_le)
  noCollision h := absurd h (gridPoint_lt_gridPoint.mpr (by omega)).ne


/-- The row at `(univ, 1)` (`A_C` at `1`, `A_D` at `ω + 1`) satisfies the constraints. -/
theorem isThinLawfulBelow_row_one : IsThinLawfulBelow (gridPoint.{u} 1 0) (gridPoint 1 1) ⊥ ⊥ where
  svAC := isSelfVisible_gridPoint 1 0
  svAD := isSelfVisible_gridPoint 1 1
  svF := isSelfVisible_bot 2
  svG := isSelfVisible_bot 3
  le_AD := gridPoint_le_gridPoint.mpr (by omega)
  G_le_F := le_rfl
  G_le_AD := bot_le
  visibilityReplaceFixed h := absurd h (not_lt.mpr bot_le)
  noCollision h := absurd h (gridPoint_lt_gridPoint.mpr (by omega)).ne

end VaughtConjecture.ThinCompletion
