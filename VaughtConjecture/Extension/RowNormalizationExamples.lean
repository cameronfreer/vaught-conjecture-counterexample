/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.Coding
import VaughtConjecture.Extension.WitnessAlgebra
import VaughtConjecture.Label.FieldLadder
import VaughtConjecture.Label.GradeOneInterpolation

/-!
# Examples: a coded row with no strongly coded row of the same targets

Roadmap, Library conventions (legality imposes coding as the range normalization only) and
Correspondence, item 1 (the range clause of the legal templates of [AFK26]); semantic contract,
item 3.

A conversion of legal schemes into strongly coded ones (`CellScheme.Rows.IsStronglyCoded`, the
range clause of [AFK26, Definition "legal"]) that keeps the lawful labellings would be immediate if
every row could be replaced, one at a time, by a strongly coded row with the same targets: the
locality of a labelling at a cell asks only that the capped labelling be a target of the row of
the cell.  This is the reading of the offset bound of [Kni26, Lemma 2.5.13] as a normalization.
It fails.

**The row `(1, 2, 3)`** (`row123`), on three cells of grade `1`, is coded and not strongly coded
at `1`.  For every row `ℓ` on the same cells whose values are strongly coded at `1`, some labelling
is a target of exactly one of `(1, 2, 3)` and `ℓ` (`exists_transformsTo_row123_iff_ne`).

*Proof.*  A target of `(1, 2, 3)` that is `⊥` at the first cell is `⊥` at the last
(`eq_bot_of_transformsTo_row123`): the zero region of a witness is closed under visibility
replacement (`IsWitness.min_visibilityReplace_eq_bot`), and replacement at threshold `3` sends `1`
to `3`.  If `ℓ` has the targets of `(1, 2, 3)`, then `(1, 2, 3)` itself is a target of `ℓ`, so the
values of `ℓ` increase strictly even after replacement at threshold `1`
(`TransformsTo.le_of_le_visibilityReplace`); being strongly coded at `1`, they have finite parts
at most `2`, so they do not lie in one block of `ω`, and the last one lies in a block above the
first.  Splitting at that block (`splitAt`, a witness bounded by `1`, `isWitness_splitAt`) gives a
target of `ℓ` that is `⊥` at the first cell and `1` at the last, which is not a target of
`(1, 2, 3)`.

**Scope.**  This rules out conversions that replace each row by a strongly coded row with the same
targets.  It does not rule out a conversion that changes several rows of a scheme together: on one
point, with three cells of grade `1` whose rows are `(1, 1, 1)`, `(1, 2, 2)`, and `(1, 2, 3)`,
replacing the last row by `(1, ω + 1, ω + 2)` keeps the lawful labellings, the second row then
carrying the constraint that `(1, 2, 3)` carried alone (a hand computation, not compiled).  The
strongly coded legal stage types are instead closed under the extension and amalgamation
constructions themselves (`VaughtConjecture.Extension.StronglyCodedAmalgamation`).

## References

The offset bound is that of [Kni26, Lemma 2.5.13] and the range clause that of [AFK26, Definition
"legal"]; witnesses and visibility replacement are [Kni26, Definitions 2.2.3 and 2.3.9].
-/

universe u

namespace VaughtConjecture

open Label
open scoped Ordinal

namespace RowNormalizationExamples

/-! ### Splitting at a block -/

/-- The shifter that is `⊥` below `μ` and `c` from `μ` on. -/
noncomputable def splitAt (μ : Ordinal.{u}) (c : Label.{u}) (x : Label.{u}) : Label.{u} :=
  if x < (μ : Label.{u}) then ⊥ else c

/-- **Splitting at a block is a witness bounded by `K`**, for `μ` zero or a limit and `c`
self-visible at `K`: visibility replacement keeps a label below `μ` exactly when it was below. -/
theorem isWitness_splitAt {μ : Ordinal.{u}} (hμ : Order.IsSuccPrelimit μ) {K : ℕ}
    {c : Label.{u}} (hc : IsSelfVisible K c) :
    IsWitness (stepSuppressor K) (splitAt μ c) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := ite_eq_left (WithBot.bot_lt_coe _)
  monotone x y hxy := by
    unfold splitAt
    by_cases hy : y < (μ : Label.{u})
    · rw [ite_eq_left (hxy.trans_lt hy), ite_eq_left hy]
    · rw [ite_eq_right hy]
      split_ifs
      exacts [bot_le, le_rfl]
  visibilityReplace_comm x k hg i hi := by
    have hsame : splitAt μ c (visibilityReplace k i x) = splitAt μ c x := by
      simp only [splitAt, Label.visibilityReplace_lt_iff hμ]
    rw [hsame]
    by_cases hk : k ≤ K
    · unfold splitAt
      split_ifs
      · rfl
      · exact ((hc.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (not_le.mp hk), le_bot_iff] at hg
      rw [hg, visibilityReplace_bot]

/-! ### Points `ω · a + b` -/

/-- The label `ω · a + b`. -/
noncomputable abbrev pt (a b : ℕ) : Label.{u} :=
  ((ω * (a : Ordinal.{u}) + b : Ordinal.{u}) : Label.{u})

/-- Points compare lexicographically in block and finite part. -/
theorem pt_le_pt {a b a' b' : ℕ} : pt.{u} a b ≤ pt a' b' ↔ a < a' ∨ a = a' ∧ b ≤ b' := by
  rw [pt, pt, WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff, Nat.cast_lt,
    Nat.cast_inj]

/-- A point lies below `ω · B` exactly when its block is below `B`. -/
theorem pt_lt_coe_omega0_mul {a b B : ℕ} :
    pt.{u} a b < ((ω * (B : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) ↔ a < B := by
  have h : ((ω * (B : Ordinal.{u}) : Ordinal.{u}) : Label.{u}) = pt B 0 := by
    simp [pt]
  rw [h, lt_iff_not_ge, pt_le_pt]
  omega

/-- Replacement at threshold `1` with value `1` raises a finite part `0` to `1`. -/
theorem visibilityReplace_one_one_pt (a b : ℕ) :
    visibilityReplace 1 1 (pt.{u} a b) = pt a (max b 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact visibilityReplace_coe_add_natCast (isSuccPrelimit_omega0_mul' _) Nat.zero_lt_one 1
  · rw [max_eq_left hb]
    exact ((isSelfVisible_coe_add_natCast_iff (isSuccPrelimit_omega0_mul' _)).mpr hb)

/-- Natural numbers compare as labels as they do in `ℕ`. -/
theorem natCast_lt_natCast {m n : ℕ} (h : m < n) : ((m : ℕ) : Label.{u}) < (n : Label.{u}) := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast, ← WithBot.coe_natCast, ← WithTop.coe_natCast]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by exact_mod_cast h))

/-! ### The row `(1, 2, 3)` -/

/-- The row `(1, 2, 3)` on three cells of grade `1`; it is coded and not strongly coded at `1`. -/
noncomputable def row123 : Fin 3 → Label.{u} := fun i ↦ ((i + 1 : ℕ) : Label.{u})

/-- **A target of `(1, 2, 3)` that is `⊥` at the first cell is `⊥` at the last**: the zero region
of a witness is closed under visibility replacement, and replacement at threshold `3` sends `1`
to `3`. -/
theorem eq_bot_of_transformsTo_row123 {r : Fin 3 → Label.{u}}
    (h : TransformsTo (fun _ ↦ 1) row123 r) (h0 : r 0 = ⊥) : r 2 = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := h
  have h1 : min (σ ((1 : ℕ) : Label.{u})) (g 1) = ⊥ := by rw [← h0, heq 0]; rfl
  have h3 := hw.min_visibilityReplace_eq_bot h1 (k := 3) (i := 3) le_rfl
  rw [Label.visibilityReplace_natCast, ite_eq_left (by omega)] at h3
  rw [heq 2]
  exact h3

/-- **No strongly coded row has the targets of `(1, 2, 3)`**: for every row `ℓ` on three cells of
grade `1` whose values are strongly coded at `1`, some labelling is a target of exactly one of
`(1, 2, 3)` and `ℓ`.  So no replacement of the row of a cell of grade `1` by a strongly coded row
keeps the set of its targets. -/
theorem exists_transformsTo_row123_iff_ne (ℓ : Fin 3 → Label.{u})
    (hℓ : ∀ i, IsStronglyCoded 1 (ℓ i)) :
    ∃ r : Fin 3 → Label.{u},
      ¬ (TransformsTo (fun _ ↦ 1) row123 r ↔ TransformsTo (fun _ ↦ 1) ℓ r) := by
  by_contra! hall
  have h123 := (hall row123).mp (TransformsTo.refl _ _)
  have hv (i : Fin 3) : IsSelfVisible 1 (row123.{u} i) := by
    simp only [row123, isSelfVisible_natCast]
    omega
  -- the values of `ℓ` increase strictly, even after replacement at `1`
  have hlt (d e : Fin 3) (hde : row123.{u} d < row123 e) :
      visibilityReplace 1 1 (ℓ d) < ℓ e :=
    lt_of_not_ge fun h ↦ (not_le.mpr hde) (h123.le_of_le_visibilityReplace hv h)
  have h01 := hlt 0 1 (natCast_lt_natCast (by decide))
  have h12 := hlt 1 2 (natCast_lt_natCast (by decide))
  have hne0 : ℓ 0 ≠ ⊥ := fun h ↦ by simpa [row123] using h123.eq_bot h
  -- every value is a point `ω · a + b` with `b ≤ 2`
  have hpt (i : Fin 3) (hi : ℓ i ≠ ⊥) : ∃ a b, b ≤ 2 ∧ ℓ i = pt a b := by
    rcases hℓ i with h | ⟨a, b, hb, h⟩
    · exact absurd h hi
    · exact ⟨a, b, hb, h⟩
  have hne1 : ℓ 1 ≠ ⊥ := fun h ↦ by
    rw [h] at h01; exact not_lt_bot h01
  have hne2 : ℓ 2 ≠ ⊥ := fun h ↦ by
    rw [h] at h12; exact not_lt_bot h12
  obtain ⟨a0, b0, hb0, he0⟩ := hpt 0 hne0
  obtain ⟨a1, b1, hb1, he1⟩ := hpt 1 hne1
  obtain ⟨a2, b2, hb2, he2⟩ := hpt 2 hne2
  rw [he0, he1, visibilityReplace_one_one_pt, lt_iff_not_ge, pt_le_pt] at h01
  rw [he1, he2, visibilityReplace_one_one_pt, lt_iff_not_ge, pt_le_pt] at h12
  -- the split target, read on `ℓ`
  have hsplit (B : ℕ) :
      TransformsTo (fun _ ↦ 1) ℓ fun i ↦ splitAt (ω * (B : Ordinal.{u})) 1 (ℓ i) := by
    refine ⟨stepSuppressor 1, splitAt (ω * (B : Ordinal.{u})) 1,
      isWitness_splitAt (isSuccPrelimit_omega0_mul' _)
        (by simp), fun i ↦ ?_⟩
    rw [stepSuppressor_of_le le_rfl, min_top_right]
  have hsplit_eq (B : ℕ) (i : Fin 3) {a b : ℕ} (he : ℓ i = pt a b) :
      splitAt (ω * (B : Ordinal.{u})) 1 (ℓ i) = if a < B then ⊥ else 1 := by
    simp only [splitAt, he, pt_lt_coe_omega0_mul]
  rcases Nat.lt_or_ge a1 a2 with ha12 | ha12
  · -- `ℓ 2` lies in a higher block than `ℓ 1`: the split at that block is `(⊥, ⊥, 1)`
    have ht := (hall _).mpr (hsplit a2)
    have h0 := eq_bot_of_transformsTo_row123 ht (by
      rw [hsplit_eq a2 0 he0, ite_eq_left (by omega)])
    rw [hsplit_eq a2 2 he2, ite_eq_right (lt_irrefl _)] at h0
    exact WithBot.one_ne_bot h0
  · -- `ℓ 1` and `ℓ 2` lie in one block, so `ℓ 0` lies in a lower one
    have ha1 : a1 = a2 := by omega
    have ha0 : a0 < a1 := by omega
    have ht := (hall _).mpr (hsplit a1)
    have h0 := eq_bot_of_transformsTo_row123 ht (by
      rw [hsplit_eq a1 0 he0, ite_eq_left ha0])
    rw [hsplit_eq a1 2 he2, ite_eq_right (by omega)] at h0
    exact WithBot.one_ne_bot h0

end RowNormalizationExamples

end VaughtConjecture
