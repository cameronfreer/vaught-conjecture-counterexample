/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import VaughtConjecture.Continuation.H2OwnerResidual

/-!
# A context of grade `2` on three points at the residual (work file)

WORK FILE (branch `research/work-owner-general`).  No `sorry`.

The witnesses for a context on three points at the residual of
`VaughtConjecture.Continuation.H2OwnerResidual`: the constant shifter (`constShift`) and the shifter
reading `1` at `m` and `3` at `y` (`finShift`, `isWitness_finShift`, for `⊥ < m ≤ y`, `m`
self-visible at `1`, `y` at `2`).

**The intended context** (argued, not compiled).  On three points with the interval plan, ten
cells, one at each graded face:

| cell | scope    | grade | row values (on the cells below)    | label |
|------|----------|-------|-------------------------------------|-------|
| 0    | `{0}`    | 1     | `⊥`                                 | `⊥`   |
| 1    | `{1}`    | 1     | `⊥`                                 | `⊥`   |
| 2    | `{0,1}`  | 1     | `⊥`                                 | `⊥`   |
| 3    | `{0,1}`  | 2     | `⊥` at `0`–`2`, `3` at `3`          | `⊤`   |
| 4    | `{2}`    | 1     | `1`                                 | `⊤`   |
| 5    | `{1,2}`  | 1     | `⊥` at `1`, `1` at `4`, `5`         | `⊤`   |
| 6    | `{1,2}`  | 2     | `⊥`                                 | `⊥`   |
| 7    | `univ`   | 1     | `⊥` at dead cells, `1` at `4,5,7`   | `⊤`   |
| 8    | `univ`   | 2     | `1` at `4,5,7`, `3` at `3,8`, else `⊥` | `⊤`   |
| 9    | `univ`   | 3     | `⊥`                                 | `⊥`   |

The lawful labellings should be `(⊥,⊥,⊥, y, x, x, ⊥, x, y, ⊥)` with `x` self-visible at `1`, `y`
at `2`, and `x = ⊥ → y = ⊥`: the cells `0, 1, 2, 6, 9` read themselves at `⊥`; availability and
the equal readings give `x` at `4, 5, 7` and `y` at `3, 8`; `H2.eq_bot_of_reading_one_three` at
the owner `8` gives `x = ⊥ → y = ⊥`; conversely the witnesses above serve every such pair.  The
capped lifts between the graded faces are then explicit (eleven pairs).  With owner `8`, lost top
`4`, lost point `2` and root top `3`, it is a source-gap context of grade `2` (the gap at `3` is
`visibilityReplace 2 2 1 = 2 < 3`), the owner is alone at `(univ, 2)`, the lost top `4` is a
designated top not determined by the root, and the donor face `(x, y) = (1, 2)` meets
`H2.not_ownerLoweringBelow_of_reading`.  Compiling the legality of this scheme is left open.
-/

universe u

namespace VaughtConjecture.ResidualInstance

open Finset Label CellScheme StageType FieldAdmission H2

/-! ### Witnesses -/

/-- A label self-visible at `1` is fixed by replacement at `2` with value `1`. -/
theorem visibilityReplace_two_one {m : Label.{u}} (hm : IsSelfVisible 1 m) :
    visibilityReplace 2 1 m = m := by
  induction m using recBotCoeTop with
  | bot => rfl
  | top => rfl
  | coe o =>
    obtain ⟨μ, hμ, j, rfl⟩ := exists_eq_add_natCast_isSuccPrelimit o
    have hj : 1 ≤ j := (isSelfVisible_coe_add_natCast_iff hμ).mp hm
    rw [visibilityReplace_coe_add hμ]
    split_ifs with h
    · obtain rfl : j = 1 := by omega
      rfl
    · rfl

/-- The constant shifter at `y` off `⊥`. -/
noncomputable def constShift (y : Label.{u}) (z : Label.{u}) : Label.{u} := if z = ⊥ then ⊥ else y

theorem isWitness_constShift {K : ℕ} {y : Label.{u}} (hy : IsSelfVisible K y) :
    IsWitness (stepSuppressor K) (constShift y) where
  antitone := (IsWitness.id_step K).antitone
  isSelfVisible := (IsWitness.id_step K).isSelfVisible
  map_bot := by simp [constShift]
  monotone := by
    intro x z hxz
    unfold constShift
    split_ifs
    · exact le_rfl
    · exact bot_le
    · exact absurd (le_bot_iff.mp (‹z = ⊥› ▸ hxz)) ‹¬x = ⊥›
    · exact le_rfl
  visibilityReplace_comm x k hx i _ := by
    unfold constShift
    by_cases hk : k ≤ K
    · simp only [visibilityReplace_eq_bot_iff]
      split_ifs
      · rfl
      · exact ((hy.mono hk).visibilityReplace_eq i).symm
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hx
      by_cases h0 : x = ⊥
      · simp [h0]
      · simp only [constShift, h0, ite_false] at hx
        simp [h0, hx]

/-- The finite labels at most `2`. -/
theorem exists_natCast_of_le_two {z : Label.{u}} (hz0 : z ≠ ⊥) (hz : z ≤ ((2 : ℕ) : Label.{u})) :
    ∃ n : ℕ, n ≤ 2 ∧ z = (n : Label.{u}) := by
  induction z using recBotCoeTop with
  | bot => exact absurd rfl hz0
  | top => exact absurd hz (by rw [natCast_label]; exact not_le.mpr (WithBot.coe_lt_coe.mpr
      (WithTop.coe_lt_top _)))
  | coe o =>
    rw [natCast_label] at hz
    have ho : o ≤ ((2 : ℕ) : Ordinal.{u}) := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hz)
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (ho.trans_lt (Ordinal.natCast_lt_omega0 2))
    refine ⟨n, by exact_mod_cast ho, ?_⟩
    rw [natCast_label]

/-- **The shifter reading `1` at `m` and `3` at `y`**: `⊥` at `⊥`, `visibilityReplace 2 n m` at a
finite label `n ≤ 2`, and `y` above `2`. -/
noncomputable def finShift (m y : Label.{u}) (z : Label.{u}) : Label.{u} :=
  if z = ⊥ then ⊥
  else if z ≤ ((0 : ℕ) : Label.{u}) then visibilityReplace 2 0 m
  else if z ≤ ((1 : ℕ) : Label.{u}) then visibilityReplace 2 1 m
  else if z ≤ ((2 : ℕ) : Label.{u}) then visibilityReplace 2 2 m else y

theorem finShift_natCast (m y : Label.{u}) {n : ℕ} (hn : n ≤ 2) :
    finShift m y (n : Label.{u}) = visibilityReplace 2 n m := by
  interval_cases n <;> simp [finShift]

theorem finShift_of_lt (m y : Label.{u}) {z : Label.{u}} (hz : ((2 : ℕ) : Label.{u}) < z) :
    finShift m y z = y := by
  have h0 : z ≠ ⊥ := ne_bot_of_gt hz
  have h2 : ¬ z ≤ ((2 : ℕ) : Label.{u}) := not_le.mpr hz
  have h1 : ¬ z ≤ ((1 : ℕ) : Label.{u}) := fun h ↦ h2 (h.trans (natCast_label_le.mpr (by omega)))
  have h00 : ¬ z ≤ ((0 : ℕ) : Label.{u}) :=
    fun h ↦ h2 (h.trans (natCast_label_le.mpr (by omega)))
  simp only [finShift, h0, h00, h1, h2, ite_false]

/-- **The shifter is a witness** with the step suppressor at `2`, for `⊥ < m ≤ y` with `m`
self-visible at `1` and `y` at `2`: on the finite labels at most `2` it is replacement of `m` at
`2`, which commutes with replacement at every threshold at most `2`
(`Label.visibilityReplace_visibilityReplace_of_le`). -/
theorem isWitness_finShift {m y : Label.{u}} (_hm : IsSelfVisible 1 m) (hy : IsSelfVisible 2 y)
    (hm0 : ⊥ < m) (hmy : m ≤ y) : IsWitness (stepSuppressor 2) (finShift m y) := by
  have h01 : visibilityReplace 2 0 m ≤ visibilityReplace 2 1 m :=
    visibilityReplace_le_visibilityReplace (by omega) m
  have h12 : visibilityReplace 2 1 m ≤ visibilityReplace 2 2 m :=
    visibilityReplace_le_visibilityReplace (by omega) m
  have h2y : visibilityReplace 2 2 m ≤ y := visibilityReplace_le_of_le le_rfl hy hmy
  have hne (z : Label.{u}) (hz : z ≠ ⊥) : finShift m y z ≠ ⊥ := by
    have hy0 : y ≠ ⊥ := (hm0.trans_le hmy).ne'
    unfold finShift
    split_ifs with h
    · exact absurd h hz
    all_goals simp [hy0, hm0.ne']
  refine ⟨(IsWitness.id_step 2).antitone, (IsWitness.id_step 2).isSelfVisible,
    by simp [finShift], ?_, ?_⟩
  · intro x z hxz
    unfold finShift
    split_ifs with a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 <;>
      first
      | exact le_rfl
      | exact bot_le
      | exact h01
      | exact h12
      | exact h01.trans h12
      | exact h2y
      | exact h12.trans h2y
      | exact (h01.trans h12).trans h2y
      | exact absurd (le_bot_iff.mp (by subst_vars; exact hxz)) ‹_›
      | exact absurd (hxz.trans ‹_›) ‹_›
  · intro x k hx i hi
    by_cases hk : k ≤ 2
    · by_cases hx0 : x = ⊥
      · subst hx0
        simp [finShift]
      by_cases hx2 : x ≤ ((2 : ℕ) : Label.{u})
      · obtain ⟨n, hn, rfl⟩ := exists_natCast_of_le_two hx0 hx2
        rw [visibilityReplace_natCast, finShift_natCast m y hn,
          visibilityReplace_visibilityReplace_of_le hk]
        have hle : (if n < k then i else n) ≤ 2 := by split_ifs <;> omega
        rw [← finShift_natCast m y hle]
        split_ifs <;> rfl
      · have h2 : ((2 : ℕ) : Label.{u}) < x := not_le.mp hx2
        have h2' : ((2 : ℕ) : Label.{u}) < visibilityReplace k i x :=
          H2.lt_visibilityReplace_of_lt hi (((isSelfVisible_natCast 2).mpr le_rfl).mono hk) h2
        rw [finShift_of_lt m y h2, finShift_of_lt m y h2', (hy.mono hk).visibilityReplace_eq]
    · rw [stepSuppressor_of_lt (by omega), le_bot_iff] at hx
      have hx0 : x = ⊥ := by
        by_contra h
        exact hne x h hx
      subst hx0
      simp [finShift]

theorem finShift_one (m y : Label.{u}) (hm : IsSelfVisible 1 m) :
    finShift m y 1 = m := by
  have := finShift_natCast m y (n := 1) (by omega)
  rw [Nat.cast_one] at this
  rw [this, visibilityReplace_two_one hm]

theorem finShift_three (m y : Label.{u}) : finShift m y ((3 : ℕ) : Label.{u}) = y :=
  finShift_of_lt m y (natCast_label_lt.mpr (by omega))

end VaughtConjecture.ResidualInstance
