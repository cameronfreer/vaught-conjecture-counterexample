/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.OrbitCode

/-!
# Examples: orbit codes at grade two

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities; here the scalar regressions of
the arity one); semantic contract, item 3.

At arity one the field layer at grade `2` has old cells of grade `1`, whose values need not be
self-visible at `2`.  Write `Q b f` for the label `ω * b + f`.

* **R5, orbit codes are necessary** (`canonicalCode_orbitLabelling`,
  `orbitCode_orbitLabelling`, `not_exists_isWitness_read`): on the labelling
  `(1, 2, ω * 3 + 1, ω * 3 + 2)` at grade `2` the canonical code merges the first two values and
  the last two, while the orbit code is `(1, 2, ω * 4 + 1, ω * 4 + 2)`: the natural strip stays,
  and the strip of the key `ω * 3 + 2` moves to the block `4` (the block move); the orbit decoder
  reads it literally.  No witness reads one label as `ω * 3 + 1` at grade `1` and as `ω * 3 + 2` at
  grade `2`, because its suppressor is antitone; so a code merging the two values cannot be read
  literally at a grade-`1` and a grade-`2` cell.
* **R6, relative room fails at a cap that is not short** (`not_min_orbitCode_eq_of_not_isShort`):
  the labelling `(ω * 2 + 1)` is orbit-canonical, the cap `ω + 7` is self-visible at `2` but not
  short, and `(ω * 5 + 3)` agrees with `(ω * 2 + 1)` capped at `ω + 7`, yet its orbit code `ω + 2`
  does not.  This is why the one-grade lift is to be used in its short-cap form
  (`CellScheme.Rows.cappedLift_of_boundary_short`) at grade `2`.
* **R7, the natural strip** (`min_orbitCode_orbitLabelling_gridPoint_zero`): the value `1` keeps
  its code `1`, so the orbit code agrees with the labelling capped at the least grid point `2`; the
  block move of `1` to the block `2` would not.

## Placement

Checkpoint 2.5 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.SmallArityOneExamples

open Finset Ordinal Label

/-- The label `ω * b + f`. -/
noncomputable def Q (b f : ℕ) : Label.{u} :=
  ((ω * (b : Ordinal.{u}) + (f : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

private theorem Q_le_Q_iff {b b' f f' : ℕ} : Q.{u} b f ≤ Q b' f' ↔ b < b' ∨ b = b' ∧ f ≤ f' := by
  rw [Q, Q, WithBot.coe_le_coe, WithTop.coe_le_coe, omega0_mul_add_natCast_le_iff, Nat.cast_lt,
    Nat.cast_inj]

private theorem Q_inj {b b' f f' : ℕ} : Q.{u} b f = Q b' f' ↔ b = b' ∧ f = f' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h.1, h.2]⟩
  have h1 := Q_le_Q_iff.mp h.le
  have h2 := Q_le_Q_iff.mp h.ge
  omega

private theorem Q_ne_bot (b f : ℕ) : Q.{u} b f ≠ ⊥ := WithBot.coe_ne_bot

private theorem visibilityReplace_Q (b f : ℕ) :
    visibilityReplace 2 2 (Q.{u} b f) = Q b (if f < 2 then 2 else f) := by
  rw [Q, Q, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]

private theorem isSelfVisible_Q {b f : ℕ} : IsSelfVisible 2 (Q.{u} b f) ↔ 2 ≤ f := by
  rw [Q, isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

private theorem gridPoint_eq_Q (b : ℕ) : gridPoint.{u} 2 b = Q b 2 := rfl

/-! ### R5: orbit codes are necessary -/

/-- The labelling of R5 at grade `2`: `(1, 2, ω * 3 + 1, ω * 3 + 2)`. -/
noncomputable def orbitLabelling : Fin 4 → Label.{u} := ![Q 0 1, Q 0 2, Q 3 1, Q 3 2]

/-- **The canonical code merges values of one strip**: at grade `2` it sends `1` and `2` to one
code, and `ω * 3 + 1` and `ω * 3 + 2` to one code. -/
theorem canonicalCode_orbitLabelling :
    canonicalCode 2 orbitLabelling.{u} 0 = canonicalCode 2 orbitLabelling 1 ∧
      canonicalCode 2 orbitLabelling.{u} 2 = canonicalCode 2 orbitLabelling 3 := by
  simp only [canonicalCode, Function.comp_apply, orbitLabelling]
  refine ⟨?_, ?_⟩ <;> simp [canonicalMap_of_ne_bot (Q_ne_bot _ _), visibilityReplace_Q]

/-- The keys of the labelling of R5 are `2` and `ω * 3 + 2`. -/
private theorem image_visibilityReplace_orbitLabelling :
    (univ.image fun i ↦ visibilityReplace 2 2 (orbitLabelling.{u} i)) ⊆ {Q 0 2, Q 3 2} := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := mem_image.mp hy
  fin_cases i <;> simp [orbitLabelling, visibilityReplace_Q]

/-- Every value of the labelling of R5 has an orbit key. -/
private theorem isOrbitKey_orbitLabelling (i : Fin 4) :
    IsOrbitKey 2 orbitLabelling.{u} (orbitLabelling i) := by
  fin_cases i
  · exact ⟨0, rfl, by simp [orbitLabelling, isSelfVisible_Q]⟩
  · exact ⟨0, by simp [orbitLabelling, visibilityReplace_Q], by simp [orbitLabelling,
      isSelfVisible_Q]⟩
  · exact ⟨2, rfl, by simp [orbitLabelling, isSelfVisible_Q]⟩
  · exact ⟨2, by simp [orbitLabelling, visibilityReplace_Q], by simp [orbitLabelling,
      isSelfVisible_Q]⟩

/-- **The orbit code of the labelling of R5** is `(1, 2, ω * 4 + 1, ω * 4 + 2)`: the natural strip
is kept and the strip of the key `ω * 3 + 2`, of key rank `2`, moves to the block `4`. -/
theorem orbitCode_orbitLabelling :
    orbitCode 2 orbitLabelling.{u} = ![Q 0 1, Q 0 2, Q 4 1, Q 4 2] := by
  have hlt : visibilityReplace 2 2 (orbitLabelling.{u} 1) <
      visibilityReplace 2 2 (orbitLabelling.{u} 3) := by
    -- The values at the cells `1` and `3`.
    change visibilityReplace 2 2 (Q.{u} 0 2) < visibilityReplace 2 2 (Q 3 2)
    rw [visibilityReplace_Q, visibilityReplace_Q]
    exact lt_of_le_of_ne (Q_le_Q_iff.mpr (.inl (by decide))) fun h ↦ by simp [Q_inj] at h
  have hkey3 : keyRank 2 orbitLabelling.{u} (orbitLabelling 3) = 2 := by
    refine le_antisymm ?_ ?_
    · exact (Finset.card_le_card (filter_subset _ _)).trans
        ((Finset.card_le_card image_visibilityReplace_orbitLabelling).trans card_le_two)
    · have h1 := one_le_keyRank (isOrbitKey_orbitLabelling.{u} 1).isKey
      have h2 := keyRank_lt_keyRank (isOrbitKey_orbitLabelling.{u} 3).isKey hlt
      omega
  have hkey2 : keyRank 2 orbitLabelling.{u} (orbitLabelling 2) = 2 := by
    refine (keyRank_congr ?_).trans hkey3
    -- The values at the cells `2` and `3`.
    change visibilityReplace 2 2 (Q.{u} 3 1) = visibilityReplace 2 2 (Q 3 2)
    rw [visibilityReplace_Q, visibilityReplace_Q]
    rfl
  have hn (b f : ℕ) (hf : f ≤ 2) : visibilityReplace 2 2 (Q.{u} b f) = Q b 2 := by
    rw [visibilityReplace_Q]
    congr 1
    split_ifs <;> omega
  have hnat (i : Fin 4) (hb : 2 ≤ (i : ℕ)) :
      visibilityReplace 2 2 (orbitLabelling.{u} i) ≠ gridPoint 2 0 := by
    fin_cases i
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · -- The value at the cell `2`.
      change visibilityReplace 2 2 (Q.{u} 3 1) ≠ Q 0 2
      rw [hn 3 1 (by decide), Ne, Q_inj]
      decide
    · -- The value at the cell `3`.
      change visibilityReplace 2 2 (Q.{u} 3 2) ≠ Q 0 2
      rw [hn 3 2 le_rfl, Ne, Q_inj]
      decide
  have hcode (i : Fin 4) (hi : (i : ℕ) < 2) :
      orbitCode 2 orbitLabelling.{u} i = orbitLabelling i := by
    have hi0 : visibilityReplace 2 2 (orbitLabelling.{u} i) = gridPoint 2 0 := by
      fin_cases i
      · exact hn 0 1 (by decide)
      · exact hn 0 2 le_rfl
      · exact absurd hi (by decide)
      · exact absurd hi (by decide)
    rw [orbitCode_apply, orbitMap_of_isOrbitKey (isOrbitKey_orbitLabelling i),
      codeBlock_of_natural (isOrbitKey_orbitLabelling i) hi0]
    exact moveToBlock_eq_self (by rw [hi0]; exact isSelfVisible_gridPoint 2 0)
  have h2 : orbitCode 2 orbitLabelling.{u} 2 = Q 4 1 := by
    rw [orbitCode_apply, orbitMap_of_isOrbitKey (isOrbitKey_orbitLabelling 2),
      codeBlock_of_isOrbitKey (isOrbitKey_orbitLabelling 2) (hnat 2 le_rfl), hkey2]
    exact moveToBlock_omega0_mul_add _ _ _ _
  have h3 : orbitCode 2 orbitLabelling.{u} 3 = Q 4 2 := by
    rw [orbitCode_apply, orbitMap_of_isOrbitKey (isOrbitKey_orbitLabelling 3),
      codeBlock_of_isOrbitKey (isOrbitKey_orbitLabelling 3) (hnat 3 (by decide)), hkey3]
    exact moveToBlock_omega0_mul_add _ _ _ _
  funext i
  fin_cases i
  · exact hcode 0 (by decide)
  · exact hcode 1 (by decide)
  · exact h2
  · exact h3

/-- **The orbit decoder reads the orbit code of R5 literally**, at the least grid point. -/
theorem orbitDecoder_orbitLabelling (i : Fin 4) :
    orbitDecoder 2 orbitLabelling.{u} (gridPoint 2 0) (orbitCode 2 orbitLabelling i) =
      orbitLabelling i :=
  orbitDecoder_orbitCode (fun _ ↦ min_orbitCode_gridPoint_zero _) i

/-- **No witness reads one label as `ω * 3 + 1` at grade `1` and as `ω * 3 + 2` at grade `2`**:
its suppressor is antitone, so the reading at grade `2` is at most the reading at grade `1`. -/
theorem not_exists_isWitness_read :
    ¬ ∃ (g : ℕ → Label.{u}) (σ : Label.{u} → Label.{u}) (x : Label.{u}), IsWitness g σ ∧
      min (σ x) (g 1) = Q 3 1 ∧ min (σ x) (g 2) = Q 3 2 := by
  rintro ⟨g, σ, x, hw, h1, h2⟩
  have hle : min (σ x) (g 2) ≤ min (σ x) (g 1) := min_le_min_left _ (hw.antitone (by decide))
  rw [h1, h2, Q_le_Q_iff] at hle
  omega

/-! ### R6: relative room fails at a cap that is not short -/

/-- **Relative room fails at a cap that is not short.**  At grade `2`, the labelling
`(ω * 2 + 1)` is orbit-canonical; the cap `ω + 7` is self-visible at `2` and not short; the
labelling `(ω * 5 + 3)` agrees with `(ω * 2 + 1)` capped at `ω + 7`; but its orbit code, `ω + 2`,
does not. -/
theorem not_min_orbitCode_eq_of_not_isShort :
    orbitCode 2 (fun _ : Fin 1 ↦ Q.{u} 2 1) = (fun _ ↦ Q 2 1) ∧ IsSelfVisible 2 (Q.{u} 1 7) ∧
      ¬ IsShort 2 (Q.{u} 1 7) ∧
      (∀ d : Fin 1, min (Q.{u} 5 3) (Q 1 7) = min ((fun _ : Fin 1 ↦ Q.{u} 2 1) d) (Q 1 7)) ∧
      orbitCode 2 (fun _ : Fin 1 ↦ Q.{u} 5 3) 0 = Q 1 2 ∧
      min (orbitCode 2 (fun _ : Fin 1 ↦ Q.{u} 5 3) 0) (Q 1 7) ≠ min (Q 2 1) (Q 1 7) := by
  have hrank (b f : ℕ) : keyRank 2 (fun _ : Fin 1 ↦ Q.{u} b f) (Q b f) = 1 :=
    le_antisymm ((keyRank_le_card _ _ _).trans_eq (by simp))
      (one_le_keyRank (k := 2) (w := fun _ : Fin 1 ↦ Q.{u} b f) ⟨0, Q_ne_bot _ _, rfl⟩)
  have hcode : orbitCode 2 (fun _ : Fin 1 ↦ Q.{u} 5 3) 0 = Q 1 2 := by
    have ho : ¬ IsOrbitKey 2 (fun _ : Fin 1 ↦ Q.{u} 5 3) (Q 5 3) := fun ⟨_, _, h⟩ ↦
      h (isSelfVisible_Q.mpr (by decide))
    have hk : IsKey 2 (fun _ : Fin 1 ↦ Q.{u} 5 3) (Q 5 3) := ⟨0, Q_ne_bot _ _, rfl⟩
    rw [orbitCode_apply, orbitMap_of_not_isOrbitKey (Q_ne_bot _ _) ho,
      codeBlock_of_not_isOrbitKey hk ho, hrank]
    rfl
  have hlt : Q.{u} 1 2 < Q 1 7 := lt_of_le_of_ne (Q_le_Q_iff.mpr (.inr ⟨rfl, by decide⟩))
    fun h ↦ by have := Q_le_Q_iff.mp h.ge; omega
  have hle (b f : ℕ) (hb : 1 < b) : Q.{u} 1 7 ≤ Q b f := Q_le_Q_iff.mpr (.inl hb)
  refine ⟨?_, isSelfVisible_Q.mpr (by decide), fun h ↦ ?_, fun _ ↦ ?_, hcode, ?_⟩
  · funext d
    have ho : IsOrbitKey 2 (fun _ : Fin 1 ↦ Q.{u} 2 1) (Q 2 1) :=
      ⟨0, rfl, fun h ↦ absurd (isSelfVisible_Q.mp h) (by decide)⟩
    rw [orbitCode_apply, orbitMap_of_isOrbitKey ho, codeBlock_of_isOrbitKey ho (by
      simp [visibilityReplace_Q, gridPoint_eq_Q, Q_inj]), hrank]
    exact moveToBlock_omega0_mul_add _ _ _ _
  · have := (isShort_coe.mp h)
    rw [omega0_mul_add_natCast_mod] at this
    exact absurd (by exact_mod_cast this : 7 ≤ 2) (by decide)
  · rw [min_eq_right (hle 5 3 (by decide)), min_eq_right (hle 2 1 (by decide))]
  · rw [hcode, min_eq_left hlt.le, min_eq_right (hle 2 1 (by decide))]
    exact hlt.ne

/-! ### R7: the natural strip -/

/-- **The natural strip is kept**: the value `1` of the labelling of R5 keeps its code `1`, so the
orbit code agrees with the labelling capped at the least grid point `2`; the block move of `1` to
the block `2`, `ω * 2 + 1`, would be read as `2` there. -/
theorem min_orbitCode_orbitLabelling_gridPoint_zero :
    min (orbitCode 2 orbitLabelling.{u} 0) (gridPoint 2 0) = Q 0 1 ∧
      min (orbitCode 2 orbitLabelling.{u} 0) (gridPoint 2 0) =
        min (orbitLabelling 0) (gridPoint 2 0) ∧
      min (Q.{u} 2 1) (gridPoint 2 0) ≠ Q 0 1 := by
  have h12 : Q.{u} 0 1 ≤ Q 0 2 := Q_le_Q_iff.mpr (.inr ⟨rfl, by decide⟩)
  refine ⟨?_, min_orbitCode_gridPoint_zero 0, ?_⟩
  · rw [orbitCode_orbitLabelling, gridPoint_eq_Q]
    exact min_eq_left h12
  · rw [gridPoint_eq_Q, min_eq_right (Q_le_Q_iff.mpr (.inl (by decide)))]
    intro h
    have := Q_le_Q_iff.mp h.le
    omega

end VaughtConjecture.SmallArityOneExamples
