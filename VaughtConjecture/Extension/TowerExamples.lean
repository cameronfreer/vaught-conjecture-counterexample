/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.Tower

/-!
# Examples: the tower at arity two, literal faces, and orbit codes at grade three

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.6 (the recursion on the grade; here the examples of
2.6a); semantic contract, items 2–4.

Write `Q b f` for the label `ω * b + f`.

* **Example 1: at arity two the step to the grade `2` assumes `2FL(1)`**
  (`exists_cell_commonFace_two`, `forall_twoFaceLift_two_iff`, `towerInvariant_two_of_twoFaceLift`,
  `towerInvariant_three_of_twoFaceLift`).  For every seed on four points the common face `{0, 1}`
  of the two coatoms carries a cell of grade `2`, which lies below no pair of grade `1`: so the
  step to the grade `2` is not the top grade, where the other coatom is reached by a lift within it
  from the lower grade.  At arity two the hypothesis of `Seed.towerInvariant_of_twoFaceLift` is
  exactly the two-face lift `2FL(1)`; under it the invariant holds at the grade `2`, and then at the
  grade `3` with no further hypothesis (`Seed.towerInvariant_top`).  At the arities `m ≤ 1` no
  hypothesis is assumed (`towerInvariant_succ_of_le_one`).
* **Example 5: literal faces of the tower** (`towerType`, `restrictFace_left_towerType`,
  `restrictFace_right_towerType`).  At a stage that is zero or a limit, the scheme reached after
  any grade `j ≤ m + 2`, with the glued labelling extended through the tower
  (`Seed.exists_isLawful_tower`) and reduced to the stage, is a stage type whose faces along the two
  coatoms are literally the two coatom types of the seed, labels included: the old cells keep
  their scopes, rows and labels, and every cell of proper scope is old.  Instances at arity two
  and the grade `3` (`restrictFace_towerType_two`).  Its legality below the full grade is the
  subject of checkpoint 2.6c.
* **Example 6: orbit codes at grade three** (`orbitCode_gradeThreeLabelling`,
  `orbitDecoder_gradeThreeLabelling`).  On the labelling `(2, 3, ω * 5 + 2, ω * 5 + 3)` at the
  grade `3` the orbit code is `(2, 3, ω * 4 + 2, ω * 4 + 3)`: the natural strip, whose key is the
  least grid point `3`, stays in the block `0`, and the strip of the key `ω * 5 + 3`, of key rank
  `2`, moves to the block `4`, keeping the finite parts; the value `ω * 5 + 2` of a cell of grade
  `2` is not self-visible at `3`, and its strip is moved, not merged.  The orbit decoder at the
  least grid point reads the code literally.

The stage type of Example 5 and its faces along the two coatoms at every arity are in the module
`VaughtConjecture.Extension.Tower`; the instance at arity two is here.  The negative example for
the step, a legal seed on four points on which the union fill fails, is the module
`VaughtConjecture.Extension.UnionFillCounterexample`.

## Placement

Checkpoint 2.6 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.TowerExamples

open Finset Label

/-! ### Example 1: the step to the grade `2` at arity two -/

section ArityTwo

variable {α : Ordinal.{u}} (I : Seed.{u} α 2)

/-- The common face of the two coatoms of a seed on four points is `{0, 1}`. -/
theorem commonFace_eq :
    (univ.erase (Fin.last 3) ∩ univ.erase (Fin.castSucc (Fin.last 2)) : Finset (Fin 4)) =
      {0, 1} := by
  decide

/-- **The common face carries a cell of grade two**, by completeness of the amalgam below the full
face; it lies below no pair of grade `1`.  So the step to the grade `2` is not the top grade: the
other coatom's cells of the grade `2` include a cell of the common face, which a lift within that
coatom from the grade `1` does not prescribe. -/
theorem exists_cell_commonFace_two :
    ∃ d, I.amalgam.toCellScheme.gradedIndex d = ({0, 1}, 2) ∧
      ∀ B : Finset (Fin 4), d ∉ I.amalgam.toCellScheme.below (B, 1) := by
  have hE : ({0, 1} : Finset (Fin 4)) ∈ I.amalgam.toCellScheme.faces := by
    convert I.commonFace_mem_faces using 1
    decide
  obtain ⟨d, hd⟩ := I.exists_gradedIndex_eq ({0, 1}, 2) ⟨hE, two_pos, by decide⟩ (by decide)
  refine ⟨d, hd, fun B hB ↦ ?_⟩
  have h2 : I.amalgam.toCellScheme.grade d = 2 := congrArg Prod.snd hd
  have h1 : I.amalgam.toCellScheme.grade d ≤ 1 := hB.2
  omega

/-- **At arity two the two-face lift is assumed at the grade `1` only**: the hypothesis of
`Seed.towerInvariant_of_twoFaceLift` is `2FL(1)`. -/
theorem forall_twoFaceLift_two_iff :
    (∀ j, 1 ≤ j → j < 2 → I.TwoFaceLift j) ↔ I.TwoFaceLift 1 :=
  ⟨fun h ↦ h 1 le_rfl one_lt_two, fun h j hj hj2 ↦ by obtain rfl : j = 1 := (by omega); exact h⟩

/-- **The step to the grade `2` at arity two, under `2FL(1)`**: from the invariant at the grade `1`
(the amalgam boundary) by `Seed.towerInvariant_succ`. -/
theorem towerInvariant_two_of_twoFaceLift (h2 : I.TwoFaceLift 1) : I.TowerInvariant 2 :=
  I.towerInvariant_succ (by omega) I.towerInvariant_one h2

/-- **The invariant up to the grade `3` at arity two, under `2FL(1)` only**: the step to the grade
`3` is the top grade (`Seed.towerInvariant_top`). -/
theorem towerInvariant_three_of_twoFaceLift (h2 : I.TwoFaceLift 1) : I.TowerInvariant 3 :=
  I.towerInvariant_top (towerInvariant_two_of_twoFaceLift I h2)

/-- **The lift at the grade `3` at arity two, coordinate by coordinate, under `2FL(1)`**: at every
cap `c` self-visible at `3`, a prescription lawful below the coatom `({0, 1, 2}, 3)` and an ambient
lawful below `(univ, 3)` with the same observation at `c` below the coatom have a lift that reads
the prescription literally and keeps the observation of the ambient at every cell below
`(univ, 3)`, those of the layers at the grades `1` and `2` included. -/
theorem exists_lift_three_of_twoFaceLift (h2 : I.TwoFaceLift 1)
    {c : Label.{u}} (hc : IsSelfVisible 3 c)
    (p : (I.tower 3).toCellScheme.below (univ.erase (Fin.last 3), 3) → Label.{u})
    (q : (I.tower 3).toCellScheme.below (univ, 3) → Label.{u})
    (hp : (I.tower 3).rows.IsLawfulBelow _ p) (hq : (I.tower 3).rows.IsLawfulBelow _ q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _
      (show ((univ.erase (Fin.last 3), 3) : Finset (Fin 4) × ℕ) ≤ (univ, 3) from
        ⟨erase_subset _ _, le_rfl⟩)) d)) c = min (p d) c) :
    ∃ q' : (I.tower 3).toCellScheme.below (univ, 3) → Label.{u},
      (I.tower 3).rows.IsLawfulBelow _ q' ∧ (∀ d, min (q' d) c = min (q d) c) ∧
        ∀ d, q' (Set.inclusion (CellScheme.below_mono _
          (show ((univ.erase (Fin.last 3), 3) : Finset (Fin 4) × ℕ) ≤ (univ, 3) from
            ⟨erase_subset _ _, le_rfl⟩)) d) = p d :=
  (CellScheme.Rows.cappedLift_iff_forall_exists _).mp
    (towerInvariant_three_of_twoFaceLift I h2 _ (mem_insert_self _ _) 3 le_rfl) c hc p q hp hq hpq

end ArityTwo

/-- **No hypothesis at the arities `m ≤ 1`**: the invariant holds up to the grade `m + 1`
(`Seed.towerInvariant_of_le_one`). -/
theorem towerInvariant_succ_of_le_one {α : Ordinal.{u}} {m : ℕ} (hm : m ≤ 1) (I : Seed.{u} α m) :
    I.TowerInvariant (m + 1) :=
  I.towerInvariant_of_le_one hm (m + 1) le_rfl

/-! ### Example 5: literal faces of the tower -/

/-- **Literal faces at arity two**: the scheme reached after the grade `3` of a seed on four
points, with the glued labelling reduced to a stage that is zero or a limit, has the two coatom
types as its faces along the two coatoms. -/
theorem restrictFace_towerType_two {α : Ordinal.{u}} (I : Seed.{u} α 2)
    (hα : Order.IsSuccPrelimit α) :
    StageType.restrictFace (Coatom.left 2) (towerType I hα (j := 3) (by omega)) = some I.left ∧
      StageType.restrictFace (Coatom.right 2) (towerType I hα (j := 3) (by omega)) =
        some I.right :=
  ⟨restrictFace_left_towerType I hα _, restrictFace_right_towerType I hα _⟩

/-! ### Example 6: orbit codes at grade three -/

section GradeThree

open Ordinal

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

private theorem visibilityReplace_Q (b f : ℕ) :
    visibilityReplace 3 3 (Q.{u} b f) = Q b (if f < 3 then 3 else f) := by
  rw [Q, Q, visibilityReplace_coe, Ordinal.visibilityReplace_omega0_mul_add_natCast]

private theorem isSelfVisible_Q {b f : ℕ} : IsSelfVisible 3 (Q.{u} b f) ↔ 3 ≤ f := by
  rw [Q, isSelfVisible_coe, omega0_mul_add_natCast_mod, Nat.cast_le]

private theorem gridPoint_eq_Q (b : ℕ) : gridPoint.{u} 3 b = Q b 3 := rfl

/-- The labelling of example 6 at the grade `3`: `(2, 3, ω * 5 + 2, ω * 5 + 3)`.  The values `2`
and `ω * 5 + 2` are values of cells of grade `2`, not self-visible at `3`. -/
noncomputable def gradeThreeLabelling : Fin 4 → Label.{u} := ![Q 0 2, Q 0 3, Q 5 2, Q 5 3]

/-- The keys of the labelling of example 6 are `3` and `ω * 5 + 3`. -/
private theorem image_visibilityReplace_gradeThreeLabelling :
    (univ.image fun i ↦ visibilityReplace 3 3 (gradeThreeLabelling.{u} i)) ⊆ {Q 0 3, Q 5 3} := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := mem_image.mp hy
  fin_cases i <;> simp [gradeThreeLabelling, visibilityReplace_Q]

/-- Every value of the labelling of example 6 has an orbit key. -/
private theorem isOrbitKey_gradeThreeLabelling (i : Fin 4) :
    IsOrbitKey 3 gradeThreeLabelling.{u} (gradeThreeLabelling i) := by
  fin_cases i
  · exact ⟨0, rfl, by simp [gradeThreeLabelling, isSelfVisible_Q]⟩
  · exact ⟨0, by simp [gradeThreeLabelling, visibilityReplace_Q], by simp [gradeThreeLabelling,
      isSelfVisible_Q]⟩
  · exact ⟨2, rfl, by simp [gradeThreeLabelling, isSelfVisible_Q]⟩
  · exact ⟨2, by simp [gradeThreeLabelling, visibilityReplace_Q], by simp [gradeThreeLabelling,
      isSelfVisible_Q]⟩

/-- **The orbit code at grade three** of `(2, 3, ω * 5 + 2, ω * 5 + 3)` is
`(2, 3, ω * 4 + 2, ω * 4 + 3)`: the natural strip is kept, and the strip of the key `ω * 5 + 3`, of
key rank `2`, moves to the block `4` with its finite parts. -/
theorem orbitCode_gradeThreeLabelling :
    orbitCode 3 gradeThreeLabelling.{u} = ![Q 0 2, Q 0 3, Q 4 2, Q 4 3] := by
  have hlt : visibilityReplace 3 3 (gradeThreeLabelling.{u} 1) <
      visibilityReplace 3 3 (gradeThreeLabelling.{u} 3) := by
    -- the entries of `gradeThreeLabelling` at `1` and `3`
    change visibilityReplace 3 3 (Q.{u} 0 3) < visibilityReplace 3 3 (Q 5 3)
    rw [visibilityReplace_Q, visibilityReplace_Q]
    exact lt_of_le_of_ne (Q_le_Q_iff.mpr (.inl (by decide))) fun h ↦ by simp [Q_inj] at h
  have hkey3 : keyRank 3 gradeThreeLabelling.{u} (gradeThreeLabelling 3) = 2 := by
    refine le_antisymm ?_ ?_
    · exact (Finset.card_le_card (filter_subset _ _)).trans
        ((Finset.card_le_card image_visibilityReplace_gradeThreeLabelling).trans card_le_two)
    · have h1 := one_le_keyRank (isOrbitKey_gradeThreeLabelling.{u} 1).isKey
      have h2 := keyRank_lt_keyRank (isOrbitKey_gradeThreeLabelling.{u} 3).isKey hlt
      omega
  have hkey2 : keyRank 3 gradeThreeLabelling.{u} (gradeThreeLabelling 2) = 2 := by
    refine (keyRank_congr ?_).trans hkey3
    -- the entries of `gradeThreeLabelling` at `2` and `3`
    change visibilityReplace 3 3 (Q.{u} 5 2) = visibilityReplace 3 3 (Q 5 3)
    rw [visibilityReplace_Q, visibilityReplace_Q]
    rfl
  have hn (b f : ℕ) (hf : f ≤ 3) : visibilityReplace 3 3 (Q.{u} b f) = Q b 3 := by
    rw [visibilityReplace_Q]
    congr 1
    split_ifs <;> omega
  have hnat (i : Fin 4) (hb : 2 ≤ (i : ℕ)) :
      visibilityReplace 3 3 (gradeThreeLabelling.{u} i) ≠ gridPoint 3 0 := by
    fin_cases i
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · -- the entry of `gradeThreeLabelling` at `2`; `gridPoint 3 0` is `Q 0 3`
      change visibilityReplace 3 3 (Q.{u} 5 2) ≠ Q 0 3
      rw [hn 5 2 (by decide), Ne, Q_inj]
      decide
    · -- the entry of `gradeThreeLabelling` at `3`; `gridPoint 3 0` is `Q 0 3`
      change visibilityReplace 3 3 (Q.{u} 5 3) ≠ Q 0 3
      rw [hn 5 3 le_rfl, Ne, Q_inj]
      decide
  have hcode (i : Fin 4) (hi : (i : ℕ) < 2) :
      orbitCode 3 gradeThreeLabelling.{u} i = gradeThreeLabelling i := by
    have hi0 : visibilityReplace 3 3 (gradeThreeLabelling.{u} i) = gridPoint 3 0 := by
      fin_cases i
      · exact hn 0 2 (by decide)
      · exact hn 0 3 le_rfl
      · exact absurd hi (by decide)
      · exact absurd hi (by decide)
    rw [orbitCode_apply, orbitMap_of_isOrbitKey (isOrbitKey_gradeThreeLabelling i),
      codeBlock_of_natural (isOrbitKey_gradeThreeLabelling i) hi0]
    exact moveToBlock_eq_self (by rw [hi0]; exact isSelfVisible_gridPoint 3 0)
  have h2 : orbitCode 3 gradeThreeLabelling.{u} 2 = Q 4 2 := by
    rw [orbitCode_apply, orbitMap_of_isOrbitKey (isOrbitKey_gradeThreeLabelling 2),
      codeBlock_of_isOrbitKey (isOrbitKey_gradeThreeLabelling 2) (hnat 2 le_rfl), hkey2]
    exact moveToBlock_omega0_mul_add _ _ _ _
  have h3 : orbitCode 3 gradeThreeLabelling.{u} 3 = Q 4 3 := by
    rw [orbitCode_apply, orbitMap_of_isOrbitKey (isOrbitKey_gradeThreeLabelling 3),
      codeBlock_of_isOrbitKey (isOrbitKey_gradeThreeLabelling 3) (hnat 3 (by decide)), hkey3]
    exact moveToBlock_omega0_mul_add _ _ _ _
  funext i
  fin_cases i
  · exact hcode 0 (by decide)
  · exact hcode 1 (by decide)
  · exact h2
  · exact h3

/-- **The orbit decoder at the least grid point reads the orbit code at grade three literally**: the
natural strip is kept, so the code agrees with the labelling capped at the least grid point `3`. -/
theorem orbitDecoder_gradeThreeLabelling (i : Fin 4) :
    orbitDecoder 3 gradeThreeLabelling.{u} (gridPoint 3 0) (orbitCode 3 gradeThreeLabelling i) =
      gradeThreeLabelling i :=
  orbitDecoder_orbitCode (fun _ ↦ min_orbitCode_gridPoint_zero _) i

/-- **The natural strip at grade three**: the value `2` keeps its code `2`, below the least grid
point `3`; its block move to the block `2`, `ω * 2 + 2`, would be read as `3` there. -/
theorem min_orbitCode_gradeThreeLabelling_gridPoint_zero :
    min (orbitCode 3 gradeThreeLabelling.{u} 0) (gridPoint 3 0) = Q 0 2 ∧
      min (Q.{u} 2 2) (gridPoint 3 0) ≠ Q 0 2 := by
  refine ⟨?_, ?_⟩
  · rw [orbitCode_gradeThreeLabelling, gridPoint_eq_Q]
    exact min_eq_left (Q_le_Q_iff.mpr (.inr ⟨rfl, by decide⟩))
  · rw [gridPoint_eq_Q, min_eq_right (Q_le_Q_iff.mpr (.inl (by decide)))]
    intro h
    have := Q_le_Q_iff.mp h.le
    omega

end GradeThree

end VaughtConjecture.TowerExamples
