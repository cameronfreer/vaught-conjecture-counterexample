/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.SmallArityExamples
import VaughtConjecture.Extension.SmallArityOne

/-!
# Examples: orbit codes at grade two, and the completion at arity one

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.5 (the two small arities; here the regressions of the
arity one); semantic contract, item 3.

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
  does not.  This is why the one-grade lift is used in its short-cap form
  (`CellScheme.Rows.cappedLift_of_boundary_short`) at grade `2`
  (`Seed.cappedLift_fieldLayerOne_two`).
* **R7, the natural strip** (`min_orbitCode_orbitLabelling_gridPoint_zero`): the value `1` keeps
  its code `1`, so the orbit code agrees with the labelling capped at the least grid point `2`; the
  block move of `1` to the block `2` would not.
* **Regression 7, the cap on the lower layer** (`exists_lift_fourCellPairSeed`,
  `exists_apex_prescription_fourCellPairSeed`).  The seed `fourCellPairSeed` has two coatom types
  that are both the completion of `SmallArityExamples.fourCellSeed`, over the common face of its
  four cells on one point; each coatom carries an apex of grade `2` labelled `⊤`.  The lift from the
  coatom `({0, 1}, 2)` to `(univ, 2)` at the cap `ω * 4 + 2` keeps the observation of the ambient at
  every cell of the lower layer, for every lawful prescription and ambient, among them a
  prescription whose owner is the apex with the maximal label `⊤` (ties are allowed).  It holds
  because the grade-two step uses the lift at grade one as the boundary lift into `(univ, 1)`, with
  `O = (C, 1)`; the catalogue at grade one does not read the cells of grade two.

**Regressions at arity one** (numbered as at arity zero, with 7 above).

1. Long rows: `longRowPairSeed`, both of whose coatom types are the completion of
   `SmallArityExamples.longRowSeed`, has a completion keeping its rows and labels
   (`exists_completion_longRowPairSeed`).
2. A label `⊤`: in every completion of a seed on three points an old cell of grade `2` labelled `⊤`
   keeps `⊤` and some cell of graded index `(univ, 2)` is labelled `⊤` (`top_of_completion`); on
   `fourCellPairSeed` the apex of the first coatom type is such a cell
   (`exists_apex_fourCellPairSeed`, `top_completion_fourCellPairSeed`).
3. The empty face against a one-point face: `SmallArityExamples.fourCellSeed` and
   `fourCellPairSeed` both have completions, and the two coatom types of `fourCellPairSeed` have
   the same face along `Fin.castSuccEmb` (`completions_fourCellSeed_fourCellPairSeed`).
4. Labels above the grade plus one, `3` and `ω * 5 + 3` at grade `2`: their orbit codes are short
   and read literally (`orbitDecoder_aboveGradeLabelling`).
5. Several cells on one point: on `fourCellPairSeed`, the lift from `({0}, 1)` to `(univ, 1)` at
   the cap `ω * 10 + 1` (`exists_lift_point_fourCellPairSeed`).
6. The three cap regimes at grade two, `⊤`, `⊥` and `ω * 4 + 2`
   (`exists_lift_capRegimes_fourCellPairSeed`; at `⊤` the lift is the ambient, `eq_of_min_top`).
8. Literal faces: the completions of `fourCellPairSeed` and `longRowPairSeed` restrict to their
   coatom types (`restrictFace_completion_pairSeeds`).

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

/-! ### Regression 7: the cap on the lower layer during a lift at grade two -/

/-- **The seed on three points with four cells on its common point.**  Its two coatom types are
both the completion of `SmallArityExamples.fourCellSeed` (legal at a stage `α` that is zero or a
limit), whose face along `Fin.castSuccEmb` is the left coatom of that seed: the four cells of
graded index `({0}, 1)`.  Each coatom type carries a cell of full scope and grade `2`, its apex,
labelled `⊤`. -/
noncomputable def fourCellPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    Seed.{u} α 1 :=
  let F := (SmallArityExamples.fourCellSeed α).completionBelowFullGradeZero
  Seed.ofCoatoms (F.isLegal_completion hα) (F.isLegal_completion hα)
    (F.restrictFace_left_completion hα) (F.restrictFace_left_completion hα)

/-- **A cell of full scope of a face type is a cell of the type**, on the face, with its grade and
label (`Scheme.map_comap_gradedIndex`). -/
theorem exists_label_of_restrictFace {α : Ordinal.{u}} {n m j : ℕ}
    {t : StageType.{u} α n} {s : StageType.{u} α m} {f : Fin m ↪ Fin n}
    (hs : StageType.restrictFace f t = some s) {e : Fin s.card}
    (he : s.toCellScheme.gradedIndex e = (Finset.univ, j)) :
    ∃ d, t.toCellScheme.gradedIndex d = (Finset.univ.map f, j) ∧ t.label d = s.label e := by
  obtain ⟨hf, rfl⟩ := (StageType.restrictFace_eq_some_iff t f).mp hs
  refine ⟨t.cellMap f e, ?_, rfl⟩
  rw [← t.toScheme.map_comap_gradedIndex f e]
  -- The graded index of `e` in the restriction is `(univ, j)`.
  change Prod.map (Finset.map f) id ((t.comap f hf).toCellScheme.gradedIndex e) = _
  rw [he]
  rfl

/-- **Regression 7, the cap on the lower layer.**  On `fourCellPairSeed`, the lift from the coatom
`({0, 1}, 2)` to `(univ, 2)` at the cap `ω * 4 + 2` keeps, at every cell of the lower layer (graded
index `(univ, 1)`), the observation of the ambient at the cap, for every lawful prescription and
ambient with the same observation below the coatom; the prescription may have the apex of the
coatom, with the maximal label `⊤`, as its owner (ties are allowed)
(`exists_apex_prescription_fourCellPairSeed`).  It is the lift
`Seed.exists_lift_fieldLayerOne_two`, whose grade-two step uses `V = (univ, 1)` and `O = (C, 1)`
and whose catalogue at grade one does not read the cells of grade two. -/
theorem exists_lift_fourCellPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α)
    (p : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below
      (Finset.univ.erase (Fin.last 2), 2) → Label.{u})
    (q : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below (Finset.univ, 2) → Label.{u})
    (hp : (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ p)
    (hq : (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _
      (show ((Finset.univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 2) from
        ⟨erase_subset _ _, le_rfl⟩)) d)) (Q 4 2) = min (p d) (Q 4 2)) :
    ∃ q' : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below (Finset.univ, 2) → Label.{u},
      (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ q' ∧
      (∀ d, q' (Set.inclusion (CellScheme.below_mono _
        (show ((Finset.univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 2) from
          ⟨erase_subset _ _, le_rfl⟩)) d) = p d) ∧
      ∀ (z : Fin (fourCellPairSeed α hα).fieldLayerOne.card)
        (hz : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.gradedIndex z = (Finset.univ, 1)),
        min (q' ⟨z, hz.trans_le ⟨subset_rfl, one_le_two⟩⟩) (Q 4 2) =
          min (q ⟨z, hz.trans_le ⟨subset_rfl, one_le_two⟩⟩) (Q 4 2) := by
  obtain ⟨q', hq', hcap, hlit⟩ := (fourCellPairSeed α hα).exists_lift_fieldLayerOne_two
    (x := Fin.last 2) (y := Fin.castSucc (Fin.last 1)) (by decide) (by decide) (by decide)
    (isSelfVisible_Q.mpr le_rfl) p q hp hq hpq
  exact ⟨q', hq', hlit, fun z _ ↦ hcap _⟩

/-- **The apex of the first coatom type of `fourCellPairSeed` is a cell of the amalgam**, of graded
index `({0, 1}, 2)` and labelled `⊤`: the apex of the completion of `fourCellSeed`, seen through the
face map along `Fin.castSuccEmb`. -/
theorem exists_apex_fourCellPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    ∃ d, (fourCellPairSeed α hα).amalgam.toCellScheme.gradedIndex d =
      (Finset.univ.erase (Fin.last 2), 2) ∧ (fourCellPairSeed α hα).amalgam.label d = ⊤ := by
  set F := (SmallArityExamples.fourCellSeed α).completionBelowFullGradeZero
  have hlabel : (F.completion hα).label (Fin.last _) = ⊤ := StageType.addApex_label_last _ _
  obtain ⟨a₀, ha₀, ha₀max⟩ := F.exists_apex_completion hα
  have ha₀l : (F.completion hα).label a₀ = ⊤ := top_le_iff.mp (hlabel ▸ ha₀max _)
  have hleft : StageType.restrictFace (Coatom.left 1) (fourCellPairSeed α hα).amalgam =
      some (F.completion hα) :=
    (fourCellPairSeed α hα).restrictFace_left
  obtain ⟨d₀, hd₀, hd₀l⟩ := exists_label_of_restrictFace (e := a₀) hleft ha₀
  rw [Coatom.univ_map_left] at hd₀
  exact ⟨d₀, hd₀, hd₀l.trans ha₀l⟩

/-- **Regression 7 is not vacuous**: on `fourCellPairSeed`, some lawful prescription below the
coatom `({0, 1}, 2)` and some lawful ambient below `(univ, 2)` with the same observation at
`ω * 4 + 2` have, as owner, the apex of the coatom, of graded index `({0, 1}, 2)`, labelled `⊤`:
the glued labelling of the amalgam, extended through both layers
(`Seed.exists_isLawful_fieldLayerOne`). -/
theorem exists_apex_prescription_fourCellPairSeed (α : Ordinal.{u})
    (hα : Order.IsSuccPrelimit α) :
    ∃ (p : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below
        (Finset.univ.erase (Fin.last 2), 2) → Label.{u})
      (q : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below (Finset.univ, 2) → Label.{u}),
      (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ p ∧
      (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ q ∧
      (∀ d, min (q (Set.inclusion (CellScheme.below_mono _
        (show ((Finset.univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 2) from
          ⟨erase_subset _ _, le_rfl⟩)) d)) (Q 4 2) = min (p d) (Q 4 2)) ∧
      ∃ o, (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.gradedIndex o.1 =
        (Finset.univ.erase (Fin.last 2), 2) ∧ p o = ⊤ := by
  set I := fourCellPairSeed α hα
  obtain ⟨r, hr, hre⟩ := I.exists_isLawful_fieldLayerOne I.amalgam.isLawful
  obtain ⟨d₀, hd₀, hd₀l⟩ := exists_apex_fourCellPairSeed α hα
  have hgi : I.fieldLayerOne.toCellScheme.gradedIndex (Fin.castAdd _ (Fin.castAdd _ d₀)) =
      (Finset.univ.erase (Fin.last 2), 2) :=
    (Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ _).trans
      ((Scheme.appendFullCellsScheme_gradedIndex_castAdd _ _ _ d₀).trans hd₀)
  refine ⟨fun d ↦ r d, fun d ↦ r d, hr.isLawfulBelow _, hr.isLawfulBelow _, fun _ ↦ rfl,
    ⟨_, hgi.le⟩, hgi, ?_⟩
  -- The prescription at the apex is the extension at its old cell.
  change r (Fin.castAdd _ (Fin.castAdd _ d₀)) = ⊤
  rw [hre, hd₀l]

/-! ### Regressions 1–6 and 8 at arity one -/

/-- The seed on three points whose two coatom types are both the completion of
`SmallArityExamples.longRowSeed`, whose rows exceed the grade plus one and whose labels are
bottom. -/
noncomputable def longRowPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    Seed.{u} α 1 :=
  let F := (SmallArityExamples.longRowSeed α).completionBelowFullGradeZero
  Seed.ofCoatoms (F.isLegal_completion hα) (F.isLegal_completion hα)
    (F.restrictFace_left_completion hα) (F.restrictFace_left_completion hα)

/-- **Regression 1, long rows.**  `longRowPairSeed` has a completion below the full grade, which
keeps the rows and the labels of the amalgam on its old cells. -/
theorem exists_completion_longRowPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    ∃ F : CompletionBelowFullGrade (longRowPairSeed α hα),
      F.scheme.rows.comap F.isLowerEmbedding = (longRowPairSeed α hα).amalgam.rows ∧
        ∀ d, F.label (F.embed d) = (longRowPairSeed α hα).amalgam.label d :=
  ⟨_, (longRowPairSeed α hα).completionBelowFullGradeOne.comap_rows,
    (longRowPairSeed α hα).completionBelowFullGradeOne.label_embed⟩

/-- **A label `⊤` at grade two is kept and carried by a new cell.**  In a completion of a seed on
three points, an old cell of grade `2` labelled `⊤` keeps `⊤`, and some cell of graded index
`(univ, 2)` is labelled `⊤` (availability). -/
theorem top_of_completion {α : Ordinal.{u}} {I : Seed.{u} α 1} (F : CompletionBelowFullGrade I)
    {d : Fin I.amalgam.card} (hd : I.amalgam.toCellScheme.grade d = 2)
    (hl : I.amalgam.label d = ⊤) :
    F.label (F.embed d) = ⊤ ∧
      ∃ z, F.scheme.toCellScheme.gradedIndex z = (Finset.univ, 2) ∧ F.label z = ⊤ := by
  refine ⟨(F.label_embed d).trans hl, ?_⟩
  have hwf := F.isLegalBelowFullGrade.isWellFormed
  obtain ⟨t, ht⟩ := F.isLegalBelowFullGrade.exists_gradedIndex_eq (Finset.univ, 2)
    ⟨hwf.univ_mem_faces, two_pos, by simp⟩ (by omega)
  have hgs : F.scheme.toCellScheme.grade (F.embed d) = F.scheme.toCellScheme.grade t :=
    ((F.isLowerEmbedding.grade_eq d).trans hd).trans (congrArg Prod.snd ht).symm
  obtain ⟨z, hz, hle⟩ := F.isLawful.availability (F.embed d) t
    (by rw [show F.scheme.toCellScheme.scope t = Finset.univ from congrArg Prod.fst ht];
        exact subset_univ _) hgs
  refine ⟨z, hz.trans ht, top_le_iff.mp ?_⟩
  rw [← (F.label_embed d).trans hl]
  exact hle

/-- **Regression 2, a `⊤` label, on a concrete seed.**  In the completion of `fourCellPairSeed`,
the apex of the first coatom type, an old cell of graded index `({0, 1}, 2)` labelled `⊤`, keeps
`⊤`, and some new cell of graded index `(univ, 2)` is labelled `⊤`. -/
theorem top_completion_fourCellPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    ∃ d, (fourCellPairSeed α hα).amalgam.toCellScheme.gradedIndex d =
        (Finset.univ.erase (Fin.last 2), 2) ∧
      (fourCellPairSeed α hα).completionBelowFullGradeOne.label
        ((fourCellPairSeed α hα).completionBelowFullGradeOne.embed d) = ⊤ ∧
      ∃ z, (fourCellPairSeed α hα).completionBelowFullGradeOne.scheme.toCellScheme.gradedIndex z =
        (Finset.univ, 2) ∧ (fourCellPairSeed α hα).completionBelowFullGradeOne.label z = ⊤ := by
  obtain ⟨d, hd, hl⟩ := exists_apex_fourCellPairSeed α hα
  exact ⟨d, hd, top_of_completion _ (congrArg Prod.snd hd) hl⟩

/-- **Regression 3, the empty face against a one-point face.**  The seed on two points
`fourCellSeed` (common face empty) and the seed on three points `fourCellPairSeed` (common face
`{0}`, carrying the four cells on one point) both have completions below the full grade, and the
two coatom types of `fourCellPairSeed` have the same face along `Fin.castSuccEmb`, literally. -/
theorem completions_fourCellSeed_fourCellPairSeed (α : Ordinal.{u})
    (hα : Order.IsSuccPrelimit α) :
    Nonempty (CompletionBelowFullGrade (SmallArityExamples.fourCellSeed α)) ∧
      Nonempty (CompletionBelowFullGrade (fourCellPairSeed α hα)) ∧
      StageType.restrictFace (Coatom.face 1) (fourCellPairSeed α hα).left =
        StageType.restrictFace (Coatom.face 1) (fourCellPairSeed α hα).right :=
  ⟨Seed.nonempty_completionBelowFullGrade_of_le_one (Nat.zero_le 1) _,
    Seed.nonempty_completionBelowFullGrade_of_le_one le_rfl _,
    (fourCellPairSeed α hα).restrictFace_face_left.trans
      (fourCellPairSeed α hα).restrictFace_face_right.symm⟩

/-- The labelling of regression 4 at grade `2`: `3` on a cell of grade `1` and `ω * 5 + 3` on a
cell of grade `2`. -/
noncomputable def aboveGradeLabelling : Fin 2 → Label.{u} := ![Q 0 3, Q 5 3]

/-- **Regression 4, labels above the grade plus one.**  At grade `2`, the labels `3` and
`ω * 5 + 3` are not short, their orbit codes are, and the orbit decoder at the least grid point
reads the codes literally. -/
theorem orbitDecoder_aboveGradeLabelling :
    ¬ IsShort 2 (aboveGradeLabelling.{u} 0) ∧ ¬ IsShort 2 (aboveGradeLabelling.{u} 1) ∧
      (∀ i, IsShort 2 (orbitCode 2 aboveGradeLabelling.{u} i)) ∧
      ∀ i, orbitDecoder 2 aboveGradeLabelling.{u} (gridPoint 2 0)
        (orbitCode 2 aboveGradeLabelling i) = aboveGradeLabelling i := by
  have hns (b : ℕ) : ¬ IsShort 2 (Q.{u} b 3) := fun h ↦ by
    have := isShort_coe.mp h
    rw [omega0_mul_add_natCast_mod] at this
    exact absurd (by exact_mod_cast this : 3 ≤ 2) (by decide)
  exact ⟨hns 0, hns 5, fun _ ↦ isShort_orbitCode _,
    orbitDecoder_orbitCode fun _ ↦ min_orbitCode_gridPoint_zero _⟩

/-- **Regression 5, several cells on one point.**  On `fourCellPairSeed`, whose common point
carries four cells of grade `1`, the completion lifts capped from `({0}, 1)` to `(univ, 1)`
(`Seed.isBountiful_fieldLayerOne`); at the cap `ω * 10 + 1` a prescription and an ambient with
the same observation below `({0}, 1)` have a lift keeping the observation at every cell. -/
theorem exists_lift_point_fourCellPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α)
    (p : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below ({0}, 1) → Label.{u})
    (q : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below (Finset.univ, 1) → Label.{u})
    (hp : (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ p)
    (hq : (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _
      (show ((({0} : Finset (Fin 3)), 1) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 1) from
        ⟨subset_univ _, le_rfl⟩)) d)) (gridPoint 1 10) = min (p d) (gridPoint 1 10)) :
    ∃ q' : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below (Finset.univ, 1) → Label.{u},
      (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ q' ∧
        (∀ d, min (q' d) (gridPoint 1 10) = min (q d) (gridPoint 1 10)) ∧
        ∀ d, q' (Set.inclusion (CellScheme.below_mono _
          (show ((({0} : Finset (Fin 3)), 1) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 1) from
            ⟨subset_univ _, le_rfl⟩)) d) = p d := by
  have h0 : ({0} : Finset (Fin 3)) ∈ (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.faces :=
    (fourCellPairSeed α hα).face_mem_faces
  have hu : (Finset.univ : Finset (Fin 3)) ∈
      (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.faces :=
    (fourCellPairSeed α hα).amalgam.univ_mem_faces
  have hle : ((({0} : Finset (Fin 3)), 1) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 1) :=
    ⟨subset_univ _, le_rfl⟩
  exact (CellScheme.Rows.cappedLift_iff_forall_exists hle).mp
    ((fourCellPairSeed α hα).isBountiful_fieldLayerOne (X := ({0}, 1)) (Y := (Finset.univ, 1))
      ⟨h0, one_pos, by simp⟩ ⟨hu, one_pos, by simp⟩ hle) _ (isSelfVisible_gridPoint 1 10) p q hp
      hq hpq

/-- **Regression 6, the three cap regimes at grade two.**  On `fourCellPairSeed`, the lift from the
coatom `({0, 1}, 2)` to `(univ, 2)` exists at the caps `⊤` (where it is the ambient itself), `⊥`
(where only the prescription matters) and `ω * 4 + 2`. -/
theorem exists_lift_capRegimes_fourCellPairSeed (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α)
    {c : Label.{u}} (hc : c = ⊤ ∨ c = ⊥ ∨ c = Q 4 2)
    (p : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below
      (Finset.univ.erase (Fin.last 2), 2) → Label.{u})
    (q : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below (Finset.univ, 2) → Label.{u})
    (hp : (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ p)
    (hq : (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ q)
    (hpq : ∀ d, min (q (Set.inclusion (CellScheme.below_mono _
      (show ((Finset.univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 2) from
        ⟨erase_subset _ _, le_rfl⟩)) d)) c = min (p d) c) :
    ∃ q' : (fourCellPairSeed α hα).fieldLayerOne.toCellScheme.below (Finset.univ, 2) → Label.{u},
      (fourCellPairSeed α hα).fieldLayerOne.rows.IsLawfulBelow _ q' ∧
        (∀ d, min (q' d) c = min (q d) c) ∧
        ∀ d, q' (Set.inclusion (CellScheme.below_mono _
          (show ((Finset.univ.erase (Fin.last 2), 2) : Finset (Fin 3) × ℕ) ≤ (Finset.univ, 2) from
            ⟨erase_subset _ _, le_rfl⟩)) d) = p d := by
  have hcv : IsSelfVisible 2 c := by
    rcases hc with rfl | rfl | rfl
    exacts [isSelfVisible_top 2, isSelfVisible_bot 2, isSelfVisible_Q.mpr le_rfl]
  exact (fourCellPairSeed α hα).exists_lift_fieldLayerOne_two (x := Fin.last 2)
    (y := Fin.castSucc (Fin.last 1)) (by decide) (by decide) (by decide) hcv p q hp hq hpq

/-- At the cap `⊤` the lift of regression 6 is the ambient itself. -/
theorem eq_of_min_top {X : Type*} {q q' : X → Label.{u}} (h : ∀ d, min (q' d) ⊤ = min (q d) ⊤) :
    q' = q :=
  funext fun d ↦ by simpa using h d

/-- **Regression 8, literal faces.**  The completions of `fourCellPairSeed` and `longRowPairSeed`
have their two coatom types as faces, literally, labels included. -/
theorem restrictFace_completion_pairSeeds (α : Ordinal.{u}) (hα : Order.IsSuccPrelimit α) :
    (StageType.restrictFace (Coatom.left 1)
        ((fourCellPairSeed α hα).completionBelowFullGradeOne.completion hα) =
          some (fourCellPairSeed α hα).left ∧
      StageType.restrictFace (Coatom.right 1)
        ((fourCellPairSeed α hα).completionBelowFullGradeOne.completion hα) =
          some (fourCellPairSeed α hα).right) ∧
    (StageType.restrictFace (Coatom.left 1)
        ((longRowPairSeed α hα).completionBelowFullGradeOne.completion hα) =
          some (longRowPairSeed α hα).left ∧
      StageType.restrictFace (Coatom.right 1)
        ((longRowPairSeed α hα).completionBelowFullGradeOne.completion hα) =
          some (longRowPairSeed α hα).right) :=
  ⟨⟨CompletionBelowFullGrade.restrictFace_left_completion _ hα,
    CompletionBelowFullGrade.restrictFace_right_completion _ hα⟩,
    ⟨CompletionBelowFullGrade.restrictFace_left_completion _ hα,
      CompletionBelowFullGrade.restrictFace_right_completion _ hα⟩⟩

end VaughtConjecture.SmallArityOneExamples
