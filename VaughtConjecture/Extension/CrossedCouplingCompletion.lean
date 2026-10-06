/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CrossedCouplingScheme

/-!
# The completion of the crossed-coupling seed

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`; here
the completion of a seed with two opposite forced separations, which has no ordered-layer step);
semantic contract, items 2–4.

Let `I` be a seed whose coatom types are `TH` and `TG`, such as `seedHG`, and `schemeHG I` its
multi-layer scheme with two new cells at `(univ, 1)`
(`VaughtConjecture.Extension.CrossedCouplingScheme`).

**The new cells carry the parameters.**  Below `(univ, k)`, a lawful labelling is, at the new cells,
the value of the old cell of the same kind: at `cellAD` and `cellAC` the values at `({4}, 1)` and
`({3}, 1)` (`eq_of_isLawfulBelow_one`: each new cell reads its own kind at `ω + 2` and the other at
`1`, so it lies below its parameter and agrees with it capped at the other cell, and availability
from `({3}, 1)` and `({4}, 1)` places each parameter below one of the two cells;
`eq_of_forced_pair`), at `cellH` and `cellG` the values at `({0, 1, 2}, 2)` and `({0, 1, 2}, 3)`
(`eq_of_isLawfulBelow_two`, `eq_of_isLawfulBelow_three`), and at the grade `4` one value at every
cell, which, if not `⊥`, forces `⊥` below the grade `4` (`eq_of_isLawfulBelow_four`,
`eq_bot_of_isLawfulBelow_four`).  So below `(univ, k)`, `1 ≤ k ≤ 3`, the lawful labellings are
exactly the labellings by kinds with parameters coupled as in `TH` and `TG`
(`exists_of_isLawfulBelow_univ`, with `isLawful_kindLabel`).

**The capped lifts.**  From `(C, k)` to `(univ, k)`, `k ≤ 3` (`cappedLift_C_of_le_three`): the
lift keeps the parameters `A_C`, `H`, `G` of the prescription and takes for `A_D` the ambient below
the cap and `⊤` above it (`liftParamsG`); the coupling `G ≤ A_D` is kept because below the cap
the parameter `G` of the prescription is that of the ambient.  From `(D, k)` to `(univ, k)`
(`cappedLift_D_of_le_three`): the lift keeps `A_D`, `H`, `G` and takes for `A_C` the ambient below
the cap, and above it `H` when `k = 3` and `H < G`, and `⊤` otherwise, so always `⊤` at `k ≤ 2`
(`liftParamsH`).  At the grade `4` (`cappedLift_four_HG`) the lift comes from the lift at the
grade `3`, as for the ordered-layer step (`OrderedLayer.cappedLift_four`).

**The completion** (`multiLayerStep_HG`, `nonempty_completionBelowFullGrade_of`,
`completionHG`, `nonempty_completionBelowFullGrade_seedHG`): every field of
`Seed.MultiLayerStep` holds, so `seedHG` has a completion below the full grade; its lawful
extension of the glued labelling is `⊤` at the cells of grade `4` and `⊥` elsewhere.  Its old
cells keep their scopes, rows and labels, so with the apex added its faces along the two coatoms
are literally `TH` and `TG`, at every stage, since its labels `⊥` and `⊤` lie at every stage
(`exists_coatomExtension_seedHG`).  Since `seedHG`
has no ordered-layer step (`not_hasOrderedLayerStep_seedHG`), the ordered-layer step is strictly
stronger than the completion (`not_forall_hasOrderedLayerStep_of_nonempty`).

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").

## References

The completion has the shape of [Kni26, Definition 4.3.14] (the old cells kept, the new cells of
full scope, two of them at `(univ, 1)`); its rows are not those of that definition, and neither
printed proof of [Kni26, Lemma 4.3.16] or [Kni26, Lemma 4.3.20] is used.
-/

universe u

namespace VaughtConjecture.CrossedCouplingCounterexample

open Finset Label CellScheme OrderedLayer
open Ordinal hiding univ
open TwoFaceLiftCounterexample (cellScope cellGrade cells v1 v2 gradedIndex_cells stripShifter
  isWitness_stripShifter stripShifter_v1 stripShifter_v2)
open TwoFaceLiftExistsCounterexample (strip3 isWitness_strip3)

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {H G : Label.{u}}
variable (hIL : I.left = TH α) (hIR : I.right = TG α)
include hIL hIR

/-! ### The new cells carry the parameters -/

omit hIL hIR in
/-- **Two values forced by two opposite readings**: in a linear order, if `x₁ ≤ A_D`, `x₂ ≤ A_C`,
`x₁` reads `A_C` as it reads `x₂`, `x₂` reads `A_D` as it reads `x₁`, and each of `A_C`, `A_D` is
at most `x₁` or `x₂`, then `x₁ = A_D` and `x₂ = A_C`. -/
theorem eq_of_forced_pair {L : Type*} [LinearOrder L] {AC AD x1 x2 : L} (a1 : x1 ≤ AD)
    (a2 : x2 ≤ AC) (c1 : min AC x1 = min x2 x1) (c2 : min AD x2 = min x1 x2)
    (e : AD ≤ x1 ∨ AD ≤ x2) (f : AC ≤ x1 ∨ AC ≤ x2) : x1 = AD ∧ x2 = AC := by
  rcases le_total AC x1 with h1 | h1 <;> rcases le_total x2 x1 with h2 | h2 <;>
    rcases le_total AD x2 with h3 | h3 <;> rcases le_total x1 x2 with h4 | h4 <;>
    simp only [min_eq_left, min_eq_right, h1, h2, h3, h4] at c1 c2 <;>
    constructor <;> rcases e with e | e <;> rcases f with f | f <;> order

omit hIL hIR in
/-- **The new cells at `(univ, 1)` carry the parameters `A_D` and `A_C`**: below `(univ, k)`,
`k ≥ 1`, a lawful labelling is `x ({4}, 1)` at the first and `x ({3}, 1)` at the second. -/
theorem eq_of_isLawfulBelow_one {k : ℕ} (hk : 1 ≤ k) {x : Fin (schemeHG I).card → Label.{u}}
    (hx : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k) fun z ↦ x z)
    {d₃ d₄ : Fin I.amalgam.card}
    (h₃ : I.amalgam.toCellScheme.gradedIndex d₃ = (({3} : Finset (Fin 5)), 1))
    (h₄ : I.amalgam.toCellScheme.gradedIndex d₄ = (({4} : Finset (Fin 5)), 1)) :
    x (cellAD I) = x (multiOldCell I multHG d₄) ∧
      x (cellAC I) = x (multiOldCell I multHG d₃) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  set o₃ := multiOldCell I multHG d₃
  set o₄ := multiOldCell I multHG d₄
  have gr₃ : (schemeHG I).toCellScheme.grade o₃ = 1 :=
    congrArg Prod.snd ((gradedIndex_multiOldCell d₃).trans h₃)
  have gr₄ : (schemeHG I).toCellScheme.grade o₄ = 1 :=
    congrArg Prod.snd ((gradedIndex_multiOldCell d₄).trans h₄)
  have k₃ : cellKind I o₃ = .ac := by rw [cellKind_multiOldCell, h₃]; decide
  have k₄ : cellKind I o₄ = .ad := by rw [cellKind_multiOldCell, h₄]; decide
  have bAD (z) (hz : (schemeHG I).toCellScheme.grade z = 1) :
      z ∈ (schemeHG I).toCellScheme.below ((schemeHG I).toCellScheme.gradedIndex (cellAD I)) := by
    rw [gradedIndex_cellAD]; exact mem_below_univ hz.le
  have bAC (z) (hz : (schemeHG I).toCellScheme.grade z = 1) :
      z ∈ (schemeHG I).toCellScheme.below ((schemeHG I).toCellScheme.gradedIndex (cellAC I)) := by
    rw [gradedIndex_cellAC]; exact mem_below_univ hz.le
  have LAD := hl (cellAD I) (mem_below_univ (by rw [grade_cellAD]; exact hk))
  have LAC := hl (cellAC I) (mem_below_univ (by rw [grade_cellAC]; exact hk))
  -- Locality at the first new cell: it reads `({4}, 1)` and itself at `ω + 2`, and `({3}, 1)` and
  -- the second new cell at `1`.
  have a1 : x (cellAD I) ≤ x o₄ := by
    have := LAD.le_of_le (d := ⟨cellAD I, bAD _ grade_cellAD⟩) (d' := ⟨o₄, bAD _ gr₄⟩)
      (by rw [row_cellAD, row_cellAD, kindLabel_cellAD]; simp [kindLabel, k₄, CellKind.val])
      (by dsimp only; rw [gr₄, grade_cellAD])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have c1 : min (x o₃) (x (cellAD I)) = min (x (cellAC I)) (x (cellAD I)) := by
    refine le_antisymm (LAD.le_of_le (d := ⟨o₃, bAD _ gr₃⟩) (d' := ⟨cellAC I, bAD _ grade_cellAC⟩)
      ?_ ?_) (LAD.le_of_le (d := ⟨cellAC I, bAD _ grade_cellAC⟩) (d' := ⟨o₃, bAD _ gr₃⟩) ?_ ?_)
    · rw [row_cellAD, row_cellAD, kindLabel_cellAC]; simp [kindLabel, k₃, CellKind.val]
    · dsimp only; rw [gr₃, grade_cellAC]
    · rw [row_cellAD, row_cellAD, kindLabel_cellAC]; simp [kindLabel, k₃, CellKind.val]
    · dsimp only; rw [gr₃, grade_cellAC]
  -- Locality at the second new cell, symmetrically.
  have a2 : x (cellAC I) ≤ x o₃ := by
    have := LAC.le_of_le (d := ⟨cellAC I, bAC _ grade_cellAC⟩) (d' := ⟨o₃, bAC _ gr₃⟩)
      (by rw [row_cellAC, row_cellAC, kindLabel_cellAC]; simp [kindLabel, k₃, CellKind.val])
      (by dsimp only; rw [gr₃, grade_cellAC])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  have c2 : min (x o₄) (x (cellAC I)) = min (x (cellAD I)) (x (cellAC I)) := by
    refine le_antisymm (LAC.le_of_le (d := ⟨o₄, bAC _ gr₄⟩) (d' := ⟨cellAD I, bAC _ grade_cellAD⟩)
      ?_ ?_) (LAC.le_of_le (d := ⟨cellAD I, bAC _ grade_cellAD⟩) (d' := ⟨o₄, bAC _ gr₄⟩) ?_ ?_)
    · rw [row_cellAC, row_cellAC, kindLabel_cellAD]; simp [kindLabel, k₄, CellKind.val]
    · dsimp only; rw [gr₄, grade_cellAD]
    · rw [row_cellAC, row_cellAC, kindLabel_cellAD]; simp [kindLabel, k₄, CellKind.val]
    · dsimp only; rw [gr₄, grade_cellAD]
  -- Availability from `({4}, 1)` and from `({3}, 1)` to `(univ, 1)`.
  have hmem : cellAD I ∈ (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), k) :=
    mem_below_univ (by rw [grade_cellAD]; exact hk)
  obtain ⟨u, hu, e⟩ := ha o₄ (cellAD I) hmem (by rw [scope_cellAD]; exact subset_univ _)
    (gr₄.trans grade_cellAD.symm)
  obtain ⟨u', hu', f⟩ := ha o₃ (cellAD I) hmem (by rw [scope_cellAD]; exact subset_univ _)
    (gr₃.trans grade_cellAD.symm)
  have e' : x o₄ ≤ x (cellAD I) ∨ x o₄ ≤ x (cellAC I) := by
    rcases eq_cellAD_or_cellAC (hu.trans gradedIndex_cellAD) with rfl | rfl
    · exact .inl e
    · exact .inr e
  have f' : x o₃ ≤ x (cellAD I) ∨ x o₃ ≤ x (cellAC I) := by
    rcases eq_cellAD_or_cellAC (hu'.trans gradedIndex_cellAD) with rfl | rfl
    · exact .inl f
    · exact .inr f
  -- The two values are forced.
  exact eq_of_forced_pair a1 a2 c1 c2 e' f'


omit hIL hIR in
/-- **The new cell at `(univ, 2)` carries the parameter `H`**: below `(univ, k)`, `k ≥ 2`, a lawful
labelling is `x ({0, 1, 2}, 2)` there. -/
theorem eq_of_isLawfulBelow_two {k : ℕ} (hk : 2 ≤ k) {x : Fin (schemeHG I).card → Label.{u}}
    (hx : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k) fun z ↦ x z)
    {e₂ : Fin I.amalgam.card}
    (h₂ : I.amalgam.toCellScheme.gradedIndex e₂ = (({0, 1, 2} : Finset (Fin 5)), 2)) :
    x (cellH I) = x (multiOldCell I multHG e₂) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  have gr : (schemeHG I).toCellScheme.grade (multiOldCell I multHG e₂) = 2 :=
    congrArg Prod.snd ((gradedIndex_multiOldCell e₂).trans h₂)
  have kd : cellKind I (multiOldCell I multHG e₂) = .h := by
    rw [cellKind_multiOldCell, h₂]; decide
  have b (z) (hz : (schemeHG I).toCellScheme.grade z ≤ 2) :
      z ∈ (schemeHG I).toCellScheme.below ((schemeHG I).toCellScheme.gradedIndex (cellH I)) := by
    rw [gradedIndex_cellH]; exact mem_below_univ hz
  have hmem : cellH I ∈ (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), k) :=
    mem_below_univ (by rw [grade_cellH]; exact hk)
  refine le_antisymm ?_ ?_
  · -- Locality: the new cell reads itself and `({0, 1, 2}, 2)` at `ω + 2`.
    have := (hl (cellH I) hmem).le_of_le (d := ⟨cellH I, b _ grade_cellH.le⟩)
      (d' := ⟨multiOldCell I multHG e₂, b _ gr.le⟩)
      (by rw [row_cellH, row_cellH, kindLabel_cellH]; simp [kindLabel, kd, CellKind.val])
      (by dsimp only; rw [gr, grade_cellH])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  · -- Availability from `({0, 1, 2}, 2)` to `(univ, 2)`.
    obtain ⟨u, hu, e⟩ := ha (multiOldCell I multHG e₂) (cellH I) hmem
      (by rw [scope_cellH]; exact subset_univ _) (gr.trans grade_cellH.symm)
    rwa [eq_cellH (hu.trans gradedIndex_cellH)] at e

omit hIL hIR in
/-- **The new cell at `(univ, 3)` carries the parameter `G`**: below `(univ, k)`, `k ≥ 3`, a lawful
labelling is `x ({0, 1, 2}, 3)` there. -/
theorem eq_of_isLawfulBelow_three {k : ℕ} (hk : 3 ≤ k) {x : Fin (schemeHG I).card → Label.{u}}
    (hx : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k) fun z ↦ x z)
    {e₃ : Fin I.amalgam.card}
    (h₃ : I.amalgam.toCellScheme.gradedIndex e₃ = (({0, 1, 2} : Finset (Fin 5)), 3)) :
    x (cellG I) = x (multiOldCell I multHG e₃) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  have gr : (schemeHG I).toCellScheme.grade (multiOldCell I multHG e₃) = 3 :=
    congrArg Prod.snd ((gradedIndex_multiOldCell e₃).trans h₃)
  have kd : cellKind I (multiOldCell I multHG e₃) = .g := by
    rw [cellKind_multiOldCell, h₃]; decide
  have b (z) (hz : (schemeHG I).toCellScheme.grade z ≤ 3) :
      z ∈ (schemeHG I).toCellScheme.below ((schemeHG I).toCellScheme.gradedIndex (cellG I)) := by
    rw [gradedIndex_cellG]; exact mem_below_univ hz
  have hmem : cellG I ∈ (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), k) :=
    mem_below_univ (by rw [grade_cellG]; exact hk)
  refine le_antisymm ?_ ?_
  · -- Locality: the new cell reads itself and `({0, 1, 2}, 3)` at `ω + 3`.
    have := (hl (cellG I) hmem).le_of_le (d := ⟨cellG I, b _ grade_cellG.le⟩)
      (d' := ⟨multiOldCell I multHG e₃, b _ gr.le⟩)
      (by rw [row_cellG, row_cellG, kindLabel_cellG]; simp [kindLabel, kd, CellKind.val])
      (by dsimp only; rw [gr, grade_cellG])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)
  · -- Availability from `({0, 1, 2}, 3)` to `(univ, 3)`.
    obtain ⟨u, hu, e⟩ := ha (multiOldCell I multHG e₃) (cellG I) hmem
      (by rw [scope_cellG]; exact subset_univ _) (gr.trans grade_cellG.symm)
    rwa [eq_cellG (hu.trans gradedIndex_cellG)] at e

omit hIL hIR in
/-- **At the grade `4`, a lawful labelling is constant on the cells of grade `4`**: locality and
availability at the new cell at `(univ, 4)`. -/
theorem eq_of_isLawfulBelow_four {x : Fin (schemeHG I).card → Label.{u}}
    (hx : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) fun z ↦ x z)
    {z : Fin (schemeHG I).card} (hz : (schemeHG I).toCellScheme.grade z = 4) :
    x z = x (cellT I) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  have kz : cellKind I z = .top := (grade_of_cellKind z).2.2.2.2.mpr hz
  have b (z) : z ∈ (schemeHG I).toCellScheme.below
      ((schemeHG I).toCellScheme.gradedIndex (cellT I)) := by
    rw [gradedIndex_cellT]; exact mem_below_univ_four_multi z
  have hmem : cellT I ∈ (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), 4) :=
    mem_below_univ_four_multi _
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu, e⟩ := ha z (cellT I) hmem (by rw [scope_cellT]; exact subset_univ _)
      (hz.trans grade_cellT.symm)
    rwa [eq_cellT (hu.trans gradedIndex_cellT)] at e
  · have := (hl (cellT I) hmem).le_of_le (d := ⟨cellT I, b _⟩) (d' := ⟨z, b _⟩)
      (by rw [row_cellT, row_cellT, kindLabel_cellT]; simp [kindLabel, kz, CellKind.val])
      (by dsimp only; rw [hz, grade_cellT])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)

omit hIL hIR in
/-- **At the grade `4`, a lawful labelling that is not `⊥` at the new cell at `(univ, 4)` is `⊥`
below the grade `4`**: the row of that cell is `⊥` there. -/
theorem eq_bot_of_isLawfulBelow_four {x : Fin (schemeHG I).card → Label.{u}}
    (hx : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) fun z ↦ x z)
    (hT : x (cellT I) ≠ ⊥) {z : Fin (schemeHG I).card}
    (hz : (schemeHG I).toCellScheme.grade z ≠ 4) : x z = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  have kz : cellKind I z ≠ .top := fun h ↦ hz ((grade_of_cellKind z).2.2.2.2.mp h)
  have bz : z ∈ (schemeHG I).toCellScheme.below
      ((schemeHG I).toCellScheme.gradedIndex (cellT I)) := by
    rw [gradedIndex_cellT]; exact mem_below_univ_four_multi z
  have := (hl (cellT I) (mem_below_univ_four_multi _)).eq_bot (d := ⟨z, bz⟩) (by
    rw [row_cellT]
    cases hk : cellKind I z with
    | top => exact absurd hk kz
    | _ => simp [kindLabel, hk, CellKind.val])
  exact (min_eq_bot.mp this).resolve_right hT

/-- **Lawful labellings below `(univ, k)`, `1 ≤ k ≤ 3`**, are labellings by kinds with parameters
coupled as in `TH` and `TG`. -/
theorem exists_of_isLawfulBelow_univ {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 3)
    {x : Fin (schemeHG I).card → Label.{u}}
    (hx : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), k) fun z ↦ x z) :
    ∃ AC AD H G : Label.{u}, IsSelfVisible 1 AC ∧ IsSelfVisible 1 AD ∧ IsSelfVisible 2 H ∧
      IsSelfVisible 3 G ∧ Coupled true AC H G ∧ Coupled false AD H G ∧
      ∀ z ∈ (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), k),
        x z = kindLabel I AC AD H G ⊥ z := by
  obtain ⟨d₃, d₄, e₂, e₃, h₃, h₄, h₂, h₃'⟩ := exists_paramCells hIL hIR
  obtain ⟨A, H, G, hA, hH, hG, hc, hC⟩ :=
    exists_of_isLawfulBelow_C hIL hk (hx.mono (X := (coatomC, k)) ⟨subset_univ _, le_rfl⟩)
  obtain ⟨A', H', G', hA', hH', hG', hc', hD⟩ :=
    exists_of_isLawfulBelow_D hIR hk (hx.mono (X := (coatomD, k)) ⟨subset_univ _, le_rfl⟩)
  obtain ⟨hHA, hAGH⟩ : H ≤ A ∧ min A G ≤ H := by simpa [Coupled] using hc
  have hGA' : G' ≤ A' := by simpa [Coupled] using hc'
  have kd₃ : cellKind I (multiOldCell I multHG d₃) = .ac := by
    rw [cellKind_multiOldCell, h₃]; decide
  have kd₄ : cellKind I (multiOldCell I multHG d₄) = .ad := by
    rw [cellKind_multiOldCell, h₄]; decide
  have ke₂ : cellKind I (multiOldCell I multHG e₂) = .h := by
    rw [cellKind_multiOldCell, h₂]; decide
  have ke₃ : cellKind I (multiOldCell I multHG e₃) = .g := by
    rw [cellKind_multiOldCell, h₃']; decide
  -- The values at the four cells carrying the parameters.
  have xd₃ : x (multiOldCell I multHG d₃) = A := by
    rw [hC _ (multiOldCell_mem_below (by
      rw [h₃]; exact ⟨(by decide : ({3} : Finset (Fin 5)) ⊆ coatomC), hk1⟩))]
    simp [kindLabel, kd₃, CellKind.val]
  have xd₄ : x (multiOldCell I multHG d₄) = A' := by
    rw [hD _ (multiOldCell_mem_below (by
      rw [h₄]; exact ⟨(by decide : ({4} : Finset (Fin 5)) ⊆ coatomD), hk1⟩))]
    simp [kindLabel, kd₄, CellKind.val]
  have xe₂ (h2 : 2 ≤ k) : x (multiOldCell I multHG e₂) = H ∧ x (multiOldCell I multHG e₂) = H' := by
    constructor
    · rw [hC _ (multiOldCell_mem_below (by
        rw [h₂]; exact ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomC), h2⟩))]
      simp [kindLabel, ke₂, CellKind.val]
    · rw [hD _ (multiOldCell_mem_below (by
        rw [h₂]; exact ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomD), h2⟩))]
      simp [kindLabel, ke₂, CellKind.val]
  have xe₃ (h3 : 3 ≤ k) : x (multiOldCell I multHG e₃) = G ∧ x (multiOldCell I multHG e₃) = G' := by
    constructor
    · rw [hC _ (multiOldCell_mem_below (by
        rw [h₃']; exact ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomC), h3⟩))]
      simp [kindLabel, ke₃, CellKind.val]
    · rw [hD _ (multiOldCell_mem_below (by
        rw [h₃']; exact ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomD), h3⟩))]
      simp [kindLabel, ke₃, CellKind.val]
  obtain ⟨fAD, fAC⟩ := eq_of_isLawfulBelow_one hk1 hx h₃ h₄
  refine ⟨A, A', if 2 ≤ k then H else ⊥, if 3 ≤ k then G else ⊥, hA, hA', ?_, ?_, ?_, ?_,
    fun z hz ↦ ?_⟩
  · split_ifs
    · exact hH
    · exact isSelfVisible_bot _
  · split_ifs
    · exact hG
    · exact isSelfVisible_bot _
  · simp only [Coupled, ite_true]
    split_ifs with h2 h3
    · exact ⟨hHA, hAGH⟩
    · exact ⟨hHA, by simp⟩
    · omega
    · simp
  · simp only [Coupled, Bool.false_eq_true, ite_false]
    split_ifs with h3
    · rw [(xe₃ h3).1.symm.trans (xe₃ h3).2]; exact hGA'
    · exact bot_le
  · have hgz : (schemeHG I).toCellScheme.grade z ≤ k := hz.2
    obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_cellKind z
    rcases cell_casesHG z with ⟨d, rfl⟩ | rfl | rfl | rfl | rfl | rfl
    · rcases mem_below_coatom_of_ne_multi hz (scope_multiOldCell_ne d) with hzC | hzD
      · rw [hC _ hzC]
        refine kindLabel_congr (fun _ ↦ rfl) (fun h ↦ absurd h (cellKind_ne_ad hzC))
          (fun h ↦ ?_) (fun h ↦ ?_) (fun _ ↦ rfl)
        · rw [ite_eq_left (by have := g3 h; omega)]
        · rw [ite_eq_left (by have := g4 h; omega)]
      · rw [hD _ hzD]
        refine kindLabel_congr (fun h ↦ absurd h (cellKind_ne_ac hzD)) (fun _ ↦ rfl)
          (fun h ↦ ?_) (fun h ↦ ?_) (fun _ ↦ rfl)
        · have h2 : 2 ≤ k := by have := g3 h; omega
          rw [ite_eq_left h2, ← (xe₂ h2).2, (xe₂ h2).1]
        · have h3 : 3 ≤ k := by have := g4 h; omega
          rw [ite_eq_left h3, ← (xe₃ h3).2, (xe₃ h3).1]
    · rw [fAD, xd₄, kindLabel_cellAD]
    · rw [fAC, xd₃, kindLabel_cellAC]
    · have h2 : 2 ≤ k := by rw [grade_cellH] at hgz; exact hgz
      rw [eq_of_isLawfulBelow_two h2 hx h₂, (xe₂ h2).1, kindLabel_cellH, ite_eq_left h2]
    · have h3 : 3 ≤ k := by rw [grade_cellG] at hgz; exact hgz
      rw [eq_of_isLawfulBelow_three h3 hx h₃', (xe₃ h3).1, kindLabel_cellG, ite_eq_left h3]
    · rw [grade_cellT] at hgz; omega


/-! ### The capped lifts below the grade `4` -/

omit hIL hIR in
/-- Two labellings by kinds agree capped at `c` at a cell when their parameters do at its kind. -/
private theorem min_kindLabel_congr {z : Fin (schemeHG I).card}
    {c AC AD Q AC' AD' H' G' Q' : Label.{u}}
    (hac : cellKind I z = .ac → min AC c = min AC' c)
    (had : cellKind I z = .ad → min AD c = min AD' c)
    (hh : cellKind I z = .h → min H c = min H' c) (hg : cellKind I z = .g → min G c = min G' c)
    (htop : cellKind I z = .top → min Q c = min Q' c) :
    min (kindLabel I AC AD H G Q z) c = min (kindLabel I AC' AD' H' G' Q' z) c := by
  cases hk : cellKind I z with
  | dead => simp only [kindLabel, hk, CellKind.val]
  | ac => simp only [kindLabel, hk, CellKind.val]; exact hac hk
  | ad => simp only [kindLabel, hk, CellKind.val]; exact had hk
  | h => simp only [kindLabel, hk, CellKind.val]; exact hh hk
  | g => simp only [kindLabel, hk, CellKind.val]; exact hg hk
  | top => simp only [kindLabel, hk, CellKind.val]; exact htop hk

omit hIL hIR in
/-- A lifted parameter of the form `liftedGH` is self-visible. -/
private theorem isSelfVisible_liftedGH {pX p : Prop} {xp xq c : Label.{u}} {k : ℕ}
    (hxp : IsSelfVisible k xp) (hxq : IsSelfVisible k xq) (hc : p → IsSelfVisible k c) :
    IsSelfVisible k (liftedGH pX p xp xq c) := by
  classical
  unfold liftedGH
  split_ifs with h1 h2
  · exact hxp
  · exact hxq
  · exact hc h2
  · exact isSelfVisible_bot k

omit hIL hIR in
/-- A lifted parameter of the form `liftedGH` with the same presence is the prescription. -/
private theorem liftedGH_of {p : Prop} {xp xq c : Label.{u}} (h : p) :
    liftedGH p p xp xq c = xp := by
  classical
  unfold liftedGH; rw [ite_eq_left h]

omit hIL hIR in
/-- A lifted parameter of the form `liftedGH` without presence is `⊥`. -/
private theorem liftedGH_of_not {p : Prop} {xp xq c : Label.{u}} (h : ¬ p) :
    liftedGH p p xp xq c = ⊥ := by
  classical
  unfold liftedGH; rw [ite_eq_right h, ite_eq_right h]

/-- **The capped lift from `(C, k)` to `(univ, k)`, `1 ≤ k ≤ 3`.**  Read the prescription as `TH`
parameters `A`, `H`, `G` and the ambient as parameters `A_C`, `A_D`, `H'`, `G'`; the lift keeps
`A`, `H` and `G` (`G` only when its cells are below the target, else `⊥`) and takes for `A_D` the
ambient below the cap and `⊤` above it (`liftParamsG`). -/
theorem cappedLift_C_of_le_three {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 3) :
    (schemeHG I).rows.CappedLift (X := (coatomC, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ := by
  classical
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨A, H, G, hA, hH, hG, hcp, hpx⟩ :=
    exists_of_isLawfulBelow_C hIL hk (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨AC, AD, H', G', hAC, hAD, hH', hG', hq1, hq2, hqx⟩ :=
    exists_of_isLawfulBelow_univ hIL hIR hk1 hk (Rows.isLawfulBelow_extendBot.mpr hq)
  have hp' (z : (schemeHG I).toCellScheme.below (coatomC, k)) :
      p z = kindLabel I A ⊥ H G ⊥ z := by rw [← hpx z z.2, Rows.extendBot_of_mem p z.2]
  have hq' (z : (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), k)) :
      q z = kindLabel I AC AD H' G' ⊥ z := by rw [← hqx z z.2, Rows.extendBot_of_mem q z.2]
  obtain ⟨d₃, d₄, e₂, e₃, h₃, h₄, h₂, h₃'⟩ := exists_paramCells hIL hIR
  -- The agreement under the cap at the cells carrying `A_C`, `H`, `G`.
  have agree {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ} {κ : CellKind}
      (hd : I.amalgam.toCellScheme.gradedIndex d = X) (hX : X ≤ (coatomC, k))
      (hκ : kindOld X = κ) :
      min (κ.val AC AD H' G' ⊥) c = min (κ.val A ⊥ H G ⊥) c := by
    have hm : multiOldCell I multHG d ∈ (schemeHG I).toCellScheme.below (coatomC, k) :=
      multiOldCell_mem_below (by rw [hd]; exact hX)
    have := hpq ⟨_, hm⟩
    rw [hq', hp'] at this
    simpa [kindLabel, hd, hκ] using this
  have ca : min AC c = min A c :=
    agree (κ := .ac) h₃ ⟨(by decide : ({3} : Finset (Fin 5)) ⊆ coatomC), hk1⟩ (by decide)
  have cg (h3 : 3 ≤ k) : min G' c = min G c :=
    agree (κ := .g) h₃' ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomC), h3⟩ (by decide)
  have ch (h2 : 2 ≤ k) : min H' c = min H c :=
    agree (κ := .h) h₂ ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomC), h2⟩ (by decide)
  have hGA : G' ≤ AD := by simpa [Coupled] using hq2
  obtain ⟨hHA, hAGH⟩ : H ≤ A ∧ min A G ≤ H := by simpa [Coupled] using hcp
  -- The lifted parameters `A_D` and `G`.
  obtain ⟨l1, l2, -⟩ := liftParamsG (aX := False) (g := 3 ≤ k) (gX := 3 ≤ k) id
    (Ap := ⊤) (Gp := G) (Aq := AD) (Gq := G') (c := c) le_top hGA (fun h ↦ h.elim) cg
  set AD' := liftedTop False ⊤ AD c with hAD'
  set G'' := liftedGH (3 ≤ k) (3 ≤ k) G G' c with hG''
  have sAD' : IsSelfVisible 1 AD' := by
    rw [hAD']; unfold liftedTop; split_ifs
    all_goals first | exact hAD | exact isSelfVisible_top 1
  have sG'' : IsSelfVisible 3 G'' := isSelfVisible_liftedGH hG hG' fun h ↦ hc.mono h
  have cTH : Coupled true A H G'' := by
    simp only [Coupled, ite_true]
    refine ⟨hHA, ?_⟩
    by_cases h3 : 3 ≤ k
    · rw [hG'', liftedGH_of h3]; exact hAGH
    · rw [hG'', liftedGH_of_not h3]; simp
  have cTG : Coupled false AD' H G'' := by simpa [Coupled] using l1
  -- The lift.
  refine ⟨fun z ↦ kindLabel I A AD' H G'' ⊥ z,
    (isLawful_kindLabel hIL hIR hA sAD' hH sG'' cTH cTG).isLawfulBelow _, fun z ↦ ?_,
    fun z ↦ ?_⟩
  · have hgz : (schemeHG I).toCellScheme.grade z.1 ≤ k := z.2.2
    obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_cellKind z.1
    rw [hq']
    refine min_kindLabel_congr (fun _ ↦ ca.symm) (fun _ ↦ l2) (fun h ↦ ?_) (fun h ↦ ?_)
      (fun _ ↦ rfl)
    · exact (ch (by have := g3 h; omega)).symm
    · have h3 : 3 ≤ k := by have := g4 h; omega
      rw [hG'', liftedGH_of h3]; exact (cg h3).symm
  · rw [hp']
    have hz := z.2
    refine kindLabel_congr (fun _ ↦ rfl) (fun h ↦ absurd h (cellKind_ne_ad hz)) (fun _ ↦ rfl)
      (fun h ↦ ?_) (fun _ ↦ rfl)
    have hzk : (schemeHG I).toCellScheme.grade z.1 ≤ k := hz.2
    have h3 : 3 ≤ k := by have := (grade_of_cellKind z.1).2.2.2.1 h; omega
    rw [hG'', liftedGH_of h3]


/-- **The capped lift from `(D, k)` to `(univ, k)`, `1 ≤ k ≤ 3`.**  Read the prescription as `TG`
parameters `A`, `H`, `G` and the ambient as parameters `A_C`, `A_D`, `H'`, `G'`; the lift keeps
`A_D = A`, `H` and `G` (each only when its cells are below the target, else `⊥`) and takes for
`A_C` the ambient below the cap, and above it `H` when `k = 3` and `H < G`, and `⊤` otherwise, so
always `⊤` at `k ≤ 2` (`liftParamsH`). -/
theorem cappedLift_D_of_le_three {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 3) :
    (schemeHG I).rows.CappedLift (X := (coatomD, k)) (Y := ((univ : Finset (Fin 5)), k))
      ⟨subset_univ _, le_rfl⟩ := by
  classical
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  obtain ⟨A, H, G, hA, hH, hG, hcp, hpx⟩ :=
    exists_of_isLawfulBelow_D hIR hk (Rows.isLawfulBelow_extendBot.mpr hp)
  obtain ⟨AC, AD, H', G', hAC, hAD, hH', hG', hq1, hq2, hqx⟩ :=
    exists_of_isLawfulBelow_univ hIL hIR hk1 hk (Rows.isLawfulBelow_extendBot.mpr hq)
  have hp' (z : (schemeHG I).toCellScheme.below (coatomD, k)) :
      p z = kindLabel I ⊥ A H G ⊥ z := by rw [← hpx z z.2, Rows.extendBot_of_mem p z.2]
  have hq' (z : (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), k)) :
      q z = kindLabel I AC AD H' G' ⊥ z := by rw [← hqx z z.2, Rows.extendBot_of_mem q z.2]
  obtain ⟨d₃, d₄, e₂, e₃, h₃, h₄, h₂, h₃'⟩ := exists_paramCells hIL hIR
  -- The agreement under the cap at the cells carrying `A_D`, `H`, `G`.
  have agree {d : Fin I.amalgam.card} {X : Finset (Fin 5) × ℕ} {κ : CellKind}
      (hd : I.amalgam.toCellScheme.gradedIndex d = X) (hX : X ≤ (coatomD, k))
      (hκ : kindOld X = κ) :
      min (κ.val AC AD H' G' ⊥) c = min (κ.val ⊥ A H G ⊥) c := by
    have hm : multiOldCell I multHG d ∈ (schemeHG I).toCellScheme.below (coatomD, k) :=
      multiOldCell_mem_below (by rw [hd]; exact hX)
    have := hpq ⟨_, hm⟩
    rw [hq', hp'] at this
    simpa [kindLabel, hd, hκ] using this
  have ca : min AD c = min A c :=
    agree (κ := .ad) h₄ ⟨(by decide : ({4} : Finset (Fin 5)) ⊆ coatomD), hk1⟩ (by decide)
  have cg (h3 : 3 ≤ k) : min G' c = min G c :=
    agree (κ := .g) h₃' ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomD), h3⟩ (by decide)
  have ch (h2 : 2 ≤ k) : min H' c = min H c :=
    agree (κ := .h) h₂ ⟨(by decide : ({0, 1, 2} : Finset (Fin 5)) ⊆ coatomD), h2⟩ (by decide)
  obtain ⟨hHA', hAGH'⟩ : H' ≤ AC ∧ min AC G' ≤ H' := by simpa [Coupled] using hq1
  have hGA : G ≤ A := by simpa [Coupled] using hcp
  -- The lifted parameters `A_C`, `H` and `G`.
  obtain ⟨l1, l2, l3, l4, l5⟩ := liftParamsH (a := True) (aX := False) (h := 2 ≤ k)
    (hX := 2 ≤ k) (g := 3 ≤ k) (gX := 3 ≤ k) (fun h ↦ h.elim) id id (fun h ↦ by omega)
    (fun h ↦ by omega) (Ap := H) (Hp := H) (Gp := G) (Aq := AC) (Hq := H') (Gq := G') (c := c)
    le_rfl (min_le_left _ _) hHA' hAGH' (fun h ↦ h.elim) ch cg
  set H'' := liftedGH (2 ≤ k) (2 ≤ k) H H' c with hH''
  set G'' := liftedGH (3 ≤ k) (3 ≤ k) G G' c with hG''
  set AC' := liftedAH False True (2 ≤ k) (3 ≤ k) H AC H G H'' c with hAC'
  have sH'' : IsSelfVisible 2 H'' := isSelfVisible_liftedGH hH hH' fun h ↦ hc.mono h
  have sG'' : IsSelfVisible 3 G'' := isSelfVisible_liftedGH hG hG' fun h ↦ hc.mono h
  have sAC' : IsSelfVisible 1 AC' := by
    rw [hAC']; unfold liftedAH; split_ifs
    all_goals first
      | exact hAC
      | exact hH.mono (by omega)
      | exact isSelfVisible_top 1
  have cTH : Coupled true AC' H'' G'' := by
    simp only [Coupled, ite_true]; exact ⟨l1, l2⟩
  have cTG : Coupled false A H'' G'' := by
    simp only [Coupled, Bool.false_eq_true, ite_false]
    by_cases h3 : 3 ≤ k
    · rw [hG'', liftedGH_of h3]; exact hGA
    · rw [hG'', liftedGH_of_not h3]; exact bot_le
  -- The lift.
  refine ⟨fun z ↦ kindLabel I AC' A H'' G'' ⊥ z,
    (isLawful_kindLabel hIL hIR sAC' hA sH'' sG'' cTH cTG).isLawfulBelow _, fun z ↦ ?_,
    fun z ↦ ?_⟩
  · have hgz : (schemeHG I).toCellScheme.grade z.1 ≤ k := z.2.2
    obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_cellKind z.1
    rw [hq']
    refine min_kindLabel_congr (fun _ ↦ l3 trivial) (fun _ ↦ ca.symm) (fun h ↦ ?_) (fun h ↦ ?_)
      (fun _ ↦ rfl)
    · exact l4 (by have := g3 h; omega)
    · exact l5 (by have := g4 h; omega)
  · rw [hp']
    have hz := z.2
    have hzk : (schemeHG I).toCellScheme.grade z.1 ≤ k := hz.2
    obtain ⟨g1, g2, g3, g4, g5⟩ := grade_of_cellKind z.1
    refine kindLabel_congr (fun h ↦ absurd h (cellKind_ne_ac hz)) (fun _ ↦ rfl) (fun h ↦ ?_)
      (fun h ↦ ?_) (fun _ ↦ rfl)
    · have h2 : 2 ≤ k := by have := g3 h; omega
      rw [hH'', liftedGH_of h2]
    · have h3 : 3 ≤ k := by have := g4 h; omega
      rw [hG'', liftedGH_of h3]


/-! ### The capped lifts at the grade `4` -/

omit hIL hIR in
/-- The labelling of `Ω` alone: `Ω` at the cells of grade `4`, `⊥` elsewhere. -/
private theorem kindLabel_omega (Ω : Label.{u}) (z : Fin (schemeHG I).card) :
    kindLabel I ⊥ ⊥ ⊥ ⊥ Ω z = if (schemeHG I).toCellScheme.grade z = 4 then Ω else ⊥ := by
  obtain ⟨-, -, -, -, g5⟩ := grade_of_cellKind z
  by_cases h : (schemeHG I).toCellScheme.grade z = 4
  · rw [ite_eq_left h]; simp [kindLabel, g5.mpr h, CellKind.val]
  · rw [ite_eq_right h]
    cases hk : cellKind I z with
    | top => exact absurd (g5.mp hk) h
    | _ => simp [kindLabel, hk, CellKind.val]

/-- The row of an old cell of grade `4` is `⊥` exactly below the grade `4`. -/
private theorem row_multiOldCell_eq_bot_iff {a : Fin I.amalgam.card}
    (ha : I.amalgam.toCellScheme.grade a = 4)
    (z : (schemeHG I).toCellScheme.below
      ((schemeHG I).toCellScheme.gradedIndex (multiOldCell I multHG a))) :
    (schemeHG I).rows.row (multiOldCell I multHG a) z = ⊥ ↔
      (schemeHG I).toCellScheme.grade z.1 ≠ 4 := by
  obtain ⟨e, he, hea⟩ := exists_multiOldCell_of_mem_below z.2
  have hrow : (schemeHG I).rows.row (multiOldCell I multHG a) z =
      I.amalgam.rows.row a ⟨e, hea⟩ := by
    rw [← row_multiOldCell a e (he ▸ z.2) hea]
    exact (schemeHG I).rows.row_congr rfl he
  rw [hrow, (hasBottomApexes_HG hIL hIR).row_apex ha, he, grade_multiOldCell]

/-- **The capped lift from a coatom at the grade `4` to `(univ, 4)`**, from the capped lift at the
grade `3`.  If the prescription is `⊥` at the apex, lift its restriction below the grade `3` (with
the ambient, or with `⊥` when the ambient is not `⊥` at the grade `4`, where the cap is then `⊥`)
and extend by `⊥`; otherwise the prescription is `⊥` below its apex, and the lift is the labelling
of its apex label alone. -/
theorem cappedLift_four_HG {B : Finset (Fin 5)} (hB : B = coatomC ∨ B = coatomD)
    (h3 : (schemeHG I).rows.CappedLift (X := (B, 3)) (Y := ((univ : Finset (Fin 5)), 3))
      ⟨subset_univ _, le_rfl⟩) :
    (schemeHG I).rows.CappedLift (X := (B, 4)) (Y := ((univ : Finset (Fin 5)), 4))
      ⟨subset_univ _, le_rfl⟩ := by
  have hI := hasBottomApexes_HG hIL hIR
  -- Step 1: the apex `a` at `(B, 4)` is the only cell of grade `4` below `(B, 4)`.
  have hBne : B ≠ univ := by rcases hB with rfl | rfl <;> decide
  have hBcard : #B = 4 := by rcases hB with rfl | rfl <;> decide
  obtain ⟨a, ha⟩ : ∃ a : Fin I.amalgam.card, I.amalgam.toCellScheme.gradedIndex a = (B, 4) := by
    refine I.exists_gradedIndex_eq _ ⟨?_, by omega, by rw [hBcard]⟩ hBne
    rcases hB with rfl | rfl
    · exact coatomC_mem_faces I
    · exact coatomD_mem_faces I
  have hag : I.amalgam.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hag' : (schemeHG I).toCellScheme.grade (multiOldCell I multHG a) = 4 := by
    rw [grade_multiOldCell, hag]
  have haB : multiOldCell I multHG a ∈ (schemeHG I).toCellScheme.below (B, 4) :=
    multiOldCell_mem_below ha.le
  have huniq : ∀ z ∈ (schemeHG I).toCellScheme.below (B, 4),
      (schemeHG I).toCellScheme.grade z = 4 → z = multiOldCell I multHG a := by
    intro z hz hz4
    obtain ⟨d, rfl⟩ := exists_eq_multiOldCell (r := rowsHG I) (z := z) fun h ↦
      hBne (univ_subset_iff.mp (h ▸ hz.1))
    have hs : I.amalgam.toCellScheme.scope d ⊆ B := by
      rw [← scope_multiOldCell (r := rowsHG I)]; exact hz.1
    have hg : I.amalgam.toCellScheme.grade d = 4 := by
      rw [← grade_multiOldCell (r := rowsHG I)]; exact hz4
    have hcard : 4 ≤ #(I.amalgam.toCellScheme.scope d) :=
      hg ▸ I.amalgam.isWellFormed.isWellFormed.grade_le_card d
    refine congrArg (multiOldCell I multHG) (hI.eq_of_grade_four hg hag ?_)
    rw [show I.amalgam.toCellScheme.scope a = B from congrArg Prod.fst ha]
    exact eq_of_subset_of_card_le hs (by rw [hBcard]; exact hcard)
  have hbelow : ∀ z ∈ (schemeHG I).toCellScheme.below (B, 4),
      z ∈ (schemeHG I).toCellScheme.below
        ((schemeHG I).toCellScheme.gradedIndex (multiOldCell I multHG a)) := fun z hz ↦ by
    rw [gradedIndex_multiOldCell, ha]; exact hz
  -- Step 2: extend the prescription `p` and the ambient `q` by `⊥` to all cells (`p'`, `q'`); it
  -- is enough to lift `p'` against `q'`.  The ambient is constant at the grade `4`.
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  let p' := Rows.extendBot (B, 4) p
  let q' := Rows.extendBot ((univ : Finset (Fin 5)), 4) q
  have hpl : (schemeHG I).rows.IsLawfulBelow (B, 4) (fun z ↦ p' z) :=
    Rows.isLawfulBelow_extendBot.mpr hp
  have hql : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) (fun z ↦ q' z) :=
    Rows.isLawfulBelow_extendBot.mpr hq
  have hp'z : ∀ z (hz : z ∈ (schemeHG I).toCellScheme.below (B, 4)), p' z = p ⟨z, hz⟩ :=
    fun _ hz ↦ Rows.extendBot_of_mem p hz
  have hq'z : ∀ z, q' z = q ⟨z, mem_below_univ_four_multi z⟩ :=
    fun z ↦ Rows.extendBot_of_mem q (mem_below_univ_four_multi z)
  have hpq' : ∀ z ∈ (schemeHG I).toCellScheme.below (B, 4), min (q' z) c = min (p' z) c :=
    fun z hz ↦ by
      rw [hp'z z hz, hq'z z]
      exact hpq ⟨z, hz⟩
  have hqa : q' (multiOldCell I multHG a) = q' (cellT I) := eq_of_isLawfulBelow_four hql hag'
  suffices h : ∃ x : Fin (schemeHG I).card → Label.{u},
      (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) (fun z ↦ x z) ∧
      (∀ z, min (x z) c = min (q' z) c) ∧
      ∀ z ∈ (schemeHG I).toCellScheme.below (B, 4), x z = p' z by
    obtain ⟨x, hx, hxq, hxp⟩ := h
    refine ⟨fun z ↦ x z, hx, fun z ↦ ?_, fun z ↦ ?_⟩
    · rw [hxq, hq'z z.1]
    · -- The restriction of `x` below `(univ, 4)`, at `z`.
      change x z.1 = p z
      rw [hxp z.1 z.2, hp'z z.1 z.2]
  by_cases hω : p' (multiOldCell I multHG a) = ⊥
  · -- Step 3: the prescription is `⊥` at the apex.  If the ambient is not `⊥` at the grade `4`,
    -- the cap is `⊥`; replace the ambient by `⊥` (`q₃`), lift below the grade `3` by `h3`, and
    -- extend by `⊥` above the grade `3`.
    have hc0 : q' (cellT I) ≠ ⊥ → c = ⊥ := fun h ↦ by
      have := hpq' _ haB
      rw [hω, min_bot_left, hqa] at this
      exact (min_eq_bot.mp this).resolve_left h
    let q₃ : Fin (schemeHG I).card → Label.{u} := fun z ↦
      if q' (cellT I) = ⊥ then q' z else ⊥
    have hq₃ : (schemeHG I).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
        (fun z ↦ q₃ z) := by
      by_cases h : q' (cellT I) = ⊥
      · have he : (fun z : (schemeHG I).toCellScheme.below
              ((univ : Finset (Fin 5)), 3) ↦ q₃ z) =
            fun z : (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), 3) ↦ q' z :=
          funext fun z ↦ ite_eq_left h
        rw [he]
        exact hql.mono (X := ((univ : Finset (Fin 5)), 3)) ⟨subset_rfl, by omega⟩
      · have he : (fun z : (schemeHG I).toCellScheme.below
              ((univ : Finset (Fin 5)), 3) ↦ q₃ z) = fun _ ↦ ⊥ :=
          funext fun z ↦ ite_eq_right h
        rw [he]
        exact Rows.isLawfulBelow_const_bot _
    have hq₃c : ∀ z, min (q₃ z) c = min (q' z) c := fun z ↦ by
      by_cases h : q' (cellT I) = ⊥
      · exact congrArg (min · c) (ite_eq_left h)
      · rw [hc0 h, min_bot_right, min_bot_right]
    obtain ⟨x₃, hx₃, hx₃q, hx₃p⟩ := (Rows.cappedLift_iff_forall_exists _).mp h3 c
      (hc.mono (by omega)) (fun z ↦ p' z) (fun z ↦ q₃ z)
      (hpl.mono (X := (B, 3)) ⟨subset_rfl, by omega⟩) hq₃
      (fun z ↦ (hq₃c z.1).trans (hpq' z.1 ⟨z.2.1, z.2.2.trans (by omega)⟩))
    refine ⟨fun z ↦ if (schemeHG I).toCellScheme.grade z ≤ 3 then
      Rows.extendBot ((univ : Finset (Fin 5)), 3) x₃ z else ⊥,
      Rows.isLawfulBelow_extendAbove (Rows.isLawfulBelow_extendBot.mpr hx₃), fun z ↦ ?_,
      fun z hz ↦ ?_⟩
    · dsimp only
      by_cases hz3 : (schemeHG I).toCellScheme.grade z ≤ 3
      · have hzm : z ∈ (schemeHG I).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
          ⟨subset_univ _, hz3⟩
        rw [ite_eq_left hz3, Rows.extendBot_of_mem x₃ hzm, hx₃q ⟨z, hzm⟩]
        exact hq₃c z
      · have hz4 : (schemeHG I).toCellScheme.grade z = 4 := by
          have : (schemeHG I).toCellScheme.grade z ≤ 4 := grade_le_four_multi z
          omega
        rw [ite_eq_right hz3, eq_of_isLawfulBelow_four hql hz4]
        by_cases h : q' (cellT I) = ⊥
        · rw [h]
        · rw [hc0 h, min_bot_right, min_bot_right]
    · dsimp only
      by_cases hz3 : (schemeHG I).toCellScheme.grade z ≤ 3
      · rw [ite_eq_left hz3, Rows.extendBot_of_mem x₃ ⟨subset_univ _, hz3⟩]
        exact hx₃p ⟨z, ⟨hz.1, hz3⟩⟩
      · have hz4 : (schemeHG I).toCellScheme.grade z = 4 := by
          have : (schemeHG I).toCellScheme.grade z ≤ 4 := grade_le_four_multi z
          omega
        rw [ite_eq_right hz3, huniq z hz hz4, hω]
  · -- Step 4: the prescription is not `⊥` at the apex, hence `⊥` below the grade `4` (the row of
    -- the apex); the lift is the labelling of its apex label `Ω` alone.  If `c ≠ ⊥`, the ambient
    -- is not `⊥` at the grade `4`, hence `⊥` below it, and agrees with `Ω` capped at `c` there.
    obtain ⟨ho, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hpl
    have hωsv : IsSelfVisible 4 (p' (multiOldCell I multHG a)) := hag' ▸ ho _ haB
    refine ⟨kindLabel I ⊥ ⊥ ⊥ ⊥ (p' (multiOldCell I multHG a)),
      (isLawful_kindLabel_omega hIL hIR hωsv).isLawfulBelow _, fun z ↦ ?_, fun z hz ↦ ?_⟩
    · by_cases hc0 : c = ⊥
      · rw [hc0, min_bot_right, min_bot_right]
      have hΩq : q' (cellT I) ≠ ⊥ := by
        intro h
        have := hpq' _ haB
        rw [hqa, h, min_bot_left] at this
        exact (min_eq_bot.mp this.symm).elim hω hc0
      rw [kindLabel_omega]
      split_ifs with hz4
      · rw [eq_of_isLawfulBelow_four hql hz4, ← hqa]
        exact (hpq' _ haB).symm
      · rw [eq_bot_of_isLawfulBelow_four hql hΩq hz4]
    · rw [kindLabel_omega]
      split_ifs with hz4
      · rw [huniq z hz hz4]
      · have := (hl _ haB).eq_bot (d := ⟨z, hbelow z hz⟩)
          ((row_multiOldCell_eq_bot_iff hIL hIR hag ⟨z, hbelow z hz⟩).mpr hz4)
        exact ((min_eq_bot.mp this).resolve_right hω).symm


/-! ### The completion -/

omit hIL hIR in
/-- A labelling by kinds with values below `ω ^ 2` is coded. -/
private theorem kindLabel_lt {AC AD Q : Label.{u}} {o : Label.{u}} (hb : (⊥ : Label.{u}) < o)
    (hAC : AC < o) (hAD : AD < o) (hH : H < o) (hG : G < o) (hQ : Q < o)
    (z : Fin (schemeHG I).card) : kindLabel I AC AD H G Q z < o := by
  cases hk : cellKind I z with
  | dead => simp only [kindLabel, hk, CellKind.val]; exact hb
  | ac => simp only [kindLabel, hk, CellKind.val]; exact hAC
  | ad => simp only [kindLabel, hk, CellKind.val]; exact hAD
  | h => simp only [kindLabel, hk, CellKind.val]; exact hH
  | g => simp only [kindLabel, hk, CellKind.val]; exact hG
  | top => simp only [kindLabel, hk, CellKind.val]; exact hQ

/-- **The multi-layer step of a seed whose coatom types are `TH` and `TG`**, with two new cells at
`(univ, 1)`, one for each forced separation, and the rows `rowsHG`. -/
theorem multiLayerStep_HG : I.MultiLayerStep multHG (rowsHG I) where
  pos k := by fin_cases k <;> decide
  row_lt k i z _ := by
    have hb : (⊥ : Label.{u}) < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u}) :=
      WithBot.bot_lt_coe _
    have g (a b : ℕ) := gridPoint_lt_omega0_sq.{u} a b
    obtain ⟨i, hi⟩ := i
    fin_cases k
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by simp [multHG] at hi; omega
      · exact kindLabel_lt hb (g 1 0) (g 2 1) hb hb hb z
      · exact kindLabel_lt hb (g 2 1) (g 1 0) hb hb hb z
    · exact kindLabel_lt hb (g 2 1) (g 1 0) (g 2 1) hb hb z
    · exact kindLabel_lt hb (g 2 0) (g 3 1) (g 2 0) (g 3 1) hb z
    · exact kindLabel_lt hb hb hb hb hb (g 4 1) z
  isLawfulBelow_row k i := by
    obtain ⟨i, hi⟩ := i
    fin_cases k
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by simp [multHG] at hi; omega
      · exact (isLawful_kindLabel hIL hIR isSelfVisible_v1 (isSelfVisible_v2.mono (by omega))
          (isSelfVisible_bot 2) (isSelfVisible_bot 3) (by simp [Coupled])
          (by simp [Coupled])).isLawfulBelow _
      · exact (isLawful_kindLabel hIL hIR (isSelfVisible_v2.mono (by omega)) isSelfVisible_v1
          (isSelfVisible_bot 2) (isSelfVisible_bot 3) (by simp [Coupled])
          (by simp [Coupled])).isLawfulBelow _
    · exact (isLawful_kindLabel hIL hIR (isSelfVisible_v2.mono (by omega)) isSelfVisible_v1
        isSelfVisible_v2 (isSelfVisible_bot 3) (by simp [Coupled])
        (by simp [Coupled])).isLawfulBelow _
    · exact (isLawful_kindLabel hIL hIR (isSelfVisible_w2.mono (by omega))
        (isSelfVisible_w3.mono (by omega)) isSelfVisible_w2 isSelfVisible_w3
        (by simp only [Coupled, ite_true, min_eq_left w2_le_w3]; exact ⟨le_rfl, le_rfl⟩)
        (by simp [Coupled])).isLawfulBelow _
    · exact (isLawful_kindLabel_omega hIL hIR (isSelfVisible_gridPoint 4 1)).isLawfulBelow _
  cappedLift_left k hk1 hk4 := by
    rcases Nat.lt_or_ge k 4 with hk | hk
    · exact cappedLift_C_of_le_three hIL hIR hk1 (by omega)
    · obtain rfl : k = 4 := by omega
      exact cappedLift_four_HG hIL hIR (.inl rfl) (cappedLift_C_of_le_three hIL hIR (by omega)
        le_rfl)
  cappedLift_right k hk1 hk4 := by
    rcases Nat.lt_or_ge k 4 with hk | hk
    · exact cappedLift_D_of_le_three hIL hIR hk1 (by omega)
    · obtain rfl : k = 4 := by omega
      exact cappedLift_four_HG hIL hIR (.inr rfl) (cappedLift_D_of_le_three hIL hIR (by omega)
        le_rfl)
  exists_isLawful := ⟨kindLabel I ⊥ ⊥ ⊥ ⊥ ⊤,
    isLawful_kindLabel_omega hIL hIR (isSelfVisible_top 4), fun d ↦ by
      rw [kindLabel_omega, grade_multiOldCell, (hasBottomApexes_HG hIL hIR).label_eq d]⟩

/-- **A seed whose coatom types are `TH` and `TG` has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_of : Nonempty (CompletionBelowFullGrade I) :=
  (multiLayerStep_HG hIL hIR).nonempty_completionBelowFullGrade

end VaughtConjecture.CrossedCouplingCounterexample

namespace VaughtConjecture.CrossedCouplingCounterexample

open Finset Label OrderedLayer

variable (α : Ordinal.{u})

/-- **The completion below the full grade of `seedHG`**: the multi-layer scheme with two new cells
at `(univ, 1)`, one for each forced separation. -/
noncomputable def completionHG : CompletionBelowFullGrade (seedHG α) :=
  (multiLayerStep_HG (I := seedHG α) rfl rfl).completion

/-- **`seedHG` has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_seedHG : Nonempty (CompletionBelowFullGrade (seedHG α)) :=
  ⟨completionHG α⟩

/-- **The coatom extension of `TH` and `TG` with apex**, at every stage: the completion of
`seedHG` with the apex added, through its lawful labelling `⊤` at the cells of grade `4` and `⊥`
elsewhere, whose labels lie at every stage. -/
theorem exists_coatomExtension_seedHG :
    ∃ t : StageType.{u} α 5, t.IsLegal ∧
      StageType.restrictFace Fin.castSuccEmb t = some (TH α) ∧
      StageType.restrictFace (extendByLast Fin.castSuccEmb) t = some (TG α) ∧
      ∃ d, t.toCellScheme.gradedIndex d = (univ, 5) ∧ ∀ e, t.label e ≤ t.label d := by
  have hl := isLawful_kindLabel_omega (I := seedHG α) rfl rfl (isSelfVisible_top 4)
  have hα (z : Fin (schemeHG (seedHG α)).card) :
      AtStage α (kindLabel (seedHG α) ⊥ ⊥ ⊥ ⊥ ⊤ z) := by
    rw [kindLabel_omega]
    split_ifs
    · exact atStage_top
    · exact atStage_bot
  refine (completionHG α).exists_coatomExtension_of_label (q := kindLabel (seedHG α) ⊥ ⊥ ⊥ ⊥ ⊤)
    hl (fun z ↦ hα z) (fun d ↦ ?_)
  · -- The old cells of the completion are the old cells of the multi-layer scheme.
    change kindLabel (seedHG α) ⊥ ⊥ ⊥ ⊥ ⊤ (multiOldCell (seedHG α) multHG d) = _
    rw [kindLabel_omega, grade_multiOldCell,
      (hasBottomApexes_HG (I := seedHG α) rfl rfl).label_eq d]

/-- **The ordered-layer step is strictly stronger than the completion**: `seedHG` has a completion
below the full grade but no ordered-layer step. -/
theorem not_forall_hasOrderedLayerStep_of_nonempty :
    ¬ ∀ I : Seed.{u} α 3, Nonempty (CompletionBelowFullGrade I) → I.HasOrderedLayerStep :=
  fun h ↦ not_hasOrderedLayerStep_seedHG (h (seedHG α) (nonempty_completionBelowFullGrade_seedHG α))

end VaughtConjecture.CrossedCouplingCounterexample
