/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerStep
import VaughtConjecture.Label.StepWitness

/-!
# The top grade of the ordered-layer step

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade at `m = 3`: the
grade `4` of the ordered-layer step, for the seeds whose coatom types are the apex added to `⊥`
labels); semantic contract, items 2–4.

Let `I` be a seed on five points.  It has **bottom apexes** (`Seed.HasBottomApexes`) when its
amalgam carries `⊤` at the cells of grade `4` and `⊥` elsewhere, the row of every cell of grade
`4` is `⊥` exactly at the cells of grade below `4`, and two cells of grade `4` with one scope are
equal.  This holds when both coatom types are the apex added to a type with every label `⊥`
(`Seed.hasBottomApexes_of_addApex`): the types `T4`, `T5` and `TL` of the compiled special cases
are of that form, so the seeds `seed4`, `seed5` and `seedL` have bottom apexes.

**The top grade is automatic** (`Seed.OrderedLayerStepBelowTop.orderedLayerStep`).  For a seed with
bottom apexes and layer rows whose row at `(univ, 4)` is the top row (`OrderedLayer.topRow`: the
cells of grade `4` at `ω + 4`, every other cell at `⊥`), the ordered-layer step follows from its
fields at the grades `k ≤ 3` (`Seed.OrderedLayerStepBelowTop`):

* the top row is coded and consistent: it is the labelling of `ω + 4` at the cells of grade `4`
  alone, lawful through the top shifter, since every row of a cell of grade `4` is `⊥` exactly
  below the grade `4` (`isLawfulBelow_omegaLabel`);
* the capped lift from a coatom at the grade `4` into `(univ, 4)` comes from the lift at the grade
  `3` (`cappedLift_four`): a lawful labelling below `(univ, 4)` is constant on the cells of grade
  `4` (`eq_newCell_four`) and, if not `⊥` there, `⊥` below the grade `4`
  (`eq_bot_of_newCell_four`); if the prescription is `⊥` at its apex, lift its restriction below the
  grade `3` and extend by `⊥`; otherwise it is `⊥` below its apex, and the lift is the labelling of
  its apex label alone;
* the lawful extension of the glued labelling is the labelling of `⊤` at the cells of grade `4`
  alone.

So for the seeds with bottom apexes the exact remaining content of the ordered-layer step is
`Seed.OrderedLayerStepBelowTop`, at the grades `1`, `2` and `3`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

/-! ### Seeds with bottom apexes -/

namespace Seed

variable {α : Ordinal.{u}}

/-- A seed on five points **has bottom apexes**: its amalgam carries `⊤` at the cells of grade `4`
and `⊥` elsewhere, the row of a cell of grade `4` is `⊥` exactly at the cells of grade below `4`,
and two cells of grade `4` with one scope are equal. -/
structure HasBottomApexes (I : Seed.{u} α 3) : Prop where
  /-- The glued labels: `⊤` at the cells of grade `4`, `⊥` elsewhere. -/
  label_eq (d : Fin I.amalgam.card) :
    I.amalgam.label d = if I.amalgam.toCellScheme.grade d = 4 then ⊤ else ⊥
  /-- The row of a cell of grade `4` is `⊥` exactly at the cells of grade below `4`. -/
  row_apex {s : Fin I.amalgam.card} (hs : I.amalgam.toCellScheme.grade s = 4)
    (i : I.amalgam.toCellScheme.below (I.amalgam.toCellScheme.gradedIndex s)) :
    I.amalgam.rows.row s i = ⊥ ↔ I.amalgam.toCellScheme.grade i ≠ 4
  /-- Two cells of grade `4` with one scope are equal. -/
  eq_of_grade_four {z z' : Fin I.amalgam.card} (hz : I.amalgam.toCellScheme.grade z = 4)
    (hz' : I.amalgam.toCellScheme.grade z' = 4)
    (h : I.amalgam.toCellScheme.scope z = I.amalgam.toCellScheme.scope z') : z = z'

/-- **A seed whose two coatom types are the apex added to `⊥` labels has bottom apexes.** -/
theorem hasBottomApexes_of_addApex {I : Seed.{u} α 3} {tL tR : StageType.{u} α 4}
    (hL : tL.IsLegalBelowFullGrade) (hR : tR.IsLegalBelowFullGrade)
    (hbL : ∀ d, tL.label d = ⊥) (hbR : ∀ d, tR.label d = ⊥)
    (hIL : I.left = tL.addApex hL (by omega)) (hIR : I.right = tR.addApex hR (by omega)) :
    I.HasBottomApexes where
  label_eq d := by
    rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem d)
      (I.scope_ne_univ d) with h | h
    · exact StageType.label_of_restrictFace (hIL ▸ I.restrictFace_left)
        (fun a l ↦ l = if a = 4 then ⊤ else ⊥) (StageType.label_addApex hL (by omega) hbL)
        ((coe_subset.mpr (Coatom.univ_map_left ▸ h)).trans (coe_map_subset_range _ _))
    · exact StageType.label_of_restrictFace (hIR ▸ I.restrictFace_right)
        (fun a l ↦ l = if a = 4 then ⊤ else ⊥) (StageType.label_addApex hR (by omega) hbR)
        ((coe_subset.mpr (Coatom.univ_map_right ▸ h)).trans (coe_map_subset_range _ _))
  row_apex {s} hs i := by
    rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem s)
      (I.scope_ne_univ s) with h | h
    · exact StageType.row_of_restrictFace (hIL ▸ I.restrictFace_left)
        (fun a b r ↦ a = 4 → (r = ⊥ ↔ b ≠ 4))
        (fun s i hs ↦ StageType.row_addApex hL (by omega) hbL s hs i)
        ((coe_subset.mpr (Coatom.univ_map_left ▸ h)).trans (coe_map_subset_range _ _)) i hs
    · exact StageType.row_of_restrictFace (hIR ▸ I.restrictFace_right)
        (fun a b r ↦ a = 4 → (r = ⊥ ↔ b ≠ 4))
        (fun s i hs ↦ StageType.row_addApex hR (by omega) hbR s hs i)
        ((coe_subset.mpr (Coatom.univ_map_right ▸ h)).trans (coe_map_subset_range _ _)) i hs
  eq_of_grade_four {z z'} hz hz' h := by
    have hgi : I.amalgam.toCellScheme.gradedIndex z = I.amalgam.toCellScheme.gradedIndex z' :=
      Prod.ext h (hz.trans hz'.symm)
    rcases I.subset_or_subset _ (I.amalgam.isWellFormed.isWellFormed.scope_mem z)
      (I.scope_ne_univ z) with hC | hD
    · exact StageType.eq_of_gradedIndex_eq_of_restrictFace_of_grade
        (hIL ▸ I.restrictFace_left)
        (fun i i' hii' hi ↦ (StageType.eq_of_grade_addApex hL _ hi).trans
          (StageType.eq_of_grade_addApex hL _ ((congrArg Prod.snd hii').symm.trans hi)).symm)
        ((coe_subset.mpr (Coatom.univ_map_left ▸ hC)).trans (coe_map_subset_range _ _))
        ((coe_subset.mpr (Coatom.univ_map_left ▸ h ▸ hC)).trans (coe_map_subset_range _ _)) hz hgi
    · exact StageType.eq_of_gradedIndex_eq_of_restrictFace_of_grade
        (hIR ▸ I.restrictFace_right)
        (fun i i' hii' hi ↦ (StageType.eq_of_grade_addApex hR _ hi).trans
          (StageType.eq_of_grade_addApex hR _ ((congrArg Prod.snd hii').symm.trans hi)).symm)
        ((coe_subset.mpr (Coatom.univ_map_right ▸ hD)).trans (coe_map_subset_range _ _))
        ((coe_subset.mpr (Coatom.univ_map_right ▸ h ▸ hD)).trans (coe_map_subset_range _ _)) hz hgi

end Seed

/-! ### The grade `4` of the layer scheme -/

namespace OrderedLayer

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {ρ : LayerRows.{u}}

variable (I ρ) in
/-- The **labelling of `Ω` alone**: `Ω` at the cells of grade `4`, `⊥` elsewhere. -/
noncomputable def omegaLabel (Ω : Label.{u}) (z : Fin (layerScheme I ρ).card) : Label.{u} :=
  if (layerScheme I ρ).toCellScheme.grade z = 4 then Ω else ⊥

variable (hρ4 : ∀ X, ρ 4 X = topRow X)
include hρ4

/-- The row of the new cell at `(univ, 4)` is `⊥` exactly below the grade `4`. -/
theorem row_newCell_four_eq_bot_iff
    (d : (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ 4))) :
    (layerScheme I ρ).rows.row (newCell I ρ 4) d = ⊥ ↔
      (layerScheme I ρ).toCellScheme.grade d.1 ≠ 4 := by
  rw [row_newCell (by omega) le_rfl, hρ4, topRow]
  split_ifs with h
  · exact ⟨fun h' ↦ absurd h' (gridPoint_ne_bot 4 1), fun h' ↦ absurd h h'⟩
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

/-- **At the grade `4`, a lawful labelling is constant on the cells of grade `4`**: locality and
availability at the new cell at `(univ, 4)`, whose row reads the cells of grade `4` at one value. -/
theorem eq_newCell_four {w : Fin (layerScheme I ρ).card → Label.{u}}
    (hw : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) fun z ↦ w z)
    {z : Fin (layerScheme I ρ).card} (hz : (layerScheme I ρ).toCellScheme.grade z = 4) :
    w z = w (newCell I ρ 4) := by
  obtain ⟨-, hl, ha⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hz' : z ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ 4)) := by
    rw [gradedIndex_newCell (by omega) le_rfl]; exact mem_below_univ_four z
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu, hle⟩ := ha z (newCell I ρ 4) (mem_below_univ_four _)
      (by rw [scope_newCell (by omega) le_rfl]; exact subset_univ _)
      (by rw [hz, grade_newCell (by omega) le_rfl])
    rwa [eq_newCell (by omega) le_rfl (hu.trans (gradedIndex_newCell (by omega) le_rfl))] at hle
  · have hself : newCell I ρ 4 ∈ (layerScheme I ρ).toCellScheme.below
        ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ 4)) :=
      (layerScheme I ρ).toCellScheme.mem_below_gradedIndex _
    have hr : (layerScheme I ρ).rows.row (newCell I ρ 4) ⟨newCell I ρ 4, hself⟩ ≤
        (layerScheme I ρ).rows.row (newCell I ρ 4) ⟨z, hz'⟩ := by
      rw [row_newCell (by omega) le_rfl, row_newCell (by omega) le_rfl, hρ4, hρ4, topRow,
        topRow]
      -- Read the graded indices of the two cells off the subtype.
      change (if ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ 4)).2 = 4 then _
        else _) ≤ (if (layerScheme I ρ).toCellScheme.grade z = 4 then _ else _)
      rw [gradedIndex_newCell (by omega) le_rfl, ite_eq_left rfl, ite_eq_left hz]
    have := (hl _ (mem_below_univ_four (newCell I ρ 4))).le_of_le hr
      (show (layerScheme I ρ).toCellScheme.grade z ≤
          (layerScheme I ρ).toCellScheme.grade (newCell I ρ 4) by
        rw [hz, grade_newCell (by omega) le_rfl])
    simp only [min_self] at this
    exact this.trans (min_le_left _ _)

/-- **At the grade `4`, a lawful labelling that is not `⊥` at the new cell at `(univ, 4)` is `⊥`
below the grade `4`**: the row of that cell is `⊥` there. -/
theorem eq_bot_of_newCell_four {w : Fin (layerScheme I ρ).card → Label.{u}}
    (hw : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) fun z ↦ w z)
    (hΩ : w (newCell I ρ 4) ≠ ⊥) {z : Fin (layerScheme I ρ).card}
    (hz : (layerScheme I ρ).toCellScheme.grade z ≠ 4) : w z = ⊥ := by
  obtain ⟨-, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  have hz' : z ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ 4)) := by
    rw [gradedIndex_newCell (by omega) le_rfl]; exact mem_below_univ_four z
  have := (hl _ (mem_below_univ_four (newCell I ρ 4))).eq_bot (d := ⟨z, hz'⟩)
    ((row_newCell_four_eq_bot_iff hρ4 ⟨z, hz'⟩).mpr hz)
  exact (min_eq_bot.mp this).resolve_right hΩ

variable (hI : I.HasBottomApexes)
include hI

/-- The row of a cell of grade `4` is `⊥` exactly below the grade `4`. -/
theorem row_eq_bot_iff_of_grade_four {s : Fin (layerScheme I ρ).card}
    (hs : (layerScheme I ρ).toCellScheme.grade s = 4)
    (d : (layerScheme I ρ).toCellScheme.below ((layerScheme I ρ).toCellScheme.gradedIndex s)) :
    (layerScheme I ρ).rows.row s d = ⊥ ↔ (layerScheme I ρ).toCellScheme.grade d.1 ≠ 4 := by
  by_cases hne : (layerScheme I ρ).toCellScheme.scope s = univ
  · obtain ⟨j, hj1, hj4, rfl⟩ := eq_newCell_of_scope hne
    obtain rfl : j = 4 := (grade_newCell hj1 hj4).symm.trans hs
    exact row_newCell_four_eq_bot_iff hρ4 d
  · obtain ⟨a, rfl⟩ := exists_eq_oldCell hne
    rw [grade_oldCell] at hs
    obtain ⟨e, he, hea⟩ := exists_oldCell_of_mem_below d.2
    have hrow : (layerScheme I ρ).rows.row (oldCell I ρ a) d =
        I.amalgam.rows.row a ⟨e, hea⟩ := by
      rw [← row_oldCell a e (he ▸ d.2) hea]
      exact (layerScheme I ρ).rows.row_congr rfl he
    rw [hrow, hI.row_apex hs, he, grade_oldCell]

/-- **The labelling of `Ω` alone is lawful below `(univ, 4)`**, for `Ω` self-visible at `4`: at
the cells of grade `4`, whose rows are `⊥` exactly below the grade `4`, the top shifter is a
witness. -/
theorem isLawfulBelow_omegaLabel {Ω : Label.{u}} (hΩ : IsSelfVisible 4 Ω) :
    (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4)
      fun z ↦ omegaLabel I ρ Ω z := by
  refine Rows.isLawfulBelow_iff_forall.mpr ⟨fun d _ ↦ ?_, fun s _ ↦ ?_, fun s t _ hst hg ↦ ?_⟩
  · rw [omegaLabel]
    split_ifs with h
    · rw [h]; exact hΩ
    · exact isSelfVisible_bot _
  · by_cases hs : (layerScheme I ρ).toCellScheme.grade s = 4
    · have hws : omegaLabel I ρ Ω s = Ω := by rw [omegaLabel, ite_eq_left hs]
      refine transformsTo_of_eq_bot_iff _
        (fun d : (layerScheme I ρ).toCellScheme.below
          ((layerScheme I ρ).toCellScheme.gradedIndex s) ↦ grade_le_four d.1) hΩ _ _ fun d ↦ ?_
      have key := row_eq_bot_iff_of_grade_four hρ4 hI hs d
      rw [hws, omegaLabel]
      by_cases hd4 : (layerScheme I ρ).toCellScheme.grade d.1 = 4
      · rw [ite_eq_left hd4, min_self, ite_eq_right (fun h ↦ (key.mp h) hd4)]
      · rw [ite_eq_right hd4, min_bot_left, ite_eq_left (key.mpr hd4)]
    · have hws : omegaLabel I ρ Ω s = ⊥ := by rw [omegaLabel, ite_eq_right hs]
      rw [hws]
      simp only [min_bot_right]
      exact TransformsTo.bot _ _
  · refine ⟨t, rfl, ?_⟩
    rw [omegaLabel, omegaLabel, hg]

/-! ### The capped lift at the grade `4` -/

/-- **The capped lift from a coatom at the grade `4` to `(univ, 4)`**, from the capped lift at the
grade `3`.  If the prescription is `⊥` at the apex, lift its restriction below the grade `3` (with
the ambient, or with `⊥` when the ambient is not `⊥` at the grade `4`, where the cap is then `⊥`)
and extend by `⊥`; otherwise the prescription is `⊥` below its apex, and the lift is the labelling
of its apex label alone. -/
theorem cappedLift_four {B : Finset (Fin 5)} (hB : B = coatomC ∨ B = coatomD)
    (h3 : (layerScheme I ρ).rows.CappedLift (X := (B, 3)) (Y := ((univ : Finset (Fin 5)), 3))
      ⟨subset_univ _, le_rfl⟩) :
    (layerScheme I ρ).rows.CappedLift (X := (B, 4)) (Y := ((univ : Finset (Fin 5)), 4))
      ⟨subset_univ _, le_rfl⟩ := by
  -- Step 1: the apex `a` at `(B, 4)` is the only cell of grade `4` below `(B, 4)`.
  have hBne : B ≠ univ := by rcases hB with rfl | rfl <;> decide
  have hBcard : #B = 4 := by rcases hB with rfl | rfl <;> decide
  obtain ⟨a, ha⟩ : ∃ a : Fin I.amalgam.card, I.amalgam.toCellScheme.gradedIndex a = (B, 4) := by
    refine I.exists_gradedIndex_eq _ ⟨?_, by omega, by rw [hBcard]⟩ hBne
    rcases hB with rfl | rfl
    · exact coatomC_mem_faces I
    · exact coatomD_mem_faces I
  have hag : I.amalgam.toCellScheme.grade a = 4 := congrArg Prod.snd ha
  have hag' : (layerScheme I ρ).toCellScheme.grade (oldCell I ρ a) = 4 := by
    rw [grade_oldCell, hag]
  have haB : oldCell I ρ a ∈ (layerScheme I ρ).toCellScheme.below (B, 4) := oldCell_mem_below ha.le
  have huniq : ∀ z ∈ (layerScheme I ρ).toCellScheme.below (B, 4),
      (layerScheme I ρ).toCellScheme.grade z = 4 → z = oldCell I ρ a := by
    intro z hz hz4
    obtain ⟨d, rfl⟩ := exists_eq_oldCell (z := z) fun h ↦ hBne (univ_subset_iff.mp (h ▸ hz.1))
    have hs : I.amalgam.toCellScheme.scope d ⊆ B := by rw [← scope_oldCell (ρ := ρ)]; exact hz.1
    have hg : I.amalgam.toCellScheme.grade d = 4 := by rw [← grade_oldCell (ρ := ρ)]; exact hz4
    have hcard : 4 ≤ #(I.amalgam.toCellScheme.scope d) :=
      hg ▸ I.amalgam.isWellFormed.isWellFormed.grade_le_card d
    refine congrArg (oldCell I ρ) (hI.eq_of_grade_four hg hag ?_)
    rw [show I.amalgam.toCellScheme.scope a = B from congrArg Prod.fst ha]
    exact eq_of_subset_of_card_le hs (by rw [hBcard]; exact hcard)
  have hbelow : ∀ z ∈ (layerScheme I ρ).toCellScheme.below (B, 4),
      z ∈ (layerScheme I ρ).toCellScheme.below
        ((layerScheme I ρ).toCellScheme.gradedIndex (oldCell I ρ a)) := fun z hz ↦ by
    rw [gradedIndex_oldCell, ha]; exact hz
  -- Step 2: extend the prescription `p` and the ambient `q` by `⊥` to all cells (`p'`, `q'`); it
  -- is enough to lift `p'` against `q'`.  The ambient is constant at the grade `4`.
  refine (Rows.cappedLift_iff_forall_exists _).mpr fun c hc p q hp hq hpq ↦ ?_
  let p' := Rows.extendBot (B, 4) p
  let q' := Rows.extendBot ((univ : Finset (Fin 5)), 4) q
  have hpl : (layerScheme I ρ).rows.IsLawfulBelow (B, 4) (fun z ↦ p' z) :=
    Rows.isLawfulBelow_extendBot.mpr hp
  have hql : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) (fun z ↦ q' z) :=
    Rows.isLawfulBelow_extendBot.mpr hq
  have hp'z : ∀ z (hz : z ∈ (layerScheme I ρ).toCellScheme.below (B, 4)), p' z = p ⟨z, hz⟩ :=
    fun _ hz ↦ Rows.extendBot_of_mem p hz
  have hq'z : ∀ z, q' z = q ⟨z, mem_below_univ_four z⟩ :=
    fun z ↦ Rows.extendBot_of_mem q (mem_below_univ_four z)
  have hpq' : ∀ z ∈ (layerScheme I ρ).toCellScheme.below (B, 4), min (q' z) c = min (p' z) c :=
    fun z hz ↦ by
      rw [hp'z z hz, hq'z z]
      exact hpq ⟨z, hz⟩
  have hqa : q' (oldCell I ρ a) = q' (newCell I ρ 4) := eq_newCell_four hρ4 hql hag'
  suffices h : ∃ x : Fin (layerScheme I ρ).card → Label.{u},
      (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 4) (fun z ↦ x z) ∧
      (∀ z, min (x z) c = min (q' z) c) ∧
      ∀ z ∈ (layerScheme I ρ).toCellScheme.below (B, 4), x z = p' z by
    obtain ⟨x, hx, hxq, hxp⟩ := h
    refine ⟨fun z ↦ x z, hx, fun z ↦ ?_, fun z ↦ ?_⟩
    · rw [hxq, hq'z z.1]
    · -- The restriction of `x` below `(univ, 4)`, at `z`.
      change x z.1 = p z
      rw [hxp z.1 z.2, hp'z z.1 z.2]
  by_cases hω : p' (oldCell I ρ a) = ⊥
  · -- Step 3: the prescription is `⊥` at the apex.  If the ambient is not `⊥` at the grade `4`,
    -- the cap is `⊥`; replace the ambient by `⊥` (`q₃`), lift below the grade `3` by `h3`, and
    -- extend by `⊥` above the grade `3`.
    have hc0 : q' (newCell I ρ 4) ≠ ⊥ → c = ⊥ := fun h ↦ by
      have := hpq' _ haB
      rw [hω, min_bot_left, hqa] at this
      exact (min_eq_bot.mp this).resolve_left h
    let q₃ : Fin (layerScheme I ρ).card → Label.{u} := fun z ↦
      if q' (newCell I ρ 4) = ⊥ then q' z else ⊥
    have hq₃ : (layerScheme I ρ).rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3)
        (fun z ↦ q₃ z) := by
      by_cases h : q' (newCell I ρ 4) = ⊥
      · have he : (fun z : (layerScheme I ρ).toCellScheme.below
              ((univ : Finset (Fin 5)), 3) ↦ q₃ z) =
            fun z : (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), 3) ↦ q' z :=
          funext fun z ↦ ite_eq_left h
        rw [he]
        exact hql.mono (X := ((univ : Finset (Fin 5)), 3)) ⟨subset_rfl, by omega⟩
      · have he : (fun z : (layerScheme I ρ).toCellScheme.below
              ((univ : Finset (Fin 5)), 3) ↦ q₃ z) = fun _ ↦ ⊥ :=
          funext fun z ↦ ite_eq_right h
        rw [he]
        exact Rows.isLawfulBelow_const_bot _
    have hq₃c : ∀ z, min (q₃ z) c = min (q' z) c := fun z ↦ by
      by_cases h : q' (newCell I ρ 4) = ⊥
      · exact congrArg (min · c) (ite_eq_left h)
      · rw [hc0 h, min_bot_right, min_bot_right]
    obtain ⟨x₃, hx₃, hx₃q, hx₃p⟩ := (Rows.cappedLift_iff_forall_exists _).mp h3 c
      (hc.mono (by omega)) (fun z ↦ p' z) (fun z ↦ q₃ z)
      (hpl.mono (X := (B, 3)) ⟨subset_rfl, by omega⟩) hq₃
      (fun z ↦ (hq₃c z.1).trans (hpq' z.1 ⟨z.2.1, z.2.2.trans (by omega)⟩))
    refine ⟨fun z ↦ if (layerScheme I ρ).toCellScheme.grade z ≤ 3 then
      Rows.extendBot ((univ : Finset (Fin 5)), 3) x₃ z else ⊥,
      Rows.isLawfulBelow_extendAbove (Rows.isLawfulBelow_extendBot.mpr hx₃), fun z ↦ ?_,
      fun z hz ↦ ?_⟩
    · dsimp only
      by_cases hz3 : (layerScheme I ρ).toCellScheme.grade z ≤ 3
      · have hzm : z ∈ (layerScheme I ρ).toCellScheme.below ((univ : Finset (Fin 5)), 3) :=
          ⟨subset_univ _, hz3⟩
        rw [ite_eq_left hz3, Rows.extendBot_of_mem x₃ hzm, hx₃q ⟨z, hzm⟩]
        exact hq₃c z
      · have hz4 : (layerScheme I ρ).toCellScheme.grade z = 4 := by
          have := grade_le_four z; omega
        rw [ite_eq_right hz3, eq_newCell_four hρ4 hql hz4]
        by_cases h : q' (newCell I ρ 4) = ⊥
        · rw [h]
        · rw [hc0 h, min_bot_right, min_bot_right]
    · dsimp only
      by_cases hz3 : (layerScheme I ρ).toCellScheme.grade z ≤ 3
      · rw [ite_eq_left hz3, Rows.extendBot_of_mem x₃ ⟨subset_univ _, hz3⟩]
        exact hx₃p ⟨z, ⟨hz.1, hz3⟩⟩
      · have hz4 : (layerScheme I ρ).toCellScheme.grade z = 4 := by
          have := grade_le_four z; omega
        rw [ite_eq_right hz3, huniq z hz hz4, hω]
  · -- Step 4: the prescription is not `⊥` at the apex, hence `⊥` below the grade `4` (the row of
    -- the apex); the lift is the labelling of its apex label `Ω` alone.  If `c ≠ ⊥`, the ambient
    -- is not `⊥` at the grade `4`, hence `⊥` below it, and agrees with `Ω` capped at `c` there.
    obtain ⟨ho, hl, -⟩ := Rows.isLawfulBelow_iff_forall.mp hpl
    have hωsv : IsSelfVisible 4 (p' (oldCell I ρ a)) := hag' ▸ ho _ haB
    refine ⟨omegaLabel I ρ (p' (oldCell I ρ a)), isLawfulBelow_omegaLabel hρ4 hI hωsv,
      fun z ↦ ?_, fun z hz ↦ ?_⟩
    · by_cases hc0 : c = ⊥
      · rw [hc0, min_bot_right, min_bot_right]
      have hΩq : q' (newCell I ρ 4) ≠ ⊥ := by
        intro h
        have := hpq' _ haB
        rw [hqa, h, min_bot_left] at this
        exact (min_eq_bot.mp this.symm).elim hω hc0
      rw [omegaLabel]
      split_ifs with hz4
      · rw [eq_newCell_four hρ4 hql hz4, ← hqa]
        exact (hpq' _ haB).symm
      · rw [eq_bot_of_newCell_four hρ4 hql hΩq hz4]
    · rw [omegaLabel]
      split_ifs with hz4
      · rw [huniq z hz hz4]
      · have := (hl _ haB).eq_bot (d := ⟨z, hbelow z hz⟩)
          ((row_eq_bot_iff_of_grade_four hρ4 hI hag' ⟨z, hbelow z hz⟩).mpr hz4)
        exact ((min_eq_bot.mp this).resolve_right hω).symm

end OrderedLayer

/-! ### The ordered-layer step from the grades below the top -/

namespace Seed

open OrderedLayer

variable {α : Ordinal.{u}} {I : Seed.{u} α 3} {ρ : LayerRows.{u}}

/-- **The top grade is automatic.**  For a seed with bottom apexes and layer rows whose row at
`(univ, 4)` is the top row, the ordered-layer step follows from its fields at the grades `k ≤ 3`:
the top row is the labelling of `ω + 4` at the cells of grade `4` alone, the lifts at the grade `4`
come from those at the grade `3` (`OrderedLayer.cappedLift_four`), and the labelling of `⊤` at the
cells of grade `4` alone extends the glued labelling. -/
theorem OrderedLayerStepBelowTop.orderedLayerStep (hI : I.HasBottomApexes)
    (hρ4 : ∀ X, ρ 4 X = topRow X) (h : I.OrderedLayerStepBelowTop ρ) : I.OrderedLayerStep ρ := by
  -- The top row, read off the graded indices, is the labelling of `ω + 4` alone.
  have htop (z : Fin (layerScheme I ρ).card) :
      ρ 4 ((layerScheme I ρ).toCellScheme.gradedIndex z) = omegaLabel I ρ (gridPoint 4 1) z := by
    rw [hρ4, topRow, omegaLabel]; rfl
  refine ⟨fun k hk1 hk4 z hz ↦ ?_, fun k hk1 hk4 ↦ ?_, fun k hk1 hk4 ↦ ?_, fun k hk1 hk4 ↦ ?_,
    ⟨omegaLabel I ρ ⊤, (isLawfulBelow_omegaLabel hρ4 hI (isSelfVisible_top 4)).isLawful
      mem_below_univ_four, fun d ↦ ?_⟩⟩
  · rcases (show k ≤ 3 ∨ k = 4 by omega) with hk3 | rfl
    · exact h.row_lt k hk1 hk3 z hz
    · rw [hρ4, topRow]
      split_ifs
      · exact gridPoint_lt_omega0_sq 4 1
      · exact WithBot.bot_lt_coe _
  · rcases (show k ≤ 3 ∨ k = 4 by omega) with hk3 | rfl
    · exact h.isLawfulBelow_row k hk1 hk3
    · exact (Rows.isLawfulBelow_congr fun z _ ↦ (htop z).symm).mp
        (isLawfulBelow_omegaLabel hρ4 hI (isSelfVisible_gridPoint 4 1))
  · rcases (show k ≤ 3 ∨ k = 4 by omega) with hk3 | rfl
    · exact h.cappedLift_left k hk1 hk3
    · exact cappedLift_four hρ4 hI (.inl rfl) (h.cappedLift_left 3 (by omega) le_rfl)
  · rcases (show k ≤ 3 ∨ k = 4 by omega) with hk3 | rfl
    · exact h.cappedLift_right k hk1 hk3
    · exact cappedLift_four hρ4 hI (.inr rfl) (h.cappedLift_right 3 (by omega) le_rfl)
  · rw [omegaLabel, grade_oldCell, hI.label_eq]

/-- **The completion from the ordered-layer step below the top grade**, for a seed with bottom
apexes and the top row at `(univ, 4)`. -/
theorem OrderedLayerStepBelowTop.nonempty_completionBelowFullGrade (hI : I.HasBottomApexes)
    (hρ4 : ∀ X, ρ 4 X = topRow X) (h : I.OrderedLayerStepBelowTop ρ) :
    Nonempty (CompletionBelowFullGrade I) :=
  (h.orderedLayerStep hI hρ4).nonempty_completionBelowFullGrade

end Seed

end VaughtConjecture
