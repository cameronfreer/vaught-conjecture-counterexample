/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.ThinCompletionMirror
import VaughtConjecture.Extension.OrderedLayerExamples
import VaughtConjecture.Extension.OrderedLayerObstruction

/-!
# The mirror of the asymmetric seed: its ordered-layer step, and the orientation it forces

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the ordered-layer step at `m = 3`: the seed whose
coatom types are `T5` and `TL`, the mirror of `seedL`, as an instance, and the orientation its rows
must have); semantic contract, items 2–4.

* **The mirror seed** (`seedLM`): the seed of `T5` on the first coatom and `TL` on the second,
  over the common face of `seedL`.  It has bottom apexes (`Seed.hasBottomApexes_of_T5_TL`) and an
  ordered-layer step with the rows `OrderedLayer.Mirror.rowsLM`, oriented `D` before `C`
  (`Seed.orderedLayerStep_of_T5_TL`, `Seed.orderedLayerStep_seedLM`).
* **The forcings** (`Seed.forcesTop_of_TL_T5`, `Seed.forcesTop_of_T5_TL`): for a seed whose types
  are `TL` and `T5`, the prescription `(A_C, F_C, G) = (1, ⊤, ⊤)` below `(C, 3)` forces `⊤` at
  `({4}, 1)` below `(D, 3)` (the coupling `G ≤ A` of `T5` on `D`); for the mirror seed, the
  prescription `(A_D, F_D, G) = (1, ⊤, ⊤)` below `(D, 3)` forces `⊤` at `({3}, 1)` below `(C, 3)`.
  These are instances of `Seed.ForcesTop`.
* **The orientation is forced `D` before `C`** (`exists_separating_cell_of_le_three`,
  `Seed.OrderedLayerStep.rowsLM_lt_of_T5_TL`): every completion below the full grade of the mirror
  seed has, at each `(univ, k)`, `1 ≤ k ≤ 3`, a cell whose row reads `({4}, 1)` strictly below
  `({3}, 1)`; so every ordered-layer step of it reads them in that order at the layers `1`, `2`,
  `3`.
* **No layer rows serve both seeds** (`not_exists_orderedLayerStep_seedL_seedLM`): `seedL` forces
  the orientation `C` before `D` (`Seed.OrderedLayerStep.thinRow_lt_of_TL_T5`), its mirror the
  orientation `D` before `C`.  The rows of the ordered-layer step depend on the seed.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme OrderedLayer
open TwoFaceLiftExistsCounterexample (TL VisibilityReplaceFixedOfLT)
open CaseSplitCounterexample (T5 tripleLabelling tripleKind)

/-! ### The mirror seed -/

/-- **The mirror of the asymmetric seed**: `T5` on the first coatom and `TL` on the second, over
the common face of `seedL`. -/
noncomputable def seedLM (α : Ordinal.{u}) : Seed.{u} α 3 :=
  Seed.ofCoatoms (CaseSplitCounterexample.isLegal_T5 α)
    (TwoFaceLiftExistsCounterexample.isLegal_TL α)
    (CaseSplitCounterexample.restrictFace_T5 α) (TwoFaceLiftExistsCounterexample.restrictFace_TL α)

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **A seed whose coatom types are `T5` and `TL` has bottom apexes.** -/
theorem hasBottomApexes_of_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α) :
    I.HasBottomApexes :=
  hasBottomApexes_of_addApex CaseSplitCounterexample.isLegalBelowFullGrade_S
    TwoFaceLiftExistsCounterexample.isLegalBelowFullGrade_SL (fun _ ↦ rfl) (fun _ ↦ rfl) hIL hIR

/-- **The ordered-layer step of a seed whose coatom types are `T5` and `TL`**, with the rows
`OrderedLayer.Mirror.rowsLM`, oriented `D` before `C`. -/
theorem orderedLayerStep_of_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α) :
    I.OrderedLayerStep Mirror.rowsLM :=
  (Mirror.orderedLayerStepBelowTop_of hIL hIR).orderedLayerStep
    (hasBottomApexes_of_T5_TL hIL hIR) fun _ ↦ rfl

/-- **The ordered-layer step of the mirror seed.** -/
theorem orderedLayerStep_seedLM : (seedLM α).OrderedLayerStep Mirror.rowsLM :=
  orderedLayerStep_of_T5_TL rfl rfl

/-- **The mirror seed has a completion below the full grade.** -/
theorem nonempty_completionBelowFullGrade_seedLM :
    Nonempty (CompletionBelowFullGrade (seedLM α)) :=
  orderedLayerStep_seedLM.nonempty_completionBelowFullGrade

/-! ### The forcings -/

private theorem left_eq_three : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.left 3)) id (TwoFaceLiftCounterexample.cells.gradedIndex c) =
      (({3} : Finset (Fin 5)), 1) → c = 3 := by decide +kernel

private theorem left_eq_sixteen : ∀ c : Fin 19,
    Prod.map (Finset.map (Coatom.left 3)) id (TwoFaceLiftCounterexample.cells.gradedIndex c) =
      (({0, 1, 2} : Finset (Fin 5)), 3) → c = 16 := by decide +kernel

/-- **On the first coatom of type `T5`, the cell `({3}, 1)` carries at least the label of the cell
of the common face of grade `3`**: the coupling `G ≤ A` of `T5`. -/
theorem le_of_isLawfulBelow_left (hIL : I.left = T5 α) {w : Fin I.amalgam.card → Label.{u}}
    (hw : I.amalgam.rows.IsLawfulBelow (coatomC, 3) fun d ↦ w d) {d₁ g : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hg : I.amalgam.toCellScheme.gradedIndex g = (({0, 1, 2} : Finset (Fin 5)), 3)) :
    w g ≤ w d₁ := by
  rw [coatomC_eq] at hw
  obtain ⟨A, F, G, -, -, -, hGA, -, hall⟩ :=
    CaseSplitCounterexample.exists_labelling_of_comap (hIL ▸ I.restrictFace_left) le_rfl w hw
  have hmem1 : d₁ ∈ I.amalgam.toCellScheme.below (univ.map (Coatom.left 3), 3) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex d₁ ≤ _
    rw [hd₁, Coatom.univ_map_left]; decide +kernel
  have hmemg : g ∈ I.amalgam.toCellScheme.below (univ.map (Coatom.left 3), 3) := by
    -- Membership below a pair is comparison of graded indices.
    change I.amalgam.toCellScheme.gradedIndex g ≤ _
    rw [hg, Coatom.univ_map_left]; decide +kernel
  obtain ⟨c₁, hc₁, hw₁⟩ := hall d₁ hmem1
  obtain ⟨cg, hcg, hwg⟩ := hall g hmemg
  obtain rfl := left_eq_three c₁ (hc₁.symm.trans hd₁)
  obtain rfl := left_eq_sixteen cg (hcg.symm.trans hg)
  rw [hw₁, hwg]
  -- The matched cells of `T5` are its cells `16` (at `({0, 1, 2}, 3)`) and `3` (at `({3}, 1)`).
  change CaseSplitCounterexample.labelling A F G 16 ≤ CaseSplitCounterexample.labelling A F G 3
  rw [CaseSplitCounterexample.labelling_three rfl rfl,
    CaseSplitCounterexample.labelling_one rfl rfl]
  exact hGA

/-- The cell of the common face of grade `3` lies below both coatoms at the grade `3`. -/
private theorem mem_below_E {g : Fin I.amalgam.card}
    (hg : I.amalgam.toCellScheme.gradedIndex g = (({0, 1, 2} : Finset (Fin 5)), 3))
    {B : Finset (Fin 5)} (hB : B = coatomC ∨ B = coatomD) :
    g ∈ I.amalgam.toCellScheme.below (B, 3) := by
  -- Membership below a pair is comparison of graded indices.
  change I.amalgam.toCellScheme.gradedIndex g ≤ _
  rw [hg]; rcases hB with rfl | rfl <;> decide

/-- **The forcing of the asymmetric seed**: for a seed whose coatom types are `TL` and `T5`, the
prescription `tripleLabelling A ⊤ ⊤ ⊤ ⊤` below `(C, 3)` forces `⊤` at the cell `({4}, 1)` below
`(D, 3)`, through the coupling `G ≤ A` of `T5` on `D`. -/
theorem forcesTop_of_TL_T5 (hIR : I.right = T5 α) (A : Label.{u}) {d₂ : Fin I.amalgam.card}
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1)) :
    I.ForcesTop (coatomC, 3) (coatomD, 3)
      (fun d ↦ tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d)) d₂ := by
  intro w hw hwP
  obtain ⟨g, hg⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hwg : w g = ⊤ := by
    rw [hwP g (mem_below_E hg (.inl rfl)) (mem_below_E hg (.inr rfl))]; simp only [hg]; rfl
  exact top_le_iff.mp
    (hwg ▸ TwoFaceLiftExistsCounterexample.le_of_isLawfulBelow_right hIR hw hd₂ hg)

/-- **The forcing of the mirror seed**: for a seed whose coatom types are `T5` and `TL`, the
prescription `tripleLabelling ⊤ ⊤ A ⊤ ⊤` below `(D, 3)` forces `⊤` at the cell `({3}, 1)` below
`(C, 3)`, through the coupling `G ≤ A` of `T5` on `C`. -/
theorem forcesTop_of_T5_TL (hIL : I.left = T5 α) (A : Label.{u}) {d₁ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1)) :
    I.ForcesTop (coatomD, 3) (coatomC, 3)
      (fun d ↦ tripleLabelling ⊤ ⊤ A ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d)) d₁ := by
  intro w hw hwP
  obtain ⟨g, hg⟩ : ∃ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hwg : w g = ⊤ := by
    rw [hwP g (mem_below_E hg (.inr rfl)) (mem_below_E hg (.inl rfl))]; simp only [hg]; rfl
  exact top_le_iff.mp (hwg ▸ le_of_isLawfulBelow_left hIL hw hd₁ hg)

end Seed

/-! ### The orientation of the mirror seed -/

namespace OrderedLayer.Mirror

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **Every completion of the mirror seed separates `D` before `C`** at each `(univ, k)`,
`1 ≤ k ≤ 3`: some cell there reads `({4}, 1)` strictly below `({3}, 1)`.  Bountifulness from
`(D, 3)` lifts the prescription `(A_D, F_D, G) = (1, ⊤, ⊤)` of `TL`; on `C` the lift is `⊤` at
`({3}, 1)` (the coupling of `T5`); availability from a cell of grade `k` labelled `⊤` (`({3}, 1)`,
`(D, 2)`, `(E, 3)`) gives the cell `u` with label `⊤`, and locality at `u` excludes reading
`({3}, 1)` at most `({4}, 1)`. -/
theorem exists_separating_cell_of_le_three (hIL : I.left = T5 α) (hIR : I.right = TL α)
    (F : CompletionBelowFullGrade I) {k : ℕ} (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1)) :
    ∃ u : Fin F.scheme.card, F.scheme.toCellScheme.gradedIndex u = (univ, k) ∧
      ∀ (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₂⟩ < F.scheme.rows.row u ⟨_, h₁⟩ := by
  classical
  -- Step 0: the cells `s_D = (D, 2)` and `g = (E, 3)`, and the pairs `X = (D, 3)`, `Y`.
  obtain ⟨sD, hsD⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2, 4} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ :=
      TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ :=
      TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hκ₂ : tripleKind (({4} : Finset (Fin 5)), 1) = 3 := by decide
  have hκs : tripleKind (({0, 1, 2, 4} : Finset (Fin 5)), 2) = 4 := by decide
  have hκg : tripleKind (({0, 1, 2} : Finset (Fin 5)), 3) = 5 := by decide
  set A : Label.{u} := TwoFaceLiftCounterexample.v1 with hA_def
  set X : Finset (Fin 5) × ℕ := (coatomD, 3) with hX_def
  set Y : Finset (Fin 5) × ℕ := ((univ : Finset (Fin 5)), 3) with hY_def
  have hXne : X.1 ≠ univ := by decide
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  -- Step 1: the prescription `P = (A_D, F_D, G) = (A, ⊤, ⊤)`, lawful below `(D, 3)`.
  set P : Fin F.scheme.card → Label.{u} := fun z ↦
    tripleLabelling ⊤ ⊤ A ⊤ ⊤ (F.scheme.toCellScheme.gradedIndex z) with hP
  have hPe (d : Fin I.amalgam.card) :
      P (F.embed d) = tripleLabelling ⊤ ⊤ A ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) := by
    simp only [hP, CompletionBelowFullGrade.gradedIndex_embed]
  have hAc : VisibilityReplaceFixedOfLT A ⊤ := fun _ ↦ by
    rw [hA_def, TwoFaceLiftCounterexample.v1_eq, Label.visibilityReplace_natCast]; simp
  have hPlaw : F.scheme.rows.IsLawfulBelow X fun z ↦ P z := by
    rw [F.isLawfulBelow_embed_iff hXne]
    simp only [hPe]
    exact (isLawfulBelow_tripleLabelling (I := I) hIL hIR (isSelfVisible_top 1)
      (isSelfVisible_top 2) (isSelfVisible_gridPoint 1 0) (isSelfVisible_top 2)
      (isSelfVisible_top 3) le_rfl le_rfl le_rfl hAc).2
  -- Step 2: the lift `w` of `P` from `(D, 3)` to `(univ, 3)` (bountifulness, cap `⊥`).
  have hXg : X ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨by rw [F.faces_eq]; exact coatomD_mem_faces I, by decide, by decide⟩
  have hYg : Y ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, by decide, by simp [hY_def]⟩
  obtain ⟨x', hx'law, -, hx'p⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (F.isLegalBelowFullGrade.isBountiful.cappedLift hXg hYg hXY) ⊥ (isSelfVisible_bot _)
    (fun z ↦ P z) (fun _ ↦ ⊥) hPlaw (Rows.isLawfulBelow_const_bot _) fun _ ↦ by simp
  set w := Rows.extendBot Y x' with hw_def
  have hw : F.scheme.rows.IsLawfulBelow Y fun z ↦ w z := Rows.isLawfulBelow_extendBot.mpr hx'law
  have hwX (z : Fin F.scheme.card) (hz : z ∈ F.scheme.toCellScheme.below X) : w z = P z := by
    rw [hw_def, Rows.extendBot_of_mem x' (F.scheme.toCellScheme.below_mono hXY hz)]
    exact hx'p ⟨z, hz⟩
  -- Step 3: the values of `w` on `D`: `A` at `d₂`, `⊤` at `s_D` and at `g`.
  have hmem (d : Fin I.amalgam.card) {Z : Finset (Fin 5) × ℕ}
      (h : I.amalgam.toCellScheme.gradedIndex d ≤ Z) :
      F.embed d ∈ F.scheme.toCellScheme.below Z := by
    rw [CellScheme.mem_below, CompletionBelowFullGrade.gradedIndex_embed]
    exact h
  have hw₂ : w (F.embed d₂) = A := by
    rw [hwX _ (hmem d₂ (by rw [hd₂]; decide +kernel)), hPe, hd₂]
    simp only [tripleLabelling, hκ₂]; rfl
  have hwS : w (F.embed sD) = ⊤ := by
    rw [hwX _ (hmem sD (by rw [hsD]; decide +kernel)), hPe, hsD]
    simp only [tripleLabelling, hκs]; rfl
  have hwG : w (F.embed gE) = ⊤ := by
    rw [hwX _ (hmem gE (by rw [hgE]; decide +kernel)), hPe, hgE]
    simp only [tripleLabelling, hκg]; rfl
  -- Step 4: on `C`, the coupling `G ≤ A` of `T5` gives `w d₁ = ⊤`.
  have hwC : F.scheme.rows.IsLawfulBelow (coatomC, 3) fun z ↦ w z :=
    hw.mono (X := (coatomC, 3)) ⟨subset_univ _, le_rfl⟩
  have hwC' := (F.isLawfulBelow_embed_iff (by decide)).mp hwC
  have hC := Seed.le_of_isLawfulBelow_left hIL (w := fun d ↦ w (F.embed d)) hwC' hd₁ hgE
  have hw₁ : w (F.embed d₁) = ⊤ := top_le_iff.mp (hwG ▸ hC)
  -- Step 5: an old cell `s` of grade `k` where `w` is `⊤`: `d₁`, `s_D` or `g`.
  have hgr (d : Fin I.amalgam.card) {W : Finset (Fin 5) × ℕ}
      (h : I.amalgam.toCellScheme.gradedIndex d = W) :
      F.scheme.toCellScheme.grade (F.embed d) = W.2 :=
    (congrArg Prod.snd (F.gradedIndex_embed d)).trans (congrArg Prod.snd h)
  obtain ⟨s, hgs, hws⟩ : ∃ s : Fin I.amalgam.card,
      F.scheme.toCellScheme.grade (F.embed s) = k ∧ w (F.embed s) = ⊤ := by
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact ⟨d₁, hgr d₁ hd₁, hw₁⟩
    · exact ⟨sD, hgr sD hsD, hwS⟩
    · exact ⟨gE, hgr gE hgE, hwG⟩
  -- Step 6: availability from `s` gives the cell `u` at `(univ, k)`, with `w u = ⊤`.
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hw
  obtain ⟨t0, ht0⟩ := F.isLegalBelowFullGrade.exists_gradedIndex_eq ((univ : Finset (Fin 5)), k)
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, hk₁,
      by dsimp only; rw [Finset.card_univ, Fintype.card_fin]; omega⟩ (by omega)
  have ht0Y : t0 ∈ F.scheme.toCellScheme.below Y := by
    rw [CellScheme.mem_below, ht0]
    exact ⟨subset_rfl, hk₃⟩
  obtain ⟨u, hu, hle⟩ := havail (F.embed s) t0 ht0Y
    (by rw [show F.scheme.toCellScheme.scope t0 = univ from congrArg Prod.fst ht0]
        exact subset_univ _)
    (by rw [hgs]; exact (congrArg Prod.snd ht0).symm)
  have hu' : F.scheme.toCellScheme.gradedIndex u = (univ, k) := hu.trans ht0
  have huY : u ∈ F.scheme.toCellScheme.below Y := by
    rw [CellScheme.mem_below, hu']
    exact ⟨subset_rfl, hk₃⟩
  have hwu : w u = ⊤ := top_le_iff.mp (hws ▸ hle)
  refine ⟨u, hu', fun h₂ h₁ ↦ ?_⟩
  -- Step 7: locality at `u`: reading `d₁` at most `d₂` would give `⊤ = w d₁ ≤ w d₂ = A`.
  by_contra hcon
  rw [not_lt] at hcon
  have h12 := (hloc u huY).le_of_le (d := ⟨_, h₁⟩) (d' := ⟨_, h₂⟩) hcon
    (by simp only [hgr d₁ hd₁, hgr d₂ hd₂, le_refl])
  simp only at h12
  rw [hw₁, hw₂, hwu, min_top_right, min_top_right] at h12
  exact gridPoint_ne_top 1 0 (top_le_iff.mp h12)

end OrderedLayer.Mirror

namespace Seed

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **Every ordered-layer step of a seed whose coatom types are `T5` and `TL` reads `D` before
`C`**: for any layer rows `ρ` with an ordered-layer step, the row at `(univ, k)`, `k = 1, 2, 3`,
reads `({4}, 1)` strictly below `({3}, 1)`.  The completion from the step has only the new cell at
`(univ, k)`, and every completion has a cell separating `D` before `C` there. -/
theorem OrderedLayerStep.rowsLM_lt_of_T5_TL (hIL : I.left = T5 α) (hIR : I.right = TL α)
    {ρ : LayerRows.{u}} (h : I.OrderedLayerStep ρ) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    ρ k (({4} : Finset (Fin 5)), 1) < ρ k (({3} : Finset (Fin 5)), 1) := by
  obtain ⟨d₁, hd₁⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ :=
      TwoFaceLiftExistsCounterexample.exists_cell_TL (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨u, hu, hsep⟩ :=
    Mirror.exists_separating_cell_of_le_three hIL hIR h.completion hk1 hk3 hd₁ hd₂
  -- The cell `u` of the completion at `(univ, k)` is the new cell of the layer scheme.
  change Fin (layerScheme I ρ).card at u
  change (layerScheme I ρ).toCellScheme.gradedIndex u = _ at hu
  obtain rfl := eq_newCell hk1 (by omega) hu
  have hmem {d : Fin I.amalgam.card} {B : Finset (Fin 5)}
      (hd : I.amalgam.toCellScheme.gradedIndex d = (B, 1)) :
      h.completion.embed d ∈ h.completion.scheme.toCellScheme.below
        (h.completion.scheme.toCellScheme.gradedIndex (newCell I ρ k)) := by
    -- The completion's scheme is the layer scheme, and its embedding is `oldCell`.
    change oldCell I ρ d ∈ (layerScheme I ρ).toCellScheme.below
      ((layerScheme I ρ).toCellScheme.gradedIndex (newCell I ρ k))
    rw [gradedIndex_newCell hk1 (by omega)]
    exact oldCell_mem_below (hd ▸ ⟨subset_univ _, hk1⟩)
  have := hsep (hmem hd₂) (hmem hd₁)
  -- The separation, read in the rows of the layer scheme.
  change (layerScheme I ρ).rows.row (newCell I ρ k) ⟨oldCell I ρ d₂, hmem hd₂⟩ <
    (layerScheme I ρ).rows.row (newCell I ρ k) ⟨oldCell I ρ d₁, hmem hd₁⟩ at this
  rwa [row_newCell hk1 (by omega), row_newCell hk1 (by omega), gradedIndex_oldCell,
    gradedIndex_oldCell, hd₂, hd₁] at this

end Seed

/-- **No layer rows serve both the asymmetric seed and its mirror**: an ordered-layer step of
`seedL` reads `({3}, 1)` below `({4}, 1)` at the layer `1`, one of `seedLM` reads `({4}, 1)` below
`({3}, 1)`.  The orientation of the rows of the ordered-layer step depends on the seed. -/
theorem not_exists_orderedLayerStep_seedL_seedLM (α : Ordinal.{u}) :
    ¬ ∃ ρ : LayerRows.{u}, (TwoFaceLiftExistsCounterexample.seedL α).OrderedLayerStep ρ ∧
      (seedLM α).OrderedLayerStep ρ := by
  rintro ⟨ρ, hL, hM⟩
  exact lt_asymm (hL.thinRow_lt_of_TL_T5 rfl rfl le_rfl (by omega))
    (hM.rowsLM_lt_of_T5_TL rfl rfl le_rfl (by omega))

end VaughtConjecture
