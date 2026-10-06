/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample

/-!
# The separating cell: a necessary condition for every completion of the asymmetric seed

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the recursion on the grade; here a condition that
every completion below the full grade of the asymmetric seed `seedL` meets); semantic contract,
items 2–4.

Write `C = {0, 1, 2, 3}` and `D = {0, 1, 2, 4}` for the two coatoms of a seed on five points,
`E = {0, 1, 2}` for their common face, `d₁` for its cell at `({3}, 1)` (on `C`) and `d₂` for its
cell at `({4}, 1)` (on `D`).

**Separating cells.**  A cell `u` of a completion below the full grade, at `(univ, k)`, is a
*separating cell* when its row reads `d₁` strictly below `d₂`.  Every completion below the full
grade of a seed whose coatom types are `TL` and `T5` (module
`VaughtConjecture.Extension.TwoFaceLiftExistsCounterexample`) has one at each `(univ, k)`,
`1 ≤ k ≤ 3`, at which a given lawful labelling reaches a given cap
(`exists_separating_cell_of_le_three`; at `(univ, 2)`, `exists_separating_cell`): for every cap
`c` self-visible at `3`, every `A ≠ ⊤` self-visible at `1` with `VisibilityReplaceFixedOfLT A ⊤`,
and every labelling `q` lawful below `(univ, 3)` that agrees capped at `c` with the prescription
`tripleLabelling A ⊤ ⊤ ⊤ ⊤` on `C`, some separating cell `u` at `(univ, k)` has `c ≤ q u`.  The
proof is the argument of the refutation of the existential two-face lift at the grade `2`
(`not_twoFaceLiftExists_two_of`, steps 4 and 5), with the tower replaced by an arbitrary
completion: bountifulness from `(C, 3)` to `(univ, 3)` lifts the prescription to `w`; on `D`, `w`
is lawful in `T5` and `⊤` at the cell of the common face of grade `3`, hence `⊤` at `d₂` (the
coupling `G ≤ A` of `T5`); availability from a cell of grade `k` where `w` is `⊤` (`d₂` at
`k = 1`, the cell `(C, 2)` at `k = 2`, the cell `(E, 3)` at `k = 3`) gives a cell `u` at
`(univ, k)` with `w u = ⊤ ≥ c`; and locality at `u` with `w d₁ = A < ⊤ = w d₂` forces the row of
`u` to read `d₁` below `d₂`.  With `c = ⊥` and `q = ⊥`: every completion has a separating cell at
each `(univ, k)` (`exists_separating_cell_of_completion_of_le_three`; at `(univ, 2)`,
`exists_separating_cell_of_completion`; for `seedL`, `exists_separating_cell_seedL_of_le_three`).
The tower of the step does not meet this condition (argued from step 3 of
`not_twoFaceLiftExists_two_of`, not formalized: every new cell at `(univ, 2)` where the catalogue
entry reaches the cap reads `d₁` and `d₂` at the same value); that the tower fails for `seedL` is
`not_towerInvariant_top_seedL`.

**Collisions.**  A *collision* at a cell `z` of grade `2` is a labelling that carries one label
`e = λ + 1`, of finite part `1` (not self-visible at `2`), at two cells of grade `1`, and a label
above `e` at `z`.  At a separating cell there is no collision (`le_of_separating`): every
labelling lawful below `(univ, 2)` with `x d₁ = x d₂ = λ + 1` has `x u ≤ λ + 1`.  This is the
collision lemma (`Label.eq_of_transformsTo_collision`): if a row transforms to a labelling with a
collision at `z`, and its values at the two cells are self-visible at `1`, then those values are
equal.  The suppressor exceeds `e` at the grade `2`, so the shifter sends both row values to `e`;
if they differed, the commutation of the shifter with `visibilityReplace 2 2` at the smaller one
would give `visibilityReplace 2 2 e ≤ e`, which fails since `e` is not self-visible at `2`
(`Label.visibilityReplace_two_two_le_of_lt`).

The separating cell is a necessary condition, not a refutation: the thin completion of
`VaughtConjecture.Extension.ThinCompletion` (the amalgam with one new cell at each graded face of
full scope) meets it, with one cell at `(univ, 2)`, and no labelling of it lawful below `(univ, 2)`
has a collision there.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture.ThinCompletion

open Finset Label CellScheme
open Ordinal hiding univ
open TwoFaceLiftExistsCounterexample
open CaseSplitCounterexample (tripleLabelling tripleKind)

/-! ### The separating cell -/

section Separation

variable {α : Ordinal.{u}}

/-- **The necessary condition for every completion of the asymmetric seed**, at every grade
`1 ≤ k ≤ 3` of the full scope.  Let `F` be a completion below the full grade of a seed whose
coatom types are `TL` and `T5`, `c` a cap self-visible at `3`, `A ≠ ⊤` a label self-visible at `1`
with `VisibilityReplaceFixedOfLT A ⊤` (finite part `1` or at least `3`), and `q` lawful below
`(univ, 3)` in `F` agreeing capped at `c` with the prescription `(A_C, F_C, G) = (A, ⊤, ⊤)` on
`C`.  Then some cell `u` of `F` at `(univ, k)` has `c ≤ q u` and its row reads `d₁ = ({3}, 1)`
strictly below `d₂ = ({4}, 1)`.

Bountifulness of `F` from `(C, 3)` to `(univ, 3)` gives a lift `w`; on `D`, `w` is lawful in
`T5` and `⊤` at the cell of the common face of grade `3`, so `⊤` at `d₂`; availability from a cell
of grade `k` labelled `⊤` (`d₂` at `k = 1`, `(C, 2)` at `k = 2`, `(E, 3)` at `k = 3`) gives `u` at
`(univ, k)` with `w u = ⊤`, hence `c ≤ q u`; locality at `u` with `w d₁ = A < ⊤ = w d₂` forces
the row of `u` to read `d₁` below `d₂`. -/
theorem exists_separating_cell_of_le_three {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) (F : CompletionBelowFullGrade I) {k : ℕ}
    (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    {c : Label.{u}} (hc : IsSelfVisible 3 c) {A : Label.{u}} (hA : IsSelfVisible 1 A)
    (hAc : VisibilityReplaceFixedOfLT A ⊤) (hAtop : A ≠ ⊤) {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hqp : ∀ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase (Fin.last 4), 3) →
      min (q (F.embed d)) c =
        min (tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d)) c)
    {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1)) :
    ∃ u : Fin F.scheme.card, F.scheme.toCellScheme.gradedIndex u = (univ, k) ∧ c ≤ q u ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ := by
  classical
  -- Step 0: the cells `s_C = (C, 2)` and `g = (E, 3)` of the amalgam, the pairs `X = (C, 3)` and
  -- `Y = (univ, 3)`, and the kinds of `tripleLabelling` at `d₁`, `s_C` and `g`.
  obtain ⟨sC, hsC⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2, 3} : Finset (Fin 5)), 2) := by
    obtain ⟨e, he⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 15
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨gE, hgE⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({0, 1, 2} : Finset (Fin 5)), 3) := by
    obtain ⟨e, he⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 16
    exact ⟨e, he.trans (by decide +kernel)⟩
  have hκ₁ : tripleKind (({3} : Finset (Fin 5)), 1) = 1 := by decide
  have hκs : tripleKind (({0, 1, 2, 3} : Finset (Fin 5)), 2) = 2 := by decide
  have hκg : tripleKind (({0, 1, 2} : Finset (Fin 5)), 3) = 5 := by decide
  set X : Finset (Fin 5) × ℕ := (univ.erase (Fin.last 4), 3) with hX_def
  set Y : Finset (Fin 5) × ℕ := ((univ : Finset (Fin 5)), 3) with hY_def
  have hXne : X.1 ≠ univ := by decide
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  -- Step 1: the prescription `P = (A, ⊤, ⊤)`, lawful below `(C, 3)`.
  set P : Fin F.scheme.card → Label.{u} := fun z ↦
    tripleLabelling A ⊤ ⊤ ⊤ ⊤ (F.scheme.toCellScheme.gradedIndex z) with hP
  have hPe (d : Fin I.amalgam.card) :
      P (F.embed d) = tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d) := by
    simp only [hP, CompletionBelowFullGrade.gradedIndex_embed]
  have hPlaw : F.scheme.rows.IsLawfulBelow X fun z ↦ P z := by
    rw [F.isLawfulBelow_embed_iff hXne]
    simp only [hPe]
    exact (isLawfulBelow_tripleLabelling (I := I) hIL hIR hA (isSelfVisible_top 2)
      (isSelfVisible_top 1) (isSelfVisible_top 2) (isSelfVisible_top 3) le_rfl hAc le_rfl
      le_rfl).1
  -- Step 2: the capped lift `w` of `P` from `(C, 3)` to `(univ, 3)`, agreeing with `q` capped at
  -- `c` (bountifulness of `F`).
  have hXg : X ∈ F.scheme.toCellScheme.gradedFaces := by
    refine ⟨?_, by decide, by decide⟩
    rw [F.faces_eq]
    obtain ⟨hf, -⟩ := (StageType.restrictFace_eq_some_iff _ _).mp I.restrictFace_left
    rw [Coatom.univ_map_left] at hf
    exact hf
  have hYg : Y ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, by decide, by simp [hY_def]⟩
  have hl := F.isLegalBelowFullGrade.isBountiful.cappedLift hXg hYg hXY
  obtain ⟨x', hx'law, hx'c, hx'p⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp hl c hc
    (fun z ↦ P z) (fun z ↦ q z) hPlaw hq (fun z ↦ by
      have hz : (z : Fin F.scheme.card) ∈ F.embed '' I.amalgam.toCellScheme.below X := by
        rw [F.image_embed_below hXne]; exact z.2
      obtain ⟨e, he, hze⟩ := hz
      -- Unfold the restrictions of `q` and `P` to the cells below `X`.
      change min (q z) c = min (P z) c
      rw [← hze, hPe]
      exact hqp e he)
  set w := Rows.extendBot Y x' with hw_def
  have hw : F.scheme.rows.IsLawfulBelow Y fun z ↦ w z := Rows.isLawfulBelow_extendBot.mpr hx'law
  have hwX (z : Fin F.scheme.card) (hz : z ∈ F.scheme.toCellScheme.below X) : w z = P z := by
    rw [hw_def, Rows.extendBot_of_mem x' (F.scheme.toCellScheme.below_mono hXY hz)]
    exact hx'p ⟨z, hz⟩
  have hwc (z : Fin F.scheme.card) (hz : z ∈ F.scheme.toCellScheme.below Y) :
      min (w z) c = min (q z) c := by
    rw [hw_def, Rows.extendBot_of_mem x' hz]
    exact hx'c ⟨z, hz⟩
  -- Step 3: the values of `w` on `C`: `A` at `d₁`, `⊤` at `s_C` and at `g`.
  have hmem (d : Fin I.amalgam.card) {Z : Finset (Fin 5) × ℕ}
      (h : I.amalgam.toCellScheme.gradedIndex d ≤ Z) :
      F.embed d ∈ F.scheme.toCellScheme.below Z := by
    rw [CellScheme.mem_below, CompletionBelowFullGrade.gradedIndex_embed]
    exact h
  have hd₁X := hmem d₁ (Z := X) (by rw [hd₁]; decide +kernel)
  have hsCX := hmem sC (Z := X) (by rw [hsC]; decide +kernel)
  have hgX := hmem gE (Z := X) (by rw [hgE]; decide +kernel)
  have hw₁ : w (F.embed d₁) = A := by
    rw [hwX _ hd₁X, hPe, hd₁]; simp only [tripleLabelling, hκ₁]; rfl
  have hwS : w (F.embed sC) = ⊤ := by
    rw [hwX _ hsCX, hPe, hsC]; simp only [tripleLabelling, hκs]; rfl
  have hwG : w (F.embed gE) = ⊤ := by
    rw [hwX _ hgX, hPe, hgE]; simp only [tripleLabelling, hκg]; rfl
  -- Step 4: on `D`, the coupling `G ≤ A` of `T5` gives `w d₂ = ⊤`.
  set Z : Finset (Fin 5) × ℕ := (univ.erase (Fin.castSucc (Fin.last 3)), 2 + 1) with hZ
  have hZne : Z.1 ≠ univ := by decide
  have hZY : Z ≤ Y := ⟨subset_univ _, le_rfl⟩
  have hwZ : F.scheme.rows.IsLawfulBelow Z fun z ↦ w z := hw.mono hZY
  have hwZ' := (F.isLawfulBelow_embed_iff hZne).mp hwZ
  have hD := le_of_isLawfulBelow_right hIR (w := fun d ↦ w (F.embed d)) hwZ' hd₂ hgE
  have hw₂ : w (F.embed d₂) = ⊤ := top_le_iff.mp (hwG ▸ hD)
  -- Step 5: an old cell `s` of grade `k` where `w` is `⊤`: `d₂`, `s_C` or `g`.
  have hgr (d : Fin I.amalgam.card) {W : Finset (Fin 5) × ℕ}
      (h : I.amalgam.toCellScheme.gradedIndex d = W) :
      F.scheme.toCellScheme.grade (F.embed d) = W.2 :=
    (congrArg Prod.snd (F.gradedIndex_embed d)).trans (congrArg Prod.snd h)
  obtain ⟨s, hgs, hws⟩ : ∃ s : Fin I.amalgam.card,
      F.scheme.toCellScheme.grade (F.embed s) = k ∧ w (F.embed s) = ⊤ := by
    obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact ⟨d₂, hgr d₂ hd₂, hw₂⟩
    · exact ⟨sC, hgr sC hsC, hwS⟩
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
  refine ⟨u, hu', ?_, fun h₁ h₂ ↦ ?_⟩
  · -- Step 7: `w u = ⊤` and `w` agrees with `q` capped at `c`, so `c ≤ q u`.
    have := hwc u huY
    rw [hwu, min_top_left] at this
    exact min_eq_right_iff.mp this.symm
  · -- Step 8: locality at `u`: reading `d₂` at most `d₁` would give `⊤ = w d₂ ≤ w d₁ = A`.
    by_contra hcon
    rw [not_lt] at hcon
    have h21 := (hloc u huY).le_of_le (d := ⟨_, h₂⟩) (d' := ⟨_, h₁⟩) hcon
      (by simp only [hgr d₁ hd₁, hgr d₂ hd₂, le_refl])
    simp only at h21
    rw [hw₂, hw₁, hwu, min_top_right, min_top_right] at h21
    exact hAtop (top_le_iff.mp h21)

/-- **The necessary condition at `(univ, 2)`**: the case `k = 2` of
`exists_separating_cell_of_le_three`. -/
theorem exists_separating_cell {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) (F : CompletionBelowFullGrade I)
    {c : Label.{u}} (hc : IsSelfVisible 3 c) {A : Label.{u}} (hA : IsSelfVisible 1 A)
    (hAc : VisibilityReplaceFixedOfLT A ⊤) (hAtop : A ≠ ⊤) {q : Fin F.scheme.card → Label.{u}}
    (hq : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin 5)), 3) fun z ↦ q z)
    (hqp : ∀ d : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex d ≤ (univ.erase (Fin.last 4), 3) →
      min (q (F.embed d)) c =
        min (tripleLabelling A ⊤ ⊤ ⊤ ⊤ (I.amalgam.toCellScheme.gradedIndex d)) c)
    {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1))
    (hd₂ : I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1)) :
    ∃ u : Fin F.scheme.card, F.scheme.toCellScheme.gradedIndex u = (univ, 2) ∧ c ≤ q u ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ :=
  exists_separating_cell_of_le_three hIL hIR F one_le_two (by omega) hc hA hAc hAtop hq hqp hd₁
    hd₂

/-- **Every completion of the asymmetric seed has a separating cell at each `(univ, k)`,
`1 ≤ k ≤ 3`**: a cell whose row reads `({3}, 1)` strictly below `({4}, 1)`.  (The case `c = ⊥`,
`q = ⊥`, `A = 1` of `exists_separating_cell_of_le_three`.) -/
theorem exists_separating_cell_of_completion_of_le_three {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) (F : CompletionBelowFullGrade I) {k : ℕ}
    (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3) :
    ∃ (d₁ d₂ : Fin I.amalgam.card) (u : Fin F.scheme.card),
      I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, k) ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ := by
  obtain ⟨d₁, hd₁⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({3} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := exists_cell_TL (hIL ▸ I.restrictFace_left) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨d₂, hd₂⟩ : ∃ e : Fin I.amalgam.card,
      I.amalgam.toCellScheme.gradedIndex e = (({4} : Finset (Fin 5)), 1) := by
    obtain ⟨e, he⟩ := CaseSplitCounterexample.exists_cell (hIR ▸ I.restrictFace_right) 3
    exact ⟨e, he.trans (by decide +kernel)⟩
  obtain ⟨u, hu, -, hsep⟩ := exists_separating_cell_of_le_three hIL hIR F hk₁ hk₃ (c := ⊥)
    (isSelfVisible_bot 3) (A := TwoFaceLiftCounterexample.v1) (isSelfVisible_gridPoint 1 0)
    (fun _ ↦ by rw [TwoFaceLiftCounterexample.v1_eq, Label.visibilityReplace_natCast]; simp)
    (gridPoint_ne_top 1 0) (q := fun _ ↦ ⊥) (Rows.isLawfulBelow_const_bot _)
    (fun _ _ ↦ by simp) hd₁ hd₂
  exact ⟨d₁, d₂, u, hd₁, hd₂, hu, hsep⟩

/-- **Every completion of the asymmetric seed has a separating cell at `(univ, 2)`**: a cell whose
row reads `({3}, 1)` strictly below `({4}, 1)`.  (The case `k = 2` of
`exists_separating_cell_of_completion_of_le_three`.) -/
theorem exists_separating_cell_of_completion {I : Seed.{u} α 3} (hIL : I.left = TL α)
    (hIR : I.right = CaseSplitCounterexample.T5 α) (F : CompletionBelowFullGrade I) :
    ∃ (d₁ d₂ : Fin I.amalgam.card) (u : Fin F.scheme.card),
      I.amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      I.amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, 2) ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ :=
  exists_separating_cell_of_completion_of_le_three hIL hIR F one_le_two (by omega)

/-- **For the asymmetric seed `seedL`**, at each `(univ, k)`, `1 ≤ k ≤ 3`. -/
theorem exists_separating_cell_seedL_of_le_three (F : CompletionBelowFullGrade (seedL α)) {k : ℕ}
    (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3) :
    ∃ (d₁ d₂ : Fin (seedL α).amalgam.card) (u : Fin F.scheme.card),
      (seedL α).amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      (seedL α).amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, k) ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ :=
  exists_separating_cell_of_completion_of_le_three rfl rfl F hk₁ hk₃

/-- **For the asymmetric seed `seedL`**, at `(univ, 2)`. -/
theorem exists_separating_cell_seedL (F : CompletionBelowFullGrade (seedL α)) :
    ∃ (d₁ d₂ : Fin (seedL α).amalgam.card) (u : Fin F.scheme.card),
      (seedL α).amalgam.toCellScheme.gradedIndex d₁ = (({3} : Finset (Fin 5)), 1) ∧
      (seedL α).amalgam.toCellScheme.gradedIndex d₂ = (({4} : Finset (Fin 5)), 1) ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, 2) ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ :=
  exists_separating_cell_of_completion rfl rfl F

end Separation

/-- **No collision at a separating cell of a completion.**  If the row of a cell `u` of a
completion at `(univ, 2)` reads `d₁` strictly below `d₂`, every labelling lawful below
`(univ, 2)` that carries one label `e` of finite part `1` (not self-visible at `2`) at `d₁` and
`d₂` has `x u ≤ e`. -/
theorem le_of_separating {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}
    (F : CompletionBelowFullGrade I) {u : Fin F.scheme.card}
    (hu : F.scheme.toCellScheme.gradedIndex u = (univ, 2)) {d₁ d₂ : Fin I.amalgam.card}
    (hg₁ : I.amalgam.toCellScheme.grade d₁ = 1) (hg₂ : I.amalgam.toCellScheme.grade d₂ = 1)
    (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
    (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
    (hsep : F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩)
    {x : Fin F.scheme.card → Label.{u}}
    (hx : F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), 2) fun z ↦ x z)
    {e : Label.{u}} (hx₁ : x (F.embed d₁) = e) (hx₂ : x (F.embed d₂) = e)
    (hev : ¬ IsSelfVisible 2 e) : x u ≤ e := by
  by_contra hlt
  rw [not_le] at hlt
  have huY : u ∈ F.scheme.toCellScheme.below ((univ : Finset (Fin (m + 2))), 2) := by
    rw [CellScheme.mem_below, hu]
  have hloc := (Rows.isLawfulBelow_iff_forall.mp hx).2.1 u huY
  have hG₁ : F.scheme.toCellScheme.grade (F.embed d₁) = 1 :=
    (F.isLowerEmbedding.grade_eq d₁).trans hg₁
  have hG₂ : F.scheme.toCellScheme.grade (F.embed d₂) = 1 :=
    (F.isLowerEmbedding.grade_eq d₂).trans hg₂
  have hor := F.isLegalBelowFullGrade.isConsistent.isOrderly u
  have heq := eq_of_transformsTo_collision hloc (d₁ := ⟨_, h₁⟩) (d₂ := ⟨_, h₂⟩)
    (z := ⟨u, F.scheme.toCellScheme.mem_below_gradedIndex u⟩) hG₁ hG₂
    (congrArg Prod.snd hu) (hG₁ ▸ hor ⟨_, h₁⟩) (hG₂ ▸ hor ⟨_, h₂⟩)
    (by simp only; rw [hx₁, min_eq_left hlt.le]) (by simp only; rw [hx₂, min_eq_left hlt.le])
    hev (by simp only [min_self]; exact hlt)
  exact absurd heq hsep.ne

end VaughtConjecture.ThinCompletion
