/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.OrderedLayerStep

/-!
# Forced separations, and the obstruction to the ordered-layer step

Roadmap, Layer 3, 3.1, (R6), checkpoint 2.7 (the completion below the full grade: a necessary
condition on every completion of a seed, and the obstruction it gives to the ordered-layer step
at `m = 3`); semantic contract, items 2–4.

**Forcing through the common face** (`Seed.ForcesTop`).  Let `I` be a seed, `X₁`, `X₂` two pairs,
`P` a labelling of the amalgam lawful below `X₁` and `d₂` a cell.  `P` *forces `⊤` at `d₂` below
`X₂`* when every labelling lawful below `X₂` that equals `P` at the cells below both `X₁` and `X₂`
is `⊤` at `d₂`.  For a seed whose coatom types are `TL` and `T5`, the prescription
`(A_C, F_C, G) = (A, ⊤, ⊤)` below `(C, 3)` forces `⊤` at `({4}, 1)` below `(D, 3)`, through the
coupling `G ≤ A_D` of `T5` (`TwoFaceLiftExistsCounterexample.le_of_isLawfulBelow_right`).

**The forced separation** (`CompletionBelowFullGrade.exists_separating_of_forcesTop`).  If `P` is
lawful below `(B₁, k)`, a cell `d₁` below `(B₁, k)` carries `P d₁ ≠ ⊤`, and `P` forces `⊤` at a cell
`d₂` below `(B₂, k)` with `grade d₁ ≤ grade d₂`, then every completion below the full grade has a
cell `u` at `(univ, grade d₂)` whose row reads `d₁` strictly below `d₂`: bountifulness lifts `P`
into `(univ, k)`, the lift is `⊤` at `d₂` by the forcing, availability from `d₂` gives `u` with
label `⊤`, and locality at `u` excludes reading `d₂` at most `d₁`.  This is the argument of the
separating cell (`VaughtConjecture.Extension.SeparatingCell`), for an arbitrary seed and an
arbitrary forcing.

**Two opposite forcings** (`CompletionBelowFullGrade.exists_ne_of_forcesTop`).  If, at one grade,
`d₁` is forced against `d₂` from the first side and `d₂` against `d₁` from the second side, every
completion has two different cells at `(univ, grade d₂)`, one reading `d₁` below `d₂` and one
reading `d₂` below `d₁`.

**The obstruction to the ordered-layer step** (`Seed.not_hasOrderedLayerStep_of_forcesTop`).  The
layer scheme has one cell at each graded face of full scope, so a seed on five points with two
opposite forcings between a cell of the first coatom and a cell of the second at one grade has no
ordered-layer step, for any layer rows.  Every completion of such a seed, if one exists, has
several new cells at one graded face of full scope, one for each orientation.  None of the seeds
`seed4`, `seed5`, `seedL` has two opposite forcings at one grade, since each has an ordered-layer
step (`VaughtConjecture.Extension.OrderedLayerExamples`).  The legal seed
`CrossedCouplingCounterexample.seedHG` has two opposite forcings at the grade `1`, so it has no
ordered-layer step (`CrossedCouplingCounterexample.not_hasOrderedLayerStep_seedHG`, module
`VaughtConjecture.Extension.CrossedCouplingCounterexample`): its two coatom types are coupled
crosswise to two parameters of the common face, at the grades `2` and `3`.  It has a completion
below the full grade with two new cells at `(univ, 1)`, one for each forced separation
(`CrossedCouplingCounterexample.nonempty_completionBelowFullGrade_seedHG`, module
`VaughtConjecture.Extension.CrossedCouplingCompletion`).  Two opposite forcings
at one grade need two such parameters (argued, not formalized): a lawful labelling capped at a cap
self-visible at every grade stays lawful, so a forcing is a lower bound by parameters of the common
face, and within one coatom type the cell of full scope at the grade `1` orders all the cells of the
grade `1`.

## Placement

Checkpoint 2.7 of the completion of the coatom extension construction (`roadmap/README.md`,
Layer 3, 3.1, under "(R6)").
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace Seed

variable {α : Ordinal.{u}} {m : ℕ} (I : Seed.{u} α m)

/-- A labelling `P` of the amalgam **forces `⊤` at `d₂` below `X₂`** from `X₁`: every labelling
lawful below `X₂` that equals `P` at the cells below both `X₁` and `X₂` is `⊤` at `d₂`. -/
def ForcesTop (X₁ X₂ : Finset (Fin (m + 2)) × ℕ) (P : Fin I.amalgam.card → Label.{u})
    (d₂ : Fin I.amalgam.card) : Prop :=
  ∀ w : Fin I.amalgam.card → Label.{u}, I.amalgam.rows.IsLawfulBelow X₂ (fun d ↦ w d) →
    (∀ d ∈ I.amalgam.toCellScheme.below X₁, d ∈ I.amalgam.toCellScheme.below X₂ → w d = P d) →
    w d₂ = ⊤

end Seed

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)

open Classical in
/-- The extension of a labelling of the amalgam to the cells of a completion: the label of the
old cell, and `⊥` at the new cells. -/
private noncomputable def extendOld (P : Fin I.amalgam.card → Label.{u}) (z : Fin F.scheme.card) :
    Label.{u} :=
  if h : ∃ d, F.embed d = z then P h.choose else ⊥

/-- The extension of a labelling to the cells of a completion is the labelling at the old cells. -/
private theorem extendOld_embed (P : Fin I.amalgam.card → Label.{u}) (d : Fin I.amalgam.card) :
    F.extendOld P (F.embed d) = P d := by
  have h : ∃ d', F.embed d' = F.embed d := ⟨d, rfl⟩
  rw [extendOld, dite_eq_left h, F.embed.injective h.choose_spec]

/-- **The forced separation.**  Let `P` be lawful below `(B₁, k)` in the amalgam, `d₁` a cell below
`(B₁, k)` with `P d₁ ≠ ⊤`, and let `P` force `⊤` at a cell `d₂` below `(B₂, k)` with
`grade d₁ ≤ grade d₂`.  Then every completion below the full grade has a cell `u` at
`(univ, grade d₂)` whose row reads `d₁` strictly below `d₂`. -/
theorem exists_separating_of_forcesTop {B₁ B₂ : Finset (Fin (m + 2))} {k : ℕ} (hB₁ : B₁ ≠ univ)
    (hB₂ : B₂ ≠ univ) (hX₁ : (B₁, k) ∈ I.amalgam.toCellScheme.gradedFaces)
    {P : Fin I.amalgam.card → Label.{u}}
    (hP : I.amalgam.rows.IsLawfulBelow (B₁, k) (fun d ↦ P d)) {d₁ d₂ : Fin I.amalgam.card}
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (B₁, k))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (B₂, k))
    (hg : I.amalgam.toCellScheme.grade d₁ ≤ I.amalgam.toCellScheme.grade d₂) (hP₁ : P d₁ ≠ ⊤)
    (hforce : I.ForcesTop (B₁, k) (B₂, k) P d₂) :
    ∃ u : Fin F.scheme.card,
      F.scheme.toCellScheme.gradedIndex u = (univ, I.amalgam.toCellScheme.grade d₂) ∧
      ∀ (h₁ : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u))
        (h₂ : F.embed d₂ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u)),
        F.scheme.rows.row u ⟨_, h₁⟩ < F.scheme.rows.row u ⟨_, h₂⟩ := by
  -- Step 0: the pairs `X = (B₁, k)` and `Y = (univ, k)`, graded faces of the completion.
  set X : Finset (Fin (m + 2)) × ℕ := (B₁, k) with hX_def
  set Y : Finset (Fin (m + 2)) × ℕ := ((univ : Finset (Fin (m + 2))), k) with hY_def
  have hXY : X ≤ Y := ⟨subset_univ _, le_rfl⟩
  have hk1 : 0 < k := hX₁.2.1
  have hXg : X ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨by rw [F.faces_eq]; exact hX₁.1, hX₁.2.1, hX₁.2.2⟩
  have hYg : Y ∈ F.scheme.toCellScheme.gradedFaces :=
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces, hk1,
      (hX₁.2.2.trans (card_le_univ _)).trans_eq (by simp [hY_def])⟩
  -- Step 1: the prescription, extended to the cells of the completion, is lawful below `X`.
  set w₀ := F.extendOld P with hw₀
  have hw₀X : F.scheme.rows.IsLawfulBelow X fun z ↦ w₀ z := by
    rw [F.isLawfulBelow_embed_iff hB₁]
    simpa only [hw₀, extendOld_embed] using hP
  -- Step 2: the capped lift at the cap `⊥` with the ambient `⊥` gives `x`, lawful below `Y` and
  -- equal to the prescription below `X`.
  obtain ⟨x', hx'law, -, hx'p⟩ := (Rows.cappedLift_iff_forall_exists hXY).mp
    (F.isLegalBelowFullGrade.isBountiful.cappedLift hXg hYg hXY) ⊥ (isSelfVisible_bot _)
    (fun z ↦ w₀ z) (fun _ ↦ ⊥) hw₀X (Rows.isLawfulBelow_const_bot _) fun _ ↦ by simp
  set x := Rows.extendBot Y x' with hx_def
  have hx : F.scheme.rows.IsLawfulBelow Y fun z ↦ x z := Rows.isLawfulBelow_extendBot.mpr hx'law
  have hxX (z : Fin F.scheme.card) (hz : z ∈ F.scheme.toCellScheme.below X) : x z = w₀ z := by
    rw [hx_def, Rows.extendBot_of_mem x' (F.scheme.toCellScheme.below_mono hXY hz)]
    exact hx'p ⟨z, hz⟩
  have hmem (d : Fin I.amalgam.card) {Z : Finset (Fin (m + 2)) × ℕ}
      (h : d ∈ I.amalgam.toCellScheme.below Z) : F.embed d ∈ F.scheme.toCellScheme.below Z := by
    rw [CellScheme.mem_below, gradedIndex_embed]; exact h
  have hx₁ : x (F.embed d₁) = P d₁ := by rw [hxX _ (hmem d₁ hd₁), hw₀, extendOld_embed]
  -- Step 3: on `(B₂, k)`, `x` is lawful in the amalgam and equals `P` on the common cells; the
  -- forcing gives `x d₂ = ⊤`.
  have hx₂ : x (F.embed d₂) = ⊤ := by
    have hxD : F.scheme.rows.IsLawfulBelow (B₂, k) fun z ↦ x z :=
      hx.mono (X := (B₂, k)) ⟨subset_univ _, le_rfl⟩
    refine hforce (fun d ↦ x (F.embed d)) ((F.isLawfulBelow_embed_iff hB₂).mp hxD) fun d hd _ ↦ ?_
    rw [hxX _ (hmem d hd), hw₀, extendOld_embed]
  -- Step 4: availability from `d₂` gives a cell `u` at `(univ, grade d₂)` with `x u = ⊤`.
  set j := I.amalgam.toCellScheme.grade d₂ with hj
  have hgd₂ : F.scheme.toCellScheme.grade (F.embed d₂) = j := F.isLowerEmbedding.grade_eq d₂
  have hjk : j ≤ k := hd₂.2
  obtain ⟨t0, ht0⟩ := F.isLegalBelowFullGrade.exists_gradedIndex_eq
    ((univ : Finset (Fin (m + 2))), j)
    ⟨F.isLegalBelowFullGrade.isWellFormed.univ_mem_faces,
      hgd₂ ▸ F.isLegalBelowFullGrade.isWellFormed.isWellFormed.grade_pos _,
      (hjk.trans (hX₁.2.2.trans (card_le_univ _))).trans_eq (by simp)⟩ (I.grade_lt d₂)
  have ht0Y : t0 ∈ F.scheme.toCellScheme.below Y := by
    rw [CellScheme.mem_below, ht0]; exact ⟨subset_rfl, hjk⟩
  obtain ⟨-, hloc, havail⟩ := Rows.isLawfulBelow_iff_forall.mp hx
  obtain ⟨u, hu, hle⟩ := havail (F.embed d₂) t0 ht0Y
    (by rw [show F.scheme.toCellScheme.scope t0 = univ from congrArg Prod.fst ht0]
        exact subset_univ _)
    (by rw [hgd₂]; exact (congrArg Prod.snd ht0).symm)
  have hu' : F.scheme.toCellScheme.gradedIndex u = (univ, j) := hu.trans ht0
  have huY : u ∈ F.scheme.toCellScheme.below Y := by
    rw [CellScheme.mem_below, hu']; exact ⟨subset_rfl, hjk⟩
  have hxu : x u = ⊤ := top_le_iff.mp (hx₂ ▸ hle)
  refine ⟨u, hu', fun h₁ h₂ ↦ ?_⟩
  -- Step 5: locality at `u`: reading `d₂` at most `d₁` would give `⊤ = x d₂ ≤ x d₁ = P d₁`.
  by_contra hcon
  rw [not_lt] at hcon
  have h21 := (hloc u huY).le_of_le (d := ⟨_, h₂⟩) (d' := ⟨_, h₁⟩) hcon
    (by
      -- The grades of the embedded cells, which the embedding preserves.
      change F.scheme.toCellScheme.grade (F.embed d₁) ≤ F.scheme.toCellScheme.grade (F.embed d₂)
      rw [F.isLowerEmbedding.grade_eq, F.isLowerEmbedding.grade_eq]; exact hg)
  simp only at h21
  rw [hx₂, hx₁, hxu, min_top_right, min_top_right] at h21
  exact hP₁ (top_le_iff.mp h21)

/-- **Two opposite forcings give two cells.**  If, at one grade, `P` forces `d₁` against `d₂` from
`(B₁, k)` and `P'` forces `d₂` against `d₁` from `(B₂, k')`, every completion below the full grade
has two different cells at `(univ, grade d₂)`, one reading `d₁` strictly below `d₂` and one
reading `d₂` strictly below `d₁`. -/
theorem exists_ne_of_forcesTop {B₁ B₂ : Finset (Fin (m + 2))} {k k' : ℕ} (hB₁ : B₁ ≠ univ)
    (hB₂ : B₂ ≠ univ) (hX₁ : (B₁, k) ∈ I.amalgam.toCellScheme.gradedFaces)
    (hX₂ : (B₂, k') ∈ I.amalgam.toCellScheme.gradedFaces)
    {P P' : Fin I.amalgam.card → Label.{u}} {d₁ d₂ : Fin I.amalgam.card}
    (hP : I.amalgam.rows.IsLawfulBelow (B₁, k) (fun d ↦ P d))
    (hP' : I.amalgam.rows.IsLawfulBelow (B₂, k') (fun d ↦ P' d))
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (B₁, k))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (B₂, k))
    (hd₁' : d₁ ∈ I.amalgam.toCellScheme.below (B₁, k'))
    (hd₂' : d₂ ∈ I.amalgam.toCellScheme.below (B₂, k'))
    (hg : I.amalgam.toCellScheme.grade d₁ = I.amalgam.toCellScheme.grade d₂)
    (hP₁ : P d₁ ≠ ⊤) (hP₂ : P' d₂ ≠ ⊤)
    (hforce : I.ForcesTop (B₁, k) (B₂, k) P d₂) (hforce' : I.ForcesTop (B₂, k') (B₁, k') P' d₁) :
    ∃ u u' : Fin F.scheme.card, u ≠ u' ∧
      F.scheme.toCellScheme.gradedIndex u = (univ, I.amalgam.toCellScheme.grade d₂) ∧
      F.scheme.toCellScheme.gradedIndex u' = (univ, I.amalgam.toCellScheme.grade d₂) := by
  obtain ⟨u, hu, hsep⟩ := F.exists_separating_of_forcesTop hB₁ hB₂ hX₁ hP hd₁ hd₂ hg.le hP₁ hforce
  obtain ⟨u', hu', hsep'⟩ :=
    F.exists_separating_of_forcesTop hB₂ hB₁ hX₂ hP' hd₂' hd₁' hg.ge hP₂ hforce'
  rw [hg] at hu'
  refine ⟨u, u', fun h ↦ ?_, hu, hu'⟩
  subst h
  have hmem (d : Fin I.amalgam.card) (hd : I.amalgam.toCellScheme.grade d ≤
      I.amalgam.toCellScheme.grade d₂) :
      F.embed d ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, gradedIndex_embed, hu]
    exact ⟨subset_univ _, hd⟩
  have h₁ := hmem d₁ hg.le
  have h₂ := hmem d₂ le_rfl
  have h₁' : F.embed d₁ ∈ F.scheme.toCellScheme.below (F.scheme.toCellScheme.gradedIndex u) := h₁
  exact lt_asymm (hsep h₁ h₂) (hsep' h₂ h₁')

end CompletionBelowFullGrade

namespace Seed

open OrderedLayer

variable {α : Ordinal.{u}} {I : Seed.{u} α 3}

/-- **The obstruction to the ordered-layer step.**  A seed on five points with two opposite
forcings at one grade, from the first coatom against a cell of the second and from the second
against a cell of the first, has no ordered-layer step, for any layer rows: the layer scheme has
only one cell at each graded face of full scope. -/
theorem not_hasOrderedLayerStep_of_forcesTop {k k' : ℕ}
    (hX₁ : (coatomC, k) ∈ I.amalgam.toCellScheme.gradedFaces)
    (hX₂ : (coatomD, k') ∈ I.amalgam.toCellScheme.gradedFaces)
    {P P' : Fin I.amalgam.card → Label.{u}} {d₁ d₂ : Fin I.amalgam.card}
    (hP : I.amalgam.rows.IsLawfulBelow (coatomC, k) (fun d ↦ P d))
    (hP' : I.amalgam.rows.IsLawfulBelow (coatomD, k') (fun d ↦ P' d))
    (hd₁ : d₁ ∈ I.amalgam.toCellScheme.below (coatomC, k))
    (hd₂ : d₂ ∈ I.amalgam.toCellScheme.below (coatomD, k))
    (hd₁' : d₁ ∈ I.amalgam.toCellScheme.below (coatomC, k'))
    (hd₂' : d₂ ∈ I.amalgam.toCellScheme.below (coatomD, k'))
    (hg : I.amalgam.toCellScheme.grade d₁ = I.amalgam.toCellScheme.grade d₂)
    (hP₁ : P d₁ ≠ ⊤) (hP₂ : P' d₂ ≠ ⊤)
    (hforce : I.ForcesTop (coatomC, k) (coatomD, k) P d₂)
    (hforce' : I.ForcesTop (coatomD, k') (coatomC, k') P' d₁) : ¬ I.HasOrderedLayerStep := by
  rintro ⟨ρ, h⟩
  obtain ⟨u, u', hne, hu, hu'⟩ := h.completion.exists_ne_of_forcesTop (by decide) (by decide) hX₁
    hX₂ hP hP' hd₁ hd₂ hd₁' hd₂' hg hP₁ hP₂ hforce hforce'
  have hj1 : 1 ≤ I.amalgam.toCellScheme.grade d₂ :=
    I.amalgam.isWellFormed.isWellFormed.grade_pos d₂
  have hj4 : I.amalgam.toCellScheme.grade d₂ ≤ 4 := Nat.lt_succ_iff.mp (I.grade_lt d₂)
  exact hne ((eq_newCell (ρ := ρ) hj1 hj4 hu).trans (eq_newCell hj1 hj4 hu').symm)

end Seed

end VaughtConjecture
