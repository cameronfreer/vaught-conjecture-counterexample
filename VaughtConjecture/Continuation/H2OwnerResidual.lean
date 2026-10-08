/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.H2OwnerGeneral

/-!
# The residual of owner lowering below the designated tops at grade `2` (work file)

WORK FILE (branch `research/work-owner-general`).  No `sorry`.

General-arity owner lowering below the designated tops (`H2.ownerLoweringBelow_of_topsAtLeastGrade`)
assumes the named condition `H2.TopsAtLeastGrade`; two-point owner lowering is unconditional
(`H2.ownerLoweringBelowAt_one`).  This file treats the residual of the named condition at grade
`2`: a designated top `t` with `⊥ < g t < 2` at a cap `⊥` and a low maximum `⊥`.

* **The mechanism** (`H2.eq_bot_of_reading_one_three`): a row reading a cell at `1` and a cell of no
  smaller grade at `3` transforms the first to `⊥` only if it transforms the second to `⊥`.
* **The conditional refutation** (`H2.not_ownerLoweringBelow_of_reading`): at a source-gap context
  of grade `2` with the lost point last, whose owner is alone at its graded index and reads the
  lost top at `1` and a root top of grade `2` at `3`, owner lowering below the designated tops fails
  for every donor face with such a designated top and a root top value above `⊥`.  A legal context
  meeting these hypotheses is described in `VaughtConjecture.Continuation.H2OwnerResidualInstance`
  (argued; its legality is not compiled).  What is refuted is the owner-lowering input of the
  clause at such a context, not the coatom statement.
-/

universe u

namespace VaughtConjecture.H2

open Finset Label StageType FieldAdmission CellScheme

/-- **A reading at `1` sent to `⊥` sends a reading at `3` to `⊥`**: if a row transforms to `q`,
reads a cell `d` at `1` and a cell `d'` of grade at least that of `d` at `3`, and `q d = ⊥`, then
`q d' = ⊥`.  Either the shifter sends `1` to `⊥`, and then (replacement at the threshold `4` with
value `3`, the shifter being `⊥` at `1`) it sends `3` to `⊥`; or the suppressor vanishes at the
grade of `d`, hence at that of `d'`. -/
theorem eq_bot_of_reading_one_three {D : Type*} {grade : D → ℕ} {p q : D → Label.{u}}
    (h : TransformsTo grade p q) {d d' : D} (hd : p d = 1) (hd' : p d' = ((3 : ℕ) : Label.{u}))
    (hg : grade d ≤ grade d') (hq : q d = ⊥) : q d' = ⊥ := by
  obtain ⟨g, σ, hw, heq⟩ := h
  rw [heq, hd] at hq
  rw [heq, hd']
  rcases min_eq_bot.mp hq with h1 | h1
  · have hc := hw.visibilityReplace_comm 1 4 (by rw [h1]; exact bot_le) 3 (by omega)
    have h13 : visibilityReplace 4 3 (1 : Label.{u}) = ((3 : ℕ) : Label.{u}) := by
      rw [visibilityReplace_one]
      simp
    rw [h13, h1, visibilityReplace_bot] at hc
    rw [hc]
    exact min_eq_left bot_le
  · exact le_bot_iff.mp ((min_le_right _ _).trans (h1 ▸ hw.antitone hg))

variable {α : Ordinal.{u}}

/-- **Owner lowering below the designated tops fails at grade `2` under a reading of the lost top
at `1` and of a root top at `3`**: at a source-gap context of grade `2` on `k + 1` points with the
lost point last, whose owner is the only cell of its graded index and reads the lost top at `1`
and a root cell `a` of grade `2` at `3`, for a donor face `g` on the grade-`2` faces with a
designated top `t` with `⊥ < g t < 2`, designated cells below the top of replaced maximum `⊥`, and
`g` above `⊥` at the root cell `a`.  At the cap `⊥`, a lowered face has the value of `g` at `a`,
so (availability) the owner is above `⊥`; the lost top is then above `⊥`
(`H2.eq_bot_of_reading_one_three` at the owner); both are self-visible at `2` after replacement,
so the frontier is at least `2`, above `g t`. -/
theorem not_ownerLoweringBelow_of_reading {k n : ℕ} {t' : StageType.{u} α (k + 1)}
    {g₀ : Fin n ↪ Fin k} {o r : Fin t'.card}
    (hs : t'.IsSourceGapContextAt 2 (g₀.trans Fin.castSuccEmb) (Fin.last k) o r)
    (honly : ∀ u, t'.toCellScheme.gradedIndex u = t'.toCellScheme.gradedIndex o → u = o)
    {p : StageType.{u} α k} (hp : restrictFace Fin.castSuccEmb t' = some p) {a : Fin p.card}
    (ha2 : t'.toCellScheme.grade (StageType.faceCell hp a) = 2) (hro : t'.rowAt o r = 1)
    (hao : t'.rowAt o (StageType.faceCell hp a) = ((3 : ℕ) : Label.{u}))
    {tb : StageType.{u} α (k + 1)} (htbp : restrictFace Fin.castSuccEmb tb = some p)
    {Lo Tops : Finset (Fin tb.card)} {g : Fin tb.card → Label.{u}} (hg : LawfulAt tb 2 g)
    {t : Fin tb.card} (ht : t ∈ Tops) (hgt0 : ⊥ < g t) (hgt : g t < ((2 : ℕ) : Label.{u}))
    (hLo : visibilityReplace 2 2 (Lo.sup g) = ⊥) (hga : ⊥ < g (StageType.faceCell htbp a)) :
    ¬ OwnerLoweringBelow (StageType.faceCell hp) (StageType.faceCell htbp) o r 2
      (LawfulAt t' 2) (LawfulAt tb 2) Lo Tops := by
  intro hOL
  have hL : LawfulAt t' 2 (fun _ ↦ ⊥) :=
    ⟨Rows.isLawfulBelow_const_bot _, fun _ _ ↦ rfl⟩
  obtain ⟨W, hW, hWr, -, hWF⟩ := hOL (isSelfVisible_bot 2) hL hg (fun x ↦ by simp)
  have hF := hWF t ht bot_le (by rw [hLo]; exact hgt0)
  set a' := StageType.faceCell hp a with ha'
  have hWa : W a' = g (StageType.faceCell htbp a) := hWr a
  have hgi : t'.toCellScheme.gradedIndex o = ((univ : Finset (Fin (k + 1))), 2) :=
    Prod.ext hs.scope_owner hs.grade_owner
  have hWX : t'.rows.IsLawfulBelow (t'.toCellScheme.gradedIndex o) (fun d ↦ W d) := by
    rw [hgi]; exact hW.1
  obtain ⟨hWo, hWl, hWav⟩ := Rows.isLawfulBelow_iff_forall.mp hWX
  have hoX : o ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) :=
    t'.toCellScheme.mem_below_gradedIndex o
  have hr2 : t'.toCellScheme.grade r ≤ 2 := hs.topGrade_eq ▸ grade_le_topGrade hs.label_lost
  have hrX : r ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) := by
    rw [hgi]; exact ⟨subset_univ _, hr2⟩
  have haX : a' ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex o) := by
    rw [hgi]; exact ⟨subset_univ _, ha2.le⟩
  -- the owner serves the root cell `a`
  obtain ⟨u, hu, hle⟩ := hWav a' o hoX (by rw [hs.scope_owner]; exact subset_univ _)
    (ha2.trans hs.grade_owner.symm)
  rw [honly u hu] at hle
  have hWo0 : ⊥ < W o := (hWa ▸ hga).trans_le hle
  -- the lost top is above `⊥`
  have hWr0 : ⊥ < W r := by
    by_contra h0
    have h0' : W r = ⊥ := le_bot_iff.mp (not_lt.mp h0)
    have hq := eq_bot_of_reading_one_three (hWl o hoX) (d := ⟨r, hrX⟩) (d' := ⟨a', haX⟩)
      (by rw [← Scheme.rowAt_of_mem hrX]; exact hro)
      (by rw [← Scheme.rowAt_of_mem haX]; exact hao)
      (show t'.toCellScheme.grade r ≤ t'.toCellScheme.grade a' by rw [ha2]; exact hr2)
      (show min (W r) (W o) = ⊥ by rw [h0']; exact min_eq_left bot_le)
    change min (W a') (W o) = ⊥ at hq
    rcases min_eq_bot.mp hq with h1 | h1
    · exact (hWa ▸ hga).ne' h1
    · exact hWo0.ne' h1
  -- the frontier is at least `2`
  have hWo2 : ((2 : ℕ) : Label.{u}) ≤ W o := by
    have := hWo o hoX
    rw [hs.grade_owner] at this
    exact natCast_le_of_isSelfVisible this hWo0
  have hWr2 : ((2 : ℕ) : Label.{u}) ≤ visibilityReplace 2 2 (W r) :=
    natCast_le_of_isSelfVisible (visibilityReplace_self_visibilityReplace le_rfl _)
      (hWr0.trans_le (le_visibilityReplace (by omega) _))
  exact absurd ((le_min hWo2 hWr2).trans hF) (not_le.mpr hgt)

end VaughtConjecture.H2
