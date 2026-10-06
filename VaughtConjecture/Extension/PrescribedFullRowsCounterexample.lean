/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Tactic.FinCases
import VaughtConjecture.Extension.PrescribedFullRows
import VaughtConjecture.Extension.GatedExtensionCounterexample

/-!
# Prescribed rows consistent at the labels fail at `P α`

Roadmap, Layer 3, 3.4 (the common shape of the finite hypotheses of the receiving rows);
`VaughtConjecture.Extension.PrescribedFullRows`.

**The input.**  The context is the private type `P α` of
`VaughtConjecture.Extension.GatedExtensionCounterexample` (two points; three dead cells of grade
`1`; the cells `C₁`, `C₂` of graded index `(univ, 2)`, labelled `⊤`), with the empty root and the
legal one-point donor of the one-point scheme.  The rows of `P` carry the lawful labellings `3, 2`
and `2, 3` of `C₁, C₂`.

**The prescription** (`prescription`): every cell of graded index `(univ, 2)` reads `C₂` at least as
`C₁`, the reading of the private top in the reading condition of (R2) and (R3).

* It is consistent with the faces at their labels (`isFaceConsistentAtLabels`): at the grade `2`
  the row of `C₂` reads `C₂` at least as `C₁` (`rowAt_cellB_le`, from locality of the labelling
  `2, 3`), and locality of the labels `⊤, ⊤` at `C₂` gives the transformation with the value `⊤`.
* It has no realization (`not_isFullRowRealization`): the lawful labelling `3, 2` extends to every
  legal one-point extension of `P α` (bountifulness at the cap `⊥`), and the reading forces
  `3 ≤ 2` (`CellScheme.Rows.IsLawful.le_of_forall_row_le`).
* So `StageType.HasPrescribedFullRowsAtLabels α` is false at every stage
  (`not_hasPrescribedFullRowsAtLabels`).  The prescription is not consistent with the faces
  uniformly (`not_isFaceConsistent`), so the uniform form `StageType.HasPrescribedFullRows α`
  survives this input.

This refutes the form of the common core whose admissibility is consistency with the labels of the
faces.  It refutes none of (R1)–(R4), nor the completion: the conditional theorems of
`VaughtConjecture.Extension.PrescribedFullRowsRoutes` assume the uniform form and the uniform
consistency of their prescription, and give nothing at an input where that consistency fails.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture.PrescribedFullRowsCounterexample

open Finset Label StageType GatedExtensionCounterexample

variable (α : Ordinal.{u})

/-! ### The input -/

/-- The cell `C₁` of `P α`: scope `univ`, grade `2`. -/
def cellA : Fin (P α).card := ⟨3, by change 3 < 5; omega⟩

/-- The cell `C₂` of `P α`: scope `univ`, grade `2`. -/
def cellB : Fin (P α).card := ⟨4, by change 4 < 5; omega⟩

/-- The donor: the legal stage type on one point of the one-point scheme, labelled `⊥`. -/
noncomputable def donor : StageType.{u} α 1 := Scheme.isLegal_onePoint.toStageType α

/-- The empty root of `P α`. -/
def root : Fin 0 ↪ Fin 2 := Function.Embedding.ofIsEmpty

/-- The **prescription**: at the grade `2`, every cell of graded index `(univ, 2)` reads `C₂` at
least as it reads `C₁`. -/
def prescription : FullRowPrescription (P α) (donor α) :=
  fun g r _ ↦ g = 2 → r (.inl (cellA α)) ≤ r (.inl (cellB α))

variable {α}

/-- The labels of `P α`: `⊤` at `C₁` and `C₂`, `⊥` at the three cells of grade `1`. -/
private theorem label_P_eq_bot_of_grade (z : Fin (P α).card)
    (hz : (P α).toCellScheme.grade z ≠ 2) : (P α).label z = ⊥ := by
  change Fin 5 at z
  fin_cases z <;> simp_all [P, labelling, S, cells, cellGrade]

/-- The grades of `P α` are at most `2`. -/
private theorem grade_P_le (z : Fin (P α).card) : (P α).toCellScheme.grade z ≤ 2 :=
  (P α).grade_le z

private theorem grade_cellA : (P α).toCellScheme.grade (cellA α) = 2 := rfl

private theorem grade_cellB : (P α).toCellScheme.grade (cellB α) = 2 := rfl

private theorem gradedIndex_cellB :
    (P α).toCellScheme.gradedIndex (cellB α) = ((univ : Finset (Fin 2)), 2) := rfl

private theorem label_cellB : (P α).label (cellB α) = ⊤ := rfl

/-- The donor has grades at most `1` and is labelled `⊥`. -/
private theorem grade_donor_le (j : Fin (donor α).card) : (donor α).toCellScheme.grade j ≤ 1 :=
  (donor α).grade_le j

private theorem label_donor (j : Fin (donor α).card) : (donor α).label j = ⊥ := rfl

/-- A stage type on no points has no cells. -/
private theorem isEmpty_card_zero (t : StageType.{u} α 0) : IsEmpty (Fin t.card) :=
  ⟨fun i ↦ absurd ((t.isWellFormed.isWellFormed.grade_pos i).trans_le (t.grade_le i))
    (lt_irrefl 0)⟩

/-! ### The row of `C₂` reads `C₂` at least as `C₁` -/

private theorem three_not_le_two : ¬ ((3 : ℕ) : Label.{u}) ≤ ((2 : ℕ) : Label.{u}) := fun h ↦
  absurd (natCast_label_le.mp h) (by decide)

/-- The row of `C₂` reads `C₁` at most as `C₂`: under the lawful labelling `2, 3` of `C₁, C₂`,
locality at `C₂` would otherwise give `3 ≤ 2`. -/
private theorem rowAt_cellB_le :
    (P α).rowAt (cellB α) (cellA α) ≤ (P α).rowAt (cellB α) (cellB α) := by
  have hA : cellA α ∈ (P α).toCellScheme.below ((P α).toCellScheme.gradedIndex (cellB α)) := by
    rw [gradedIndex_cellB]; exact ⟨subset_univ _, le_rfl⟩
  have hB := (P α).toCellScheme.mem_below_gradedIndex (cellB α)
  rw [Scheme.rowAt_of_mem hA, Scheme.rowAt_of_mem hB]
  by_contra hlt
  have key := (isLawful_labelling_two_three.{u}.locality (cellB α)).le_of_le
    (d := ⟨cellB α, hB⟩) (d' := ⟨cellA α, hA⟩) (le_of_not_ge hlt) le_rfl
  change min ((3 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) ≤
    min ((2 : ℕ) : Label.{u}) ((3 : ℕ) : Label.{u}) at key
  rw [min_self, min_eq_left (natCast_label_le.mpr (by decide : 2 ≤ 3))] at key
  exact three_not_le_two key

/-! ### Consistency at the labels -/

/-- **The prescription is consistent with the faces at their labels.**  At the grade `2` the row
of `C₂`, with `⊥` at the donor, is admissible with the value `⊤`: it reads `C₂` at least as `C₁`,
it is coded and lawful below `(univ, 2)`, and locality of the labels of `P α` at `C₂` is the
transformation.  At the grades `1` and `3` the bottom readings with the value `⊥` are admissible,
since the known cells of grade `1` are labelled `⊥` and none has grade `3`. -/
theorem isFaceConsistentAtLabels {t : StageType.{u} α 0}
    (ht : restrictFace (root) (P α) = some t)
    (hd : restrictFace Fin.castSuccEmb (donor α) = some t) :
    IsFaceConsistentAtLabels (P α) ht (donor α) hd (prescription α) := by
  have := isEmpty_card_zero t
  refine ⟨(donor α).label, (donor α).isLawful, fun i ↦ isEmptyElim i, ?_⟩
  intro g hg0 hg3 T hT
  by_cases hg2 : g = 2
  · subst hg2
    obtain ⟨gs, σ, hw, heq⟩ := (P α).isLawful.locality (cellB α)
    have hmem (z : Fin (P α).card) :
        z ∈ (P α).toCellScheme.below ((P α).toCellScheme.gradedIndex (cellB α)) := by
      rw [gradedIndex_cellB]; exact ⟨subset_univ _, grade_P_le z⟩
    refine ⟨Sum.elim (fun z ↦ (P α).rowAt (cellB α) z) fun _ ↦ ⊥,
      (P α).rowAt (cellB α) (cellB α), ⊤, fun _ _ ↦ le_top, fun _ ↦ rowAt_cellB_le,
      fun T' ↦ ?_, (P α).isCoded.rowAt_lt _ _, ?_, ?_, gs, σ, hw, ?_, ?_⟩
    · cases T' with
      | inl z => exact (P α).isCoded.rowAt_lt _ _
      | inr j => exact WithBot.bot_lt_coe _
    · exact (P α).toScheme.isLawfulBelow_rowAt (isLegal_P α).isConsistent gradedIndex_cellB
    · exact CellScheme.Rows.isLawfulBelow_const_bot _
    · have := heq ⟨cellB α, hmem _⟩
      simp only [min_self] at this
      rw [Scheme.rowAt_of_mem (hmem _)]
      rw [label_cellB] at this
      exact this
    · intro T' hT'
      cases T' with
      | inl z =>
        have := heq ⟨z, hmem z⟩
        simp only [label_cellB, min_top_right] at this
        simp only [Sum.elim_inl, min_top_right, Scheme.rowAt_of_mem (hmem z)]
        exact this
      | inr j =>
        simp only [Sum.elim_inr, label_donor, hw.map_bot, bot_le, min_eq_left]
  · refine ⟨fun _ ↦ ⊥, ⊥, ⊥, fun T' hT' ↦ ?_, fun h ↦ absurd h hg2, fun _ ↦ WithBot.bot_lt_coe _,
      WithBot.bot_lt_coe _, CellScheme.Rows.isLawfulBelow_const_bot _,
      CellScheme.Rows.isLawfulBelow_const_bot _, fun _ ↦ ⊤, fun _ ↦ ⊥, IsWitness.bot_top, by simp,
      fun T' _ ↦ by simp⟩
    have hg := hT T' hT'
    cases T' with
    | inl z =>
      exact (label_P_eq_bot_of_grade z (by simp only [knownGrade, Sum.elim_inl] at hg; omega)).le
    | inr j => exact (label_donor j).le

/-- **The prescription is not consistent with the faces** (uniformly): at the lawful labelling
`3, 2` of `C₁, C₂`, an admissible row at the grade `2` with a value at least `3` would read `C₂` at
least as `C₁` and transform to `3` at `C₁` and `2` at `C₂`. -/
theorem not_isFaceConsistent {t : StageType.{u} α 0} (ht : restrictFace root (P α) = some t)
    (hd : restrictFace Fin.castSuccEmb (donor α) = some t) :
    ¬ IsFaceConsistent (P α) ht (donor α) hd (prescription α) := by
  intro hc
  obtain ⟨b, -, -, hadm⟩ := hc _ isLawful_labelling_three_two
  obtain ⟨r, w, v, hv, hΦ, -, -, -, -, gs, σ, hw, -, htr⟩ :=
    hadm 2 (by omega) (by omega) (some (.inl (cellA α))) (fun T' hT' ↦ by
      cases hT'; exact grade_cellA)
  have h3 : ((3 : ℕ) : Label.{u}) ≤ v := hv _ rfl
  have hA := htr (.inl (cellA α)) grade_cellA.le
  have hB := htr (.inl (cellB α)) grade_cellB.le
  change min ((3 : ℕ) : Label.{u}) v = min (σ (r (.inl (cellA α)))) (gs 2) at hA
  change min ((2 : ℕ) : Label.{u}) v = min (σ (r (.inl (cellB α)))) (gs 2) at hB
  rw [min_eq_left h3] at hA
  rw [min_eq_left ((natCast_label_le.mpr (by decide : 2 ≤ 3)).trans h3)] at hB
  exact three_not_le_two (hA ▸ hB ▸ min_le_min (hw.monotone (hΦ rfl)) le_rfl)

/-! ### No realization -/

/-- **No legal one-point extension of `P α` reads `C₂` at least as `C₁` at every cell of graded
index `(univ, 2)`**: the lawful labelling `3, 2` of `P α` extends to the extension (bountifulness
at the cap `⊥`), and the reading forces `3 ≤ 2`
(`CellScheme.Rows.IsLawful.le_of_forall_row_le`). -/
theorem not_isFullRowRealization (D : StageType.{u} α 3) :
    ¬ IsFullRowRealization (P α) root (donor α) (prescription α) D := by
  rintro ⟨hD, h₁, -, he₁, he₂, hreal⟩
  obtain ⟨a', ha', hext⟩ := exists_isLawful_extend_of_restrictFace hD h₁
    isLawful_labelling_three_two
  have hle := ha'.le_of_forall_row_le (Y := ((univ : Finset (Fin 3)), 2))
    (hD.isComplete _ ⟨D.univ_mem_faces, by omega, by simp⟩)
    (s := faceCell h₁ (cellA α)) (x := faceCell h₁ (cellB α)) (subset_univ _)
    (by rw [grade_faceCell]; exact grade_cellA) (subset_univ _)
    (by rw [grade_faceCell, grade_faceCell]; exact le_rfl) ?_
  · rw [hext, hext] at hle
    exact three_not_le_two hle
  · intro u hu a b ha hb
    have := hreal u 2 hu rfl
    change D.rowAt u (faceCell h₁ (cellA α)) ≤ D.rowAt u (faceCell h₁ (cellB α)) at this
    rw [← ha, ← hb, Scheme.rowAt_of_mem a.2, Scheme.rowAt_of_mem b.2] at this
    exact this

/-- **Prescribed rows consistent at the labels fail at every stage**: the prescription that every
cell of graded index `(univ, 2)` reads `C₂` at least as `C₁`, over `P α` with the empty root and
the one-point donor, is consistent with the faces at their labels and has no realization. -/
theorem not_hasPrescribedFullRowsAtLabels : ¬ HasPrescribedFullRowsAtLabels.{u} α := by
  intro hc
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((P α).isSome_restrictFace_of_zero root)
  obtain ⟨t₀, ht₀⟩ := Option.isSome_iff_exists.mp
    ((donor α).isSome_restrictFace_of_zero Fin.castSuccEmb)
  have hd : restrictFace Fin.castSuccEmb (donor α) = some t := ht₀.trans (by rw [eq_of_zero t₀ t])
  obtain ⟨D, hD⟩ := hc (P α) root t ht (donor α) hd (isLegal_P α)
    (Scheme.isLegal_onePoint.isLegal_toStageType α) (prescription α)
    (isFaceConsistentAtLabels ht hd)
  exact not_isFullRowRealization D hD

end VaughtConjecture.PrescribedFullRowsCounterexample
