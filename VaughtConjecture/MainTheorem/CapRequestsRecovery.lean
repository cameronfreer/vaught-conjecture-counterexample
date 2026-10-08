/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Extension.CapRequestsGrade
import VaughtConjecture.MainTheorem.CutoffCoatomRelabel

/-!
# Cutoff stable recovery from a correct completion

Roadmap, Layer 4, output 3 of higher-stage reconstruction, and Layer 3, 3.3–3.4 ((R4) of the
table of Layer 3: the reading through a proper cap, at the seed of the first coatom).

## Placement

This file belongs to Layer 4 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The old cells after appending a cell of full scope -/

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {j : ℕ} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

/-- **A lawful labelling restricts to the old cells**: below a pair not above `(univ, j)`, a
lawful labelling of the scheme with a cell appended is, on the old cells, lawful for `S`. -/
theorem isLawfulBelow_castSucc {ℓ : Fin (S.card + 1) → Label.{u}}
    (hℓ : (S.appendFullCell j r h).rows.IsLawful ℓ) {X : Finset (Fin n) × ℕ}
    (hX : ¬ ((univ : Finset (Fin n)), j) ≤ X) :
    S.rows.IsLawfulBelow X fun d ↦ ℓ d.1.castSucc := by
  have hc := CellScheme.Rows.isLawfulBelow_comap_iff (R := (S.appendFullCell j r h).rows)
    (isLowerEmbedding_castSucc j r h) (image_castSucc_below hX) (r := fun z ↦ ℓ z)
  rw [comap_rows_castSucc] at hc
  exact hc.mpr (hℓ.isLawfulBelow X)

end Scheme

/-! ### The cells of the completion along a proper face -/

namespace CompletionBelowFullGrade

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  (hα : Order.IsSuccPrelimit α)

/-- **The cells of the completion along a proper face** are the old cells of the amalgam along it,
at equal positions. -/
theorem cellMap_completion {k : ℕ} (f : Fin k ↪ Fin (m + 2)) (hf : univ.map f ≠ univ)
    {i : Fin (I.amalgam.toScheme.comap f).card} {z : Fin ((F.completion hα).toScheme.comap f).card}
    (hiz : (i : ℕ) = z) :
    (F.completion hα).toScheme.cellMap f z = (F.embed (I.amalgam.toScheme.cellMap f i)).castSucc :=
  Scheme.cellMap_eq_of_strictMono_of_mem_range (S := I.amalgam.toScheme)
    (T := (F.completion hα).toScheme) f (φ := fun d ↦ (F.embed d).castSucc)
    (Fin.strictMono_castSucc.comp F.embed.strictMono)
    (fun d ↦ (Scheme.appendFullCellScheme_scope_castSucc _ _ _).trans (F.scope_embed d))
    (fun z hz ↦ by
      obtain ⟨w, rfl⟩ := StageType.mem_range_castSucc_of_addApex _ _ f hf z hz
      have hne : F.scheme.toCellScheme.scope w ≠ univ := fun he ↦ hf (eq_univ_of_forall fun x ↦ by
        have hx : x ∈ ((F.completion hα).toCellScheme.scope w.castSucc : Set (Fin (m + 2))) := by
          change x ∈
            (Scheme.appendFullCellScheme (F.truncate hα).toScheme (m + 2)).scope w.castSucc
          rw [Scheme.appendFullCellScheme_scope_castSucc,
            show (F.truncate hα).toCellScheme.scope w = univ from he]
          exact mem_univ x
        obtain ⟨y, rfl⟩ := hz hx
        exact mem_map_of_mem _ (mem_univ y))
      obtain ⟨d, rfl⟩ := F.mem_range_embed w hne
      exact ⟨d, rfl⟩)
    hiz

/-- **A lawful labelling of the completed scheme with the apex is lawful on the old cells** below
every pair `(univ, N)` with `N < m + 2`. -/
theorem isLawfulBelow_castSucc {ℓ : Fin (F.completion hα).card → Label.{u}}
    (hℓ : (F.completion hα).rows.IsLawful ℓ) {N : ℕ} (hN : N < m + 2) :
    F.scheme.rows.IsLawfulBelow ((univ : Finset (Fin (m + 2))), N) fun z ↦ ℓ z.1.castSucc :=
  Scheme.isLawfulBelow_castSucc (h := F.isLegalBelowFullGrade.not_le) hℓ fun hle ↦
    absurd hle.2 (by simp only; omega)

end CompletionBelowFullGrade

/-! ### The data of a margin calibration with a cap of full scope -/

namespace StageType

variable {ξ : Ordinal.{u}} {m k : ℕ}

/-- **Cap data for the margin calibration**: a cap of full scope and grade `N` labelled at least
`λ_ξ + N`, with `k < N`, an offset `R < N` with `γ < λ_ξ + R`, a marker labelled `λ_ξ + i` with
`i < N` and grade at most `N`, and, for each cell of `D` labelled an ordinal `μ + n` (`μ` zero or a
limit), the offset `n < N` and a reference cell of grade at most `N` labelled `μ + i'`, `i' < N`. -/
structure MarginCapData (Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1))
    (D : StageType.{u} (blockStage (ξ + 1)) (k + 1)) (γ : Ordinal.{u}) where
  /-- The cap. -/
  cap : Fin Tp.card
  /-- The marker. -/
  marker : Fin Tp.card
  /-- The offset of the marker reading. -/
  R : ℕ
  /-- The finite part of the label of the marker. -/
  i : ℕ
  /-- The reference cell of a cell of `D`. -/
  ref : Fin D.card → Fin Tp.card
  /-- The offset of a cell of `D`. -/
  off : Fin D.card → ℕ
  /-- The cap has full scope. -/
  scope_cap : Tp.toCellScheme.scope cap = univ
  /-- The cap is labelled at least `λ_ξ + N`. -/
  le_label_cap :
    ((blockStage ξ + Tp.toCellScheme.grade cap : Ordinal.{u}) : Label.{u}) ≤ Tp.label cap
  /-- The root has fewer points than the grade of the cap. -/
  lt_grade_cap : k < Tp.toCellScheme.grade cap
  /-- The offset is below the grade of the cap. -/
  R_lt : R < Tp.toCellScheme.grade cap
  /-- The margin. -/
  lt_R : γ < blockStage ξ + R
  /-- The finite part of the marker is below the grade of the cap. -/
  i_lt : i < Tp.toCellScheme.grade cap
  /-- The marker has grade at most that of the cap. -/
  grade_marker_le : Tp.toCellScheme.grade marker ≤ Tp.toCellScheme.grade cap
  /-- The marker is labelled `λ_ξ + i`. -/
  label_marker : Tp.label marker = ((blockStage ξ + i : Ordinal.{u}) : Label.{u})
  /-- The references of the ordinal labels of `D`. -/
  ref_spec : ∀ (j : Fin D.card) (o : Ordinal.{u}), D.label j = o →
    ∃ (μ : Ordinal.{u}) (i' : ℕ), Order.IsSuccPrelimit μ ∧ o = μ + off j ∧
      off j < Tp.toCellScheme.grade cap ∧ i' < Tp.toCellScheme.grade cap ∧
      Tp.toCellScheme.grade (ref j) ≤ Tp.toCellScheme.grade cap ∧
      Tp.label (ref j) = ((μ + i' : Ordinal.{u}) : Label.{u})

/-- **The margin calibration gives cap data**, for a legal `T⁺`: availability within `T⁺` moves the
cap to a cell of full scope and the same grade, labelled at least the cap. -/
theorem GradedCapMarginCalibration.nonempty_marginCapData
    {Tp : StageType.{u} (blockStage (ξ + 1)) (m + 1)} {f : Fin k ↪ Fin (m + 1)}
    {D : StageType.{u} (blockStage (ξ + 1)) (k + 1)} {γ : Ordinal.{u}} (hT : Tp.IsLegal)
    (h : GradedCapMarginCalibration ξ Tp f D γ) : Nonempty (MarginCapData Tp D γ) := by
  classical
  obtain ⟨b, hb, hk, ⟨R, hR, hγ⟩, ⟨a, i, hi, ha, hal⟩, href⟩ := h
  obtain ⟨s, hs⟩ := hT.isComplete ((univ : Finset (Fin (m + 1))), Tp.toCellScheme.grade b)
    ⟨Tp.univ_mem_faces, show 0 < Tp.toCellScheme.grade b by omega, by
      rw [card_univ, Fintype.card_fin]
      exact Tp.grade_le b⟩
  obtain ⟨u, hu, hbu⟩ := Tp.isLawful.availability b s
    (by rw [show Tp.toCellScheme.scope s = univ from congrArg Prod.fst hs]; exact subset_univ _)
    (congrArg Prod.snd hs).symm
  have hus : Tp.toCellScheme.gradedIndex u = ((univ : Finset (Fin (m + 1))),
      Tp.toCellScheme.grade b) := hu.trans hs
  have hg : Tp.toCellScheme.grade u = Tp.toCellScheme.grade b := congrArg Prod.snd hus
  have hspec (j : Fin D.card) : ∃ (r : Fin Tp.card) (n : ℕ), ∀ o : Ordinal.{u}, D.label j = o →
      ∃ (μ : Ordinal.{u}) (i' : ℕ), Order.IsSuccPrelimit μ ∧ o = μ + n ∧
        n < Tp.toCellScheme.grade b ∧ i' < Tp.toCellScheme.grade b ∧
        Tp.toCellScheme.grade r ≤ Tp.toCellScheme.grade b ∧
        Tp.label r = ((μ + i' : Ordinal.{u}) : Label.{u}) := by
    by_cases hj : ∃ o : Ordinal.{u}, D.label j = o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨μ, n, i', r, hμ, hon, hn, hi', hr, hrl⟩ := href j o ho
      refine ⟨r, n, fun o' ho' ↦ ⟨μ, i', hμ, ?_, hn, hi', hr, hrl⟩⟩
      rw [ho] at ho'
      exact (WithTop.coe_injective (WithBot.coe_injective ho')).symm.trans hon
    · exact ⟨b, 0, fun o ho ↦ absurd ⟨o, ho⟩ hj⟩
  choose ref off hro using hspec
  exact ⟨{ cap := u, marker := a, R := R, i := i, ref := ref, off := off
           scope_cap := congrArg Prod.fst hus
           le_label_cap := by rw [hg]; exact hb.trans hbu
           lt_grade_cap := by rw [hg]; exact hk
           R_lt := by rw [hg]; exact hR
           lt_R := hγ
           i_lt := by rw [hg]; exact hi
           grade_marker_le := by rw [hg]; exact ha
           label_marker := hal
           ref_spec := fun j o ho ↦ by rw [hg]; exact hro j o ho }⟩

end StageType

end VaughtConjecture
