/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapClean

/-!
# The vacuous admission: readings that reflect `⊥`, and closure under transformation images

Roadmap, Layer 3 ((R3) of the table of 3.4).

The **vacuous admission** admits every state outside the bottom class of the context and asks
correctness of the states in it.  Recognition (locality at a cell `u` labelled `⊤`, then closure of
the admission under transformation images) transports admission from the row of `u` to the
observed state; for the vacuous admission it needs a reading of the row that reflects `⊥`.

* **Reflection is the agreement of the bottom patterns**
  (`StageType.exists_reflecting_reading_iff`, compiled in this repository (theorem named)): at a
  cell `u` labelled `⊤` by a lawful labelling `a`, some map reading the row of `u` as `a` below `u`
  sends only `⊥` to `⊥` on the row exactly when `a` and the row of `u` are `⊥` at the same cells
  below `u`.  Lawfulness does not force it.
* **It fails at the context with root cells labelled `⊥`**
  (`BottomRootCounterexample.not_reflecting_reading`, compiled): its labels and the row of its cap
  differ in their bottom pattern at a root cell.
* **The vacuous admission is not closed under transformation images**
  (`BottomRootCounterexample.exists_vacAdm_not_vacAdm_keepTop`, compiled): at every legal carrier
  of that context (faces the context and the donor), a lawful extension of the separating
  labelling is admitted (it is out of the class), and its image under `Label.keepTopShifter` (a
  witness) is in the class and not correct.  So the vacuous admission violates the law (A1) of the
  engine's admissions, and recognition does not transport the class from a state to a row.
* **The acquisition property** (`Realization.RootBottomAcquisition`, a named statement,
  prospective): hollow acquisition of the marked-cap contexts with root offsets below the grade of
  the cap and the cap reading the root cells labelled `⊥` as `⊥`
  (`TiedRootCapRelabel.MarkedCapContextBelow'`).  It is not derived from the clauses of
  `Realization.IsModel` here.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u w

namespace VaughtConjecture

open Finset Label

/-! ### Readings reflecting `⊥` -/

namespace StageType

variable {α : Ordinal.{u}} {k : ℕ}

/-- **A reading at a cell labelled `⊤` reflects `⊥` on the row exactly when the bottom patterns
agree.**  For a lawful labelling `a` of `t'` with `a u = ⊤`, some map reading the row of `u` as `a`
below `u` sends only `⊥` to `⊥` on the values of the row there, exactly when `a` and the row of `u`
are `⊥` at the same cells below `u`. -/
theorem exists_reflecting_reading_iff {t' : StageType.{u} α k} {a : Fin t'.card → Label.{u}}
    (ha : t'.rows.IsLawful a) {u : Fin t'.card} (hu : a u = ⊤) :
    (∃ σ : Label.{u} → Label.{u},
      (∀ d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex u),
        σ (t'.rowAt u d) = ⊥ ↔ t'.rowAt u d = ⊥) ∧
      ∀ d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex u), a d = σ (t'.rowAt u d)) ↔
    ∀ d ∈ t'.toCellScheme.below (t'.toCellScheme.gradedIndex u),
      a d = ⊥ ↔ t'.rowAt u d = ⊥ := by
  constructor
  · rintro ⟨σ, hrefl, hread⟩ d hd
    rw [hread d hd]
    exact hrefl d hd
  · intro hpat
    obtain ⟨σ, -, hread⟩ := exists_isBoundedReading ha hu
    exact ⟨σ, fun d hd ↦ by rw [← hread d hd]; exact hpat d hd, hread⟩

end StageType

/-! ### At the context with root cells labelled `⊥` -/

namespace BottomRootCounterexample

open StageType TiedRootCapRelabel
open TiedRootCapCounterexample (rootRow rootEmb)

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **The labelling of the context does not reflect `⊥` through its cap**: below the cap, the
labels and the row of the cap are not `⊥` at the same cells (a root cell labelled `⊥` is read as
`1`), so no map reading the row of the cap as the labels reflects `⊥` on the row
(`StageType.exists_reflecting_reading_iff`). -/
theorem not_reflecting_reading :
    ¬ ∀ d ∈ (context hα).toCellScheme.below
        ((context hα).toCellScheme.gradedIndex (capCell hα)),
      (context hα).label d = ⊥ ↔ (context hα).rowAt (capCell hα) d = ⊥ := by
  intro hpat
  refine not_rootBottomRespected hα fun y hy hyb ↦ (hpat y ?_).mp hyb
  exact mem_below_of_mem_visibleCells (h := rootEmb) (context_scope_cap hα)
    (by rw [context_grade_cap]; omega) hy

variable {D : StageType.{u} α 4} (h₁ : restrictFace Fin.castSuccEmb D = some (context hα))
  (h₂ : restrictFace (extendByLast rootEmb) D = some (donor hα))

/-- The cap requests of (R3) on the cells of a carrier: the cap of the context as cap and marker,
threshold `3`, the apex of the donor read from below. -/
noncomputable def capRequestsD : CapRequests (Fin D.card) where
  cap := faceCell h₁ (capCell hα)
  N := 3
  R := 0
  R_lt_N := by omega
  Z := ∅
  F := ∅
  T := {faceCell h₂ (donorApex hα)}
  ref := id
  off := fun _ ↦ 0
  marker := faceCell h₁ (capCell hα)

/-- The **vacuous admission**: a state in the bottom class of the context is correct; a state out
of the class is admitted. -/
def VacAdm (s : Fin D.card → Label.{u}) : Prop :=
  (∀ z, s (faceCell h₁ z) = ⊥ ↔ (context hα).label z = ⊥) → (capRequestsD hα h₁ h₂).IsCorrect s

/-- **The vacuous admission is not closed under transformation images** at a carrier of the
context with root cells labelled `⊥`: a lawful extension of the separating labelling is admitted
(it is out of the class), and its image under the shifter keeping only `⊤` (a witness) is in the
class and not correct (the extension is not `⊤` at the donor's apex, whose row ties the root
cells that the separating labelling reads as `1 < 2`). -/
theorem exists_vacAdm_not_vacAdm_keepTop (hD : D.IsLegal) :
    ∃ s : Fin D.card → Label.{u}, D.rows.IsLawful s ∧ VacAdm hα h₁ h₂ s ∧
      ¬ VacAdm hα h₁ h₂ (keepTopShifter ∘ s) := by
  obtain ⟨a, ha, hext⟩ := exists_isLawful_extend_of_restrictFace hD h₁ (isLawful_separating hα)
  -- the extension is not `⊤` at the donor's apex
  have happex : a (faceCell h₂ (donorApex hα)) ≠ ⊤ := by
    intro htop
    set b : Fin (donor hα).card → Label.{u} := fun j ↦ a (faceCell h₂ j)
    have hb : (donor hα).rows.IsLawful b := isLawful_comp_faceCell h₂ ha
    have hbroot (y : Fin 2) : b (faceCell (restrictFace_donor hα) y) = rootRow y := by
      change a (faceCell h₂ (faceCell (restrictFace_donor hα) y)) = _
      rw [← faceCell_faceCell h₁ h₂ (restrictFace_context hα) (restrictFace_donor hα) y, hext]
      exact separating_root hα y
    have hy (y : Fin 2) := mem_below_donor_last hα (faceCell (restrictFace_donor hα) y)
    have hloc := (hb.locality (donorApex hα)).le_of_le
      (d := ⟨_, hy ⟨1, by decide⟩⟩) (d' := ⟨_, hy ⟨0, by decide⟩⟩)
      (le_of_eq ((donor_row_root hα _ _).trans (donor_row_root hα _ _).symm))
      (le_of_eq ((grade_faceCell (restrictFace_donor hα) (⟨0, by decide⟩ : Fin 2)).trans
        (grade_faceCell (restrictFace_donor hα) (⟨1, by decide⟩ : Fin 2)).symm))
    change min (b (faceCell _ _)) (b (donorApex hα)) ≤ min (b (faceCell _ _)) (b (donorApex hα))
      at hloc
    have hbj : b (donorApex hα) = ⊤ := htop
    rw [hbj, min_top_right, min_top_right, hbroot, hbroot] at hloc
    exact absurd (natCast_label_le.mp hloc) (by decide)
  refine ⟨a, ha, fun hcl ↦ ?_, fun hadm ↦ ?_⟩
  · have h := (hcl (faceCell (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2))).mpr
      ((label_faceCell _ _).trans rfl)
    rw [hext, separating_root] at h
    exact absurd h (natCast_label_ne_bot _)
  · have hcl : ∀ z, (keepTopShifter ∘ a) (faceCell h₁ z) = ⊥ ↔ (context hα).label z = ⊥ := by
      intro z
      simp only [Function.comp_apply, hext]
      induction z using Fin.lastCases with
      | last =>
        rw [separating_capCell, keepTopShifter_top, context_label_cap]
      | cast d =>
        rw [context_label_castSucc, show separating hα d.castSucc = ell hα d from
          topExtension_castSucc _ d, keepTopShifter_of_ne (ell_ne_top hα d)]
    have hcorr := hadm hcl
    have hcap : (keepTopShifter ∘ a) (faceCell h₁ (capCell hα)) = ⊤ := by
      simp only [Function.comp_apply, hext, separating_capCell, keepTopShifter_top]
    have h := hcorr.markerValue_le _ rfl
    simp only [CapRequests.markerValue, capRequestsD, hcap, visibilityReplace_top, min_self,
      min_top_right] at h
    have h' : keepTopShifter (a (faceCell h₂ (donorApex hα))) = ⊤ := top_le_iff.mp h
    exact happex (by
      by_contra hne
      rw [keepTopShifter_of_ne hne] at h'
      exact bot_ne_top h')

end BottomRootCounterexample

/-! ### The acquisition of the root bottoms (a named statement) -/

namespace Realization

/-- **Acquisition of marked-cap contexts respecting the root bottoms** (a named statement,
prospective; not derived from the clauses of `Realization.IsModel`): hollow acquisition of the
marked-cap contexts with root offsets below the grade of the cap whose cap reads every root cell
labelled `⊥` as `⊥`. -/
def RootBottomAcquisition : Prop :=
  HollowAcquisition.{u, w} IsCoverHollowAtBlock fun t' h ↦
    TiedRootCapRelabel.MarkedCapContextBelow' t' h

end Realization

end VaughtConjecture
