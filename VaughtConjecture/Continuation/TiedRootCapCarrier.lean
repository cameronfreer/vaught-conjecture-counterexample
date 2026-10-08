/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapCounterexample
import VaughtConjecture.Continuation.TopReadingCarrier
import VaughtConjecture.Extension.PinnedExtension
import VaughtConjecture.Extension.TwoFaceLift

/-!
# Carriers at the context with separated tied root cells

Roadmap, Layer 3 ((R3) of the table of 3.4).

At the context of `TiedRootCapCounterexample` the all-cells top-marked design fails
(`StageType.not_hasTopMarkedCarriers`).  This file tests the cutoff form there: the clause of hollow
cutoff determination at the context and the donor, `∃ D' ∈ t'.cofaces, ∃ δ, IsPermittedCutoff α δ ∧
IsDeterminedWithin (receivingFamily D' δ) t' h d` (the statement `HollowCutoffDetermination` of the
compositions lane; its parts `IsDeterminedWithin`, `receivingFamily` and `IsPermittedCutoff` are
on this branch).

* **Reduction** (`TiedRootCapCounterexample.exists_isDeterminedWithin_of_isTopReadingCarrier`,
  compiled in this repository (theorem named)): a top-reading carrier at the context
  (`StageType.IsTopReadingCarrier`, with top cap and marker the cap: every cell of graded index
  `(univ, 3)` labelled `⊤` in the carrier reads the new tops of the donor at least as the cap)
  gives the clause, with a permitted cutoff above the labels of the carrier other than `⊤`
  (`StageType.exists_isPermittedCutoff_gt`).
* **Carriers exist** (`TiedRootCapCounterexample.exists_carrier`, compiled): a legal one-point
  extension of the context whose face along `extendByLast rootEmb` is the donor, by the exact
  pinned extension with coatom extensions on at most four points
  (`StageType.exists_coatomExtension_of_le_two`, from the completions with `m ≤ 2`).
* **What a top-reading carrier must avoid** (`TiedRootCapCounterexample.exists_cell_reads_lt`,
  `TiedRootCapCounterexample.exists_cell_label_ne_top`, compiled): every carrier has a cell of
  graded index `(univ, 3)` reading the apex of the donor strictly below the cap (otherwise the
  separating labelling extends with `⊤` at the apex and inverts the tie), and a top-reading carrier
  labels every such cell below `⊤`.

**Status.**  Not compiled: a carrier with a lawful labelling, literal on the context and on the
donor, that is `⊤` at no cell of graded index `(univ, 3)` reading the apex below the cap (while
availability from the cap forces some such cell labelled `⊤`, which must then read it at least as
the cap).  Not refuted either.  The constraint is on the labelling of the cells of full scope at
the grade of the cap, the selective layer of the engine; no compiled lemma lowers a cell of that
graded index below `⊤` while keeping the locality of the cells reading it.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### Coatom extensions at small arities, and permitted cutoffs -/

namespace StageType

variable {α : Ordinal.{u}}

/-- **Coatom extensions on at most four points**, from the completions of seeds with `m ≤ 2`
(`Seed.nonempty_completionBelowFullGrade_of_le_two`), at a stage that is zero or a limit. -/
theorem exists_coatomExtension_of_le_two (hα : Order.IsSuccPrelimit α) {m : ℕ} (hm : m ≤ 2)
    (ta tb : StageType.{u} α (m + 1)) (p : StageType.{u} α m) (hta : ta.IsLegal)
    (htb : tb.IsLegal) (hpa : restrictFace Fin.castSuccEmb ta = some p)
    (hpb : restrictFace Fin.castSuccEmb tb = some p) :
    ∃ t : StageType.{u} α (m + 2), t.IsLegal ∧ restrictFace Fin.castSuccEmb t = some ta ∧
      restrictFace (extendByLast Fin.castSuccEmb) t = some tb := by
  obtain ⟨F⟩ := (Seed.ofCoatoms hta htb hpa hpb).nonempty_completionBelowFullGrade_of_le_two hm
  exact ⟨F.completion hα, F.isLegal_completion hα, F.restrictFace_left_completion hα,
    F.restrictFace_right_completion hα⟩

/-- **A permitted cutoff above the labels other than `⊤`**: at a limit stage, the labels of a
stage type other than `⊤` lie below some permitted cutoff. -/
theorem exists_isPermittedCutoff_gt (hα : Order.IsSuccLimit α) {k : ℕ}
    (D : StageType.{u} α k) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧ ∀ j, D.label j ≠ ⊤ → D.label j < δ := by
  have h0 : ((0 : Ordinal.{u}) : Label.{u}) < α :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hα.bot_lt)
  obtain ⟨c, h0c, hcα, -, hc⟩ := exists_isSelfVisible_bound hα.isSuccPrelimit 0 h0 D.label
  induction c using recBotCoeTop with
  | bot => exact absurd h0c (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact absurd hcα (not_lt.mpr le_top)
  | coe o =>
    have hoα : o < α := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hcα)
    refine ⟨((o + 1 : Ordinal.{u}) : Label.{u}), ⟨WithBot.bot_lt_coe _, ?_⟩, fun j hj ↦ ?_⟩
    · exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (hα.add_one_lt hoα))
    · have hjα : D.label j < α := (D.atStage j).resolve_right hj
      exact (hc j hjα).trans_lt
        (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (Order.lt_add_one_iff.mpr le_rfl)))

end StageType

namespace TiedRootCapCounterexample

open StageType

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- The apex of the donor, a new cell labelled `⊤`. -/
noncomputable abbrev donorApex : Fin (donor hα).card := Fin.last _

theorem donorApex_label : (donor hα).label (donorApex hα) = ⊤ :=
  addApex_label_last (t := (donorLower hα).truncate hα.isSuccPrelimit)
    (donorLower hα).isLegalBelowFullGrade (Nat.succ_pos _)

theorem donorApex_scope : Fin.last 1 ∈ (donor hα).toCellScheme.scope (donorApex hα) := by
  have : (donor hα).toCellScheme.scope (Fin.last _) = univ :=
    addApex_scope_last (t := (donorLower hα).truncate hα.isSuccPrelimit)
      (donorLower hα).isLegalBelowFullGrade (Nat.succ_pos _)
  rw [this]
  exact mem_univ _

/-- **Carriers exist**: a legal one-point extension of the context whose face along
`extendByLast rootEmb` is the donor (the exact pinned extension, by coatom extensions on at most
four points). -/
theorem exists_carrier : ∃ D : StageType.{u} α 4, D.IsLegal ∧
    restrictFace Fin.castSuccEmb D = some (context hα) ∧
    restrictFace (extendByLast rootEmb) D = some (donor hα) :=
  exists_pinned_extension_of_lt (fun m' hm' ta tb p ↦
    exists_coatomExtension_of_le_two hα.isSuccPrelimit (by omega) ta tb p)
    (isLegal_context hα) (restrictFace_context hα) (isLegal_donor hα) (restrictFace_donor hα)

/-- **Every carrier has a cell of graded index `(univ, 3)` reading the apex of the donor strictly
below the cap.**  Otherwise every such cell reads it at least as the cap, the separating
labelling extends to the carrier with `⊤` at the apex (`StageType.exists_extend_top_of_reads`),
and its restriction to the donor, lawful and `⊤` at the apex, inverts the two root cells that the
apex ties. -/
theorem exists_cell_reads_lt {D : StageType.{u} α 4} (hD : D.IsLegal)
    (h₁ : restrictFace Fin.castSuccEmb D = some (context hα))
    (h₂ : restrictFace (extendByLast rootEmb) D = some (donor hα)) :
    ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) ∧
      D.rowAt u (faceCell h₂ (donorApex hα)) < D.rowAt u (faceCell h₁ (capCell hα)) := by
  by_contra hall
  simp only [not_exists, not_and, not_lt] at hall
  obtain ⟨a', ha', hext, htop⟩ := exists_extend_top_of_reads hD h₁ h₂ (context_grade_cap hα)
    (context_grade_cap hα).le (P := (· = donorApex hα))
    (fun j _ ↦ ((donor hα).grade_le j).trans (by omega))
    (fun u hu j hj ↦ hj ▸ hall u hu) (isLawful_separating hα) (separating_capCell hα)
    (separating_capCell hα)
  set b : Fin (donor hα).card → Label.{u} := fun j ↦ a' (faceCell h₂ j)
  have hb : (donor hα).rows.IsLawful b := isLawful_comp_faceCell h₂ ha'
  have hbj : b (donorApex hα) = ⊤ := htop _ rfl
  have hbroot (y : Fin 2) : b (faceCell (restrictFace_donor hα) y) = rootRow y := by
    change a' (faceCell h₂ (faceCell (restrictFace_donor hα) y)) = _
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
  rw [hbj, min_top_right, min_top_right, hbroot, hbroot] at hloc
  exact absurd (natCast_label_le.mp hloc) (by decide)

/-- **A top-reading carrier labels such a cell below `⊤`**: the reading clause of a top-reading
carrier (with top cap and marker the cap) holds at every cell of graded index `(univ, 3)` labelled
`⊤`, so the cell of `TiedRootCapCounterexample.exists_cell_reads_lt` is not labelled `⊤`. -/
theorem exists_cell_label_ne_top {D : StageType.{u} α 4}
    (hD : (context hα).IsTopReadingCarrier rootEmb (donor hα) (capCell hα) (capCell hα) D) :
    ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) ∧
      D.rowAt u (faceCell hD.restrictFace_extendByLast (donorApex hα)) <
        D.rowAt u (faceCell hD.restrictFace_castSucc (capCell hα)) ∧ D.label u ≠ ⊤ := by
  obtain ⟨u, hu, hlt⟩ := exists_cell_reads_lt hα hD.isLegal hD.restrictFace_castSucc
    hD.restrictFace_extendByLast
  refine ⟨u, hu, hlt, fun htop ↦ ?_⟩
  have := hD.reads u (by rw [hu, context_grade_cap]) htop (donorApex hα) (donorApex_scope hα)
    (donorApex_label hα)
  exact absurd this (not_le.mpr hlt)

/-- **Cutoff determination at the context from a top-reading carrier**: a top-reading carrier
over the context for the donor, with top cap and marker the cap, is a coface of the context, and
determines the donor within its receiving family at a permitted cutoff (the clause of hollow
cutoff determination at this context and donor). -/
theorem exists_isDeterminedWithin_of_isTopReadingCarrier {D : StageType.{u} α 4}
    (hD : (context hα).IsTopReadingCarrier rootEmb (donor hα) (capCell hα) (capCell hα) D) :
    D ∈ (context hα).cofaces ∧ ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D δ) (context hα) rootEmb (donor hα) := by
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα D
  exact ⟨⟨hD.isLegal, hD.restrictFace_castSucc⟩, δ, hδ,
    isDeterminedWithin_receivingFamily_of_isTopReadingCarrier (restrictFace_context hα)
      (restrictFace_donor hα) (isMarkedCapContextAt_context hα).1 (context_label_cap hα)
      (by rw [context_grade_cap]; omega) hD hδD⟩

end TiedRootCapCounterexample

end VaughtConjecture
