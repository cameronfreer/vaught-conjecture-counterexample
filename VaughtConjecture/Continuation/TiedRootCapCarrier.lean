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

* **The reading layer fails here** (`TiedRootCapCounterexample.not_exists_fill_bot`, compiled):
  in every carrier, no labelling lawful below `(univ, 3)` equal to the separating labelling on the
  context reads the apex of the donor at least as the cap.  This is the failure of the fill at `⊥`
  from the context coatom, the condition under which a reading layer at the grade of the cap
  (every cell of graded index `(univ, 3)` reading the apex at least as the cap, as in the reading
  layer of the (R3) lane at five points) is legal; such a layer would contradict
  `TiedRootCapCounterexample.exists_cell_reads_lt`.

* **Determination at a cutoff is the top clause**
  (`StageType.isDeterminedWithin_receivingFamily_iff`,
  `TiedRootCapCounterexample.isDeterminedWithin_carrier_iff`, compiled): with `δ` above the labels
  of the carrier other than `⊤`, the donor is determined within the receiving family exactly when
  every member literal on the context is `⊤` at every cell of the donor labelled `⊤`.  The
  receiving family keeps the labels below `δ` only: at a cell where the carrier is `⊤` (the apex
  of the donor) a member is asked to be at least `δ`, not `⊤`, so the clause is not automatic.

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

namespace StageType

variable {α : Ordinal.{u}}

/-- **Determination at a cutoff is the top clause.**  Let `D` restrict along `extendByLast h` to
`d`, and let `δ` lie above every label of `D` other than `⊤`.  The donor is determined within the
receiving family of `D` at `δ` exactly when every member literal on `t'` is `⊤` at every cell of
`d` labelled `⊤`.  The members agree with `D` below `δ`, hence with `d` at every cell of `d`
labelled other than `⊤`; at a cell of `d` labelled `⊤` they are only asked to be at least `δ`. -/
theorem isDeterminedWithin_receivingFamily_iff {k n : ℕ} {t' : StageType.{u} α k}
    {h : Fin n ↪ Fin k} {d : StageType.{u} α (n + 1)} {D : StageType.{u} α (k + 1)}
    (h₂ : restrictFace (extendByLast h) D = some d) {δ : Label.{u}}
    (hδ : ∀ j, D.label j ≠ ⊤ → D.label j < δ) :
    IsDeterminedWithin (receivingFamily D δ) t' h d ↔
      ∀ q ∈ receivingFamily D δ, restrictFace Fin.castSuccEmb q = some t' →
        ∀ (i : Fin q.card) (j : Fin d.card), (i : ℕ) = faceCell h₂ j → d.label j = ⊤ →
          q.label i = ⊤ := by
  constructor
  · rintro hdet ⟨S, ℓ, hw, hcod, hl, hat⟩ hq hq₁ i j hij hj
    have hq₂ := hdet _ hq hq₁
    obtain ⟨hS, -⟩ := hq
    change S = D.toScheme at hS
    subst hS
    obtain rfl : i = faceCell h₂ j := Fin.ext hij
    exact (label_faceCell hq₂ j).trans hj
  · rintro H ⟨S, ℓ, hw, hcod, hl, hat⟩ hq hq₁
    have H' := H _ hq hq₁
    obtain ⟨hS, hcut⟩ := hq
    change S = D.toScheme at hS
    subst hS
    refine (restrictFace_congr_label (t := ⟨D.toScheme, ℓ, hw, hcod, hl, hat⟩) (s := D) rfl
      fun i j hij hi ↦ ?_).trans h₂
    obtain rfl : i = j := Fin.ext hij
    obtain ⟨z, rfl⟩ := exists_faceCell_eq h₂ hi
    change ℓ (faceCell h₂ z) = D.label (faceCell h₂ z)
    by_cases hz : d.label z = ⊤
    · exact (H' _ z rfl hz).trans ((label_faceCell h₂ z).trans hz).symm
    · have hlt : D.label (faceCell h₂ z) < δ := hδ _ (by rw [label_faceCell]; exact hz)
      have hmin : min (ℓ (faceCell h₂ z)) δ = D.label (faceCell h₂ z) :=
        (hcut _ _ rfl).trans (min_eq_left hlt.le)
      have hℓ : ℓ (faceCell h₂ z) < δ :=
        (min_lt_iff.mp (hmin ▸ hlt)).resolve_right (lt_irrefl δ)
      rw [← hmin, min_eq_left hℓ.le]

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

/-- **The fill at `⊥` from the coatom of the context fails along the separating labelling**: in
every carrier, no labelling lawful below `(univ, 3)` equal to the separating labelling on the
context reads the apex of the donor at least as the cap.  It would be `⊤` at the apex, whose row
ties the two root cells, which the separating labelling inverts.  This is the failure of the fill
condition `ReadingFillBot` of the reading layer of the (R3) lane (its fill at `⊥` from the context
coatom, with the reading of the apex against the cap), so no reading layer, a layer whose every
cell of graded index `(univ, 3)` reads the apex at least as the cap, is part of a carrier here
(`TiedRootCapCounterexample.exists_cell_reads_lt`). -/
theorem not_exists_fill_bot {D : StageType.{u} α 4}
    (h₁ : restrictFace Fin.castSuccEmb D = some (context hα))
    (h₂ : restrictFace (extendByLast rootEmb) D = some (donor hα)) :
    ¬ ∃ g : Fin D.card → Label.{u},
      D.rows.IsLawfulBelow ((univ : Finset (Fin 4)), 3) (fun d ↦ g d) ∧
      (∀ z, g (faceCell h₁ z) = separating hα z) ∧
      g (faceCell h₁ (capCell hα)) ≤ g (faceCell h₂ (donorApex hα)) := by
  rintro ⟨g, hg, hgz, hread⟩
  obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hg
  have hAtop : g (faceCell h₂ (donorApex hα)) = ⊤ :=
    top_le_iff.mp (by rw [← separating_capCell hα, ← hgz]; exact hread)
  have hAb : faceCell h₂ (donorApex hα) ∈ D.toCellScheme.below ((univ : Finset (Fin 4)), 3) := by
    rw [CellScheme.mem_below]
    refine Prod.mk_le_mk.mpr ⟨subset_univ _, ?_⟩
    rw [grade_faceCell]
    exact ((donor hα).grade_le _).trans (by omega)
  have hy (i : Fin 2) : faceCell h₂ (faceCell (restrictFace_donor hα) i) ∈
      D.toCellScheme.below (D.toCellScheme.gradedIndex (faceCell h₂ (donorApex hα))) := by
    have hz := mem_below_donor_last hα (faceCell (restrictFace_donor hα) i)
    rw [CellScheme.mem_below] at hz ⊢
    obtain ⟨hs, hgr⟩ := Prod.mk_le_mk.mp hz
    refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
    · change D.toCellScheme.scope _ ⊆ D.toCellScheme.scope _
      rw [scope_faceCell, scope_faceCell]
      exact map_subset_map.mpr hs
    · change D.toCellScheme.grade _ ≤ D.toCellScheme.grade _
      rw [grade_faceCell, grade_faceCell]
      exact hgr
  have hrow (i : Fin 2) : D.rows.row (faceCell h₂ (donorApex hα)) ⟨_, hy i⟩ =
      blockEncode (apexCodes (t := (donorLower hα).truncate hα.isSuccPrelimit)
        (donorLower hα).isLegalBelowFullGrade) 2 three := by
    rw [← Scheme.rowAt_of_mem (hy i), rowAt_faceCell h₂, Scheme.rowAt_of_mem
      (mem_below_donor_last hα _)]
    exact donor_row_root hα _ _
  have hgy (i : Fin 2) : g (faceCell h₂ (faceCell (restrictFace_donor hα) i)) = rootRow i := by
    rw [← faceCell_faceCell h₁ h₂ (restrictFace_context hα) (restrictFace_donor hα) i, hgz]
    exact separating_root hα i
  have hloc' := (hloc _ hAb).le_of_le (d := ⟨_, hy ⟨1, by decide⟩⟩) (d' := ⟨_, hy ⟨0, by decide⟩⟩)
    (le_of_eq ((hrow _).trans (hrow _).symm)) (by
      rw [grade_faceCell, grade_faceCell]
      exact le_of_eq ((grade_faceCell (restrictFace_donor hα) (⟨0, by decide⟩ : Fin 2)).trans
        (grade_faceCell (restrictFace_donor hα) (⟨1, by decide⟩ : Fin 2)).symm))
  change min (g _) (g _) ≤ min (g _) (g _) at hloc'
  rw [hAtop, min_top_right, min_top_right, hgy, hgy] at hloc'
  exact absurd (natCast_label_le.mp hloc') (by decide)

/-- **Cutoff determination at the context, unfolded**: for every carrier and the permitted cutoff
above its labels other than `⊤`, the donor is determined within the receiving family exactly when
every member literal on the context is `⊤` at every cell of the donor labelled `⊤` (the apex of the
donor among them).  The receiving family does not give it: at a cell where the carrier is `⊤` a
member is only asked to be at least the cutoff. -/
theorem isDeterminedWithin_carrier_iff {D : StageType.{u} α 4}
    (h₂ : restrictFace (extendByLast rootEmb) D = some (donor hα)) :
    ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      (IsDeterminedWithin (receivingFamily D δ) (context hα) rootEmb (donor hα) ↔
        ∀ q ∈ receivingFamily D δ, restrictFace Fin.castSuccEmb q = some (context hα) →
          ∀ (i : Fin q.card) (j : Fin (donor hα).card), (i : ℕ) = faceCell h₂ j →
            (donor hα).label j = ⊤ → q.label i = ⊤) := by
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα D
  exact ⟨δ, hδ, isDeterminedWithin_receivingFamily_iff h₂ hδD⟩

end TiedRootCapCounterexample

end VaughtConjecture
