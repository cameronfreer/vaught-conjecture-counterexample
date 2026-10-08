/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapLowered
import VaughtConjecture.Continuation.TiedRootCapBottomRow

/-!
# Carriers and cofaces at the context with root cells labelled `⊥`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The context of `BottomRootCounterexample` (root cells labelled `⊥`, read by the cap as `1` and `2`)
is an acquired marked-cap context (`BottomRootCounterexample.markedCapContextBelow_context`) whose
cap does not respect the root bottoms (`BottomRootCounterexample.not_markedCapContextBelow'`).
This file tests, at this context, the clause of hollow cutoff determination for every carrier, and
the acquisition of a cap respecting the root bottoms over an occurrence of this type.

**Cutoff determination** (with the zero-one law `StageType.isDeterminedWithin_of_exists`):

* carriers exist (`BottomRootCounterexample.exists_carrier`, compiled in this repository (theorem
  named));
* every carrier has a cell of graded index `(univ, 3)` reading the apex of the donor strictly
  below the cap (`BottomRootCounterexample.exists_cell_reads_lt`, compiled), and a top-reading
  carrier labels it below `⊤` (`BottomRootCounterexample.exists_cell_label_ne_top`, compiled);
* a top-reading carrier gives the clause
  (`BottomRootCounterexample.exists_isDeterminedWithin_of_isTopReadingCarrier`, compiled);
* some carrier determines the donor at no permitted cutoff, for `α` a limit of stages zero or
  limits (`BottomRootCounterexample.exists_carrier_not_isDeterminedWithin`, compiled): the pinned
  extension over the donor capped at `δ + 4`, raised above `δ`
  (`StageType.not_isDeterminedWithin_raiseAbove`).

So the clause at this context holds exactly when some carrier determines at a stage above its
labels (`StageType.isDeterminedWithin_of_exists`), that is, when some carrier `D` and stage `δ`
admit no lawful labelling of the scheme of `D`, literal on the context, agreeing with `D` below
`δ`, at least `δ` where `D` is `⊤`, and below `⊤` at the apex of the donor.  Neither such a
carrier nor the failure of every carrier is compiled (prospective).  The separation of the root
cells enters only through `BottomRootCounterexample.exists_cell_reads_lt`: a member of a receiving
family is literal on the context, so `⊥` at the root cells, and a lawful labelling `⊤` at the cap
and at a cell of graded index `(univ, 3)` reading the apex at least as the cap is `⊤` at the apex,
hence `⊥` at both root cells (the apex reads them as `⊥`; argued, not formalized).

**Acquisition of a cap respecting the root bottoms over an occurrence of this type**:

* **The scheme does not give it** (`BottomRootCounterexample.exists_cell_reads_root_ne_bot`,
  compiled): every legal one-point coface of the context has a cell of graded index `(univ, 3)`
  reading both root cells other than `⊥` (availability and locality of a lawful extension of the
  separating labelling).  So no scheme realized by generalized saturation has all its cells of
  full scope at the grade of the cap respecting the root bottoms; the cap of a realized coface
  respects them only through its labels.
* **The bottom pattern gives it from a selective coface**
  (`BottomRootCounterexample.markedCapContextBelow'_of_mem_bottomPatternFamily`, compiled): if a
  legal coface `qs` of the context has its cells of full scope and grade `4`, and those of grade
  `3` not labelled `⊥`, reading the root cells as `⊥`, then every coface of the context with the
  scheme and the bottom pattern of `qs` (a member of the instance of clause 4(a)ii of
  `Realization.IsModel` that `qs` makes nonempty) is a marked-cap context along the root with root
  offsets below its cap and its cap respecting the root bottoms
  (`TiedRootCapRelabel.MarkedCapContextBelow'`).
* **The selective coface** (`BottomRootCounterexample.HasSelectiveCoface`, a named statement,
  prospective): such a `qs` exists.  Not compiled, not refuted.  An apex added to a completion
  below the full grade labelled literally on the root has the cell of grade `4` required
  (`StageType.rootBottomRespected_of_addApex`); what remains is a lawful labelling, literal on the
  context, `⊥` at every cell of graded index `(univ, 3)` reading a root cell other than `⊥`.

Clauses 4(b) and 4(c) of `Realization.IsModel` (uniformity, high-arity dominance) realize members
of families on uncontrolled schemes, so they place no label at a prescribed cell (argued, not
formalized).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

namespace BottomRootCounterexample

open StageType
open TiedRootCapCounterexample (rootRow rootEmb low isSelfVisible_low le_low low_ne_top low_lt)

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-! ### Carriers -/

/-- **Carriers exist**: a legal one-point extension of the context whose face along
`extendByLast rootEmb` is the donor (the exact pinned extension, by coatom extensions on at most
four points). -/
theorem exists_carrier : ∃ D : StageType.{u} α 4, D.IsLegal ∧
    restrictFace Fin.castSuccEmb D = some (context hα) ∧
    restrictFace (extendByLast rootEmb) D = some (donor hα) :=
  exists_pinned_extension_of_lt (fun m' hm' ta tb p ↦
    exists_coatomExtension_of_le_two hα.isSuccPrelimit (by omega) ta tb p)
    (isLegal_context hα) (restrictFace_context hα) (isLegal_donor hα) (restrictFace_donor hα)

theorem donorApex_scope : Fin.last 1 ∈ (donor hα).toCellScheme.scope (donorApex hα) := by
  have : (donor hα).toCellScheme.scope (Fin.last _) = univ :=
    addApex_scope_last (t := donorLower.truncate hα.isSuccPrelimit)
      donorLower.isLegalBelowFullGrade (Nat.succ_pos _)
  rw [this]
  exact mem_univ _

theorem isTopCap_cap : (context hα).IsTopCap (capCell hα) :=
  ⟨context_scope_cap hα, context_label_cap hα,
    fun x _ ↦ by rw [context_grade_cap]; exact (context hα).grade_le x⟩

theorem context_label_top_or_bot (z : Fin (context hα).card) :
    (context hα).label z = ⊤ ∨ (context hα).label z = ⊥ := by
  induction z using Fin.lastCases with
  | last => exact .inl (context_label_cap hα)
  | cast d => exact .inr (context_label_castSucc hα d)

/-- **Every carrier has a cell of graded index `(univ, 3)` reading the apex of the donor strictly
below the cap.**  Otherwise the separating labelling extends to the carrier with `⊤` at the apex
(`StageType.exists_extend_top_of_reads`), and its restriction to the donor, lawful and `⊤` at the
apex, inverts the two root cells that the apex ties at `⊥`. -/
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

/-- **A top-reading carrier labels such a cell below `⊤`.** -/
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

/-- **Cutoff determination at the context from a top-reading carrier.** -/
theorem exists_isDeterminedWithin_of_isTopReadingCarrier {D : StageType.{u} α 4}
    (hD : (context hα).IsTopReadingCarrier rootEmb (donor hα) (capCell hα) (capCell hα) D) :
    D ∈ (context hα).cofaces ∧ ∃ δ : Label.{u}, IsPermittedCutoff α δ ∧
      IsDeterminedWithin (receivingFamily D δ) (context hα) rootEmb (donor hα) := by
  obtain ⟨δ, hδ, hδD⟩ := exists_isPermittedCutoff_gt hα D
  exact ⟨⟨hD.isLegal, hD.restrictFace_castSucc⟩, δ, hδ,
    isDeterminedWithin_receivingFamily_of_isTopReadingCarrier (restrictFace_context hα)
      (restrictFace_donor hα) (isTopCap_cap hα) (context_label_cap hα)
      (by rw [context_grade_cap]; omega) hD hδD⟩

/-! ### A carrier failing at every cutoff -/

section Lowered

variable {δ : Ordinal.{u}} (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α)

/-- **The lowered donor**: the donor with its labels capped at `δ + 4`. -/
noncomputable def lowDonor (δ : Ordinal.{u}) (hδ : Order.IsSuccPrelimit δ) (hδα : δ < α) :
    StageType.{u} α 2 where
  toScheme := (donor hα).toScheme
  label j := min ((donor hα).label j) (low δ)
  isWellFormed := (donor hα).isWellFormed
  isCoded := (donor hα).isCoded
  isLawful := (donor hα).isLawful.min_const_of_isSelfVisible (K := 4)
    (fun d ↦ ((donor hα).grade_le d).trans (by omega)) (isSelfVisible_low hδ)
  atStage j := .inl ((min_le_right _ _).trans_lt (low_lt hα hδα))

theorem restrictFace_lowDonor :
    restrictFace Fin.castSuccEmb (lowDonor hα δ hδ hδα) = some root := by
  refine (restrictFace_congr_label (t := lowDonor hα δ hδ hδα) (s := donor hα) rfl
    fun i j hij hi ↦ ?_).trans (restrictFace_donor hα)
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨y, rfl⟩ := exists_faceCell_eq (restrictFace_donor hα) hi
  change min ((donor hα).label _) (low δ) = _
  rw [label_faceCell]
  have hy : (root (α := α)).label y = ⊥ := rfl
  rw [hy]
  exact min_eq_left bot_le

theorem lowDonor_apex : (lowDonor hα δ hδ hδα).label (donorApex hα) = low δ := by
  change min ((donor hα).label (donorApex hα)) (low δ) = low δ
  rw [donorApex_label, min_top_left]

/-- **The lowered carrier**: a legal one-point extension of the context whose face along
`extendByLast rootEmb` is the lowered donor (the exact pinned extension). -/
theorem exists_lowCarrier : ∃ D : StageType.{u} α 4, D.IsLegal ∧
    restrictFace Fin.castSuccEmb D = some (context hα) ∧
    restrictFace (extendByLast rootEmb) D = some (lowDonor hα δ hδ hδα) :=
  exists_pinned_extension_of_lt (fun m' hm' ta tb p ↦
    exists_coatomExtension_of_le_two hα.isSuccPrelimit (by omega) ta tb p)
    (isLegal_context hα) (restrictFace_context hα) (isLegal_donor hα)
    (restrictFace_lowDonor hα hδ hδα)

theorem restrictFace_raiseAbove_context {D : StageType.{u} α 4}
    (h₁ : restrictFace Fin.castSuccEmb D = some (context hα)) :
    restrictFace Fin.castSuccEmb (D.raiseAbove δ hδ hδα) = some (context hα) := by
  refine (restrictFace_congr_label (t := D.raiseAbove δ hδ hδα) (s := D) rfl
    fun i j hij hi ↦ ?_).trans h₁
  obtain rfl : i = j := Fin.ext hij
  obtain ⟨z, rfl⟩ := exists_faceCell_eq h₁ hi
  change Label.reduce δ (D.label _) = _
  rw [label_faceCell]
  rcases context_label_top_or_bot hα z with h | h
  · rw [h, reduce_top]
  · rw [h, reduce_bot]

theorem restrictFace_raiseAbove_donor
    (hdδ : ∀ j, (donor hα).label j ≠ ⊤ → (donor hα).label j < δ) {D : StageType.{u} α 4}
    (h₂ : restrictFace (extendByLast rootEmb) D = some (lowDonor hα δ hδ hδα)) :
    restrictFace (extendByLast rootEmb) (D.raiseAbove δ hδ hδα) = some (donor hα) := by
  obtain ⟨hf, hcomap⟩ := (restrictFace_eq_some_iff D _).mp h₂
  rw [restrictFace_of_mem (D.raiseAbove δ hδ hδα) _ hf]
  have hS : (D.comap _ hf).toScheme = (lowDonor hα δ hδ hδα).toScheme :=
    congrArg StageType.toScheme hcomap
  refine congrArg some (StageType.ext hS fun i j hij ↦ ?_)
  have hl : D.label (D.cellMap (extendByLast rootEmb) i) = (lowDonor hα δ hδ hδα).label j :=
    label_congr hcomap (i := i) (j := j) hij
  change Label.reduce δ (D.label (D.cellMap (extendByLast rootEmb) i)) = _
  rw [hl]
  change Label.reduce δ (min ((donor hα).label j) (low δ)) = _
  by_cases hj : (donor hα).label j = ⊤
  · rw [hj, min_top_left, reduce_of_le le_low]
  · rw [min_eq_left ((hdδ j hj).le.trans le_low), reduce_of_lt (hdδ j hj)]

end Lowered

/-- **Some carrier determines the donor at no permitted cutoff.**  Let `α` be a limit of stages
that are zero or limits.  The pinned extension over the donor capped at `δ + 4` (for `δ` above the
labels of the donor other than `⊤`), raised above `δ`, is a legal one-point coface of the context
with face the donor, and it is below `⊤` at the apex of the donor before raising
(`StageType.not_isDeterminedWithin_raiseAbove`). -/
theorem exists_carrier_not_isDeterminedWithin
    (hα₂ : ∀ γ < α, ∃ δ : Ordinal.{u}, Order.IsSuccPrelimit δ ∧ γ < δ ∧ δ < α) :
    ∃ D : StageType.{u} α 4, D ∈ (context hα).cofaces ∧
      restrictFace (extendByLast rootEmb) D = some (donor hα) ∧
      ∀ c : Label.{u}, IsPermittedCutoff α c →
        ¬ IsDeterminedWithin (receivingFamily D c) (context hα) rootEmb (donor hα) := by
  have h0 : ((0 : Ordinal.{u}) : Label.{u}) < α :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hα.bot_lt)
  obtain ⟨c₀, h0c, hcα, -, hc⟩ :=
    exists_isSelfVisible_bound hα.isSuccPrelimit 0 h0 (donor hα).label
  induction c₀ using recBotCoeTop with
  | bot => exact absurd h0c (not_le.mpr (WithBot.bot_lt_coe _))
  | top => exact absurd hcα (not_lt.mpr le_top)
  | coe γ =>
  have hγα : γ < α := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hcα)
  obtain ⟨δ, hδ, hγδ, hδα⟩ := hα₂ γ hγα
  have hγδ' : ((γ : Ordinal.{u}) : Label.{u}) < δ :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr hγδ)
  have hdδ : ∀ j, (donor hα).label j ≠ ⊤ → (donor hα).label j < δ := fun j hj ↦
    (hc j ((donor hα).atStage j |>.resolve_right hj)).trans_lt hγδ'
  obtain ⟨D, hD, h₁, h₂⟩ := exists_lowCarrier hα hδ hδα
  have h₂' := restrictFace_raiseAbove_donor hα hδ hδα hdδ h₂
  refine ⟨D.raiseAbove δ hδ hδα, ⟨hD, restrictFace_raiseAbove_context hα hδ hδα h₁⟩, h₂',
    fun c hc ↦ not_isDeterminedWithin_raiseAbove hα hδ hδα h₁
      (fun z ↦ (context_label_top_or_bot hα z).imp id fun h ↦ by
        rw [h]; exact WithBot.bot_lt_coe _) h₂'
      (donorApex_label hα) (fun i hi ↦ ?_) c hc⟩
  obtain rfl : i = faceCell h₂ (donorApex hα) := Fin.ext hi
  rw [label_faceCell h₂ (donorApex hα), lowDonor_apex]
  exact low_ne_top

/-! ### Acquisition of a cap respecting the root bottoms -/

/-- **Every legal one-point coface of the context has a cell of graded index `(univ, 3)` reading
both root cells other than `⊥`.**  A lawful extension of the separating labelling (`⊤` at the cap,
`1` and `2` at the root cells) is `⊤` at a cell of graded index `(univ, 3)` (availability from the
cap); locality there sends a row entry `⊥` to `⊥`, while the root cells are labelled `1` and `2`. -/
theorem exists_cell_reads_root_ne_bot {D : StageType.{u} α 4} (hD : D.IsLegal)
    (h₁ : restrictFace Fin.castSuccEmb D = some (context hα)) :
    ∃ u, D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) ∧
      ∀ y : Fin 2, D.rowAt u (faceCell h₁ (faceCell (restrictFace_context hα) y)) ≠ ⊥ := by
  obtain ⟨a, ha, hext⟩ := exists_isLawful_extend_of_restrictFace hD h₁ (isLawful_separating hα)
  obtain ⟨u₀, hu₀⟩ := hD.isComplete ((univ : Finset (Fin 4)), 3)
    ⟨D.univ_mem_faces, by omega, by simp⟩
  have hcg : D.toCellScheme.grade (faceCell h₁ (capCell hα)) = 3 :=
    (grade_faceCell h₁ _).trans (context_grade_cap hα)
  obtain ⟨u, hu, hcu⟩ := ha.availability (faceCell h₁ (capCell hα)) u₀
    (by rw [show D.toCellScheme.scope u₀ = univ from congrArg Prod.fst hu₀]; exact subset_univ _)
    (hcg.trans (congrArg Prod.snd hu₀).symm)
  have hut : a u = ⊤ := top_le_iff.mp (by rw [← separating_capCell hα, ← hext]; exact hcu)
  refine ⟨u, hu.trans hu₀, fun y hrow ↦ ?_⟩
  set x := faceCell h₁ (faceCell (restrictFace_context hα) y)
  have hx : x ∈ D.toCellScheme.below (D.toCellScheme.gradedIndex u) := by
    rw [CellScheme.mem_below, hu, hu₀]
    refine Prod.mk_le_mk.mpr ⟨subset_univ _, ?_⟩
    change D.toCellScheme.grade x ≤ 3
    have hg : D.toCellScheme.grade x = (root (α := α)).toCellScheme.grade y :=
      (grade_faceCell h₁ _).trans (grade_faceCell (restrictFace_context hα) y)
    rw [hg]
    exact ((root (α := α)).grade_le y).trans (by omega)
  rw [Scheme.rowAt_of_mem hx] at hrow
  have hbot := (ha.locality u).eq_bot (d := ⟨x, hx⟩) hrow
  change min (a x) (a u) = ⊥ at hbot
  rw [hut, min_top_right, hext, separating_root] at hbot
  exact natCast_label_ne_bot _ hbot

/-- **A selective coface of the context**: a legal one-point coface whose cells of full scope and
grade `4`, and those of grade `3` not labelled `⊥`, read the root cells as `⊥`. -/
def IsSelectiveCoface (qs : StageType.{u} α 4) : Prop :=
  qs ∈ (context hα).cofaces ∧
    ∀ u, qs.toCellScheme.scope u = univ → 3 ≤ qs.toCellScheme.grade u →
      (qs.toCellScheme.grade u = 4 ∨ qs.label u ≠ ⊥) →
        ∀ y ∈ qs.visibleCells (rootEmb.trans Fin.castSuccEmb), qs.rowAt u y = ⊥

/-- **The selective coface** (a named statement, prospective; not compiled, not refuted): the
context has a selective coface. -/
def HasSelectiveCoface : Prop := ∃ qs : StageType.{u} α 4, IsSelectiveCoface hα qs

/-- **The bottom pattern of a selective coface acquires a cap respecting the root bottoms.**  Every
coface of the context with the scheme of a selective coface `qs` and its bottom pattern at the
cells of grade at most `3` is a marked-cap context along the root, with root offsets below its cap
and its cap reading the root cells as `⊥`.  A top cap has full scope and grade at least `3` (the
cap of the context is `⊤`); at the grade `4` the scheme of `qs` reads the root as `⊥`; at the
grade `3` the cap is `⊤`, so not `⊥` in `qs` (the bottom pattern), and is read as in `qs`. -/
theorem markedCapContextBelow'_of_mem_bottomPatternFamily {qs : StageType.{u} α 4}
    (hqs : IsSelectiveCoface hα qs) {q : StageType.{u} α 4}
    (hq : q ∈ (context hα).cofaces ∩ bottomPatternFamily qs.toScheme qs.label) :
    TiedRootCapRelabel.MarkedCapContextBelow' q (rootEmb.trans Fin.castSuccEmb) := by
  obtain ⟨-, hclean⟩ := hqs
  obtain ⟨S, ℓ, hw, hcod, hl, hat⟩ := q
  obtain ⟨⟨hql, hq₁⟩, hS, hpat⟩ := hq
  change S = qs.toScheme at hS
  subst hS
  set q : StageType.{u} α 4 := ⟨qs.toScheme, ℓ, hw, hcod, hl, hat⟩ with hqdef
  have hroot : restrictFace (rootEmb.trans Fin.castSuccEmb) q = some root := by
    rw [← restrictFace_trans _ _ _ hq₁]
    exact restrictFace_context hα
  have hvis (y : Fin q.card) (hy : y ∈ q.visibleCells (rootEmb.trans Fin.castSuccEmb)) :
      q.label y = ⊥ := by
    obtain ⟨z, rfl⟩ := exists_faceCell_eq hroot hy
    rw [label_faceCell]
    rfl
  -- the cap of the context, a cell of `q` of grade `3` labelled `⊤`
  set x₀ : Fin q.card := faceCell hq₁ (capCell hα)
  have hx₀ : q.label x₀ = ⊤ := (label_faceCell hq₁ _).trans (context_label_cap hα)
  have hx₀g : q.toCellScheme.grade x₀ = 3 := (grade_faceCell hq₁ _).trans (context_grade_cap hα)
  have hnt : ¬ q.IsTopFree := fun htf ↦ by
    rw [← StageType.topGrade_eq_zero_iff] at htf
    have := grade_le_topGrade hx₀
    omega
  obtain ⟨c, hc⟩ := StageType.exists_isTopCap hql hnt
  obtain ⟨r, hr⟩ := StageType.exists_isMarker hc.2.1
  have hcg : 3 ≤ q.toCellScheme.grade c := hx₀g ▸ hc.2.2 x₀ hx₀
  refine ⟨c, r, ⟨hc, hr, by omega, fun a ha hat ↦ absurd ((hvis a ha).symm.trans hat) bot_ne_top⟩,
    fun y hy μ f _ hf ↦ absurd ((hvis y hy).symm.trans hf) (WithBot.bot_ne_coe), fun y hy _ ↦ ?_⟩
  have hc4 : q.toCellScheme.grade c ≤ 4 := q.grade_le c
  refine hclean c hc.1 hcg ?_ y hy
  rcases Nat.lt_or_ge (q.toCellScheme.grade c) 4 with h4 | h4
  · right
    exact fun hb ↦ top_ne_bot (hc.2.1.symm.trans ((hpat c c rfl (by omega)).mpr hb))
  · left
    exact le_antisymm hc4 h4

end BottomRootCounterexample

end VaughtConjecture
