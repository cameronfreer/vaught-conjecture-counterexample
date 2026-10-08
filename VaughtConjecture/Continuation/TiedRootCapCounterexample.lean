/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCap
import VaughtConjecture.Extension.CapTransport
import VaughtConjecture.Extension.SmallArityOne
import VaughtConjecture.Extension.SmallArityExamples

/-!
# A legal marked-cap context whose cap separates two tied root cells

Roadmap, Layer 3 ((R3) of the table of 3.4).

A legal instance of the refutation schema `StageType.not_raisesNewTops_of_row_le`, at every limit
stage `α`, with the inverting labelling in the bottom class of the context.

* **The root** (`root`): one point, two cells of graded index `({0}, 1)` with rows `(1, 2)`, both
  labelled `3`; the row `(1, 2)` is lawful (`isLawful_rootRow`) and collapses to `(3, 3)`.
* **The donor** (`donor`, legal): the completion of the seed on two points of two copies of the
  root (arity zero, `Seed.completionBelowFullGradeZero`); its face on the first point is the root.
  Its apex is a new cell labelled `⊤` whose row reads both root cells at the code of `3`.
* **The context** (`context`, legal, `isLegal_context`): the completion below the full grade of
  the seed on three points of two copies of the donor over the root (arity one,
  `Seed.completionBelowFullGradeOne`), labelled by the collapse (`Label.collapseShifter` at `3`)
  of a lawful labelling `ell` that reads the root as `(1, 2)` (an extension from the root face of
  the completion), with the coded cap of `ell` (`StageType.addCodedCap`): a cell of full scope and
  grade `3`, labelled `⊤`, whose row is the coded copy of `ell`.  It is not an apex: its row
  separates the two root cells (`1 < 2`), which its labels tie (`3 = 3`).  Its face along
  `rootEmb` (the point `0`) is the root (`restrictFace_context`).
* **Marked-cap context** (`isMarkedCapContextAt_context`, compiled in this repository (theorem
  named)): the cap is a top cap and its own marker, `1 + 1 < 3`, and no root cell is labelled `⊤`.
* **The raise fails** (`not_raisesNewTopsInClass`, `not_raisesNewTops`, compiled): the separating
  labelling (`ell`, and `⊤` at the cap) is lawful, in the bottom class of the context, `⊤` at the
  cap, and inverts the two root cells that the apex of the donor ties.  The cap does not keep the
  root ties (`not_keepsRootTies`).
* **Consequences** (compiled, at every limit stage, every universe):
  `StageType.not_hasRaisingMarkedCaps` and `StageType.not_hasTopMarkedCarriers` (the universal
  clause over all legal marked-cap contexts of the all-cells top-marked design is false), and
  `StageType.not_exists_correct_carrier` (no legal carrier of the donor over the context has
  correctness at cap and marker `⊤` in the bottom class at the cells of graded index `(univ, 3)`
  that availability reaches).

**What is refuted.**  The clause "for every legal marked-cap context" of
`StageType.HasTopMarkedCarriers` and `StageType.HasRaisingMarkedCaps`, and any carrier design
whose capped correctness at cap and marker `⊤` is asked of every lawful labelling in the bottom
class at this context.  Not refuted: (R3); `StageType.HasTopReadingCarriers` (it reads only at
cells labelled `⊤` in the carrier); any design asked only at the contexts produced by acquisition.
Whether acquisition can avoid such contexts is open: a sufficient property is that the top cap
keeps the root ties (`StageType.KeepsRootTies`, held by apex contexts), and no clause of
modelhood used by `Realization.IsModel.exists_synchronized` controls the row of the top cap beyond
the forced thresholds (argued, not formalized).

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label CellScheme

namespace TiedRootCapCounterexample

open SmallArityExamples StageType

/-! ### The root: one point, two cells -/

/-- The row of the root: `1` at the first cell, `2` at the second. -/
noncomputable def rootRow (i : Fin 2) : Label.{u} := ((i.val + 1 : ℕ) : Label.{u})

/-- The label `3` of the root cells. -/
noncomputable abbrev three : Label.{u} := ((3 : ℕ) : Label.{u})

theorem three_ne_bot : three.{u} ≠ ⊥ := natCast_label_ne_bot 3

theorem three_ne_top : three.{u} ≠ ⊤ := by
  rw [three, natCast_label]
  exact fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)

theorem rootRow_ne_bot (i : Fin 2) : rootRow.{u} i ≠ ⊥ := natCast_label_ne_bot _

theorem rootRow_ne_top (i : Fin 2) : rootRow.{u} i ≠ ⊤ := by
  rw [rootRow, natCast_label]
  exact fun h ↦ WithTop.coe_ne_top (WithBot.coe_injective h)

theorem monotone_rootRow : Monotone rootRow.{u} := fun _ _ h ↦
  natCast_label_le.mpr (Nat.succ_le_succ (Fin.le_iff_val_le_val.mp h))

theorem isSelfVisible_rootRow (i : Fin 2) : IsSelfVisible 1 (rootRow.{u} i) :=
  (isSelfVisible_natCast _).mpr (by omega)

/-- The scheme of the root: two cells of graded index `({0}, 1)`, each with the row `(1, 2)`. -/
noncomputable def rootScheme : Scheme.{u} 1 := onePointScheme 2 rootRow

theorem isLegal_rootScheme : rootScheme.{u}.IsLegal :=
  isLegal_onePointScheme (by decide) monotone_rootRow
    (fun _ ↦ natCast_label_lt_omega0_sq _) isSelfVisible_rootRow

/-- **The row `(1, 2)` is a lawful labelling of the root.** -/
theorem isLawful_rootRow : rootScheme.{u}.rows.IsLawful rootRow where
  orderly d := isSelfVisible_rootRow d
  locality s := (TransformsTo.refl _ _).min_const (K := 1) (fun _ ↦ le_rfl)
    (isSelfVisible_rootRow s)
  availability s _ _ _ := ⟨(⟨1, by decide⟩ : Fin 2), rfl,
    monotone_rootRow (Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ s.isLt))⟩

theorem isWitness_three : IsWitness (stepSuppressor.{u} 3) (collapseShifter three) :=
  isWitness_collapseShifter ((isSelfVisible_natCast 3).mpr le_rfl) three_ne_bot

/-- The constant label `3` is lawful on the root: it collapses the row `(1, 2)`. -/
theorem isLawful_const_three : rootScheme.{u}.rows.IsLawful fun _ ↦ three := by
  have h := isLawful_rootRow.map_of_apply_eq_bot (K := 3) (fun _ ↦ by
      change 1 ≤ 3
      omega) isWitness_three fun d hd ↦ eq_bot_of_collapseShifter_eq_bot three_ne_bot hd
  convert h using 1
  funext d
  exact (collapseShifter_of_ne (rootRow_ne_bot d) (rootRow_ne_top d)).symm

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

include hα in
theorem atStage_three : AtStage α three.{u} :=
  (atStage_natCast 3).mpr (Ordinal.natCast_lt_of_isSuccLimit hα 3)

/-- **The root**: the stage type on one point with two cells of graded index `({0}, 1)`, rows
`(1, 2)`, both labelled `3`. -/
noncomputable def root : StageType.{u} α 1 where
  toScheme := rootScheme
  label _ := three
  isWellFormed := isLegal_rootScheme.isWellFormed
  isCoded := isLegal_rootScheme.isCoded
  isLawful := isLawful_const_three
  atStage _ := atStage_three hα

theorem isLegal_root : (root hα).IsLegal := isLegal_rootScheme

/-! ### The donor: the completion of the seed of two copies of the root -/

theorem exists_face_root : ∃ p, restrictFace (Coatom.face 0) (root hα) = some p :=
  Option.isSome_iff_exists.mp ((root hα).isSome_restrictFace_of_zero _)

/-- The seed on two points of two copies of the root over the empty face. -/
noncomputable def seedTwo : Seed.{u} α 0 :=
  Seed.ofCoatoms (isLegal_root hα) (isLegal_root hα) (exists_face_root hα).choose_spec
    (exists_face_root hα).choose_spec

/-- The completion below the full grade of `seedTwo`. -/
@[irreducible] noncomputable def donorLower : CompletionBelowFullGrade (seedTwo hα) :=
  (seedTwo hα).completionBelowFullGradeZero

/-- **The donor**: the completion of `seedTwo`, on two points, with its apex labelled `⊤`. -/
noncomputable def donor : StageType.{u} α 2 :=
  (donorLower hα).completion hα.isSuccPrelimit

theorem isLegal_donor : (donor hα).IsLegal :=
  CompletionBelowFullGrade.isLegal_completion _ _

/-- The face of the donor on its first point is the root. -/
theorem restrictFace_donor : restrictFace Fin.castSuccEmb (donor hα) = some (root hα) :=
  CompletionBelowFullGrade.restrictFace_left_completion _ _

/-! ### The context: three points, a cap carrying the code of a separating labelling -/

/-- The seed on three points of two copies of the donor over the root. -/
noncomputable def seedThree : Seed.{u} α 1 :=
  Seed.ofCoatoms (isLegal_donor hα) (isLegal_donor hα) (restrictFace_donor hα)
    (restrictFace_donor hα)

/-- The completion below the full grade of `seedThree`. -/
@[irreducible] noncomputable def lower : CompletionBelowFullGrade (seedThree hα) :=
  (seedThree hα).completionBelowFullGradeOne

/-- The embedding of the root point `0` into three points. -/
def rootEmb : Fin 1 ↪ Fin 3 := Fin.castSuccEmb.trans Fin.castSuccEmb

theorem rootEmb_ne_univ : univ.map rootEmb ≠ univ := fun h ↦ by
  have := congrArg Finset.card h
  simp at this

/-- The face of the truncation of `lower` along `rootEmb` is the root. -/
theorem restrictFace_truncate :
    restrictFace rootEmb ((lower hα).truncate hα.isSuccPrelimit) = some (root hα) :=
  ((restrictFace_trans (g := Fin.castSuccEmb)
    (hu := (lower hα).restrictFace_left_truncate hα.isSuccPrelimit)).symm).trans
    (restrictFace_donor hα)

/-- The face of the completion of `lower` along `rootEmb` is the root. -/
theorem restrictFace_completion :
    restrictFace rootEmb ((lower hα).completion hα.isSuccPrelimit) = some (root hα) :=
  (restrictFace_addApex _ _ _ rootEmb_ne_univ).trans (restrictFace_truncate hα)

theorem exists_extension : ∃ a' : Fin ((lower hα).completion hα.isSuccPrelimit).card → Label.{u},
    ((lower hα).completion hα.isSuccPrelimit).rows.IsLawful a' ∧
      ∀ i, a' (faceCell (restrictFace_completion hα) i) = rootRow i :=
  exists_isLawful_extend_of_restrictFace ((lower hα).isLegal_completion _)
    (restrictFace_completion hα) isLawful_rootRow

/-- **The separating labelling**: a lawful labelling of the completion below the full grade that
reads the root as `(1, 2)`. -/
noncomputable def ell : Fin (lower hα).scheme.card → Label.{u} :=
  fun d ↦ (exists_extension hα).choose d.castSucc

theorem isLawful_ell : (lower hα).scheme.rows.IsLawful (ell hα) :=
  (lower hα).isLawful_comp_castSucc hα.isSuccPrelimit (exists_extension hα).choose_spec.1

/-- The cells of the root in the truncation. -/
theorem ell_faceCell (i : Fin 2) :
    ell hα (faceCell (restrictFace_truncate hα) i) = rootRow i := by
  have h := (exists_extension hα).choose_spec.2 i
  rw [show faceCell (restrictFace_completion hα) i =
      (faceCell (restrictFace_truncate hα) i).castSucc
    from (lower hα).faceCell_completion hα.isSuccPrelimit rootEmb_ne_univ
      (restrictFace_truncate hα) (restrictFace_completion hα) i] at h
  exact h

theorem grade_lower_le (d : Fin (lower hα).scheme.card) :
    (lower hα).scheme.toCellScheme.grade d ≤ 3 :=
  ((lower hα).isLegalBelowFullGrade.grade_lt d).le

theorem exists_codes : ∃ V : Finset Label.{u}, (∀ d, ell hα d ∈ V) ∧
    (lower hα).scheme.rows.IsLawful (blockEncode V 3 ∘ ell hα) :=
  (isLawful_ell hα).exists_blockEncode (grade_lower_le hα)

/-- The codes of the separating labelling. -/
noncomputable def codes : Finset Label.{u} := (exists_codes hα).choose

theorem isLawful_lowerLabel :
    (lower hα).scheme.rows.IsLawful (collapseShifter three ∘ ell hα) :=
  (isLawful_ell hα).map_of_apply_eq_bot (grade_lower_le hα) isWitness_three
    fun _ hd ↦ eq_bot_of_collapseShifter_eq_bot three_ne_bot hd

theorem atStage_lowerLabel (d : Fin (lower hα).scheme.card) :
    AtStage α ((collapseShifter three ∘ ell hα) d) := by
  simp only [Function.comp_apply, collapseShifter]
  split_ifs
  · exact atStage_bot
  · exact atStage_top
  · exact atStage_three hα

/-- The completion below the full grade labelled by the collapse of the separating labelling: `⊥`
where it is `⊥`, `⊤` where it is `⊤`, and `3` elsewhere. -/
noncomputable def base : StageType.{u} α 3 :=
  (lower hα).withLabel (isLawful_lowerLabel hα) (atStage_lowerLabel hα)

theorem isLegalBelowFullGrade_base : (base hα).IsLegalBelowFullGrade :=
  (lower hα).isLegalBelowFullGrade

theorem isLawful_apexLabel_base :
    (codedScheme (isLegalBelowFullGrade_base hα) (codes hα) (ell hα)).rows.IsLawful
      (apexLabel (t := base hα)) :=
  isLawful_apexLabel_codedScheme _ isWitness_three
    (fun _ hx ↦ eq_bot_of_collapseShifter_eq_bot three_ne_bot hx) collapseShifter_top
    (exists_codes hα).choose_spec.1 fun _ ↦ rfl

/-- **The context**: three points; below the full grade the completion of `seedThree`, labelled
`⊥`, `3` or `⊤` as the separating labelling is `⊥`, other than `⊥` and `⊤`, or `⊤`; one cell of
full scope and grade `3`, labelled `⊤`, whose row is the coded copy of the separating labelling. -/
noncomputable def context : StageType.{u} α 3 :=
  (base hα).addCodedCap (isLegalBelowFullGrade_base hα) (by omega) (isLawful_apexLabel_base hα)

/-- The top cap of the context. -/
noncomputable abbrev capCell : Fin (context hα).card := Fin.last _

theorem isLegal_context : (context hα).IsLegal :=
  isLegal_addCodedCap _ _ _ (exists_codes hα).choose_spec.2

theorem restrictFace_base : restrictFace rootEmb (base hα) = some (root hα) :=
  (restrictFace_congr_label (t := base hα) (s := (lower hα).truncate hα.isSuccPrelimit) rfl
    fun i j hij hi ↦ by
      obtain rfl : i = j := Fin.ext hij
      obtain ⟨y, rfl⟩ := exists_faceCell_eq (restrictFace_truncate hα) hi
      rw [label_faceCell]
      exact (congrArg (collapseShifter three) (ell_faceCell hα y)).trans
        (collapseShifter_of_ne (rootRow_ne_bot y) (rootRow_ne_top y))).trans
    (restrictFace_truncate hα)

/-- **The face of the context along `rootEmb` is the root.** -/
theorem restrictFace_context : restrictFace rootEmb (context hα) = some (root hα) :=
  (restrictFace_addCodedCap _ _ _ rootEmb rootEmb_ne_univ).trans (restrictFace_base hα)

/-! ### The marked-cap context, and the failure of the raise -/

/-- The cells of the root keep the label `3` in the context. -/
theorem context_label_root (y : Fin (root hα).card) :
    (context hα).label (faceCell (restrictFace_context hα) y) = three :=
  label_faceCell _ y

theorem context_label_castSucc (d : Fin (base hα).card) :
    (context hα).label d.castSucc = collapseShifter three (ell hα d) :=
  addCodedCap_label_castSucc (isLegalBelowFullGrade_base hα) (by omega)
    (isLawful_apexLabel_base hα) d

theorem context_label_cap : (context hα).label (capCell hα) = ⊤ :=
  addCodedCap_label_last (isLegalBelowFullGrade_base hα) (by omega) (isLawful_apexLabel_base hα)

theorem context_gradedIndex_cap :
    (context hα).toCellScheme.gradedIndex (capCell hα) = (univ, 3) :=
  addCodedCap_gradedIndex_last (isLegalBelowFullGrade_base hα) (by omega)
    (isLawful_apexLabel_base hα)

theorem context_grade_cap : (context hα).toCellScheme.grade (capCell hα) = 3 :=
  congrArg Prod.snd (context_gradedIndex_cap hα)

theorem context_scope_cap : (context hα).toCellScheme.scope (capCell hα) = univ :=
  congrArg Prod.fst (context_gradedIndex_cap hα)

theorem context_rowAt_cap (z : Fin (context hα).card) :
    (context hα).toScheme.rowAt (capCell hα) z = codedRow (codes hα) (ell hα) z :=
  rowAt_addCodedCap_last (isLegalBelowFullGrade_base hα) (by omega) (isLawful_apexLabel_base hα) z

/-- **The separating labelling of the context**: the separating labelling below the full grade,
and `⊤` at the cap. -/
noncomputable def separating : Fin (context hα).card → Label.{u} := topExtension (ell hα)

theorem isLawful_separating : (context hα).rows.IsLawful (separating hα) :=
  isLawful_topExtension (isLegalBelowFullGrade_base hα) (isLawful_ell hα)
    (exists_codes hα).choose_spec.1

theorem separating_capCell : separating hα (capCell hα) = ⊤ := topExtension_last _

theorem separating_castSucc (d : Fin (base hα).card) : separating hα d.castSucc = ell hα d :=
  topExtension_castSucc _ d

/-- The separating labelling reads the root as `(1, 2)`. -/
theorem separating_root (y : Fin 2) :
    separating hα (faceCell (restrictFace_context hα) y) = rootRow y := by
  have h := faceCell_addCodedCap (isLegalBelowFullGrade_base hα) (by omega)
    (isLawful_apexLabel_base hα) rootEmb_ne_univ (restrictFace_base hα)
    (restrictFace_context hα) y
  exact (congrArg (separating hα) h).trans ((separating_castSucc hα _).trans (ell_faceCell hα y))

/-- **The separating labelling is in the bottom class of the context.** -/
theorem separating_eq_bot_iff (z : Fin (context hα).card) :
    separating hα z = ⊥ ↔ (context hα).label z = ⊥ := by
  induction z using Fin.lastCases with
  | last =>
    exact ⟨fun h ↦ absurd ((separating_capCell hα).symm.trans h) top_ne_bot,
      fun h ↦ absurd ((context_label_cap hα).symm.trans h) top_ne_bot⟩
  | cast d =>
    rw [context_label_castSucc, separating_castSucc]
    exact ⟨fun h ↦ by rw [h]; exact collapseShifter_bot,
      eq_bot_of_collapseShifter_eq_bot three_ne_bot⟩

/-- **The context is a marked-cap context** along `rootEmb`, with the cap as top cap and marker:
the cap has full scope and grade `3`, its row is least at itself among the cells labelled `⊤`
(they are read at the code of `⊤`), `1 + 1 < 3`, and no cell of the root is labelled `⊤`. -/
theorem isMarkedCapContextAt_context :
    (context hα).IsMarkedCapContextAt rootEmb (capCell hα) (capCell hα) := by
  have hc : (context hα).IsTopCap (capCell hα) :=
    ⟨context_scope_cap hα, context_label_cap hα,
      fun x _ ↦ by rw [context_grade_cap]; exact (context hα).grade_le x⟩
  refine ⟨hc, ⟨context_label_cap hα, (context hα).toCellScheme.mem_below_gradedIndex _,
    fun x hx _ ↦ ?_⟩, by rw [context_grade_cap]; omega, fun a ha hat ↦ ?_⟩
  · rw [context_rowAt_cap, context_rowAt_cap]
    induction x using Fin.lastCases with
    | last => exact le_rfl
    | cast d =>
      rw [context_label_castSucc] at hx
      have h1 : codedRow (t := base hα) (codes hα) (ell hα) (Fin.last _) =
          blockEncode (codes hα) 3 ⊤ := codedRow_last _ _
      have h2 : codedRow (t := base hα) (codes hα) (ell hα) d.castSucc =
          blockEncode (codes hα) 3 (ell hα d) := codedRow_castSucc _ _ d
      rw [eq_top_of_collapseShifter_eq_top three_ne_top hx] at h2
      exact (h1.trans h2.symm).le
  · obtain ⟨y, rfl⟩ := exists_faceCell_eq (restrictFace_context hα) ha
    exact absurd ((context_label_root hα y).symm.trans hat) three_ne_top

/-- The apex of the donor reads every cell of the root at the code of `3`. -/
theorem donor_row_root (y : Fin (root hα).card)
    (hy : faceCell (restrictFace_donor hα) y ∈
      (donor hα).toCellScheme.below ((donor hα).toCellScheme.gradedIndex (Fin.last _))) :
    (donor hα).rows.row (Fin.last _) ⟨faceCell (restrictFace_donor hα) y, hy⟩ =
      blockEncode (apexCodes (t := (donorLower hα).truncate hα.isSuccPrelimit)
        (donorLower hα).isLegalBelowFullGrade) 2 three := by
  have h := row_addApex_last_eq (t₀ := (donorLower hα).truncate hα.isSuccPrelimit)
    (donorLower hα).isLegalBelowFullGrade (Nat.succ_pos _) hy
  refine h.trans (congrArg (blockEncode _ 2) ?_)
  exact (label_faceCell (restrictFace_donor hα) y :)

theorem mem_below_donor_last (z : Fin (donor hα).card) :
    z ∈ (donor hα).toCellScheme.below ((donor hα).toCellScheme.gradedIndex (Fin.last _)) := by
  have hlast : (donor hα).toCellScheme.gradedIndex (Fin.last _) = (univ, 2) :=
    addApex_gradedIndex_last (t := (donorLower hα).truncate hα.isSuccPrelimit)
      (donorLower hα).isLegalBelowFullGrade
      (Nat.succ_pos _)
  rw [CellScheme.mem_below, hlast]
  exact Prod.mk_le_mk.mpr ⟨subset_univ _, (donor hα).grade_le z⟩

/-- **The raise fails in the bottom class at the context**: the separating labelling is lawful,
in the bottom class, `⊤` at the cap (top cap and marker), and labels the second root cell `2`
above the first, `1`; the apex of the donor, a new cell labelled `⊤`, reads both at the code of
`3`, so every lawful labelling of the donor labelling it `⊤` ties them. -/
theorem not_raisesNewTopsInClass :
    ¬ (context hα).RaisesNewTopsInClass (restrictFace_context hα) (donor hα)
      (restrictFace_donor hα) (capCell hα) (capCell hα) := by
  refine not_raisesNewTopsInClass_of_row_le (restrictFace_context hα) (restrictFace_donor hα)
    (isLawful_separating hα) (separating_eq_bot_iff hα) (separating_capCell hα)
    (separating_capCell hα)
    (j := Fin.last _) (by
      have : (donor hα).toCellScheme.scope (Fin.last _) = univ :=
        addApex_scope_last (t := (donorLower hα).truncate hα.isSuccPrelimit)
          (donorLower hα).isLegalBelowFullGrade (Nat.succ_pos _)
      rw [this]
      exact mem_univ _)
    (addApex_label_last (t := (donorLower hα).truncate hα.isSuccPrelimit)
      (donorLower hα).isLegalBelowFullGrade
      (Nat.succ_pos _))
    (y₁ := (⟨1, by decide⟩ : Fin 2)) (y₂ := (⟨0, by decide⟩ : Fin 2))
    (mem_below_donor_last hα _) (mem_below_donor_last hα _) ?_ le_rfl ?_
  · exact le_of_eq ((donor_row_root hα _ _).trans (donor_row_root hα _ _).symm)
  · rw [separating_root, separating_root]
    exact natCast_label_lt.mpr (by decide)

/-- **The raise fails at the context.** -/
theorem not_raisesNewTops :
    ¬ (context hα).RaisesNewTops (restrictFace_context hα) (donor hα)
      (restrictFace_donor hα) (capCell hα) (capCell hα) :=
  fun h ↦ not_raisesNewTopsInClass hα h.inClass

/-- **The cap of the context does not keep the root ties.** -/
theorem not_keepsRootTies : ¬ (context hα).KeepsRootTies rootEmb (capCell hα) := by
  intro hk
  have h := le_of_keepsRootTies hk (context_scope_cap hα)
    (by rw [context_grade_cap]; omega) (isLawful_separating hα) (separating_capCell hα)
    (faceCell_mem_visibleCells (restrictFace_context hα) (⟨1, by decide⟩ : Fin 2))
    (faceCell_mem_visibleCells (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2))
    ((context_label_root hα _).trans (context_label_root hα _).symm).le
    (le_of_eq (by erw [grade_faceCell, grade_faceCell]; rfl))
  rw [separating_root, separating_root] at h
  exact absurd (natCast_label_le.mp h) (by decide)

end TiedRootCapCounterexample

/-! ### Consequences at every limit stage -/

namespace StageType

open TiedRootCapCounterexample

variable {α : Ordinal.{u}}

/-- **Raising marked caps fails at every limit stage**: the context of
`TiedRootCapCounterexample` is a legal marked-cap context along `rootEmb` (top cap and marker the
cap), the donor is legal, and the raise fails there. -/
theorem not_hasRaisingMarkedCaps (hα : Order.IsSuccLimit α) : ¬ HasRaisingMarkedCaps.{u} α :=
  fun H ↦ not_raisesNewTops hα (H (context hα) rootEmb (root hα) (restrictFace_context hα)
    (donor hα) (restrictFace_donor hα) (capCell hα) (capCell hα) (isLegal_context hα)
    (isLegal_donor hα) (isMarkedCapContextAt_context hα))

/-- **Top-marked carriers fail at every limit stage** (the all-cells design). -/
theorem not_hasTopMarkedCarriers (hα : Order.IsSuccLimit α) : ¬ HasTopMarkedCarriers.{u} α :=
  fun H ↦ not_hasRaisingMarkedCaps hα H.hasRaisingMarkedCaps

/-- **No carrier with correctness at cap and marker `⊤` in the bottom class exists at the
context**: no legal one-point extension of the context carrying the donor has the property that,
at every cell of graded index `(univ, 3)` labelled `⊤` by a lawful labelling whose part on the
context is in its bottom class and `⊤` at the cap, that labelling is `⊤` at the new tops of the
donor. -/
theorem not_exists_correct_carrier (hα : Order.IsSuccLimit α) :
    ¬ ∃ (D : StageType.{u} α 4) (_ : D.IsLegal)
      (h₁ : restrictFace Fin.castSuccEmb D = some (context hα))
      (h₂ : restrictFace (extendByLast rootEmb) D = some (donor hα)),
      ∀ a' : Fin D.card → Label.{u}, D.rows.IsLawful a' → ∀ u,
        D.toCellScheme.gradedIndex u = ((univ : Finset (Fin 4)), 3) → a' u = ⊤ →
        (∀ z, a' (faceCell h₁ z) = ⊥ ↔ (context hα).label z = ⊥) →
        a' (faceCell h₁ (capCell hα)) = ⊤ → a' (faceCell h₁ (capCell hα)) = ⊤ →
        ∀ j, Fin.last 1 ∈ (donor hα).toCellScheme.scope j → (donor hα).label j = ⊤ →
          a' (faceCell h₂ j) = ⊤ :=
  fun ⟨_, hD, h₁, h₂, hcorr⟩ ↦ not_raisesNewTopsInClass hα
    (raisesNewTopsInClass_of_correct (restrictFace_context hα) (restrictFace_donor hα) hD h₁ h₂
      (context_grade_cap hα) hcorr)

end StageType

end VaughtConjecture
