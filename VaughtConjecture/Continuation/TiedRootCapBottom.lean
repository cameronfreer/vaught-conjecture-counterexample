/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import VaughtConjecture.Continuation.TiedRootCapRelabel
import VaughtConjecture.Continuation.TiedRootCapEngine

/-!
# The engine's coatom provision at an acquired context: root cells labelled `⊥`

Roadmap, Layer 3 ((R3) of the table of 3.4).

The engine's admission of correct states (on the engine's branch: `Adm` the correct states,
`InClass` everything, `CapBot` the states with private cap `⊥`) asks, through its coatom provision
from the grade of the cap, that every state lawful below the private coatom and `⊤` at the cap
extend to a correct state lawful on the cut.  This file tests it at an **acquired** marked-cap
context, one whose root offsets lie below the grade of its cap
(`TiedRootCapRelabel.MarkedCapContextBelow`).

* **The forbidden-extension lemma** (`TiedRootCapEngine.not_coatomProvision_of_forbidden`,
  compiled in this repository (theorem named)): a state lawful below a coatom, `⊤` at a cell of the
  grade `N` below it, whose cut-lawful extensions all violate a consequence of admission at cap
  `⊤`, refutes the coatom provision from the grade `N`.
* **The coded cap over a type labelled `⊥`** (`StageType.isLawful_apexLabel_codedScheme_of_bot`,
  with `Label.keepTopShifter`, compiled).
* **The instance** (`BottomRootCounterexample`, compiled): the root of
  `TiedRootCapCounterexample` (rows `(1, 2)`) labelled `⊥`; its donor (the completion of two
  copies), whose apex reads both root cells at `⊥`; the context (the coded cap, over the completion
  below the full grade labelled `⊥`, of a labelling reading the root as `(1, 2)` and capped at
  `3`).  The context is an acquired marked-cap context
  (`BottomRootCounterexample.markedCapContextBelow_context`: the root labels are `⊥`, so the
  offset bound holds vacuously).
* **The provision fails** (`BottomRootCounterexample.not_coatomProvision`, compiled): over the
  seed of the context and a three-point carrier of the donor, for every set `T` of cells read
  from below containing the donor's apex, `¬ CoatomProvision seedFour 3 (capRequestsT T).IsCorrect`.
  The separating labelling, `⊤` at the cap, separates two root cells labelled `⊥` that the donor's
  apex ties.  It is outside the bottom class of the context
  (`BottomRootCounterexample.separating_not_inClass`).

**What fails.**  The root offset bound keeps ordinal root ties (`StageType.le_of_rootOffsetsBelow`)
and the row inequality keeps ties at `⊤` at labellings `⊤` at the marker; ties at `⊥` are kept only
by the bottom class.  The engine's admission of correct states has no bottom class, so its coatom
provision asks the raise at labellings separating root cells labelled `⊥`, and fails there.

## Placement

This file belongs to Layer 3 of `roadmap/README.md`.
-/

universe u

namespace VaughtConjecture

open Finset Label

/-! ### The provision fails at a forbidden extension -/

namespace TiedRootCapEngine

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m}

/-- **The coatom provision fails at a state whose extensions are all forbidden.**  Let `W` be
lawful below the coatom `univ.erase x` at the grade `N`, `⊤` at a cell `capA` of the grade `N`
below that coatom, and let every admitted state `⊤` at `capA` have a property `Q`.  If no state
lawful on the grade-`N` cut and agreeing with `W` below the coatom has its splice with `Q`, the
coatom provision from the grade `N` fails. -/
theorem not_coatomProvision_of_forbidden {N : ℕ} (hN0 : 0 < N) (hNm : N ≤ m + 1)
    {x : Fin (m + 2)} (hx : x ∈ (Pts : Finset (Fin (m + 2)))) {Adm Q : Prof I → Prop}
    {W : Prof I} (hW : I.amalgam.rows.IsLawfulBelow (univ.erase x, N) (fun d ↦ W d))
    {capA : Fin I.amalgam.card} (hcapg : I.amalgam.toCellScheme.grade capA = N)
    (hcapb : capA ∈ I.amalgam.toCellScheme.below (univ.erase x, N)) (hcap : W capA = ⊤)
    (hAdm : ∀ s, Adm s → s capA = ⊤ → Q s)
    (hforbid : ∀ W', IsCutLawful I N W' →
      (∀ d ∈ I.amalgam.toCellScheme.below (univ.erase x, N), W' d = W d) → ¬ Q (hat I N W')) :
    ¬ CoatomProvision I N Adm := by
  intro hprov
  obtain ⟨W', hW', hW'W, hpr⟩ := hprov le_rfl hN0 hNm hx hW
  have hcap' : W' capA = ⊤ := (hW'W _ hcapb).trans hcap
  have hadm := (provisionAt_iff_of_eq_top hcapg hcap').mp hpr
  exact hforbid W' hW' hW'W (hAdm _ hadm (by rw [hat_of_le hcapg.le]; exact hcap'))

end TiedRootCapEngine

/-! ### A shifter keeping only the formal top -/

namespace Label

open Classical in
/-- The shifter sending the formal top to itself and every other label to `⊥`. -/
noncomputable def keepTopShifter (x : Label.{u}) : Label.{u} := if x = ⊤ then ⊤ else ⊥

theorem keepTopShifter_top : keepTopShifter (⊤ : Label.{u}) = ⊤ := by simp [keepTopShifter]

theorem keepTopShifter_of_ne {x : Label.{u}} (h : x ≠ ⊤) : keepTopShifter x = ⊥ := by
  simp [keepTopShifter, h]

theorem monotone_keepTopShifter : Monotone (keepTopShifter : Label.{u} → Label.{u}) :=
    fun a b hab ↦ by
  by_cases hb : b = ⊤
  · rw [hb, keepTopShifter_top]; exact le_top
  · have ha : a ≠ ⊤ := fun h ↦ hb (top_le_iff.mp (h ▸ hab))
    rw [keepTopShifter_of_ne ha]; exact bot_le

theorem keepTopShifter_visibilityReplace (k i : ℕ) (x : Label.{u}) :
    keepTopShifter (visibilityReplace k i x) = visibilityReplace k i (keepTopShifter x) := by
  induction x using recBotCoeTop with
  | bot => rw [visibilityReplace_bot, keepTopShifter_of_ne bot_ne_top, visibilityReplace_bot]
  | top => rw [visibilityReplace_top, keepTopShifter_top, visibilityReplace_top]
  | coe o =>
    rw [visibilityReplace_coe, keepTopShifter_of_ne (by simp), keepTopShifter_of_ne (by simp),
      visibilityReplace_bot]

end Label

/-! ### The coded cap over a type labelled `⊥` -/

namespace StageType

variable {α : Ordinal.{u}} {n : ℕ} {t : StageType.{u} α n} (ht : t.IsLegalBelowFullGrade)
  {V : Finset Label.{u}} {ℓ : Fin t.card → Label.{u}}

/-- **Over a type labelled `⊥`, the labels with `⊤` at the coded cap are lawful** when `ℓ` is
never the formal top: the block decoding followed by the shifter keeping only `⊤`. -/
theorem isLawful_apexLabel_codedScheme_of_bot (hbot : ∀ d, t.label d = ⊥)
    (hℓ : ∀ d, ℓ d ≠ ⊤) (hV : ∀ d, ℓ d ∈ V) :
    (codedScheme ht V ℓ).rows.IsLawful (apexLabel (t := t)) := by
  refine Scheme.isLawful_appendFullCell ?_ ?_ ?_ fun d hd ↦ absurd hd (ht.grade_lt d).ne
  · convert t.isLawful using 1
    funext d
    exact apexLabel_castSucc d
  · rw [apexLabel_last]
    exact isSelfVisible_top n
  · have hw : IsWitness (fun _ ↦ (⊤ : Label.{u})) (keepTopShifter ∘ blockDecode V) :=
      ⟨antitone_const, fun _ ↦ isSelfVisible_top _, by
        simp [blockDecode_bot, keepTopShifter_of_ne bot_ne_top],
        monotone_keepTopShifter.comp isWitness_blockDecode.monotone, fun x k _ i hi ↦ by
          simp only [Function.comp_apply]
          rw [isWitness_blockDecode.visibilityReplace_comm x k le_top i hi,
            keepTopShifter_visibilityReplace]⟩
    refine ⟨fun _ ↦ ⊤, keepTopShifter ∘ blockDecode V, hw, fun d ↦ ?_⟩
    beta_reduce
    rw [min_top_right, apexLabel_last, min_top_right]
    induction d using Fin.lastCases with
    | last =>
      rw [apexLabel_last, Function.comp_apply, codedRow_last, blockDecode_blockEncode_top,
        keepTopShifter_top]
    | cast d =>
      rw [apexLabel_castSucc, Function.comp_apply, codedRow_castSucc,
        blockDecode_blockEncode (hV d), keepTopShifter_of_ne (hℓ d), hbot]

end StageType

/-! ### The instance: a context with its root labelled `⊥` -/

namespace BottomRootCounterexample

open StageType TiedRootCapEngine TiedRootCapRelabel
open TiedRootCapCounterexample (rootScheme isLegal_rootScheme rootRow isLawful_rootRow three
  three_ne_top rootEmb rootEmb_ne_univ isWitness_three)

variable {α : Ordinal.{u}} (hα : Order.IsSuccLimit α)

/-- **The root**: the scheme of `TiedRootCapCounterexample.rootScheme` (two cells of graded index
`({0}, 1)`, rows `(1, 2)`) labelled `⊥`. -/
noncomputable def root : StageType.{u} α 1 := isLegal_rootScheme.toStageType α

theorem isLegal_root : (root (α := α)).IsLegal := isLegal_rootScheme.isLegal_toStageType α

theorem exists_face_root : ∃ p, restrictFace (Coatom.face 0) (root (α := α)) = some p :=
  Option.isSome_iff_exists.mp ((root (α := α)).isSome_restrictFace_of_zero _)

/-- The seed on two points of two copies of the root. -/
noncomputable def seedTwo : Seed.{u} α 0 :=
  Seed.ofCoatoms isLegal_root isLegal_root exists_face_root.choose_spec
    exists_face_root.choose_spec

@[irreducible] noncomputable def donorLower : CompletionBelowFullGrade (seedTwo (α := α)) :=
  (seedTwo (α := α)).completionBelowFullGradeZero

/-- **The donor**: the completion of `seedTwo`; its apex is labelled `⊤` and reads both root cells
at `⊥` (the code of their label). -/
noncomputable def donor : StageType.{u} α 2 := donorLower.completion hα.isSuccPrelimit

theorem isLegal_donor : (donor hα).IsLegal := CompletionBelowFullGrade.isLegal_completion _ _

theorem restrictFace_donor : restrictFace Fin.castSuccEmb (donor hα) = some root :=
  CompletionBelowFullGrade.restrictFace_left_completion _ _

/-- The seed on three points of two copies of the donor over the root. -/
noncomputable def seedThree : Seed.{u} α 1 :=
  Seed.ofCoatoms (isLegal_donor hα) (isLegal_donor hα) (restrictFace_donor hα)
    (restrictFace_donor hα)

@[irreducible] noncomputable def lower : CompletionBelowFullGrade (seedThree hα) :=
  (seedThree hα).completionBelowFullGradeOne

theorem restrictFace_truncate :
    restrictFace rootEmb ((lower hα).truncate hα.isSuccPrelimit) = some root :=
  ((restrictFace_trans (g := Fin.castSuccEmb)
    (hu := (lower hα).restrictFace_left_truncate hα.isSuccPrelimit)).symm).trans
    (restrictFace_donor hα)

theorem restrictFace_completion :
    restrictFace rootEmb ((lower hα).completion hα.isSuccPrelimit) = some root :=
  (restrictFace_addApex _ _ _ rootEmb_ne_univ).trans (restrictFace_truncate hα)

theorem exists_extension : ∃ a' : Fin ((lower hα).completion hα.isSuccPrelimit).card → Label.{u},
    ((lower hα).completion hα.isSuccPrelimit).rows.IsLawful a' ∧
      ∀ i, a' (faceCell (restrictFace_completion hα) i) = rootRow i :=
  exists_isLawful_extend_of_restrictFace ((lower hα).isLegal_completion _)
    (restrictFace_completion hα) isLawful_rootRow

/-- **The separating labelling**: a lawful labelling of the completion below the full grade that
reads the root as `(1, 2)`, capped at `3` (never `⊤`). -/
noncomputable def ell : Fin (lower hα).scheme.card → Label.{u} :=
  fun d ↦ min ((exists_extension hα).choose d.castSucc) three

theorem isLawful_ell : (lower hα).scheme.rows.IsLawful (ell hα) :=
  ((lower hα).isLawful_comp_castSucc hα.isSuccPrelimit
    (exists_extension hα).choose_spec.1).min_const_of_isSelfVisible (K := 3)
    (fun d ↦ ((lower hα).isLegalBelowFullGrade.grade_lt d).le)
    ((isSelfVisible_natCast 3).mpr le_rfl)

theorem ell_ne_top (d : Fin (lower hα).scheme.card) : ell hα d ≠ ⊤ :=
  ne_top_of_le_ne_top three_ne_top (min_le_right _ _)

theorem ell_faceCell (i : Fin 2) :
    ell hα (faceCell (restrictFace_truncate hα) i) = rootRow i := by
  have h := (exists_extension hα).choose_spec.2 i
  rw [show faceCell (restrictFace_completion hα) i =
      (faceCell (restrictFace_truncate hα) i).castSucc
    from (lower hα).faceCell_completion hα.isSuccPrelimit rootEmb_ne_univ
      (restrictFace_truncate hα) (restrictFace_completion hα) i] at h
  have hle : rootRow i ≤ three := natCast_label_le.mpr (by have := i.isLt; omega)
  exact (congrArg (fun z ↦ min z three) h).trans (min_eq_left hle)

theorem exists_codes : ∃ V : Finset Label.{u}, (∀ d, ell hα d ∈ V) ∧
    (lower hα).scheme.rows.IsLawful (blockEncode V 3 ∘ ell hα) :=
  (isLawful_ell hα).exists_blockEncode fun d ↦ ((lower hα).isLegalBelowFullGrade.grade_lt d).le

noncomputable def codes : Finset Label.{u} := (exists_codes hα).choose

/-- The completion below the full grade labelled `⊥`. -/
noncomputable def base : StageType.{u} α 3 :=
  (lower hα).withLabel CellScheme.Rows.isLawful_const_bot fun _ ↦ atStage_bot

theorem isLegalBelowFullGrade_base : (base hα).IsLegalBelowFullGrade :=
  (lower hα).isLegalBelowFullGrade

theorem isLawful_apexLabel_base :
    (codedScheme (isLegalBelowFullGrade_base hα) (codes hα) (ell hα)).rows.IsLawful
      (apexLabel (t := base hα)) :=
  isLawful_apexLabel_codedScheme_of_bot _ (fun _ ↦ rfl) (ell_ne_top hα)
    (exists_codes hα).choose_spec.1

/-- **The context**: three points; below the full grade the completion of `seedThree` labelled
`⊥`; one cell of full scope and grade `3`, labelled `⊤`, whose row is the coded copy of `ell`. -/
noncomputable def context : StageType.{u} α 3 :=
  (base hα).addCodedCap (isLegalBelowFullGrade_base hα) (by omega) (isLawful_apexLabel_base hα)

noncomputable abbrev capCell : Fin (context hα).card := Fin.last _

theorem isLegal_context : (context hα).IsLegal :=
  isLegal_addCodedCap _ _ _ (exists_codes hα).choose_spec.2

theorem restrictFace_base : restrictFace rootEmb (base hα) = some root :=
  (restrictFace_congr_label (t := base hα) (s := (lower hα).truncate hα.isSuccPrelimit) rfl
    fun i j hij hi ↦ by
      obtain rfl : i = j := Fin.ext hij
      obtain ⟨y, rfl⟩ := exists_faceCell_eq (restrictFace_truncate hα) hi
      rw [label_faceCell]
      rfl).trans (restrictFace_truncate hα)

theorem restrictFace_context : restrictFace rootEmb (context hα) = some root :=
  (restrictFace_addCodedCap _ _ _ rootEmb rootEmb_ne_univ).trans (restrictFace_base hα)

theorem context_label_castSucc (d : Fin (base hα).card) : (context hα).label d.castSucc = ⊥ :=
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

theorem eq_cap_of_label_eq_top {x : Fin (context hα).card} (hx : (context hα).label x = ⊤) :
    x = capCell hα := by
  induction x using Fin.lastCases with
  | last => rfl
  | cast d => exact absurd ((context_label_castSucc hα d).symm.trans hx) bot_ne_top

/-- **The context is an acquired marked-cap context**: the cap is the only cell labelled `⊤`, so
it is a top cap and its own marker; no root cell is labelled `⊤`; the root labels are `⊥`, so the
root offsets lie below every grade. -/
theorem markedCapContextBelow_context : MarkedCapContextBelow (context hα) rootEmb := by
  have hc : (context hα).IsTopCap (capCell hα) :=
    ⟨context_scope_cap hα, context_label_cap hα,
      fun x _ ↦ by rw [context_grade_cap]; exact (context hα).grade_le x⟩
  refine ⟨capCell hα, capCell hα, ⟨hc, ⟨context_label_cap hα,
    (context hα).toCellScheme.mem_below_gradedIndex _, fun x hx _ ↦ ?_⟩,
    by rw [context_grade_cap]; omega, fun a ha hat ↦ ?_⟩, fun y hy μ f _ hf ↦ ?_⟩
  · rw [eq_cap_of_label_eq_top hα hx]
  · obtain ⟨z, rfl⟩ := exists_faceCell_eq (restrictFace_context hα) ha
    rw [label_faceCell] at hat
    exact absurd hat bot_ne_top
  · obtain ⟨z, rfl⟩ := exists_faceCell_eq (restrictFace_context hα) hy
    rw [label_faceCell] at hf
    exact absurd hf.symm WithBot.coe_ne_bot

/-- The separating labelling of the context: `ell` with `⊤` at the cap. -/
noncomputable def separating : Fin (context hα).card → Label.{u} := topExtension (ell hα)

theorem isLawful_separating : (context hα).rows.IsLawful (separating hα) :=
  isLawful_topExtension (isLegalBelowFullGrade_base hα) (isLawful_ell hα)
    (exists_codes hα).choose_spec.1

theorem separating_capCell : separating hα (capCell hα) = ⊤ := topExtension_last _

theorem separating_root (y : Fin 2) :
    separating hα (faceCell (restrictFace_context hα) y) = rootRow y := by
  have h := faceCell_addCodedCap (isLegalBelowFullGrade_base hα) (by omega)
    (isLawful_apexLabel_base hα) rootEmb_ne_univ (restrictFace_base hα)
    (restrictFace_context hα) y
  exact (congrArg (separating hα) h).trans ((topExtension_castSucc _ _).trans (ell_faceCell hα y))

/-! ### The donor's apex -/

noncomputable abbrev donorApex : Fin (donor hα).card := Fin.last _

theorem donorApex_label : (donor hα).label (donorApex hα) = ⊤ :=
  addApex_label_last (t := donorLower.truncate hα.isSuccPrelimit)
    donorLower.isLegalBelowFullGrade (Nat.succ_pos _)

theorem mem_below_donor_last (z : Fin (donor hα).card) :
    z ∈ (donor hα).toCellScheme.below ((donor hα).toCellScheme.gradedIndex (Fin.last _)) := by
  have hlast : (donor hα).toCellScheme.gradedIndex (Fin.last _) = (univ, 2) :=
    addApex_gradedIndex_last (t := donorLower.truncate hα.isSuccPrelimit)
      donorLower.isLegalBelowFullGrade (Nat.succ_pos _)
  rw [CellScheme.mem_below, hlast]
  exact Prod.mk_le_mk.mpr ⟨subset_univ _, (donor hα).grade_le z⟩

/-- The apex of the donor reads every cell of the root at `⊥` (the code of `⊥`). -/
theorem donor_row_root (y : Fin root.card)
    (hy : faceCell (restrictFace_donor hα) y ∈
      (donor hα).toCellScheme.below ((donor hα).toCellScheme.gradedIndex (Fin.last _))) :
    (donor hα).rows.row (Fin.last _) ⟨faceCell (restrictFace_donor hα) y, hy⟩ = ⊥ := by
  have h := row_addApex_last_eq (t₀ := donorLower.truncate hα.isSuccPrelimit)
    donorLower.isLegalBelowFullGrade (Nat.succ_pos _) hy
  refine h.trans ?_
  have hl : (donor hα).label (faceCell (restrictFace_donor hα) y) = ⊥ :=
    (label_faceCell (restrictFace_donor hα) y).trans rfl
  exact (congrArg (blockEncode _ 2) hl).trans blockEncode_bot

/-! ### The seed of the context and a three-point carrier of the donor -/

theorem univ_map_castSuccEmb_mem_faces_context :
    univ.map (Fin.castSuccEmb : Fin 2 ↪ Fin 3) ∈ (context hα).toCellScheme.faces :=
  ((restrictFace_eq_some_iff _ _).mp
    ((lower hα).restrictFace_left_truncate hα.isSuccPrelimit)).1

noncomputable def faceZeroOne : StageType.{u} α 2 :=
  (context hα).comap Fin.castSuccEmb (univ_map_castSuccEmb_mem_faces_context hα)

theorem restrictFace_faceZeroOne :
    restrictFace Fin.castSuccEmb (context hα) = some (faceZeroOne hα) :=
  restrictFace_of_mem _ _ _

theorem restrictFace_faceZeroOne_root :
    restrictFace Fin.castSuccEmb (faceZeroOne hα) = some root := by
  rw [restrictFace_trans _ _ _ (restrictFace_faceZeroOne hα)]
  exact restrictFace_context hα

theorem exists_threePoint : ∃ tb : StageType.{u} α 3, tb.IsLegal ∧
    restrictFace Fin.castSuccEmb tb = some (faceZeroOne hα) ∧
    restrictFace (extendByLast Fin.castSuccEmb) tb = some (donor hα) :=
  exists_coatomExtension_of_le_two hα.isSuccPrelimit (m := 1) (by omega) _ _ _
    ((isLegal_context hα).restrictFace _ (restrictFace_faceZeroOne hα)) (isLegal_donor hα)
    (restrictFace_faceZeroOne_root hα) (restrictFace_donor hα)

/-- **The seed of the context and a three-point carrier of the donor** over the face of the
context on `{0, 1}`. -/
noncomputable def seedFour : Seed.{u} α 2 :=
  Seed.ofCoatoms (isLegal_context hα) (exists_threePoint hα).choose_spec.1
    (restrictFace_faceZeroOne hα) (exists_threePoint hα).choose_spec.2.1

theorem restrictFace_amalgam_context :
    restrictFace Fin.castSuccEmb (seedFour hα).amalgam = some (context hα) :=
  (seedFour hα).restrictFace_left

theorem restrictFace_amalgam_donor :
    restrictFace (extendByLast rootEmb) (seedFour hα).amalgam = some (donor hα) := by
  have h : extendByLast rootEmb =
      (extendByLast (Fin.castSuccEmb : Fin 1 ↪ Fin 2)).trans
        (extendByLast (Fin.castSuccEmb : Fin 2 ↪ Fin 3)) := by
    rw [extendByLast_trans]
    rfl
  rw [h, ← restrictFace_trans _ _ _ (seedFour hα).restrictFace_right]
  exact (exists_threePoint hα).choose_spec.2.2

noncomputable abbrev capA : Fin (seedFour hα).amalgam.card :=
  faceCell (restrictFace_amalgam_context hα) (capCell hα)

noncomputable abbrev apexA : Fin (seedFour hα).amalgam.card :=
  faceCell (restrictFace_amalgam_donor hα) (donorApex hα)

/-- **Cap requests with cap and marker the cap of the context**, threshold `3`, and any set `T` of
cells read from below. -/
noncomputable def capRequestsT (T : Set (Fin (seedFour hα).amalgam.card)) :
    CapRequests (Fin (seedFour hα).amalgam.card) where
  cap := capA hα
  N := 3
  R := 0
  R_lt_N := by omega
  Z := ∅
  F := ∅
  T := T
  ref := id
  off := fun _ ↦ 0
  marker := capA hα

/-- **The engine's coatom provision fails at this acquired context**: for every set `T` of cells
read from below containing the apex of the donor (the donor's cells labelled `⊤`, for instance),
the coatom provision from the grade `3` of the admission of correct states fails.  The separating
labelling, `⊤` at the cap and reading the two root cells (labelled `⊥`) as `1 < 2`, is lawful
below the private coatom; the provision's cap is `⊤`, so its splice must be `⊤` at the apex of the
donor, whose row ties the two root cells. -/
theorem not_coatomProvision (T : Set (Fin (seedFour hα).amalgam.card)) (hT : apexA hα ∈ T) :
    ¬ CoatomProvision (seedFour hα) 3 (capRequestsT hα T).IsCorrect := by
  have hα' := hα.isSuccPrelimit
  obtain ⟨F⟩ := (seedFour hα).nonempty_completionBelowFullGrade_of_le_two le_rfl
  have hD := F.restrictFace_left_completion hα'
  obtain ⟨a, ha, hext⟩ := exists_isLawful_extend_of_restrictFace (F.isLegal_completion hα') hD
    (isLawful_separating hα)
  set W : Prof (seedFour hα) := fun d ↦ a (F.embed d).castSucc
  have hCne : (univ.erase (Fin.last 3) : Finset (Fin 4)) ≠ univ := Seed.ne_univ_erase _
  have hW : (seedFour hα).amalgam.rows.IsLawfulBelow (univ.erase (Fin.last 3), 3)
      (fun d ↦ W d) := by
    have h := (F.isLawfulBelow_embed_iff (X := (univ.erase (Fin.last 3), 3)) hCne
      (w := fun z ↦ a z.castSucc)).mp ((F.isLawful_comp_castSucc hα' ha).isLawfulBelow _)
    exact h
  have hT' := F.restrictFace_left_truncate hα'
  have hWz (z : Fin (context hα).card) :
      W (faceCell (restrictFace_amalgam_context hα) z) = separating hα z := by
    have h1 := F.faceCell_truncate hα' Coatom.univ_map_left_ne hT'
      (restrictFace_amalgam_context hα) z
    have h2 := F.faceCell_completion hα' Coatom.univ_map_left_ne hT' hD z
    have h3 : faceCell hD z = (F.embed (faceCell (restrictFace_amalgam_context hα) z)).castSucc :=
      h2.trans (congrArg Fin.castSucc h1)
    exact (congrArg a h3).symm.trans (hext z)
  have hbelowC (z : Fin (context hα).card) :
      faceCell (restrictFace_amalgam_context hα) z ∈
        (seedFour hα).amalgam.toCellScheme.below (univ.erase (Fin.last 3), 3) := by
    rw [CellScheme.mem_below]
    refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
    · change (seedFour hα).amalgam.toCellScheme.scope _ ⊆ _
      rw [scope_faceCell, ← Coatom.univ_map_left]
      exact map_subset_map.mpr (subset_univ _)
    · change (seedFour hα).amalgam.toCellScheme.grade _ ≤ 3
      rw [grade_faceCell]
      exact (context hα).grade_le z
  have hcapg : (seedFour hα).amalgam.toCellScheme.grade (capA hα) = 3 :=
    (grade_faceCell _ _).trans (context_grade_cap hα)
  refine not_coatomProvision_of_forbidden (Q := fun s ↦ s (apexA hα) = ⊤) (by omega) le_rfl
    (by simp) hW hcapg (hbelowC _) ((hWz _).trans (separating_capCell hα))
    (fun s hs hcap ↦ ?_) fun W' hW' hW'W happex ↦ ?_
  · have h := hs.markerValue_le _ hT
    simp only [CapRequests.markerValue, capRequestsT, hcap, visibilityReplace_top, min_self,
      min_top_right] at h
    exact top_le_iff.mp h
  · obtain ⟨-, hW'D⟩ := hW'
    have hW'z (z : Fin (context hα).card) :
        W' (faceCell (restrictFace_amalgam_context hα) z) = separating hα z :=
      (hW'W _ (hbelowC z)).trans (hWz z)
    have happex' : W' (apexA hα) = ⊤ := by
      rwa [hat_of_le ((grade_faceCell _ _).trans_le (((donor hα).grade_le _).trans
        (by omega)))] at happex
    obtain ⟨-, hloc, -⟩ := CellScheme.Rows.isLawfulBelow_iff_forall.mp hW'D
    have hAb : apexA hα ∈ (seedFour hα).amalgam.toCellScheme.below
        ((univ : Finset (Fin 4)).erase (Fin.castSucc (Fin.last 2)), 3) := by
      rw [CellScheme.mem_below]
      refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
      · rw [scope_faceCell]
        intro x hx
        obtain ⟨y, -, rfl⟩ := mem_map.mp hx
        refine mem_erase.mpr ⟨?_, mem_univ _⟩
        induction y using Fin.lastCases with
        | last =>
          rw [extendByLast_last]
          exact fun h ↦ absurd (congrArg Fin.val h) (by simp)
        | cast y =>
          obtain rfl : y = 0 := Subsingleton.elim _ _
          rw [extendByLast_castSucc]
          exact fun h ↦ absurd (congrArg Fin.val h) (by simp [rootEmb])
      · rw [grade_faceCell]
        exact ((donor hα).grade_le _).trans (by omega)
    have hy (i : Fin 2) : faceCell (restrictFace_amalgam_donor hα)
        (faceCell (restrictFace_donor hα) i) ∈ (seedFour hα).amalgam.toCellScheme.below
          ((seedFour hα).amalgam.toCellScheme.gradedIndex (apexA hα)) := by
      have hz := mem_below_donor_last hα (faceCell (restrictFace_donor hα) i)
      rw [CellScheme.mem_below] at hz ⊢
      obtain ⟨hs, hgr⟩ := Prod.mk_le_mk.mp hz
      refine Prod.mk_le_mk.mpr ⟨?_, ?_⟩
      · change (seedFour hα).amalgam.toCellScheme.scope _ ⊆
          (seedFour hα).amalgam.toCellScheme.scope _
        rw [scope_faceCell, scope_faceCell]
        exact map_subset_map.mpr hs
      · change (seedFour hα).amalgam.toCellScheme.grade _ ≤
          (seedFour hα).amalgam.toCellScheme.grade _
        rw [grade_faceCell, grade_faceCell]
        exact hgr
    have hrow (i : Fin 2) : (seedFour hα).amalgam.rows.row (apexA hα) ⟨_, hy i⟩ = ⊥ := by
      rw [← Scheme.rowAt_of_mem (hy i), rowAt_faceCell (restrictFace_amalgam_donor hα),
        Scheme.rowAt_of_mem (mem_below_donor_last hα _)]
      exact donor_row_root hα _ _
    have hW'y (i : Fin 2) : W' (faceCell (restrictFace_amalgam_donor hα)
        (faceCell (restrictFace_donor hα) i)) = rootRow i := by
      rw [← faceCell_faceCell (restrictFace_amalgam_context hα) (restrictFace_amalgam_donor hα)
        (restrictFace_context hα) (restrictFace_donor hα) i, hW'z]
      exact separating_root hα i
    have hloc' := (hloc _ hAb).le_of_le (d := ⟨_, hy ⟨1, by decide⟩⟩)
      (d' := ⟨_, hy ⟨0, by decide⟩⟩) (le_of_eq ((hrow _).trans (hrow _).symm)) (by
        rw [grade_faceCell, grade_faceCell]
        exact le_of_eq ((grade_faceCell (restrictFace_donor hα) (⟨0, by decide⟩ : Fin 2)).trans
          (grade_faceCell (restrictFace_donor hα) (⟨1, by decide⟩ : Fin 2)).symm))
    change min (W' _) (W' _) ≤ min (W' _) (W' _) at hloc'
    rw [happex', min_top_right, min_top_right, hW'y, hW'y] at hloc'
    exact absurd (natCast_label_le.mp hloc') (by decide)

/-- The separating labelling is not in the bottom class of the context: the root cells are
labelled `⊥` and it reads them as `1` and `2`. -/
theorem separating_not_inClass :
    ¬ ∀ z, separating hα z = ⊥ ↔ (context hα).label z = ⊥ := fun h ↦ by
  have := (h (faceCell (restrictFace_context hα) (⟨0, by decide⟩ : Fin 2))).mpr
    ((label_faceCell _ _).trans rfl)
  rw [separating_root] at this
  exact absurd this (natCast_label_ne_bot _)

end BottomRootCounterexample

end VaughtConjecture
